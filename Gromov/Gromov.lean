import Mathlib
import Mathlib.Algebra.Group.Gromov.UnitaryGromov
import Mathlib.Algebra.Group.Gromov.UnipotentGromov

set_option linter.style.longLine false
set_option linter.style.cdot false
-- TODO - vscode stops reporting underlines if there are too many total underlines / gutter messages
-- I've disabled some failing lints for now so that error underlines still sho up
set_option linter.style.commandStart false
--set_option linter.unusedVariables true
--set_option linter.unusedVariables.analyzeTactics true

open Subgroup
open scoped Finset
open scoped Pointwise

-- Based on https://github.com/YaelDillies/LeanCamCombi/blob/b6312bee17293272af6bdcdb47b3ffe98fca46a4/LeanCamCombi/GrowthInGroups/Lecture1.lean#L41
-- and the Vikman paper
def HasPolynomialGrowthD {G: Type*} [Group G] [DecidableEq G] (S: Finset G) (d: ℕ): Prop := ∃ a: ℕ, ∀ n ≥ 1, #(S ^ n) ≤ a * n ^ d
def HasPolynomialGrowth  {G: Type*} [Group G] [DecidableEq G] (S: Finset G): Prop := ∃ d, HasPolynomialGrowthD S d


-- TODO - I don't really understand why `S` needs to be an `outParam`?
-- If I remove that, then the `PseudoMetricSpace G` starts erroring
-- See also:
-- * `set_option synthInstance.checkSynthOrder false`
class Generates where
  G: Type*
  g_group: Group G
  g_eq: DecidableEq G
  S: Finset G
  hS: Nonempty S
  generates : ((closure (S : Set G) : Set G) = ⊤)
  -- This should be fine, since the growth rate doesn't depend on the generating set
  one_mem: (1 : G) ∈ S
  has_inv: ∀ g ∈ S, g⁻¹ ∈ S
  g_infinite: Infinite G

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

instance G_group: Group G := hGS.g_group
instance G_dec_eq: DecidableEq G := hGS.g_eq
-- [hGS': Generates (S := S')] [hS': Nonempty S]


lemma s_union_sinv : S ∪ S⁻¹ = S := by
  ext a
  have foo := hGS.has_inv (a⁻¹)
  simp only [inv_inv] at foo
  simpa using foo

lemma S_eq_Sinv: S = S⁻¹ := by
  ext a
  refine ⟨?_, ?_⟩
  . intro ha
    have a_inv := hGS.has_inv a ha
    exact Finset.mem_inv'.mpr a_inv
  . intro ha
    simp at ha
    have a_inv := hGS.has_inv a⁻¹ ha
    simp only [inv_inv] at a_inv
    exact a_inv

instance G_FG: Group.FG G := {
  out := by
    unfold Subgroup.FG
    use S
    have foo := hGS.generates
    simp at foo
    exact foo
}



lemma mem_closure (x: G): x ∈ closure (S : Set G) := by
  have hg := hGS.generates
  simp only [Set.top_eq_univ, coe_eq_univ] at hg
  simp [hg]

-- Predicate stating that an element of G equals a product of elements of S
def ProdS (x: G) (l: List S): Prop := l.unattach.prod = x

-- Each element of G can be written as a product of elements of S in at least one way
lemma mem_S_prod_list (x: G): ∃ l: List S, ProdS x l := by
  -- https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Group.20.28.2FMonoid.2Fetc.29.20closures.20are.20a.20finite.20product.2Fsum/near/477951441
  have foo := Submonoid.exists_list_of_mem_closure (s := S ∪ S⁻¹) (x := x)
  rw [← Subgroup.closure_toSubmonoid _] at foo
  simp only [mem_toSubmonoid, Finset.mem_coe] at foo
  specialize foo (mem_closure x)
  norm_cast at foo
  rw [s_union_sinv] at foo
  obtain ⟨l, ⟨mem_s, prod_eq⟩⟩ := foo
  use (l.attach).map (fun x => ⟨x.val, mem_s (x.val) x.property⟩)
  unfold ProdS
  unfold List.unattach
  simp [prod_eq]

lemma list_tail_unattach (T: Type*)  {p : T → Prop} (l: List { x : T // p x}): l.tail.unattach = l.unattach.tail := by
  unfold List.unattach
  simp

noncomputable def WordNorm (g: G) := sInf {n: ℕ | ∃ l: List S, l.length = n ∧ ProdS g l}

lemma word_norm_prod (g: G) (n: ℕ) (hgn: WordNorm g = n): ∃ l: List S, ProdS g l ∧ l.length = n := by
  have foo := Nat.sInf_mem (s := {n: ℕ | ∃ l: List S, l.length = n ∧ ProdS g l})
  obtain ⟨l, hl⟩ := mem_S_prod_list  g
  unfold ProdS at hl
  rw [Set.nonempty_def] at foo
  specialize foo ⟨l.length, ⟨l, ⟨by simp, hl⟩⟩⟩
  simp only [Set.mem_setOf_eq] at foo
  obtain ⟨l, ⟨hl, hl_prod⟩⟩ := foo
  rw [← hgn]
  exact ⟨l, ⟨hl_prod, hl⟩⟩

lemma word_norm_prod_self (g: G): ∃ l: List S, ProdS g l ∧ l.length = WordNorm  g := by
  exact word_norm_prod  g (WordNorm  g) rfl

lemma word_norm_le (g: G) (l: List S) (hgl: ProdS g l): WordNorm  g ≤ l.length := by
  unfold WordNorm
  apply Nat.sInf_le
  use l

-- TODO - this probably needs to be swapped to make 'gAct' work
noncomputable def WordDist (x y: G) := WordNorm  (y * x⁻¹)

lemma WordDist_self (x: G): WordDist  x x = 0 := by
  unfold WordDist
  rw [mul_inv_cancel]
  unfold WordNorm
  simp only [Nat.sInf_eq_zero, Set.mem_setOf_eq, List.length_eq_zero_iff, exists_eq_left]
  left
  rfl

lemma WordDist_swap_le (x y: G): WordDist  y x ≤ WordDist  x y := by
  unfold WordDist
  obtain ⟨l, l_prod, l_len⟩ := word_norm_prod (y * x⁻¹) (WordNorm (y * x⁻¹)) (rfl)
  unfold ProdS at l_prod
  apply_fun (fun x => x⁻¹) at l_prod
  rw [mul_inv_rev, inv_inv] at l_prod
  rw [List.prod_inv_reverse] at l_prod

  have commute_unattach: List.map (Inv.inv) l.unattach = (l.map (fun x => ⟨x.val⁻¹, hGS.has_inv x.val x.property⟩)).unattach := by
    apply List.ext_getElem?
    intro i
    simp


  rw [commute_unattach, ← List.unattach_reverse] at l_prod
  have prod_le := word_norm_le  (x * y⁻¹) _ l_prod
  conv at prod_le =>
    rhs
    equals l.length =>
      simp
  rw [l_len] at prod_le
  exact prod_le

lemma WordDist_comm (x y: G): WordDist  x y = WordDist  y x := by
  have le_left := WordDist_swap_le  x y
  have le_right := WordDist_swap_le  y x
  exact Nat.le_antisymm le_right le_left

lemma WordDist_triangle (x y z: G): WordDist  x z ≤ WordDist  x y + WordDist  y z := by
  have eq_through_y: z * x⁻¹ = z  * y * y⁻¹ * x⁻¹ := by
    simp

  unfold WordDist
  obtain ⟨l_x_y, x_y_prod, x_y_len⟩ := word_norm_prod_self  (y * x⁻¹)
  obtain ⟨l_y_z, y_z_prod, y_z_len⟩ := word_norm_prod_self  (z * y⁻¹)
  unfold ProdS at x_y_prod
  unfold ProdS at y_z_prod

  have prod_append: ProdS  (z * x⁻¹) (l_y_z ++ l_x_y) := by
    unfold ProdS
    simp
    rw [x_y_prod, y_z_prod]
    rw [← mul_assoc]
    simp

  have le_append := word_norm_le  (z * x⁻¹) _ prod_append
  rw [List.length_append] at le_append
  rw [x_y_len, y_z_len] at le_append
  rw [add_comm] at le_append
  exact le_append

-- TODO - I'm not certain that these are actually the correct instances for the proof


noncomputable instance WordDist.instPseudoMetricSpace: PseudoMetricSpace G where
  dist x y := WordDist  x y
  dist_self x := by
    norm_cast
    exact WordDist_self  x
  dist_comm x y := by
    norm_cast
    exact WordDist_comm  x y
  dist_triangle x y z := by
    norm_cast
    exact WordDist_triangle  x y z

lemma word_norm_eq_zero {x y: G} (hdist: WordDist x y = 0): x = y := by
  simp [WordDist, WordNorm] at hdist
  match hdist with
  | .inl empty_prod =>
    unfold ProdS at empty_prod
    simp only [List.unattach_nil, List.prod_nil] at empty_prod
    apply_fun (fun y => y * x) at empty_prod
    simpa using empty_prod
  | .inr empty_set =>
    obtain ⟨l, hl⟩ := mem_S_prod_list  (y * x⁻¹)
    unfold ProdS at hl
    have len_in_set: l.unattach.length ∈ (∅ : Set ℕ) := by
      rw [← empty_set]
      simp only [List.length_unattach, Set.mem_setOf_eq]
      use l
      refine ⟨rfl, hl⟩
    simp only [Set.mem_empty_iff_false] at len_in_set

lemma dist_word_mul {x y : G} (hy: y ∈ S): dist x (y * x) ≤ 1 := by
  simp [dist, WordDist, WordNorm]
  apply csInf_le
  . simp
  . simp
    use [⟨y, hy⟩]
    simp [ProdS]

lemma dist_word_mul_le {x y z : G} (hy: y ∈ S): dist x (y * z) ≤ 1 + dist x z := by
  conv =>
    lhs
    simp [dist, WordDist, WordNorm]

  grw [csInf_le (a := 1 + (WordDist x z))]
  . simp [dist]
  . simp
  . simp

    have dist_eq: dist x z = dist x z := rfl
    conv at dist_eq =>
      lhs
      simp [dist, WordDist, WordNorm]

    have inf_mem := csInf_mem (s := {n | ∃ l, l.length = n ∧ ProdS (z * x⁻¹) l}) ?_
    .
      simp at inf_mem
      obtain ⟨l, l_len, l_prod⟩ := inf_mem
      simp [ProdS] at l_prod
      use [⟨y, hy⟩] ++ l
      simp [l_len, WordDist, WordNorm]
      rw [add_comm]
      simp
      simp [ProdS]
      rw [l_prod]
      group
    .
      obtain ⟨l, l_prod⟩ := mem_S_prod_list (z * x⁻¹)
      use l.length
      simp
      use l

lemma dist_word_le_mul {x y z : G} (hy: y ∈ S): WordDist x z ≤ (WordDist x (y * z)) + 1 := by
  by_cases x_eq: x = y * z
  . simp [x_eq]
    rw [WordDist_self]
    simp
    simp [WordDist_comm]
    have mul_dist := dist_word_mul (x := z) (y := y) hy
    simp [dist] at mul_dist
    exact mul_dist


  conv =>
    lhs
    simp [dist, WordDist, WordNorm]


  grw [csInf_le (a := (WordDist x (y * z)) + 1)]
  .
    simp


  simp
  obtain ⟨l, l_prod, l_len⟩ := word_norm_prod (n := WordDist x (y * z)) (y * z * x⁻¹) (rfl)
  match l with
  | [] =>
    simp [ProdS] at l_prod
    simp at l_len
    simp [← l_len]
    simp [ProdS]
    rw [eq_comm] at l_prod
    rw [mul_inv_eq_one] at l_prod
    grind
  | h::tail =>
    use [ ⟨y⁻¹, by simp [hGS.has_inv, hy]⟩, ⟨h.val, by simp [hGS.has_inv]⟩,] ++ tail
    simp [ProdS]
    simp [← l_len]
    simp [ProdS] at l_prod
    simp [l_prod]
    group

noncomputable instance WordDist.instMetricSpace: MetricSpace G where
  eq_of_dist_eq_zero := by
    intro x y hdist
    apply word_norm_eq_zero
    simp [dist] at hdist
    exact hdist

-- TODO - is there an easier way to transfer all of the theorems/instances from `G` to `Additive G`?

noncomputable instance WordDist.instPseudoMetricSpaceAddOpp: PseudoMetricSpace (Additive G) where
  dist x y := dist x.toMul y.toMul
  dist_self x := by
    apply PseudoMetricSpace.dist_self
  dist_comm x y := by
    apply PseudoMetricSpace.dist_comm
  dist_triangle x y z := by
    apply PseudoMetricSpace.dist_triangle

noncomputable instance WordDist.instMetricSpaceAddOpp: MetricSpace (Additive G) where
  eq_of_dist_eq_zero := by
    intro x y hxy
    have := MetricSpace.eq_of_dist_eq_zero (x := x.toMul) (y := y.toMul) hxy
    exact this


--def WordMetricSpace := MetricSpace.ofDistTopology ()
noncomputable instance WordDist.instMeasurableSpace: MeasurableSpace G := borel G

noncomputable instance WordDist.instMeasureableSpaceOpp: MeasurableSpace (Additive G) := borel (Additive G)

noncomputable instance WordDist.instBorelSpace: BorelSpace G where
  measurable_eq := rfl


noncomputable instance WordDist.instBorelSpaceAddOpp: BorelSpace (Additive G) where
  measurable_eq := rfl

-- TODO - are we really supposed to be using a metric topology if it turns out to be the discrete topology?
lemma singleton_open (x: G): IsOpen {x} := by
  rw [Metric.isOpen_singleton_iff]
  use 1
  simp only [gt_iff_lt, zero_lt_one, true_and]
  intro y hy
  simp [dist] at hy
  have dist_zero := dist_eq_zero (x := y) (y := x)
  simp [dist] at dist_zero
  rw [dist_zero] at hy
  exact hy

instance discreteTopology: DiscreteTopology G := by
  rw [← singletons_open_iff_discrete]
  exact singleton_open

instance : ContinuousMul G where
  continuous_mul := continuous_of_discreteTopology

instance : ContinuousInv G where
  continuous_inv := continuous_of_discreteTopology

instance: IsTopologicalGroup G where
  continuous_mul := continuous_of_discreteTopology
  continuous_inv := continuous_of_discreteTopology


-- instance IsTopologicalGroupAddOpp: IsTopologicalAddGroup (Additive G) where
--   continuous_add := continuous_of_discreteTopology
--   continuous_neg := continuous_of_discreteTopology

-- Define Haar measure so that singleton sets have measure 1 -
-- I think this is what we want in order to be able to nicely convert integrals to sums
noncomputable def haarSingleton: TopologicalSpace.PositiveCompacts G := {
  carrier := {1}
  isCompact' := by
    simp
  interior_nonempty' := by
    have one_mem: (1 : G) ∈ interior {1} := by
      rw [mem_interior]
      use {1}
      simp
    apply Set.nonempty_def.mpr
    exact ⟨1, one_mem⟩
}

lemma mul_singleton_carrier: (haarSingleton.carrier) = ({1} : (Set G)) := by
  unfold haarSingleton
  rfl

noncomputable abbrev myHaar := MeasureTheory.Measure.haarMeasure haarSingleton

noncomputable instance WordDist.measureSpace: MeasureTheory.MeasureSpace G := {
  volume := myHaar
}

noncomputable def addHaarSingleton: TopologicalSpace.PositiveCompacts (Additive G) := {
  carrier := {0}
  isCompact' := by
    simp
  interior_nonempty' := by
    have zero_mem: (0 : Additive G) ∈ interior {0} := by
      rw [mem_interior]
      use {0}
      simp
    apply Set.nonempty_def.mpr
    exact ⟨0, zero_mem⟩
}

lemma singleton_carrier: (addHaarSingleton.carrier) = ({0} : (Set (Additive G))) := by
  unfold addHaarSingleton
  rfl

noncomputable abbrev myHaarAddOpp := MeasureTheory.Measure.addHaarMeasure (G := Additive G) addHaarSingleton

-- Definition 3.5 in Vikman - a harmonic function on G
-- Note that our multiplication order is swapped: f (s * x) instead of f (x * s)
-- This is needed to make it match up with the result of MeasureTheory.convolution
def Harmonic (f: G → ℂ): Prop := ∀ x: G, f x = ((1 : ℂ) / #(S)) * ∑ s ∈ S, f (s * x)

-- A Lipschitz harmonic function from section 3.2 of Vikman
structure LipschitzH [Generates ] where
  -- The underlying function
  toFun: G → ℂ
  -- The function is Lipschitz for some constant C
  lipschitz: ∃ C, LipschitzWith C toFun
  -- The function is harmonic
  harmonic: Harmonic  toFun

def IsLipschitz (f: G → ℂ) := ∃ C, LipschitzWith C f

instance: FunLike (LipschitzH) G ℂ where
  coe := LipschitzH.toFun
  -- TODO - why does this work? I blindly copied it from `OneHom.funLike`
  coe_injective' f g h := by cases f; cases g; congr

@[ext]
theorem LipschitzH.ext [Generates ] {f g: LipschitzH} (h: ∀ x, f.toFun x = g.toFun x): f = g := DFunLike.ext _ _ h

instance LipschitzH.add [Generates ] : Add (LipschitzH) := {
  add := fun f g => {
    toFun := fun x => f.toFun x + g.toFun x
    lipschitz := by
      obtain ⟨C1, hC1⟩ := f.lipschitz
      obtain ⟨C2, hC2⟩ := g.lipschitz
      use C1 + C2
      exact LipschitzWith.add hC1 hC2
    harmonic := by
      unfold Harmonic
      intro x
      have ha := f.harmonic
      have hb := g.harmonic
      unfold Harmonic at ha hb
      simp_rw [ha x, hb x]
      field_simp
      rw [← Finset.sum_add_distrib]
  }
}


-- TODO - mark this as a simp lemma
@[simp]
lemma LipschitzH_apply [Generates ] (f: LipschitzH) (x: G): f x = f.toFun x := rfl


lemma S_nonempty: S.Nonempty := by exact Finset.nonempty_coe_sort.mp hS

def ConstLipschitzH (z: ℂ) : LipschitzH := {
  toFun := fun x => z
  lipschitz := by
    use 0
    apply LipschitzWith.const
  harmonic := by
    unfold Harmonic
    intro x
    simp
    field_simp
    have card_ne_zero: (#(S) : ℂ) ≠ 0 := by
      norm_cast
      simp
      have foo := hS
      simp only [nonempty_subtype] at foo
      exact Finset.nonempty_iff_ne_empty.mp foo
    field_simp
}

lemma ConstLipschitzH_apply (z : ℂ) (g: G): (ConstLipschitzH z) g = z := by
  unfold ConstLipschitzH
  rfl

instance LipschitzH.zero [Generates ] : Zero (LipschitzH) := {
  zero := {
    toFun := fun x => 0
    lipschitz := by
      use 0
      exact LipschitzWith.const 0
    harmonic := by simp [Harmonic]
  }
}


@[simp]
theorem LipschitzH.add_apply (f g: LipschitzH) (x: G): (f + g).toFun x = f x + g x := by
  unfold LipschitzH.add
  rfl

instance lipschitzSMul: SMul ℂ (LipschitzH) := {
  smul := fun c f => {
    toFun := fun x => c * f.toFun x
    lipschitz := by
      conv =>
        rhs
        intro C
        rhs
        equals (fun (x: ℂ) => c * x) ∘ f.toFun =>
          unfold Function.comp
          simp
      obtain ⟨C, hC⟩ := f.lipschitz
      use ‖c‖₊ * C
      apply LipschitzWith.comp (lipschitzWith_smul _) hC
    harmonic := by
      unfold Harmonic
      intro x
      field_simp
      rw [← Finset.mul_sum]
      rw [← mul_div]
      rw [mul_eq_mul_left_iff]
      left
      have hf := f.harmonic x
      unfold Harmonic at hf
      simp at hf
      field_simp at hf
      exact hf
  }
}


instance negLipschitzH: Neg (LipschitzH) := {
  neg := fun f => {
    toFun := fun x => -f.toFun x
    lipschitz := by
      obtain ⟨C, hC⟩ := f.lipschitz
      use C
      exact LipschitzWith.neg hC
    harmonic := by
      have f_harmonic := f.harmonic
      simp [Harmonic] at f_harmonic
      unfold Harmonic
      intro g
      simp
      specialize f_harmonic g
      exact f_harmonic
  }
}

-- TODO - is there an existing instance we should be using here?
instance subLipschithZ: Sub (LipschitzH) := {
  sub := fun f g => f + -g
}

instance lipschitzSmulZ: SMul ℤ (LipschitzH) := {
  smul := fun n f => (n : ℂ) • f
}



@[simp]
lemma lipschitz_neg_tofun (f: LipschitzH): (-f).toFun = -(f.toFun) := by
  rfl


@[simp]
lemma lipschitz_add_tofun (f g: LipschitzH): (f + g).toFun = f.toFun + g.toFun := by
  rfl

@[simp]
lemma lipschitz_sub_tofun (f g: LipschitzH): (f - g).toFun = f.toFun - g.toFun := by
  rfl

@[simp]
lemma lipschitz_smul_tofun (c: ℂ) (f: LipschitzH): (c • f).toFun = c • f.toFun := by
  rfl

instance LipschitzH.addMonoid [Generates ] : AddMonoid (LipschitzH) := {
  LipschitzH.zero,
  LipschitzH.add with
  add_assoc := fun _ _ _ => ext fun _ => add_assoc _ _ _
  zero_add := fun _ => ext fun _ => zero_add _
  add_zero := fun _ => ext fun _ => add_zero _
  nsmul := fun n f => (n : ℂ) • f
  nsmul_zero := by
    intro f
    dsimp [HSMul.hSMul, SMul.smul]
    dsimp [OfNat.ofNat]
    dsimp [Zero.zero]
    simp
  nsmul_succ := by
    intro n f
    ext g
    simp [lipschitz_smul_tofun]
    rw [add_mul]
    simp
}


-- -- See https://github.com/leanprover-community/mathlib4/blob/6c6e0180f0d3dc9f47f85532f48d268d8656789a/Mathlib/Topology/ContinuousMap/Bounded/Normed.lean#L194-L196
-- instance lipschitzHAddCommGroup: AddCommGroup (LipschitzH) := by
--   apply DFunLike.coe_injective.addCommGroup
--   .
--     ext g
--     simp [DFunLike.coe]
--     unfold Zero.toOfNat0
--     simp [Zero.zero]
--   .
--     intro x y
--     simp [DFunLike.coe]
--     ext g
--     simp [DFunLike.coe]
--   . intro f
--     ext g
--     simp [DFunLike.coe]
--     simp [negLipschitzH]
--   .
--     intro f h
--     ext g
--     simp [DFunLike.coe]
--     conv =>
--       lhs
--       dsimp [HSub.hSub]
--     simp [subLipschithZ]
--     simp [DFunLike.coe]
--     simp [negLipschitzH]
--     rw [sub_eq_add_neg]
--   . intro f
--     intro n
--     simp [DFunLike.coe]
--     dsimp [HSMul.hSMul]
--     dsimp [SMul.smul]



instance LipschitzH.instAddCommMonoid: AddCommMonoid (LipschitzH) := {
  LipschitzH.addMonoid with add_comm := fun _ _ => ext fun _ => add_comm _ _
}



instance LipschitzH.instAddCommGroup: AddCommGroup (LipschitzH) := {
  LipschitzH.instAddCommMonoid with
  sub_eq_add_neg := by
    intro f h
    ext g
    simp [lipschitz_sub_tofun, lipschitz_add_tofun, lipschitz_neg_tofun]
    rfl
  zsmul := fun n f => (n : ℂ) • f
  zsmul_zero' := by
    intro f
    dsimp [HSMul.hSMul, SMul.smul]
    ext g
    simp [DFunLike.coe]
    unfold Zero.toOfNat0
    unfold OfNat.ofNat
    simp [Zero.zero]
  neg_add_cancel := by
    intro f
    ext g
    simp [negLipschitzH]
    unfold Zero.toOfNat0
    unfold OfNat.ofNat
    simp [Zero.zero]
  zsmul_succ' := by
    intro n f
    simp
    ext g
    simp [lipschitz_smul_tofun]
    rw [add_mul]
    simp
  zsmul_neg' := by
    intro n hn
    simp
    ext g
    simp [lipschitz_smul_tofun]
    group
}


-- V is the vector space
abbrev V := Module ℂ (LipschitzH)



@[simp]
lemma zero_apply (x: G): (0: LipschitzH ).toFun x = 0 := by
  unfold LipschitzH.zero
  rfl

--set_option pp.all true

instance lipschitzHVectorSpace : V := {
  smul := lipschitzSMul.smul
  one_smul := by simp [HSMul.hSMul, SMul.smul]
  mul_smul := by
    intro x y f
    simp [HSMul.hSMul, SMul.smul]
    ext g
    rw [mul_assoc]
  smul_zero := by
    intro c
    dsimp [HSMul.hSMul, SMul.smul]
    ext g
    simp
  smul_add := by
    intro a f g
    dsimp [HSMul.hSMul, SMul.smul]
    simp [mul_add]
    ext p
    simp [DFunLike.coe]
  add_smul := by
    intro a f g
    dsimp [HSMul.hSMul, SMul.smul]
    simp [add_mul]
    ext p
    simp [DFunLike.coe]
  zero_smul := by
    intro a
    dsimp [HSMul.hSMul, SMul.smul]
    dsimp [OfNat.ofNat]
    dsimp [Zero.zero]
    simp
}

instance V_FiniteDimentional: FiniteDimensional ℂ (LipschitzH) := by
  -- This is a very long part of the proof in Vikman
  sorry


def ConstF: Submodule ℂ (LipschitzH) := {
  carrier := Set.range ConstLipschitzH
  add_mem' := by
    intro a b ha hb
    simp at ha
    simp at hb
    obtain ⟨x, hx⟩ := ha
    obtain ⟨y, hy⟩ := hb
    simp
    use (x + y)
    ext g
    simp [ConstLipschitzH]
    rw [← hx, ← hy]
    dsimp [ConstLipschitzH]
  zero_mem' := by
    use (0 : ℂ)
    simp [ConstLipschitzH]
    ext g
    simp
  smul_mem' := by
    intro c f hf
    simp at hf
    simp
    obtain ⟨x, hx⟩ := hf
    use (c * x)
    ext g
    simp [ConstLipschitzH]
    left
    rw [← hx]
    simp [ConstLipschitzH]
}

instance isometricGMul: IsIsometricSMul (MulOpposite G) (G) where
  isometry_smul := by
    intro g
    simp [Isometry]
    intro a b
    simp [edist]
    simp [PseudoMetricSpace.edist]
    simp [WordDist]
    group


-- instance isometricGMul: IsIsometricSMul G G where
--   isometry_smul := by
--     intro g
--     simp [Isometry]
--     intro a b
--     simp [edist]
--     simp [PseudoMetricSpace.edist]
--     simp [WordDist]
--     group


def gAct (g: G) (v: LipschitzH ): LipschitzH  := {
  toFun := fun x => v (x * g)
  lipschitz := by
    obtain ⟨C, hC⟩ := v.lipschitz
    use C
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    rw [lipschitzWith_iff_dist_le_mul] at hC
    specialize hC (x * g) (y * g)
    simp [DFunLike.coe]
    grw [hC]
    simp [dist, WordDist]
    group
    rfl
  harmonic := by
    unfold Harmonic
    intro x
    simp
    have v_harmonic := v.harmonic
    simp [Harmonic] at v_harmonic
    specialize v_harmonic (x * g)
    rw [v_harmonic]
    simp_rw [← mul_assoc]
}

lemma gAct_mul (g h : G) (f: LipschitzH ): gAct (g * h) f = gAct g (gAct h f) := by
  unfold gAct
  ext x
  simp [DFunLike.coe]
  rw [← mul_assoc]



def gAct_const (g: G) (z: ℂ): gAct g (ConstLipschitzH z) = ConstLipschitzH z := by
  unfold gAct
  unfold ConstLipschitzH
  ext x
  simp [DFunLike.coe]

#synth Module ℂ (LipschitzH)
#synth AddCommGroup (LipschitzH)

abbrev W := (LipschitzH) ⧸ ConstF


instance W_FiniteDimensional: FiniteDimensional ℂ (W) := by
  -- This is a very long part of the proof in Vikman
  sorry


#synth Module ℂ (W)

def gActW (g: G): W → W := Quotient.lift (fun f => Submodule.Quotient.mk (gAct g f)) (by
  intro f h hfh
  simp
  rw [Submodule.Quotient.eq']
  dsimp [HasEquiv.Equiv] at hfh
  rw [ConstF.quotientRel_def] at hfh
  dsimp [gAct]
  simp [HAdd.hAdd]
  dsimp [Add.add]
  simp [ConstF] at hfh
  obtain ⟨z, hz⟩ := hfh
  simp [ConstLipschitzH] at hz
  simp [ConstF]
  simp [ConstLipschitzH]
  use -z
  ext a
  apply_fun LipschitzH.toFun at hz
  have app_eq := congrFun hz (a * g)
  simp at app_eq
  rw [app_eq]
  simp
  rw [sub_eq_add_neg]
  rw [add_comm]
)



noncomputable def LipschitzSemiNorm (f: G → ℂ): NNReal := sInf { k: NNReal | LipschitzWith k f }

-- The lift of LipschitzSemiNorm to W, using a proof that LipschitzSemiNorm doesn't depend on the choice representative
-- (adding a constant to a Lipschitz function doesn't change its Lipschitz constant)
noncomputable def LipschitzSemiNorm_w (w: W) := Quotient.lift ((fun f => LipschitzSemiNorm f.toFun)) (by
  intro f g hfg
  dsimp [HasEquiv.Equiv] at hfg
  rw [ConstF.quotientRel_def] at hfg
  simp [ConstF] at hfg
  obtain ⟨k, hk⟩ := hfg
  have f_eq_g_k: f = g + (ConstLipschitzH k) := by
    exact Eq.symm (add_eq_of_eq_sub' hk)
  rw [f_eq_g_k]
  simp [LipschitzSemiNorm]
  simp [LipschitzWith]
  simp_rw [edist_eq_enorm_sub]
  simp [ConstLipschitzH]
) w



lemma lipschiz_norm_zero: LipschitzSemiNorm  (0) = 0 := by
  unfold LipschitzSemiNorm
  have zero_mem: 0 ∈ { k: NNReal | LipschitzWith k (0 : LipschitzH) } := by
    simp
    apply LipschitzWith.const
  have sinf_le: sInf { k: NNReal | LipschitzWith k (0 : LipschitzH) } ≤ 0 := by
    exact csInf_le' zero_mem
  exact nonpos_iff_eq_zero.mp sinf_le



#synth IsStrictOrderedRing NNReal


lemma lipschitzWith_mul_prod  {K: Type*} [RCLike K] (f: G → K) {C: NNReal} (hf: ∀ g: G, ∀ s ∈ S, dist (f (s*g)) (f (g)) ≤ C)
  (g: G) (s: List S): dist (f (s.unattach.prod * g)) (f g) ≤ C * s.length := by

  induction s with
  | nil =>
    simp
  | cons head tail ih =>
    simp
    have triangle := dist_triangle (f (head * tail.unattach.prod * g)) (f (tail.unattach.prod * g)) (f g)
    grw [triangle]
    grw [ih]
    rw [mul_assoc]
    grw [hf _ _ (by simp)]
    grind

lemma lipschitzWith_discrete {K: Type*} [RCLike K] (f: G → K) {C: NNReal} (hf: ∀ g: G, ∀ s ∈ S, dist (f (s*g)) (f (g)) ≤ C):
    LipschitzWith C f := by

  apply LipschitzWith.of_dist_le_mul
  intro x y

  have prod_eq := word_norm_prod (y * x⁻¹) (WordNorm (y * x⁻¹)) rfl
  obtain ⟨l, l_prod, l_len⟩ := prod_eq
  simp [ProdS] at l_prod

  have mul_prod := lipschitzWith_mul_prod f hf x l
  simp [l_prod] at mul_prod
  rw [dist_comm]
  grw [mul_prod]
  simp [dist, WordDist, l_len]

-- TODO - upstream to mathlib
lemma lipschitz_attains_norm (f: G → ℂ) (hf: IsLipschitz f): LipschitzWith (LipschitzSemiNorm f) f := by
  by_contra!
  have orig_this := this
  simp [LipschitzWith] at this
  obtain ⟨x, y, hdist⟩ := this
  have edist_ne_zero: edist x y ≠ 0 := by
    by_contra!
    rw [this] at hdist
    simp at this
    rw [this] at hdist
    simp at hdist

  have edist_not_top: edist x y ≠ ⊤ := by
    rw [edist_nndist]
    exact ENNReal.coe_ne_top

  rw [← ENNReal.lt_div_iff_mul_lt (by simp) (Or.inl edist_not_top)] at hdist
  simp [LipschitzSemiNorm] at hdist
  have isglb_sinf := isGLB_csInf (s := { k: NNReal | LipschitzWith k f }) (by
    obtain ⟨K, hK⟩ := hf
    use K
    simp
    exact hK
  ) (by simp)



  have between := IsGLB.exists_between (b := (edist (f x) (f y) / edist x y).toNNReal) isglb_sinf (by
    rw [edist_nndist]
    rw [edist_nndist]
    conv =>
      rhs
      equals (nndist (f x) (f y)) / (nndist x y) =>
        rw [← ENNReal.coe_div]
        simp
        exact ENNReal.coe_ne_zero.mp edist_ne_zero

    rw [edist_nndist] at hdist
    rw [edist_nndist] at hdist
    have edist_gt_zero: edist x y > 0 := by
      exact pos_of_ne_zero edist_ne_zero

    have x_ne_y := edist_pos.mp edist_gt_zero

    conv at hdist =>
      rhs
      equals ENNReal.ofNNReal ((nndist (f x) (f y)) / (nndist x y)) =>
        rw [ENNReal.coe_div]
        simp [x_ne_y]


    norm_cast at hdist
  )
  obtain ⟨D, lipschitz_d, sinf_le_d, d_lt_slope⟩ := between
  simp [LipschitzWith] at lipschitz_d
  specialize lipschitz_d x y
  rw [mul_comm] at lipschitz_d
  apply ENNReal.div_le_of_le_mul' at lipschitz_d
  repeat rw [edist_nndist] at lipschitz_d
  repeat rw [edist_nndist] at d_lt_slope
  rw [← ENNReal.coe_div] at lipschitz_d
  .
    norm_cast at lipschitz_d
    rw [← ENNReal.coe_div] at d_lt_slope
    .
      norm_cast at d_lt_slope
      apply not_lt_of_le at lipschitz_d
      contradiction
    . rw [edist_nndist] at edist_ne_zero
      exact fun a ↦ edist_ne_zero (congrArg ENNReal.ofNNReal a)
  . rw [edist_nndist] at edist_ne_zero
    exact fun a ↦ edist_ne_zero (congrArg ENNReal.ofNNReal a)

lemma lipschitz_norm_triangle (x y z: G → ℂ) (hx: IsLipschitz x) (hy: IsLipschitz y) (hz: IsLipschitz z): LipschitzSemiNorm (x - z) ≤ LipschitzSemiNorm (x - y) + LipschitzSemiNorm (y - z) := by
  simp [LipschitzSemiNorm]
  conv =>
    pattern x - z
    equals (x - y) + (y - z) =>
      simp


  have sum_norm_mem: (LipschitzSemiNorm (x - y)) + (LipschitzSemiNorm (y - z)) ∈ { k: NNReal | LipschitzWith k ((x - y) + (y - z)) } := by
    simp only [LipschitzSemiNorm]
    apply LipschitzWith.add
    .
      apply lipschitz_attains_norm
      simp [IsLipschitz]
      simp [IsLipschitz] at hx
      simp [IsLipschitz] at hy
      obtain ⟨X, hX⟩ := hx
      obtain ⟨Y, hY⟩ := hy
      use X + Y
      apply LipschitzWith.sub hX hY
    .
      apply lipschitz_attains_norm
      simp [IsLipschitz]
      simp [IsLipschitz] at hy
      simp [IsLipschitz] at hz
      obtain ⟨Y, hY⟩ := hy
      obtain ⟨Z, hZ⟩ := hz
      use Y + Z
      apply LipschitzWith.sub hY hZ

  have sinf_le_sum := csInf_le (by simp) sum_norm_mem
  simp [LipschitzSemiNorm] at sinf_le_sum
  conv at sinf_le_sum =>
    pattern x - z
    equals (x - y) + (y - z) =>
      simp
  exact sinf_le_sum


lemma lipschitzH_norm_triangle (x y z: LipschitzH): LipschitzSemiNorm (x - z) ≤ LipschitzSemiNorm (x - y) + LipschitzSemiNorm (y - z) := by
  apply lipschitz_norm_triangle x y z x.lipschitz y.lipschitz z.lipschitz



--section lipschitz_norm
noncomputable local instance LipschitzH_seminorm: SeminormedAddCommGroup (LipschitzH) where
  norm := fun v => LipschitzSemiNorm v
  dist_self := by
    intro v
    simp [LipschitzSemiNorm]
    exact lipschiz_norm_zero
  dist_comm := by
    intro x y
    simp [LipschitzSemiNorm]
    conv =>
      lhs
      pattern ⇑(x - y)
      equals -⇑((y - x)) =>
        ext a
        simp


    simp_rw [lipschitzWith_neg_iff]
  dist_triangle := by
    intro x y z
    simp
    apply lipschitzH_norm_triangle

-- Note that we only implement SeminormedAddCommGroup for LipschitzH, so this is only
-- really a seminormed space. The quotient space W := LipschitzH ⧸ ConstF
-- is an actual normed space.
noncomputable local instance LipschitzH_normed: NormedSpace ℂ (LipschitzH) where
  norm_smul_le := by
    intro c f
    simp [HSMul.hSMul, SMul.smul]
    simp [norm]
    conv =>
      lhs
      simp [LipschitzSemiNorm]
    norm_cast
    apply csInf_le (by
      simp [BddBelow]
      apply Set.nonempty_of_mem (x := 0)
      rw [mem_lowerBounds]
      simp
    )
    simp
    let K := LipschitzSemiNorm f
    have hK := lipschitz_attains_norm f (f.lipschitz)
    use ‖ (c * K) ‖₊
    simp
    have comp_mul_const := LipschitzWith.comp (Kf := ‖c‖₊) (Kg := K) (f := fun x => c • x) (g := f.toFun) (by apply lipschitzWith_smul) hK
    simp at comp_mul_const
    conv =>
      lhs
      arg 2
      simp [DFunLike.coe]
      equals (fun x ↦ c • x) ∘ f.toFun => rfl


    refine ⟨comp_mul_const, ?_⟩
    simp [norm]
    left
    simp [K]


#synth TopologicalSpace (LipschitzH)
--def myInst := Submodule.Quotient.normedAddCommGroup (S := ConstF)

lemma lipschitz_norm_const (z: ℂ): LipschitzSemiNorm (ConstLipschitzH z) = 0 := by
  unfold LipschitzSemiNorm
  have zero_mem: 0 ∈ { k: NNReal | LipschitzWith k (ConstLipschitzH z).toFun } := by
    simp
    simp [ConstLipschitzH]
    simp [LipschitzWith]
  have my_le := csInf_le (by simp) zero_mem
  exact nonpos_iff_eq_zero.mp my_le


lemma constf_eq_null: (ConstF : Set (LipschitzH)) = nullAddSubgroup (LipschitzH) := by
  unfold ConstF
  unfold nullAddSubgroup
  ext f
  simp
  refine ⟨?_, ?_⟩
  .
    intro hf
    obtain ⟨z, hz⟩ := hf
    rw [← hz]
    simp [norm]
    apply lipschitz_norm_const
  .
    intro hf
    simp [norm, LipschitzSemiNorm] at hf
    have lipschitz_zero := lipschitz_attains_norm f (f.lipschitz)
    simp [LipschitzSemiNorm] at lipschitz_zero
    rw [hf] at lipschitz_zero
    simp [LipschitzWith] at lipschitz_zero
    use (f.toFun 1)
    simp [ConstLipschitzH]
    ext a
    simp
    apply lipschitz_zero

instance const_isClosed: IsClosed (ConstF : Set (LipschitzH)) := by
  rw [constf_eq_null]
  exact isClosed_nullAddSubgroup


#synth NormedSpace ℂ (W )
#synth NormedAddCommGroup (W )

#synth TopologicalSpace (W)


set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 9000000

-- The space 'GL(W)' of invertible continuous linear functions from W to W
abbrev GL_W := (W →L[ℂ] W)ˣ

--#synth LieGroup (modelWithCornersSelf ℂ ((W →L[ℂ] W))) 1 (GL_W)
--#synth TopologicalSpace ((W →L[ℂ] W))
--#synth TopologicalSpace ((W →L[ℂ] W))ˣ


#synth NormedRing (((W →L[ℂ] W)))

#synth NormedAddCommGroup (((W →L[ℂ] W)))

lemma opnorm_continuous: Continuous fun (f: (W →L[ℂ] W)) => ‖f‖ := by
  apply continuous_norm

#synth FiniteDimensional ℂ (((W →L[ℂ] W)))

-- Homeomorph.isCompact_preimage

instance proper_linear_w: ProperSpace (((W →L[ℂ] W))) := FiniteDimensional.proper_rclike ℂ (((W →L[ℂ] W)))


--#synth NormedSpace ℂ (GL_W)
--#synth MetricSpace (GL_W)


#synth FiniteDimensional ℂ (LipschitzH)
#synth TopologicalSpace (LipschitzH)
#synth BorelSpace (((W →L[ℂ] W)))

#synth ProperSpace (((W →L[ℂ] W)))



def GRep: Representation ℂ G (LipschitzH)  := {
  toFun := fun g => {
    toFun := gAct g
    map_add' := by
      intro f h
      ext a
      simp [gAct]
    map_smul' := by
      intro c f
      ext a
      simp [gAct]
  }
  map_one' := by
    ext f a
    simp [gAct]
  map_mul' := by
    intro g h
    ext f a
    simp [gAct]
    simp [mul_assoc]
}


--attribute [-instance] QuotientModule.Quotient.topologicalSpace

-- We start with a map from G into the space of (not necessarily invertible) linear maps from W to W
def GRepW_non_invertible: Representation ℂ G (W) := Representation.quotient (GRep) ConstF (by
  intro g
  intro f hf
  simp
  simp [ConstF]
  simp [ConstF] at hf
  obtain ⟨K, hK⟩ := hf
  use K
  ext a
  simp [GRep]
  rw [← hK]
  rw [gAct_const]
)

-- We then build a map from G into the group of invertible linear maps from W to W
noncomputable def GRepW_base := Representation.asGroupHom GRepW_non_invertible


-- GRep just translates functions by g⁻¹, so it preserves the Lipschitz operator norm
lemma GRep_preserves_norm (g: G) (f: LipschitzH): ‖(GRep g) f‖ = ‖f‖ := by
  simp [GRep]
  simp [norm]
  nth_rw 1 [LipschitzSemiNorm]
  rw [gAct]
  simp [DFunLike.coe]
  conv =>
    lhs
    arg 1
    arg 1
    intro k
    equals (LipschitzWith k (f.toFun ∘ (fun y => (y * g)))) =>
      rfl

  have comp := LipschitzWith.comp (f := f.toFun) (g := fun y => (y * g)) (Kf := (LipschitzSemiNorm ⇑f)) (Kg := 1) ?_ ?_
  rotate_left 1
  . apply lipschitz_attains_norm
    exact f.lipschitz
  .
    simp [LipschitzWith]

  have norm_mem: (LipschitzSemiNorm f) ∈ { k: NNReal | LipschitzWith k (f.toFun ∘ (fun y => (y * g))) } := by
    simp
    simp at comp
    exact comp


  apply le_antisymm
  .
    apply csInf_le (by
      simp [BddBelow]
      apply Set.nonempty_of_mem (x := 0)
      rw [mem_lowerBounds]
      simp
    ) norm_mem
  .
    apply le_csInf
    .
      apply Set.nonempty_of_mem (x := (LipschitzSemiNorm ⇑f)) norm_mem
    . intro b hb
      simp at hb
      simp [LipschitzSemiNorm]
      apply csInf_le
      .
        simp [BddBelow]
        apply Set.nonempty_of_mem (x := 0)
        rw [mem_lowerBounds]
        simp
      . simp
        simp [LipschitzWith] at hb
        simp [LipschitzWith]
        intro x y
        specialize hb (x * g⁻¹) (y * g⁻¹)
        simp at hb
        grw [hb]




-- Takes in an invertible linear map from W to W, and produces a *continuous* linear map from W to W
set_option trace.profiler true in
noncomputable def GRepW: (W →ₗ[ℂ] W)ˣ →* (W →L[ℂ] W)ˣ := {
  toFun := fun f => {
    val := LinearMap.toContinuousLinearMap f.val
    inv := LinearMap.toContinuousLinearMap f.inv
    val_inv := by
      have old_inv := f.val_inv
      ext a
      apply_fun (fun f => f a) at old_inv
      simp
      simp only [Units.inv_eq_val_inv, Module.End.one_apply] at old_inv
      apply old_inv
    inv_val := by
      have old_inv := f.inv_val
      ext a
      apply_fun (fun f => f a) at old_inv
      simp
      simp only [Units.inv_eq_val_inv, Module.End.one_apply] at old_inv
      apply old_inv
  }
  map_one' := by
    ext a
    simp
  map_mul' := by
    intro f g
    ext a
    simp
}

-- noncomputable def GRepW_Multiplicative: (W →ₗ[ℂ] W) →* (Multiplicative (GL_W)) := {
--   toFun := fun f => Multiplicative.ofAdd (GRepW f)
--   map_one' := by
--     simp
--   map_mul' := by
--     intro f g
--     ext
--     simp [DFunLike.coe]
--     simp [ContinuousLinearMap.toFun_eq_coe]
--     simp [ContinuousLinearMap.mul_apply]
-- }

#synth Group (GL_W)

lemma quotient_norm_eq_norm (f: LipschitzH): ‖(Submodule.Quotient.mk f : W)‖ = ‖f‖ := by
  have foo := QuotientAddGroup.norm_mk (S := ConstF.toAddSubgroup) f
  conv =>
    lhs
    equals ‖(QuotientAddGroup.mk f : (LipschitzH ⧸ ConstF.toAddSubgroup))‖ =>
      rfl
  rw [QuotientAddGroup.norm_mk]
  simp [Metric.infDist]
  dsimp [EMetric.infEdist]

  conv =>
    lhs
    arg 1
    arg 1
    intro y
    arg 1
    intro hy
    equals (‖f‖₊ : ENNReal) =>
      simp [ConstF] at hy
      obtain ⟨a, ha⟩ := hy
      simp [edist, PseudoMetricSpace.edist]
      simp [LipschitzSemiNorm]
      simp [LipschitzWith]
      simp_rw [← ha]
      simp [ConstLipschitzH]
      rfl

  conv =>
    arg 1
    arg 1
    arg 1
    intro y
    arg 1
    intro hy

  rw [biInf_const ?_]
  . simp
  . exact Submodule.nonempty ConstF

#synth NormedRing (W →L[ℂ] W)
#synth TopologicalSpace (W →L[ℂ] W)ˣ


lemma GLW_preseves_norm (g: G) (w: W): ‖(GRepW (GRepW_base g)).val w‖ = ‖w‖ := by
  have exists_v: ∃ v, Submodule.Quotient.mk v = w := by
    apply Quotient.exists_rep
  obtain ⟨v, hv⟩ := exists_v
  simp [GRepW, GRepW_base, GRepW_non_invertible]
  nth_rw 1 [← hv]
  rw [Representation.asGroupHom_apply]
  simp only [Representation.quotient_apply, Submodule.mapQ_apply]
  --rw [Submodule.mapQ_apply]
  rw [quotient_norm_eq_norm]
  rw [GRep_preserves_norm]
  rw [← hv]
  rw [quotient_norm_eq_norm]


lemma GRepW_norm_le (g: G): ‖(GRepW (GRepW_base g)).val‖ ≤ 1 := by
  rw [ContinuousLinearMap.opNorm_le_iff]
  . simp [GLW_preseves_norm]
  . simp
  -- apply ContinuousLinearMap.opNorm_eq_of_bounds (by simp)
  -- . simp [GLW_preseves_norm]
  -- . intro n hn
  --   simp [GLW_preseves_norm]
  --   intro x

  --   by_contra!
  --   unfold W at x
  --   specialize x (Submodule.Quotient.mk (ConstLipschitzH 1))
  --   simp at hn
  --   by_cases n_eq_zero: n = 0
  --   .
  --     simp [n_eq_zero] at x

  --   have mul_lt := mul_lt_of_lt_one_left (a := ‖((Submodule.Quotient.mk (ConstLipschitzH 1)) : W)‖) (b := n) (by linarith)
  -- rw [ContinuousLinearMap.norm_def]
  -- simp [GLW_preseves_norm]


--#synth CompleteSpace (W)

    --infer_instance

lemma continuous_GRepW : Continuous (fun g => GRepW (GRepW_base g)) := by
  fun_prop

set_option synthInstance.maxHeartbeats 500000

lemma continous_of_map (v: W): Continuous (fun (r: (W →L[ℂ] W)ˣ) => r.val v) := by
  apply Continuous.comp (g := (fun r => r v)) (f := (fun (r : (W →L[ℂ] W)ˣ) => r.val))
  -- TODO - how does this work???
  . exact Continuous.clm_apply continuous_id' continuous_const
  . apply Units.continuous_val




-- The image of G under our representation: ρ(G) in the Vikman paper
--noncomputable def rho_g := ((GRepW).restrict ((GRepW_base).range)).range

noncomputable def rho_g := (GRepW_base).range

--noncomputable instance GL_W_TopologicalSpace: TopologicalSpace (GL_W) := TopologicalSpace.induced Units.val (by infer_instance)
--noncomputable instance GL_W_PseudoMetricSpace: PseudoMetricSpace (GL_W) := Topology.IsInducing.comapPseudoMetricSpace (f := Units.val) (by apply Topology.IsInducing.induced)


--def rho_g_closure := _root_.closure (rho_g).carrier

-- instance GL_W_proper: ProperSpace (GL_W) := by
--   unfold GL_W
--   apply FiniteDimensional.proper

def isembedding_units_val := Units.isEmbedding_val_mk' (M := (W →L[ℂ] W)) (f := ContinuousLinearMap.inverse) (by
  intro x hx
  have foo := ContDiffAt.continuousAt (ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse (e := x) (n := 0) (by
    simp at hx
    obtain ⟨u, hu⟩ := hx
    apply ContinuousLinearMap.IsInvertible.of_inverse (g := u.inv)
    .
      simp
      have mul_inv := u.val_inv
      dsimp [HMul.hMul, Mul.mul] at mul_inv
      rw [hu] at mul_inv
      exact mul_inv
    . simp
      have inv_val := u.inv_val
      dsimp [HMul.hMul, Mul.mul] at inv_val
      rw [hu] at inv_val
      exact inv_val
  ))
  apply ContinuousAt.continuousWithinAt
  exact foo
  -- ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse
) (by
  intro u
  have mul_inv := u.val_inv
  dsimp [HMul.hMul, Mul.mul] at mul_inv
  apply ContinuousLinearMap.inverse_eq
  . exact u.val_inv
  . exact u.inv_val
)

#synth NormedSpace ℂ (W →L[ℂ] W)
#synth MetricSpace (W →L[ℂ] W)




-- All norms are equivalent on finite-dimensional spaces:
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Normed/Module/FiniteDimension.html

-- Section 3.3 in Vikmanm, "Construction of a representation"
-- This is a combination of Cartan's Theorem and Theorem 3.6, giving us the conclusion that
-- ρ(G) contains an abelian subgroup of finite index

--#synth MeasurableSpace (W →L[ℂ] W)ˣ
--#synth TopologicalSpace (W →L[ℂ] W)ˣ
--#synth BorelSpace (W →L[ℂ] W)




--borelize (W →L[ℂ] W)ˣ

--#synth BorelSpace (Units.val '' (rho_g).carrier)

#synth ContinuousMul (W →L[ℂ] W)


#synth NormedAddCommGroup (W)

#synth FiniteDimensional ℂ (W)

--#synth CompleteSpace (W)

--#synth IsBoundedSMul ℂ (LipschitzH)



--end lipschitz_norm



-- WRONG?: We want the topology to come from our metric space 'GL_W_psuedoMetric', not from the units

-- We actualy want the topology to be the induced topology from the space of (not necessarily invertible) linear maps from W to W
--attribute [-instance] Units.instTopologicalSpaceUnits

--instance Units_subtype_Topology {T: Type*} [Monoid T] [TopologicalSpace T]: TopologicalSpace (T)ˣ := TopologicalSpace.induced Units.val (by infer_instance)


#synth TopologicalSpace (W)


--attribute [-instance] QuotientModule.Quotient.topologicalSpace
def FreshTopology (V: Type*) := V
instance (V: Type*) [base_group: Group V]: Group (FreshTopology V) := base_group
instance (V: Type*) [base_comm: AddCommGroup V]: AddCommGroup (FreshTopology V) := base_comm
instance (V: Type*) [AddCommGroup V] [base_module: Module ℂ V]: Module ℂ (FreshTopology V) := base_module
instance (V: Type*) [AddCommGroup V] [Module ℂ V]  [base_finite: FiniteDimensional ℂ V]: FiniteDimensional ℂ (FreshTopology V) := base_finite
-- instance (V: Type*) [base_topology: TopologicalSpace V]: TopologicalSpace (FreshTopology V) := base_topology
-- instance (V: Type*) [TopologicalSpace V] [AddCommGroup V] [base_add: IsTopologicalAddGroup V]: IsTopologicalAddGroup (FreshTopology V) := base_add
-- #synth Group (FreshTopology (W →L[ℂ] W)ˣ)

--instance proper_fresh_topology [TopologicalSpace (FreshTopology (W))]: ProperSpace ((((FreshTopology (W)) →L[ℂ] (FreshTopology (W))))) := FiniteDimensional.proper_rclike ℂ (((W →L[ℂ] W)))

#synth CStarAlgebra ((ℂ →L[ℂ] ℂ))

#synth AddCommMonoid (W)

instance T2_W: T2Space (W) := TopologicalSpace.t2Space_of_metrizableSpace

#synth T2Space (W)


#synth TopologicalSpace (W →L[ℂ] W)
#synth FiniteDimensional ℂ (W →L[ℂ] W)

noncomputable def G_SPolyData {d: ℕ} (h_poly: HasPolynomialGrowthD hGS.S d): SPolyData (T := G) ⊤ := {
  S := Subgroup.topEquiv.symm.toMonoidHom '' hGS.S
  S_finite := by
    apply Set.Finite.image
    simp
  S_one := by
    simp
    apply hGS.one_mem
  S_inv := by
    rw [← Set.image_inv]
    nth_rw 1 [S_eq_Sinv]
    simp
  S_generates := by
    rw [← MonoidHom.map_closure]
    have foo := hGS.generates
    simp at foo
    simp [foo]

  S_poly_const := h_poly.choose
  S_poly_const_pos := by
    by_contra!
    have foo := h_poly.choose_spec
    simp [← this] at foo
    specialize foo 1 (by simp)
    simp at foo
    have S_nonempty := hGS.hS
    simp at S_nonempty
    grind
  S_poly_deg := d
  S_poly := by
    have foo := h_poly.choose_spec
    intro r hr
    rw [Set.Finite.toFinset_image]
    rw [← Finset.image_pow]
    grw [Finset.card_image_le]
    .
      specialize foo r hr
      simpa using foo
    . simp
}


-- Theorem 3.8 in Vikman
set_option maxHeartbeats 500000 in
lemma theorem_3_8 {V: Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (H: Subgroup (V →L[ℂ] V)ˣ) [DecidableEq H] (h_compact: CompactSpace H) (G: Subgroup H) (G_fg: G.FG) (S_data: SPolyData G): ∃ A: Subgroup G, IsMulCommutative A ∧ A.FiniteIndex := by
  obtain ⟨H', ⟨H_equiv_H'⟩⟩ := new_weyl_unitarian_trick (V := V) (H := H)
  --let first := Subgroup.map H'.subtype.restrict_range (Subgroup.map H_equiv_H'.symm.toMonoidHom G)
  let G' := Subgroup.map H'.subtype (Subgroup.map H_equiv_H'.symm.toMonoidHom G)
  let my_hom := MonoidHom.ofInjective (f := H'.subtype) (by exact subtype_injective H')
  let other := Subgroup.map my_hom.toMonoidHom (Subgroup.map H_equiv_H'.symm.toMonoidHom G)
  --let other' := other.toMonoidHom.restrict

  let reverse := Subgroup.comap H'.subtype


  let G'_to_G: G' →* G := {
    toFun := fun g => (by
      use ⟨H_equiv_H' (my_hom.symm ⟨g, by (
        have g_prop := g.property
        simp only [G'] at g_prop
        rw [Subgroup.mem_map] at g_prop
        obtain ⟨x, x_mem, g_eq⟩ := g_prop
        rw [← g_eq]
        simp
      )⟩), by (
        simp [my_hom]
      )⟩
      simp [my_hom]
      have g_prop := g.property
      simp only [G'] at g_prop
      rw [Subgroup.mem_map] at g_prop
      obtain ⟨x, x_mem, g_eq⟩ := g_prop
      simp_rw [← g_eq]
      rw [Subgroup.mem_map] at x_mem
      obtain ⟨y, y_mem, x_eq⟩ := x_mem
      simp_rw [← x_eq]
      simp [MonoidHom.ofInjective, MulEquiv.ofBijective, Equiv.ofBijective, Function.surjInv]
      exact y_mem
    )
    map_one' := by simp
    map_mul' := by
      intro a b
      conv =>
        enter [1, 1, 1, 1, 2, 2]
        equals ⟨a.val, (by
          have a_prop := a.property
          simp only [G'] at a_prop
          rw [Subgroup.mem_map] at a_prop
          obtain ⟨x, x_mem, a_eq⟩ := a_prop
          rw [← a_eq]
          simp
        )⟩ * ⟨b.val, (by
          have b_prop := b.property
          simp only [G'] at b_prop
          rw [Subgroup.mem_map] at b_prop
          obtain ⟨y, y_mem, b_eq⟩ := b_prop
          rw [← b_eq]
          simp
        )⟩ =>
          rfl

      simp_rw [MulEquiv.map_mul]
      rfl
  }

  have G'_fg: G'.FG := by
    simp [G']
    apply group_fg_map
    apply group_fg_map
    exact G_fg

  by_cases dim_le_one: Module.finrank ℂ (V) ≤ 1
  .
    use ⊤
    refine ⟨?_, ?_⟩
    .

      have map_dim := Module.finrank_linearMap ℂ ℂ V V
      -- TODO - is there an easier way to prove this?
      have map_dim_le_one: Module.finrank ℂ (V →ₗ[ℂ] V) ≤ 1 := by
        rw [map_dim]
        by_cases dim_eq_zero: Module.finrank ℂ (V) = 0
        . simp [dim_eq_zero]
        . simp at dim_eq_zero
          have dim_eq_one: Module.finrank ℂ (V) = 1 := by omega
          simp [dim_eq_one]

      rw [finrank_le_one_iff] at map_dim_le_one
      obtain ⟨v, v_span⟩ := map_dim_le_one
      refine { is_comm := ?_ }
      refine { comm := ?_ }
      intro x y
      ext a
      simp
      obtain ⟨p, hx⟩ := v_span x.val.val.val
      obtain ⟨q, hy⟩ := v_span y.val.val.val

      -- TODO - upstream to mathlib
      have clm_apply (f: V →L[ℂ] V) (v: V): f v = f.toLinearMap v := rfl
      rw [clm_apply]
      rw [clm_apply]
      rw [clm_apply]
      rw [clm_apply]

      rw [← hx, ← hy]
      simp
      rw [smul_comm]
    . infer_instance
  .
    have dim_ge_two: 2 ≤ Module.finrank ℂ (V) := by omega

    let new_S_data := map_S_data G (f := H'.subtype.comp (H_equiv_H'.symm.toMonoidHom)) S_data
    obtain ⟨N, N_comm, N_finite_index⟩ := compact_lie_virtually_abelian (Module.finrank ℂ V) (by omega) G' G'_fg (by
      unfold G'
      rw [Subgroup.map_map]
      exact new_S_data
    )

    let new_N := N
    simp [G'] at new_N
    --let new_N' := H'.subtype


    let new_N' := Subgroup.map G'.subtype N

    let new_N' := Subgroup.map G'_to_G N
    use new_N'
    refine ⟨?_, ?_⟩
    .
      simp [new_N']
      apply Subgroup.map_isMulCommutative
    .
      simp [new_N']
      rw [Subgroup.finiteIndex_iff]
      rw [Subgroup.index_map_of_injective]
      . simp
        refine ⟨?_, ?_⟩
        . exact N_finite_index.index_ne_zero
        . conv =>
            arg 1
            arg 1
            arg 1
            equals ⊤ =>
              rw [MonoidHom.range_eq_top]
              simp [G'_to_G]
              intro a
              simp
              use H'.subtype (H_equiv_H'.symm a)
              simp [my_hom]
              use ?_
              . simp [MonoidHom.ofInjective, MulEquiv.ofBijective, Equiv.ofBijective, Function.surjInv]
              . simp [G']
                use a.val
                use ?_
                . simp
                . simp

          simp
      .
        simp [G'_to_G]
        intro a b hab
        simpa using hab

instance rho_g_FG: Group.FG (rho_g) := by
  have fg_grep: Group.FG ↥(GRepW_base).range := by
    apply Group.fg_range
  unfold rho_g
  apply Group.fg_range

-- TODO - deduplicate with 'map_S_Data'
def map_range_S_data {G H: Type*} [Group G] [Group H] [DecidableEq G] [DecidableEq H] {f: G →* H} (S_data: SPolyData (T := G) ⊤): SPolyData f.range := {
  S := (f.rangeRestrict.comp (Subgroup.topEquiv.toMonoidHom)) '' S_data.S
  S_finite := by
    apply Set.Finite.image
    apply S_data.S_finite
  S_one := by
    simp only [Set.mem_image]
    use 1
    simp
    apply S_data.S_one
  S_inv := by
    rw [← Set.image_inv]
    rw [← S_data.S_inv]
  S_generates := by
    rw [← MonoidHom.map_closure]
    rw [S_data.S_generates]
    rw [Subgroup.map_top_of_surjective]
    simp
    apply MonoidHom.rangeRestrict_surjective
  S_poly_const := S_data.S_poly_const
  S_poly_const_pos := S_data.S_poly_const_pos
  S_poly_deg := S_data.S_poly_deg
  S_poly := by
    intro r hr
    rw [Set.Finite.toFinset_image]
    rw [← Finset.image_pow]
    grw [Finset.card_image_le]
    .
      apply S_data.S_poly r hr
    . exact S_data.S_finite
}

def map_equiv_S_data {A B: Type*} [Group A] [Group B] [DecidableEq A] [DecidableEq B] {G: Subgroup A} {H: Subgroup B} (f: G ≃* H) (S_data: SPolyData G): SPolyData H := {
  S := f.toMonoidHom '' S_data.S
  S_finite := by
    apply Set.Finite.image
    apply S_data.S_finite
  S_one := by
    simp only [Set.mem_image]
    use 1
    simp
    apply S_data.S_one
  S_inv := by
    rw [← Set.image_inv]
    rw [← S_data.S_inv]
  S_generates := by
    rw [← MonoidHom.map_closure]
    rw [S_data.S_generates]
    rw [Subgroup.map_top_of_surjective]
    simp
    exact MulEquiv.surjective f
  S_poly_const := S_data.S_poly_const
  S_poly_const_pos := S_data.S_poly_const_pos
  S_poly_deg := S_data.S_poly_deg
  S_poly := by
    intro r hr
    rw [Set.Finite.toFinset_image]
    rw [← Finset.image_pow]
    grw [Finset.card_image_le]
    .
      apply S_data.S_poly r hr
    . exact S_data.S_finite
}


--#synth NormedAddCommGroup (W)
open scoped ComplexInnerProductSpace in
set_option maxHeartbeats 900000 in
set_option synthInstance.maxHeartbeats 600000 in
--set_option trace.Meta.synthInstance true in
lemma rho_g_contains_abelian {d: ℕ} (hd: HasPolynomialGrowthD S d) : ∃ M: Subgroup ((rho_g)), IsMulCommutative M ∧ M.FiniteIndex := by
  classical
  let my_map := Subgroup.subtype (rho_g)
  have W_equiv: (W) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin <| Module.finrank ℂ W) := LinearEquiv.ofFinrankEq _ _ finrank_euclideanSpace_fin.symm



  unfold GL_W at my_map
  -- TODO - is there a simpler way to get an arbitrary inner product space?
  let inner_prod_core: InnerProductSpace.Core ℂ (FreshTopology (W)) := {
    inner := fun v w => ⟪W_equiv v, W_equiv w⟫,
    conj_inner_symm := by simp,
    re_inner_nonneg := by
      exact fun x ↦ inner_self_nonneg
    add_left := by simp
    smul_left := by
      intro x y r
      simp
      rw [mul_comm]
    definite := by simp
  }

  let temp_inner := InnerProductSpace.ofCore inner_prod_core.toCore
  let add_comm := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := (FreshTopology (W)))

  let normed_space := InnerProductSpace.Core.toNormedSpace (𝕜 := ℂ) (F := (FreshTopology (W)))

  have proper_space: ProperSpace (FreshTopology (W)) := FiniteDimensional.proper_rclike ℂ _

  have fresh_t2: T2Space (FreshTopology (W)) := TopologicalSpace.t2Space_of_metrizableSpace


  let plain_linear_to_clm: (((W)) →ₗ[ℂ] ((W)))ˣ →* (((W)) →L[ℂ] ((W)))ˣ := {
    toFun := fun f => {
      val := LinearMap.toContinuousLinearMap f.val
      inv := LinearMap.toContinuousLinearMap f.inv
      val_inv := by
        have old_inv := f.val_inv
        ext a
        apply_fun (fun f => f a) at old_inv
        simp only [Units.inv_eq_val_inv, Module.End.one_apply] at old_inv
        apply old_inv
      inv_val := by
        have old_inv := f.inv_val
        ext a
        apply_fun (fun f => f a) at old_inv
        simp only [Units.inv_eq_val_inv, Module.End.one_apply] at old_inv
        apply old_inv
    }
    -- TODO - why is a normal `simp` so slow here?
    map_one' := by
      ext a
      simp only []
      rfl
    map_mul' := by
      intro f g
      ext a
      simp only []
      rfl
  }

  let linear_to_clm: ((FreshTopology (W)) →ₗ[ℂ] (FreshTopology (W)))ˣ →* ((FreshTopology (W)) →L[ℂ] (FreshTopology (W)))ˣ := {
    toFun := fun f => {
      val := LinearMap.toContinuousLinearMap f.val
      inv := LinearMap.toContinuousLinearMap f.inv
      val_inv := by
        have old_inv := f.val_inv
        ext a
        apply_fun (fun f => f a) at old_inv
        simp only [Units.inv_eq_val_inv, Module.End.one_apply] at old_inv
        apply old_inv
      inv_val := by
        have old_inv := f.inv_val
        ext a
        apply_fun (fun f => f a) at old_inv
        simp only [Units.inv_eq_val_inv, Module.End.one_apply] at old_inv
        apply old_inv
    }
    -- TODO - why is a normal `simp` so slow here?
    map_one' := by
      ext a
      simp only []
      rfl
    map_mul' := by
      intro f g
      ext a
      simp only []
      rfl
  }


  have plain_linear_to_clm_preserves_norm (g: G) (w: (W)): ‖(plain_linear_to_clm (GRepW_base g)).val w‖ = ‖w‖ := by
    simp [plain_linear_to_clm]
    have exists_v: ∃ v, Submodule.Quotient.mk v = w := by
      apply Quotient.exists_rep
    obtain ⟨v, hv⟩ := exists_v
    simp [GRepW, GRepW_base, GRepW_non_invertible]
    nth_rw 1 [← hv]
    rw [Representation.asGroupHom_apply]
    simp only [Representation.quotient_apply, Submodule.mapQ_apply]

    rw [quotient_norm_eq_norm]
    rw [GRep_preserves_norm]
    rw [← hv]
    rw [quotient_norm_eq_norm]


  let my_range := (linear_to_clm.comp GRepW_base).range

  have fresh_complete: CompleteSpace (FreshTopology (W)) := by apply complete_of_proper (α := FreshTopology (W))

  have locally_compact_map: LocallyCompactSpace ((FreshTopology (W)) →L[ℂ] (FreshTopology (W))) := locallyCompact_of_proper
  have units_locally:  LocallyCompactSpace ((FreshTopology (W)) →L[ℂ] (FreshTopology (W)))ˣ := by
    infer_instance



  -- TODO - generalize to LinearMap/ContinuousLinearMap
  have units_val_embedding: Topology.IsEmbedding (Units.val (α := ((FreshTopology (W)) →L[ℂ] (FreshTopology (W))))) := by
    apply Units.isEmbedding_val_mk' (f := fun g => g.inverse)
    . intro a ha
      apply (ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse (n := 1) ?_).continuousAt.continuousWithinAt
      simp at ha
      obtain ⟨b, hb⟩ := ha
      use ContinuousLinearEquiv.ofUnit b
      rw [← hb]
      rfl
    . intro u
      have u_unit: IsUnit u.val := by
        use u
      apply ContinuousLinearMap.inverse_eq
      .
        have u_val_inv := u.val_inv
        rw [ContinuousLinearMap.mul_def] at u_val_inv
        -- TODO - avoid the unfold somehow
        unfold Inv.inv
        unfold Units.instInv
        simp only []
        rw [u_val_inv]
        rfl
      .
        unfold Inv.inv
        unfold Units.instInv
        simp only []
        have u_inv_val := u.inv_val
        rw [ContinuousLinearMap.mul_def] at u_inv_val
        rw [u_inv_val]
        rfl


  let my_new_range := ((GRepW).comp GRepW_base).range
  unfold rho_g


  have continuous_mul: ContinuousMul ((W) →L[ℂ] (W)) := by
    infer_instance

  have is_topological: IsTopologicalGroup ((W) →L[ℂ] (W))ˣ := by
    infer_instance

  let plain_units_metric: MetricSpace (((W)) →L[ℂ] ((W)))ˣ := by
    apply Topology.IsEmbedding.comapMetricSpace (f := Units.val)
    exact isembedding_units_val

  let units_metric: MetricSpace ((FreshTopology (W)) →L[ℂ] (FreshTopology (W)))ˣ := by
    apply Topology.IsEmbedding.comapMetricSpace (f := Units.val)
    apply units_val_embedding



  have fresh_equiv: W ≃L[ℂ] FreshTopology (W) := ContinuousLinearEquiv.ofFinrankEq (rfl)

  let to_fresh (f: (W) ≃ₗ[ℂ] (W)): (FreshTopology (W)) ≃ₗ[ℂ] (FreshTopology (W)) := f
  let new_map_entry (f: (W →L[ℂ] W)ˣ): ((FreshTopology W) →L[ℂ] (FreshTopology W))ˣ := {
    val := ContinuousLinearEquiv.arrowCongr fresh_equiv fresh_equiv f.val,
    inv := ContinuousLinearEquiv.arrowCongr fresh_equiv fresh_equiv f.inv
    val_inv := by
      ext a
      simp
      conv =>
        arg 1
        equals (fresh_equiv ((f.val * f.inv) (fresh_equiv.symm a))) =>
          rfl
      simp
    inv_val := by
      ext a
      simp
      conv =>
        arg 1
        equals (fresh_equiv ((f.inv * f.val) (fresh_equiv.symm a))) =>
          rfl
      simp
  }

  let new_map_entry_inv (f: ((FreshTopology W) →L[ℂ] (FreshTopology W))ˣ ): (W →L[ℂ] W)ˣ  := {
    val := (ContinuousLinearEquiv.arrowCongr fresh_equiv fresh_equiv).symm f.val,
    inv := (ContinuousLinearEquiv.arrowCongr fresh_equiv fresh_equiv).symm f.inv
    val_inv := by
      ext a
      simp
      conv =>
        arg 1
        equals (fresh_equiv.symm ((f.val * f.inv) (fresh_equiv a))) =>
          rfl
      simp
    inv_val := by
      ext a
      simp
      conv =>
        arg 1
        equals (fresh_equiv.symm ((f.inv * f.val) (fresh_equiv a))) =>
          rfl
      simp
  }

  let to_continuous_hom: (FreshTopology (W) →ₗ[ℂ] FreshTopology (W)) →* (FreshTopology (W) →L[ℂ] FreshTopology (W)) := {
    toFun := fun f => f.toContinuousLinearMap,
    map_one' := by
      ext a
      simp
    map_mul' := by
      intro a b
      rfl
    }

  let new_map_hom: (W →L[ℂ] W)ˣ ≃* ((FreshTopology W) →L[ℂ] (FreshTopology W))ˣ := {
    toFun := new_map_entry,
    invFun := new_map_entry_inv,
    left_inv := by
      simp [Function.LeftInverse]
      intro x
      ext a
      simp [new_map_entry, new_map_entry_inv]
    right_inv := by
      simp [Function.RightInverse]
      intro x
      ext a
      simp [new_map_entry, new_map_entry_inv]
    map_mul' := by
      intro f g
      simp [new_map_entry]
      ext a
      simp
  }


  let mapped_group := Subgroup.map new_map_hom.toMonoidHom my_new_range.topologicalClosure

  have my_new_range_compact: CompactSpace my_new_range.topologicalClosure := by
    refine { isCompact_univ := ?_ }
    rw [Subtype.isCompact_iff]
    rw [Topology.IsEmbedding.isCompact_iff (f := Units.val) ?_]
    . rw [Metric.isCompact_iff_isClosed_bounded]
      refine ⟨?_, ?_⟩
      . apply IsSeqClosed.isClosed
        by_contra!
        simp [IsSeqClosed] at this
        obtain ⟨seq, seq_in, ⟨lim_seq, seq_tendsto_lim_seq, lim_seq_not_mem⟩⟩ := this

        by_cases lim_seq_invertible: IsUnit lim_seq.toLinearMap
        .
          -- If the limit (in the space of linear maps) is invertible, then the limit will also exist in the space
          -- of units, which will then imply that the limit exists in the space of linear maps.
          -- TODO - this probably can be a direct proof, rather than by contradiction
          obtain ⟨u, hu⟩ := lim_seq_invertible
          have closure_closed := Subgroup.isClosed_topologicalClosure my_new_range
          apply IsClosed.isSeqClosed at closure_closed
          dsimp [IsSeqClosed] at closure_closed

          have seq_units: ∀ n: ℕ, IsUnit (seq n) := by
            intro n
            obtain ⟨x, x_mem, seq_eq_x⟩ := (seq_in n)
            rw [← seq_eq_x]
            apply Units.isUnit

          have lim_units := closure_closed (x := fun n => (seq_units n).unit) (p := plain_linear_to_clm u) ?_ ?_
          .
            specialize lim_seq_not_mem (plain_linear_to_clm u) lim_units
            conv at lim_seq_not_mem =>
              arg 1
              lhs
              equals u.val.toContinuousLinearMap =>
                rfl
            rw [hu] at lim_seq_not_mem
            conv at lim_seq_not_mem =>
              arg 1
              lhs
              equals lim_seq =>
                rfl
            simp at lim_seq_not_mem
          . intro n
            simp
            have seq_n := seq_in n
            obtain ⟨x, x_mem, seq_eq_x⟩ := seq_n
            simp_rw [← seq_eq_x]
            simpa using x_mem
          .
            rw [Topology.IsEmbedding.tendsto_nhds_iff (g := Units.val)]
            .
              conv =>
                arg 1
                equals seq =>
                  rfl

              have to_clm_u: plain_linear_to_clm u = u.val.toContinuousLinearMap := by
                rfl

              have u_val_eq_lim: u.val.toContinuousLinearMap = lim_seq := by
                rw [hu]
                rfl

              rw [to_clm_u, u_val_eq_lim]
              exact seq_tendsto_lim_seq
            .
              exact isembedding_units_val


        -- If the limit (in the space of linear maps) is not invertible, then it has a non-trivial kernel.
        rw [LinearMap.isUnit_iff_ker_eq_bot] at lim_seq_invertible
        apply Submodule.exists_mem_ne_zero_of_ne_bot at lim_seq_invertible
        obtain ⟨v, v_in_ker, v_ne_zero⟩ := lim_seq_invertible
        simp at v_in_ker


        have eval_at := Filter.Tendsto.eval_const seq_tendsto_lim_seq v
        have norm_tendsto := Continuous.tendsto (f := fun (x: W) => ‖x‖) (by fun_prop) (lim_seq v)
        have norm_seq_lim := Filter.Tendsto.comp norm_tendsto eval_at
        rw [v_in_ker] at norm_seq_lim
        rw [norm_zero] at norm_seq_lim
        conv at norm_seq_lim =>
          arg 1
          -- Use the fact that the action preserves the euclidian norm (maybe just up to a constant),
          -- so the sequence is actually constant
          equals fun x => ‖v‖ =>
            funext n
            simp
            have seq_mem := seq_in n
            obtain ⟨x, x_mem, seq_eq_x⟩ := seq_mem
            rw [← seq_eq_x]
            apply ContinousWithinAt.eq_const_of_mem_closure (f := fun (x: ((W) →L[ℂ] (W))ˣ) => ‖x.val v‖) (c := ‖v‖) (x := x) (s := my_new_range)
            . apply Continuous.continuousWithinAt
              fun_prop
            . exact x_mem
            . intro y hy
              simp [my_range] at hy
              obtain ⟨g, rep_g_eq_y⟩ := hy
              rw [← rep_g_eq_y]
              apply plain_linear_to_clm_preserves_norm

        -- TODO - why do we need this?
        have r_t2: T2Space ℝ := TopologicalSpace.t2Space_of_metrizableSpace

        have tendsto_norm_v := tendsto_const_nhds (α := ℕ) (f := Filter.atTop) (x := ‖v‖)
        have norm_v_zero := tendsto_nhds_unique tendsto_norm_v norm_seq_lim
        simp at norm_v_zero
        contradiction
      .
        simp
        apply LipschitzWith.isBounded_image (f := Units.val) (K := 1)
        . rw [lipschitzWith_iff_dist_le_mul]
          intro a b
          simp
          rfl
        .
          apply Bornology.IsBounded.closure
          rw [Metric.isBounded_iff_subset_ball 1]
          use 3
          intro a ha
          simp [my_new_range] at ha
          obtain ⟨g, rep_g_eq_a⟩ := ha
          simp
          conv =>
            lhs
            equals dist (a.val) (ContinuousLinearMap.id _ _) =>
              rfl
          grw [dist_le_norm_add_norm]
          grw [ContinuousLinearMap.norm_id_le]
          rw [← rep_g_eq_a]
          grw [GRepW_norm_le]
          norm_num
        -- Bornology.isBounded_image_subtype_val
    . exact isembedding_units_val




  have continuous_new_map_entry: Continuous new_map_entry := by
    simp [new_map_entry]
    rw [Units.continuous_iff]
    refine ⟨?_, ?_⟩
    . fun_prop
    . fun_prop

  --have compact_map := IsCompact.image my_range_compact.isCompact_univ (f := new_map_hom)

  have compact_mapped_group: CompactSpace mapped_group := by
    simp [mapped_group]
    refine { isCompact_univ := ?_ }
    rw [Subtype.isCompact_iff]
    simp
    conv =>
      arg 1
      equals new_map_hom '' my_new_range.topologicalClosure =>
        simp
        rfl
    apply IsCompact.image
    . exact isCompact_iff_compactSpace.mpr my_new_range_compact
    . simp [new_map_hom]
      apply continuous_new_map_entry

  let map_sub_equiv := (Subgroup.subgroupOfEquivOfLe (H := map new_map_hom.toMonoidHom my_new_range) (K := mapped_group) (by
    unfold mapped_group
    simp
    rw [Subgroup.map_le_map_iff]
    apply le_sup_of_le_left
    exact le_topologicalClosure my_new_range
  )).symm

  have S_data_range := map_range_S_data (f := (GRepW.comp GRepW_base)) (G_SPolyData hd)
  have mapped_S_data := map_S_data (f := new_map_hom.toMonoidHom) _ S_data_range
  have final_data := map_equiv_S_data map_sub_equiv mapped_S_data


  let data := theorem_3_8 (H := mapped_group) compact_mapped_group ((Subgroup.map new_map_hom.toMonoidHom my_new_range).subgroupOf mapped_group) ?_ (final_data)
  obtain ⟨B, B_abelian, B_finite_index⟩ := data

  let reverse_hom: ((map new_map_hom.toMonoidHom my_new_range).subgroupOf mapped_group) →* (GRepW_base).range := {
    toFun := fun g => (
      ((⟨Units.map (ContinuousLinearMap.toLinearMapRingHom.toMonoidHom) (new_map_hom.symm g.val), by (
        simp
        have g_prop := g.property
        rw [Subgroup.mem_subgroupOf] at g_prop
        rw [Subgroup.mem_map] at g_prop
        obtain ⟨x, x_mem, g_eq⟩ := g_prop
        simp [my_new_range] at x_mem
        obtain ⟨a, ha⟩ := x_mem
        use a
        ext f
        simp
        apply_fun (fun h => Units.map (ContinuousLinearMap.toLinearMapRingHom.toMonoidHom) h) at ha
        simp [GRepW] at ha
        rw [ha]
        simp [new_map_hom, new_map_entry_inv]
        rw [← g_eq]
        simp [new_map_hom, new_map_entry]
      )⟩) : GRepW_base.range)
    ),
    map_one' := by
      simp
    map_mul' := by
      intro a b
      simp
  }

  have reverse_hom_ker_bot: reverse_hom.ker = ⊥ := by
    simp [reverse_hom]
    rw [MonoidHom.ker_eq_bot_iff]
    intro a b hab
    simp at hab
    apply Units.map_injective at hab
    .
      simp at hab
      exact hab
    .
      intro a b hab
      simpa using hab

  have reverse_hom_range_top: reverse_hom.range = ⊤ := by
    simp [reverse_hom]
    rw [Subgroup.eq_top_iff']
    intro x
    simp
    use new_map_entry (plain_linear_to_clm x.val)
    use ?_
    .
      use ?_
      . ext f
        simp [new_map_hom, new_map_entry, new_map_entry_inv]
        rfl
      .
        rw [Subgroup.mem_subgroupOf]
        . simp [my_new_range]
          have x_prop := x.property
          rw [MonoidHom.mem_range] at x_prop
          obtain ⟨g, hg⟩ := x_prop
          use g
          simp [new_map_hom, new_map_entry]
          refine ⟨?_, ?_⟩
          . ext f
            rw [← hg]
            rfl
          . ext f
            rw [← hg]
            rfl
    .
      simp [mapped_group, my_new_range]
      have x_prop := x.property
      rw [MonoidHom.mem_range] at x_prop
      obtain ⟨g, hg⟩ := x_prop
      use (plain_linear_to_clm x.val)
      refine ⟨?_, ?_⟩
      .
        have mem_range: plain_linear_to_clm ↑x ∈ (GRepW.comp GRepW_base).range := by
          simp
          use g
          rw [← hg]
          rfl
        apply Subgroup.le_topologicalClosure (GRepW.comp (GRepW_base)).range mem_range
      . rfl



  let B' := Subgroup.map reverse_hom B
  use B'
  refine ⟨?_, ?_⟩
  . simp only [B']
    apply Subgroup.map_isMulCommutative
  . simp [B']
    rw [Subgroup.finiteIndex_iff]
    rw [Subgroup.index_map]
    simp
    rw [reverse_hom_ker_bot]
    simp
    rw [reverse_hom_range_top]
    simp
    exact B_finite_index.index_ne_zero
  .
    have base_fg: (map new_map_hom.toMonoidHom my_new_range).FG := by
      apply group_fg_map
      simp [my_new_range]
      have group_fg: Group.FG (GRepW.comp (GRepW_base)).range := by
        apply Group.fg_range
      exact (Group.fg_iff_subgroup_fg (GRepW.comp GRepW_base).range).mp group_fg

    have base_le: (map new_map_hom.toMonoidHom my_new_range) ≤ mapped_group := by
      intro a ha
      simp at ha
      simp [mapped_group]
      obtain ⟨g, g_mem, g_eq_a⟩ := ha
      use g
      refine ⟨?_, g_eq_a⟩
      apply Subgroup.le_topologicalClosure my_new_range g_mem



    rw [Subgroup.fg_iff]
    rw [Subgroup.fg_iff] at base_fg
    obtain ⟨S, S_eq, S_finite⟩ := base_fg

    have S_in_map: ∀ s ∈ S, s ∈ (map new_map_hom.toMonoidHom my_new_range) := by
      rw [Subgroup.ext_iff] at S_eq
      intro s hs
      apply (S_eq s).mp ?_
      exact Subgroup.mem_closure.mpr fun K a ↦ a hs

    let S' := Set.range (fun (s: S) => (⟨s.val, base_le (S_in_map s s.property)⟩ : mapped_group))
    use S'
    -- TODO - this is a huge mess. This can be a general proof about the closure of Subgroup.subgroupOf
    refine ⟨?_, ?_⟩
    .
      simp only [S']
      rw [← S_eq]
      ext a
      refine ⟨?_, ?_⟩
      . intro ha
        rw [Subgroup.mem_subgroupOf]
        simp at ha
        induction ha using Subgroup.closure_induction_left with
        | one => simp
        | mul_left y hy z hz h_other_z =>
          simp
          apply Subgroup.mul_mem
          . simp at hy
            obtain ⟨p, p_mem, p_eq_y⟩ := hy
            rw [← p_eq_y]
            simp
            apply Subgroup.mem_closure_of_mem p_mem
          . exact h_other_z
        | inv_mul_cancel y hy z hz h_other_z =>
          simp
          apply Subgroup.mul_mem
          . simp
            simp at hy
            obtain ⟨p, p_mem, p_eq_y⟩ := hy
            rw [← p_eq_y]
            simp
            apply Subgroup.mem_closure_of_mem p_mem
          . exact h_other_z
      . intro ha
        rw [Subgroup.mem_subgroupOf] at ha
        rw [Subgroup.mem_closure]
        intro K hK
        rw [Subgroup.mem_closure] at ha
        have a_mem := ha (Subgroup.map mapped_group.subtype K) ?_
        . simpa using a_mem
        . simp
          intro s hs
          rw [Set.range_subset_iff] at hK
          have s_mem := hK ⟨s, hs⟩
          simp
          simp at s_mem
          use ?_
          apply base_le (S_in_map s hs)
    .
      simp [S']
      rw [← Set.finite_coe_iff] at S_finite
      apply Set.finite_range

-- We need this to work with Finset
noncomputable instance GL_W_DecidableEq: DecidableEq (GL_W) := by
  apply Classical.typeDecidableEq

noncomputable instance w_map_DecidableEq: DecidableEq (W →ₗ[ℂ] W) := by
  apply Classical.typeDecidableEq



-- The input data and proofs for Theorem 3.1 in Vikman
omit hGS in
structure Theorem3_1_Input (G: Type*) [Group G] where
  -- A finite index subgroup G' of G
  G': Subgroup G
  finite_index: G'.FiniteIndex
  -- G' can be mapped homomorphically onto ℤ
  φ: (Additive G') →+ ℤ
  hφ: Function.Surjective φ





#synth Group.FG (rho_g)




lemma g_hom_abelian {T: Type*} [Group T] (A: Subgroup G) (A_finite_index: A.FiniteIndex) (hom: A →* T) (hom_surjective: Function.Surjective hom) (H: Subgroup T) (H_infinite: Infinite H) (H_abeliean: IsMulCommutative H) (H_finite_index: H.FiniteIndex) (H_FG: Group.FG H): Nonempty (Theorem3_1_Input G) := by
  -- TODO - generalize this to a lemma: finite-index subgroup of an infinite group is infinite
  -- and upstream to mathlib


  --have h_commgroup: CommGroup H := by
  --  apply CommGroup.ofIsMulCommutative

  --have h_fg: Group.FG H := by
  --  apply

    --infer_instance
  --have h_fg_comm: @Group.FG ↥H CommGroup.toGroup := by
  --  dsimp [CommGroup.toGroup]
  --  exact h_fg




  -- TODO - figure out how to make instance inference work here
  obtain ⟨i, j, i_fin, j_fin, p, p_prime, e, exists_iso⟩ := @CommGroup.equiv_free_prod_directSum_zmod H (by apply CommGroup.ofIsMulCommutative) (H_FG)
  have iso := Classical.choice exists_iso

  have j_nonempty: Nonempty j := by
    by_contra!
    simp [this] at iso
    have H_finite : Finite H := by
      rw [Equiv.finite_iff iso.toEquiv]
      have finite_i: Finite i := by
        infer_instance
      have finite_mul: ∀ f: i, Finite (Multiplicative (ZMod (p f ^ e f))) := by
        intro f
        simp [Multiplicative]
        have pow_ne_zero: NeZero (p f ^ e f) := by
          exact {
            out := by
              simp
              have first_ne_zero := Nat.Prime.ne_zero (p_prime f)
              simp [first_ne_zero]
          }
        apply Finite.of_fintype
      apply Finite.instProd
    have no_finite := H_infinite.not_finite
    contradiction

  -- TODO - can we get the comp '∘' syntax to give us a monoid hom, instead of a plain function?
  let h_to_z := (Pi.evalMonoidHom _ (Classical.choice (by
    exact j_nonempty
  ))).comp ((MonoidHom.fst _ _).comp iso.toMonoidHom)

  have h_to_z_surjective: Function.Surjective h_to_z := by
    unfold h_to_z
    simp
    apply Function.Surjective.comp
    .
      intro x
      simp
      use fun _ => x
    . apply Function.Surjective.comp
      . exact Prod.fst_surjective
      . exact iso.surjective



  -- Interpret H as a subgroup of GL_W
  --let H_as_GL_W := Subgroup.map (Subgroup.subtype (hom.range)) H
  let G' := Subgroup.comap hom H
  have H_index_ne_zero := H_finite_index.index_ne_zero

  -- TODO - generalize this and PR to mathlib
  have rangerestrict_range: hom.rangeRestrict.range = ⊤ := by
    ext a
    simp
    have a_prop := a.property
    rw [MonoidHom.mem_range] at a_prop
    obtain ⟨x, hx⟩ := a_prop
    use x
    use x.property
    rw [Subtype.ext_iff]
    simp
    exact hx



  have G'_finite_index: G'.FiniteIndex := by
    unfold G'
    exact {
      index_ne_zero := by
        simp
        rw [Subgroup.index_comap]
        -- apply somehow found this - how does it work???
        exact Subgroup.FiniteIndex.index_ne_zero
    }



  -- TODO - there must be an easier way to do this
  let g'_to_h: (map A.subtype G') →* H := {
    toFun := fun g => ⟨hom ⟨g.val, by (
      -- TODO - clean this up
      have foo := g.property
      rw [Subgroup.mem_map] at foo
      obtain ⟨x, hx, a_subtype⟩ := foo
      rw [← a_subtype]
      simp
    )⟩, by (
      have g_prop := g.property
      simp only [G', Subgroup.mem_comap] at g_prop
      rw [Subgroup.mem_map] at g_prop
      obtain ⟨x, hx, a_subtype⟩ := g_prop
      simp_rw [← a_subtype]
      simp
      simp at hx
      exact hx
    )⟩
    map_one' := by
      simp
      conv =>
        lhs
        arg 2
        equals 1 => simp
      simp

    map_mul' := by
      simp
      intro a ha a_mem b hb b_mem

      conv =>
        lhs
        arg 2
        equals ⟨a, ha⟩ * ⟨b, hb⟩ => simp
      rw [MonoidHom.map_mul]
  }

  let additive_g'_to_h := g'_to_h.toAdditive
  let additive_h_to_z := h_to_z.toAdditive

  let g_to_additive_z := additive_h_to_z.comp additive_g'_to_h
  let g_to_z := (AddEquiv.additiveMultiplicative ℤ).toAddMonoidHom.comp g_to_additive_z


  apply Nonempty.intro
  exact {
    G' := Subgroup.map A.subtype G',
    finite_index := by
      rw [Subgroup.finiteIndex_iff]
      simp [Subgroup.index_map_subtype]
      refine ⟨?_, ?_⟩
      . rw [← ne_eq]
        rw [← Subgroup.finiteIndex_iff]
        exact G'_finite_index
      . exact A_finite_index.index_ne_zero
      -- G'_finite_index
    φ := g_to_z,
    hφ := by
      simp [g_to_z, g_to_additive_z]
      apply Function.Surjective.comp
      . simp [additive_h_to_z]
        exact h_to_z_surjective
      .
        simp [additive_g'_to_h, g'_to_h]
        intro h
        obtain ⟨a, hom_a⟩ := hom_surjective h
        simp
        use a
        simp
        simp [G', hom_a]
  }

#print axioms g_hom_abelian

-- Case 1 in Section 3.3 of Vikman, where the representation ρ(G) is infinite
lemma rho_g_case_infinite {d: ℕ} (hd: HasPolynomialGrowthD S d) (hr: Infinite (↥(rho_g))): Nonempty (Theorem3_1_Input G) := by
  obtain ⟨H, H_abelian, H_finite_index⟩ := rho_g_contains_abelian hd


  have h_fg: Group.FG H := by
    apply Subgroup.fg_of_index_ne_zero

  let top_equiv := Subgroup.topEquiv (G := G)
  let top_comp := (GRepW_base).comp top_equiv.toMonoidHom
  let g_rho := (GRepW_base).rangeRestrict.comp top_equiv.toMonoidHom



  --let H' := top_equiv.toMonoidHom
  --let other_H' := H'.range

  have target := g_hom_abelian ⊤ (by infer_instance) (g_rho) ?_ (H) ?_ ?_ ?_ ?_
  . exact target
  .
    simp [g_rho]
    exact MonoidHom.rangeRestrict_surjective GRepW_base
  .
    dsimp [MonoidHom.range]
    unfold rho_g at hr
    have card_mul := Subgroup.card_mul_index H
    unfold rho_g at card_mul
    nth_rw 2 [Nat.card_eq_zero_of_infinite] at card_mul
    rw [Nat.mul_eq_zero] at card_mul
    simp [H_finite_index.index_ne_zero] at card_mul
    rw [Nat.card_eq_zero] at card_mul
    simp at card_mul
    exact card_mul
  . exact H_abelian
  . exact H_finite_index
  . exact h_fg

#print axioms rho_g_case_infinite




instance countable_G: Countable G := by
  apply Function.Surjective.countable (f := fun (x: List S) => x.unattach.prod)
  intro g
  obtain ⟨l, hl⟩ := mem_S_prod_list  g
  use l
  simp only
  unfold ProdS at hl
  rw [hl]


-- TODO - use the fact that G is finitely generated
instance countable_add_G: Countable (Additive G) := by
  apply inferInstanceAs (Countable G)

lemma singleton_pairwise_disjoint {T: Type*} (s: Set (T)) : s.PairwiseDisjoint Set.singleton := by
  refine Set.pairwiseDisjoint_iff.mpr ?_
  intro a ha b hb hab
  unfold Set.singleton at hab
  simp at hab
  exact hab.symm


instance G_Add_MeasureableSingleton: MeasurableSingletonClass (Additive G) := {
  measurableSet_singleton := by
    intro x
    apply IsOpen.measurableSet
    simp
}

instance G_MeasureableSingleton: MeasurableSingletonClass (G) := {
  measurableSet_singleton := by
    intro x
    apply IsOpen.measurableSet
    simp
}

-- Use the fact that we have the discrete topology
set_option maxHeartbeats 500000 in
lemma my_add_haar_eq_count: (myHaarAddOpp) = MeasureTheory.Measure.count := by
  ext s hs
  by_cases s_finite: Set.Finite s
  .
    have eq_singletons := Set.biUnion_of_singleton (s := s)
    nth_rw 1 [← eq_singletons]
    rw [MeasureTheory.Measure.count_apply_finite s s_finite]
    rw [MeasureTheory.measure_biUnion]
    .
      -- TODO - extract 'measure {a} = 1' to a lemma
      simp_rw [MeasureTheory.Measure.addHaar_singleton]
      unfold myHaarAddOpp
      simp_rw [← singleton_carrier]
      simp_rw [TopologicalSpace.PositiveCompacts.carrier_eq_coe]
      rw [MeasureTheory.Measure.addHaarMeasure_self]
      rw [ENNReal.tsum_set_const]
      simp
      norm_cast
      rw [Set.Finite.encard_eq_coe_toFinset_card s_finite]
    . exact Set.Finite.countable s_finite
    .
      apply singleton_pairwise_disjoint
    .
      intro a ha
      apply IsOpen.measurableSet
      simp
  .
    have s_infinite: s.Infinite := by
      exact s_finite
    rw [MeasureTheory.Measure.count_apply_infinite s_infinite]
    have eq_singletons := Set.biUnion_of_singleton (s := s)
    nth_rw 1 [← eq_singletons]
    rw [MeasureTheory.measure_biUnion]
    .
      simp_rw [MeasureTheory.Measure.addHaar_singleton]
      unfold myHaarAddOpp
      simp_rw [← singleton_carrier]
      simp_rw [TopologicalSpace.PositiveCompacts.carrier_eq_coe]
      rw [MeasureTheory.Measure.addHaarMeasure_self]
      simp only [ENNReal.tsum_one, ENat.toENNReal_eq_top, ENat.card_eq_top]
      exact Set.infinite_coe_iff.mpr s_finite
    . exact Set.to_countable s
    . apply singleton_pairwise_disjoint
    .
      intro a ha
      apply IsOpen.measurableSet
      simp

lemma my_haar_eq_count: (myHaar) = MeasureTheory.Measure.count := by
  ext s hs
  by_cases s_finite: Set.Finite s
  .
    have eq_singletons := Set.biUnion_of_singleton (s := s)
    nth_rw 1 [← eq_singletons]
    rw [MeasureTheory.Measure.count_apply_finite s s_finite]
    rw [MeasureTheory.measure_biUnion]
    .
      -- TODO - extract 'measure {a} = 1' to a lemma
      simp_rw [MeasureTheory.Measure.haar_singleton]
      unfold myHaar
      simp_rw [← mul_singleton_carrier]
      simp_rw [TopologicalSpace.PositiveCompacts.carrier_eq_coe]
      rw [MeasureTheory.Measure.haarMeasure_self]
      rw [ENNReal.tsum_set_const]
      simp
      norm_cast
      rw [Set.Finite.encard_eq_coe_toFinset_card s_finite]
    . exact Set.Finite.countable s_finite
    .
      apply singleton_pairwise_disjoint
    .
      intro a ha
      apply IsOpen.measurableSet
      simp
  .
    have s_infinite: s.Infinite := by
      exact s_finite
    rw [MeasureTheory.Measure.count_apply_infinite s_infinite]
    have eq_singletons := Set.biUnion_of_singleton (s := s)
    nth_rw 1 [← eq_singletons]
    rw [MeasureTheory.measure_biUnion]
    .
      simp_rw [MeasureTheory.Measure.haar_singleton]
      unfold myHaar
      simp_rw [← mul_singleton_carrier]
      simp_rw [TopologicalSpace.PositiveCompacts.carrier_eq_coe]
      rw [MeasureTheory.Measure.haarMeasure_self]
      simp only [ENNReal.tsum_one, ENat.toENNReal_eq_top, ENat.card_eq_top]
      exact Set.infinite_coe_iff.mpr s_finite
    . exact Set.to_countable s
    . apply singleton_pairwise_disjoint
    .
      intro a ha
      apply IsOpen.measurableSet
      simp


-- With the counting measure, A.E is the same as everywgere
lemma count_ae_everywhere (p: G → Prop): (∀ᵐ g ∂(MeasureTheory.Measure.count), p g) = ∀ a: G, p a := by
  rw [MeasureTheory.ae_iff]
  simp [MeasureTheory.Measure.count_eq_zero_iff]
  -- TODO - there has to be a much simpler way of proving this
  refine ⟨?_, ?_⟩
  . intro h
    intro a
    by_contra this
    have a_in: a ∈ {a | ¬ p a} := by
      simp [this]
    have foo := Set.nonempty_of_mem a_in
    rw [← Set.not_nonempty_iff_eq_empty] at h
    contradiction
  . intro h
    by_contra this
    simp at this
    rw [← ne_eq] at this
    rw [← Set.nonempty_iff_ne_empty'] at this
    obtain ⟨a, ha⟩ := this
    specialize h a
    simp at ha
    contradiction

lemma ae_eventually_everywhere {f g: G → ℝ}: ((∀ᵐ (x : G), f x = g x)) ↔ (f = g) := by
  simp [MeasureTheory.volume]
  simp_rw [my_haar_eq_count]
  have foo := count_ae_everywhere (p := fun a => f a = g a)
  conv at foo =>
    rhs
    equals f = g =>
      have my_ext := funext_iff (f := f) (g := g)
      simp at my_ext
      simp
      exact id (Iff.symm my_ext)

  simp
  simp at foo
  exact foo


@[simp]
lemma ae_eq_everywhere {f g: G → ℝ}: (f =ᶠ[MeasureTheory.ae MeasureTheory.volume (α := G)] g) ↔ (f = g) := by
  simp [Filter.EventuallyEq]
  apply ae_eventually_everywhere


-- Use the fact that our measure is the counting measure (since we have the discrete topology),
-- and negating a finite set of points in an additive group leaves the cardinality unchanged
instance myNegInvariant: MeasureTheory.Measure.IsNegInvariant (myHaarAddOpp) := {
  neg_eq_self := by
    rw [my_add_haar_eq_count]
    simp only [MeasureTheory.Measure.neg_eq_self]
}

-- TODO - I don't think we can use this, as `MeasureTheory.convolution' would require our group to be commutative
-- (via `NormedAddCommGroup`)
open scoped Convolution
open MeasureTheory
-- TODO - should we define this using 'Lp'?
-- NOTE - the Mathlib convolution uses the opposite order of arguments as in the Vikman paper (g(x - t) instead of g(t - x))
-- I originally used 'MulOpposite' make our usage agree with the paper, but this made it an enormous pain to work with
-- (since while Additive G is defeq to G, MulOpposite G is not defeq to G)
-- Nothing in the paper should actually depend on this (since we take a convolution over a symmetric generating set S)
-- Some of our definitions will have an inverse or order swap compared to the paper, but this is better than
-- fighting with 'MulOpposite' every time we need to prove something about a convolution

-- Note - there's some defeq abuse going on here, as we're passing in 'f' and 'g' directly (they take in G, not 'Additive G')
-- However, this makes it much easier to prove properties about this via the `MeasureTheory.ConvolutionExists` API
noncomputable def Conv (f g: G → ℝ) (x: G) : ℝ :=
  (MeasureTheory.convolution (G := Additive G) f g (ContinuousLinearMap.mul ℝ ℝ) myHaarAddOpp x)


def ConvExists (f g: G → ℝ) := MeasureTheory.ConvolutionExists (G := Additive G) (fun x => f x.toMul) (fun x => g x.toMul) (ContinuousLinearMap.mul ℝ ℝ) myHaarAddOpp

def ConvExistsAt (f g: G → ℝ) (x: G) := MeasureTheory.ConvolutionExistsAt (G := Additive G) (fun x => f x.toMul) (fun x => g x.toMul) x (ContinuousLinearMap.mul ℝ ℝ) myHaarAddOpp

-- lemma conv_lp2 (f g: (MeasureTheory.Lp ℝ 2 (MeasureTheory.volume (α := G)))): MemLp (Conv f g) 2 := by
--   unfold Conv
--   have foo := ENNReal.eLpNorm_top_convolution_le
--     (L := (ContinuousLinearMap.mul ℝ ℝ))
--     (f := fun (x: Additive (MulOpposite G)) => f x.toMul.unop)
--     (g := fun (x: Additive (MulOpposite G)) => g x.toMul.unop)
--     (p := 2) (q := 2)
--     (μ := myHaarAddOpp)
--     (by
--       simp [ENNReal.HolderConjugate]
--       exact {
--         inv_add_inv_eq_inv := by field_simp
--       }
--     )
--     (by apply AEMeasurable.of_discrete)
--     (by apply AEMeasurable.of_discrete) 1
--     (by simp)
--   simp at foo



-- TODO - this is left over from when I used MulOpposite
-- we should remove all usages of this
abbrev opAdd (g : G) := Additive.ofMul g


-- A versi on of `conv_exists` where at least one of the functions has finite support
-- This lets us avoid dealing with 'MemLp' in most cases
lemma conv_exists_fin_supp (f g: G → ℝ) (hfg: f.support.Finite ∨ g.support.Finite): ConvExists f g := by
  unfold ConvExists MeasureTheory.ConvolutionExists MeasureTheory.ConvolutionExistsAt
  intro x
  apply Continuous.integrable_of_hasCompactSupport
  . exact continuous_of_discreteTopology
  .
    unfold HasCompactSupport
    rw [isCompact_iff_finite]
    dsimp [tsupport]
    rw [closure_discrete]
    simp only [Function.support_mul]
    match hfg with
    | .inl hf =>
      apply Set.Finite.inter_of_left
      apply Set.Finite.subset (s := opAdd '' f.support)
      . unfold opAdd
        exact Set.Finite.image (fun g ↦ Additive.ofMul g) hf
      . intro a ha
        simp at ha
        simp [opAdd]
        exact ha
    | .inr hg =>
      apply Set.Finite.inter_of_right
      let myFun := fun a => -(opAdd a) + x
      have finite_image := Set.finite_image_iff (f := myFun) (s := g.support) ?_
      .
        conv =>
          arg 1
          equals (myFun '' Function.support g) =>
            ext a
            simp
            refine ⟨?_, ?_⟩
            . intro ha
              use (Additive.toMul x) / ((Additive.toMul a))
              refine ⟨ha, ?_⟩
              simp [myFun, opAdd]
            . intro ha
              simp [myFun, opAdd] at ha
              obtain ⟨b, b_zero, a_eq⟩ := ha
              rw [← a_eq]
              simp [b_zero]
        rw [finite_image]
        exact hg
      .
        simp [myFun, opAdd]

lemma lt_top_mul {a b c : ENNReal} (hab: a ≤ b * c) (hb: b < ⊤) (hc: c < ⊤) : a < ⊤ := by
  have b_c_not_top: b * c < ⊤ := by
    apply WithTop.mul_lt_top (hb) (hc)
  grw [hab]
  exact b_c_not_top


instance my_add_haar_left_invariant: (myHaarAddOpp.IsAddLeftInvariant (G := Additive (G))) := by
  rw [my_add_haar_eq_count]
  infer_instance

instance my_add_haar_right_invariant: (myHaarAddOpp.IsAddRightInvariant (G := Additive (G))) := by
  rw [my_add_haar_eq_count]
  infer_instance

-- lemma conv_exists_lp1 (f g: G → ℝ)
--   (hf: MeasureTheory.MemLp ((fun x => f x.toMul)) 1 myHaarAddOpp)
--   (hg: ∀ y: G, MeasureTheory.MemLp ((fun x => g x.toMul)) 1 myHaarAddOpp)
--   : ConvExists f g := by

--   apply ENNReal.ConvolutionExists.of_memLp_memLp (p := 1) (q := 1) (μ := myHaarAddOpp) (by
--     simp [ENNReal.HolderConjugate]
--     exact {
--       inv_add_inv_eq_inv := by field_simp
--     }
--   )
--     -- (f := fun a => f (MulOpposite.unop (Additive.toMul a)))
--     -- (g := fun a => g ((MulOpposite.unop (Additive.toMul a))))
--     -- (hf := AEMeasurable.of_discrete)
--     -- (hg := AEMeasurable.of_discrete)
--     -- (by simp [ENNReal.HolderConjugate])
--     -- (by simp [ENNReal.HolderConjugate])

--   have young_bound := ENNReal.eLpNorm_convolution_le_enorm_mul
--     (f := fun a => f (MulOpposite.unop (Additive.toMul a)))
--     (g := fun a => g ((MulOpposite.unop (Additive.toMul a))))
--     (L := (ContinuousLinearMap.mul ℝ ℝ))
--     (r := 1)
--     (p := 1)
--     (q := 1)
--     (μ := myHaarAddOpp)
--     (by simp)
--     (by simp)
--     (by simp)
--     (by simp)
--     (by apply AEMeasurable.of_discrete)
--     (by apply AEMeasurable.of_discrete)

--   have young_lt_top := lt_top_mul young_bound ?_ ?_
--   .
--     simp [eLpNorm, eLpNorm'] at young_lt_top
--     --

--     unfold ConvExists MeasureTheory.ConvolutionExists MeasureTheory.ConvolutionExistsAt MeasureTheory.Integrable
--     intro z
--     refine ⟨MeasureTheory.AEStronglyMeasurable.of_discrete, ?_⟩
--     unfold MeasureTheory.HasFiniteIntegral
--     simp [MeasureTheory.convolution] at young_lt_top
--     simp

--     rw [WithTop.lt_top_iff_ne_top] at young_lt_top
--     apply MeasureTheory.measure_eq_top_of_lintegral_ne_top _ at young_lt_top
--     rw [my_add_haar_eq_count] at young_lt_top
--     rw [MeasureTheory.Measure.count_eq_zero_iff] at young_lt_top
--     simp only [enorm_ne_top] at young_lt_top




--   unfold ConvExists MeasureTheory.ConvolutionExists MeasureTheory.ConvolutionExistsAt MeasureTheory.Integrable
--   intro g
--   refine ⟨MeasureTheory.AEStronglyMeasurable.of_discrete, ?_⟩
--   unfold MeasureTheory.HasFiniteIntegral
--   simp [eLpNorm, eLpNorm'] at young_bound
--   --simp [MeasureTheory.convolution] at young_bound
--   grw [young_bound]



--   unfold ConvExists MeasureTheory.ConvolutionExists MeasureTheory.ConvolutionExistsAt MeasureTheory.Integrable
--   intro x
--   simp only [toMul_sub, MulOpposite.unop_div, ContinuousLinearMap.mul_apply']
--   refine ⟨MeasureTheory.AEStronglyMeasurable.of_discrete, ?_⟩
--   unfold MeasureTheory.HasFiniteIntegral
--   grw [ENNReal.eLpNorm_convolution_le_enorm_mul]


lemma conv_exists (p q : ℝ) (hp: 0 < p) (hq: 0 < q) (hpq: p.HolderConjugate q) (f g: G → ℝ)
  (hf: MeasureTheory.MemLp ((fun x => f x.toMul)) (ENNReal.ofReal p) myHaarAddOpp)
  (hg: ∀ y: G, MeasureTheory.MemLp ((fun x => g (y / x.toMul))) (ENNReal.ofReal q) myHaarAddOpp)
  : ConvExists f g := by
  unfold ConvExists MeasureTheory.ConvolutionExists MeasureTheory.ConvolutionExistsAt MeasureTheory.Integrable
  intro x
  simp only [toMul_sub, MulOpposite.unop_div, ContinuousLinearMap.mul_apply']
  refine ⟨MeasureTheory.AEStronglyMeasurable.of_discrete, ?_⟩
  unfold MeasureTheory.HasFiniteIntegral
  simp
  have holder_bound := ENNReal.lintegral_mul_le_Lp_mul_Lq (MeasureTheory.Measure.count) (hpq)
    (AEMeasurable.of_discrete) (AEMeasurable.of_discrete)
    (f := fun a => ‖f ( (Additive.toMul a))‖ₑ)
    (g := fun a => ‖g ((Additive.toMul x) / ((Additive.toMul a)))‖ₑ)
  simp at holder_bound
  rw [my_add_haar_eq_count]

  have p_ne_zero: ENNReal.ofReal p ≠ 0 := by
    simp [hp]


  have p_ge_zero: 0 ≤ p := by
    linarith

  have q_ge_zero: 0 ≤ q := by
    linarith

  have q_ne_zero: ENNReal.ofReal q ≠ 0 := by
    simp
    linarith

  have integral_lt_top := ne_top_of_le_ne_top (?_) holder_bound
  . exact Ne.lt_top' (id (Ne.symm integral_lt_top))
  . apply WithTop.mul_ne_top
    .
      have foo := MeasureTheory.lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top p_ne_zero (by simp) (MeasureTheory.MemLp.eLpNorm_lt_top hf)
      rw [my_add_haar_eq_count] at foo
      rw [ENNReal.toReal_ofReal p_ge_zero] at foo
      apply ENNReal.rpow_ne_top_of_nonneg (?_) ?_
      . simp only [inv_nonneg]
        linarith
      . exact LT.lt.ne_top foo
    .

      have foo := MeasureTheory.lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top q_ne_zero (by simp) (MeasureTheory.MemLp.eLpNorm_lt_top (hg x.toMul))
      rw [my_add_haar_eq_count] at foo
      rw [ENNReal.toReal_ofReal q_ge_zero] at foo
      apply ENNReal.rpow_ne_top_of_nonneg (?_) ?_
      . simp only [inv_nonneg]
        linarith
      .
        exact LT.lt.ne_top foo


-- Defintion 3.11 in Vikman: The function 'μ',  not to be confused with a measure on a measure space
noncomputable def mu: G → ℝ := ((1 : ℝ) / (#(S) : ℝ)) • ∑ s ∈ S, Pi.single s (1 : ℝ)

-- Definition 3.11 in Vikman - the m-fold convolution of μ with itself
noncomputable def muConv (n: ℕ): G → ℝ := (Nat.iterate (fun f => Conv  f (mu )) n) (mu )



abbrev delta (s: G): G → ℝ := Pi.single s 1

lemma conv_eq_sum {f h: G → ℝ} (hconv: ConvExists f h) (g: G): Conv f h g = ∑' (a : Additive G), f (a) * h (g * (Additive.toMul a)⁻¹) := by
  unfold Conv
  unfold MeasureTheory.convolution
  rw [MeasureTheory.integral_countable']
  .
    simp_rw [MeasureTheory.measureReal_def]
    unfold myHaarAddOpp
    simp_rw [MeasureTheory.Measure.addHaar_singleton]
    simp [MeasureTheory.Measure.addHaarMeasure_self]
    simp_rw [← singleton_carrier]
    simp_rw [TopologicalSpace.PositiveCompacts.carrier_eq_coe]
    simp [MeasureTheory.Measure.addHaarMeasure_self]
    field_simp

    -- TODO - avoid defeq abuse here
    conv =>
      lhs
      arg 1
      intro a
      rhs
      equals h (Additive.ofMul g - a) =>
        rfl

    conv =>
      rhs
      arg 1
      intro a
      rhs
      arg 1
      equals Additive.ofMul g - a =>
        unfold Additive.toMul
        unfold Additive.ofMul
        simp
        rw [sub_eq_add_neg]
        rfl

  . exact (hconv (opAdd g))

lemma conv_eq_sum'  {f h: G → ℝ} (hconv: ConvExists f h): Conv f h = fun g => ∑' (a : Additive G), f ((Additive.toMul a)) * h (g * (Additive.toMul a)⁻¹) := by
  funext g
  exact conv_eq_sum hconv g


-- Linearity lemmas for convolution - this is basically just wrapping the MeasureTheory.ConvolutionExists lemmas,
-- specialized for our own Additive/MulOpposite wrappers
lemma conv_add_right {f g h: G → ℝ} (h_fg: ConvExists f g) (h_fh : ConvExists f h):  Conv f (g + h) = Conv f g + Conv f h := by
  unfold Conv
  conv =>
    lhs
    intro x
    arg 2
    equals (fun x => g ((Additive.toMul x))) + (fun x => h ((Additive.toMul x))) =>
      rfl

  rw [MeasureTheory.ConvolutionExists.distrib_add]
  . rfl
  . exact h_fg
  . exact h_fh

lemma conv_add_left {f g h: G → ℝ} (h_fh: ConvExists f h) (h_gh : ConvExists g h):  Conv (f + g) h = Conv f h + Conv g h := by
  unfold Conv
  conv =>
    lhs
    intro x
    arg 1
    equals (fun x => f ((Additive.toMul x))) + (fun x => g ((Additive.toMul x))) =>
      rfl

  rw [MeasureTheory.ConvolutionExists.add_distrib]
  . rfl
  . exact h_fh
  . exact h_gh

lemma conv_smul {f h: G → ℝ} (k: ℝ): Conv (k • f) h = k • Conv f h := by
  funext g
  unfold Conv
  rw [MeasureTheory.smul_convolution]
  simp

lemma smul_conv (f h: G → ℝ) (k: ℝ): Conv f (k • h) = k • Conv f h := by
  funext g
  unfold Conv
  rw [MeasureTheory.convolution_smul]
  simp


-- Proving associativity in full generality is very annoying
-- Fortunately, we only need to use it once, so we can use restrictive hypothesis that match
-- the functions we invoke this with
lemma conv_assoc {f g h: G → ℝ} (h_fg: ConvExists f g) (h_gh: ConvExists g h) (g_finsupp: g.support.Finite) (g_nonneg: ∀ a : G, 0 ≤ g a) (h_finsupp: h.support.Finite) (h_nonneg: ∀ a : G, 0 ≤ h a): Conv (Conv f g) h = Conv f (Conv g h) := by
  unfold Conv
  unfold ConvExists at h_fg
  funext x
  conv =>
    lhs
    arg 1
    simp
    eta_reduce
  rw [MeasureTheory.convolution_assoc (L := ContinuousLinearMap.mul ℝ ℝ) (L₂ := ContinuousLinearMap.mul ℝ ℝ) (L₃ := ContinuousLinearMap.mul ℝ ℝ) (L₄ := ContinuousLinearMap.mul ℝ ℝ)]
  . rfl
  . intro x y z
    simp
    rw [mul_assoc]
  . apply MeasureTheory.AEStronglyMeasurable.of_discrete
  . apply MeasureTheory.AEStronglyMeasurable.of_discrete
  . apply MeasureTheory.AEStronglyMeasurable.of_discrete
  .
    apply Filter.Eventually.of_forall
    exact h_fg
  . apply Filter.Eventually.of_forall
    intro a
    conv =>
      arg 1
      intro b
      rw [Real.norm_of_nonneg (g_nonneg b)]

    conv =>
      arg 2
      intro b
      rw [Real.norm_of_nonneg (h_nonneg b)]
    apply h_gh a
  .

    have g_supp_compact: HasCompactSupport fun x ↦ ‖g x‖ := by
      apply HasCompactSupport.intro (K := g.support)
      . apply Set.Finite.isCompact
        apply g_finsupp
      . simp

    have h_supp_compact: HasCompactSupport fun x ↦ ‖h x‖ := by
      apply HasCompactSupport.intro (K := h.support)
      . apply Set.Finite.isCompact
        apply h_finsupp
      . simp

    apply HasCompactSupport.convolutionExists_right
    .
      apply HasCompactSupport.convolution
      .
        apply g_supp_compact
      . apply h_supp_compact
    . apply Continuous.locallyIntegrable
      exact continuous_of_discreteTopology
    .
      apply HasCompactSupport.continuous_convolution_right
      . apply h_supp_compact
      .
        apply Continuous.locallyIntegrable
        exact continuous_of_discreteTopology
      . exact continuous_of_discreteTopology
    -- let other := ((fun (x: (Additive G)) ↦ ‖g x‖) ⋆[ContinuousLinearMap.mul ℝ ℝ, myHaarAddOpp] fun (x: (Additive G)) ↦ ‖h x‖)
    -- have finsupp_conv := conv_exists_fin_supp (fun (b: G) => ‖f b‖) (fun b => other (Additive.ofMul b)) ?_
    -- . apply finsupp_conv x
    -- . left
    --   simp
    --   rw [← Function.comp_def]
    --   rw [Function.support_comp_eq]
    --   . apply f_finsupp
    --   . simp


-- -- We take advantage of junk values to avoid needing to prove that the convolutions actually exist
-- lemma conv_assoc_le {f g h b: G → ℝ} (x: G) (right_le: ‖Conv f (Conv g h) x‖ ≤ ‖b x‖): ‖Conv (Conv f g) h x‖ ≤ ‖b x‖ := by
--   by_cases f_g_exists: ConvExistsAt f g x
--   .
--     rw [conv_assoc]
--   .
--     conv =>
--       arg 1
--       arg 1
--       arg 1
--       unfold Conv
--     simp [convolution, integral]
--     unfold ConvExistsAt ConvolutionExistsAt at f_g_exists
--     simp [-toMul_sub] at f_g_exists
--     conv at f_g_exists =>
--       arg 1
--       arg 1
--       equals fun t ↦ f (t) * g (((Additive.ofMul x) - (Additive.ofMul t))) =>
--         rfl


--     conv =>
--       lhs
--       arg 1
--       arg 1
--       intro x
--       arg 2
--       intro y
--       rw [dif_neg (by
--         exact f_g_exists
--       )]
--       arg 2
--       equals (fun (hf: Integrable (fun t ↦ f (t) * g (((Additive.ofMul x) - (Additive.ofMul t))))) ↦ L1.integral (Integrable.toL1 (fun t ↦ f (t) * g (((Additive.ofMul x) - (Additive.ofMul t)))) hf)) =>
--         rfl



--     simp
--     simp [f_g_exists]
--     simp


-- TODO - can we replace 'conv_assoc' with this?
lemma conv_assoc_of_lp2 {f g h: G → ℝ} (hf: MemLp f 2 Measure.count) (hg: MemLp g 2 Measure.count) (h_finsupp: h.support.Finite): Conv (Conv f g) h = Conv f (Conv g h) := by
  unfold Conv
  funext x


  have h_lp_n (n: ℕ): MemLp h n myHaarAddOpp := by
    apply Continuous.memLp_of_hasCompactSupport
    . fun_prop
    .
      simp [HasCompactSupport]
      apply Set.Finite.isCompact
      simp [tsupport]
      exact h_finsupp

  conv =>
    lhs
    arg 1
    simp
    eta_reduce
  rw [MeasureTheory.convolution_assoc (L := ContinuousLinearMap.mul ℝ ℝ) (L₂ := ContinuousLinearMap.mul ℝ ℝ) (L₃ := ContinuousLinearMap.mul ℝ ℝ) (L₄ := ContinuousLinearMap.mul ℝ ℝ)]
  . rfl
  . intro x y z
    simp
    rw [mul_assoc]
  . apply MeasureTheory.AEStronglyMeasurable.of_discrete
  . apply MeasureTheory.AEStronglyMeasurable.of_discrete
  . apply MeasureTheory.AEStronglyMeasurable.of_discrete
  .
    apply Filter.Eventually.of_forall
    intro a
    rw [my_add_haar_eq_count]
    apply ENNReal.ConvolutionExists.of_memLp_memLp (p := 2) (q := 2) (μ := Measure.count)
    . infer_instance
    . simp
    . apply AEStronglyMeasurable.of_discrete
    . apply AEStronglyMeasurable.of_discrete
    .
      exact hf
    . exact hg
  . apply Filter.Eventually.of_forall
    intro a
    rw [my_add_haar_eq_count]
    apply ENNReal.ConvolutionExists.of_memLp_memLp (p := 2) (q := 2) (μ := Measure.count)
    . infer_instance
    . simp
    . apply AEStronglyMeasurable.of_discrete
    . apply AEStronglyMeasurable.of_discrete
    .
      apply MeasureTheory.MemLp.abs
      exact hg
    . apply MeasureTheory.MemLp.abs
      rw [← my_add_haar_eq_count]
      apply h_lp_n
  .
    rw [my_add_haar_eq_count]
    apply ENNReal.ConvolutionExists.of_memLp_memLp (p := 2) (q := 2) (μ := Measure.count)
    . infer_instance
    . simp
    . apply AEStronglyMeasurable.of_discrete
    . apply AEStronglyMeasurable.of_discrete
    .
      apply MeasureTheory.MemLp.abs
      exact hf
    .
      unfold MeasureTheory.MemLp
      refine ⟨by apply AEStronglyMeasurable.of_discrete, ?_⟩
      rw [← my_add_haar_eq_count]
      grw [ENNReal.eLpNorm_convolution_le_enorm_mul' (p := 2) (q := 1)]
      .
        simp
        apply ENNReal.mul_lt_top
        . apply ENNReal.mul_lt_top
          . simp
          .
            simp_rw [← Real.norm_eq_abs]
            rw [MeasureTheory.eLpNorm_norm]
            rw [my_add_haar_eq_count]
            exact MemLp.eLpNorm_lt_top hg
        .



          simp_rw [← Real.norm_eq_abs]
          rw [MeasureTheory.eLpNorm_norm]
          rw [my_add_haar_eq_count]
          rw [← my_add_haar_eq_count]
          have foo := h_lp_n 1
          simp at foo
          exact MemLp.eLpNorm_lt_top foo
      . simp
      . simp
      . simp
      . simp
      . apply AEStronglyMeasurable.of_discrete
      . apply AEStronglyMeasurable.of_discrete


-- TODO - figure out why we need these
instance Real.t2Space: T2Space ℝ := TopologicalSpace.t2Space_of_metrizableSpace
instance Real.firstCountable: FirstCountableTopology ℝ := TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology

lemma conv_sum {T: Type*} (H: Finset T) (f: T → G → ℝ) (h: G → ℝ) (h_finsupp: h.support.Finite): Conv (∑ t ∈ H, f t) h = ∑ t ∈ H, (Conv (f t) h) := by
  funext g
  rw [conv_eq_sum]
  .
    simp
    conv =>
      rhs
      arg 2
      intro t
      rw [conv_eq_sum (by
        apply conv_exists_fin_supp
        right
        exact h_finsupp
      )]

    conv =>
      lhs
      arg 1
      intro a
      rw [Finset.sum_mul]

    rw [Summable.tsum_finsetSum]
    intro s hs
    apply summable_of_finite_support
    simp
    apply Set.Finite.inter_of_right
    rw [← Function.comp_def]
    rw [Function.support_comp_eq_preimage]
    apply Set.Finite.preimage
    .
      intro y hy z hz
      simp
    . exact h_finsupp
  . apply conv_exists_fin_supp
    right
    exact h_finsupp



-- Old stuff for two LP_2 function - might be useful later
    -- unfold ConvExists MeasureTheory.ConvolutionExists MeasureTheory.ConvolutionExistsAt
    -- have my_exists := conv_exists  (p := 2) (q := 2) (by simp) (by simp) (by exact Real.HolderConjugate.two_two) f (delta s) hf ?_
    -- .
    --   intro x
    --   exact MeasureTheory.ConvolutionExistsAt.integrable (my_exists x)
    -- .
    --   intro x
    --   unfold delta
    --   apply Continuous.memLp_of_hasCompactSupport
    --   . exact continuous_of_discreteTopology
    --   .
    --     unfold HasCompactSupport
    --     rw [isCompact_iff_finite]
    --     dsimp [tsupport]
    --     rw [closure_discrete]

    --     apply Set.Finite.subset (s := {opAdd (x * s⁻¹)}) (by simp)
    --     intro a ha
    --     dsimp [Pi.single, Function.update] at ha
    --     simp at ha
    --     simp [opAdd]
    --     rw [← ha]
    --     simp

-- Proposition 3.12, item 1, in Vikman
lemma f_conv_delta (f: G → ℝ) (g s: G): (Conv  f (delta s)) g = f (s⁻¹ * g) := by
  unfold delta
  rw [conv_eq_sum]
  .
    rw [tsum_eq_sum (s := {opAdd ((s⁻¹ * g))}) ?_]
    .
      simp
      -- TODO - why does this need 'conv'?
      conv =>
        lhs
        arg 2
        arg 3
        simp only [mul_inv_rev, inv_inv, inv_mul_cancel_right]
      rw [← mul_assoc]
      -- TODO - why is 'simp' not doing these?
      rw [mul_inv_cancel]
      rw [one_mul]
      simp
      rfl
    .
      intro b hb
      simp only [Finset.mem_singleton] at hb
      simp only [mul_eq_zero]
      right
      apply Pi.single_eq_of_ne
      apply_fun (fun x => s⁻¹ * x)
      simp
      apply_fun (fun x => (x * (Additive.toMul b)) )
      simp
      rw [eq_comm]
      unfold opAdd at hb
      apply_fun Additive.ofMul
      simp
      apply_fun (fun x => x + b)
      simp only []
      rw [add_assoc]
      simp
      exact hb
  .
    apply conv_exists_fin_supp
    right
    simp

lemma f_conv_delta_helper (f: G → ℝ) (s: G): (Conv  f (delta s)) = fun g => f (s⁻¹ * g) := by
  funext g
  exact f_conv_delta f g s

lemma f_mul_mu_summable (f: G → ℝ) (g: G) (s: G):
  Summable fun a ↦
    (f ((Additive.toMul a))) * (if s = ((((Additive.toMul a))⁻¹ * g)) then 1 else 0) := by
  apply summable_of_finite_support
  simp only [one_div, Function.support_mul, Function.support_inv]
  apply Set.Finite.inter_of_right
  apply Set.Finite.subset (s := {(opAdd (g * s⁻¹))})
  . simp
  . intro a ha
    simp at ha
    simp [opAdd]
    rw [ha]
    simp


lemma mu_finsupp: (mu ).support.Finite := by
  simp [mu]
  rw [Function.support_const_smul_of_ne_zero]
  .
    apply Set.Finite.subset (s := ⋃ i ∈ S, Function.support (Pi.single i (1 : ℝ)))
    .
      simp
      exact Set.toFinite (⋃ i ∈ S, {i})
    .
      conv =>
        lhs
        arg 1
        equals fun (x: G) => ∑ s ∈ S, Pi.single s (1 : ℝ) x =>
          funext a
          simp
      apply Finset.support_sum (s := S) (f := fun i => Pi.single i (1: ℝ))
  . simp
    have foo := hS
    simp at foo
    exact Finset.nonempty_iff_ne_empty.mp foo

#print axioms mu_finsupp
-- Proposition 3.12, item 2, in Vikman
lemma f_conv_mu (f: G → ℝ): (Conv  f (mu )) = fun g => ((1 : ℝ) / (#(S) : ℝ)) * ∑ s ∈ S, f (s * g) := by
  funext g
  rw [conv_eq_sum]
  .

    dsimp [mu]
    simp_rw [← mul_assoc]
    conv =>
      lhs
      arg 1
      intro a
      rhs
      equals (∑ s ∈ S, (Pi.single s (1 : ℝ) ((g * (Additive.toMul a)⁻¹)))) =>
        simp

    simp_rw [Finset.mul_sum]
    rw [Summable.tsum_finsetSum]
    .
      --rw [Finset.sum_comm]
      have delta_conv := f_conv_delta  f g
      conv at delta_conv =>
        intro x
        rw [conv_eq_sum (by
          apply conv_exists_fin_supp
          right
          simp
        )]

      simp_rw [mul_comm, mul_assoc]
      --simp_rw [← mul_tsum]
      conv =>
        lhs
        rhs
        intro x
        arg 1
        intro b
        rw [mul_comm]
        rw [mul_assoc]
      simp [delta] at delta_conv
      conv at delta_conv =>
        intro x
        lhs
        arg 1
        intro a
        rw [mul_comm]
      conv =>
        lhs
        rhs
        intro x
        rw [Summable.tsum_mul_left (hf := by (
          simp [Pi.single_apply]
          apply summable_of_finite_support
          apply Set.Finite.subset (s := {(opAdd (   x⁻¹ * g  ))})
          . simp
          . intro z hz
            simp
            simp at hz
            rw [← hz.1]
            simp
          --apply f_mul_mu_summable
        ))]
        rw [delta_conv x]

      simp
      rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
      rw [mul_comm]
      simp
      left
      conv =>
        lhs
        arg 1
        equals S⁻¹ =>
          exact S_eq_Sinv
      simp
    .
      intro s hs
      by_cases card_zero: #(S) = 0
      .
        simp [card_zero]
        unfold Summable
        use 0
        exact hasSum_zero
      .
        conv =>
          arg 1
          intro a
          rw [mul_assoc, mul_comm, mul_assoc]
        rw [summable_mul_left_iff]
        .
          -- TODO - deduplicate this
          simp [Pi.single_apply]
          apply summable_of_finite_support
          apply Set.Finite.subset (s := {(opAdd (s⁻¹ * g ))})
          . simp
          . intro z hz
            simp
            simp at hz
            rw [← hz.1]
            simp
          --apply f_mul_mu_summable
        .
          simp [card_zero]
  . apply conv_exists_fin_supp
    right
    apply mu_finsupp


-- Copied from https://github.com/leanprover/lean4/blob/6741444a63eec253a7eae7a83f1beb3de015023d/src/Init/Data/List/OfFn.lean#L81
theorem ofFn_succ_last (α: Type*) {n} {f : Fin (n + 1) → α} :
    List.ofFn f = (List.ofFn fun i => f i.castSucc) ++ [f (Fin.last n)] := by
  induction n with
  | zero => simp [List.ofFn_succ]
  | succ n ih =>
    rw [List.ofFn_succ]
    conv => rhs; rw [List.ofFn_succ]
    rw [ih]
    simp


lemma list_prod_eq {T : Type*} [Mul T] [One T] (f g: List T) (hfg: f = g): f.prod = g.prod := by
  rw [hfg]

lemma list_unattach_eq {T : Type*}  {p : T → Prop} (f g : List { x : T // p x }) (h: f = g): f.unattach = g.unattach := by
  rw [h]

-- The expression 'Σ s_1, ..., s_n ∈ S, f(s_1 * ... * s_n)'
-- This is a sum over all n-tuples of elements in S, where each term in is f (s_1 * ... * s_n)
-- TODO - is there aless horrible way to write in in mathlib?
def NTupleSum (n: ℕ) (f: G → ℝ): ℝ := ∑ s : (Fin n → S), f ((List.ofFn s).unattach.prod)
--∑ s ∈ (Finset.pi (Finset.range (n + 1))) (fun _ => S), f (List.ofFn (n := n + 1) (fun m => s m.val (by simp))).prod


lemma mu_conv_finsupp (m: ℕ): (muConv  m).support.Finite := by
  induction m with
  | zero =>
    simp [muConv]
    apply mu_finsupp
  | succ n ih =>
    unfold muConv
    rw [Function.iterate_succ_apply']

    --let other := (fun (g:  Additive Gᵐᵒᵖ) => (g))
    conv =>
      arg 1
      arg 1
      rw [conv_eq_sum' (by
        apply conv_exists_fin_supp
        right
        apply mu_finsupp
      )]




      intro g
      rw [tsum_eq_sum (s := (Finset.image Additive.ofMul (ih).toFinset)) (by
        intro a ha
        simp at ha
        simp
        unfold muConv at ha
        left
        have foo := ha (a.toMul)
        simp at foo
        exact foo
      )]


    apply Set.Finite.subset (ht := Finset.support_sum _ _)
    .

      simp [-Function.mem_support]
      apply Set.Finite.biUnion'
      . exact ih
      .
        intro i hi
        apply Set.Finite.inter_of_right
        apply Set.Finite.of_injOn (f := fun x => x * i⁻¹) (t := (mu_finsupp ).toFinset)
        .
          intro x hx
          simp at hx
          simp
          exact hx
        .
          intro y hy z hz
          simp
        . simp
          apply (mu_finsupp )






    -- simp_rw [tsum_eq_sum]

    -- simp_rw [conv_eq_sum]
    -- rw [conv_eq_sum]

    -- nth_rw 3 [mu]
    -- apply Finite.support_conv
    -- exact ih

-- Proposition 3.12, item 3, in Vikman
-- The 'm + 1' terms are due to the fact that 'muConv 0' still applies mu once (without any convolution)
theorem mu_conv_eq_sum (m: ℕ): muConv m = fun g => (((1 : ℝ) / (#(S) : ℝ)) ^ (m + 1)) * (NTupleSum  (m + 1) (delta g))  := by
  induction m with
  | zero =>
    funext g
    simp [muConv, NTupleSum, mu, delta, Pi.single, Function.update]
    by_cases g_in_s: g ∈ S
    .
      simp [g_in_s]
      conv =>
        rhs
        rhs
        rhs
        rhs
        equals {fun (a : Fin 1) => ⟨g, g_in_s⟩} =>
          ext a
          simp
          refine ⟨?_, ?_⟩
          . intro a_zero_eq
            ext x
            simp
            have x_eq_zero: x = 0 := by
              exact Fin.fin_one_eq_zero x
            rw [x_eq_zero]
            exact a_zero_eq
          . intro a_eq
            simp [a_eq]
      simp
    .
      simp [g_in_s]
      right
      by_contra this
      .
        simp at this
        obtain ⟨x, hx⟩ := this
        rw [← hx] at g_in_s
        simp at g_in_s
  | succ n ih =>
    unfold muConv
    rw [Function.iterate_succ_apply']
    nth_rw 3 [mu]
    funext g
    nth_rw 1 [conv_eq_sum]
    simp [-Finset.sum_pi_single]
    simp_rw [mul_comm]
    simp_rw [mul_assoc]
    rw [Summable.tsum_mul_left]
    simp_rw [Finset.sum_mul]
    rw [Summable.tsum_finsetSum]
    .
      conv =>
        lhs
        rhs
        arg 2
        intro x
        equals (Conv (muConv n) (delta x) ) g =>
          rw [conv_eq_sum]
          .
            unfold muConv
            unfold delta
            simp_rw [mul_comm]
          .
            apply conv_exists_fin_supp
            right
            simp [delta]



      simp_rw [f_conv_delta]
      simp_rw [ih]
      rw [← Finset.mul_sum]
      conv =>
        lhs
        rhs
        rhs
        arg 2
        intro s
        simp only [NTupleSum]

      rw [← mul_assoc]
      conv =>
        lhs
        lhs
        simp
        equals (((#S) : ℝ) ^ (n + 1 + 1))⁻¹ =>
          field_simp
          nth_rw 2 [pow_succ]
          simp
          rw [mul_comm]
      simp only [mul_eq_mul_left_iff, inv_eq_zero, ne_eq, Nat.add_eq_zero, one_ne_zero, and_false,
        and_self, not_false_eq_true, pow_eq_zero_iff, Nat.cast_eq_zero, Finset.card_eq_zero]
      left
      rw [← Finset.sum_attach]
      rw [← Finset.sum_product']
      apply Fintype.sum_bijective (e := fun (x) => (fun (i: Fin (n + 1 + 1)) => if hi: i.val = 0 then x.fst else x.snd ⟨i - 1, by omega⟩))
      .
        refine ⟨?_, ?_⟩
        .
          intro a b hab
          simp at hab
          ext p
          .
            have fst_eq := congrFun hab (⟨0, by omega⟩)
            simp at fst_eq
            rw [fst_eq]

          .
            have p_lt_n_plus := p.prop
            have p_val_neq: p.val ≠ n + 1 := by omega

            have cast_succ_ne: p.castSucc.val ≠ n + 1 := by
              simp
              omega

            have snd_eq := congrFun hab (⟨p + 1, by omega⟩)
            by_cases p_eq_zero: p = 0
            .
              simp [p_eq_zero] at snd_eq
              rw [p_eq_zero]
              rw [snd_eq]
            .
              simp [p_eq_zero] at snd_eq
              rw [snd_eq]
        .
          intro f
          use ((f (⟨0, by omega⟩)), fun i => f (⟨i + 1, by omega⟩))
          funext i
          simp
          by_cases i_eq_zero: i = 0
          . simp [i_eq_zero]
          .
            simp [i_eq_zero]
            have i_val_neq_zero: i.val ≠ 0 := by
              simp [i_eq_zero]
            have one_le_i: 1 ≤ i.val := by omega
            simp [Nat.sub_add_cancel one_le_i]
      .
        intro x
        simp only [delta]
        rw [Pi.single_apply]
        rw [Pi.single_apply]


        split_ifs
        .
          rename _ => hi
          simp [hi]
        .
          rename_i g_eq g_mul_neq
          apply_fun (fun y =>  (x.fst.val) * y ) at g_eq
          rw [← mul_assoc] at g_eq
          simp at g_eq
          rw [← g_eq] at g_mul_neq
          rw [List.ofFn_succ] at g_mul_neq
          --rw [ofFn_fir] at g_mul_neq
          norm_cast at g_mul_neq
          conv at g_mul_neq =>
            arg 1
            lhs
            simp


          contradiction
        . rename_i g_mul_neq g_eq

          simp [List.ofFn_succ] at g_eq
          rw [← g_eq] at g_mul_neq
          simp at g_mul_neq
        . rfl
    . intro s hs
      simp [Pi.single_apply]
      rw [← summable_norm_iff]
      apply Summable.of_nonneg_of_le (f := fun a => ‖(fun f ↦ Conv f mu)^[n] mu ((Additive.toMul a))‖)
      .
        intro x
        simp
      . intro x
        split_ifs
        . rfl
        . simp
      .
        rw [summable_norm_iff]
        have conv_finsupp := mu_conv_finsupp  n
        unfold muConv at conv_finsupp

        apply summable_of_finite_support
        apply Set.Finite.of_injOn (f := fun a => ( (Additive.toMul a))) (ht := conv_finsupp)
        .
          intro a ha
          exact ha
        . intro a ha b hb
          simp
    -- TODO - deduplicate this with the above goal
    .
      simp [Pi.single_apply]
      rw [← summable_norm_iff]
      apply Summable.of_nonneg_of_le (f := fun a => ‖(fun f ↦ Conv f mu)^[n] mu ((Additive.toMul a))‖)
      .
        intro x
        simp
      . intro x
        split_ifs
        . rfl
        . simp
      .
        rw [summable_norm_iff]
        have conv_finsupp := mu_conv_finsupp  n
        unfold muConv at conv_finsupp

        apply summable_of_finite_support
        apply Set.Finite.of_injOn (f := fun a => ( (Additive.toMul a))) (ht := conv_finsupp)
        .
          intro a ha
          exact ha
        . intro a ha b hb
          simp
    .
      apply conv_exists_fin_supp
      right
      simp [delta]
      apply Set.Finite.subset (ht := Function.support_const_smul_subset _ _)
      have supp_sum := Finset.support_sum (s := S) (f := fun s => Pi.single s (1: ℝ))
      conv =>
        arg 1
        arg 1
        equals fun x => ∑ s ∈ S, Pi.single s (1 : ℝ) x =>
          funext a
          simp

      apply Set.Finite.subset (ht := supp_sum)
      simp
      exact Set.toFinite (⋃ i ∈ S, {i})

lemma lintegral_g_eq_add (f: G → ENNReal): (∫⁻ (g: G), f g) = (∑' (g : G), f g) := by
  rw [MeasureTheory.lintegral_countable']
  simp [MeasureTheory.volume]
  unfold myHaar
  conv =>
    arg 1
    arg 1
    intro a
    rw [MeasureTheory.Measure.haar_singleton]
    simp [MeasureTheory.Measure.haarMeasure_self]
    rw [← mul_singleton_carrier]
    simp [TopologicalSpace.PositiveCompacts.carrier_eq_coe]
    simp [MeasureTheory.Measure.haarMeasure_self]

lemma integral_eq_eq_sum (f: G → ℝ) (hf: Integrable f): (∫ (g: G), f g) = (∑' (g : G), f g) := by
  rw [MeasureTheory.integral_countable']
  .
    simp [MeasureTheory.volume]
    simp_rw [my_haar_eq_count]
    simp
  . apply hf

lemma mu_norm_one (m: ℕ): MeasureTheory.eLpNorm (muConv  m) 1 = 1 := by
  simp [MeasureTheory.eLpNorm, MeasureTheory.eLpNorm']
  rw [lintegral_g_eq_add]
  simp [mu_conv_eq_sum]
  rw [ENNReal.tsum_mul_left]
  simp [NTupleSum, delta]
  conv =>
    lhs
    rhs
    equals ENNReal.ofReal (∑' (i : G), (∑ x : (Fin (m + 1) → { x // x ∈ S }), if (List.ofFn x).unattach.prod = i then 1 else 0 )) =>
      conv =>
        lhs
        arg 1
        intro i
        rw [Real.enorm_of_nonneg (by
          apply Finset.sum_nonneg
          intro x hx
          simp [delta, Pi.single_apply]
          split_ifs
          . simp
          . simp
        )]


      rw [← ENNReal.ofReal_tsum_of_nonneg]
      simp [Pi.single_apply]
      . intro g
        apply Finset.sum_nonneg
        intro i
        simp [Pi.single_apply]
        split_ifs
        . simp
        . simp
      .
        apply summable_sum
        intro i hi
        simp only [Pi.single_apply]
        apply summable_of_finite_support
        apply Set.Finite.subset (s := {(List.ofFn i).unattach.prod})
        . simp
        . intro a ha
          simp
          simp at ha
          rw [ha]
  rw [Summable.tsum_finsetSum]
  .
    conv =>
      lhs
      rhs
      rhs
      arg 2
      intro i
      simp only [eq_comm]
      rw [tsum_ite_eq]
    simp
    rw [Real.enorm_of_nonneg (by
      simp
    )]
    field_simp
    rw [← ENNReal.ofReal_natCast]
    rw [← ENNReal.ofReal_pow]
    rw [← ENNReal.ofReal_mul]
    .
      field_simp
      simp
      apply div_self
      simp
      have foo := hS
      simp at foo
      exact Finset.nonempty_iff_ne_empty.mp foo
    . simp
    . simp
  .
    -- TODO - deduplicate this with the above goal
    intro a ha
    apply summable_of_finite_support
    apply Set.Finite.subset (s := {(List.ofFn a).unattach.prod})
    . simp
    . intro a ha
      simp
      simp at ha
      rw [ha]

-- Defintion 3.14 from Vikman
-- We offset by one to avoid the need to carry around a '0 < n' hypothesis everywgere
noncomputable def f_n (n: ℕ) (g: G): ℝ := ((1: ℝ) / ((n + 1): ℝ)) * ∑ m: Fin (n + 1), muConv  (m.val) g

lemma mu_conv_nonneg (n: ℕ): ∀ g, 0 ≤ muConv  n g := by
  intro g
  induction n with
  | zero =>
    simp [muConv, mu]
    split_ifs
    . simp
    . simp
  | succ n ih =>
    rw [mu_conv_eq_sum]
    apply mul_nonneg
    . simp
    .
      simp [NTupleSum]
      apply Finset.sum_nonneg
      intro i hi
      simp [delta, Pi.single_apply]
      split_ifs
      . simp
      . simp

--set_option pp.analyze true

-- Proposition 3.15.1 from Vikman
theorem f_n_norm_one (n: ℕ): MeasureTheory.eLpNorm (f_n  n) 1 = 1 := by
  unfold f_n
  simp [MeasureTheory.eLpNorm, MeasureTheory.eLpNorm']
  rw [lintegral_g_eq_add]
  rw [ENNReal.tsum_mul_left]
  conv =>
    lhs
    arg 2
    arg 1
    intro g
    equals ∑ m: Fin (n + 1), ‖muConv (↑m) g‖ₑ =>
      rw [Real.enorm_of_nonneg (by
        apply Finset.sum_nonneg
        intro i hi
        apply mu_conv_nonneg
      )]
      rw [ENNReal.ofReal_sum_of_nonneg (by
        intro i hi
        apply mu_conv_nonneg
      )]
      conv =>
        lhs
        arg 2
        intro i
        rw [← Real.enorm_of_nonneg (by
          apply mu_conv_nonneg
        )]

  rw [Summable.tsum_finsetSum]
  .
    have mu_norm := mu_norm_one
    simp [MeasureTheory.eLpNorm, MeasureTheory.eLpNorm'] at mu_norm
    simp_rw [lintegral_g_eq_add] at mu_norm
    simp_rw [mu_norm]
    simp
    norm_cast
    rw [Real.enorm_of_nonneg (by
      simp
      linarith
    )]
    rw [← ENNReal.ofReal_natCast]
    rw [← ENNReal.ofReal_mul]
    .
      field_simp
      simp
    . simp
      linarith
  .
    simp

-- Proposition 3.15.2 from Vikman
theorem f_n_sub_conv (n: ℕ): MeasureTheory.eLpNorm ((f_n  n) - (Conv (f_n  n) (mu ))) 1 ≤ ENNReal.ofReal ((2 : ℝ) / ((n + 1) : ℝ)) := by
  unfold f_n
  conv =>
    lhs
    arg 1


  --rw [f_conv_mu]
  conv =>
    lhs
    arg 1
    arg 1
    equals ((1: ℝ) / (n + 1)) • ∑ m: Fin (n + 1), muConv (↑m) =>
      funext p
      simp
  simp_rw [← smul_eq_mul]
  --simp_rw [← Finset.smul_sum]
  --simp_rw [← smul_assoc]
  --rw [← Pi.smul_def]
  conv =>
    lhs
    arg 1
    rhs
    arg 1
    rw [← Pi.smul_def]



  rw [conv_smul]
  conv =>
    lhs
    arg 1
    rhs
    equals ((1 : ℝ) / ((n + 1) : ℝ)) • (Conv (∑ m: Fin (n + 1), muConv (m)) (mu )) =>
      funext g
      simp
      left
      conv =>
        lhs
        arg 1
        equals ∑ m: Fin (n + 1), muConv  (m) =>
          funext y
          simp

  rw [conv_sum]
  .
    rw [← smul_sub]
    rw [← Finset.sum_sub_distrib]
    conv =>
      lhs
      arg 1
      rhs
      arg 2
      intro x
      rhs
      equals muConv (↑x + 1) =>
        unfold muConv
        rw [Function.iterate_succ_apply']

    conv =>
      lhs
      arg 1
      rhs
      equals -∑ x: Fin (n + 1), ((muConv  (↑x + 1)) - (muConv  (x.val))) =>
        simp


    conv =>
      lhs
      arg 1
      rhs
      rhs
      equals (muConv (n + 1)) - muConv (0) =>
        induction n with
        | zero =>
          simp
          group

        | succ y iy =>
          rw [Finset.sum_fin_eq_sum_range]
          rw [Finset.sum_range_succ_comm]
          rw [Finset.sum_fin_eq_sum_range] at iy
          simp at iy
          simp
          conv =>
            lhs
            rhs
            rw [Finset.sum_congr (s₂ := Finset.range (y + 1)) rfl (g := fun x => if x < y + 1 then muConv (x + 1) - muConv (x) else 0) (by
              intro x hx
              simp
              simp at hx
              split_ifs
              . simp
              . omega
            )]



          rw [iy]
          simp

    simp
    nth_rw 1 [muConv]
    simp
    calc
      _ ≤ ‖((n + 1): ℝ)⁻¹‖ₑ * MeasureTheory.eLpNorm ((mu - muConv (n + 1))) 1 MeasureTheory.volume := by
        apply MeasureTheory.eLpNorm_const_smul_le
      _ ≤ ‖((n + 1): ℝ)⁻¹‖ₑ * (MeasureTheory.eLpNorm ((mu)) 1 MeasureTheory.volume + (MeasureTheory.eLpNorm ((muConv (n + 1))) 1 MeasureTheory.volume)) := by
        have sub_le := MeasureTheory.eLpNorm_sub_le (p := 1) (f := mu ) (g := muConv  (n + 1)) (μ := MeasureTheory.volume) ?_ ?_ (by simp)
        .
          apply mul_le_mul_left' sub_le
        . apply MeasureTheory.AEStronglyMeasurable.of_discrete
        . apply MeasureTheory.AEStronglyMeasurable.of_discrete
      _ ≤ ENNReal.ofReal ((2: ℝ) / ((n + 1): ℝ)) := by
        rw [mu_norm_one]
        have mu_single_norm := mu_norm_one  0
        simp [muConv] at mu_single_norm
        rw [mu_single_norm]
        field_simp
        norm_cast
        rw [Real.enorm_of_nonneg (by
          simp
          linarith
        )]
        rw [← ENNReal.ofReal_natCast]
        rw [← ENNReal.ofReal_mul]
        simp
        rw [mul_comm]
        field_simp
        simp
        positivity
  . exact mu_finsupp


  -- rw [conv_const_mul]
#print axioms mu_conv_eq_sum
#print axioms f_n_norm_one
#print axioms f_n_sub_conv


noncomputable def conv_mu_lp2 (f: (MeasureTheory.Lp ℝ 2 (MeasureTheory.volume (α := G)))): (MeasureTheory.Lp ℝ 2 (MeasureTheory.volume (α := G))) := MeasureTheory.MemLp.toLp (Conv f (mu )) (by
  rw [MeasureTheory.MemLp]
  refine ⟨MeasureTheory.AEStronglyMeasurable.of_discrete, ?_⟩
  simp [MeasureTheory.eLpNorm, MeasureTheory.eLpNorm']
  rw [f_conv_mu]
  --apply ENNReal.rpow_lt_top_of_nonneg
  --. simp
  --.
  simp_rw [Finset.mul_sum]
  --  (1 : ℝ) / (#(S) : ℝ) * f (a * s)
  have other := MeasureTheory.memLp_finset_sum (μ := MeasureTheory.volume (α := G)) (s := S) (p := 2) (f := fun s a => ((1 : ℝ) / (#(S) : ℝ)) * f (s * a)) (by
    intro s hs
    simp
    apply MeasureTheory.MemLp.const_mul
    rw [← Function.comp_def]
    apply MeasureTheory.MemLp.comp_of_map
    .
      simp [MeasureTheory.volume]
      simp_rw [my_haar_eq_count]
      rw [MeasureTheory.Measure.IsMulLeftInvariant.map_mul_left_eq_self s]
      have mem_f := Lp.memLp f
      simp [volume, my_haar_eq_count] at mem_f
      exact mem_f
    . apply AEMeasurable.of_discrete
  )
  have sum_norm := other.2
  simp [eLpNorm, eLpNorm'] at sum_norm
  field_simp at sum_norm
  field_simp
  exact sum_norm
)

instance volume_finite_compact: IsFiniteMeasureOnCompacts (volume (α := G)) := by
  simp [volume]
  rw [my_haar_eq_count]
  exact {
    lt_top_of_isCompact := by
      intro k hk
      have finite := IsCompact.finite hk (by infer_instance)
      exact Measure.count_apply_lt_top.mpr finite
  }

lemma finsupp_lp_top (f: G → ℝ) (hf: f.support.Finite) (p: ENNReal): MeasureTheory.MemLp f p (Measure.count) := by
  rw [← my_haar_eq_count]
  apply Continuous.memLp_of_hasCompactSupport
  . apply continuous_of_discreteTopology
  .
    simp [HasCompactSupport]
    rw [isCompact_iff_finite]
    simp [tsupport]
    exact hf


-- The convolution of an Lp2 function with a finitely-supported function is LP2
--set_option maxHeartbeats 1000000 in
noncomputable def conv_finsupp_lp2 (f: (MeasureTheory.Lp ℝ 2 (MeasureTheory.volume (α := G)))) (g : G → ℝ) (hg : g.support.Finite): (MeasureTheory.Lp ℝ 2 (MeasureTheory.volume (α := G))) := MeasureTheory.MemLp.toLp (Conv f g) (by
  simp [MemLp]
  refine ⟨by apply AEStronglyMeasurable.of_discrete, ?_⟩
  have norm_bound := ENNReal.eLpNorm_convolution_le_enorm_mul (G := Additive G)  (f := f) (g := g) (E' := ℝ) (E := ℝ) (F := ℝ) (𝕜 := ℝ) (p := 2) (q := 1) (r := 2) (μ := myHaarAddOpp) (ContinuousLinearMap.mul ℝ ℝ)
    (by simp) (by simp) (by simp) (by simp) (by apply AEMeasurable.of_discrete) (by apply AEMeasurable.of_discrete)

  unfold Conv
  eta_reduce
  rw [my_add_haar_eq_count]
  dsimp [volume]
  simp_rw [my_haar_eq_count]
  rw [my_add_haar_eq_count] at norm_bound
  grw [norm_bound]
  apply WithTop.mul_lt_top
  . apply WithTop.mul_lt_top
    . norm_cast
    . rw [← my_add_haar_eq_count]
      apply (MeasureTheory.Lp.memLp f).2
  .
    simp [eLpNorm, eLpNorm']
    rw [MeasureTheory.lintegral_count]
    rw [tsum_eq_sum (s := hg.toFinset) (β := Additive G)]
    . simp_rw [Real.enorm_eq_ofReal_abs]
      rw [← ENNReal.ofReal_sum_of_nonneg]
      . -- TODO - why can't simp' find this?
        apply ENNReal.ofReal_lt_top
      . simp
    . simp
)

-- The Vikman paper defines the Laplace operator as a function ' ∆ : ℓ2(G) → ℓ2(G)'
-- However, we later have '∆ H_n', where H_n is only known to be in L∞
-- We should eventually refactor this, but for we, we just define it twice, once with just plain functions
-- The 'b' is for 'base' (we should come up with a better name)
noncomputable def Laplace_b (f: G → ℝ): G → ℝ := f - (Conv f (mu ))
noncomputable def Laplace (f: (MeasureTheory.Lp ℝ 2 (MeasureTheory.volume (α := G)))): (MeasureTheory.Lp ℝ 2 (MeasureTheory.volume (α := G))) := f - (conv_mu_lp2 f)

lemma conv_neg_left (f g: G → ℝ): Conv (-f) g = -(Conv f g) := by
  conv =>
    pattern -f
    equals (-1 : ℝ) • f => simp

  rw [conv_smul]
  simp

lemma laplace_b_sub (f g: G → ℝ): Laplace_b (f - g) = Laplace_b f - Laplace_b g := by
  simp [Laplace_b]
  nth_rw 3 [sub_eq_add_neg]
  rw [conv_add_left]
  .
    rw [conv_neg_left]
    ring_nf
  .
    apply conv_exists_fin_supp
    right
    apply mu_finsupp
  . apply conv_exists_fin_supp
    right
    apply mu_finsupp

lemma measure_preserving_inv: MeasurePreserving Inv.inv ((MeasureTheory.volume (α := G))) (MeasureTheory.volume (α := G)) := {
  measurable := by
    exact measurable_inv
  map_eq := by
    simp [volume]
    simp [my_haar_eq_count]
}


lemma measure_preserving_unop_tomul: MeasurePreserving (fun (x: Additive (G)) ↦ (Additive.toMul x)) myHaarAddOpp volume := by
  apply MeasureTheory.MeasurePreserving.id

lemma measure_preserving_op_add: MeasurePreserving (fun (x: G) ↦ Additive.ofMul (x)) volume myHaarAddOpp := by
  apply MeasureTheory.MeasurePreserving.id


-- Proposition 3.17.1: "∆ is bounded" from Vikman
-- The paper also proves that the Laplace operator is self-adjoint as part of this step,
-- but we split it out
lemma laplace_bounded (f: (MeasureTheory.Lp ℝ 2 (MeasureTheory.volume (α := G)))): ‖(Laplace  f)‖ₑ ≤ 2 * ‖f‖ₑ := by
  unfold Laplace
  unfold conv_mu_lp2
  simp_rw [f_conv_mu]
  grw [enorm_sub_le]
  --grw [norm_sub_le]
  --grw [norm_add_le]
  --grw [MeasureTheory.eLpNorm_sub_le]
  simp_rw [← smul_eq_mul]
  simp_rw [← Pi.smul_def]
  rw [MeasureTheory.MemLp.toLp_const_smul]
  rw [enorm_smul]
  --rw [MeasureTheory.eLpNorm_const_smul]
  conv =>
    lhs
    rhs
    rhs
    arg 1
    arg 1
    equals ∑ x ∈ S, fun g => f (x • g) =>
      funext g
      simp

  rw [MeasureTheory.Lp.enorm_toLp]
  grw [MeasureTheory.eLpNorm_sum_le]
  simp_rw [← Function.comp_def]
  conv =>
    lhs
    rhs
    rhs
    arg 2
    intro x
    rw [MeasureTheory.eLpNorm_comp_measurePreserving (ν := MeasureTheory.volume) (by
      apply MeasureTheory.AEStronglyMeasurable.of_discrete
    ) (by
    exact {
      measurable := by
        apply Measurable.of_discrete
      map_eq := by
        simp [MeasureTheory.volume]
    }
  )]
  simp
  rw [Real.enorm_of_nonneg (by simp)]
  rw [← mul_assoc]
  rw [← ENNReal.ofReal_natCast]
  rw [← ENNReal.ofReal_mul]
  field_simp
  rw [div_self (by
    have foo := hS
    simp at foo
    simp
    exact Finset.nonempty_iff_ne_empty.mp foo
  )]
  simp
  rw [two_mul]
  . simp
  -- TODO - inline these in the right places
  .
    intro i hs
    apply MeasureTheory.AEStronglyMeasurable.of_discrete
  . simp
  .
    apply MeasureTheory.memLp_finset_sum
    intro s hs
    rw [← Function.comp_def]
    apply MeasureTheory.MemLp.comp_of_map
    .
      simp [MeasureTheory.volume]
      apply MeasureTheory.Lp.memLp f
    . apply AEMeasurable.of_discrete

lemma laplace_bounded' (f: (MeasureTheory.Lp ℝ 2 (MeasureTheory.volume (α := G)))): ‖(Laplace  f)‖ ≤ 2 * ‖f‖ := by
  have bounded := laplace_bounded f
  rw [← ofReal_norm_eq_enorm] at bounded
  rw [← ofReal_norm_eq_enorm] at bounded
  simp_rw [← ENNReal.ofReal_ofNat] at bounded
  rw [← ENNReal.ofReal_mul] at bounded
  .
    rw [ENNReal.ofReal_le_ofReal_iff] at bounded
    . exact bounded
    . simp
  . simp

-- The only measure-zero sets are empty sets, so we can evaluate a MemLp function by evaluating any function
-- from the equivalence class
lemma tolp_apply (f: G → ℝ) {p: ENNReal}  (hf: MeasureTheory.MemLp f p) (g: G): (MeasureTheory.MemLp.toLp f hf) g = f g := by
  have eq_fun := MeasureTheory.AEEqFun.coeFn_mk f (μ := MeasureTheory.volume (α := G)) (by apply MeasureTheory.AEStronglyMeasurable.of_discrete)
  rw [ae_eq_everywhere] at eq_fun
  nth_rw 2 [← eq_fun]
  rfl

lemma tolp_val_apply (f: G → ℝ) {p: ENNReal}  (hf: MeasureTheory.MemLp f p) (g: G): (MeasureTheory.MemLp.toLp f hf).val g = f g := by
  have eq_fun := MeasureTheory.AEEqFun.coeFn_mk f (μ := MeasureTheory.volume (α := G)) (by apply MeasureTheory.AEStronglyMeasurable.of_discrete)
  rw [ae_eq_everywhere] at eq_fun
  nth_rw 2 [← eq_fun]
  rfl

--lemma lp_apply (f: Lp ℝ 2 (μ := volume (α := G)):

instance volume_mul_left_invariant: (volume (α := G)).IsMulLeftInvariant := by
  simp [volume]
  rw [my_haar_eq_count]
  infer_instance

instance volume_mul_right_invariant: (volume (α := G)).IsMulRightInvariant := by
  simp [volume]
  rw [my_haar_eq_count]
  infer_instance


open scoped RealInnerProductSpace
lemma laplace_self_adjoint (f h: (MeasureTheory.Lp ℝ 2 (μ := volume (α := G)))): ⟪f, (Laplace  h)⟫ = ⟪(Laplace  f), h⟫ := by

  simp [MeasureTheory.L2.inner_def]

  have my_eq := ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_sub h (conv_mu_lp2 h))

  --simp only [AddSubgroupClass.coe_sub, ae_eq_everywhere] at my_eq

  -- MeasureTheory.Lp.coeFn_smul


  conv =>
    lhs
    arg 2
    intro g
    rw [mul_comm]
    rw [Laplace]
    rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_sub _ _)]
    simp
    rw [mul_sub]
    rhs
    equals (f g • (conv_mu_lp2 h)) g =>
      rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_smul _ _)]
      simp

  conv =>
    lhs
    arg 2
    intro g
    rhs
    unfold conv_mu_lp2
    rw [← MeasureTheory.MemLp.toLp_const_smul]

  simp_rw [f_conv_mu]
  simp_rw [Pi.smul_def]
  simp
  simp_rw [← mul_assoc]
  simp_rw [mul_comm]
  simp_rw [mul_assoc]
  simp_rw [Finset.mul_sum]


  --simp_rw [← smul_eq_mul]

  conv =>
    lhs
    arg 2
    intro g
    rhs
    arg 1
    rhs
    arg 1
    intro i
    --rw [← Finset.mul_sum]


  simp_rw [tolp_apply]
  rw [integral_sub]
  rw [MeasureTheory.integral_finset_sum]
  conv =>
    lhs
    rhs
    arg 2
    intro s
    rw [← MeasureTheory.integral_mul_left_eq_self (g := s⁻¹)]
    simp
  rw [← MeasureTheory.integral_finset_sum]
  conv =>
    lhs
    rhs
    arg 2
    intro g
    rw [← Finset.mul_sum]
    rw [Finset.sum_bijective (s := S) (t := S) (e := fun s => s⁻¹) (g := fun i => (f (i * g) * (h g))) (by
      refine ⟨?_, ?_⟩
      . exact inv_injective
      . exact inv_surjective
    ) (by
      intro a
      simp
      have foo := hGS.has_inv a
      refine ⟨?_, ?_⟩
      . apply hGS.has_inv a
      . simpa using (hGS.has_inv a⁻¹)
    ) (by
      simp
    )]

  simp_rw [Finset.mul_sum]
  rw [← integral_sub]
  simp_rw [← mul_assoc]
  simp_rw [← Finset.sum_mul]
  simp_rw [mul_comm]
  conv =>
    lhs
    arg 2
    intro a
    rw [mul_comm]
    rw [← mul_sub]



  conv =>
    rhs
    arg 2
    intro g
    rw [Laplace]
    rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_sub _ _)]
    unfold conv_mu_lp2
    simp [f_conv_mu]
    rw [tolp_apply]
    --rw [← MeasureTheory.MemLp.toLp_const_smul]


  simp_rw [Finset.mul_sum]
  .
    have prod_lp1 := MeasureTheory.MemLp.smul (φ := f) (f := h) (p := 2) (q := 2) (r := 1) (μ := volume) (MeasureTheory.Lp.memLp h) (MeasureTheory.Lp.memLp f)
    rw [MeasureTheory.memLp_one_iff_integrable] at prod_lp1
    exact prod_lp1
  .
    apply MeasureTheory.integrable_finset_sum
    intro s hs
    apply MeasureTheory.Integrable.const_mul
    have mem_lp_f_comp: MemLp (f ∘ (fun x => s * x)) 2 := by
      apply MeasureTheory.MemLp.comp_measurePreserving (ν := volume)
      . apply MeasureTheory.Lp.memLp f
      . exact measurePreserving_mul_left volume s

    have prod_lp1 := MeasureTheory.MemLp.smul (f := h) (p := 2) (q := 2) (r := 1) (μ := volume) (MeasureTheory.Lp.memLp h) mem_lp_f_comp
    rw [MeasureTheory.memLp_one_iff_integrable] at prod_lp1
    exact prod_lp1
  .
    intro s hs
    apply MeasureTheory.Integrable.const_mul
    have mem_lp_f_comp: MemLp (f ∘ (fun x => s⁻¹ * x)) 2 := by
      apply MeasureTheory.MemLp.comp_measurePreserving (ν := volume)
      . apply MeasureTheory.Lp.memLp f
      . exact measurePreserving_mul_left volume s⁻¹
    have prod_lp1 := MeasureTheory.MemLp.smul (f := h) (p := 2) (q := 2) (r := 1) (μ := volume) (MeasureTheory.Lp.memLp h) mem_lp_f_comp
    rw [MeasureTheory.memLp_one_iff_integrable] at prod_lp1
    exact prod_lp1
  .
    intro s hs
    apply MeasureTheory.Integrable.const_mul

    have mem_lp_h_comp: MemLp (h ∘ (fun x => s * x)) 2 := by
      apply MeasureTheory.MemLp.comp_measurePreserving (ν := volume)
      . apply MeasureTheory.Lp.memLp h
      . exact measurePreserving_mul_left volume s

    have prod_lp1 := MeasureTheory.MemLp.smul (p := 2) (q := 2) (r := 1) (μ := volume) mem_lp_h_comp (MeasureTheory.Lp.memLp f)
    rw [MeasureTheory.memLp_one_iff_integrable] at prod_lp1
    exact prod_lp1
  .
    have prod_lp1 := MeasureTheory.MemLp.smul (φ := f) (f := h) (p := 2) (q := 2) (r := 1) (μ := volume) (MeasureTheory.Lp.memLp h) (MeasureTheory.Lp.memLp f)
    rw [MeasureTheory.memLp_one_iff_integrable] at prod_lp1
    exact prod_lp1
  .
    apply MeasureTheory.integrable_finset_sum
    intro s hs
    apply MeasureTheory.Integrable.const_mul

    have mem_lp_h_comp: MemLp (h ∘ (fun x => s * x)) 2 := by
      apply MeasureTheory.MemLp.comp_measurePreserving (ν := volume)
      . apply MeasureTheory.Lp.memLp h
      . exact measurePreserving_mul_left volume s

    have prod_lp1 := MeasureTheory.MemLp.smul (p := 2) (q := 2) (r := 1) (μ := volume) mem_lp_h_comp (MeasureTheory.Lp.memLp f)
    rw [MeasureTheory.memLp_one_iff_integrable] at prod_lp1
    exact prod_lp1
    -- rw [mul_sub]
    -- rhs
    -- equals (f g • (conv_mu_lp2 h)) g =>
    --   rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_smul _ _)]
    --   sim

-- Note - this might only true because our measure is equivalen to the counting measure,
-- so a.e. is the same thing as everywhere.
lemma lp_finset_sum {R: Finset G} (f: G → (MeasureTheory.Lp ℝ 2 (μ := volume (α := G)))) (g: G): (∑ s ∈ R, (f s) g) = ((∑ s ∈ R, f s) : (MeasureTheory.Lp ℝ 2 (μ := volume (α := G)))) g := by
  -- have foo := Finset.sum_induction (p := fun (m: (MeasureTheory.Lp ℝ 2 (μ := volume (α := G)))) => m g = (∑ s ∈ S, f s g)) (s := S)
  rw [eq_comm]
  refine Finset.induction_on R ?_ ?_
  .
    simp only [Finset.sum_empty]
    rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_zero _ _ _)]
    simp
  .
    intro a s ha sum_eq
    rw [Finset.sum_insert ha]
    rw [Finset.sum_insert ha]
    rw [← sum_eq]
    rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_add _ _)]
    simp



-- Proposition 3.17.2: "∆ is positive semidefinite" from Vikman
set_option maxHeartbeats 200000 in
lemma laplace_positive_semidefinite (f: (MeasureTheory.Lp ℝ 2 (μ := volume (α := G)))): 0 ≤ ⟪f, (Laplace  f)⟫ := by
  unfold Laplace
  rw [inner_sub_right]
  rw [real_inner_self_eq_norm_sq]
  rw [conv_mu_lp2]
  rw [MeasureTheory.L2.inner_def]
  simp_rw [tolp_apply]
  simp_rw [f_conv_mu]
  simp_rw [← smul_eq_mul]
  simp_rw [inner_smul_right]
  simp_rw [inner_sum]
  rw [integral_const_mul]
  rw [MeasureTheory.integral_finset_sum]

  -- I couldn't figure how to to handle 'toLp (∑ x ∈ S), so I ended up manipulating the integral to avoid dealing with it
  have comp_smul_left (i: G) := MeasureTheory.Lp.coeFn_compMeasurePreserving (g := f) (f := fun a => i * a) (μ := volume) (by
    exact measurePreserving_mul_left volume i
  )
  simp_rw [ae_eq_everywhere] at comp_smul_left
  have congr_comp (i: G) (x: G) := congrFun (comp_smul_left i) x
  simp only [Function.comp_apply] at congr_comp
  simp_rw [smul_eq_mul]
  simp_rw [← congr_comp]
  simp_rw [← MeasureTheory.L2.inner_def]

  let f_eq_coe: f = f := by rfl
  nth_rw 1 [← MeasureTheory.Lp.toLp_coeFn (f := f) (hf := Lp.memLp f)] at f_eq_coe


  conv =>
    rhs
    rhs
    rhs
    arg 2
    intro x
    rw [← f_eq_coe]
    rw [MeasureTheory.Lp.toLp_compMeasurePreserving]
    simp



    --rw [MeasureTheory.Lp.toLp_compMeasurePreserving]

  -- We've now packed everything back up in an inner product -
  -- we no longer need to deal with commuting toLp and Finset.sum


  --simp [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_compMeasurePreserving _ _)]

  --rw [← MeasureTheory.L2.inner_def]


  -- have comp_mul_mem_lp (i: G) (f: MeasureTheory.Lp ℝ 2 (μ := volume)): MemLp (f ∘ (fun x => i * x)) 2 (μ := volume) := by
  --   apply MeasureTheory.MemLp.comp_measurePreserving (ν := volume)
  --   . apply MeasureTheory.Lp.memLp f
  --   . exact measurePreserving_mul_left volume i


  -- conv =>
  --   rhs
  --   rhs
  --   rhs
  --   arg 2
  --   equals ∑ x ∈ S, MemLp.toLp (fun i => f (i • x)) (by
  --     apply MeasureTheory.MemLp.comp_measurePreserving (ν := volume)
  --     . apply MeasureTheory.Lp.memLp f
  --     . exact measurePreserving_mul_right volume x
  --   ) =>

  --     apply Lp.ext
  --     rw [ae_eq_everywhere]
  --     funext a
  --     --simp
  --     rw [tolp_apply]
  --     conv =>
  --       rhs
  --     rw [Finsupp.sum_apply'']

  --     rw [eq_comm]
  --     refine Finset.induction_on S ?_ ?_
  --     .
  --       simp only [Finset.sum_empty]
  --       rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_zero _ _ _)]
  --       simp
  --     .
  --       intro a s ha sum_eq
  --       rw [Finset.sum_insert ha]
  --       rw [Finset.sum_insert ha]
  --       rw [← sum_eq]
  --       rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_add _ _)]
  --       simp





  --rw [inner_smul_right]
  --rw [inner_sum]

  let conv_f_delta_lp (i: G) :=  MemLp.toLp (Conv (f) (delta i⁻¹)) (μ := volume) (p := 2) (by
    simp_rw [f_conv_delta_helper]
    apply MeasureTheory.MemLp.comp_measurePreserving (ν := volume)
    . apply MeasureTheory.Lp.memLp f
    . exact measurePreserving_mul_left volume _
  )


  -- conv =>
  --   rhs
  --   rhs
  --   rhs
  --   arg 2
  --   intro i
  --   rhs
  --   equals conv_f_delta_lp i =>
  --     unfold conv_f_delta_lp
  --     simp_rw [f_conv_delta_helper]
  --     simp
    -- arg 1
    -- intro i
    -- rhs
    -- equals fun x => (fun i => (MemLp.toLp _  (comp_mul_mem_lp i f)) x) i =>
    --   funext x
    --   simp
    --   rw [tolp_apply]
    --   simp

  have sum_le := Finset.sum_le_sum (g := fun i => ‖f‖ * ‖conv_f_delta_lp i‖) (f := fun i => ⟪f, conv_f_delta_lp i⟫) (s := S) (by
    intro s hs
    simp
    have foo := norm_inner_le_norm (x := f) (y := conv_f_delta_lp s) (𝕜 := ℝ)
    rw [Real.norm_eq_abs] at foo
    exact real_inner_le_norm f (conv_f_delta_lp s)
  )
  rw [← ge_iff_le]
  conv =>
    lhs
    rhs
    rhs
    arg 2
    intro x
    rhs
    equals conv_f_delta_lp x =>
      apply Lp.ext
      rw [ae_eq_everywhere]
      funext g
      rw [tolp_apply]
      simp [conv_f_delta_lp]
      rw [tolp_apply]
      rw [f_conv_delta]
      simp


  calc
    _ ≥ ‖f‖ ^ 2 - 1 / ↑(#S) * ∑ i ∈ S, ‖f‖ * ‖conv_f_delta_lp i‖ := by

      apply sub_le_sub_left
      simp
      rw [mul_le_mul_left]
      .
        exact sum_le
      . simpa using hS
    _ ≥ 0 := by
      unfold conv_f_delta_lp
      simp_rw [f_conv_delta_helper]
      conv =>
        lhs
        rhs
        rhs
        arg 2
        intro x
        rhs
        equals ‖f‖ =>
          simp
          rw [← Function.comp_def]
          rw [MeasureTheory.eLpNorm_comp_measurePreserving (ν := volume)]
          . simp [norm]
          . apply MeasureTheory.AEStronglyMeasurable.of_discrete
          . exact measurePreserving_mul_left volume x
      simp
      have s_card_ne_zero: (#S : ℝ) ≠ 0 := by
        simp
        have foo := hS
        simp at foo
        exact Finset.nonempty_iff_ne_empty.mp foo

      rw [← mul_assoc]
      simp [s_card_ne_zero]
      rw [pow_two]
  .
    intro s hs
    simp

    have mem_lp_h_comp: MemLp (f ∘ (fun x => s * x)) 2 := by
      apply MeasureTheory.MemLp.comp_measurePreserving (ν := volume)
      . apply MeasureTheory.Lp.memLp f
      . exact measurePreserving_mul_left volume s

    have prod_lp1 := MeasureTheory.MemLp.smul (p := 2) (q := 2) (r := 1) (μ := volume) (MeasureTheory.Lp.memLp f) mem_lp_h_comp
    rw [MeasureTheory.memLp_one_iff_integrable] at prod_lp1
    exact prod_lp1



noncomputable def Laplace_linear: (MeasureTheory.Lp ℝ 2 (μ := volume (α := G))) →ₗ[ℝ] (MeasureTheory.Lp ℝ 2 (μ := volume (α := G))) := {
  toFun := Laplace
  map_add' := by
    intro x y
    simp [Laplace]
    simp [conv_mu_lp2]
    have coe_add := MeasureTheory.Lp.coeFn_add x y
    rw [ae_eq_everywhere] at coe_add
    norm_cast
    simp_rw [coe_add]
    conv =>
      pattern Conv _ _
      rw [conv_add_left (by
        apply conv_exists_fin_supp
        right
        apply mu_finsupp
      ) (by
        apply conv_exists_fin_supp
        right
        apply mu_finsupp
      )]

    rw [MeasureTheory.MemLp.toLp_add]
    . abel
    .
      have foo := MeasureTheory.Lp.memLp (conv_mu_lp2 x)
      simp [conv_mu_lp2] at foo
      rw [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)] at foo
      exact foo
    . have foo := MeasureTheory.Lp.memLp (conv_mu_lp2 y)
      simp [conv_mu_lp2] at foo
      rw [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)] at foo
      exact foo
  map_smul' := by
    intro c f
    simp [Laplace, conv_mu_lp2]
    have smul_ae := MeasureTheory.Lp.coeFn_smul c f
    rw [ae_eq_everywhere] at smul_ae
    simp_rw [smul_ae]
    simp_rw [conv_smul]
    rw [MeasureTheory.MemLp.toLp_const_smul]
    rw [smul_sub]
}
-- spectrum.norm_le_norm_mul_of_mem
--lemma laplce_spectrum_real (z: ℂ) (hz: z ∈ spectrum ℂ (Laplace_linear )): z.im = 0 := by
--  sorry

lemma f_n_fin_supp (n: ℕ): (f_n  n).support.Finite := by
  unfold f_n
  simp
  apply Set.Finite.inter_of_right
  apply Set.Finite.subset (hs := ?_) (ht := Finset.support_sum _ _)
  refine Set.Finite.biUnion' ?_ ?_
  . exact Set.toFinite (Membership.mem Finset.univ.val)
  . intro m hm
    apply mu_conv_finsupp

noncomputable def F_n (n : ℕ) := Real.sqrt ∘ (f_n  n)
noncomputable def F_n_lp2 (n : ℕ) := MeasureTheory.MemLp.toLp (F_n  n) (by
  simp [volume]
  rw [my_haar_eq_count]
  apply finsupp_lp_top
  simp [F_n]
  apply Set.Finite.subset (s := (f_n n).support)
  .
    unfold f_n
    apply f_n_fin_supp
  .
    apply Function.support_comp_subset
    simp
) (μ := volume (α := G)) (p := 2)

-- Lemma 3.16 in Vikman

-- The case split statement in Vikman
def f_n_conv_delta_tendsto: Prop :=  ∀ s: S, Filter.Tendsto (fun n: ℕ => MeasureTheory.eLpNorm (f_n n - (Conv (f_n n) (delta s.val))) 1 MeasureTheory.volume) Filter.atTop (nhds 0)

lemma F_n_conv_mu_lim (f_n_limit: f_n_conv_delta_tendsto):
    Filter.Tendsto (fun n => ‖(F_n_lp2 n) - conv_mu_lp2 (F_n_lp2 n)‖ₑ) Filter.atTop (nhds 0) := by



  sorry


noncomputable def laplace_range := LinearMap.range (Laplace_linear )

#synth TopologicalSpace ↥(Lp ℝ 2 volume (α := G))

-- If a harmonic function has a maximum value, then it must be a constant function
-- We state 'f is harmonc' as 'Laplace_b f = 0', as this is the hypothesis we have where we need to call this lemma
-- This is true even if it's a local maximum (considered in terms of the  poitns reached by multiply by S), but
-- we don't need that result yet
lemma harmonic_maximum_implies_const (f: G → ℝ) (hf: Laplace_b  f = 0) (a: G) (h_max: ∀ g: G, f g ≤ f a): f = fun _ => f a := by
  have path_implies_max (l : List S): f (l.unattach.prod * a) = f a := by
    induction l with
    | nil =>
      simp
    | cons s l ih =>
      simp
      simp [Laplace_b, f_conv_mu] at hf
      have f_at_l := congrFun hf (l.unattach.prod * a)
      simp at f_at_l
      rw [sub_eq_zero] at f_at_l
      rw [ih] at f_at_l
      field_simp at f_at_l

      -- TODO - is there a 'Finset.expect' theorem we can use?
     -- rw [← Finset.expect_eq_sum_div_card] at f_at_l
     -- TODO - upstream this to mathlib in some form
      have f_s_eq: ∀ s: S, f a = f (s * (l.unattach.prod * a)) := by
        by_contra!
        simp at this
        obtain ⟨s, s_mem_s, hs⟩ := this
        by_cases val_le_max: f (s * (l.unattach.prod * a)) ≤ f a
        .
          have val_lt_max: f (s * (l.unattach.prod * a)) < f a := by
            exact lt_of_le_of_ne (h_max (↑s * (l.unattach.prod * a))) (id (Ne.symm hs))

          have sum_strict_lt := Finset.sum_lt_sum (f := fun x => f (x * (l.unattach.prod * a))) (g := fun x => f a) (s := S) ?_ ?_
          .
            simp at sum_strict_lt
            rw [mul_comm] at sum_strict_lt
            rw [← div_lt_iff₀] at sum_strict_lt
            .
              apply ne_of_gt at sum_strict_lt
              contradiction
            . simpa using hS
          . intro s hs
            apply h_max
          . use s
        .
          have val_gt := h_max (s * (l.unattach.prod * a))
          simp at val_le_max
          linarith
      specialize f_s_eq s
      rw [f_s_eq]
      rw [mul_assoc]
  ext g

  obtain ⟨l, h_l_prod⟩ := mem_S_prod_list (g * a⁻¹)
  simp [ProdS] at h_l_prod
  specialize path_implies_max l
  rw [h_l_prod] at path_implies_max
  simpa using path_implies_max


lemma harmonic_abs_max_implies_const (f: G → ℝ) (hf: Laplace_b  f = 0) (a: G) (h_max: ∀ g: G, |f g| ≤ |f a|): f = fun _ => f a := by
  by_cases f_a_pos: 0 ≤ f a
  .
    have lt_f_a: ∀ g: G, f g ≤ f a := by
      intro g
      by_cases f_g_pos: 0 ≤ f g
      . specialize h_max g
        rw [abs_eq_self.mpr ?_] at h_max
        rw [abs_eq_self.mpr f_a_pos] at h_max
        . exact h_max
        . exact f_g_pos
      . linarith
    exact harmonic_maximum_implies_const f hf a lt_f_a
  .
    have f_neg_le: ∀ g, (-f) g ≤ (-f) a := by
      intro g
      simp at f_a_pos
      simp
      specialize h_max g
      rw [abs_of_neg f_a_pos] at h_max
      by_cases f_g_pos: 0 ≤ f g
      . rw [abs_of_nonneg f_g_pos] at h_max
        linarith
      . simp at f_g_pos
        rw [abs_of_neg f_g_pos] at h_max
        linarith
    have neg_const := harmonic_maximum_implies_const (-f) ?_ a f_neg_le
    .
      apply_fun (fun h => -h) at neg_const
      simp at neg_const
      rw [Pi.neg_def] at neg_const
      simpa using neg_const
    .
      simp_rw [Laplace_b]
      simp_rw [Laplace_b] at hf
      conv =>
        lhs
        rhs
        arg 1
        equals (-1 : ℝ) • f =>
          simp
      rw [conv_smul]
      simp
      rw [add_comm]
      rw [← sub_eq_add_neg]
      rw [sub_eq_zero]
      rw [sub_eq_zero] at hf
      exact hf.symm


lemma laplace_smul (k: ℝ) (f: (Lp ℝ 2 volume (α := G))): Laplace (k • f) = k • (Laplace f) := by
  simp [Laplace, conv_mu_lp2]
  simp_rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_smul _ _)]
  simp_rw [conv_smul]
  rw [MeasureTheory.MemLp.toLp_const_smul]
  rw [smul_sub]

set_option maxHeartbeats 500000 in
lemma laplace_zero_iff_zero (g: (Lp ℝ 2 volume (α := G))) (eq_zero: Laplace g = 0): g = 0 := by
  by_cases g_has_maximum: ∃ a: G, ∀ b: G, ‖Complex.ofReal (g b)‖ ≤ ‖g a‖
  .
    obtain ⟨a, ha⟩ := g_has_maximum
    have laplace_b_zero: Laplace_b  g = 0 := by
      simp [Laplace, conv_mu_lp2, f_conv_mu] at eq_zero
      simp_rw [Laplace_b, f_conv_mu]
      apply_fun (fun f => f.val.cast) at eq_zero
      rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_sub _ _)] at eq_zero
      rw [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)] at eq_zero
      rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_zero _ _ _)] at eq_zero
      field_simp at eq_zero
      field_simp
      exact eq_zero

    simp [Laplace_b] at laplace_b_zero
    simp [f_conv_mu] at laplace_b_zero
    rw [sub_eq_zero] at laplace_b_zero

    have g_const := harmonic_abs_max_implies_const g (by
      simp [Laplace_b]
      simp [f_conv_mu]
      nth_rw 1 [laplace_b_zero]
      simp
    ) a (by simpa using ha)
    have new_g_const_zero := MeasureTheory.memLp_const_iff_enorm (p := 2) (by simp) (by simp) (c := g a) (μ := volume (α := G)) (by simp)
    rw [← g_const] at new_g_const_zero
    simp [MeasureTheory.Lp.memLp] at new_g_const_zero
    simp [volume, my_haar_eq_count] at new_g_const_zero
    have g_infinity := hGS.g_infinite
    rw [← not_infinite_iff_finite] at new_g_const_zero
    simp [hGS.g_infinite] at new_g_const_zero


    have g_eq_zero: g.val.cast = 0 := by
      rw [g_const]
      rw [new_g_const_zero]
      ext a
      simp

    ext
    rw [ae_eq_everywhere]
    rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_zero _ _ _)]
    exact g_eq_zero
  . rename _ => g_no_maximum
    simp at g_no_maximum
    have integrable_g := MeasureTheory.MemLp.integrable_sq (MeasureTheory.Lp.memLp g)
    simp [Integrable, HasFiniteIntegral] at integrable_g
    obtain ⟨_, integral_lt⟩ := integrable_g
    rw [lintegral_g_eq_add] at integral_lt
    rw [WithTop.lt_top_iff_ne_top] at integral_lt
    by_contra g_ne_zero
    simp at g_ne_zero
    have nonzero_val: ∃ a: G, g a ≠ 0 := by
      rw [MeasureTheory.Lp.ext_iff] at g_ne_zero
      rw [ae_eq_everywhere] at g_ne_zero
      rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_zero _ _ _)] at g_ne_zero
      exact Function.ne_iff.mp g_ne_zero

    obtain ⟨a, ha⟩ := nonzero_val
    have finite_gt := ENNReal.finite_const_le_of_tsum_ne_top integral_lt (ε := ‖|g a|‖ₑ ^ 2) (by
      simpa using ha
    )
    have maximal := Set.Finite.exists_maximalFor (f := fun h => |g h|) _ finite_gt (by
      apply Set.nonempty_of_mem (x := a)
      simp
    )
    obtain ⟨m, m_in_g, hm⟩ := maximal
    simp at m_in_g
    -- Obtain an element greater than the maximum
    obtain ⟨p, hp⟩ := g_no_maximum m
    have p_gt := hm (j := p) ?_ ?_
    .
      have not_g_le := not_lt_of_ge p_gt
      contradiction
    .
      simp
      grw [m_in_g]
      rw [← ENNReal.toReal_le_toReal]
      .
        simp
        rw [sq_le_sq]
        linarith
      . simp
      . simp
    linarith

lemma norm_conv_mu_le  (f: (Lp ℝ 2 volume (α := G))): ‖conv_mu_lp2 f‖ ≤ ‖f‖ := by
  simp [conv_mu_lp2]
  simp [f_conv_mu]
  simp_rw [← smul_eq_mul]
  rw [← Pi.smul_def]
  rw [MeasureTheory.eLpNorm_const_smul]
  -- TODO - deduplicate this with 'laplace_bounded'
  conv =>
    lhs
    rhs
    rhs
    arg 1
    equals ∑ x ∈ S, fun g => f (x • g) =>
      funext g
      simp

  have card_s_ne: (#S : ℝ) ≠ 0 := by
    simp
    have foo := hS
    simp at foo
    exact Finset.nonempty_iff_ne_empty.mp foo

  grw [MeasureTheory.eLpNorm_sum_le]
  simp_rw [← Function.comp_def]
  conv =>
    lhs
    rhs
    rhs
    arg 2
    intro x
    rw [MeasureTheory.eLpNorm_comp_measurePreserving (ν := MeasureTheory.volume) (by
      apply MeasureTheory.AEStronglyMeasurable.of_discrete
    ) (by
    exact {
      measurable := by
        apply Measurable.of_discrete
      map_eq := by
        simp [MeasureTheory.volume]
    }
  )]
  . simp
    field_simp
    rfl
  .
    apply WithTop.mul_ne_top
    .
      rw [Real.enorm_of_nonneg (by simp)]
      apply ENNReal.ofReal_ne_top
    .
      rw [WithTop.sum_ne_top]
      intro s hs
      rw [← Function.comp_def]
      conv =>
        rw [MeasureTheory.eLpNorm_comp_measurePreserving (ν := MeasureTheory.volume) (by
          apply MeasureTheory.AEStronglyMeasurable.of_discrete
        ) (by
        exact {
          measurable := by
            apply Measurable.of_discrete
          map_eq := by
            simp [MeasureTheory.volume]
        }
      )]
      rw [← WithTop.lt_top_iff_ne_top]
      apply (MeasureTheory.Lp.memLp f).2
  . intro s hs
    apply AEStronglyMeasurable.of_discrete
  .
    simp


lemma inner_laplace_zero (f: (Lp ℝ 2 volume (α := G))) (hf: ⟪Laplace f, f⟫ = 0): Laplace f = 0 := by
  have inner_le := real_inner_le_norm (conv_mu_lp2 f) f

  by_cases norm_f_zero: ‖f‖ = 0
  .
    simp at norm_f_zero
    simp [Laplace, conv_mu_lp2]
    simp [f_conv_mu]
    simp_rw [norm_f_zero]
    simp_rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_zero _ _ _)]
    simp
    simp_rw [← Pi.zero_def]
    rw [MeasureTheory.MemLp.toLp_zero]

  simp [Laplace] at hf
  rw [inner_sub_left] at hf
  rw [real_inner_self_eq_norm_sq] at hf
  rw [sub_eq_zero] at hf
  rw [eq_comm] at hf
  rw [pow_two] at hf
  --rw [inner_eq_norm_mul_iff_real] at hf
  rw [hf] at inner_le
  nth_rw 2 [mul_comm] at inner_le
  rw [mul_le_mul_iff_of_pos_left] at inner_le
  have conv_le_f := norm_conv_mu_le f
  have f_norm_eq: ‖f‖ = ‖conv_mu_lp2 f‖ := by
    linarith

  have f_sub_norm := norm_sub_sq_real f (conv_mu_lp2 f)
  rw [real_inner_comm] at f_sub_norm
  rw [hf] at f_sub_norm
  rw [← f_norm_eq] at f_sub_norm
  rw [← pow_two] at f_sub_norm
  group at f_sub_norm
  rw [zpow_two] at f_sub_norm
  rw [mul_self_eq_zero] at f_sub_norm
  simp at f_sub_norm
  simpa [Laplace] using f_sub_norm
  simpa using norm_f_zero

lemma laplace_range_dense: Dense (X := ↥(Lp ℝ 2 volume (α := G))) (laplace_range ) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  rw [Submodule.topologicalClosure_eq_top_iff]
  simp_rw [laplace_range]
  ext g
  rw [Submodule.mem_bot]
  refine ⟨?_, ?_⟩
  .
    intro hg
    simp at hg
    rw [Submodule.mem_orthogonal] at hg
    have inner_laplace_zero: ∀ u: (Lp ℝ 2 volume), ⟪Laplace_linear u, g⟫ = 0 := by
      intro u
      specialize hg (Laplace_linear u)
      simpa using hg

    simp only [Laplace_linear, LinearMap.coe_mk, AddHom.coe_mk] at inner_laplace_zero
    simp_rw [← laplace_self_adjoint] at inner_laplace_zero
    simp at inner_laplace_zero

    have eq_zero:= Dense.eq_zero_of_inner_right (K := ⊤) (E := (Lp ℝ 2 (volume (α := G)))) (𝕜 := ℝ) (by apply dense_univ) (x := (Laplace g))
    simp at eq_zero
    specialize eq_zero inner_laplace_zero
    apply laplace_zero_iff_zero _ eq_zero
  . intro hg
    rw [hg]
    simp




lemma laplace_g_n (n: ℕ) (hn: 0 < n): ∃ g: (Lp ℝ 2 volume (α := G)), ‖Laplace g‖ ≤ (1 : ℝ) / n ∧ ⟪Laplace g, g⟫ = 1 := by
  sorry
  -- This whole proof is completely wrong - it needs to use the spectral theorem

  -- have ball_open: IsOpen (Metric.ball (0 : Lp ℝ 2 volume (α := G)) (1 / n)) := by
  --   exact Metric.isOpen_ball


  -- have punctured_ball_open: IsOpen ((Metric.ball (0 : Lp ℝ 2 volume (α := G)) (1 / n)) \ {0})  := by
  --   apply IsOpen.sdiff
  --   . exact ball_open
  --   .
  --     rw [← Metric.closedBall_zero]
  --     apply Metric.isClosed_closedBall

  -- have dense := laplace_range_dense
  -- rw [dense_iff_inter_open] at dense

  -- let lp_point: (Lp ℝ 2 volume (α := G)) := MemLp.toLp (fun (g: G) => if g = 1 then (1 : ℝ) / ((n + 1)^2) else 0) (by
  --   simp [MemLp]
  --   refine ⟨by apply AEStronglyMeasurable.of_discrete, ?_⟩
  --   simp [eLpNorm, eLpNorm']
  --   rw [lintegral_g_eq_add]
  --   rw [tsum_eq_sum (s := {1})]
  --   . simp
  --     rw [Real.enorm_eq_ofReal_abs]
  --     norm_cast
  --     simp
  --     apply ENNReal.rpow_lt_top_of_nonneg
  --     . simp
  --     .
  --       apply ENNReal.pow_ne_top
  --       apply ENNReal.ofReal_ne_top
  --   . intro b hb
  --     simp at hb
  --     simp [hb]
  -- )

  -- have lp_point_norm: ‖lp_point‖ < (n: ℝ)⁻¹ := by
  --   simp [lp_point, eLpNorm, eLpNorm']
  --   rw [lintegral_g_eq_add]
  --   simp_rw [Real.enorm_eq_ofReal_abs]
  --   conv =>
  --     lhs
  --     arg 1
  --     lhs
  --     arg 1
  --     intro g
  --     rw [← ENNReal.ofReal_pow (by simp)]
  --   rw [tsum_eq_sum (s := {1})]
  --   .
  --     simp
  --     rw [ENNReal.ofReal_rpow_of_nonneg]
  --     rw [ENNReal.toReal_ofReal]
  --     .
  --       rw [← Real.rpow_neg_one]
  --       rw [← Real.rpow_mul]
  --       rw [← Real.rpow_natCast]
  --       rw [← Real.rpow_mul]
  --       rw [← Real.rpow_natCast]
  --       rw [← Real.rpow_mul]
  --       field_simp
  --       simp
  --       rw [Real.rpow_neg]
  --       rw [mul_inv_lt_iff₀']
  --       field_simp
  --       norm_cast
  --       rw [pow_two]
  --       ring
  --       norm_cast
  --       rw [mul_two]
  --       . omega
  --       .
  --         norm_cast
  --         positivity
  --       . norm_cast
  --         omega
  --       . norm_cast
  --         linarith
  --       . norm_cast
  --         positivity
  --       . norm_cast
  --         positivity
  --     . positivity
  --     . positivity
  --     . simp
  --   . intro b hb
  --     simp at hb
  --     simp [hb]

  -- use (Real.sqrt ⟪Laplace lp_point, lp_point⟫)⁻¹ • lp_point
  -- refine ⟨?_, ?_⟩
  -- .
  --   rw [laplace_smul]
  --   rw [norm_smul]
  --   simp only [norm_inv, Real.norm_eq_abs, one_div]
  --   grw [laplace_bounded']
  --   grw [lp_point_norm]
  --   rw [inv_mul_le_iff₀]
  --   .
  --     rw [← Real.norm_eq_abs]
  --     rw [Real.norm_of_nonneg (by apply Real.sqrt_nonneg)]
  --     simp_rw [Laplace]
  --     simp_rw [inner_sub_left, conv_mu_lp2]
  --     simp_rw [f_conv_mu]
  --     sorry
  --     --grw [real_inner_le_norm]
  --   . sorry


  -- -- Show that the punctured open ball is nonempty, so a dense set has a nonempty intersection with it
  -- have mem_ball := dense _ punctured_ball_open (by
  --   simp
  --   use lp_point
  --   simp
  --   refine ⟨?_, ?_⟩
  --   . simp [lp_point, eLpNorm, eLpNorm']
  --     rw [lintegral_g_eq_add]
  --     simp_rw [Real.enorm_eq_ofReal_abs]
  --     conv =>
  --       lhs
  --       arg 1
  --       lhs
  --       arg 1
  --       intro g
  --       rw [← ENNReal.ofReal_pow (by simp)]
  --     rw [tsum_eq_sum (s := {1})]
  --     .
  --       simp
  --       rw [ENNReal.ofReal_rpow_of_nonneg]
  --       rw [ENNReal.toReal_ofReal]
  --       .
  --         rw [← Real.rpow_neg_one]
  --         rw [← Real.rpow_mul]
  --         rw [← Real.rpow_natCast]
  --         rw [← Real.rpow_mul]
  --         rw [← Real.rpow_natCast]
  --         rw [← Real.rpow_mul]
  --         field_simp
  --         simp
  --         rw [Real.rpow_neg]
  --         rw [mul_inv_lt_iff₀']
  --         norm_num
  --         norm_cast
  --         rw [pow_two]
  --         ring
  --         norm_cast
  --         rw [mul_two]
  --         . omega
  --         .
  --           norm_cast
  --           positivity
  --         . norm_cast
  --           simp
  --         . norm_cast
  --           linarith
  --         . norm_cast
  --           positivity
  --         . norm_cast
  --           positivity
  --       . positivity
  --       . positivity
  --       . simp
  --     . intro b hb
  --       simp at hb
  --       simp [hb]
  --   . by_contra!
  --     rw [MeasureTheory.Lp.ext_iff] at this
  --     rw [ae_eq_everywhere] at this
  --     have eval_one := congrFun this (1 : G)
  --     rw [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)] at eval_one
  --     rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_zero _ _ _)] at eval_one
  --     simp at eval_one
  --     linarith
  -- )
  -- simp only [Set.Nonempty] at mem_ball
  -- obtain ⟨g, gh⟩ := mem_ball
  -- simp at gh
  -- have g_norm := gh.1
  -- have g_range := gh.2
  -- simp only [laplace_range] at g_range
  -- simp only [LinearMap.mem_range] at g_range
  -- obtain ⟨a, ha⟩ := g_range
  -- sorry

  -- by_cases inner_laplace_nonneg: 0 ≤ ⟪Laplace a, a⟫
  -- .
  --   --use (Real.sqrt ⟪Laplace a, a⟫)⁻¹ • a
  --   --simp [Laplace_linear] at ha
  --   field_simp at g_norm
  --   refine ⟨?_, ?_⟩
  --   .
  --     rw [laplace_smul]
  --     rw [norm_smul]
  --     simp
  --     rw [norm_eq_sqrt_real_inner]
  --     rw [ha]
  --     rw [← norm_eq_sqrt_real_inner]

  --     simp
  --     rw [inner_smul_left]
  --     rw [inner_smul_right]
  --     field_simp
  --     simp [Laplace]
  --   .
  --     rw [laplace_smul]
  --     rw [inner_smul_left]
  --     rw [inner_smul_right]
  --     field_simp
  --     apply div_self
  --     rw [Real.sqrt_ne_zero]
  --     . by_contra!
  --       apply inner_laplace_zero at this
  --       rw [this] at ha
  --       have g_nonzero := g_norm.2
  --       rw [eq_comm] at ha
  --       contradiction
  --     . exact inner_laplace_nonneg
  -- . sorry


#print axioms laplace_g_n

lemma lp_summable {p: ℕ} (hp: 0 < p) (f: (Lp ℝ p volume (α := G))): Summable (fun g: G => |(f g)|^p) := by
  have f_norm := (MeasureTheory.Lp.memLp f).2
  simp [eLpNorm, eLpNorm'] at f_norm
  have not_le: ¬(p = 0) := by linarith
  simp [not_le] at f_norm
  rw [lintegral_g_eq_add] at f_norm
  rw [WithTop.lt_top_iff_ne_top] at f_norm
  rw [Ne] at f_norm
  rw [ENNReal.rpow_eq_top_iff] at f_norm
  simp at f_norm
  have not_ofreal: ¬((ENNReal.ofReal p).toReal ≤ 0) := by
    simp
    linarith
  simp [not_le] at f_norm
  simp_rw [Real.enorm_eq_ofReal_abs] at f_norm
  conv at f_norm =>
    arg 1
    lhs
    arg 1
    intro g
    rw [← ENNReal.ofReal_pow (by simp)]
  apply ENNReal.summable_toReal at f_norm
  conv at f_norm =>
    arg 1
    intro x
    rw [ENNReal.toReal_ofReal (by
      simp
    )]
  exact f_norm

lemma lp2_summable (f: (Lp ℝ 2 volume (α := G))): Summable (fun g: G => (f g)^2) := by
  conv =>
    arg 1
    intro g
    rw [← sq_abs]
  apply lp_summable (p := 2) (by simp) f

lemma summable_f_mul_translate (f: (Lp ℝ 2 volume (α := G))) (i: G): Summable (fun x => (f x) * (f (i * x))) := by
  have lp_mul := (MeasureTheory.MemLp.mul (φ := f) (f := fun x => f (i * x)) (p := 2) (q := 2) (r := 1) (μ := volume) ?_ ?_).2
  .
    simp [MemLp, eLpNorm, eLpNorm'] at lp_mul
    rw [lintegral_g_eq_add] at lp_mul
    simp [Real.enorm_eq_ofReal_abs] at lp_mul
    simp [← ENNReal.ofReal_mul] at lp_mul
    rw [WithTop.lt_top_iff_ne_top] at lp_mul
    apply ENNReal.summable_toReal at lp_mul
    conv at lp_mul =>
      arg 1
      intro x
      rw [ENNReal.toReal_ofReal (by
        apply mul_nonneg
        . simp
        . simp
      )]
    apply Summable.of_abs
    simp_rw [abs_mul]
    exact lp_mul
  .
    rw [← Function.comp_def]
    apply MeasureTheory.MemLp.comp_measurePreserving (ν := volume)
    . apply MeasureTheory.Lp.memLp f
    . exact measurePreserving_mul_left volume i
  . apply Lp.memLp f


-- Note - this is stated incorrectly in Vikman
-- The RHS should have a squared norm
lemma proposition_3_18 (f: (Lp ℝ 2 volume (α := G))): (∑' g: G, (f g) * (Laplace f) g) = ((2) * (#(S) : ℝ))⁻¹ * ∑ s ∈ S, ‖(f - (conv_finsupp_lp2 f (delta s) (by simp [delta])))‖^2 := by
  simp_rw [Laplace]
  simp_rw [conv_mu_lp2]
  simp_rw [f_conv_mu]
  conv =>
    enter [1, 1, g, 2, 1, 1, 2, 1, g, 2, 2, s]
    rw[ ← inv_inv s]
    rw [← f_conv_delta (s := s⁻¹) (f := f.val.cast)]

  simp_rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_sub _ _)]
  simp only [Pi.sub_apply]
  conv =>
    lhs
    arg 1
    intro g
    lhs
    rw [← inv_mul_cancel_left₀ (a := 2) (by simp) (f g)]



  simp_rw [mul_assoc]
  rw [Summable.tsum_mul_left]
  simp_rw [← mul_assoc]

  conv =>
    lhs
    rhs
    arg 1
    intro g
    rw [mul_sub]
  rw [Summable.tsum_sub]
  have sum_f: ∀ c: ℝ, c = (#(S) : ℝ)⁻¹ * ∑ s ∈ S, c := by
    intro g
    simp
    have card_nonneg: #(S) ≠ 0 := by
      have foo := S_nonempty
      simp
      push_neg
      rw [← Finset.nonempty_iff_ne_empty]
      apply foo
    field_simp
  conv =>
    lhs
    rhs
    lhs
    arg 1
    intro g
    rw [mul_assoc]
    rw [← pow_two]
    rw [sum_f (c := (f g)^2)]

  rw [Summable.tsum_mul_left]
  rw [Summable.tsum_mul_left]
  have f_norm := MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm (p := 2) (by simp) (by simp) (f := f.val.cast) (μ := volume (α := G))
  simp_rw [lintegral_g_eq_add] at f_norm
  simp [enorm] at f_norm
  apply_fun ENNReal.toReal at f_norm
  norm_cast at f_norm
  rw [← ENNReal.toReal_rpow] at f_norm
  rw [ENNReal.tsum_toReal_eq] at f_norm
  simp at f_norm
  apply_fun (fun x => x^2) at f_norm
  nth_rw 2 [← Real.rpow_natCast] at f_norm
  rw [← Real.rpow_mul] at f_norm
  simp at f_norm
  have f_summable := lp_summable (p := 2) (by simp) f
  conv =>
    lhs
    rhs
    lhs
    rhs
    rhs
    rw [Summable.tsum_finsetSum (by
      intro i hi
      apply lp2_summable
    )]
    rw [← f_norm]

  conv =>
    lhs
    rhs
    rhs
    arg 1
    intro b
    rw [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)]
    rw [← mul_assoc]
    rw [mul_comm (2 * _)]
    rw [mul_assoc]
    rw [mul_assoc]
    rw [Finset.mul_sum]
    rw [← mul_assoc]

  rw [Summable.tsum_mul_left]
  rw [Summable.tsum_finsetSum (by
    intro i hi
    simp [f_conv_delta]
    apply summable_f_mul_translate
  )]
  simp_rw [f_conv_delta]
  simp only [inv_inv]
  let f_conv := fun (s: G) => conv_finsupp_lp2 f (delta s) (by
    simp [delta]
  )
  have inner_f_conv := fun (s: G) => MeasureTheory.L2.inner_def (𝕜 := ℝ) (f := f) (g := f_conv s)
  simp [f_conv, conv_finsupp_lp2] at inner_f_conv
  simp_rw [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)] at inner_f_conv
  conv at inner_f_conv =>
    intro a
    rhs
    -- TODO  - deduplicate this with the 'have lp_mul' block above
    rw [MeasureTheory.integral_countable' (by
      simp [f_conv_delta]
      simp [Integrable]
      refine ⟨by apply AEStronglyMeasurable.of_discrete, ?_⟩
      simp [HasFiniteIntegral]
      simp [Real.enorm_eq_ofReal_abs]
      simp [← ENNReal.ofReal_mul]
      rw [lintegral_g_eq_add]
      rw [WithTop.lt_top_iff_ne_top]
      rw [← ENNReal.ofReal_tsum_of_nonneg]
      . apply ENNReal.ofReal_ne_top
      . intro n
        apply mul_nonneg
        . simp
        . simp
      .
        simp_rw [← abs_mul]
        apply Summable.abs
        simp_rw [mul_comm]
        apply summable_f_mul_translate
    )]
  simp [volume, my_haar_eq_count, f_conv_delta] at inner_f_conv
  conv =>
    lhs
    rhs
    rhs
    rhs
    arg 1
    rw [S_eq_Sinv ]

  simp only [Finset.sum_inv_index]
  simp [mul_comm] at inner_f_conv

  simp_rw [← inner_f_conv]
  -- Split '2 * ‖f‖^2 into two copies of ‖f‖^2, and convert one into ‖Conv f delta‖^2
  rw [two_mul]
  conv =>
    lhs
    rhs
    lhs
    lhs
    rhs
    arg 2
    intro s
    rw [← MeasureTheory.eLpNorm_comp_measurePreserving (f := fun x => s⁻¹ * x) (ν := volume) (by apply AEStronglyMeasurable.of_discrete) (by apply measurePreserving_mul_left)]
    -- TODO - why does doing this result in a weird metavariable outside of conv?
    --pattern _ ∘ _
    --equals fun g => f (s⁻¹ * g) =>
    --  funext a
    --  simp



  simp_rw [Function.comp_def]
  simp_rw [← f_conv_delta]
  have card_s_ne: #(S) ≠ 0 := by
    simp
    have foo := S_nonempty
    simp at foo
    exact Finset.nonempty_iff_ne_empty.mp foo
  field_simp

  simp_rw [add_comm]

  conv =>
    rhs
    arg 2
    intro s
    rw [norm_sub_sq_real]


  rw [Finset.sum_add_distrib]
  rw [Finset.sum_sub_distrib]
  simp [MeasureTheory.Lp.norm_def]
  simp_rw [MeasureTheory.L2.inner_def, conv_finsupp_lp2]
  field_simp
  rw [sub_add]
  rw [← add_sub]
  rw [sub_sub_eq_add_sub]
  rw [add_sub_assoc]
  rw [mul_comm]
  rw [add_left_cancel_iff]


  simp_rw [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)]
  eta_reduce
  rw [Finset.mul_sum]
  . apply summable_sum
    intro s hs
    simp_rw [f_conv_delta]
    apply summable_f_mul_translate
  .
    apply tsum_nonneg
    intro g
    apply sq_nonneg
  . simp
  . apply summable_sum
    intro s hs
    apply lp2_summable
  .
    apply Summable.mul_left
    apply summable_sum
    intro s hs
    apply lp2_summable
  . simp_rw [mul_assoc]
    apply Summable.mul_left
    simp_rw [← pow_two]
    apply lp2_summable
  . simp_rw [mul_assoc]
    apply Summable.mul_left
    rw [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)]
    simp_rw [← mul_assoc]
    simp_rw [Finset.mul_sum]
    apply summable_sum
    intro s hs
    simp_rw [f_conv_delta]
    simp_rw [mul_comm]
    simp_rw [mul_assoc]
    apply Summable.mul_left
    apply summable_f_mul_translate
  .
    apply Summable.mul_left
    rw [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)]
    simp_rw [mul_sub]
    apply Summable.sub
    . simp_rw [← pow_two]
      apply lp2_summable
    .
      simp_rw [← mul_assoc]
      simp_rw [Finset.mul_sum]
      apply summable_sum
      intro s hs
      simp_rw [f_conv_delta]
      simp_rw [mul_comm]
      simp_rw [mul_assoc]
      apply Summable.mul_left
      apply summable_f_mul_translate

noncomputable def G_n (n: ℕ) (hn: 0 < n) := Classical.choose (laplace_g_n n hn )

lemma g_n_laplace_enorm_le (n: ℕ) (hn: 0 < n): ‖Laplace (G_n n hn)‖ₑ ≤ 1/n := by
  have g_n_prop := (laplace_g_n n hn).choose_spec
  sorry

lemma g_n_laplace_norm_le (n: ℕ) (hn: 0 < n): ‖Laplace (G_n n hn)‖ ≤ 1/n := by
  have g_n_prop := (laplace_g_n n hn).choose_spec
  exact g_n_prop.1

lemma g_n_conv_norm (n: ℕ) (hn: 0 < n): ⟪Laplace (G_n n hn), (G_n n hn)⟫ = 1 := by
  have g_n_prop := (laplace_g_n n hn).choose_spec
  exact g_n_prop.2

lemma g_n_ne_zero (n: ℕ) (hn: 0 < n): G_n n hn ≠ 0 := by
  simp
  by_contra!
  have g_n_prop := (laplace_g_n n hn).choose_spec
  simp [G_n] at this
  simp [this] at g_n_prop


lemma g_sub_norm_gt (n: ℕ): ∃ s ∈ S, ‖(G_n (n + 1) (by simp)) - (conv_finsupp_lp2 (G_n (n + 1) (by simp)) (delta s) (by simp [delta]))‖^2 > 1 := by
  by_contra!
  have card_le := Finset.sum_le_card_nsmul S _ (1 : ℝ) this
  have sum_norm := (proposition_3_18 (G_n (n + 1) (by simp)) )
  have g_inner_laplace := MeasureTheory.L2.inner_def (Laplace (G_n (n + 1) (by simp))) (G_n (n + 1) (by simp)) (𝕜 := ℝ) (α := G)
  have g_n_prop := (Classical.choose_spec (laplace_g_n (n + 1) (by simp))).2
  rw [integral_eq_eq_sum] at g_inner_laplace
  .
    simp at g_inner_laplace
    simp_rw [← g_inner_laplace] at sum_norm
    nth_rw 1 [G_n] at sum_norm
    nth_rw 1 [G_n] at sum_norm
    rw [g_n_prop] at sum_norm
    rw [eq_inv_mul_iff_mul_eq₀] at sum_norm
    simp at sum_norm
    rw [← sum_norm] at card_le
    simp at card_le
    rw [mul_le_iff_le_one_left] at card_le
    . norm_num at card_le
    . simp
      have foo := S_nonempty
      grind
    .
      simp
      have foo := S_nonempty
      grind

  .
    rw [MeasureTheory.L2.inner_def] at g_n_prop
    apply MeasureTheory.integrable_of_integral_eq_one at g_n_prop
    exact g_n_prop






  -- field_simp at sum_norm
  -- sorry

#print sorries proposition_3_18
#print axioms proposition_3_18
#print axioms laplace_range_dense


lemma g_sub_norm_single_s: ∃ s ∈ S, { n: ℕ | ‖(G_n (n + 1) (by simp)) - (conv_finsupp_lp2 (G_n (n + 1) (by simp)) (delta s) (by simp [delta]))‖^2 > 1 }.Infinite := by

  have frequent := Filter.Frequently.of_forall (f := Filter.atTop) g_sub_norm_gt
  simp at frequent
  obtain ⟨s, s_mem, s_frequently⟩ := frequent
  rw [Nat.frequently_atTop_iff_infinite] at s_frequently
  use s
  refine ⟨s_mem, ?_⟩
  simpa using s_frequently

lemma f_n_nonneg: ∀ n: ℕ, ∀ g: G,  0 ≤ f_n n g := by
  intro n g
  simp [f_n]
  apply mul_nonneg
  . positivity
  . apply Finset.sum_nonneg
    intro i hi
    apply mu_conv_nonneg

lemma F_n_norm_eq_one: ∀ n, MeasureTheory.eLpNorm (F_n n) 2 MeasureTheory.volume (α := G) = 1 := by
  simp [eLpNorm, eLpNorm', lintegral_g_eq_add]
  simp [F_n, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow]

  intro n
  simp [f_n_nonneg]
  have norm_one := f_n_norm_one (n)
  simp [eLpNorm, eLpNorm', lintegral_g_eq_add] at norm_one
  simp_rw [Real.enorm_eq_ofReal_abs] at norm_one
  simp [f_n_nonneg, abs_of_nonneg] at norm_one
  simp [norm_one]

lemma ennreal_ofReal_toReal_eq (a: ENNReal): ENNReal.ofReal a.toReal = a ∨ ENNReal.ofReal a.toReal = 0 := by
  match a with
  | none =>
    simp
  | some val =>
    simp

-- lemma ennreal_div_le_of_zero (a b c: ENNReal) (ha: (((ENNReal.ofReal a.toReal) / b) ≤ c)): a / b ≤ c  := by
--   by_cases a_eq_top: a = ⊤
--   .
--     rw [a_eq_top] at ha
--   cases ha
--   . rename_i a_top
--     simp [a_top]
--   . rename_i div_le
--     grw [ENNReal.ofReal_toReal_le]
--     exact div_le

lemma laplace_spectrum_contains_zero (f_n_limit: f_n_conv_delta_tendsto): 0 ∈ spectrum ℝ (Laplace_linear ) := by
  rw [spectrum.zero_mem_iff]
  by_contra this
  obtain ⟨f, hf⟩ := this
  -- Copied from https://github.com/leanprover-community/mathlib4/blob/60041760fb96850991084120a9a9b217890cf1f1/Mathlib/Topology/Algebra/Module/Equiv.lean#L760
  let laplace_equiv: (MeasureTheory.Lp ℝ 2 (μ := volume (α := G))) ≃ₗ[ℝ] (MeasureTheory.Lp ℝ 2 (μ := volume (α := G))) := {
      toFun := f.val
      map_add' := by simp
      map_smul' := by simp
      invFun := f.inv
      left_inv := fun x =>
        show (f.inv * f.val) x = x by
          rw [f.inv_val]
          simp
      right_inv := fun x =>
        show (f.val * f.inv) x = x by
          rw [f.val_inv]
          simp
      }
  have laplace_cont := continuous_of_linear_of_bound (C := 2) (𝕜 := ℝ ) (f := f.val) ?_ ?_ ?_
  let cont_equiv :=  LinearEquiv.toContinuousLinearEquivOfContinuous laplace_equiv laplace_cont

  have inv_bounded := ContinuousLinearMap.isBoundedLinearMap (𝕜 := ℝ) (cont_equiv.symm.toContinuousLinearMap)

  have nontrival_lp : Nontrivial ↥(Lp ℝ 2 (volume (α := G))) := by
    rw [nontrivial_iff]
    use 0
    use MemLp.toLp (Pi.single 1 1) (by
      apply Continuous.memLp_of_hasCompactSupport
      . apply continuous_of_discreteTopology
      . simp [HasCompactSupport, tsupport]
    )
    simp
    rw [MeasureTheory.Lp.ext_iff]
    rw [ae_eq_everywhere]
    rw [ae_eq_everywhere.mp (MemLp.coeFn_toLp _)]
    conv =>
      arg 1
      lhs
      equals 0 =>
        rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_zero _ _ _)]
    by_contra!
    apply_fun (fun f => f 1) at this
    simp at this


  have norm_mul_bound := ContinuousLinearEquiv.one_le_norm_mul_norm_symm cont_equiv



  have inv_norm_ge (n: ℕ) : (1 : ENNReal) / (eLpNorm (Laplace_b (F_n n)) 2 (μ := volume (α := G))) ≤ ENNReal.ofReal ‖cont_equiv.symm.toContinuousLinearMap‖ := by

    calc
    _ = (eLpNorm (F_n n) 2 (μ := volume (α := G))) / ((eLpNorm (Laplace_b (F_n n)) 2 (μ := volume (α := G)))) := by
      rw [F_n_norm_eq_one]
    _ = (eLpNorm (cont_equiv.symm.toFun (cont_equiv.toFun (F_n_lp2 n))) 2) / ((eLpNorm (Laplace_b (F_n n)) 2 (μ := volume (α := G)))) := by
      simp [F_n_lp2]
      rw [ae_eq_everywhere.mp (MemLp.coeFn_toLp _)]
    _ ≤ ENNReal.ofReal ‖cont_equiv.symm.toContinuousLinearMap‖ := by
      have other := ContinuousLinearMap.ratio_le_opNorm (f := cont_equiv.symm.toContinuousLinearMap) (x := (((F_n_lp2 n) - conv_mu_lp2 (F_n_lp2 n))))
      conv at other =>
        lhs
        rw [Lp.norm_def]
        --rw [ContinuousLinearMap.map_sub]
        --rw [ae_eq_everywhere.mp (Lp.coeFn_sub _ _)]



      conv =>
        lhs
        arg 1
        arg 1
        rhs
        rhs
        rhs
        simp [cont_equiv, laplace_equiv]
        simp [hf, Laplace_linear]
      simp [-AddSubgroupClass.coe_sub, -AddSubgroup.coe_sub, Laplace]
      apply_fun ENNReal.ofReal at other
      -- TODO - consider removing @[simp] from 'AddSubgroupClass.coe_sub'
      simp only [ContinuousLinearEquiv.coe_coe, map_sub, ofReal_norm] at other
      simp only [F_n_lp2, Laplace_b, conv_mu_lp2]
      simp_rw [ae_eq_everywhere.mp (MemLp.coeFn_toLp _)]
      by_cases norm_f_eq_zero: ‖F_n_lp2 n - conv_mu_lp2 (F_n_lp2 n)‖ = 0
      . rw [norm_eq_zero] at norm_f_eq_zero
        have foo := laplace_zero_iff_zero (F_n_lp2 n) (by
          simp [Laplace]
          exact norm_f_eq_zero
        )
        simp [F_n_lp2] at foo
        apply_fun (fun f => (f: (G → ℝ))) at foo
        simp_rw [ae_eq_everywhere.mp (MemLp.coeFn_toLp _)] at foo
        conv at foo =>
          rhs
          equals 0 =>
            rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_zero _ _ _)]
        simp [foo]
        unfold Conv
        simp
        conv =>
          lhs
          pattern MemLp.toLp _ _
          equals 0 =>
            conv =>
              arg 1
              arg 1
              equals 0 =>
                ext a
                simp
            simp
        simp
        conv =>
          arg 1
          arg 1
          arg 1
          equals 0 =>
            rw [ae_eq_everywhere.mp (MeasureTheory.AEEqFun.coeFn_zero)]
        simp
      -- . rw [Lp.norm_def] at norm_eq_zero
      --   rw [ae_eq_everywhere.mp (Lp.coeFn_sub _ _)]  at norm_eq_zero
      --   simp only [F_n_lp2, conv_mu_lp2] at norm_eq_zero
      --   simp_rw [ae_eq_everywhere.mp (MemLp.coeFn_toLp _)] at norm_eq_zero
      --   rw [ENNReal.toReal_eq_zero_iff] at norm_eq_zero
      --   cases norm_eq_zero
      --   . rename_i foo
      --     simp [foo]
      --   simp [norm_eq_zero]
      --   sorry
      rw [ENNReal.ofReal_div_of_pos] at other
      .
        simp only [ofReal_norm, Lp.enorm_def] at other
        rw [ae_eq_everywhere.mp (Lp.coeFn_sub _ _)] at other
        simp only [F_n_lp2, conv_mu_lp2] at other
        simp_rw [ae_eq_everywhere.mp (MemLp.coeFn_toLp _)] at other
        rw [ENNReal.ofReal_toReal] at other
        .
          rw [ae_eq_everywhere.mp (Lp.coeFn_sub _ _)]
          rw [ae_eq_everywhere.mp (Lp.coeFn_sub _ _)] at other
          simp_rw [ae_eq_everywhere.mp (MemLp.coeFn_toLp _)] at other
          exact other
        .
          rw [← ae_eq_everywhere.mp (Lp.coeFn_sub _ _)]
          apply MeasureTheory.Lp.eLpNorm_ne_top
      . simpa using norm_f_eq_zero
      . exact ENNReal.ofReal_mono
  .
    rw [isBoundedLinearMap_iff] at inv_bounded
    obtain ⟨M, M_pos, le_M⟩ := inv_bounded.2

    have foo := F_n_conv_mu_lim f_n_limit
    rw [ENNReal.tendsto_atTop_zero] at foo
    obtain ⟨n, hn⟩ := foo  ((1: ENNReal) /(2 * ‖cont_equiv.symm.toContinuousLinearMap‖ₑ)) (by
      simp
      rw [ENNReal.mul_eq_top]
      simp
    )
    specialize hn n (by simp)

    rw [Lp.enorm_def] at hn
    specialize inv_norm_ge n
    simp [Laplace_b] at inv_norm_ge
    rw [ae_eq_everywhere.mp (Lp.coeFn_sub _ _)] at hn
    simp only [F_n_lp2, conv_mu_lp2] at hn
    simp_rw [ae_eq_everywhere.mp (MemLp.coeFn_toLp _)] at hn
    grw [hn] at inv_norm_ge
    simp at inv_norm_ge

    have norm_nonzero :‖cont_equiv.symm.toContinuousLinearMap‖ ≠ 0 := by
      by_contra!
      simp [this] at norm_mul_bound
      norm_num at norm_mul_bound

    simp [enorm] at inv_norm_ge
    norm_cast at inv_norm_ge
    rw [two_mul] at inv_norm_ge
    simp at inv_norm_ge
    apply_fun norm at inv_norm_ge
    rw [inv_norm_ge] at norm_nonzero
    simp at norm_nonzero
  . simp
  . simp
  . intro x
    rw [hf]
    apply laplace_bounded'


#print axioms laplace_bounded
#print axioms laplace_self_adjoint
#print axioms laplace_positive_semidefinite



lemma laplace_b_const (k: ℝ): Laplace_b (fun g => k) = 0 := by
  simp [Laplace_b]
  simp [f_conv_mu]
  ext a
  simp
  norm_cast
  rw [← mul_assoc]

  rw [inv_mul_cancel₀]
  . simp
  . simp
    have foo := S_nonempty
    grind

lemma laplace_conv_eq_laplace_right_of_lp2 (f g: G → ℝ) (hfg: ConvExists f g) (hf: MemLp f 2 Measure.count) (hg: MemLp g 2 Measure.count): Laplace_b (Conv f g) = Conv f (Laplace_b g) := by
  simp_rw [Laplace_b]
  rw [conv_assoc_of_lp2]

  nth_rw 2 [sub_eq_add_neg]
  rw [conv_add_right]
  -- TODO - figure out how to do this without a 'conv' block
  conv =>
    rhs
    rhs
    equals Conv f ((-1 : ℝ) • (Conv g (mu ))) =>
      simp
  rw [smul_conv]
  simp
  . rw [← sub_eq_add_neg]
  . exact hfg
  .
    simp [ConvExists, MeasureTheory.ConvolutionExists, MeasureTheory.ConvolutionExistsAt]
    intro a
    simp_rw [← neg_mul]
    simp_rw [f_conv_mu]
    simp_rw [← mul_assoc, mul_comm, mul_assoc]
    apply MeasureTheory.Integrable.const_mul
    simp_rw [Finset.mul_sum]
    apply MeasureTheory.integrable_finset_sum
    intro s hs
    simp [ConvExists, MeasureTheory.ConvolutionExists, MeasureTheory.ConvolutionExistsAt] at hfg
    specialize hfg (s * a)
    simp only [neg_mul]
    apply MeasureTheory.Integrable.neg
    simp_rw [mul_div]
    exact hfg
  . exact hf
  . exact hg
  . apply mu_finsupp

lemma laplace_conv_eq_laplace_right (f g: G → ℝ) (hfg: ConvExists f g) (g_nonneg: ∀ a: G, 0 ≤ g a) (g_finsupp: g.support.Finite): Laplace_b (Conv f g) = Conv f (Laplace_b g) := by
  simp_rw [Laplace_b]
  rw [conv_assoc]

  nth_rw 2 [sub_eq_add_neg]
  rw [conv_add_right]
  -- TODO - figure out how to do this without a 'conv' block
  conv =>
    rhs
    rhs
    equals Conv f ((-1 : ℝ) • (Conv g (mu ))) =>
      simp
  rw [smul_conv]
  simp
  . rw [← sub_eq_add_neg]
  . exact hfg
  .
    simp [ConvExists, MeasureTheory.ConvolutionExists, MeasureTheory.ConvolutionExistsAt]
    intro a
    simp_rw [← neg_mul]
    simp_rw [f_conv_mu]
    simp_rw [← mul_assoc, mul_comm, mul_assoc]
    apply MeasureTheory.Integrable.const_mul
    simp_rw [Finset.mul_sum]
    apply MeasureTheory.integrable_finset_sum
    intro s hs
    simp [ConvExists, MeasureTheory.ConvolutionExists, MeasureTheory.ConvolutionExistsAt] at hfg
    specialize hfg (s * a)
    simp only [neg_mul]
    apply MeasureTheory.Integrable.neg
    simp_rw [mul_div]
    exact hfg
  . exact hfg
  .
    apply conv_exists_fin_supp
    right
    exact mu_finsupp
  . apply g_finsupp
  . exact g_nonneg
  . exact mu_finsupp
  . intro a
    simp [mu]
    positivity

#print axioms laplace_conv_eq_laplace_right



#synth Module ℝ (Lp ℝ 2 (μ := MeasureTheory.volume (α := G)))

lemma abs_sub_sq_eq (a b : ℝ): (a - b)^2 = |a - b|^2 := by
  nth_rw 2 [pow_two]
  rw [abs_sub_sq]
  rw [sub_sq]
  group

lemma sub_sq_le_abs (a b : ℝ) (ha: 0 ≤ a) (hb: 0 ≤ b): (a - b)^2 ≤ |a^2 - b^2| := by
  rw [sq_sub_sq]
  rw [abs_mul]
  have sub_le_add: |a - b| ≤ |a + b| := by
    have sum_pos: 0 ≤ a + b := by linarith
    rw [abs_of_nonneg sum_pos]
    rw [abs_le]
    refine ⟨?_, ?_⟩
    . linarith
    . linarith
  rw [abs_sub_sq_eq]
  grw [← sub_le_add]
  rw [pow_two]

lemma card_s_ne: #(S) ≠ 0 := by
  simp
  have foo := S_nonempty
  simp at foo
  exact Finset.nonempty_iff_ne_empty.mp foo

lemma bounded_from_elpnorm_bound (f: G → ℝ) (p: ℕ) (hp: p ≠ 0) (C: ℝ) (hC: 0 ≤ C) (hf: eLpNorm f p (volume) ≤ (ENNReal.ofReal C)): ∀ g: G, |f g| ≤ C := by
  simp [eLpNorm, eLpNorm', hp] at hf
  simp_rw [lintegral_g_eq_add] at hf
  by_contra!
  obtain ⟨g, hg⟩ := this
  have norm_le := ENNReal.le_tsum (f := fun a => ‖f a‖ₑ ^ p) g
  rw [ENNReal.rpow_inv_le_iff] at hf
  .
    rw [Real.enorm_eq_ofReal_abs] at norm_le
    grw [hf] at norm_le
    norm_cast at norm_le
    rw [← ENNReal.ofReal_pow (by simp)] at norm_le
    rw [← ENNReal.ofReal_pow hC] at norm_le
    rw [ENNReal.ofReal_le_ofReal_iff (by simp [hC])] at norm_le
    rw [pow_le_pow_iff_left₀ (by simp) hC (by omega)] at norm_le
    linarith
  . simp only [Nat.cast_pos]
    omega






  --simp at norm_zero
  --have foo (n: ℕ) := F_n_norm_eq_one (seq n)
  --simp [F_n_norm_eq_one] at norm_zero

    -- apply Filter.Eventually.of_forall
    -- rw [tendsto_pi_nhds] at tendsto_F
    -- apply tendsto_F

  --sorry
-- We need to prove that a bounded seqence of Lipschitz harmonic functions has a subsequence that converges to a Lipschitz harmonic function
-- lp.memℓp_of_tendsto
-- MeasureTheory.ae_bdd_liminf_atTop_of_eLpNorm_bdd
-- IsCompact.tendsto_subseq

lemma haar_eq_haar_add : myHaar = myHaarAddOpp := by
  rfl

lemma conv_laplce_norm (n: ℕ) (H_n: ℕ → G → ℝ): eLpNorm ((Laplace_b ((Conv (H_n n)) (f_n n)))) ⊤ (μ := volume (α := G)) ≤ eLpNorm (H_n n) ⊤ * (eLpNorm (Laplace_b (f_n n)) 1 (μ := volume (α := G))) := by
  rw [laplace_conv_eq_laplace_right]
  .
    unfold Conv
    eta_reduce
    simp only [volume]
    rw [haar_eq_haar_add]

    have my_norm := ENNReal.eLpNorm_convolution_le_enorm_mul (f := H_n n) (G := (Additive G)) (L := (ContinuousLinearMap.mul ℝ ℝ))
      (g := Laplace_b (f_n n)) (r := ⊤) (p := ⊤) (q := 1) (μ := myHaarAddOpp)
      (by simp)
      (by simp)
      (by simp)
      (by simp)
      (by apply AEMeasurable.of_discrete)
      (by apply AEMeasurable.of_discrete)


    grw [my_norm]
    simp [enorm]
  .
    apply conv_exists_fin_supp
    right
    exact f_n_fin_supp n
  . apply f_n_nonneg
  . exact f_n_fin_supp n

set_option maxHeartbeats 60000 in
def nontrivial_harmonic_common (k: ℕ) (seq: ℕ → ℕ) (h_seq: Filter.Tendsto seq Filter.atTop Filter.atTop) (F: G → ℝ) (H_n: ℕ → G → ℝ) (h_conv_lipschitz: ∀ n, LipschitzWith k (Conv (H_n n) (f_n n)))
(tendsto_F: Filter.Tendsto ((fun n ↦ Conv (H_n (seq n)) (f_n (seq n)))) Filter.atTop (nhds F))
(H_n_norm: ∀ n: ℕ, MeasureTheory.eLpNorm (H_n n) (p := ⊤) MeasureTheory.volume = 1): LipschitzH := by

  let conv_h_n_cont (n: ℕ): C(G, ℝ) := {
    toFun := Conv (H_n (seq n)) (f_n (seq n)),
    continuous_toFun := by exact continuous_of_discreteTopology
  }

  let F_lipschitzh: LipschitzH := {
    toFun := (fun (g: G) => Complex.ofReal (F g)),
    lipschitz := by
      use k
      rw [← Function.comp_def]
      conv =>
        arg 1
        equals ((1 * k) : NNReal) =>
          simp
      apply LipschitzWith.comp (Kf := 1) (Kg := k)
      .
        exact Isometry.lipschitz (Complex.isometry_ofReal)
      .
        have closed_lipschitz := isClosed_setOf_lipschitzWith (α := G) (β := ℝ) k
        apply IsClosed.isSeqClosed at closed_lipschitz
        simp [IsSeqClosed] at closed_lipschitz
        have F_lipschitz := closed_lipschitz (p := F) (x := (fun n ↦ Conv (H_n (seq n)) (f_n (seq n)))) (by
          intro n
          simp
          apply h_conv_lipschitz
        ) tendsto_F
        exact F_lipschitz
    harmonic := by
      simp [Harmonic]
      intro g
      rw [tendsto_pi_nhds] at tendsto_F
      have lim_f_sum := tendsto_finset_sum (ι := S) (M := ℝ) (s := Finset.univ) (a := fun s => F (s.val * g)) (f := (fun (s: S) n ↦ Conv (H_n (seq n)) (f_n (seq n)) (s.val *g))) (x := Filter.atTop (α := ℕ)) ?_

      -- TODO - figure out why lean hangs without this
      have my_mul : ContinuousMul ℝ := instIsTopologicalRingReal.toContinuousMul
      have lim_f_mul_sum := Filter.Tendsto.const_mul ((#S) : ℝ)⁻¹ lim_f_sum
      .
        have lim_f_g := tendsto_F g
        have lim_f_g_sub := Filter.Tendsto.sub lim_f_g lim_f_mul_sum

        have laplace_conv_tendsto_zero: Filter.Tendsto (fun n => eLpNorm (Laplace_b (Conv (H_n (seq n)) (f_n (seq n)))) ⊤) Filter.atTop (nhds 0) := by
          apply tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun n => 0) (h := fun (n: ℕ) => ENNReal.ofReal ((2: ℝ) / ((seq n) + 1) : ℝ))
          . simp
          .
            rw [← ENNReal.tendsto_toReal_iff]
            conv =>
              arg 1
              intro n
              rw [ENNReal.toReal_ofReal (by
                norm_cast
                positivity
              )]
            conv =>
              arg 1
              intro n
              rhs
              equals ((((((seq n) + 1): ℕ)) : ℕ ) : ℝ) => simp
            conv =>
              arg 1
              equals (fun (n: ℕ) => (2 : ℝ) / (n) ) ∘ (fun n => (seq n) + 1) =>
                ext n
                simp
            apply Filter.Tendsto.comp
            .
              conv =>
                arg 1
                equals (fun (n: ℕ) => (2 : ℝ) / ((n) : ℕ)) =>
                  ext n
                  simp
              --rw [Filter.tendsto_add_atTop_iff_nat (f := fun n => (2 : ℝ) / (n))]
              apply tendsto_const_div_atTop_nhds_zero_nat
            .
              --apply Filter.tendsto_atTop_add_const_right (f := fun n => eps_seq (seq n))
              apply Filter.Tendsto.comp
              . conv =>
                  arg 1
                  equals fun n => n + 1 =>
                    simp
                apply Filter.tendsto_add_atTop_nat

              . simp
                exact h_seq
            . simp
            . simp
          . rw [Pi.le_def]
            intro x
            simp
          . rw [Pi.le_def]
            intro n
            simp
            have bound_by_norm_one := conv_laplce_norm (seq n)
            have norm_le_two_div := f_n_sub_conv  (seq n)
            nth_rw 1 [eLpNorm] at bound_by_norm_one
            simp at bound_by_norm_one
            grw [bound_by_norm_one]
            have h_norm := H_n_norm (seq n)
            simp [eLpNorm, eLpNorm'] at h_norm
            rw [h_norm]
            simp
            simp_rw [Laplace_b]
            simp [eLpNorm] at norm_le_two_div
            exact norm_le_two_div

        rw [← ENNReal.tendsto_toReal_iff] at laplace_conv_tendsto_zero

        have laplace_real_tendsto_zero: Filter.Tendsto (fun n => |(Laplace_b (Conv (H_n (seq n)) (f_n (seq n))) (g))|) Filter.atTop (nhds 0)  := by
          apply squeeze_zero (g := fun n => (eLpNorm (Laplace_b (Conv (H_n (seq n)) (f_n (seq n)))) ⊤ volume).toReal)
          .
            intro n
            simp
          . intro n
            have ae_le := ENNReal.ae_le_essSup (fun x ↦ ‖Laplace_b (Conv (H_n (seq n)) (f_n (seq n))) x‖ₑ) (μ := volume)
            simp [volume] at ae_le
            rw [my_haar_eq_count] at ae_le
            rw [count_ae_everywhere] at ae_le
            specialize ae_le g
            simp [eLpNorm, eLpNorm']
            simp [eLpNormEssSup]
            rw [← ENNReal.toReal_le_toReal] at ae_le
            simp only [toReal_enorm, Real.norm_eq_abs, OrderTop.bddAbove] at ae_le
            simp [volume]
            rw [my_haar_eq_count]
            exact ae_le
            . simp
            .
              -- TODO - deduplicate this
              have bound_by_norm_one := conv_laplce_norm (seq n) H_n
              have norm_le_two_div := f_n_sub_conv (seq n)
              nth_rw 1 [eLpNorm] at bound_by_norm_one
              simp at bound_by_norm_one
              have h_norm := H_n_norm (seq n)
              simp [eLpNorm, eLpNorm'] at h_norm
              rw [h_norm] at bound_by_norm_one
              simp only [eLpNormEssSup] at bound_by_norm_one
              simp [volume] at bound_by_norm_one
              rw [my_haar_eq_count] at bound_by_norm_one
              rw [← WithTop.lt_top_iff_ne_top]
              grw [bound_by_norm_one]
              simp_rw [Laplace_b]
              simp [volume] at norm_le_two_div
              rw [my_haar_eq_count] at norm_le_two_div
              grw [norm_le_two_div]
              apply ENNReal.ofReal_lt_top
          . apply laplace_conv_tendsto_zero

        simp_rw [Laplace_b] at laplace_real_tendsto_zero
        simp_rw [f_conv_mu] at laplace_real_tendsto_zero
        beta_reduce at laplace_real_tendsto_zero
        conv at laplace_real_tendsto_zero =>
          arg 1
          rw [← Function.comp_def]
        rw [← tendsto_zero_iff_abs_tendsto_zero] at laplace_real_tendsto_zero
        --simp_rw [Function.comp_def] at lim_f_g_sub
        conv at laplace_real_tendsto_zero =>
          arg 1
          intro n
          simp

        conv at lim_f_g_sub =>
          arg 1
          intro n
          rw [← Finset.sum_subtype (s := S) (f := fun s => Conv (H_n (seq n)) (f_n (seq n)) (s * g)) (h := by
            intro s
            simp
          )]
        have lim_eq := tendsto_nhds_unique laplace_real_tendsto_zero lim_f_g_sub
        rw [eq_comm] at lim_eq
        rw [sub_eq_zero] at lim_eq
        rw [lim_eq]
        norm_cast
        rw [← Finset.sum_subtype (s := S) (f := fun i => (F (i * g)))]
        simp
        . simp
        . intro n
          -- TODO - deduplicate this. I'm sure there's lots of other versions of it scattered around this file
          rw [← WithTop.lt_top_iff_ne_top]
          grw [conv_laplce_norm]
          rw [H_n_norm]
          simp
          simp_rw [Laplace_b]
          grw [MeasureTheory.eLpNorm_sub_le]
          rw [f_n_norm_one]
          simp_rw [f_conv_mu]
          simp_rw [← smul_eq_mul]
          rw [← Pi.smul_def]
          rw [MeasureTheory.eLpNorm_const_smul]
          conv =>
            lhs
            rhs
            rhs
            arg 1
            equals ∑ x ∈ S, (fun g => f_n (seq n) (x • g)) =>
              funext g
              simp


          grw [MeasureTheory.eLpNorm_sum_le]
          simp_rw [← Function.comp_def]
          conv =>
            lhs
            rhs
            rhs
            arg 2
            intro x
            rw [MeasureTheory.eLpNorm_comp_measurePreserving (ν := MeasureTheory.volume) (by
              apply MeasureTheory.AEStronglyMeasurable.of_discrete
            ) (by
            exact {
              measurable := by
                apply Measurable.of_discrete
              map_eq := by
                simp [MeasureTheory.volume]
            }
          )]
          simp_rw [f_n_norm_one]
          simp
          field_simp
          norm_cast
          rw [Real.enorm_eq_ofReal_abs]
          simp
          norm_cast
          rw [ENNReal.add_lt_top]
          refine ⟨by simp, ?_⟩
          apply ENNReal.mul_lt_top
          . simp
          . simp
          .
            intro s hs
            apply AEStronglyMeasurable.of_discrete
          . simp
          . apply AEStronglyMeasurable.of_discrete
          . apply AEStronglyMeasurable.of_discrete
          . simp




        . simp
      . intro s hs
        apply tendsto_F
  }
  exact F_lipschitzh

lemma counting_le_essSup (f: G → ℝ): ∀ g : G, ‖f g‖ₑ ≤ essSup  (fun g => ‖f g‖ₑ) volume := by
  intro g
  have ae_le := ENNReal.ae_le_essSup (fun g => ‖f g‖ₑ) (μ := volume)
  simp [MeasureTheory.volume] at ae_le
  rw [my_haar_eq_count] at ae_le
  rw [count_ae_everywhere] at ae_le
  specialize ae_le g
  simp
  simp [volume]
  rw [my_haar_eq_count]
  exact ae_le

lemma essSup_eq_elpNorm_top (f: G → ℝ): (essSup (fun g => ‖f g‖ₑ) volume) = (eLpNorm f ⊤ volume) := by
  rfl

lemma neg_smul (f: G → ℝ): -f = (-1 : ℝ) • f := by
  simp

-- lemma aeqfun_cast (f: G →ₘ[volume] ℝ):  := by
--   have eq_fun := MeasureTheory.AEEqFun.coeFn_mk f (μ := MeasureTheory.volume (α := G)) (by apply MeasureTheory.AEStronglyMeasurable.of_discrete)
--   rw [ae_eq_everywhere] at eq_fun
--   nth_rw 2 [← eq_fun]
--   rfl


-- TODO - cleanup and upstream to mathlib
lemma nat_mono_le {f: ℕ → ℕ} (hf: StrictMono f) (n: ℕ): n ≤ f n := by
  induction n with
  | zero =>
    simp
  | succ k ih =>
    have k_le := hf (a := k) (b := k + 1) (by simp)
    have succ_le : k + 1 ≤ (f k) + 1 := by grind

    have succ_le_f: (f k) + 1 ≤ f (k + 1) := by
      have foo := hf.add_le_nat 1 k
      grind
    grind


-- DO NOT REMOVE `f_n_limit` - this will be needed by the spectral theorem part of the proof
lemma nontrivial_harmonic_case_one (f_n_limit: ∀ s: S, (Filter.Tendsto (fun n: ℕ => MeasureTheory.eLpNorm (f_n n - (Conv (f_n n) (delta s.val))) 1 MeasureTheory.volume) Filter.atTop (nhds 0))): ∃ F: LipschitzH , ∀ z: ℂ, F ≠ ConstLipschitzH z := by



  let H_n (n: ℕ) (s: G): (MeasureTheory.Lp ℝ 2 (μ := volume (α := G))) :=
    (1 / (‖(((G_n (n + 1) (by simp)) - (conv_finsupp_lp2 (G_n (n + 1) (by simp)) (delta s) (by simp [delta]))))‖)) •
      MeasureTheory.Lp.compMeasurePreserving (Inv.inv) (measure_preserving_inv) (((G_n (n + 1) (by simp)) - (conv_finsupp_lp2 (G_n (n + 1) (by simp)) (delta s) (by simp [delta]))))

  obtain ⟨s, s_mem_S, s_infinite⟩ := g_sub_norm_single_s
  let seq := Nat.nth ({n | ‖(G_n (n + 1) (by simp)) - (conv_finsupp_lp2 (G_n (n + 1) (by simp)) (delta s) (by simp))‖ ^ 2 > 1})
  have seq_mono : StrictMono seq := Nat.nth_strictMono s_infinite


  have H_n_norm (n: ℕ): ‖H_n (seq n) s‖ₑ = 1 := by
    conv =>
      rhs
      equals ‖(1: ℝ)‖ₑ => simp
    rw [enorm_eq_iff_norm_eq]
    unfold H_n
    have norm_gt := Nat.nth_mem_of_infinite s_infinite n
    rw [norm_smul]
    rw [MeasureTheory.Lp.norm_compMeasurePreserving]
    field_simp
    simp
    rw [mul_inv_cancel₀]
    simp [seq]
    simp at norm_gt
    by_contra!
    simp [setOf] at this
    simp [this] at norm_gt
    norm_num at norm_gt

  have seq_add_pos: ∀ {n}, 0 < (seq (n + 1)) := by
    intro n
    have prev_lt := (seq_mono.lt_iff_lt (a := n) (b := n + 1)).mpr (by simp)
    grind

  have h_n_f_lipschitz: ∀ n: ℕ, LipschitzWith ((2 * #(S))^((2 : ℝ)⁻¹)) (Conv (H_n (seq (n)) s) (G_n ((seq n) + 1) (by simp))) := by
    intro n
    let G'_n := (G_n ((seq n) + 1) (by simp))
    apply lipschitzWith_discrete
    intro g y hy
    rw [Real.dist_eq]
    rw [← Real.norm_eq_abs]
    rw [norm_sub_rev]
    have y_eq_inv_inv: y = y⁻¹⁻¹ := by simp
    rw [y_eq_inv_inv]
    rw [← f_conv_delta (f := Conv (↑↑(H_n (seq (n)) s)) (G_n ((seq n) + 1) (by simp)))]
    rw [← Pi.sub_apply]
    rw [sub_eq_add_neg]
    rw [neg_smul]
    rw [← conv_smul]
    rw [ ← smul_conv]
    rw [conv_assoc_of_lp2]
    .
      rw [← conv_add_right]
      .
        rw [← ENNReal.ofReal_le_ofReal_iff]
        .
          rw [ofReal_norm_eq_enorm]
          grw [counting_le_essSup]
          rw [essSup_eq_elpNorm_top]
          simp only [volume]
          simp_rw [my_haar_eq_count]
          rw [← my_haar_eq_count]
          conv =>
            lhs
            arg 1
            arg 0
            unfold Conv
          eta_reduce
          simp_rw [my_haar_eq_count]
          conv =>
            arg 1
            arg 3
            equals myHaarAddOpp =>
              rw [← my_add_haar_eq_count]

          grw [ENNReal.eLpNorm_top_convolution_le (μ := myHaarAddOpp) (c := 1) (p := 2) (q := 2)]
          .
            simp
            simp [norm, volume] at H_n_norm
            simp_rw [my_haar_eq_count] at H_n_norm
            rw [my_add_haar_eq_count]
            simp [H_n_norm]

            have sum_norm := proposition_3_18 G'_n
            have g_inner_laplace := MeasureTheory.L2.inner_def (Laplace G'_n) G'_n (𝕜 := ℝ) (α := G)
            have g_n_prop := (Classical.choose_spec (laplace_g_n (n + 1) (by simp))).2
            rw [integral_eq_eq_sum] at g_inner_laplace
            simp at g_inner_laplace
            rw [sum_norm] at g_inner_laplace
            rw [g_n_conv_norm] at g_inner_laplace
            field_simp at g_inner_laplace
            rw [eq_div_iff_mul_eq] at g_inner_laplace

            --simp at g_inner_laplace
            --simp_rw [mul_comm] at g_inner_laplace
            .
              simp [eLpNorm, eLpNorm']
              simp [-AddSubgroupClass.coe_sub, -AddSubgroup.coe_sub, MeasureTheory.Lp.norm_def, eLpNorm, eLpNorm', conv_finsupp_lp2] at g_inner_laplace
              rw [← ENNReal.ofReal_rpow_of_pos]
              .
                apply ENNReal.rpow_le_rpow
                .
                  generalize_proofs p_1 p_2 p_3
                  -- TODO - make this less horrible
                  grw [Finset.single_le_sum (f := (fun g => ∫⁻ (a : Additive G), ‖(G_n ((seq n) + 1) (by simp)) a + Conv (-↑↑(G_n ((seq n) + 1) (by simp))) (delta g) a‖ₑ ^ 2 ∂Measure.count)) (s := S) (hf := by simp) (h := (by rw [S_eq_Sinv]; simp [hy]))]



                  simp_rw [← ENNReal.rpow_natCast] at g_inner_laplace
                  simp_rw [← ENNReal.toReal_pow] at g_inner_laplace
                  simp_rw [← ENNReal.rpow_natCast] at g_inner_laplace
                  simp_rw [← ENNReal.rpow_mul] at g_inner_laplace
                  simp  [-AddSubgroupClass.coe_sub, -AddSubgroup.coe_sub] at g_inner_laplace
                  simp_rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_sub _ _)] at g_inner_laplace
                  simp_rw [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)] at g_inner_laplace
                  simp at g_inner_laplace
                  rw [neg_smul]
                  simp_rw [conv_smul]
                  simp
                  simp_rw [← sub_eq_add_neg]
                  simp [G'_n] at g_inner_laplace
                  apply_fun ENNReal.ofReal at g_inner_laplace
                  simp at g_inner_laplace
                  rw [g_inner_laplace]
                  norm_cast
                  rw [ENNReal.ofReal_sum_of_nonneg]
                  .
                    conv =>
                      rhs
                      arg 2
                      intro i
                      rw [ENNReal.ofReal_toReal (by
                        simp [f_conv_delta_helper]
                        have g_norm := MeasureTheory.Lp.eLpNorm_lt_top ((G_n ((seq n) + 1) (by simp)) - (Lp.compMeasurePreserving (fun x => i⁻¹ * x) (by
                          apply measurePreserving_mul_left
                        ) (G_n ((seq n) + 1) (by simp))))
                        rw [ae_eq_everywhere.mp (Lp.coeFn_sub _ _)] at g_norm
                        rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_compMeasurePreserving _ _)] at g_norm
                        simp [eLpNorm, eLpNorm', Lp.compMeasurePreserving] at g_norm
                        rw [ENNReal.rpow_lt_top_iff_of_pos (by simp)] at g_norm
                        grind
                      )]
                    simp [volume]
                    simp_rw [my_haar_eq_count]
                    apply le_refl
                  . simp
                . simp
              .
                simpa using hGS.hS

              -- Finset.single_le_sum
            . simp
              grind
            .
              apply MeasureTheory.Integrable.of_integral_ne_zero
              rw [← g_inner_laplace]
              simp [G'_n]
              have foo := g_n_conv_norm (seq (n) + 1) (by simp)
              grind
          . infer_instance
          . apply AEMeasurable.of_discrete
          . apply AEMeasurable.of_discrete
          . intro a b
            simp
        .
          positivity
      .
        simp [ConvExists]
        rw [my_add_haar_eq_count]
        apply ENNReal.ConvolutionExists.of_memLp_memLp (p := 2) (q := 2) (μ := Measure.count)
        . infer_instance
        . simp
        . apply AEStronglyMeasurable.of_discrete
        . apply AEStronglyMeasurable.of_discrete
        . rw [← my_add_haar_eq_count]
          apply Lp.memLp
        . rw [← my_add_haar_eq_count]
          apply Lp.memLp
      .
        simp [ConvExists]
        rw [my_add_haar_eq_count]
        apply ENNReal.ConvolutionExists.of_memLp_memLp (p := 2) (q := 2) (μ := Measure.count)
        . infer_instance
        . simp
        . apply AEStronglyMeasurable.of_discrete
        . apply AEStronglyMeasurable.of_discrete
        . rw [← my_haar_eq_count]
          apply Lp.memLp
        .
          refine ⟨by apply AEStronglyMeasurable.of_discrete, ?_⟩
          rw [← my_add_haar_eq_count]
          rw [neg_smul]
          rw [conv_smul]
          simp
          rw [← Pi.neg_def]
          simp [Conv]
          rw [← Function.comp_def (β := Additive G)]
          rw [MeasureTheory.eLpNorm_comp_measurePreserving (ν := Measure.count)]
          .
            conv =>
              arg 1
              arg 1
              arg 1
              equals ↑↑(G_n ((seq (n)) + 1) (by simp)) ∘ Additive.toMul =>
                rfl

            conv =>
              arg 1
              arg 1
              arg 2
              equals (delta y⁻¹) ∘ Additive.toMul =>
                rfl

            rw [← my_add_haar_eq_count]
            grw [ENNReal.eLpNorm_convolution_le_enorm_mul (p := 2) (q := 1)]
            .
              rw [MeasureTheory.eLpNorm_comp_measurePreserving (ν := Measure.count)]
              .
                apply ENNReal.mul_lt_top
                . apply ENNReal.mul_lt_top
                  . simp
                  .
                    rw [← my_haar_eq_count]
                    apply MemLp.eLpNorm_lt_top
                    apply Lp.memLp
                .
                  apply MemLp.eLpNorm_lt_top
                  apply Continuous.memLp_of_hasCompactSupport
                  . fun_prop
                  . simp [HasCompactSupport, tsupport]
                    apply Set.Finite.isCompact
                    simp [delta]
                    simp [Function.comp_def]
                    conv =>
                      arg 1
                      arg 1
                      intro x
                      arg 3
                      equals x => rfl
                    simp
              . apply AEStronglyMeasurable.of_discrete
              . rw [my_add_haar_eq_count]
                apply MeasurePreserving.id
            . simp
            . simp
            . simp
            . simp
            . apply AEMeasurable.of_discrete
            . apply AEMeasurable.of_discrete
          . apply AEStronglyMeasurable.of_discrete
          . rw [my_add_haar_eq_count]
            apply MeasurePreserving.id
    . rw [← my_add_haar_eq_count]
      apply Lp.memLp
    . rw [← my_add_haar_eq_count]
      simp
      apply MemLp.neg
      apply Lp.memLp
    . simp

  -- Now rename Hn ∗Gn such that we have added a constant so that Hn ∗Gn(e) = 0
  let new_seq: ℕ → ℕ := seq
  let H_G_conv_zero (n: ℕ) (g: G) := ((Conv (H_n ((new_seq n)) s) (G_n ((new_seq n) + 1) (by simp))) g) - (Conv (H_n ((new_seq n)) s) (G_n ((new_seq n) + 1) (by simp)) 1)


  -- TODO - can the lipschitz constant can be improved?
  have H_G_conv_zero_lipschitz: ∀ n: ℕ, LipschitzWith ((((2 * #(S))^((2 : ℝ)⁻¹))) + 0) (H_G_conv_zero n) := by
    intro n
    simp only [H_G_conv_zero]
    simp only [new_seq]
    apply LipschitzWith.sub
    .
      apply h_n_f_lipschitz
    . apply LipschitzWith.const


  have H_n_conv_zero_eq: ∀ n: ℕ, (H_G_conv_zero (n) 1) - (H_G_conv_zero (n) s⁻¹) = ‖(G_n ((new_seq n) + 1) (by simp)) - (conv_finsupp_lp2 (((G_n ((new_seq n) + 1) (by simp)))) (delta s) (by simp [delta]))‖ := by
    intro n
    simp [H_G_conv_zero]
    have s_inv_eq: s⁻¹ = s⁻¹ * 1 := by
      simp
    rw [s_inv_eq]
    rw [← f_conv_delta  (f := Conv ((H_n ((new_seq n)) s)) ((G_n ((new_seq n) + 1) (by simp))))]
    rw [← Pi.sub_apply]
    rw [sub_eq_add_neg]
    rw [neg_smul]
    rw [← conv_smul]
    rw [ ← smul_conv]
    rw [conv_assoc_of_lp2]
    .
      rw [← conv_add_right]
      .
        simp [H_n, conv_finsupp_lp2]
        rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_smul _ _)]
        rw [conv_smul]
        conv =>
          lhs
          lhs
          arg 0
          unfold Conv

        rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_sub _ _)]
        rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_compMeasurePreserving _ _)]
        rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_compMeasurePreserving _ _)]
        simp only [convolution,
          ContinuousLinearMap.coe_sub', ContinuousLinearMap.mul_apply', Pi.smul_apply, smul_eq_mul]
        simp
        have t_fake_inv: ∀ (t: G), (t: (Additive G))⁻¹ = -(Additive.ofMul t) := by
          intro t
          rfl

        simp [t_fake_inv, Additive.ofMul]
        have one_g_eq: (1 : G) = (0 : (Additive G)) := rfl
        simp_rw [one_g_eq]
        simp_rw [zero_sub]
        conv =>
          lhs
          rhs
          arg 2
          intro t
          rhs
          rhs
          equals (conv_finsupp_lp2 (-(G_n (new_seq n + 1) (by simp))) (delta s) (by simp [delta])) (-t) =>
            simp [conv_finsupp_lp2]
            simp_rw [tolp_apply]
            norm_cast
            rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_neg _)]

        simp [conv_finsupp_lp2]
        norm_cast
        simp_rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_neg _)]
        simp_rw [neg_smul]
        simp_rw [conv_smul]
        simp
        rw [MeasureTheory.MemLp.toLp_neg (by
          rw [f_conv_delta_helper]
          rw [← Function.comp_def]
          apply MeasureTheory.MemLp.comp_measurePreserving (ν := volume)
          . apply MeasureTheory.Lp.memLp
          .
            exact measurePreserving_mul_left volume s⁻¹
        )]
        rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_neg _)]
        simp_rw [← Pi.sub_apply]
        have real_inner: ∀ a b : ℝ, ⟪a, b⟫ = a * b := by
          intro a b
          simp
          rw [mul_comm]
        conv =>
          lhs
          rhs
          arg 2
          intro t
          rw [← Pi.add_apply]
          rw [← Pi.mul_apply]


        rw [MeasureTheory.integral_neg_eq_self]
        simp_rw [Pi.mul_apply]
        simp_rw [← real_inner]
        simp_rw [← sub_eq_add_neg]
        conv =>
          lhs
          rhs
          equals ‖(G_n (new_seq n + 1) (by simp)) - (MemLp.toLp (Conv ((G_n ((new_seq n) + 1) (by simp))) (delta s)) (by
              rw [f_conv_delta_helper]
              rw [← Function.comp_def]
              apply MeasureTheory.MemLp.comp_measurePreserving (ν := volume)
              . apply MeasureTheory.Lp.memLp
              .
                exact measurePreserving_mul_left volume s⁻¹
            ))‖^2 =>
            rw [← real_inner_self_eq_norm_sq]
            rw [MeasureTheory.L2.inner_def]
            simp
            norm_cast
            simp_rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_sub _ _)]
            rfl

        rw [pow_two]
        simp
      .
        simp [ConvExists]
        rw [my_add_haar_eq_count]
        apply ENNReal.ConvolutionExists.of_memLp_memLp (p := 2) (q := 2) (μ := Measure.count)
        . infer_instance
        . simp
        . apply AEStronglyMeasurable.of_discrete
        . apply AEStronglyMeasurable.of_discrete
        . rw [← Function.comp_def]
          apply MeasureTheory.MemLp.comp_measurePreserving
          . apply Lp.memLp
          . simp [volume]
            rw [my_haar_eq_count]
            apply MeasureTheory.MeasurePreserving.id
        .
          apply MeasureTheory.MemLp.comp_measurePreserving
          . apply Lp.memLp
          . simp [volume]
            rw [my_haar_eq_count]
            apply MeasureTheory.MeasurePreserving.id
      .
        -- TODO - deduplicate this
        simp [f_conv_delta_helper]
        simp [ConvExists]
        rw [my_add_haar_eq_count]
        apply ENNReal.ConvolutionExists.of_memLp_memLp (p := 2) (q := 2) (μ := Measure.count)
        . infer_instance
        . simp
        . apply AEStronglyMeasurable.of_discrete
        . apply AEStronglyMeasurable.of_discrete
        . rw [← Function.comp_def]
          apply MeasureTheory.MemLp.comp_measurePreserving
          . apply Lp.memLp
          . simp [volume]
            rw [my_haar_eq_count]
            apply MeasureTheory.MeasurePreserving.id
        .
          apply MeasureTheory.MemLp.neg
          rw [← Function.comp_def]
          apply MeasureTheory.MemLp.comp_measurePreserving
          . apply Lp.memLp
          .
            simp [volume]
            rw [my_haar_eq_count]
            refine MeasurePreserving.mul_left Measure.count s⁻¹ ?_
            apply MeasureTheory.MeasurePreserving.id
    . rw [← my_haar_eq_count]
      apply Lp.memLp
    . rw [← my_haar_eq_count]
      simp
      apply MemLp.neg
      apply Lp.memLp
    . simp [delta]



  --let F := fun (n : ℕ) (g: G) => (Conv (H_n (seq n) s) (f_n (seq n)))
  --have F_tendsto: Filter.Tendsto F Filter.atTop

  have compact_with_fixed_g (g: G): IsCompact (closure ( (Set.range (fun n => H_G_conv_zero n g)))) := by

    apply Bornology.IsBounded.isCompact_closure
    rw [Metric.isBounded_iff]
    use 2 * ((↑(#S) * 2) ^ (2 : ℝ)⁻¹) * (dist g 1)
    intro x hx y hy
    simp at hx
    simp at hy

    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy

    rw [← ha, ← hb]


    have foo := (H_G_conv_zero_lipschitz a).dist_le_mul g 1
    have bar := (H_G_conv_zero_lipschitz b).dist_le_mul g 1
    grw [dist_triangle (y := (H_G_conv_zero a) 1)]
    grw [foo]
    grw [dist_triangle (y := (H_G_conv_zero b) 1)]
    rw [dist_comm] at bar
    grw [bar]
    simp [H_G_conv_zero]
    ring
    simp

  have new_compact_closure: IsCompact (closure (Set.range (fun n => H_G_conv_zero n))) := by
    rw [Pi.isCompact_closure_iff]
    intro g
    apply Bornology.IsBounded.isCompact_closure
    rw [Metric.isBounded_iff]
    use 2 * ((↑(#S) * 2) ^ (2 : ℝ)⁻¹) * (dist g 1)
    intro x hx y hy
    simp at hx
    simp at hy

    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy

    rw [← ha, ← hb]

    have foo := (H_G_conv_zero_lipschitz a).dist_le_mul g 1
    have bar := (H_G_conv_zero_lipschitz b).dist_le_mul g 1
    grw [dist_triangle (y := (H_G_conv_zero a) 1)]
    grw [foo]
    grw [dist_triangle (y := (H_G_conv_zero b) 1)]
    rw [dist_comm] at bar
    grw [bar]
    simp [H_G_conv_zero]
    ring
    simp

  have arzela_tendsto := IsCompact.tendsto_subseq new_compact_closure (x := fun n => (
    H_G_conv_zero n
  )) (by
    intro n
    simp
    apply _root_.subset_closure
    simp
  )
  obtain ⟨arzela_lim, arzela_lim_mem, arzela_seq, arzela_seq_mono, tendsto_arzela_lim⟩ := arzela_tendsto
  rw [tendsto_pi_nhds] at tendsto_arzela_lim

  have tendsto_one := tendsto_arzela_lim 1
  have tendsto_s_inv := tendsto_arzela_lim s⁻¹
  simp at tendsto_one
  simp at tendsto_s_inv

  have abs_tendsto : ∀ z: ℝ, Filter.Tendsto (fun x => |x|) (nhds z) (nhds |z|)  := by
    intro z
    apply Continuous.tendsto
    fun_prop

  have tendsto_sub := tendsto_one.sub tendsto_s_inv
  use {
    toFun := fun g => arzela_lim g
    lipschitz := by
      use ⟨(((↑(#S) * 2) ^ (2 : ℝ)⁻¹)), by positivity⟩
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [Complex.dist_eq]
      simp

      have new_tendsto_sub := (abs_tendsto _).comp ((tendsto_arzela_lim x).sub (tendsto_arzela_lim y))
      have sub_le := le_of_tendsto new_tendsto_sub (b := ((↑(#S) * 2) ^ (2 : ℝ)⁻¹) * (dist x y)) ?_
      . norm_cast
        norm_cast at sub_le
      . apply Filter.Eventually.of_forall
        intro n
        have foo := (H_G_conv_zero_lipschitz (arzela_seq n)).dist_le_mul x y
        rw [Real.dist_eq] at foo
        simp
        norm_cast
        simp at foo
        norm_cast at foo
        ring_nf at foo
        ring_nf
        exact foo

    harmonic := by
      simp [Harmonic]
      intro x
      rw [← sub_eq_zero]

      have sum_lim := tendsto_finset_sum (s := S) (fun s hs => tendsto_arzela_lim (s * x))
      have tendsto_sub := (tendsto_arzela_lim x).sub (sum_lim.const_mul ((#S : ℝ))⁻¹)
      norm_cast

      have lim_zero := squeeze_zero (t₀ := Filter.atTop)
        (f := (fun x_1 ↦ |((fun n ↦ H_G_conv_zero n) ∘ arzela_seq) x_1 x - (↑(#S))⁻¹ * ∑ c ∈ S, ((fun n ↦ H_G_conv_zero n) ∘ arzela_seq) x_1 (c * x)|))
        (g := fun n => (1 / (n + 1)))
        ?_ ?_ ?_
      .
        have target_eq_zero := tendsto_nhds_unique ((abs_tendsto _).comp tendsto_sub) (lim_zero)
        rw [abs_eq_zero] at target_eq_zero
        rw [sub_eq_zero] at target_eq_zero
        simp [target_eq_zero]
      . simp
      . intro n
        simp
        conv =>
          lhs
          arg 1
          equals Laplace_b (H_G_conv_zero (arzela_seq n)) x =>
            simp [Laplace_b]
            simp [f_conv_mu]


        have ae_le := ENNReal.ae_le_essSup (fun x ↦ ENNReal.ofReal |Laplace_b (H_G_conv_zero (arzela_seq n)) x|) (μ := volume)
        simp [volume] at ae_le
        rw [my_haar_eq_count] at ae_le
        rw [count_ae_everywhere] at ae_le
        specialize ae_le x
        rw [← ENNReal.ofReal_le_ofReal_iff (by positivity)]
        grw [ae_le]

        simp [H_G_conv_zero]
        intro i
        rw [← Pi.sub_def]
        rw [laplace_b_sub]
        simp
        rw [sub_eq_add_neg]
        grw [abs_add_le]
        simp
        rw [laplace_conv_eq_laplace_right_of_lp2]
        .
          simp [Conv]
          grw [ENNReal.ofReal_add_le]
          rw [← Real.enorm_eq_ofReal_abs]
          grw [counting_le_essSup]
          rw [essSup_eq_elpNorm_top]
          simp only [volume]
          simp_rw [my_haar_eq_count]
          rw [← my_add_haar_eq_count]
          conv =>
            lhs
            arg 1
            arg 1
            arg 2
            equals (Laplace_b (G_n ((new_seq (arzela_seq n)) + 1) (by simp))) ∘ Additive.toMul =>
              rfl

          conv =>
            lhs
            arg 1
            arg 1
            arg 1
            equals (H_n (new_seq (arzela_seq n)) s) ∘ Additive.toMul =>
              rfl

          grw [ENNReal.eLpNorm_convolution_le_enorm_mul (G := Additive G) (p := 2) (q := 2)]
          .
            conv =>
              lhs
              pattern _ ∘ Additive.toMul
              equals ↑↑(H_n (seq (arzela_seq n)) s) => rfl


            rw [my_add_haar_eq_count]
            rw [← my_haar_eq_count]
            have my_haar_eq : myHaar = volume := rfl
            simp_rw [my_haar_eq]
            rw [← MeasureTheory.Lp.enorm_def]
            simp only [new_seq]
            rw [H_n_norm]
            simp [enorm]
            have g_norm := g_n_laplace_enorm_le (seq (arzela_seq n) + 1) (by simp)
            rw [MeasureTheory.Lp.enorm_def] at g_norm
            simp only [Laplace] at g_norm
            rw [laplace_b_const]
            simp [Laplace_b]
            rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_sub _ _)] at g_norm
            simp only [conv_mu_lp2] at g_norm
            rw [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)] at g_norm
            conv =>
              lhs
              pattern ⇑Additive.toMul
              equals id => rfl
            simp
            grw [g_norm]
            norm_cast
            simp
            norm_cast
            rw [ENNReal.ofReal_inv_of_pos (by positivity)]
            simp
            norm_cast
            have seq_le_n : n ≤ seq (arzela_seq n) := by
              have n_arzela : n ≤ arzela_seq n := by
                apply nat_mono_le arzela_seq_mono
              apply LE.le.trans n_arzela

              apply nat_mono_le seq_mono

            omega
          . simp
          . simp
          . simp
          . norm_num
            norm_cast
            conv =>
              lhs
              equals (ENNReal.ofReal ((2: ℝ)⁻¹ + (2: ℝ)⁻¹)) =>
                rw [ENNReal.ofReal_add]
                . simp
                . simp
                . simp

            simp
            norm_num
          . apply AEMeasurable.of_discrete
          . apply AEMeasurable.of_discrete

        .
          -- TODO - deduplicate this
          simp [ConvExists]
          rw [my_add_haar_eq_count]
          apply ENNReal.ConvolutionExists.of_memLp_memLp (p := 2) (q := 2) (μ := Measure.count)
          . infer_instance
          . simp
          . apply AEStronglyMeasurable.of_discrete
          . apply AEStronglyMeasurable.of_discrete
          . rw [← Function.comp_def]
            apply MeasureTheory.MemLp.comp_measurePreserving
            . apply Lp.memLp
            . simp [volume]
              rw [my_haar_eq_count]
              apply MeasureTheory.MeasurePreserving.id
          .
            apply MeasureTheory.MemLp.comp_measurePreserving
            . apply Lp.memLp
            . simp [volume]
              rw [my_haar_eq_count]
              apply MeasureTheory.MeasurePreserving.id
        . rw [← my_haar_eq_count]
          apply Lp.memLp
        . rw [← my_haar_eq_count]
          apply Lp.memLp
      .
        simp
        simp_rw [inv_eq_one_div]
        apply tendsto_one_div_add_atTop_nhds_zero_nat
  }
  intro z
  by_contra!
  have lim_ge := ge_of_tendsto tendsto_sub (b := 1) (by
    apply Filter.Eventually.of_forall
    intro n
    rw [H_n_conv_zero_eq]
    simp [new_seq, seq]
    have norm_gt := Nat.nth_mem_of_infinite s_infinite ((arzela_seq n))
    simp at norm_gt
    apply le_of_lt
    exact norm_gt
  )

  apply_fun (fun f => f 1 - f s⁻¹) at this
  simp [ConstLipschitzH] at this
  norm_cast at this
  grind



-- Case two of Theorem 3.6
set_option maxHeartbeats 2000000 in
lemma nontrivial_harmonic_case_two (f_n_limit: ∃ s: S, ¬(Filter.Tendsto (fun n: ℕ => MeasureTheory.eLpNorm (f_n n - (Conv (f_n n) (delta s.val))) 1 MeasureTheory.volume) Filter.atTop (nhds 0))): ∃ F: LipschitzH , ∀ z: ℂ, F ≠ ConstLipschitzH z := by
  obtain ⟨s, hs⟩ := f_n_limit
  let H_n := fun n g => if  ((f_n n g⁻¹) - (Conv (f_n n) (delta s.val)) g⁻¹) ≠ 0 then ((f_n n g⁻¹) - (Conv (f_n n) (delta s.val)) g⁻¹) / |((f_n n g⁻¹) - (Conv (f_n n) (delta s.val)) g⁻¹)| else 1

  -- TODO - why can't we write '∞' here
  have H_n_norm: ∀ n: ℕ, MeasureTheory.eLpNorm (H_n n) (p := ⊤) MeasureTheory.volume = 1 := by
    intro n
    simp [H_n]
    simp [MeasureTheory.eLpNormEssSup]
    --rw [essSup_eq_sInf]
    simp [MeasureTheory.volume]
    rw [my_haar_eq_count]
    simp
    have h_norm_one: ∀ x, ‖H_n n x‖ₑ = 1 := by
      simp [H_n]
      intro g
      split_ifs
      . simp
      .

        rename_i foo
        by_cases val_pos: 0 ≤ ((f_n n g⁻¹) - (Conv (f_n n) (delta s.val)) g⁻¹)
        .
          rw [abs_of_nonneg val_pos]
          rw [div_self]
          . simp
          . exact foo
        .
          rw [abs_of_neg]
          .
            rw [div_neg_self]
            .
              simp
            . exact foo
          . linarith

    unfold H_n at h_norm_one
    simp at h_norm_one
    simp_rw [h_norm_one]
    simp

  have H_n_diff_pos: ∀ n: ℕ,  ∀ (i : G), 0 ≤ H_n n i⁻¹ * f_n n i - H_n n i⁻¹ * f_n n ((↑s)⁻¹ * i) := by
    intro n g
    simp [H_n]
    simp [f_conv_delta]
    split_ifs
    . linarith
    .
      rename_i diff_zero
      by_cases val_pos: 0 ≤ f_n n g - f_n n ((↑s)⁻¹ * g)
      .
        rw [abs_of_nonneg val_pos]
        rw [div_self]
        . linarith
        . assumption
      .
        rw [abs_of_neg]
        . rw [div_neg_self]
          . linarith
          . assumption
        .
          simpa using val_pos

  have fn_sub_norm: ∀ n: ℕ, eLpNorm (f_n n - (Conv (f_n n) (delta s.val))) 1 = ENNReal.ofReal |((Conv (H_n n) (f_n n)) 1) - ((Conv (H_n n) (f_n n)) s⁻¹)| := by
    intro n
    simp [eLpNorm, eLpNorm']
    rw [lintegral_g_eq_add]
    conv =>
      lhs
      arg 1
      intro g
      rw [Real.enorm_eq_ofReal_abs]
      arg 1
      equals (H_n n g⁻¹) * (f_n n g - (Conv (f_n n) (delta s.val)) g) =>
        simp [H_n]
        split_ifs
        .
          rename_i diff_eq_zero
          simp [diff_eq_zero]
        .
          rename_i diff_ne_zero
          by_cases val_pos: 0 ≤ ((f_n n g) - (Conv (f_n n) (delta s.val)) g)
          .
            rw [abs_of_nonneg]
            .
             rw [div_self]
             simp
             apply diff_ne_zero
            . exact val_pos
          .
            rw [abs_of_neg]
            .
              rw [div_neg_self]
              simp
              exact diff_ne_zero
            .
              simpa using val_pos

    rw [conv_eq_sum (by
      apply conv_exists_fin_supp
      right
      unfold f_n
      simp
      apply Set.Finite.inter_of_right
      apply Set.Finite.subset (hs := ?_) (ht := Finset.support_sum _ _)
      refine Set.Finite.biUnion' ?_ ?_
      . exact Set.toFinite (Membership.mem Finset.univ.val)
      . intro m hm
        apply mu_conv_finsupp
    )]

    rw [conv_eq_sum (by
      apply conv_exists_fin_supp
      right
      unfold f_n
      simp
      apply Set.Finite.inter_of_right
      apply Set.Finite.subset (hs := ?_) (ht := Finset.support_sum _ _)
      refine Set.Finite.biUnion' ?_ ?_
      . exact Set.toFinite (Membership.mem Finset.univ.val)
      . intro m hm
        apply mu_conv_finsupp
    )]


    conv =>
      rhs
      arg 1
      arg 1
      rw [← Summable.tsum_sub (by
        apply summable_of_finite_support
        simp
        apply Set.Finite.inter_of_right
        unfold f_n
        simp
        apply Set.Finite.inter_of_right
        apply Set.Finite.subset (hs := ?_) (ht := Finset.support_sum _ _)
        refine Set.Finite.biUnion' ?_ ?_
        . exact Set.toFinite (Membership.mem Finset.univ.val)
        .
          intro m hm
          apply Set.Finite.of_injOn (f := fun a => ((Additive.toMul a))⁻¹) (ht := mu_conv_finsupp  m)
          .
            intro a ha
            exact ha
          . intro a ha b hb
            simp
      ) (by
        apply summable_of_finite_support
        simp
        apply Set.Finite.inter_of_right
        unfold f_n
        simp
        apply Set.Finite.inter_of_right
        apply Set.Finite.subset (hs := ?_) (ht := Finset.support_sum _ _)
        refine Set.Finite.biUnion' ?_ ?_
        . exact Set.toFinite (Membership.mem Finset.univ.val)
        .
          intro m hm
          apply Set.Finite.of_injOn (f := fun a => s.val⁻¹ * ((Additive.toMul a))⁻¹ ) (ht := mu_conv_finsupp  m)
          .
            intro a ha
            exact ha
          . intro a ha b hb
            simp
      )]
    simp_rw [mul_sub]
    simp_rw [f_conv_delta]
    rw [← ENNReal.ofReal_tsum_of_nonneg]
    rw [ENNReal.ofReal_eq_ofReal_iff]
    rw [← Function.Injective.tsum_eq (γ := G) (β := Additive (G)) (g := fun a => Additive.ofMul (a⁻¹))]
    simp
    unfold Additive.ofMul
    simp
    simp [Neg.neg, Multiplicative.ofAdd]
    unfold Additive.toMul
    unfold Additive.ofMul
    simp
    rw [abs_of_nonneg]
    .
      apply tsum_nonneg
      apply H_n_diff_pos n
    .
      simp
      apply Function.Injective.comp
      . exact neg_injective
      . exact fun ⦃a₁ a₂⦄ a ↦ a
    .
      simp
      intro g hg
      use g⁻¹
      simp
    .
      apply tsum_nonneg
      apply H_n_diff_pos n
    . simp
    . apply H_n_diff_pos n
    .
      simp_rw [← mul_sub]
      apply summable_of_finite_support
      simp
      apply Set.Finite.inter_of_right
      apply Set.Finite.subset (hs := ?_) (ht := Function.support_sub _ _)
      simp
      refine ⟨?_, ?_⟩
      . apply f_n_fin_supp
      .
        apply Set.Finite.of_injOn (f := fun a => s.val⁻¹ * a) (ht := f_n_fin_supp n)
        . intro a ha
          simpa using ha
        . simp


  have haar_eq_haar_add : myHaar = myHaarAddOpp := by
    rfl

  have h_conv_f_bounded (n: ℕ): eLpNorm (Conv (H_n n) (f_n n)) ⊤ ≤ 1 := by
    unfold Conv
    rw [← Function.comp_def]
    rw [MeasureTheory.eLpNorm_comp_measurePreserving (ν := myHaarAddOpp)]
    .
      grw [ENNReal.eLpNorm_convolution_le_enorm_mul (p := ⊤) (q := 1)]
      have norm_one := f_n_norm_one (n )
      simp [volume] at norm_one
      rw [haar_eq_haar_add] at norm_one
      rw [norm_one]
      simp only  [volume] at H_n_norm
      rw [haar_eq_haar_add] at H_n_norm
      rw [H_n_norm]
      simp
      simp [enorm]
      . simp
      . simp
      . simp
      . simp
      . apply AEMeasurable.of_discrete
      . apply AEMeasurable.of_discrete
    . apply AEStronglyMeasurable.of_discrete
    . exact measure_preserving_op_add

  have conv_laplce_norm (n: ℕ): eLpNorm ((Laplace_b ((Conv (H_n n)) (f_n n)))) ⊤ (μ := volume (α := G)) ≤ eLpNorm (H_n n) ⊤ * (eLpNorm (Laplace_b (f_n n)) 1 (μ := volume (α := G))) := by
    rw [laplace_conv_eq_laplace_right]
    .
      unfold Conv
      eta_reduce
      simp only [volume]
      rw [haar_eq_haar_add]

      have my_norm := ENNReal.eLpNorm_convolution_le_enorm_mul (f := H_n n) (G := (Additive G)) (L := (ContinuousLinearMap.mul ℝ ℝ))
        (g := Laplace_b (f_n n)) (r := ⊤) (p := ⊤) (q := 1) (μ := myHaarAddOpp)
        (by simp)
        (by simp)
        (by simp)
        (by simp)
        (by apply AEMeasurable.of_discrete)
        (by apply AEMeasurable.of_discrete)


      grw [my_norm]
      simp [enorm]
    .
      apply conv_exists_fin_supp
      right
      exact f_n_fin_supp n
    . apply f_n_nonneg
    . exact f_n_fin_supp n


  let conv_h_n_cont (n: ℕ): C(G, ℝ) := {
    toFun := Conv (H_n n) (f_n n),
    continuous_toFun := by exact continuous_of_discreteTopology
  }

  have abs_conv_le_one: ∀ g: G, ∀ n: ℕ,  |Conv (H_n n) (f_n n) g| ≤ 1 := by
    intro g n
    have norm_bound := h_conv_f_bounded n
    simp [eLpNorm, eLpNormEssSup] at norm_bound
    have ae_le := ENNReal.ae_le_essSup (fun x ↦ ‖Conv (H_n n) (f_n n) x‖ₑ) (μ := volume)
    simp [volume] at ae_le
    rw [my_haar_eq_count] at ae_le
    rw [count_ae_everywhere] at ae_le
    simp_rw [Real.enorm_eq_ofReal_abs] at ae_le
    simp_rw [Real.enorm_eq_ofReal_abs] at norm_bound
    norm_cast at ae_le
    simp [volume] at norm_bound
    rw [my_haar_eq_count] at norm_bound
    specialize ae_le g
    have ennreal_bound := le_trans ae_le norm_bound
    norm_cast at ennreal_bound

  have conv_h_n_lipschitz (n: ℕ): LipschitzWith 2 (conv_h_n_cont n) := by
    unfold conv_h_n_cont
    simp [LipschitzWith]
    intro x y
    by_cases x_eq_y: x = y
    . simp [x_eq_y]
    .
      norm_cast
      rw [edist_dist]
      rw [Real.dist_eq]
      rw [edist_dist]
      conv =>
        rhs
        equals ENNReal.ofReal (2 * (dist x y)) =>
          rw [ENNReal.ofReal_mul]
          . simp
          . linarith
      rw [ENNReal.ofReal_le_ofReal_iff]
      .
        grw [abs_sub]
        grw [abs_conv_le_one x]
        grw [abs_conv_le_one y]
        rw [one_add_one_eq_two]
        simp
        simp [dist]
        have dist_ne_zero: dist x y ≠ 0 := by
          exact dist_ne_zero.mpr x_eq_y
        simp [dist] at dist_ne_zero
        omega
      . simp [dist]




  have compact_closure_f: IsCompact (closure ( (Set.range (fun n => (Conv (H_n n) (f_n n)))))) := by
    rw [Pi.isCompact_closure_iff]
    intro g
    apply Bornology.IsBounded.isCompact_closure
    rw [Metric.isBounded_iff]
    use 2
    intro x hx y hy
    simp at hx
    simp at hy
    obtain ⟨n, h_x_n⟩ := hx
    obtain ⟨m, h_y_m⟩ := hy
    rw [Real.dist_eq]
    grw [abs_sub]
    rw [← h_x_n, ← h_y_m]
    grw [abs_conv_le_one]
    grw [abs_conv_le_one]
    linarith


  rw [Filter.not_tendsto_iff_exists_frequently_notMem] at hs
  obtain ⟨eps, h_eps, frequently_gt_eps⟩ := hs
    -- We obtain a subsequence where all of the points satisfy the 'norm > ε' condition
  obtain ⟨eps_seq, mono_eps_seq, eps_seq_gt_x⟩ := Filter.extraction_of_frequently_atTop frequently_gt_eps

  -- Along this sequence, the evauation of 'Conv H_n f_n' at is leq to 1,
  -- so it's in a compact set
  have locally_bounded_at_g: ∀ g: G, ∀ n, Conv (H_n (eps_seq n)) (f_n (eps_seq n)) g ∈ Metric.closedBall 0 1 := by
    intro g n
    simp
    apply abs_conv_le_one


  have h_n_pointwise_converge := IsCompact.tendsto_subseq compact_closure_f (x := fun n => (Conv (H_n (eps_seq n)) (f_n (eps_seq n)))) (by
    intro n
    simp
    apply Set.mem_of_subset_of_mem (_root_.subset_closure)
    simp
  )
  -- We now have a sequence of functions which converges pointwise, where all of the
  -- elements of the sequence satisfy the 'norm > ε' condition
  obtain ⟨F, F_mem, seq, seq_mono, tendsto_F⟩ := h_n_pointwise_converge
  let F_lipschitzh := nontrivial_harmonic_common 2 (eps_seq ∘ seq) (by
    apply Filter.Tendsto.comp (x := Filter.atTop) (y := Filter.atTop)
    . exact StrictMono.tendsto_atTop mono_eps_seq
    . exact StrictMono.tendsto_atTop seq_mono
  ) F H_n conv_h_n_lipschitz tendsto_F H_n_norm
  use F_lipschitzh
  --use F_lipschitzh
  intro z
  have not_conv_tendsto_zero: ¬Filter.Tendsto (fun n => ENNReal.ofReal |Conv (H_n (eps_seq (seq n))) (f_n (eps_seq (seq n))) 1 - Conv (H_n (eps_seq (seq n))) (f_n (eps_seq (seq n))) (↑s)⁻¹|) Filter.atTop (nhds 0) := by
    rw [Filter.not_tendsto_iff_exists_frequently_notMem]
    use eps
    refine ⟨h_eps, ?_⟩
    simp_rw [← fn_sub_norm]
    apply Filter.Frequently.of_forall
    intro n
    exact eps_seq_gt_x (seq n)

  have F_non_const: F 1 ≠ F s⁻¹ := by
    by_contra!
    rw [← sub_eq_zero] at this
    rw [tendsto_pi_nhds] at tendsto_F
    have lim_f_sub := Filter.Tendsto.sub (tendsto_F 1) (tendsto_F s⁻¹)
    rw [this] at lim_f_sub
    simp_rw [Function.comp_def] at lim_f_sub
    rw [tendsto_zero_iff_abs_tendsto_zero] at lim_f_sub
    rw [Function.comp_def] at lim_f_sub
    have f_sub_ennreal := ENNReal.tendsto_ofReal lim_f_sub
    simp only [ENNReal.ofReal_zero] at f_sub_ennreal
    contradiction

  by_contra!
  -- TODO - there must be a cleaner way
  have app_one_eq: F_lipschitzh 1 = ConstLipschitzH z (1: G) := by
    rw [this]
  unfold F_lipschitzh ConstLipschitzH at app_one_eq
  simp [DFunLike.coe] at app_one_eq

  have app_s_inv_eq: F_lipschitzh s⁻¹ = ConstLipschitzH z (s⁻¹: G) := by
    rw [this]
  unfold F_lipschitzh ConstLipschitzH at app_s_inv_eq
  simp [DFunLike.coe] at app_s_inv_eq
  rw [← app_one_eq] at app_s_inv_eq
  norm_cast at app_s_inv_eq
  rw [eq_comm] at app_s_inv_eq
  simp [nontrivial_harmonic_common] at app_s_inv_eq
  contradiction

#print sorries nontrivial_harmonic_case_one
#print sorries nontrivial_harmonic_case_two

#synth OrderTopology ENNReal

-- Theorem 3.6 - a non-constant harmonic function exists on G
theorem exists_nontrivial_harmonic: ∃ F: LipschitzH , ∀ z: ℂ, F ≠ ConstLipschitzH z := by
  by_cases f_n_limit: ∃ s: S, ¬(Filter.Tendsto (fun n: ℕ => MeasureTheory.eLpNorm (f_n n - (Conv (f_n n) (delta s.val))) 1 MeasureTheory.volume) Filter.atTop (nhds 0))
  . exact nontrivial_harmonic_case_two f_n_limit
  .
    simp at f_n_limit
    exact nontrivial_harmonic_case_one (by
      intro s
      exact f_n_limit s.val s.property
    )

lemma rangeRestrict_range {A B: Type*} [Group A] [Group B] (f: A →* B): f.rangeRestrict.range = ⊤ := by
  ext a
  have a_prop := a.property
  simp only [mem_top, iff_true]
  rw [MonoidHom.mem_range] at a_prop
  rw [MonoidHom.mem_range]
  obtain ⟨x, hx⟩ := a_prop
  use x
  ext
  simp [hx]


lemma rho_g_case_finite (hr: Finite (↥(rho_g))): Nonempty (Theorem3_1_Input G) := by
  have quotient_iso := QuotientGroup.quotientKerEquivRange (GRepW_base)
  unfold rho_g at hr

  have ker_finite_index := Subgroup.finiteIndex_ker (GRepW_base)
  let G' := (GRepW_base).ker

  let G'_action := (GRepW_base).restrict G'

  have act_ker (g: G) := MonoidHom.mem_ker (f := (GRepW_base)) (x := g)

  have act_v (g: G) (hg: g ∈ (GRepW_base).ker) (f: LipschitzH ): Submodule.Quotient.mk (GRep  g f) = (Submodule.Quotient.mk (f) : W) := by
    simp [GRep]
    have apply_g := (act_ker g).mp hg
    simp [GRepW_base, GRepW_non_invertible, GRep] at apply_g
    apply_fun Units.val at apply_g
    rw [Representation.asGroupHom_apply] at apply_g
    rw [Representation.quotient_apply] at apply_g
    apply_fun (fun y => y (Submodule.Quotient.mk f)) at apply_g
    simp at apply_g
    exact apply_g

  let extract_const (f: LipschitzH) (hf: f ∈ ConstF ) := f 1

  simp_rw [Submodule.Quotient.eq] at act_v

  -- As proved in 'act_v', we have  '(GRep g f) - f' is a constant function. We can therefore evaluate
  -- it any poitn in G (here, 1) to get the constant
  let lambda_g := fun (g: G') (f: LipschitzH ) => ((GRep g.val) f - f) 1
  let lambda_g_dual (g: G'): Module.Dual ℂ (LipschitzH) := {
    toFun := fun w => lambda_g g w
    map_add' := by
      intro x y
      simp [lambda_g]
      abel
    map_smul' := by
      intro c x
      simp [lambda_g]
      rw [mul_sub]
  }

  -- TODO - this could be much cleaner
  have act_eq_lambda (g: G) (hg: g ∈ (GRepW_base).ker) (f: LipschitzH ): (gAct g f) = f + ConstLipschitzH (lambda_g ⟨g, hg⟩ f) := by
    have act := act_v g hg f
    simp [GRep, gAct, ConstF] at act
    simp [gAct]
    obtain ⟨y, hy⟩ := act
    simp [lambda_g, GRep, gAct]
    ext a
    simp
    apply_fun (fun l => l.toFun) at hy
    have app_a := congrFun hy a
    simp [lipschitz_sub_tofun] at app_a
    rw [eq_comm] at app_a
    apply eq_add_of_sub_eq at app_a
    rw [app_a]
    rw [add_comm]
    simp [LipschitzH_apply]
    simp [LipschitzH_apply] at hy
    have other_app := congrFun hy 1
    simp at other_app
    rw [← other_app]
    simp [ConstLipschitzH]

  have lambda_const (g: (GRepW_base).ker) (f: LipschitzH ) (k: ℂ): (lambda_g g (f + (ConstLipschitzH k))) = (lambda_g g f) := by
    simp [lambda_g, GRep, gAct]
    simp [ConstLipschitzH]


  let lambda_g_hom: G' →* Multiplicative (Module.Dual ℂ (LipschitzH)) := {
    toFun := fun g => Multiplicative.ofAdd (lambda_g_dual g)
    map_one' := by
      simp [lambda_g_dual]
      simp [lambda_g]
      ext f
      simp
    map_mul' := by
      intro g h
      ext f
      simp [lambda_g_dual]
      conv =>
        lhs
        dsimp [lambda_g]
      simp [GRep]
      rw [gAct_mul]
      rw [act_eq_lambda h.val h.property]
      rw [act_eq_lambda g.val g.property]
      rw [lambda_const]
      simp [ConstLipschitzH]
      group
  }

  by_cases lambda_g_infinite: Infinite (lambda_g_hom.range)
  .

    apply g_hom_abelian G' ?_ lambda_g_hom.rangeRestrict ?_ lambda_g_hom.rangeRestrict.range ?_ ?_ ?_ ?_
    . simp [G']
      exact ker_finite_index
    . exact MonoidHom.rangeRestrict_surjective lambda_g_hom
    . rw [rangeRestrict_range]
      simp
      -- TODO: PR this to mathlib
      apply (Equiv.infinite_iff (α := lambda_g_hom.range) _).mp
      . exact lambda_g_infinite
      . exact {
          toFun := fun g => ⟨g, trivial⟩
          invFun := fun g => g.val
          left_inv := by simp [Function.LeftInverse]
          right_inv := by simp [Function.RightInverse, Function.LeftInverse]
        }
    . exact {
        is_comm := {
          comm := by
            intro a b
            ext
            simp
            rw [add_comm]
        }
      }
    . rw [Subgroup.finiteIndex_iff]
      rw [rangeRestrict_range]
      simp
    . rw [rangeRestrict_range]
      simp
      exact Group.FG.out
  .
    simp only [not_infinite_iff_finite] at lambda_g_infinite
    let G'' := lambda_g_hom.ker
    have G''_finite_index := Subgroup.finiteIndex_ker lambda_g_hom

  -- TODO - this could be a lot cleaner
    have G''_act_v (g: lambda_g_hom.ker) (x: G) (f: LipschitzH ): f (x * g) = f x := by
      specialize act_v g
      simp at act_v
      have g_prop := g.property
      rw [MonoidHom.mem_ker] at g_prop
      simp [lambda_g_hom, lambda_g_dual, lambda_g, GRep] at g_prop
      apply_fun (fun p => p f) at g_prop
      simp at g_prop
      rw [sub_eq_zero] at g_prop
      simp [gAct] at g_prop
      specialize act_v f
      simp [GRep, gAct, ConstF] at act_v
      obtain ⟨y, hy⟩ := act_v
      simp [ConstLipschitzH] at hy
      apply_fun (fun l => l.toFun) at hy
      simp at hy
      rw [Pi.sub_def] at hy
      have eval_one := hy
      apply_fun (fun f => f 1) at eval_one
      apply_fun (fun f => f x) at hy
      simp at hy
      simp at eval_one
      rw [← g_prop] at eval_one
      simp at eval_one
      rw [eq_comm] at hy
      apply eq_add_of_sub_eq' at hy
      simp
      rw [hy]
      simp
      exact eval_one


    -- View G'' as a subgroup of G
    let G''_subgroup_G := (Subgroup.map G'.subtype lambda_g_hom.ker)

    -- TODO - clean up this proof
    have G''_subgroup_finite_index: G''_subgroup_G.FiniteIndex := by
      unfold G''_subgroup_G
      rw [Subgroup.finiteIndex_iff]
      rw [Subgroup.index_map]
      simp
      unfold G'
      rw [Subgroup.finiteIndex_iff] at ker_finite_index
      refine ⟨?_, ker_finite_index⟩
      rw [Subgroup.finiteIndex_iff] at G''_finite_index
      exact G''_finite_index


    have finite_quotient := Subgroup.finite_quotient_of_finiteIndex (H := G''_subgroup_G)

    have coset_union := QuotientGroup.univ_eq_iUnion_smul G''_subgroup_G
    have f_range_eq (f: LipschitzH ): Set.range f = Set.range ((fun (x: G ⧸ G''_subgroup_G) => f (x.out))) := by
      ext a
      refine ⟨?_, ?_⟩
      . intro ha
        simp at ha
        obtain ⟨y, hy⟩ := ha
        have y_mem: y ∈ Set.univ := by simp
        rw [coset_union] at y_mem
        simp at y_mem
        obtain ⟨i, hi⟩ := y_mem
        rw [Set.mem_smul_set] at hi
        obtain ⟨x, x_mem, y_eq⟩ := hi
        rw [← y_eq] at hy

        unfold G''_subgroup_G at x_mem
        simp at x_mem
        obtain ⟨x_mem_g', hx'⟩ := x_mem

        have x_mem_ker: ⟨x, x_mem_g'⟩ ∈ lambda_g_hom.ker := by
          simp
          exact hx'

        let x_ker: lambda_g_hom.ker := ⟨⟨x, x_mem_g'⟩, x_mem_ker⟩
        have f_translate := G''_act_v x_ker i.out f

        simp only [Set.mem_range]
        use i
        rw [← f_translate]
        exact hy
      . intro ha
        simp only [Set.mem_range] at ha
        obtain ⟨y, hy⟩ := ha
        simp
        simp at hy
        use y.out


    have all_f_const (f: LipschitzH ): ∃ z: ℂ, f = ConstLipschitzH z := by
      have f_max_re := Set.Finite.exists_maximalFor (fun y => ‖y.re‖) (Set.range f) ?_ ?_
      obtain ⟨z_re, z_re_mem, hz_re⟩ := f_max_re

      have z_re_max: ∀ p ∈ Set.range f, ‖p.re‖ ≤ ‖z_re.re‖ := by
        intro p hp
        simp at hp
        obtain ⟨y, hy⟩ := hp
        by_cases p_le_z: ‖p.re‖ ≤ ‖z_re.re‖
        . exact p_le_z
        . simp at p_le_z

          have f_le := hz_re (j := f.toFun y) ?_ ?_
          .
            simp at f_le
            rw [← hy]
            exact f_le
          . simp
          . simp
            rw [← hy] at p_le_z
            linarith

      simp at z_re_mem
      obtain ⟨g_re, f_g_re_eq⟩ := z_re_mem


      have f_max_im := Set.Finite.exists_maximalFor (fun y => ‖y.im‖) (Set.range f) ?_ ?_
      obtain ⟨z_im, z_im_mem, hz_im⟩ := f_max_im

      have z_im_max: ∀ p ∈ Set.range f, ‖p.im‖ ≤ ‖z_im.im‖ := by
        intro p hp
        simp at hp
        obtain ⟨y, hy⟩ := hp
        by_cases p_le_z: ‖p.im‖ ≤ ‖z_im.im‖
        . exact p_le_z
        . simp at p_le_z

          have f_le := hz_im (j := f.toFun y) ?_ ?_
          .
            simp at f_le
            rw [← hy]
            exact f_le
          . simp
          . simp
            rw [← hy] at p_le_z
            linarith

      simp at z_im_mem
      obtain ⟨g_im, f_g_im_eq⟩ := z_im_mem

      have f_re_const := harmonic_abs_max_implies_const  (Complex.re ∘ f.toFun) (by
        have f_harmonic := f.harmonic
        simp [Harmonic] at f_harmonic
        simp [Laplace_b, f_conv_mu]
        ext x
        simp
        have f_harmonic_real := f_harmonic x
        apply_fun Complex.re at f_harmonic_real
        simp at f_harmonic_real
        rw [sub_eq_zero]
        exact f_harmonic_real
      ) g_re (by
        intro a
        specialize z_re_max ((f.toFun a)) (by (
          simp
        ))
        rw [← f_g_re_eq] at z_re_max
        simpa using z_re_max
      )

      have f_im_const := harmonic_abs_max_implies_const  (Complex.im ∘ f.toFun) (by
        have f_harmonic := f.harmonic
        simp [Harmonic] at f_harmonic
        simp [Laplace_b, f_conv_mu]
        ext x
        simp
        have f_harmonic_real := f_harmonic x
        apply_fun Complex.im at f_harmonic_real
        simp at f_harmonic_real
        rw [sub_eq_zero]
        exact f_harmonic_real
      ) g_im (by
        intro a
        specialize z_im_max ((f.toFun a)) (by (
          simp
        ))
        rw [← f_g_im_eq] at z_im_max
        simpa using z_im_max
      )

      let const_val: ℂ := {
        re := (f g_re).re,
        im := (f g_im).im
      }

      have f_const: f.toFun = fun x ↦ const_val  := by
        ext g
        apply Complex.ext
        .
          have app_re := congrFun f_re_const g
          simpa using app_re
        . have app_im := congrFun f_im_const g
          simpa using app_im





      --have f_const := harmonic_extreme_val_implies_const  f.toFun ?_ g ?_
      use const_val
      ext a
      rw [f_const]
      simp [ConstLipschitzH]
      .
        rw [f_range_eq]
        apply Set.finite_range
      . apply Set.range_nonempty
      .
        rw [f_range_eq]
        apply Set.finite_range
      . apply Set.range_nonempty

    obtain ⟨f, nontrivial_f⟩ := exists_nontrivial_harmonic
    obtain ⟨z, f_eq_const⟩ := all_f_const f
    specialize nontrivial_f z
    contradiction


-- TODO - upstream to mathlib
lemma s_pow_inv (n: ℕ): (S^n)⁻¹ = (S⁻¹)^n := by
  induction n with
  | zero =>
    simp only [pow_zero, inv_one]
  | succ n ih =>
    simp only [inv_pow]

-- TODO - upstream to mathlib
lemma mem_closure_iff_mem_pow (g: G): g ∈ Subgroup.closure S ↔ ∃ n, g ∈ S^n := by
  refine ⟨?_, ?_⟩
  .
    intro hg
    induction hg using Subgroup.closure_induction with
    | one =>
      use 1
      simp
      exact hGS.one_mem
    | inv a ha a_mem =>
      obtain ⟨n, hn⟩ := a_mem
      use n
      rw [← Finset.mem_inv']
      rw [s_pow_inv]
      rw [← S_eq_Sinv]
      exact hn
    | mem s hs =>
      use 1
      simp
      exact hs
    | mul a b ha hb iha ihb =>
      obtain ⟨p, hp⟩ := iha
      obtain ⟨q, hq⟩ := ihb
      use (p + q)
      rw [pow_add]
      rw [Finset.mem_mul]
      refine ⟨a, hp, b, hq, rfl⟩
  .
    intro _
    apply mem_closure g

-- TODO - get rid of the duplicate 'hGS'
lemma exists_theorem_3_1_input [hGS: Generates ] {d: ℕ} (hd: HasPolynomialGrowthD S d): Nonempty (Theorem3_1_Input G) := by
  by_cases rho_g_infinite: Infinite (↥(rho_g))
  . exact rho_g_case_infinite hd rho_g_infinite
  . exact rho_g_case_finite (by simpa using rho_g_infinite)


-- lemma poly_growth_implies (S': Finset G) (d: ℕ) (hd: HasPolynomialGrowthD S d): HasPolynomialGrowthD S' d := by

--   simp [HasPolynomialGrowthD] at hd
--   obtain ⟨a, s_poly⟩ := hd
--   simp [HasPolynomialGrowthD]
--   have b: ℕ := 1
--   have C: ℕ := 0
--   use #(S ^ C) * ↑a
--   intro n hn
--   --have inject_s_card := Finset.card_le_card_of_injOn (s := S') (t := S ^ C) sorry sorry sorry
--   specialize s_poly n hn
--   have le_pow := Finset.card_pow_le (s := S') (n := n)

--   calc
--     #(S' ^ n) ≤ #((S ^ C) * S^n) := sorry
--     _ ≤ #((S ^ C)) * #(S ^ n) := by
--       exact Finset.card_mul_le
--     _ ≤ #((S ^ C)) * (↑a * n ^ d) := by
--       exact Nat.mul_le_mul_left (#(S ^ C)) s_poly

--     -- _ = #((S ^ n) ^ C) := by
--     --   rw [← pow_mul]
--     --   rw [mul_comm]
--     --   rw [pow_mul]
--     -- _ ≤ #(S ^ n)^C := by exact Finset.card_pow_le
--     -- _ ≤ (↑a * n ^ d)^C := by
--     --   exact Nat.pow_le_pow_left s_poly C

--   rw [← mul_assoc]
--   -- calc
--   --   #(S' ^ n) ≤ #(S') ^ n := by apply Finset.card_pow_le
--   --   _ ≤ #(S ^ C) ^ n := by exact Nat.pow_le_pow_left inject_s_card n
--   --   _ ≤ (↑a * C ^ d)^n := by exact Nat.pow_le_pow_left s_poly n


-- #print axioms poly_growth_implies







-- TODO - get rid of this, since all groups must be inhabited
variable [Inhabited G]

structure PreservesProd (T: Type*) (l h: List G) (γ: G) where
  prod_eq: l.prod = h.prod
  same_sum: (l.map (fun s => if s = γ then 1 else 0)).sum = (h.map (fun s => if s = γ then 1 else 0)).sum


abbrev countElemOrInv {T: Type*} [ht: Group T] [heq: DecidableEq T] {E: Set T} (l: List E) (γ: T): ℤ := (l.map (fun (s: E) => if s = γ then 1 else if s = γ⁻¹ then -1 else 0)).sum
abbrev isElemOrInv {T: Type*} [ht: Group T] [heq: DecidableEq T] (g: T): T → Bool := fun a => decide (a = g ∨ a = g⁻¹)
lemma take_count_sum_eq_exp {T: Type*} [ht: Group T] [heq: DecidableEq T] {E: Set T} (l: List E) (g: T) (hg: g ≠ g⁻¹) (hl: ∀ val ∈ l, val = g ∨ val = g⁻¹): l.unattach.prod = g^(countElemOrInv l g) := by
  induction l with
  | nil =>
    simp [countElemOrInv]
  | cons h t ih =>
    simp [countElemOrInv]
    by_cases h_eq_g: h = g
    .
      simp [h_eq_g]
      rw [ih]
      . rw [← zpow_one_add]
      . simp at hl
        intro val hval
        have hl_right := hl.2 val (by simp) (by simp [hval])
        exact hl_right
    .
      have h_eq_inv: h = g⁻¹ := by
        specialize hl h
        simp at hl
        simp  [h_eq_g] at hl
        exact hl
      simp [h_eq_g, h_eq_inv]
      rw [ih]
      .
        rw [← zpow_neg_one]
        rw [← zpow_add]
        simp [hg.symm]
      .
        simp at hl
        intro val hval
        have hl_right := hl.2 val (by simp) (by simp [hval])
        exact hl_right

open Additive


lemma list_filter_one {T: Type*} [DecidableEq T] [Group T] (l: List T): (l.filter (fun s => !decide (s = 1))).prod = l.prod := by
  induction l with
  | nil =>
    simp
  | cons h t ih =>
    simp
    by_cases h_eq_one: h = 1
    .
      simp [h_eq_one]
      exact ih
    .
      rw [List.filter_cons]
      simp [h_eq_one]
      exact ih

def e_i_regular_helper {G: Type*} [Group G] [DecidableEq G] {S: Finset G} (φ: (Additive G) →+ ℤ) (γ: G) (s: S): G := (ofMul s.val) +  ((-1 : ℤ) • (φ (ofMul s.val))) • (ofMul (γ))

def E_helper (φ: (Additive G) →+ ℤ) (γ: G) := {γ, γ⁻¹} ∪ Set.range (ι := S) (e_i_regular_helper φ γ)

lemma take_drop_len {T: Type*} {l: List T} {p: T → Bool}: (l.takeWhile p).length + (l.dropWhile p).length = l.length := by
  suffices h: l.takeWhile p ++ l.dropWhile p = l by
    nth_rw 3 [← h]
    rw [List.length_append]
  exact List.takeWhile_append_dropWhile

def gamma_m_helper {G: Type*} [Group G] [DecidableEq G] {S: Finset G} (φ: (Additive G) →+ ℤ) (γ: G) (m: ℤ) (s: S): G := γ^m * (e_i_regular_helper φ γ s) * γ^(-m)

lemma gamma_m_eq_mulAt (φ: (Additive G) →+ ℤ) (γ: G) (m: ℤ) (s: S): gamma_m_helper φ γ m s = (MulAut.conj ((γ^m))) (e_i_regular_helper φ γ s) := by
  dsimp [gamma_m_helper]
  simp


-- The set {γ_m_i}_{m ≤ n}
omit hGS in
def three_two_S_n {G: Type*} [Group G] [DecidableEq G] (S: Finset G) (φ: (Additive G) →+ ℤ) (γ: G) (n: ℕ): Finset G := Finset.image (Function.uncurry (gamma_m_helper φ γ)) ((Finset.Icc (-n : ℤ) n).product S.attach)
--def three_two_S_n (φ: (Additive G) →+ ℤ) (γ: G) (n: ℕ): Finset G := (Function.uncurry (gamma_m_helper  φ γ)) '' ({ m: ℤ | |m| ≤ n} ×ˢ Set.univ)
-- The set of words of at length at most n generated by {γ_m_i}_{m ≤ n}
-- Note - This is based on https://terrytao.wordpress.com/2010/02/18/a-proof-of-gromovs-theorem/, which uses
-- "length at most n"
-- The Vikman paper says "words of length n", which seems incorrect

omit hGS in
lemma gamma_helper_subset_S_n {G: Type*} [Group G] [DecidableEq G] {S: Finset G} (φ: (Additive G) →+ ℤ) (γ: G) (n: ℕ): Set.range (gamma_m_helper (S := S) φ γ n) ⊆ three_two_S_n S  φ γ n := by
  intro val hval
  simp [three_two_S_n]
  use n
  refine ⟨by omega, ?_⟩
  simp at hval
  exact hval

omit hGS in
instance simple_finite_list {G: Type*} (P: Finset G) (n: ℕ): Finite { l: List P | l.length ≤ n } := by
  apply List.finite_length_le

-- List.finite_length_le
-- instance finite_list (P: Finset G) (n: ℕ): Finite { l: List G | l.length ≤ n ∧ ∀ x ∈ l, x ∈ P } := by
--   apply Finite.of_injective (β := { l: List P | l.length ≤ n }) (f := fun l => by (
--     have l_prop := l.property
--     simp only [Set.mem_setOf_eq] at l_prop
--     have mem_prop := l_prop.2
--     exact ⟨l.val.attach.map (fun g => ⟨g.val, mem_prop g.val g.property⟩), by (
--       simp
--       exact l_prop.1
--     )⟩
--   ))
--   simp
--   intro a b
--   induction a.val
--   .
--     simp
--     simp
--   . sorry
--   hint
--   intro hab
--   simp_rw [List.map_eq_iff] at hab
--   ext n g
--   specialize hab n
--   simp at hab
--   simp [Option.map] at hab
--   split at hab
--   .
--     split at hab
--     .
--       rename _ => some_eq
--       simp at some_eq
--       simp at hab
--       sorry
--     . sorry
--   . sorry

--   -- convert (Finset.range n).finite_toSet.biUnion (fun i _ => by (

--   --   sorry
--   -- ))
--   -- . sorry
--   -- . sorry
--   -- . sorry
--   -- . sorry
--   apply @Finite.of_injective _ (β := { l: List P | l.length ≤ n }) (List.finite_length_le _ _) (f := fun l => by (
--     simp at l
--     simp
--     let other: { l: List P // l.length ≤ n} := ⟨l.val.attach.map (fun q => ⟨q.val, ?_⟩), ?_⟩
--     . exact other
--     .
--       have prop := q.property
--       have l_prop := l.property.2
--       exact l_prop q prop
--     . simp
--       exact l.property.1
--   ))
--   simp
--   intro a b hab

--   simp at hab

--   rw [Subtype.eq_iff]
--   rw [List.map_eq_iff] at hab
--   ext n g
--   specialize hab n
--   simp only [List.getElem?_map] at hab

--   rw [List.eq_iff]
--   induction ha: a.val with
--   | nil =>


--       simp [ha]
--   | cons c =>
--     simp_rw [ha] at hab





--   --apply
--   sorry

omit hGS in
noncomputable def list_len_n {G: Type*} [Group G] [DecidableEq G] (S: Finset G) (φ: (Additive G) →+ ℤ) (γ: G) (n: ℕ): Finset (List ((three_two_S_n S φ γ n ))) := @Set.toFinset _ { l: List ((three_two_S_n S φ γ n )) | l.length ≤ n } (@Fintype.ofFinite _ _)

omit hGS in
noncomputable def three_two_B_n {G: Type*} [Group G] [DecidableEq G] (S: Finset G) (φ: (Additive G) →+ ℤ) (γ: G) (n: ℕ): Finset G := Finset.image (fun l => l.unattach.prod) (list_len_n S φ γ n )

--noncomputable def three_two_B_n_single_s (φ: (Additive G) →+ ℤ) (γ: G) (n: ℕ) (s: G): Finset G := Finset.image (fun l => l.unattach.prod) (list_len_n φ γ n (S := {s}))



--set_option maxHeartbeats 600000

-- If G has polynomial growth, than we can find an N such that S_n ⊆ B_n * B_n⁻¹
set_option maxHeartbeats 2000000 in
lemma new_three_two_poly_growth (d: ℕ) (hd: d >= 1) (hG: HasPolynomialGrowthD S d ) (γ: G) (φ: (Additive G) →+ ℤ) (hφ: Function.Surjective φ) (hγ: φ γ = 1) (s: G) (s_mem: s ∈ S): ∃ n, three_two_S_n (S := {s}) φ γ (n + 1) ⊆ ((three_two_B_n (S := {s}) φ γ n) * (three_two_B_n (S := {s}) φ γ n)⁻¹)  := by
  by_contra!
  simp [HasPolynomialGrowthD] at hG
  have little_o_poly := isLittleO_pow_exp_pos_mul_atTop d (b := Real.log 2) (Real.log_pos (by simp))
  simp at little_o_poly
  simp_rw [Real.exp_mul] at little_o_poly
  rw [Real.exp_log (by simp)] at little_o_poly
  apply Asymptotics.IsLittleO.eventuallyLE at little_o_poly
  apply Filter.Eventually.natCast_atTop at little_o_poly
  simp at little_o_poly

  -- Find an N' such that N^D < 2^N
  obtain ⟨N', hN⟩ := little_o_poly

  -- Write γ as a product of elements in S
  obtain ⟨gamma_list, gamma_list_prod⟩ := mem_S_prod_list γ
  simp [ProdS] at gamma_list_prod

  have gamma_list_inv: ((gamma_list.unattach).map (fun x => x⁻¹)).reverse.prod = γ⁻¹ := by
    rw [← List.prod_inv_reverse]
    rw [gamma_list_prod]

  have gamma_list_comm_inv: ((gamma_list.unattach).map (fun x => x⁻¹)) = (gamma_list.map (fun s => ⟨s.val⁻¹, hGS.has_inv s.val s.property⟩)).unattach := by
    clear gamma_list_prod gamma_list_inv
    induction gamma_list with
    | nil =>
      simp
    | cons a b ih =>
      simp
      exact ih

  rw [gamma_list_comm_inv] at gamma_list_inv



  -- Choose our N large enough that we can apply all of the above conditions
  let N := max N' (max gamma_list.length (max (φ (ofMul s)).natAbs 2))
  -- specialize hN N (by simp [N])
  -- specialize this N
  -- rw [Finset.not_subset] at this
  -- obtain ⟨p, ⟨p_mem, p_not_prod⟩⟩ := this
  -- rw [Finset.mem_mul.not] at p_not_prod
  -- push_neg at p_not_prod


  have disjoint_smul (M: ℕ) (hM: N ≤ M) (p: G) (p_mem: p ∈ three_two_S_n (S := {s}) φ γ (M + 1)) (p_not_prod: p ∉ three_two_B_n (S := {s}) φ γ M * (three_two_B_n (S := {s}) φ γ M)⁻¹): (p • three_two_B_n (S := {s}) φ γ M) ∩ (three_two_B_n (S := {s}) φ γ M) = ∅ := by
    rw [Finset.mem_mul.not] at p_not_prod
    push_neg at p_not_prod

    ext a
    simp only [Finset.mem_inter, Finset.not_mem_empty, iff_false, not_and]
    intro ha
    simp only [Finset.smul_finset_def, smul_eq_mul, Finset.mem_image] at ha
    obtain ⟨b, b_mem, s_b_eq⟩ := ha
    apply_fun (fun g => g * b⁻¹ ) at s_b_eq
    simp at s_b_eq
    apply Finset.inv_mem_inv at b_mem
    by_contra!
    specialize p_not_prod a this b⁻¹ b_mem
    rw [ne_comm] at p_not_prod
    contradiction


  have s_n_subset: ∀ M, N ≤ M → three_two_S_n (S := {s}) φ γ M ⊆ three_two_S_n (S := {s}) φ γ (M + 1) := by
    intro m hM a ha
    simp [three_two_S_n] at ha
    simp [three_two_S_n]
    obtain ⟨n, hn, s_n_eq⟩ := ha
    use n
    refine ⟨by omega, s_n_eq⟩

  have s_n_subset_all (x y: ℕ) (hxy: x ≤ y): three_two_S_n (S := {s}) φ γ x ⊆ three_two_S_n (S := {s}) φ γ (y) := by
    intro a ha
    simp [three_two_S_n] at ha
    simp [three_two_S_n]
    obtain ⟨n, hn, s_n_eq⟩ := ha
    use n
    refine ⟨by omega, s_n_eq⟩


  have b_n_subset_b_n_succ: ∀ M, N ≤ M → three_two_B_n (S := {s}) φ γ M ⊆ three_two_B_n (S := {s}) φ γ (M + 1) := by
    intro M hM a ha
    simp [three_two_B_n] at ha
    simp [three_two_B_n]
    obtain ⟨l, l_len, l_prod⟩ := ha
    simp [list_len_n]
    use l.map (fun s => ⟨s.val, by (
      exact s_n_subset M hM s.property
    )⟩)
    simp
    simp [list_len_n] at l_len
    refine ⟨by omega, ?_⟩
    conv =>
      lhs
      arg 1
      equals l.unattach =>
        simp [List.unattach, -List.map_subtype]
    exact l_prod

  have smul_subset (M: ℕ) (hM: N ≤ M) (p: G) (p_mem: p ∈ three_two_S_n (S := {s}) φ γ (M + 1)): p • three_two_B_n (S := {s}) φ γ M ⊆ three_two_B_n (S := {s}) φ γ (M + 1) := by
    intro a ha
    simp [three_two_B_n] at ha
    simp [three_two_B_n]
    simp only [Finset.smul_finset_def, smul_eq_mul, Finset.mem_image] at ha
    obtain ⟨list_prod, ⟨list, list_mem, list_prod_eq⟩, p_mul_eq⟩ := ha
    --have new_p_mem := (s_n_subset_all (N + 1) (M + 1) (by omega)) p_mem
    --have p_mem_M := s_n_subset M hM p_mem
    use (⟨p, p_mem⟩ :: (list.map (fun s => ⟨s.val, by (
      exact s_n_subset M hM s.property
    )⟩)))
    refine ⟨?_, ?_⟩
    .
      simp [list_len_n, list_mem]
      simp [list_len_n] at list_mem
      exact list_mem

    .
      simp
      conv =>
        lhs
        arg 2
        arg 1
        equals list.unattach =>
          simp [List.unattach, -List.map_subtype]
      rw [list_prod_eq, p_mul_eq]


  have s_n_bound: ∀ M: ℕ, N ≤ M → ∀ a ∈ three_two_S_n (S := {s}) φ γ M, ∃ l: List S, l.unattach.prod = a ∧ l.length ≤ 4*M^2 := by
    intro M hM a ha
    simp [three_two_S_n, gamma_m_helper, e_i_regular_helper] at ha
    obtain ⟨m, m_bound, s_m_eq⟩ := ha
    let gamma_inv_list: List S := (gamma_list.map (fun s => ⟨s.val⁻¹, hGS.has_inv s.val s.property⟩)).reverse

    -- Depending on whether these values are positive or negative, we either need to repeat γ or γ⁻¹ in the first list
    let m_list_choice := if 0 < m then gamma_list else gamma_inv_list
    let phi_list_choice := if 0 < (-φ (ofMul s)) then gamma_list else gamma_inv_list

    let m_list_choice_inv := if 0 < m then gamma_inv_list else gamma_list

      --
    --have phi_natabs: (φ (ofMul s)).natAbs = -φ (ofMul s) := by omega
    use (List.replicate m.natAbs m_list_choice).flatten ++ [⟨s, s_mem⟩] ++ (List.replicate (-(φ (ofMul s))).natAbs phi_list_choice).flatten ++ (List.replicate m.natAbs m_list_choice_inv).flatten
    refine ⟨?_, ?_⟩
    .
      simp [phi_list_choice]
      --rw [gamma_list_prod]
      norm_cast
      rw [← s_m_eq]
      rw [← zpow_natCast]
      conv =>
        rhs
        arg 1
        arg 2
        -- TODO - is there a tactic that can normalize the 'ofMul' stuff for us?
        equals s * γ^(-(φ (ofMul s))) =>
          rw [← ofMul_zpow]
          rw [← sub_eq_add_neg]
          rw [← ofMul_div]
          rw [div_eq_mul_inv]
          rw [← inv_zpow]
          rw [inv_zpow']
          rfl


      --rw [← zpow_natCast, phi_natabs]
      simp
      simp_rw [m_list_choice, m_list_choice_inv]
      by_cases m_pos: 0 < m
      .
        simp_rw [m_pos]
        simp
        have m_eq_abs : |m| = m := by
          rw [Int.abs_eq_natAbs]
          omega
        rw [← zpow_natCast]
        simp [gamma_inv_list]
        rw [gamma_list_inv]
        rw [gamma_list_prod]
        rw [m_eq_abs]
        group
        by_cases phi_neg: (φ (ofMul s)) < 0
        .
          have phi_abs: |(φ (ofMul s))| = -φ (ofMul s) := by
            rw [Int.abs_eq_natAbs]
            omega
          rw [phi_abs]
          simp_rw [phi_neg]
          simp
          rw [gamma_list_prod]
          rw [m_eq_abs]
          group
        .
          have phi_abs: |(φ (ofMul s))| = φ (ofMul s) := by
            rw [Int.abs_eq_natAbs]
            omega
          rw [phi_abs]
          simp_rw [phi_neg]
          simp
          rw [gamma_list_inv]
          rw [m_eq_abs]
          group
      .
        simp_rw [m_pos]
        simp
        have neg_abs_m : |m| = - m := by
          rw [Int.abs_eq_natAbs]
          omega
        rw [← zpow_natCast]
        simp [gamma_inv_list]
        rw [gamma_list_inv]
        rw [gamma_list_prod]
        group
        rw [neg_abs_m]
        group
        -- TODO - this can be deduplicated
        by_cases phi_neg: (φ (ofMul s)) < 0
        .
          have phi_abs: |(φ (ofMul s))| = -φ (ofMul s) := by
            rw [Int.abs_eq_natAbs]
            omega
          rw [phi_abs]
          simp_rw [phi_neg]
          simp
          rw [gamma_list_prod]
          rw [neg_abs_m]
          group
        .
          have phi_abs: |(φ (ofMul s))| = φ (ofMul s) := by
            rw [Int.abs_eq_natAbs]
            omega
          rw [phi_abs]
          simp_rw [phi_neg]
          simp
          rw [gamma_list_inv]
          rw [neg_abs_m]
          group
    .

      simp [m_list_choice, m_list_choice_inv]
      simp_rw [apply_ite]
      have m_natabs_le: m.natAbs ≤ M := by omega
      have gamma_list_len_le: gamma_list.length ≤ N := by omega
      have inv_list_len_eq: gamma_inv_list.length = gamma_list.length := by
        simp [gamma_inv_list]
      simp [inv_list_len_eq]
      have n_squared_pos: 1 ≤ N * N := by
        simp [N]
      have m_squared_pos: 1 ≤ M * M := by
        nlinarith
      have phi_choice_len: phi_list_choice.length = gamma_list.length := by
        simp [phi_list_choice]
        simp_rw [apply_ite]
        simp [inv_list_len_eq]
      rw [phi_choice_len]
      have phi_s_le_: (φ (ofMul s)).natAbs ≤ M := by omega
      calc
        _ ≤ M * M + ((φ (ofMul s)).natAbs * gamma_list.length + M * M + 1) := by
          nlinarith
        _ ≤ 2 * M * M + ((φ (ofMul s)).natAbs * gamma_list.length) + 1 := by
          nlinarith
        -- Extremely crude upper bound, but we only need to show a polynomial bound,
        -- so it's fine to use '1 <= N * N'
        _ ≤ 2 * M * M + ((φ (ofMul s)).natAbs * gamma_list.length) + M*M := by
          nlinarith
        _ ≤ 3 * M * M + ((φ (ofMul s)).natAbs * gamma_list.length) := by
          nlinarith
        _ ≤ 3 * M * M + (M * gamma_list.length) := by
          nlinarith
        _ ≤ 3 * M * M + (M * M) := by
          nlinarith
        _ = 4 * M * M := by
          nlinarith
        _ = 4 * M^2 := by nlinarith


  have b_n_subset_s_n_squared: ∀ M, N ≤ M → three_two_B_n (S := {s}) φ γ M ⊆ S ^ (M * (4 * M^2)) := by
    intro M hM a ha
    have orig_ha := ha
    rw [Finset.mem_pow]
    simp [three_two_B_n] at ha
    obtain ⟨l, l_len, l_prod⟩ := ha
    let nested_list := l.map (fun s => ((s_n_bound M hM s.val s.property).choose))
    have flat_list_prod: nested_list.flatten.unattach.prod = a := by
      simp [nested_list]
      rw [← l_prod]
      conv =>
        lhs
        arg 1
        equals l.unattach =>
          clear l_len l_prod nested_list
          induction l with
          | nil =>
            simp
          | cons h t ih =>
            simp
            rw [ih]
            simp [List.unattach, -List.map_subtype]
            simp at ih
            have my_spec := Exists.choose_spec ((s_n_bound M hM h h.property))
            have first_prop := my_spec.1
            -- wtf
            nth_rw 8 [← first_prop]
            simp



    have flat_list_len: nested_list.flatten.length ≤ nested_list.length • (4 * M^2) := by
      simp
      have foo := List.sum_le_card_nsmul (l := (List.map List.length nested_list)) (4 * M^2) ?_
      --simp only [List.length_map, smul_eq_mul, nested_list] at foo
      .
        conv at foo =>
          rhs
          simp
        exact foo
      .
        intro q hq
        simp at hq
        obtain ⟨s_list, h_s_prod, s_len⟩ := hq
        simp [nested_list] at h_s_prod
        obtain ⟨gamma_n, gamma_n_mem, gamma_n_mem_l, s_prod_eq⟩ := h_s_prod
        have s_prod_prop: s_list.unattach.prod = gamma_n ∧ s_list.length ≤ 4*M^2 := by
          have my_spec := Exists.choose_spec ((s_n_bound M hM gamma_n gamma_n_mem))
          rw [s_prod_eq] at my_spec
          exact my_spec
        rw [← s_len]
        exact s_prod_prop.2

    have nested_len_eq: nested_list.length = l.length := by
      simp [nested_list]

    rw [nested_len_eq] at flat_list_len
    simp [list_len_n] at l_len
    simp only [smul_eq_mul] at flat_list_len
    have nested_list_le_n_squared: nested_list.flatten.length ≤ M * (4 * M^2) := by
      apply le_mul_of_le_mul_right (b := l.length)
      . omega
      . omega


    let filled_list := nested_list.flatten ++ (List.replicate ((M * (4 * M^2)) - nested_list.flatten.length) ⟨1, hGS.one_mem⟩)

    have filled_list_prod: filled_list.unattach.prod = nested_list.flatten.unattach.prod := by
      simp [filled_list]


    have len_eq: filled_list.length = M * (4 * M^2) := by
      simp [filled_list]
      apply Nat.add_sub_of_le
      simp at nested_list_le_n_squared
      exact nested_list_le_n_squared

    rw [← len_eq]
    use filled_list.get
    conv =>
      lhs
      equals (List.ofFn (filled_list.get)).unattach.prod =>
        simp

    simp
    rw [filled_list_prod]
    exact flat_list_prod

  conv at b_n_subset_s_n_squared =>
    intro M hM
    rhs
    rhs
    equals 4 * M^3 => ring


  -- #(B_n) grows exponentially, at least from N onword
  have b_n_card_exp: ∀ M: ℕ, N ≤ M → 2^(M - N) ≤ #(three_two_B_n (S := {s}) φ γ M) := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base =>
      simp [three_two_B_n, list_len_n]
      use [⟨(gamma_m_helper φ γ 0 ⟨s, s_mem⟩), ?_⟩]
      . simp [N]
      .
        simp [three_two_S_n]
        use 0
        refine ⟨by omega, ?_⟩
        simp [gamma_m_helper, e_i_regular_helper]

    | succ k hk ih =>
      rw [← tsub_add_eq_add_tsub hk]
      rw [pow_succ]

      --specialize hN N (by simp [N])
      specialize this k
      rw [Finset.not_subset] at this
      obtain ⟨p, ⟨p_mem, p_not_prod⟩⟩ := this
      --rw [Finset.mem_mul.not] at p_not_prod
      --push_neg at p_not_prod

      have union_subset_n_succ: three_two_B_n (S := {s}) φ γ k ∪ (p • three_two_B_n (S := {s}) φ γ k) ⊆ three_two_B_n (S := {s}) φ γ (k + 1) := by
        apply Finset.union_subset
        . exact b_n_subset_b_n_succ k hk
        . exact smul_subset k hk p p_mem


      have card_le := Finset.card_le_card (union_subset_n_succ)
      rw [Finset.card_union_of_disjoint ?_] at card_le
      .
        simp at card_le
        ring_nf at card_le
        rw [add_comm] at card_le
        omega
        --have b_n_subset_n := Finset.card_le_card (b_n_subset_s_n_squared N (by simp))
        --have b_n_succ_subset := Finset.card_le_card (b_n_subset_s_n_squared (N + 1) (by simp))
        --simp at b_n_succ_subset
      .
        specialize disjoint_smul  k hk p p_mem p_not_prod
        rw [Finset.inter_comm] at disjoint_smul
        rw [Finset.disjoint_iff_inter_eq_empty]
        exact disjoint_smul


  have little_o_poly := isLittleO_pow_exp_pos_mul_atTop (3 * d) (b := (Real.log 2)) (by
    --simp
    apply Real.log_pos
    simp
  )
  simp at little_o_poly
  simp_rw [Real.exp_mul] at little_o_poly
  rw [Real.exp_log (by simp)] at little_o_poly


  obtain ⟨a, hG⟩ := hG

  have a_ne_zero: a ≠ 0 := by
    by_contra!
    rw [this] at hG
    have hg_one := hG 1 (by omega)
    simp at hg_one
    have one_mem := hGS.one_mem
    rw [hg_one] at one_mem
    simp at one_mem

  have mul_four := Asymptotics.IsLittleO.const_mul_left little_o_poly (a * 4^d)
  rw [← Asymptotics.isLittleO_const_mul_right_iff (c := 2^(-N : ℤ)) (hc := (by simp))] at mul_four
  --have mul_four := little_o_poly


  --rw [Asymptotics.IsLittleO.tendsto_zero_of_tendsto] at little_o_poly
  apply Asymptotics.IsLittleO.def (c := (1 : ℝ)  / 2) (hc := by simp) at mul_four
  apply Filter.Eventually.natCast_atTop at mul_four
  simp at mul_four
  obtain ⟨M', hM⟩ := mul_four
  let M: ℕ := max N M'





  have m_le_n: N ≤ M := by omega


  specialize b_n_card_exp M m_le_n
  specialize b_n_subset_s_n_squared
  have b_n_subset_n := Finset.card_le_card (b_n_subset_s_n_squared M (m_le_n))

  have m_ge_one: 1 ≤ M := by
    omega

  have m_cubed: 1 ≤ M^3 := by
    apply Nat.one_le_pow
    omega


  have other_poly := hG (4 * M ^ 3) (by
    omega
  )

  have m_pow_lt := hM (M) (by omega)
  rw [pow_mul] at m_pow_lt

  -- apply_fun (fun (g: ℝ) => 2 * g) at m_pow_lt
  -- .
  --   simp at m_pow_lt

  -- .
  --   apply Monotone.const_mul
  --   exact fun ⦃a b⦄ a ↦ a
  --   simp


  have helper_lemma (a b c : ℝ) (ha: 0 < a) (hb: 0 < b) (hc: 0 < c) (habc: a ≤ b * c) (hb: b < 1): a < c := by
    nlinarith

  have strict_lt: a * 4 ^ d * (↑M ^ 3) ^ d < (((2 : ℝ) ^ N)⁻¹ * 2 ^ M) := by
    apply helper_lemma (b := 2⁻¹)
    .
      field_simp
      positivity
    . simp
    . simp
    . exact m_pow_lt
    . norm_num



    -- apply lt_or_eq_of_le at m_pow_lt
    -- match m_pow_lt with
    -- | .inl strict =>
    --   omega
    -- | .inr eq =>
    --   rw [eq]
    --   rw [mul_comm]l
    --   apply mul_lt_of_lt_one_right'
    --   apply lt_mul_of_one_lt_right'
    --   apply mul_lt_of_lt_of_le_one


  conv at strict_lt =>
    rhs
    equals 2^(M - N) =>
      have m_minu_n_pos: N ≤ M := by omega
      field_simp
      rw [← pow_add]
      simp
      omega


  norm_cast at strict_lt
  rw [mul_assoc, ← mul_pow] at strict_lt

  have eventually_lt_double: a * (4 * M ^ 3) ^ d < 2 ^ (M - N) := by
    exact strict_lt

  omega



set_option maxHeartbeats 300000 in
lemma closure_iterate_mulact {T: Type*} [Group T] [DecidableEq T] (a b: T) (n: ℤ)
  (conj_in: (a^n * b * a^(-n)) ∈ (Subgroup.closure (G := T) (Set.image (fun (m: ℤ) => a^m * b * a^(-m)) (Set.Ioo (-n.natAbs) n.natAbs))))
  (conj_inv_in: (a^(-n) * b * a^(n)) ∈ (Subgroup.closure (G := T) (Set.image (fun (m: ℤ) => a^m * b * a^(-m)) (Set.Ioo (-n.natAbs) n.natAbs)))) :
 (Subgroup.closure (G := T) (Set.image (fun (m: ℤ) => a^m * b * a^(-m)) (Set.Ioo (-n.natAbs) n.natAbs) )) = (Subgroup.closure (G := T) (Set.range (fun (m : ℤ) => a^m * b * a^(-m)))) := by
  ext x
  refine ⟨?_, ?_⟩
  .
    intro hx
    apply Subgroup.closure_mono (h := (fun (m: ℤ) ↦ a ^ m * b * a ^ (-m)) '' Set.Ioo (-n.natAbs) n.natAbs)
    .
      intro y hy
      simp at hy
      simp
      obtain ⟨m, hm, y_eq⟩ := hy
      use m
    . exact hx
  .
    intro hx
    have closed_under_conj: ∀ y ∈ (Subgroup.closure (G := T) (Set.image (fun (m: ℤ) => a^m * b * a^(-m)) (Set.Ioo (-n.natAbs) n.natAbs) )), a * y * a⁻¹ ∈  (Subgroup.closure (G := T) (Set.image (fun (m: ℤ) => a^m * b * a^(-m)) (Set.Ioo (-n.natAbs) n.natAbs) )) := by
      intro y hy
      induction hy using Subgroup.closure_induction with
      | mem z hz =>
        simp at hz
        obtain ⟨m, hm, z_eq⟩ := hz
        rw [← z_eq]
        by_cases m_lt_n_sub: m < (n.natAbs : ℤ) - 1
        . apply Subgroup.subset_closure
          simp
          use (m + 1)
          refine ⟨?_, ?_⟩
          .
            refine ⟨?_, ?_⟩
            . omega
            .
              apply_fun (fun (z: ℤ) => z + 1) at m_lt_n_sub
              .
                simp at m_lt_n_sub
                exact m_lt_n_sub
              . exact StrictMono.add_const (fun ⦃a b⦄ a ↦ a) 1
          .
            rw [← mul_self_zpow]
            simp
            repeat rw [← mul_assoc]
        .
          have n_minus_eq: n - 1 + 1 = n := by
            omega
          simp at m_lt_n_sub
          have m_eq_n_minus: m = (|n|) - 1 := by
            omega
          -- TODO - there must be an easier way to do this
          rw [m_eq_n_minus]
          repeat rw [← mul_assoc]
          rw [mul_self_zpow]
          simp
          rw [← zpow_neg]
          rw [← inv_zpow']
          rw [mul_assoc]
          rw [← zpow_add_one]
          simp
          simp at conj_in
          by_cases n_pos: 0 < n
          .
            have n_eq_abs: n = |n| := by
              exact Eq.symm (abs_of_pos n_pos)
            nth_rw 3 [← n_eq_abs]
            nth_rw 3 [← n_eq_abs]
            exact conj_in
          .
            have n_eq_neg_abs: |n| = -n := by
              apply abs_of_nonpos
              omega
            simp at n_pos
            nth_rw 3 [n_eq_neg_abs]
            nth_rw 3 [n_eq_neg_abs]
            simp
            simp at conj_inv_in
            exact conj_inv_in
      | one =>
        simp
      | mul y z hy hz y_mem z_mem =>
        have mul_mem := Subgroup.mul_mem _ y_mem z_mem
        simp at mul_mem
        simp
        exact mul_mem
      | inv y hy y_mem =>
        rw [← Subgroup.inv_mem_iff]
        simp
        rw [← mul_assoc]
        simp at y_mem
        exact y_mem

    -- TODO - deduplicate this
    have closed_under_conj_inv: ∀ y ∈ (Subgroup.closure (G := T) (Set.image (fun (m: ℤ) => a^m * b * a^(-m)) (Set.Ioo (-n.natAbs) n.natAbs) )), a⁻¹ * y * a ∈  (Subgroup.closure (G := T) (Set.image (fun (m: ℤ) => a^m * b * a^(-m)) (Set.Ioo (-n.natAbs) n.natAbs) )) := by
      intro y hy
      induction hy using Subgroup.closure_induction with
      | mem z hz =>
        simp at hz
        obtain ⟨m, hm, z_eq⟩ := hz
        rw [← z_eq]
        by_cases m_lt_n_sub: (-n.natAbs : ℤ) < m - 1
        . apply Subgroup.subset_closure
          simp
          use (m - 1)
          refine ⟨?_, ?_⟩
          .
            refine ⟨?_, ?_⟩
            .
              simp at m_lt_n_sub
              have ⟨m_gt, other⟩ := hm
              omega

            .
              apply_fun (fun (z: ℤ) => z - 1) at m_lt_n_sub
              .
                simp at m_lt_n_sub
                omega
              . exact StrictMono.add_const (fun ⦃a b⦄ a ↦ a) (-1)
          .
            repeat rw [← mul_assoc]
            nth_rw 2 [← zpow_neg_one]
            rw [← zpow_add]
            rw [add_comm, ← sub_eq_add_neg]
            conv =>
              rhs
              rw [mul_assoc]
              rhs
              rw [← inv_zpow]
              rw [inv_zpow']
              rw [mul_zpow_self]
              rw [add_comm]
            simp
            rw [← inv_zpow]
            simp
            rw [sub_eq_add_neg]

        .
          have n_minus_eq: n - 1 + 1 = n := by
            omega
          simp at m_lt_n_sub
          have m_eq_n_minus: m = (-|n|) + 1 := by
            omega
          -- TODO - there must be an easier way to do this
          rw [m_eq_n_minus]
          repeat rw [← mul_assoc]
          rw [← mul_self_zpow]
          simp
          rw [← zpow_neg]
          rw [← zpow_neg_one]
          rw [mul_assoc]
          rw [mul_assoc]
          rw [mul_assoc]
          simp
          repeat rw [← mul_assoc]
          simp at conj_inv_in
          by_cases n_pos: 0 < n
          .
            have n_eq_abs: n = |n| := by
              exact Eq.symm (abs_of_pos n_pos)
            nth_rw 3 [← n_eq_abs]
            nth_rw 3 [← n_eq_abs]
            exact conj_inv_in
          .
            have n_eq_neg_abs: |n| = -n := by
              apply abs_of_nonpos
              omega
            simp at n_pos
            nth_rw 3 [n_eq_neg_abs]
            nth_rw 3 [n_eq_neg_abs]
            simp
            simp at conj_in
            exact conj_in
      | one =>
        simp
      | mul y z hy hz y_mem z_mem =>
        have mul_mem := Subgroup.mul_mem _ y_mem z_mem
        repeat rw [← mul_assoc] at mul_mem
        simp at mul_mem
        simp
        repeat rw [← mul_assoc]
        exact mul_mem
      | inv y hy y_mem =>
        rw [← Subgroup.inv_mem_iff]
        simp
        rw [← mul_assoc]
        simp at y_mem
        exact y_mem



    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      simp at hy
      obtain ⟨m, hm, y_eq⟩ := hy
      by_cases m_in_range: m ∈ Set.Ioo (-n.natAbs : ℤ) n.natAbs
      .
        apply Subgroup.subset_closure
        simp
        use m
        simp at m_in_range
        refine ⟨by omega, by simp⟩
      .
        simp only [Set.mem_Ioo] at m_in_range
        rw [not_and_or] at m_in_range
        simp at m_in_range
        by_cases m_pos: 0 < m
        .
          -- TODO - why is this needed?
          have exists_nat_abs: ∃ m_abs: ℕ, m = m_abs := by
            use m.natAbs
            omega
          obtain ⟨m_abs, m_eq_abs⟩ := exists_nat_abs
          have abs_n_le: |n| ≤ m_abs := by
            by_contra!
            rw [← m_eq_abs] at this
            omega
          have nat_abs_n_le: n.natAbs ≤ m_abs := by
            rw [Int.abs_eq_natAbs] at abs_n_le
            omega
          rw [m_eq_abs]
          clear m_eq_abs
          clear abs_n_le
          induction m_abs, nat_abs_n_le using Nat.le_induction with
          | base =>
            simp at conj_in
            simp
            by_cases n_pos: 0 < n
            .
              have n_eq_abs: n = |n| := by
                exact Eq.symm (abs_of_pos n_pos)
              nth_rw 3 [← n_eq_abs]
              nth_rw 3 [← n_eq_abs]
              exact conj_in
            .
              have n_eq_neg_abs: |n| = -n := by
                apply abs_of_nonpos
                omega
              simp at conj_inv_in
              rw [n_eq_neg_abs] at conj_inv_in
              simp at conj_inv_in
              rw [n_eq_neg_abs]
              simp
              exact conj_inv_in
          | succ p hsucc ih =>
            specialize closed_under_conj _ ih
            norm_cast
            rw [pow_succ']
            repeat rw [← mul_assoc] at closed_under_conj
            simp at closed_under_conj
            simp
            repeat rw [← mul_assoc]
            exact closed_under_conj

        .
          -- TODO - why is this needed?
          have exists_nat_abs: ∃ m_abs: ℕ, m = -m_abs := by
            use m.natAbs
            omega
          obtain ⟨m_abs, m_eq_abs⟩ := exists_nat_abs
          have abs_n_le: |n| ≤ m_abs := by
            by_contra!
            omega
          have nat_abs_n_le: n.natAbs ≤ m_abs := by
            rw [Int.abs_eq_natAbs] at abs_n_le
            omega
          rw [m_eq_abs]
          clear m_eq_abs
          clear abs_n_le
          induction m_abs, nat_abs_n_le using Nat.le_induction with
          | base =>
            simp at conj_in
            simp
            by_cases n_pos: 0 < n
            .
              have n_eq_abs: n = |n| := by
                exact Eq.symm (abs_of_pos n_pos)
              nth_rw 3 [← n_eq_abs]
              nth_rw 3 [← n_eq_abs]
              simp at conj_inv_in
              exact conj_inv_in
            .
              have n_eq_neg_abs: |n| = -n := by
                apply abs_of_nonpos
                omega
              rw [n_eq_neg_abs] at conj_in
              simp at conj_in
              rw [n_eq_neg_abs]
              simp
              exact conj_in
          | succ p hsucc ih =>
            --rw [← Subgroup.inv_mem_iff]
            --simp
            specialize closed_under_conj_inv _ ih
            simp at ih
            norm_cast
            rw [zpow_negSucc]
            rw [pow_succ]
            --rw [zpow_add]
            repeat rw [← mul_assoc] at closed_under_conj_inv
            simp at closed_under_conj_inv
            simp
            repeat rw [← mul_assoc]
            exact closed_under_conj_inv


    | one => apply Subgroup.one_mem
    | mul y z hy hz y_mem z_mem =>
      apply Subgroup.mul_mem
      . exact y_mem
      . exact z_mem
    | inv y hy y_mem =>
      apply Subgroup.inv_mem _ y_mem

#print axioms closure_iterate_mulact

--- Consequence of `three_two_poly_growth` - the set of all 'γ^n *e_i γ^(-n)' is contained the closure of S_n
lemma three_poly_poly_growth_all_s_n (d: ℕ) (hd: d >= 1) (hG: HasPolynomialGrowthD S d ) (γ: G) (φ: (Additive G) →+ ℤ) (hφ: Function.Surjective φ) (hγ: φ γ = 1)
  : ∃ n, ∀ m, (Finset.image (gamma_m_helper (S := S) φ γ m) Finset.univ).toSet ⊆ Subgroup.closure (three_two_S_n S  φ γ (n)).toSet := by

  -- by_cases S_empty: S = ∅
  -- .
  --   simp [S_empty, gamma_m_helper, three_two_S_n]
  --   use 1
  --   intro m
  --   intro a ha
  --   simp at ha
  --   obtain ⟨s, hs, a_eq⟩ := ha
  --   grind


  let r: ℕ := Finset.max' (Finset.image (fun s => (by
    exact sInf { n: ℕ | three_two_S_n (S := {s}) φ γ (n + 1) ⊆ ((three_two_B_n (S := {s}) φ γ n) * (three_two_B_n (S := {s}) φ γ n)⁻¹) }
    --exact {Classical.choose (new_three_two_poly_growth  d hd hG γ φ hφ hγ s)}
  )) S) (by
    simp
    exact S_nonempty
  )
  use r
  intro m
  intro x hx
  simp [gamma_m_helper] at hx
  simp [three_two_S_n, gamma_m_helper]
  obtain ⟨s, hs, x_eq_conj⟩ := hx

  let all_n_vals := { n : ℕ | three_two_S_n (S := {s}) φ γ (n + 1) ⊆ ((three_two_B_n (S := {s}) φ γ n) * (three_two_B_n (S := {s}) φ γ n)⁻¹)}
  let n := sInf all_n_vals
  have set_nonempty: all_n_vals.Nonempty := by
    exact new_three_two_poly_growth  d hd hG γ φ hφ hγ s hs
  have temp_s_n_subset := Nat.sInf_mem set_nonempty
  have s_n_subset: n ∈ all_n_vals := by
    exact temp_s_n_subset
  simp [all_n_vals] at s_n_subset
  --obtain ⟨n, s_n_subset⟩ := new_three_two_poly_growth  d hd hG γ φ hφ hγ s
  have n_le_r: n ≤ r := by
    simp [r]
    apply Finset.le_max'
    simp
    use s


  have my_iter := closure_iterate_mulact γ (e_i_regular_helper φ γ ⟨s, hs⟩) (n + 1)
  simp [three_two_S_n, gamma_m_helper] at s_n_subset
  have closure_eq := my_iter ?_ ?_
  .
    have x_mem_closure_range: x ∈ Subgroup.closure (Set.range fun (m : ℤ) ↦ γ ^ m * e_i_regular_helper φ γ ⟨s, hs⟩ * γ ^ (-m : ℤ)) := by
      by_cases m_pos: 0 < m
      .
        have m_eq_natabs: m = m.natAbs := by
          omega
        apply Subgroup.subset_closure
        simp
        use m.natAbs
        rw [m_eq_natabs] at x_eq_conj
        rw [← x_eq_conj]
      .
        --rw [← Subgroup.closure_inv]
        --rw [← Subgroup.inv_mem_iff]
        have m_eq_neg_natabs: m = -m.natAbs := by
          omega
        apply Subgroup.subset_closure
        simp
        --simp only [zpow_neg, zpow_natCast, Set.mem_range]
        use m

    rw [← closure_eq] at x_mem_closure_range
    apply Subgroup.closure_mono (h := ((fun (m : ℤ) ↦ γ ^ m * e_i_regular_helper φ γ ⟨s, hs⟩ * γ ^ (-m : ℤ)) '' (Set.Ioo (-(r + 1) : ℤ) (r + 1 : ℤ))))
    .
      intro p hp
      simp at hp
      simp
      obtain ⟨q, hp, p_eq⟩ := hp
      use q
      refine ⟨by omega, ?_⟩
      use s
      use hs
    .
      apply (Subgroup.closure_mono _) x_mem_closure_range
      intro z hz
      simp at hz
      simp
      obtain ⟨a, ⟨a_gt, a_lt⟩, z_eq⟩ := hz
      use a
      refine ⟨⟨?_, ?_⟩, z_eq⟩
      .
        --have neg_n_gt_r: (-r : ℤ) ≤ (-n : ℤ) := by omega
        norm_cast at a_gt
        omega
      .
        norm_cast at a_lt
        omega
  .
    specialize s_n_subset (n + 1) (by omega) (by omega) s rfl
    --specialize s_n_subset ⟨s, hs⟩
    simp [three_two_B_n] at s_n_subset
    rw [Finset.mem_mul] at s_n_subset
    obtain ⟨val, val_in_image, other_val, ⟨other_val_in_image, prod_vals_eq⟩⟩ := s_n_subset
    rw [← zpow_neg] at prod_vals_eq
    -- todo - avoid needing to do these simps
    simp [e_i_regular_helper] at prod_vals_eq
    simp [e_i_regular_helper]
    rw [← prod_vals_eq]
    apply Subgroup.mul_mem
    .
      simp at val_in_image
      obtain ⟨list, hlist, list_prod_eq⟩ := val_in_image
      rw [← list_prod_eq]
      apply Subgroup.list_prod_mem
      intro z hz
      simp [list_len_n] at hlist
      simp at hz
      obtain ⟨z_in_s_n, z_in_list⟩ := hz
      simp [three_two_S_n] at z_in_s_n
      apply Subgroup.subset_closure
      simp
      obtain ⟨p, p_in_range, e_i_eq⟩ := z_in_s_n
      use p
      norm_cast
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      simp [gamma_m_helper] at e_i_eq
      obtain ⟨q, q_mem, e_i_eq'⟩ := e_i_eq
      simp [e_i_regular_helper]
    .
      simp at other_val_in_image
      obtain ⟨list, hlist, list_prod_eq⟩ := other_val_in_image
      apply_fun Inv.inv at list_prod_eq
      simp at list_prod_eq
      rw [← list_prod_eq]
      apply Subgroup.inv_mem
      apply Subgroup.list_prod_mem
      intro z hz
      simp [list_len_n] at hlist
      simp at hz
      obtain ⟨z_in_s_n, z_in_list⟩ := hz
      simp [three_two_S_n] at z_in_s_n
      apply Subgroup.subset_closure
      simp
      obtain ⟨p, p_in_range, e_i_eq⟩ := z_in_s_n
      use p
      norm_cast
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      simp [gamma_m_helper] at e_i_eq
      obtain ⟨q, q_mem, e_i_eq'⟩ := e_i_eq
      simp [e_i_regular_helper]
  .
    -- TODO - 99% of this can be deduplicated
    specialize s_n_subset (-(n + 1)) (by omega) (by omega) s rfl
    -- Deduplicate verything after here
    simp [three_two_B_n] at s_n_subset

    rw [Finset.mem_mul] at s_n_subset
    obtain ⟨val, val_in_image, other_val, ⟨other_val_in_image, prod_vals_eq⟩⟩ := s_n_subset
    rw [← zpow_neg] at prod_vals_eq
    -- todo - avoid needing to do these simps
    simp [e_i_regular_helper] at prod_vals_eq
    simp [e_i_regular_helper]
    rw [← prod_vals_eq]
    apply Subgroup.mul_mem
    .
      simp at val_in_image
      obtain ⟨list, hlist, list_prod_eq⟩ := val_in_image
      rw [← list_prod_eq]
      apply Subgroup.list_prod_mem
      intro z hz
      simp [list_len_n] at hlist
      simp at hz
      obtain ⟨z_in_s_n, z_in_list⟩ := hz
      simp [three_two_S_n] at z_in_s_n
      apply Subgroup.subset_closure
      simp
      obtain ⟨p, p_in_range, e_i_eq⟩ := z_in_s_n
      use p
      norm_cast
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      simp [gamma_m_helper] at e_i_eq
      obtain ⟨q, q_mem, e_i_eq'⟩ := e_i_eq
      simp [e_i_regular_helper]
    .
      simp at other_val_in_image
      obtain ⟨list, hlist, list_prod_eq⟩ := other_val_in_image
      apply_fun Inv.inv at list_prod_eq
      simp at list_prod_eq
      rw [← list_prod_eq]
      apply Subgroup.inv_mem
      apply Subgroup.list_prod_mem
      intro z hz
      simp [list_len_n] at hlist
      simp at hz
      obtain ⟨z_in_s_n, z_in_list⟩ := hz
      simp [three_two_S_n] at z_in_s_n
      apply Subgroup.subset_closure
      simp
      obtain ⟨p, p_in_range, e_i_eq⟩ := z_in_s_n
      use p
      norm_cast
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      simp [gamma_m_helper] at e_i_eq
      obtain ⟨q, q_mem, e_i_eq'⟩ := e_i_eq
      simp [e_i_regular_helper]


-- The kernel of `φ` is generated by {γ_m_i}
set_option maxHeartbeats 1000000
lemma three_two_gamma_m_generates(φ: (Additive G) →+ ℤ) (hφ: Function.Surjective φ) (γ: G) (hγ: φ γ = 1) : Subgroup.closure (Set.range (Function.uncurry (gamma_m_helper (S := S)  φ γ))) = AddSubgroup.toSubgroup φ.ker := by
  have phi_ofmul: φ (ofMul γ) = 1 := by
    exact hγ
  --
  let e_i: S → (Additive G) := fun s => (ofMul s.val) +  ((-1 : ℤ) • (φ (ofMul s.val))) • (ofMul (γ))
  let e_i_regular: S → G := fun s => (ofMul s.val) +  ((-1 : ℤ) • (φ (ofMul s.val))) • (ofMul (γ))



  let max_phi := max 1 ((Finset.image Int.natAbs (Finset.image φ (Finset.image ofMul S))).max' (by simp [S_nonempty]))
  have e_i_zero: ∀ s: S, φ (e_i s) = 0 := by
    intro s
    unfold e_i
    simp
    simp [phi_ofmul]

  have e_i_regular_zero: ∀ s: S, φ (ofMul (e_i_regular s)) = 0 := by
    dsimp [ofMul]
    intro s
    unfold e_i_regular
    simp
    simp [phi_ofmul]

  have closure_enlarge: Subgroup.closure ({1, γ, γ⁻¹} ∪ (e_i '' Set.univ)) = Subgroup.closure (({1, γ, γ⁻¹} ∪ (e_i_regular '' Set.univ))^(max_phi + 1)) := by
    rw [Subgroup.closure_pow]
    . simp
    . unfold max_phi
      simp


  have new_closure_e_i: Subgroup.closure ({1, γ, γ⁻¹} ∪ (e_i '' Set.univ)) = (Subgroup.closure S) := by
    rw [closure_enlarge]
    apply Subgroup.closure_eq_of_le
    .
      rw [hGS.generates]
      exact fun ⦃a⦄ a ↦ trivial
    .
      simp
      intro s hs
      simp
      rw [← mem_toSubmonoid]
      rw [Subgroup.closure_toSubmonoid]
      dsimp [Membership.mem]
      rw [Submonoid.closure_eq_image_prod]
      -- TODO - why do we need any of this?
      dsimp [Set.Mem]
      rw [← Set.mem_def (a := s) (s := List.prod '' _)]
      rw [Set.mem_image]


      have foo := Submonoid.exists_list_of_mem_closure (s := ((S ∪ S⁻¹) : Set G)) (x := s)
      rw [← Subgroup.closure_toSubmonoid _] at foo
      simp only [mem_toSubmonoid, Finset.mem_coe] at foo
      have generates := hGS.generates
      have x_in_top: s ∈ (⊤: Set G) := by
        simp

      rw [← generates] at x_in_top
      specialize foo x_in_top
      obtain ⟨l, ⟨l_mem_s, l_prod⟩⟩ := foo
      norm_cast at l_mem_s
      rw [s_union_sinv] at l_mem_s

      let l_attach := l.attach
      let list_with_mem: List S := (l_attach).map (fun a => ⟨a.val, l_mem_s a.val a.prop⟩)
      let new_list := list_with_mem.map (fun s => (e_i s) + ofMul (γ^(((φ (ofMul s.val))))))

      have cancel_add_minus: max_phi - 1 + 1 = max_phi := by
        omega

      use new_list
      refine ⟨?_, ?_⟩
      .
        simp
        intro x hx
        unfold new_list list_with_mem l_attach at hx
        simp at hx
        obtain ⟨a, ha, x_eq_sum⟩ := hx
        left

        have gamma_phi_in_minus_plus: γ^(φ a) ∈ ({1, γ, γ⁻¹} ∪ Set.range e_i_regular) ^ (max_phi - 1  +1) := by
          by_cases val_pos: 0 < φ a
          .
            have eq_self: Int.natAbs (φ a) = φ a := by
              simp [val_pos]
              linarith
            conv =>
              arg 2
              equals γ ^ (Int.natAbs (φ a)) =>
                nth_rw 1 [← eq_self]
                norm_cast
            apply Set.pow_subset_pow_right (m := Int.natAbs (φ a)) (n := max_phi - 1 + 1)
            . simp
            .
              rw [cancel_add_minus]
              unfold max_phi
              simp
              right
              apply Finset.le_max'
              simp
              use a
              refine ⟨l_mem_s a ha, ?_⟩
              conv =>
                pattern ofMul a
                equals a => rfl
            .
              apply Set.pow_mem_pow
              simp
          .
            have eq_neg_abs: (φ a) = -(φ a).natAbs := by
              rw [← Int.abs_eq_natAbs]
              simp at val_pos
              rw [← abs_eq_neg_self] at val_pos
              omega
            rw [eq_neg_abs]
            conv =>
              arg 2
              equals (γ⁻¹) ^ (↑(φ a).natAbs) =>
                simp
                rw [Int.abs_eq_natAbs]
                norm_cast
            -- TOOD - deduplicate this with the positive case
            apply Set.pow_subset_pow_right (m := Int.natAbs (φ a)) (n := max_phi - 1 + 1)
            . simp
            .
              rw [cancel_add_minus]
              unfold max_phi
              simp
              right
              apply Finset.le_max'
              simp
              use a
              refine ⟨l_mem_s a ha, ?_⟩
              conv =>
                pattern ofMul a
                equals a => rfl
            .
              apply Set.pow_mem_pow
              simp
        have a_mem_s: a ∈ S := by exact l_mem_s a ha
        have prod_mem_power: e_i_regular ⟨a, a_mem_s⟩ * γ ^ φ (ofMul a) ∈ ({1, γ, γ⁻¹} ∪ Set.range e_i_regular) ^ (max_phi - 1 + 1 + 1) := by
          rw [pow_succ']
          rw [Set.mem_mul]
          use e_i_regular ⟨a, a_mem_s⟩
          refine ⟨by simp, ?_⟩
          use γ ^ φ (ofMul a)
          refine ⟨gamma_phi_in_minus_plus, ?_⟩
          simp

        have prod_eq_sum: e_i ⟨a, l_mem_s a ha⟩ + φ (ofMul a) • ofMul γ = (e_i_regular ⟨a, a_mem_s⟩) * (γ ^ φ (ofMul a)) := by
          simp [e_i, e_i_regular, cancel_add_minus]


          conv =>
            rhs
            arg 1
            equals ofMul (a* γ^(-(φ (ofMul a)))) =>
              simp

          apply_fun (fun x => x * (γ ^ (- φ (ofMul a))))
          .
            simp only
            simp
            conv =>
              lhs
              equals a * (γ ^ φ (ofMul a))⁻¹ =>
                simp
                rfl
            conv =>
              rhs
              rhs
              equals ofMul (γ ^ (- φ (ofMul a))) =>
                simp

            rw [← ofMul_mul]
            conv =>
              rhs
              equals (a * γ ^ (-φ (ofMul a))) =>
                rfl
            simp
          .
            exact mul_left_injective (γ ^ (-φ (ofMul a)))






        rw [← x_eq_sum]
        rw [prod_eq_sum]
        rw [cancel_add_minus] at prod_mem_power
        apply prod_mem_power








      unfold new_list list_with_mem l_attach
      simp
      conv =>
        arg 1
        arg 1
        arg 1
        arg 1
        intro z
        unfold e_i
        simp
      simp
      conv =>
        arg 1
        arg 1
        arg 1
        equals id =>
          rfl
      simp
      exact l_prod
  let gamma_m := fun (m: ℤ) (s: S) => γ^m * (e_i s).toMul * γ^(-m)
  have gamma_m_ker_phi: (Subgroup.closure (Set.range (Function.uncurry gamma_m))) = φ.ker.toSubgroup := by
    ext z
    refine ⟨?_, ?_⟩
    . intro hz
      have foo := Submonoid.exists_list_of_mem_closure (s := Set.range (Function.uncurry gamma_m) ∪ (Set.range (Function.uncurry gamma_m))⁻¹) (x := z)
      rw [← Subgroup.closure_toSubmonoid _] at foo
      specialize foo hz
      obtain ⟨l, ⟨l_mem_s, l_prod⟩⟩ := foo
      rw [← l_prod]
      rw [← MonoidHom.coe_toMultiplicative_ker]
      rw [MonoidHom.mem_ker]
      rw [MonoidHom.map_list_prod]
      apply List.prod_eq_one
      intro x hx
      simp at hx
      obtain ⟨a, a_mem_l, phi_a⟩ := hx
      specialize l_mem_s a a_mem_l
      unfold gamma_m at l_mem_s
      simp at l_mem_s
      rw [← phi_a]
      match l_mem_s with
      | .inl a_eq_prod =>
        obtain ⟨n, val, val_in_s, prod_eq_a⟩ := a_eq_prod
        rw [← prod_eq_a]
        simp
        have apply_mult := AddMonoidHom.toMultiplicative_apply_apply φ (toMul (e_i ⟨val, val_in_s⟩))
        conv at apply_mult =>
          rhs
          rhs
          arg 2
          equals e_i ⟨val, val_in_s⟩ => rfl
        rw [e_i_zero] at apply_mult
        exact apply_mult
      | .inr a_eq_prod =>
        obtain ⟨n, val, val_in_s, prod_eq_a⟩ := a_eq_prod
        apply_fun Inv.inv at prod_eq_a
        simp at prod_eq_a
        -- TODO - deduplicate this with the branch above
        rw [← prod_eq_a]
        simp
        have apply_mult := AddMonoidHom.toMultiplicative_apply_apply φ (toMul (e_i ⟨val, val_in_s⟩))
        conv at apply_mult =>
          rhs
          rhs
          arg 2
          equals e_i ⟨val, val_in_s⟩ => rfl
        rw [e_i_zero] at apply_mult
        exact apply_mult
    .
      intro hz

      -- We need to write 'γ^a (f⁻¹ )' as an element of e_i

      -- γ^(φ(f_1)) (f_1⁻¹ ) = f_2 γ^(-φ(f_2))

      have foo := Submonoid.exists_list_of_mem_closure (s := ({1, γ, γ⁻¹} ∪ e_i '' Set.univ) ∪ ({1, γ, γ⁻¹} ∪ e_i '' Set.univ)⁻¹) (x := z)
      apply_fun Subgroup.toSubmonoid at new_closure_e_i
      rw [Subgroup.closure_toSubmonoid _] at new_closure_e_i
      rw [Subgroup.closure_toSubmonoid _] at new_closure_e_i
      rw [new_closure_e_i] at foo
      rw [← Subgroup.closure_toSubmonoid _] at foo
      simp only [mem_toSubmonoid, Finset.mem_coe] at foo

      conv at foo =>
        intro hz
        arg 1
        intro l
        lhs
        intro y
        intro hy
        rw [Set.union_comm {1, γ, γ⁻¹} (e_i '' Set.univ)]
        rw [Set.union_assoc]
        arg 1
        rhs
        rw [Set.union_comm]
        rw [Set.union_inv]
        rw [Set.union_assoc]
        rhs
        simp

      have generates := hGS.generates
      have z_in_top: z ∈ (⊤: Set G) := by
        simp

      rw [← generates] at z_in_top
      have z_eq_prod := foo z_in_top
      clear foo

      let E: Set G := {γ, γ⁻¹} ∪ Set.range e_i_regular ∪ (Set.range e_i_regular)⁻¹

      let rec rewrite_list (list: List (E)) (hlist: φ (ofMul list.unattach.prod) = 0): { t: List (((Set.range (Function.uncurry gamma_m) : (Set G)) ∪ (Set.range (Function.uncurry gamma_m))⁻¹ : (Set G))) // list.unattach.prod = t.unattach.prod } := by
        let is_gamma: E → Bool := fun (k: E) => k = γ ∨ k = γ⁻¹
        let is_gamma_prop: E → Prop := fun (k: E) => k = γ ∨ k = γ⁻¹
        have eq_split: list = list.takeWhile is_gamma ++ list.dropWhile is_gamma := by
          exact Eq.symm List.takeWhile_append_dropWhile
        by_cases header_eq_full: list.takeWhile is_gamma = list
        .
          have list_eq_gamma_m: ∃ m: ℤ, list.unattach.prod = γ ^ m := by
            unfold is_gamma at header_eq_full
            clear eq_split is_gamma is_gamma_prop hlist

            induction list with
            | nil =>
              use 0
              simp
            | cons h t ih =>
              have h_gamma: h = γ ∨ h = γ⁻¹ := by
                simp at header_eq_full
                exact header_eq_full.1
              rw [List.takeWhile_cons_of_pos] at header_eq_full
              .
                rw [List.cons_eq_cons] at header_eq_full
                specialize ih header_eq_full.2
                obtain ⟨m, hm⟩ := ih
                by_cases h_eq_gamma: h = γ
                .
                  use (m + 1)
                  simp [h_eq_gamma, hm]
                  exact mul_self_zpow γ m
                . use (-1 + m)
                  simp [h_eq_gamma] at h_gamma
                  simp [h_gamma, hm]
                  rw [← zpow_neg_one]
                  rw [zpow_add]
              . simp [h_gamma]


          have empty_prod_eq: list.unattach.prod = ([] : List E).unattach.prod := by
            obtain ⟨m, hm⟩ := list_eq_gamma_m
            rw [hm]
            simp
            rw [hm] at hlist
            simp at hlist
            simp [phi_ofmul] at hlist
            simp [hlist]

          exact ⟨[], empty_prod_eq⟩
        .

          have tail_nonempty: list.dropWhile is_gamma ≠ [] := by
            rw [not_iff_not.mpr List.takeWhile_eq_self_iff] at header_eq_full
            rw [← not_iff_not.mpr List.dropWhile_eq_nil_iff] at header_eq_full
            exact header_eq_full

          have dropwhile_len_gt: 0 < (list.dropWhile is_gamma).length := by
            exact List.length_pos_iff.mpr tail_nonempty

          have not_is_gamma := List.dropWhile_get_zero_not is_gamma list dropwhile_len_gt
          simp at not_is_gamma

          have not_is_gamma_prop: ¬ is_gamma_prop (List.dropWhile is_gamma list)[0] := by
            dsimp [is_gamma_prop]
            dsimp [is_gamma] at not_is_gamma
            exact of_decide_eq_false not_is_gamma

          simp [is_gamma_prop] at not_is_gamma_prop
          have drop_head_in_e_i: (List.dropWhile is_gamma list)[0].val ∈ (Set.range e_i_regular) ∪ (Set.range e_i_regular)⁻¹ := by
            have drop_in_E: (List.dropWhile is_gamma list)[0].val ∈ E := by
              simp [E]
            simp only [E] at drop_in_E
            simp_rw [Set.union_assoc] at drop_in_E
            rw [Set.mem_union] at drop_in_E
            have not_in_left: (List.dropWhile is_gamma list)[0].val ∉ ({γ, γ⁻¹} : Set G) := by
              simp [not_is_gamma_prop]

            -- TODO - why can't simp handle this?
            have in_right := Or.resolve_left drop_in_E not_in_left
            exact in_right


          let m := ((list.takeWhile is_gamma).map (fun (k : E) => if k = γ then 1 else if k = γ⁻¹ then -1 else 0)).sum

          have in_range: γ ^ m * ↑(List.dropWhile is_gamma list)[0] * γ ^ (-m) ∈ (Set.range (Function.uncurry gamma_m)) ∪ ((Set.range (Function.uncurry gamma_m)))⁻¹ := by
            simp [gamma_m]
            simp at drop_head_in_e_i
            match drop_head_in_e_i with
            | .inl drop_head_in_e_i =>
              obtain ⟨s, s_in_S, eq_e_i⟩ := drop_head_in_e_i
              left
              use m
              use s
              use s_in_S
              simp
              rw [← eq_e_i]
              rfl
            | .inr drop_head_in_e_i =>
              obtain ⟨s, s_in_S, eq_e_i⟩ := drop_head_in_e_i
              right
              use m
              use s
              use s_in_S
              conv =>
                rhs
                rw [← mul_assoc]
              simp
              rw [← eq_e_i]
              rfl

          have phi_ofmul_gamma: φ (ofMul γ) = 1 := by
            exact hγ

          have gamma_ne_inv: γ ≠ γ⁻¹ := by
            by_contra this
            apply_fun ofMul at this
            apply_fun φ at this
            rw [phi_ofmul_gamma] at this
            rw [ofMul_inv] at this
            rw [AddMonoidHom.map_neg] at this
            rw [phi_ofmul_gamma] at this
            omega

          let gamma_copy: List E := if (m >= 0) then List.replicate m.natAbs ⟨γ, by simp [E]⟩ else List.replicate (m.natAbs) ⟨γ⁻¹, by simp [E]⟩
          let gamma_copy_inv: List E := if (m >= 0) then List.replicate m.natAbs ⟨γ⁻¹, by simp [E]⟩ else List.replicate (m.natAbs) ⟨γ, by simp [E]⟩

          have gamma_copy_prod: gamma_copy.unattach.prod = γ^m := by
            simp [gamma_copy]
            by_cases m_ge: 0 ≤ m
            .
              simp [m_ge]
              rw [← zpow_natCast]
              simp
              rw [← abs_eq_self] at m_ge
              rw [m_ge]
            .
              simp [m_ge]
              rw [← zpow_natCast]
              simp
              simp at m_ge
              have m_le: m ≤ 0 := by omega
              rw [← abs_eq_neg_self] at m_le
              simp [m_le]

          have gamma_copy_inv_prod: gamma_copy_inv.unattach.prod = γ^(-m) := by
            simp [gamma_copy_inv]
            by_cases m_ge: 0 ≤ m
            .
              simp [m_ge]
              rw [← zpow_natCast]
              simp
              rw [← abs_eq_self] at m_ge
              rw [m_ge]
            .
              simp [m_ge]
              rw [← zpow_natCast]
              simp
              simp at m_ge
              have m_le: m ≤ 0 := by omega
              rw [← abs_eq_neg_self] at m_le
              simp [m_le]

          have E_inhabited: Inhabited E := by
            use γ
            simp [E]

          have header_prod: (List.takeWhile is_gamma list).unattach.prod = γ^m := by
            have my_lemma := take_count_sum_eq_exp (List.takeWhile is_gamma list) γ gamma_ne_inv ?_
            .
              rw [my_lemma]
            .
              have foo (x: E) := List.mem_takeWhile_imp (p := fun (val: E) => (val = γ ∨ val = γ⁻¹)) (l := list) (x := x)
              conv at foo =>
                intro x hx
                equals ↑x = γ ∨ ↑x = γ⁻¹ =>
                  simp
              exact foo

          -- 'γ^n * a * γ^(_n) * γn * tail', as a list of elements in E
          let mega_list := (gamma_copy ++ [(List.dropWhile is_gamma list)[0]] ++ gamma_copy_inv) ++ (gamma_copy ++ (list.dropWhile is_gamma).tail)
          have mega_list_prod: mega_list.unattach.prod = list.unattach.prod := by
            simp [mega_list]
            simp [gamma_copy_prod, gamma_copy_inv_prod]
            conv =>
              rhs
              rw [eq_split]
              rw [List.unattach_append]
              simp
            have dropwhile_not_nul : (List.dropWhile is_gamma list) ≠ [] := by
              exact tail_nonempty
            apply_fun (fun x => x * (List.dropWhile is_gamma list).unattach.prod⁻¹)
            .
              simp
              conv =>
                pattern _[0]
                equals (List.dropWhile is_gamma list).headI =>
                  rw [← List.head_eq_getElem_zero dropwhile_not_nul]
                  rw [← List.getI_zero_eq_headI]
                  rw [List.head_eq_getElem_zero]
                  exact
                    Eq.symm
                      (List.getI_eq_getElem (List.dropWhile is_gamma list)
                        (List.length_pos_iff.mpr dropwhile_not_nul))

              have unattach_len_pos: 0 < (List.dropWhile is_gamma list).unattach.length := by
                rw [List.length_unattach]
                exact List.length_pos_iff.mpr dropwhile_not_nul

              conv =>
                lhs
                lhs
                rhs
                equals (List.dropWhile is_gamma list).unattach.headI * (List.dropWhile is_gamma list).unattach.tail.prod =>
                  rw [← List.getI_zero_eq_headI]
                  rw [← List.getI_zero_eq_headI]
                  rw [List.getI_eq_getElem _ (List.length_pos_iff.mpr dropwhile_not_nul)]
                  rw [List.getI_eq_getElem _ unattach_len_pos]
                  simp [List.getElem_unattach _ unattach_len_pos]
                  rw [list_tail_unattach]

              rw [List.headI_mul_tail_prod_of_ne_nil]
              .
                simp
                simp [header_prod]
              .
                by_contra this
                rw [List.eq_nil_iff_length_eq_zero] at this
                rw [List.length_unattach] at this
                rw [← List.eq_nil_iff_length_eq_zero] at this
                contradiction


            . exact mul_left_injective (List.dropWhile is_gamma list).unattach.prod⁻¹

          have sublist_phi_zero: φ (gamma_copy ++ (List.dropWhile is_gamma list).tail).unattach.prod = 0 := by
            rw [← mega_list_prod] at hlist
            unfold mega_list at hlist
            simp at hlist
            simp at drop_head_in_e_i
            match drop_head_in_e_i with
            | .inl drop_head_in_e_i =>
              obtain ⟨s, s_in_S, eq_e_i⟩ := drop_head_in_e_i
              rw [← eq_e_i] at hlist
              simp [e_i_regular_zero] at hlist
              nth_rw 1 [← ofMul_list_prod] at hlist
              nth_rw 1 [← ofMul_list_prod] at hlist
              rw [gamma_copy_prod, gamma_copy_inv_prod] at hlist
              simp at hlist
              rw [← ofMul_list_prod] at hlist
              rw [← ofMul_list_prod] at hlist
              simp
              conv =>
                lhs
                arg 2
                equals (ofMul gamma_copy.unattach.prod) + (ofMul (List.dropWhile is_gamma list).tail.unattach.prod) =>
                  rfl

              simp
              rw [← ofMul_list_prod]
              rw [← ofMul_list_prod]
              exact hlist
            | .inr drop_head_in_e_i =>
              obtain ⟨s, s_in_S, eq_e_i⟩ := drop_head_in_e_i
              rw [inv_eq_iff_eq_inv.symm] at eq_e_i
              rw [← eq_e_i] at hlist
              simp [e_i_regular_zero] at hlist
              nth_rw 1 [← ofMul_list_prod] at hlist
              nth_rw 1 [← ofMul_list_prod] at hlist
              rw [gamma_copy_prod, gamma_copy_inv_prod] at hlist
              simp at hlist
              rw [← ofMul_list_prod] at hlist
              rw [← ofMul_list_prod] at hlist
              simp
              conv =>
                lhs
                arg 2
                equals (ofMul gamma_copy.unattach.prod) + (ofMul (List.dropWhile is_gamma list).tail.unattach.prod) =>
                  rfl

              simp
              rw [← ofMul_list_prod]
              rw [← ofMul_list_prod]
              exact hlist

          have count_head_lt: (List.map (fun (k: E) ↦ if ↑k = γ then (1 : ℤ) else if ↑k = γ⁻¹ then -1 else 0)
          (List.takeWhile (fun (k: E) ↦ decide (↑k = γ) || decide (↑k = γ⁻¹)) list)).sum.natAbs ≤ (List.takeWhile (fun (k: E) ↦ decide (↑k = γ) || decide (↑k = γ⁻¹)) list).length := by
            induction (List.takeWhile (fun (k: E) ↦ decide (↑k = γ) || decide (↑k = γ⁻¹)) list) with
            | nil =>
              simp
            | cons h t ih =>
              simp
              split_ifs
              . omega
              . omega
              . omega

          let rewritten_sub_list := (rewrite_list (gamma_copy ++ (list.dropWhile is_gamma).tail) sublist_phi_zero)
          let return_list := (⟨γ^m * (List.dropWhile is_gamma list)[0] * γ^(-m), in_range⟩) :: rewritten_sub_list.val

          -- Show that the list (rewritten in terms of `γ^m * e_i * γ^(-m)` terms) is in the kernel of φ


          have mega_list_prod_preserve: mega_list.unattach.prod = return_list.unattach.prod := by
            unfold mega_list return_list
            simp
            rw [gamma_copy_prod]
            rw [gamma_copy_inv_prod]
            simp
            rw [← rewritten_sub_list.property]
            simp
            rw [gamma_copy_prod]
            conv =>
              rhs
              rw [mul_assoc]
              rhs
              rw [← mul_assoc]
              simp
            rw [mul_assoc]

          have return_list_prod: list.unattach.prod = return_list.unattach.prod := by
            rw [← mega_list_prod_preserve]
            exact mega_list_prod.symm


          exact ⟨return_list, return_list_prod⟩
      termination_by list.length
      decreasing_by {
        simp
        have inhabited_g : Inhabited G := by
          use 1
        split_ifs
        .
          simp
          conv =>
            rhs
            rw [← take_drop_len (p := fun (k: E) ↦ decide (↑k = γ) || decide (↑k = γ⁻¹))]
          apply add_lt_add_of_le_of_lt
          . apply count_head_lt
          . simp [is_gamma] at dropwhile_len_gt
            apply Nat.sub_one_lt
            apply Nat.pos_iff_ne_zero.mp dropwhile_len_gt
        .
          simp-- [count_gamma_copy]
          conv =>
            rhs
            rw [← take_drop_len (p := fun (k: E) ↦ decide (↑k = γ) || decide (↑k = γ⁻¹))]
          apply add_lt_add_of_le_of_lt
          . apply count_head_lt
          . simp [is_gamma] at dropwhile_len_gt
            apply Nat.sub_one_lt
            apply Nat.pos_iff_ne_zero.mp dropwhile_len_gt
      }

      obtain ⟨z_list, h_z_list⟩ := z_eq_prod
      rw [← list_filter_one] at h_z_list
      have z_filter_mem_e: ∀ p ∈ (List.filter (fun s ↦ !decide (s = 1)) z_list), p ∈ E := by
        intro p hp
        dsimp [E]
        simp at hp
        obtain ⟨h_z_list_in, _⟩ := h_z_list
        specialize h_z_list_in p hp.1
        rw [Set.mem_union] at h_z_list_in
        rw [Set.mem_union] at h_z_list_in
        match h_z_list_in with
        | .inl h_z_list_in =>
          simp at h_z_list_in
          obtain ⟨a, a_mem_s, e_i_ap⟩ := h_z_list_in
          apply Set.mem_union_left
          apply Set.mem_union_right
          simp
          use a
          use a_mem_s
        | .inr h_z_list_in =>
          simp at h_z_list_in
          match h_z_list_in with
          | .inl h_z_list_in =>
            obtain ⟨a, a_mem_s, e_i_ap⟩ := h_z_list_in
            apply Set.mem_union_right
            simp
            use a
            use a_mem_s
          | .inr h_z_list_in =>
            simp [hp.2] at h_z_list_in
            apply Set.mem_union_left
            apply Set.mem_union_left
            simp
            exact h_z_list_in.symm

      let my_res := rewrite_list ((z_list.filter (fun s ↦ !decide (s = 1))).attach.map (fun (g) => ⟨g.val, z_filter_mem_e g.val g.property⟩)) (by
        simp
        -- TODO - there has to be a less awful way of doing this
        conv =>
          arg 1
          arg 2
          arg 1
          arg 2
          equals (List.filter (fun s ↦ !decide (s = 1)) z_list) =>
            clear h_z_list

            ext i q
            simp
            by_cases list_get: (List.filter (fun s ↦ !decide (s = 1)) z_list)[i]? = none
            . simp [list_get]
            . simp at list_get
              simp [list_get]
        rw [← ofMul_list_prod]
        rw [h_z_list.2]
        exact hz
      )
      have my_res_prop := my_res.property
      rw [← Subgroup.mem_toSubmonoid]
      rw [Subgroup.closure_toSubmonoid _]
      conv =>
        equals z ∈ (Submonoid.closure (Set.range (Function.uncurry gamma_m) ∪ (Set.range (Function.uncurry gamma_m))⁻¹) : Set _) =>
          rfl
      rw [Submonoid.closure_eq_image_prod]
      rw [Set.mem_image]
      use my_res.val.unattach
      refine ⟨?_, ?_⟩
      . simp only [Set.mem_setOf_eq]
        intro x hx
        rw [List.mem_unattach] at hx
        obtain ⟨x_prop, _⟩ := hx
        exact x_prop
      .
        rw [← my_res_prop]
        conv =>
          pattern List.unattach _
          equals (List.filter (fun s ↦ !decide (s = 1)) z_list) =>
            ext i q
            simp
            by_cases list_get: (List.filter (fun s ↦ !decide (s = 1)) z_list)[i]? = none
            . simp [list_get]
            . simp at list_get
              simp [list_get]
        exact h_z_list.2
  exact gamma_m_ker_phi

noncomputable def phi_generating (n: ℕ) (φ: (Additive G) →+ ℤ) (γ: G) := Finset.preimage (three_two_S_n S  φ γ (n)) Multiplicative.ofAdd (by
    apply Set.injOn_of_injective
    exact fun ⦃a₁ a₂⦄ a ↦ a
  )

lemma three_two_S_n_subset_ker  (φ: (Additive G) →+ ℤ) (γ: G) (phi_gamma: φ γ = 1) (n: ℕ):
   ↑(three_two_S_n S φ γ n) ⊆ Additive.toMul '' φ.ker.carrier := by

  intro x hx
  simp [three_two_S_n, gamma_m_helper, e_i_regular_helper] at hx
  obtain ⟨m, m_in_range, s, s_mem_s, prod_eq_x⟩ := hx
  apply_fun ofMul at prod_eq_x
  rw [ofMul_mul] at prod_eq_x
  rw [ofMul_mul] at prod_eq_x
  apply_fun φ at prod_eq_x
  rw [AddMonoidHom.map_add] at prod_eq_x
  rw [AddMonoidHom.map_add] at prod_eq_x
  simp at prod_eq_x
  conv at prod_eq_x =>
    arg 1
    arg 2
    equals (ofMul s + -(φ (ofMul s) • ofMul γ)) => rfl

  simp at prod_eq_x
  conv at prod_eq_x =>
    pattern φ (ofMul γ)
    equals φ γ => rfl

  simp [phi_gamma] at prod_eq_x
  simp
  exact id (Eq.symm prod_eq_x)

lemma three_two_ker_fg  (d: ℕ) (hd: d >= 1) (hG: HasPolynomialGrowthD S d ) (φ: (Additive G) →+ ℤ) (hφ: Function.Surjective φ): φ.ker.FG := by
  simp only [AddSubgroup.FG]
  obtain ⟨γ, phi_gamma⟩ := hφ 1
  --obtain ⟨n, hn⟩ := three_two_poly_growth d hd hG γ φ hφ phi_gamma
  obtain ⟨n, hn⟩ := three_poly_poly_growth_all_s_n d hd hG γ φ hφ phi_gamma
  use (Finset.preimage (three_two_S_n S  φ γ (n)) Multiplicative.ofAdd (by
    apply Set.injOn_of_injective
    exact fun ⦃a₁ a₂⦄ a ↦ a
  ))
  simp
  ext z
  refine ⟨?_, ?_⟩
  . intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem x hx =>
      have helper := three_two_S_n_subset_ker φ γ phi_gamma n
      have x_mem: x ∈ three_two_S_n S φ γ n := by
        simp at hx
        exact hx

      have helper := (three_two_S_n_subset_ker φ γ phi_gamma n) x_mem
      simpa using helper
    | zero =>
      simp
    | add y z y_mem z_mem hy hz =>
      exact (AddSubgroup.add_mem_cancel_right φ.ker hz).mpr hy
    | neg x x_mem hx =>
      exact AddSubgroup.neg_mem φ.ker hx
  . intro hz
    have generates_ker := three_two_gamma_m_generates φ hφ γ phi_gamma
    --obtain ⟨γ, hγ, generates_ker⟩ := three_two_gamma_m_generates φ hφ

    have mem_ker_iff: ∀ z, z ∈ (AddSubgroup.toSubgroup φ.ker) ↔ z ∈ φ.ker := by
      exact fun z ↦ Eq.to_iff rfl
    rw [← mem_ker_iff] at hz
    rw [← generates_ker] at hz

    --have exists_prod_list := Submonoid.exists_list_of_mem_closure (s := S ∪ S⁻¹) (x := x)
    rw [← mem_toSubmonoid] at hz
    rw [Subgroup.closure_toSubmonoid _] at hz
    have exists_prod := Submonoid.exists_list_of_mem_closure hz
    obtain ⟨l, l_mem, z_eq_prod⟩ := exists_prod
    rw [← z_eq_prod]
    conv =>
      arg 2
      equals ofMul l.prod => rfl
    apply AddSubgroup.list_sum_mem
    simp only [Additive.forall]
    intro a ha
    specialize l_mem (ofMul a) ha
    --simp [three_two_S_n]
    simp at l_mem
    match l_mem with
    | .inl l_mem =>
      obtain ⟨p, s, s_mem, helper_eq_a⟩ := l_mem
      specialize hn p
      simp at hn
      rw [Set.range_subset_iff] at hn
      specialize hn ⟨s, s_mem⟩
      simp at hn

      rw [← helper_eq_a]
      rw [← Subgroup.toAddSubgroup'_closure]
      exact hn
    | .inr l_mem =>
      rw [← AddSubgroup.neg_mem_iff]
      obtain ⟨p, s, s_mem, helper_eq_a⟩ := l_mem
      conv at helper_eq_a =>
        rhs
        equals -ofMul a => rfl
      specialize hn p
      simp at hn
      rw [Set.range_subset_iff] at hn
      specialize hn ⟨s, s_mem⟩
      simp at hn
      rw [← helper_eq_a]
      rw [← Subgroup.toAddSubgroup'_closure]
      exact hn

-- Extract a generatating set for the kernel of φ
noncomputable def phi_S (d: ℕ) (hd: d >= 1) (hG: HasPolynomialGrowthD S d ) (φ: (Additive G) →+ ℤ) (hφ: Function.Surjective φ): Finset (φ.ker) := by
  have fg := three_two_ker_fg d hd hG φ hφ
  rw [AddSubgroup.fg_iff] at fg
  let S := Classical.choose fg
  have s_generates := (Classical.choose_spec fg).1
  have s_finite := (Classical.choose_spec fg).2
  have fintype : Fintype S := by
    exact s_finite.fintype

  let s_fin: Finset φ.ker := S.toFinset.attach.image (fun a => ⟨a.val, (by
    rw [← s_generates]
    apply AddSubgroup.mem_closure_of_mem
    have a_prop := a.property
    rw [Set.mem_toFinset] at a_prop
    exact a_prop
  )⟩)
  exact s_fin



def S_n_ker_phi (φ: (Additive G) →+ ℤ) (γ: G) (hγ : φ γ = 1) (n: ℕ)  : Finset φ.ker := (three_two_S_n S φ γ n).attach.image (fun x => ⟨x.val, (by
have foo := (three_two_S_n_subset_ker φ γ hγ n) x.property
simpa using foo
)⟩) ∪ {0}

omit hGS in
lemma poly_growth_equiv_generates (hG: Generates) (S': Finset hG.G) {d: ℕ} (h_poly: HasPolynomialGrowthD hG.S d): HasPolynomialGrowthD S' d := by
  unfold HasPolynomialGrowthD at h_poly
  obtain ⟨a, ha⟩ := h_poly
  have a_ne_zero: a ≠ 0 := by
    by_contra a_eq_zero
    simp [a_eq_zero] at ha
    specialize ha 1 (by simp)
    simp at ha
    have s_nonempty := hG.one_mem
    grind
  have poly := poly_growth_equiv a d (by omega) hG.S S' (S_eq_Sinv) (hG.one_mem) (by simpa using hG.generates) ha
  obtain ⟨b, b_ge, hb⟩ := poly
  use b


lemma three_two_kernel_poly_growth  (d: ℕ) (hd: d >= 1) (n: ℕ) (hG: HasPolynomialGrowthD S d ) (φ: (Additive G) →+ ℤ) (γ: G) (hγ : φ γ = 1)
 : HasPolynomialGrowthD (G := Multiplicative φ.ker) (d - 1) (S := (S_n_ker_phi φ γ hγ n)) := by

  -- The set S_n, viewed a subset of ker φ



  obtain ⟨a, ha⟩ := hG

  by_cases a_eq_zero: a = 0
  .
    simp [a_eq_zero] at ha
    specialize ha 1 (by simp)
    simp at ha
    have s_nonempty := hGS.one_mem
    grind



  unfold HasPolynomialGrowthD




  have S_n_poly := poly_growth_equiv a d (by omega) S (three_two_S_n S φ γ n ∪ {γ} ∪ {1}) S_eq_Sinv hGS.one_mem (by simpa using hGS.generates) ha
  obtain ⟨b, hb, ker_poly⟩ := S_n_poly



  use b * (2 ^ d)

  intro r hr
  specialize ker_poly (2 * r) (by omega)

  -- -- The kernel is an additive group, so we use hsmul instead of hpow for repeatedly adding elements in the group
  -- have poly_r: ∀ r: ℕ, r * #(r • S_n_ker_phi) ≤ #((three_two_S_n S φ γ n)) := by
  --   intro r

  --   by_cases r_zero: r = 0
  --   . simp [r_zero]

  let mul_by_i := fun (g: G) (i: Fin r) => g * (γ ^ i.val)
  have new_phi_gamma: φ (Additive.ofMul γ) = 1 := hγ
  have card_mul_range (g: G): #(Finset.image (mul_by_i g) Finset.univ) = r := by
    rw [Finset.card_image_of_injOn]
    . simp
    .

      intro j _ k _ mul_eq
      simp [mul_by_i] at mul_eq
      apply_fun φ ∘ (Additive.ofMul) at mul_eq
      simp [new_phi_gamma] at mul_eq
      rw [Fin.ext_iff]
      exact mul_eq

  have card_union: #(((((S_n_ker_phi φ γ hγ n).image Multiplicative.ofAdd) ^ r).image ofMul).biUnion (fun a => Finset.image (mul_by_i a.val) Finset.univ)) = r * #(r • (S_n_ker_phi φ γ hγ n)) := by
    rw [Finset.card_biUnion]
    .
      simp_rw [card_mul_range]
      simp
      rw [mul_comm]
      conv =>
        lhs
        arg 2
        arg 1
        equals r • S_n_ker_phi φ γ hγ n =>
          ext a
          rw [Finset.mem_image]
          simp_rw [Finset.mem_pow]
          rw [Finset.mem_nsmul]
          refine ⟨?_, ?_⟩
          . intro h
            obtain ⟨b, ⟨f, hf⟩, b_eq_a⟩ := h
            use (fun i => ⟨(f i).val, (by
              have f_prop := (f i).property
              rw [Finset.mem_image] at f_prop
              obtain ⟨g, g_mem, hg⟩ := f_prop
              rw [← hg]
              exact g_mem
            )⟩)
            rw [← b_eq_a]
            rw [← hf]
            rfl
          . intro h
            obtain ⟨f, hf⟩ := h
            use a
            refine ⟨?_, rfl⟩
            use (fun i => ⟨(f i).val, (by
              have f_prop := (f i).property
              rw [Finset.mem_image]
              use (f i).val
              refine ⟨f_prop, ?_⟩
              rfl
            )⟩)
            rw [← hf]
            rfl



    .
      intro a ha b hb hab x h_first h_second
      simp at h_first
      simp at h_second
      simp

      by_contra!
      rw [← Finset.nonempty_iff_ne_empty] at this
      obtain ⟨p, hp⟩ := this
      have orig_h_first := h_first hp
      have orig_h_second := h_second hp
      specialize h_first hp
      specialize h_second hp

      simp at h_first
      simp at h_second

      obtain ⟨y, hy⟩ := h_first
      obtain ⟨z, hz⟩ := h_second

      have orig_hy := hy
      have orig_hz := hz

      rw [← hz] at hy
      simp [mul_by_i] at hy
      apply_fun φ ∘ (Additive.ofMul) at hy
      simp [new_phi_gamma] at hy

      have a_ker: a.val ∈ φ.ker := by
        simp

      have b_ker: b.val ∈ φ.ker := by
        simp

      rw [AddMonoidHom.mem_ker] at a_ker
      rw [AddMonoidHom.mem_ker] at b_ker
      simp [ofMul] at hy
      simp [a_ker, b_ker] at hy

      rw [← Fin.ext_iff] at hy
      rw [hy] at orig_hy
      rw [← orig_hy] at orig_hz
      simp [mul_by_i] at orig_hz
      rw [eq_comm] at orig_hz
      contradiction



  have card_union_le: #(((((S_n_ker_phi φ γ hγ n).image Multiplicative.ofAdd) ^ r).image ofMul).biUnion (fun a => Finset.image (mul_by_i a.val) Finset.univ)) ≤ #(((three_two_S_n S φ γ n) ∪ {γ} ∪ {1}) ^ (2 * r)) := by
    grw [Finset.card_le_card]
    intro a ha
    rw [Finset.mem_biUnion] at ha
    obtain ⟨s, s_mem, a_mem⟩ := ha
    rw [Finset.mem_image] at a_mem
    obtain ⟨k, _, hk⟩ := a_mem
    simp [mul_by_i] at hk
    rw [← hk]
    rw [two_mul]
    rw [pow_add]
    apply Finset.mul_mem_mul
    .
      unfold S_n_ker_phi at s_mem

      rw [Finset.mem_image] at s_mem
      obtain ⟨z, z_mem, hz⟩ := s_mem
      rw [← hz]

      rw [Finset.mem_pow] at z_mem
      obtain ⟨f, hf⟩ := z_mem
      rw [Finset.mem_pow]
      use (fun i => ⟨(f i).val.val, (by
        have f_prop := (f i).property
        rw [Finset.mem_image] at f_prop
        obtain ⟨g, g_mem, hg⟩ := f_prop
        rw [← hg]
        simp at g_mem
        cases g_mem
        .
          rename_i g_eq_zero
          simp [g_eq_zero]
          left
          rfl
        . rename_i g_eq_nonzero
          obtain ⟨z, z_mem, hz⟩ := g_eq_nonzero
          rw [← hz]
          apply Finset.mem_union_left
          apply Finset.mem_union_left
          exact z_mem
      )⟩)
      rw [← hf]
      simp
      rw [AddSubgroup.val_list_sum]
      simp
      rfl
    .
      have gamma_pow_subset: {γ}^r ⊆ (three_two_S_n S φ γ n ∪ {γ})^r := by
        apply Finset.pow_subset_pow_left
        simp



      have gamma_r_subset: ({γ, 1} : Finset G)^r ⊆ (three_two_S_n S φ γ n ∪ {γ} ∪ {1})^r := by
        apply Finset.pow_subset_pow
        . grind
        . grind
        . simp

      have gamma_subset: ({γ, 1} : Finset G)^k.val ⊆ ({γ, 1} : Finset G)^r := by
        apply Finset.pow_subset_pow
        . simp
        . simp
        . simp


      have gamma_mem_self: γ^k.val ∈ ({γ, 1} : Finset G)^k.val := by
        apply Finset.pow_mem_pow
        simp

      grind




  rw [card_union] at card_union_le
  grw [ker_poly] at card_union_le
  rw [mul_pow] at card_union_le
  rw [← mul_assoc] at card_union_le
  rw [mul_comm] at card_union_le
  rw [← Nat.le_div_iff_mul_le] at card_union_le
  .
    rw [Nat.mul_div_assoc] at card_union_le
    .
      nth_rw 3 [← pow_one (a := r)] at card_union_le
      rw [Nat.pow_div] at card_union_le
      .
        -- TODO - get rid of this obnoxious  Additive/Multiplicative defeq abuse
        conv =>
          lhs
          arg 1
          equals r • (S_n_ker_phi φ γ hγ n) =>
            ext a
            rw [Finset.mem_pow]
            -- TODO - why do we need explicit args here
            rw [Finset.mem_nsmul (a := a) (s := S_n_ker_phi φ γ hγ n) (n := r)]
            refine ⟨?_, ?_⟩
            .
              intro hf
              obtain ⟨f, hf⟩ := hf
              use f
              exact hf
            . intro hf
              obtain ⟨f, hf⟩ := hf
              use f
              exact hf
        exact card_union_le
      . omega
      . omega

    .
      nth_rw 1 [← pow_one (a := r)]
      apply Nat.pow_dvd_pow
      omega
  . omega

#print axioms three_two_kernel_poly_growth

def iteratedCommutator {T: Type*} [Group T] {M: Subgroup T} (base right: M) (n: ℕ) := Nat.iterate (fun x => ⁅base, x⁆) n right

structure G''CommData {T: Type*} [Group T] (M: Subgroup T) where
  -- Our 'γ^α' element
  gamma_alpha: M
  -- The result of repeatedly applying commutators
  cur: M

  -- When we take a commutator, we increment the second component if we take a commutator with 'right',
  -- and reset it to zero and increment the first component if we take a commutator with anything else
  -- As a result, 'pos' strictly increases at each step
  pos: Lex (ℕ × ℕ)
  -- The first component of our position is our index in the lower central series of M
  pos_first: cur ∈ (lowerCentralSeries M pos.1)
  -- The second component is the number of copies of 'right' that occur in successive adjacent commutators
  pos_second: pos.2 ≠ 0 → ∃ b: M, cur = iteratedCommutator b gamma_alpha pos.2

set_option trace.profiler true in
set_option trace.Elab.command true in
set_option tactic.simp.trace true in
open Classical in
noncomputable def G''_comm {T: Type*} [Group T] {N: Subgroup T} (N_normal: N.Normal) {M: Subgroup T} (gamma_alpha base next: M) (gamma_N: gamma_alpha.val ∈ N) (n: ℕ): G''CommData M := match n with
| 0 => {
  gamma_alpha := gamma_alpha
  cur := base
  pos := (0, 0)
  pos_first := by
    simp [lowerCentralSeries]
  pos_second := by
    simp
}
| n + 1 => {
  gamma_alpha := gamma_alpha
  cur := ⁅(G''_comm N_normal gamma_alpha base next gamma_N n).cur, next⁆
  pos := if (next = gamma_alpha) then ((G''_comm N_normal gamma_alpha base next gamma_N n).pos.1, (G''_comm N_normal gamma_alpha base next gamma_N n).pos.2 + 1)
         else ((G''_comm N_normal gamma_alpha base next gamma_N n).pos.1 + 1, 0)
  pos_first := by
    split_ifs
    .
      rename_i next_eq_gamma
      simp [next_eq_gamma]
      sorry
    . sorry
  pos_second := by
    split_ifs
    . rename_i next_eq_gamma
      intro _
      have prev := (G''_comm N_normal gamma_alpha base next gamma_N n).pos_second
      by_cases prev_zero: (G''_comm N_normal gamma_alpha base next gamma_N n).pos.2 = 0
      . use (G''_comm N_normal gamma_alpha base next gamma_N n).cur
        simp [prev_zero]
        simp [prev_zero, next_eq_gamma, iteratedCommutator]
      . have prev_eq := prev prev_zero
        obtain ⟨b, b_eq⟩ := prev_eq
        use b
        simp [next_eq_gamma, iteratedCommutator]
        sorry
    .
      rename_i next_ne_gamma
      simp
}
termination_by n
decreasing_by
  all_goals { sorry }
-- StrictMono.not_bddAbove_range_of_wellFoundedLT


-- TODO - add an explicit top-level universe parameter to avoid this 'omit hGS' hack
set_option maxHeartbeats 2500000 in
omit hGS in
lemma theorem_3_1.{u} [hGS: Generates.{u}] (data: Theorem3_1_Input G) (d: ℕ) (hd: 1 ≤ d) (h_growth: HasPolynomialGrowthD S d)
(inductive_gromov: ∀ {Q: Type u}, [DecidableEq Q] → [Group Q] → (Q_fg: Group.FG Q) → (Q_growth : (HasPolynomialGrowthD (Q_fg.out.choose) (d - 1))) → Group.IsVirtuallyNilpotent Q)
: Group.IsVirtuallyNilpotent G := by

  have G'_finite_index := data.finite_index
  have G'_fg: Group.FG data.G' := by
    apply Subgroup.fg_of_index_ne_zero

  -- A symmetric generating set for G'
  let S_G' := G'_fg.out.choose ∪  G'_fg.out.choose⁻¹ ∪ {1}

  -- TODO - factor out this proof that a subgroup has polynomial growth
  have G'_poly: HasPolynomialGrowthD (G := data.G') S_G' d := by
    unfold HasPolynomialGrowthD
    obtain ⟨a, ha⟩ := h_growth

    have a_pos: 0 < a := by
      by_contra!
      simp at this
      simp [this] at ha
      specialize ha 1 (by simp)
      simp at ha
      have s_one := hGS.one_mem
      grind

    have my_equiv := poly_growth_equiv a d a_pos S (Finset.image Subtype.val S_G')
      S_eq_Sinv hGS.one_mem (by simpa using hGS.generates) ha

    obtain ⟨b, hb, poly_growth_G'⟩ := my_equiv

    use b
    intro n hn
    rw [← Finset.card_image_of_injective (f := data.G'.subtype)]
    .
      rw [Finset.image_pow]
      exact poly_growth_G' n hn
    . simp

  have inhabited_G': Inhabited data.G' := by
    use 1
    simp

  have inhabited_G: Inhabited G := by
    use 1

  -- TODO - figure out how to avoid registering this instance
  let new_generates: Generates := {
    G := data.G'
    g_group := by infer_instance
    g_eq := by infer_instance
    S := S_G'
    hS := by
      simp [S_G']
    generates := by
      simp [S_G']
      rw [Subgroup.closure_union]
      rw [G'_fg.out.choose_spec]
      simp
    one_mem := by
      simp [S_G']
    has_inv := by
      intro g hg
      unfold S_G'
      unfold S_G' at hg
      rw [← Finset.mem_inv']
      simp
      simp at hg
      grind
    g_infinite := by
      have index_ne := G'_finite_index.index_ne_zero
      simp [Subgroup.index] at index_ne
      -- TODO - generalize and upstream this to mathlib
      by_contra!
      have finite_iff := Subgroup.finite_iff_finite_and_finiteIndex data.G'
      simp [this, G'_finite_index] at finite_iff
      have G_infinite := hGS.g_infinite
      rw [← not_finite_iff_infinite] at G_infinite
      contradiction
  }


  obtain ⟨γ, hγ⟩ := data.hφ 1
  have kernel_poly := three_two_kernel_poly_growth (hGS := new_generates) d hd 1 G'_poly data.φ γ hγ

  have kernel_fg := three_two_ker_fg d hd G'_poly data.φ data.hφ
  --have kernel_poly_fg_out := poly_growth_equiv_generates new_generates kernel_fg.choose (d := 2)




  rw [← AddGroup.fg_iff_addSubgroup_fg] at kernel_fg
  rw [AddGroup.fg_iff_mul_fg] at kernel_fg
  --have kernel_poly_fg_out := poly_growth_equiv_generates hGS (sorry) kernel_poly

  --have h_new_growth := poly_growth_equiv_generates hGS S_G'
  have kernel_virtually_nilpotent := inductive_gromov (Q := ↑(Multiplicative data.φ.ker)) kernel_fg ?_
  .
    obtain ⟨pre_N, pre_N_nilpotent, pre_N_finiteindex⟩ := kernel_virtually_nilpotent
    let N := pre_N.normalCore
    have N_normal: N.Normal := Subgroup.normalCore_normal pre_N
    have N_finite_index: N.FiniteIndex := Subgroup.finiteIndex_normalCore pre_N
    have N_nilpotent: Group.IsNilpotent N := by
      have normalCore_iso := Subgroup.subgroupOfEquivOfLe (Subgroup.normalCore_le pre_N)
      unfold N
      rw [← Group.isNilpotent_congr normalCore_iso]
      apply Subgroup.isNilpotent

    rw [Subgroup.finiteIndex_iff] at N_finite_index
    let N' := Subgroup.closure (Set.range (fun (a: Multiplicative data.φ.ker) => a ^ N.index))



    -- Page 24 of Vikman, "G′′ is virtually nilpotent:"
    have alpha_unipotent: ∃ α: ℕ, ∃ m: ℕ, ∀ g ∈ N', Nat.iterate (fun x => ⁅x, γ.toMul^α⁆) m g.val = 1 := by
      sorry

    obtain ⟨α, m, alpha_is_unipotent⟩ := alpha_unipotent

    have N'_le_N: N' ≤ N := by
      unfold N'
      simp
      intro n hn
      rw [Set.mem_range] at hn
      obtain ⟨a, ha⟩ := hn
      rw [← ha]
      apply Subgroup.pow_index_mem

    have N'_nilpotent: Group.IsNilpotent N' := by
      rw [← Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe N'_le_N)]
      exact isNilpotent (N'.subgroupOf N)

    have N'_char: Subgroup.Characteristic N' := by
      rw [Subgroup.characteristic_iff_map_eq]
      intro f
      unfold N'
      simp
      rw [MonoidHom.map_closure]
      simp
      congr
      ext a
      refine ⟨?_, ?_⟩
      . intro ha
        rw [Set.mem_image] at ha
        obtain ⟨b, hb, ab_eq⟩ := ha
        rw [Set.mem_range] at hb
        obtain ⟨c, hc⟩ := hb
        rw [← hc] at ab_eq
        simp at ab_eq
        grind
      . intro ha
        rw [Set.mem_range] at ha
        obtain ⟨b, hb⟩ := ha
        rw [← hb]
        rw [Set.mem_image]
        use f⁻¹ (b ^ N.index)
        refine ⟨?_, by simp⟩
        simp

    have N'_normal: N'.Normal := by
      infer_instance

    let G'' := Subgroup.closure (((Additive.toMul ∘ data.φ.ker.subtype) '' N'.carrier) ∪ {γ.toMul})

    let N'_as_G'' := (AddSubgroup.map (AddSubgroup.subtype _) (Subgroup.toAddSubgroup' N')).toSubgroup'.subgroupOf G''

    have N'_as_G''_normal: N'_as_G''.Normal := by
      simp [N'_as_G'']
      exact {
        conj_mem n := by
          intro hn g
          unfold G'' at g
          rw [Subgroup.mem_subgroupOf]
          -- TODO - figure out how to make 'induction' tactic work here
          simp
          use (sorry)
          sorry
          -- apply Subgroup.closure_induction (k :=  (((Additive.toMul ∘ data.φ.ker.subtype) '' N'.carrier) ∪ {γ.toMul})) (p := fun g hg => g * n * g⁻¹ ∈ (AddSubgroup.toSubgroup' (AddSubgroup.map data.φ.ker.subtype (toAddSubgroup' N'))))
          -- . intro x hx
          --   rw [Set.mem_union] at hx
          --   cases hx
          --   .
          --     rename_i x_mem
          --     apply Subgroup.mul_mem
          --     . apply Subgroup.mul_mem
          --       . exact x_mem
          --       . exact hn
          --     . simp
          --       exact x_mem
          --   . rename_i x_eq
          --     simp at x_eq
          --     rw [Subgroup.mem_subgroupOf] at hn

          --     have mul_mem_ker: x * n.val * x⁻¹ ∈ data.φ.ker := by
          --       simp [x_eq]
          --       conv =>
          --         arg 1
          --         arg 2
          --         equals γ + (Additive.ofMul n.val) + -γ =>
          --           rfl
          --       simp
          --       conv =>
          --         arg 1
          --         equals (data.φ γ) + (data.φ (Additive.ofMul n.val)) + (data.φ (-γ)) =>
          --           rfl

          --       simp [hγ]
          --       have n_mem_ker: n.val ∈ data.φ.ker := by
          --         have add_n_mem: Additive.ofMul n.val ∈ (AddSubgroup.map data.φ.ker.subtype (toAddSubgroup' N')) := by
          --           exact hn

          --         simp at add_n_mem
          --         obtain ⟨x, hx⟩ := add_n_mem
          --         exact x
          --       simp at n_mem_ker
          --       exact n_mem_ker


          --     have n_conj := N'_normal.conj_mem ⟨n.val, by sorry⟩ sorry
          --     sorry
          -- . simp
          --   exact hn
          -- . intro x y hx hy x_conj y_conj
          --   rw [mul_inv_rev]
          --   conv =>
          --     arg 2
          --     equals x * (y * n * y⁻¹) * x⁻¹ => group


          --   have new_conj := N'_normal.conj_mem
          --   apply Subgroup.mul_mem
          --   . apply Subgroup.mul_mem
          --     . sorry
          --     . exact y_conj
          --   .
          --     have x_prop := x.property
          --     sorry
          -- . intro x hx conj_mem
          --   simp
          --   sorry
          -- . exact g.property
      }


    -- let N'_as_G'' := (Subgroup.map data.φ.ker.subtype.toMultiplicative N').toAddSubgroup'.toSubgroup'.subgroupOf G''


    -- --let N'_as_G' := (Subgroup.map data.φ.ker.subtype.toMultiplicative N').toAddSubgroup'.toSubgroup'



    -- have add_normal: (AddSubgroup.map data.φ.ker.subtype (toAddSubgroup' N')).Characteristic := by
    --   sorry

    -- have new_N'_as_G''_normal: new_N'_as_G''.Normal := by
    --   simp [new_N'_as_G'']
    --   exact {
    --     conj_mem n := by
    --       intro hn g
    --       have toAdd_mem: Additive.ofMul (g * n * g⁻¹) ∈ (AddSubgroup.map data.φ.ker.subtype (toAddSubgroup' N')) := by
    --         simp
    --         have n_mem_ker: n ∈ data.φ.ker := by
    --           simp [AddSubgroup.toSubgroup'] at hn
    --           simp [toAddSubgroup] at hn
    --           sorry

    --         have n_mem_N': ⟨n, n_mem_ker⟩ ∈ N' := by
    --           sorry
    --         use ?_
    --         .
    --           have N'_conj := N'_normal.conj_mem


    --       exact toAdd_mem

    --   }

    -- have N'_as_G''_normal: N'_as_G''.Normal := by
    --   unfold N'_as_G''
    --   --simp [AddSubgroup.toSubgroup']
    --   apply Subgroup.Normal.subgroupOf
    --   exact {
    --     conj_mem n := by
    --       intro hn g
    --       unfold AddSubgroup.toSubgroup'
    --       unfold toAddSubgroup'
    --       sorry
    --   }





    --have N'_normal: ((Subgroup.map (Subgroup.subtype _) N').subgroupOf G'').Normal := by

    --have G''_lower_subset: ∀ n: ℕ, (lowerCentralSeries G'' (n + 1)) ≤ (lowerCentralSeries N' )

    -- Take some base element, and repeatedly take commutators with γ^α on the right
    --let repeat_comm_gamma := Nat.iterate (fun x => ⁅x, γ.toMul^α⁆)


    -- have G''_nilpotent: Group.IsNilpotent G'' := by
    --   have eventually_le := RepeatComm_eventually_le N'_as_G''_normal ⟨(γ.toMul)^α, (by
    --     unfold G''
    --     apply Subgroup.pow_mem
    --     apply Subgroup.mem_closure_of_mem
    --     simp
    --   )⟩ ?_
    --   . sorry
    --   . sorry
    --   -- DONE - implemented a better idea in UnipotentGromov
    --   -- Idea: Each time we take a cummutator ⁅g'', a], we either have:
    --   -- g'' = γ^α, in which case we stay in the same subgroup
    --   -- g'' ∈ N', in which case we move upward in the central series of N'
    --   -- We want to either hit α copies of γ in a row, or reach the nilpotency class of N'
    --   -- Our position is (n'_level, gamma_count) under a lexical ordering
    --   -- We want to show that at each step of the lower central series for G'', this position strictly increases
    --   -- So, it must either reach (_, m) or (nilpotency_class_N', _), at which point we are done

    -- have G''_finite_index: G''.FiniteIndex := by
    --   unfold G''
    --   simp

    -- let conj_gamma: N' ≃* N' := {
    --   toFun := fun n => ⟨⟨Additive.ofMul (γ.toMul * n.val.val.toMul * γ.toMul⁻¹), by (
    --     simp
    --     have n_prop := n.val.property
    --     exact n_prop
    --   )⟩, by (
    --     simp [N']
    --     sorry
    --   )⟩
    --   left_inv := sorry
    --   right_inv := sorry
    -- }

    -- let conj_gamma_pow (z: ℤ): N' ≃* N' := {
    --   toFun := fun n => ⟨⟨Additive.ofMul (γ.toMul^(-z) * n.val.val.toMul * γ.toMul^z), by (
    --     simp
    --     have n_prop := n.val.property
    --     exact n_prop
    --   )⟩, by (
    --     simp [N']
    --     sorry
    --     -- simp [N']
    --     -- have n_prop := n.val.property
    --     -- apply Subgroup.mem_closure_of_mem
    --     -- rw [Set.mem_range]
    --     -- use ⟨ofMul (γ.toMul * n.val.val.toMul * γ.toMul⁻¹), by (
    --     --   simp
    --     --   exact n_prop
    --     -- )⟩

    --     -- simp

    --     -- let N'_as_G' := (Subgroup.map data.φ.ker.subtype.toMultiplicative N').toAddSubgroup'.toSubgroup'
    --     -- have N'_normal: N'.Normal := by
    --     --   infer_instance
    --     -- have N'_as_G'_normal: N'_as_G'.Normal := by
    --     --   simp [N'_as_G']
    --     --   simp [AddSubgroup.toSubgroup']

    --     --   apply Subgroup.Normal.map
    --     --   . exact N'_normal
    --     --   .
    --     --     simp [AddMonoidHom.toMultiplicative]
    --     --     intro a
    --     --     use a
    --     -- have N'_conj := Subgroup.Normal.conj_smul_eq_self ((γ.toMul)^z) N'_as_G'
    --     -- sorry
    --   )⟩
    --   invFun := fun n => ⟨⟨Additive.ofMul (γ.toMul^(z) * n.val.val.toMul * γ.toMul^(-z)), by (
    --     simp
    --     have n_prop := n.val.property
    --     exact n_prop
    --   )⟩, by (
    --     simp [N']
    --     sorry
    --   )⟩
    --   left_inv := by
    --     simp
    --     intro a
    --     simp
    --     simp_rw [← add_assoc]
    --     simp
    --   right_inv := by
    --     simp
    --     intro a
    --     simp
    --     simp_rw [← add_assoc]
    --     simp
    --   map_mul' := by
    --     intro a b
    --     conv =>
    --       rhs
    --       simp
    --     simp
    --     apply_fun Additive.toMul
    --     conv =>
    --       rhs
    --       simp
    --     simp
    --     sorry
    -- }

    -- --let foo := SemidirectProduct.mulEquivSubgroup (G := G'') (H := N')

    -- let aut_map: Multiplicative ℤ →* MulAut N' := {
    --   toFun := fun z => conj_gamma_pow z.toAdd
    --   map_one' := by
    --     simp [conj_gamma_pow]
    --     rfl
    --   map_mul' := by
    --     intro p q
    --     simp [conj_gamma_pow]
    --     ext z
    --     simp
    --     sorry
    -- }

    -- --let new_G'': (N' ⋊[aut_map] (Multiplicative ℤ)) := ⊤


    -- let G''_iso: G'' ≃* (N' ⋊[aut_map] (Multiplicative ℤ)) := {
    --   toFun := fun g => sorry
    --   invFun := fun g => sorry
    --   left_inv := sorry
    --   right_inv := sorry
    --   map_mul' := sorry
    -- }



    --let N'_of_G' := Subgroup.map (data.φ.ker).subtype ⊥

    --let G'' := Subgroup.closure (((Subgroup.subtype _ ) '' N'.carrier) ∪ ({γ.toMul} : (Set data.G')))






    -- let a := (MulAut.conj (Additive.toMul γ))

    -- have N'_conj_gamma: (MulAut.conj (Additive.toMul γ)) N' = N' := by
    --   unfold N'
    --   apply Subgroup.conj_pow_subgroup_eq
    --   exact N_normal






    sorry
  .
    -- let ker_generatse: Generates := {
    --   G := Multiplicative data.φ.ker
    --   g_group := by infer_instance
    --   g_eq := by infer_instance
    --   S := (S_n_ker_phi φ γ hγ n)
    --   hS := sorry
    --   generates := sorry
    --   one_mem := sorry
    --   has_inv := sorry
    --   g_infinite := sorry
    -- }
    sorry

lemma three_two_kernel_virtually_nilpotent (d: ℕ) (hd: d >= 1) (n: ℕ) (hG: HasPolynomialGrowthD S d) (g: G) (φ: (Additive G) →+ ℤ) (γ: G)  (hγ : φ γ = 1) (phi_gromov: Group.IsVirtuallyNilpotent (Multiplicative φ.ker))
 : HasPolynomialGrowthD (d - 1) (S := phi_generating n φ γ ) := by
  unfold HasPolynomialGrowthD
  unfold Group.IsVirtuallyNilpotent at phi_gromov
  obtain ⟨pre_N, nilpotent_pre_N, old_finite_index_pre_N⟩ := phi_gromov
  let N := pre_N.normalCore
  have nilpotent_N: Group.IsNilpotent N := by
    rw [nilpotent_iff_lowerCentralSeries]
    rw [nilpotent_iff_lowerCentralSeries] at nilpotent_pre_N
    obtain ⟨n, hn⟩ := nilpotent_pre_N
    have := lowerCentralSeries_map_subtype_le N n
    simp at this
    sorry
  have N_normal: N.Normal := by
    simp [N]
    apply Subgroup.normalCore_normal
  sorry

--have poly_r: ∀ r: ℕ, r * #()

  --let new_elem := fun (s: G) => s * (γ ^ )



-- Decompose list of {e_k, γ}:

-- The starting list must have the powers of γ sum to zero (since it's in the kernel of φ)


-- Map the list in a way that maintains the invariant that the powers of γ sum to zero:
-- If the head is e_i, then map it to γ_0,i = e_i
-- Otherwise, collect gamma terms:
-- If we get γ^a e_i * γ^b, then
-- * If the head is γ^n e_i for some n (collecting up adjacent γ), then choose γ_n,i = γ^n * e_i * γ^(-n)
-- * If the remaining list is just γ^n, then n must be 0 (since we maintained the invariant)

#print axioms three_two_gamma_m_generates
#print axioms three_two_ker_fg

lemma main_gromov_theorem (n: ℕ) (h: HasPolynomialGrowthD S n): Group.IsVirtuallyNilpotent G := by
  induction hn: n generalizing hGS n with
  | zero =>
    simp [HasPolynomialGrowthD] at h
    obtain ⟨a, ha⟩ := h
    simp [hn] at ha

    have S_closure := hGS.generates

    let pow_cards := Set.range (fun (n: ℕ) => #(S ^ n))
    -- TODO - this can probably be much simpler
    have pow_cards_bounded: ∃ y, ∀ n ∈ pow_cards, n ≤ y := by
      use a
      intro n hn
      simp [pow_cards] at hn
      obtain ⟨y, hy⟩ := hn
      rw [← hy]

      by_cases y_eq_zero: y = 0
      . simp [y_eq_zero]

        -- TODO - deduplicate this
        have a_ne_zero: a ≠ 0 := by
          by_contra!
          rw [this] at ha
          have hg_one := ha 1 (by omega)
          simp at hg_one
          have one_mem := hGS.one_mem
          rw [hg_one] at one_mem
          simp at one_mem

        omega
      . by_cases y_eq_one: y = 1
        .
          simp [y_eq_one]
          have card_mono := Finset.card_pow_mono (s := S) (m := 1) (n := 2) (by simp) (by simp)
          have card_two_le := ha 2 (by simp)
          simp at card_mono
          linarith
        .
          exact ha y (by omega)



    classical
    have max_card_mem := Nat.sSup_mem (s := pow_cards) ?_ ?_
    . simp [pow_cards] at max_card_mem
      obtain ⟨y, hy⟩ := max_card_mem



      have all_closure_mem: ∀ s ∈ (Subgroup.closure S), s ∈ (S ^ y) := by
        intro s hs
        induction hs using Subgroup.closure_induction with
        | one =>
          apply Finset.one_mem_pow
          exact Generates.one_mem
        | mem x hx =>
          by_cases y_eq_zero: y = 0
          .
            rw [y_eq_zero]
            rw [y_eq_zero] at hy
            simp at hy
            simp
            have y_eq := Nat.sSup_def (s := pow_cards) pow_cards_bounded
            have find_le := Nat.find_spec pow_cards_bounded
            rw [← y_eq] at find_le
            have S_one_le := find_le #(S) ?_
            .
              simp [pow_cards] at S_one_le
              rw [← hy] at S_one_le
              rw [Finset.card_le_one] at S_one_le
              have one_mem: 1 ∈ S := by exact Generates.one_mem
              have x_eq := S_one_le 1 one_mem x hx
              apply x_eq.symm
            . simp [pow_cards]
              use 1
              simp
          .
            have pow_mono := Finset.pow_subset_pow_right (s := S) (Generates.one_mem) (n := y) (m := 1) (by omega)
            simp at pow_mono
            apply pow_mono hx
        | mul a b a_mem_closure b_mem_closure a_mem_pow b_mem_pow =>
          by_cases y_eq_zero: y = 0
          .
            simp [y_eq_zero]
            simp [y_eq_zero] at a_mem_pow b_mem_pow
            simp [a_mem_pow, b_mem_pow]
          .
            by_contra!
            have a_b_mem_two: a * b ∈ (S ^ (y * 2)) := by
              have mem_mul := Finset.mul_mem_mul a_mem_pow b_mem_pow
              rw [← pow_two] at mem_mul
              rw [← pow_mul] at mem_mul
              exact mem_mul

            have card_le := Finset.card_pow_mono (s := S) (m := y) (n := (y * 2))  (by omega) (by omega)
            have subset := Finset.pow_subset_pow_right (s := S) (Generates.one_mem) (m := y) (n := (y * 2)) (by omega)

            have strict_subset : (S ^ y) ⊂ (S ^ (y * 2)) := by
              rw [Finset.ssubset_iff_of_subset subset]
              use (a * b)

            have card_lt: #(S ^ y) < #(S ^ (y * 2)) := by
              exact Finset.card_lt_card strict_subset


            rw [hy] at card_lt
            have y_eq := Nat.sSup_def (s := pow_cards) pow_cards_bounded
            have find_le := Nat.find_spec pow_cards_bounded
            rw [← y_eq] at find_le
            have reverse_le := find_le #(S ^ (y * 2)) ?_
            .
              simp [pow_cards] at reverse_le
              linarith
            . simp [pow_cards]
        | inv a ha a_mem_pow =>
          rw [← Finset.mem_inv']
          rw [← inv_pow]
          rw [← S_eq_Sinv]
          exact a_mem_pow

      have G_finite: Finite G := by
        rw [← Set.finite_univ_iff]
        have univ_eq: (Set.univ : Set G) = (S ^ y) := by
          simp at S_closure

          apply_fun (fun y => y.carrier) at S_closure
          conv at S_closure =>
            rhs
            equals Set.univ =>
              exact rfl

          rw [← S_closure]
          ext a
          refine ⟨?_, ?_⟩
          . intro ha
            simp at ha
            rw [← Finset.coe_pow]
            exact all_closure_mem a ha
          . intro ha
            simp
            exact mem_closure a

        rw [univ_eq]
        rw [← Finset.coe_pow]
        exact Finset.finite_toSet (S ^ y)

      rw [Group.IsVirtuallyNilpotent]
      use ⊥
      refine ⟨?_, ?_⟩
      . exact CommGroup.isNilpotent
        -- TODO - prove that a finite group is nilpotent, and upstream to mathlib
      . infer_instance
    .
      simp [pow_cards]
      apply Set.range_nonempty
    .
      rw [bddAbove_def]
      exact pow_cards_bounded
  | succ k ih =>
    obtain ⟨data⟩ := exists_theorem_3_1_input h
    apply theorem_3_1 data n (by omega) h
    intro Q Q_dec_eq Q_group Q_FG hS

    let generates: Generates := {
      G := Q,
      g_group := Q_group
      g_eq := Q_dec_eq
      S := Q_FG.out.choose ∪ Q_FG.out.choose⁻¹ ∪ {1}
      hS := by simp
      generates := by
        simp
        rw [Subgroup.closure_union]
        rw [Q_FG.out.choose_spec]
        simp
      one_mem := by
        simp
      has_inv := by
        intro g hg
        simp at hg
        simp
        grind
      g_infinite := by
        sorry
    }
    have new_poly := poly_growth_equiv_generates generates Q_FG.out.choose (d := n - 1) sorry
    have prev := @ih generates (by sorry) (n - 1) sorry
    sorry
