import Mathlib

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
open scoped commutatorElement

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

lemma word_dist_mul_eq {x y z : G} (hy: y ∈ S): WordDist x z = (WordDist x (y * z)) + 1 ∨ WordDist x z + 1 = (WordDist x (y * z)) ∨ WordDist x z = (WordDist x (y * z)) := by
  have first := dist_word_le_mul (x := x) (y := y) (z := z) hy
  have second := dist_word_le_mul (x := x) (y := y⁻¹) (z := (y * z)) (by rw [S_eq_Sinv]; simp [hy])
  simp at second
  grind

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

lemma word_norm_inv_le (x: G): WordNorm x ≤ WordNorm x⁻¹ := by
  simp [WordNorm]
  apply csInf_le'
  simp
  obtain ⟨lx, x_prod, x_len⟩ := word_norm_prod_self x⁻¹
  use (lx.map (fun (x: S) => ⟨x.val⁻¹, by (
      rw [← Finset.mem_inv']
      rw [← S_eq_Sinv]
      simp
    )⟩)).reverse
  refine ⟨?_, ?_⟩
  .
    simp
    exact x_len
  .
    simp [ProdS]

    clear x_len

    induction lx generalizing x with
    | nil =>
      simp
      simp [ProdS] at x_prod
      grind
    | cons head tail ih =>
      simp
      simp [ProdS] at x_prod
      simp [ProdS] at ih
      rw [ih (x := tail.unattach.prod⁻¹)]
      .
        rw[← inv_eq_iff_eq_inv] at x_prod
        simp [← x_prod]
      . simp


lemma word_norm_inv (x: G): WordNorm x = WordNorm x⁻¹ := by
apply Nat.le_antisymm
. apply word_norm_inv_le
.
  conv =>
    rhs
    equals WordNorm x⁻¹⁻¹ => simp
  apply word_norm_inv_le


lemma WordDist_one (x: G): WordDist x 1 = WordNorm x := by
  simp [WordDist]
  rw [← word_norm_inv]


-- noncomputable instance WordNorm.instSemiNormedGroup: SeminormedGroup G where
--   norm := fun g => WordNorm g
--   dist_eq := by
--     intro x y
--     simp [dist, WordDist]
--     sorry



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

lemma S_card_ne_zero_re: (#(S) : ℝ) ≠ 0 := by
  norm_cast
  simp
  have foo := hS
  simp only [nonempty_subtype] at foo
  exact Finset.nonempty_iff_ne_empty.mp foo

lemma S_card_ne_zero: (#(S) : ℂ) ≠ 0 := by
  norm_cast
  simp
  have foo := hS
  simp only [nonempty_subtype] at foo
  exact Finset.nonempty_iff_ne_empty.mp foo

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
    have foo := S_card_ne_zero
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

noncomputable instance finite_ball (x: G) (r: ℝ): Set.Finite (Metric.ball x r) := Set.Finite.of_finite_image (f := fun a => (word_norm_prod_self a).choose) (by
  have foo := List.finite_length_le S (WordNorm x + ⌈r⌉₊)
  rw [← Set.finite_coe_iff, Set.coe_setOf] at foo
  apply Finite.of_injective (β := {l : List S // l.length ≤ WordNorm x + ⌈r⌉₊}) (fun a => ⟨a.val, by (
    have ha := a.prop
    simp [-Subtype.coe_prop] at ha
    obtain ⟨y, hy, a_prod⟩ := ha
    have ⟨prod_eq, prod_len⟩ := (word_norm_prod_self y).choose_spec
    rw [a_prod] at prod_len
    rw [prod_len]
    simp [dist] at hy
    conv =>
      lhs
      equals WordDist 1 y =>
        simp [WordDist]


    grw [WordDist_triangle (y := x)]
    nth_rw 2 [WordDist_comm]
    simp [WordDist]
    simp [WordDist] at hy
    rw [← Nat.lt_ceil] at hy
    grind
  )⟩) ?_
  intro a b hab
  grind
) (by
  intro a ha b hb hab
  have a_prop := (word_norm_prod_self a).choose_spec.1
  have b_prop := (word_norm_prod_self b).choose_spec.1
  rw [← a_prop, ← b_prop]
  simp [hab]
)

-- TODO - deduplicate 99% of this with finite_ball
noncomputable instance finite_closed_ball (x: G) (r: ℝ): Set.Finite (Metric.closedBall x r) := Set.Finite.of_finite_image (f := fun a => (word_norm_prod_self a).choose) (by
  have foo := List.finite_length_le S (WordNorm x + ⌈r⌉₊)
  rw [← Set.finite_coe_iff, Set.coe_setOf] at foo
  apply Finite.of_injective (β := {l : List S // l.length ≤ WordNorm x + ⌈r⌉₊}) (fun a => ⟨a.val, by (
    have ha := a.prop
    simp [-Subtype.coe_prop] at ha
    obtain ⟨y, hy, a_prod⟩ := ha
    have ⟨prod_eq, prod_len⟩ := (word_norm_prod_self y).choose_spec
    rw [a_prod] at prod_len
    rw [prod_len]
    simp [dist] at hy
    conv =>
      lhs
      equals WordDist 1 y =>
        simp [WordDist]


    grw [WordDist_triangle (y := x)]
    nth_rw 2 [WordDist_comm]
    simp [WordDist]
    simp [WordDist] at hy
    -- This is the only part that's different from finite_ball
    grw [Nat.le_ceil (a := r)] at hy
    simpa using hy
  )⟩) ?_
  intro a b hab
  grind
) (by
  intro a ha b hb hab
  have a_prop := (word_norm_prod_self a).choose_spec.1
  have b_prop := (word_norm_prod_self b).choose_spec.1
  rw [← a_prop, ← b_prop]
  simp [hab]
)

-- TODO - make this Finite to avoid a non-compuatable Fintype instance
noncomputable instance fintype_ball (x: G) (r: ℝ): Fintype ↑(Metric.ball x r) := Set.Finite.fintype (finite_ball _ _)
noncomputable instance fintype_closedBall (x: G) (r: ℝ): Fintype ↑(Metric.closedBall x r) := Set.Finite.fintype (finite_closed_ball _ _)

instance fintype_ball_boundary (x: G) (r: ℝ): Fintype ↑{y | dist y x = r} := by
  sorry

-- Graphs and Discrete Direchlet Spaces
-- https://www.math.uni-potsdam.de/fileadmin/user_upload/Prof-GraphTh/Keller/KellerLenzWojciechowski_GraphsAndDiscreteDirichletSpaces_wu_version.pdf


-- Lemma 12.2 in Keller (Graphs and Discrete Dirichlet Spaces), specialized to harmonic functions: L(u) = 0
--lemma laplace_harmonic_cutoff (f φ : G → ℝ) (x): ∑ x ∈ Metric.ball 1 (2 * r), ∑ s ∈ S, |(f x) - f (s * x)|^2


-- lemma s_sinv_split_one: S = (S \ {1}) ∪ (S⁻¹ \ {1}) ∪ {1} := by
--   rw [← s_union_sinv]
--   ext a
--   by_cases a_eq_one: a = 1
--   .
--     simp [a_eq_one]
--     apply hGS.one_mem
--   .
--     simp [a_eq_one]
--     grind




-- New argument:
-- Write ∑ s ∈ S (f x - f (x * s))^2
-- = ∑ s ∈ S (f x)^2 - (f x) (f ( x * s)) + (f (x * s))^2
-- = |S| * (f x)^2 - (f x) * |S| * (f x) + |S| * (f x)^2 -- use harmonicity, and simplify the shift 'f ( x *s)' when summing over all x
-- = |S| * (f x)^2

-- New approach
-- (f△f) = f(f - (f ⬝ μ)) = f^2 - f(f ⬝ μ)

--  f^2 - f(f ⬝ μ) +

-- Other stuff:
--   (∑ s ∈ S, (f x - f (x * s)))^2
-- = (∑ s_1 ∈ S, ∑ s_2 ∈ S, ((f x) - f(x * s_1))*((f x) - f(x * s_2)
-- = (∑ s_1 ∈ S, ∑ s_2 ∈ S, (f x)^2 - (f x)(f (x * s_1)) - (f x) (f (x * s_2)) + (f (x * s_1))(f (x * s_2)))
-- = (∑ s_1 ∈ S, ∑ s_2 ∈ S, (f x)^2 - (f x)((f (x * s_1) - (f (x * s_2))) + (f (x * s_1))(f (x * s_2)))
lemma harmonic_stokes_theorem (f: G → ℂ) (hf: Harmonic f) (r: ℝ): ∑ x ∈ Metric.ball 1 (2 * r), ∑ s ∈ S, (f x - f (x * s))^2 = 0 := by
  sorry
  --rw [s_sinv_split_one]
  --rw []


  -- Use this if we end up with closedBall in the theorem statement
  -- conv =>
  --   arg 1
  --   arg 1
  --   equals (Metric.ball 1 (2 * r)).toFinset ∪ {x : G | dist x 1 = 2 * r}.toFinset =>
  --     rw [← Set.toFinset_union]
  --     simp_rw [Metric.closedBall, Metric.ball]
  --     simp [le_iff_lt_or_eq]
  --     rw [Set.setOf_or]

  -- rw [Finset.sum_union]
  -- conv =>
  --   lhs
  --   lhs
  --   equals 0 =>


  --     sorry
  -- simp_rw [Metric.closedBall]

  --sorry

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
  replace hfh := ConstF.quotientRel_def.mp hfh
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




end GeneratesNS
