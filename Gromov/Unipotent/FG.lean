module

public import Mathlib
public import Gromov.Unipotent.Commutator

/-!
# Finite generation of subgroups

That subgroups of finitely generated abelian and nilpotent groups are finitely generated, plus
the supporting transfer lemmas along homomorphisms.
-/

public section

set_option linter.style.longLine false
set_option linter.style.commandStart false
set_option linter.style.cdot false

open scoped commutatorElement IsMulCommutative Pointwise

variable {G: Type*} [Group G] [DecidableEq G] (S: Finset G)

variable {G: Type*} [Group G] [DecidableEq G] (S: Finset G)


-- https://math.stackexchange.com/questions/4995327/group-in-the-lower-central-series-is-generated-by-conjugates-of-comutators-of-ge
lemma iterate_comm_generates (hS: Subgroup.closure (S: Set G) = ⊤) (n: ℕ):
  (Subgroup.normalClosure (iterate_comm_set (S) n)) = (⊤ : Subgroup G).lowerCentralSeries n := by
  induction n with
  | zero =>
    simp [iterate_comm_set]

    have closure_le: ⊤ ≤ Subgroup.closure (S : Set G) := by
      simp [hS]


    rw [eq_top_iff]
    grw [closure_le]
    apply Subgroup.closure_le_normalClosure
  | succ n ih =>
    simp [lowerCentralSeries]
    rw [le_antisymm_iff]
    refine ⟨?_, ?_⟩
    .
      simp [Subgroup.normalClosure]
      intro y hy
      simp [Group.conjugatesOfSet, iterate_comm_set] at hy
      obtain ⟨s, s_mem, ⟨c, c_mem, c_comm⟩⟩ := hy
      simp [conjugatesOf] at c_comm
      obtain ⟨x, x_mem⟩ := c_comm
      rw [← x_mem]
      apply Subgroup.Normal.conj_mem
      . infer_instance
      .
        apply Subgroup.commutator_mem_commutator
        .
          rw [← ih]
          apply Subgroup.mem_closure_of_mem
          simp [Group.conjugatesOfSet]
          use c
          refine ⟨c_mem, ?_⟩
          simp [conjugatesOf]
          use 1
          simp
        . simp
    .

      have image_commute: ∀ s ∈ S, ∀ g ∈ (iterate_comm_set (S) n), QuotientGroup.mk' (((Subgroup.normalClosure (iterate_comm_set (S) (n + 1))))) (s * g) = QuotientGroup.mk' (((Subgroup.normalClosure (iterate_comm_set (S) (n + 1))))) (g * s) := by
        intro s hs g hg
        simp
        rw [← QuotientGroup.mk_mul]
        rw [← QuotientGroup.mk_mul]
        rw [QuotientGroup.eq]
        simp [Subgroup.normalClosure]
        rw [← Subgroup.inv_mem_iff]
        simp
        rw [← Subgroup.closure_inv]
        apply Subgroup.mem_closure_of_mem
        simp [-Set.mem_inv, Group.conjugatesOfSet]
        simp only [conjugatesOf]
        use g * s * g⁻¹ * s⁻¹
        refine ⟨?_, ?_⟩
        . simp [iterate_comm_set]
          use s
          refine ⟨by simp [hs], ?_⟩
          use g
          refine ⟨hg, ?_⟩
          simp [Bracket.bracket]
        .
          simp
          use s⁻¹ * g⁻¹
          group

      have comm_subset_center: (QuotientGroup.mk' _) '' (iterate_comm_set (S) n) ⊆ ((Subgroup.center (G ⧸ ((Subgroup.normalClosure (iterate_comm_set (S) (n + 1)))))).carrier) := by
        intro x hx
        simp at hx
        obtain ⟨a, a_mem, hx⟩ := hx
        rw [Subgroup.mem_carrier]
        rw [Subgroup.mem_center_iff]
        intro b
        rw [← QuotientGroup.out_eq' (a := b)]
        rw [← hx]
        rw [← QuotientGroup.mk_mul]
        rw [← QuotientGroup.mk_mul]
        rw [QuotientGroup.eq]
        simp


        have b_mem_top: Quotient.out b ∈ (⊤ : (Subgroup G)) := by
          simp

        rw [← hS] at b_mem_top

        -- TODO - figure out how to get the 'induction' tactic working here
        apply Subgroup.closure_induction (p := fun y hy => a⁻¹ * y⁻¹ * (a * y) ∈ Subgroup.normalClosure (iterate_comm_set (S) (n + 1))) (hx := b_mem_top)
        .
          intro s hs
          have comm := image_commute s hs a a_mem
          simp at comm
          rw [← QuotientGroup.mk_mul] at comm
          rw [← QuotientGroup.mk_mul] at comm
          rw [QuotientGroup.eq] at comm
          simp at comm
          exact comm
        . simp
        . intro y hy z hz y_mem z_mem
          simp
          conv =>
            arg 2
            equals (a⁻¹ * hy⁻¹ * a * hy) * (hy⁻¹ * a⁻¹ * y⁻¹ * a * y * hy) =>
              group
          apply Subgroup.mul_mem
          . group
            group at z_mem
            exact z_mem
          .
            have foo := (Subgroup.normalClosure_normal).conj_mem _ y_mem hy⁻¹
            simp at foo
            group at foo
            group
            exact foo
        .
          intro y hy y_mem
          rw [← Subgroup.inv_mem_iff]
          simp
          have foo := (Subgroup.normalClosure_normal).conj_mem _ y_mem y
          group at foo
          group
          exact foo


      simp [Bracket.bracket]
      intro g hg
      simp at hg
      obtain ⟨a, a_mem, b, g_eq⟩ := hg
      have normal_le_center := Subgroup.normalClosure_le_normal comm_subset_center
      rw [← Subgroup.map_normalClosure] at normal_le_center
      rw [ih] at normal_le_center
      simp
      have a_mem_center := @normal_le_center a⁻¹ ?_
      .
        rw [Subgroup.mem_center_iff] at a_mem_center
        specialize a_mem_center (QuotientGroup.mk b⁻¹)
        rw [← QuotientGroup.mk_inv] at a_mem_center
        rw [← QuotientGroup.mk_mul] at a_mem_center
        rw [← QuotientGroup.mk_mul] at a_mem_center
        rw [QuotientGroup.eq] at a_mem_center
        simp at a_mem_center
        rw [← g_eq]
        group at a_mem_center
        group
        exact a_mem_center
      . simp
        use a


      simp
      exact QuotientGroup.mk_surjective

#print axioms iterate_comm_generates

-- Lemma 13.55 from https://www.math.ucdavis.edu/~kapovich/EPR/ggt.pdf
lemma comm_trivial_implies_nilpotent {G: Type*} [DecidableEq G] [Group G] (S: Finset G) (hS: Subgroup.closure (S: Set G) = ⊤) (n: ℕ) (h_comm: iterate_comm_set (S) (n) = {1}):
    (⊤ : Subgroup G).lowerCentralSeries n = ⊥ := by

  rw [← iterate_comm_generates S hS n]
  rw [h_comm]
  simp [Subgroup.normalClosure]
  intro g hg
  simp [Group.conjugatesOfSet, conjugatesOf] at hg
  exact hg


lemma normal_comm_mem {G: Type*} [Group G] {N: Subgroup G} (N_normal: N.Normal) (a b: G) (ha: a ∈ N) :
  ⁅a, b⁆ ∈ N := by

  dsimp [Bracket.bracket]
  have conj_mem := N_normal.conj_mem a⁻¹ (by simp [ha]) b
  conv =>
    arg 2
    equals a * (b * a⁻¹ * b⁻¹) => group

  apply Subgroup.mul_mem
  . exact ha
  . exact conj_mem


-- TODO - cleanup and upstream to mathlib
@[expose]
instance torsion_characteristic {G: Type*} [CommGroup G]: (CommGroup.torsion G).Characteristic := by
  rw [Subgroup.characteristic_iff_le_map]
  intro f g hg
  simp
  rw [CommGroup.mem_torsion] at hg
  use (f.symm.toMonoidHom g)
  refine ⟨?_, by simp⟩
  rw [CommGroup.mem_torsion]
  apply MonoidHom.isOfFinOrder
  exact hg

-- TODO - generalize and upstream to mathlib


@[expose]
instance subgroup_map_finite {A B: Type*} [Group A] [Group B] (f: A →* B) (G: Subgroup A) [Finite G]: Finite (Subgroup.map f G) := by
  have foo: (Subgroup.map f G) ≃ (Set.image f G.carrier) := {
    toFun := fun a => a
    invFun := fun a => a
  }
  rw [Equiv.finite_iff foo]
  rw [Set.finite_coe_iff]
  apply Finite.Set.finite_image

-- TODO - generalize and pr to mathlib
lemma fg_of_subgroup_fg_comm {A : Type*} [CommGroup A] [Group.FG A] (H : Subgroup A) : H.FG := by
  rw [Subgroup.fg_iff_add_fg]
  have : Module.Finite ℤ (Additive A) := Module.Finite.iff_addGroup_fg.mpr inferInstance
  have h := IsNoetherian.noetherian (R := ℤ) (AddSubgroup.toIntSubmodule H.toAddSubgroup)
  rw [Submodule.fg_iff_addSubgroup_fg] at h
  simpa using h

lemma fg_extension {A: Type*} [Group A] (N: Subgroup A) [N.Normal] (hN: N.FG) (hQ: Group.FG (A ⧸ N)): Group.FG A := by
  classical
  obtain ⟨S_Q, hS_Q⟩ := hQ
  obtain ⟨S_N, hS_N⟩ := hN
  let SQ_out := Finset.image (fun (a: (A ⧸ N)) => a.out) S_Q
  have SQ_eq: S_Q = Finset.image (QuotientGroup.mk' _) SQ_out := by
    simp [SQ_out]
    ext a
    simp

  rw [Group.fg_def, Subgroup.fg_iff]
  rw [SQ_eq] at hS_Q
  use S_N ∪ SQ_out
  refine ⟨?_, ?_⟩
  .
    simp [SQ_out]
    rw [Subgroup.closure_union]
    simp [hS_N]
    ext a
    simp
    by_cases mem_N: a ∈ N
    . apply Subgroup.mem_sup_left
      exact mem_N
    .
      let a_map: (A ⧸ N) := a
      have a_mem_top: a_map ∈ (⊤ : Subgroup (A ⧸ N)) := by
        simp

      rw [← hS_Q] at a_mem_top
      simp only [Finset.coe_image] at a_mem_top
      rw [← MonoidHom.map_closure] at a_mem_top
      simp at a_mem_top
      obtain ⟨k, hk⟩ := a_mem_top
      simp [SQ_out] at hk
      simp [a_map] at hk
      have a_eq := hk.2
      rw [QuotientGroup.eq] at a_eq
      rw [← Subgroup.mul_mem_cancel_left (x := k⁻¹)]
      .
        apply Subgroup.mem_sup_left
        exact a_eq
      . apply Subgroup.mem_sup_right
        simp
        exact hk.1

  . simp

lemma fg_domain_of_ker_range {A B: Type*} [Group A] [Group B] (f : A →* B) (hA: Subgroup.FG f.ker) (hB: Subgroup.FG f.range): Group.FG A := by
  have new_fg := fg_extension (f.ker) hA
  apply new_fg
  have equiv := QuotientGroup.quotientKerEquivRange f
  rw [← Group.fg_iff_subgroup_fg] at hB
  apply Group.fg_of_surjective (f := equiv.symm.toMonoidHom)
  simp
  exact MulEquiv.surjective equiv.symm

lemma Group.FG.of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (h : Group.FG G) :
    Group.FG H :=
  haveI := h
  Group.fg_of_surjective (f := e.toMonoidHom) e.surjective

set_option maxHeartbeats 5000000 in
lemma fg_of_subgroup_fg_nilpotent {A: Type*} [DecidableEq A] [Group A] [Group.IsNilpotent A] (A_fg: Group.FG A) (H: Subgroup A): H.FG := by
  classical
  revert H
  induction hn: Group.nilpotencyClass A using Nat.strong_induction_on generalizing A with
  | h n ih =>
  match n with
  | 0 =>
    rw [Group.nilpotencyClass_zero_iff_subsingleton] at hn
    intro H
    have H_eq: H = ⊥ := by
      ext a
      simp
      simp [Subsingleton.eq_one a]
    simp [H_eq]
    exact fg_of_subgroup_fg_comm ⊥
  | n + 1 =>
    have comm_eq := Subgroup.lowerCentralSeries_succ (⊤ : Subgroup A) n
    rw [← hn] at comm_eq
    rw [Subgroup.lowerCentralSeries_nilpotencyClass] at comm_eq
    conv at comm_eq =>
      rhs
      simp
    rw [eq_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at comm_eq
    simp [Subgroup.centralizer_univ] at comm_eq
    have n_fg: (Subgroup.lowerCentralSeries (⊤ : Subgroup A) n).FG := by
      obtain ⟨S, hS⟩ := A_fg
      rw [lower_central_generates_succ (G := A) S hS]
      rw [← hn]
      simp
      rw [← Group.fg_iff_subgroup_fg]
      apply Group.closure_finset_fg

    specialize ih (A := A ⧸  (Subgroup.lowerCentralSeries (⊤ : Subgroup A) n)) (Group.nilpotencyClass (A ⧸ (⊤ : Subgroup A).lowerCentralSeries n)) (by
      -- The `n`-th term of the lower central series of `A ⧸ Cⁿ A` is the image of `Cⁿ A`, i.e. `⊥`.
      -- Hence that quotient has class `≤ n < n + 1 = nilpotencyClass A`.
      have key : (⊤ : Subgroup (A ⧸ (⊤ : Subgroup A).lowerCentralSeries n)).lowerCentralSeries n
          = ⊥ := by
        have hmap : Subgroup.map
            (QuotientGroup.mk' ((⊤ : Subgroup A).lowerCentralSeries n)) (⊤ : Subgroup A) = ⊤ :=
          Subgroup.map_top_of_surjective _ QuotientGroup.mk_surjective
        rw [← hmap, ← Subgroup.map_lowerCentralSeries, Subgroup.map_eq_bot_iff,
          QuotientGroup.ker_mk']
      have h_le := Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp key
      omega
    ) (by infer_instance) rfl

    intro H
    have h_inf_fg: ((H ⊓ (⊤ : Subgroup A).lowerCentralSeries n).subgroupOf ((⊤ : Subgroup A).lowerCentralSeries n)).FG := by
      let c_comm := Group.commGroupOfCenterEqTop (G := ((⊤ : Subgroup A).lowerCentralSeries n)) (by
        rw [Subgroup.eq_top_iff']
        intro x
        rw [Subgroup.mem_center_iff]
        intro y
        have foo := comm_eq x.prop
        rw [Subgroup.mem_center_iff] at foo
        specialize foo y.val
        ext
        simpa using foo
      )
      rw [← Group.fg_iff_subgroup_fg] at n_fg
      apply fg_of_subgroup_fg_comm


    rw [← Group.fg_iff_subgroup_fg]
    apply fg_domain_of_ker_range ((QuotientGroup.mk' ((⊤: Subgroup A).lowerCentralSeries n)).comp H.subtype)
    .
      -- The kernel is `N.subgroupOf H = (H ⊓ N).subgroupOf H`, which is the same abstract group as
      -- `(H ⊓ N).subgroupOf N` — the version we proved FG using that `N` is abelian.
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', Subgroup.comap_subtype,
        ← Subgroup.inf_subgroupOf_left, ← Group.fg_iff_subgroup_fg]
      exact Group.FG.of_mulEquiv
        ((Subgroup.subgroupOfEquivOfLe inf_le_right).trans
          (Subgroup.subgroupOfEquivOfLe inf_le_left).symm)
        ((Group.fg_iff_subgroup_fg _).mpr h_inf_fg)
    .
      -- The range is the image of `H` in `A ⧸ Cⁿ A`, which is FG by the induction hypothesis.
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
      exact ih (Subgroup.map (QuotientGroup.mk' _) H)

lemma mul_aut_iterate {G: Type*} [Group G] (f: MulAut G) (n: ℕ): f^[n] = ⇑(f ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    ext a
    rw [Function.iterate_succ_apply, pow_succ, MulAut.mul_apply, ← ih]


lemma toIntLinearMap_pow_apply {M : Type*}  [AddCommGroup M]  (f : M →+ M) (g: M) (n: ℕ): ((f.toIntLinearMap)^(n)) g = (f^[n]) g := by
  induction n generalizing g with
  | zero =>
    simp
  | succ n ih =>
    rw [pow_succ]
    rw [Function.iterate_succ]
    simp
    rw [ih]

lemma toIntLinearMap_comp_mul {M : Type*}  [AddCommGroup M] (f g : M →+ M): ((f.comp g).toIntLinearMap) = f.toIntLinearMap * g.toIntLinearMap := by
  ext a
  simp


@[simp]
lemma toIntLinearMap_id {M : Type*}  [AddCommGroup M]: (AddMonoidHom.id M).toIntLinearMap = LinearMap.id := by
  ext a
  simp

/-- Compare cardinalities of two images of the same underlying products, pushed through a
homomorphism `ψ` and through an injective homomorphism `j`.  Used to move a bound proved in
`↥N'` across to the quotient `↥(Subgroup.center ↥N') ⧸ torsion`. -/
theorem card_image_listProd_hom_le {C Q N ι : Type*}
    [Group C] [Group Q] [Group N] [DecidableEq Q] [DecidableEq N]
    (ψ : C →* Q) (j : C →* N) (hj : Function.Injective j)
    (P : Finset (Finset ι)) (f : ι → C) :
    (P.image (fun x => (List.map (fun i => ψ (f i)) x.toList).prod)).card
      ≤ (P.image (fun x => (List.map (fun i => j (f i)) x.toList).prod)).card := by
  classical
  have h1 : ∀ x : Finset ι,
      (List.map (fun i => ψ (f i)) x.toList).prod = ψ ((List.map f x.toList).prod) := by
    intro x
    rw [show (fun i => ψ (f i)) = (ψ : C → Q) ∘ f from rfl, ← List.map_map, List.prod_hom]
  have h2 : ∀ x : Finset ι,
      (List.map (fun i => j (f i)) x.toList).prod = j ((List.map f x.toList).prod) := by
    intro x
    rw [show (fun i => j (f i)) = (j : C → N) ∘ f from rfl, ← List.map_map, List.prod_hom]
  simp_rw [h1, h2]
  rw [show (fun x : Finset ι => ψ ((List.map f x.toList).prod))
        = ψ ∘ (fun x : Finset ι => (List.map f x.toList).prod) from rfl,
     show (fun x : Finset ι => j ((List.map f x.toList).prod))
        = j ∘ (fun x : Finset ι => (List.map f x.toList).prod) from rfl,
     ← Finset.image_image, ← Finset.image_image, Finset.card_image_of_injective _ hj]
  exact Finset.card_image_le
