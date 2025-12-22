import Mathlib

lemma addgroup_fg_map {G G': Type*} [AddGroup G] [AddGroup G'] (H: AddSubgroup G) (h_fg: H.FG) (f: G →+ G'): (AddSubgroup.map f H).FG := by
  obtain ⟨s, hs⟩ := h_fg
  classical
  rw [AddSubgroup.fg_iff]
  use s.image f
  refine ⟨?_, ?_⟩
  .
    rw [Finset.coe_image]
    rw [← AddMonoidHom.map_closure]
    rw [hs]
  . simp
    exact Set.toFinite (⇑f '' ↑s)

lemma addsubgroup_z_map (n: ℕ) (H: AddSubgroup (Fin n → ℤ)): H.FG := by
  sorry

lemma fg_subgroup_of_abelian {G : Type*} [AddCommGroup G] (hG : AddGroup.FG G) (H : AddSubgroup G): H.FG := by
  have fg_top: (⊤ : AddSubgroup G).FG := by
    rw [← AddGroup.fg_def]
    infer_instance

  rw [AddSubgroup.fg_iff_exists_fin_addMonoidHom] at fg_top
  obtain ⟨n, f, hf⟩ := fg_top

  let H' := AddSubgroup.comap f H

  have H'_fg: H'.FG := by
   apply addsubgroup_z_map


  let new_H := AddSubgroup.map f (AddSubgroup.comap f H)

  have H_eq := AddSubgroup.map_comap_eq f H
  simp [hf] at H_eq
  rw [← H_eq]
  apply addgroup_fg_map
  apply H'_fg
