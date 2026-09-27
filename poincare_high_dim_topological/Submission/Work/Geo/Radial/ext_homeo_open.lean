import Mathlib

namespace Work.Geo.Radial

open Set Metric

/-- The naive extension of a self-homeomorphism `g` of an open set `O ⊆ M` to a self-map of `M`:
`g` on `O` and the identity off `O`.  (Continuity needs a hypothesis that `g` is the identity
off a compact subset of `O`; see `Work.Geo.Radial.ext_homeo_open`.) -/
noncomputable def radExt {M : Type*} [TopologicalSpace M] (O : Set M) (g : O ≃ₜ O) (x : M) : M := by
  classical
  exact if hx : x ∈ O then (g ⟨x, hx⟩ : M) else x

lemma radExt_of_mem {M : Type*} [TopologicalSpace M] (O : Set M) (g : O ≃ₜ O) {x : M}
    (hx : x ∈ O) : radExt O g x = (g ⟨x, hx⟩ : M) := by
  rw [radExt, dite_eq_left hx]

lemma radExt_of_notMem {M : Type*} [TopologicalSpace M] (O : Set M) (g : O ≃ₜ O) {x : M}
    (hx : x ∉ O) : radExt O g x = x := by
  rw [radExt, dite_eq_right hx]

/-- Blueprint C0 (`Work.Geo.Radial.ext_homeo_open`): a self-homeomorphism of an open subset `O`
of a Hausdorff space `M` which is the identity off a compact set `C ⊆ O` extends to a
self-homeomorphism of `M` which is the identity outside `O`.

Proof route: `C` is compact in `M` (continuous inclusion) hence closed (`T2Space`), so
`M \ C` is an open neighbourhood of `∂O` on which the extension `H` (given by `h` on `O` and the
identity outside) agrees with the identity; `h` and `h.symm` both fix `O \ C`, giving continuity
of `H` and of its inverse.

The intended fully-qualified name is `Work.Geo.Radial.ext_homeo_open`. -/
theorem ext_homeo_open {M : Type*} [TopologicalSpace M] [T2Space M] (O : Set M) (hO : IsOpen O)
    (h : O ≃ₜ O) (C : Set O) (hC : IsCompact C) (hid : ∀ x ∉ C, h x = x) :
    ∃ H : M ≃ₜ M, (∀ x : O, H x = h x) ∧ ∀ x ∉ O, H x = x := by
  classical
  -- `C`, viewed in `M`, is compact (continuous image of a compact set) hence closed.
  set Cm : Set M := (Subtype.val : O → M) '' C with hCmdef
  have hCmc : IsCompact Cm := hC.image continuous_subtype_val
  have hCcl : IsClosed Cm := hCmc.isClosed
  have hCsub : Cm ⊆ O := by
    rintro x ⟨c, hc, rfl⟩; exact c.2
  -- `h.symm` also fixes `O \ C` pointwise.
  have hid_symm : ∀ x ∉ C, h.symm x = x := by
    intro x hx
    have h2 : h.symm (h x) = h.symm x := congrArg h.symm (hid x hx)
    rw [Homeomorph.symm_apply_apply] at h2
    exact h2.symm
  -- The extension of any `g` fixing `O \ C` is continuous: `O` and `M \ C` are open and cover `M`.
  have contEf : ∀ (g : O ≃ₜ O), (∀ x ∉ C, g x = x) → Continuous (radExt O g) := by
    intro g hg
    have hOnO : ContinuousOn (radExt O g) O := by
      rw [continuousOn_iff_continuous_domRestrict]
      have key : O.domRestrict (radExt O g) = (Subtype.val : O → M) ∘ g := by
        funext x
        rw [Set.domRestrict_apply, Function.comp_apply, radExt_of_mem O g x.2]
      rw [key]
      exact continuous_subtype_val.comp g.continuous
    have hOnCompl : ContinuousOn (radExt O g) Cmᶜ := by
      refine ContinuousOn.congr continuousOn_id ?_
      intro x hx
      by_cases hxO : x ∈ O
      · have hxC : (⟨x, hxO⟩ : O) ∉ C := fun hc => hx ⟨⟨x, hxO⟩, hc, rfl⟩
        rw [radExt_of_mem O g hxO]
        exact congrArg Subtype.val (hg ⟨x, hxO⟩ hxC)
      · exact radExt_of_notMem O g hxO
    have hcover : O ∪ Cmᶜ = Set.univ := by
      rw [eq_univ_iff_forall]
      intro x
      by_cases hx : x ∈ O
      · exact Or.inl hx
      · exact Or.inr (fun hxc => hx (hCsub hxc))
    have hunion := ContinuousOn.union_of_isOpen hOnO hOnCompl hO hCcl.isOpen_compl
    rwa [hcover, continuousOn_univ] at hunion
  -- `radExt O h` and `radExt O h.symm` are mutually inverse.
  have hleft : Function.LeftInverse (radExt O h.symm) (radExt O h) := by
    intro x
    by_cases hx : x ∈ O
    · rw [radExt_of_mem O h hx, radExt_of_mem O h.symm (h ⟨x, hx⟩).2]
      rw [show (⟨((h ⟨x, hx⟩ : O) : M), (h ⟨x, hx⟩).2⟩ : O) = h ⟨x, hx⟩ from rfl]
      rw [Homeomorph.symm_apply_apply]
    · rw [radExt_of_notMem O h hx, radExt_of_notMem O h.symm hx]
  have hright : Function.RightInverse (radExt O h.symm) (radExt O h) := by
    intro x
    by_cases hx : x ∈ O
    · rw [radExt_of_mem O h.symm hx, radExt_of_mem O h (h.symm ⟨x, hx⟩).2]
      rw [show (⟨((h.symm ⟨x, hx⟩ : O) : M), (h.symm ⟨x, hx⟩).2⟩ : O) = h.symm ⟨x, hx⟩ from rfl]
      rw [Homeomorph.apply_symm_apply]
    · rw [radExt_of_notMem O h.symm hx, radExt_of_notMem O h hx]
  refine ⟨Homeomorph.mk (Equiv.mk (radExt O h) (radExt O h.symm) hleft hright)
      (contEf h hid) (contEf h.symm hid_symm), ?_, ?_⟩
  · intro x
    show radExt O h (x : M) = h x
    rw [radExt_of_mem O h x.2]
  · intro x hx
    exact radExt_of_notMem O h hx

end Work.Geo.Radial
