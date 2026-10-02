import Mathlib
import Submission.Work.ELAssembly.covering_sheet

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The fibre over a connected evenly-covered base set

Let `H : ↥(f ⁻¹' W) ≃ₜ ↥W × I` be a local trivialisation of `f` over a preconnected base `W`,
compatible with `f`.  Let `A = ↥(Subtype.val ⁻¹' U)` be the part of the total space lying over
`U`, and assume `A` is clopen.  Then for `z, z' ∈ W` the fibre `U ∩ f ⁻¹' {z'}` is in bijection
with the fixed index set `J = {i | H.symm (z, i) ∈ A}`.

This is the combinatorial heart of `bijOn_of_isCoveringMapOn_of_fibre`: it shows that the
"number of sheets" of the covering over `U` is constant along the connected base `V`.
-/

namespace Work.ELAssembly

open Set

noncomputable def fibre_equiv {f : ℂ → ℂ} {U W : Set ℂ} (hW : IsPreconnected W)
    {I : Type*} [TopologicalSpace I] (H : ↥(f ⁻¹' W) ≃ₜ ↥W × I)
    (hH : ∀ e, (H e).1.1 = f e.1)
    (hA : IsClopen (Subtype.val ⁻¹' U : Set ↥(f ⁻¹' W)))
    {z : ℂ} (hz : z ∈ W) (z' : ℂ) (hz' : z' ∈ W) :
    ↥(U ∩ f ⁻¹' {z'}) ≃
      ↥{i : I | H.symm ((⟨z, hz⟩ : ↥W), i) ∈ (Subtype.val ⁻¹' U : Set ↥(f ⁻¹' W))} := by
  have hAlc : IsLocallyConstant
      (fun e : ↥(f ⁻¹' W) => e ∈ (Subtype.val ⁻¹' U : Set ↥(f ⁻¹' W))) :=
    isLocallyConstant_mem_of_isClopen hA
  -- fibre value of a point of `U ∩ f ⁻¹' {z'}`
  have hval : ∀ e : ↥(U ∩ f ⁻¹' {z'}), f e.1 = z' := by
    intro e
    have hh := e.2.2
    rwa [Set.mem_preimage, Set.mem_singleton_iff] at hh
  have memW : ∀ e : ↥(U ∩ f ⁻¹' {z'}), f e.1 ∈ W := fun e => by
    rw [hval e]; exact hz'
  -- forward direction lands in `J`
  have key : ∀ e : ↥(U ∩ f ⁻¹' {z'}),
      (H ⟨e.1, memW e⟩).2 ∈
        {i : I | H.symm ((⟨z, hz⟩ : ↥W), i) ∈ (Subtype.val ⁻¹' U : Set ↥(f ⁻¹' W))} := by
    intro e
    have hx1 : (H ⟨e.1, memW e⟩).1 = (⟨z', hz'⟩ : ↥W) :=
      Subtype.ext (by rw [hH, hval e])
    have hs : H.symm ((⟨z', hz'⟩ : ↥W), (H ⟨e.1, memW e⟩).2) = ⟨e.1, memW e⟩ := by
      rw [← hx1, Prod.mk.eta, Homeomorph.symm_apply_apply]
    have hxmem : (⟨e.1, memW e⟩ : ↥(f ⁻¹' W)) ∈ (Subtype.val ⁻¹' U : Set ↥(f ⁻¹' W)) :=
      e.2.1
    have hind := sheet_independence hW (subset_refl W) H hAlc
      (⟨z', hz'⟩ : ↥W) (⟨z, hz⟩ : ↥W) ((H ⟨e.1, memW e⟩).2)
    exact hind.mp (by rw [hs]; exact hxmem)
  -- backward map
  have back : ∀ i : ↥{i : I |
        H.symm ((⟨z, hz⟩ : ↥W), i) ∈ (Subtype.val ⁻¹' U : Set ↥(f ⁻¹' W))},
      (H.symm ((⟨z', hz'⟩ : ↥W), i.1)).1 ∈ U ∩ f ⁻¹' {z'} := by
    intro i
    have hyA : H.symm ((⟨z', hz'⟩ : ↥W), i.1) ∈
        (Subtype.val ⁻¹' U : Set ↥(f ⁻¹' W)) := by
      have hind := sheet_independence hW (subset_refl W) H hAlc
        (⟨z, hz⟩ : ↥W) (⟨z', hz'⟩ : ↥W) i.1
      exact hind.mp i.2
    have hyf : f (H.symm ((⟨z', hz'⟩ : ↥W), i.1)).1 = z' := by
      have h1 := hH (H.symm ((⟨z', hz'⟩ : ↥W), i.1))
      rw [Homeomorph.apply_symm_apply] at h1
      exact h1.symm
    exact ⟨hyA, by rw [Set.mem_preimage, Set.mem_singleton_iff]; exact hyf⟩
  refine
    { toFun := fun e => ⟨(H ⟨e.1, memW e⟩).2, key e⟩
      invFun := fun i => ⟨(H.symm ((⟨z', hz'⟩ : ↥W), i.1)).1, back i⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro e
    simp only []
    apply Subtype.ext
    simp only []
    have hx1 : (H ⟨e.1, memW e⟩).1 = (⟨z', hz'⟩ : ↥W) :=
      Subtype.ext (by rw [hH, hval e])
    have hs : H.symm ((⟨z', hz'⟩ : ↥W), (H ⟨e.1, memW e⟩).2) = ⟨e.1, memW e⟩ := by
      rw [← hx1, Prod.mk.eta, Homeomorph.symm_apply_apply]
    rw [hs]
  · intro i
    simp only []
    apply Subtype.ext
    simp only []
    have hstep : (⟨(H.symm ((⟨z', hz'⟩ : ↥W), i.1)).1,
        memW ⟨(H.symm ((⟨z', hz'⟩ : ↥W), i.1)).1, back i⟩⟩ : ↥(f ⁻¹' W)) =
        H.symm ((⟨z', hz'⟩ : ↥W), i.1) := Subtype.ext rfl
    rw [hstep, Homeomorph.apply_symm_apply]

end Work.ELAssembly
