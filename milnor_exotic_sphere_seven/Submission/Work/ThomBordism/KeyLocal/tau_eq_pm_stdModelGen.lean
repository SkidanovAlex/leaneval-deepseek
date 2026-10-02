import Mathlib
import Submission.Work.ThomBordism.KeyLocal.tubeSets
import Submission.Work.ThomBordism.FrameSigns.Defs
import Submission.Work.ThomBordism.stdModelGen_pm_stdThomGen
import Submission.Work.Thom.relCohomology_euclidean_punctured

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory

namespace Work.ThomBordism.KeyLocal

noncomputable section

/-!
# The frame-signature model class `FrameSigns.tau` is `± stdModelGen 8`

`Work.ThomBordism.FrameSigns.tau` is the element of the model relative cohomology
`H⁸(ℝ⁸, ℝ⁸∖0;ℤ)` that pairs to `1` with the fixed generator `sigma0` of the model *homology*,
`Work.ThomBordism.stdModelGen 8` is the determinate generator of the same group obtained by pulling
`Work.Thom.Mpun 8 PUnit` back along `ℝ⁸ ≅ PUnit × ℝ⁸`.

Both are generators of a `ℤ`-module isomorphic to `ℤ` (`H⁸(ℝ⁸, ℝ⁸∖0;ℤ) ≅ ℤ`,
`Work.Thom.relCohomology_euclidean_punctured`), hence differ by a *sign*.  The file proves this in
two steps: an elementary lemma that two generators of a `ℤ`-module isomorphic to `ℤ` differ by a
sign, and the proof that `tau` generates (it is the image of the surjective functional `dual0` under
the isomorphism `kronIso`), the generation of `stdModelGen 8` being already available
(`Work.ThomBordism.stdModelGen_span`).
-/

/-- **Two generators of a `ℤ`-module isomorphic to `ℤ` differ by a sign.**  If `e : M ≃ₗ[ℤ] ℤ` is an
isomorphism, `a` and `b` both generate `M` and `e b = ±1`, then `a = ± b`. -/
theorem exists_pm_smul_of_span_eq_top {M : Type*} [AddCommGroup M] [Module ℤ M]
    (h : Nonempty (M ≃ₗ[ℤ] ℤ)) {a b : M} (ha : Submodule.span ℤ ({a} : Set M) = ⊤)
    (hb : Submodule.span ℤ ({b} : Set M) = ⊤) :
    ∃ t : ℤ, (t = 1 ∨ t = -1) ∧ a = t • b := by
  obtain ⟨e⟩ := h
  -- a generator of `M` is mapped to `±1`
  have key : ∀ {x : M}, Submodule.span ℤ ({x} : Set M) = ⊤ → e x = 1 ∨ e x = -1 := by
    intro x hx
    have hspan : Submodule.span ℤ ({(e x)} : Set ℤ) = ⊤ := by
      have hmap : Submodule.map (e : M →ₗ[ℤ] ℤ) (Submodule.span ℤ ({x} : Set M))
          = Submodule.span ℤ ({(e x)} : Set ℤ) := by
        rw [Submodule.map_span, Set.image_singleton]
        ext w
        simp
      rw [← hmap, hx, Submodule.map_top]
      exact LinearMap.range_eq_top.mpr e.surjective
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp
      (show (1 : ℤ) ∈ Submodule.span ℤ ({(e x)} : Set ℤ) by
        rw [hspan]; exact Submodule.mem_top)
    have hu : IsUnit (e x) := by
      refine isUnit_iff_exists_inv.mpr ⟨k, ?_⟩
      rw [mul_comm]
      rw [zsmul_eq_mul] at hk
      simpa using hk
    rwa [Int.isUnit_iff] at hu
  rcases key ha with ha1 | ha1 <;> rcases key hb with hb1 | hb1
  · exact ⟨1, Or.inl rfl, by rw [one_smul]; exact e.injective (by rw [ha1, hb1])⟩
  · refine ⟨-1, Or.inr rfl, ?_⟩
    have h2 : a = -b := by
      refine e.injective ?_
      rw [map_neg]
      linarith
    rw [show (-1 : ℤ) • b = -b by simp]
    exact h2
  · refine ⟨-1, Or.inr rfl, ?_⟩
    have h2 : a = -b := by
      refine e.injective ?_
      rw [map_neg]
      linarith
    rw [show (-1 : ℤ) • b = -b by simp]
    exact h2
  · exact ⟨1, Or.inl rfl, by rw [one_smul]; exact e.injective (by rw [ha1, hb1])⟩

/-- **`FrameSigns.tau` generates the model relative cohomology.**  `tau` is
`kronIso.symm dual0` (`Work.ThomBordism.FrameSigns.tau`), `kronIso` is the relative Kronecker
pairing isomorphism `H⁸ ≅ Hom(H₈, ℤ)` and `dual0 = (e8.hom).hom` is a surjective functional; the
element `sigma0 = (e8.inv).hom 1` generates the model homology (`z = dual0 z • sigma0`), so every
functional is a multiple of `dual0`. -/
theorem tau_span_eq_top :
    Submodule.span ℤ ({Work.ThomBordism.FrameSigns.tau} :
      Set ↑Work.ThomBordism.FrameSigns.modelCoh) = ⊤ := by
  -- `sigma0` generates the model homology: `z = dual0 z • sigma0`
  have hz : ∀ z : ↥(Work.ThomBordism.FrameSigns.modelC.homology 8),
      z = Work.ThomBordism.FrameSigns.dual0 z • Work.ThomBordism.FrameSigns.sigma0 := by
    intro z
    have h1 : (Work.ThomBordism.FrameSigns.e8.inv).hom
        (Work.ThomBordism.FrameSigns.dual0 z) = z := by
      have hh : (Work.ThomBordism.FrameSigns.e8.hom ≫ Work.ThomBordism.FrameSigns.e8.inv).hom
          = LinearMap.id := by
        rw [Iso.hom_inv_id Work.ThomBordism.FrameSigns.e8, ModuleCat.hom_id]
      have h2 := congrArg (fun f : ↥(Work.ThomBordism.FrameSigns.modelC.homology 8) →ₗ[ℤ]
          ↥(Work.ThomBordism.FrameSigns.modelC.homology 8) => f z) hh
      rw [ModuleCat.hom_comp] at h2
      simpa [Work.ThomBordism.FrameSigns.dual0] using h2
    have h2 : (Work.ThomBordism.FrameSigns.e8.inv).hom
        (Work.ThomBordism.FrameSigns.dual0 z)
        = Work.ThomBordism.FrameSigns.dual0 z • Work.ThomBordism.FrameSigns.sigma0 := by
      have h3 := map_zsmul (f := (Work.ThomBordism.FrameSigns.e8.inv).hom)
        (Work.ThomBordism.FrameSigns.dual0 z) (1 : ℤ)
      simpa [Work.ThomBordism.FrameSigns.sigma0, zsmul_eq_mul, Int.cast_id] using h3
    rw [← h2, h1]
  -- every functional on the model homology is a multiple of `dual0`
  refine Submodule.eq_top_iff'.mpr fun y => ?_
  rw [Submodule.mem_span_singleton]
  set m : ℤ := Work.ThomBordism.FrameSigns.kronIso y Work.ThomBordism.FrameSigns.sigma0 with hm
  have hkey : ∀ z : ↥(Work.ThomBordism.FrameSigns.modelC.homology 8),
      Work.ThomBordism.FrameSigns.kronIso y z = m * Work.ThomBordism.FrameSigns.dual0 z := by
    intro z
    rw [hm]
    calc Work.ThomBordism.FrameSigns.kronIso y z
        = Work.ThomBordism.FrameSigns.kronIso y
            (Work.ThomBordism.FrameSigns.dual0 z • Work.ThomBordism.FrameSigns.sigma0) := by
          rw [← hz z]
      _ = Work.ThomBordism.FrameSigns.dual0 z
            • Work.ThomBordism.FrameSigns.kronIso y Work.ThomBordism.FrameSigns.sigma0 :=
          map_zsmul _ _ _
      _ = Work.ThomBordism.FrameSigns.kronIso y Work.ThomBordism.FrameSigns.sigma0
            * Work.ThomBordism.FrameSigns.dual0 z := by
          rw [zsmul_eq_mul, Int.cast_id, mul_comm]
  have hlm : Work.ThomBordism.FrameSigns.kronIso y
      = m • Work.ThomBordism.FrameSigns.dual0 := by
    ext z
    rw [hkey z, LinearMap.smul_apply, zsmul_eq_mul, Int.cast_id]
  refine ⟨m, ?_⟩
  apply Work.ThomBordism.FrameSigns.kronIso.injective
  have htau : Work.ThomBordism.FrameSigns.kronIso Work.ThomBordism.FrameSigns.tau
      = Work.ThomBordism.FrameSigns.dual0 := by
    dsimp only [Work.ThomBordism.FrameSigns.tau]
    exact Work.ThomBordism.FrameSigns.kronIso.apply_symm_apply Work.ThomBordism.FrameSigns.dual0
  rw [LinearEquiv.map_smul, htau, hlm]

theorem tau_eq_pm_stdModelGen : ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
    Work.ThomBordism.FrameSigns.tau = s • Work.ThomBordism.stdModelGen 8 := by
  classical
  -- the model relative cohomology in degree `8` is `ℤ`
  obtain ⟨e⟩ := Work.Thom.relCohomology_euclidean_punctured 8 (by norm_num) 8
  rw [if_pos rfl] at e
  let E : ↑Work.ThomBordism.FrameSigns.modelCoh ≃ₗ[ℤ] ℤ :=
    e.toLinearEquiv.trans (LinearEquiv.funUnique (Fin 1) ℤ ℤ)
  exact exists_pm_smul_of_span_eq_top ⟨E⟩ tau_span_eq_top
    (Work.ThomBordism.stdModelGen_span 8 (by norm_num))

end

end Work.ThomBordism.KeyLocal
