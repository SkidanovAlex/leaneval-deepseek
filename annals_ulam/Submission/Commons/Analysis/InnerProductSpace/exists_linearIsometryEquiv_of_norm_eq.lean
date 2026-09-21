import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.Analysis.InnerProductSpace

open Module

/-- Given a finite-dimensional real inner product space `E`, a finite type `ι` with
`Fintype.card ι = finrank ℝ E`, and a unit vector `u`, there is an orthonormal basis of `E` whose
`i₀`-th element is `u`. -/
lemma exists_orthonormalBasis_apply_eq_of_norm_eq_one {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]
    (hcard : finrank ℝ E = Fintype.card ι) (i₀ : ι) {u : E} (hu : ‖u‖ = 1) :
    ∃ b : OrthonormalBasis ι ℝ E, b i₀ = u := by
  have horth : Orthonormal ℝ (({i₀} : Set ι).domRestrict (fun _ : ι => u)) := by
    rw [orthonormal_subsingleton_iff]
    intro i
    simpa using hu
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard horth
  exact ⟨b, hb i₀ (Set.mem_singleton i₀)⟩

theorem exists_linearIsometryEquiv_of_norm_eq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {x y : E} (h : ‖x‖ = ‖y‖) :
    ∃ S : E ≃ₗᵢ[ℝ] E, S x = y := by
  rcases eq_or_ne x 0 with hx | hx
  · subst hx
    have hy : y = 0 := by
      have : ‖y‖ = 0 := by rw [← h, norm_zero]
      exact norm_eq_zero.mp this
    subst hy
    exact ⟨LinearIsometryEquiv.refl ℝ E, rfl⟩
  · have hy : y ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at h
      exact hx (norm_eq_zero.mp h)
    have hnt : Nontrivial E := ⟨x, 0, hx⟩
    have _hnz : NeZero (finrank ℝ E) :=
      ⟨ne_of_gt (Module.finrank_pos (R := ℝ) (M := E))⟩
    let u : E := (‖x‖⁻¹ : ℝ) • x
    let v : E := (‖y‖⁻¹ : ℝ) • y
    have hu : ‖u‖ = 1 := norm_smul_inv_norm hx
    have hv : ‖v‖ = 1 := norm_smul_inv_norm hy
    have hcard : finrank ℝ E = Fintype.card (Fin (finrank ℝ E)) :=
      (Fintype.card_fin (finrank ℝ E)).symm
    obtain ⟨b₁, hb₁⟩ :=
      exists_orthonormalBasis_apply_eq_of_norm_eq_one hcard (0 : Fin (finrank ℝ E)) hu
    obtain ⟨b₂, hb₂⟩ :=
      exists_orthonormalBasis_apply_eq_of_norm_eq_one hcard (0 : Fin (finrank ℝ E)) hv
    have hSu : (b₁.repr.trans b₂.repr.symm) u = v := by
      rw [LinearIsometryEquiv.trans_apply]
      rw [show b₁.repr u = EuclideanSpace.single (0 : Fin (finrank ℝ E)) 1 by
            rw [← hb₁]; exact b₁.repr_self 0]
      rw [b₂.repr_symm_single, hb₂]
    have hxu : ‖x‖ • u = x := by
      simp only [u, smul_smul]
      rw [mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]
    refine ⟨b₁.repr.trans b₂.repr.symm, ?_⟩
    calc (b₁.repr.trans b₂.repr.symm) x
        = (b₁.repr.trans b₂.repr.symm) (‖x‖ • u) := by rw [hxu]
      _ = ‖x‖ • (b₁.repr.trans b₂.repr.symm) u := by rw [map_smul]
      _ = ‖x‖ • v := by rw [hSu]
      _ = ‖x‖ • (‖y‖⁻¹ • y) := by simp only [v]
      _ = y := by
            rw [smul_smul, h, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hy), one_smul]

end Commons.Analysis.InnerProductSpace