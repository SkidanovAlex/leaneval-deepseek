import Mathlib
import Submission.Work.Beltrami.Defs

namespace Work.Beltrami

open LeanEval.Geometry.NewlanderNirenberg

/-- A non-zero real-linear map `E 1 = ℝ² → ℂ` that is complex linear with respect to a complex
structure `J` on `ℝ²` (i.e. `L (J v) = I * L v`) is bijective: its kernel is `J`-invariant, hence
is either `0` or all of `E 1`, and `L ≠ 0` rules out the latter. -/
theorem bijective_of_ne_zero {J : E 1 →L[ℝ] E 1} (hJ : ∀ v, J (J v) = -v)
    {L : E 1 →L[ℝ] ℂ} (hL : ∀ v, L (J v) = Complex.I * L v) (h0 : L ≠ 0) :
    Function.Bijective L := by
  -- Surjectivity: `L ≠ 0` gives a vector `v` with `L v ≠ 0`; the range of `L` is closed
  -- under multiplication by `I` (because `L (J v) = I * L v`), hence is a non-zero
  -- complex subspace of `ℂ`, i.e. all of `ℂ`.
  have hsurj : Function.Surjective L := by
    have hne : ∃ v : E 1, L v ≠ 0 := by
      by_contra h
      push Not at h
      exact h0 (by ext v; simp [h v])
    obtain ⟨v, hv⟩ := hne
    intro z
    refine ⟨((z / L v).re) • v + ((z / L v).im) • J v, ?_⟩
    have hz : (↑(z / L v).re : ℂ) + (↑(z / L v).im : ℂ) * Complex.I = z / L v :=
      Complex.re_add_im (z / L v)
    have hmul : ((↑(z / L v).re : ℂ) + (↑(z / L v).im : ℂ) * Complex.I) * (L v) = z := by
      rw [hz, div_mul_cancel₀ z hv]
    rw [map_add, map_smul, map_smul, hL v]
    rw [Complex.real_smul, Complex.real_smul]
    linear_combination hmul
  -- Injectivity: `E 1 = ℝ²` and `ℂ` both have real dimension `2`, so a surjective
  -- real-linear map between them is injective.
  have hfin : Module.finrank ℝ (E 1) = Module.finrank ℝ ℂ := by
    simp [Complex.finrank_real_complex]
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mpr hsurj, hsurj⟩

end Work.Beltrami
