import Mathlib
import Submission.Work.WilE9G.Sard.goodFDerivSurjective

namespace Work.WilE7.DimAPI

/-- For an ambient `Good` stratum `S` (`p = 0`), the Fréchet differential at `z ∈ S.X.set` of the
tuple `w ↦ (a ↦ eaEval S.X.c (S.h a) w)` is surjective (`goodFDerivSurjective`), so its kernel has
dimension `#coordinates − #equations = N − S.j` by rank–nullity. -/
theorem finrank_ker_fderiv_eqMap {N : ℕ} (S : WilkiesDesign.E.Stratum 0 N) (hS : S.Good)
    {z : Fin (0 + N) → ℝ} (hz : z ∈ S.X.set) :
    Module.finrank ℝ (LinearMap.ker ((fderiv ℝ (fun w : Fin (0 + N) → ℝ => fun a : Fin S.j =>
      WilkiesDesign.E.eaEval S.X.c (S.h a) w) z).toLinearMap)) = N - S.j := by
  -- The differential of the tuple of `eaEval`s is surjective at a point of a `Good` stratum.
  have hsurj := Work.WilE9G.Sard.goodFDerivSurjective S hS hz
  have hsurj' : Function.Surjective
      ((fderiv ℝ (fun w : Fin (0 + N) → ℝ => fun a : Fin S.j =>
        WilkiesDesign.E.eaEval S.X.c (S.h a) w) z).toLinearMap) := by
    intro y
    obtain ⟨x, hx⟩ := hsurj y
    exact ⟨x, hx⟩
  -- hence its range is everything.
  have hrange : LinearMap.range
      ((fderiv ℝ (fun w : Fin (0 + N) → ℝ => fun a : Fin S.j =>
        WilkiesDesign.E.eaEval S.X.c (S.h a) w) z).toLinearMap) = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj'
  -- rank–nullity.
  have hrn := LinearMap.finrank_range_add_finrank_ker
    ((fderiv ℝ (fun w : Fin (0 + N) → ℝ => fun a : Fin S.j =>
        WilkiesDesign.E.eaEval S.X.c (S.h a) w) z).toLinearMap)
  rw [hrange] at hrn
  have htop : Module.finrank ℝ (⊤ : Submodule ℝ (Fin S.j → ℝ)) = S.j := by simp
  have hdom : Module.finrank ℝ (Fin (0 + N) → ℝ) = N := by simp
  rw [htop, hdom] at hrn
  omega

end Work.WilE7.DimAPI
