import Mathlib

namespace Work.WilE2

theorem contDiff_fderiv_component {m : ℕ} (V : (Fin (m + 1) → ℝ) → (Fin m → ℝ)) (hV : ContDiff ℝ 2 V)
    (a : Fin m) (r : Fin (m + 1)) :
    ContDiff ℝ 1 (fun z : Fin (m + 1) → ℝ => fderiv ℝ (fun w => V w a) z (Pi.single r (1 : ℝ))) := by
  -- `V` is `C^2`, hence so is its component `w ↦ V w a`.
  have hf : ContDiff ℝ 2 (fun w : Fin (m + 1) → ℝ => V w a) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) a).contDiff.comp hV
  -- The bundled derivative of a `C^2` function is `C^1`.
  have h1 : ContDiff ℝ 1 (fderiv ℝ (fun w : Fin (m + 1) → ℝ => V w a)) :=
    hf.fderiv_right (by norm_num)
  -- Evaluation of a continuous linear map at a fixed vector is itself linear and continuous.
  have h2 : ContDiff ℝ 1 (fun w : Fin (m + 1) → ℝ =>
      fderiv ℝ (fun z => V z a) w (Pi.single r (1 : ℝ))) :=
    (ContinuousLinearMap.apply ℝ ℝ (Pi.single r (1 : ℝ) : Fin (m + 1) → ℝ)).contDiff.comp h1
  exact h2

end Work.WilE2
