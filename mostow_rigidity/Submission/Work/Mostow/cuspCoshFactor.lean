import Mathlib
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.levYcFormula
import Submission.Work.Mostow.hptOfLevelYc
import Submission.Work.Mostow.cuspMap

namespace Work.Mostow

open Submission.Mostow

/-- **The cosh of the distance between two horospherical points produced by the cusp map.**

For `ξ,η ∈ Sph n`, a scaling `lam > 0` and a map `ψ` carrying `ξ^⊥` into `η^⊥`, the two points
`hptOf η (ψ (yc ξ u)) (lam * lev ξ u)` and `hptOf η (ψ (yc ξ v)) (lam * lev ξ v)` of the horosphere
of `η` satisfy

`cosh (hdist P_u P_v) = cosh (log (lev ξ u / lev ξ v)) + (lam lev ξ u)(lam lev ξ v)/2 · ‖ψ(yc ξ u) − ψ(yc ξ v)‖²`.

This is the horospherical distance formula `levYcFormula` at `η`, combined with the fact that
`hptOf η y D` has level `D` and flat coordinate `y` when `y ⊥ η`, and that `ψ` maps `yc ξ · ⊥ ξ`
into `η^⊥` so that `ψ (yc ξ ·)` is an admissible flat coordinate at `η`. -/
theorem cuspCoshFactor {n : ℕ} {ξ η : Submission.Mostow.E n}
    (hξ : ξ ∈ Submission.Mostow.Sph n) (hη : η ∈ Submission.Mostow.Sph n)
    {lam : ℝ} (hlam : 0 < lam)
    {ψ : Submission.Mostow.E n → Submission.Mostow.E n}
    (hψperp : ∀ x : Submission.Mostow.E n, inner ℝ x ξ = 0 → inner ℝ (ψ x) η = 0)
    (u v : Submission.Mostow.E n) :
    Real.cosh (Submission.Mostow.hdist
        (Work.Mostow.hptOf η (ψ (Work.Mostow.yc ξ u)) (lam * Work.Mostow.lev ξ u))
        (Work.Mostow.hptOf η (ψ (Work.Mostow.yc ξ v)) (lam * Work.Mostow.lev ξ v)))
      = Real.cosh (Real.log (Work.Mostow.lev ξ u / Work.Mostow.lev ξ v))
        + (lam * Work.Mostow.lev ξ u) * (lam * Work.Mostow.lev ξ v) / 2
            * ‖ψ (Work.Mostow.yc ξ u) - ψ (Work.Mostow.yc ξ v)‖ ^ 2 := by
  -- the flat coordinates `yc ξ ·` lie in `ξ^⊥`, so `ψ` carries them into `η^⊥`
  have hyu : inner ℝ (yc ξ u) ξ = 0 := yc_orth hξ
  have hyv : inner ℝ (yc ξ v) ξ = 0 := yc_orth hξ
  -- the levels `lam * lev ξ ·` are positive
  have hDu : 0 < lam * lev ξ u := mul_pos hlam (lev_pos ξ hξ u)
  have hDv : 0 < lam * lev ξ v := mul_pos hlam (lev_pos ξ hξ v)
  have hηu : inner ℝ (ψ (yc ξ u)) η = 0 := hψperp _ hyu
  have hηv : inner ℝ (ψ (yc ξ v)) η = 0 := hψperp _ hyv
  -- the horospherical distance formula at `η`
  have h1 := levYcFormula hη (hptOf η (ψ (yc ξ u)) (lam * lev ξ u))
      (hptOf η (ψ (yc ξ v)) (lam * lev ξ v))
  rw [(hptOfLevelYc η hη hηu hDu).1, (hptOfLevelYc η hη hηu hDu).2.1,
      (hptOfLevelYc η hη hηv hDv).1, (hptOfLevelYc η hη hηv hDv).2.1] at h1
  rw [h1]
  -- `log ((lam L_u)/(lam L_v)) = log (L_u/L_v)`
  have hlog : Real.log ((lam * lev ξ u) / (lam * lev ξ v)) = Real.log (lev ξ u / lev ξ v) := by
    congr 1
    field_simp
  rw [hlog]

end Work.Mostow
