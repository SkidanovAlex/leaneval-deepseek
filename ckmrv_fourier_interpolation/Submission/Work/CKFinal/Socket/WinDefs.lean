/-
# The window charts `W1` of the socket construction

The window chart of `Work.CKFinal.windowChart_data` at height `s` is packaged here as
`Socket.chartFun ℓ d hd s hs`, with radius shrunk to `Socket.winRad s hs = min ε_s (min s s⁻¹/16)`
so that the ball satisfies the thinness and containment conditions `Socket.winBall_geometry`.
`Socket.W1` is the union of the (open) window balls.
-/
import Mathlib
import Submission.Work.CKFinal.U0Defs
import Submission.Work.CKFinal.windowChart_data
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.CKFinal.Socket.Basic
import Submission.Work.CKFinal.Socket.winBall_geometry

noncomputable section

open UpperHalfPlane
open scoped Topology Manifold

namespace Work.CKFinal
namespace Socket

/-- The layer as a function of `τ` alone. -/
def layerFn (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (r : ℝ) : ℍ → ℂ :=
  fun τ => Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r

/-- The shrunk window radius factor `min s s⁻¹ / 16`. -/
def winR (s : ℝ) : ℝ := min s s⁻¹ / 16

/-- The radius of the window chart at height `s`, as produced by `windowChart_data`. -/
noncomputable def chartEps (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (s : ℝ) (hs : 0 < s) : ℝ :=
  Classical.choose (windowChart_data ℓ d hd s hs)

/-- The window chart at height `s`, as produced by `windowChart_data`. -/
noncomputable def chartFun (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (s : ℝ) (hs : 0 < s) : ℝ → ℍ → ℂ :=
  Classical.choose (Classical.choose_spec (windowChart_data ℓ d hd s hs))

lemma chartEps_pos (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (s : ℝ) (hs : 0 < s) : 0 < chartEps ℓ d hd s hs :=
  (Classical.choose_spec (Classical.choose_spec (windowChart_data ℓ d hd s hs))).1

lemma chartFun_mdiff (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (s : ℝ) (hs : 0 < s) (r : ℝ) :
    MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (chartFun ℓ d hd s hs r) (Metric.ball (Work.Asymptotics.onePlusI s hs) (chartEps ℓ d hd s hs)) :=
  (Classical.choose_spec (Classical.choose_spec (windowChart_data ℓ d hd s hs))).2.1 r

lemma chartFun_Dside (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (s : ℝ) (hs : 0 < s) (r : ℝ) {τ : ℍ}
    (h : dist τ (Work.Asymptotics.onePlusI s hs) < chartEps ℓ d hd s hs)
    (hd' : τ ∈ Work.Asymptotics.DomainD) :
    chartFun ℓ d hd s hs r τ = layerFn ℓ d r τ :=
  (Classical.choose_spec (Classical.choose_spec (windowChart_data ℓ d hd s hs))).2.2.1 r τ h hd'

lemma chartFun_far (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (s : ℝ) (hs : 0 < s) (r : ℝ) {τ : ℍ}
    (h : dist τ (Work.Asymptotics.onePlusI s hs) < chartEps ℓ d hd s hs) (hr : 1 < τ.re) :
    chartFun ℓ d hd s hs r τ
      = layerFn ℓ d r τ + Work.Asymptotics.sinSqC r * Work.Asymptotics.resCorr r τ :=
  (Classical.choose_spec (Classical.choose_spec (windowChart_data ℓ d hd s hs))).2.2.2.1 r τ h hr

lemma chartFun_even (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (s : ℝ) (hs : 0 < s) (r : ℝ) (τ : ℍ) :
    chartFun ℓ d hd s hs (-r) τ = chartFun ℓ d hd s hs r τ :=
  (Classical.choose_spec (Classical.choose_spec (windowChart_data ℓ d hd s hs))).2.2.2.2 r τ

/-- The shrunk radius used for the socket. -/
noncomputable def winRad (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (s : ℝ) (hs : 0 < s) : ℝ := min (chartEps ℓ d hd s hs) (winR s)

/-- The window ball at height `s`. -/
noncomputable def winBall (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (s : ℝ) (hs : 0 < s) : Set ℍ :=
  Metric.ball (Work.Asymptotics.onePlusI s hs) (winRad ℓ d hd s hs)

/-- `W1`, the union of the window balls. -/
noncomputable def W1 (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) : Set ℍ :=
  ⋃ (s : ℝ) (hs : 0 < s), winBall ℓ d hd s hs

lemma isOpen_winBall (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (s : ℝ) (hs : 0 < s) : IsOpen (winBall ℓ d hd s hs) := Metric.isOpen_ball

lemma winBall_subset_eps (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (s : ℝ) (hs : 0 < s) :
    winBall ℓ d hd s hs ⊆ Metric.ball (Work.Asymptotics.onePlusI s hs) (chartEps ℓ d hd s hs) :=
  Metric.ball_subset_ball (min_le_left _ _)

lemma winBall_subset_geo (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (s : ℝ) (hs : 0 < s) :
    winBall ℓ d hd s hs ⊆ Metric.ball (Work.Asymptotics.onePlusI s hs) (min s s⁻¹ / 16) :=
  Metric.ball_subset_ball (min_le_right _ _)

lemma winBall_mem_re (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {s : ℝ} {hs : 0 < s} {τ : ℍ} (h : τ ∈ winBall ℓ d hd s hs) :
    |τ.re - 1| < thin τ.im :=
  (winBall_geometry s hs).1 τ (winBall_subset_geo ℓ d hd s hs h)

lemma winBall_mem_DomainD (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {s : ℝ} {hs : 0 < s} {τ : ℍ} (h : τ ∈ winBall ℓ d hd s hs) (hre : τ.re < 1) :
    τ ∈ Work.Asymptotics.DomainD :=
  (winBall_geometry s hs).2 τ (winBall_subset_geo ℓ d hd s hs h) hre

/-- A point of `W1` need not be in any prescribed ball, but every point of `W1` lies in some. -/
lemma mem_W1 {ℓ : Work.Kernels.LogLambdaData} {d : ℕ} {hd : d = 8 ∨ d = 24} {τ : ℍ} :
    τ ∈ W1 ℓ d hd ↔ ∃ (s : ℝ) (hs : 0 < s), τ ∈ winBall ℓ d hd s hs := by
  simp [W1]

end Socket
end Work.CKFinal
