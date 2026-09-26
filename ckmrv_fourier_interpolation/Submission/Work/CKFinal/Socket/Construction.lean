/-
# The socket `F₂`, `O` for `Work.CKFinal.exists_F2_socket`

`O = U0 ∪ W1 ∪ Wm1` (`Socket.O`) and `F₂` (`Socket.F2`) is the glued function `G` on `U0 ∪ W1`
and, on `Wm1`, the value forced by the first recurrence `(T-I)²F₂ = -T2op gauss`.

The well-definedness of `G` (that is, that the window charts agree on the intersection of two
balls) is `Socket.chartFun_agree`; `Socket.exists_chartVal` turns it into the chart value
`Socket.chartVal`.
-/
import Mathlib
import Submission.Work.CKFinal.Socket.WinDefs
import Submission.Work.CKFinal.Socket.Region
import Submission.Work.CKFinal.Socket.chartFun_agree
import Submission.Work.LayerCont.Glue.All
import Submission.Work.Asymptotics.PropagateDefs

noncomputable section

open UpperHalfPlane
open scoped Topology Manifold

namespace Work.CKFinal
namespace Socket

/-- The value of the window chart at `τ ∈ W1`, well defined by `Socket.chartFun_agree`. -/
theorem exists_chartVal (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (r : ℝ) {τ : ℍ} (h : τ ∈ W1 ℓ d hd) :
    ∃ c : ℂ, ∀ (s : ℝ) (hs : 0 < s), τ ∈ winBall ℓ d hd s hs →
      chartFun ℓ d hd s hs r τ = c := by
  obtain ⟨s₀, hs₀, h₀⟩ := mem_W1.mp h
  exact ⟨chartFun ℓ d hd s₀ hs₀ r τ, fun s hs hh => chartFun_agree ℓ d hd r hh h₀⟩

/-- The window-chart value at a point of `W1`. -/
noncomputable def chartVal (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (r : ℝ) (τ : ℍ) (h : τ ∈ W1 ℓ d hd) : ℂ :=
  Classical.choose (exists_chartVal ℓ d hd r h)

lemma chartVal_spec (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (r : ℝ) {τ : ℍ} (h : τ ∈ W1 ℓ d hd) (s : ℝ) (hs : 0 < s)
    (hh : τ ∈ winBall ℓ d hd s hs) :
    chartFun ℓ d hd s hs r τ = chartVal ℓ d hd r τ h :=
  Classical.choose_spec (exists_chartVal ℓ d hd r h) s hs hh

/-- The glued function on `U0 ∪ W1`. -/
noncomputable def G (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (r : ℝ) (τ : ℍ) : ℂ := by
  classical
  exact if h : τ ∈ U0 then layerFn ℓ d r τ
    else if h : τ ∈ W1 ℓ d hd then chartVal ℓ d hd r τ h
    else layerFn ℓ d r τ

/-- The layer `F₂` of the socket: the glued function on `U0 ∪ W1`, and on `Wm1` the value forced
by the first recurrence. -/
noncomputable def F2 (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (r : ℝ) (τ : ℍ) : ℂ := by
  classical
  exact if h : τ ∈ Wm1 ℓ d hd then
    2 * G ℓ d hd r ((1 : ℝ) +ᵥ τ) - G ℓ d hd r ((2 : ℝ) +ᵥ τ)
      - Work.Kernels.T2op (fun σ : ℍ => Work.Kernels.gaussTerm σ r) τ
  else G ℓ d hd r τ

lemma G_of_mem_U0 (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (r : ℝ) {τ : ℍ} (h : τ ∈ U0) : G ℓ d hd r τ = layerFn ℓ d r τ := by
  classical
  rw [G, dif_pos h]

lemma chartVal_eq_layerFn_of_mem_U0 (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (r : ℝ) {τ : ℍ} (h : τ ∈ W1 ℓ d hd) (h0 : τ ∈ U0) :
    chartVal ℓ d hd r τ h = layerFn ℓ d r τ := by
  obtain ⟨s, hs, hb⟩ := mem_W1.mp h
  rw [← chartVal_spec ℓ d hd r h s hs hb]
  exact chartFun_Dside ℓ d hd s hs r (winBall_subset_eps ℓ d hd s hs hb)
    (winBall_mem_DomainD ℓ d hd hb (Work.CKFinal.mem_U0_iff.mp h0).2.1)

lemma G_of_mem_W1 (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (r : ℝ) {τ : ℍ} (h : τ ∈ W1 ℓ d hd) : G ℓ d hd r τ = chartVal ℓ d hd r τ h := by
  classical
  by_cases h0 : τ ∈ U0
  · rw [G_of_mem_U0 ℓ d hd r h0, chartVal_eq_layerFn_of_mem_U0 ℓ d hd r h h0]
  · rw [G, dif_neg h0, dif_pos h]

/-- `G` agrees with the chart on every window ball. -/
lemma G_of_mem_winBall (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (r : ℝ) {s : ℝ} {hs : 0 < s} {τ : ℍ} (h : τ ∈ winBall ℓ d hd s hs) :
    G ℓ d hd r τ = chartFun ℓ d hd s hs r τ := by
  rw [G_of_mem_W1 ℓ d hd r (mem_W1.mpr ⟨s, hs, h⟩)]
  exact (chartVal_spec ℓ d hd r _ s hs h).symm

lemma F2_of_not_mem_Wm1 (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (r : ℝ) {τ : ℍ} (h : τ ∉ Wm1 ℓ d hd) : F2 ℓ d hd r τ = G ℓ d hd r τ := by
  classical
  rw [F2, dif_neg h]

lemma F2_of_mem_Wm1 (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (r : ℝ) {τ : ℍ} (h : τ ∈ Wm1 ℓ d hd) :
    F2 ℓ d hd r τ = 2 * G ℓ d hd r ((1 : ℝ) +ᵥ τ) - G ℓ d hd r ((2 : ℝ) +ᵥ τ)
      - Work.Kernels.T2op (fun σ : ℍ => Work.Kernels.gaussTerm σ r) τ := by
  classical
  rw [F2, dif_pos h]

/-- `G` is holomorphic on `U0 ∪ W1` as soon as the layer is holomorphic on `U0`. -/
lemma G_mdiff (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (r : ℝ)
    (hU0 : MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (layerFn ℓ d r) U0) :
    MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (G ℓ d hd r) (U0 ∪ W1 ℓ d hd) := by
  intro τ hτ
  rcases hτ with h0 | h1
  · -- near a point of `U0`, `G = layerFn`
    have hcongr : G ℓ d hd r =ᶠ[𝓝 τ] layerFn ℓ d r := by
      filter_upwards [isOpen_U0.mem_nhds h0] with y hy
      exact G_of_mem_U0 ℓ d hd r hy
    exact (hcongr.mdifferentiableAt_iff.mpr
      ((hU0 τ h0).mdifferentiableAt (isOpen_U0.mem_nhds h0))).mdifferentiableWithinAt
  · -- near a point of `W1`, `G = chartFun`
    obtain ⟨s, hs, hb⟩ := mem_W1.mp h1
    have hcongr : G ℓ d hd r =ᶠ[𝓝 τ] chartFun ℓ d hd s hs r := by
      filter_upwards [isOpen_winBall ℓ d hd s hs |>.mem_nhds hb] with y hy
      exact G_of_mem_winBall ℓ d hd r hy
    have hmem : Metric.ball (Work.Asymptotics.onePlusI s hs) (chartEps ℓ d hd s hs) ∈ 𝓝 τ :=
      Metric.isOpen_ball.mem_nhds (winBall_subset_eps ℓ d hd s hs hb)
    exact (hcongr.mdifferentiableAt_iff.mpr
      ((chartFun_mdiff ℓ d hd s hs r τ (winBall_subset_eps ℓ d hd s hs hb)).mdifferentiableAt
        hmem)).mdifferentiableWithinAt

end Socket
end Work.CKFinal
