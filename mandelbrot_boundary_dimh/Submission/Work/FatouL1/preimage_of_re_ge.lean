import Mathlib
import Submission.Work.FatouL1.orbitData
import Submission.Work.Fatou.Qreg.InjGeom

/-!
# A preimage to the right of the level line `Re = x₀` (Shishikura A.2.1(i))

For a near-translation `F` on Shishikura's region `𝒬 = Qreg b₁ b₂` (i.e.
`‖F w - (w + 1)‖ ≤ 1/32` on `𝒬`), every point `z ∈ 𝒬` which is at least `1 + 1/31` to the right of
the level line `Re = x₀` (with `x₀` strictly to the right of every vertex of `b₁`) has a preimage
`w ∈ 𝒬` of `Re w ≥ x₀`.

The mathematical content is one quantitative step of the inverse function theorem:

* **Geometry** (`closedBall_subset_Qreg`).  `z - 1` lies in `𝒬` with cone *slack*: the two cone
  inequalities have margins of at least `1` at `z`, because `Re z > Re a + 2` at every vertex `a`
  of `b₁`, while the margin of the `b₂`-inequality is inherited from `z ∈ 𝒬`.  Moving by at most
  `1/32` costs at most `2/32` of slack, so the whole closed ball `B̄(z - 1, 1/32)` lies in `𝒬`.
* **Contraction** (`exists_preimage_in_closedBall`).  On that ball the map
  `𝒯 w = z - F w + w` is a self-map (`‖𝒯 w - (z - 1)‖ = ‖F w - (w + 1)‖ ≤ 1/32`) and a
  `1/32`-contraction (`deriv 𝒯 = 1 - deriv F`, and `‖deriv F - 1‖ ≤ 1/32`), so Banach's fixed
  point theorem gives `w` with `𝒯 w = w`, i.e. `F w = z`.
* The real-part bound `x₀ ≤ Re w` is then immediate from `‖w - (z - 1)‖ ≤ 1/32 > 1/31`... i.e.
  from `Re w ≥ Re z - 1 - 1/32 ≥ x₀ + 1/31 - 1/32 ≥ x₀`.

The statement of `preimage_of_re_ge` is used to show that the fundamental strip of `F` (the set of
points of `𝒬` whose `F`-preimages in `𝒬` all have real part `< x₀`) is contained in the bounded
strip `Re < x₀ + 1 + 1/31`.
-/

set_option linter.unusedVariables false

namespace Work.FatouL1

/-- **Geometry of the preimage ball.**  If `Re z` is at least `1 + 1/31` to the right of the level
line `Re = x₀`, which itself is strictly to the right of every vertex of `b₁`, then the closed ball
of radius `1/32` about `z - 1` is contained in `𝒬 = Qreg b₁ b₂`.

Indeed the `b₁`-inequalities have slack `> 1` at `z` (`Re (z - a) > 2 + 1/31`), and the
`b₂`-inequalities are inherited from `z ∈ 𝒬`; a displacement of norm `≤ 1/32` changes each cone
margin by at most `2/32 < 1`. -/
theorem closedBall_subset_Qreg {b₁ b₂ : Option ℂ} {x₀ : ℝ}
    (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) {z : ℂ} (hz : z ∈ MandelDim.Qreg b₁ b₂)
    (hzx : x₀ + 1 + 1 / 31 ≤ z.re) :
    Metric.closedBall (z - 1) (1 / 32) ⊆ MandelDim.Qreg b₁ b₂ := by
  intro w hw
  rw [Metric.mem_closedBall, dist_eq_norm] at hw
  -- write `w = z - 1 + ε` with `‖ε‖ ≤ 1/32`
  set ε : ℂ := w - (z - 1) with hεdef
  have hε : ‖ε‖ ≤ 1 / 32 := by rw [hεdef]; exact hw
  have hreε : |ε.re| ≤ 1 / 32 := le_trans (Complex.abs_re_le_norm ε) hε
  have himε : |ε.im| ≤ 1 / 32 := le_trans (Complex.abs_im_le_norm ε) hε
  have hweq : w = z - 1 + ε := by rw [hεdef]; ring
  refine ⟨?_, ?_⟩
  · -- the `b₁`-inequalities: `Re (w - a) + |Im (w - a)| > 0`
    intro a ha
    have ha' : a.re + 1 < x₀ := h₁ a ha
    have hrea : (w - a).re = (z - a).re - 1 + ε.re := by rw [hweq]; simp; ring
    have hima : (w - a).im = (z - a).im + ε.im := by rw [hweq]; simp; ring
    have hzrea : (z - a).re ≥ x₀ + 1 + 1 / 31 - a.re := by
      have : (z - a).re = z.re - a.re := by simp
      linarith
    have h1' : (w - a).re ≥ (z - a).re - 1 - 1 / 32 := by
      rw [hrea]; linarith [(abs_le.mp hreε).1]
    have h2' : |(w - a).im| ≥ |(z - a).im| - 1 / 32 := by
      rw [hima]
      have hh := abs_sub_abs_le_abs_add ((z - a).im) ε.im
      linarith [(abs_le.mp himε).2, hh]
    have : 0 < (w - a).re + |(w - a).im| := by
      have := abs_nonneg ((z - a).im)
      linarith
    linarith
  · -- the `b₂`-inequalities: `|Im (w - b)| - Re (w - b) > 0`
    intro b hb
    have hb' : (z - b).re < |(z - b).im| := hz.2 b hb
    have hreb : (w - b).re = (z - b).re - 1 + ε.re := by rw [hweq]; simp; ring
    have himb : (w - b).im = (z - b).im + ε.im := by rw [hweq]; simp; ring
    have h1' : (w - b).re ≤ (z - b).re - 1 + 1 / 32 := by
      rw [hreb]; linarith [(abs_le.mp hreε).2]
    have h2' : |(w - b).im| ≥ |(z - b).im| - 1 / 32 := by
      rw [himb]
      have hh := abs_sub_abs_le_abs_add ((z - b).im) ε.im
      linarith [(abs_le.mp hreε).2, hh]
    have : 0 < |(w - b).im| - (w - b).re := by linarith
    linarith

/-- **Inverse-function step.**  Let `F` be differentiable on an open set `Q` containing the closed
ball `B̄(z - 1, 1/32)`, with `‖F w - (w + 1)‖ ≤ 1/32` and `‖deriv F w - 1‖ ≤ 1/32` on `Q`.  Then
`F` attains the value `z` inside that ball.

Proof: `𝒯 w = z - F w + w` maps the ball to itself (`𝒯 w - (z - 1) = -(F w - (w + 1))`) and is a
`1/32`-Lipschitz self-map (`deriv 𝒯 = 1 - deriv F w`), so it has a fixed point `w` there by the
Banach fixed point theorem; a fixed point is exactly a solution of `F w = z`. -/
theorem exists_preimage_in_closedBall {F : ℂ → ℂ} {Q : Set ℂ} {z : ℂ}
    (hQ : IsOpen Q) (hball : Metric.closedBall (z - 1) (1 / 32) ⊆ Q)
    (hdiff : DifferentiableOn ℂ F Q)
    (hFb : ∀ w ∈ Q, ‖F w - (w + 1)‖ ≤ 1 / 32)
    (hFd : ∀ w ∈ Q, ‖deriv F w - 1‖ ≤ 1 / 32) :
    ∃ w ∈ Metric.closedBall (z - 1) (1 / 32), F w = z := by
  let 𝒯 : ℂ → ℂ := fun w => z - F w + w
  -- `F` is differentiable at every point of the ball (the ball lies in the open set `Q`)
  have hFdat : ∀ w ∈ Metric.closedBall (z - 1) (1 / 32), DifferentiableAt ℂ F w :=
    fun w hw => (hdiff w (hball hw)).differentiableAt (hQ.mem_nhds (hball hw))
  -- derivative of the correction map `𝒯`
  have hderiv : ∀ w ∈ Metric.closedBall (z - 1) (1 / 32), deriv 𝒯 w = 1 - deriv F w := by
    intro w hw
    have h1 : DifferentiableAt ℂ (fun w => z - F w) w :=
      (differentiableAt_const z).sub (hFdat w hw)
    have h2 : DifferentiableAt ℂ (fun w : ℂ => w) w := differentiableAt_id
    have h3 : (fun w : ℂ => z - F w + w) = (fun w => z - F w) + (fun w : ℂ => w) := rfl
    rw [show 𝒯 = fun w : ℂ => z - F w + w from rfl, h3, deriv_add h1 h2, deriv_const_sub,
      show deriv (fun w : ℂ => w) w = 1 from deriv_id w]
    ring
  have hode : ∀ w ∈ Metric.closedBall (z - 1) (1 / 32), DifferentiableAt ℂ 𝒯 w := by
    intro w hw
    have h1 : DifferentiableAt ℂ (fun w => z - F w) w :=
      (differentiableAt_const z).sub (hFdat w hw)
    exact h1.add differentiableAt_id
  have hbound : ∀ w ∈ Metric.closedBall (z - 1) (1 / 32), ‖deriv 𝒯 w‖₊ ≤ (1 / 32 : NNReal) := by
    intro w hw
    have h' : ‖deriv 𝒯 w‖ ≤ 1 / 32 := by
      rw [hderiv w hw, norm_sub_rev]
      exact hFd w (hball hw)
    exact_mod_cast h'
  -- mean value inequality: `𝒯` is `1/32`-Lipschitz on the convex ball
  have hlip : LipschitzOnWith (1 / 32 : NNReal) 𝒯 (Metric.closedBall (z - 1) (1 / 32)) :=
    Convex.lipschitzOnWith_of_nnnorm_deriv_le (𝕜 := ℂ) (G := ℂ) (f := 𝒯)
      (s := Metric.closedBall (z - 1) (1 / 32)) hode hbound (convex_closedBall (z - 1) (1 / 32))
  -- `𝒯` maps the ball to itself
  have hmap : Set.MapsTo 𝒯 (Metric.closedBall (z - 1) (1 / 32))
      (Metric.closedBall (z - 1) (1 / 32)) := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm]
    have heq : 𝒯 w - (z - 1) = -(F w - (w + 1)) := by simp only [𝒯]; ring
    rw [heq, norm_neg]
    exact hFb w (hball hw)
  have hcontr : ContractingWith (1 / 32 : NNReal)
      (hmap.restrict 𝒯 (Metric.closedBall (z - 1) (1 / 32))
        (Metric.closedBall (z - 1) (1 / 32))) := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    change dist (𝒯 (x : ℂ)) (𝒯 (y : ℂ)) ≤ (1 / 32 : ℝ) * dist (x : ℂ) (y : ℂ)
    exact hlip.dist_le_mul (x : ℂ) x.2 (y : ℂ) y.2
  -- Banach fixed point theorem on the complete ball
  obtain ⟨w, hwmem, hfix, -⟩ :=
    ContractingWith.exists_fixedPoint' (f := 𝒯) (K := (1 / 32 : NNReal))
      (s := Metric.closedBall (z - 1) (1 / 32)) (Metric.isClosed_closedBall.isComplete) hmap hcontr
      (x := z - 1) (by rw [Metric.mem_closedBall, dist_self]; norm_num)
      (by rw [edist_dist]; exact ENNReal.ofReal_ne_top)
  refine ⟨w, hwmem, ?_⟩
  have hfix' : z - F w + w = w := hfix
  have h2 : z - F w = 0 := by
    have h3 : (z - F w) + w = 0 + w := by simpa using hfix'
    exact add_right_cancel h3
  exact (sub_eq_zero.mp h2).symm

/-- **A preimage to the right of the level line.**  Let `F` be a near-translation on
`𝒬 = Qreg b₁ b₂`, let `x₀` be strictly to the right of every vertex of `b₁`, and let `z ∈ 𝒬` have
`Re z ≥ x₀ + 1 + 1/31`.  Then `z` has a preimage `w ∈ 𝒬` with `Re w ≥ x₀`. -/
theorem preimage_of_re_ge {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {x₀ : ℝ}
    (hadm : MandelDim.QAdm b₁ b₂) (hF : MandelDim.NearTranslationOn F (MandelDim.Qreg b₁ b₂))
    (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) {z : ℂ} (hz : z ∈ MandelDim.Qreg b₁ b₂)
    (hzx : x₀ + 1 + 1 / 31 ≤ z.re) :
    ∃ w ∈ MandelDim.Qreg b₁ b₂, F w = z ∧ x₀ ≤ w.re := by
  have hQ : IsOpen (MandelDim.Qreg b₁ b₂) := Work.Fatou.Qreg.isOpen_Qreg b₁ b₂
  have hball := closedBall_subset_Qreg (b₁ := b₁) (b₂ := b₂) (x₀ := x₀) h₁ hz hzx
  obtain ⟨w, hwball, hFw⟩ := exists_preimage_in_closedBall hQ hball hF.1
    (fun u hu => (hF.2 u hu).1) (fun u hu => (hF.2 u hu).2)
  refine ⟨w, hball hwball, hFw, ?_⟩
  -- `Re w ≥ Re z - 1 - 1/32 ≥ x₀ + 1/31 - 1/32 ≥ x₀`
  rw [Metric.mem_closedBall, dist_eq_norm] at hwball
  have h1 : |(w - (z - 1)).re| ≤ 1 / 32 := le_trans (Complex.abs_re_le_norm _) hwball
  have h2 : (w - (z - 1)).re = w.re - z.re + 1 := by simp; ring
  rw [h2] at h1
  linarith [(abs_le.mp h1).1]

end Work.FatouL1
