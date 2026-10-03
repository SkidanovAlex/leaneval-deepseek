import Mathlib
import Submission.Work.L62LD.setup
import Submission.Work.L62LD.norm_deriv_leftInverse_le

/-!
# L62LD — the diameter bound for the discs of the lower-end head of Lemma 6.2

`Work.L62LD.diam_le_of_chain`: for a backward chain of discs `W` of `ĥ = d.E - β`
(`Work.L62LD.Chain`), starting at a ball `W 0 = ball ζc ρ`, if `Ψ j` is a differentiable right
inverse of `ĥ^[j]` on that ball with values in `W j`, and if the derivative of `ĥ^[j]` is bounded
below by `C⁻¹` on `W j`, then `diam (W j) ≤ 2 ρ C`:

```
  W j --ĥ^[j]--> W 0 = ball ζc ρ ,   |(ĥ^[j])'| ≥ C⁻¹  on W j
  ⟹  |(Ψ j)'| ≤ C  on the ball  (chain rule + F^[j] ∘ Ψ j = id)
  ⟹  diam (W j) ≤ C · diam (ball ζc ρ) ≤ 2 ρ C   (mean value inequality).
```

The inverse-branch derivative bound is `Work.L62LD.norm_deriv_leftInverse_le`; the iterates of the
chain are holomorphic on the discs, and the iterate is injective there, so `W j` is exactly the
`Ψ j`-image of the ball.
-/

namespace Work.L62LD

open Classical MandelDim Set Filter Topology
open scoped Topology

noncomputable section

variable {g₀ : ℂ → ℂ} {D : Set ℂ}

/-! ## Elementary facts about chains of discs -/

/-- The lifted horn map `d.E = Φ ∘ φ` is holomorphic on the lower horn `hd.Bl`. -/
theorem differentiableOn_E_of_Bl (d : MandelDim.ParabData g₀ D) (hd : MandelDim.HornData d) :
    DifferentiableOn ℂ d.E hd.Bl :=
  d.Φ_holo.comp (d.φ_holo.mono (fun _w hw => (hd.sub (Or.inr hw)).1))
    (fun _w hw => (hd.sub (Or.inr hw)).2)

/-- **The iterates of a chain are holomorphic on the discs of the chain.**  If `F` is holomorphic
on every disc `W j` of positive index and `F` maps `W (j+1)` onto `W j`, then `F^[j]` is
holomorphic on `W j`.  (Induction, using the chain rule `F^[j+1] = F^[j] ∘ F`.) -/
theorem iterate_differentiableOn_of_chain {F : ℂ → ℂ} {W : ℕ → Set ℂ} {J : ℕ}
    (hFdiff : ∀ j, 1 ≤ j → j ≤ J → DifferentiableOn ℂ F (W j))
    (himg : ∀ i, i < J → F '' W (i + 1) = W i) :
    ∀ j, j ≤ J → DifferentiableOn ℂ (F^[j]) (W j) := by
  intro j
  induction j with
  | zero => intro _; rw [Function.iterate_zero]; exact differentiableOn_id
  | succ m ih =>
      intro hmJ
      have hm : m ≤ J := Nat.le_of_succ_le hmJ
      have hmJ' : m < J := Nat.lt_of_succ_le hmJ
      rw [Function.iterate_succ]
      exact (ih hm).comp (hFdiff (m + 1) (by omega) hmJ) (fun w hw => by
        rw [← himg m hmJ']; exact ⟨w, hw, rfl⟩)

/-- **The iterates of a chain are injective on the discs of the chain.**  If `F` is injective on
every disc `W (j+1)` and `F '' W (j+1) = W j`, then `F^[j]` is injective on `W j`. -/
theorem iterate_injOn_of_chain {F : ℂ → ℂ} {W : ℕ → Set ℂ} {J : ℕ}
    (hinj : ∀ i, i < J → Set.InjOn F (W (i + 1)))
    (himg : ∀ i, i < J → F '' W (i + 1) = W i) :
    ∀ j, j ≤ J → Set.InjOn (F^[j]) (W j) := by
  intro j
  induction j with
  | zero => intro _; rw [Function.iterate_zero]; exact Set.injOn_id _
  | succ m ih =>
      intro hmJ
      have hm : m ≤ J := Nat.le_of_succ_le hmJ
      have hmJ' : m < J := Nat.lt_of_succ_le hmJ
      intro a ha b hb hab
      have hmem : ∀ w ∈ W (m + 1), F w ∈ W m := fun w hw => by
        rw [← himg m hmJ']; exact ⟨w, hw, rfl⟩
      have h1 : F a = F b :=
        ih hm (hmem a ha) (hmem b hb) (by simpa [Function.iterate_succ_apply] using hab)
      exact hinj m hmJ' ha hb h1

/-! ## The diameter bound -/

/-- **A diameter bound from a Lipschitz inverse branch.**  If `Ψ` is a differentiable right
inverse of `F^[j]` on the ball `W 0 = ball ζc ρ`, with values in `W j`, and `‖deriv Ψ‖ ≤ C` on
that ball, then `diam (W j) ≤ 2 ρ C`: the ball is convex, so the mean value inequality bounds
`Ψ` by `C`, and `F^[j]` maps `W j` onto a subset of the ball. -/
theorem diam_le_of_lipschitz_inverse {F : ℂ → ℂ} {ζc : ℂ} {ρ C : ℝ} {W : ℕ → Set ℂ} {j : ℕ}
    (hρ : 0 < ρ) (hC : 0 ≤ C) (hW0 : W 0 = Metric.ball ζc ρ)
    (hinj : Set.InjOn (F^[j]) (W j)) (himg : (F^[j]) '' W j = W 0)
    {Ψ : ℂ → ℂ} (hΨd : DifferentiableOn ℂ Ψ (Metric.ball ζc ρ))
    (hΨmem : ∀ u ∈ Metric.ball ζc ρ, Ψ u ∈ W j)
    (hΨinv : ∀ u ∈ Metric.ball ζc ρ, (F^[j]) (Ψ u) = u)
    (hDb : ∀ u ∈ Metric.ball ζc ρ, ‖deriv Ψ u‖ ≤ C) :
    Metric.diam (W j) ≤ 2 * ρ * C := by
  have hmemball : ∀ w ∈ W j, (F^[j]) w ∈ Metric.ball ζc ρ := by
    intro w hw
    have h : (F^[j]) w ∈ W 0 := by rw [← himg]; exact ⟨w, hw, rfl⟩
    rwa [hW0] at h
  have hrepr : ∀ w ∈ W j, Ψ ((F^[j]) w) = w := by
    intro w hw
    exact hinj (hΨmem _ (hmemball w hw)) hw (hΨinv _ (hmemball w hw))
  have hlip : ∀ u ∈ Metric.ball ζc ρ, ∀ u' ∈ Metric.ball ζc ρ,
      ‖Ψ u - Ψ u'‖ ≤ C * ‖u - u'‖ := by
    intro u hu u' hu'
    exact (convex_ball ζc ρ).norm_image_sub_le_of_norm_deriv_le
      (fun z hz => hΨd.differentiableAt (Metric.isOpen_ball.mem_nhds hz))
      (fun z hz => hDb z hz) hu' hu
  have h2rho : (0 : ℝ) ≤ 2 * ρ := by linarith
  refine Metric.diam_le_of_forall_dist_le (by positivity) ?_
  intro w hw w' hw'
  have hw0 := hmemball w hw
  have hw0' := hmemball w' hw'
  have h2 : ‖(F^[j]) w - (F^[j]) w'‖ ≤ 2 * ρ := by
    have h3 : ‖(F^[j]) w - ζc‖ < ρ := by
      simpa [dist_eq_norm] using Metric.mem_ball.mp hw0
    have h4 : ‖(F^[j]) w' - ζc‖ < ρ := by
      simpa [dist_eq_norm] using Metric.mem_ball.mp hw0'
    calc ‖(F^[j]) w - (F^[j]) w'‖
        = ‖((F^[j]) w - ζc) - ((F^[j]) w' - ζc)‖ := by
          rw [show (F^[j]) w - (F^[j]) w'
              = ((F^[j]) w - ζc) - ((F^[j]) w' - ζc) from by ring]
      _ ≤ ‖(F^[j]) w - ζc‖ + ‖(F^[j]) w' - ζc‖ := norm_sub_le _ _
      _ ≤ 2 * ρ := by linarith
  calc dist w w' = ‖w - w'‖ := dist_eq_norm w w'
    _ = ‖Ψ ((F^[j]) w) - Ψ ((F^[j]) w')‖ := by rw [hrepr w hw, hrepr w' hw']
    _ ≤ C * ‖(F^[j]) w - (F^[j]) w'‖ := hlip _ hw0 _ hw0'
    _ ≤ C * (2 * ρ) := mul_le_mul_of_nonneg_left h2 hC
    _ = 2 * ρ * C := by ring

/-! ## The requested lemma -/

theorem diam_le_of_chain {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d)
    {β ζc : ℂ} {ρ C : ℝ} {W : ℕ → Set ℂ} {J : ℕ} {Ψ : ℕ → ℂ → ℂ}
    (hρ : 0 < ρ) (hC : 1 ≤ C) (hc : Work.L62LD.Chain d hd β W) (hW0 : W 0 = Metric.ball ζc ρ)
    (hΨd : ∀ j, j ≤ J → DifferentiableOn ℂ (Ψ j) (Metric.ball ζc ρ))
    (hΨmem : ∀ j, j ≤ J → ∀ u ∈ Metric.ball ζc ρ, Ψ j u ∈ W j)
    (hΨinv : ∀ j, j ≤ J → ∀ u ∈ Metric.ball ζc ρ, ((fun w => d.E w - β)^[j]) (Ψ j u) = u)
    (hratio : ∀ j, 1 ≤ j → j ≤ J → ∀ w ∈ W j,
      C⁻¹ ≤ ‖deriv ((fun w => d.E w - β)^[j]) w‖) :
    ∀ j, j ≤ J → Metric.diam (W j) ≤ 2 * ρ * C := by
  -- `ĥ = d.E - β` is holomorphic on the lower horn, hence on every disc of the chain
  have hEdiff : DifferentiableOn ℂ d.E hd.Bl := differentiableOn_E_of_Bl d hd
  have hFdiff : DifferentiableOn ℂ (fun w => d.E w - β) hd.Bl := hEdiff.sub_const β
  -- the iterates of `ĥ` are holomorphic on the discs of the chain
  have hiterDiff : ∀ j, j ≤ J → DifferentiableOn ℂ ((fun w => d.E w - β)^[j]) (W j) :=
    iterate_differentiableOn_of_chain
      (fun j h1 _ => hFdiff.mono (hc.mem_Bl j h1)) (fun i _ => hc.img i)
  -- `ĥ^[j]` is injective on `W j` and maps it onto `W 0`
  have hinj : ∀ j, j ≤ J → Set.InjOn ((fun w => d.E w - β)^[j]) (W j) :=
    iterate_injOn_of_chain (fun i _ => hc.inj i) (fun i _ => hc.img i)
  have himg : ∀ j, j ≤ J → ((fun w => d.E w - β)^[j]) '' W j = W 0 := by
    intro j hj
    have h := hc.iterate_image j j le_rfl
    simpa [Nat.sub_self] using h
  intro j hj
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · -- `j = 0`: the disc IS the ball
    subst h0
    calc Metric.diam (W 0) ≤ 2 * ρ := by
          rw [hW0]; exact Metric.diam_ball (le_of_lt hρ)
      _ ≤ 2 * ρ * C := by
          have h5 : (0 : ℝ) ≤ 2 * ρ * (C - 1) := mul_nonneg (by positivity) (by linarith)
          nlinarith [h5]
  · -- `j ≥ 1`: the derivative of the inverse branch is bounded by `C`
    have hdb : ∀ u ∈ Metric.ball ζc ρ, ‖deriv (Ψ j) u‖ ≤ C :=
      norm_deriv_leftInverse_le (hc.opconn j).1 Metric.isOpen_ball
        (hiterDiff j hj) (hΨd j hj) (hΨmem j hj) (hΨinv j hj) hC
        (fun w hw => hratio j hpos hj w hw)
    exact diam_le_of_lipschitz_inverse hρ (le_trans zero_le_one hC) hW0
      (hinj j hj) (himg j hj) (hΨd j hj) (hΨmem j hj) (hΨinv j hj) hdb

end

end Work.L62LD
