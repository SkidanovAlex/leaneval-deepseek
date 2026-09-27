import Mathlib
import Submission.Work.Drive.N2.windowDatum
import Submission.Work.Drive.N2.levelBoundsOfJourney
import Submission.Work.Drive.N2.extremumJourney_avoids
import Submission.Work.Drive.N2.chartModelDrawing
import Submission.Work.Drive.N2.norm_le_of_mem_closure_modelBall
import Submission.Work.Drive.N2.hmono_of_chartODE
import Submission.Work.Drive.N2.ModelDefs

/-!
# The model region of an extremum window (`n = 2`, H8 lane)

`Work.Drive.N2.exists_extremumModelRegion` is the *extremum* analogue of
`Work.Drive.N2.exists_saddleModelRegion`.  At a critical point `p` at which the two Morse signs
*agree* (a local maximum or minimum), and for a window half-width `η` with

* `(ρ / 8)² ≤ η / 2` (the value-confined region `U = modelBall (φ j) (√(η/2))` contains the
  flow's speed-drop ball `modelBall (φ j) (ρ/8)`), and
* `η ≤ ηd` (the window is inside the datum's value-separation distance);

the fourth row `4 η ≤ ρ²` of the requested interface is carried for its consumers (the `√η`-ball
inside the chart region); it is *not* used by the construction below.

there is an open *model region* `U` (`= modelBall (φ j) (√(η/2))`, on which `|f x - f p| < η/2`),
a model drawing `model` with values in `{x₀ < 0}` which is a `GoodDrawingOnK f U A` for the whole
window `A = (f p - η, f p + η)`, and the *landing row*: every point of the window outside `U` has
its journey in the model-adapted flow land exactly on the anchor level `f p + s η`.

The drawing half is the chart brick `Work.Drive.N2.goodDrawingOnK_of_chartCoord` (no Morse theory
needed).  The landing half is the content: for `x` off the `ρ/8`-ball and inside the window the
whole journey up to the anchor level avoids *every* model ball, so that the datum's level law
`WindowDatum.hlevel` gives the landing.  The avoidance is proved **without** any continuity
hypothesis on `f` (`f` is only known through the datum, which does not force it to be continuous):

* the values along the journey are trapped in `[c - η, c + η]` by `WindowDatum.level_trap`
  (`f x + min 0 u ≤ f (Φ (u,x)) ≤ f x + max 0 u`), the monotonicity clause of the datum plus the
  proved backward level bound `Work.Drive.N2.levelBoundsOfJourney`;
* hence no ball of an *other* chart can be met: its values are more than `2 ηd ≥ 2 η` away from
  `f p` (`WindowDatum.hsepK`), while the journey's values are in the closed window;
* the *home* ball `modelBall (φ j) (ρ/8)` is excluded by the first-entry argument: if `m` is the
  infimum of the times at which the journey is in the ball, then either the journey is in the ball
  at `m` (impossible by openness), or it lies on the sphere `‖φ j ·‖ = ρ/8`; there the restarted
  chart ODE (`WindowDatum.hODE` with the proved monotonicity of the squared chart radius
  `Work.Drive.N2.monotoneOn_normSq_of_chartODE`) keeps the journey off the ball, contradicting the
  existence of bad times arbitrarily close above `m`.  The only continuity used is that of the
  journey `u ↦ Φ (u,x)`, which the datum supplies (`hΦsm`).
-/

namespace Work.Drive.N2

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped Manifold _root_.ContDiff _root_.Topology
open Set Function Filter

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-! ## Small bricks -/

/-- The three coordinates of `incl23`. -/
@[simp] lemma incl23_apply_zero (u : EuclideanSpace ℝ (Fin 2)) : (incl23 u) 0 = u 0 := by
  simp [incl23, WithLp.linearEquiv]

@[simp] lemma incl23_apply_one (u : EuclideanSpace ℝ (Fin 2)) : (incl23 u) 1 = u 1 := by
  simp [incl23, WithLp.linearEquiv]

@[simp] lemma incl23_apply_two (u : EuclideanSpace ℝ (Fin 2)) : (incl23 u) 2 = 0 := by
  simp [incl23, WithLp.linearEquiv]

lemma incl23_injective : Function.Injective incl23 := by
  intro u w h
  ext i
  fin_cases i
  · have := congrArg (fun z : EuclideanSpace ℝ (Fin 3) => z 0) h
    simpa using this
  · have := congrArg (fun z : EuclideanSpace ℝ (Fin 3) => z 1) h
    simpa using this

/-- The rows of `GoodDrawingOnK f U A` only see the drawing on `U`. -/
lemma goodDrawingOnK_congr {f : M → ℝ} {U : Set M} {A : Set ℝ}
    {g h : M → EuclideanSpace ℝ (Fin 3)} (hU : IsOpen U) (heq : ∀ x ∈ U, g x = h x)
    (hg : GoodDrawingOnK f U A g) : GoodDrawingOnK f U A h := by
  have hn : ((∞ : WithTop ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  refine ⟨?_, ?_, ?_⟩
  · intro x hx hxA
    refine ((hg.1 x hx hxA).congr_of_eventuallyEq ?_)
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (heq y hy).symm
  · intro x hx hxA v hv hvh
    have hmdeq : mfderiv (𝓡 2) (𝓡 3) g x = mfderiv (𝓡 2) (𝓡 3) h x := by
      refine (show g =ᶠ[𝓝 x] h from ?_).mfderiv_eq
      filter_upwards [hU.mem_nhds hx] with y hy
      exact heq y hy
    rw [← hmdeq] at hvh
    exact hg.2.1 x hx hxA v hv hvh
  · intro x y hx hy hxA hyA hfxy hh
    exact hg.2.2 x y hx hy hxA hyA hfxy (by rw [heq x hx, heq y hy, hh])

/-- The reflection of the symmetric interval `[min 0 a, max 0 a]`. -/
lemma neg_mem_Icc_neg' {a t : ℝ} (h : t ∈ Set.Icc (min 0 a) (max 0 a)) :
    -t ∈ Set.Icc (min 0 (-a)) (max 0 (-a)) := by
  have h1 : min 0 (-a) = -max 0 a := by simpa using min_neg_neg (0:ℝ) a
  have h2 : max 0 (-a) = -min 0 a := by simpa using max_neg_neg (0:ℝ) a
  rw [h1, h2]
  simp only [Set.mem_Icc] at h ⊢
  exact ⟨by linarith [h.2], by linarith [h.1]⟩

/-- Chain rule for a negated parametrisation. -/
lemma hasDerivAt_neg_comp' {g : ℝ → ℝ} {g' t : ℝ} (h : HasDerivAt g g' (-t)) :
    HasDerivAt (fun s : ℝ => g (-s)) (-g') t := by
  have h2 : HasDerivAt (g ∘ fun s : ℝ => -s) (g' * (-1)) t := h.comp t (hasDerivAt_neg t)
  have hv : g' * (-1) = -g' := by ring
  rw [hv] at h2
  exact h2

/-- **The level trap.**  Along any orbit of the model-adapted flow the value of `f` is trapped
between `f x + min 0 u` and `f x + max 0 u`: the lower bound is the monotonicity clause of the
datum, the upper bound is the backward level bound `Work.Drive.N2.levelBoundsOfJourney`. -/
theorem WindowDatum.level_trap {f : M → ℝ} {p : M} (D : WindowDatum f p) (x : M) (u : ℝ) :
    f x + min 0 u ≤ f (D.Φ (u, x)) ∧ f (D.Φ (u, x)) ≤ f x + max 0 u := by
  have hrot : ∀ y : M, D.Φ (-u, D.Φ (u, y)) = y := by
    intro y
    rw [D.hΦcomp (-u) u y, neg_add_cancel, D.hΦ0]
  rcases le_total 0 u with hu | hu
  · refine ⟨?_, ?_⟩
    · rw [min_eq_left hu]
      have h := D.hmono x (show (0:ℝ) ∈ Set.Ici 0 by simp)
        (show u ∈ Set.Ici 0 by simpa using hu) hu
      have h' : f (D.Φ (0, x)) ≤ f (D.Φ (u, x)) := h
      rw [D.hΦ0] at h'
      linarith
    · rw [max_eq_right hu]
      have h := (levelBoundsOfJourney (D := D) (x := D.Φ (u, x)) (τ := -u) (by linarith)).1
      rw [hrot x] at h
      linarith
  · refine ⟨?_, ?_⟩
    · rw [min_eq_right hu]
      exact (levelBoundsOfJourney (D := D) (x := x) (τ := u) hu).1
    · rw [max_eq_left hu]
      have h := D.hmono (D.Φ (u, x)) (show (0:ℝ) ∈ Set.Ici 0 by simp)
        (show -u ∈ Set.Ici 0 by simpa using (by linarith : (0:ℝ) ≤ -u)) (by linarith)
      have h' : f (D.Φ (0, D.Φ (u, x))) ≤ f (D.Φ (-u, D.Φ (u, x))) := h
      rw [D.hΦ0, hrot x] at h'
      simpa using h'

/-- **The chart value at the marked chart**: if the two Morse signs agree, `f` is `f p` plus the
(signed) squared chart radius on the chart source. -/
theorem WindowDatum.chart_val_at_j {f : M → ℝ} {p : M} (D : WindowDatum f p)
    (hext : D.s₁ D.j = D.s₂ D.j) {y : M} (hy : y ∈ (D.φ D.j).source) :
    f y = f p + D.s₁ D.j * ‖D.φ D.j y‖ ^ 2 := by
  have h := D.hval D.j y hy
  rw [chartQ] at h
  have hxj : f (D.x D.j) = f p := by rw [D.hxj]
  rw [h, hxj, hext]
  rw [← mul_add, norm_uVec]

/-- **A point of the closed window misses every model ball of another chart.** -/
lemma notMem_modelBall_of_win {f : M → ℝ} {p : M} (D : WindowDatum f p)
    {η : ℝ} (hη : 0 < η) (hηd : η ≤ D.ηd) {z : M} (hz : |f z - f p| ≤ η)
    {i : Fin D.N} (hi : i ≠ D.j) :
    z ∉ modelBall (D.φ i) (D.ρ i / 8) := by
  intro hmem
  have hsep := D.mem_K_of_mem_other (i := i) hi hmem
  have hxj : f (D.x D.j) = f p := by rw [D.hxj]
  rw [hxj] at hsep
  have h2 : (2:ℝ) * η ≤ 2 * D.ηd := by linarith
  linarith [hsep, hz]

/-- **First-entry exclusion of the home model ball** for a flow `Ψ` whose chart radius evolves by
the model ODE: if the journey `u ↦ Ψ (u, x)` starts off `modelBall φ r` and, near every point of
the closure of that ball, the flow keeps a region `C` for a short positive time while solving the
chart ODE with multiplier `chartMult r`, then the journey never enters the ball. -/
theorem avoid_homeBall_of_flow {Ψ : ℝ × M → M}
    {φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))} {C : Set M} {r T : ℝ} {x : M}
    (h0 : ∀ y : M, Ψ (0, y) = y)
    (hcomp : ∀ (a b : ℝ) (y : M), Ψ (a, Ψ (b, y)) = Ψ (a + b, y))
    (hcont : Continuous Ψ)
    (hx : x ∉ modelBall φ r)
    (hODE : ∀ (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), Ψ (u, y) ∈ C) →
      HasDerivAt (fun s : ℝ => φ (Ψ (s, y)) 0)
        (chartMult r (‖φ (Ψ (t, y))‖ ^ 2) * φ (Ψ (t, y)) 0) t ∧
      HasDerivAt (fun s : ℝ => φ (Ψ (s, y)) 1)
        (chartMult r (‖φ (Ψ (t, y))‖ ^ 2) * φ (Ψ (t, y)) 1) t)
    (hCseg : ∀ y ∈ closure (modelBall φ r), ∃ ε : ℝ, 0 < ε ∧
      ∀ t ∈ Set.Icc (0:ℝ) ε, Ψ (t, y) ∈ C)
    (hsrc : closure (modelBall φ r) ⊆ φ.source)
    (hT : 0 ≤ T) :
    ∀ u ∈ Set.Icc (0:ℝ) T, Ψ (u, x) ∉ modelBall φ r := by
  classical
  intro u₁ hu₁
  by_contra hcon
  set W : Set ℝ := {u : ℝ | u ∈ Set.Icc (0:ℝ) T ∧ Ψ (u, x) ∈ modelBall φ r} with hW
  have hWmem : ∀ u : ℝ, u ∈ W ↔ u ∈ Set.Icc (0:ℝ) T ∧ Ψ (u, x) ∈ modelBall φ r := by
    intro u; rw [hW]; exact Iff.rfl
  have hWne : W.Nonempty := ⟨u₁, (hWmem u₁).mpr ⟨hu₁, hcon⟩⟩
  have hWbdd : BddBelow W := ⟨0, fun u hu => ((hWmem u).mp hu).1.1⟩
  set m : ℝ := sInf W with hm
  have hm0 : 0 ≤ m := le_csInf hWne (fun u hu => ((hWmem u).mp hu).1.1)
  have hmT : m ≤ T := le_trans (csInf_le hWbdd ((hWmem u₁).mpr ⟨hu₁, hcon⟩)) hu₁.2
  have hle_m : ∀ u ∈ W, m ≤ u := fun u hu => csInf_le hWbdd hu
  have hcontx : Continuous fun v : ℝ => Ψ (v, x) :=
    hcont.comp (continuous_id.prodMk continuous_const)
  -- the infimum is not in `W`
  have hmW : m ∉ W := by
    intro hmw
    have hmwm : Ψ (m, x) ∈ modelBall φ r := ((hWmem m).mp hmw).2
    rcases eq_or_lt_of_le hm0 with h0m | hpos
    · have hzero : Ψ (0, x) ∈ modelBall φ r := by rw [h0m]; exact hmwm
      rw [h0] at hzero
      exact hx hzero
    · have hev : ∀ᶠ v in 𝓝 m, Ψ (v, x) ∈ modelBall φ r :=
        hcontx.continuousAt.preimage_mem_nhds ((isOpen_modelBall φ r).mem_nhds hmwm)
      obtain ⟨δ, hδ0, hδ⟩ := Metric.eventually_nhds_iff.mp hev
      obtain ⟨v, hv1, hv2⟩ := exists_between (show max 0 (m - δ / 2) < m by
        rw [max_lt_iff]
        exact ⟨hpos, by linarith⟩)
      have hv0 : 0 ≤ v := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hv1)
      have hvmδ : m - δ < v := by
        have := le_max_right (0:ℝ) (m - δ / 2)
        linarith
      have hdist : dist v m < δ := by
        rw [Real.dist_eq, abs_lt]
        exact ⟨by linarith, by linarith⟩
      have hvW : v ∈ W := (hWmem v).mpr ⟨Set.mem_Icc.mpr ⟨hv0, by linarith⟩, hδ hdist⟩
      linarith [hle_m v hvW, hv2]
  have hmT' : m < T := by
    rcases lt_or_eq_of_le hmT with h | h
    · exact h
    · exfalso
      obtain ⟨w, hw⟩ := hWne
      have hwT : w = T := le_antisymm ((hWmem w).mp hw).1.2 (by rw [← h]; exact hle_m w hw)
      exact hmW (by rw [h, ← hwT]; exact hw)
  -- the infimum lies in the closure of the ball
  have hcl : Ψ (m, x) ∈ closure (modelBall φ r) := by
    rw [mem_closure_iff_nhds]
    intro U hU
    have hevU : ∀ᶠ v in 𝓝 m, Ψ (v, x) ∈ U := hcontx.continuousAt hU
    obtain ⟨δ, hδ0, hδ⟩ := Metric.eventually_nhds_iff.mp hevU
    obtain ⟨w, hwW, hwlt⟩ := (csInf_lt_iff hWbdd hWne).mp
      (show sInf W < m + δ by rw [← hm]; linarith)
    have hwm : m < w := by
      rcases lt_or_eq_of_le (hle_m w hwW) with h | h
      · exact h
      · exact absurd (by rw [h]; exact hwW) hmW
    have hdist : dist w m < δ := by
      rw [Real.dist_eq, abs_lt]
      exact ⟨by linarith, by linarith⟩
    exact ⟨Ψ (w, x), ⟨hδ hdist, ((hWmem w).mp hwW).2⟩⟩
  -- the chart radius at the infimum is exactly `r`
  have hnorm : ‖φ (Ψ (m, x))‖ = r := by
    refine le_antisymm (norm_le_of_mem_closure_modelBall φ r hsrc _ hcl) ?_
    by_contra hlt
    rw [not_le] at hlt
    exact hmW ((hWmem m).mpr ⟨⟨hm0, hmT⟩, ⟨hsrc hcl, hlt⟩⟩)
  -- the restarted chart ODE at the sphere point
  obtain ⟨ε, hε0, hεC⟩ := hCseg (Ψ (m, x)) hcl
  have hode : ∀ s ∈ Set.Icc (0:ℝ) ε,
      HasDerivAt (fun u : ℝ => φ (Ψ (u, Ψ (m, x))) 0)
        (chartMult r (‖φ (Ψ (s, Ψ (m, x)))‖ ^ 2) * φ (Ψ (s, Ψ (m, x))) 0) s ∧
      HasDerivAt (fun u : ℝ => φ (Ψ (u, Ψ (m, x))) 1)
        (chartMult r (‖φ (Ψ (s, Ψ (m, x)))‖ ^ 2) * φ (Ψ (s, Ψ (m, x))) 1) s := by
    intro s hs
    refine hODE (Ψ (m, x)) s (fun u hu => ?_)
    rw [min_eq_left hs.1, max_eq_right hs.1] at hu
    exact hεC u ⟨hu.1, le_trans hu.2 hs.2⟩
  have hmono := monotoneOn_normSq_of_chartODE hode
  -- a bad time just above the infimum contradicts the monotonicity
  obtain ⟨w, hwW, hwlt⟩ := (csInf_lt_iff hWbdd hWne).mp
    (show sInf W < m + ε by rw [← hm]; linarith)
  have hwm : m < w := by
    rcases lt_or_eq_of_le (hle_m w hwW) with h | h
    · exact h
    · exact absurd (by rw [h]; exact hwW) hmW
  have hrew : Ψ (w, x) = Ψ (w - m, Ψ (m, x)) := by
    rw [hcomp]
    congr 1
    ring
  have hge : ‖φ (Ψ (0, Ψ (m, x)))‖ ^ 2 ≤ ‖φ (Ψ (w - m, Ψ (m, x)))‖ ^ 2 :=
    hmono ⟨le_rfl, hε0.le⟩ ⟨by linarith, by linarith⟩ (by linarith)
  rw [h0, ← hrew, hnorm] at hge
  have hlt : ‖φ (Ψ (w, x))‖ < r := ((hWmem w).mp hwW).2.2
  nlinarith [norm_nonneg (φ (Ψ (w, x)))]

/-- **The journey to the anchor level avoids every model ball.**  For a point `x` off the
`ρ j / 8`-ball whose value lies in the window `(f p - η, f p + η)`, the whole journey in the
`Φ`-parametrisation up to the anchor level `f p + s₁ j * η` avoids all the model balls.  No
continuity of `f` is needed: the values are trapped in the window by `WindowDatum.level_trap`, and
the home ball is excluded by the first-entry argument `avoid_homeBall_of_flow`. -/
theorem journey_avoids_modelBalls {f : M → ℝ} {p : M} (D : WindowDatum f p)
    (hext : D.s₁ D.j = D.s₂ D.j)
    {η : ℝ} (hη : 0 < η) (hηd : η ≤ D.ηd) {x : M}
    (hx : x ∉ modelBall (D.φ D.j) (D.ρ D.j / 8))
    (hband : f x ∈ Set.Ioo (f p - η) (f p + η)) :
    ∀ u ∈ Set.Icc (min 0 (f p + D.s₁ D.j * η - f x))
        (max 0 (f p + D.s₁ D.j * η - f x)),
      ∀ i : Fin D.N, D.Φ (u, x) ∉ modelBall (D.φ i) (D.ρ i / 8) := by
  classical
  have hsrccl : closure (modelBall (D.φ D.j) (D.ρ D.j / 8)) ⊆ (D.φ D.j).source :=
    (closure_mono (D.hCball D.j)).trans (D.hCcl D.j).2
  rcases (D.hsgn D.j).1 with hs1 | hs1
  · -- a minimum: the datum's own flow
    have hs2 : D.s₂ D.j = 1 := by rw [← hext]; exact hs1
    have hT : 0 ≤ f p + η - f x := by linarith [hband.2]
    have hwin : ∀ u ∈ Set.Icc (0:ℝ) (f p + η - f x), |f (D.Φ (u, x)) - f p| ≤ η := by
      intro u hu
      have htr := WindowDatum.level_trap D x u
      rw [min_eq_left hu.1, max_eq_right hu.1] at htr
      rw [abs_le]
      exact ⟨by linarith [htr.1, hband.1], by linarith [htr.2, hu.2, hband.2]⟩
    have hhome : ∀ u ∈ Set.Icc (0:ℝ) (f p + η - f x),
        D.Φ (u, x) ∉ modelBall (D.φ D.j) (D.ρ D.j / 8) :=
      avoid_homeBall_of_flow (Ψ := D.Φ) (φ := D.φ D.j) (C := D.C D.j)
        (r := D.ρ D.j / 8) (T := f p + η - f x) (x := x)
        D.hΦ0 D.hΦcomp D.hΦsm.continuous hx
        (fun y t hconf => by
          have h := D.hODE D.j y t hconf
          simpa [hs1, hs2] using h)
        (fun y hy => by
          obtain ⟨δ, hδ0, hδ⟩ := mem_C_of_mem_closure_modelBall D D.j (y := y) (σ := 0)
            (by simpa [D.hΦ0] using hy)
          refine ⟨δ / 2, by linarith, fun t ht => ?_⟩
          exact hδ t (by
            rw [sub_zero, abs_of_nonneg ht.1]
            linarith [ht.2]))
        hsrccl hT
    intro u hu i
    have ha : f p + D.s₁ D.j * η - f x = f p + η - f x := by rw [hs1]; ring
    have hu' : u ∈ Set.Icc (0:ℝ) (f p + η - f x) := by
      refine Set.mem_Icc.mpr ⟨?_, ?_⟩
      · calc (0:ℝ) = min 0 (f p + D.s₁ D.j * η - f x) := by rw [ha]; exact (min_eq_left hT).symm
        _ ≤ u := hu.1
      · calc u ≤ max 0 (f p + D.s₁ D.j * η - f x) := hu.2
        _ = f p + η - f x := by rw [ha]; exact max_eq_right hT
    by_cases hi : i = D.j
    · subst hi
      exact hhome u hu'
    · exact notMem_modelBall_of_win D hη hηd (hwin u hu') hi
  · -- a maximum: the reversed parametrisation
    have hs2 : D.s₂ D.j = -1 := by rw [← hext]; exact hs1
    have hT : 0 ≤ f x - f p + η := by linarith [hband.1]
    have hwin : ∀ u ∈ Set.Icc (0:ℝ) (f x - f p + η), |f (D.Φ (-u, x)) - f p| ≤ η := by
      intro u hu
      have htr := WindowDatum.level_trap D x (-u)
      rw [min_eq_right (by linarith [hu.1]), max_eq_left (by linarith [hu.1])] at htr
      rw [abs_le]
      exact ⟨by linarith [htr.1, hu.2], by linarith [htr.2, hband.2]⟩
    have hhome : ∀ u ∈ Set.Icc (0:ℝ) (f x - f p + η),
        D.Φ (-u, x) ∉ modelBall (D.φ D.j) (D.ρ D.j / 8) :=
      avoid_homeBall_of_flow (Ψ := fun q : ℝ × M => D.Φ (-q.1, q.2)) (φ := D.φ D.j)
        (C := D.C D.j) (r := D.ρ D.j / 8) (T := f x - f p + η) (x := x)
        (fun y => by simp [D.hΦ0])
        (fun a b y => by
          show D.Φ (-a, D.Φ (-b, y)) = D.Φ (-(a + b), y)
          rw [D.hΦcomp]
          congr 1
          ring_nf)
        (D.hΦsm.continuous.comp (by fun_prop))
        hx
        (fun y t hconf => by
          have hmain := D.hODE D.j y (-t) (fun u' hu' => by
            have hu : -u' ∈ Set.Icc (min 0 t) (max 0 t) := by
              simpa using neg_mem_Icc_neg' (a := -t) hu'
            simpa using hconf (-u') hu)
          refine ⟨?_, ?_⟩
          · refine (hasDerivAt_neg_comp'
              (g := fun τ : ℝ => D.φ D.j (D.Φ (τ, y)) 0) hmain.1).congr_deriv ?_
            show -(chartMult (D.ρ D.j / 8) (‖D.φ D.j (D.Φ (-t, y))‖ ^ 2)
                * (D.s₁ D.j * D.φ D.j (D.Φ (-t, y)) 0))
              = chartMult (D.ρ D.j / 8) (‖D.φ D.j (D.Φ (-t, y))‖ ^ 2)
                * D.φ D.j (D.Φ (-t, y)) 0
            rw [hs1]; ring
          · refine (hasDerivAt_neg_comp'
              (g := fun τ : ℝ => D.φ D.j (D.Φ (τ, y)) 1) hmain.2).congr_deriv ?_
            show -(chartMult (D.ρ D.j / 8) (‖D.φ D.j (D.Φ (-t, y))‖ ^ 2)
                * (D.s₂ D.j * D.φ D.j (D.Φ (-t, y)) 1))
              = chartMult (D.ρ D.j / 8) (‖D.φ D.j (D.Φ (-t, y))‖ ^ 2)
                * D.φ D.j (D.Φ (-t, y)) 1
            rw [hs2]; ring)
        (fun y hy => by
          obtain ⟨δ, hδ0, hδ⟩ := mem_C_of_mem_closure_modelBall D D.j (y := y) (σ := 0)
            (by simpa [D.hΦ0] using hy)
          refine ⟨δ / 2, by linarith, fun t ht => ?_⟩
          exact hδ (-t) (by
            rw [sub_zero, abs_neg, abs_of_nonneg ht.1]
            linarith [ht.2]))
        hsrccl hT
    intro u hu i
    have ha : f p + D.s₁ D.j * η - f x = -(f x - f p + η) := by rw [hs1]; ring
    have ha' : f p + D.s₁ D.j * η - f x ≤ 0 := by rw [ha]; linarith [hη]
    have hu' : -u ∈ Set.Icc (0:ℝ) (f x - f p + η) := by
      refine Set.mem_Icc.mpr ⟨?_, ?_⟩
      · have h2 : u ≤ 0 := by
          have hmax : max 0 (f p + D.s₁ D.j * η - f x) ≤ 0 := max_le (le_refl 0) ha'
          exact le_trans hu.2 hmax
        linarith
      · have hmin : min 0 (f p + D.s₁ D.j * η - f x) = f p + D.s₁ D.j * η - f x :=
          min_eq_right ha'
        have h1 : f p + D.s₁ D.j * η - f x ≤ u := hmin ▸ hu.1
        rw [ha] at h1
        linarith
    by_cases hi : i = D.j
    · subst hi
      simpa using hhome (-u) hu'
    · simpa using notMem_modelBall_of_win D hη hηd (hwin (-u) hu') hi


theorem exists_extremumModelRegion {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    (hext : D.s₁ D.j = D.s₂ D.j)
    {η : ℝ} (hη : 0 < η) (hηρ : 4 * η ≤ (D.ρ D.j) ^ 2) (hηd : η ≤ D.ηd)
    (hηbig : (D.ρ D.j / 8) ^ 2 ≤ η / 2) :
    ∃ (U : Set M) (model : M → EuclideanSpace ℝ (Fin 3)),
      IsOpen U ∧ (∀ x ∈ U, |f x - f p| < η / 2) ∧ (∀ x : M, (model x) 0 < 0) ∧
      Work.Drive.N2.GoodDrawingOnK f U (Set.Ioo (f p - η) (f p + η)) model ∧
      (∀ x : M, x ∉ U → f x ∈ Set.Ioo (f p - η) (f p + η) →
        f (D.Φ (f p + D.s₁ D.j * η - f x, x)) = f p + D.s₁ D.j * η) := by
  classical
  set b : ℝ := Real.sqrt (η / 2) with hb
  have hb2 : b ^ 2 = η / 2 := by rw [hb]; exact Real.sq_sqrt (by linarith)
  have hrb : D.ρ D.j / 8 ≤ b := by
    rw [hb]
    have hρ8 : 0 ≤ D.ρ D.j / 8 := by have := D.hρ D.j; linarith
    calc D.ρ D.j / 8 = Real.sqrt ((D.ρ D.j / 8) ^ 2) := (Real.sqrt_sq hρ8).symm
      _ ≤ Real.sqrt (η / 2) := Real.sqrt_le_sqrt hηbig
  set U : Set M := modelBall (D.φ D.j) b with hU
  have hUopen : IsOpen U := by rw [hU]; exact isOpen_modelBall _ _
  -- the value confinement of the region
  have hUval : ∀ x ∈ U, |f x - f p| < η / 2 := by
    intro x hx
    rw [hU] at hx
    have h1 := D.chart_val_at_j hext hx.1
    have h2 : |f x - f p| = ‖D.φ D.j x‖ ^ 2 := by
      rw [h1]
      have hsabs : |D.s₁ D.j| = 1 := by
        rcases (D.hsgn D.j).1 with h | h <;> rw [h] <;> norm_num
      rw [add_sub_cancel_left, abs_mul, hsabs, one_mul, abs_of_nonneg (sq_nonneg _)]
    rw [h2]
    nlinarith [norm_nonneg (D.φ D.j x), hx.2, hb2]
  -- the model: the chart coordinate, pushed into the half-space `{x₀ < 0}`
  set v0 : EuclideanSpace ℝ (Fin 3) := (-(b + 1)) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
    with hv0
  have hv0c : v0 0 = -(b + 1) := by rw [hv0]; simp
  set model : M → EuclideanSpace ℝ (Fin 3) :=
    fun x => if x ∈ U then incl23 (D.φ D.j x) + v0 else v0 with hmodel
  have hsign : ∀ x : M, (model x) 0 < 0 := by
    intro x
    by_cases hx : x ∈ U
    · have h1 : D.φ D.j x 0 ≤ ‖D.φ D.j x‖ := by
        have h := PiLp.norm_apply_le (D.φ D.j x) (0 : Fin 2)
        rw [Real.norm_eq_abs] at h
        exact le_trans (le_abs_self _) h
      have h2 : ‖D.φ D.j x‖ < b := by rw [hU] at hx; exact hx.2
      have e1 : (model x) = incl23 (D.φ D.j x) + v0 := by
        rw [hmodel]; exact if_pos hx
      have e2 : (incl23 (D.φ D.j x) + v0 : EuclideanSpace ℝ (Fin 3)) 0
          = D.φ D.j x 0 + (-(b + 1)) := by
        rw [PiLp.add_apply, incl23_apply_zero, hv0c]
      rw [e1, e2]
      linarith
    · have hb0 : 0 ≤ b := by rw [hb]; exact Real.sqrt_nonneg _
      have e1 : (model x) = v0 := by
        rw [hmodel]; exact if_neg hx
      rw [e1, hv0c]
      linarith
  -- the drawing rows: the chart-coordinate brick
  have hchart_sm : ∀ y : M, y ∈ U → ContMDiffAt (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞
      (fun z : M => D.φ D.j z) y := by
    intro y hy
    rw [hU] at hy
    exact (D.hφ D.j).contMDiffAt ((D.φ D.j).open_source.mem_nhds hy.1)
  have hchart_inj : ∀ y : M, y ∈ U → ∀ z : M, z ∈ U → D.φ D.j y = D.φ D.j z → y = z := by
    intro y hy z hz h
    rw [hU] at hy hz
    rw [← (D.φ D.j).left_inv hy.1, h, (D.φ D.j).left_inv hz.1]
  have hchart_imm : ∀ y : M, y ∈ U → Function.Injective
      (mfderiv (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (fun z : M => D.φ D.j z) y) := by
    intro y hy
    rw [hU] at hy
    have hysrc : y ∈ (D.φ D.j).source := hy.1
    have hn : ((∞ : WithTop ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
    have hZmd : MDifferentiableAt (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
        (fun z : M => D.φ D.j z) y :=
      ((D.hφ D.j).contMDiffAt ((D.φ D.j).open_source.mem_nhds hysrc)).mdifferentiableAt hn
    have hgmd : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
        (fun w : EuclideanSpace ℝ (Fin 2) => (D.φ D.j).symm w) (D.φ D.j y) :=
      ((D.hφ' D.j).contMDiffAt ((D.φ D.j).open_target.mem_nhds
        ((D.φ D.j).map_source hysrc))).mdifferentiableAt hn
    have hev : ((fun w : EuclideanSpace ℝ (Fin 2) => (D.φ D.j).symm w) ∘
        (fun z : M => D.φ D.j z)) =ᶠ[𝓝 y] id := by
      filter_upwards [(D.φ D.j).open_source.mem_nhds hysrc] with z hz
      exact (D.φ D.j).left_inv hz
    have hkey : ∀ u : TangentSpace (𝓡 2) y,
        mfderiv (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (fun z : M => D.φ D.j z) y u = 0 → u = 0 := by
      intro u hu
      have hchain := mfderiv_comp_apply (I := 𝓡 2) (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
        (I'' := 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
        (f := fun z : M => D.φ D.j z)
        (g := fun w : EuclideanSpace ℝ (Fin 2) => (D.φ D.j).symm w) y hgmd hZmd u
      have h0 : mfderiv (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
          ((fun w : EuclideanSpace ℝ (Fin 2) => (D.φ D.j).symm w) ∘
            (fun z : M => D.φ D.j z)) y u = 0 := by
        rw [hchain, hu]
        exact map_zero _
      have h1 : mfderiv (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
          ((fun w : EuclideanSpace ℝ (Fin 2) => (D.φ D.j).symm w) ∘
            (fun z : M => D.φ D.j z)) y u = u := by
        rw [hev.mfderiv_eq, mfderiv_id]
        rfl
      rw [h1] at h0
      exact h0
    intro v w hvw
    have hsub : (mfderiv (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
        (fun z : M => D.φ D.j z) y) (v - w) = 0 := by
      rw [map_sub, hvw, sub_self]
    exact sub_eq_zero.mp (hkey (v - w) hsub)
  have hdraw : GoodDrawingOnK f U (Set.Ioo (f p - η) (f p + η))
      (fun x : M => incl23 (D.φ D.j x) + v0) :=
    goodDrawingOnK_of_chartCoord (E := EuclideanSpace ℝ (Fin 2)) incl23 incl23_injective v0
      hchart_sm hchart_inj hchart_imm _
  have hdraw' : GoodDrawingOnK f U (Set.Ioo (f p - η) (f p + η)) model :=
    goodDrawingOnK_congr hUopen (fun x hx => by simp only [hmodel, if_pos hx]) hdraw
  refine ⟨U, model, hUopen, hUval, hsign, hdraw', ?_⟩
  -- the landing row
  intro x hxU hxband
  have hx' : x ∉ modelBall (D.φ D.j) (D.ρ D.j / 8) := by
    intro hmem
    exact hxU (by rw [hU]; exact ⟨hmem.1, lt_of_lt_of_le hmem.2 hrb⟩)
  have havoid := journey_avoids_modelBalls D hext hη hηd hx' hxband
  have hlev := D.hlevel x (f p + D.s₁ D.j * η - f x) (fun u hu i => havoid u hu i)
  rw [hlev]
  ring

end Work.Drive.N2
