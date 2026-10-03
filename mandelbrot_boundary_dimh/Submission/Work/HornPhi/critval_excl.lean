import Mathlib
import Submission.Work.Interfaces.HornParts
import Submission.Work.Horn.pushdown_critval_unique
import Submission.Work.HornPhi.crit_preimage_of_iterate

/-!
# AREA HORN-PHI: the critical points of `f₀^[N]` in `B` avoid `Φ⁻¹(ball y r)`

Shishikura, *The Hausdorff dimension of the boundary of the Mandelbrot set* (arXiv math/9201282),
Proposition 5.3 / the section construction of `Work.HornPhi.horn_phi` (Claim A).  Let `f₀ ∈ 𝓕₀`
with immediate basin `B` and unique critical point `c ∈ B`, and let `(φ₀, Φ₀)` be the §4.1
coordinates (`d : ParabData f₀ D₀`).  The Fatou coordinate `Φ₀` is a *translation by `1`* along the
forward orbit in `B`, so the critical values of the iterate `f₀^[N]` on `B` are pushed to the
discrete set `Φ₀ c - ℕ`: if `(f₀^[N])' w = 0` with `w ∈ B`, then some `f₀^[j] w` (`j < N`) is the
critical point `c` (`Work.HornPhi.crit_preimage_of_iterate`), whence
`Φ₀ (f₀^[N] w) = Φ₀ c + (N - j)`, i.e. `Φ₀ (f₀^[N] w) - N = Φ₀ c - j`.

Consequently, if the point `y` keeps the discrete set `Φ₀ c - ℕ` at distance `r > 0`, and the orbit
point `f₀^[N] w` has its `Φ₀`-value in `ball (y + N) r`, then `w` cannot be critical for `f₀^[N]`:
the shifted value `Φ₀ (f₀^[N] w) - N` would be both in `ball y r` and of the forbidden form
`Φ₀ c - j`.  This is the step "critical values of `f^N` in `B` lying over `W_N` are excluded"
of `HornPhi` (`horn_phi.lean`).
-/

namespace Work.HornPhi

open MandelDim Metric Set

noncomputable section

/-- A ball is preserved by shifting the centre by a natural number: `z ∈ ball (y + N) r` implies
`z - N ∈ ball y r`.  (The step "`Φ₀ c - k ∈ ball (y + N) r` gives `Φ₀ c - (k - N) ∈ ball y r`".) -/
theorem mem_ball_sub_natCast {y z : ℂ} {r : ℝ} {N : ℕ}
    (h : z ∈ Metric.ball (y + N) r) : z - (N : ℂ) ∈ Metric.ball y r := by
  rw [Metric.mem_ball, dist_eq_norm] at h ⊢
  have h2 : z - (y + (N : ℂ)) = z - (N : ℂ) - y := by ring
  rwa [h2] at h

/-- **The critical points of `f₀^[N]` in the immediate basin do not lie over `ball y r`.**

`f₀ ∈ 𝓕₀` with immediate basin `B` and unique critical point `c ∈ B`, §4.1 data `d`.  If the
discrete set `Φ₀ c - ℕ` avoids the ball `ball y r` (with `r > 0`), then no point `w ∈ B` with
`Φ₀ (f₀^[N] w) ∈ ball (y + N) r` is a critical point of `f₀^[N]`. -/
theorem critval_excl {f₀ : ℂ → ℂ} {D₀ B : Set ℂ} {c : ℂ} {d : MandelDim.ParabData f₀ D₀}
    (h : MandelDim.IsF0Setup f₀ D₀ B c) {y : ℂ} {r : ℝ} (hr : 0 < r)
    (hav : ∀ k : ℕ, d.Φ c - (k : ℂ) ∉ Metric.ball y r)
    {N : ℕ} {w : ℂ} (hwB : w ∈ B)
    (hwball : d.Φ ((f₀^[N]) w) ∈ Metric.ball (y + N) r) :
    deriv (f₀^[N]) w ≠ 0 := by
  obtain ⟨hgerm, hB, _, _, huniq⟩ := h
  -- the orbit of `w` stays in `B` (forward invariance of an immediate basin)
  have hiter : ∀ n : ℕ, f₀^[n] w ∈ B := by
    intro n
    induction n with
    | zero => simpa using hwB
    | succ m ih => rw [Function.iterate_succ_apply']; exact hB.2.2.2.2.1 ih
  intro hderiv
  -- a critical point of the iterate is a backward image of the critical point `c`
  obtain ⟨j, hjN, hjc⟩ := crit_preimage_of_iterate hgerm hB huniq hwB hderiv
  -- `Φ₀` translates by `1` along the orbit, so `Φ₀ (f₀^[N] w) - N = Φ₀ c - j`
  have hshift := Work.Horn.critval_Phi_iterate d hB (hiter j) (N - j)
  have hcomp : f₀^[N - j] (f₀^[j] w) = f₀^[N] w := by
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel (le_of_lt hjN)]
  have hΦN : d.Φ (f₀^[N] w) = d.Φ c + ((N - j : ℕ) : ℂ) := by
    rw [← hcomp, ← hshift, hjc]
  -- shifting the `ball` back by `N` contradicts the avoidance hypothesis at `j`
  have hsub : d.Φ (f₀^[N] w) - (N : ℂ) = d.Φ c - (j : ℂ) := by
    rw [hΦN, Nat.cast_sub (le_of_lt hjN)]
    ring
  have hmem : d.Φ c - (j : ℂ) ∈ Metric.ball y r := by
    rw [← hsub]
    exact mem_ball_sub_natCast hwball
  exact (hav j) hmem

end

end Work.HornPhi
