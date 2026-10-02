import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The barrier cut off by a snail path: basic definitions and drift estimates

This file collects the *elementary* (no topology) part of the construction of Milnor's
invariant region `V₀` used in the proof of the Snail lemma (Milnor, *Dynamics in one complex
variable*, Lemma 13.2; for the application see `Multicorns are not path connected`).

Setting: `F : ℂ → ℂ` is differentiable and injective on the half plane `{z | z.re < X}`,
`F (Z + 2πi) = F Z + 2πi` on that half plane, and `F Z - Z → c` as `re Z → -∞`, where
`re c = 0 < im c`.  The path `P` satisfies `F (P t) = P (t+1)`, `(P t).re → -∞`,
`(P t).im → +∞` and `(P t).re < X`.

Contents:

* `exists_drift_bound` — on a sufficiently deep left half plane `F` raises the imaginary
  part by at least `c.im / 2`, keeps the real part below `X`, and moves the real part by less
  than `c.im / 4`.
* `exists_path_tail` — the tail of the path lies in that half plane.
* `path_step_height`, `path_height_growth` — the height of the path grows by at least
  `c.im / 2` per unit of time, hence linearly.
* `pathTail`, `leftCross` — the barrier (the image of the tail of the path) and its leftmost
  real part at a given height.

The remaining, topological, steps (the tail is closed; the leftmost point at a height is
attained and bounded on compact height bands; it tends to `-∞`; `F` maps the leftmost
component of the complement of the barrier into itself) are stated as separate lemmas.
-/

open Filter Set
open scoped Topology

namespace Work.LandLeaves.Snail

/-- **Drift, quantified.**  If `F Z - Z → c` as `re Z → -∞` and `0 < im c`, then on some left
half plane `re < X₀ ⊆ re < X` the map `F` raises the imaginary part by at least `c.im / 2`,
keeps the real part below `X`, and changes the real part by less than `c.im / 4`. -/
theorem exists_drift_bound {F : ℂ → ℂ} {X : ℝ} {c : ℂ} (hc_re : c.re = 0) (hc_im : 0 < c.im)
    (hdrift : Tendsto (fun Z : ℂ => F Z - Z) (comap Complex.re atBot) (nhds c)) :
    ∃ X₀ : ℝ, X₀ < X ∧ ∀ Z : ℂ, Z.re < X₀ →
      Z.im + c.im / 2 ≤ (F Z).im ∧ (F Z).re < X ∧ |(F Z).re - Z.re| < c.im / 4 := by
  set ε : ℝ := c.im / 4 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  have hEv : ∀ᶠ Z in comap Complex.re atBot, F Z - Z ∈ Metric.ball c ε :=
    hdrift.eventually (Metric.ball_mem_nhds c hεpos)
  rw [Filter.eventually_comap] at hEv
  rw [Filter.eventually_atBot] at hEv
  obtain ⟨a₀, ha₀⟩ := hEv
  have hXε : X - ε < X := by linarith
  refine ⟨min a₀ (X - ε), lt_of_le_of_lt (min_le_right _ _) hXε, ?_⟩
  intro Z hZ
  have hZa : Z.re < a₀ := lt_of_lt_of_le hZ (min_le_left _ _)
  have hZX : Z.re < X - ε := lt_of_lt_of_le hZ (min_le_right _ _)
  have hball : F Z - Z ∈ Metric.ball c ε := ha₀ Z.re (le_of_lt hZa) Z rfl
  rw [Metric.mem_ball, dist_eq_norm] at hball
  have hre : |(F Z - Z - c).re| < ε := lt_of_le_of_lt (Complex.abs_re_le_norm _) hball
  have him : |(F Z - Z - c).im| < ε := lt_of_le_of_lt (Complex.abs_im_le_norm _) hball
  have h1 : |(F Z).re - Z.re| < ε := by
    have h : (F Z - Z - c).re = (F Z).re - Z.re - c.re := by simp
    rw [h, hc_re, sub_zero] at hre
    exact hre
  have h2 : c.im - ε < (F Z).im - Z.im := by
    have h : (F Z - Z - c).im = (F Z).im - Z.im - c.im := by simp
    rw [h] at him
    have := abs_lt.mp him
    linarith [this.2]
  refine ⟨?_, ?_, ?_⟩
  · rw [hε] at h2; linarith
  · have := abs_lt.mp h1
    linarith [this.2, hZX]
  · rw [hε] at h1
    exact h1

/-- **The tail of the path lies in a deep left half plane.** -/
theorem exists_path_tail {P : ℝ → ℂ} {T X₀ : ℝ}
    (hPre : Tendsto (fun t : ℝ => (P t).re) atTop atBot) :
    ∃ t₀ : ℝ, T + 1 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t → (P t).re < X₀ := by
  have h : ∀ᶠ t : ℝ in atTop, (P t).re ≤ X₀ - 1 :=
    hPre.eventually (Filter.mem_atBot (X₀ - 1))
  rw [Filter.eventually_atTop] at h
  obtain ⟨a, ha⟩ := h
  refine ⟨max a (T + 1), le_max_right _ _, fun t ht => ?_⟩
  have h1 := ha t (le_trans (le_max_left _ _) ht)
  linarith

/-- **One time step of the path raises the height.** -/
theorem path_step_height {F : ℂ → ℂ} {P : ℝ → ℂ} {c : ℂ} {T X₀ t₀ : ℝ}
    (hheight : ∀ Z : ℂ, Z.re < X₀ → Z.im + c.im / 2 ≤ (F Z).im)
    (hPinv : ∀ t ∈ Set.Ici T, F (P t) = P (t + 1)) (htT : T ≤ t₀)
    (hPt : ∀ t : ℝ, t₀ ≤ t → (P t).re < X₀) {t : ℝ} (ht : t₀ ≤ t) :
    (P t).im + c.im / 2 ≤ (P (t + 1)).im := by
  have hT : t ∈ Set.Ici T := le_trans htT ht
  rw [← hPinv t hT]
  exact hheight (P t) (hPt t ht)

/-- **The height of the path grows linearly.** -/
theorem path_height_growth {F : ℂ → ℂ} {P : ℝ → ℂ} {c : ℂ} {T X₀ t₀ : ℝ}
    (hheight : ∀ Z : ℂ, Z.re < X₀ → Z.im + c.im / 2 ≤ (F Z).im)
    (hPinv : ∀ t ∈ Set.Ici T, F (P t) = P (t + 1)) (htT : T ≤ t₀)
    (hPt : ∀ t : ℝ, t₀ ≤ t → (P t).re < X₀) {r : ℝ} (hr : t₀ ≤ r) (n : ℕ) :
    (P r).im + n * (c.im / 2) ≤ (P (r + n)).im := by
  induction n with
  | zero => simp
  | succ k ih =>
      have hrk : t₀ ≤ r + k := by
        have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        linarith
      have h1 : (P (r + k)).im + c.im / 2 ≤ (P (r + k + 1)).im :=
        path_step_height hheight hPinv htT hPt hrk
      have h2 : (P r).im + k * (c.im / 2) ≤ (P (r + k)).im := ih
      have heq : r + ((k : ℝ) + 1) = r + k + 1 := by ring
      have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      rw [hcast, heq]
      linarith

/-- **The barrier**: the image of the tail of the path. -/
def pathTail (P : ℝ → ℂ) (t₀ : ℝ) : Set ℂ := P '' Set.Ici t₀

/-- **The leftmost point of the barrier at a given height** (`sInf` of the real parts of the
barrier points of height `h`; `+∞` if there are none). -/
noncomputable def leftCross (P : ℝ → ℂ) (t₀ : ℝ) (h : ℝ) : ℝ :=
  sInf ((fun W : ℂ => W.re) '' (pathTail P t₀ ∩ {W : ℂ | W.im = h}))

end Work.LandLeaves.Snail
