import Mathlib
import Submission.Work.TMContract.Defs

/-!
# The invariant section relation for the almost Mathieu `m`-function

`amoM α lam E x` is AJ's `m(E,x) = lim_n S(x-α)⋯S(x-nα)·i` (AJ (3.10)–(3.11)), stated in
`TMContract.Defs` as a `limUnder`.  This file proves the section relation

  `S_E(x) · m(E,x) = m(E,x+α)`   (AJ (2.6), (4.12)),

i.e. `mob (tmC lam E x) (m x) = m (x+α)`, from the hypothesis that the backward iterates
`mob (backIterC α lam E n y) i` converge (with limit `m y`) — which is what Kotani theory
supplies for `0 < Im E`.

The two ingredients are

* the Möbius multiplicativity `mob (A*B) z = mob A (mob B z)`, valid as soon as
  `z ↦ mob B z` is finite at `z`, together with continuity of `z ↦ mob A z`;
* the shift identity `backIterC (n+1) (x+α) = tmC lam E x * backIterC n x`, from which
  `mob (backIterC (n+1) (x+α)) i = mob (tmC lam E x) (mob (backIterC n x) i)`:
  the LHS converges to `m (x+α)` and the RHS to `mob (tmC lam E x) (m x)`.

The finiteness/non-vanishing that the Möbius multiplicativity needs is supplied by a
Herglotz-type lower bound: for `0 < Im E` the approximants `mob (backIterC n y) i` have
imaginary part `≥ min 1 (Im E) > 0`, so no pole is hit and the limit `m y` is non-zero.
-/

open Work.TMContract Filter Topology

namespace Work.TMComp.MAnalytic

/-! ## 1. Möbius algebra of the transfer matrix -/

/-- Multiplicativity of the Möbius action, as soon as `mob B z` is finite.  The hypothesis
cannot be dropped: `mob` is total with junk value `0` at a pole. -/
theorem amoM_mob_mul {A B : Matrix (Fin 2) (Fin 2) ℂ} {z : ℂ}
    (h : B 1 0 * z + B 1 1 ≠ 0) : mob (A * B) z = mob A (mob B z) := by
  simp only [mob, Matrix.mul_apply, Fin.sum_univ_two]
  field_simp
  ring

/-- Continuity of the Möbius action away from its pole. -/
theorem amoM_mob_continuousAt (A : Matrix (Fin 2) (Fin 2) ℂ) {z : ℂ}
    (h : A 1 0 * z + A 1 1 ≠ 0) : ContinuousAt (mob A) z := by
  change ContinuousAt (fun w : ℂ => (A 0 0 * w + A 0 1) / (A 1 0 * w + A 1 1)) z
  exact ContinuousAt.div (by fun_prop) (by fun_prop) h

/-- The Möbius action of `tmC lam E y` is `z ↦ E - 2λ cos 2πy - 1/z`. -/
theorem amoM_mob_tmC (lam : ℝ) (E : ℂ) (y : ℝ) {z : ℂ} (hz : z ≠ 0) :
    mob (tmC lam E y) z = E - ((2 * lam * Real.cos (2 * Real.pi * y) : ℝ) : ℂ) - 1 / z := by
  have h1 : (tmC lam E y) 0 0 = E - ((2 * lam * Real.cos (2 * Real.pi * y) : ℝ) : ℂ) := by
    simp [tmC]
  have h2 : (tmC lam E y) 0 1 = -1 := by simp [tmC]
  have h3 : (tmC lam E y) 1 0 = 1 := by simp [tmC]
  have h4 : (tmC lam E y) 1 1 = 0 := by simp [tmC]
  rw [mob, h1, h2, h3, h4, one_mul, add_zero]
  field_simp
  ring

/-- `backIterC n x = S(x-α)S(x-2α)⋯S(x-nα)`, so shifting the argument to `x+α` and raising
`n` by one prepends the factor `S(x)`. -/
theorem amoM_backIterC_succ_shift (α lam : ℝ) (E : ℂ) (n : ℕ) (x : ℝ) :
    backIterC α lam E (n + 1) (x + α) = tmC lam E x * backIterC α lam E n x := by
  induction n generalizing x with
  | zero => simp [backIterC]
  | succ n ih =>
    rw [backIterC, ih, backIterC, ← mul_assoc]
    have harg : x + α - (↑(n + 1) + 1) * α = x - (↑n + 1) * α := by push_cast; ring
    rw [harg]

/-! ## 2. The approximants lie in the upper half plane, uniformly below -/

/-- Herglotz-type bound: when `0 < Im E`, every backward approximant
`mob (backIterC α lam E n y) i` has imaginary part at least `min 1 (Im E) > 0`.  (The value
`n = 0` gives `i`, whence the `1`.) -/
theorem amoM_mob_backIterC_im_lower {α lam : ℝ} {E : ℂ} (hE : 0 < E.im) (n : ℕ) (y : ℝ) :
    min 1 E.im ≤ (mob (backIterC α lam E n y) Complex.I).im := by
  induction n generalizing y with
  | zero =>
    have h0 : mob (backIterC α lam E 0 y) Complex.I = Complex.I := by
      rw [backIterC, mob]
      simp
    rw [h0, Complex.I_im]
    exact min_le_left _ _
  | succ n ih =>
    have hshift : backIterC α lam E (n + 1) y
        = tmC lam E (y - α) * backIterC α lam E n (y - α) := by
      simpa [show y - α + α = y by ring] using amoM_backIterC_succ_shift α lam E n (y - α)
    have hB : min 1 E.im ≤ (mob (backIterC α lam E n (y - α)) Complex.I).im := ih (y - α)
    have hc : 0 < min 1 E.im := lt_min one_pos hE
    have hwpos : 0 < (mob (backIterC α lam E n (y - α)) Complex.I).im := lt_of_lt_of_le hc hB
    have hw : mob (backIterC α lam E n (y - α)) Complex.I ≠ 0 := by
      intro h0
      rw [h0] at hwpos
      simp at hwpos
    have hD : (backIterC α lam E n (y - α)) 1 0 * Complex.I
        + (backIterC α lam E n (y - α)) 1 1 ≠ 0 := by
      intro h0
      exact hw (by simp [mob, h0])
    rw [hshift, amoM_mob_mul (A := tmC lam E (y - α))
      (B := backIterC α lam E n (y - α)) (z := Complex.I) hD]
    rw [amoM_mob_tmC lam E (y - α) hw]
    have him : (E - ((2 * lam * Real.cos (2 * Real.pi * (y - α)) : ℝ) : ℂ)
          - 1 / mob (backIterC α lam E n (y - α)) Complex.I).im
        = E.im + (mob (backIterC α lam E n (y - α)) Complex.I).im
            / Complex.normSq (mob (backIterC α lam E n (y - α)) Complex.I) := by
      rw [one_div, Complex.sub_im, Complex.sub_im, Complex.ofReal_im, Complex.inv_im]
      ring
    rw [him]
    have hnsq : 0 < Complex.normSq (mob (backIterC α lam E n (y - α)) Complex.I) :=
      Complex.normSq_pos.mpr hw
    have hq : 0 < (mob (backIterC α lam E n (y - α)) Complex.I).im
        / Complex.normSq (mob (backIterC α lam E n (y - α)) Complex.I) := div_pos hwpos hnsq
    exact le_trans (min_le_right _ _) (le_add_of_nonneg_right hq.le)

/-- The approximant `mob (backIterC α lam E n y) i` is never zero when `0 < Im E`. -/
theorem amoM_mob_backIterC_ne_zero {α lam : ℝ} {E : ℂ} (hE : 0 < E.im) (n : ℕ) (y : ℝ) :
    mob (backIterC α lam E n y) Complex.I ≠ 0 := by
  intro h0
  have h1 := amoM_mob_backIterC_im_lower (α := α) (lam := lam) hE n y
  rw [h0] at h1
  simp only [Complex.zero_im] at h1
  linarith [lt_min one_pos hE]

/-- The denominator of the Möbius action of `backIterC α lam E n y` at `i` does not vanish
when `0 < Im E` (so that `mob (backIterC α lam E n y) i` is not the point at infinity). -/
theorem amoM_backIterC_den_ne_zero {α lam : ℝ} {E : ℂ} (hE : 0 < E.im) (n : ℕ) (y : ℝ) :
    (backIterC α lam E n y) 1 0 * Complex.I + (backIterC α lam E n y) 1 1 ≠ 0 := by
  intro h0
  exact amoM_mob_backIterC_ne_zero (α := α) (lam := lam) hE n y (by simp [mob, h0])

/-! ## 3. The section relation -/

/-- **The invariant section of the almost Mathieu cocycle.**  If the backward approximants
converge with limit `m`, then `m` satisfies the section relation `S_E(x)·m(x) = m(x+α)`
(AJ (2.6), (4.12)).  No hypothesis on `α`, `λ` is needed; the hypothesis `0 < Im E` is what
makes the limit non-zero (`m` takes values in the upper half plane). -/
theorem amoM_section {α lam : ℝ} {E : ℂ} (hE : 0 < E.im) {m : ℝ → ℂ}
    (hm : ∀ y, Filter.Tendsto (fun n : ℕ => Work.TMContract.mob (Work.TMContract.backIterC α lam E n y) Complex.I) Filter.atTop (nhds (m y))) :
    ∀ x, Work.TMContract.mob (Work.TMContract.tmC lam E x) (m x) = m (x + α) := by
  -- the limit values lie in the upper half plane, hence are non-zero
  have hmim : ∀ y, 0 < (m y).im := by
    intro y
    have ht : Tendsto (fun n : ℕ => (mob (backIterC α lam E n y) Complex.I).im) atTop
        (nhds ((m y).im)) := by
      have h := (Complex.continuous_im.tendsto (m y)).comp (hm y)
      simpa [Function.comp_def] using h
    have hle : min 1 E.im ≤ (m y).im :=
      ge_of_tendsto' ht (fun n => amoM_mob_backIterC_im_lower hE n y)
    linarith [lt_min one_pos hE]
  intro x
  have hmx : m x ≠ 0 := by
    intro h0
    have h := hmim x
    rw [h0] at h
    simp at h
  have hden : (tmC lam E x) 1 0 * m x + (tmC lam E x) 1 1 ≠ 0 := by
    simpa [tmC] using hmx
  -- the sequence `n ↦ mob (backIterC (n+1) (x+α)) i` tends to `m (x+α)` ...
  have hlim₁ : Tendsto (fun n : ℕ => mob (backIterC α lam E (n + 1) (x + α)) Complex.I) atTop
      (nhds (m (x + α))) := by
    have h := (hm (x + α)).comp (Filter.tendsto_add_atTop_nat 1)
    simpa [Function.comp_def] using h
  -- ... and, by the shift identity, also to `mob (tmC lam E x) (m x)`.
  have hlim₂ : Tendsto (fun n : ℕ => mob (backIterC α lam E (n + 1) (x + α)) Complex.I) atTop
      (nhds (mob (tmC lam E x) (m x))) := by
    have hbase : Tendsto
        (fun n : ℕ => mob (tmC lam E x) (mob (backIterC α lam E n x) Complex.I)) atTop
        (nhds (mob (tmC lam E x) (m x))) :=
      ((amoM_mob_continuousAt (tmC lam E x) hden).tendsto).comp (hm x)
    refine Filter.Tendsto.congr ?_ hbase
    intro n
    have h := amoM_mob_mul (A := tmC lam E x) (B := backIterC α lam E n x)
      (z := Complex.I) (amoM_backIterC_den_ne_zero (α := α) (lam := lam) hE n x)
    rw [← h, amoM_backIterC_succ_shift]
  exact (tendsto_nhds_unique hlim₁ hlim₂).symm

end Work.TMComp.MAnalytic
