import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Escape.Defs
import Submission.Work.Escape.Basic
import Submission.Work.Escape.tendsto_greenIter
import Submission.Work.Escape.tendsto_norm_iterate_atTop
import Submission.Work.Escape.mem_escapeRegion_iterate

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Positivity of the Green function of the tricorn

`G_c(z) > 0` exactly when the orbit of `z` under `T_c(w) = conj w ^ 2 + c` escapes to infinity.

The Green function is defined as the limit `G_f(z) = lim_n d^{-n} log⁺ ‖f^[n] z‖`
(`Work.Escape.green`), and the two implications are proved through the escape region
`escapeRegion A = {w | max 2 A < ‖w‖}` of the monic growth constant `A`:

* if an orbit ever enters `escapeRegion A`, it stays there and grows, and the partial Green
  functions lose at most `d^{-(n+1)} log 2` per step, which bounds the limit from below by a
  positive constant (`green_pos_of_mem_escapeRegion`);
* if the orbit is bounded, the partial Green functions are squeezed between `0` and
  `d^{-n} log⁺ M → 0`, so the limit vanishes (`green_eq_zero_of_bounded_gen`).

Together with `‖f^[n] z‖ → ∞ ↔ ∃ n, f^[n] z ∈ escapeRegion A` these give the equivalence.
-/

open Filter Function
open scoped Topology

namespace Work.Bottcher.Green

open LeanEval.ComplexAnalysis (Tantibar)

variable {f : ℂ → ℂ} {d : ℕ} {A : ℝ}

/-! ## The escaping region and divergence of orbits -/

/-- If some iterate of `z` lies in the escaping region `escapeRegion A`, then the norms of the
orbits of `z` tend to infinity.  (Escape is preserved forever, after which the norm grows at least
geometrically.) -/
theorem tendsto_norm_iterate_atTop_of_mem_escapeRegion (h : Work.Escape.MonicGrowth f d A)
    (hd : 2 ≤ d) {z : ℂ} {N : ℕ} (hN : (f^[N]) z ∈ Work.Escape.escapeRegion A) :
    Tendsto (fun n : ℕ => ‖(f^[n]) z‖) atTop atTop := by
  have ht := Work.Escape.tendsto_norm_iterate_atTop f d A h hd hN
  have hfun : (fun k : ℕ => ‖(f^[k]) ((f^[N]) z)‖) = fun k : ℕ => ‖(f^[k + N]) z‖ := by
    funext k
    rw [Function.iterate_add_apply]
  rw [hfun] at ht
  exact (tendsto_add_atTop_iff_nat N).mp ht

/-- If the orbit of `z` is unbounded then some iterate of `z` lies in the escaping region. -/
theorem exists_mem_escapeRegion_of_not_bounded {z : ℂ}
    (h : ¬ ∃ M : ℝ, ∀ n : ℕ, ‖(f^[n]) z‖ ≤ M) :
    ∃ N : ℕ, (f^[N]) z ∈ Work.Escape.escapeRegion A := by
  by_contra hc
  refine h ⟨max 2 A, fun n => ?_⟩
  by_contra hlt
  exact hc ⟨n, not_le.mp hlt⟩

/-! ## Vanishing of the Green function on bounded orbits -/

/-- If the orbit of `z` is bounded then the Green function of `z` vanishes. -/
theorem green_eq_zero_of_bounded_gen (h : Work.Escape.MonicGrowth f d A) (hd : 2 ≤ d) {z : ℂ}
    {M : ℝ} (hM : ∀ n : ℕ, ‖(f^[n]) z‖ ≤ M) : Work.Escape.green f d z = 0 := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hM1 : (1 : ℝ) ≤ max M 1 := le_max_right _ _
  have hle : ∀ n : ℕ, Work.Escape.greenIter f d z n ≤ ((d : ℝ)⁻¹) ^ n * Real.log (max M 1) := by
    intro n
    have h1 := Work.Escape.greenIter_le_of_norm_le (f := f) (d := d) (z := z) (n := n) hM1
      (le_trans (hM n) (le_max_left M 1))
    rw [← inv_pow] at h1
    exact h1
  have hupper : Tendsto (fun n : ℕ => ((d : ℝ)⁻¹) ^ n * Real.log (max M 1)) atTop (nhds 0) := by
    have h0 : (0 : ℝ) ≤ (d : ℝ)⁻¹ := by positivity
    have h1 : (d : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (by omega : 1 < d))
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).mul_const (Real.log (max M 1))
  have hsqueeze : Tendsto (fun n : ℕ => Work.Escape.greenIter f d z n) atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0)) hupper
      (fun n => Work.Escape.greenIter_nonneg f d z n) hle
  exact tendsto_nhds_unique (Work.Escape.tendsto_greenIter f d A h hd z) hsqueeze

/-! ## Step inequality for the partial Green functions -/

/-- **Step inequality.**  If the `n`-th iterate of `z` lies in the escaping region, then one step
of the partial Green functions loses at most `d^{-(n+1)} log 2`. -/
theorem greenIter_step_ge (h : Work.Escape.MonicGrowth f d A) (hd : 2 ≤ d) {z : ℂ} {n : ℕ}
    (hz : (f^[n]) z ∈ Work.Escape.escapeRegion A) :
    Work.Escape.greenIter f d z (n + 1) ≥
      Work.Escape.greenIter f d z n - ((d : ℝ) ^ (n + 1))⁻¹ * Real.log 2 := by
  have h1d : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : 1 ≤ d)
  have hd0 : (0 : ℝ) < (d : ℝ) := by linarith
  have hr2 : 2 < ‖(f^[n]) z‖ := Work.Escape.two_lt_norm_of_mem_escapeRegion hz
  have hrA : A < ‖(f^[n]) z‖ := Work.Escape.lt_norm_of_mem_escapeRegion hz
  have hr1 : (1 : ℝ) ≤ ‖(f^[n]) z‖ := by linarith
  have hr0 : (0 : ℝ) < ‖(f^[n]) z‖ := by linarith
  have hs_eq : (f^[n + 1]) z = f ((f^[n]) z) := Function.iterate_succ_apply' f n z
  have hle : ‖(f^[n]) z‖ ^ d - A ≤ ‖(f^[n + 1]) z‖ := by
    rw [hs_eq]
    exact h.le_norm _
  have hsq : ‖(f^[n]) z‖ ≤ ‖(f^[n]) z‖ ^ d := by
    calc ‖(f^[n]) z‖ = ‖(f^[n]) z‖ ^ 1 := (pow_one _).symm
      _ ≤ ‖(f^[n]) z‖ ^ d := pow_le_pow_right₀ hr1 (by omega : 1 ≤ d)
  have hrhalf : ‖(f^[n]) z‖ ≤ ‖(f^[n]) z‖ ^ d / 2 := by
    have h1 : ‖(f^[n]) z‖ ^ 2 ≤ ‖(f^[n]) z‖ ^ d := pow_le_pow_right₀ hr1 hd
    nlinarith [h1, hr2]
  have hhalf : ‖(f^[n]) z‖ ^ d / 2 ≤ ‖(f^[n + 1]) z‖ := by linarith
  have hs1 : (1 : ℝ) ≤ ‖(f^[n + 1]) z‖ := by nlinarith
  rw [Work.Escape.greenIter_eq_of_one_le (f := f) (d := d) (z := z) (n := n) hr1,
    Work.Escape.greenIter_eq_of_one_le (f := f) (d := d) (z := z) (n := n + 1) hs1]
  set r : ℝ := ‖(f^[n]) z‖ with hr
  set s : ℝ := ‖(f^[n + 1]) z‖ with hs
  have hr2' : 2 < r := by rw [hr]; exact hr2
  have hr0' : (0 : ℝ) < r := by linarith
  have hr1' : (1 : ℝ) ≤ r := by linarith
  have hlog : (d : ℝ) * Real.log r - Real.log 2 ≤ Real.log s := by
    have h1 : Real.log (r ^ d / 2) ≤ Real.log s := Real.log_le_log (by positivity) (by linarith)
    have h2 : Real.log (r ^ d / 2) = (d : ℝ) * Real.log r - Real.log 2 := by
      rw [Real.log_div (pow_ne_zero d (ne_of_gt hr0')) (by norm_num), Real.log_pow]
    linarith [h1, h2.le]
  have hkey : ((d : ℝ) ^ (n + 1))⁻¹ * ((d : ℝ) * Real.log r - Real.log 2)
      = ((d : ℝ) ^ n)⁻¹ * Real.log r - ((d : ℝ) ^ (n + 1))⁻¹ * Real.log 2 := by
    have hpow : ((d : ℝ) ^ (n + 1))⁻¹ * (d : ℝ) = ((d : ℝ) ^ n)⁻¹ := by
      rw [pow_succ, mul_inv, mul_assoc, inv_mul_cancel₀ (ne_of_gt hd0), mul_one]
    rw [mul_sub, ← mul_assoc, hpow]
  have hmul := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ ((d : ℝ) ^ (n + 1))⁻¹)
  linarith [hmul, hkey.le, hkey.ge]

/-! ## Positivity of the Green function on escaping orbits -/

/-- If some iterate of `z` lies in the escaping region, then the Green function of `z` is
positive.

Once the orbit has entered `escapeRegion A` the norms grow via `‖f w‖ ≥ ‖w‖^d - A ≥ ‖w‖^d / 2`
(here `A < ‖w‖/2`), i.e. `log ‖f w‖ ≥ d log ‖w‖ - log 2`; feeding this into the step inequality
shows that from that index on the partial Green functions stay above the positive constant
`d^{-N} (log ‖f^N z‖ - log 2 / (d - 1))`. -/
theorem green_pos_of_mem_escapeRegion (h : Work.Escape.MonicGrowth f d A) (hd : 2 ≤ d) {z : ℂ}
    {N : ℕ} (hN : (f^[N]) z ∈ Work.Escape.escapeRegion A) :
    0 < Work.Escape.green f d z := by
  have h1d : (1 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 1 < d)
  have hd0 : (d : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hdm1 : (d : ℝ) - 1 ≠ 0 := by linarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let R : ℝ := ‖(f^[N]) z‖
  have hR2 : 2 < R := Work.Escape.two_lt_norm_of_mem_escapeRegion hN
  have hR1 : (1 : ℝ) ≤ R := by linarith
  have hlogR : Real.log 2 < Real.log R := Real.log_lt_log (by norm_num) hR2
  have hLnonneg : 0 ≤ Real.log 2 / ((d : ℝ) - 1) := div_nonneg hlog2pos.le (by linarith)
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hLle : Real.log 2 / ((d : ℝ) - 1) ≤ Real.log 2 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < (d : ℝ) - 1)]
    nlinarith [hlog2pos]
  let C : ℝ := ((d : ℝ) ^ N)⁻¹ * (Real.log R - Real.log 2 / ((d : ℝ) - 1))
  have hCpos : 0 < C := by
    refine mul_pos (by positivity) ?_
    linarith
  -- every iterate from `N` on lies in the escaping region
  have hesc : ∀ k : ℕ, (f^[N + k]) z ∈ Work.Escape.escapeRegion A := by
    intro k
    have hk := Work.Escape.mem_escapeRegion_iterate f d A h hd hN k
    rw [← Function.iterate_add_apply] at hk
    simpa [Nat.add_comm] using hk
  -- the partial Green functions stay above `C`
  have hmain : ∀ k : ℕ, C + ((d : ℝ) ^ (N + k))⁻¹ * (Real.log 2 / ((d : ℝ) - 1))
      ≤ Work.Escape.greenIter f d z (N + k) := by
    intro k
    induction k with
    | zero =>
      have hgi : Work.Escape.greenIter f d z N = ((d : ℝ) ^ N)⁻¹ * Real.log R :=
        Work.Escape.greenIter_eq_of_one_le (f := f) (d := d) (z := z) (n := N) hR1
      simp only [Nat.add_zero]
      rw [hgi]
      dsimp only [C]
      have hsplit : ((d : ℝ) ^ N)⁻¹ * (Real.log R - Real.log 2 / ((d : ℝ) - 1))
          + ((d : ℝ) ^ N)⁻¹ * (Real.log 2 / ((d : ℝ) - 1))
          = ((d : ℝ) ^ N)⁻¹ * Real.log R := by ring
      rw [hsplit]
    | succ k ih =>
      show C + ((d : ℝ) ^ (N + k + 1))⁻¹ * (Real.log 2 / ((d : ℝ) - 1))
        ≤ Work.Escape.greenIter f d z (N + k + 1)
      have hstep : Work.Escape.greenIter f d z (N + k + 1) ≥
          Work.Escape.greenIter f d z (N + k) - ((d : ℝ) ^ (N + k + 1))⁻¹ * Real.log 2 :=
        greenIter_step_ge (f := f) (d := d) (A := A) h hd (hesc k)
      have hkey2 : (d : ℝ) * (Real.log 2 / ((d : ℝ) - 1))
          = Real.log 2 / ((d : ℝ) - 1) + Real.log 2 := by
        field_simp
        ring
      have hpow : ((d : ℝ) ^ (N + k + 1))⁻¹ * (d : ℝ) = ((d : ℝ) ^ (N + k))⁻¹ := by
        rw [pow_succ, mul_inv, mul_assoc, inv_mul_cancel₀ hd0, mul_one]
      have hkey : ((d : ℝ) ^ (N + k + 1))⁻¹ * (Real.log 2 / ((d : ℝ) - 1) + Real.log 2)
          = ((d : ℝ) ^ (N + k))⁻¹ * (Real.log 2 / ((d : ℝ) - 1)) := by
        rw [← hkey2, ← mul_assoc, hpow]
      have hkey' : ((d : ℝ) ^ (N + k + 1))⁻¹ * (Real.log 2 / ((d : ℝ) - 1))
            + ((d : ℝ) ^ (N + k + 1))⁻¹ * Real.log 2
          = ((d : ℝ) ^ (N + k))⁻¹ * (Real.log 2 / ((d : ℝ) - 1)) := by
        rw [← mul_add]
        exact hkey
      linarith [ih, hstep, hkey']
  have hevent : ∀ᶠ n : ℕ in atTop, C ≤ Work.Escape.greenIter f d z n := by
    rw [Filter.eventually_atTop]
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = N + k := ⟨n - N, by omega⟩
    have h1 := hmain k
    have h2 : 0 ≤ ((d : ℝ) ^ (N + k))⁻¹ * (Real.log 2 / ((d : ℝ) - 1)) :=
      mul_nonneg (by positivity) hLnonneg
    linarith
  have hlim : C ≤ Work.Escape.green f d z :=
    ge_of_tendsto (Work.Escape.tendsto_greenIter f d A h hd z) hevent
  linarith

/-! ## The main theorem -/

/-- **The Green function of the tricorn is positive exactly on escaping orbits.** -/
theorem green_pos_iff (c z : ℂ) :
    0 < Work.Bottcher.green c z ↔
      Filter.Tendsto (fun n : ℕ => ‖(LeanEval.ComplexAnalysis.Tantibar c)^[n] z‖)
        Filter.atTop Filter.atTop := by
  have hmg : Work.Escape.MonicGrowth (Tantibar c) 2 ‖c‖ := Work.Escape.monicGrowth_Tantibar c
  have hd : (2 : ℕ) ≤ 2 := le_rfl
  constructor
  · intro hpos
    by_contra hnot
    have hbdd : ∃ M : ℝ, ∀ n : ℕ, ‖(Tantibar c)^[n] z‖ ≤ M := by
      refine ⟨max 2 ‖c‖, fun n => ?_⟩
      refine le_of_not_gt fun hlt => hnot ?_
      exact tendsto_norm_iterate_atTop_of_mem_escapeRegion (f := Tantibar c) (d := 2)
        (A := ‖c‖) hmg hd hlt
    obtain ⟨M, hM⟩ := hbdd
    have h0 : Work.Escape.green (Tantibar c) 2 z = 0 :=
      green_eq_zero_of_bounded_gen (f := Tantibar c) (d := 2) (A := ‖c‖) hmg hd hM
    rw [Work.Bottcher.green_def, h0] at hpos
    exact lt_irrefl 0 hpos
  · intro hT
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hT.eventually_ge_atTop (max 2 ‖c‖ + 1))
    have hesc : (Tantibar c)^[N] z ∈ Work.Escape.escapeRegion ‖c‖ := by
      show max 2 ‖c‖ < ‖(Tantibar c)^[N] z‖
      have := hN N le_rfl
      linarith
    have hpos := green_pos_of_mem_escapeRegion (f := Tantibar c) (d := 2) (A := ‖c‖) hmg hd hesc
    simpa [Work.Bottcher.green_def] using hpos

end Work.Bottcher.Green
