import Mathlib
import Submission.Work.Escape.Basic
import Submission.Work.Escape.tendsto_norm_iterate_atTop
import Submission.Work.Escape.mem_escapeRegion_iterate

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The partial Green functions converge to the Green function

For a `MonicGrowth f d A` map with `d ≥ 2`, the sequence of partial Green functions
`greenIter f d z n = d^{-n} log⁺ ‖f^[n] z‖` is convergent, with limit `green f d z`
(defined as `limUnder atTop (greenIter f d z)`).

Two regimes.

* If `z` lies in the filled Julia set `K_f` (bounded orbit), then `0 ≤ greenIter f d z n ≤
  d^{-n} log⁺ M` for a bound `M` on the orbit, so the partial Green functions tend to `0`.
* Otherwise the orbit escapes: some iterate of `z` enters the escaping region
  `{w | max 2 A < ‖w‖}`, after which the norms grow and the successive differences satisfy
  `|greenIter f d z (n+1) - greenIter f d z n| ≤ d^{-(n+1)} log 2`.  These bounds are summable,
  so the sequence converges.

In both cases `greenIter f d z` has an honest limit, which by `Filter.Tendsto.limUnder_eq`
coincides with its `limUnder`, i.e. with `green f d z`.
-/

open Filter Function Metric Set
open scoped Topology

noncomputable section

namespace Work.Escape

variable {f : ℂ → ℂ} {d : ℕ} {A : ℝ} {z : ℂ} {n : ℕ}

/-- Elementary logarithmic bound: if `r ≥ 2`, `A < r` and `r^d - A ≤ s ≤ r^d + A` with
`d ≥ 2`, then `|log (s / r^d)| ≤ log 2`, i.e. the ratio `s / r^d` stays within a factor `2`
of `1`. -/
private lemma log_ratio_abs_le {d : ℕ} (hd : 2 ≤ d) {A r s : ℝ}
    (hr2 : 2 < r) (hrA : A < r) (hs1 : r ^ d - A ≤ s) (hs2 : s ≤ r ^ d + A) :
    |Real.log (s / r ^ d)| ≤ Real.log 2 := by
  have hr1 : (1:ℝ) ≤ r := by linarith
  have hrd_pos : 0 < r ^ d := pow_pos (by linarith) d
  have hsq : r ^ 2 ≤ r ^ d := pow_le_pow_right₀ hr1 hd
  have hrd_half : r ≤ r ^ d / 2 := by nlinarith
  have hA_lt : A < r ^ d / 2 := by linarith
  have hlo : r ^ d / 2 < s := by linarith
  have hhi : s < 3 / 2 * r ^ d := by linarith
  have hratio_pos : 0 < s / r ^ d := div_pos (by linarith) hrd_pos
  have h1 : (r^d/2)/r^d = (1:ℝ)/2 := by field_simp
  have h2 : (3/2 * r^d)/r^d = (3:ℝ)/2 := by
    rw [mul_div_cancel_right₀ _ hrd_pos.ne']
  have hlo' : (1:ℝ)/2 < s / r ^ d := by
    rw [← h1]; exact div_lt_div_of_pos_right hlo hrd_pos
  have hhi' : s / r ^ d < 3 / 2 := by
    rw [← h2]; exact div_lt_div_of_pos_right hhi hrd_pos
  have hloglo : Real.log (1/2) ≤ Real.log (s / r ^ d) :=
    Real.log_le_log (by norm_num) hlo'.le
  have hloghi : Real.log (s / r ^ d) ≤ Real.log (3/2) :=
    Real.log_le_log hratio_pos hhi'.le
  have h32 : Real.log (3/2) ≤ Real.log 2 := Real.log_le_log (by norm_num) (by norm_num)
  have hhalf : Real.log (1/2) = - Real.log 2 := by
    rw [show (1:ℝ)/2 = 2⁻¹ by norm_num, Real.log_inv]
  rw [abs_le]
  constructor <;> linarith

/-- **Increment bound.**  Once the orbit of `z` is in the escaping region, the successive
differences of the partial Green functions are bounded by `d^{-(n+1)} log 2`. -/
private lemma greenIter_step_le (f : ℂ → ℂ) (d : ℕ) (A : ℝ) (h : MonicGrowth f d A) (hd : 2 ≤ d)
    {z : ℂ} {n : ℕ} (hz : (f^[n]) z ∈ escapeRegion A) :
    |greenIter f d z (n+1) - greenIter f d z n| ≤ ((d:ℝ)^(n+1))⁻¹ * Real.log 2 := by
  have hstep : (f^[n+1]) z = f ((f^[n]) z) := Function.iterate_succ_apply' f n z
  have hr2 : 2 < ‖(f^[n]) z‖ := two_lt_norm_of_mem_escapeRegion hz
  have hrA : A < ‖(f^[n]) z‖ := lt_norm_of_mem_escapeRegion hz
  have hr1 : (1:ℝ) ≤ ‖(f^[n]) z‖ := by linarith
  have hr_pos : 0 < ‖(f^[n]) z‖ := by linarith
  have hsq : ‖(f^[n]) z‖ ^ 2 ≤ ‖(f^[n]) z‖ ^ d := pow_le_pow_right₀ hr1 hd
  have hA_lt : A < ‖(f^[n]) z‖ ^ d / 2 := by nlinarith
  have hs_ge : ‖(f^[n]) z‖ ^ d - A ≤ ‖(f^[n+1]) z‖ := by
    rw [hstep]; exact h.le_norm _
  have hs_le : ‖(f^[n+1]) z‖ ≤ ‖(f^[n]) z‖ ^ d + A := by
    rw [hstep]; exact h.norm_le _
  have hs_pos : 0 < ‖(f^[n+1]) z‖ := by
    have : (0:ℝ) < ‖(f^[n]) z‖ ^ d := pow_pos hr_pos d
    linarith
  have hs1 : (1:ℝ) ≤ ‖(f^[n+1]) z‖ := by
    have : (1:ℝ) ≤ ‖(f^[n]) z‖ ^ d := by nlinarith [hsq, hr2, pow_pos hr_pos d]
    nlinarith
  have hlogr : logPos ‖(f^[n]) z‖ = Real.log ‖(f^[n]) z‖ := logPos_eq_log hr1
  have hlogs : logPos ‖(f^[n+1]) z‖ = Real.log ‖(f^[n+1]) z‖ := logPos_eq_log hs1
  have hratio : |Real.log (‖(f^[n+1]) z‖ / ‖(f^[n]) z‖ ^ d)| ≤ Real.log 2 :=
    log_ratio_abs_le hd hr2 hrA hs_ge hs_le
  have hid : greenIter f d z (n+1) - greenIter f d z n
      = ((d:ℝ)^(n+1))⁻¹ * Real.log (‖(f^[n+1]) z‖ / ‖(f^[n]) z‖ ^ d) := by
    rw [greenIter_def, greenIter_def, hlogr, hlogs]
    have hlogdiv : Real.log (‖(f^[n+1]) z‖ / ‖(f^[n]) z‖ ^ d)
        = Real.log ‖(f^[n+1]) z‖ - (d:ℝ) * Real.log ‖(f^[n]) z‖ := by
      rw [Real.log_div hs_pos.ne' (pow_ne_zero d hr_pos.ne'), Real.log_pow]
    rw [hlogdiv]
    rw [pow_succ, mul_inv]
    field_simp
  rw [hid, abs_mul]
  have hnn : 0 ≤ ((d:ℝ)^(n+1))⁻¹ := by positivity
  rw [abs_of_nonneg hnn]
  exact mul_le_mul_of_nonneg_left hratio hnn

/-- If the orbit of `z` is unbounded then some iterate of `z` lies in the escaping region
`{w | max 2 A < ‖w‖}`. -/
private lemma exists_mem_escapeRegion_of_not_mem_filledJulia (f : ℂ → ℂ) (A : ℝ) {z : ℂ}
    (hz : z ∉ filledJulia f) : ∃ N, (f^[N]) z ∈ escapeRegion A := by
  rw [mem_filledJulia] at hz
  rw [isBounded_iff_forall_norm_le] at hz
  push Not at hz
  obtain ⟨x, hxmem, hxgt⟩ := hz (max 2 A)
  obtain ⟨N, rfl⟩ := hxmem
  exact ⟨N, hxgt⟩

theorem tendsto_greenIter (f : ℂ → ℂ) (d : ℕ) (A : ℝ) (h : MonicGrowth f d A) (hd : 2 ≤ d) (z : ℂ) :
    Filter.Tendsto (greenIter f d z) Filter.atTop (nhds (green f d z)) := by
  have hconv : ∃ L, Filter.Tendsto (greenIter f d z) Filter.atTop (nhds L) := by
    rcases em (z ∈ filledJulia f) with hzK | hzK
    · obtain ⟨M, hM⟩ := norm_le_of_mem_filledJulia hzK
      refine ⟨0, ?_⟩
      have hM1 : (1:ℝ) ≤ max M 1 := le_max_right _ _
      have hle : ∀ n, greenIter f d z n ≤ ((d:ℝ)⁻¹)^n * Real.log (max M 1) := fun n => by
        have := greenIter_le_of_norm_le (f := f) (d := d) (z := z) (n := n) hM1
          (le_trans (hM n) (le_max_left _ _))
        simpa [inv_pow] using this
      have hupper : Filter.Tendsto (fun n : ℕ => ((d:ℝ)⁻¹)^n * Real.log (max M 1))
          Filter.atTop (nhds 0) := by
        have hnn : (0:ℝ) ≤ ((d:ℝ))⁻¹ := by positivity
        have hlt : ((d:ℝ))⁻¹ < 1 := by
          apply inv_lt_one_of_one_lt₀
          have : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
          linarith
        simpa using
          (tendsto_pow_atTop_nhds_zero_of_lt_one hnn hlt).mul_const (Real.log (max M 1))
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
        (fun n => greenIter_nonneg f d z n) hle
    · obtain ⟨N, hN⟩ := exists_mem_escapeRegion_of_not_mem_filledJulia f A hzK
      have hgec : ∀ᶠ k in Filter.atTop, (f^[k]) z ∈ escapeRegion A := by
        rw [Filter.eventually_atTop]
        refine ⟨N, fun k hk => ?_⟩
        have hiter : (f^[k]) z = (f^[k-N]) ((f^[N]) z) := by
          conv_lhs => rw [← Nat.sub_add_cancel hk]
          exact Function.iterate_add_apply f (k - N) N z
        rw [hiter]
        exact mem_escapeRegion_iterate f d A h hd hN (k - N)
      have hbnd : ∀ᶠ k in Filter.atTop,
          ‖greenIter f d z (k+1) - greenIter f d z k‖ ≤ ((d:ℝ)^(k+1))⁻¹ * Real.log 2 :=
        hgec.mono (fun k hk => by
          rw [Real.norm_eq_abs]
          exact greenIter_step_le f d A h hd hk)
      have hgsum : Summable (fun k : ℕ => ((d:ℝ)^(k+1))⁻¹ * Real.log 2) := by
        have hnn : (0:ℝ) ≤ ((d:ℝ))⁻¹ := by positivity
        have hlt : ((d:ℝ))⁻¹ < 1 := by
          apply inv_lt_one_of_one_lt₀
          have : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
          linarith
        have hgeo : Summable (fun k : ℕ => (((d:ℝ))⁻¹)^k) :=
          summable_geometric_of_lt_one hnn hlt
        have h2 := (hgeo.mul_left ((d:ℝ))⁻¹).mul_left (Real.log 2)
        simpa [pow_succ', mul_assoc, mul_comm, mul_left_comm] using h2
      have hincsum : Summable (fun k : ℕ => greenIter f d z (k+1) - greenIter f d z k) :=
        Summable.of_norm_bounded_eventually hgsum (by rw [Nat.cofinite_eq_atTop]; exact hbnd)
      refine ⟨greenIter f d z 0 + ∑' k, (greenIter f d z (k+1) - greenIter f d z k), ?_⟩
      have hpartial : Filter.Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n,
          (greenIter f d z (k+1) - greenIter f d z k)) Filter.atTop
          (nhds (∑' k, (greenIter f d z (k+1) - greenIter f d z k))) :=
        hincsum.hasSum.tendsto_sum_nat
      have hconst := hpartial.const_add (greenIter f d z 0)
      have hfun : greenIter f d z
          = fun n => greenIter f d z 0 + (∑ k ∈ Finset.range n,
              (greenIter f d z (k+1) - greenIter f d z k)) := by
        funext n
        rw [Finset.sum_range_sub (fun k => greenIter f d z k) n]
        ring
      nth_rewrite 1 [hfun]
      exact hconst
  obtain ⟨L, hL⟩ := hconv
  have hgreen : green f d z = L := by
    unfold green
    exact hL.limUnder_eq
  rw [hgreen]
  exact hL

end Work.Escape
