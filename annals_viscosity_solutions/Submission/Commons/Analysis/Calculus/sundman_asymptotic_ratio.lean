import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.Topology.Algebra.Module.ModuleTopology

namespace Commons.Analysis.Calculus

open Filter Set

/-- Chain rule for `rpow` with a positive base, in the form used below. -/
private lemma hasDerivAt_rpow_comp {f : ℝ → ℝ} {f' x r : ℝ} (hf : HasDerivAt f f' x)
    (hx : f x ≠ 0) : HasDerivAt (fun s => (f s) ^ r) (r * (f x) ^ (r - 1) * f') x := by
  simpa [Function.comp_def, mul_assoc] using
    (Real.hasDerivAt_rpow_const (Or.inl hx) (p := r)).comp x hf

/-- **Sundman's asymptotic ratio.**

Let `f` be a `C²` function on `(0, ε)` with `f > 0`, `f' ≥ 0` and `f(t) → 0` as `t → 0⁺`, satisfying
the two differential inequalities

* `(f')² ≤ b·f·f'' + c·f`  (Ostrogradsky-type inequality, `2 < b`), and
* `d ≤ f''·f^((b-2)/b)`  (`0 < d`, a positive lower bound for `f'' f^{(b-2)/b}`).

Then the ratio `(f')² / f^(2/b)` has a *positive* limit as `t → 0⁺`.

The proof rests on two one-sided monotonicity facts:

* `W t = (f')² - b·d·f^(2/b)` is nondecreasing (this uses only the second inequality), and its
  `liminf` at `0⁺` is `≥ 0` because `W ≥ -b·d·f^(2/b) → 0`; hence `(f')² ≥ b·d·f^(2/b)` and the
  limit, if it exists, is `≥ b·d > 0`.
* `Φ t = (f')²/f^(2/b) - b·d + (2c/(b-2))·f^((b-2)/b)` is nondecreasing (this uses only the first
  inequality), and is bounded below; a monotone bounded-below function has a limit at `0⁺`.

The ratio itself is then `Φ + b·d - (2c/(b-2))·f^((b-2)/b)`, and the last term tends to `0`. -/
theorem sundman_asymptotic_ratio {f : ℝ → ℝ} {b c d ε : ℝ} (hε : 0 < ε) (hb : 2 < b) (hd : 0 < d)
    (hf1 : ∀ t ∈ Set.Ioo (0:ℝ) ε, HasDerivAt f (deriv f t) t)
    (hf2 : ∀ t ∈ Set.Ioo (0:ℝ) ε, HasDerivAt (deriv f) (deriv (deriv f) t) t)
    (hfpos : ∀ t ∈ Set.Ioo (0:ℝ) ε, 0 < f t)
    (hineq : ∀ t ∈ Set.Ioo (0:ℝ) ε, (deriv f t) ^ (2:ℕ) ≤ b * f t * deriv (deriv f) t + c * f t)
    (hmono : ∀ t ∈ Set.Ioo (0:ℝ) ε, 0 ≤ deriv f t)
    (hlim : Filter.Tendsto f (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0))
    (hbound : ∀ t ∈ Set.Ioo (0:ℝ) ε, d ≤ deriv (deriv f) t * (f t) ^ ((b - 2) / b)) :
    ∃ η : ℝ, 0 < η ∧
      Filter.Tendsto (fun t : ℝ => (deriv f t) ^ (2:ℕ) / (f t) ^ (2 / b))
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds η) := by
  ------------------------------------------------------------------ basic constants
  have hb0 : (0 : ℝ) < b := by linarith
  have hb2_ne : b - 2 ≠ 0 := by intro h; linarith
  set p : ℝ := 2 / b with hp
  set q : ℝ := (b - 2) / b with hq
  set k : ℝ := 2 * c / (b - 2) with hk
  have hp_pos : 0 < p := by rw [hp]; positivity
  have hq_pos : 0 < q := by rw [hq]; positivity
  have hq_eq : q = 1 - p := by rw [hp, hq]; field_simp
  have hp_lt_one : p < 1 := by linarith
  have hq1 : q - 1 = -p := by linarith
  have hpm1 : p - 1 = -q := by linarith
  have hpb : p * b = 2 := by rw [hp]; field_simp
  have hkq : k * q = p * c := by rw [hk, hq, hp]; field_simp
  have hδ : (0 : ℝ) < ε / 2 := by linarith
  ------------------------------------------------------------------ f is monotone
  have hfmono : MonotoneOn f (Ioo (0:ℝ) ε) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioo _ _) ?_ ?_ ?_
    · intro t ht
      have ht' : t ∈ Ioo (0:ℝ) ε := by simpa only [interior_Ioo] using ht
      exact (hf1 t ht').continuousAt.continuousWithinAt
    · intro t ht
      have ht' : t ∈ Ioo (0:ℝ) ε := by simpa only [interior_Ioo] using ht
      exact (hf1 t ht').differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : t ∈ Ioo (0:ℝ) ε := by simpa only [interior_Ioo] using ht
      rw [(hf1 t ht').deriv]
      exact hmono t ht'
  ------------------------------------------------------------------ STEP 1 : the function W
  let W : ℝ → ℝ := fun t => (deriv f t)^2 - (b*d) * (f t)^p
  have hWderiv : ∀ t ∈ Ioo (0:ℝ) (ε/2),
      HasDerivAt W (2 * deriv f t * deriv (deriv f) t - (b*d) * (p * (f t)^(p-1) * deriv f t)) t := by
    intro t ht
    have htε : t ∈ Ioo (0:ℝ) ε := ⟨ht.1, by linarith [ht.2]⟩
    have hft : 0 < f t := hfpos t htε
    have hA2 : HasDerivAt (fun s => (deriv f s)^2) (2 * deriv f t * deriv (deriv f) t) t := by
      have := (hf2 t htε).fun_pow 2
      simpa [mul_assoc] using this
    have hu : HasDerivAt (fun s => (f s)^p) (p * (f t)^(p-1) * deriv f t) t :=
      hasDerivAt_rpow_comp (hf1 t htε) (ne_of_gt hft) (r := p)
    have hres := hA2.sub (hu.const_mul (b*d))
    convert hres using 1
    all_goals rfl
  have hWdiff : ∀ t ∈ Ioo (0:ℝ) (ε/2),
      0 ≤ 2 * deriv f t * deriv (deriv f) t - (b*d) * (p * (f t)^(p-1) * deriv f t) := by
    intro t ht
    have htε : t ∈ Ioo (0:ℝ) ε := ⟨ht.1, by linarith [ht.2]⟩
    have hft : 0 < f t := hfpos t htε
    have hdf : 0 ≤ deriv f t := hmono t htε
    have hqd : d * (f t)^(p-1) ≤ deriv (deriv f) t := by
      have hpos : 0 < (f t)^q := Real.rpow_pos_of_pos hft q
      have h1 : d / (f t)^q ≤ deriv (deriv f) t := (div_le_iff₀ hpos).2 (hbound t htε)
      have hX : (f t)^(p-1) = ((f t)^q)⁻¹ := by
        rw [hpm1, Real.rpow_neg (le_of_lt hft) q]
      rw [div_eq_mul_inv, ← hX] at h1
      exact h1
    have hbp : b*d*p = 2*d := by nlinarith [hpb]
    have hkey : 0 ≤ 2 * deriv (deriv f) t - (b*d)*p*(f t)^(p-1) := by
      rw [hbp]; linarith
    have hfac : 2 * deriv f t * deriv (deriv f) t - (b*d) * (p * (f t)^(p-1) * deriv f t)
        = deriv f t * (2 * deriv (deriv f) t - (b*d)*p*(f t)^(p-1)) := by ring
    rw [hfac]
    exact mul_nonneg hdf hkey
  have hWmono : MonotoneOn W (Ioo (0:ℝ) (ε/2)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioo _ _) ?_ ?_ ?_
    · intro t ht
      have ht' : t ∈ Ioo (0:ℝ) (ε/2) := by simpa only [interior_Ioo] using ht
      exact (hWderiv t ht').continuousAt.continuousWithinAt
    · intro t ht
      have ht' : t ∈ Ioo (0:ℝ) (ε/2) := by simpa only [interior_Ioo] using ht
      exact (hWderiv t ht').differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : t ∈ Ioo (0:ℝ) (ε/2) := by simpa only [interior_Ioo] using ht
      rw [(hWderiv t ht').deriv]
      exact hWdiff t ht'
  -- W(t) >= 0 for small t, from monotonicity and the limit at 0
  have hWnn : ∀ t ∈ Ioo (0:ℝ) (ε/2), 0 ≤ W t := by
    intro t ht
    by_contra hcon
    rw [not_le] at hcon
    have hlt : 0 < -W t := by linarith
    have hlimpow : Tendsto (fun s => (b*d) * (f s)^p) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) := by
      have hc : Tendsto (fun x : ℝ => x^p) (nhds (0:ℝ)) (nhds 0) := by
        have hcont := (Real.continuousAt_rpow_const 0 p (Or.inr (le_of_lt hp_pos))).tendsto
        simpa [Real.zero_rpow (ne_of_gt hp_pos)] using hcont
      simpa [Function.comp_def] using (hc.comp hlim).const_mul (b*d)
    have hev1 : ∀ᶠ s in nhdsWithin (0:ℝ) (Ioi 0), (b*d) * (f s)^p < -W t :=
      hlimpow.eventually (isOpen_Iio.mem_nhds hlt)
    have hev2 : ∀ᶠ s in nhdsWithin (0:ℝ) (Ioi 0), s ∈ Ioo (0:ℝ) t :=
      Ioo_mem_nhdsGT ht.1
    obtain ⟨s, hs1, hs2⟩ := (hev1.and hev2).exists
    have hs_mem : s ∈ Ioo (0:ℝ) (ε/2) := ⟨hs2.1, by linarith [hs2.2, ht.2]⟩
    have hle : W s ≤ W t := hWmono hs_mem ht (le_of_lt hs2.2)
    have hWs : -(b*d) * (f s)^p ≤ W s := by
      simp only [W]
      nlinarith [sq_nonneg (deriv f s)]
    linarith
  ------------------------------------------------------------------ STEP 2 : the function Φ
  let Φ : ℝ → ℝ := fun t => (deriv f t)^2 * (f t)^(-p) - (b*d) + k*(f t)^q
  have hΦderiv : ∀ t ∈ Ioo (0:ℝ) (ε/2),
      HasDerivAt Φ (deriv f t * (f t)^(-p-1)
        * (2*(f t)*deriv (deriv f) t - p*(deriv f t)^2 + p*c*(f t))) t := by
    intro t ht
    have htε : t ∈ Ioo (0:ℝ) ε := ⟨ht.1, by linarith [ht.2]⟩
    have hft : 0 < f t := hfpos t htε
    have hA2 : HasDerivAt (fun s => (deriv f s)^2) (2 * deriv f t * deriv (deriv f) t) t := by
      have := (hf2 t htε).fun_pow 2
      simpa [mul_assoc] using this
    have hu : HasDerivAt (fun s => (f s)^(-p)) ((-p) * (f t)^(-p-1) * deriv f t) t :=
      hasDerivAt_rpow_comp (hf1 t htε) (ne_of_gt hft) (r := -p)
    have hw : HasDerivAt (fun s => (f s)^q) (q * (f t)^(q-1) * deriv f t) t :=
      hasDerivAt_rpow_comp (hf1 t htε) (ne_of_gt hft) (r := q)
    have hmain : HasDerivAt (fun s => (deriv f s)^2 * (f s)^(-p))
        ((2 * deriv f t * deriv (deriv f) t) * (f t)^(-p)
          + (deriv f t)^2 * ((-p) * (f t)^(-p-1) * deriv f t)) t := hA2.mul hu
    have hres := (hmain.sub_const (b*d)).add (hw.const_mul k)
    have e1 : (f t)^(-p) = (f t)^(-p-1) * (f t) := by
      have h : (-p : ℝ) = (-p - 1) + 1 := by ring
      conv_lhs => rw [h]
      rw [Real.rpow_add hft (-p-1) 1, Real.rpow_one]
    have e2 : (f t)^(q-1) = (f t)^(-p-1) * (f t) := by
      rw [hq1, e1]
    convert hres using 1
    all_goals first
      | rfl
      | (rw [e1, e2]
         rw [show k * (q * ((f t)^(-p-1) * (f t)) * deriv f t)
               = (k*q) * ((f t)^(-p-1) * (f t) * deriv f t) by ring, hkq]
         ring)
  have hΦdiff : ∀ t ∈ Ioo (0:ℝ) (ε/2), 0 ≤ deriv f t * (f t)^(-p-1)
        * (2*(f t)*deriv (deriv f) t - p*(deriv f t)^2 + p*c*(f t)) := by
    intro t ht
    have htε : t ∈ Ioo (0:ℝ) ε := ⟨ht.1, by linarith [ht.2]⟩
    have hft : 0 < f t := hfpos t htε
    have hdf : 0 ≤ deriv f t := hmono t htε
    have hv : 0 < (f t)^(-p-1) := Real.rpow_pos_of_pos hft (-p-1)
    have hbr : 0 ≤ 2*(f t)*deriv (deriv f) t - p*(deriv f t)^2 + p*c*(f t) := by
      have hi := hineq t htε
      have h2 : p * (deriv f t)^2 ≤ p * (b * f t * deriv (deriv f) t + c * f t) :=
        mul_le_mul_of_nonneg_left hi (le_of_lt hp_pos)
      have h3 : p * (b * f t * deriv (deriv f) t + c * f t)
          = 2 * f t * deriv (deriv f) t + p*c*(f t) := by
        rw [mul_add,
          show p * (b * f t * deriv (deriv f) t) = (p*b) * (f t * deriv (deriv f) t) by ring,
          hpb]
        ring
      linarith [h2, h3]
    exact mul_nonneg (mul_nonneg hdf (le_of_lt hv)) hbr
  have hΦmono : MonotoneOn Φ (Ioo (0:ℝ) (ε/2)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioo _ _) ?_ ?_ ?_
    · intro t ht
      have ht' : t ∈ Ioo (0:ℝ) (ε/2) := by simpa only [interior_Ioo] using ht
      exact (hΦderiv t ht').continuousAt.continuousWithinAt
    · intro t ht
      have ht' : t ∈ Ioo (0:ℝ) (ε/2) := by simpa only [interior_Ioo] using ht
      exact (hΦderiv t ht').differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : t ∈ Ioo (0:ℝ) (ε/2) := by simpa only [interior_Ioo] using ht
      rw [(hΦderiv t ht').deriv]
      exact hΦdiff t ht'
  have hΦbdd : BddBelow (Φ '' Ioo (0:ℝ) (ε/2)) := by
    rcases le_or_gt 0 k with hk0 | hk0
    · refine ⟨-(b*d), ?_⟩
      rintro y ⟨t, ht, rfl⟩
      have htε : t ∈ Ioo (0:ℝ) ε := ⟨ht.1, by linarith [ht.2]⟩
      have hft : 0 < f t := hfpos t htε
      simp only [Φ]
      have h1 : 0 ≤ (deriv f t)^2 * (f t)^(-p) :=
        mul_nonneg (sq_nonneg _) (le_of_lt (Real.rpow_pos_of_pos hft _))
      have h2 : 0 ≤ k * (f t)^q := mul_nonneg hk0 (Real.rpow_nonneg (le_of_lt hft) q)
      linarith
    · refine ⟨-(b*d) + k * (f (ε/2))^q, ?_⟩
      rintro y ⟨t, ht, rfl⟩
      have htε : t ∈ Ioo (0:ℝ) ε := ⟨ht.1, by linarith [ht.2]⟩
      have hhalf : (ε/2) ∈ Ioo (0:ℝ) ε := ⟨by linarith, by linarith⟩
      have hft : 0 < f t := hfpos t htε
      have hle : f t ≤ f (ε/2) := hfmono htε hhalf (le_of_lt ht.2)
      have hqle : (f t)^q ≤ (f (ε/2))^q :=
        Real.rpow_le_rpow (le_of_lt hft) hle (le_of_lt hq_pos)
      have hkqle : k * (f (ε/2))^q ≤ k * (f t)^q :=
        mul_le_mul_of_nonpos_left hqle (le_of_lt hk0)
      simp only [Φ]
      have h1 : 0 ≤ (deriv f t)^2 * (f t)^(-p) :=
        mul_nonneg (sq_nonneg _) (le_of_lt (Real.rpow_pos_of_pos hft _))
      linarith
  ------------------------------------------------------------------ STEP 3 : the limit
  have hΦlim : Tendsto Φ (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (sInf (Φ '' Ioo (0:ℝ) (ε/2)))) :=
    MonotoneOn.tendsto_nhdsWithin_Ioo_right (x := 0) (y := ε/2)
      ⟨ε/4, by constructor <;> linarith⟩ hΦmono hΦbdd
  have hpowlim : Tendsto (fun t => (f t)^q) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) := by
    have hc : Tendsto (fun x : ℝ => x^q) (nhds (0:ℝ)) (nhds 0) := by
      have hcont := (Real.continuousAt_rpow_const 0 q (Or.inr (le_of_lt hq_pos))).tendsto
      simpa [Real.zero_rpow (ne_of_gt hq_pos)] using hcont
    simpa [Function.comp_def] using hc.comp hlim
  have hcorr : Tendsto (fun t => (b*d) - k*(f t)^q) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (b*d)) := by
    have h1 : Tendsto (fun t => k*(f t)^q) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) := by
      simpa using hpowlim.const_mul k
    simpa using tendsto_const_nhds.sub h1
  have hsum : Tendsto (fun t => Φ t + ((b*d) - k*(f t)^q)) (nhdsWithin (0:ℝ) (Ioi 0))
      (nhds (sInf (Φ '' Ioo (0:ℝ) (ε/2)) + (b*d))) := hΦlim.add hcorr
  have hsum2 : Tendsto (fun t : ℝ => (deriv f t)^2 * (f t)^(-p)) (nhdsWithin (0:ℝ) (Ioi 0))
      (nhds (sInf (Φ '' Ioo (0:ℝ) (ε/2)) + (b*d))) := by
    refine hsum.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hδ] with t ht
    simp only [Φ]
    ring
  have htarget : Tendsto (fun t : ℝ => (deriv f t)^(2:ℕ) / (f t)^p)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (sInf (Φ '' Ioo (0:ℝ) (ε/2)) + (b*d))) := by
    refine hsum2.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hδ] with t ht
    have hft : 0 < f t := hfpos t ⟨ht.1, by linarith [ht.2]⟩
    rw [Real.rpow_neg (le_of_lt hft) p, div_eq_mul_inv]
  ------------------------------------------------------------------ STEP 4 : positivity of the limit
  have hbd_le : ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0),
      (b*d) ≤ (deriv f t)^(2:ℕ) / (f t)^p := by
    filter_upwards [Ioo_mem_nhdsGT hδ] with t ht
    have htε : t ∈ Ioo (0:ℝ) ε := ⟨ht.1, by linarith [ht.2]⟩
    have hft : 0 < f t := hfpos t htε
    have hWt : (b*d) * (f t)^p ≤ (deriv f t)^2 := by
      have := hWnn t ht
      simp only [W] at this
      linarith
    have h1 : (f t)^p * (f t)^(-p) = 1 := by
      rw [← Real.rpow_add hft p (-p), add_neg_cancel, Real.rpow_zero]
    have h2 : (b*d) ≤ (deriv f t)^2 * (f t)^(-p) := by
      calc (b*d) = (b*d) * ((f t)^p * (f t)^(-p)) := by rw [h1, mul_one]
        _ = (b*d) * (f t)^p * (f t)^(-p) := by ring
        _ ≤ (deriv f t)^2 * (f t)^(-p) :=
            mul_le_mul_of_nonneg_right hWt (le_of_lt (Real.rpow_pos_of_pos hft (-p)))
    rw [Real.rpow_neg (le_of_lt hft) p] at h2
    rw [div_eq_mul_inv]
    exact h2
  have hη_ge : (b*d) ≤ sInf (Φ '' Ioo (0:ℝ) (ε/2)) + (b*d) :=
    le_of_tendsto_of_tendsto tendsto_const_nhds htarget hbd_le
  exact ⟨sInf (Φ '' Ioo (0:ℝ) (ε/2)) + (b*d), lt_of_lt_of_le (mul_pos hb0 hd) hη_ge, htarget⟩

end Commons.Analysis.Calculus