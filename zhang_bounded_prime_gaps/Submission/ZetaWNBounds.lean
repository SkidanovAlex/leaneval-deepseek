import Mathlib
import Submission.ZetaWN
import Submission.ZetaRatio
import Submission.CrudeKernelBound
import Submission.Commons.NumberTheory.Zeta.riemannZeta_norm_antitone_re

open scoped BigOperators Topology
open Filter

set_option linter.unusedVariables false

/-!
# P8 Lemma 4.1 (ii): the crude half-plane bounds for the modified zeta `ζ_WN`

Polymath8a, proof of Lemma 4.1, needs the *crude bounds*, valid for
`Re s ≥ 1 + 1/log x`:

    |ζ_WN(s)| , |ζ_WN(s)|⁻¹ ≤ ζ(1 + 1/log x) ≪ log x        (P8, p. 19)

where `ζ_WN(s) = ∏_{p ∤ WN}(1 − p⁻ˢ)⁻¹` is the modified zeta
(`zetaWN`, `Submission.ZetaWN`).  The inequality is obtained "by comparing the
factors in the Euler product": for any complex `s` with `Re s > 1`, at every
prime `p`,

   |(1 − p⁻ˢ)⁻¹| ≤ (1 − p^{−Re s})⁻¹ ,   |1 − p⁻ˢ| ≤ (1 − p^{−Re s})⁻¹ ,

because `|p⁻ˢ| = p^{−Re s}` and both bounds follow from
`‖1 − w‖ ≥ 1 − ‖w‖` (first) and `‖1 − w‖ ≤ (1 + ‖w‖) ≤ (1 − ‖w‖)⁻¹`
(second).  Multiplying over the allowed primes and letting the finite prime
range grow gives the half-plane bounds

    ‖ζ_q(s)‖ ≤ ‖ζ((Re s : ℂ))‖ ,   ‖ζ_q(s)⁻¹‖ ≤ ‖ζ((Re s : ℂ))‖ .

This module proves exactly those two statements (`zetaWN_norm_le_re`,
`zetaWN_inv_norm_le_re`) for every `q ≠ 0` and every `1 < s.re`; the passage
to the `ζ(1 + 1/log x)` form is the monotonicity of `‖ζ(σ:ℂ)‖` on the real
axis (`Commons.NumberTheory.Zeta.riemannZeta_norm_antitone_re`).

All kernel-verified, zero `sorry`.
-/

namespace Commons.NumberTheory.MaynardSieve

variable {s : ℂ}

/-! ## Per-prime norm estimates -/

/-- Reverse triangle inequality in the form needed below: for `‖w‖ < 1`,
`1 − ‖w‖ ≤ ‖1 − w‖`. -/
lemma norm_one_sub_ge_of_norm_lt {w : ℂ} (hw : ‖w‖ < 1) : 1 - ‖w‖ ≤ ‖1 - w‖ := by
  have h : (1 : ℝ) ≤ ‖1 - w‖ + ‖w‖ := by
    calc
      (1 : ℝ) = ‖(1 : ℂ)‖ := by simp
      _ = ‖(1 - w) + w‖ := by congr 1; ring
      _ ≤ ‖1 - w‖ + ‖w‖ := norm_add_le (1 - w) w
  linarith

/-- `‖(1 − w)⁻¹‖ ≤ (1 − ‖w‖)⁻¹` for `‖w‖ < 1`. -/
lemma norm_inv_one_sub_le_inv {w : ℂ} (hw : ‖w‖ < 1) :
    ‖(1 - w)⁻¹‖ ≤ (1 - ‖w‖)⁻¹ := by
  have h1 : 1 - ‖w‖ ≤ ‖1 - w‖ := norm_one_sub_ge_of_norm_lt hw
  have hpos : 0 < 1 - ‖w‖ := by linarith
  have hwz : 1 - w ≠ 0 := by
    intro hz
    have hle := h1
    rw [hz] at hle
    norm_num at hle
    linarith
  rw [norm_inv]
  exact (inv_le_inv₀ (norm_pos_iff.mpr hwz) hpos).mpr h1

/-- `‖1 − w‖ ≤ (1 − ‖w‖)⁻¹` for `‖w‖ < 1`. -/
lemma norm_one_sub_le_inv {w : ℂ} (hw : ‖w‖ < 1) : ‖1 - w‖ ≤ (1 - ‖w‖)⁻¹ := by
  have h1 : ‖1 - w‖ ≤ 1 + ‖w‖ := by simpa using norm_sub_le (1 : ℂ) w
  have hpos : 0 < 1 - ‖w‖ := by linarith
  have h2 : 1 + ‖w‖ ≤ (1 - ‖w‖)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hpos]
    nlinarith [sq_nonneg (‖w‖)]
  exact h1.trans h2

/-- The complex power of a natural base at a real exponent is the embedding of
the real power. -/
lemma cpow_real_embed (p : ℕ) (σ : ℝ) :
    (p : ℂ) ^ (-(σ : ℂ)) = Complex.ofReal ((p : ℝ) ^ (-σ)) := by
  rw [show (-(σ : ℂ)) = Complex.ofReal (-σ) by rw [Complex.ofReal_neg]]
  exact (Complex.ofReal_cpow (by positivity : 0 ≤ (p : ℝ)) (-σ)).symm

/-- Norm of the inverse of `1 − u` for a real `u ∈ [0,1)`. -/
lemma norm_inv_one_sub_real {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    ‖(1 - (u : ℂ))⁻¹‖ = (1 - u)⁻¹ := by
  have hnn : 0 ≤ 1 - u := by linarith
  have hneq : ‖(1 : ℂ) - (u : ℂ)‖ = 1 - u := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
    rw [Complex.norm_real, Real.norm_eq_abs]
    simp [abs_of_nonneg hnn]
  calc
    ‖(1 - (u : ℂ))⁻¹‖ = ‖(((1 : ℂ) - (u : ℂ)))⁻¹‖ := by rfl
    _ = ‖(1 : ℂ) - (u : ℂ)‖⁻¹ := by rw [norm_inv]
    _ = (1 - u)⁻¹ := by rw [hneq]

/-- `1 ≤ (1 − u)⁻¹` for a real `u ∈ [0,1)`. -/
lemma one_le_inv_one_sub {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) : 1 ≤ (1 - u)⁻¹ :=
  (one_le_inv₀ (by linarith : 0 < 1 - u)).mpr (by linarith)

/-- **Per-prime norm identity.**  For a prime `p ≥ 2` and `σ > 1`:

    ‖(1 − p^{−σ})⁻¹‖ = (1 − p^{−σ})⁻¹        (σ : ℂ in the left expression). -/
lemma perPrime_norm_eq (p : ℕ) (hp2 : 2 ≤ p) {σ : ℝ} (hσ : 1 < σ) :
    ‖(1 - (p : ℂ) ^ (-(σ : ℂ)))⁻¹‖ = (1 - (p : ℝ) ^ (-σ))⁻¹ := by
  rw [cpow_real_embed]
  have hp_gt1 : 1 < (p : ℝ) := by exact_mod_cast (by omega : 2 ≤ p)
  have hu1' : (p : ℝ) ^ (-σ) < 1 := by
    have hle : (p : ℝ) ^ (-σ) < (p : ℝ) ^ (0 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt hp_gt1 (by linarith : -σ < 0)
    simpa using hle
  exact norm_inv_one_sub_real (Real.rpow_nonneg (by positivity : 0 ≤ (p : ℝ)) (-σ)) hu1'

/-- `‖(p:ℂ)^{−s}‖ = p^{−s.re}`. -/
lemma norm_cpow_neg_re (p : ℕ) (hp : p ≠ 0) : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
  rw [norm_cpow_nat_eq hp (-s), Complex.neg_re]

/-- `‖(p:ℂ)^{−s}‖ < 1` for a prime `p ≥ 2` and `1 < s.re`. -/
lemma norm_cpow_neg_lt_one_of (p : ℕ) (hp2 : 2 ≤ p) (hs : 1 < s.re) :
    ‖(p : ℂ) ^ (-s)‖ < 1 := by
  rw [norm_cpow_neg_re p (by omega)]
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hlt : (p : ℝ) ^ (-s.re) < (p : ℝ) ^ (0 : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt hp1 (by linarith : -s.re < 0)
  simpa using hlt

/-- **Per-prime Euler-factor bound (inverted factor).**  For a prime `p ≥ 2`
and `1 < s.re`: `‖(1 − p⁻ˢ)⁻¹‖ ≤ ‖(1 − p^{−Re s})⁻¹‖`. -/
lemma perPrime_inv_norm_le (p : ℕ) (hp2 : 2 ≤ p) (hs : 1 < s.re) :
    ‖(1 - (p : ℂ) ^ (-s))⁻¹‖ ≤ ‖(1 - (p : ℂ) ^ (-(s.re : ℂ)))⁻¹‖ := by
  calc
    ‖(1 - (p : ℂ) ^ (-s))⁻¹‖ ≤ (1 - ‖(p : ℂ) ^ (-s)‖)⁻¹ :=
      norm_inv_one_sub_le_inv (norm_cpow_neg_lt_one_of p hp2 hs)
    _ = (1 - (p : ℝ) ^ (-s.re))⁻¹ := by rw [norm_cpow_neg_re p (by omega)]
    _ = ‖(1 - (p : ℂ) ^ (-(s.re : ℂ)))⁻¹‖ := (perPrime_norm_eq p hp2 hs).symm

/-- **Per-prime Euler-factor bound (numerator).**  For a prime `p ≥ 2` and
`1 < s.re`: `‖1 − p⁻ˢ‖ ≤ ‖(1 − p^{−Re s})⁻¹‖`. -/
lemma perPrime_norm_le (p : ℕ) (hp2 : 2 ≤ p) (hs : 1 < s.re) :
    ‖1 - (p : ℂ) ^ (-s)‖ ≤ ‖(1 - (p : ℂ) ^ (-(s.re : ℂ)))⁻¹‖ := by
  calc
    ‖1 - (p : ℂ) ^ (-s)‖ ≤ (1 - ‖(p : ℂ) ^ (-s)‖)⁻¹ :=
      norm_one_sub_le_inv (norm_cpow_neg_lt_one_of p hp2 hs)
    _ = (1 - (p : ℝ) ^ (-s.re))⁻¹ := by rw [norm_cpow_neg_re p (by omega)]
    _ = ‖(1 - (p : ℂ) ^ (-(s.re : ℂ)))⁻¹‖ := (perPrime_norm_eq p hp2 hs).symm

/-! ## Product comparisons -/

/-- A finite product of reals `≥ 1` is `≥ 1`. -/
lemma one_le_prod_of_forall_one_le (t : Finset ℕ) (f : ℕ → ℝ)
    (hf : ∀ p ∈ t, 1 ≤ f p) : 1 ≤ ∏ p ∈ t, f p := by
  have h := Finset.prod_le_prod₀ (s := t) (f := fun _ : ℕ => (1 : ℝ)) (g := f)
    (fun i _ => by norm_num) (fun i hi => hf i hi)
  simpa using h

/-- Enlarging the index set of a finite product with factors `≥ 1` increases
the product. -/
lemma prod_subset_le_of_one_le {s t : Finset ℕ} (hst : s ⊆ t) (f : ℕ → ℝ)
    (hf : ∀ p ∈ t, 1 ≤ f p) : ∏ p ∈ s, f p ≤ ∏ p ∈ t, f p := by
  classical
  have hdisj : Disjoint (t \ s) s := Finset.sdiff_disjoint
  have hunion : t \ s ∪ s = t := Finset.sdiff_union_of_subset hst
  have hD : 1 ≤ ∏ p ∈ t \ s, f p :=
    one_le_prod_of_forall_one_le _ _ (fun p hp => hf p (Finset.mem_sdiff.mp hp).1)
  have hSnn : 0 ≤ ∏ p ∈ s, f p :=
    Finset.prod_nonneg (fun p hp => by linarith [hf p (hst hp)])
  calc
    ∏ p ∈ s, f p = (∏ p ∈ s, f p) * 1 := by rw [mul_one]
    _ ≤ (∏ p ∈ s, f p) * (∏ p ∈ t \ s, f p) :=
        mul_le_mul_of_nonneg_left hD hSnn
    _ = (∏ p ∈ t \ s, f p) * (∏ p ∈ s, f p) := by ring
    _ = ∏ p ∈ t \ s ∪ s, f p := (Finset.prod_union hdisj).symm
    _ = ∏ p ∈ t, f p := by rw [hunion]

/-- Every prime in `n.primesBelow` is `≥ 2`. -/
lemma two_le_of_mem_primesBelow {p n : ℕ} (hp : p ∈ n.primesBelow) : 2 ≤ p :=
  Nat.Prime.two_le (Nat.prime_of_mem_primesBelow hp)

/-- The factors `‖(1 − p^{−Re s})⁻¹‖` are `≥ 1` at primes `p ≥ 2`. -/
lemma one_le_perPrime_factor (p : ℕ) (hp2 : 2 ≤ p) (hs : 1 < s.re) :
    1 ≤ ‖(1 - (p : ℂ) ^ (-(s.re : ℂ)))⁻¹‖ := by
  rw [perPrime_norm_eq p hp2 hs]
  refine one_le_inv_one_sub (Real.rpow_nonneg (by positivity : 0 ≤ (p : ℝ)) _) ?_
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hlt : (p : ℝ) ^ (-s.re) < (p : ℝ) ^ (0 : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt hp1 (by linarith : -s.re < 0)
  simpa using hlt

/-- **Partial-product bound, inverted factors.**  The finite Euler product of
`ζ_q` over the primes `p ∤ q` below `n` is bounded in norm by the full finite
Euler product of `ζ` at the real point `s.re`. -/
lemma partialProduct_norm_le (q n : ℕ) (hs : 1 < s.re) :
    ‖∏ p ∈ (n.primesBelow).filter (fun p => ¬ p ∣ q), (1 - (p : ℂ) ^ (-s))⁻¹‖ ≤
      ‖∏ p ∈ n.primesBelow, (1 - (p : ℂ) ^ (-(s.re : ℂ)))⁻¹‖ := by
  rw [Complex.norm_prod, Complex.norm_prod]
  refine (Finset.prod_le_prod₀ (s := (n.primesBelow).filter (fun p : ℕ => ¬ p ∣ q))
    (f := fun p : ℕ => ‖(1 - (p : ℂ) ^ (-s))⁻¹‖)
    (g := fun p : ℕ => ‖(1 - (p : ℂ) ^ (-(s.re : ℂ)))⁻¹‖)
    (fun i _ => norm_nonneg _) (fun i hi => ?_)).trans ?_
  · exact perPrime_inv_norm_le i (two_le_of_mem_primesBelow (Finset.mem_of_mem_filter i hi)) hs
  · exact prod_subset_le_of_one_le (Finset.filter_subset _ _) _
      (fun p hp => one_le_perPrime_factor p (two_le_of_mem_primesBelow hp) hs)

/-- **Partial-product bound, numerator factors.**  Same bound for the inverted
Euler product `∏_{p∤q}(1 − p⁻ˢ) → ζ_q(s)⁻¹`. -/
lemma partialInvProduct_norm_le (q n : ℕ) (hs : 1 < s.re) :
    ‖∏ p ∈ (n.primesBelow).filter (fun p => ¬ p ∣ q), (1 - (p : ℂ) ^ (-s))‖ ≤
      ‖∏ p ∈ n.primesBelow, (1 - (p : ℂ) ^ (-(s.re : ℂ)))⁻¹‖ := by
  rw [Complex.norm_prod, Complex.norm_prod]
  refine (Finset.prod_le_prod₀ (s := (n.primesBelow).filter (fun p : ℕ => ¬ p ∣ q))
    (f := fun p : ℕ => ‖1 - (p : ℂ) ^ (-s)‖)
    (g := fun p : ℕ => ‖(1 - (p : ℂ) ^ (-(s.re : ℂ)))⁻¹‖)
    (fun i _ => norm_nonneg _) (fun i hi => ?_)).trans ?_
  · exact perPrime_norm_le i (two_le_of_mem_primesBelow (Finset.mem_of_mem_filter i hi)) hs
  · exact prod_subset_le_of_one_le (Finset.filter_subset _ _) _
      (fun p hp => one_le_perPrime_factor p (two_le_of_mem_primesBelow hp) hs)

/-! ## The half-plane crude bounds -/

/-- **P8 Lemma 4.1, crude bound (direct factor).**  For `q ≠ 0` and
`1 < s.re`: `‖ζ_q(s)‖ ≤ ‖ζ((Re s : ℂ))‖`. -/
theorem zetaWN_norm_le_re (q : ℕ) (hq : q ≠ 0) (hs : 1 < s.re) :
    ‖zetaWN q s‖ ≤ ‖riemannZeta (((s.re : ℝ)) : ℂ)‖ := by
  have hseq := zetaWN_eulerProduct q hq (s := s) hs
  have hA := (continuous_norm.tendsto (zetaWN q s)).comp hseq
  have hs' : 1 < (((s.re : ℝ)) : ℂ).re := by simpa using hs
  have hB := (continuous_norm.tendsto (riemannZeta (((s.re : ℝ)) : ℂ))).comp
      (riemannZeta_eulerProduct (s := (((s.re : ℝ)) : ℂ)) hs')
  exact le_of_tendsto_of_tendsto' hA hB (fun n => partialProduct_norm_le q n hs)

/-- **P8 Lemma 4.1, crude bound (inverse factor).**  For `q ≠ 0` and
`1 < s.re`: `‖ζ_q(s)⁻¹‖ ≤ ‖ζ((Re s : ℂ))‖`. -/
theorem zetaWN_inv_norm_le_re (q : ℕ) (hq : q ≠ 0) (hs : 1 < s.re) :
    ‖(zetaWN q s)⁻¹‖ ≤ ‖riemannZeta (((s.re : ℝ)) : ℂ)‖ := by
  have hseq := eulerProduct_inv_zetaWN q hq (s := s) hs
  have hA := (continuous_norm.tendsto ((zetaWN q s)⁻¹)).comp hseq
  have hs' : 1 < (((s.re : ℝ)) : ℂ).re := by simpa using hs
  have hB := (continuous_norm.tendsto (riemannZeta (((s.re : ℝ)) : ℂ))).comp
      (riemannZeta_eulerProduct (s := (((s.re : ℝ)) : ℂ)) hs')
  exact le_of_tendsto_of_tendsto' hA hB (fun n => partialInvProduct_norm_le q n hs)

/-! ## The `ζ(1 + 1/log x)` form (Polymath8a, p. 19)

Combining the half-plane bounds with the monotonicity of `‖ζ(σ)‖` on the real
axis (`Commons.NumberTheory.Zeta.riemannZeta_norm_antitone_re`) gives the
paper's display `|ζ_WN(s)|, |ζ_WN(s)|⁻¹ ≤ ζ(1 + 1/log x) ≪ log x` for all `s`
with `1 + 1/log x ≤ Re s`. -/

/-- For `Re s ≥ 1 + δ` (`δ > 0`): `‖ζ_q(s)‖ ≤ ‖ζ(1+δ)‖`. -/
theorem zetaWN_norm_le_one_add (q : ℕ) (hq : q ≠ 0) {δ : ℝ} (hδ : 0 < δ) {s : ℂ}
    (hs : 1 + δ ≤ s.re) :
    ‖zetaWN q s‖ ≤ ‖riemannZeta (((1 + δ : ℝ)) : ℂ)‖ := by
  have hs1 : 1 < s.re := lt_of_lt_of_le (by linarith) hs
  exact (zetaWN_norm_le_re q hq hs1).trans
    (Commons.NumberTheory.Zeta.riemannZeta_norm_antitone_re (by linarith) hs)

/-- For `Re s ≥ 1 + δ` (`δ > 0`): `‖ζ_q(s)⁻¹‖ ≤ ‖ζ(1+δ)‖`. -/
theorem zetaWN_inv_norm_le_one_add (q : ℕ) (hq : q ≠ 0) {δ : ℝ} (hδ : 0 < δ) {s : ℂ}
    (hs : 1 + δ ≤ s.re) :
    ‖(zetaWN q s)⁻¹‖ ≤ ‖riemannZeta (((1 + δ : ℝ)) : ℂ)‖ := by
  have hs1 : 1 < s.re := lt_of_lt_of_le (by linarith) hs
  exact (zetaWN_inv_norm_le_re q hq hs1).trans
    (Commons.NumberTheory.Zeta.riemannZeta_norm_antitone_re (by linarith) hs)

/-- **Polymath8a's crude display.**  There is `C > 0` such that for all
sufficiently large `x` and every `s` with `1 + 1/log x ≤ Re s`,

    ‖ζ_q(s)‖ ≤ C·log x   and   ‖ζ_q(s)⁻¹‖ ≤ C·log x . -/
theorem zetaWN_norm_and_inv_norm_le_log_mul (q : ℕ) (hq : q ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop, ∀ s : ℂ,
      1 + 1 / Real.log (x : ℝ) ≤ s.re →
        ‖zetaWN q s‖ ≤ C * Real.log (x : ℝ) ∧
        ‖(zetaWN q s)⁻¹‖ ≤ C * Real.log (x : ℝ) := by
  rcases zeta_bound_near_one with ⟨C, hC, δ, hδ, hb⟩
  refine ⟨C, hC, ?_⟩
  filter_upwards [riemannZeta_one_add_inv_log_eventually C δ hC hδ hb,
    eventually_gt_atTop 1] with x hx hx1
  intro s hs
  have hlogpos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx1)
  have hηpos : 0 < 1 / Real.log (x : ℝ) := div_pos one_pos hlogpos
  have hζ : ‖riemannZeta (((1 + 1 / Real.log (x : ℝ) : ℝ)) : ℂ)‖ =
      ‖riemannZeta (1 + 1 / ((Real.log (x : ℝ) : ℝ) : ℂ))‖ := by
    congr 2
    push_cast
    ring
  constructor
  · calc
      ‖zetaWN q s‖ ≤ ‖riemannZeta (((1 + 1 / Real.log (x : ℝ) : ℝ)) : ℂ)‖ :=
        zetaWN_norm_le_one_add q hq hηpos hs
      _ = ‖riemannZeta (1 + 1 / ((Real.log (x : ℝ) : ℝ) : ℂ))‖ := hζ
      _ ≤ C * Real.log (x : ℝ) := hx
  · calc
      ‖(zetaWN q s)⁻¹‖ ≤ ‖riemannZeta (((1 + 1 / Real.log (x : ℝ) : ℝ)) : ℂ)‖ :=
        zetaWN_inv_norm_le_one_add q hq hηpos hs
      _ = ‖riemannZeta (1 + 1 / ((Real.log (x : ℝ) : ℝ) : ℂ))‖ := hζ
      _ ≤ C * Real.log (x : ℝ) := hx

end Commons.NumberTheory.MaynardSieve
