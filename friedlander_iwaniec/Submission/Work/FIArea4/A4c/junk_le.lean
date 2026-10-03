import Mathlib
import Submission.Work.FIArea4.A4c.Defs
import Submission.Work.FIArea4.A6Crude
import Submission.Work.FIArea4.A6Ener3_le
import Submission.Work.FIArea4.A4c.card_pairs_junk_le
import Submission.Work.FIArea4.A4c.junkDsum_abs_le

namespace Work.FIArea4.A4c

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## The inner `d`-sum of the junk cut -/

/-- The inner `d`-sum of the junk cut for one pair `(z₁,z₂)`: the `(z₁,z₂)`-factor of
`Tcut (radN Pa) (junkCut X m) β`. -/
def junkDsum (X m : ℕ) (z1 z2 : GaussianInt) : ℝ :=
  ∑ d ∈ Work.FITop4.Sset z1 z2,
    ((Nat.totient d : ℝ) / (d : ℝ)) * junkCut X m z1 z2 d
      * (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2

/-! ## Elementary bounds on the data -/

/-- `1 ≤ Pa.τ`: `τ` dominates `(log x)^{A+124}` with `log x ≥ 1` and `A + 124 ≥ 0`. -/
lemma one_le_tau (Pa : Work.FITop.Params) : 1 ≤ Pa.τ := by
  have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
  have hlog1 : (1 : ℝ) ≤ Real.log (Pa.x : ℝ) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_three]
  have hexp : (0 : ℝ) ≤ Pa.A + 124 := by linarith [Pa.hA]
  calc (1 : ℝ) = (1 : ℝ) ^ (Pa.A + 124) := (Real.one_rpow _).symm
    _ ≤ (Real.log (Pa.x : ℝ)) ^ (Pa.A + 124) :=
        Real.rpow_le_rpow (by norm_num) hlog1 hexp
    _ ≤ Pa.τ := Pa.hτ1

/-- The (5.9) divisor clause of a round-6 coefficient at a support point. -/
lemma IsBetaCoeff6.dvd_card_le {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (h : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) {z : GaussianInt}
    (hz : β z ≠ 0) :
    (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ Pa.τ := by
  obtain ⟨q, p, -, -, -, -, -, -, -, -, -, -, hβ⟩ := h
  rw [hβ z] at hz
  by_cases hc : Work.FITop4.InPolarBox Pa φ z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
      (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ Work.FITop4.SameClass8 z z0
      ∧ Work.FITop4.IsAxisFree Pa z
  · exact hc.2.2.1
  · rw [if_neg hc] at hz; exact absurd rfl hz

/-- **A round-6 coefficient is bounded by `Pa.τ`**: `‖β z‖ ≤ τ(|z|²) ≤ Pa.τ` on the support and
`β z = 0` elsewhere. -/
lemma beta_norm_le_tau {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (h : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) (z : GaussianInt) :
    ‖β z‖ ≤ Pa.τ := by
  rcases eq_or_ne (β z) 0 with h0 | hne
  · rw [h0, norm_zero]
    linarith [one_le_tau Pa]
  · exact le_trans (Work.FIArea4.IsBetaCoeff6_norm_le Pa φ z0 β h z)
      (IsBetaCoeff6.dvd_card_le h hne)

/-- The pointwise size of `logFac6` on the inner box. -/
lemma logFac6_abs_le_boxN (Pa : Work.FITop.Params) {z1 z2 : GaussianInt}
    (hz1 : z1 ∈ Work.FITop.boxN Pa) (hz2 : z2 ∈ Work.FITop.boxN Pa) :
    |Work.FITop4.logFac6 z1 z2| ≤ 40 * (Real.log (4 * Pa.N) + 1) :=
  Work.FIArea4.a6_logFac6_abs_le Pa.N (by exact_mod_cast Pa.hN1) z1 z2
    (Work.FIArea4.a6_mem_boxN_gnorm_le Pa hz1) (Work.FIArea4.a6_mem_boxN_gnorm_le Pa hz2)

/-! ## The `(z₁,z₂)`-summand of `Tcut (junkCut X m)` -/

/-- The `(z₁,z₂)`-summand of `Tcut` with the junk cut: the coprimality cut times `β z₁ β̄ z₂` times
the inner `d`-sum. -/
def junkInner (X m : ℕ) (β : GaussianInt → ℂ) (z1 z2 : GaussianInt) : ℂ :=
  if Work.FIPlan.GaussCoprime z1 z2 then
    β z1 * star (β z2) * ((junkDsum X m z1 z2 : ℝ) : ℂ) else 0

/-- `Tcut` with the junk cut, as an ordered-pair sum of `junkInner`. -/
lemma tcut_junk_eq (Rz : ℤ) (X m : ℕ) (β : GaussianInt → ℂ) :
    Work.FITop4.Tcut Rz (junkCut X m) β
      = 2 * ∑ z1 ∈ Work.FIPlan.gBox Rz, ∑ z2 ∈ Work.FIPlan.gBox Rz,
          junkInner X m β z1 z2 := by
  rw [Work.FIArea4.Tcut_eq_sum_ofReal]
  congr 1

/-- **A double sum of an indicator times a constant is the constant times a cardinality.** -/
lemma sum_sum_mul_ite_card (s : Finset GaussianInt) (P : GaussianInt → GaussianInt → Prop)
    [DecidableRel P] (c d : ℝ) :
    (∑ z1 ∈ s, ∑ z2 ∈ s, c * (if P z1 z2 then d else 0))
      = c * d * (((s.product s).filter (fun p : GaussianInt × GaussianInt => P p.1 p.2)).card : ℝ) := by
  have h1 : ∀ z1 : GaussianInt, (∑ z2 ∈ s, c * (if P z1 z2 then d else 0))
      = c * d * ((s.filter (fun z2 => P z1 z2)).card : ℝ) := by
    intro z1
    rw [← Finset.mul_sum, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    ring
  have h3 : ((s.product s).filter (fun p : GaussianInt × GaussianInt => P p.1 p.2)).card
      = ∑ z1 ∈ s, (s.filter (fun z2 => P z1 z2)).card := by
    rw [Finset.product_eq_sprod, Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl (fun z1 _ => ?_)
    rw [Finset.card_filter]
  have e2 : (∑ z1 ∈ s, ((s.filter (fun z2 => P z1 z2)).card : ℝ))
      = (((s.product s).filter (fun p : GaussianInt × GaussianInt => P p.1 p.2)).card : ℝ) := by
    rw [← Nat.cast_sum, ← h3]
  calc (∑ z1 ∈ s, ∑ z2 ∈ s, c * (if P z1 z2 then d else 0))
      = ∑ z1 ∈ s, c * d * ((s.filter (fun z2 => P z1 z2)).card : ℝ) :=
        Finset.sum_congr rfl (fun z1 _ => h1 z1)
    _ = c * d * (∑ z1 ∈ s, ((s.filter (fun z2 => P z1 z2)).card : ℝ)) := by
        rw [Finset.mul_sum]
    _ = c * d * (((s.product s).filter
          (fun p : GaussianInt × GaussianInt => P p.1 p.2)).card : ℝ) := by
        rw [e2]

/-- **The crude bound for the junk cut** (design `Submission/Work/FIArea4/AREA4_ENGINES_LEAD.md`
§3.3, node N7).

`junkCut X m z1 z2 d = 1{m < d ∧ d ≤ X ∧ |Δ(z1,z2)| ≤ 4dm}`, so it is supported on `d ≤ X`
(at most `X` values of `d`, before the `4d ∣ |Δ|` filter of `Sset`) and `|Δ| ≤ 4dm < 4X²`.

Proof route: use `Work.FIArea4.Tcut_eq_sum_ofReal` (`Submission/Work/FIArea4/A6Setup.lean`), bound
the inner sum by the number of admissible triples times the pointwise size:
* `‖β z1‖ ‖β z2‖ ≤ Pa.τ ^ 2` — the support clause of `IsBetaCoeff6` gives
  `((gnorm z).divisors.card : ℝ) ≤ Pa.τ` and `IsBetaCoeff6 ⟹ IsPrimBoxCoeff ⟹ IsBoxCoeff` gives
  `‖β z‖ ≤ τ(gnorm z)`;
* `|Nat.totient d / d| ≤ 1`, `|ratioSym| ≤ 1` (`Work.FIArea4.a6_ratioSym_abs_le` or the analogous
  workspace lemma), `|logFac6 z1 z2| ≤ C (log N + 1)` (both `|Δ| ≥ 1` and
  `gnorm (z1*z2) ≤ (2N)²` give `|log (8√(gnorm (z1*z2))/|Δ|)| ≤ C(log N+1)`);
* the triple count: for `z1` with `β z1 ≠ 0` the primary condition `InPolarBox` gives
  `Re z1` odd hence `≠ 0`, and `|Δ| ≤ 4X²`; for fixed `z1` and each `k = |Δ|` with
  `1 ≤ |k| ≤ 4X²`, the equation `Re z1·Im z2 - Im z1·Re z2 = k` determines `Im z2` for each of the
  `≤ 2R+1` values of `Re z2` (`R = radN Pa ≤ 2√N + 1`); the `k = 0` solutions and the `z1`-count
  `≤ (2R+1)²` are absorbed by the same constant.  Hence the pair count is `≤ (2R+1)³·8X² ≤ C'X²N^{3/2}`
  and the triple count `≤ C'X³N^{3/2}`.  `∃ C` absorbs all constants (including the factor `2` of
  `Tcut`). -/
theorem junk_le : ∃ C : ℝ, 0 < C ∧ ∀ (Pa : Work.FITop.Params) (φ : ℝ) (z0 : GaussianInt)
    (β : GaussianInt → ℂ) (X m : ℕ), Work.FITop4.IsBetaCoeff6 Pa φ z0 β → 1 ≤ m → m < X →
    ‖Work.FITop4.Tcut (Work.FITop.radN Pa) (Work.FIArea4.A4c.junkCut X m) β‖
      ≤ C * Pa.τ ^ 2 * (X : ℝ) ^ 3 * Pa.N ^ ((3 : ℝ) / 2) * (Real.log Pa.N + 1) := by
  refine ⟨1000000000, by norm_num, ?_⟩
  intro Pa φ z0 β X m hβ hm1 hmX
  set Ns : ℝ := Pa.N ^ ((3 : ℝ) / 2) with hNs
  have hX1 : 1 ≤ X := by omega
  have hmle : m ≤ X := le_of_lt hmX
  have hN1 : (1 : ℝ) ≤ Pa.N := by exact_mod_cast Pa.hN1
  have hN0 : (0 : ℝ) ≤ Pa.N := le_trans zero_le_one hN1
  have hNpos : (0 : ℝ) < Pa.N := lt_of_lt_of_le zero_lt_one hN1
  have hτ1 : (1 : ℝ) ≤ Pa.τ := one_le_tau Pa
  have hτ0 : (0 : ℝ) ≤ Pa.τ := le_trans zero_le_one hτ1
  have hlogN : (0 : ℝ) ≤ Real.log Pa.N := Real.log_nonneg hN1
  have hNs0 : (0 : ℝ) ≤ Ns := by rw [hNs]; exact Real.rpow_nonneg hN0 _
  have hL0 : (0 : ℝ) ≤ 40 * (Real.log (4 * Pa.N) + 1) := by
    have : (0 : ℝ) ≤ Real.log (4 * Pa.N) := Real.log_nonneg (by linarith)
    linarith
  have hLle : 40 * (Real.log (4 * Pa.N) + 1) ≤ 120 * (Real.log Pa.N + 1) := by
    have hlog4 : Real.log (4 * Pa.N) = Real.log 4 + Real.log Pa.N :=
      Real.log_mul (by norm_num) (ne_of_gt hNpos)
    have hlog4le : Real.log (4 : ℝ) ≤ 2 := by
      have h1 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
      have h2 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
      linarith
    rw [hlog4]
    linarith
  -- the pair count
  have hcardle :
      ((((Work.FIPlan.gBox (Work.FITop.radN Pa)).product
          (Work.FIPlan.gBox (Work.FITop.radN Pa))).filter
          (fun p : GaussianInt × GaussianInt =>
            Work.FIPlan.absDelta p.1 p.2 ≤ 4 * X * X)).card : ℝ)
        ≤ 100000 * (X : ℝ) ^ 2 * Ns := by
    rw [hNs]; exact card_pairs_junk_le Pa X hX1
  -- the pointwise bound on one summand
  have hpoint : ∀ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
      ∀ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
      ‖junkInner X m β z1 z2‖
        ≤ Pa.τ * Pa.τ * (if Work.FIPlan.absDelta z1 z2 ≤ 4 * X * X then
            (X : ℝ) * (40 * (Real.log (4 * Pa.N) + 1)) else 0) := by
    intro z1 hz1 z2 hz2
    have hD := junkDsum_abs_le Pa X m hX1 hmle
      (by simpa only [Work.FITop.boxN] using hz1)
      (by simpa only [Work.FITop.boxN] using hz2)
    have hb1 : ‖β z1‖ ≤ Pa.τ := beta_norm_le_tau hβ z1
    have hb2 : ‖β z2‖ ≤ Pa.τ := beta_norm_le_tau hβ z2
    have hC0 : (0 : ℝ) ≤ (if Work.FIPlan.absDelta z1 z2 ≤ 4 * X * X then
        (X : ℝ) * (40 * (Real.log (4 * Pa.N) + 1)) else 0) := by
      split_ifs with h
      · exact mul_nonneg (Nat.cast_nonneg _) hL0
      · rfl
    by_cases hg : Work.FIPlan.GaussCoprime z1 z2
    · simp only [junkInner, hg, if_true]
      rw [norm_mul, norm_mul, norm_star]
      have hno : ‖((junkDsum X m z1 z2 : ℝ) : ℂ)‖ = |junkDsum X m z1 z2| := by
        have h1 : ‖((junkDsum X m z1 z2 : ℝ) : ℂ)‖
            = Real.sqrt (Complex.normSq ((junkDsum X m z1 z2 : ℝ) : ℂ)) := by
          rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
        rw [h1, Complex.normSq_ofReal, ← pow_two, Real.sqrt_sq_eq_abs]
      rw [hno]
      exact mul_le_mul (mul_le_mul hb1 hb2 (norm_nonneg _) hτ0) hD (abs_nonneg _)
        (mul_nonneg hτ0 hτ0)
    · simp only [junkInner, hg, if_false, norm_zero]
      exact mul_nonneg (mul_nonneg hτ0 hτ0) hC0
  -- the double sum
  have hnorm : ‖∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
        ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), junkInner X m β z1 z2‖
      ≤ ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
          ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
            (Pa.τ * Pa.τ * (if Work.FIPlan.absDelta z1 z2 ≤ 4 * X * X then
              (X : ℝ) * (40 * (Real.log (4 * Pa.N) + 1)) else 0)) := by
    calc ‖∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
            ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), junkInner X m β z1 z2‖
        ≤ ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
            ‖∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), junkInner X m β z1 z2‖ :=
          norm_sum_le _ _
      _ ≤ ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
            ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖junkInner X m β z1 z2‖ :=
          Finset.sum_le_sum (fun z1 _ => norm_sum_le _ _)
      _ ≤ ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
            ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
              (Pa.τ * Pa.τ * (if Work.FIPlan.absDelta z1 z2 ≤ 4 * X * X then
                (X : ℝ) * (40 * (Real.log (4 * Pa.N) + 1)) else 0)) :=
          Finset.sum_le_sum (fun z1 hz1 => Finset.sum_le_sum (fun z2 hz2 => hpoint z1 hz1 z2 hz2))
  -- the indicator sum is the constant times the cardinality
  have hsum_eq :
      (∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
        ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
          (Pa.τ * Pa.τ * (if Work.FIPlan.absDelta z1 z2 ≤ 4 * X * X then
            (X : ℝ) * (40 * (Real.log (4 * Pa.N) + 1)) else 0)))
        = (Pa.τ * Pa.τ * ((X : ℝ) * (40 * (Real.log (4 * Pa.N) + 1))))
          * ((((Work.FIPlan.gBox (Work.FITop.radN Pa)).product
              (Work.FIPlan.gBox (Work.FITop.radN Pa))).filter
              (fun p : GaussianInt × GaussianInt =>
                Work.FIPlan.absDelta p.1 p.2 ≤ 4 * X * X)).card : ℝ) :=
    sum_sum_mul_ite_card (Work.FIPlan.gBox (Work.FITop.radN Pa))
      (fun z1 z2 => Work.FIPlan.absDelta z1 z2 ≤ 4 * X * X)
      (Pa.τ * Pa.τ) ((X : ℝ) * (40 * (Real.log (4 * Pa.N) + 1)))
  -- the main chain
  have hmain : ‖Work.FITop4.Tcut (Work.FITop.radN Pa) (junkCut X m) β‖
      ≤ 2 * ((Pa.τ * Pa.τ * ((X : ℝ) * (40 * (Real.log (4 * Pa.N) + 1))))
          * (100000 * (X : ℝ) ^ 2 * Ns)) := by
    rw [tcut_junk_eq]
    rw [norm_mul]
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2]
    calc 2 * ‖∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
          ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), junkInner X m β z1 z2‖
        ≤ 2 * (∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
            ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
              (Pa.τ * Pa.τ * (if Work.FIPlan.absDelta z1 z2 ≤ 4 * X * X then
                (X : ℝ) * (40 * (Real.log (4 * Pa.N) + 1)) else 0))) :=
          mul_le_mul_of_nonneg_left hnorm (by norm_num)
      _ = 2 * ((Pa.τ * Pa.τ * ((X : ℝ) * (40 * (Real.log (4 * Pa.N) + 1))))
            * ((((Work.FIPlan.gBox (Work.FITop.radN Pa)).product
                (Work.FIPlan.gBox (Work.FITop.radN Pa))).filter
                (fun p : GaussianInt × GaussianInt =>
                  Work.FIPlan.absDelta p.1 p.2 ≤ 4 * X * X)).card : ℝ)) := by
          rw [hsum_eq]
      _ ≤ 2 * ((Pa.τ * Pa.τ * ((X : ℝ) * (40 * (Real.log (4 * Pa.N) + 1))))
            * (100000 * (X : ℝ) ^ 2 * Ns)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_left hcardle
            (mul_nonneg (mul_nonneg hτ0 hτ0) (mul_nonneg (Nat.cast_nonneg _) hL0))
  refine le_trans hmain ?_
  show 2 * ((Pa.τ * Pa.τ * ((X : ℝ) * (40 * (Real.log (4 * Pa.N) + 1))))
        * (100000 * (X : ℝ) ^ 2 * Ns))
      ≤ 1000000000 * Pa.τ ^ 2 * (X : ℝ) ^ 3 * Ns * (Real.log Pa.N + 1)
  have hkey : 2 * ((Pa.τ * Pa.τ * ((X : ℝ) * (40 * (Real.log (4 * Pa.N) + 1))))
        * (100000 * (X : ℝ) ^ 2 * Ns))
      = 200000 * (Pa.τ ^ 2 * ((X : ℝ) ^ 3
          * (Ns * (40 * (Real.log (4 * Pa.N) + 1))))) := by ring
  rw [hkey]
  have hkey2 : 200000 * (40 * (Real.log (4 * Pa.N) + 1)) ≤ 1000000000 * (Real.log Pa.N + 1) := by
    nlinarith [hLle, hlogN]
  have hnn : (0 : ℝ) ≤ Pa.τ ^ 2 * ((X : ℝ) ^ 3 * Ns) :=
    mul_nonneg (sq_nonneg _) (mul_nonneg (pow_nonneg (Nat.cast_nonneg X) 3) hNs0)
  calc 200000 * (Pa.τ ^ 2 * ((X : ℝ) ^ 3
          * (Ns * (40 * (Real.log (4 * Pa.N) + 1)))))
      = (Pa.τ ^ 2 * ((X : ℝ) ^ 3 * Ns))
          * (200000 * (40 * (Real.log (4 * Pa.N) + 1))) := by ring
    _ ≤ (Pa.τ ^ 2 * ((X : ℝ) ^ 3 * Ns))
          * (1000000000 * (Real.log Pa.N + 1)) :=
        mul_le_mul_of_nonneg_left hkey2 hnn
    _ = 1000000000 * Pa.τ ^ 2 * (X : ℝ) ^ 3 * Ns * (Real.log Pa.N + 1) := by ring

end

end Work.FIArea4.A4c
