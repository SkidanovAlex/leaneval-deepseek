import Mathlib
import Submission.Work.FIChain.Defs
import Submission.Work.FIChain.AcountAtilC_ge_const_mul_rpow
import Submission.Work.FIChain.AcountAtilC_le_const_mul_rpow
import Submission.Commons.Analysis.Asymptotics.integral_one_div_Ioc_exp_mul
import Submission.Work.FIChain.S3plusC_aux
import Submission.Work.FIChain.S3plusC_lamPlus_identity
import Submission.Work.FIChain.mu_gtil_coprime_le
import Submission.Work.FIChain.S3plusC_route_defs
import Submission.Work.FIChain.FIgtil_tau_div_sum_le
import Submission.Work.FIChain.FIgtil_prime_sum_loglog
import Submission.Work.FIChain.FIgtil_prime_div_sqrt_sum
import Submission.Work.FIChain.mu_gtil_interval_le
import Submission.Work.FIChain.sum_divisors_reindex
import Submission.Work.FIChain.s3InnerInt_eq_integral_swap
import Submission.Work.FIChain.remainder_all_at_07
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.NormNum.RealSqrt
import Submission.Commons.NumberTheory.Sieve.sieve_mu_sum_coprime_powLog
import Submission.Work.FIChain.window_marginsC
import Submission.Work.FIChain.chainRangeFactsC
import Submission.Work.FIChain.Ad_block_eq_real
import Submission.Work.FIChain.s3InnerInt_eq_dsum
import Submission.Work.FIChain.Ad_atilc_split_real
import Submission.Work.FIChain.s3InnerInt_eq_split
import Submission.Work.FIChain.S3plusC_uIntegral_reduce
import Submission.Work.FIChain.s3RemPlus_defs

/-!
# `Submission.Work.FIChain.S3plusC_aux2` — the auxiliary lemmas of the `S3plusC` chapter

These are the elementary glue lemmas used by `Work.FIChain.S3plusC_zavg_le`: the un-reindexed
form of `S3plusC` (`S3plusC_eq_sum_eb`), the coprimality factorisations
(`FIgtil_mul_coprime`, `rhoOf_mul_coprime`), the fibre bound `sum_divisors_rhoOf_le` (with
`abs_rhoOf_le_card`), and the window-reduction lemmas for the `y`- and `z`-averages
(`integral_const_div_exp_mul`, `integral_abs_div_le_of_bound`, `S3plusC_yavg_le`), together with
the small arithmetic helper `log_sub_one_rpow_neg_le`.

They are kept in a `sorry`-free module of their own so that they can be imported (and reused) by
other files without dragging in the chapter's single outstanding `sorry`.
-/

namespace Work.FIChain


/-! ## Helpers for the corrected route — see `NOTES_S3plusC_route.md`, session-7 section.

The route (summary): un-reindex `S3plusC = Σ_{b>sy} μ(b) Σ_e ρ(eb)·I(eb)`, use the PROVED
`S3plusC_lamPlus_identity` and the Fubini step `s3InnerInt_eq_integral_swap` to write `I(ℓ)` as
`∫_1^{sz/Cm}(du/u) Σ_c ã(ℓc)ρ(c;u)`; substitute `u = t/(ℓCm)` and `z ↦ z_new := ℓz` (the `z`
of the target's `∫_{zc}^{e·zc}·dz/z` is an integration variable) so that the `(1.7)`-split
arguments become `⌊min(sc·z_new,x)⌋₊`, `⌊max(t,z_new)⌋₊` — **free of `e,b,d`**; then
`(2.4)` on the `b`-sum (after `ρ(eb) = Σ_{ν|eb}λ(ν)`, `ν=ν_eν_b`, `b = ν_b·b'`) and on the
`d`-sum, and `(R′)` on the `r̃`-part grouped by `ζ = ebd`.
-/
/-- For `y ≥ 3`: `(log (y-1))^{-6} ≤ 64·(log y)^{-6}`; equivalent to `y ≤ (y-1)²` via `log`. -/
lemma log_sub_one_rpow_neg_le (y : ℕ) (hy : 3 ≤ y) :
    (Real.log (((y - 1 : ℕ)) : ℝ)) ^ (-6 : ℝ) ≤ 64 * (Real.log (y : ℝ)) ^ (-6 : ℝ) := by
  have hy2 : 2 ≤ y - 1 := by omega
  have hcast : (((y - 1 : ℕ)) : ℝ) = (y : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ y)]; norm_num
  have hy3 : (3:ℝ) ≤ (y:ℝ) := by exact_mod_cast hy
  have hv0 : (0 : ℝ) < (y : ℝ) := by linarith
  have hvsq : (y : ℝ) ≤ (((y - 1 : ℕ)) : ℝ) ^ 2 := by
    rw [hcast]; nlinarith [hy3]
  have hlog : (Real.log (y:ℝ)) ≤ 2 * Real.log (((y - 1 : ℕ)) : ℝ) := by
    calc Real.log (y:ℝ) ≤ Real.log ((((y - 1 : ℕ)) : ℝ) ^ 2) := Real.log_le_log hv0 hvsq
      _ = 2 * Real.log (((y - 1 : ℕ)) : ℝ) := by rw [Real.log_pow]; ring
  have hhalf : Real.log (y:ℝ) / 2 ≤ Real.log (((y - 1 : ℕ)) : ℝ) := by linarith
  have hpos : 0 < Real.log (y:ℝ) / 2 := by
    have h : 0 < Real.log (y:ℝ) := Real.log_pos (by linarith [hy3])
    linarith
  have hmono := Real.rpow_le_rpow_of_nonpos hpos hhalf (by norm_num : (-6:ℝ) ≤ 0)
  have hkey : (Real.log (y:ℝ) / 2) ^ (-6 : ℝ) = 64 * (Real.log (y:ℝ)) ^ (-6 : ℝ) := by
    have h3 : Real.log (y:ℝ) / 2 = (1/2) * Real.log (y:ℝ) := by ring
    rw [h3, Real.mul_rpow (by norm_num : (0:ℝ) ≤ 1/2) (Real.log_nonneg (by linarith [hy3]))]
    rw [show ((1:ℝ)/2)^(-6:ℝ) = (64:ℝ) by norm_num [Real.rpow_neg, Real.rpow_natCast]]
  linarith [hmono, hkey]

/-- Interval splitting: `Σ_{a..b} = Σ_{1..b} − Σ_{1..a−1}` for `1 ≤ a ≤ b+1`. -/
lemma sum_Icc_eq_sub (g : ℕ → ℝ) (a b : ℕ) (h : 1 ≤ a) (h2 : a ≤ b + 1) :
    ∑ d ∈ Finset.Icc a b, g d
      = (∑ d ∈ Finset.Icc 1 b, g d) - (∑ d ∈ Finset.Icc 1 (a - 1), g d) := by
  have hsub : Finset.Icc 1 (a - 1) ⊆ Finset.Icc 1 b := by
    intro d hd
    rw [Finset.mem_Icc] at hd ⊢
    exact ⟨hd.1, by omega⟩
  have hsdiff : Finset.Icc 1 b \ Finset.Icc 1 (a - 1) = Finset.Icc a b := by
    ext d
    rw [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Icc, Finset.mem_Icc]
    omega
  have hsum := Finset.sum_sdiff (f := g) hsub
  rw [hsdiff] at hsum
  linarith [hsum]

/-- **The inner sum vanishes past `N`** — the first obstruction to un-reindexing `S3plusC`:
`S3plusInnerC`'s filter asks for `z < c`, `c ≤ sz` and `ℓ*c ≤ N` with `c ≥ 1`, so `ℓ ≤ N`. -/
lemma S3plusInnerC_eq_zero_of_lt (a : ℕ → ℝ) (N ℓ : ℕ) (z sz C : ℝ) (h : N < ℓ) :
    S3plusInnerC a N ℓ z sz C = 0 := by
  rw [S3plusInnerC]
  refine Finset.sum_eq_zero (fun c hc => ?_)
  rw [Finset.mem_filter, Finset.mem_Icc] at hc
  obtain ⟨⟨hc1, -⟩, -, -, hcl⟩ := hc
  have h1 : ℓ * 1 ≤ ℓ * c := Nat.mul_le_mul_left ℓ hc1
  rw [mul_one] at h1
  omega

/-- **The un-reindexed form of `S3plusC`** (the companion's `ℓ = eb` split): the outer weight
`Σ_{b | ℓ, b > sy} μ b` becomes an *interval* sum over `b > sy` — the form the Möbius
cancellation `(2.4)` can consume.  (Uses `S3plusInnerC_eq_zero_of_lt` so that the `e`-range may be
taken as all of `Icc 1 N`.) -/
theorem S3plusC_eq_sum_eb (a lam : ℕ → ℝ) (N : ℕ) (z sy sz C : ℝ) :
    S3plusC a lam N z sy sz C
      = ∑ b ∈ (Finset.Icc 1 N).filter (fun b => sy < ((b : ℕ) : ℝ)),
          (ArithmeticFunction.moebius b : ℝ) *
            ∑ e ∈ Finset.Icc 1 N,
              Submission.ASP.rhoOf lam (b * e) * S3plusInnerC a N (b * e) z sz C := by
  rw [S3plusC]
  trans ∑ ℓ ∈ Finset.Icc 1 N,
      (∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
        (ArithmeticFunction.moebius b : ℝ))
        * (Submission.ASP.rhoOf lam ℓ * S3plusInnerC a N ℓ z sz C)
  · refine Finset.sum_congr rfl (fun ℓ _ => ?_); ring
  · exact sum_divisors_reindex
      (fun ℓ => Submission.ASP.rhoOf lam ℓ * S3plusInnerC a N ℓ z sz C) N sy
      (fun ℓ hℓ => by rw [S3plusInnerC_eq_zero_of_lt a N ℓ z sz C hℓ, mul_zero])


/-! ## The `(2.4)`-application on the `b`-sum: the two algebraic moves. -/

/-- **Weight factorisation.**  For `b` coprime to `e*l`, `g̃(e*b*l) = g̃(e*l)·g̃(b)` — this is what
makes the `b`-weight *constant*, the form `(2.4)` consumes.  (`g̃` vanishes unless its argument is
squarefree, so in the application the coprimality is free.) -/
lemma FIgtil_mul_coprime (e l b : ℕ) (h : Nat.Coprime b (e * l)) :
    Submission.ASP.FIgtil (e * b * l) = Submission.ASP.FIgtil (e * l) * Submission.ASP.FIgtil b := by
  rw [show e * b * l = (e * l) * b by ring]
  exact Submission.ASP.FIgtil_mul h.symm

/-- **The `ν`-split of the sieve weight**: for `e`, `b` coprime, `ρ(eb) = Σ_{νe | e}Σ_{νb | b}λ(νe·νb)`.
This is the first move of the `(2.4)`-application: after it, the `b`-sum runs over the fresh
variable `ν_b` and the density weight is constant in it. -/
lemma rhoOf_mul_coprime (lam : ℕ → ℝ) {e b : ℕ} (h : Nat.Coprime e b) :
    Submission.ASP.rhoOf lam (e * b)
      = ∑ νe ∈ e.divisors, ∑ νb ∈ b.divisors, lam (νe * νb) := by
  have hR : (∑ νe ∈ e.divisors, ∑ νb ∈ b.divisors, lam (νe * νb))
      = ∑ p ∈ (e.divisors ×ˢ b.divisors), lam (p.1 * p.2) := by
    rw [Finset.sum_product]
  rw [Submission.ASP.rhoOf, hR]
  refine Eq.symm ?_
  refine Finset.sum_bij (s := e.divisors ×ˢ b.divisors) (t := (e * b).divisors)
    (fun p _ => p.1 * p.2) ?_ ?_ ?_ ?_
  · rintro ⟨a, c⟩ hp
    rw [Finset.mem_product] at hp
    rw [Nat.mem_divisors]
    exact ⟨Nat.mul_dvd_mul (Nat.mem_divisors.mp hp.1).1 (Nat.mem_divisors.mp hp.2).1,
      Nat.mul_ne_zero (Nat.mem_divisors.mp hp.1).2 (Nat.mem_divisors.mp hp.2).2⟩
  · rintro ⟨a₁, c₁⟩ hp₁ ⟨a₂, c₂⟩ hp₂ heq
    simp only at heq
    rw [Finset.mem_product] at hp₁ hp₂
    have hne : a₁ ≠ 0 := by
      intro h0
      exact (Nat.mem_divisors.mp hp₁.1).2 (zero_dvd_iff.mp (h0 ▸ (Nat.mem_divisors.mp hp₁.1).1))
    have h₁ : a₁ ∣ a₂ := by
      have hc : Nat.Coprime a₁ c₂ := (h.coprime_dvd_left (Nat.mem_divisors.mp hp₁.1).1).coprime_dvd_right (Nat.mem_divisors.mp hp₂.2).1
      exact hc.dvd_of_dvd_mul_right (heq ▸ dvd_mul_right a₁ c₁)
    have h₂ : a₂ ∣ a₁ := by
      have hc : Nat.Coprime a₂ c₁ := (h.coprime_dvd_left (Nat.mem_divisors.mp hp₂.1).1).coprime_dvd_right (Nat.mem_divisors.mp hp₁.2).1
      exact hc.dvd_of_dvd_mul_right (heq.symm ▸ dvd_mul_right a₂ c₂)
    have ha : a₁ = a₂ := Nat.dvd_antisymm h₁ h₂
    subst ha
    simp only [Prod.mk.injEq, true_and]
    exact Nat.mul_left_cancel (Nat.pos_of_ne_zero hne) heq
  · intro ν hν
    rw [h.divisors_mul] at hν
    rw [Finset.mem_map] at hν
    obtain ⟨a, -, haν⟩ := hν
    refine ⟨a.val, ?_, ?_⟩
    · rw [Finset.mem_product]
      exact Finset.mem_product.mp a.2
    · exact haν
  · intro p _
    rfl

/-- `|ρ(ν)| ≤ τ(ν)`. -/
lemma abs_rhoOf_le_card (lam : ℕ → ℝ) (hlam : ∀ ν : ℕ, |lam ν| ≤ 1) (n : ℕ) :
    |Submission.ASP.rhoOf lam n| ≤ ((n.divisors.card : ℕ) : ℝ) := by
  rw [Submission.ASP.rhoOf]
  calc |∑ ν ∈ n.divisors, lam ν| ≤ ∑ ν ∈ n.divisors, |lam ν| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ν ∈ n.divisors, (1 : ℝ) := Finset.sum_le_sum (fun ν _ => hlam ν)
    _ = ((n.divisors.card : ℕ) : ℝ) := by simp

theorem sum_divisors_rhoOf_le : ∃ c : ℝ, 0 < c ∧ ∀ (lam : ℕ → ℝ), (∀ ν : ℕ, |lam ν| ≤ 1) → ∀ ζ : ℕ, 1 ≤ ζ →
    ∑ e ∈ ζ.divisors, ∑ b ∈ (ζ / e).divisors, |Submission.ASP.rhoOf lam (e * b)|
      ≤ c * ((ζ.divisors.card : ℝ)) ^ 5 := by
  refine ⟨1, one_pos, ?_⟩
  intro lam hlam ζ hζ
  have hτpos : (0 : ℝ) < ((ζ.divisors.card : ℕ) : ℝ) := by
    have : 0 < ζ.divisors.card := Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩
    exact_mod_cast this
  have hτ1 : (1 : ℝ) ≤ ((ζ.divisors.card : ℕ) : ℝ) := by
    have : 1 ≤ ζ.divisors.card := Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩
    exact_mod_cast this
  have hcard : ∀ n : ℕ, n ∣ ζ → ((n.divisors.card : ℕ) : ℝ) ≤ ((ζ.divisors.card : ℕ) : ℝ) := by
    intro n hn
    have := Finset.card_le_card (Nat.divisors_subset_of_dvd (by omega : ζ ≠ 0) hn)
    simpa using this
  have hinner : ∀ e ∈ ζ.divisors,
      ∑ b ∈ (ζ / e).divisors, |Submission.ASP.rhoOf lam (e * b)|
        ≤ ((ζ.divisors.card : ℕ) : ℝ) * (((ζ / e).divisors.card : ℕ) : ℝ) := by
    intro e he
    have hedvd : e ∣ ζ := Nat.dvd_of_mem_divisors he
    have hmlt : ∀ b ∈ (ζ / e).divisors, e * b ∣ ζ := by
      intro b hb
      have hb' : b ∣ ζ / e := Nat.dvd_of_mem_divisors hb
      exact (Nat.mul_div_cancel' hedvd).symm ▸ Nat.mul_dvd_mul_left e hb'
    calc ∑ b ∈ (ζ / e).divisors, |Submission.ASP.rhoOf lam (e * b)|
        ≤ ∑ _b ∈ (ζ / e).divisors, ((ζ.divisors.card : ℕ) : ℝ) :=
          Finset.sum_le_sum (fun b hb =>
            le_trans (abs_rhoOf_le_card lam hlam (e * b)) (hcard (e * b) (hmlt b hb)))
      _ = (((ζ / e).divisors.card : ℕ) : ℝ) * ((ζ.divisors.card : ℕ) : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((ζ.divisors.card : ℕ) : ℝ) * (((ζ / e).divisors.card : ℕ) : ℝ) := by ring
  calc ∑ e ∈ ζ.divisors, ∑ b ∈ (ζ / e).divisors, |Submission.ASP.rhoOf lam (e * b)|
      ≤ ∑ e ∈ ζ.divisors, ((ζ.divisors.card : ℕ) : ℝ) * (((ζ / e).divisors.card : ℕ) : ℝ) :=
        Finset.sum_le_sum hinner
    _ = ((ζ.divisors.card : ℕ) : ℝ) * ∑ e ∈ ζ.divisors, (((ζ / e).divisors.card : ℕ) : ℝ) := by
        rw [Finset.mul_sum]
    _ ≤ ((ζ.divisors.card : ℕ) : ℝ) * ∑ _e ∈ ζ.divisors, ((ζ.divisors.card : ℕ) : ℝ) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun e he => ?_)) hτpos.le
        exact hcard (ζ / e) (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors he))
    _ = ((ζ.divisors.card : ℕ) : ℝ) * (((ζ.divisors.card : ℕ) : ℝ) * ((ζ.divisors.card : ℕ) : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 1 * ((ζ.divisors.card : ℝ)) ^ 5 := by
        rw [one_mul]
        have h3 : ((ζ.divisors.card : ℕ) : ℝ) * (((ζ.divisors.card : ℕ) : ℝ) * ((ζ.divisors.card : ℕ) : ℝ))
            = ((ζ.divisors.card : ℕ) : ℝ) ^ 3 := by ring
        rw [h3]
        calc ((ζ.divisors.card : ℕ) : ℝ) ^ 3 = ((ζ.divisors.card : ℕ) : ℝ) ^ 3 * 1 := (mul_one _).symm
          _ ≤ ((ζ.divisors.card : ℕ) : ℝ) ^ 3 * (((ζ.divisors.card : ℕ) : ℝ)) ^ 2 :=
              mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
          _ = _ := by ring




/-- `∫_a^{e·a} S/z dz = S`: an integrand bounded by a constant `S` over the `z`-window contributes
at most `S`, since the window has `dz/z`-mass `1`. -/
lemma integral_const_div_exp_mul (S a : ℝ) (ha : 0 < a) :
    ∫ z in a..(Real.exp 1 * a), S / z = S := by
  have h : ∀ z : ℝ, S / z = S * (1 / z) := fun z => by rw [div_eq_mul_one_div]
  rw [intervalIntegral.integral_congr (fun z _ => h z)]
  rw [intervalIntegral.integral_const_mul,
    Commons.Analysis.Asymptotics.integral_one_div_Ioc_exp_mul a ha, mul_one]

/-- **The window reduction.**  If `|G| ≤ S` on the multiplicative window `[a, e·a]` (`a > 0`),
then `∫_a^{e·a} |G y|/y dy ≤ S`: the window carries `dy/y`-mass exactly `1`.  This reduces the
chain's `y`-average — and, verbatim, its `z`-average — to a pointwise bound.  Both integrability
hypotheses are supplied in the application by `intervalIntegrable_div_Ioc` (cf. the private
`integral_le_const_div_zavg` of `S3minusC_zavg_le`). -/
theorem integral_abs_div_le_of_bound (G : ℝ → ℝ) (a S : ℝ) (ha : 0 < a) (hS : 0 ≤ S)
    (hIntG : IntervalIntegrable (fun y : ℝ => |G y| / y) MeasureTheory.volume a (Real.exp 1 * a))
    (hIntS : IntervalIntegrable (fun y : ℝ => S / y) MeasureTheory.volume a (Real.exp 1 * a))
    (hpt : ∀ y ∈ Set.Icc a (Real.exp 1 * a), |G y| ≤ S) :
    ∫ y in a..(Real.exp 1 * a), |G y| / y ≤ S := by
  have hle : a ≤ Real.exp 1 * a := by
    nlinarith [Real.one_le_exp (show (0:ℝ) ≤ 1 by norm_num), ha]
  have hmono : (∫ y in a..(Real.exp 1 * a), |G y| / y)
      ≤ ∫ y in a..(Real.exp 1 * a), S / y := by
    refine intervalIntegral.integral_mono_on hle hIntG hIntS ?_
    intro y hy
    exact div_le_div_of_nonneg_right (hpt y hy) (le_of_lt (lt_of_lt_of_le ha hy.1))
  rwa [integral_const_div_exp_mul S a ha] at hmono


/-- **The per-`z` bound.**  For a fixed `z`, if the `S3plusC` integrand is uniformly bounded by `S`
over the chain's `y`-window `[Yc, e·Yc]`, then its `y`-average is at most `S` — the window carries
`dy/y`-mass `1` (`integral_abs_div_le_of_bound` instantiated at the chain's parameters).  MAIN and
REM supply the pointwise bound; this lemma is the `y`-half of the final assembly. -/
theorem S3plusC_yavg_le (x : ℕ) (B : ℝ) (lam : ℕ → ℝ) (z S : ℝ)
    (hYc : 0 < Yc x B) (hS : 0 ≤ S)
    (hIntG : IntervalIntegrable
      (fun y : ℝ => |S3plusC atilc lam x z (sc x B * y) (sc x B * z)
        (((⌊(zc x B) ^ (1 - etac)⌋₊ : ℕ) : ℝ))| / y)
      MeasureTheory.volume (Yc x B) (Real.exp 1 * Yc x B))
    (hIntS : IntervalIntegrable (fun y : ℝ => S / y) MeasureTheory.volume
      (Yc x B) (Real.exp 1 * Yc x B))
    (hpt : ∀ y ∈ Set.Icc (Yc x B) (Real.exp 1 * Yc x B),
      |S3plusC atilc lam x z (sc x B * y) (sc x B * z)
        (((⌊(zc x B) ^ (1 - etac)⌋₊ : ℕ) : ℝ))| ≤ S) :
    ∫ y in (Yc x B)..(Real.exp 1 * Yc x B),
      |S3plusC atilc lam x z (sc x B * y) (sc x B * z)
        (((⌊(zc x B) ^ (1 - etac)⌋₊ : ℕ) : ℝ))| / y ≤ S :=
  integral_abs_div_le_of_bound _ _ _ hYc hS hIntG hIntS hpt

