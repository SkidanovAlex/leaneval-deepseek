import Mathlib
import Submission.CDTPlan.Interfaces
import Submission.Work.Holonomy3.defs
import Submission.Work.Holonomy3.count_le_of_disc
import Submission.Work.Holonomy3.tauFlat_eq_colShape
import Submission.Work.Holonomy3.PullbackMero_mul_X_pow
import Submission.Work.Holonomy3.balanced_indices
import Submission.Work.Holonomy3.fstats
import Submission.Work.Holonomy3.rearrInt_eq_integral_integral_max
import Submission.Work.Holonomy3.rearrInt_ge_mean
import Submission.Work.Holonomy3.koksma_monotone
import Submission.Work.Holonomy3.circleLog_average_ge
import Submission.Work.Holonomy3.seed_sum_estimate
import Submission.Work.Holonomy3.single_step_valuationwise
import Submission.Work.Holonomy3.log_lcm_cap_le
import Submission.Work.Holonomy3.pullback_coeff_growth
import Submission.Work.Holonomy3.pointwise_rearrangement_bound
import Submission.Work.Holonomy3.expectation_max_blocked
import Submission.Work.Holonomy3.radius_reduction
import Submission.Work.Holonomy3.comp_defs
import Submission.Work.Holonomy3.min_coeff
import Submission.Work.Holonomy3.coeff_cleared_eq
import Submission.Work.Holonomy3.cleared_taylor
import Submission.Work.Holonomy3.assembly_lemmas
import Submission.Work.Holonomy3.siegel
import Submission.Work.Holonomy3.seeding_defs
import Submission.Work.Holonomy3.blockIdx_spec
import Submission.Work.Holonomy3.card_blockIdx_close
import Submission.Work.Holonomy3.exists_monotone_perm
import Submission.Work.Holonomy3.exists_lexmin_minimal
import Submission.Work.Holonomy3.mv_lexmin_coeff_le_integral_smoothed
import Submission.Work.Holonomy3.clearedFun_pointwise_bound
import Submission.Work.Holonomy3.integral_sup_bound
import Submission.Work.Holonomy3.log_den_coeff_le
import Submission.Work.Holonomy3.abel_sum_bound
import Submission.Work.Holonomy3.scaled_setup
import Submission.Work.Holonomy3.exists_scaled_family
import Submission.Work.Holonomy3.exists_sup_bound_circle
import Submission.Work.Holonomy3.exists_circleLog_bound
import Submission.Work.Holonomy3.final_sift
import Submission.Work.Holonomy3.assembly
import Submission.Work.ZeroEst2.zero_estimate_all

/-! Guidance from the project lead (the requester):

# Area H — the fine holonomy bound (`Submission.CDTPlan.HolonomyBoundL2`, assuming `ZeroEstimate`)

Target is the `l ≤ 2` version (at most three maps φ₀, φ₁, φ₂): Theorem C uses l = 0,
Theorem A uses l = 2. You may prove it for general l if that is cleaner (the proof is blockwise),
but you only need l ≤ 2. Suggested structure: prove the l = 0 case (Corollary `basic main corollary`)
first end-to-end, then add the block partition (the seeding step of the paper, §4005–4031, assigns
variables j with γ_k/m ≤ j/d < γ_{k+1}/m to map φ_k).

You own the crux of the whole problem: paper Theorem `main:elementary form` (REFS/L2chi.tex lines
3437–4643: statement 3477–3537, proof §§ "Horizontal integration" 3699, "The auxiliary construction"
3784, "The box principle step" 3949, "Seeding" 4005, "Equidistribution" 4031, "Denominator
arithmetic" 4251, "Proof of Theorem" 4521). Read those lines fully first. The concentration of
measure is §3141–3267, the cost of an integration (I_u^v) §3267–3437, filtered evaluation modules
§2538–2768. You may use `hZ : ZeroEstimate` (another area proves it) exactly where the paper uses
Lemma `lem_Shidlovsky` (in the proof of Lemma `Siegel`, to get property (⋆): SOME nonzero
minimal-order monomial of F lies in the box [0,(m+δ)D]^d).

History: a first owner (H5) found the contract false without the conformality hypothesis
(`φ_k'(0) = 0` makes the paper's log-ratio +∞ but Lean's log 0 = 0); the hypothesis
`∀ k, 0 < ‖deriv (φ k) 0‖` is now in the contract. See `Submission/Work/Holonomy/holonomy_bound_false.lean`.
If you find another defect, `declare_false` with a machine-checked counterexample in the same way.

Contract notes (differences from the paper, all in your favour or harmless):
- f's are D-closed ⇒ holonomic, so the weaker hypothesis `τ < log|φ_l'(0)|` suffices (paper's
  last sentence of the theorem). ξ is fixed (any ξ ∈ [0,m] gives the bound with τ♯ replaced by
  `tauSharpAt e ξ`; the proof is the paper's with that ξ).
- Denominator types allow a fixed shift c inside each lcm and a fixed factor K: lcm(1..bn+c) ≤
  lcm(1..bn)·(bn+c)^c, a sub-exponential factor; K is a constant. Both vanish in the limit.
- Pullbacks are meromorphic with a POLYNOMIAL denominator P (P(0) ≠ 0); multiply the auxiliary
  function's pullback by ∏_j P(z_j)^{…} — the degree is fixed, so its contribution is o(dD).
- Maps are only continuous on the closed disc (holomorphic inside) and zero-free on the circle:
  prove the bound for φ(rz), r<1, and let r → 1 (log|φ(r e^{it})| → log|φ(e^{it})| uniformly).
- The rearrangement integral is written blockwise as `rearrInt` (a finite sum of double interval
  integrals of max); it equals the paper's ∫₀¹ 2t g*(t) dt. The prior run's
  `Submission/CDT/Rearrangement.lean` has `integral_two_mul_fstar`, `measureReal_prod_max_gt`.

Existing workspace material to reuse (grep before building anything):
`Submission/CDT/DiscrepancyFour.lean` (`disc_concentration_four`: box discrepancy concentration),
`Discrepancy.lean`, `MvVanishing*.lean` (vanishing filtration, jump count = finrank, Cartesian
products), `Rearrangement.lean`, `RiemannSum.lean`, `StepRiemann.lean`, `IntegratedLcm.lean`,
`FineHolonomy.lean` (τ♭ identities), `Lcm*.lean`, `Lcm2Bound.lean` (lemma `lcm-2`), `LcmUniform`,
`ModelRiemann.lean`; Commons: Hadamard determinant inequality, Fekete torus bound `|V| ≤ d^{d/2}`,
PNT-type `log lcm(1..n) ~ n`. Mathlib: `Mathlib/NumberTheory/SiegelsLemma.lean`
(`Int.exists_ne_zero_int_vec_norm_le`), Cauchy estimates, `circleIntegral`.
-/

namespace Work.Holonomy3

open Submission.CDTPlan
open scoped BigOperators

/-! ## Part 1: arithmetic of the denominator lcms

The paper's Remark `rem:overflow` allows a fixed shift `c` inside every `lcm` and a fixed factor
`K` in the denominator type `(den type int)`.  The content of that remark is that
`lcm(1,…,bn+c) ≤ lcm(1,…,bn)·(bn+c)^c`, a sub-exponential factor, which is what the first lemma
below records (in the form actually used, with `N = bn`). -/

/-- `lcmUpto` is Mathlib's `Nat.lcmUpto`. -/
theorem lcmUpto_eq_natLcmUpto (N : ℕ) : lcmUpto N = Nat.lcmUpto N := rfl

theorem lcmUpto_pos (N : ℕ) : 0 < lcmUpto N := Nat.lcmUpto_pos N

/-- Every `m` with `1 ≤ m ≤ N` divides `lcmUpto N`. -/
theorem dvd_lcmUpto {m N : ℕ} (hm : 1 ≤ m) (h : m ≤ N) : m ∣ lcmUpto N :=
  Finset.dvd_lcm (f := id) (by simp [hm, h])

/-- `lcmUpto` is monotone for divisibility. -/
theorem lcmUpto_dvd_lcmUpto {m n : ℕ} (h : m ≤ n) : lcmUpto m ∣ lcmUpto n := by
  unfold lcmUpto
  exact Finset.lcm_mono (fun a ha => by simp only [Finset.mem_Icc] at ha ⊢; omega)

/-- **Remark `rem:overflow`**: `lcm(1,…,N+c) ≤ lcm(1,…,N)·(N+c)^c`. -/
theorem lcmUpto_add_le (N c : ℕ) : lcmUpto (N + c) ≤ lcmUpto N * (N + c) ^ c := by
  have hle : lcmUpto (N + c) ∣ lcmUpto N * ∏ i ∈ Finset.Icc (N + 1) (N + c), i := by
    rw [lcmUpto]
    refine Finset.lcm_dvd (fun b hb => ?_)
    simp only [Finset.mem_Icc] at hb
    by_cases h : b ≤ N
    · exact dvd_mul_of_dvd_left (Finset.dvd_lcm (f := id) (by simp [hb.1, h])) _
    · have hb' : b ∈ Finset.Icc (N + 1) (N + c) := by
        simp only [Finset.mem_Icc]; omega
      exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem id hb') _
  have hP : (∏ i ∈ Finset.Icc (N + 1) (N + c), i) ≤ (N + c) ^ c := by
    have hcard : (Finset.Icc (N + 1) (N + c)).card = c := by rw [Nat.card_Icc]; omega
    calc (∏ i ∈ Finset.Icc (N + 1) (N + c), i)
        ≤ ∏ _i ∈ Finset.Icc (N + 1) (N + c), (N + c) :=
          Finset.prod_le_prod₀ (fun i _ => Nat.zero_le _)
            (fun i hi => by simp only [Finset.mem_Icc] at hi; omega)
      _ = (N + c) ^ (Finset.Icc (N + 1) (N + c)).card := Finset.prod_const _
      _ = (N + c) ^ c := by rw [hcard]
  have hpos : 0 < lcmUpto N * ∏ i ∈ Finset.Icc (N + 1) (N + c), i :=
    Nat.mul_pos (Nat.lcmUpto_pos N)
      (Finset.prod_pos (fun i hi => by simp only [Finset.mem_Icc] at hi; omega))
  exact le_trans (Nat.le_of_dvd hpos hle) (Nat.mul_le_mul_left _ hP)

/-! ## Part 2: the Euler operator `x·d/dx` and denominator types

The paper's §"The box principle step" observes that, in the *a priori* holonomic case, applying
`(x d/dx)^{e_i}` to `f_i` removes the extra `n^{e_i}` from the denominators of `(den type int)`,
while preserving holonomicity and the meromorphicity of the pullbacks.  The formal counterpart
proved here is that `(x d/dx)^e` lowers the exponent vector `e` to `0` without changing the lcm
array `b`. -/

theorem coeff_euler (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n (euler f) = (n : ℚ) * PowerSeries.coeff n f := by
  rcases n with _ | n
  · rw [euler, PowerSeries.coeff_zero_X_mul]; simp
  · rw [euler, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
    push_cast
    ring

theorem coeff_euler_iterate (f : PowerSeries ℚ) (e n : ℕ) :
    PowerSeries.coeff n (euler^[e] f) = (n : ℚ) ^ e * PowerSeries.coeff n f := by
  induction e with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', coeff_euler, ih, pow_succ]
    ring

/-- `(x d/dx)^e` removes the `n^e` from the denominator type. -/
theorem HasDenomType.euler {r e : ℕ} {b : Fin r → ℕ} {f : PowerSeries ℚ}
    (h : HasDenomType e b f) : HasDenomType 0 b (euler^[e] f) := by
  obtain ⟨K, c, hK, hcoe⟩ := h
  refine ⟨K, c, hK, fun n hn => ?_⟩
  obtain ⟨a, ha⟩ := hcoe n hn
  refine ⟨a, ?_⟩
  rw [coeff_euler_iterate]
  calc (K : ℚ) * (n : ℚ) ^ 0 * (∏ j, (lcmUpto (b j * n + c) : ℚ))
        * ((n : ℚ) ^ e * PowerSeries.coeff n f)
      = ((K : ℚ) * (n : ℚ) ^ e * ∏ j, (lcmUpto (b j * n + c) : ℚ)) * PowerSeries.coeff n f := by
        ring
    _ = (a : ℚ) := ha

/-! ## Part 3: the denominator rate `τ♭` and the integration rate `τ♯`

The paper proves (display `(taub)`) that `τ♭(b) ∈ [0, σ_m]`; here we record the two facts needed
downstream, `0 ≤ τ♭` and `0 ≤ τ♯`, together with the nonnegativity of the two integrands of the
paper's Definition `integrated lcm`. -/

theorem tauFlat_nonneg {m r : ℕ} (b : Fin m → Fin r → ℕ) : 0 ≤ tauFlat b := by
  unfold tauFlat
  refine mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _ => ?_))
  have h1 : (0 : ℝ) ≤ (rowSum b i : ℝ) := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ 2 * (i : ℝ) + 1 := by positivity
  nlinarith

theorem harmonicFun_nonneg (w t : ℝ) : 0 ≤ harmonicFun w t := by
  refine Finset.sum_nonneg (fun h _ => ?_)
  exact div_nonneg zero_le_one (Nat.cast_nonneg _)

theorem correctionFun_nonneg (w t : ℝ) : 0 ≤ correctionFun w t := le_max_right _ _

/-- `I_ξ^m(ξ) ≥ 0` on the paper's range `0 ≤ ξ ≤ m` (`m ≥ 1`). -/
theorem integratedLcm_self_nonneg {m : ℕ} {ξ : ℝ} (hm : 1 ≤ m) (hξm : ξ ≤ (m : ℝ)) :
    0 ≤ integratedLcm ξ (m : ℝ) ξ := by
  have h1 : min ξ 1 ≤ 1 := min_le_right _ _
  have h2 : max ξ 1 ≤ (m : ℝ) := by
    rw [max_le_iff]
    exact ⟨hξm, by exact_mod_cast hm⟩
  refine add_nonneg (add_nonneg ?_ ?_) ?_
  · exact intervalIntegral.integral_nonneg h1 (fun u _ => le_max_right _ _)
  · exact intervalIntegral.integral_nonneg h2 (fun u _ => harmonicFun_nonneg ξ u)
  · exact intervalIntegral.integral_nonneg h2 (fun u _ => correctionFun_nonneg ξ u)

/-- `τ♯(e) ≥ 0` on the paper's range `0 ≤ ξ ≤ m`. -/
theorem tauSharpAt_nonneg {m : ℕ} {e : Fin m → ℕ} {ξ : ℝ} (hm : 1 ≤ m) (h0 : 0 ≤ ξ)
    (hξm : ξ ≤ (m : ℝ)) : 0 ≤ tauSharpAt e ξ := by
  unfold tauSharpAt
  refine mul_nonneg (by positivity) (add_nonneg ?_ ?_)
  · exact mul_nonneg h0 (Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _))
  · exact mul_nonneg (Nat.cast_nonneg _) (integratedLcm_self_nonneg hm hξm)

/-- `τ(b;e) ≥ 0`, so that the hypothesis `τ < log|φ_l'(0)|` of the holonomy bound is a genuine
smallness condition on the denominators. -/
theorem tau_nonneg {m r : ℕ} {b : Fin m → Fin r → ℕ} {e : Fin m → ℕ} {ξ : ℝ} (hm : 1 ≤ m)
    (h0 : 0 ≤ ξ) (hξm : ξ ≤ (m : ℝ)) : 0 ≤ tauFlat b + tauSharpAt e ξ :=
  add_nonneg (tauFlat_nonneg b) (tauSharpAt_nonneg hm h0 hξm)

/-! ## Part 4: the patched function of the paper's display `(rearrangement fine)`

`rearrInt` is the *blockwise* form of the rearrangement integral of the paper, and the paper writes
it as `∬ max(g(s),g(t))` for the patched function `g` (whose blocks carry the maps `φ k` with
weights `w k = (γ_{k+1} - γ_k)/m`).  Both the patched function and its block boundaries are needed
to state that identity, so we define them here. -/

/-! ## Part 5: monotonicity of `HasDenomType`, and discharging the hypotheses on the test
functions `1` (integer coefficients, trivially holonomic) -/

/-- `HasDenomType` is monotone in the exponent vector and in the lcm array. -/
theorem HasDenomType.mono {r : ℕ} {e e' : ℕ} {b b' : Fin r → ℕ} {f : PowerSeries ℚ}
    (hee : e ≤ e') (hbb : ∀ j, b j ≤ b' j) (h : HasDenomType e b f) :
    HasDenomType e' b' f := by
  obtain ⟨K, c, hK, hcoe⟩ := h
  refine ⟨K, c, hK, fun n hn => ?_⟩
  obtain ⟨a, ha⟩ := hcoe n hn
  set q : ℕ := n ^ (e' - e) * ∏ j, (lcmUpto (b' j * n + c) / lcmUpto (b j * n + c)) with hq
  refine ⟨a * (q : ℤ), ?_⟩
  have hfac : ∀ j : Fin r, lcmUpto (b j * n + c) ∣ lcmUpto (b' j * n + c) := by
    intro j
    unfold lcmUpto
    apply Finset.lcm_mono
    intro s hs
    simp only [Finset.mem_Icc] at hs ⊢
    have hmul : b j * n ≤ b' j * n := Nat.mul_le_mul_right n (hbb j)
    omega
  have hpow : (n : ℚ) ^ e' = (n : ℚ) ^ e * (n : ℚ) ^ (e' - e) := by
    rw [← pow_add, Nat.add_sub_cancel' hee]
  have hprod : ∏ j, (lcmUpto (b' j * n + c) : ℚ)
      = (∏ j, (lcmUpto (b j * n + c) : ℚ)) *
        ∏ j, ((lcmUpto (b' j * n + c) / lcmUpto (b j * n + c) : ℕ) : ℚ) := by
    have hpt : ∀ j, (lcmUpto (b' j * n + c) : ℚ)
        = (lcmUpto (b j * n + c) : ℚ) *
          ((lcmUpto (b' j * n + c) / lcmUpto (b j * n + c) : ℕ) : ℚ) := by
      intro j
      conv_lhs => rw [← Nat.mul_div_cancel' (hfac j)]
      push_cast; ring
    rw [Finset.prod_congr rfl (fun j _ => hpt j), Finset.prod_mul_distrib]
  rw [hpow, hprod]
  have hstep : ((K : ℚ) * ((n : ℚ) ^ e * (n : ℚ) ^ (e' - e)) *
      ((∏ j, (lcmUpto (b j * n + c) : ℚ)) *
        ∏ j, ((lcmUpto (b' j * n + c) / lcmUpto (b j * n + c) : ℕ) : ℚ))) * PowerSeries.coeff n f
    = ((K : ℚ) * (n : ℚ) ^ e * ∏ j, (lcmUpto (b j * n + c) : ℚ)) * PowerSeries.coeff n f *
      ((n : ℚ) ^ (e' - e) * ∏ j, ((lcmUpto (b' j * n + c) / lcmUpto (b j * n + c) : ℕ) : ℚ)) := by
    ring
  rw [hstep, ha]
  have hcast : ((a * (q : ℤ) : ℤ) : ℚ) = (a : ℚ) * ((q : ℕ) : ℚ) := by push_cast; ring
  rw [hcast]
  have hq' : ((q : ℕ) : ℚ) = (n : ℚ) ^ (e' - e) *
      ∏ j, ((lcmUpto (b' j * n + c) / lcmUpto (b j * n + c) : ℕ) : ℚ) := by
    rw [hq]; push_cast; ring
  rw [hq']

/-- The constant function `1`: the standard first element of a holonomic system. -/
theorem HasDenomType_one {r : ℕ} (b : Fin r → ℕ) : HasDenomType 0 b (1 : PowerSeries ℚ) := by
  refine ⟨1, 0, by norm_num, fun n hn => ⟨0, ?_⟩⟩
  rw [PowerSeries.coeff_one, if_neg (by omega)]
  simp

/-- Integer-coefficient series have trivially good denominators, for every lcm array. -/
theorem HasDenomType_of_int_coeff {r : ℕ} (b : Fin r → ℕ) {f : PowerSeries ℚ}
    (hf : ∀ n : ℕ, 1 ≤ n → ∃ a : ℤ, PowerSeries.coeff n f = a) : HasDenomType 0 b f := by
  refine ⟨1, 0, by norm_num, fun n hn => ?_⟩
  obtain ⟨a, ha⟩ := hf n hn
  refine ⟨a * (∏ j, (lcmUpto (b j * n + 0) : ℕ) : ℤ), ?_⟩
  rw [ha]
  push_cast
  ring

/-- The pullback of the constant function `1` is meromorphic for every map. -/
theorem PullbackMero_one (φ : ℂ → ℂ) : PullbackMero (1 : PowerSeries ℚ) φ := by
  refine ⟨1, fun _ => 1, by norm_num, differentiableOn_const 1, ?_⟩
  filter_upwards
  intro z
  simp only [Polynomial.eval_one, div_one]
  have h : (fun n : ℕ => ((PowerSeries.coeff n (1 : PowerSeries ℚ) : ℚ) : ℂ) * φ z ^ n)
      = (fun n : ℕ => if n = 0 then (1 : ℂ) else 0) := by
    funext n
    rw [PowerSeries.coeff_one]
    by_cases hn : n = 0 <;> simp [hn]
  rw [h]
  simpa using hasSum_ite_eq (0 : ℕ) (1 : ℂ)

/-- A single nonzero function is `Q(x)`-independent. -/
theorem PolyIndependent_fin_one {f : PowerSeries ℚ} :
    PolyIndependent (fun _ : Fin 1 => f) ↔ f ≠ 0 := by
  constructor
  · intro h hf0
    have h1 : (∑ i : Fin 1, ((fun _ : Fin 1 => (1 : Polynomial ℚ)) i : PowerSeries ℚ) *
        (fun _ : Fin 1 => f) i) = 0 := by
      simp [hf0]
    have h2 := h (fun _ : Fin 1 => 1) h1 0
    simpa using h2
  · intro hf P hP i
    fin_cases i
    have h : (P 0 : PowerSeries ℚ) * f = 0 := by simpa using hP
    rcases mul_eq_zero.mp h with h' | h'
    · exact Polynomial.coe_injective ℚ (by simpa using h')
    · exact absurd h' hf

/-! ## Part 6: the route to the target — see `Submission/Work/Holonomy3/NOTES_DESIGN.md`

The proof is the paper's §"fine section" (Theorem `main:elementary form`), following the project
lead's `REFS/NOTES_LEAD_holonomy_limits.md`; **read `Submission/Work/Holonomy3/NOTES_DESIGN.md`
first** (it contains the corrected design, the full inventory of proved lemmas, and the precise
remaining steps).

Summary of the design actually adopted (it differs in one important respect from the earlier
sketch): the contract's `PullbackMero f φ` writes the pullback germ as `N z / P.eval z` with the
denominator a polynomial in the **pullback variable** `z`.  All local definitions
(`comp_defs.lean`: `PullbackData`, `clearedFun`, `uPoly`, `ClearedTaylorClaim`) therefore evaluate
`P` at `z`, the clearing series is the polynomial `uPoly P = ∏_s ∏_i P_{i,s}(x_s)`, and the
*scaling* `φ k ↦ φ k (r·)` (`r < 1`, STEP 0) produces both the polydisc radius `ρ = 1/r > 1` and
the wider analyticity ball of the numerators `N`.

The chain, for fixed `r ∈ (0,1)`:

1. `scaled_setup`, `exists_scaled_family`, `pullback_coeff_growth` produce the scaled maps
   `ψ k := φ k (r·)`, their Taylor series `Φ k`, the pullback data `(N i k, P i k)`, and the
   normalised family `f'` with `‖coeff n (f' i)‖ ≤ Aⁿ`.
2. `siegel` (box principle) produces the template `Q`; `exists_lexmin_minimal` extracts the
   lex-minimal minimal-degree monomial `n`; `min_monomial_lowdisc` (this file, Part 9) gives
   property `(⋆)`.
3. `coeff_cleared_eq` / `coeff_cleared_ne_zero` (STEP 2) identify the leading coefficient of the
   cleared composite as `u₀ · β_n · ∏_s (ψ_{κ s}'(0))^{n_s}`, where `κ s := blockIdx m γ (π.symm s)`
   is the seeding block of the rank of `n_s` (`π` sorts `n`, `exists_monotone_perm`).
4. `cleared_taylor` + `mv_lexmin_coeff_le_integral` (STEP 3) bound its logarithm by
   `∫ log‖clearedFun‖`.
5. `clearedFun_pointwise_bound_max` + `integral_max_sup_bound` (STEP 4–5) bound that integral by
   `(α/m)·rearrInt + o(α)` with `α = mdD/2`.
6. `log_den_coeff_le` (STEP 6) is the arithmetic lower bound `log|β_n| ≥ -α(τ + η)`.
7. `abel_sum_bound` + `sum_comp_blockIdx` (STEP 7) handle `Σ_s n_s L_{κ s}`; the limits
   `D → ∞`, `d → ∞`, `ε → 0` finish the proof.
8. `radius_reduction` removes the truncation `r < 1`.
-/

/-! ## Part 9: the `(⋆)` property of Lemma `Siegel`

The box principle delivers an auxiliary function `F = auxSeries f Q` whose coefficients vanish on
the box `[0,(m-δ)D]^d` and on the high-discrepancy part of `[0,(m+δ)D]^d`.  Property `(⋆)` of the
paper is that *every* nonzero minimal-degree monomial `n` of `F` lies in `((m+δ)D)·P_ε^d`, i.e. has
box discrepancy `< ε`.  That is exactly what the higher-dimensional Shidlovsky lemma
(`ZeroEstimateAll`, proved in Area Z) gives: every minimal-degree monomial has all exponents
`≤ m·D + C`, and for `δ·D ≥ C` this puts it inside `[0,(m+δ)D]^d`, where the vanishing conditions
of the box principle exclude the high-discrepancy part. -/

/-- **Property `(⋆)` of Lemma `Siegel`.**  From the multivariable Shidlovsky lemma, every nonzero
minimal-degree monomial of the auxiliary series has box discrepancy `< ε` in the box
`[0,(m+δ)D]^d` (as soon as `δ·D` dominates the Shidlovsky constant). -/
theorem min_monomial_lowdisc (hZ : ZeroEstimateAll) {m : ℕ} (f : Fin m → PowerSeries ℚ)
    (hpi : PolyIndependent f) (hdc : DClosed f) :
    ∃ C : ℕ, ∀ (d D : ℕ) (Q : (Fin d → Fin m) → MvPolynomial (Fin d) ℚ),
      (∀ i j, (Q i).degreeOf j < D) → ∀ δ ε : ℝ, 0 < δ → (C : ℝ) ≤ δ * D →
      (∀ n : Fin d →₀ ℕ, (∀ j, (n j : ℝ) ≤ (m + δ) * D) →
        ε ≤ Submission.CDT.Discrepancy.disc (fun j => (n j : ℝ) / ((m + δ) * D)) →
        MvPowerSeries.coeff n (auxSeries f Q) = 0) →
      ∀ n : Fin d →₀ ℕ, MvPowerSeries.coeff n (auxSeries f Q) ≠ 0 →
      (∀ n' : Fin d →₀ ℕ, n'.degree < n.degree → MvPowerSeries.coeff n' (auxSeries f Q) = 0) →
      (∀ j, (n j : ℝ) ≤ (m + δ) * D) →
      Submission.CDT.Discrepancy.disc (fun j => (n j : ℝ) / ((m + δ) * D)) < ε := by
  obtain ⟨C, hC⟩ := hZ m f hpi hdc
  refine ⟨C, fun d D Q hQD δ ε hδ hCD hvan n hn hmin hbox => ?_⟩
  by_contra hnot
  refine hn (hvan n ?_ (not_lt.mp hnot))
  intro j
  have h1 := hC d D Q hQD n hn hmin j
  have h1' : (n j : ℝ) ≤ (m : ℝ) * D + C := by exact_mod_cast h1
  have h2 : (m : ℝ) * D + C ≤ (m : ℝ) * D + δ * D := by linarith
  have h3 : (m : ℝ) * D + δ * D = (m + δ) * D := by ring
  linarith [h3.le, h3.ge]

theorem holonomy_bound_l2 (hZ : ZeroEstimate) : HolonomyBoundL2 := by
  intro m r l b e f φ γ ξ hm hl hb hden hpi hdc hadm hpm hderiv hmono
    hγ0 hγlast hγmono hξ0 hξm hτ
  have hZall : ZeroEstimateAll := Work.ZeroEst2.zero_estimate_all
  set S : ℝ := (1 / (m : ℝ)) * ∑ k : Fin l, (γ k.succ.castSucc) ^ 2 *
      Real.log (‖deriv (φ k.succ) 0‖ / ‖deriv (φ k.castSucc) 0‖) with hSdef
  set A : ℝ := (m : ℝ) * (Real.log ‖deriv (φ (Fin.last l)) 0‖
      - (tauFlat b + tauSharpAt e ξ)) - S with hAdef
  have key : A ≤ rearrInt (fun k => (γ k.succ - γ k.castSucc) / m) φ := by
    refine radius_reduction (fun k => (γ k.succ - γ k.castSucc) / m) φ A m ?_ ?_ ?_
    · intro k
      exact (hadm k).1
    · intro k z hz
      exact (hadm k).2.2.2 z hz
    · intro r' hr0 hr1 hzf
      have hd0 : ∀ k, DifferentiableAt ℂ (φ k) 0 := fun k =>
        (hadm k).2.1.differentiableAt (Metric.ball_mem_nhds (0 : ℂ) one_pos)
      have hnorm : ‖((r' : ℝ) : ℂ)‖ = r' :=
        (RCLike.norm_ofReal (K := ℂ) r').trans (abs_of_pos hr0)
      have hlog : Real.log ‖deriv (fun z : ℂ => φ (Fin.last l) ((r' : ℂ) * z)) 0‖
          = Real.log r' + Real.log ‖deriv (φ (Fin.last l)) 0‖ := by
        rw [deriv_comp_mul (φ (Fin.last l)) (hd0 (Fin.last l)) r', norm_mul, hnorm,
          Real.log_mul (ne_of_gt hr0) (ne_of_gt (hderiv (Fin.last l)))]
      have h := main_bound_scaled hZall hm hl hb hden hpi hdc hadm hpm hderiv hmono
        hγ0 hγlast hγmono hξ0 hξm hτ hr0 hr1 hzf
      rw [hlog] at h
      have hsplit : (m : ℝ) * (Real.log r' + Real.log ‖deriv (φ (Fin.last l)) 0‖
          - (tauFlat b + tauSharpAt e ξ))
          = (m : ℝ) * (Real.log ‖deriv (φ (Fin.last l)) 0‖ - (tauFlat b + tauSharpAt e ξ))
            + (m : ℝ) * Real.log r' := by ring
      rw [hsplit] at h
      rw [hAdef, hSdef]
      linarith [h]
  rw [hAdef, hSdef] at key
  linarith [key]

end Work.Holonomy3
