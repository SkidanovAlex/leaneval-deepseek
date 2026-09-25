import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_minor_sup
import Submission.Work.BourgainPlan.Maximal.polyWeylKernel_offArc_gauss
import Submission.Work.BourgainPlan.Maximal.major_arc_bound_pre
import Submission.Work.BourgainPlan.Maximal.onArc_kernel_decay
import Submission.Work.BourgainPlan.Maximal.offArc_numeric
import Submission.Work.BourgainPlan.Maximal.nat_pow_le_two_rpow_mul

/-! # `mst_minor_sup` without the Weyl-with-log-loss hypothesis

This file proves `Work.BourgainPlan.Maximal.mst_minor_sup_direct`: the pointwise minor-arc bound
of Mirek--Stein--Trojan's §4.1 with the hypothesis `MSTWeylBound` (the classical Weyl inequality
with polylogarithmic loss for *arbitrary* real polynomials) removed.  The only Weyl input used is
`polyWeylKernel_offArc_gauss` (an `A 2^{-m sigma} + C N^{-c_0}` off-arc bound) together with the
major-arc approximation `major_arc_bound_pre` and the sharp profile decay `polyProfile_decay_sharp`.

The argument, for fixed `l` and `n` and `ξ` with `θ = iwRep ξ` reduced to `[0,1]` (the kernel is
`1`-periodic), with `τ := n^{l-1}` and `m := Nat.log 2 τ`:

* if `θ` is at distance `> N^{-(d-1/4)}` from every `a/q + l` with `q < 2^m` — hence, as
  `2^m ≤ τ`, from every `a/q + l` with `q ≤ τ` — then `polyWeylKernel_offArc_gauss` gives
  `‖m_{2^n}(θ)‖ ≤ A 2^{-mσ} + C N^{-c_0} ≤ A 2^σ τ^{-σ} + C 2^{-n c_0}`, and `τ = n^{l-1}` with
  `(l-1)σ ≥ α+1` makes this `≤ (n+1)^{-α}`;
* otherwise `θ` lies on the arc `a/q + j` with `q ≤ τ`; the point `β₀ = (a + j q)/(q c)` has
  denominator `≤ c τ ≤ n^l`, so `β₀ ∈ 𝒰(n)` and, unless `Ξ_n(ξ) = 1` (in which case the product
  vanishes), `ξ` lies outside the inner ball of `β₀`.  Then `major_arc_bound_pre` and
  `polyProfile_decay_sharp` give an exponential bound `≲ N^{-χ/d}`.

The output is multiplied by `‖1 - Ξ_n(ξ)‖ ≤ 1 + M`. -/

namespace Work.BourgainPlan.Maximal

open Finset MeasureTheory
open scoped BigOperators ENNReal
open Work.BourgainPlan.IonescuWainger
set_option autoImplicit false
set_option maxHeartbeats 1000000

private lemma exp_neg_sep_bound_direct {d : ℕ} {χ : ℝ} (hd : 2 ≤ d) (hχ : χ < 1 / 10) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      (2 : ℝ) ^ (-((n : ℝ) * ((d : ℝ) - χ)))
        < 2 * Real.exp (-((n : ℝ) ^ ((1 : ℝ) / 10))) := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdχ : (19 / 10 : ℝ) < (d : ℝ) - χ := by linarith
  have hlog : (1 : ℝ) < ((d : ℝ) - χ) * Real.log 2 := by
    have h2 := Real.log_two_gt_d9
    nlinarith [hdχ, h2]
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    have h : (((1 : ℕ)) : ℝ) ≤ (((n : ℕ)) : ℝ) := Nat.cast_le.mpr hn
    simpa using h
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hroot : (n : ℝ) ^ ((1 : ℝ) / 10) ≤ (n : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : ((1 : ℝ) / 10) ≤ 1)
    rwa [Real.rpow_one] at h
  have hL : (2 : ℝ) ^ (-((n : ℝ) * ((d : ℝ) - χ)))
      = Real.exp (Real.log 2 * (-((n : ℝ) * ((d : ℝ) - χ)))) :=
    Real.rpow_def_of_pos (x := 2) (by norm_num) _
  have hR : 2 * Real.exp (-((n : ℝ) ^ ((1 : ℝ) / 10)))
      = Real.exp (Real.log 2 + -((n : ℝ) ^ ((1 : ℝ) / 10))) := by
    rw [Real.exp_add, Real.exp_log (show (0 : ℝ) < 2 by norm_num)]
  rw [hL, hR, Real.exp_lt_exp]
  nlinarith [hroot, hlog, hnpos, hlog2pos]

private lemma polyWeylKernel_add_one_direct (P : Polynomial ℤ) (N : ℕ) (θ : ℝ) :
    polyWeylKernel P N (θ + 1) = polyWeylKernel P N θ := by
  unfold polyWeylKernel
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  have harg : (2 * Real.pi * Complex.I) * ((((θ + 1) * ((P.eval (n : ℤ) : ℤ) : ℝ) : ℝ)) : ℂ)
      = (2 * Real.pi * Complex.I) * (((θ * ((P.eval (n : ℤ) : ℤ) : ℝ) : ℝ)) : ℂ)
        + ((P.eval (n : ℤ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

private lemma arc_ratio (P : Polynomial ℤ) (hc : 0 < P.leadingCoeff) {q : ℕ} (hq : q ≠ 0)
    (a : ℕ) (j : ℤ) :
    ((((a : ℤ) + j * (q : ℤ) : ℤ) : ℝ) / ((q * P.leadingCoeff.toNat : ℕ) : ℝ))
      = ((a : ℝ) / (q : ℝ) + (j : ℝ)) / (P.leadingCoeff : ℝ) := by
  have hcN : ((P.leadingCoeff.toNat : ℕ) : ℝ) = (P.leadingCoeff : ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg (le_of_lt hc))
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have hcR : (P.leadingCoeff : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hc)
  push_cast
  rw [hcN]
  field_simp

theorem mst_minor_sup_direct
    (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (hc : 0 < P.leadingCoeff)
    {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10)
    (η : ℝ → ℂ) (M : ℝ) (hM : 0 ≤ M) (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M)
    (hη1 : ∀ x : ℝ, |x| ≤ 1 / 4 → η x = 1) (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0)
    {α : ℝ} (hα : 0 < α) :
    ∃ l₀ : ℕ, ∀ l : ℕ, l₀ ≤ l → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∀ ξ : Work.BourgainPlan.IonescuWainger.Circle,
        ‖star (Work.BourgainPlan.Maximal.mstWeyl P (2 ^ n) ξ) *
            (1 - Work.BourgainPlan.Maximal.mstXi l P.natDegree χ η n ξ)‖
          ≤ C * ((n : ℝ) + 1) ^ (-α) := by
  obtain ⟨A, σ, Cg, c₀, hApos, hσpos, hCgpos, hc₀pos, hoff⟩ :=
    polyWeylKernel_offArc_gauss P hc hd
  obtain ⟨ConArc, hConArcpos, Nona, honarc⟩ := onArc_kernel_decay P hc hd hχ0 hα
  have hcR : (0 : ℝ) < (P.leadingCoeff : ℝ) := by exact_mod_cast hc
  have hcR1 : (1 : ℝ) ≤ (P.leadingCoeff : ℝ) := by
    have : (1 : ℤ) ≤ P.leadingCoeff := by omega
    exact_mod_cast this
  refine ⟨⌈(α + 2) / σ⌉₊ + 3, fun l hl => ?_⟩
  have hl1 : 1 ≤ l := by
    have h1 : 1 ≤ ⌈(α + 2) / σ⌉₊ + 3 := by omega
    omega
  have hlR : (α + 2) / σ + 3 ≤ (l : ℝ) := by
    have h1 : (α + 2) / σ ≤ (((⌈(α + 2) / σ⌉₊ : ℕ)) : ℝ) := Nat.le_ceil _
    have h2 : (((⌈(α + 2) / σ⌉₊ : ℕ)) : ℝ) + 3 ≤ (l : ℝ) := by
      have h3 : (((⌈(α + 2) / σ⌉₊ + 3 : ℕ)) : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
      push_cast at h3
      linarith
    linarith
  have hlsub : α + 1 ≤ ((l : ℝ) - 1) * σ := by
    have hle : (α + 2) / σ + 2 ≤ (l : ℝ) - 1 := by linarith
    have h2 : ((α + 2) / σ + 2) * σ ≤ ((l : ℝ) - 1) * σ :=
      mul_le_mul_of_nonneg_right hle hσpos.le
    have h3 : ((α + 2) / σ + 2) * σ = α + 2 + 2 * σ := by
      field_simp
    nlinarith [h2, h3, hσpos]
  obtain ⟨Nnum1, hnum1⟩ := offArc_numeric A σ Cg c₀ α l hApos hσpos hCgpos hc₀pos hα hl1 hlsub
  obtain ⟨Nnum2, hnum2⟩ := nat_pow_le_two_rpow_mul (l - 1) (by norm_num : (0 : ℝ) < 1 / 4)
  have hρpos : 0 < mstRho l := by rw [mstRho]; positivity
  obtain ⟨Nsep, hsep_all⟩ := sigmaN_separated (ρ := mstRho l) hρpos
  obtain ⟨Nsep2, hsepbound⟩ := exp_neg_sep_bound_direct (d := P.natDegree) hd hχ1
  refine ⟨(1 + M) * max 1 ConArc + 1, by positivity,
    max Nona (max Nnum1 (max Nnum2 (max Nsep (max Nsep2
      (max P.leadingCoeff.toNat (max (2 ^ 21) 4)))))),
    fun n hn ξ => ?_⟩
  simp only [max_le_iff] at hn
  obtain ⟨hnona, hnn1, hnn2, hnsep, hnsep2, hncn, hn21, hn4⟩ := hn
  have hn1 : 1 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hN3 : 3 ≤ 2 ^ n := by
    have h : 2 ^ 2 ≤ (2 : ℕ) ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    rw [show (2 : ℕ) ^ 2 = 4 from by norm_num] at h
    omega
  set τ : ℕ := n ^ (l - 1) with hτdef
  have hτne : τ ≠ 0 := by rw [hτdef]; exact pow_ne_zero _ (by omega)
  have hτpos : (0 : ℝ) < (τ : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hτne)
  set m : ℕ := Nat.log 2 τ with hmdef
  have hm_le : 2 ^ m ≤ τ := by rw [hmdef]; exact Nat.pow_log_le_self 2 hτne
  have hm_lt : τ < 2 ^ (m + 1) := by
    have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) τ
    rw [← hmdef] at h
    simpa [Nat.succ_eq_add_one] using h
  have hτcast : ((τ : ℕ) : ℝ) = (n : ℝ) ^ (l - 1) := by rw [hτdef, Nat.cast_pow]
  -- separation
  set sep : ℝ := 2 * Real.exp (-(((n ^ l : ℕ) : ℝ) ^ (mstRho l))) with hsepdef
  have hsep : ∀ β ∈ mstU l n, ∀ β' ∈ mstU l n, β ≠ β' → sep ≤ ‖β - β'‖ := by
    intro β hβ β' hβ' hne
    have h1 : Nsep ≤ n ^ l := le_trans hnsep (Nat.le_self_pow (n := l) (by omega) n)
    have h2 : β ∈ IonescuWainger.sigmaLeFinset (IonescuWainger.taoSetS (mstRho l) (n ^ l))
        (⌊2 / mstRho l⌋₊ + 1) := by simpa [mstU, iwSigma, iwK] using hβ
    have h3 : β' ∈ IonescuWainger.sigmaLeFinset (IonescuWainger.taoSetS (mstRho l) (n ^ l))
        (⌊2 / mstRho l⌋₊ + 1) := by simpa [mstU, iwSigma, iwK] using hβ'
    have := hsep_all (n ^ l) h1 β h2 β' h3 hne
    rwa [hsepdef]
  have hrpow : (((n ^ l : ℕ) : ℝ)) ^ (mstRho l) = (n : ℝ) ^ ((1 : ℝ) / 10) := by
    have h1 : (((n ^ l : ℕ) : ℝ)) = (n : ℝ) ^ ((l : ℕ) : ℝ) := by
      rw [Nat.cast_pow, Real.rpow_natCast]
    rw [h1, show mstRho l = 1 / (10 * (l : ℝ)) from rfl, ← Real.rpow_mul (le_of_lt hnpos)]
    have hexp : ((l : ℕ) : ℝ) * (1 / (10 * (l : ℝ))) = 1 / 10 := by
      have hlne : ((l : ℕ) : ℝ) ≠ 0 := by positivity
      rw [mul_one_div]
      have h := mul_div_mul_right (1 : ℝ) 10 hlne
      simpa using h
    rw [hexp]
  have hsep_gt : (2 : ℝ) ^ (-((n : ℝ) * ((P.natDegree : ℝ) - χ))) < sep := by
    rw [hsepdef, hrpow]
    exact hsepbound n hnsep2
  have hgeom := mstXi_bound_and_eq_one (l := l) (d := P.natDegree) (χ := χ) (η := η) (n := n)
    (sep := sep) (M := M) hηbd hη1 hη2 hsep hsep_gt ξ
  have hXi_le : ‖mstXi l P.natDegree χ η n ξ‖ ≤ M := hgeom.1
  have hXi_one := hgeom.2
  have hXi_norm : ‖(1 : ℂ) - mstXi l P.natDegree χ η n ξ‖ ≤ 1 + M := by
    calc ‖(1 : ℂ) - mstXi l P.natDegree χ η n ξ‖
        ≤ ‖(1 : ℂ)‖ + ‖mstXi l P.natDegree χ η n ξ‖ := norm_sub_le _ _
      _ ≤ 1 + M := by rw [norm_one]; linarith
  -- the reduction of `θ = iwRep ξ` to `[0,1]`
  set θ : ℝ := iwRep ξ with hθdef
  set th : ℝ := if 0 ≤ θ then θ else θ + 1 with hthdef
  have hth0 : 0 ≤ th := by
    rw [hthdef]; split_ifs with h
    · exact h
    · have hmem := iwRep_mem_Ioc ξ
      rw [hθdef] at h ⊢
      rw [Set.mem_Ioc] at hmem
      linarith [hmem.1]
  have hth1 : th ≤ 1 := by
    rw [hthdef]; split_ifs with h
    · have hmem := iwRep_mem_Ioc ξ
      rw [hθdef] at h ⊢
      rw [Set.mem_Ioc] at hmem
      linarith [hmem.2]
    · linarith
  have hker_per : polyWeylKernel P (2 ^ n) th = polyWeylKernel P (2 ^ n) θ := by
    rw [hthdef]; split_ifs with h
    · rfl
    · exact polyWeylKernel_add_one_direct P (2 ^ n) θ
  have hcoe_th : ((th : ℝ) : Work.BourgainPlan.IonescuWainger.Circle) = ξ := by
    rw [hthdef]; split_ifs with h
    · rw [hθdef]; exact coe_iwRep ξ
    · rw [AddCircle.coe_add, hθdef, coe_iwRep ξ]
      have hone : (((1 : ℝ)) : Work.BourgainPlan.IonescuWainger.Circle) = 0 := by
        rw [AddCircle.coe_eq_zero_iff]
        exact ⟨1, by simp⟩
      rw [hone, add_zero]
  set arcRad : ℝ := (((2 ^ n : ℕ)) : ℝ) ^ (-((P.natDegree : ℝ) - (1 : ℝ) / 4)) with harcRad
  have hNpos : (0 : ℝ) < (((2 ^ n : ℕ)) : ℝ) := by positivity
  have harcRad_lt : arcRad < 1 / 2 := by
    have hN4 : (4 : ℝ) ≤ (((2 ^ n : ℕ)) : ℝ) := by
      have h : (4 : ℕ) ≤ 2 ^ n := by
        have h2 := Nat.pow_le_pow_right (by norm_num : 0 < 2) hn2
        simpa using h2
      exact_mod_cast h
    have hNp : (0 : ℝ) < (((2 ^ n : ℕ)) : ℝ) := by linarith
    have hexp : (3 / 2 : ℝ) ≤ (P.natDegree : ℝ) - 1 / 4 := by
      have hdR : (2 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd
      linarith
    have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    have hpow : (8 : ℝ) ≤ (((2 ^ n : ℕ)) : ℝ) ^ ((P.natDegree : ℝ) - 1 / 4) := by
      have hbase : (((2 ^ n : ℕ)) : ℝ) = (2 : ℝ) ^ n := by push_cast; norm_num
      rw [hbase, ← Real.rpow_natCast (2 : ℝ) n,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      have h3 : ((3 : ℕ) : ℝ) ≤ (n : ℝ) * ((P.natDegree : ℝ) - 1 / 4) := by
        have h4 : (3 : ℝ) ≤ (n : ℝ) * ((P.natDegree : ℝ) - 1 / 4) := by nlinarith [hn2R, hexp]
        simpa using h4
      have h83 : (8 : ℝ) = (2 : ℝ) ^ ((3 : ℕ) : ℝ) := by rw [Real.rpow_natCast]; norm_num
      rw [h83]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h3
    rw [harcRad, Real.rpow_neg (le_of_lt hNp)]
    have hpos : (0 : ℝ) < (((2 ^ n : ℕ)) : ℝ) ^ ((P.natDegree : ℝ) - 1 / 4) :=
      Real.rpow_pos_of_pos hNp _
    calc ((((2 ^ n : ℕ)) : ℝ) ^ ((P.natDegree : ℝ) - 1 / 4))⁻¹ ≤ (8 : ℝ)⁻¹ :=
          (inv_le_inv₀ hpos (by norm_num : (0 : ℝ) < 8)).mpr hpow
      _ < 1 / 2 := by norm_num
  by_cases hcase : ¬ (∃ (q a : ℕ) (j : ℤ), 1 ≤ q ∧ q ≤ τ ∧ a < q ∧ Nat.gcd a q = 1 ∧
      j ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff ∧
      |(P.leadingCoeff : ℝ) * th - (a : ℝ) / (q : ℝ) - (j : ℝ)| ≤ arcRad)
  · -- ## Case 1: `θ` is off every arc of denominator `≤ τ`
    have hoffarc : ∀ (q a : ℕ) (j : ℤ), 1 ≤ q → q < 2 ^ m → a < q → Nat.gcd a q = 1 →
        j ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff →
        arcRad < |(P.leadingCoeff : ℝ) * th - (a : ℝ) / (q : ℝ) - (j : ℝ)| := by
      intro q a j hq hqm haq hg hj
      have hqτ : q ≤ τ := by omega
      by_contra hle
      exact hcase ⟨q, a, j, hq, hqτ, haq, hg, hj, le_of_not_gt hle⟩
    have hker := hoff m (2 ^ n) th hN3 hth0 hth1 hoffarc
    have hmt : ((2 : ℝ) ^ m) ^ (-σ) ≤ (2 : ℝ) ^ σ * (((n : ℝ) ^ (l - 1)) ^ (-σ)) := by
      have h1 : ((2 : ℝ) ^ m) ^ (-σ) ≤ ((τ : ℝ) / 2) ^ (-σ) := by
        refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith [hσpos])
        have h := hm_lt
        have h2 : (τ : ℝ) < (2 : ℝ) ^ (m + 1) := by exact_mod_cast h
        rw [pow_succ] at h2
        push_cast
        linarith
      have h2 : ((τ : ℝ) / 2) ^ (-σ) = (2 : ℝ) ^ σ * (τ : ℝ) ^ (-σ) := by
        rw [div_eq_mul_inv,
          Real.mul_rpow (le_of_lt hτpos) (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹),
          Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2),
          ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), neg_neg]
        ring
      rw [h2] at h1
      rw [hτcast] at h1
      exact h1
    have hAterm : A * (2 : ℝ) ^ (-(m : ℝ) * σ)
        ≤ A * (2 : ℝ) ^ σ * (((n : ℝ) ^ (l - 1)) ^ (-σ)) := by
      have heq : (2 : ℝ) ^ (-(m : ℝ) * σ) = ((2 : ℝ) ^ m) ^ (-σ) := by
        rw [← Real.rpow_natCast (2 : ℝ) m, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
      rw [heq]
      calc A * ((2 : ℝ) ^ m) ^ (-σ) ≤ A * ((2 : ℝ) ^ σ * (((n : ℝ) ^ (l - 1)) ^ (-σ))) :=
            mul_le_mul_of_nonneg_left hmt hApos.le
        _ = A * (2 : ℝ) ^ σ * (((n : ℝ) ^ (l - 1)) ^ (-σ)) := by ring
    have hCterm : (((2 ^ n : ℕ)) : ℝ) ^ (-c₀) = (2 : ℝ) ^ (-(n : ℝ) * c₀) := by
      have hbase : (((2 ^ n : ℕ)) : ℝ) = (2 : ℝ) ^ n := by push_cast; norm_num
      rw [hbase, ← Real.rpow_natCast (2 : ℝ) n,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    have hb1 : ‖polyWeylKernel P (2 ^ n) th‖ ≤ ((n : ℝ) + 1) ^ (-α) := by
      calc ‖polyWeylKernel P (2 ^ n) th‖
          ≤ A * (2 : ℝ) ^ (-(m : ℝ) * σ) + Cg * (((2 ^ n : ℕ)) : ℝ) ^ (-c₀) := hker
        _ ≤ A * (2 : ℝ) ^ σ * (((n : ℝ) ^ (l - 1)) ^ (-σ))
              + Cg * (2 : ℝ) ^ (-(n : ℝ) * c₀) := by
            rw [hCterm]
            exact add_le_add hAterm le_rfl
        _ ≤ ((n : ℝ) + 1) ^ (-α) := hnum1 n hnn1
    have hkerθ : ‖polyWeylKernel P (2 ^ n) θ‖ ≤ ((n : ℝ) + 1) ^ (-α) := by
      rw [← hker_per]
      exact hb1
    calc ‖star (mstWeyl P (2 ^ n) ξ) * (1 - mstXi l P.natDegree χ η n ξ)‖
        = ‖mstWeyl P (2 ^ n) ξ‖ * ‖(1 : ℂ) - mstXi l P.natDegree χ η n ξ‖ := by
          rw [norm_mul, norm_star]
      _ = ‖polyWeylKernel P (2 ^ n) θ‖ * ‖(1 : ℂ) - mstXi l P.natDegree χ η n ξ‖ := by
          rw [mstWeyl_apply]
      _ ≤ ((n : ℝ) + 1) ^ (-α) * (1 + M) :=
          mul_le_mul hkerθ hXi_norm (norm_nonneg _) (Real.rpow_nonneg (by positivity) _)
      _ ≤ ((1 + M) * max 1 ConArc + 1) * ((n : ℝ) + 1) ^ (-α) := by
          rw [mul_comm (((n : ℝ) + 1) ^ (-α)) (1 + M)]
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
          nlinarith [hM, le_max_left (1 : ℝ) ConArc, hConArcpos.le]
  · -- ## Case 2: `θ` lies on an arc of denominator `≤ τ`
    obtain ⟨q, a, j, hq1, hqτ, haq, hgcd, hj, harc⟩ := not_not.mp hcase
    have hqne : q ≠ 0 := by omega
    have hcnpos : 0 < P.leadingCoeff.toNat := by
      have h : (0 : ℤ) < (P.leadingCoeff.toNat : ℤ) := by
        rw [Int.toNat_of_nonneg (le_of_lt hc)]
        exact hc
      exact_mod_cast h
    have hden : P.leadingCoeff.toNat * q ≤ n ^ l := by
      calc P.leadingCoeff.toNat * q ≤ P.leadingCoeff.toNat * τ := Nat.mul_le_mul_left _ hqτ
        _ = P.leadingCoeff.toNat * n ^ (l - 1) := by rw [hτdef]
        _ ≤ n * n ^ (l - 1) := Nat.mul_le_mul_right _ hncn
        _ = n ^ (l - 1) * n := by ring
        _ = n ^ ((l - 1) + 1) := (pow_succ n (l - 1)).symm
        _ = n ^ l := by rw [Nat.sub_add_cancel hl1]
    have hNmem : 2 ^ iwK (mstRho l) ≤ n ^ l := by
      have hK : iwK (mstRho l) = 20 * l + 1 := by
        rw [iwK, mstRho]
        have h1 : 2 / (1 / (10 * (l : ℝ))) = ((20 * l : ℕ) : ℝ) := by
          push_cast
          field_simp
          norm_num
        rw [h1, Nat.floor_natCast]
      rw [hK]
      calc 2 ^ (20 * l + 1) ≤ 2 ^ (21 * l) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = (2 ^ 21) ^ l := by rw [← pow_mul]
        _ ≤ n ^ l := Nat.pow_le_pow_left hn21 l
    have hb0 : arcPt (P.leadingCoeff.toNat * q) ((a : ℤ) + j * (q : ℤ)) ∈ mstU l n := by
      have hq1' : 1 ≤ P.leadingCoeff.toNat * q :=
        Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      obtain ⟨A', hAS, hAcard, hdiv⟩ :=
        farey_cover_by_taoSetS (mstRho l) hρpos (n ^ l) (by simpa [iwK] using hNmem)
          (P.leadingCoeff.toNat * q) hq1' hden
      rw [mstU, iwSigma, sigmaLeFinset, Finset.mem_biUnion]
      refine ⟨A', ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_powerset]
        exact ⟨hAS, by rw [iwK]; exact hAcard⟩
      · exact arcPt_mem_sigmaSubAFinset_of_dvd hq1' (QA_ne_zero_of_subset_taoSetS hAS) hdiv _
    set β : ℝ := th - (((a : ℝ) / (q : ℝ) + (j : ℝ)) / (P.leadingCoeff : ℝ)) with hβdef
    have hβcoeeq : ((β : ℝ) : Work.BourgainPlan.IonescuWainger.Circle)
        = ξ - arcPt (P.leadingCoeff.toNat * q) ((a : ℤ) + j * (q : ℤ)) := by
      have h1 : ((((a : ℝ) / (q : ℝ) + (j : ℝ)) / (P.leadingCoeff : ℝ) : ℝ))
          = ((((a : ℤ) + j * (q : ℤ) : ℤ) : ℝ) / ((q * P.leadingCoeff.toNat : ℕ) : ℝ)) :=
        (arc_ratio P hc hqne a j).symm
      rw [hβdef, h1, AddCircle.coe_sub, hcoe_th, arcPt, Nat.mul_comm q P.leadingCoeff.toNat]
    have hβabs : |β| ≤ arcRad / (P.leadingCoeff : ℝ) := by
      have hcb : (P.leadingCoeff : ℝ) * β
          = (P.leadingCoeff : ℝ) * th - ((a : ℝ) / (q : ℝ) + (j : ℝ)) := by
        rw [hβdef]
        field_simp
      have h4 : (P.leadingCoeff : ℝ) * |β|
          = |(P.leadingCoeff : ℝ) * th - ((a : ℝ) / (q : ℝ) + (j : ℝ))| := by
        rw [← hcb, abs_mul, abs_of_pos hcR]
      have h5 : |β| = |(P.leadingCoeff : ℝ) * th - ((a : ℝ) / (q : ℝ) + (j : ℝ))|
          / (P.leadingCoeff : ℝ) := by
        rw [← h4, mul_div_cancel_left₀ _ (ne_of_gt hcR)]
      have h6 : |(P.leadingCoeff : ℝ) * th - ((a : ℝ) / (q : ℝ) + (j : ℝ))| ≤ arcRad := by
        rw [show (P.leadingCoeff : ℝ) * th - ((a : ℝ) / (q : ℝ) + (j : ℝ))
            = (P.leadingCoeff : ℝ) * th - (a : ℝ) / (q : ℝ) - (j : ℝ) by ring]
        exact harc
      rw [h5]
      exact div_le_div_of_nonneg_right h6 hcR.le
    have harcRad_nn : 0 ≤ arcRad := by rw [harcRad]; positivity
    have hβhalf : |β| < 1 / 2 := by
      have h1 : arcRad / (P.leadingCoeff : ℝ) ≤ arcRad := by
        rw [div_le_iff₀ hcR]
        nlinarith [harcRad_nn, hcR1]
      exact lt_of_le_of_lt (le_trans hβabs h1) harcRad_lt
    have hβmem : β ∈ Set.Ioc (-(1 / 2) : ℝ) (-(1 / 2) + 1) := by
      rw [Set.mem_Ioc]
      exact ⟨by linarith [neg_abs_le β], by linarith [le_abs_self β]⟩
    have hiwrep : iwRep (ξ - arcPt (P.leadingCoeff.toNat * q) ((a : ℤ) + j * (q : ℤ))) = β := by
      rw [← hβcoeeq]
      show AddCircle.liftIoc (1 : ℝ) (-(1 / 2)) (fun y : ℝ => y)
        ((β : ℝ) : Work.BourgainPlan.IonescuWainger.Circle) = β
      exact AddCircle.liftIoc_coe_apply (f := fun y : ℝ => y) hβmem
    have hqquarter : (q : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * (1 / 4)) := by
      have h1 : (q : ℝ) ≤ (τ : ℝ) := by exact_mod_cast hqτ
      have h2 : (τ : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * (1 / 4)) := by
        rw [hτcast]
        have h3 := hnum2 n hnn2
        rwa [show (2 : ℝ) ^ ((1 : ℝ) / 4 * (n : ℝ)) = (2 : ℝ) ^ ((n : ℝ) * (1 / 4))
          from by ring_nf] at h3
      linarith
    by_cases hXi : mstXi l P.natDegree χ η n ξ = 1
    · rw [hXi, sub_self, mul_zero, norm_zero]
      positivity
    · have hgt : (1 / 4 : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * ((P.natDegree : ℝ) - χ))) < |β| := by
        by_contra hle
        rw [not_lt] at hle
        exact hXi (hXi_one (arcPt (P.leadingCoeff.toNat * q) ((a : ℤ) + j * (q : ℤ))) hb0
          (by rw [hiwrep]; exact hle))
      have hkerII : ‖polyWeylKernel P (2 ^ n) th‖ ≤ ConArc * ((n : ℝ) + 1) ^ (-α) :=
        honarc n hnona q a j th hq1 hqquarter haq hgcd hj harc hgt
      have hkerθ : ‖polyWeylKernel P (2 ^ n) θ‖ ≤ ConArc * ((n : ℝ) + 1) ^ (-α) := by
        rw [← hker_per]
        exact hkerII
      calc ‖star (mstWeyl P (2 ^ n) ξ) * (1 - mstXi l P.natDegree χ η n ξ)‖
          = ‖polyWeylKernel P (2 ^ n) θ‖ * ‖(1 : ℂ) - mstXi l P.natDegree χ η n ξ‖ := by
            rw [norm_mul, norm_star, mstWeyl_apply]
        _ ≤ ConArc * ((n : ℝ) + 1) ^ (-α) * (1 + M) :=
            mul_le_mul hkerθ hXi_norm (norm_nonneg _) (by positivity)
        _ = ((1 + M) * ConArc) * ((n : ℝ) + 1) ^ (-α) := by ring
        _ ≤ ((1 + M) * max 1 ConArc + 1) * ((n : ℝ) + 1) ^ (-α) := by
            apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
            nlinarith [hM, le_max_right (1 : ℝ) ConArc, hConArcpos.le]

end Work.BourgainPlan.Maximal
