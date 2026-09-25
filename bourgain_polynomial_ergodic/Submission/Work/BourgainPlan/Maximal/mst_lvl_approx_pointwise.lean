import Mathlib
import Submission.Work.BourgainPlan.Maximal.mstU_rep
import Submission.Work.BourgainPlan.Maximal.mst_major_err1_l2
import Submission.Work.BourgainPlan.Maximal.major_arc_nbd_bound
import Submission.Work.BourgainPlan.Maximal.polyProfile_sub_one_le
import Submission.Work.BourgainPlan.Maximal.mstG_spec

namespace Work.BourgainPlan.Maximal

open Finset
open scoped BigOperators

open Work.BourgainPlan.IonescuWainger

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle

/-! ## Sublinearity of the level parameters -/

/-- For every `B > 0` and all large `s`, `√(s+1) ≤ B·s`. -/
lemma sqrt_add_one_le_mul (B : ℝ) (hB : 0 < B) :
    ∃ N₁ : ℕ, ∀ s : ℕ, N₁ ≤ s → Real.sqrt ((s : ℝ) + 1) ≤ B * (s : ℝ) := by
  have hB2 : 0 < B ^ 2 := by positivity
  refine ⟨max 1 ⌈2 / B ^ 2⌉₊, fun s hs => ?_⟩
  have hs1 : 1 ≤ s := le_trans (le_max_left _ _) hs
  have hsnn : (0 : ℝ) ≤ (s : ℝ) := by positivity
  have h2 : 2 / B ^ 2 ≤ (s : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hs)
  have h3 : 2 ≤ B ^ 2 * (s : ℝ) := by
    rw [div_le_iff₀ hB2] at h2; linarith
  have h4 : (s : ℝ) + 1 ≤ B ^ 2 * (s : ℝ) ^ 2 := by
    have h5 : (2 : ℝ) * (s : ℝ) ≤ B ^ 2 * (s : ℝ) * (s : ℝ) := by
      have := mul_le_mul_of_nonneg_right h3 hsnn
      simpa [mul_assoc] using this
    have hsR1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs1
    nlinarith [h5, hsnn]
  have h6 : Real.sqrt ((s : ℝ) + 1) ≤ Real.sqrt (B ^ 2 * (s : ℝ) ^ 2) :=
    Real.sqrt_le_sqrt h4
  rw [Real.sqrt_mul hB2.le, Real.sqrt_sq hB.le, Real.sqrt_sq hsnn] at h6
  exact h6

/-- For every `B > 0` and all large `s`, `(s+1)^{1/10} ≤ B·s`. -/
lemma rpow_ten_add_one_le_mul (B : ℝ) (hB : 0 < B) :
    ∃ N₁ : ℕ, ∀ s : ℕ, N₁ ≤ s → ((s : ℝ) + 1) ^ (1 / 10 : ℝ) ≤ B * (s : ℝ) := by
  obtain ⟨n₀, hn₀⟩ := rpow_ten_le_mul (B / 2) (by positivity)
  refine ⟨max n₀ 1, fun s hs => ?_⟩
  have hs1 : 1 ≤ s := le_trans (le_max_right _ _) hs
  have hsR1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs1
  have h := hn₀ (s + 1) (by omega : n₀ ≤ s + 1)
  have hcast : (((s + 1 : ℕ)) : ℝ) = (s : ℝ) + 1 := by push_cast; ring
  rw [hcast] at h
  calc ((s : ℝ) + 1) ^ (1 / 10 : ℝ) ≤ (B / 2) * ((s : ℝ) + 1) := h
    _ = (B / 2) * (s : ℝ) + B / 2 := by ring
    _ ≤ B * (s : ℝ) := by nlinarith

/-- **The exponent conditions for the level-`s` approximation at scale
`J = ⌊exp √(s+1)⌋`.**  For all large `s`, with `α = (s+1)^{1/10}`, `t = √(s+1)`: the integer `⌊e^t⌋`
is `≥ 3` and dominates `2e^α`, and the four exponent inequalities that let the major-arc error
`2^{−s(d−χ)} J^{d−1} + J^{−1}` together with the profile error be absorbed into `e^{−t/2}` hold. -/
lemma mst_lvl_exp_arith (d : ℕ) (hd : 2 ≤ d) {χ : ℝ} (hχ1 : χ < 1 / 10) :
    ∃ N₁ : ℕ, ∀ s : ℕ, N₁ ≤ s →
      3 ≤ ⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊ ∧
      2 * Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ))
        ≤ (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊ : ℝ) ∧
      ((s : ℝ) + 1) ^ (1 / 10 : ℝ) + ((d : ℝ) - 1) * Real.sqrt ((s : ℝ) + 1)
        ≤ (s : ℝ) * ((d : ℝ) - χ) * Real.log 2 - Real.sqrt ((s : ℝ) + 1) / 2 ∧
      ((s : ℝ) + 1) ^ (1 / 10 : ℝ) + Real.log 2 ≤ Real.sqrt ((s : ℝ) + 1) / 2 ∧
      (d : ℝ) * Real.sqrt ((s : ℝ) + 1)
        ≤ (s : ℝ) * ((d : ℝ) - χ) * Real.log 2 - Real.sqrt ((s : ℝ) + 1) / 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hβpos : 0 < ((d : ℝ) - χ) * Real.log 2 := by
    have : 0 < (d : ℝ) - χ := by linarith
    exact mul_pos this hlog2
  set β : ℝ := ((d : ℝ) - χ) * Real.log 2 with hβdef
  have hβ : 0 < β := hβpos
  obtain ⟨Ns, hNs⟩ := sqrt_add_one_le_mul (β / (3 * ((d : ℝ) + 1))) (by positivity)
  obtain ⟨Nt, hNt⟩ := rpow_ten_add_one_le_mul (β / 3) (by positivity)
  refine ⟨max (max Ns Nt) (max ⌈3 / β⌉₊ 64), fun s hs => ?_⟩
  have hs_s : Ns ≤ s := by omega
  have hs_t : Nt ≤ s := by omega
  have hs_c : ⌈3 / β⌉₊ ≤ s := by omega
  have hs_64 : 64 ≤ s := by omega
  set t : ℝ := Real.sqrt ((s : ℝ) + 1) with htdef
  have hxpos : 0 < (s : ℝ) + 1 := by positivity
  have hx32 : (32 : ℝ) ≤ (s : ℝ) + 1 := by
    have h32 : (32 : ℝ) ≤ (s : ℝ) := by exact_mod_cast (by omega : 32 ≤ s)
    linarith
  have hs64R : (64 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs_64
  have ht8 : 8 ≤ t := by
    rw [htdef]
    calc (8 : ℝ) = Real.sqrt ((8 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ = Real.sqrt 64 := by norm_num
      _ ≤ Real.sqrt ((s : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
  have hpow : ((32 : ℝ)) ^ (2 / 5 : ℝ) = 4 := by
    have h2 : (0 : ℝ) ≤ 2 := by norm_num
    rw [show (32 : ℝ) = (2 : ℝ) ^ 5 by norm_num, ← Real.rpow_natCast (2 : ℝ) 5,
      ← Real.rpow_mul h2]
    norm_num
  have hx25 : (4 : ℝ) ≤ ((s : ℝ) + 1) ^ (2 / 5 : ℝ) := by
    rw [← hpow]
    exact Real.rpow_le_rpow (by norm_num) hx32 (by norm_num)
  have hsplit : ((s : ℝ) + 1) ^ ((1 : ℝ) / 2)
      = ((s : ℝ) + 1) ^ (1 / 10 : ℝ) * ((s : ℝ) + 1) ^ (2 / 5 : ℝ) := by
    rw [← Real.rpow_add hxpos]; norm_num
  have ht_eq : t = ((s : ℝ) + 1) ^ ((1 : ℝ) / 2) := by rw [htdef, Real.sqrt_eq_rpow]
  have hten_quarter : ((s : ℝ) + 1) ^ (1 / 10 : ℝ) ≤ t / 4 := by
    rw [ht_eq, hsplit, le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
    have hx10 : 0 ≤ ((s : ℝ) + 1) ^ (1 / 10 : ℝ) := (Real.rpow_pos_of_pos hxpos _).le
    have := mul_le_mul_of_nonneg_left hx25 hx10
    linarith
  have hlog1 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlog_quarter : Real.log 2 ≤ t / 4 := by linarith
  have ha0 : 0 ≤ ((s : ℝ) + 1) ^ (1 / 10 : ℝ) := (Real.rpow_pos_of_pos hxpos _).le
  have hmain : ((d : ℝ) + 1) * t + ((s : ℝ) + 1) ^ (1 / 10 : ℝ) + 1 ≤ β * (s : ℝ) := by
    have h1 : ((d : ℝ) + 1) * t ≤ β / 3 * (s : ℝ) := by
      have hs' := hNs s hs_s
      rw [← htdef] at hs'
      calc ((d : ℝ) + 1) * t
          ≤ ((d : ℝ) + 1) * (β / (3 * ((d : ℝ) + 1)) * (s : ℝ)) :=
            mul_le_mul_of_nonneg_left hs' (by linarith)
        _ = β / 3 * (s : ℝ) := by field_simp
    have h2 : ((s : ℝ) + 1) ^ (1 / 10 : ℝ) ≤ β / 3 * (s : ℝ) := hNt s hs_t
    have h3 : 1 ≤ β / 3 * (s : ℝ) := by
      have hceil : 3 / β ≤ (s : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hs_c)
      rw [div_le_iff₀ hβ] at hceil
      linarith
    linarith
  have hmainE : ((d : ℝ) + 1) * t + ((s : ℝ) + 1) ^ (1 / 10 : ℝ) + 1
      ≤ (s : ℝ) * ((d : ℝ) - χ) * Real.log 2 := by
    have h := hmain
    rw [hβdef] at h
    rwa [show ((d : ℝ) - χ) * Real.log 2 * (s : ℝ) = (s : ℝ) * ((d : ℝ) - χ) * Real.log 2
      by ring] at h
  have hJ3 : 3 ≤ ⌊Real.exp t⌋₊ := by
    have he : (3 : ℝ) ≤ Real.exp t := by
      calc (3 : ℝ) ≤ Real.exp 4 := by
            have h := Real.add_one_le_exp (4 : ℝ); linarith [Real.exp_pos 4]
        _ ≤ Real.exp t := Real.exp_le_exp.mpr (by linarith)
    exact Nat.le_floor he
  have hJg : Real.exp t / 2 ≤ (⌊Real.exp t⌋₊ : ℝ) := by
    have h := Nat.lt_floor_add_one (Real.exp t)
    have he2 : (2 : ℝ) ≤ Real.exp t := by
      calc (2 : ℝ) ≤ Real.exp 1 := by
            have h := Real.add_one_le_exp (1 : ℝ); linarith [Real.exp_pos 1]
        _ ≤ Real.exp t := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hJexp : 2 * Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)) ≤ (⌊Real.exp t⌋₊ : ℝ) := by
    have hstep : 2 * Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)) ≤ Real.exp t / 2 := by
      have h1 : Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)) ≤ Real.exp (t / 4) :=
        Real.exp_le_exp.mpr hten_quarter
      have h4 : (4 : ℝ) ≤ Real.exp (3 * t / 4) := by
        have h := Real.add_one_le_exp (3 * t / 4); linarith [Real.exp_pos (3 * t / 4)]
      have h2 : 2 * Real.exp (t / 4) ≤ Real.exp t / 2 := by
        have hexp_t : Real.exp t = Real.exp (3 * t / 4) * Real.exp (t / 4) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [hexp_t, le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
        have hh := mul_le_mul_of_nonneg_right h4 (Real.exp_pos (t / 4)).le
        nlinarith [hh]
      calc 2 * Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)) ≤ 2 * Real.exp (t / 4) := by linarith
        _ ≤ Real.exp t / 2 := h2
    linarith
  have hexp2 : ((s : ℝ) + 1) ^ (1 / 10 : ℝ) + Real.log 2 ≤ t / 2 := by linarith
  have hexp1 : ((s : ℝ) + 1) ^ (1 / 10 : ℝ) + ((d : ℝ) - 1) * t
      ≤ (s : ℝ) * ((d : ℝ) - χ) * Real.log 2 - t / 2 := by
    nlinarith [hmainE, ht8, ha0]
  have hexp3 : (d : ℝ) * t ≤ (s : ℝ) * ((d : ℝ) - χ) * Real.log 2 - t / 2 := by
    nlinarith [hmainE, ht8, ha0]
  exact ⟨hJ3, hJexp, hexp1, hexp2, hexp3⟩

/-! ## The one-arc major-arc approximation at an arbitrary scale -/

/-- **The major-arc error at one level-`s` arc, at an arbitrary scale `N`.**  For `β ∈ 𝒰(s+1)` with a
representative `β = arcPt q a` carrying the weight `mstG P β = polyWeight P q a` and
`q ≤ e^{(s+1)^{1/10}}`, and for `ξ` in the support of the level bump `η_s(· − β)`, the Weyl kernel
`mstWeyl P N ξ` differs from the model term `mstG P β · mstProf P N (ξ − β)` by at most
`C e^{(s+1)^{1/10}} (2^{−s(d−χ)} N^{d−1} + N^{−1})`, provided `N ≥ 3` and
`2 e^{(s+1)^{1/10}} ≤ N`.

This is the general-scale form of `mst_major_err1_term` (`Maximal/mst_major_err1_l2.lean`), which
covers only the scales `N = 2^n` with the bump at the *same* level `n`.  The proof is the same:
the bump support gives `|iwRep (ξ − β)| ≤ ½·2^{−s(d−χ)}`; `major_arc_nbd_bound` is applied at the
real point `iwRep (ξ − β) + a/q` (whose class is that of `iwRep ξ`, so the Weyl kernel is the one at
`ξ`, and whose offset from `a/q` is exactly `iwRep (ξ − β)`, so the profile is the one at
`ξ − β`) with `M = 2^{s(d−χ)}` and `2^{l'}` the dyadic rounding of `q`. -/
lemma mst_lvl_arc_term (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    {χ : ℝ} (hχ1 : χ < 1 / 10) (η : ℝ → ℂ)
    (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0) (l : ℕ) (hl : 1 ≤ l) (N₀ : ℕ)
    (hrep : ∀ n : ℕ, N₀ ≤ n → ∀ β ∈ mstU l n, ∃ (q : ℕ) (a : ℤ),
      0 < q ∧ 0 ≤ a ∧ a < q ∧ Work.BourgainPlan.IonescuWainger.arcPt q a = β ∧
        mstG P β = polyWeight P q a ∧
        (q : ℝ) ≤ Real.exp (((n : ℝ) ^ l) ^ (mstRho l))) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₁ : ℕ, ∀ s : ℕ, N₁ ≤ s → ∀ (N : ℕ), 3 ≤ N →
      ∀ (β ξ : Circ), β ∈ mstU l (s + 1) → mstEta P.natDegree χ η s (ξ - β) ≠ 0 →
      2 * Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)) ≤ (N : ℝ) →
      ‖mstWeyl P N ξ - mstG P β * mstProf P N (ξ - β)‖
        ≤ C * (Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)) *
            ((2 : ℝ) ^ (-((s : ℝ) * ((P.natDegree : ℝ) - χ)))
                * (N : ℝ) ^ ((P.natDegree : ℝ) - 1) + (N : ℝ)⁻¹)) := by
  classical
  obtain ⟨Ca, hCa, hMA⟩ := major_arc_nbd_bound P hd
  refine ⟨2 * Ca, mul_pos (by norm_num) hCa, N₀, fun s hs N hN β ξ hβ hne hNexp => ?_⟩
  have hsN₀ : N₀ ≤ s + 1 := by omega
  have hs1 : 1 ≤ s + 1 := by omega
  obtain ⟨q, a, hq0, ha0, haq, harc, hG, hqbd⟩ := hrep (s + 1) hsN₀ β hβ
  have hq1 : 1 ≤ q := hq0
  set l' : ℕ := Nat.log 2 (2 * q) with hl'def
  have hq2l : q ≤ 2 ^ l' := by
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (2 * q)
    rw [← hl'def] at h
    rw [Nat.succ_eq_add_one, pow_add, pow_one] at h
    omega
  have h2l'' : 2 ^ l' ≤ 2 * q := by
    have h := Nat.pow_log_le_self 2 (by omega : 2 * q ≠ 0)
    rwa [← hl'def] at h
  have hql' : (q : ℝ) ≤ (2 : ℝ) ^ l' := by
    calc (q : ℝ) ≤ ((2 ^ l' : ℕ) : ℝ) := by exact_mod_cast hq2l
      _ = (2 : ℝ) ^ l' := by push_cast; ring
  have hqexp : (q : ℝ) ≤ Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)) := by
    have h := hqbd
    rw [mstRho_pow_eq_real l hl (s + 1) hs1] at h
    have hcast : (((s + 1 : ℕ)) : ℝ) = (s : ℝ) + 1 := by push_cast; ring
    rwa [hcast] at h
  have h2l' : (2 : ℝ) ^ l' ≤ 2 * Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)) := by
    calc (2 : ℝ) ^ l' = ((2 ^ l' : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((2 * q : ℕ) : ℝ) := by exact_mod_cast h2l''
      _ = 2 * (q : ℝ) := by push_cast; ring
      _ ≤ 2 * Real.exp _ := by linarith
  have hl'N : (2 : ℝ) ^ l' ≤ (N : ℝ) := le_trans h2l' hNexp
  set M : ℝ := (2 : ℝ) ^ ((s : ℝ) * ((P.natDegree : ℝ) - χ)) with hMdef
  have hM1 : 1 ≤ M := by
    rw [hMdef]
    refine Real.one_le_rpow (by norm_num) ?_
    have hd1 : (1 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast (by omega : 1 ≤ P.natDegree)
    have hde : 0 ≤ (P.natDegree : ℝ) - χ := by linarith
    exact mul_nonneg (by positivity) hde
  have hu : |iwRep (ξ - β)| ≤ (1 / 2) * (2 : ℝ) ^ (-((s : ℝ) * ((P.natDegree : ℝ) - χ))) :=
    mstEta_ne_zero_abs_iwRep P.natDegree χ η hη2 s hne
  have hcond : |(iwRep (ξ - β) + (a : ℝ) / (q : ℝ)) - (a : ℝ) / (q : ℝ)| ≤ 1 / M := by
    have h1 : |iwRep (ξ - β)| ≤ M⁻¹ := by
      rw [hMdef, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (-((s : ℝ) * ((P.natDegree : ℝ) - χ))) := by positivity
      linarith
    rw [add_sub_cancel_right, one_div]
    exact h1
  have hx : ((iwRep (ξ - β) + (a : ℝ) / (q : ℝ) : ℝ) : Circ) = ((iwRep ξ : ℝ) : Circ) := by
    rw [AddCircle.coe_add, coe_iwRep (ξ - β), coe_iwRep ξ, ← harc, arcPt]
    abel
  have hkey := hMA N q a l' (iwRep (ξ - β) + (a : ℝ) / (q : ℝ)) M
    hN hq1 hql' hl'N hM1 hcond
  have hxsub : (iwRep (ξ - β) + (a : ℝ) / (q : ℝ)) - (a : ℝ) / (q : ℝ) = iwRep (ξ - β) := by ring
  rw [hxsub, ← hG] at hkey
  have hweyl : polyWeylKernel P N (iwRep (ξ - β) + (a : ℝ) / (q : ℝ)) = mstWeyl P N ξ := by
    rw [mstWeyl_apply]
    exact polyWeylKernel_of_coe_eq P N hx
  rw [hweyl] at hkey
  have hMinv : M⁻¹ = (2 : ℝ) ^ (-((s : ℝ) * ((P.natDegree : ℝ) - χ))) := by
    rw [hMdef]
    exact (Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) _).symm
  rw [hMinv] at hkey
  refine hkey.trans ?_
  have hbrnn : 0 ≤ (2 : ℝ) ^ (-((s : ℝ) * ((P.natDegree : ℝ) - χ)))
        * (N : ℝ) ^ ((P.natDegree : ℝ) - 1) + (N : ℝ)⁻¹ := by
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    positivity
  calc Ca * (2 : ℝ) ^ l' * ((2 : ℝ) ^ (-((s : ℝ) * ((P.natDegree : ℝ) - χ)))
          * (N : ℝ) ^ ((P.natDegree : ℝ) - 1) + (N : ℝ)⁻¹)
      ≤ Ca * (2 * Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)))
          * ((2 : ℝ) ^ (-((s : ℝ) * ((P.natDegree : ℝ) - χ)))
            * (N : ℝ) ^ ((P.natDegree : ℝ) - 1) + (N : ℝ)⁻¹) := by
        apply mul_le_mul_of_nonneg_right _ hbrnn
        exact mul_le_mul_of_nonneg_left h2l' hCa.le
    _ = (2 * Ca) * (Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ))
          * ((2 : ℝ) ^ (-((s : ℝ) * ((P.natDegree : ℝ) - χ)))
            * (N : ℝ) ^ ((P.natDegree : ℝ) - 1) + (N : ℝ)⁻¹)) := by ring

/-- **MST Theorem 7, step (i) (arXiv:1512.07518 §4.4 eq. (95)), at the level scale `J = ⌊exp √(s+1)⌋`**:
on the support of the level-`s` bump around an arc `β ∈ 𝒰(s+1)`, the Weyl kernel `m_J = polyWeylKernel P J`
(read on the circle, `mstWeyl`) differs from the complete sum `G(β) = mstG P β` by at most
`C exp(−√(s+1)/2)`. -/
theorem mst_lvl_approx_pointwise (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (hc : 0 < P.leadingCoeff)
    {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10) (η : ℝ → ℂ)
    (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0) (l : ℕ) (hl : 1 ≤ l) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₁ : ℕ, ∀ s : ℕ, N₁ ≤ s → ∀ (β ξ : Work.BourgainPlan.IonescuWainger.Circle),
      β ∈ mstU l (s + 1) → mstEta P.natDegree χ η s (ξ - β) ≠ 0 →
      ‖mstWeyl P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊) ξ - mstG P β‖
        ≤ C * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2)) := by
  classical
  obtain ⟨Nrep, hNrep⟩ := mstU_rep l hl
  have hrep : ∀ n : ℕ, max Nrep 1 ≤ n → ∀ β ∈ mstU l n, ∃ (q : ℕ) (a : ℤ),
      0 < q ∧ 0 ≤ a ∧ a < q ∧ arcPt q a = β ∧ mstG P β = polyWeight P q a ∧
        (q : ℝ) ≤ Real.exp (((n : ℝ) ^ l) ^ (mstRho l)) := by
    intro n hn β hβ
    obtain ⟨q, a, hq0, ha0, haq, _, harc, hqbd⟩ :=
      hNrep n (le_trans (le_max_left _ _) hn) β hβ
    exact ⟨q, a, hq0, ha0, haq, harc, mstG_spec P hq0 ha0 haq harc, hqbd⟩
  obtain ⟨Carc, hCarc, Narc, hA⟩ := mst_lvl_arc_term P hd hχ1 η hη2 l hl (max Nrep 1) hrep
  obtain ⟨Ne, hNe⟩ := mst_lvl_exp_arith P.natDegree hd (χ := χ) hχ1
  set A : ℝ := ∑ i ∈ Finset.range (P.natDegree + 1), |((P.coeff i : ℤ) : ℝ)| with hAdef
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  refine ⟨3 * Carc + 2 * Real.pi * A, by nlinarith [hCarc, hA0, Real.pi_pos],
    max (max Narc Ne) 64, fun s hs β ξ hβ hne => ?_⟩
  have hsNarc : Narc ≤ s := by omega
  have hsNe : Ne ≤ s := by omega
  set t : ℝ := Real.sqrt ((s : ℝ) + 1) with htdef
  obtain ⟨hJ3, hJexp, hexp1, hexp2, hexp3⟩ := hNe s hsNe
  rw [← htdef] at hJ3 hJexp hexp1 hexp2 hexp3
  set J : ℕ := ⌊Real.exp t⌋₊ with hJdef
  have hJ1 : 1 ≤ J := by omega
  have hJle : (J : ℝ) ≤ Real.exp t := by
    rw [hJdef]; exact Nat.floor_le (Real.exp_pos t).le
  have hJge : Real.exp t / 2 ≤ (J : ℝ) := by
    rw [hJdef]
    have h := Nat.lt_floor_add_one (Real.exp t)
    have he2 : (2 : ℝ) ≤ Real.exp t := by
      have h1 : (1 : ℝ) ≤ t := by
        rw [htdef]
        have h0 : (0 : ℝ) ≤ (s : ℝ) := by positivity
        calc (1 : ℝ) = Real.sqrt 1 := (Real.sqrt_one).symm
          _ ≤ Real.sqrt ((s : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
      calc (2 : ℝ) ≤ Real.exp 1 := by
            have h := Real.add_one_le_exp (1 : ℝ); linarith [Real.exp_pos 1]
        _ ≤ Real.exp t := Real.exp_le_exp.mpr h1
    linarith
  have harc := hA s hsNarc J hJ3 β ξ hβ hne hJexp
  have hprof : ‖mstProf P J (ξ - β) - 1‖
      ≤ 4 * Real.pi * A * (|iwRep (ξ - β)| * (J : ℝ) ^ P.natDegree) := by
    have h := polyProfile_sub_one_le P J hJ1 (iwRep (ξ - β))
    rw [← hAdef] at h
    simpa [mstProf_apply] using h
  have hdd : (J : ℝ) ^ P.natDegree ≤ Real.exp ((P.natDegree : ℝ) * t) := by
    rw [← Real.rpow_natCast (J : ℝ) P.natDegree]
    calc (J : ℝ) ^ (((P.natDegree : ℕ)) : ℝ) ≤ (Real.exp t) ^ (((P.natDegree : ℕ)) : ℝ) :=
          Real.rpow_le_rpow (by positivity) hJle (by positivity)
      _ = Real.exp ((P.natDegree : ℝ) * t) := by
          rw [Real.rpow_def_of_pos (Real.exp_pos t), Real.log_exp, mul_comm]
  have hpow2 : (2 : ℝ) ^ (-((s : ℝ) * ((P.natDegree : ℝ) - χ)))
      = Real.exp (-(((s : ℝ) * ((P.natDegree : ℝ) - χ)) * Real.log 2)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1; ring
  have h4A : 0 ≤ 4 * Real.pi * A := by nlinarith [hA0, Real.pi_pos]
  have hterm2 : ‖mstG P β * (mstProf P J (ξ - β) - 1)‖
      ≤ 2 * Real.pi * A * Real.exp (-(t / 2)) := by
    rw [norm_mul]
    have h1 : ‖mstG P β‖ ≤ 1 := mstG_norm_le_one P β
    have hprod : ‖mstG P β‖ * ‖mstProf P J (ξ - β) - 1‖
        ≤ 1 * (4 * Real.pi * A * (|iwRep (ξ - β)| * (J : ℝ) ^ P.natDegree)) :=
      mul_le_mul h1 hprof (norm_nonneg _) (by norm_num)
    rw [one_mul] at hprod
    refine hprod.trans ?_
    have hu2 : |iwRep (ξ - β)| ≤ (1 / 2) * (2 : ℝ) ^ (-((s : ℝ) * ((P.natDegree : ℝ) - χ))) :=
      mstEta_ne_zero_abs_iwRep P.natDegree χ η hη2 s hne
    have hstep : |iwRep (ξ - β)| * (J : ℝ) ^ P.natDegree
        ≤ ((1 / 2) * (2 : ℝ) ^ (-((s : ℝ) * ((P.natDegree : ℝ) - χ))))
            * Real.exp ((P.natDegree : ℝ) * t) :=
      mul_le_mul hu2 hdd (by positivity) (by positivity)
    have hexp_le : (2 : ℝ) ^ (-((s : ℝ) * ((P.natDegree : ℝ) - χ)))
          * Real.exp ((P.natDegree : ℝ) * t) ≤ Real.exp (-(t / 2)) := by
      rw [hpow2, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith [hexp3]
    calc 4 * Real.pi * A * (|iwRep (ξ - β)| * (J : ℝ) ^ P.natDegree)
        ≤ 4 * Real.pi * A
            * (((1 / 2) * (2 : ℝ) ^ (-((s : ℝ) * ((P.natDegree : ℝ) - χ))))
              * Real.exp ((P.natDegree : ℝ) * t)) :=
          mul_le_mul_of_nonneg_left hstep h4A
      _ = 2 * Real.pi * A
            * ((2 : ℝ) ^ (-((s : ℝ) * ((P.natDegree : ℝ) - χ)))
              * Real.exp ((P.natDegree : ℝ) * t)) := by ring
      _ ≤ 2 * Real.pi * A * Real.exp (-(t / 2)) :=
          mul_le_mul_of_nonneg_left hexp_le (by nlinarith [hA0, Real.pi_pos])
  have hbracket : Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ))
        * ((2 : ℝ) ^ (-((s : ℝ) * ((P.natDegree : ℝ) - χ))) * (J : ℝ) ^ ((P.natDegree : ℝ) - 1)
            + (J : ℝ)⁻¹)
      ≤ 3 * Real.exp (-(t / 2)) := by
    have hJd1 : (J : ℝ) ^ ((P.natDegree : ℝ) - 1) ≤ Real.exp (((P.natDegree : ℝ) - 1) * t) := by
      have hd1 : (0 : ℝ) ≤ (P.natDegree : ℝ) - 1 := by
        have h1 : (1 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast (by omega : 1 ≤ P.natDegree)
        linarith
      calc (J : ℝ) ^ ((P.natDegree : ℝ) - 1) ≤ (Real.exp t) ^ ((P.natDegree : ℝ) - 1) :=
            Real.rpow_le_rpow (by positivity) hJle hd1
        _ = Real.exp (((P.natDegree : ℝ) - 1) * t) := by
            rw [Real.rpow_def_of_pos (Real.exp_pos t), Real.log_exp, mul_comm]
    have hc2nn : 0 ≤ (2 : ℝ) ^ (-((s : ℝ) * ((P.natDegree : ℝ) - χ))) := by positivity
    have hP1 : Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ))
          * ((2 : ℝ) ^ (-((s : ℝ) * ((P.natDegree : ℝ) - χ)))
            * (J : ℝ) ^ ((P.natDegree : ℝ) - 1))
        ≤ Real.exp (-(t / 2)) := by
      have hstep : (2 : ℝ) ^ (-((s : ℝ) * ((P.natDegree : ℝ) - χ)))
            * (J : ℝ) ^ ((P.natDegree : ℝ) - 1)
          ≤ Real.exp (-(((s : ℝ) * ((P.natDegree : ℝ) - χ)) * Real.log 2)
              + (((P.natDegree : ℝ) - 1) * t)) := by
        calc (2 : ℝ) ^ (-((s : ℝ) * ((P.natDegree : ℝ) - χ)))
              * (J : ℝ) ^ ((P.natDegree : ℝ) - 1)
            ≤ (2 : ℝ) ^ (-((s : ℝ) * ((P.natDegree : ℝ) - χ)))
              * Real.exp (((P.natDegree : ℝ) - 1) * t) :=
                mul_le_mul_of_nonneg_left hJd1 hc2nn
          _ = Real.exp (-(((s : ℝ) * ((P.natDegree : ℝ) - χ)) * Real.log 2))
              * Real.exp (((P.natDegree : ℝ) - 1) * t) := by rw [hpow2]
          _ = Real.exp (-(((s : ℝ) * ((P.natDegree : ℝ) - χ)) * Real.log 2)
              + (((P.natDegree : ℝ) - 1) * t)) := by rw [← Real.exp_add]
      calc Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ))
            * ((2 : ℝ) ^ (-((s : ℝ) * ((P.natDegree : ℝ) - χ)))
              * (J : ℝ) ^ ((P.natDegree : ℝ) - 1))
          ≤ Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ))
              * Real.exp (-(((s : ℝ) * ((P.natDegree : ℝ) - χ)) * Real.log 2)
                  + (((P.natDegree : ℝ) - 1) * t)) :=
            mul_le_mul_of_nonneg_left hstep (Real.exp_pos _).le
        _ = Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)
              + (-(((s : ℝ) * ((P.natDegree : ℝ) - χ)) * Real.log 2)
                  + (((P.natDegree : ℝ) - 1) * t))) := by rw [← Real.exp_add]
        _ ≤ Real.exp (-(t / 2)) := by
            apply Real.exp_le_exp.mpr
            linarith [hexp1]
    have hJinv : (J : ℝ)⁻¹ ≤ 2 * Real.exp (-t) := by
      have hpos : 0 < Real.exp t / 2 := by positivity
      have hJpos : (0 : ℝ) < (J : ℝ) := by exact_mod_cast (by omega : 0 < J)
      have h1 : (J : ℝ)⁻¹ ≤ (Real.exp t / 2)⁻¹ := (inv_le_inv₀ hJpos hpos).mpr hJge
      have h2 : (Real.exp t / 2)⁻¹ = 2 * Real.exp (-t) := by
        rw [inv_div, Real.exp_neg]; ring
      linarith
    have hP2 : Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)) * (J : ℝ)⁻¹
        ≤ 2 * Real.exp (-(t / 2)) := by
      calc Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)) * (J : ℝ)⁻¹
          ≤ Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)) * (2 * Real.exp (-t)) :=
            mul_le_mul_of_nonneg_left hJinv (Real.exp_pos _).le
        _ = 2 * Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ) - t) := by
            rw [Real.exp_sub, Real.exp_neg]; ring
        _ ≤ 2 * Real.exp (-(t / 2)) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            apply Real.exp_le_exp.mpr
            linarith [Real.log_pos one_lt_two]
    calc Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ))
          * ((2 : ℝ) ^ (-((s : ℝ) * ((P.natDegree : ℝ) - χ)))
              * (J : ℝ) ^ ((P.natDegree : ℝ) - 1) + (J : ℝ)⁻¹)
        = Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ))
            * ((2 : ℝ) ^ (-((s : ℝ) * ((P.natDegree : ℝ) - χ)))
              * (J : ℝ) ^ ((P.natDegree : ℝ) - 1))
          + Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)) * (J : ℝ)⁻¹ := by ring
      _ ≤ Real.exp (-(t / 2)) + 2 * Real.exp (-(t / 2)) := add_le_add hP1 hP2
      _ = 3 * Real.exp (-(t / 2)) := by ring
  have hsplit : mstWeyl P J ξ - mstG P β
      = (mstWeyl P J ξ - mstG P β * mstProf P J (ξ - β))
        + mstG P β * (mstProf P J (ξ - β) - 1) := by ring
  rw [hsplit]
  calc ‖(mstWeyl P J ξ - mstG P β * mstProf P J (ξ - β))
        + mstG P β * (mstProf P J (ξ - β) - 1)‖
      ≤ ‖mstWeyl P J ξ - mstG P β * mstProf P J (ξ - β)‖
        + ‖mstG P β * (mstProf P J (ξ - β) - 1)‖ := norm_add_le _ _
    _ ≤ Carc * (Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ))
          * ((2 : ℝ) ^ (-((s : ℝ) * ((P.natDegree : ℝ) - χ))) * (J : ℝ) ^ ((P.natDegree : ℝ) - 1)
              + (J : ℝ)⁻¹))
        + 2 * Real.pi * A * Real.exp (-(t / 2)) := add_le_add harc hterm2
    _ ≤ Carc * (3 * Real.exp (-(t / 2))) + 2 * Real.pi * A * Real.exp (-(t / 2)) := by
        apply add_le_add _ le_rfl
        exact mul_le_mul_of_nonneg_left hbracket hCarc.le
    _ = (3 * Carc + 2 * Real.pi * A) * Real.exp (-(t / 2)) := by ring

end

end Work.BourgainPlan.Maximal
