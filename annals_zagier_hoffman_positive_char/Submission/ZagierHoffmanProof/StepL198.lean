import Submission.ZagierHoffmanProof.StepL196
import Submission.ZagierHoffmanProof.StepL2

set_option autoImplicit false
set_option maxHeartbeats 4000000
open Polynomial RatFunc
open scoped BigOperators WithZero Topology
open WithZero

/-!
# Step L198: `ζ_A(q) ≠ 0` and `ζ_A(1, q−1) ≠ 0` — the second and third non-vanishing MZVs

StepL196 proved `ζ_A(1) ≠ 0` from the block decomposition and the closed form of the
depth-one power sums `P_d(1)`.  The same principle applies to the exponent `q = |F|`,
provided one controls `v (P_d(q))` for every level `d`.  That is done here by the
committed 3-term recurrence `ID2` (StepK34's `ID2_all_unc`), which reads

    `P_{d+1}(q)·(P_{d+1}(1) + D1·P_{d+2}(1)) = P_{d+2}(1)·P_d(q)`      (d ≥ 0)

and, together with the exact valuations `v (P_e(1)) = exp (−Σ_{i<e} q^{i+1})` (StepL195)
and `v (D1) = exp q`, gives the recursion `v (P_{d+1}(q)) = exp (−q^{d+2})·v (P_d(q))`,
i.e. `v (P_d(q)) = exp (−Σ_{i<d} q^{i+2}) < 1` for `d ≥ 1`.  Hence `ζ_A(q) = Σ_d P_d(q)`
is `1 + (terms of valuation < 1)`, so `v (ζ_A(q)) = 1` and `ζ_A(q) ≠ 0`.

Composing with the ζ-level relation `R1` (`zeta_R1`, StepL2)
`ζ_A(q) + D1·ζ_A(1, q−1) = 0` finally gives `ζ_A(1, q−1) ≠ 0` as well.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## 2. The valuation of `D1 = X^q − X` -/

/-- ★ `v (D1) = exp q`. -/
theorem val_D1c : Valued.v (D1c F) = WithZero.exp ((Nat.card F : ℤ)) := by
  classical
  have hne : D1rat F ≠ 0 := by
    intro h0
    have hd : intDegree (D1rat F) = ((Nat.card F : ℕ) : ℤ) := by
      rw [D1rat]
      change intDegree (algebraMap F[X] (RatFunc F) (carlitzOne F)) = _
      rw [RatFunc.intDegree_polynomial, carlitzOne_natDegree F]
    rw [h0, RatFunc.intDegree_zero] at hd
    have hq : (2 : ℤ) ≤ (Nat.card F : ℤ) := by
      exact_mod_cast card_ge_two F
    omega
  rw [D1c_eq_D1rat F, inftyValued_v_ratFunc F (D1rat F) hne]
  congr 1
  rw [D1rat]
  change intDegree (algebraMap F[X] (RatFunc F) (carlitzOne F)) = _
  rw [RatFunc.intDegree_polynomial, carlitzOne_natDegree F]

/-! ## 3. The valuations of the depth-one power sums `P_d(q)` -/

/-- `Wtwo d := Σ_{i<d} q^{i+2}`: the exponent in `v (P_d(q)) = exp (−Wtwo d)`. -/
noncomputable def Wtwo (d : ℕ) : ℤ :=
  ∑ i ∈ Finset.range d, ((Nat.card F : ℤ) ^ (i + 2))

/-- `Sexp d := Σ_{i<d} q^{i+1}`: the exponent in `v (P_d(1)) = exp (−Sexp d)`. -/
noncomputable def Sexp (d : ℕ) : ℤ :=
  ∑ i ∈ Finset.range d, ((Nat.card F : ℤ) ^ (i + 1))

lemma Wtwo_succ (d : ℕ) :
    Wtwo F (d + 1) = Wtwo F d + ((Nat.card F : ℤ) ^ (d + 2)) := by
  rw [Wtwo, Finset.sum_range_succ, Wtwo]

lemma Sexp_succ (d : ℕ) :
    Sexp F (d + 1) = Sexp F d + ((Nat.card F : ℤ) ^ (d + 1)) := by
  rw [Sexp, Finset.sum_range_succ, Sexp]

/-- `v (P_e(1)) = exp (−Sexp e)` in `Sexp`-notation. -/
lemma val_P_oneExp' (e : ℕ) (he : 1 ≤ e) :
    Valued.v (P F e oneExp) = WithZero.exp (-(Sexp F e)) := by
  rw [val_P_oneExp F e he, Sexp]

/-- `Wtwo d > 0` for `d ≥ 1`. -/
lemma Wtwo_pos (d : ℕ) (hd : 1 ≤ d) : 0 < Wtwo F d := by
  have hpow : (0 : ℤ) < (Nat.card F : ℤ) ^ (0 + 2) := by
    have h : (2 : ℤ) ≤ (Nat.card F : ℤ) := by exact_mod_cast card_ge_two F
    positivity
  have hmem : 0 ∈ Finset.range d := Finset.mem_range.mpr (by omega)
  have hle : (Nat.card F : ℤ) ^ (0 + 2)
      ≤ Wtwo F d := by
    rw [Wtwo]
    exact Finset.single_le_sum (f := fun i => ((Nat.card F : ℤ) ^ (i + 2)))
      (fun i _ => by positivity) hmem
  linarith

/-- ★★ `v (P_d(q)) = exp (−Σ_{i<d} q^{i+2})` for every level `d`.

Induction on `d` using the committed 3-term recurrence `ID2`:
`P_{d+1}(q)·(P_{d+1}(1) + D1·P_{d+2}(1)) = P_{d+2}(1)·P_d(q)`; the bracket has the
valuation of `P_{d+1}(1)` because `v (D1·P_{d+2}(1)) = exp(q)exp(−Sexp(d+2))` is smaller. -/
theorem val_P_qExp (d : ℕ) :
    Valued.v (P F d (qExp F)) = WithZero.exp (-(Wtwo F d)) := by
  classical
  induction d with
  | zero =>
      rw [P_zero_eq_one F (qExp F), map_one]
      simp [Wtwo]
  | succ d ih =>
      have hID : P F (d + 1) (qExp F) * (P F (d + 1) oneExp + D1c F * P F (d + 2) oneExp)
          = P F (d + 2) oneExp * P F d (qExp F) := ID2_all_unc F (d + 1) (by omega)
      have hpow2 : (Nat.card F : ℤ) < ((Nat.card F : ℤ)) ^ (d + 2) := by
        have hq1 : (1 : ℤ) < (Nat.card F : ℤ) := by
          have := card_ge_two F
          exact_mod_cast (by omega : 1 < Nat.card F)
        have hqpos : (0 : ℤ) < (Nat.card F : ℤ) := by linarith
        have hpow1 : (1 : ℤ) < ((Nat.card F : ℤ)) ^ (d + 1) := one_lt_pow₀ hq1 (by omega)
        rw [pow_succ]
        calc (Nat.card F : ℤ) = 1 * (Nat.card F : ℤ) := by ring
          _ < ((Nat.card F : ℤ)) ^ (d + 1) * (Nat.card F : ℤ) :=
              mul_lt_mul_of_pos_right hpow1 hqpos
      have hlt : Valued.v (D1c F * P F (d + 2) oneExp) < Valued.v (P F (d + 1) oneExp) := by
        rw [map_mul, val_D1c F, val_P_oneExp' F (d + 2) (by omega),
          val_P_oneExp' F (d + 1) (by omega), ← WithZero.exp_add, WithZero.exp_lt_exp,
          Sexp_succ (F := F) (d + 1)]
        linarith
      have hb : Valued.v (P F (d + 1) oneExp + D1c F * P F (d + 2) oneExp)
          = Valued.v (P F (d + 1) oneExp) := by
        rw [Valuation.map_add_eq_of_lt_left (v := Valued.v) hlt]
      have hv : Valued.v (P F (d + 1) (qExp F)) * Valued.v (P F (d + 1) oneExp)
          = Valued.v (P F (d + 2) oneExp) * WithZero.exp (-(Wtwo F d)) := by
        have h1 := congrArg Valued.v hID
        rw [map_mul, hb, map_mul, ih] at h1
        exact h1
      have harith : -(Sexp F (d + 2)) + (-(Wtwo F d))
          = (-(Wtwo F (d + 1))) + (-(Sexp F (d + 1))) := by
        rw [Sexp_succ (F := F) (d + 1), Wtwo_succ (F := F) d]
        ring
      have h2 : WithZero.exp (-(Sexp F (d + 2))) * WithZero.exp (-(Wtwo F d))
          = WithZero.exp (-(Wtwo F (d + 1))) * WithZero.exp (-(Sexp F (d + 1))) := by
        rw [← WithZero.exp_add, ← WithZero.exp_add, harith]
      refine mul_right_cancel₀ (WithZero.exp_ne_zero (a := -(Sexp F (d + 1)))) ?_
      calc Valued.v (P F (d + 1) (qExp F)) * WithZero.exp (-(Sexp F (d + 1)))
          = Valued.v (P F (d + 1) (qExp F)) * Valued.v (P F (d + 1) oneExp) := by
            rw [val_P_oneExp' F (d + 1) (by omega)]
        _ = Valued.v (P F (d + 2) oneExp) * WithZero.exp (-(Wtwo F d)) := hv
        _ = WithZero.exp (-(Sexp F (d + 2))) * WithZero.exp (-(Wtwo F d)) := by
            rw [val_P_oneExp' F (d + 2) (by omega)]
        _ = WithZero.exp (-(Wtwo F (d + 1))) * WithZero.exp (-(Sexp F (d + 1))) := h2

/-- `v (P_d(q)) < 1` for `d ≥ 1`. -/
theorem val_P_qExp_lt_one (d : ℕ) (hd : 1 ≤ d) :
    Valued.v (P F d (qExp F)) < (1 : ℤᵐ⁰) := by
  rw [val_P_qExp F d, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  have := Wtwo_pos F d hd
  omega

/-! ## 4. The non-vanishing of `ζ_A(q)` and of `ζ_A(1, q−1)` -/

/-- ★★★ `v (ζ_A(q)) = 1`, from the block decomposition `ζ_A(q) = Σ_d P_d(q)`, the base
term `P_0(q) = 1` and `v (P_d(q)) < 1` for `d ≥ 1`. -/
theorem val_zeta_qExp : Valued.v (ζ_A F (single (qExp F))) = (1 : ℤᵐ⁰) := by
  classical
  have hsumm := summable_S F (r := 1) (by norm_num) (single (qExp F))
  have hf0 : S F 1 (by norm_num) (single (qExp F)) 0 = 1 := by
    rw [S_one_eq_P F 0 (by norm_num) (single (qExp F))]
    exact P_zero_eq_one F (qExp F)
  have hlt : ∀ n : ℕ, 1 ≤ n →
      Valued.v (S F 1 (by norm_num) (single (qExp F)) n) < (1 : ℤᵐ⁰) := by
    intro n hn
    rw [S_one_eq_P F n (by norm_num) (single (qExp F))]
    exact val_P_qExp_lt_one F n hn
  have h := val_tsum_eq_one_of F
    (fun n => S F 1 (by norm_num) (single (qExp F)) n) hf0 hsumm hlt
  rw [zeta_eq_tsum_block F (by norm_num) (single (qExp F))]
  exact h

/-- ★★★ `ζ_A(q) ≠ 0`. -/
theorem zeta_qExp_ne_zero : ζ_A F (single (qExp F)) ≠ 0 := by
  intro hzero
  have h := val_zeta_qExp F
  rw [hzero] at h
  simp at h

/-- `ζ_A(q) ∈ 𝒵 F q`. -/
theorem zeta_qExp_mem_Z : ζ_A F (single (qExp F)) ∈ 𝒵 F (qExp F : ℕ) := by
  classical
  refine Submodule.subset_span ?_
  rw [Set.mem_iUnion]
  refine ⟨1, ?_⟩
  exact ⟨single (qExp F), by simp [𝔖_w, weight, single], rfl⟩

/-- `𝒵 F q ≠ ⊥`: the weight-`q` zeta space is not trivial. -/
theorem Z_qExp_ne_bot :
    𝒵 F (qExp F : ℕ) ≠ (⊥ : Submodule (RatFunc F) (RatFunc.CompletionAtInfty F)) := by
  intro hbot
  have hmem := zeta_qExp_mem_Z F
  rw [hbot] at hmem
  exact zeta_qExp_ne_zero F (by simpa using hmem)

/-- ★★★ `ζ_A(1, q−1) ≠ 0`: the `ζ`-level relation `R1` transports the non-vanishing of
`ζ_A(q)` to the depth-two value `ζ_A(1, q−1)`. -/
theorem zeta_pair_one_qMinus_ne_zero : ζ_A F (pair oneExp (qMinusExp F)) ≠ 0 := by
  intro hzero
  have hR1 := zeta_R1 F
  rw [hzero, mul_zero, add_zero] at hR1
  exact zeta_qExp_ne_zero F hR1

end ZagierHoffmanPositiveChar
