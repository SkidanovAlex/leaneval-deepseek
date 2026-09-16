/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.ZagierHoffmanProof.StepL199
import Submission.ZagierHoffmanProof.StepD
import Submission.ZagierHoffmanProof.StepB5
import Submission.ZagierHoffmanProof.DegLin

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Polynomial RatFunc
open scoped BigOperators WithZero
open WithZero

/-!
# The degree of an MZV with entries `≤ q`, over an *arbitrary* finite field

For a tuple `𝔰` of positive exponents with all entries `≤ q = |F|`, the depth-one power sums are
*multiplicatively* pure (`StepL199.P_eq_pow_of_le_card`), so their valuations are exactly known,
`v (P_d n) = exp (-(n * Sexp d))` (`StepL199.val_P_se`), for **every** finite field.  Writing

  `degExp 𝔰 = ∑_j (𝔰 j) * Sexp (r-1-j)`,

we show that the block sums `S_d(𝔰)` are dominated by the minimal level `d = r-1`, whence
`v (ζ_A 𝔰) = exp (-(degExp 𝔰))` and `ζ_A 𝔰 ≠ 0` — Thakur's non-vanishing theorem for
Hoffman-type tuples over an arbitrary finite field.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

section DegExp

/-- `degExp 𝔰 = ∑_j (𝔰 j : ℤ) * Sexp (r-1-j)`: the degree exponent of an MZV whose entries are
all `≤ q`. -/
noncomputable def degExp {r : ℕ} (𝔰 : Fin r → ℕ+) : ℤ :=
  ∑ j : Fin r, (𝔰 j : ℤ) * Sexp F (r - 1 - (j : ℕ))

/-- `(Nat.card F : ℤ) > 0`. -/
lemma card_pos_int : (0 : ℤ) < (Nat.card F : ℤ) := by
  have := card_ge_two F
  omega

lemma Sexp_nonneg (d : ℕ) : 0 ≤ Sexp F d := by
  rw [Sexp]
  exact Finset.sum_nonneg fun i _ => le_of_lt (pow_pos (card_pos_int F) _)

lemma Sexp_pos {d : ℕ} (hd : 1 ≤ d) : 0 < Sexp F d := by
  rw [Sexp]
  refine Finset.sum_pos (fun i _ => pow_pos (card_pos_int F) _)
    (Finset.nonempty_range_iff.mpr (by omega))

lemma Sexp_mono {d d' : ℕ} (h : d ≤ d') : Sexp F d ≤ Sexp F d' := by
  rw [Sexp, Sexp]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr h)
    (fun i _ _ => le_of_lt (pow_pos (card_pos_int F) _))

lemma Sexp_lt {d d' : ℕ} (h : d < d') : Sexp F d < Sexp F d' := by
  have h1 : Sexp F d' = Sexp F d + ∑ i ∈ Finset.Ico d d', ((Nat.card F : ℤ) ^ (i + 1)) := by
    rw [Sexp, Sexp, Finset.sum_range_add_sum_Ico _ (le_of_lt h)]
  have hpos : 0 < ∑ i ∈ Finset.Ico d d', ((Nat.card F : ℤ) ^ (i + 1)) := by
    refine Finset.sum_pos (fun i _ => pow_pos (card_pos_int F) _) (Finset.nonempty_Ico.mpr h)
  rw [h1]
  linarith

/-- Splitting off the head from `degExp`. -/
lemma degExp_cons {r : ℕ} (𝔰 : Fin (r + 1) → ℕ+) :
    degExp F 𝔰 = (𝔰 0 : ℤ) * Sexp F r + degExp F (expTail 𝔰) := by
  rw [degExp, Fin.sum_univ_succ, degExp]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have hv : (𝔰 (Fin.succ j) : ℤ) = ((expTail 𝔰) j : ℤ) := rfl
  have hje : ((j : ℕ) + 1) = ((Fin.succ j : Fin (r + 1)) : ℕ) := rfl
  have he : r + 1 - 1 - (↑j + 1) = r + 1 - 1 - 1 - ↑j := by omega
  rw [hv, ← hje, he]

lemma Sexp_zero : Sexp F 0 = 0 := by
  rw [Sexp]; simp

lemma degExp_fin_one (𝔰 : Fin 1 → ℕ+) : degExp F 𝔰 = 0 := by
  rw [degExp, Fin.sum_univ_one]
  rw [show (1 : ℕ) - 1 - ((0 : Fin 1) : ℕ) = 0 from rfl, Sexp_zero F, mul_zero]

end DegExp

section Bounds

/-- `E 𝔰 := exp (-(degExp 𝔰))`. -/
noncomputable def degExpE {r : ℕ} (𝔰 : Fin r → ℕ+) : ℤᵐ⁰ :=
  WithZero.exp (-(degExp F 𝔰))

lemma degExpE_eq {r : ℕ} (𝔰 : Fin r → ℕ+) :
    degExpE F 𝔰 = WithZero.exp (-(degExp F 𝔰)) := rfl

/-- **The block sums of a tuple with entries `≤ q` are dominated by the minimal level.**
For every finite field `F`:
* the partial sums `S_<d` are bounded by `degExpE 𝔰 = exp (-(degExp 𝔰))`;
* the minimal level `d = r-1` has *exactly* the valuation `degExpE 𝔰`;
* every level `d ≥ r-1` has valuation `≤ degExpE 𝔰`;
* every level `d ≥ r` has valuation `< degExpE 𝔰` (strict domination). -/
theorem degExp_bounds :
    ∀ (r : ℕ) (hr : 0 < r) (𝔰 : Fin r → ℕ+), (∀ i, (𝔰 i : ℕ) ≤ Nat.card F) →
      (∀ d, Valued.v (S_lt F r hr 𝔰 d) ≤ WithZero.exp (-(degExp F 𝔰))) ∧
      (Valued.v (S F r hr 𝔰 (r - 1)) = WithZero.exp (-(degExp F 𝔰))) ∧
      (∀ d, r - 1 ≤ d → Valued.v (S F r hr 𝔰 d) ≤ WithZero.exp (-(degExp F 𝔰))) ∧
      (∀ d, r ≤ d → Valued.v (S F r hr 𝔰 d) < WithZero.exp (-(degExp F 𝔰))) := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro hr 𝔰 hle
    have hr1' : 1 ≤ r := hr
    rcases eq_or_lt_of_le hr1' with hr1 | hr2
    · -- r = 1
      subst hr1
      have hE : WithZero.exp (-(degExp F 𝔰)) = 1 := by
        rw [degExp_fin_one F 𝔰, neg_zero, WithZero.exp_zero]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro d
        rw [S_lt_eq_sum_levels F 1 hr 𝔰 d]
        refine Valuation.map_sum_le (v := (Valued.v : Valuation (RatFunc.CompletionAtInfty F) ℤᵐ⁰)) ?_
        intro e he
        rw [S_one_eq_P F e hr 𝔰, val_P_se F (𝔰 ⟨0, hr⟩) (hle ⟨0, hr⟩) e, hE,
          show (1 : ℤᵐ⁰) = WithZero.exp 0 from WithZero.exp_zero.symm, WithZero.exp_le_exp,
          neg_nonpos, Se]
        exact mul_nonneg (by positivity) (Sexp_nonneg F e)
      · rw [show (1 : ℕ) - 1 = 0 from rfl, S_one_eq_P F 0 hr 𝔰, P_zero_eq_one F (𝔰 ⟨0, hr⟩)]
        rw [hE, map_one]
      · intro d hd
        rw [S_one_eq_P F d hr 𝔰, val_P_se F (𝔰 ⟨0, hr⟩) (hle ⟨0, hr⟩) d, hE,
          show (1 : ℤᵐ⁰) = WithZero.exp 0 from WithZero.exp_zero.symm, WithZero.exp_le_exp,
          neg_nonpos, Se]
        exact mul_nonneg (by positivity) (Sexp_nonneg F d)
      · intro d hd
        rw [S_one_eq_P F d hr 𝔰, val_P_se F (𝔰 ⟨0, hr⟩) (hle ⟨0, hr⟩) d, hE,
          show (1 : ℤᵐ⁰) = WithZero.exp 0 from WithZero.exp_zero.symm, WithZero.exp_lt_exp,
          neg_lt_zero, Se]
        exact mul_pos (by positivity) (Sexp_pos F (by omega))
    · -- r ≥ 2
      obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
      have hm : 0 < m := by omega
      have hle' : ∀ i : Fin m, (expTail 𝔰 i : ℕ) ≤ Nat.card F :=
        fun i => hle ⟨(i : ℕ) + 1, by omega⟩
      obtain ⟨ihB, ihC, ihA, ihD⟩ := ih m (by omega) hm (expTail 𝔰) hle'
      -- the recursion and the telescoping of `S_<d`
      have hrec : ∀ d, S F (m + 1) hr 𝔰 d = P F d (𝔰 0) * S_lt F m hm (expTail 𝔰) d := by
        intro d
        rw [S_d_recursion F (m + 1) (by omega) hr hm 𝔰 d]
        congr 1
      have hlt_eq : S_lt F m hm (expTail 𝔰) m = S F m hm (expTail 𝔰) (m - 1) := by
        rw [S_lt_eq_sum_levels F m hm (expTail 𝔰) m,
          show Finset.range m = Finset.range ((m - 1) + 1) from by
            rw [Nat.sub_add_cancel (by omega : 1 ≤ m)],
          Finset.sum_range_succ]
        have hz : ∑ i ∈ Finset.range (m - 1), S F m hm (expTail 𝔰) i = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          exact S_eq_zero_of_lt (F := F) (hr := hm) (𝔰 := expTail 𝔰)
            (Finset.mem_range.mp hi)
        rw [hz, zero_add]
      -- exact value at the minimal level
      have hC : Valued.v (S F (m + 1) hr 𝔰 ((m + 1) - 1)) = WithZero.exp (-(degExp F 𝔰)) := by
        rw [show (m + 1) - 1 = m from rfl, hrec m, hlt_eq, map_mul,
          val_P_se F (𝔰 0) (hle 0) m, ihC, Se, ← WithZero.exp_add,
          degExp_cons (F := F) (r := m) 𝔰]
        congr 1
        ring
      -- the sharp bound at level `d`
      have hsharp : ∀ d, Valued.v (S F (m + 1) hr 𝔰 d) ≤
          WithZero.exp (-((𝔰 0 : ℤ) * Sexp F d + degExp F (expTail 𝔰))) := by
        intro d
        rw [hrec d, map_mul, val_P_se F (𝔰 0) (hle 0) d, Se]
        refine le_trans (mul_le_mul_right (ihB d) _) ?_
        rw [← WithZero.exp_add]
        exact le_of_eq (by congr 1; ring)
      -- (A)
      have hA : ∀ d, (m + 1) - 1 ≤ d → Valued.v (S F (m + 1) hr 𝔰 d) ≤ WithZero.exp (-(degExp F 𝔰)) := by
        intro d hd
        refine le_trans (hsharp d) ?_
        rw [degExp_cons (F := F) (r := m) 𝔰, WithZero.exp_le_exp, neg_le_neg_iff]
        have h1 : (𝔰 0 : ℤ) * Sexp F m ≤ (𝔰 0 : ℤ) * Sexp F d :=
          mul_le_mul_of_nonneg_left (Sexp_mono F (by omega)) (by positivity)
        linarith
      -- (D)
      have hD : ∀ d, (m + 1) ≤ d → Valued.v (S F (m + 1) hr 𝔰 d) < WithZero.exp (-(degExp F 𝔰)) := by
        intro d hd
        refine lt_of_le_of_lt (hsharp d) ?_
        rw [degExp_cons (F := F) (r := m) 𝔰, WithZero.exp_lt_exp, neg_lt_neg_iff]
        have h1 : (𝔰 0 : ℤ) * Sexp F m < (𝔰 0 : ℤ) * Sexp F d :=
          mul_lt_mul_of_pos_left (Sexp_lt F (by omega)) (by positivity)
        linarith
      -- (B)
      refine ⟨?_, hC, hA, hD⟩
      intro d
      rw [S_lt_eq_sum_levels F (m + 1) hr 𝔰 d]
      refine Valuation.map_sum_le (v := (Valued.v : Valuation (RatFunc.CompletionAtInfty F) ℤᵐ⁰)) ?_
      intro e he
      rcases lt_or_ge e ((m + 1) - 1) with he' | he'
      · rw [S_eq_zero_of_lt (F := F) (hr := hr) (𝔰 := 𝔰) (d := e) he', map_zero]
        exact zero_le
      · exact hA e he'

end Bounds

section Main

/-- ★★★ **The exact degree of an MZV with entries `≤ q`**, over an arbitrary finite field:
`v (ζ_A 𝔰) = exp (-(degExp 𝔰))`. -/
theorem val_zeta_le_card {r : ℕ} (hr : 1 ≤ r) (𝔰 : Fin r → ℕ+)
    (hle : ∀ i, (𝔰 i : ℕ) ≤ Nat.card F) :
    Valued.v (ζ_A F 𝔰) = WithZero.exp (-(degExp F 𝔰)) := by
  have hr0 : 0 < r := hr
  have hb := degExp_bounds F r hr0 𝔰 hle
  rw [zeta_eq_tsum_block F hr0 𝔰]
  refine val_tsum_eq_of_dominates F (fun n => S F r hr0 𝔰 n) (r - 1)
    (WithZero.exp (-(degExp F 𝔰))) WithZero.exp_ne_zero hb.2.1
    (summable_S F hr0 𝔰) ?_
  intro n hn
  rcases lt_or_ge n (r - 1) with hlt | hge
  · rw [S_eq_zero_of_lt F hr0 𝔰 hlt, map_zero]
    exact WithZero.exp_pos
  · exact hb.2.2.2 n (by omega)

/-- ★★★ **Thakur's non-vanishing theorem for Hoffman-type tuples over any finite field**:
every MZV whose entries are all `≤ q` is nonzero. -/
theorem zeta_ne_zero_le_card {r : ℕ} (hr : 1 ≤ r) (𝔰 : Fin r → ℕ+)
    (hle : ∀ i, (𝔰 i : ℕ) ≤ Nat.card F) :
    ζ_A F 𝔰 ≠ 0 := by
  intro h
  have h1 := val_zeta_le_card F hr 𝔰 hle
  rw [h, map_zero] at h1
  exact WithZero.exp_ne_zero h1.symm

end Main

section Code

/-- `(q-1) * Sexp m = q * (q^m - 1)`. -/
lemma pred_mul_Sexp (m : ℕ) : ((Nat.card F - 1 : ℕ) : ℤ) * Sexp F m
    = (Nat.card F : ℤ) * ((Nat.card F : ℤ) ^ m - 1) := by
  have hq1 : 1 ≤ Nat.card F := by have := card_ge_two F; omega
  have hcast : ((Nat.card F - 1 : ℕ) : ℤ) = (Nat.card F : ℤ) - 1 := by
    rw [Nat.cast_sub hq1, Nat.cast_one]
  have hgeom : ((Nat.card F : ℤ) - 1) * ∑ i ∈ Finset.range m, (Nat.card F : ℤ) ^ i
      = (Nat.card F : ℤ) ^ m - 1 := mul_geom_sum (Nat.card F : ℤ) m
  rw [hcast, Sexp]
  calc ((Nat.card F : ℤ) - 1) * ∑ i ∈ Finset.range m, (Nat.card F : ℤ) ^ (i + 1)
      = ((Nat.card F : ℤ) - 1)
        * ((Nat.card F : ℤ) * ∑ i ∈ Finset.range m, (Nat.card F : ℤ) ^ i) := by
        congr 1
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [pow_succ, mul_comm]
    _ = (Nat.card F : ℤ)
        * (((Nat.card F : ℤ) - 1) * ∑ i ∈ Finset.range m, (Nat.card F : ℤ) ^ i) := by ring
    _ = (Nat.card F : ℤ) * ((Nat.card F : ℤ) ^ m - 1) := by rw [hgeom]

/-- `(q-1) * degExp 𝔰 = q * (code 𝔰 - weight 𝔰)`: the degree exponent is a linear form in the
base-`q` code of the tuple. -/
theorem degExp_pred_mul_eq_code {r : ℕ} (𝔰 : Fin r → ℕ+) :
    ((Nat.card F - 1 : ℕ) : ℤ) * degExp F 𝔰
      = (Nat.card F : ℤ) * (((tupleCode F 𝔰 : ℕ) : ℤ) - ((tupleWeight 𝔰 : ℕ) : ℤ)) := by
  have hterm : ∀ j : Fin r,
      ((Nat.card F - 1 : ℕ) : ℤ) * ((𝔰 j : ℤ) * Sexp F (r - 1 - (j : ℕ)))
        = (Nat.card F : ℤ) * ((𝔰 j : ℤ) * (Nat.card F : ℤ) ^ (r - 1 - (j : ℕ)) - (𝔰 j : ℤ)) := by
    intro j
    have hS := pred_mul_Sexp F (r - 1 - (j : ℕ))
    calc ((Nat.card F - 1 : ℕ) : ℤ) * ((𝔰 j : ℤ) * Sexp F (r - 1 - (j : ℕ)))
        = (𝔰 j : ℤ) * (((Nat.card F - 1 : ℕ) : ℤ) * Sexp F (r - 1 - (j : ℕ))) := by ring
      _ = (𝔰 j : ℤ) * ((Nat.card F : ℤ) * ((Nat.card F : ℤ) ^ (r - 1 - (j : ℕ)) - 1)) := by
            rw [hS]
      _ = (Nat.card F : ℤ)
            * ((𝔰 j : ℤ) * (Nat.card F : ℤ) ^ (r - 1 - (j : ℕ)) - (𝔰 j : ℤ)) := by ring
  have hcode : ((tupleCode F 𝔰 : ℕ) : ℤ)
      = ∑ j : Fin r, (𝔰 j : ℤ) * (Nat.card F : ℤ) ^ (r - 1 - (j : ℕ)) := by
    rw [tupleCode]
    push_cast
    rfl
  have hwt : ((tupleWeight 𝔰 : ℕ) : ℤ) = ∑ j : Fin r, (𝔰 j : ℤ) := by
    rw [tupleWeight]
    push_cast
    rfl
  rw [degExp, Finset.mul_sum, Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.mul_sum,
    Finset.sum_sub_distrib, ← hcode, ← hwt]

/-- ★★★ **The MZV attached to a tuple with entries `≤ q` determines the tuple** (same weight),
over an arbitrary finite field. -/
theorem zeta_A_injective_le_card :
    ∀ {r r' : ℕ} (hr : 1 ≤ r) (hr' : 1 ≤ r') (𝔰 : Fin r → ℕ+) (𝔰' : Fin r' → ℕ+),
      (∀ i, (𝔰 i : ℕ) ≤ Nat.card F) → (∀ i, (𝔰' i : ℕ) ≤ Nat.card F) →
      tupleWeight 𝔰 = tupleWeight 𝔰' → ζ_A F 𝔰 = ζ_A F 𝔰' →
      ∃ h : r = r', ∀ i : Fin r, 𝔰 i = 𝔰' (h ▸ i) := by
  intro r r' hr hr' 𝔰 𝔰' hle hle' hw hzeta
  have h1 := val_zeta_le_card F hr 𝔰 hle
  have h2 := val_zeta_le_card F hr' 𝔰' hle'
  rw [hzeta] at h1
  have hdeg : degExp F 𝔰 = degExp F 𝔰' := by
    have h3 : WithZero.exp (-(degExp F 𝔰)) = WithZero.exp (-(degExp F 𝔰')) := h1.symm.trans h2
    exact neg_inj.mp (WithZero.exp_inj.mp h3)
  have hqne : (Nat.card F : ℤ) ≠ 0 := by
    have := card_ge_two F; omega
  have hcode : tupleCode F 𝔰 = tupleCode F 𝔰' := by
    have h3 := degExp_pred_mul_eq_code F 𝔰
    have h4 := degExp_pred_mul_eq_code F 𝔰'
    rw [hdeg, hw] at h3
    have h5 : (Nat.card F : ℤ) * (((tupleCode F 𝔰 : ℕ) : ℤ) - ((tupleWeight 𝔰' : ℕ) : ℤ))
        = (Nat.card F : ℤ) * (((tupleCode F 𝔰' : ℕ) : ℤ) - ((tupleWeight 𝔰' : ℕ) : ℤ)) := by
      rw [← h3, ← h4]
    have h6 := mul_left_cancel₀ hqne h5
    have h7 : ((tupleCode F 𝔰 : ℕ) : ℤ) = ((tupleCode F 𝔰' : ℕ) : ℤ) := by linarith
    exact_mod_cast h7
  exact tupleCode_injective F 𝔰 𝔰' hle hle' hcode

end Code

section LinearIndependent

/-- ★★ **Linear independence over the prime field** of MZVs with entries `≤ q` and pairwise
distinct degrees `degExp`, over an arbitrary finite field. -/
theorem zeta_linearIndependent_le_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝔰 : ι → Σ r : ℕ, Fin r → ℕ+)
    (hr : ∀ i, 1 ≤ (𝔰 i).1) (hle : ∀ i j, ((𝔰 i).2 j : ℕ) ≤ Nat.card F)
    (hdeg : Function.Injective (fun i => degExp F (𝔰 i).2))
    (c : ι → F) (h : (∑ i, cst F (c i) * ζ_A F (𝔰 i).2) = 0) :
    ∀ i, c i = 0 := by
  classical
  set I : Finset ι := Finset.univ.filter (fun i => c i ≠ 0) with hI
  by_contra hcon
  simp only [not_forall] at hcon
  obtain ⟨i0, hi0⟩ := hcon
  have hInon : I.Nonempty := ⟨i0, by simp [hI, hi0]⟩
  obtain ⟨j0, hj0I, hj0min⟩ := Finset.exists_min_image I (fun i => degExp F (𝔰 i).2) hInon
  have hcj0 : c j0 ≠ 0 := by
    have h' := hj0I
    rw [hI] at h'
    simpa using h'
  have hsub : (∑ i ∈ I, cst F (c i) * ζ_A F (𝔰 i).2)
      = ∑ i, cst F (c i) * ζ_A F (𝔰 i).2 := by
    rw [hI]
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro i _ hi
    have hci : c i = 0 := by
      by_contra hc
      exact hi (by simp [hc])
    have hz : cst F (0 : F) = 0 := map_zero (cstHom F)
    rw [hci, hz, zero_mul]
  have hv : ∀ i ∈ I \ {j0},
      Valued.v (cst F (c i) * ζ_A F (𝔰 i).2) < Valued.v (cst F (c j0) * ζ_A F (𝔰 j0).2) := by
    intro i hi
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
    obtain ⟨hiI, hij⟩ := hi
    have hci : c i ≠ 0 := by
      have h' := hiI
      rw [hI] at h'
      simpa using h'
    rw [map_mul, map_mul, v_cst_of_ne_zero F hci, v_cst_of_ne_zero F hcj0, one_mul, one_mul,
      val_zeta_le_card F (hr i) (𝔰 i).2 (hle i), val_zeta_le_card F (hr j0) (𝔰 j0).2 (hle j0),
      WithZero.exp_lt_exp]
    have h2 := hj0min i hiI
    have h3 : degExp F (𝔰 i).2 ≠ degExp F (𝔰 j0).2 := fun hh => hij (hdeg hh)
    omega
  have hval := Valuation.map_sum_eq_of_lt (v := Valued.v) hj0I hv
  have hzero : Valued.v (∑ i ∈ I, cst F (c i) * ζ_A F (𝔰 i).2) = 0 := by
    rw [hsub, h, map_zero]
  rw [hval, map_mul, v_cst_of_ne_zero F hcj0, one_mul,
    val_zeta_le_card F (hr j0) (𝔰 j0).2 (hle j0)] at hzero
  exact WithZero.exp_ne_zero hzero

end LinearIndependent

end ZagierHoffmanPositiveChar
