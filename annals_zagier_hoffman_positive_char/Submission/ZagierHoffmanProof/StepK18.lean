import Submission.ZagierHoffmanProof.StepK17

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Polynomial
open scoped BigOperators

/-!
# Step K18: the uniform stage-step of the `EvalStep d` collapse (polynomial level)

Coefficients are indexed by their degree: a monic degree-`d` polynomial is
`X^d + Σ_{j<d} a_j·X^j` with `a_j ∈ F`; `coeffSeq d a` extends the tuple by the leading
coefficient `a_d = 1`.  The collapse (PLAN SESSION 151/152) removes the coefficients
`a_0, a_1, …, a_{d−1}` in increasing degree; after `s` collapses the current denominator
is `D_s := Σ_{m=0}^{d−s} a_{m+s}·hh 0 (s+1) m`.  The single engine lemma proved here,
for ARBITRARY `d, s` and coefficient tuple `a`, is the uniform per-stage factorisation
(removing the next coefficient `a_s`):

    E_s − E_s^q = (X − X^{q^{s+1}})·D_{s+1},
    E_s := Σ_{m=0}^{d−s−1} a_{m+s+1}·hh 0 (s+1) (m+1)   (D_s with the a_s-term removed)

It is `hh_key` (StepK17, r = s+1) applied termwise to the F-linear combination, using
frobenius additivity (`sum_pow_char_pow'`) and `γ^q = γ` for coefficients.  The s=0 case
(`first_factor_hh`) is the first factor of `EvalStep d` (the constant-coefficient
collapse).  The remaining assembly (nested coefficient sums over `Fin d → F`, iteration
of the stages, final product = 1/ℓ_d) is the next milestone.  All lemmas here are
sorry-free.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

noncomputable def coeffSeq (d : ℕ) (a : Fin d → F) : ℕ → F :=
  fun j => if h : j < d then a ⟨j, h⟩ else 1

/-- `coeffSeq` on the leading index. -/
lemma coeffSeq_d (d : ℕ) (a : Fin d → F) : coeffSeq F d a d = 1 := by
  dsimp [coeffSeq]
  simp

/-- `coeffSeq` matches `a` below `d`. -/
lemma coeffSeq_lt (d : ℕ) (a : Fin d → F) (j : ℕ) (hj : j < d) :
    coeffSeq F d a j = a ⟨j, hj⟩ := by
  dsimp [coeffSeq]
  simp [hj]

/-- ★ THE STAGE STEP (polynomial level).  With `E_s` the stage-`s` combination with the
`s`-coefficient removed and `D_{s+1}` the next-stage combination,

    E_s − E_s^q = (X − X^{q^{s+1}})·D_{s+1},

which is `hh_key` (r = s+1) applied termwise to an arbitrary `F`-linear combination
(frobenius linearity + `γ^q = γ` for the coefficients).  This is the uniform per-stage
factorisation of the `EvalStep d` collapse. -/
lemma stage_step (d s : ℕ) (a : Fin d → F) :
    (∑ m ∈ Finset.range (d - s), C (coeffSeq F d a (m + s + 1)) * hh F 0 (s + 1) (m + 1))
      - ((∑ m ∈ Finset.range (d - s), C (coeffSeq F d a (m + s + 1)) * hh F 0 (s + 1) (m + 1))
          ^ (Nat.card F)) =
      (X - X ^ ((Nat.card F) ^ (s + 1))) *
        (∑ m ∈ Finset.range (d - s), C (coeffSeq F d a (m + s + 1)) * hh F 0 (s + 2) m) := by
  classical
  let E : F[X] := ∑ m ∈ Finset.range (d - s), C (coeffSeq F d a (m + s + 1)) * hh F 0 (s + 1) (m + 1)
  let γ : ℕ → F := fun m => coeffSeq F d a (m + s + 1)
  change E - E ^ (Nat.card F) =
      (X - X ^ ((Nat.card F) ^ (s + 1))) *
        (∑ m ∈ Finset.range (d - s), C (γ m) * hh F 0 (s + 2) m)
  have hkey (m : ℕ) : hh F 0 (s + 1) (m + 1) - hh F 1 (s + 1) (m + 1) =
      (X - X ^ ((Nat.card F) ^ (s + 1))) * hh F 0 (s + 2) m := by
    have hk := hh_key F 0 (s + 1) (m + 1) (by omega)
    -- hk : hh 0 (s+1) (m+1) − hh 1 (s+1) (m+1) = (X^{q^0} − X^{q^{s+1}})·hh 0 (s+2) ((m+1)−1)
    have hsub : (m + 1) - 1 = m := by omega
    rw [hsub] at hk
    -- exponent q^0 = 1 → X
    simpa using hk
  have hfrob (m : ℕ) : (hh F 0 (s + 1) (m + 1)) ^ (Nat.card F) = hh F 1 (s + 1) (m + 1) :=
    hh_frob F 0 (s + 1) (m + 1)
  have hterm (m : ℕ) (hm : m ∈ Finset.range (d - s)) :
      C (γ m) * hh F 0 (s + 1) (m + 1) - (C (γ m) * hh F 0 (s + 1) (m + 1)) ^ (Nat.card F) =
        (X - X ^ ((Nat.card F) ^ (s + 1))) * (C (γ m) * hh F 0 (s + 2) m) := by
    have hpow : (C (γ m)) ^ (Nat.card F) = C (γ m) := by
      calc
        (C (γ m)) ^ (Nat.card F) = C ((γ m) ^ (Nat.card F)) := by
              exact (map_pow C (γ m) (Nat.card F)).symm
        _ = C (γ m) := by
              have hγ : (γ m) ^ (Nat.card F) = γ m := by
                classical
                letI : Fintype F := Fintype.ofFinite F
                rw [← Fintype.card_eq_nat_card]
                exact FiniteField.pow_card (K := F) (γ m)
              rw [hγ]
    calc
      C (γ m) * hh F 0 (s + 1) (m + 1) - (C (γ m) * hh F 0 (s + 1) (m + 1)) ^ (Nat.card F)
          = C (γ m) * hh F 0 (s + 1) (m + 1) - (C (γ m)) ^ (Nat.card F) * (hh F 0 (s + 1) (m + 1)) ^ (Nat.card F) := by
            rw [mul_pow]
      _ = C (γ m) * (hh F 0 (s + 1) (m + 1) - (hh F 0 (s + 1) (m + 1)) ^ (Nat.card F)) := by
            rw [hpow]
            ring
      _ = C (γ m) * ((X - X ^ ((Nat.card F) ^ (s + 1))) * hh F 0 (s + 2) m) := by
            rw [hfrob m]
            rw [hkey m]
      _ = (X - X ^ ((Nat.card F) ^ (s + 1))) * (C (γ m) * hh F 0 (s + 2) m) := by
            ring
  -- frobenius over the sum
  letI : Fintype F := Fintype.ofFinite F
  haveI : CharP F (ringChar F) := ringChar.charP F
  rcases FiniteField.card (K := F) (p := ringChar F) with ⟨n, hprime, hcard⟩
  haveI : Fact (Nat.Prime (ringChar F)) := ⟨hprime⟩
  have hcard' : Nat.card F = (ringChar F) ^ (n : ℕ) := by
    rw [← Fintype.card_eq_nat_card]
    exact hcard
  haveI : CharP (F[X]) (ringChar F) := by
    refine charP_of_injective_algebraMap (R := F) (A := F[X]) ?_ (ringChar F)
    intro u v h
    exact Polynomial.C_injective h
  have hfsum :
      E ^ (Nat.card F) = ∑ m ∈ Finset.range (d - s),
        (C (γ m) * hh F 0 (s + 1) (m + 1)) ^ (Nat.card F) := by
    dsimp [E]
    have hf := sum_pow_char_pow' (p := ringChar F) (n := (n : ℕ)) (R := F[X])
      (s := (Finset.range (d - s) : Finset ℕ))
      (f := fun m : ℕ => C (γ m) * hh F 0 (s + 1) (m + 1))
    rw [← hcard'] at hf
    exact hf
  calc
    E - E ^ (Nat.card F)
        = (∑ m ∈ Finset.range (d - s), C (γ m) * hh F 0 (s + 1) (m + 1))
            - ∑ m ∈ Finset.range (d - s), (C (γ m) * hh F 0 (s + 1) (m + 1)) ^ (Nat.card F) := by
          dsimp [E]
          rw [hfsum]
    _ = ∑ m ∈ Finset.range (d - s),
          (C (γ m) * hh F 0 (s + 1) (m + 1) - (C (γ m) * hh F 0 (s + 1) (m + 1)) ^ (Nat.card F)) := by
          rw [Finset.sum_sub_distrib]
    _ = ∑ m ∈ Finset.range (d - s),
          (X - X ^ ((Nat.card F) ^ (s + 1))) * (C (γ m) * hh F 0 (s + 2) m) := by
          apply Finset.sum_congr rfl
          intro m hm
          exact hterm m hm
    _ = (X - X ^ ((Nat.card F) ^ (s + 1))) *
          (∑ m ∈ Finset.range (d - s), C (γ m) * hh F 0 (s + 2) m) := by
          rw [← Finset.mul_sum]



/-! # monic degree-`d` parametrisation (scaffolding) -/



/-- the monic degree-`d` polynomial with coefficient tuple `a`:
`X^d + Σ_{j<d} a_j·X^j`. -/
noncomputable def monicPd (d : ℕ) (a : Fin d → F) : F[X] :=
  X ^ d + ∑ j : Fin d, C (a j) * X ^ (j : ℕ)

/-- coefficient at the leading degree is `1`. -/
lemma monicPd_coeff_d (d : ℕ) (a : Fin d → F) : (monicPd F d a).coeff d = 1 := by
  classical
  dsimp [monicPd]
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow d d, if_pos rfl]
  have hlow : (∑ j : Fin d, C (a j) * X ^ (j : ℕ)).coeff d = 0 := by
    simp [Polynomial.coeff_C_mul_X_pow]
    apply Finset.sum_eq_zero
    intro j hj
    have hx : (j : ℕ) < d := j.2
    have hne : d ≠ (j : ℕ) := by omega
    simp [hne]
  rw [hlow]
  simp

/-- coefficient beyond the leading degree vanishes. -/
lemma monicPd_coeff_gt (d : ℕ) (a : Fin d → F) (N : ℕ) (hN : d < N) :
    (monicPd F d a).coeff N = 0 := by
  classical
  dsimp [monicPd]
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow d N, if_neg (by omega : N ≠ d)]
  have hlow : (∑ j : Fin d, C (a j) * X ^ (j : ℕ)).coeff N = 0 := by
    simp [Polynomial.coeff_C_mul_X_pow]
    apply Finset.sum_eq_zero
    intro j hj
    by_cases ha : a j = 0
    · simp [ha]
    · rw [if_neg]
      have hx : (j : ℕ) < d := j.2
      omega
  rw [hlow]
  simp

/-- `monicPd d a` has degree ≤ d. -/
lemma monicPd_natDegree_le (d : ℕ) (a : Fin d → F) : (monicPd F d a).natDegree ≤ d := by
  classical
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  exact monicPd_coeff_gt F d a N hN

/-- `monicPd d a` is monic of natural degree `d`. -/
lemma monicPd_monic (d : ℕ) (a : Fin d → F) : (monicPd F d a).Monic := by
  classical
  have hd : (monicPd F d a).natDegree = d := by
    apply le_antisymm (monicPd_natDegree_le F d a)
    by_contra hlt
    have hlt' : (monicPd F d a).natDegree < d := by omega
    have hz : (monicPd F d a).coeff d = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hlt'
    rw [monicPd_coeff_d F d a] at hz
    exact one_ne_zero hz
  change (monicPd F d a).leadingCoeff = 1
  rw [Polynomial.leadingCoeff]
  rw [hd]
  exact monicPd_coeff_d F d a

/-- `monicPd d a` has natural degree `d`. -/
lemma monicPd_natDegree (d : ℕ) (a : Fin d → F) : (monicPd F d a).natDegree = d := by
  classical
  apply le_antisymm (monicPd_natDegree_le F d a)
  by_contra hlt
  have hlt' : (monicPd F d a).natDegree < d := by omega
  have hz : (monicPd F d a).coeff d = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hlt'
  rw [monicPd_coeff_d F d a] at hz
  exact one_ne_zero hz


end ZagierHoffmanPositiveChar
