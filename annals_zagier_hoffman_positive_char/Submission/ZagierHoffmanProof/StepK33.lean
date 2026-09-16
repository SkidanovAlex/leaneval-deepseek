import Submission.ZagierHoffmanProof.StepK32

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Polynomial
open scoped BigOperators

/-!
# Step K33: the UNIFORM stage collapse — StatePoly machinery + `stage_collapse`

`StatePoly s m u := hh 0 (s+1) m + Σ_{j:Fin m} C(u j)·hh 0 (s+1) (j:ℕ)` encodes the
stage-`s` state over the `m` remaining coefficients `u : Fin m`.  The s=0,1 collapses
(Hsum_collapse0/collapse1) are instances of the single uniform collapse
  ★ stage_collapse (s m) : Σ_{u:Fin(m+1)} inv(StatePoly s (m+1) u)
      = A_{s+1}⁻¹·Σ_{v:Fin m} inv(StatePoly (s+1) m v),  A_{s+1} := X−X^{q^{s+1}},
proven from: StatePoly_zero_eq_monicPd (s=0 is monicPd), StatePoly_cons_affine
(slope-1 affine in the head), state_coeff_top/state_nonconst (head-zeroed state is
nonconstant — its top coefficient is 1), StatePoly_glue (Z−Z^q = A_{s+1}·StatePoly(s+1))
via hh_key, frob_add/frob_fin_sum, and Hsum_one_subst for the inner collapse.  Then the
tower + Hsum_closed + EvalU_all close the power-sum evaluation for every level.
All sorry-free.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- the stage-`s` state polynomial over the `m` remaining coefficients `u`:
`hh 0 (s+1) m` (leading block, coefficient 1) plus the `u`-combination. -/
noncomputable def StatePoly (s m : ℕ) (u : Fin m → F) : F[X] :=
  hh F 0 (s + 1) m + ∑ j : Fin m, C (u j) * hh F 0 (s + 1) (j : ℕ)

/-- s=0: the state is the monic polynomial `monicPd`. -/
lemma StatePoly_zero_eq_monicPd (m : ℕ) (u : Fin m → F) :
    StatePoly F 0 m u = monicPd F m u := by
  classical
  have hh1 (k : ℕ) : hh F 0 1 k = X ^ k := by
    rw [hh_one F 0 k]
    simp
  calc
    StatePoly F 0 m u = hh F 0 1 m + ∑ j : Fin m, C (u j) * hh F 0 1 (j : ℕ) := by rfl
    _ = X ^ m + ∑ j : Fin m, C (u j) * X ^ (j : ℕ) := by
          rw [hh1 m]
          apply congrArg (fun p : F[X] => X ^ m + p)
          apply Finset.sum_congr rfl
          intro j hj
          rw [hh1 (j : ℕ)]
    _ = monicPd F m u := by rfl

/-- expanding the cons-state: head term `C x·hh 0 (s+1) 0` plus the `v`-tail. -/
lemma StatePoly_cons_expand (s m : ℕ) (x : F) (v : Fin m → F) :
    StatePoly F s (m + 1) (Fin.cons x v) =
      hh F 0 (s + 1) (m + 1) + C x * hh F 0 (s + 1) 0 +
        (∑ k : Fin m, C (v k) * hh F 0 (s + 1) ((k : ℕ) + 1)) := by
  classical
  dsimp [StatePoly]
  rw [Fin.sum_univ_succ]
  have ht : (∑ k : Fin m, C (((Fin.cons x v : Fin (m + 1) → F)) k.succ) * hh F 0 (s + 1) (k.succ : ℕ)) =
      ∑ k : Fin m, C (v k) * hh F 0 (s + 1) ((k : ℕ) + 1) := by
    apply Finset.sum_congr rfl
    intro k hk
    simp [Fin.cons_succ, Fin.val_succ]
  have hf0 : C (((Fin.cons x v : Fin (m + 1) → F)) (0 : Fin (m + 1))) * hh F 0 (s + 1) ((0 : Fin (m + 1)) : ℕ) =
      C x * hh F 0 (s + 1) 0 := by
    simp [Fin.cons_zero, Fin.val_zero]
  rw [ht, hf0]
  rw [add_assoc]

/-- the state is affine in its first remaining coefficient, with slope 1. -/
lemma StatePoly_cons_affine (s m : ℕ) (c : F) (v : Fin m → F) :
    StatePoly F s (m + 1) (Fin.cons c v) = C c + StatePoly F s (m + 1) (Fin.cons 0 v) := by
  classical
  have hc := StatePoly_cons_expand F s m c v
  have h0 := StatePoly_cons_expand F s m (0 : F) v
  have hh0 : hh F 0 (s + 1) 0 = 1 := hh_zero F 0 (s + 1)
  have hC0 : C (0 : F) = 0 := by simp
  calc
    StatePoly F s (m + 1) (Fin.cons c v)
        = hh F 0 (s + 1) (m + 1) + C c * hh F 0 (s + 1) 0 + (∑ k : Fin m, C (v k) * hh F 0 (s + 1) ((k : ℕ) + 1)) := hc
    _ = C c + (hh F 0 (s + 1) (m + 1) + C (0 : F) * hh F 0 (s + 1) 0 + (∑ k : Fin m, C (v k) * hh F 0 (s + 1) ((k : ℕ) + 1))) := by
          rw [hh0, hC0]
          ring
    _ = C c + StatePoly F s (m + 1) (Fin.cons 0 v) := by rw [h0]


/-- frobenius-additivity in `F[X]`: `(a+b)^q = a^q + b^q`. -/
lemma frob_add (a b : F[X]) :
    (a + b) ^ (Nat.card F) = a ^ (Nat.card F) + b ^ (Nat.card F) := by
  classical
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
  calc
    (a + b) ^ (Nat.card F) = (a + b) ^ ((ringChar F) ^ (n : ℕ)) := by rw [hcard']
    _ = a ^ ((ringChar F) ^ (n : ℕ)) + b ^ ((ringChar F) ^ (n : ℕ)) := by
          exact add_pow_char_pow a b (ringChar F) (n : ℕ)
    _ = a ^ (Nat.card F) + b ^ (Nat.card F) := by rw [hcard']

/-- frobenius over a `Fin`-sum in `F[X]`. -/
lemma frob_fin_sum (m : ℕ) (f : Fin m → F[X]) :
    (∑ j : Fin m, f j) ^ (Nat.card F) = ∑ j : Fin m, (f j) ^ (Nat.card F) := by
  classical
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
  have hf := sum_pow_char_pow' (p := ringChar F) (n := (n : ℕ)) (R := F[X])
    (s := (Finset.univ : Finset (Fin m))) (f := f)
  -- hf : (∑ x ∈ univ, f x) ^ (ringChar F ^ n) = ∑ x ∈ univ, (f x) ^ (ringChar F ^ n)
  -- membership sums are the Fin sums
  rw [hcard']
  simpa using hf

/-- the head-zeroed state has top coefficient `1` at degree `q^s·(m+1)`. -/
lemma state_coeff_top (s m : ℕ) (v : Fin m → F) :
    (StatePoly F s (m + 1) (Fin.cons 0 v)).coeff ((Nat.card F) ^ s * (m + 1)) = 1 := by
  classical
  have hz := StatePoly_cons_expand F s m (0 : F) v
  -- Z = hh(m+1) + C 0·hh 0 + Σ C(v k)·hh(k.val+1)
  rw [hz]
  rw [Polynomial.coeff_add]
  rw [Polynomial.coeff_add]
  -- term1: hh 0 (s+1)(m+1) at q^s·(m+1) = 1
  have ht : (hh F 0 (s + 1) (m + 1)).coeff ((Nat.card F) ^ s * (m + 1)) = 1 :=
    hh_topcoeff0 F s (m + 1) (by omega)
  -- term2: C 0·hh 0 (s+1) 0 = 0 → coeff 0
  have hc0 : C (0 : F) * hh F 0 (s + 1) 0 = 0 := by simp
  have hz2 : (C (0 : F) * hh F 0 (s + 1) 0).coeff ((Nat.card F) ^ s * (m + 1)) = 0 := by
    rw [hc0]
    simp
  -- term3: the sum, coeff 0 at e
  have hsum : (∑ k : Fin m, C (v k) * hh F 0 (s + 1) ((k : ℕ) + 1)).coeff
      ((Nat.card F) ^ s * (m + 1)) = 0 := by
    rw [finsetSum_coeff]
    apply Finset.sum_eq_zero
    intro k hk
    have hklt : (k : ℕ) < m := k.2
    have hlt : (Nat.card F) ^ s * ((k : ℕ) + 1) < (Nat.card F) ^ s * (m + 1) := by
      have hqpos : 0 < (Nat.card F) ^ s := by
        have hq0 : 0 < Nat.card F := by
          have hq1 : 2 ≤ Nat.card F := card_ge_two F
          omega
        exact pow_pos hq0 s
      nlinarith
    have hhcoeff := hh_above0 F s ((k : ℕ) + 1) ((Nat.card F) ^ s * (m + 1)) hlt
    rw [Polynomial.coeff_C_mul]
    rw [hhcoeff]
    simp
  rw [ht, hz2, hsum]
  simp

/-- the head-zeroed state is nonconstant (used as the `Hsum_one_subst` argument). -/
lemma state_nonconst (s m : ℕ) (v : Fin m → F) :
    (StatePoly F s (m + 1) (Fin.cons 0 v)).natDegree ≠ 0 := by
  classical
  intro hz0
  have hc := state_coeff_top F s m v
  have he : 0 < (Nat.card F) ^ s * (m + 1) := by
    have hq0 : 0 < Nat.card F := by
      have hq1 : 2 ≤ Nat.card F := card_ge_two F
      omega
    have hq : 0 < (Nat.card F) ^ s := pow_pos hq0 s
    exact mul_pos hq (by omega)
  have hz : (StatePoly F s (m + 1) (Fin.cons 0 v)).coeff ((Nat.card F) ^ s * (m + 1)) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hz0]; exact he)
  rw [hc] at hz
  exact one_ne_zero hz


/-- ★ THE GLUE at every stage: the head-zeroed state collapses with factor
`X − X^{q^{s+1}}` onto the next state. -/
lemma StatePoly_glue (s m : ℕ) (v : Fin m → F) :
    StatePoly F s (m + 1) (Fin.cons 0 v) - (StatePoly F s (m + 1) (Fin.cons 0 v)) ^ (Nat.card F) =
      (X - X ^ ((Nat.card F) ^ (s + 1))) * StatePoly F (s + 1) m v := by
  classical
  let T : F[X] := hh F 0 (s + 1) (m + 1)
  let S : F[X] := ∑ k : Fin m, C (v k) * hh F 0 (s + 1) ((k : ℕ) + 1)
  have hZ : StatePoly F s (m + 1) (Fin.cons 0 v) = T + S := by
    have hz := StatePoly_cons_expand F s m (0 : F) v
    rw [hz]
    have hC0 : C (0 : F) * hh F 0 (s + 1) 0 = 0 := by simp
    rw [hC0]
    dsimp [T, S]
    ring
  -- per-block factorisations (hh_key with r = s+1)
  have hkT : hh F 0 (s + 1) (m + 1) - hh F 1 (s + 1) (m + 1) =
      (X - X ^ ((Nat.card F) ^ (s + 1))) * hh F 0 (s + 2) m := by
    have hk := hh_key F 0 (s + 1) (m + 1) (by omega)
    have hsub : (m + 1) - 1 = m := by omega
    rw [hsub] at hk
    simpa using hk
  have hfk (k : Fin m) : hh F 0 (s + 1) ((k : ℕ) + 1) - hh F 1 (s + 1) ((k : ℕ) + 1) =
      (X - X ^ ((Nat.card F) ^ (s + 1))) * hh F 0 (s + 2) (k : ℕ) := by
    have hk := hh_key F 0 (s + 1) ((k : ℕ) + 1) (by omega)
    have hsub : ((k : ℕ) + 1) - 1 = (k : ℕ) := by omega
    rw [hsub] at hk
    simpa using hk
  -- per-term of S
  have hterm (k : Fin m) :
      C (v k) * hh F 0 (s + 1) ((k : ℕ) + 1) - (C (v k) * hh F 0 (s + 1) ((k : ℕ) + 1)) ^ (Nat.card F) =
        (X - X ^ ((Nat.card F) ^ (s + 1))) * (C (v k) * hh F 0 (s + 2) (k : ℕ)) := by
    have hpow : (C (v k)) ^ (Nat.card F) = C (v k) := by
      calc
        (C (v k)) ^ (Nat.card F) = C ((v k) ^ (Nat.card F)) := (map_pow C (v k) (Nat.card F)).symm
        _ = C (v k) := by
          have hγ : (v k) ^ (Nat.card F) = v k := by
            classical
            letI : Fintype F := Fintype.ofFinite F
            rw [← Fintype.card_eq_nat_card]
            exact FiniteField.pow_card (K := F) (v k)
          rw [hγ]
    have hhf := hh_frob F 0 (s + 1) ((k : ℕ) + 1)
    calc
      C (v k) * hh F 0 (s + 1) ((k : ℕ) + 1) - (C (v k) * hh F 0 (s + 1) ((k : ℕ) + 1)) ^ (Nat.card F)
          = C (v k) * hh F 0 (s + 1) ((k : ℕ) + 1) - (C (v k)) ^ (Nat.card F) * (hh F 0 (s + 1) ((k : ℕ) + 1)) ^ (Nat.card F) := by
            rw [mul_pow]
      _ = C (v k) * (hh F 0 (s + 1) ((k : ℕ) + 1) - (hh F 0 (s + 1) ((k : ℕ) + 1)) ^ (Nat.card F)) := by
            rw [hpow]
            ring
      _ = C (v k) * ((X - X ^ ((Nat.card F) ^ (s + 1))) * hh F 0 (s + 2) (k : ℕ)) := by
            rw [hhf]
            rw [hfk k]
      _ = (X - X ^ ((Nat.card F) ^ (s + 1))) * (C (v k) * hh F 0 (s + 2) (k : ℕ)) := by
            ring
  have hS : S - S ^ (Nat.card F) =
      (X - X ^ ((Nat.card F) ^ (s + 1))) * (∑ k : Fin m, C (v k) * hh F 0 (s + 2) (k : ℕ)) := by
    dsimp [S]
    have hfrob := frob_fin_sum F m (fun k : Fin m => C (v k) * hh F 0 (s + 1) ((k : ℕ) + 1))
    calc
      (∑ k : Fin m, C (v k) * hh F 0 (s + 1) ((k : ℕ) + 1))
          - (∑ k : Fin m, C (v k) * hh F 0 (s + 1) ((k : ℕ) + 1)) ^ (Nat.card F)
          = (∑ k : Fin m, C (v k) * hh F 0 (s + 1) ((k : ℕ) + 1))
              - ∑ k : Fin m, (C (v k) * hh F 0 (s + 1) ((k : ℕ) + 1)) ^ (Nat.card F) := by
            rw [hfrob]
      _ = ∑ k : Fin m, (C (v k) * hh F 0 (s + 1) ((k : ℕ) + 1)
              - (C (v k) * hh F 0 (s + 1) ((k : ℕ) + 1)) ^ (Nat.card F)) := by
            rw [Finset.sum_sub_distrib]
      _ = ∑ k : Fin m, ((X - X ^ ((Nat.card F) ^ (s + 1))) * (C (v k) * hh F 0 (s + 2) (k : ℕ))) := by
            apply Finset.sum_congr rfl
            intro k hk
            exact hterm k
      _ = (X - X ^ ((Nat.card F) ^ (s + 1))) * (∑ k : Fin m, C (v k) * hh F 0 (s + 2) (k : ℕ)) := by
            rw [← Finset.mul_sum]
  calc
    StatePoly F s (m + 1) (Fin.cons 0 v) - (StatePoly F s (m + 1) (Fin.cons 0 v)) ^ (Nat.card F)
        = (T + S) - (T + S) ^ (Nat.card F) := by rw [hZ]
    _ = (T + S) - (T ^ (Nat.card F) + S ^ (Nat.card F)) := by rw [frob_add F T S]
    _ = (T - T ^ (Nat.card F)) + (S - S ^ (Nat.card F)) := by ring
    _ = (X - X ^ ((Nat.card F) ^ (s + 1))) * (hh F 0 (s + 2) m) +
          (X - X ^ ((Nat.card F) ^ (s + 1))) * (∑ k : Fin m, C (v k) * hh F 0 (s + 2) (k : ℕ)) := by
          have hT : T - T ^ (Nat.card F) = (X - X ^ ((Nat.card F) ^ (s + 1))) * hh F 0 (s + 2) m := by
            dsimp [T]
            rw [hh_frob F 0 (s + 1) (m + 1)]
            rw [hkT]
          rw [hT, hS]
    _ = (X - X ^ ((Nat.card F) ^ (s + 1))) *
          (hh F 0 (s + 2) m + ∑ k : Fin m, C (v k) * hh F 0 (s + 2) (k : ℕ)) := by
          rw [← mul_add]
    _ = (X - X ^ ((Nat.card F) ^ (s + 1))) * StatePoly F (s + 1) m v := by
          rfl


/-- ★ THE STAGE COLLAPSE (uniform in `s`): the state-`s` sum over `Fin (m+1)` collapses
with factor `A_{s+1}⁻¹` onto the state-`(s+1)` sum over `Fin m`. -/
lemma stage_collapse (s m : ℕ) :
    letI : Fintype F := Fintype.ofFinite F
    (∑ u : Fin (m + 1) → F, ((((StatePoly F s (m + 1) u : F[X]) : F[X]) : RatFunc F)⁻¹)) =
      ((((X - X ^ ((Nat.card F) ^ (s + 1)) : F[X]) : F[X]) : RatFunc F)⁻¹) *
        (∑ v : Fin m → F, ((((StatePoly F (s + 1) m v : F[X]) : F[X]) : RatFunc F)⁻¹)) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  letI : DecidableEq F := Classical.decEq F
  let Acast : RatFunc F := (((X - X ^ ((Nat.card F) ^ (s + 1)) : F[X]) : F[X]) : RatFunc F)
  calc
    (∑ u : Fin (m + 1) → F, ((((StatePoly F s (m + 1) u : F[X]) : F[X]) : RatFunc F)⁻¹))
        = ∑ c : F, ∑ v : Fin m → F, ((((StatePoly F s (m + 1) (Fin.cons c v) : F[X]) : F[X]) : RatFunc F)⁻¹) := by
            rw [sum_cons_split F m (fun u : Fin (m + 1) → F =>
              ((((StatePoly F s (m + 1) u : F[X]) : F[X]) : RatFunc F)⁻¹))]
            rw [Fintype.sum_prod_type]
    _ = ∑ v : Fin m → F, ∑ c : F, ((((C c + StatePoly F s (m + 1) (Fin.cons 0 v) : F[X]) : F[X]) : RatFunc F)⁻¹) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro v hv
            apply Finset.sum_congr rfl
            intro c hc
            apply congrArg (fun x : RatFunc F => x⁻¹)
            have hm := congrArg (fun p : F[X] => (((p : F[X]) : F[X]) : RatFunc F))
              (StatePoly_cons_affine F s m c v)
            simpa using hm
    _ = ∑ v : Fin m → F, ((((StatePoly F s (m + 1) (Fin.cons 0 v) - (StatePoly F s (m + 1) (Fin.cons 0 v)) ^ (Nat.card F) : F[X]) : F[X]) : RatFunc F)⁻¹) := by
          apply Finset.sum_congr rfl
          intro v hv
          have h := Hsum_one_subst F (StatePoly F s (m + 1) (Fin.cons 0 v)) (state_nonconst F s m v)
          simpa [add_comm] using h
    _ = Acast⁻¹ * (∑ v : Fin m → F, ((((StatePoly F (s + 1) m v : F[X]) : F[X]) : RatFunc F)⁻¹)) := by
          have hfac (v : Fin m → F) :
              ((((StatePoly F s (m + 1) (Fin.cons 0 v) - (StatePoly F s (m + 1) (Fin.cons 0 v)) ^ (Nat.card F) : F[X]) : F[X]) : RatFunc F)⁻¹) =
                Acast⁻¹ * ((((StatePoly F (s + 1) m v : F[X]) : F[X]) : RatFunc F)⁻¹) := by
            have hg := StatePoly_glue F s m v
            have hc' : ((((StatePoly F s (m + 1) (Fin.cons 0 v) - (StatePoly F s (m + 1) (Fin.cons 0 v)) ^ (Nat.card F) : F[X]) : F[X]) : RatFunc F)) =
                Acast * ((((StatePoly F (s + 1) m v : F[X]) : F[X]) : RatFunc F)) := by
              dsimp [Acast]
              have h := congrArg (algebraMap (F[X]) (RatFunc F)) hg
              rw [map_mul] at h
              exact h
            calc
              ((((StatePoly F s (m + 1) (Fin.cons 0 v) - (StatePoly F s (m + 1) (Fin.cons 0 v)) ^ (Nat.card F) : F[X]) : F[X]) : RatFunc F)⁻¹)
                  = (Acast * ((((StatePoly F (s + 1) m v : F[X]) : F[X]) : RatFunc F)))⁻¹ := by rw [hc']
              _ = Acast⁻¹ * ((((StatePoly F (s + 1) m v : F[X]) : F[X]) : RatFunc F)⁻¹) := by
                    rw [mul_inv_rev, mul_comm]
          calc
            (∑ v : Fin m → F, ((((StatePoly F s (m + 1) (Fin.cons 0 v) - (StatePoly F s (m + 1) (Fin.cons 0 v)) ^ (Nat.card F) : F[X]) : F[X]) : RatFunc F)⁻¹))
                = ∑ v : Fin m → F, (Acast⁻¹ * ((((StatePoly F (s + 1) m v : F[X]) : F[X]) : RatFunc F)⁻¹)) := by
                  apply Finset.sum_congr rfl
                  intro v hv
                  exact hfac v
            _ = Acast⁻¹ * (∑ v : Fin m → F, ((((StatePoly F (s + 1) m v : F[X]) : F[X]) : RatFunc F)⁻¹)) := by
                  rw [Finset.mul_sum]




/-- `A_e := X − X^{q^e}` cast into `RatFunc F`. -/
noncomputable def Afac (e : ℕ) : RatFunc F :=
  ((((X - X ^ ((Nat.card F) ^ e) : F[X]) : F[X]) : RatFunc F))

/-- `G(s,m)` — the stage-`s` state sum over `Fin m` coefficients. -/
noncomputable def G (s m : ℕ) : RatFunc F :=
  letI : Fintype F := Fintype.ofFinite F
  ∑ u : Fin m → F, ((((StatePoly F s m u : F[X]) : F[X]) : RatFunc F)⁻¹)

/-- the collapse in `G`-form: `G(s,m+1) = A_{s+1}⁻¹·G(s+1,m)`. -/
lemma G_collapse (s m : ℕ) :
    letI : Fintype F := Fintype.ofFinite F
    G F s (m + 1) = (Afac F (s + 1))⁻¹ * G F (s + 1) m := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have h := stage_collapse F s m
  dsimp [G, Afac]
  exact h

/-- the terminal state at `m = 0` is `1`. -/
lemma StatePoly_zero_zero (s : ℕ) (u : Fin 0 → F) : StatePoly F s 0 u = 1 := by
  classical
  dsimp [StatePoly]
  have hh0 : hh F 0 (s + 1) 0 = 1 := hh_zero F 0 (s + 1)
  rw [hh0]
  simp

/-- `G(s,0) = 1` for every stage `s`. -/
lemma G_zero (s : ℕ) :
    letI : Fintype F := Fintype.ofFinite F
    G F s 0 = 1 := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  let a : Fin 0 → F := fun _ : Fin 0 => (0 : F)
  have huniq : ∀ u : Fin 0 → F, u = a := by
    intro u
    funext j
    exact Fin.elim0 j
  have hsum : (∑ u : Fin 0 → F, ((((StatePoly F s 0 u : F[X]) : F[X]) : RatFunc F)⁻¹)) =
      ((((StatePoly F s 0 a : F[X]) : F[X]) : RatFunc F)⁻¹) := by
    exact Fintype.sum_eq_single a (fun u hu => False.elim (hu (huniq u)))
  calc
    G F s 0 = ∑ u : Fin 0 → F, ((((StatePoly F s 0 u : F[X]) : F[X]) : RatFunc F)⁻¹) := by rfl
    _ = ((((StatePoly F s 0 a : F[X]) : F[X]) : RatFunc F)⁻¹) := hsum
    _ = ((((1 : F[X]) : F[X]) : RatFunc F)⁻¹) := by
          have hp : StatePoly F s 0 a = 1 := StatePoly_zero_zero F s a
          rw [hp]
    _ = 1 := by simp

/-- ★ THE TOWER: `G(s,m) = (∏_{i<m} A_{s+1+i}⁻¹)·G(s+m, 0)`. -/
lemma tower : ∀ (m : ℕ), ∀ (s : ℕ),
    letI : Fintype F := Fintype.ofFinite F
    G F s m = (∏ i ∈ Finset.range m, (Afac F (s + 1 + i))⁻¹) * G F (s + m) 0 := by
  classical
  intro m
  induction m with
  | zero =>
      intro s
      letI : Fintype F := Fintype.ofFinite F
      have hz := G_zero F s
      calc
        G F s 0 = 1 := hz
        _ = (∏ i ∈ Finset.range 0, (Afac F (s + 1 + i))⁻¹) * G F (s + 0) 0 := by
              simpa using hz.symm
  | succ m ih =>
      intro s
      letI : Fintype F := Fintype.ofFinite F
      have hcol := G_collapse F s m
      have hstep := ih (s + 1)
      -- hstep : G (s+1) m = (∏_{i<m} (Afac ((s+1)+1+i))⁻¹) · G ((s+1)+m) 0
      calc
        G F s (m + 1) = (Afac F (s + 1))⁻¹ * G F (s + 1) m := hcol
        _ = (Afac F (s + 1))⁻¹ *
              ((∏ i ∈ Finset.range m, (Afac F ((s + 1) + 1 + i))⁻¹) * G F ((s + 1) + m) 0) := by
              rw [hstep]
        _ = ((∏ i ∈ Finset.range (m + 1), (Afac F (s + 1 + i))⁻¹)) * G F (s + (m + 1)) 0 := by
              -- rearrange: (f0⁻¹)·((∏_{i<m} f(i+1)⁻¹)·G0) = (∏_{i<m+1} f i⁻¹)·G0
              have hprod : (∏ i ∈ Finset.range (m + 1), (Afac F (s + 1 + i))⁻¹) =
                  (Afac F (s + 1))⁻¹ * (∏ i ∈ Finset.range m, (Afac F ((s + 1) + 1 + i))⁻¹) := by
                -- ∏ over range(m+1) = f 0 · ∏_{i<m} f(i+1); then exponents match
                have hre := Finset.prod_range_succ' (fun i : ℕ => (Afac F (s + 1 + i))⁻¹) m
                -- hre : ∏_{k∈range(m+1)} f k = (∏_{k∈range m} f(k+1)) · f 0
                rw [hre]
                have he (i : ℕ) : s + 1 + (i + 1) = (s + 1) + 1 + i := by omega
                have hf : (∏ i ∈ Finset.range m, (Afac F (s + 1 + (i + 1)))⁻¹) =
                    (∏ i ∈ Finset.range m, (Afac F ((s + 1) + 1 + i))⁻¹) := by
                  apply Finset.prod_congr rfl
                  intro i hi
                  congr 1
                  congr 1
                  omega
                rw [hf]
                ring
              have hG : G F ((s + 1) + m) 0 = G F (s + (m + 1)) 0 := by
                congr 1
                omega
              rw [hprod, hG]
              ring



/-- the level-`e` factor `A_e` is nonzero in `RatFunc` for `e ≥ 1`. -/
lemma Afac_ne_zero (e : ℕ) (he : 1 ≤ e) : Afac F e ≠ 0 := by
  classical
  dsimp [Afac]
  intro hz
  have hq : 2 ≤ Nat.card F := card_ge_two F
  have hme : 2 ≤ (Nat.card F) ^ e := by
    have hq0 : 0 < Nat.card F := by omega
    have h1e : 1 ≤ e := he
    have hpowmono := Nat.pow_le_pow_right hq0 h1e  -- q^1 ≤ q^e
    have hq1 : 2 ≤ (Nat.card F) ^ 1 := by simpa using hq
    omega
  have hp : (X - X ^ ((Nat.card F) ^ e) : F[X]) ≠ 0 := by
    intro h0
    have hc : (X - X ^ ((Nat.card F) ^ e) : F[X]).coeff 1 = 1 := by
      have hne : 1 ≠ (Nat.card F) ^ e := by omega
      rw [Polynomial.coeff_sub]
      simp [Polynomial.coeff_X, Polynomial.coeff_X_pow ((Nat.card F) ^ e) 1, hne]
    have hz' : (X - X ^ ((Nat.card F) ^ e) : F[X]).coeff 1 = 0 := by
      rw [h0]
      simp
    rw [hc] at hz'
    exact one_ne_zero hz'
  have hcast : (((X - X ^ ((Nat.card F) ^ e) : F[X]) : F[X]) : RatFunc F) = 0 := by
    simpa using hz
  exact hp (RatFunc.algebraMap_injective F (by simpa using hcast))

/-- ★ THE CLOSED FORM: `Hsum F D 1 = ∏_{i<D} A_{i+1}⁻¹` (i.e. `U_D = 1/ℓ_D`). -/
lemma Hsum_closed (D : ℕ) :
    letI : Fintype F := Fintype.ofFinite F
    Hsum F D 1 = ∏ i ∈ Finset.range D, (Afac F (i + 1))⁻¹ := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have ht := tower F D 0
  have hz := G_zero F D
  have hsumG : Hsum F D 1 = G F 0 D := by
    calc
      Hsum F D 1 = ∑ a : Fin D → F, ((((monicPd F D a : F[X]) : F[X]) : RatFunc F)⁻¹) := Hsum_tuple F D
      _ = G F 0 D := by
            dsimp [G]
            apply Finset.sum_congr rfl
            intro a ha
            apply congrArg (fun x : RatFunc F => x⁻¹)
            have hm := congrArg (fun p : F[X] => (((p : F[X]) : F[X]) : RatFunc F))
              (StatePoly_zero_eq_monicPd F D a).symm
            simpa using hm
  calc
    Hsum F D 1 = G F 0 D := hsumG
    _ = (∏ i ∈ Finset.range D, (Afac F (0 + 1 + i))⁻¹) * G F (0 + D) 0 := ht
    _ = ∏ i ∈ Finset.range D, (Afac F (i + 1))⁻¹ := by
          have hG : G F (0 + D) 0 = 1 := by
            have h0 : 0 + D = D := by omega
            rw [h0]
            exact G_zero F D
          have hfac (i : ℕ) (hi : i ∈ Finset.range D) : (Afac F (0 + 1 + i))⁻¹ = (Afac F (i + 1))⁻¹ := by
            congr 1
            congr 1
            omega
          calc
            (∏ i ∈ Finset.range D, (Afac F (0 + 1 + i))⁻¹) * G F (0 + D) 0
                = (∏ i ∈ Finset.range D, (Afac F (0 + 1 + i))⁻¹) * 1 := by rw [hG]
            _ = ∏ i ∈ Finset.range D, (Afac F (0 + 1 + i))⁻¹ := by simp
            _ = ∏ i ∈ Finset.range D, (Afac F (i + 1))⁻¹ := by
                  apply Finset.prod_congr rfl
                  intro i hi
                  exact hfac i hi

/-- the cast of `ℓ_D` is the product of the `A_{i+1}`. -/
lemma lFact_cast_eq (D : ℕ) :
    ((lFact F D : F[X]) : RatFunc F) = ∏ i ∈ Finset.range D, Afac F (i + 1) := by
  classical
  -- unfold lFact; cast the product through algebraMap
  have hdef : (lFact F D : RatFunc F) =
      (algebraMap (F[X]) (RatFunc F)) (∏ j ∈ Finset.range D, (X - X ^ ((Nat.card F) ^ (j + 1)) : F[X])) := by
    dsimp [lFact]
  rw [hdef]
  rw [map_prod]
  -- goal: ∏_{j∈range D} algebraMap(X − X^{q^{j+1}}) = ∏_{i∈range D} Afac (i+1)
  apply Finset.prod_congr rfl
  intro j hj
  dsimp [Afac]

/-- ★ `EvalU` AT EVERY LEVEL: `Hsum F e 1 · ℓ_e = 1` (Thakur's evaluation, all `e`). -/
theorem EvalU_all : ∀ e : ℕ, EvalU F e := by
  classical
  intro e
  unfold EvalU
  have hc := Hsum_closed F e
  rw [hc]
  have hl := lFact_cast_eq F e
  rw [hl]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro i hi
  exact inv_mul_cancel₀ (Afac_ne_zero F (i + 1) (by omega))

end ZagierHoffmanPositiveChar
