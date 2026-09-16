import Submission.ZagierHoffmanProof.StepK13
import Submission.ZagierHoffmanProof.StepK11

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Polynomial
open scoped BigOperators

/-!
# Step K16: `EvalU ∀d ⇒ ID2 ∀d ⇒ R1 ∀d` (the R1-chain closure)

The single open input of the R1 chain (StepK7–K13) is `ID2(d)` at every level `d ≥ 1`.
This module shows `ID2(d)` follows from the power-sum evaluation `EvalU e`
(`Hsum F e 1 · ℓ_e = 1`, i.e. `U_e = 1/ℓ_e`) for all `e`:
  * the embedded evaluation gives `u_e · ℓ_e = 1` in the completion `K∞`
    (`uEval_mul_lK`, `u_e := P F e 1`), hence `u_e ≠ 0`, `ℓ_e ≠ 0`;
  * `ℓ_{e+1} = ℓ_e·(X−X^{q^{e+1}})` (`lK_succ`) gives the ratio
    `u_e·(u_{e+1})⁻¹ = X − X^{q^{e+1}}` (`uEval_ratio`);
  * the freshman identity `(X−X^{q^{d+1}}) + D1 = (X−X^{q^d})^q`
    (`carlitz_freshman` in `F[X]`, embedded in `facK_freshman`) closes the ratio
    recursion `w_d + D1 = w_{d−1}^q`, i.e. exactly `ID2(d)` (`ID2_of_EvalU`).
Consequences (theorem form): `R1Prop_of_EvalU` (paper (2.8) for every level) and
`P_oneExp_ne_zero_of_EvalU`.  All sorry-free.  (PLAN SESSION 151b.)
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]




/-- cast of a product in `RatFunc F` into the completion is the product of the casts. -/
lemma coe_K_mul (a b : RatFunc F) :
    ((a * b : RatFunc F) : RatFunc.CompletionAtInfty F) =
      ((a : RatFunc F) : RatFunc.CompletionAtInfty F) *
        ((b : RatFunc F) : RatFunc.CompletionAtInfty F) := by
  simp [rat_cast_eq_algebraMap, map_mul]

/-- full pipeline: a polynomial product, cast all the way to the completion. -/
lemma coe_K_poly_mul (p q : F[X]) :
    ((((p * q : F[X]) : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F) =
      ((((p : F[X]) : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F) *
        ((((q : F[X]) : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F) := by
  rw [show (((p * q : F[X]) : F[X]) : RatFunc F) =
      ((((p : F[X]) : F[X]) : RatFunc F) * (((q : F[X]) : F[X]) : RatFunc F)) by
    simp [poly_cast_eq_algebraMap, map_mul]]
  exact coe_K_mul F (((p : F[X]) : F[X]) : RatFunc F) (((q : F[X]) : F[X]) : RatFunc F)

/-- exponent-one power sum at level `e`, in the completion. -/
noncomputable def uEval (e : ℕ) : RatFunc.CompletionAtInfty F :=
  P F e oneExp

/-- the Carlitz factorial `ℓ_e` cast into the completion. -/
noncomputable def lK (e : ℕ) : RatFunc.CompletionAtInfty F :=
  ((((lFact F e : F[X]) : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F)

/-- the factor `X − X^{q^e}` cast into the completion. -/
noncomputable def facK (e : ℕ) : RatFunc.CompletionAtInfty F :=
  ((((X - X ^ ((Nat.card F) ^ e) : F[X]) : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F)

/-- `u_e · ℓ_e = 1` in the completion, from the RatFunc-level `EvalU e`. -/
lemma uEval_mul_lK (e : ℕ) (hEval : EvalU F e) : uEval F e * lK F e = 1 := by
  classical
  dsimp [EvalU] at hEval
  let φ : RatFunc F →+* RatFunc.CompletionAtInfty F :=
    algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)
  have hφ := congrArg (fun x : RatFunc F => φ x) hEval
  rw [map_mul] at hφ
  rw [map_one] at hφ
  unfold uEval lK
  rw [P_eq_coe_Hsum F e oneExp]
  simpa [rat_cast_eq_algebraMap, oneExp] using hφ

/-- `u_e ≠ 0`. -/
lemma uEval_ne_zero (e : ℕ) (hEval : EvalU F e) : uEval F e ≠ 0 := by
  exact left_ne_zero_of_mul_eq_one (uEval_mul_lK F e hEval)

/-- `ℓ_e ≠ 0` in the completion. -/
lemma lK_ne_zero (e : ℕ) (hEval : EvalU F e) : lK F e ≠ 0 := by
  exact right_ne_zero_of_mul_eq_one (uEval_mul_lK F e hEval)

/-- `ℓ_{e+1} = ℓ_e·(X−X^{q^{e+1}})` in the completion. -/
lemma lK_succ (e : ℕ) : lK F (e + 1) = lK F e * facK F (e + 1) := by
  classical
  have h := congrArg (fun p : F[X] => ((((p : F[X]) : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F)) (lFact_succ F e)
  -- h : cast(lFact(e+1)) = cast(lFact e · factor)
  change ((((lFact F (e + 1) : F[X]) : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F) =
      ((((lFact F e : F[X]) : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F) *
        ((((X - X ^ ((Nat.card F) ^ (e + 1)) : F[X]) : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F)
  rw [h]
  exact coe_K_poly_mul F (lFact F e) (X - X ^ ((Nat.card F) ^ (e + 1)) : F[X])

/-- the ratio `w_e := u_e/u_{e+1}` equals the factor `X − X^{q^{e+1}}`. -/
lemma uEval_ratio (e : ℕ) (hEvalE : EvalU F e) (hEvalE1 : EvalU F (e + 1)) :
    uEval F e * (uEval F (e + 1))⁻¹ = facK F (e + 1) := by
  classical
  have hE : uEval F e = (lK F e)⁻¹ := eq_inv_of_mul_eq_one_left (uEval_mul_lK F e hEvalE)
  have hE1 : uEval F (e + 1) = (lK F (e + 1))⁻¹ := eq_inv_of_mul_eq_one_left (uEval_mul_lK F (e + 1) hEvalE1)
  have hsucc : lK F (e + 1) = lK F e * facK F (e + 1) := lK_succ F e
  have hℓ0 : lK F e ≠ 0 := lK_ne_zero F e hEvalE
  calc
    uEval F e * (uEval F (e + 1))⁻¹ = (lK F e)⁻¹ * ((lK F (e + 1))⁻¹)⁻¹ := by rw [hE, hE1]
    _ = (lK F e)⁻¹ * (lK F e * facK F (e + 1)) := by
          rw [hsucc]
          simp
    _ = facK F (e + 1) := by
          rw [← mul_assoc, inv_mul_cancel₀ hℓ0, one_mul]



/-- `(X−X^{q^{d+1}}) + carlitzOne = (X−X^{q^d})^q` in `F[X]` (freshman's dream). -/
lemma carlitz_freshman (d : ℕ) :
    (X - X ^ ((Nat.card F) ^ (d + 1)) : F[X]) + carlitzOne F =
      (X - X ^ ((Nat.card F) ^ d) : F[X]) ^ (Nat.card F) := by
  classical
  have h1 := X_sub_X_pow_card_iter F d
  calc
    (X - X ^ ((Nat.card F) ^ (d + 1)) : F[X]) + carlitzOne F
        = (X - X ^ ((Nat.card F) ^ (d + 1)) : F[X]) + (X ^ (Nat.card F) - X) := by
          dsimp [carlitzOne]
    _ = X ^ (Nat.card F) - X ^ ((Nat.card F) ^ (d + 1)) := by ring
    _ = (X - X ^ ((Nat.card F) ^ d) : F[X]) ^ (Nat.card F) := h1.symm

/-- the factor/carlitz freshman identity in the completion:
`facK(d+1) + D1 = (facK d)^q`. -/
lemma facK_freshman (d : ℕ) :
    facK F (d + 1) + D1c F = (facK F d) ^ (Nat.card F) := by
  classical
  have hP := carlitz_freshman F d
  have hc := congrArg (fun p : F[X] => ((((p : F[X]) : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F)) hP
  -- hc : cast((X−X^{q^{d+1}}) + carlitzOne) = cast((X−X^{q^d})^q)
  -- LHS of the goal: facK(d+1) + D1c = cast((X−X^{q^{d+1}})) + cast(carlitzOne)
  -- RHS: (facK d)^q = (cast(X−X^{q^d}))^q
  dsimp [facK, D1c, carlitzOne] at hc ⊢
  -- convert casts to algebraMap and use ring-hom lemmas
  simp [map_add, map_sub, map_pow, rat_cast_eq_algebraMap, poly_cast_eq_algebraMap] at hc
  simpa [map_add, map_sub, map_pow, rat_cast_eq_algebraMap, poly_cast_eq_algebraMap] using hc


/-- ★ `ID2(d)` for every `d ≥ 1`, given the power-sum evaluation `EvalU e` for all `e`. -/
theorem ID2_of_EvalU (hEval : ∀ e : ℕ, EvalU F e) (d : ℕ) (hd : 1 ≤ d) : ID2 F d := by
  classical
  have hqpow (e : ℕ) : P F e (qExp F) = (uEval F e) ^ (Nat.card F) := by
    dsimp [uEval]
    exact P_d_q_eq_pow_one F e
  unfold ID2
  rw [hqpow d, hqpow (d - 1)]
  change uEval F d ^ (Nat.card F) * (uEval F d + D1c F * uEval F (d + 1)) =
      uEval F (d + 1) * uEval F (d - 1) ^ (Nat.card F)
  have hu (e : ℕ) : uEval F e ≠ 0 := uEval_ne_zero F e (hEval e)
  have hW (e : ℕ) : uEval F e * (uEval F (e + 1))⁻¹ = facK F (e + 1) :=
    uEval_ratio F e (hEval e) (hEval (e + 1))
  have hFr := facK_freshman F d
  have hd' : d - 1 + 1 = d := by omega
  have hR : uEval F d * (uEval F (d + 1))⁻¹ + D1c F =
      (uEval F (d - 1) * (uEval F d)⁻¹) ^ (Nat.card F) := by
    have h2 : uEval F (d - 1) * (uEval F d)⁻¹ = facK F d := by
      have hw := hW (d - 1)
      rw [hd'] at hw
      exact hw
    calc
      uEval F d * (uEval F (d + 1))⁻¹ + D1c F = facK F (d + 1) + D1c F := by rw [hW d]
      _ = (facK F d) ^ (Nat.card F) := hFr
      _ = (uEval F (d - 1) * (uEval F d)⁻¹) ^ (Nat.card F) := by rw [h2]
  let c : RatFunc.CompletionAtInfty F := uEval F d ^ (Nat.card F) * uEval F (d + 1)
  have hL : uEval F d ^ (Nat.card F) * (uEval F d + D1c F * uEval F (d + 1)) =
      c * (uEval F d * (uEval F (d + 1))⁻¹ + D1c F) := by
    dsimp [c]
    field_simp [hu d, hu (d + 1)]
  have h1 : uEval F d ^ (Nat.card F) *
        ((uEval F (d - 1) * (uEval F d)⁻¹) ^ (Nat.card F)) =
      uEval F (d - 1) ^ (Nat.card F) := by
    calc
      uEval F d ^ (Nat.card F) * ((uEval F (d - 1) * (uEval F d)⁻¹) ^ (Nat.card F))
          = uEval F d ^ (Nat.card F) * (uEval F (d - 1) ^ (Nat.card F) * (uEval F d)⁻¹ ^ (Nat.card F)) := by
            rw [mul_pow]
      _ = uEval F (d - 1) ^ (Nat.card F) * (uEval F d ^ (Nat.card F) * (uEval F d)⁻¹ ^ (Nat.card F)) := by ring
      _ = uEval F (d - 1) ^ (Nat.card F) * (uEval F d ^ (Nat.card F) * (uEval F d ^ (Nat.card F))⁻¹) := by
            rw [inv_pow]
      _ = uEval F (d - 1) ^ (Nat.card F) := by
            have hz : uEval F d ^ (Nat.card F) ≠ 0 := pow_ne_zero (Nat.card F) (hu d)
            field_simp [hz]
  have hR2 : uEval F (d + 1) * uEval F (d - 1) ^ (Nat.card F) =
      c * (uEval F (d - 1) * (uEval F d)⁻¹) ^ (Nat.card F) := by
    calc
      uEval F (d + 1) * uEval F (d - 1) ^ (Nat.card F)
          = uEval F (d - 1) ^ (Nat.card F) * uEval F (d + 1) := by ring
      _ = uEval F d ^ (Nat.card F) * ((uEval F (d - 1) * (uEval F d)⁻¹) ^ (Nat.card F)) * uEval F (d + 1) := by
            rw [← h1]
      _ = c * ((uEval F (d - 1) * (uEval F d)⁻¹) ^ (Nat.card F)) := by
            dsimp [c]
            ring

  calc
    uEval F d ^ (Nat.card F) * (uEval F d + D1c F * uEval F (d + 1))
        = c * (uEval F d * (uEval F (d + 1))⁻¹ + D1c F) := hL
    _ = c * (uEval F (d - 1) * (uEval F d)⁻¹) ^ (Nat.card F) := by rw [hR]
    _ = uEval F (d + 1) * uEval F (d - 1) ^ (Nat.card F) := hR2.symm


/-- ★ `R1Prop(d)` for every `d`, given `EvalU e` for all `e` (paper (2.8) resolved). -/
theorem R1Prop_of_EvalU (hEval : ∀ e : ℕ, EvalU F e) : ∀ d : ℕ, R1Prop F d := by
  intro d
  exact R1_all F (fun n hn => ID2_of_EvalU F hEval n hn) d

/-- Exponent-one power-sum nonvanishing at every level, given `EvalU e` for all `e`. -/
theorem P_oneExp_ne_zero_of_EvalU (hEval : ∀ e : ℕ, EvalU F e) :
    ∀ d : ℕ, P F d oneExp ≠ 0 := by
  intro d
  exact P_oneExp_ne_zero_all F (fun n hn => ID2_of_EvalU F hEval n hn) d

end ZagierHoffmanPositiveChar
