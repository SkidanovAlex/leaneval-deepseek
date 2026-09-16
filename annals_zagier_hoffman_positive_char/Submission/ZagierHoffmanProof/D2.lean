import Submission.ZagierHoffmanProof.D1
import Submission.ZagierHoffmanProof.StepA
import Submission.ZagierHoffmanProof.Linear

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Polynomial RatFunc
open scoped BigOperators

/-!
# The level-one shuffle identity in the completion (`d1`)

From the polynomial identity `thakurP1` (`(P1)`, `D1.lean`) we derive, in the
completion `RatFunc.CompletionAtInfty F` of `F(t)` at infinity, the depth-one
product identity at level `d = 1`:

    P F 1 a * P F 1 b  =  P F 1 (a+b)  +  Σ_{0<i<a+b} Δ^i_{a,b} · P F 1 (a+b-i)

This is paper (2.1) specialised to `d = 1`, where the depth-two `S`-term collapses
to `P F 1` (`S_two_d1_eq_P_head`, `Linear.lean`).

The bridge is the rational-function avatar `P1rat F n = Σ_c (X+c)^{-n} ∈ RatFunc F`
of `P F 1 n`:  `P F 1 n = coe(P1rat F n)`, and `A F n ↦ [1]^n · P1rat F n`.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- `R_n := Σ_c (X + c)^{-n}` in `RatFunc F`, the rational-function avatar of `P F 1 n`. -/
noncomputable def P1rat (n : ℕ) : RatFunc F := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  exact ∑ c : F, ((((Polynomial.X + Polynomial.C c : F[X]) : RatFunc F) ^ n)⁻¹)

/-- Push the finite sum over `F` through the completion embedding. -/
lemma coe_sum_F (f : F → RatFunc F) :
    letI : Fintype F := Fintype.ofFinite F
    (((∑ c : F, f c : RatFunc F) : RatFunc.CompletionAtInfty F)) =
      ∑ c : F, ((f c : RatFunc F) : RatFunc.CompletionAtInfty F) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  exact map_sum (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)) f (Finset.univ : Finset F)

/-- Definitional expansion of `P1rat`. -/
lemma P1rat_unfold (n : ℕ) :
    letI : Fintype F := Fintype.ofFinite F
    P1rat F n = ∑ c : F, ((((Polynomial.X + Polynomial.C c : F[X]) : RatFunc F) ^ n)⁻¹) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  rfl

/-- `P F 1 n` equals the completion image of `P1rat F n`. -/
lemma P_one_eq_coe_P1rat (n : ℕ+) :
    P F 1 n = (P1rat F (n : ℕ) : RatFunc.CompletionAtInfty F) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  let C := RatFunc.CompletionAtInfty F
  calc
    P F 1 n
        = (∑ c : F, (((((Polynomial.X + Polynomial.C c : F[X]) : RatFunc F) : C) ^ (n : ℕ))⁻¹)) := by
          rw [P_one_eq_sum_translate F n]
    _ = (((∑ c : F, ((((Polynomial.X + Polynomial.C c : F[X]) : RatFunc F) ^ (n : ℕ))⁻¹) : RatFunc F) : C)) := by
          rw [coe_sum_F F (fun c : F => ((((Polynomial.X + Polynomial.C c : F[X]) : RatFunc F) ^ (n : ℕ))⁻¹))]
          apply Finset.sum_congr rfl
          intro c hc
          let x : RatFunc F := ((Polynomial.X + Polynomial.C c : F[X]) : RatFunc F)
          change (((x : C) ^ (n : ℕ))⁻¹) = ((↑((x ^ (n : ℕ))⁻¹) : C))
          exact (congrArg (fun y : C => y⁻¹) (map_pow (algebraMap (RatFunc F) C) x (n : ℕ))).symm.trans
            (map_inv₀ (algebraMap (RatFunc F) C) (x ^ (n : ℕ))).symm
    _ = (P1rat F (n : ℕ) : C) := by rfl

/-- `[1]^n · (X + c)^{-n} = Q_c^n` in `RatFunc F`. -/
lemma carlitz_mul_inv (n : ℕ) (c : F) :
    ((carlitzOne F : F[X]) : RatFunc F) ^ n *
        ((((Polynomial.X + Polynomial.C c : F[X]) : RatFunc F) ^ n)⁻¹) =
      ((qPoly F c : F[X]) : RatFunc F) ^ n := by
  let a : RatFunc F := ((Polynomial.X + Polynomial.C c : F[X]) : RatFunc F)
  let b : RatFunc F := ((qPoly F c : F[X]) : RatFunc F)
  let g : RatFunc F := ((carlitzOne F : F[X]) : RatFunc F)
  have hg : g = a * b := by
    dsimp [a, b, g]
    rw [carlitzOne_eq_mul_qPoly F c]
    rw [map_mul]
  have ha : a ≠ 0 := by
    dsimp [a]
    have hmon : (Polynomial.X + Polynomial.C c : F[X]).Monic := Polynomial.monic_X_add_C c
    intro hz
    have : (Polynomial.X + Polynomial.C c : F[X]) = 0 := RatFunc.algebraMap_injective F (by simpa using hz)
    exact hmon.ne_zero this
  calc
    g ^ n * (a ^ n)⁻¹ = (a * b) ^ n * (a ^ n)⁻¹ := by rw [hg]
    _ = (a ^ n * b ^ n) * (a ^ n)⁻¹ := by rw [mul_pow]
    _ = b ^ n * (a ^ n * (a ^ n)⁻¹) := by ring
    _ = b ^ n * 1 := by rw [mul_inv_cancel₀ (pow_ne_zero n ha)]
    _ = b ^ n := by rw [mul_one]

/-- `A F n`, viewed in `RatFunc F`, is `[1]^n · P1rat F n`. -/
lemma A_RatFunc_eq (n : ℕ) :
    algebraMap F[X] (RatFunc F) (A F n) =
      (algebraMap F[X] (RatFunc F) (carlitzOne F)) ^ n * P1rat F n := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  calc
    algebraMap F[X] (RatFunc F) (A F n)
        = algebraMap F[X] (RatFunc F) (∑ c : F, (qPoly F c) ^ n) := by
          rfl
    _ = ∑ c : F, algebraMap F[X] (RatFunc F) ((qPoly F c) ^ n) := by
          exact map_sum (algebraMap F[X] (RatFunc F)) (fun c : F => (qPoly F c)^n) (Finset.univ : Finset F)
    _ = ∑ c : F, (algebraMap F[X] (RatFunc F) (qPoly F c)) ^ n := by
          apply Finset.sum_congr rfl
          intro c hc
          exact map_pow (algebraMap F[X] (RatFunc F)) (qPoly F c) n
    _ = (algebraMap F[X] (RatFunc F) (carlitzOne F)) ^ n * P1rat F n := by
          rw [P1rat_unfold F n]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro c hc
          exact (carlitz_mul_inv F n c).symm

/-- Scalar constants: the composite `F → F[X] → RatFunc F`. -/
lemma map_C_rat (k : F) :
    algebraMap F[X] (RatFunc F) (Polynomial.C k) = RatFunc.C k := by
  exact RatFunc.algebraMap_C k

/-- `RatFunc.C` is the image of `F` in `RatFunc F` (constants). -/
lemma C_eq_algebraMap (k : F) : RatFunc.C k = algebraMap F (RatFunc F) k := by
  rw [RatFunc.algebraMap_eq_C]

/-- Level-one shuffle identity over the rational functions (variable `X`):
`R_a · R_b = R_{a+b} + Σ Δ^i · R_{a+b-i}` in `RatFunc F`. -/
lemma P1rat_mul (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    P1rat F a * P1rat F b =
      P1rat F (a + b) +
        ∑ i ∈ Finset.Icc 1 (a + b - 1),
          RatFunc.C (ChenDeltaZ F a b i : F) * P1rat F (a + b - i) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  let s : Finset ℕ := Finset.Icc 1 (a + b - 1)
  let q : RatFunc F := algebraMap F[X] (RatFunc F) (carlitzOne F)
  have hq : q ≠ 0 := by
    dsimp [q]
    intro hz
    have hc : carlitzOne F = 0 := RatFunc.algebraMap_injective F (by simpa using hz)
    exact (carlitzOne_monic F).ne_zero hc
  have hP1 := thakurP1 F a b ha hb
  have hmap : algebraMap F[X] (RatFunc F) (A F a * A F b) =
      algebraMap F[X] (RatFunc F) (A F (a + b) +
        ∑ i ∈ s, Polynomial.C (ChenDeltaZ F a b i : F) * (carlitzOne F) ^ i * A F (a + b - i)) := by
    exact congrArg (algebraMap F[X] (RatFunc F)) hP1
  -- LHS in `q`-form
  have hL : algebraMap F[X] (RatFunc F) (A F a * A F b) =
      q ^ (a + b) * (P1rat F a * P1rat F b) := by
    dsimp [q]
    rw [map_mul, A_RatFunc_eq F a, A_RatFunc_eq F b]
    calc
      (algebraMap F[X] (RatFunc F) (carlitzOne F)) ^ a * P1rat F a *
          ((algebraMap F[X] (RatFunc F) (carlitzOne F)) ^ b * P1rat F b)
          = ((algebraMap F[X] (RatFunc F) (carlitzOne F)) ^ a *
              (algebraMap F[X] (RatFunc F) (carlitzOne F)) ^ b) *
              (P1rat F a * P1rat F b) := by ring
      _ = (algebraMap F[X] (RatFunc F) (carlitzOne F)) ^ (a + b) *
              (P1rat F a * P1rat F b) := by
            rw [← pow_add]
  -- summand mapping
  have hsum : (∑ i ∈ s, algebraMap F[X] (RatFunc F)
        (Polynomial.C (ChenDeltaZ F a b i : F) * (carlitzOne F) ^ i * A F (a + b - i))) =
      ∑ i ∈ s, RatFunc.C (ChenDeltaZ F a b i : F) * q ^ i * (q ^ (a + b - i) * P1rat F (a + b - i)) := by
    dsimp [q]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_mul, map_mul, map_pow, A_RatFunc_eq F (a + b - i), map_C_rat]
  -- mapped RHS equals the `q`-factored identity
  have hR : algebraMap F[X] (RatFunc F) (A F (a + b) +
        ∑ i ∈ s, Polynomial.C (ChenDeltaZ F a b i : F) * (carlitzOne F) ^ i * A F (a + b - i)) =
      q ^ (a + b) * (P1rat F (a + b) +
        ∑ i ∈ s, RatFunc.C (ChenDeltaZ F a b i : F) * P1rat F (a + b - i)) := by
    calc
      algebraMap F[X] (RatFunc F) (A F (a + b) +
          ∑ i ∈ s, Polynomial.C (ChenDeltaZ F a b i : F) * (carlitzOne F) ^ i * A F (a + b - i))
          = q ^ (a + b) * P1rat F (a + b) +
              ∑ i ∈ s, RatFunc.C (ChenDeltaZ F a b i : F) * q ^ i *
                (q ^ (a + b - i) * P1rat F (a + b - i)) := by
            rw [map_add]
            rw [A_RatFunc_eq F (a + b)]
            rw [map_sum (algebraMap F[X] (RatFunc F))
                (fun i : ℕ => Polynomial.C (ChenDeltaZ F a b i : F) * (carlitzOne F) ^ i * A F (a + b - i)) s]
            rw [hsum]
      _ = q ^ (a + b) * P1rat F (a + b) +
              ∑ i ∈ s, q ^ (a + b) * (RatFunc.C (ChenDeltaZ F a b i : F) * P1rat F (a + b - i)) := by
            apply congrArg (fun t : RatFunc F => q ^ (a + b) * P1rat F (a + b) + t)
            apply Finset.sum_congr rfl
            intro i hi
            calc
              RatFunc.C (ChenDeltaZ F a b i : F) * q ^ i * (q ^ (a + b - i) * P1rat F (a + b - i))
                  = (q ^ i * q ^ (a + b - i)) * (RatFunc.C (ChenDeltaZ F a b i : F) * P1rat F (a + b - i)) := by ring
              _ = q ^ (a + b) * (RatFunc.C (ChenDeltaZ F a b i : F) * P1rat F (a + b - i)) := by
                    have hle : i ≤ a + b := by
                      have hin : i ≤ a + b - 1 := (Finset.mem_Icc.mp hi).2
                      omega
                    rw [← pow_add]
                    rw [Nat.add_sub_of_le hle]
      _ = q ^ (a + b) * (P1rat F (a + b) +
              ∑ i ∈ s, RatFunc.C (ChenDeltaZ F a b i : F) * P1rat F (a + b - i)) := by
            rw [← Finset.mul_sum]
            ring
  -- combine and cancel the nonzero factor `q^(a+b)`
  have hboth : q ^ (a + b) * (P1rat F a * P1rat F b) =
      q ^ (a + b) * (P1rat F (a + b) +
        ∑ i ∈ s, RatFunc.C (ChenDeltaZ F a b i : F) * P1rat F (a + b - i)) := by
    rw [← hL, hmap, hR]
  have hcancel := mul_left_cancel₀ (pow_ne_zero (a + b) hq) hboth
  simpa [s] using hcancel

/-- For `i ∈ [1, a+b-1]` the exponent `a+b-i` is positive. -/
lemma P1sub_pos (a b : ℕ+) (i : ℕ) (hi : i ∈ Finset.Icc 1 ((a : ℕ) + (b : ℕ) - 1)) :
    0 < (a : ℕ) + (b : ℕ) - i := by
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hin : i ≤ (a : ℕ) + (b : ℕ) - 1 := (Finset.mem_Icc.mp hi).2
  have h1 : 1 ≤ (a : ℕ) := PNat.pos a
  have h2 : 1 ≤ (b : ℕ) := PNat.pos b
  omega

/-- Casting an integer through `F` and into the completion agrees with the direct
integer cast into the completion. -/
lemma intCast_completion (z : ℤ) :
    ((RatFunc.C (z : F) : RatFunc F) : RatFunc.CompletionAtInfty F) =
      (z : RatFunc.CompletionAtInfty F) := by
  let f : F →+* RatFunc.CompletionAtInfty F :=
    (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)).comp RatFunc.C
  change f (z : F) = (z : RatFunc.CompletionAtInfty F)
  exact map_intCast f z

/-- The completion embedding commutes with finite sums over a finite type. -/
lemma coe_sum_fintype (ι : Type*) [Fintype ι] (f : ι → RatFunc F) :
    (((∑ i : ι, f i : RatFunc F) : RatFunc.CompletionAtInfty F)) =
      ∑ i : ι, ((f i : RatFunc F) : RatFunc.CompletionAtInfty F) := by
  classical
  exact map_sum (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)) f (Finset.univ : Finset ι)

lemma P_one_mul_d1 (a b : ℕ+) :
    P F 1 a * P F 1 b =
      P F 1 ⟨(a : ℕ) + (b : ℕ), Nat.add_pos_left (PNat.pos a) (b : ℕ)⟩ +
      ∑ i : {i : ℕ // i ∈ Finset.Icc 1 ((a : ℕ) + (b : ℕ) - 1)},
        (ChenDeltaZ F (a : ℕ) (b : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
        P F 1 ⟨(a : ℕ) + (b : ℕ) - i.1, P1sub_pos a b i.1 i.2⟩ := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  let A : ℕ := (a : ℕ)
  let B : ℕ := (b : ℕ)
  have hP := P1rat_mul F A B (by dsimp [A]; exact PNat.pos a) (by dsimp [B]; exact PNat.pos b)
  -- convert the membership sum in `hP` into a subtype sum
  have hPsub : P1rat F A * P1rat F B =
      P1rat F (A + B) +
        ∑ i : {i : ℕ // i ∈ Finset.Icc 1 (A + B - 1)},
          RatFunc.C (ChenDeltaZ F A B i.1 : F) * P1rat F (A + B - i.1) := by
    rw [hP]
    congr 1
    rw [Finset.sum_subtype (Finset.Icc 1 (A + B - 1)) (fun x : ℕ => Iff.rfl)
      (fun i : ℕ => RatFunc.C (ChenDeltaZ F A B i : F) * P1rat F (A + B - i))]
  -- move `hPsub` into the completion
  have hC : ((P1rat F A * P1rat F B : RatFunc F) : RatFunc.CompletionAtInfty F) =
      (P1rat F (A + B) : RatFunc.CompletionAtInfty F) +
        ∑ i : {i : ℕ // i ∈ Finset.Icc 1 (A + B - 1)},
          ((RatFunc.C (ChenDeltaZ F A B i.1 : F) : RatFunc F) : RatFunc.CompletionAtInfty F) *
          ((P1rat F (A + B - i.1) : RatFunc F) : RatFunc.CompletionAtInfty F) := by
    calc
      ((P1rat F A * P1rat F B : RatFunc F) : RatFunc.CompletionAtInfty F)
          = ((P1rat F (A + B) +
              ∑ i : {i : ℕ // i ∈ Finset.Icc 1 (A + B - 1)},
                RatFunc.C (ChenDeltaZ F A B i.1 : F) * P1rat F (A + B - i.1) : RatFunc F) : RatFunc.CompletionAtInfty F) := by
            exact congrArg (fun x : RatFunc F => (x : RatFunc.CompletionAtInfty F)) hPsub
      _ = (P1rat F (A + B) : RatFunc.CompletionAtInfty F) +
          ((∑ i : {i : ℕ // i ∈ Finset.Icc 1 (A + B - 1)},
              RatFunc.C (ChenDeltaZ F A B i.1 : F) * P1rat F (A + B - i.1) : RatFunc F) : RatFunc.CompletionAtInfty F) := by
            exact map_add (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)) (P1rat F (A + B))
              (∑ i : {i : ℕ // i ∈ Finset.Icc 1 (A + B - 1)},
                RatFunc.C (ChenDeltaZ F A B i.1 : F) * P1rat F (A + B - i.1))
      _ = (P1rat F (A + B) : RatFunc.CompletionAtInfty F) +
          ∑ i : {i : ℕ // i ∈ Finset.Icc 1 (A + B - 1)},
            (((RatFunc.C (ChenDeltaZ F A B i.1 : F) * P1rat F (A + B - i.1) : RatFunc F)) : RatFunc.CompletionAtInfty F) := by
            apply congrArg (fun t : RatFunc.CompletionAtInfty F => (P1rat F (A + B) : RatFunc.CompletionAtInfty F) + t)
            exact map_sum (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F))
              (fun i : {i : ℕ // i ∈ Finset.Icc 1 (A + B - 1)} =>
                (RatFunc.C (ChenDeltaZ F A B i.1 : F) * P1rat F (A + B - i.1) : RatFunc F))
              (Finset.univ : Finset {i : ℕ // i ∈ Finset.Icc 1 (A + B - 1)})
      _ = (P1rat F (A + B) : RatFunc.CompletionAtInfty F) +
          ∑ i : {i : ℕ // i ∈ Finset.Icc 1 (A + B - 1)},
            ((RatFunc.C (ChenDeltaZ F A B i.1 : F) : RatFunc F) : RatFunc.CompletionAtInfty F) *
            ((P1rat F (A + B - i.1) : RatFunc F) : RatFunc.CompletionAtInfty F) := by
            apply congrArg (fun t : RatFunc.CompletionAtInfty F => (P1rat F (A + B) : RatFunc.CompletionAtInfty F) + t)
            apply Finset.sum_congr rfl
            intro i hi
            exact map_mul (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F))
              (RatFunc.C (ChenDeltaZ F A B i.1 : F)) (P1rat F (A + B - i.1))
  -- target
  calc
    P F 1 a * P F 1 b
        = (P1rat F A : RatFunc.CompletionAtInfty F) * (P1rat F B : RatFunc.CompletionAtInfty F) := by
          rw [P_one_eq_coe_P1rat F a, P_one_eq_coe_P1rat F b]
    _ = ((P1rat F A * P1rat F B : RatFunc F) : RatFunc.CompletionAtInfty F) := by
          exact (map_mul (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)) (P1rat F A) (P1rat F B)).symm
    _ = (P1rat F (A + B) : RatFunc.CompletionAtInfty F) +
          ∑ i : {i : ℕ // i ∈ Finset.Icc 1 (A + B - 1)},
            ((RatFunc.C (ChenDeltaZ F A B i.1 : F) : RatFunc F) : RatFunc.CompletionAtInfty F) *
            ((P1rat F (A + B - i.1) : RatFunc F) : RatFunc.CompletionAtInfty F) := hC
    _ = P F 1 ⟨(a : ℕ) + (b : ℕ), Nat.add_pos_left (PNat.pos a) (b : ℕ)⟩ +
          ∑ i : {i : ℕ // i ∈ Finset.Icc 1 ((a : ℕ) + (b : ℕ) - 1)},
            (ChenDeltaZ F (a : ℕ) (b : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
            P F 1 ⟨(a : ℕ) + (b : ℕ) - i.1, P1sub_pos a b i.1 i.2⟩ := by
          rw [show ((P1rat F (A + B) : RatFunc F) : RatFunc.CompletionAtInfty F) =
              P F 1 ⟨(a : ℕ) + (b : ℕ), Nat.add_pos_left (PNat.pos a) (b : ℕ)⟩ by
            exact (P_one_eq_coe_P1rat F ⟨(a : ℕ) + (b : ℕ), Nat.add_pos_left (PNat.pos a) (b : ℕ)⟩).symm]
          apply congrArg (fun t : RatFunc.CompletionAtInfty F => P F 1 ⟨(a : ℕ) + (b : ℕ), Nat.add_pos_left (PNat.pos a) (b : ℕ)⟩ + t)
          apply Finset.sum_congr rfl
          intro i hi
          rw [show ((RatFunc.C (ChenDeltaZ F A B i.1 : F) : RatFunc F) : RatFunc.CompletionAtInfty F) =
              (ChenDeltaZ F A B i.1 : RatFunc.CompletionAtInfty F) by
            exact intCast_completion F (ChenDeltaZ F A B i.1)]
          rw [show ((P1rat F (A + B - i.1) : RatFunc F) : RatFunc.CompletionAtInfty F) =
              P F 1 ⟨(a : ℕ) + (b : ℕ) - i.1, P1sub_pos a b i.1 i.2⟩ by
            exact (P_one_eq_coe_P1rat F ⟨(a : ℕ) + (b : ℕ) - i.1, P1sub_pos a b i.1 i.2⟩).symm]


/-- The `d = 1` case of `thakur_prod_one` (paper (2.1)): at level one the depth-two
`S`-term collapses to `P F 1` (`S_two_d1_eq_P_head`). -/
lemma thakur_prod_one_d1 (a b : ℕ+) :
    P F 1 a * P F 1 b =
      P F 1 ⟨(a : ℕ) + (b : ℕ), Nat.add_pos_left (PNat.pos a) (b : ℕ)⟩ +
      ∑ i : {i : ℕ // i ∈ Finset.Icc 1 ((a : ℕ) + (b : ℕ) - 1)},
        (ChenDeltaZ F (a : ℕ) (b : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
        S F 2 (by omega)
          (fun j : Fin 2 => if (j : ℕ) = 0
            then ⟨(a : ℕ) + (b : ℕ) - i.1, by
              have hi1 : 1 ≤ i.1 := (Finset.mem_Icc.mp i.2).1
              have hin : i.1 ≤ (a : ℕ) + (b : ℕ) - 1 := (Finset.mem_Icc.mp i.2).2
              omega⟩
            else ⟨i.1, by
              have hi1 : 1 ≤ i.1 := (Finset.mem_Icc.mp i.2).1
              omega⟩) 1 := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have h := P_one_mul_d1 F a b
  rw [h]
  apply congrArg (fun t : RatFunc.CompletionAtInfty F =>
    P F 1 ⟨(a : ℕ) + (b : ℕ), Nat.add_pos_left (PNat.pos a) (b : ℕ)⟩ + t)
  apply Finset.sum_congr rfl
  intro i hi
  have hS : S F 2 (by omega)
      (fun j : Fin 2 => if (j : ℕ) = 0
        then ⟨(a : ℕ) + (b : ℕ) - i.1, by
          have hi1 : 1 ≤ i.1 := (Finset.mem_Icc.mp i.2).1
          have hin : i.1 ≤ (a : ℕ) + (b : ℕ) - 1 := (Finset.mem_Icc.mp i.2).2
          omega⟩
        else ⟨i.1, by
          have hi1 : 1 ≤ i.1 := (Finset.mem_Icc.mp i.2).1
          omega⟩) 1 =
      P F 1 ⟨(a : ℕ) + (b : ℕ) - i.1, P1sub_pos a b i.1 i.2⟩ := by
    rw [S_two_d1_eq_P_head F
      (fun j : Fin 2 => if (j : ℕ) = 0
        then ⟨(a : ℕ) + (b : ℕ) - i.1, by
          have hi1 : 1 ≤ i.1 := (Finset.mem_Icc.mp i.2).1
          have hin : i.1 ≤ (a : ℕ) + (b : ℕ) - 1 := (Finset.mem_Icc.mp i.2).2
          omega⟩
        else ⟨i.1, by
          have hi1 : 1 ≤ i.1 := (Finset.mem_Icc.mp i.2).1
          omega⟩) (by omega)]
    congr 1
  rw [← hS]

end ZagierHoffmanPositiveChar
