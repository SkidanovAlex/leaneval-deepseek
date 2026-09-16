import Submission.ZagierHoffmanProof.StepB2
import Submission.ZagierHoffmanProof.D2

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Polynomial RatFunc
open scoped BigOperators

/-!
# Step B3 (completion side): `S_<d` at depth one, and `thakur_prod_one`

`StepB2.lean` established the level-`d` shuffle in `RatFunc F` (`headProdSum`).
This module embeds it into the completion, identifies the head/monic power sums with
`P F d` and `S_lt F 1`, and applies `S_d_recursion` to obtain the depth-two form
`thakur_prod_one` (paper (2.1)) for every `d ≥ 1`.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Level-`d` power sum over heads, in `RatFunc F`. -/
noncomputable def Hsum (d : ℕ) (n : ℕ) : RatFunc F :=
  ∑ p : HeadD F d, (((p.1 : RatFunc F) ^ n)⁻¹)

/-- Sum over monic degree-`< d`, in `RatFunc F`. -/
noncomputable def Msum (d : ℕ) (n : ℕ) : RatFunc F :=
  ∑ m : MonicLt F d, (((m.1 : RatFunc F) ^ n)⁻¹)

/-- Length-one monic tuples with degree `< d` are just monic polynomials of degree `< d`. -/
noncomputable def monicTuple1Equiv (d : ℕ) (hr : 0 < 1) :
    MonicLt F d ≃ TailLT F 1 hr d where
  toFun m := by
    refine ⟨⟨fun _ : Fin 1 => m.1, ?_, ?_⟩, ?_⟩
    · intro i j hij
      exfalso
      have hi : (i : ℕ) < 1 := i.2
      have hj : (j : ℕ) < 1 := j.2
      have hij' : (i : ℕ) < (j : ℕ) := hij
      omega
    · intro i
      exact m.2.1
    · change (m.1).natDegree < d
      exact m.2.2
  invFun b := ⟨(b.1.1 ⟨0, hr⟩), by
      change (b.1.1 ⟨0, hr⟩).Monic ∧ (b.1.1 ⟨0, hr⟩).natDegree < d
      exact ⟨b.1.2.2 ⟨0, hr⟩, by simpa [blockSetLT] using b.2⟩⟩
  left_inv := by
    intro m
    apply Subtype.ext
    rfl
  right_inv := by
    intro b
    apply Subtype.ext
    apply Subtype.ext
    funext i
    fin_cases i
    rfl

/-- The completion embedding commutes with the power-sum summands over heads. -/
lemma coe_head_pow_inv (d : ℕ) (n : ℕ) :
    ((∑ p : HeadD F d, (((p.1 : RatFunc F) ^ n)⁻¹) : RatFunc F) :
        RatFunc.CompletionAtInfty F) =
      ∑ p : HeadD F d, ((((p.1 : RatFunc F) : RatFunc.CompletionAtInfty F) ^ n)⁻¹) := by
  classical
  change ((algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F))
    (∑ p : HeadD F d, (((p.1 : RatFunc F) ^ n)⁻¹))) =
      ∑ p : HeadD F d, ((((p.1 : RatFunc F) : RatFunc.CompletionAtInfty F) ^ n)⁻¹)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hm := map_inv₀ (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)) ((p.1 : RatFunc F) ^ n)
  have hpow := map_pow (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)) (p.1 : RatFunc F) n
  rw [hpow] at hm
  change (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)) (((p.1 : RatFunc F) ^ n)⁻¹) =
      (((p.1 : RatFunc F) : RatFunc.CompletionAtInfty F) ^ n)⁻¹
  exact hm

lemma P_eq_coe_Hsum (d : ℕ) (n : ℕ+) :
    P F d n = ((Hsum F d (n : ℕ) : RatFunc F) : RatFunc.CompletionAtInfty F) := by
  classical
  dsimp [Hsum]
  rw [P_eq_sum F d n]
  exact (coe_head_pow_inv F d (n : ℕ)).symm

lemma coe_Msum (d : ℕ) (n : ℕ) :
    ((Msum F d n : RatFunc F) : RatFunc.CompletionAtInfty F) =
      ∑ m : MonicLt F d, ((((m.1 : RatFunc F) : RatFunc.CompletionAtInfty F) ^ n)⁻¹) := by
  classical
  dsimp [Msum]
  change ((algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F))
      (∑ m : MonicLt F d, (((m.1 : RatFunc F) ^ n)⁻¹))) =
      ∑ m : MonicLt F d, ((((m.1 : RatFunc F) : RatFunc.CompletionAtInfty F) ^ n)⁻¹)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hm' := map_inv₀ (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)) ((m.1 : RatFunc F) ^ n)
  have hpow := map_pow (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)) (m.1 : RatFunc F) n
  rw [hpow] at hm'
  change (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)) (((m.1 : RatFunc F) ^ n)⁻¹) =
      (((m.1 : RatFunc F) : RatFunc.CompletionAtInfty F) ^ n)⁻¹
  exact hm'

/-- At depth one, `S_<d(s)` is the completion-embedded power sum over monic degree-`< d`. -/
lemma S_lt_one_eq_coe_Msum (d : ℕ) (hr : 0 < 1) (𝔰 : Fin 1 → ℕ+) :
    S_lt F 1 hr 𝔰 d = ((Msum F d (𝔰 ⟨0, hr⟩ : ℕ) : RatFunc F) :
        RatFunc.CompletionAtInfty F) := by
  classical
  let e : MonicLt F d ≃ TailLT F 1 hr d := monicTuple1Equiv F d hr
  letI : Fintype (TailLT F 1 hr d) := Fintype.ofEquiv (MonicLt F d) e
  calc
    S_lt F 1 hr 𝔰 d
        = ∑' b : TailLT F 1 hr d, zetaTerm F 𝔰 b.1 := by rfl
    _ = ∑ b : TailLT F 1 hr d, zetaTerm F 𝔰 b.1 := by
          rw [tsum_fintype]
    _ = ∑ m : MonicLt F d, zetaTerm F 𝔰 (e m).1 := by
          exact (Equiv.sum_comp (e := e) (g := fun b : TailLT F 1 hr d => zetaTerm F 𝔰 b.1)).symm
    _ = ∑ m : MonicLt F d,
          ((((m.1 : RatFunc F) : RatFunc.CompletionAtInfty F) ^ (𝔰 ⟨0, hr⟩ : ℕ))⁻¹) := by
          apply Finset.sum_congr rfl
          intro m hm
          dsimp [e, zetaTerm, monicTuple1Equiv]
          rw [Fin.prod_univ_one]
    _ = ((Msum F d (𝔰 ⟨0, hr⟩ : ℕ) : RatFunc F) : RatFunc.CompletionAtInfty F) := by
          exact (coe_Msum F d (𝔰 ⟨0, hr⟩ : ℕ)).symm




/-- The level-`d` shuffle in the completion, with `S_<d` and `P` (before the depth-two
collapse `S_d_recursion`). -/
lemma headProdSum_comp (d : ℕ) (hd : 1 ≤ d) (a b : ℕ+) :
    P F d a * P F d b =
      P F d ⟨(a : ℕ) + (b : ℕ), Nat.add_pos_left (PNat.pos a) (b : ℕ)⟩ +
      ∑ i : {i : ℕ // i ∈ Finset.Icc 1 ((a : ℕ) + (b : ℕ) - 1)},
        (ChenDeltaZ F (a : ℕ) (b : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
        (P F d ⟨(a : ℕ) + (b : ℕ) - i.1, by
            have hi1 : 1 ≤ i.1 := (Finset.mem_Icc.mp i.2).1
            have hin : i.1 ≤ (a : ℕ) + (b : ℕ) - 1 := (Finset.mem_Icc.mp i.2).2
            omega⟩ *
         S_lt F 1 (by omega) (fun _ : Fin 1 => ⟨i.1, (Finset.mem_Icc.mp i.2).1⟩) d) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  let A : ℕ := (a : ℕ)
  let B : ℕ := (b : ℕ)
  let s : Finset ℕ := Finset.Icc 1 (A + B - 1)
  have hA : 1 ≤ A := by dsimp [A]; exact PNat.pos a
  have hB : 1 ≤ B := by dsimp [B]; exact PNat.pos b
  let nAB : ℕ+ := ⟨A + B, by dsimp [A, B]; exact Nat.add_pos_left (PNat.pos a) (b : ℕ)⟩
  let φ : RatFunc F →+* RatFunc.CompletionAtInfty F := algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)
  have hRat' : Hsum F d A * Hsum F d B =
      Hsum F d (A + B) + ∑ i ∈ s, RatFunc.C (ChenDeltaZ F A B i : F) * Msum F d i * Hsum F d (A + B - i) := by
    simpa [Hsum, Msum, s] using (headProdSum F d hd A B hA hB)
  have hSub : Hsum F d A * Hsum F d B =
      Hsum F d (A + B) + ∑ i : {i : ℕ // i ∈ s},
        RatFunc.C (ChenDeltaZ F A B i.1 : F) * Msum F d i.1 * Hsum F d (A + B - i.1) := by
    rw [hRat']
    congr 1
    rw [Finset.sum_subtype (Finset.Icc 1 (A + B - 1)) (fun x : ℕ => Iff.rfl)
      (fun i : ℕ => RatFunc.C (ChenDeltaZ F A B i : F) * Msum F d i * Hsum F d (A + B - i))]
  have hL : P F d a * P F d b = ((Hsum F d A * Hsum F d B : RatFunc F) : RatFunc.CompletionAtInfty F) := by
    rw [P_eq_coe_Hsum F d a, P_eq_coe_Hsum F d b]
    exact (map_mul φ (Hsum F d A) (Hsum F d B)).symm
  have hterm (i : {i : ℕ // i ∈ s}) :
      (((RatFunc.C (ChenDeltaZ F A B i.1 : F) * Msum F d i.1 * Hsum F d (A + B - i.1) : RatFunc F) :
          RatFunc.CompletionAtInfty F)) =
      (ChenDeltaZ F A B i.1 : RatFunc.CompletionAtInfty F) *
        (P F d ⟨A + B - i.1, by
          have hi1 : 1 ≤ i.1 := (Finset.mem_Icc.mp i.2).1
          have hin : i.1 ≤ A + B - 1 := (Finset.mem_Icc.mp i.2).2
          omega⟩ *
         S_lt F 1 (by omega) (fun _ : Fin 1 => ⟨i.1, (Finset.mem_Icc.mp i.2).1⟩) d) := by
    have h1 : (((RatFunc.C (ChenDeltaZ F A B i.1 : F) * Msum F d i.1 * Hsum F d (A + B - i.1) : RatFunc F) :
        RatFunc.CompletionAtInfty F)) =
        ((RatFunc.C (ChenDeltaZ F A B i.1 : F) : RatFunc F) : RatFunc.CompletionAtInfty F) *
        ((Msum F d i.1 : RatFunc F) : RatFunc.CompletionAtInfty F) *
        ((Hsum F d (A + B - i.1) : RatFunc F) : RatFunc.CompletionAtInfty F) := by
      change (φ (RatFunc.C (ChenDeltaZ F A B i.1 : F) * Msum F d i.1 * Hsum F d (A + B - i.1))) =
        φ (RatFunc.C (ChenDeltaZ F A B i.1 : F)) * φ (Msum F d i.1) * φ (Hsum F d (A + B - i.1))
      rw [map_mul, map_mul]
    have h2 : ((RatFunc.C (ChenDeltaZ F A B i.1 : F) : RatFunc F) : RatFunc.CompletionAtInfty F) =
        (ChenDeltaZ F A B i.1 : RatFunc.CompletionAtInfty F) := by
      exact intCast_completion F (ChenDeltaZ F A B i.1)
    have h3 : ((Msum F d i.1 : RatFunc F) : RatFunc.CompletionAtInfty F) =
        S_lt F 1 (by omega) (fun _ : Fin 1 => ⟨i.1, (Finset.mem_Icc.mp i.2).1⟩) d := by
      rw [S_lt_one_eq_coe_Msum F d (by omega) (fun _ : Fin 1 => ⟨i.1, (Finset.mem_Icc.mp i.2).1⟩)]
      rfl
    have h4 : ((Hsum F d (A + B - i.1) : RatFunc F) : RatFunc.CompletionAtInfty F) =
        P F d ⟨A + B - i.1, by
          have hi1 : 1 ≤ i.1 := (Finset.mem_Icc.mp i.2).1
          have hin : i.1 ≤ A + B - 1 := (Finset.mem_Icc.mp i.2).2
          omega⟩ := by
      rw [P_eq_coe_Hsum F d ⟨A + B - i.1, by
          have hi1 : 1 ≤ i.1 := (Finset.mem_Icc.mp i.2).1
          have hin : i.1 ≤ A + B - 1 := (Finset.mem_Icc.mp i.2).2
          omega⟩]
      rfl
    rw [h1, h2, h3, h4]
    ring
  calc
    P F d a * P F d b
        = ((Hsum F d A * Hsum F d B : RatFunc F) : RatFunc.CompletionAtInfty F) := hL
    _ = ((Hsum F d (A + B) +
          (∑ i : {i : ℕ // i ∈ s}, RatFunc.C (ChenDeltaZ F A B i.1 : F) * Msum F d i.1 *
            Hsum F d (A + B - i.1)) : RatFunc F) : RatFunc.CompletionAtInfty F) := by
          exact congrArg (fun x : RatFunc F => (x : RatFunc.CompletionAtInfty F)) hSub
    _ = ((Hsum F d (A + B) : RatFunc F) : RatFunc.CompletionAtInfty F) +
          (((∑ i : {i : ℕ // i ∈ s}, RatFunc.C (ChenDeltaZ F A B i.1 : F) * Msum F d i.1 *
              Hsum F d (A + B - i.1) : RatFunc F) : RatFunc.CompletionAtInfty F)) := by
          change (φ (Hsum F d (A + B) + (∑ i : {i : ℕ // i ∈ s}, RatFunc.C (ChenDeltaZ F A B i.1 : F) * Msum F d i.1 * Hsum F d (A + B - i.1)))) =
            φ (Hsum F d (A + B)) + φ (∑ i : {i : ℕ // i ∈ s}, RatFunc.C (ChenDeltaZ F A B i.1 : F) * Msum F d i.1 * Hsum F d (A + B - i.1))
          rw [map_add]
    _ = ((Hsum F d (A + B) : RatFunc F) : RatFunc.CompletionAtInfty F) +
          ∑ i : {i : ℕ // i ∈ s}, (((RatFunc.C (ChenDeltaZ F A B i.1 : F) * Msum F d i.1 *
              Hsum F d (A + B - i.1) : RatFunc F) : RatFunc.CompletionAtInfty F)) := by
          apply congrArg (fun t : RatFunc.CompletionAtInfty F =>
            ((Hsum F d (A + B) : RatFunc F) : RatFunc.CompletionAtInfty F) + t)
          change φ (∑ i : {i : ℕ // i ∈ s}, RatFunc.C (ChenDeltaZ F A B i.1 : F) * Msum F d i.1 * Hsum F d (A + B - i.1)) =
            ∑ i : {i : ℕ // i ∈ s}, φ (RatFunc.C (ChenDeltaZ F A B i.1 : F) * Msum F d i.1 * Hsum F d (A + B - i.1))
          rw [map_sum]
    _ = P F d nAB +
          ∑ i : {i : ℕ // i ∈ s}, (((RatFunc.C (ChenDeltaZ F A B i.1 : F) * Msum F d i.1 *
              Hsum F d (A + B - i.1) : RatFunc F) : RatFunc.CompletionAtInfty F)) := by
          have hf : ((Hsum F d (A + B) : RatFunc F) : RatFunc.CompletionAtInfty F) = P F d nAB := by
            exact (P_eq_coe_Hsum F d nAB).symm
          rw [hf]
    _ = P F d nAB +
          ∑ i : {i : ℕ // i ∈ s}, (ChenDeltaZ F A B i.1 : RatFunc.CompletionAtInfty F) *
            (P F d ⟨A + B - i.1, by
              have hi1 : 1 ≤ i.1 := (Finset.mem_Icc.mp i.2).1
              have hin : i.1 ≤ A + B - 1 := (Finset.mem_Icc.mp i.2).2
              omega⟩ *
             S_lt F 1 (by omega) (fun _ : Fin 1 => ⟨i.1, (Finset.mem_Icc.mp i.2).1⟩) d) := by
          apply congrArg (fun t : RatFunc.CompletionAtInfty F => P F d nAB + t)
          apply Finset.sum_congr rfl
          intro i hi
          exact hterm i

/-- The two-exponent tuple `(A+B-i, i)` (level-`d` depth-two index of paper (2.1)). -/
noncomputable def thakurExp (A B : ℕ) (i : {i : ℕ // i ∈ Finset.Icc 1 (A + B - 1)}) : Fin 2 → ℕ+ :=
  fun j : Fin 2 => if (j : ℕ) = 0 then
    ⟨A + B - i.1, by
      have hi1 : 1 ≤ i.1 := (Finset.mem_Icc.mp i.2).1
      have hin : i.1 ≤ A + B - 1 := (Finset.mem_Icc.mp i.2).2
      omega⟩
  else ⟨i.1, by
      have hi1 : 1 ≤ i.1 := (Finset.mem_Icc.mp i.2).1
      omega⟩

/-- The depth-two `S`-block at level `d` factors (`S_d_recursion` specialised to the
tuple `thakurExp`). -/
lemma thakur_S_two_eq (d : ℕ) (A B : ℕ)
    (i : {i : ℕ // i ∈ Finset.Icc 1 (A + B - 1)}) :
    S F 2 (by omega) (thakurExp A B i) d =
      P F d ⟨A + B - i.1, by
        have hi1 : 1 ≤ i.1 := (Finset.mem_Icc.mp i.2).1
        have hin : i.1 ≤ A + B - 1 := (Finset.mem_Icc.mp i.2).2
        omega⟩ *
      S_lt F 1 (by omega) (fun _ : Fin 1 => ⟨i.1, (Finset.mem_Icc.mp i.2).1⟩) d := by
  classical
  rw [S_d_recursion F 2 (by omega) (by omega) (by omega) (thakurExp A B i) d]
  simp [thakurExp]

/-- THAKUR PRODUCT IDENTITY, paper (2.1), at every level `d ≥ 1`:
`P_d(a) · P_d(b) = P_d(a+b) + Σ_{0<i<a+b} Δ^i_{a,b} · S_d(a+b-i, i)`. -/
lemma thakur_prod_one (d : ℕ) (hd : 1 ≤ d) (a b : ℕ+) :
    P F d a * P F d b =
      P F d ⟨(a : ℕ) + (b : ℕ), Nat.add_pos_left (PNat.pos a) (b : ℕ)⟩ +
      ∑ i : {i : ℕ // i ∈ Finset.Icc 1 ((a : ℕ) + (b : ℕ) - 1)},
        (ChenDeltaZ F (a : ℕ) (b : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
        S F 2 (by omega) (thakurExp (a : ℕ) (b : ℕ) i) d := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have h := headProdSum_comp F d hd a b
  rw [h]
  apply congrArg (fun t : RatFunc.CompletionAtInfty F =>
    P F d ⟨(a : ℕ) + (b : ℕ), Nat.add_pos_left (PNat.pos a) (b : ℕ)⟩ + t)
  apply Finset.sum_congr rfl
  intro i hi
  calc
    (ChenDeltaZ F (a : ℕ) (b : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
        (P F d ⟨(a : ℕ) + (b : ℕ) - i.1, by
          have hi1 : 1 ≤ i.1 := (Finset.mem_Icc.mp i.2).1
          have hin : i.1 ≤ (a : ℕ) + (b : ℕ) - 1 := (Finset.mem_Icc.mp i.2).2
          omega⟩ *
         S_lt F 1 (by omega) (fun _ : Fin 1 => ⟨i.1, (Finset.mem_Icc.mp i.2).1⟩) d)
        = (ChenDeltaZ F (a : ℕ) (b : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
          S F 2 (by omega) (thakurExp (a : ℕ) (b : ℕ) i) d := by
          rw [← thakur_S_two_eq F d (a : ℕ) (b : ℕ) i]

end ZagierHoffmanPositiveChar
