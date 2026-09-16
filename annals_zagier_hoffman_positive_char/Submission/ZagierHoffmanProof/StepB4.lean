import Submission.ZagierHoffmanProof.StepB3

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Polynomial RatFunc
open scoped BigOperators

/-!
# Step B4: pure products of power sums (paper Remark 2.2(2))

When `a + b ≤ q = |F|`, the shuffle (2.1) has no depth-two terms:
`S_d(a) · S_d(b) = S_d(a+b)` for every level `d`.  All Chen coefficients vanish:
for `0 < i < a+b ≤ q`, `(q-1) ∤ i` unless `i = q-1` (only possible when `a+b = q`),
and then `Δ^i_{a,b} = ±C ± C` with equal binomials, which is `0` in `F`.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Chen's coefficients vanish in `F` when the two exponents sum to at most `q`. -/
lemma chenDeltaZ_cast_zero_of_sum_le_card (a b i : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hi0 : 0 < i) (hi : i < a + b) (hq : a + b ≤ Nat.card F) :
    ((ChenDeltaZ F a b i : ℤ) : F) = 0 := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  let q : ℕ := Nat.card F
  have hq2 : 2 ≤ q := by
    dsimp [q]
    have h1 := Fintype.one_lt_card (α := F)
    have hc : 2 ≤ Fintype.card F := by omega
    simpa [Nat.card_eq_fintype_card] using hc
  by_cases hdiv : (q - 1) ∣ i
  · have hi_le : i ≤ q - 1 := by omega
    have hq1_le : q - 1 ≤ i := Nat.le_of_dvd hi0 hdiv
    have hiq : i = q - 1 := le_antisymm hi_le hq1_le
    have habq : a + b = q := by omega
    have htwo_of_same : (Even (a - 1) ↔ Even (b - 1)) → (2 : F) = 0 := by
      intro hiff
      have hpar : Even ((a - 1) + (b - 1)) := by
        exact Nat.even_add.mpr hiff
      have hqE : Even q := by
        have hqexp : q = ((a - 1) + (b - 1)) + 2 := by omega
        rw [hqexp]
        exact Nat.even_add.mpr ⟨(fun _ => even_two), (fun _ => hpar)⟩
      have hmod : Fintype.card F % 2 = 0 := by
        have hE : Even (Fintype.card F) := by
          simpa [q, Nat.card_eq_fintype_card] using hqE
        exact Nat.even_iff.mp hE
      have hch := (FiniteField.even_card_iff_char_two (F := F)).mpr hmod
      exact (ringChar.spec F 2).mpr (by simpa [hch])
    have hC : (Nat.choose (i - 1) (a - 1) : F) = (Nat.choose (i - 1) (b - 1) : F) := by
      rw [hiq]
      have hsub : q - 1 - 1 = q - 2 := by omega
      rw [hsub]
      apply congrArg (fun n : ℕ => (n : F))
      rw [← Nat.choose_symm (by omega : a - 1 ≤ q - 2)]
      congr 1
      omega
    let ΔF : F := (if Even (a - 1) then 1 else -1 : F) * (Nat.choose (i - 1) (a - 1) : F) +
        (if Even (b - 1) then 1 else -1 : F) * (Nat.choose (i - 1) (b - 1) : F)
    have hz : ((ChenDeltaZ F a b i : ℤ) : F) = ΔF := by
      unfold ChenDeltaZ
      have hd : (Nat.card F - 1) ∣ i := by simpa [q] using hdiv
      rw [if_pos hd]
      by_cases ea : Even (a - 1) <;> by_cases eb : Even (b - 1)
      · simp [ΔF, ea, eb]
      · simp [ΔF, ea, eb]
      · simp [ΔF, ea, eb]
      · simp [ΔF, ea, eb]
    rw [hz]
    by_cases ea : Even (a - 1) <;> by_cases eb : Even (b - 1)
    · have h2zero : (2 : F) = 0 := htwo_of_same ⟨(fun _ => eb), (fun _ => ea)⟩
      dsimp [ΔF]
      simp [ea, eb]
      rw [hC]
      rw [← two_mul]
      rw [h2zero]
      simp
    · dsimp [ΔF]
      simp [ea, eb]
      rw [hC]
      ring
    · dsimp [ΔF]
      simp [ea, eb]
      rw [hC]
      ring
    · have h2zero : (2 : F) = 0 := htwo_of_same ⟨(fun hea => False.elim (ea hea)), (fun heb => False.elim (eb heb))⟩
      dsimp [ΔF]
      simp [ea, eb]
      rw [hC]
      rw [← two_mul]
      rw [h2zero]
      simp
  · unfold ChenDeltaZ
    have hd : ¬ (Nat.card F - 1) ∣ i := by simpa [q] using hdiv
    rw [if_neg hd]
    simp

/-- Paper Remark 2.2(2): for `a + b ≤ q`, the depth-one product at any level is pure:
`S_d(a) · S_d(b) = S_d(a+b)`. -/
lemma P_pure (d : ℕ) (hd : 1 ≤ d) (a b : ℕ+)
    (hab : (a : ℕ) + (b : ℕ) ≤ Nat.card F) :
    P F d a * P F d b =
      P F d ⟨(a : ℕ) + (b : ℕ), Nat.add_pos_left (PNat.pos a) (b : ℕ)⟩ := by
  classical
  rw [thakur_prod_one F d hd a b]
  have hsum : (∑ i : {i : ℕ // i ∈ Finset.Icc 1 ((a : ℕ) + (b : ℕ) - 1)},
      (ChenDeltaZ F (a : ℕ) (b : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
      S F 2 (by omega) (thakurExp (a : ℕ) (b : ℕ) i) d) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hzi : ((ChenDeltaZ F (a : ℕ) (b : ℕ) i.1 : ℤ) : F) = 0 := by
      apply chenDeltaZ_cast_zero_of_sum_le_card F (a : ℕ) (b : ℕ) i.1 (PNat.pos a) (PNat.pos b)
      · exact (Finset.mem_Icc.mp i.2).1
      · have hin : i.1 ≤ (a : ℕ) + (b : ℕ) - 1 := (Finset.mem_Icc.mp i.2).2
        have ha1 : 1 ≤ (a : ℕ) := PNat.pos a
        have hb1 : 1 ≤ (b : ℕ) := PNat.pos b
        omega
      · exact hab
    have hzc : (ChenDeltaZ F (a : ℕ) (b : ℕ) i.1 : RatFunc.CompletionAtInfty F) = 0 := by
      rw [← intCast_completion F (ChenDeltaZ F (a : ℕ) (b : ℕ) i.1)]
      have hC : RatFunc.C ((ChenDeltaZ F (a : ℕ) (b : ℕ) i.1 : ℤ) : F) = 0 := by
        simp [hzi]
      rw [hC]
      change (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F) (0 : RatFunc F)) = 0
      exact map_zero (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F))
    rw [hzc]
    simp
  rw [hsum]
  simp

end ZagierHoffmanPositiveChar
