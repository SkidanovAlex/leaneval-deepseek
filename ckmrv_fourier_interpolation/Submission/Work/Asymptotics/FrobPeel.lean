/-
# The elementary reduction step for `SL(2,ℤ)`

Every `γ ∈ SL(2,ℤ)` of squared Frobenius norm `> 2` can be right-multiplied by one of the four
elements `T`, `T⁻¹`, `S*T`, `S*T⁻¹` so that the squared Frobenius norm drops by at least `1`.
The four moves reduce the second column of `γ` by an integral multiple of the first (`T^{±1}`), or
-- after the swap `S` -- the first column by a multiple of the second (`S*T^{±1}`).

The proof is the classical column computation.  Writing `V₁ = a² + c²`, `V₂ = b² + d²` for the
squared norms of the two columns and `p = ab + cd` for their inner product, the four moves give

  `frobSq (γT) = V₁+V₂+(V₁+2p)`, `frobSq (γT⁻¹) = V₁+V₂+(V₁-2p)`,
  `frobSq (γST) = V₁+V₂+(V₂-2p)`, `frobSq (γST⁻¹) = V₁+V₂+(V₂+2p)`,

so the best move decreases the norm by `2|p| - min (V₁,V₂)`.  Since `ad - bc = 1`, the Lagrange
identity `p² + 1 = V₁ * V₂` holds; with `m = min (V₁,V₂) ≥ 1` and `V₁ + V₂ > 2` this forces
`4p² = 4V₁V₂ - 4 ≥ (m+1)²`, hence `2|p| ≥ m+1`, i.e. a decrease of at least `1`.

The elements of norm `≤ 2` are exactly `±1` and `±S`.
-/
import Mathlib
import Submission.Work.Asymptotics.CarryDefs

set_option maxHeartbeats 800000

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

set_option maxHeartbeats 800000

/-- `frobSq` in terms of the entries, over `ℤ`. -/
lemma frobSq_cast (γ : SL(2,ℤ)) :
    ((frobSq γ : ℤ)) = (γ 0 0) ^ 2 + (γ 0 1) ^ 2 + (γ 1 0) ^ 2 + (γ 1 1) ^ 2 := by
  simp only [frobSq]
  push_cast
  rw [sq_abs, sq_abs, sq_abs, sq_abs]

private lemma coe_T : ((ModularGroup.T : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 1; 0, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

private lemma coe_Tinv :
    ((ModularGroup.T⁻¹ : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, -1; 0, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

private lemma coe_S : ((ModularGroup.S : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![0, -1; 1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

/-- The entries of `γ * ℓ` are the matrix product entries. -/
lemma entry_mul (γ ℓ : SL(2,ℤ)) (i j : Fin 2) :
    (γ * ℓ) i j = ∑ k : Fin 2, γ i k * (ℓ : Matrix (Fin 2) (Fin 2) ℤ) k j := by
  conv_lhs => rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]

private lemma entries_mul_T (γ : SL(2,ℤ)) :
    (γ * ModularGroup.T) 0 0 = γ 0 0 ∧ (γ * ModularGroup.T) 0 1 = γ 0 0 + γ 0 1 ∧
      (γ * ModularGroup.T) 1 0 = γ 1 0 ∧ (γ * ModularGroup.T) 1 1 = γ 1 0 + γ 1 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · rw [entry_mul]
      simp only [Fin.sum_univ_two, Fin.isValue, coe_T, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
        Matrix.of_apply]
      ring

private lemma entries_mul_Tinv (γ : SL(2,ℤ)) :
    (γ * ModularGroup.T⁻¹) 0 0 = γ 0 0 ∧ (γ * ModularGroup.T⁻¹) 0 1 = γ 0 1 - γ 0 0 ∧
      (γ * ModularGroup.T⁻¹) 1 0 = γ 1 0 ∧ (γ * ModularGroup.T⁻¹) 1 1 = γ 1 1 - γ 1 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · rw [entry_mul]
      simp only [Fin.sum_univ_two, Fin.isValue, coe_Tinv, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
        Matrix.of_apply]
      ring

private lemma entries_mul_S (γ : SL(2,ℤ)) :
    (γ * ModularGroup.S) 0 0 = γ 0 1 ∧ (γ * ModularGroup.S) 0 1 = -γ 0 0 ∧
      (γ * ModularGroup.S) 1 0 = γ 1 1 ∧ (γ * ModularGroup.S) 1 1 = -γ 1 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · rw [entry_mul]
      simp only [Fin.sum_univ_two, Fin.isValue, coe_S, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
        Matrix.of_apply]
      ring

/-- The four `frobSq` values of the four elementary moves, in terms of the two column norms
`V₁ = a² + c²`, `V₂ = b² + d²` and the inner product `p = ab + cd` of the columns. -/
lemma frobSq_moves (γ : SL(2,ℤ)) :
    ((frobSq (γ * ModularGroup.T) : ℤ))
        = 2 * ((γ 0 0) ^ 2 + (γ 1 0) ^ 2) + ((γ 0 1) ^ 2 + (γ 1 1) ^ 2)
          + 2 * ((γ 0 0) * (γ 0 1) + (γ 1 0) * (γ 1 1))
    ∧ ((frobSq (γ * ModularGroup.T⁻¹) : ℤ))
        = 2 * ((γ 0 0) ^ 2 + (γ 1 0) ^ 2) + ((γ 0 1) ^ 2 + (γ 1 1) ^ 2)
          - 2 * ((γ 0 0) * (γ 0 1) + (γ 1 0) * (γ 1 1))
    ∧ ((frobSq (γ * (ModularGroup.S * ModularGroup.T)) : ℤ))
        = ((γ 0 0) ^ 2 + (γ 1 0) ^ 2) + 2 * ((γ 0 1) ^ 2 + (γ 1 1) ^ 2)
          - 2 * ((γ 0 0) * (γ 0 1) + (γ 1 0) * (γ 1 1))
    ∧ ((frobSq (γ * (ModularGroup.S * ModularGroup.T⁻¹)) : ℤ))
        = ((γ 0 0) ^ 2 + (γ 1 0) ^ 2) + 2 * ((γ 0 1) ^ 2 + (γ 1 1) ^ 2)
          + 2 * ((γ 0 0) * (γ 0 1) + (γ 1 0) * (γ 1 1)) := by
  have hST : (γ * (ModularGroup.S * ModularGroup.T)) = (γ * ModularGroup.S) * ModularGroup.T :=
    (mul_assoc _ _ _).symm
  have hSTi : (γ * (ModularGroup.S * ModularGroup.T⁻¹))
      = (γ * ModularGroup.S) * ModularGroup.T⁻¹ := (mul_assoc _ _ _).symm
  have eT := entries_mul_T γ
  have eTi := entries_mul_Tinv γ
  have eS := entries_mul_S γ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [frobSq_cast, eT.1, eT.2.1, eT.2.2.1, eT.2.2.2]; ring
  · rw [frobSq_cast, eTi.1, eTi.2.1, eTi.2.2.1, eTi.2.2.2]; ring
  · have fT := entries_mul_T (γ * ModularGroup.S)
    rw [hST, frobSq_cast, fT.1, fT.2.1, fT.2.2.1, fT.2.2.2, eS.1, eS.2.1, eS.2.2.1, eS.2.2.2]
    ring
  · have fTi := entries_mul_Tinv (γ * ModularGroup.S)
    rw [hSTi, frobSq_cast, fTi.1, fTi.2.1, fTi.2.2.1, fTi.2.2.2, eS.1, eS.2.1, eS.2.2.1,
      eS.2.2.2]
    ring

/-- The integer core of the reduction step: `2|p| ≥ min(V₁,V₂) + 1`. -/
lemma int_core (V1 V2 p : ℤ) (h1 : 1 ≤ V1) (h2 : 1 ≤ V2) (h3 : 2 < V1 + V2)
    (h4 : p ^ 2 + 1 = V1 * V2) : 2 * |p| ≥ min V1 V2 + 1 := by
  have hV1 : 0 ≤ V1 := by omega
  have hV2 : 0 ≤ V2 := by omega
  have hsq : (min V1 V2 + 1) ^ 2 ≤ (2 * p) ^ 2 := by
    rcases le_total V1 V2 with hle | hle
    · rw [min_eq_left hle]
      rcases le_or_gt 2 V1 with hV | hV
      · nlinarith [h4, hle, h1, hV]
      · have hV1' : V1 = 1 := by omega
        have hV2' : 2 ≤ V2 := by omega
        rw [hV1']
        nlinarith [h4, hV2']
    · rw [min_eq_right hle]
      rcases le_or_gt 2 V2 with hV | hV
      · nlinarith [h4, hle, h2, hV]
      · have hV2' : V2 = 1 := by omega
        have hV1' : 2 ≤ V1 := by omega
        rw [hV2']
        nlinarith [h4, hV1']
  have hle := (sq_le_sq).mp hsq
  have h1' : |min V1 V2 + 1| = min V1 V2 + 1 := abs_of_nonneg (by omega)
  have h2' : |2 * p| = 2 * |p| := by rw [abs_mul]; norm_num
  rwa [h1', h2'] at hle

end Work.Asymptotics

namespace Work.Asymptotics

/-- The integer solutions of `x² + y² = 1`. -/
lemma unit_pair (x y : ℤ) (h : x ^ 2 + y ^ 2 = 1) :
    (x = 1 ∧ y = 0) ∨ (x = -1 ∧ y = 0) ∨ (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = -1) := by
  have hx : -1 ≤ x ∧ x ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg y, sq_nonneg (x - 1), sq_nonneg (x + 1)]
  have hy : -1 ≤ y ∧ y ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg x, sq_nonneg (y - 1), sq_nonneg (y + 1)]
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  interval_cases x <;> interval_cases y <;> simp_all

theorem frobSq_peel (γ : SL(2,ℤ)) :
    (2 < frobSq γ → ∃ ℓ : SL(2,ℤ),
      (ℓ = ModularGroup.T ∨ ℓ = ModularGroup.T⁻¹ ∨ ℓ = ModularGroup.S * ModularGroup.T
        ∨ ℓ = ModularGroup.S * ModularGroup.T⁻¹) ∧ frobSq (γ * ℓ) + 1 ≤ frobSq γ)
    ∧ (frobSq γ ≤ 2 → γ = 1 ∨ γ = -1 ∨ γ = ModularGroup.S ∨ γ = -ModularGroup.S) := by
  generalize ha : γ 0 0 = a
  generalize hb : γ 0 1 = b
  generalize hc : γ 1 0 = c
  generalize hd : γ 1 1 = d
  have hdet : a * d - b * c = 1 := by
    have h := γ.2
    rw [Matrix.det_fin_two] at h
    rw [← ha, ← hb, ← hc, ← hd]
    exact h
  have hlagr : (a * b + c * d) ^ 2 + 1 = (a ^ 2 + c ^ 2) * (b ^ 2 + d ^ 2) := by nlinarith
  have hV1 : 1 ≤ a ^ 2 + c ^ 2 := by
    by_contra h
    push_neg at h
    have ha0 : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg c]
    have hc0 : c = 0 := by nlinarith [sq_nonneg a, sq_nonneg c]
    rw [ha0, hc0] at hdet
    norm_num at hdet
  have hV2 : 1 ≤ b ^ 2 + d ^ 2 := by
    by_contra h
    push_neg at h
    have hb0 : b = 0 := by nlinarith [sq_nonneg b, sq_nonneg d]
    have hd0 : d = 0 := by nlinarith [sq_nonneg b, sq_nonneg d]
    rw [hb0, hd0] at hdet
    norm_num at hdet
  have hcast : (frobSq γ : ℤ) = (a ^ 2 + c ^ 2) + (b ^ 2 + d ^ 2) := by
    have h := frobSq_cast γ
    rw [ha, hb, hc, hd] at h
    linarith
  obtain ⟨mT, mTi, mST, mSTi⟩ := frobSq_moves γ
  rw [ha, hb, hc, hd] at mT mTi mST mSTi
  constructor
  · intro hgt
    have hgt' : (2 : ℤ) < (a ^ 2 + c ^ 2) + (b ^ 2 + d ^ 2) := by
      have h : (2 : ℤ) < (frobSq γ : ℤ) := by exact_mod_cast hgt
      rwa [hcast] at h
    have hbound := int_core (a ^ 2 + c ^ 2) (b ^ 2 + d ^ 2) (a * b + c * d) hV1 hV2 hgt' hlagr
    rcases le_total (a ^ 2 + c ^ 2) (b ^ 2 + d ^ 2) with hle | hle
    · rw [min_eq_left hle] at hbound
      rcases le_or_gt 0 (a * b + c * d) with hp | hp
      · refine ⟨ModularGroup.T⁻¹, Or.inr (Or.inl rfl), ?_⟩
        have hone : |a * b + c * d| = a * b + c * d := abs_of_nonneg hp
        rw [hone] at hbound
        have : (frobSq (γ * ModularGroup.T⁻¹) : ℤ) + 1 ≤ (frobSq γ : ℤ) := by
          rw [mTi, hcast]; linarith
        exact_mod_cast this
      · refine ⟨ModularGroup.T, Or.inl rfl, ?_⟩
        have hone : |a * b + c * d| = -(a * b + c * d) := abs_of_neg hp
        rw [hone] at hbound
        have : (frobSq (γ * ModularGroup.T) : ℤ) + 1 ≤ (frobSq γ : ℤ) := by
          rw [mT, hcast]; linarith
        exact_mod_cast this
    · rw [min_eq_right hle] at hbound
      rcases le_or_gt 0 (a * b + c * d) with hp | hp
      · refine ⟨ModularGroup.S * ModularGroup.T, Or.inr (Or.inr (Or.inl rfl)), ?_⟩
        have hone : |a * b + c * d| = a * b + c * d := abs_of_nonneg hp
        rw [hone] at hbound
        have : (frobSq (γ * (ModularGroup.S * ModularGroup.T)) : ℤ) + 1 ≤ (frobSq γ : ℤ) := by
          rw [mST, hcast]; linarith
        exact_mod_cast this
      · refine ⟨ModularGroup.S * ModularGroup.T⁻¹, Or.inr (Or.inr (Or.inr rfl)), ?_⟩
        have hone : |a * b + c * d| = -(a * b + c * d) := abs_of_neg hp
        rw [hone] at hbound
        have : (frobSq (γ * (ModularGroup.S * ModularGroup.T⁻¹)) : ℤ) + 1 ≤ (frobSq γ : ℤ) := by
          rw [mSTi, hcast]; linarith
        exact_mod_cast this
  · intro hle2
    clear mT mTi mST mSTi hlagr
    have hsum : (a ^ 2 + c ^ 2) + (b ^ 2 + d ^ 2) ≤ 2 := by
      rw [← hcast]
      exact_mod_cast hle2
    have hV1' : a ^ 2 + c ^ 2 = 1 := by omega
    have hV2' : b ^ 2 + d ^ 2 = 1 := by omega
    rcases unit_pair a c hV1' with h1 | h1 | h1 | h1
    · -- (a,c) = (1,0), so γ = 1
      obtain ⟨ha1, hc0⟩ := h1
      have hd1 : d = 1 := by rw [ha1, hc0] at hdet; linarith only [hdet]
      have hb0 : b = 0 := by nlinarith only [hV2', hd1, sq_nonneg b]
      exact Or.inl (Subtype.ext (by
        ext i j
        fin_cases i <;> fin_cases j <;> simp_all))
    · -- (a,c) = (-1,0), so γ = -1
      obtain ⟨ha1, hc0⟩ := h1
      have hd1 : d = -1 := by rw [ha1, hc0] at hdet; linarith only [hdet]
      have hb0 : b = 0 := by nlinarith only [hV2', hd1, sq_nonneg b]
      refine Or.inr (Or.inl ?_)
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        (rw [Matrix.SpecialLinearGroup.coe_neg]; simp_all [Matrix.neg_apply])
    · -- (a,c) = (0,1), so γ = S
      obtain ⟨ha0, hc1⟩ := h1
      have hb1 : b = -1 := by rw [ha0, hc1] at hdet; linarith only [hdet]
      have hd0 : d = 0 := by nlinarith only [hV2', hb1, sq_nonneg d]
      exact Or.inr (Or.inr (Or.inl (Subtype.ext (by
        ext i j
        fin_cases i <;> fin_cases j <;> simp_all [ModularGroup.S]))))
    · -- (a,c) = (0,-1), so γ = -S
      obtain ⟨ha0, hc1⟩ := h1
      have hb1 : b = 1 := by rw [ha0, hc1] at hdet; linarith only [hdet]
      have hd0 : d = 0 := by nlinarith only [hV2', hb1, sq_nonneg d]
      refine Or.inr (Or.inr (Or.inr ?_))
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        (rw [Matrix.SpecialLinearGroup.coe_neg]; simp_all [ModularGroup.S, Matrix.neg_apply])

end Work.Asymptotics
