import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Field.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.E2Bound.SlotMul

theorem zrev_seq_bound (N : ℕ) (c : ℕ → ℝ) (hc0 : c 0 ≠ 0) :
    ∃ D : ℝ, 0 < D ∧ ∀ (f g : ℕ → ℝ),
      (∀ i ≤ N, g i = ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ) * c b * f (i - b)) →
      ∀ j ≤ N, (f j) ^ 2 ≤ D * ∑ k ∈ Finset.range (j + 1), (g k) ^ 2 := by
  -- The relation `g i = ∑ b, (i.choose b) * c b * f (i - b)` is triangular in `f`, with the
  -- coefficient of `f i` equal to `c 0 ≠ 0`.  We solve it by strong induction on the index,
  -- producing a constant `B` such that `(f i)^2 ≤ B * ∑_{k ≤ i} (g k)^2` for all `i ≤ j`,
  -- uniformly in `(f, g)` satisfying the relation up to `j`.
  have key : ∀ j : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ (f g : ℕ → ℝ),
      (∀ i ≤ j, g i = ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ) * c b * f (i - b)) →
      ∀ i ≤ j, (f i) ^ 2 ≤ B * ∑ k ∈ Finset.range (i + 1), (g k) ^ 2 := by
    intro j
    induction j with
    | zero =>
      -- `g 0 = c 0 * f 0`, hence `f 0 = g 0 / c 0`.
      refine ⟨((c 0)⁻¹)^2 + 1, by positivity, ?_⟩
      intro f g hrel i hi
      have hi0 : i = 0 := Nat.le_zero.mp hi
      subst hi0
      rw [Nat.zero_add, Finset.sum_range_one]
      have hg : g 0 = c 0 * f 0 := by
        have h := hrel 0 (le_refl 0)
        rw [Finset.sum_range_one] at h
        simpa using h
      have hf0 : f 0 = g 0 / c 0 := by
        rw [eq_div_iff hc0, hg]; ring
      rw [hf0, div_pow, div_eq_mul_inv, ← inv_pow]
      calc (g 0)^2 * ((c 0)⁻¹)^2 = ((c 0)⁻¹)^2 * (g 0)^2 := by ring
        _ ≤ (((c 0)⁻¹)^2 + 1) * (g 0)^2 := by
            apply mul_le_mul_of_nonneg_right _ (sq_nonneg (g 0))
            linarith [sq_nonneg ((c 0)⁻¹)]
    | succ j ih =>
      obtain ⟨B, hBpos, hB⟩ := ih
      -- the off-diagonal coefficient square sum at index `j+1`
      set Ac : ℝ := ∑ b ∈ Finset.range (j + 1), (((j + 1).choose (b + 1) : ℝ) * c (b + 1))^2 with hAc
      have hAcnn : 0 ≤ Ac := by rw [hAc]; exact Finset.sum_nonneg (fun b _ => sq_nonneg _)
      refine ⟨max B (2 * (1 + Ac * ((j:ℝ) + 1) * B) / (c 0)^2),
        lt_of_lt_of_le hBpos (le_max_left _ _), ?_⟩
      intro f g hrel i hi
      have hrel_j : ∀ i ≤ j, g i = ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ) * c b * f (i - b) :=
        fun i hi' => hrel i (by omega)
      set T : ℝ := ∑ b ∈ Finset.range (j + 1), (((j + 1).choose (b + 1) : ℝ) * c (b + 1)) * f (j - b) with hT
      set G : ℝ := ∑ k ∈ Finset.range (j + 2), (g k)^2 with hG
      have hGnn : 0 ≤ G := by rw [hG]; exact Finset.sum_nonneg (fun k _ => sq_nonneg _)
      -- isolate the diagonal term `c 0 * f (j+1)` in the `(j+1)`-th relation
      have key1 : (∑ b ∈ Finset.range (j + 2), ((j+1).choose b : ℝ) * c b * f (j + 1 - b))
          = (∑ b ∈ Finset.range (j + 1), ((j+1).choose (b+1) : ℝ) * c (b+1) * f (j - b)) + c 0 * f (j+1) := by
        rw [Finset.sum_range_succ']
        congr 1
        · apply Finset.sum_congr rfl
          intro b hb
          rw [Nat.succ_sub_succ]
        · simp [Nat.choose_zero_right]
      have hsplit : g (j + 1) = T + c 0 * f (j + 1) := by
        rw [hrel (j + 1) (le_refl _), key1, hT]
      -- Cauchy–Schwarz bound on `T`
      have hTbound : T^2 ≤ Ac * (((j:ℝ)+1) * (B * G)) := by
        have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (j + 1))
          (fun b => ((j + 1).choose (b + 1) : ℝ) * c (b + 1)) (fun b => f (j - b))
        have hstep : ∑ b ∈ Finset.range (j + 1), (f (j - b))^2 ≤ ((j:ℝ)+1) * (B * G) := by
          have hb : ∀ b ∈ Finset.range (j + 1), (f (j - b))^2 ≤ B * G := by
            intro b hbmem
            have h1 := hB f g hrel_j (j - b) (Nat.sub_le j b)
            have h2 : ∑ k ∈ Finset.range (j - b + 1), (g k)^2 ≤ G := by
              rw [hG]
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro x hx
                rw [Finset.mem_range] at hx ⊢
                omega
              · intro x _ _
                exact sq_nonneg _
            exact le_trans h1 (mul_le_mul_of_nonneg_left h2 hBpos.le)
          calc ∑ b ∈ Finset.range (j + 1), (f (j - b))^2
              ≤ ∑ _b ∈ Finset.range (j + 1), B * G := Finset.sum_le_sum hb
            _ = ((j:ℝ)+1) * (B * G) := by
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
                push_cast
                ring
        calc T^2 = (∑ b ∈ Finset.range (j + 1), ((j + 1).choose (b + 1) : ℝ) * c (b + 1) * f (j - b))^2 := by rw [hT]
          _ ≤ (∑ b ∈ Finset.range (j + 1), (((j + 1).choose (b + 1) : ℝ) * c (b + 1))^2) * (∑ b ∈ Finset.range (j + 1), (f (j - b))^2) := hcs
          _ ≤ Ac * (((j:ℝ)+1) * (B * G)) := by
              rw [hAc]
              exact mul_le_mul_of_nonneg_left hstep (Finset.sum_nonneg (fun b _ => sq_nonneg _))
      have hcase : i ≤ j ∨ i = j + 1 := by omega
      rcases hcase with hi' | hi'
      · -- `i ≤ j`: use the induction hypothesis, upgraded to the larger constant
        have h1 := hB f g hrel_j i hi'
        have h2 : B ≤ max B (2 * (1 + Ac * ((j:ℝ) + 1) * B) / (c 0)^2) := le_max_left _ _
        have h3 : 0 ≤ ∑ k ∈ Finset.range (i+1), (g k)^2 := Finset.sum_nonneg (fun k _ => sq_nonneg _)
        calc (f i)^2 ≤ B * ∑ k ∈ Finset.range (i + 1), (g k)^2 := h1
          _ ≤ max B (2 * (1 + Ac * ((j:ℝ) + 1) * B) / (c 0)^2) * ∑ k ∈ Finset.range (i + 1), (g k)^2 :=
              mul_le_mul_of_nonneg_right h2 h3
      · -- `i = j + 1`: solve for `f (j+1)` and bound by Cauchy–Schwarz
        subst hi'
        rw [show j + 1 + 1 = j + 2 from by omega, ← hG]
        have hf : f (j + 1) = (g (j + 1) - T) / c 0 := by
          rw [eq_div_iff hc0, hsplit]; ring
        rw [hf, div_pow]
        have hcs2 : (g (j + 1) - T)^2 / (c 0)^2
            ≤ (2 * (1 + Ac * ((j:ℝ) + 1) * B) / (c 0)^2) * G := by
          have hnum : (g (j + 1) - T)^2 ≤ 2 * (1 + Ac * ((j:ℝ) + 1) * B) * G := by
            have h1 : (g (j + 1) - T)^2 ≤ 2 * (g (j + 1))^2 + 2 * T^2 := by
              nlinarith [sq_nonneg (g (j + 1) + T)]
            have h2 : (g (j + 1))^2 ≤ G := by
              rw [hG]
              exact Finset.single_le_sum (fun k _ => sq_nonneg (g k)) (by rw [Finset.mem_range]; omega)
            have hj1pos : (0:ℝ) < (j:ℝ) + 1 := by positivity
            nlinarith [h1, h2, hTbound, hAcnn, hGnn, hBpos, hj1pos]
          have hdiv := div_le_div_of_nonneg_right hnum (by positivity : (0:ℝ) ≤ (c 0)^2)
          have h3 : (2 * (1 + Ac * ((j:ℝ) + 1) * B) * G) / (c 0)^2
              = (2 * (1 + Ac * ((j:ℝ) + 1) * B) / (c 0)^2) * G := by ring
          rw [h3] at hdiv
          exact hdiv
        have hXle : 2 * (1 + Ac * ((j:ℝ) + 1) * B) / (c 0)^2
            ≤ max B (2 * (1 + Ac * ((j:ℝ) + 1) * B) / (c 0)^2) := le_max_right _ _
        calc (g (j + 1) - T)^2 / (c 0)^2
            ≤ (2 * (1 + Ac * ((j:ℝ) + 1) * B) / (c 0)^2) * G := hcs2
          _ ≤ max B (2 * (1 + Ac * ((j:ℝ) + 1) * B) / (c 0)^2) * G :=
              mul_le_mul_of_nonneg_right hXle hGnn
  obtain ⟨B, hBpos, hB⟩ := key N
  exact ⟨B, hBpos, fun f g hrel j hj => hB f g hrel j hj⟩

end Work.FTS.CoercivityFix.E2Bound.SlotMul
