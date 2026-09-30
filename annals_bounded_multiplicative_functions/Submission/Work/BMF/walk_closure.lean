import Mathlib
import Submission.Work.BMF.adi_graph_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Finset

/-- Telescoping bound: if `s j * x (j+1)` is within `ε` of `x j` for `j < ℓ`, and `|s j| ≤ 2`,
then the accumulated product `(∏_{j<ℓ} s j) · x ℓ` stays within `ε · 2^ℓ` of `x 0`. -/
lemma telescope_prod_le (ℓ : ℕ) (s x : ℕ → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hstep : ∀ j, j < ℓ → |s j * x (j + 1) - x j| ≤ ε)
    (hs : ∀ j, j < ℓ → |s j| ≤ 2) :
    |(∏ j ∈ Finset.range ℓ, s j) * x ℓ - x 0| ≤ ε * 2 ^ ℓ := by
  have key : ∀ j, j ≤ ℓ → |(∏ i ∈ Finset.range j, s i) * x j - x 0| ≤ ε * 2 ^ j := by
    intro j
    induction j with
    | zero =>
      intro _
      simp only [Finset.prod_range_zero, one_mul, sub_self, abs_zero, pow_zero, mul_one]
      exact hε
    | succ k ih =>
      intro hk
      have hklt : k < ℓ := by omega
      have ihk := ih (by omega)
      have hstepk := hstep k hklt
      rw [Finset.prod_range_succ]
      have split : (∏ i ∈ Finset.range k, s i) * s k * x (k+1) - x 0
          = ((∏ i ∈ Finset.range k, s i) * s k * x (k+1) - (∏ i ∈ Finset.range k, s i) * x k)
            + ((∏ i ∈ Finset.range k, s i) * x k - x 0) := by ring
      rw [split]
      refine le_trans (abs_add_le _ _) ?_
      have hprod : |(∏ i ∈ Finset.range k, s i)| ≤ 2 ^ k := by
        rw [Finset.abs_prod]
        calc ∏ i ∈ Finset.range k, |s i| ≤ ∏ i ∈ Finset.range k, (2:ℝ) := by
              apply Finset.prod_le_prod₀
              · intro i hi; positivity
              · intro i hi
                exact hs i (by have := Finset.mem_range.mp hi; omega)
          _ = 2 ^ k := by rw [Finset.prod_const]; simp
      have hterm : |(∏ i ∈ Finset.range k, s i) * s k * x (k+1) - (∏ i ∈ Finset.range k, s i) * x k|
          ≤ 2 ^ k * ε := by
        rw [show (∏ i ∈ Finset.range k, s i) * s k * x (k+1) - (∏ i ∈ Finset.range k, s i) * x k
              = (∏ i ∈ Finset.range k, s i) * (s k * x (k+1) - x k) by ring, abs_mul]
        exact mul_le_mul hprod hstepk (abs_nonneg _) (by positivity)
      calc |(∏ i ∈ Finset.range k, s i) * s k * x (k+1) - (∏ i ∈ Finset.range k, s i) * x k|
            + |(∏ i ∈ Finset.range k, s i) * x k - x 0|
          ≤ 2 ^ k * ε + ε * 2 ^ k := add_le_add hterm ihk
        _ = ε * 2 ^ (k+1) := by rw [pow_succ]; ring
  exact key ℓ le_rfl

theorem walk_closure (k : ℕ) (f : ℕ → ℂ) (c C X L P₁ P₂ : ℝ)
    (D : Work.BMF.QuadData k f c C X L P₁ P₂) (hP : 0 < P₁) (hL : 0 < L) (hX : 0 < X)
    (q ℓ : ℕ) {W : Fin (ℓ + 1) → Work.BMF.GVert D}
    (hcyc : W ⟨ℓ, Nat.lt_succ_self ℓ⟩ = W ⟨0, Nat.zero_lt_succ ℓ⟩)
    (hadj : ∀ j : Fin ℓ, Work.BMF.GAdjQ D q (W j.castSucc) (W j.succ)) :
    |((Work.BMF.walkProdV D ℓ W : ℕ) : ℝ) - ((Work.BMF.walkProdU D ℓ W : ℕ) : ℝ)| ≤
      10 ^ 5 * (4 : ℝ) ^ ℓ * P₁ ^ ℓ / (X / L) := by
  classical
  have hX0 : X ≠ 0 := ne_of_gt hX
  have hL0 : L ≠ 0 := ne_of_gt hL
  set stV : ℕ → ℕ := fun j =>
    if h : j < ℓ then stepV D (W ⟨j, Nat.lt_succ_of_lt h⟩) (W ⟨j+1, Nat.succ_lt_succ h⟩) else 1
    with hstV
  set stU : ℕ → ℕ := fun j =>
    if h : j < ℓ then stepU D (W ⟨j, Nat.lt_succ_of_lt h⟩) (W ⟨j+1, Nat.succ_lt_succ h⟩) else 1
    with hstU
  set xx : ℕ → ℝ := fun j =>
    if h : j ≤ ℓ then (W ⟨j, Nat.lt_succ_of_le h⟩).1 else 0 with hxx
  set s : ℕ → ℝ := fun j => (stV j : ℝ) / (stU j : ℝ) with hss
  -- basic facts
  have hx0pos : 0 < xx 0 := by
    have h0 : xx 0 = (W ⟨0, Nat.lt_succ_of_le (Nat.zero_le ℓ)⟩).1 := by
      simp only [hxx, dif_pos (Nat.zero_le ℓ)]
    have hle := (D.isFam.1 _ (W ⟨0, Nat.lt_succ_of_le (Nat.zero_le ℓ)⟩).2).1
    rw [h0]; linarith
  have hcycx : xx ℓ = xx 0 := by
    have h1 : xx ℓ = (W ⟨ℓ, Nat.lt_succ_of_le (le_refl ℓ)⟩).1 := by
      simp only [hxx, dif_pos (le_refl ℓ)]
    have h0 : xx 0 = (W ⟨0, Nat.lt_succ_of_le (Nat.zero_le ℓ)⟩).1 := by
      simp only [hxx, dif_pos (Nat.zero_le ℓ)]
    rw [h1, h0]
    have hc : W (⟨ℓ, Nat.lt_succ_of_le (le_refl ℓ)⟩ : Fin (ℓ+1))
        = W (⟨0, Nat.lt_succ_of_le (Nat.zero_le ℓ)⟩ : Fin (ℓ+1)) := by
      rw [show (⟨ℓ, Nat.lt_succ_of_le (le_refl ℓ)⟩ : Fin (ℓ+1)) = ⟨ℓ, Nat.lt_succ_self ℓ⟩
            from Fin.ext rfl,
          show (⟨0, Nat.lt_succ_of_le (Nat.zero_le ℓ)⟩ : Fin (ℓ+1))
              = ⟨0, Nat.zero_lt_succ ℓ⟩ from Fin.ext rfl]
      exact hcyc
    exact congrArg (fun z : GVert D => z.1) hc
  -- step relation
  have hstep : ∀ j, j < ℓ → |s j * xx (j+1) - xx j| ≤ 200 * L := by
    intro j hj
    have h1 : xx j = (W (⟨j,hj⟩ : Fin ℓ).castSucc).1 := by
      have e : (⟨j, Nat.lt_succ_of_le (le_of_lt hj)⟩ : Fin (ℓ+1)) = (⟨j,hj⟩ : Fin ℓ).castSucc :=
        Fin.ext rfl
      simp only [hxx, dif_pos (le_of_lt hj), e]
    have h2 : xx (j+1) = (W (⟨j,hj⟩ : Fin ℓ).succ).1 := by
      have hj1 : j + 1 ≤ ℓ := by omega
      have e : (⟨j+1, Nat.lt_succ_of_le hj1⟩ : Fin (ℓ+1)) = (⟨j,hj⟩ : Fin ℓ).succ := Fin.ext rfl
      simp only [hxx, dif_pos hj1, e]
    have h3 : s j = ((stepV D (W (⟨j,hj⟩ : Fin ℓ).castSucc) (W (⟨j,hj⟩ : Fin ℓ).succ) : ℕ) : ℝ)
        / ((stepU D (W (⟨j,hj⟩ : Fin ℓ).castSucc) (W (⟨j,hj⟩ : Fin ℓ).succ) : ℕ) : ℝ) := by
      simp only [hss, hstV, hstU, dif_pos hj]
      rw [show (⟨j, Nat.lt_succ_of_lt hj⟩ : Fin (ℓ+1)) = (⟨j,hj⟩ : Fin ℓ).castSucc from Fin.ext rfl,
          show (⟨j+1, Nat.succ_lt_succ hj⟩ : Fin (ℓ+1)) = (⟨j,hj⟩ : Fin ℓ).succ from Fin.ext rfl]
    rw [h1, h2, h3, abs_sub_comm]
    exact stepGeom D (hadj ⟨j,hj⟩) hP hL
  -- ratio bound |s j| ≤ 2
  have hs : ∀ j, j < ℓ → |s j| ≤ 2 := by
    intro j hj
    have hpV := stepV_prime D (hadj ⟨j,hj⟩)
    have hpU := stepU_prime D (hadj ⟨j,hj⟩)
    have hVpos : 0 < (stepV D (W (⟨j,hj⟩ : Fin ℓ).castSucc) (W (⟨j,hj⟩ : Fin ℓ).succ) : ℝ) := by
      linarith [hP, hpV.2.1]
    have hUpos : 0 < (stepU D (W (⟨j,hj⟩ : Fin ℓ).castSucc) (W (⟨j,hj⟩ : Fin ℓ).succ) : ℝ) := by
      linarith [hP, hpU.2.1]
    have h3 : s j = ((stepV D (W (⟨j,hj⟩ : Fin ℓ).castSucc) (W (⟨j,hj⟩ : Fin ℓ).succ) : ℕ) : ℝ)
        / ((stepU D (W (⟨j,hj⟩ : Fin ℓ).castSucc) (W (⟨j,hj⟩ : Fin ℓ).succ) : ℕ) : ℝ) := by
      simp only [hss, hstV, hstU, dif_pos hj]
      rw [show (⟨j, Nat.lt_succ_of_lt hj⟩ : Fin (ℓ+1)) = (⟨j,hj⟩ : Fin ℓ).castSucc from Fin.ext rfl,
          show (⟨j+1, Nat.succ_lt_succ hj⟩ : Fin (ℓ+1)) = (⟨j,hj⟩ : Fin ℓ).succ from Fin.ext rfl]
    rw [h3, abs_of_nonneg (div_nonneg hVpos.le hUpos.le), div_le_iff₀ hUpos]
    linarith [hpV.2.2, hpU.2.1]
  -- telescoping
  have htele := telescope_prod_le ℓ s xx (200 * L) (by positivity) hstep hs
  rw [hcycx] at htele
  have hQ1 : |(∏ j ∈ Finset.range ℓ, s j) - 1| ≤ 200 * L * 2^ℓ / (X/10) := by
    have hX10 : (0:ℝ) < X/10 := by linarith
    have hmain : |(∏ j ∈ Finset.range ℓ, s j) - 1| * (X/10) ≤ 200 * L * 2^ℓ := by
      have h1 : |(∏ j ∈ Finset.range ℓ, s j) - 1| * xx 0 ≤ 200 * L * 2^ℓ := by
        rw [show (∏ j ∈ Finset.range ℓ, s j) * xx 0 - xx 0
              = ((∏ j ∈ Finset.range ℓ, s j) - 1) * xx 0 by ring,
            abs_mul, abs_of_pos hx0pos] at htele
        exact htele
      calc |(∏ j ∈ Finset.range ℓ, s j) - 1| * (X/10)
          ≤ |(∏ j ∈ Finset.range ℓ, s j) - 1| * xx 0 := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            have h0 : xx 0 = (W ⟨0, Nat.lt_succ_of_le (Nat.zero_le ℓ)⟩).1 := by
              simp only [hxx, dif_pos (Nat.zero_le ℓ)]
            rw [h0]
            exact (D.isFam.1 _ (W ⟨0, Nat.lt_succ_of_le (Nat.zero_le ℓ)⟩).2).1
        _ ≤ 200 * L * 2^ℓ := h1
    rw [le_div_iff₀ hX10]
    exact hmain
  -- identify the product with walkProdV / walkProdU
  have hVnat : (∏ j ∈ Finset.range ℓ, stV j) = walkProdV D ℓ W := by
    rw [walkProdV, ← Fin.prod_univ_eq_prod_range stV]
    apply Finset.prod_congr rfl
    intro j _
    simp only [hstV, dif_pos j.2]
    rw [show (⟨j.1, Nat.lt_succ_of_lt j.2⟩ : Fin (ℓ+1)) = j.castSucc from Fin.ext rfl,
        show (⟨j.1 + 1, Nat.succ_lt_succ j.2⟩ : Fin (ℓ+1)) = j.succ from Fin.ext rfl]
  have hUnat : (∏ j ∈ Finset.range ℓ, stU j) = walkProdU D ℓ W := by
    rw [walkProdU, ← Fin.prod_univ_eq_prod_range stU]
    apply Finset.prod_congr rfl
    intro j _
    simp only [hstU, dif_pos j.2]
    rw [show (⟨j.1, Nat.lt_succ_of_lt j.2⟩ : Fin (ℓ+1)) = j.castSucc from Fin.ext rfl,
        show (⟨j.1 + 1, Nat.succ_lt_succ j.2⟩ : Fin (ℓ+1)) = j.succ from Fin.ext rfl]
  have hQ : (∏ j ∈ Finset.range ℓ, s j)
      = ((walkProdV D ℓ W : ℕ):ℝ) / ((walkProdU D ℓ W : ℕ):ℝ) := by
    rw [hss, Finset.prod_div_distrib]
    rw [show (∏ j ∈ Finset.range ℓ, ((stV j : ℕ):ℝ)) = ((walkProdV D ℓ W : ℕ) : ℝ) by
          rw [← Nat.cast_prod, hVnat],
        show (∏ j ∈ Finset.range ℓ, ((stU j : ℕ):ℝ)) = ((walkProdU D ℓ W : ℕ) : ℝ) by
          rw [← Nat.cast_prod, hUnat]]
  -- bounds on walkProdU
  have hUcast : ((walkProdU D ℓ W : ℕ):ℝ)
      = ∏ j : Fin ℓ, ((stepU D (W j.castSucc) (W j.succ) : ℕ):ℝ) := by
    rw [walkProdU, Nat.cast_prod]
  have hBpos : 0 < ((walkProdU D ℓ W : ℕ) : ℝ) := by
    rw [hUcast]
    apply Finset.prod_pos
    intro j _
    have := (stepU_prime D (hadj j)).2.1
    linarith
  have hBle : ((walkProdU D ℓ W : ℕ) : ℝ) ≤ 2^ℓ * P₁^ℓ := by
    rw [hUcast]
    calc ∏ j : Fin ℓ, ((stepU D (W j.castSucc) (W j.succ) : ℕ):ℝ)
        ≤ ∏ _j : Fin ℓ, (2*P₁) := by
          apply Finset.prod_le_prod₀
          · intro j _; positivity
          · intro j _
            linarith [(stepU_prime D (hadj j)).2.2]
      _ = (2*P₁)^ℓ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ = 2^ℓ * P₁^ℓ := by rw [mul_pow]
  have hdiff : ((walkProdV D ℓ W : ℕ):ℝ) - ((walkProdU D ℓ W : ℕ):ℝ)
      = ((walkProdU D ℓ W : ℕ):ℝ) * ((∏ j ∈ Finset.range ℓ, s j) - 1) := by
    rw [hQ]
    field_simp
  have hQ1' : |(∏ j ∈ Finset.range ℓ, s j) - 1| ≤ 2000 * L * 2^ℓ / X := by
    have h := hQ1
    have key : (200:ℝ) * L * 2^ℓ / (X/10) = 2000 * L * 2^ℓ / X := by
      field_simp
      ring
    rwa [key] at h
  have hfour : (4:ℝ)^ℓ = 2^ℓ * 2^ℓ := by
    rw [show (4:ℝ) = 2*2 by norm_num, mul_pow]
  rw [hdiff, abs_mul, abs_of_pos hBpos]
  calc ((walkProdU D ℓ W : ℕ):ℝ) * |(∏ j ∈ Finset.range ℓ, s j) - 1|
      ≤ (2^ℓ * P₁^ℓ) * (2000 * L * 2^ℓ / X) :=
        mul_le_mul hBle hQ1' (abs_nonneg _) (by positivity)
    _ = 2000 * (4:ℝ)^ℓ * P₁^ℓ * L / X := by
        rw [hfour]; field_simp
    _ ≤ 10^5 * (4:ℝ)^ℓ * P₁^ℓ * L / X := by
        have hA : (0:ℝ) ≤ (4:ℝ)^ℓ * P₁^ℓ * L := by positivity
        have h2 : (2000:ℝ) * ((4:ℝ)^ℓ * P₁^ℓ * L) ≤ 10^5 * ((4:ℝ)^ℓ * P₁^ℓ * L) := by
          nlinarith [hA]
        have e1 : (2000:ℝ) * (4:ℝ)^ℓ * P₁^ℓ * L = 2000 * ((4:ℝ)^ℓ * P₁^ℓ * L) := by ring
        have e2 : (10:ℝ)^5 * (4:ℝ)^ℓ * P₁^ℓ * L = 10^5 * ((4:ℝ)^ℓ * P₁^ℓ * L) := by ring
        rw [e1, e2]
        exact div_le_div_of_nonneg_right h2 hX.le
    _ = 10^5 * (4:ℝ)^ℓ * P₁^ℓ / (X/L) := by
        have hXL : X/L ≠ 0 := div_ne_zero hX0 hL0
        field_simp

end Work.BMF
