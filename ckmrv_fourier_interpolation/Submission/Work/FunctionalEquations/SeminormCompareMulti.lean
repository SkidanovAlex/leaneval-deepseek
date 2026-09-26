import Submission.Work.FunctionalEquations.SeminormCompareOneD

open scoped ContDiff BigOperators

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace Work.FunctionalEquations

variable {n : ℕ} [NeZero n]

/-- The `j`-th derivative of a function along a line is the `j`-th Fréchet derivative
evaluated on `j` copies of the direction. -/
lemma iteratedDeriv_line {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : EuclideanSpace ℝ (Fin n) → F) (hg : ContDiff ℝ ∞ g) (x u : EuclideanSpace ℝ (Fin n))
    (j : ℕ) (t : ℝ) :
    iteratedDeriv j (fun s : ℝ => g (x + s • u)) t =
      (iteratedFDeriv ℝ j g (x + t • u)) (fun _ : Fin j => u) := by
  have h1 : ContDiff ℝ ∞ (fun z : EuclideanSpace ℝ (Fin n) => g (x + z)) := by
    have h : ContDiff ℝ ∞ (fun z : EuclideanSpace ℝ (Fin n) => x + z) := by fun_prop
    exact hg.comp h
  have hcomp : (fun s : ℝ => g (x + s • u))
      = (fun z : EuclideanSpace ℝ (Fin n) => g (x + z))
          ∘ (ContinuousLinearMap.toSpanSingleton ℝ u) := by
    funext s
    rw [Function.comp_apply, ContinuousLinearMap.toSpanSingleton_apply]
  rw [iteratedDeriv_eq_iteratedFDeriv, hcomp]
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right (ContinuousLinearMap.toSpanSingleton ℝ u)
        (n := ∞) h1 t (WithTop.coe_le_coe.mpr le_top)]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul]
  rw [iteratedFDeriv_comp_add_left]

/-- Norm form of `iteratedDeriv_line`. -/
lemma norm_iteratedDeriv_line_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : EuclideanSpace ℝ (Fin n) → F) (hg : ContDiff ℝ ∞ g) (x u : EuclideanSpace ℝ (Fin n))
    (hu : ‖u‖ ≤ 1) (j : ℕ) (t : ℝ) :
    ‖iteratedDeriv j (fun s : ℝ => g (x + s • u)) t‖
      ≤ ‖iteratedFDeriv ℝ j g (x + t • u)‖ := by
  rw [iteratedDeriv_line g hg x u j t]
  calc ‖(iteratedFDeriv ℝ j g (x + t • u)) (fun _ : Fin j => u)‖
      ≤ ‖iteratedFDeriv ℝ j g (x + t • u)‖ * ∏ _i : Fin j, ‖u‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖iteratedFDeriv ℝ j g (x + t • u)‖ * ‖u‖^j := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ ‖iteratedFDeriv ℝ j g (x + t • u)‖ * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact pow_le_one₀ (norm_nonneg _) hu
    _ = ‖iteratedFDeriv ℝ j g (x + t • u)‖ := by ring


/-- Universe-`0` version of `oneD_bound_gen`, pinning the universe so that the
constant can be chosen once and for all. -/
lemma oneD_bound_gen_zero (P j : ℕ) (hj : j ≤ P) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (g : ℝ → V),
      ContDiff ℝ (P : ℕ∞ω) g → ∀ (R M N : ℝ), 0 < R → 0 ≤ M → 0 ≤ N →
      (∀ t ∈ Set.Icc (0:ℝ) R, ‖g t‖ ≤ M) →
      (∀ t ∈ Set.Icc (0:ℝ) R, ‖iteratedDeriv P g t‖ ≤ N) →
      ‖iteratedDeriv j g 0‖ ≤ c * (M / R^j + R^(P-j) * N) :=
  oneD_bound_gen P j hj

open scoped BigOperators in
/-- Near the origin the weight `‖y‖ ^ P` carries no information, but the bound on the
`P`-th derivative together with the decay away from the origin still controls `g` on the
ball of radius `3`. -/
theorem origin_bound (P : ℕ) (hP : 1 ≤ P) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
      (g : EuclideanSpace ℝ (Fin n) → F), ContDiff ℝ ∞ g →
      ∀ (A B : ℝ), 0 ≤ A → 0 ≤ B →
      (∀ y, ‖y‖^P * ‖g y‖ ≤ A) → (∀ y, ‖iteratedFDeriv ℝ P g y‖ ≤ B) →
      ∀ x, ‖x‖ ≤ 3 → ‖g x‖ ≤ C * (A + B) := by
  classical
  let cj : ℕ → ℝ := fun j => if h : j ≤ P then Classical.choose (oneD_bound_gen_zero P j h) else 0
  have hcj : ∀ j (hj : j ≤ P), 0 ≤ cj j ∧ ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
      (g : ℝ → V), ContDiff ℝ (P : ℕ∞ω) g → ∀ (R M N : ℝ), 0 < R → 0 ≤ M → 0 ≤ N →
      (∀ t ∈ Set.Icc (0:ℝ) R, ‖g t‖ ≤ M) →
      (∀ t ∈ Set.Icc (0:ℝ) R, ‖iteratedDeriv P g t‖ ≤ N) →
      ‖iteratedDeriv j g 0‖ ≤ cj j * (M / R^j + R^(P-j) * N) := by
    intro j hj
    have h := Classical.choose_spec (oneD_bound_gen_zero P j hj)
    rw [show cj j = Classical.choose (oneD_bound_gen_zero P j hj) from dif_pos hj]
    exact h
  have hcjnn : ∀ j, 0 ≤ max 1 (cj j) := fun j => le_trans zero_le_one (le_max_left _ _)
  refine ⟨1 + (∑ j ∈ Finset.range P, ((Nat.factorial j : ℝ)⁻¹ * (3:ℝ)^j * max 1 (cj j)))
      + (3:ℝ)^P / ((P-1).factorial : ℝ), ?_, ?_⟩
  · have h1 : 0 ≤ ∑ j ∈ Finset.range P, ((Nat.factorial j : ℝ)⁻¹ * (3:ℝ)^j * max 1 (cj j)) := by
      refine Finset.sum_nonneg fun j _ => ?_
      have h2 : (0:ℝ) ≤ (Nat.factorial j : ℝ)⁻¹ := by positivity
      positivity
    have h3 : 0 ≤ (3:ℝ)^P / ((P-1).factorial : ℝ) := by positivity
    linarith
  · intro F _ _ g hg A B hA hB hAg hBg x hx
    have hC1 : (1:ℝ) ≤ 1 + (∑ j ∈ Finset.range P, ((Nat.factorial j : ℝ)⁻¹ * (3:ℝ)^j * max 1 (cj j)))
        + (3:ℝ)^P / ((P-1).factorial : ℝ) := by
      have h3 : 0 ≤ (3:ℝ)^P / ((P-1).factorial : ℝ) := by positivity
      have h1 : 0 ≤ ∑ j ∈ Finset.range P, ((Nat.factorial j : ℝ)⁻¹ * (3:ℝ)^j * max 1 (cj j)) := by
        refine Finset.sum_nonneg fun j _ => ?_
        have h2 : (0:ℝ) ≤ (Nat.factorial j : ℝ)⁻¹ := by positivity
        positivity
      linarith
    by_cases hx1 : (1:ℝ) ≤ ‖x‖
    · have hxP : (1:ℝ) ≤ ‖x‖^P := one_le_pow₀ hx1
      have hgx : ‖g x‖ ≤ A := by
        have := hAg x
        have h0 : (0:ℝ) ≤ ‖g x‖ := norm_nonneg _
        nlinarith [this, hxP, h0, hA]
      calc ‖g x‖ ≤ A := hgx
        _ ≤ (1 + (∑ j ∈ Finset.range P, ((Nat.factorial j : ℝ)⁻¹ * (3:ℝ)^j * max 1 (cj j)))
              + (3:ℝ)^P / ((P-1).factorial : ℝ)) * (A + B) := by
            have hAB : A ≤ A + B := by linarith
            nlinarith [hC1, hA, hB, hAB]
    · -- ‖x‖ < 1
      obtain ⟨x₁, hx₁⟩ := exists_norm_eq (EuclideanSpace ℝ (Fin n)) (by norm_num : (0:ℝ) ≤ 2)
      have hRpos : 0 < ‖x - x₁‖ := by
        have htr : ‖x₁‖ ≤ ‖x₁ - x‖ + ‖x‖ := by
          have := norm_add_le (x₁ - x) x
          simpa using this
        rw [norm_sub_rev] at htr
        rw [hx₁] at htr
        linarith
      let u : EuclideanSpace ℝ (Fin n) := ‖x - x₁‖⁻¹ • (x - x₁)
      have hu1 : ‖u‖ = 1 := by
        simp only [u, norm_smul, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ ‖x - x₁‖⁻¹)]
        field_simp
      let φ : ℝ → F := fun s => g (x₁ + s • u)
      have hφ : ContDiff ℝ ∞ φ := by
        have h : ContDiff ℝ ∞ (fun s : ℝ => x₁ + s • u) := by fun_prop
        exact hg.comp h
      have hφP : ContDiff ℝ (P : ℕ∞ω) φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
      have hRle : ‖x - x₁‖ ≤ 3 := by
        have := norm_sub_le x x₁
        rw [hx₁] at this
        linarith
      have hphiR : φ ‖x - x₁‖ = g x := by
        simp only [φ]
        have hs : (‖x - x₁‖ : ℝ) • u = x - x₁ := by
          simp only [u, smul_smul, mul_inv_cancel₀ (ne_of_gt hRpos), one_smul]
        rw [hs]
        congr 1
        abel
      have hgb : ∀ s ∈ Set.Icc (0:ℝ) ‖x - x₁‖, ‖iteratedDeriv P φ s‖ ≤ B := by
        intro s _
        exact (norm_iteratedDeriv_line_le g hg x₁ u hu1.le P s).trans (hBg _)
      have hmain := taylor_remainder_bound_V (V := F) (g := φ) (Q := P) hP hφP
        (x₀ := 0) (t := ‖x - x₁‖) (N := B) (le_of_lt hRpos) hB hgb
      have hφ0 : ∀ k, k ≤ P → ‖iteratedDeriv k φ 0‖ ≤ max 1 (cj k) * (A + B) := by
        intro k hkP
        have hk := (hcj k hkP).2 F φ hφP 1 A B one_pos hA hB
          (fun t ht => ?_) (fun t ht => ?_)
        · simp only [one_pow, div_one, one_mul] at hk
          exact hk.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith))
        · rw [Set.mem_Icc] at ht
          have ht1 : ‖t‖ ≤ 1 := by
            rw [Real.norm_eq_abs, abs_le]; exact ⟨by linarith [ht.1], ht.2⟩
          have htu : ‖t • u‖ ≤ 1 := by rw [norm_smul, Real.norm_eq_abs, hu1, mul_one]; exact ht1
          have hbig : (1:ℝ) ≤ ‖x₁ + t • u‖ := by
            have h := norm_sub_le (x₁ + t • u) (t • u)
            rw [add_sub_cancel_right, hx₁] at h
            linarith
          have hP1 : (1:ℝ) ≤ ‖x₁ + t • u‖^P := one_le_pow₀ hbig
          have h0 : (0:ℝ) ≤ ‖g (x₁ + t • u)‖ := norm_nonneg _
          have hmono : ‖g (x₁ + t • u)‖ ≤ ‖x₁ + t • u‖^P * ‖g (x₁ + t • u)‖ := by
            nlinarith [hP1, h0]
          simp only [φ]
          linarith [hAg (x₁ + t • u), hmono]
        · rw [Set.mem_Icc] at ht
          exact (norm_iteratedDeriv_line_le g hg x₁ u hu1.le P t).trans (hBg _)
      have hTaylor : ‖∑ k ∈ Finset.range P,
          ((Nat.factorial k : ℝ)⁻¹ * (‖x - x₁‖)^k) • iteratedDeriv k φ 0‖
          ≤ (∑ j ∈ Finset.range P,
              ((Nat.factorial j : ℝ)⁻¹ * (3:ℝ)^j * max 1 (cj j))) * (A + B) := by
        calc ‖∑ k ∈ Finset.range P,
              ((Nat.factorial k : ℝ)⁻¹ * (‖x - x₁‖)^k) • iteratedDeriv k φ 0‖
            ≤ ∑ k ∈ Finset.range P,
              ‖((Nat.factorial k : ℝ)⁻¹ * (‖x - x₁‖)^k) • iteratedDeriv k φ 0‖ :=
              norm_sum_le _ _
          _ ≤ ∑ k ∈ Finset.range P,
              (Nat.factorial k : ℝ)⁻¹ * (3:ℝ)^k * (max 1 (cj k) * (A + B)) := by
              refine Finset.sum_le_sum fun k hk => ?_
              rw [norm_smul, Real.norm_of_nonneg (by positivity)]
              have hkP : k ≤ P := by
                rw [Finset.mem_range] at hk; omega
              have hrk : (‖x - x₁‖)^k ≤ (3:ℝ)^k := pow_le_pow_left₀ (norm_nonneg _) hRle k
              have hle := hφ0 k hkP
              have hf : (0:ℝ) ≤ (Nat.factorial k : ℝ)⁻¹ := by positivity
              have hD : (0:ℝ) ≤ max 1 (cj k) * (A + B) := by
                have : (0:ℝ) ≤ A + B := by linarith
                positivity
              calc (Nat.factorial k : ℝ)⁻¹ * (‖x - x₁‖)^k * ‖iteratedDeriv k φ 0‖
                  = (Nat.factorial k : ℝ)⁻¹ * ((‖x - x₁‖)^k * ‖iteratedDeriv k φ 0‖) := by ring
                _ ≤ (Nat.factorial k : ℝ)⁻¹ * ((3:ℝ)^k * (max 1 (cj k) * (A + B))) := by
                    exact mul_le_mul_of_nonneg_left
                      (mul_le_mul hrk hle (norm_nonneg _) (by positivity)) hf
                _ = (Nat.factorial k : ℝ)⁻¹ * (3:ℝ)^k * (max 1 (cj k) * (A + B)) := by ring
          _ = (∑ j ∈ Finset.range P,
              ((Nat.factorial j : ℝ)⁻¹ * (3:ℝ)^j * max 1 (cj j))) * (A + B) := by
              rw [Finset.sum_mul]
              exact Finset.sum_congr rfl fun k _ => by ring
      rw [sub_zero] at hmain
      have hrem : ‖φ ‖x - x₁‖ - ∑ k ∈ Finset.range P,
          ((Nat.factorial k : ℝ)⁻¹ * (‖x - x₁‖)^k) • iteratedDeriv k φ 0‖
          ≤ (3:ℝ)^P / ((P-1).factorial : ℝ) * B := by
        refine hmain.trans ?_
        have h0 : (0:ℝ) < ((P-1).factorial : ℝ) := by positivity
        have hrk : (‖x - x₁‖)^P ≤ (3:ℝ)^P := pow_le_pow_left₀ (norm_nonneg _) hRle P
        rw [div_mul_eq_mul_div]
        apply div_le_div_of_nonneg_right _ h0.le
        calc B * ‖x - x₁‖^P = ‖x - x₁‖^P * B := by ring
          _ ≤ 3^P * B := mul_le_mul_of_nonneg_right hrk hB
      calc ‖g x‖ = ‖φ ‖x - x₁‖‖ := by rw [hphiR]
        _ ≤ ‖φ ‖x - x₁‖ - ∑ k ∈ Finset.range P,
              ((Nat.factorial k : ℝ)⁻¹ * (‖x - x₁‖)^k) • iteratedDeriv k φ 0‖
            + ‖∑ k ∈ Finset.range P,
              ((Nat.factorial k : ℝ)⁻¹ * (‖x - x₁‖)^k) • iteratedDeriv k φ 0‖ := by
            have := norm_add_le (φ ‖x - x₁‖ - ∑ k ∈ Finset.range P,
              ((Nat.factorial k : ℝ)⁻¹ * (‖x - x₁‖)^k) • iteratedDeriv k φ 0)
              (∑ k ∈ Finset.range P, ((Nat.factorial k : ℝ)⁻¹ * (‖x - x₁‖)^k) • iteratedDeriv k φ 0)
            simpa using this
        _ ≤ (3:ℝ)^P / ((P-1).factorial : ℝ) * B
            + (∑ j ∈ Finset.range P,
              ((Nat.factorial j : ℝ)⁻¹ * (3:ℝ)^j * max 1 (cj j))) * (A + B) :=
            add_le_add hrem hTaylor
        _ ≤ (1 + (∑ j ∈ Finset.range P, ((Nat.factorial j : ℝ)⁻¹ * (3:ℝ)^j * max 1 (cj j)))
              + (3:ℝ)^P / ((P-1).factorial : ℝ)) * (A + B) := by
            have h0 : (0:ℝ) ≤ (3:ℝ)^P / ((P-1).factorial : ℝ) := by positivity
            have hAB : (0:ℝ) ≤ A + B := by linarith
            have hBA : B ≤ A + B := by linarith
            have hS : (0:ℝ) ≤ ∑ j ∈ Finset.range P,
                ((Nat.factorial j : ℝ)⁻¹ * (3:ℝ)^j * max 1 (cj j)) := by
              refine Finset.sum_nonneg fun j _ => ?_
              have h2 : (0:ℝ) ≤ (Nat.factorial j : ℝ)⁻¹ := by positivity
              positivity
            calc (3:ℝ)^P / ((P-1).factorial : ℝ) * B
                  + (∑ j ∈ Finset.range P,
                      ((Nat.factorial j : ℝ)⁻¹ * (3:ℝ)^j * max 1 (cj j))) * (A + B)
                ≤ (3:ℝ)^P / ((P-1).factorial : ℝ) * (A + B)
                  + (∑ j ∈ Finset.range P,
                      ((Nat.factorial j : ℝ)⁻¹ * (3:ℝ)^j * max 1 (cj j))) * (A + B) :=
                  add_le_add (mul_le_mul_of_nonneg_left hBA h0) (le_refl _)
              _ = ((3:ℝ)^P / ((P-1).factorial : ℝ)
                  + ∑ j ∈ Finset.range P,
                      ((Nat.factorial j : ℝ)⁻¹ * (3:ℝ)^j * max 1 (cj j))) * (A + B) := by
                  rw [add_mul]
              _ ≤ (1 + (∑ j ∈ Finset.range P, ((Nat.factorial j : ℝ)⁻¹ * (3:ℝ)^j * max 1 (cj j)))
                  + (3:ℝ)^P / ((P-1).factorial : ℝ)) * (A + B) := by
                  apply mul_le_mul_of_nonneg_right _ hAB
                  linarith
/-- The base case `b = 1` of the multivariate estimate: the first derivative is
controlled by the weighted bound on `g` and the bound on the `P`-th derivative. -/
theorem G_base (a P : ℕ) (haP : a + 1 ≤ P) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
      (g : EuclideanSpace ℝ (Fin n) → F), ContDiff ℝ ∞ g →
      ∀ (A B : ℝ), 0 ≤ A → 0 ≤ B →
      (∀ y, ‖y‖^P * ‖g y‖ ≤ A) → (∀ y, ‖iteratedFDeriv ℝ P g y‖ ≤ B) →
      ∀ x, ‖x‖^a * ‖iteratedFDeriv ℝ 1 g x‖ ≤ C * (A + B) := by
  have hP1 : 1 ≤ P := by omega
  obtain ⟨C0, hC0nn, hC0⟩ := origin_bound (n := n) P hP1
  obtain ⟨c1, hc1nn, hc1⟩ := oneD_bound_gen_zero P 1 hP1
  refine ⟨max 1 (max (c1 * ((2:ℝ)^P + 1)) (c1 * (C0 + 1) * (2:ℝ)^a)),
    le_trans zero_le_one (le_max_left _ _), ?_⟩
  intro F _ _ g hg A B hA hB hAg hBg x
  have hC0' : ∀ y, ‖y‖ ≤ 3 → ‖g y‖ ≤ C0 * (A + B) := hC0 F g hg A B hA hB hAg hBg
  by_cases hx : (2:ℝ) ≤ ‖x‖
  · have hxpos : (0:ℝ) < ‖x‖ := by linarith
    have hxne : ‖x‖ ≠ 0 := ne_of_gt hxpos
    have hdir : ∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ = 1 →
        ‖fderiv ℝ g x u‖ ≤ c1 * ((2:ℝ)^P * A + B) * (‖x‖⁻¹)^(P-1) := by
      intro u hu
      have hφ : ContDiff ℝ ∞ (fun t : ℝ => g (x + t • u)) := by
        have hlin : ContDiff ℝ ∞ (fun t : ℝ => x + t • u) := by fun_prop
        exact hg.comp hlin
      have hMb : ∀ t ∈ Set.Icc (0:ℝ) ‖x‖⁻¹, ‖g (x + t • u)‖ ≤ (2:ℝ)^P * A / ‖x‖^P := by
        intro t ht
        rw [Set.mem_Icc] at ht
        have htu : ‖t • u‖ ≤ ‖x‖⁻¹ := by
          rw [norm_smul, Real.norm_eq_abs, hu, mul_one, abs_of_nonneg ht.1]; exact ht.2
        have h1 : ‖x‖⁻¹ ≤ ‖x‖ / 2 := by
          rw [inv_le_iff_one_le_mul₀ hxpos]
          nlinarith [hx, norm_nonneg x]
        have hbig : ‖x‖ / 2 ≤ ‖x + t • u‖ := by
          have h2 : ‖x + t • u‖ ≥ ‖x‖ - ‖t • u‖ := by
            have h3 := norm_sub_le (x + t • u) (t • u)
            rw [add_sub_cancel_right] at h3
            linarith
          linarith
        have hle : (‖x‖ / 2)^P ≤ ‖x + t • u‖^P := pow_le_pow_left₀ (by positivity) hbig P
        have hM : (2:ℝ)^P * A / ‖x‖^P = A / (‖x‖ / 2)^P := by
          rw [div_pow]
          field_simp
        rw [hM, le_div_iff₀ (by positivity : (0:ℝ) < (‖x‖ / 2)^P)]
        calc ‖g (x + t • u)‖ * (‖x‖ / 2)^P ≤ ‖g (x + t • u)‖ * ‖x + t • u‖^P :=
              mul_le_mul_of_nonneg_left hle (norm_nonneg _)
          _ ≤ A := by rw [mul_comm]; exact hAg _
      have hNb : ∀ t ∈ Set.Icc (0:ℝ) ‖x‖⁻¹, ‖iteratedDeriv P (fun t : ℝ => g (x + t • u)) t‖ ≤ B := by
        intro t _
        exact (norm_iteratedDeriv_line_le g hg x u hu.le P t).trans (hBg _)
      have h1d := hc1 F (fun t : ℝ => g (x + t • u))
        (hφ.of_le (WithTop.coe_le_coe.mpr le_top)) ‖x‖⁻¹ ((2:ℝ)^P * A / ‖x‖^P) B
        (by positivity) (by positivity) hB hMb hNb
      have h0 : iteratedDeriv 1 (fun t : ℝ => g (x + t • u)) 0 = fderiv ℝ g x u := by
        rw [iteratedDeriv_line g hg x u 1 0]
        simp only [zero_smul, add_zero, iteratedFDeriv_one_apply]
      rw [h0] at h1d
      simp only [pow_one] at h1d
      have h1 : ‖x‖^P * ‖x‖⁻¹ = ‖x‖^(P-1) := by
        rw [pow_sub₀ ‖x‖ hxne hP1, pow_one]
      have hM2 : (2:ℝ)^P * A / ‖x‖^P / ‖x‖⁻¹ = (2:ℝ)^P * A * (‖x‖⁻¹)^(P-1) := by
        rw [div_div, h1, div_eq_mul_inv, inv_pow]
      have heq : c1 * ((2:ℝ)^P * A / ‖x‖^P / ‖x‖⁻¹ + (‖x‖⁻¹)^(P-1) * B)
          = c1 * ((2:ℝ)^P * A + B) * (‖x‖⁻¹)^(P-1) := by
        rw [hM2]; ring
      exact h1d.trans heq.le
    have hop : ‖iteratedFDeriv ℝ 1 g x‖ ≤ c1 * ((2:ℝ)^P * A + B) * (‖x‖⁻¹)^(P-1) := by
      rw [norm_iteratedFDeriv_one]
      refine (ContinuousLinearMap.opNorm_le_iff (by positivity)).mpr ?_
      intro v
      by_cases hv : v = 0
      · simp [hv]
      · have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
        set w : EuclideanSpace ℝ (Fin n) := ‖v‖⁻¹ • v with hw
        have hw1 : ‖w‖ = 1 := by
          rw [hw, norm_smul, Real.norm_of_nonneg (by positivity), inv_mul_cancel₀ (ne_of_gt hvpos)]
        have hvw : v = ‖v‖ • w := by
          rw [hw, smul_smul, mul_inv_cancel₀ (ne_of_gt hvpos), one_smul]
        have hthis : (fderiv ℝ g x) v = ‖v‖ • (fderiv ℝ g x) w := by
          conv_lhs => rw [hvw]
          rw [map_smul]
        rw [hthis, norm_smul, Real.norm_of_nonneg (norm_nonneg v)]
        calc ‖v‖ * ‖(fderiv ℝ g x) w‖ ≤
              ‖v‖ * (c1 * ((2:ℝ)^P * A + B) * (‖x‖⁻¹)^(P-1)) :=
              mul_le_mul_of_nonneg_left (hdir w hw1) (norm_nonneg v)
          _ = c1 * ((2:ℝ)^P * A + B) * (‖x‖⁻¹)^(P-1) * ‖v‖ := by ring
    have hpow : ‖x‖^a * (‖x‖⁻¹)^(P-1) ≤ 1 := by
      rw [inv_pow, ← div_eq_mul_inv, div_le_one₀ (by positivity : (0:ℝ) < ‖x‖^(P-1))]
      exact pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ ‖x‖) (by omega : a ≤ P - 1)
    have hAB : (0:ℝ) ≤ A + B := by linarith
    have hstep1 : ‖x‖^a * ‖iteratedFDeriv ℝ 1 g x‖
        ≤ ‖x‖^a * (c1 * ((2:ℝ)^P * A + B) * (‖x‖⁻¹)^(P-1)) :=
      mul_le_mul_of_nonneg_left hop (pow_nonneg (norm_nonneg x) a)
    have hstep2 : ‖x‖^a * (c1 * ((2:ℝ)^P * A + B) * (‖x‖⁻¹)^(P-1))
        ≤ c1 * ((2:ℝ)^P * A + B) * 1 := by
      rw [show ‖x‖^a * (c1 * ((2:ℝ)^P * A + B) * (‖x‖⁻¹)^(P-1))
            = c1 * ((2:ℝ)^P * A + B) * (‖x‖^a * (‖x‖⁻¹)^(P-1)) from by ring]
      exact mul_le_mul_of_nonneg_left hpow (by positivity)
    have hstep3 : c1 * ((2:ℝ)^P * A + B) * 1
        ≤ max 1 (max (c1 * ((2:ℝ)^P + 1)) (c1 * (C0 + 1) * (2:ℝ)^a)) * (A + B) := by
      rw [mul_one]
      have h2 : (2:ℝ)^P * A + B ≤ ((2:ℝ)^P + 1) * (A + B) := by
        nlinarith [hA, hB, pow_nonneg (by norm_num : (0:ℝ) ≤ 2) P]
      have h3 : c1 * ((2:ℝ)^P * A + B) ≤ c1 * ((2:ℝ)^P + 1) * (A + B) := by
        calc c1 * ((2:ℝ)^P * A + B) ≤ c1 * (((2:ℝ)^P + 1) * (A + B)) :=
              mul_le_mul_of_nonneg_left h2 hc1nn
          _ = c1 * ((2:ℝ)^P + 1) * (A + B) := by ring
      have h4 : c1 * ((2:ℝ)^P + 1)
          ≤ max 1 (max (c1 * ((2:ℝ)^P + 1)) (c1 * (C0 + 1) * (2:ℝ)^a)) :=
        (le_max_left _ _).trans (le_max_right 1 _)
      exact h3.trans (mul_le_mul_of_nonneg_right h4 hAB)
    exact hstep1.trans (hstep2.trans hstep3)
  · have hx2 : ‖x‖ < 2 := lt_of_not_ge hx
    have hdir : ∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ = 1 →
        ‖fderiv ℝ g x u‖ ≤ c1 * (C0 * (A + B) + B) := by
      intro u hu
      have hφ : ContDiff ℝ ∞ (fun t : ℝ => g (x + t • u)) := by
        have hlin : ContDiff ℝ ∞ (fun t : ℝ => x + t • u) := by fun_prop
        exact hg.comp hlin
      have hMb : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖g (x + t • u)‖ ≤ C0 * (A + B) := by
        intro t ht
        rw [Set.mem_Icc] at ht
        refine hC0' (x + t • u) ?_
        have htu : ‖t • u‖ ≤ 1 := by
          rw [norm_smul, Real.norm_eq_abs, hu, mul_one, abs_of_nonneg ht.1]; exact ht.2
        calc ‖x + t • u‖ ≤ ‖x‖ + ‖t • u‖ := norm_add_le _ _
          _ ≤ 2 + 1 := by linarith
          _ = 3 := by norm_num
      have hNb : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖iteratedDeriv P (fun t : ℝ => g (x + t • u)) t‖ ≤ B := by
        intro t _
        exact (norm_iteratedDeriv_line_le g hg x u hu.le P t).trans (hBg _)
      have h1d := hc1 F (fun t : ℝ => g (x + t • u))
        (hφ.of_le (WithTop.coe_le_coe.mpr le_top)) 1 (C0 * (A + B)) B
        one_pos (by positivity) hB hMb hNb
      have h0 : iteratedDeriv 1 (fun t : ℝ => g (x + t • u)) 0 = fderiv ℝ g x u := by
        rw [iteratedDeriv_line g hg x u 1 0]
        simp only [zero_smul, add_zero, iteratedFDeriv_one_apply]
      rw [h0] at h1d
      simpa using h1d
    have hop : ‖iteratedFDeriv ℝ 1 g x‖ ≤ c1 * (C0 * (A + B) + B) := by
      rw [norm_iteratedFDeriv_one]
      refine (ContinuousLinearMap.opNorm_le_iff (by positivity)).mpr ?_
      intro v
      by_cases hv : v = 0
      · simp [hv]
      · have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
        set w : EuclideanSpace ℝ (Fin n) := ‖v‖⁻¹ • v with hw
        have hw1 : ‖w‖ = 1 := by
          rw [hw, norm_smul, Real.norm_of_nonneg (by positivity), inv_mul_cancel₀ (ne_of_gt hvpos)]
        have hvw : v = ‖v‖ • w := by
          rw [hw, smul_smul, mul_inv_cancel₀ (ne_of_gt hvpos), one_smul]
        have hthis : (fderiv ℝ g x) v = ‖v‖ • (fderiv ℝ g x) w := by
          conv_lhs => rw [hvw]
          rw [map_smul]
        rw [hthis, norm_smul, Real.norm_of_nonneg (norm_nonneg v)]
        calc ‖v‖ * ‖(fderiv ℝ g x) w‖ ≤ ‖v‖ * (c1 * (C0 * (A + B) + B)) :=
              mul_le_mul_of_nonneg_left (hdir w hw1) (norm_nonneg v)
          _ = c1 * (C0 * (A + B) + B) * ‖v‖ := by ring
    have hxa : ‖x‖^a ≤ (2:ℝ)^a := pow_le_pow_left₀ (norm_nonneg _) hx2.le a
    have hAB : (0:ℝ) ≤ A + B := by linarith
    have hstep1 : ‖x‖^a * ‖iteratedFDeriv ℝ 1 g x‖ ≤ ‖x‖^a * (c1 * (C0 * (A + B) + B)) :=
      mul_le_mul_of_nonneg_left hop (pow_nonneg (norm_nonneg x) a)
    have hstep2 : ‖x‖^a * (c1 * (C0 * (A + B) + B)) ≤ (2:ℝ)^a * (c1 * (C0 * (A + B) + B)) :=
      mul_le_mul_of_nonneg_right hxa (by positivity)
    have hstep3 : (2:ℝ)^a * (c1 * (C0 * (A + B) + B))
        ≤ max 1 (max (c1 * ((2:ℝ)^P + 1)) (c1 * (C0 + 1) * (2:ℝ)^a)) * (A + B) := by
      have h2 : C0 * (A + B) + B ≤ (C0 + 1) * (A + B) := by nlinarith [hA, hB, hC0nn]
      have h3 : c1 * (C0 * (A + B) + B) ≤ c1 * (C0 + 1) * (A + B) := by
        calc c1 * (C0 * (A + B) + B) ≤ c1 * ((C0 + 1) * (A + B)) :=
              mul_le_mul_of_nonneg_left h2 hc1nn
          _ = c1 * (C0 + 1) * (A + B) := by ring
      have h4 : (2:ℝ)^a * (c1 * (C0 + 1) * (A + B))
          ≤ (c1 * (C0 + 1) * (2:ℝ)^a) * (A + B) := by
        rw [show (2:ℝ)^a * (c1 * (C0 + 1) * (A + B))
            = (c1 * (C0 + 1) * (2:ℝ)^a) * (A + B) from by ring]
      have h5 : c1 * (C0 + 1) * (2:ℝ)^a
          ≤ max 1 (max (c1 * ((2:ℝ)^P + 1)) (c1 * (C0 + 1) * (2:ℝ)^a)) :=
        (le_max_right _ _).trans (le_max_right 1 _)
      calc (2:ℝ)^a * (c1 * (C0 * (A + B) + B))
          ≤ (2:ℝ)^a * (c1 * (C0 + 1) * (A + B)) :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
        _ ≤ (c1 * (C0 + 1) * (2:ℝ)^a) * (A + B) := h4
        _ ≤ max 1 (max (c1 * ((2:ℝ)^P + 1)) (c1 * (C0 + 1) * (2:ℝ)^a)) * (A + B) :=
            mul_le_mul_of_nonneg_right h5 hAB
    exact hstep1.trans (hstep2.trans hstep3)
/-- The multivariate estimate, by induction on the order `b ≥ 1`. -/
theorem G_all : ∀ (b : ℕ), 1 ≤ b → ∀ (a P : ℕ), a + b ≤ P → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
      (g : EuclideanSpace ℝ (Fin n) → F), ContDiff ℝ ∞ g →
      ∀ (A B : ℝ), 0 ≤ A → 0 ≤ B →
      (∀ y, ‖y‖^P * ‖g y‖ ≤ A) → (∀ y, ‖iteratedFDeriv ℝ P g y‖ ≤ B) →
      ∀ x, ‖x‖^a * ‖iteratedFDeriv ℝ b g x‖ ≤ C * (A + B) := by
  intro b hb
  induction b, hb using Nat.le_induction with
  | base =>
      intro a P haP
      exact G_base (n := n) a P haP
  | succ b hb ih =>
      intro a P haP
      obtain ⟨C0, hC0nn, hC0⟩ := G_base (n := n) (P - 1) P (by omega)
      obtain ⟨C1, hC1nn, hC1⟩ := ih a (P - 1) (by omega)
      refine ⟨C1 * (C0 + 1), by positivity, ?_⟩
      intro F _ _ g hg A B hA hB hAg hBg x
      have hg' : ContDiff ℝ ∞ (fderiv ℝ g) := (contDiff_infty_iff_fderiv.mp hg).2
      have hA' : (0:ℝ) ≤ C0 * (A + B) := by positivity
      have hDg : ∀ y, ‖y‖^(P-1) * ‖fderiv ℝ g y‖ ≤ C0 * (A + B) := by
        intro y
        rw [← norm_iteratedFDeriv_one]
        exact hC0 F g hg A B hA hB hAg hBg y
      have hDPh : ∀ y, ‖iteratedFDeriv ℝ (P-1) (fderiv ℝ g) y‖ ≤ B := by
        intro y
        rw [norm_iteratedFDeriv_fderiv]
        rw [show (P - 1) + 1 = P from by omega]
        exact hBg y
      have hmain := hC1 (EuclideanSpace ℝ (Fin n) →L[ℝ] F) (fderiv ℝ g) hg' (C0 * (A + B)) B hA' hB hDg hDPh x
      have hnorm : ‖iteratedFDeriv ℝ (b+1) g x‖ = ‖iteratedFDeriv ℝ b (fderiv ℝ g) x‖ :=
        (norm_iteratedFDeriv_fderiv (f := g) (x := x) (n := b)).symm
      rw [hnorm]
      refine hmain.trans ?_
      have h2 : C0 * (A + B) + B ≤ (C0 + 1) * (A + B) := by nlinarith [hA, hB, hC0nn]
      calc C1 * (C0 * (A + B) + B) ≤ C1 * ((C0 + 1) * (A + B)) :=
            mul_le_mul_of_nonneg_left h2 hC1nn
        _ = C1 * (C0 + 1) * (A + B) := by ring
/-- The weighted seminorm bound for all orders `b`, uniform in the pair `(a, b)`. -/
theorem seminorm_bound_aux (P : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
      (g : EuclideanSpace ℝ (Fin n) → F), ContDiff ℝ ∞ g →
      ∀ (A B : ℝ), 0 ≤ A → 0 ≤ B →
      (∀ y, ‖y‖^P * ‖g y‖ ≤ A) → (∀ y, ‖iteratedFDeriv ℝ P g y‖ ≤ B) →
      ∀ (a b : ℕ), a + b ≤ P → ∀ x, ‖x‖^a * ‖iteratedFDeriv ℝ b g x‖ ≤ C * (A + B) := by
  classical
  rcases Nat.eq_zero_or_pos P with hP0 | hPpos
  · subst hP0
    refine ⟨1, zero_le_one, ?_⟩
    intro F _ _ g hg A B hA hB hAg hBg a b hab x
    have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst ha; subst hb
    rw [pow_zero, norm_iteratedFDeriv_zero, one_mul]
    calc ‖g x‖ ≤ A := by simpa using hAg x
      _ ≤ 1 * (A + B) := by linarith
  · obtain ⟨C0, hC0nn, hC0⟩ := origin_bound (n := n) P hPpos
    let K : ℕ → ℕ → ℝ := fun a b => dite (1 ≤ b ∧ a + b ≤ P)
      (fun h => Classical.choose (G_all (n := n) b h.1 a P h.2)) (fun _ => 0)
    have hKnn : ∀ a b, 0 ≤ K a b := by
      intro a b
      by_cases h : 1 ≤ b ∧ a + b ≤ P
      · rw [show K a b = Classical.choose (G_all (n := n) b h.1 a P h.2) from dif_pos h]
        exact (Classical.choose_spec (G_all (n := n) b h.1 a P h.2)).1
      · rw [show K a b = 0 from dif_neg h]
    have hKspec : ∀ a b (h : 1 ≤ b ∧ a + b ≤ P),
        ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
          (g : EuclideanSpace ℝ (Fin n) → F), ContDiff ℝ ∞ g →
          ∀ (A B : ℝ), 0 ≤ A → 0 ≤ B →
          (∀ y, ‖y‖^P * ‖g y‖ ≤ A) → (∀ y, ‖iteratedFDeriv ℝ P g y‖ ≤ B) →
          ∀ x, ‖x‖^a * ‖iteratedFDeriv ℝ b g x‖ ≤ K a b * (A + B) := by
      intro a b h
      have hspec := (Classical.choose_spec (G_all (n := n) b h.1 a P h.2)).2
      rw [show K a b = Classical.choose (G_all (n := n) b h.1 a P h.2) from dif_pos h]
      exact hspec
    refine ⟨1 + C0 + ∑ b ∈ Finset.range (P+1), ∑ a ∈ Finset.range (P+1), K a b, ?_, ?_⟩
    · refine add_nonneg (add_nonneg zero_le_one hC0nn) ?_
      exact Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun a _ => hKnn a b
    · intro F _ _ g hg A B hA hB hAg hBg a b hab x
      have hAB : (0:ℝ) ≤ A + B := by linarith
      have hCnn : (0:ℝ) ≤ 1 + C0 + ∑ b' ∈ Finset.range (P+1), ∑ a' ∈ Finset.range (P+1), K a' b' :=
        add_nonneg (add_nonneg zero_le_one hC0nn)
          (Finset.sum_nonneg fun b' _ => Finset.sum_nonneg fun a' _ => hKnn a' b')
      rcases Nat.eq_zero_or_pos b with hb0 | hbpos
      · subst hb0
        rw [norm_iteratedFDeriv_zero]
        have haP : a ≤ P := by omega
        by_cases hx : (1:ℝ) ≤ ‖x‖
        · have hgx : ‖g x‖ ≤ A / ‖x‖^P := by
            rw [le_div_iff₀ (by positivity : (0:ℝ) < ‖x‖^P)]
            calc ‖g x‖ * ‖x‖^P = ‖x‖^P * ‖g x‖ := by ring
              _ ≤ A := hAg x
          have h1 : ‖x‖^a * (A / ‖x‖^P) ≤ A := by
            rw [← mul_div_assoc, div_le_iff₀ (by positivity : (0:ℝ) < ‖x‖^P)]
            calc ‖x‖^a * A ≤ ‖x‖^P * A :=
                  mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hx haP) hA
              _ = A * ‖x‖^P := by ring
          calc ‖x‖^a * ‖g x‖ ≤ ‖x‖^a * (A / ‖x‖^P) :=
                mul_le_mul_of_nonneg_left hgx (pow_nonneg (norm_nonneg x) a)
            _ ≤ A := h1
            _ ≤ (1 + C0 + ∑ b' ∈ Finset.range (P+1), ∑ a' ∈ Finset.range (P+1), K a' b')
                  * (A + B) := by
                have h1' : (1:ℝ) ≤ 1 + C0 + ∑ b' ∈ Finset.range (P+1),
                    ∑ a' ∈ Finset.range (P+1), K a' b' := by
                  have h2 : (0:ℝ) ≤ C0 + ∑ b' ∈ Finset.range (P+1),
                      ∑ a' ∈ Finset.range (P+1), K a' b' :=
                    add_nonneg hC0nn (Finset.sum_nonneg fun b' _ =>
                      Finset.sum_nonneg fun a' _ => hKnn a' b')
                  linarith
                calc A ≤ 1 * (A + B) := by linarith
                  _ ≤ (1 + C0 + ∑ b' ∈ Finset.range (P+1), ∑ a' ∈ Finset.range (P+1), K a' b')
                        * (A + B) := mul_le_mul_of_nonneg_right h1' hAB
        · have hx2 : ‖x‖ < 1 := lt_of_not_ge hx
          have hgx : ‖g x‖ ≤ C0 * (A + B) :=
            hC0 F g hg A B hA hB hAg hBg x (by linarith)
          have hxa : ‖x‖^a ≤ 1 := pow_le_one₀ (norm_nonneg _) hx2.le
          calc ‖x‖^a * ‖g x‖ ≤ 1 * (C0 * (A + B)) :=
                mul_le_mul hxa hgx (norm_nonneg _) (by norm_num)
            _ ≤ (1 + C0 + ∑ b' ∈ Finset.range (P+1), ∑ a' ∈ Finset.range (P+1), K a' b')
                  * (A + B) := by
                have h1' : C0 + 0 ≤ 1 + C0 + ∑ b' ∈ Finset.range (P+1),
                    ∑ a' ∈ Finset.range (P+1), K a' b' := by
                  have h2 : (0:ℝ) ≤ ∑ b' ∈ Finset.range (P+1),
                      ∑ a' ∈ Finset.range (P+1), K a' b' :=
                    Finset.sum_nonneg fun b' _ => Finset.sum_nonneg fun a' _ => hKnn a' b'
                  linarith
                calc (1:ℝ) * (C0 * (A + B)) = C0 * (A + B) := by ring
                  _ ≤ (1 + C0 + ∑ b' ∈ Finset.range (P+1), ∑ a' ∈ Finset.range (P+1), K a' b')
                        * (A + B) := by
                      apply mul_le_mul_of_nonneg_right _ hAB
                      have h2 : (0:ℝ) ≤ ∑ b' ∈ Finset.range (P+1),
                          ∑ a' ∈ Finset.range (P+1), K a' b' :=
                        Finset.sum_nonneg fun b' _ => Finset.sum_nonneg fun a' _ => hKnn a' b'
                      linarith
      · have hK := hKspec a b ⟨hbpos, hab⟩ F g hg A B hA hB hAg hBg x
        have haP : a ≤ P := by omega
        have hbP : b ≤ P := by omega
        have hle_inner : K a b ≤ ∑ a' ∈ Finset.range (P+1), K a' b :=
          Finset.single_le_sum (fun a' _ => hKnn a' b) (Finset.mem_range.mpr (by omega))
        have hle : K a b ≤ ∑ b' ∈ Finset.range (P+1), ∑ a' ∈ Finset.range (P+1), K a' b' :=
          hle_inner.trans (Finset.single_le_sum
            (fun b' _ => Finset.sum_nonneg fun a' _ => hKnn a' b')
            (Finset.mem_range.mpr (by omega)))
        refine hK.trans ?_
        have h1' : K a b ≤ 1 + C0 + ∑ b' ∈ Finset.range (P+1),
            ∑ a' ∈ Finset.range (P+1), K a' b' := by
          have h2 : (0:ℝ) ≤ 1 + C0 := by linarith
          linarith
        exact mul_le_mul_of_nonneg_right h1' hAB
end Work.FunctionalEquations
