import Mathlib
import Submission.Work.Kernels.All
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Asymptotics.Xi8_eq
import Submission.Work.Asymptotics.Xi24_eq

namespace Work.Asymptotics

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

noncomputable section

/-! ## Toolbox -/

/-- `‖a·b·c‖ ≤ A·B·C` from `‖a‖ ≤ A`, `‖b‖ ≤ B`, `‖c‖ ≤ C`. -/
private lemma norm_mul_mul_le {a b c : ℂ} {A B C : ℝ} (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B)
    (hc : ‖c‖ ≤ C) : ‖a * b * c‖ ≤ A * B * C := by
  rw [norm_mul, norm_mul]
  have h1 : ‖a‖ * ‖b‖ ≤ A * B := mul_le_mul ha hb (norm_nonneg b) (le_trans (norm_nonneg a) ha)
  have h2 : (0 : ℝ) ≤ A * B := le_trans (mul_nonneg (norm_nonneg _) (norm_nonneg _)) h1
  calc ‖a‖ * ‖b‖ * ‖c‖ ≤ A * B * ‖c‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ ≤ A * B * C := mul_le_mul_of_nonneg_left hc h2

/-- `‖a·b·c·d‖ ≤ A·B·C·D` from the four component bounds. -/
private lemma norm_mul_mul_mul_le {a b c d : ℂ} {A B C D : ℝ} (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B)
    (hc : ‖c‖ ≤ C) (hd : ‖d‖ ≤ D) : ‖a * b * c * d‖ ≤ A * B * C * D := by
  have h3 : ‖a * b * c‖ ≤ A * B * C := norm_mul_mul_le ha hb hc
  rw [norm_mul]
  exact mul_le_mul h3 hd (norm_nonneg d) (le_trans (norm_nonneg (a * b * c)) h3)

/-! ## Auxiliary cusp estimates for `Ξ₂₄` -/

/-- `E₆ - E₄E₂ = -720 q + O(q²)`. -/
private lemma E6_sub_E4E2_two_term :
    IsBigOq (fun τ => Work.Kernels.E6Fun τ - Work.Kernels.E4Fun τ * Work.Kernels.E2Fun τ
      + 720 * Work.Kernels.qParamFun τ) 2 := by
  have h_u : IsBigOq (fun τ => Work.Kernels.E4Fun τ - 1 - 240 * Work.Kernels.qParamFun τ) 2 :=
    E4Fun_isBigOq
  have h_v : IsBigOq (fun τ => Work.Kernels.E2Fun τ - 1 + 24 * Work.Kernels.qParamFun τ) 2 :=
    E2Fun_isBigOq
  have h_w : IsBigOq (fun τ => Work.Kernels.E6Fun τ - 1 + 504 * Work.Kernels.qParamFun τ) 2 :=
    E6Fun_isBigOq
  have h1 : IsBigOq (fun τ => (Work.Kernels.E4Fun τ - 1 - 240 * Work.Kernels.qParamFun τ)
      * (1 + (-24) * Work.Kernels.qParamFun τ)) 2 :=
    h_u.mul (isBigOq_one_add_const_mul_q (-24))
  have h2 : IsBigOq (fun τ => (Work.Kernels.E2Fun τ - 1 + 24 * Work.Kernels.qParamFun τ)
      * (1 + 240 * Work.Kernels.qParamFun τ)) 2 :=
    h_v.mul (isBigOq_one_add_const_mul_q 240)
  have h3 : IsBigOq (fun τ => (Work.Kernels.E4Fun τ - 1 - 240 * Work.Kernels.qParamFun τ)
      * (Work.Kernels.E2Fun τ - 1 + 24 * Work.Kernels.qParamFun τ)) 2 :=
    IsBigOq.mono (h_u.mul h_v) (by norm_num)
  have h4 : IsBigOq (fun τ => (5760 : ℂ) * Work.Kernels.qParamFun τ ^ 2) 2 :=
    qParamFun_sq_isBigOq.const_mul 5760
  refine ((((h_w.add h1.neg).add h2.neg).add h3.neg).add h4).congr (fun τ => ?_)
  ring

/-- `1728 E₂² Δ - 6 E₄³(E₄ - E₂²) = O(q²)`. -/
private lemma Xi24_aux_N0 :
    IsBigOq (fun τ => 1728 * Work.Kernels.E2Fun τ ^ 2 * Work.Kernels.DeltaFun τ
      - 6 * Work.Kernels.E4Fun τ ^ 3
        * (Work.Kernels.E4Fun τ - Work.Kernels.E2Fun τ ^ 2)) 2 :=
  (E4cube_delta1_minus_E2sqDelta.const_mul (-6)).congr (fun τ => by ring)

/-- `1728 E₄ Δ - 6 E₄³(E₄ - E₂²) = O(q²)`. -/
private lemma Xi24_aux_N2 :
    IsBigOq (fun τ => 1728 * Work.Kernels.E4Fun τ * Work.Kernels.DeltaFun τ
      - 6 * Work.Kernels.E4Fun τ ^ 3
        * (Work.Kernels.E4Fun τ - Work.Kernels.E2Fun τ ^ 2)) 2 := by
  have h1 : IsBigOq (fun τ => 1728 * (Work.Kernels.DeltaFun τ
      * (Work.Kernels.E4Fun τ - 1))) 2 :=
    (DeltaFun_isBigOq_one.mul E4_minus_one).const_mul 1728
  refine ((E4cube_delta1_minus_Delta.const_mul (-6)).add h1).congr (fun τ => ?_)
  ring

/-- `12 E₄³(E₄ - E₂²) + 1728 Δ (5E₄ - 7E₂²) = O(q²)`. -/
private lemma Xi24_aux_U :
    IsBigOq (fun τ => 12 * Work.Kernels.E4Fun τ ^ 3
        * (Work.Kernels.E4Fun τ - Work.Kernels.E2Fun τ ^ 2)
      + 1728 * Work.Kernels.DeltaFun τ
        * (5 * Work.Kernels.E4Fun τ - 7 * Work.Kernels.E2Fun τ ^ 2)) 2 := by
  have hlin : IsBigOq (fun τ => 2 + 5 * Work.Kernels.E4Fun τ
      - 7 * Work.Kernels.E2Fun τ ^ 2) 1 := by
    have h := (E4_minus_one.const_mul 5).add (E2sq_minus_one.const_mul (-7))
    refine (IsBigOq.mono h (le_refl 1)).congr (fun τ => ?_)
    ring
  have h2 : IsBigOq (fun τ => 1728 * (Work.Kernels.DeltaFun τ
      * (2 + 5 * Work.Kernels.E4Fun τ - 7 * Work.Kernels.E2Fun τ ^ 2))) 2 :=
    (DeltaFun_isBigOq_one.mul hlin).const_mul 1728
  refine ((E4cube_delta1_minus_Delta.const_mul 12).add h2).congr (fun τ => ?_)
  ring

/-- `5E₄² - 7E₄E₂² + 2E₆E₂ = O(q²)`. -/
private lemma Xi24_aux_R :
    IsBigOq (fun τ => 5 * Work.Kernels.E4Fun τ ^ 2
      - 7 * Work.Kernels.E4Fun τ * Work.Kernels.E2Fun τ ^ 2
      + 2 * Work.Kernels.E6Fun τ * Work.Kernels.E2Fun τ) 2 := by
  have h1 : IsBigOq (fun τ => 5 * (Work.Kernels.E4Fun τ ^ 2
      - Work.Kernels.E6Fun τ * Work.Kernels.E2Fun τ
      - 1008 * Work.Kernels.qParamFun τ)) 2 := eps_two_term.const_mul 5
  have h2 : IsBigOq (fun τ => 7 * Work.Kernels.E2Fun τ * (Work.Kernels.E6Fun τ
      - Work.Kernels.E4Fun τ * Work.Kernels.E2Fun τ
      + 720 * Work.Kernels.qParamFun τ)) 2 :=
    ((E2Fun_bdd.mul E6_sub_E4E2_two_term).const_mul 7).congr (fun τ => by ring)
  have h3 : IsBigOq (fun τ => -5040 * (Work.Kernels.E2Fun τ - 1)
      * Work.Kernels.qParamFun τ) 2 :=
    ((E2_minus_one.mul qParamFun_isBigOq).const_mul (-5040)).congr (fun τ => by ring)
  refine ((h1.add h2).add h3).congr (fun τ => ?_)
  ring

/-! ## The row identities for `Ξ₂₄`

With `A = E₄(z)`, `B = E₆(z)`, `C = E₂(z)`, `D = Δ(z)`, `j = j(τ)`, `jz = j(z)` and `D·jz = A³`,
the three rows of the matrix of `Ξ₂₄` are combinations of the small quantities
`σ = A - C²`, `R = 5A²-7AC²+2BC`, `U = 12A³σ + 1728D(5A-7C²)`, `N₀`, `N₂`, all divided by `D`. -/

private lemma Xi24_row0_aux {A C D j jz : ℂ} (hD : D ≠ 0) (hjz : D * jz = A ^ 3) :
    6 * (j - jz) * A + (1728 - 6 * (j - jz)) * C ^ 2
      = (6 * j * (A - C ^ 2) * D + (1728 * C ^ 2 * D - 6 * A ^ 3 * (A - C ^ 2))) / D := by
  have hj : jz = A ^ 3 / D := by rw [eq_div_iff hD, mul_comm]; exact hjz
  rw [hj]
  field_simp
  ring

private lemma Xi24_row2_aux {A C D j jz : ℂ} (hD : D ≠ 0) (hjz : D * jz = A ^ 3) :
    (1728 + 6 * (j - jz)) * A - 6 * (j - jz) * C ^ 2
      = (6 * j * (A - C ^ 2) * D + (1728 * A * D - 6 * A ^ 3 * (A - C ^ 2))) / D := by
  have hj : jz = A ^ 3 / D := by rw [eq_div_iff hD, mul_comm]; exact hjz
  rw [hj]
  field_simp
  ring

private lemma Xi24_row1_aux {A B C D j jz : ℂ} (hD : D ≠ 0) (hjz : D * jz = A ^ 3) :
    (-12 * j * (j - jz) + 5 * 1728 * (j - jz)) * A
      + (-2 * 1728) * (A ^ 2 * B / D) * C
      + (12 * j * (j - jz) - 7 * 1728 * (j - jz)) * C ^ 2
    = (-12 * j ^ 2 * (A - C ^ 2) * D
        + j * (12 * A ^ 3 * (A - C ^ 2) + 1728 * D * (5 * A - 7 * C ^ 2))
        - 1728 * A ^ 2 * (5 * A ^ 2 - 7 * A * C ^ 2 + 2 * B * C)) / D := by
  have hj : jz = A ^ 3 / D := by rw [eq_div_iff hD, mul_comm]; exact hjz
  rw [hj]
  field_simp
  ring

/-! ## The numerator `Ξ₈` is `O(q)` on the closed ball -/

theorem Xi8_bound (τ₀ : ℍ) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ z : ℍ, dist τ τ₀ ≤ R → 1 ≤ z.im →
      ‖Xi8 τ z‖ ≤ C * ‖Work.Kernels.qParamFun z‖ := by
  obtain ⟨M, hM, hb⟩ := ball_factor_bounds τ₀ R
  obtain ⟨Cd, hCd, hd⟩ := DeltaFun_isBigOq_one
  obtain ⟨Cδ, hCδ, hδ⟩ := delta1_isBigOq
  obtain ⟨Cε, hCε, hε⟩ := eps_isBigOq
  obtain ⟨C4, hC4, hE4b⟩ := E4Fun_bdd
  refine ⟨M * M * (Cd * M + C4 * C4 * Cδ) + M * M * (2 * Cd * M + 2 * C4 * Cε)
      + M * M * Cd + 1, by positivity, fun τ z hτ hz => ?_⟩
  obtain ⟨hjτ, hphi0, hphi1, hphi2, hfk2, hfk4, hfk6, hfk10, hfk12, hfk14⟩ := hb τ hτ
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
  have hΔz : ‖Work.Kernels.DeltaFun z‖ ≤ Cd * ‖Work.Kernels.qParamFun z‖ := by
    simpa using hd z hz
  have hσ : ‖Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2‖
      ≤ Cδ * ‖Work.Kernels.qParamFun z‖ := by simpa using hδ z hz
  have heps : ‖Work.Kernels.E4Fun z ^ 2 - Work.Kernels.E6Fun z * Work.Kernels.E2Fun z‖
      ≤ Cε * ‖Work.Kernels.qParamFun z‖ := by simpa using hε z hz
  have hA : ‖Work.Kernels.E4Fun z‖ ≤ C4 := by simpa using hE4b z hz
  have hXi : Xi8 τ z
      = Work.Kernels.phiVec τ 0 * Work.Kernels.fk 6 τ
          * (Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ
              - Work.Kernels.E4Fun z ^ 2 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2))
        + Work.Kernels.phiVec τ 1 * Work.Kernels.fk 4 τ
          * (2 * (Work.Kernels.E4Fun z * (Work.Kernels.E4Fun z ^ 2
              - Work.Kernels.E6Fun z * Work.Kernels.E2Fun z))
            - 2 * (Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ))
        + Work.Kernels.phiVec τ 2 * Work.Kernels.fk 2 τ * Work.Kernels.DeltaFun z := by
    have hJ : Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun z = Work.Kernels.E4Fun z ^ 3 :=
      Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun z
    have hΔ : Work.Kernels.DeltaFun z ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z
    have hjz : Work.Kernels.jInvariantFun z = Work.Kernels.E4Fun z ^ 3 / Work.Kernels.DeltaFun z := by
      rw [eq_div_iff hΔ, mul_comm]; exact hJ
    have hfk12 : Work.Kernels.fk (12 : ℤ) z = Work.Kernels.DeltaFun z := rfl
    have hfk10 : Work.Kernels.fk (10 : ℤ) z = Work.Kernels.E10Fun z := rfl
    have hfk8 : Work.Kernels.fk (8 : ℤ) z = Work.Kernels.E8Fun z := rfl
    simp only [Xi8, Fin.sum_univ_three, Work.Kernels.phiVec, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply,
      Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, mul_one]
    rw [hfk12, hfk10, hfk8, hjz]
    field_simp
    ring
  rw [hXi]
  have t1 : ‖Work.Kernels.phiVec τ 0 * Work.Kernels.fk 6 τ
      * (Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ
          - Work.Kernels.E4Fun z ^ 2 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2))‖
      ≤ M * M * (Cd * M + C4 * C4 * Cδ) * ‖Work.Kernels.qParamFun z‖ := by
    have ha : ‖Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ‖
        ≤ Cd * M * ‖Work.Kernels.qParamFun z‖ := by
      rw [norm_mul]
      calc ‖Work.Kernels.DeltaFun z‖ * ‖Work.Kernels.jInvariantFun τ‖
          ≤ (Cd * ‖Work.Kernels.qParamFun z‖) * M :=
            mul_le_mul hΔz hjτ (norm_nonneg _) (by positivity)
        _ = Cd * M * ‖Work.Kernels.qParamFun z‖ := by ring
    have hb2 : ‖Work.Kernels.E4Fun z ^ 2 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2)‖
        ≤ C4 * C4 * Cδ * ‖Work.Kernels.qParamFun z‖ := by
      have h4sq : ‖Work.Kernels.E4Fun z ^ 2‖ ≤ C4 * C4 := by
        rw [norm_pow, pow_two]; exact mul_le_mul hA hA (norm_nonneg _) hC4.le
      rw [norm_mul]
      calc ‖Work.Kernels.E4Fun z ^ 2‖ * ‖Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2‖
          ≤ (C4 * C4) * (Cδ * ‖Work.Kernels.qParamFun z‖) :=
            mul_le_mul h4sq hσ (norm_nonneg _) (by positivity)
        _ = C4 * C4 * Cδ * ‖Work.Kernels.qParamFun z‖ := by ring
    have hinner : ‖Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ
        - Work.Kernels.E4Fun z ^ 2 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2)‖
        ≤ (Cd * M + C4 * C4 * Cδ) * ‖Work.Kernels.qParamFun z‖ := by
      calc ‖Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ
              - Work.Kernels.E4Fun z ^ 2 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2)‖
          ≤ ‖Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ‖
            + ‖Work.Kernels.E4Fun z ^ 2 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2)‖ :=
            norm_sub_le _ _
        _ ≤ Cd * M * ‖Work.Kernels.qParamFun z‖ + C4 * C4 * Cδ * ‖Work.Kernels.qParamFun z‖ :=
            add_le_add ha hb2
        _ = (Cd * M + C4 * C4 * Cδ) * ‖Work.Kernels.qParamFun z‖ := by ring
    calc ‖Work.Kernels.phiVec τ 0 * Work.Kernels.fk 6 τ
            * (Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ
                - Work.Kernels.E4Fun z ^ 2 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2))‖
        ≤ M * M * ((Cd * M + C4 * C4 * Cδ) * ‖Work.Kernels.qParamFun z‖) :=
          norm_mul_mul_le hphi0 hfk6 hinner
      _ = M * M * (Cd * M + C4 * C4 * Cδ) * ‖Work.Kernels.qParamFun z‖ := by ring
  have t2 : ‖Work.Kernels.phiVec τ 1 * Work.Kernels.fk 4 τ
      * (2 * (Work.Kernels.E4Fun z * (Work.Kernels.E4Fun z ^ 2
            - Work.Kernels.E6Fun z * Work.Kernels.E2Fun z))
          - 2 * (Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ))‖
      ≤ M * M * (2 * Cd * M + 2 * C4 * Cε) * ‖Work.Kernels.qParamFun z‖ := by
    have ha : ‖(2 : ℂ) * (Work.Kernels.E4Fun z * (Work.Kernels.E4Fun z ^ 2
            - Work.Kernels.E6Fun z * Work.Kernels.E2Fun z))‖
        ≤ 2 * C4 * Cε * ‖Work.Kernels.qParamFun z‖ := by
      rw [norm_mul, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
      calc 2 * (‖Work.Kernels.E4Fun z‖
            * ‖Work.Kernels.E4Fun z ^ 2 - Work.Kernels.E6Fun z * Work.Kernels.E2Fun z‖)
          ≤ 2 * (C4 * (Cε * ‖Work.Kernels.qParamFun z‖)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hA heps (norm_nonneg _) hC4.le) (by norm_num)
        _ = 2 * C4 * Cε * ‖Work.Kernels.qParamFun z‖ := by ring
    have hb2 : ‖(2 : ℂ) * (Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ)‖
        ≤ 2 * Cd * M * ‖Work.Kernels.qParamFun z‖ := by
      rw [norm_mul, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
      calc 2 * (‖Work.Kernels.DeltaFun z‖ * ‖Work.Kernels.jInvariantFun τ‖)
          ≤ 2 * ((Cd * ‖Work.Kernels.qParamFun z‖) * M) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hΔz hjτ (norm_nonneg _) (by positivity))
              (by norm_num)
        _ = 2 * Cd * M * ‖Work.Kernels.qParamFun z‖ := by ring
    have hinner : ‖2 * (Work.Kernels.E4Fun z * (Work.Kernels.E4Fun z ^ 2
            - Work.Kernels.E6Fun z * Work.Kernels.E2Fun z))
          - 2 * (Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ)‖
        ≤ (2 * Cd * M + 2 * C4 * Cε) * ‖Work.Kernels.qParamFun z‖ := by
      calc ‖2 * (Work.Kernels.E4Fun z * (Work.Kernels.E4Fun z ^ 2
              - Work.Kernels.E6Fun z * Work.Kernels.E2Fun z))
            - 2 * (Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ)‖
          ≤ ‖(2 : ℂ) * (Work.Kernels.E4Fun z * (Work.Kernels.E4Fun z ^ 2
              - Work.Kernels.E6Fun z * Work.Kernels.E2Fun z))‖
            + ‖(2 : ℂ) * (Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ)‖ :=
            norm_sub_le _ _
        _ ≤ 2 * C4 * Cε * ‖Work.Kernels.qParamFun z‖ + 2 * Cd * M * ‖Work.Kernels.qParamFun z‖ :=
            add_le_add ha hb2
        _ = (2 * Cd * M + 2 * C4 * Cε) * ‖Work.Kernels.qParamFun z‖ := by ring
    calc ‖Work.Kernels.phiVec τ 1 * Work.Kernels.fk 4 τ
            * (2 * (Work.Kernels.E4Fun z * (Work.Kernels.E4Fun z ^ 2
                  - Work.Kernels.E6Fun z * Work.Kernels.E2Fun z))
                - 2 * (Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ))‖
        ≤ M * M * ((2 * Cd * M + 2 * C4 * Cε) * ‖Work.Kernels.qParamFun z‖) :=
          norm_mul_mul_le hphi1 hfk4 hinner
      _ = M * M * (2 * Cd * M + 2 * C4 * Cε) * ‖Work.Kernels.qParamFun z‖ := by ring
  have t3 : ‖Work.Kernels.phiVec τ 2 * Work.Kernels.fk 2 τ * Work.Kernels.DeltaFun z‖
      ≤ M * M * Cd * ‖Work.Kernels.qParamFun z‖ := by
    calc ‖Work.Kernels.phiVec τ 2 * Work.Kernels.fk 2 τ * Work.Kernels.DeltaFun z‖
        ≤ M * M * (Cd * ‖Work.Kernels.qParamFun z‖) := norm_mul_mul_le hphi2 hfk2 hΔz
      _ = M * M * Cd * ‖Work.Kernels.qParamFun z‖ := by ring
  have hsum : ‖Work.Kernels.phiVec τ 0 * Work.Kernels.fk 6 τ
        * (Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ
            - Work.Kernels.E4Fun z ^ 2 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2))
      + Work.Kernels.phiVec τ 1 * Work.Kernels.fk 4 τ
        * (2 * (Work.Kernels.E4Fun z * (Work.Kernels.E4Fun z ^ 2
            - Work.Kernels.E6Fun z * Work.Kernels.E2Fun z))
          - 2 * (Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ))
      + Work.Kernels.phiVec τ 2 * Work.Kernels.fk 2 τ * Work.Kernels.DeltaFun z‖
      ≤ (M * M * (Cd * M + C4 * C4 * Cδ) + M * M * (2 * Cd * M + 2 * C4 * Cε)
        + M * M * Cd) * ‖Work.Kernels.qParamFun z‖ := by
    have h1 : ‖Work.Kernels.phiVec τ 0 * Work.Kernels.fk 6 τ
          * (Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ
              - Work.Kernels.E4Fun z ^ 2 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2))
        + Work.Kernels.phiVec τ 1 * Work.Kernels.fk 4 τ
          * (2 * (Work.Kernels.E4Fun z * (Work.Kernels.E4Fun z ^ 2
              - Work.Kernels.E6Fun z * Work.Kernels.E2Fun z))
            - 2 * (Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ))
        + Work.Kernels.phiVec τ 2 * Work.Kernels.fk 2 τ * Work.Kernels.DeltaFun z‖
        ≤ ‖Work.Kernels.phiVec τ 0 * Work.Kernels.fk 6 τ
            * (Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ
                - Work.Kernels.E4Fun z ^ 2
                  * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2))
          + Work.Kernels.phiVec τ 1 * Work.Kernels.fk 4 τ
            * (2 * (Work.Kernels.E4Fun z * (Work.Kernels.E4Fun z ^ 2
                - Work.Kernels.E6Fun z * Work.Kernels.E2Fun z))
              - 2 * (Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ))‖
          + ‖Work.Kernels.phiVec τ 2 * Work.Kernels.fk 2 τ * Work.Kernels.DeltaFun z‖ :=
        norm_add_le _ _
    have h2 : ‖Work.Kernels.phiVec τ 0 * Work.Kernels.fk 6 τ
          * (Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ
              - Work.Kernels.E4Fun z ^ 2 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2))
        + Work.Kernels.phiVec τ 1 * Work.Kernels.fk 4 τ
          * (2 * (Work.Kernels.E4Fun z * (Work.Kernels.E4Fun z ^ 2
              - Work.Kernels.E6Fun z * Work.Kernels.E2Fun z))
            - 2 * (Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ))‖
        ≤ ‖Work.Kernels.phiVec τ 0 * Work.Kernels.fk 6 τ
            * (Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ
                - Work.Kernels.E4Fun z ^ 2
                  * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2))‖
          + ‖Work.Kernels.phiVec τ 1 * Work.Kernels.fk 4 τ
            * (2 * (Work.Kernels.E4Fun z * (Work.Kernels.E4Fun z ^ 2
                - Work.Kernels.E6Fun z * Work.Kernels.E2Fun z))
              - 2 * (Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ))‖ :=
        norm_add_le _ _
    rw [show (M * M * (Cd * M + C4 * C4 * Cδ) + M * M * (2 * Cd * M + 2 * C4 * Cε)
          + M * M * Cd) * ‖Work.Kernels.qParamFun z‖
        = M * M * (Cd * M + C4 * C4 * Cδ) * ‖Work.Kernels.qParamFun z‖
          + M * M * (2 * Cd * M + 2 * C4 * Cε) * ‖Work.Kernels.qParamFun z‖
          + M * M * Cd * ‖Work.Kernels.qParamFun z‖ by ring]
    linarith [h1, h2, t1, t2, t3]
  refine le_trans hsum ?_
  rw [show (M * M * (Cd * M + C4 * C4 * Cδ) + M * M * (2 * Cd * M + 2 * C4 * Cε)
        + M * M * Cd + 1) * ‖Work.Kernels.qParamFun z‖
      = (M * M * (Cd * M + C4 * C4 * Cδ) + M * M * (2 * Cd * M + 2 * C4 * Cε)
        + M * M * Cd) * ‖Work.Kernels.qParamFun z‖ + ‖Work.Kernels.qParamFun z‖ by ring]
  linarith [hq0]


/-! ## The numerator `Ξ₂₄` is `O(q)` on the closed ball -/

theorem Xi24_bound (τ₀ : ℍ) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ z : ℍ, dist τ τ₀ ≤ R → 1 ≤ z.im →
      ‖Xi24 τ z‖ ≤ C * ‖Work.Kernels.qParamFun z‖ := by
  obtain ⟨M, hM, hb⟩ := ball_factor_bounds τ₀ R
  obtain ⟨Cd, hCd, hd⟩ := DeltaFun_isBigOq_one
  obtain ⟨Cδ, hCδ, hδ⟩ := delta1_isBigOq
  obtain ⟨C4, hC4, hE4b⟩ := E4Fun_bdd
  obtain ⟨C0, hC0, hN0⟩ := Xi24_aux_N0
  obtain ⟨C2, hC2, hN2⟩ := Xi24_aux_N2
  obtain ⟨CU, hCU, hU⟩ := Xi24_aux_U
  obtain ⟨CR, hCR, hR⟩ := Xi24_aux_R
  obtain ⟨cdl, hcdl, hdl⟩ := DeltaFun_lower
  refine ⟨M * M * ((6 * M * Cδ * Cd + C0) / cdl + (12 * M * M * Cδ * Cd + M * CU + 1728 * C4 * C4 * CR) / cdl
      + (6 * M * Cδ * Cd + C2) / cdl) + 1, by positivity, fun τ z hτ hz => ?_⟩
  obtain ⟨hjτ, hphi0, hphi1, hphi2, hfk2, hfk4, hfk6, hfk10, hfk12, hfk14⟩ := hb τ hτ
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
  have hDpos : 0 < ‖Work.Kernels.DeltaFun z‖ := norm_pos_iff.mpr (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z)
  have hΔz : ‖Work.Kernels.DeltaFun z‖ ≤ Cd * ‖Work.Kernels.qParamFun z‖ := by simpa using hd z hz
  have hσ : ‖(Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2)‖ ≤ Cδ * ‖Work.Kernels.qParamFun z‖ := by simpa using hδ z hz
  have hA : ‖Work.Kernels.E4Fun z‖ ≤ C4 := by simpa using hE4b z hz
  have hA2 : ‖Work.Kernels.E4Fun z ^ 2‖ ≤ C4 * C4 := by rw [norm_pow, pow_two]; exact mul_le_mul hA hA (norm_nonneg _) hC4.le
  have hj2 : ‖Work.Kernels.jInvariantFun τ ^ 2‖ ≤ M * M := by rw [norm_pow, pow_two]; exact mul_le_mul hjτ hjτ (norm_nonneg _) hM.le
  have hDl : cdl * ‖Work.Kernels.qParamFun z‖ ≤ ‖Work.Kernels.DeltaFun z‖ := hdl z hz
  have hN0b : ‖1728 * Work.Kernels.E2Fun z ^ 2 * Work.Kernels.DeltaFun z - 6 * Work.Kernels.E4Fun z ^ 3 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2)‖ ≤ C0 * ‖Work.Kernels.qParamFun z‖ ^ 2 := hN0 z hz
  have hN2b : ‖1728 * Work.Kernels.E4Fun z * Work.Kernels.DeltaFun z - 6 * Work.Kernels.E4Fun z ^ 3 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2)‖ ≤ C2 * ‖Work.Kernels.qParamFun z‖ ^ 2 := hN2 z hz
  have hUb : ‖12 * Work.Kernels.E4Fun z ^ 3 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) + 1728 * Work.Kernels.DeltaFun z * (5 * Work.Kernels.E4Fun z - 7 * Work.Kernels.E2Fun z ^ 2)‖ ≤ CU * ‖Work.Kernels.qParamFun z‖ ^ 2 := hU z hz
  have hRb : ‖5 * Work.Kernels.E4Fun z ^ 2 - 7 * Work.Kernels.E4Fun z * Work.Kernels.E2Fun z ^ 2 + 2 * Work.Kernels.E6Fun z * Work.Kernels.E2Fun z‖ ≤ CR * ‖Work.Kernels.qParamFun z‖ ^ 2 := hR z hz
  have hunf : Xi24 τ z = Work.Kernels.phiVec τ 0 * Work.Kernels.fk 14 τ * (6 * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) * Work.Kernels.E4Fun z + (1728 - 6 * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)) * Work.Kernels.E2Fun z ^ 2)
        + Work.Kernels.phiVec τ 1 * Work.Kernels.fk 12 τ * ((-12 * Work.Kernels.jInvariantFun τ * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) + 5 * 1728 * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)) * Work.Kernels.E4Fun z + (-2 * 1728) * (Work.Kernels.E4Fun z ^ 2 * Work.Kernels.E6Fun z / Work.Kernels.DeltaFun z) * Work.Kernels.E2Fun z + (12 * Work.Kernels.jInvariantFun τ * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) - 7 * 1728 * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)) * Work.Kernels.E2Fun z ^ 2)
        + Work.Kernels.phiVec τ 2 * Work.Kernels.fk 10 τ * ((1728 + 6 * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)) * Work.Kernels.E4Fun z - 6 * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) * Work.Kernels.E2Fun z ^ 2) := by
    simp only [Xi24, Fin.sum_univ_three, Work.Kernels.phiVec, Work.Kernels.c1728,
      Work.Kernels.E14Fun, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply, Fin.val_zero, Fin.val_one,
      Fin.val_two, pow_zero, pow_one, mul_one]
    rw [show Work.Kernels.fk (4 : ℤ) z = Work.Kernels.E4Fun z from rfl,
      show Work.Kernels.fk (2 : ℤ) z
        = Work.Kernels.E4Fun z ^ 2 * Work.Kernels.E6Fun z / Work.Kernels.DeltaFun z from rfl,
      show Work.Kernels.fk (0 : ℤ) z = 1 from rfl]
    ring
  have hrel : Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun z = Work.Kernels.E4Fun z ^ 3 := Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun z
  have hXi : Xi24 τ z = Work.Kernels.phiVec τ 0 * Work.Kernels.fk 14 τ * ((6 * Work.Kernels.jInvariantFun τ * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) * Work.Kernels.DeltaFun z + (1728 * Work.Kernels.E2Fun z ^ 2 * Work.Kernels.DeltaFun z - 6 * Work.Kernels.E4Fun z ^ 3 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2))) / Work.Kernels.DeltaFun z)
        + Work.Kernels.phiVec τ 1 * Work.Kernels.fk 12 τ * ((-12 * Work.Kernels.jInvariantFun τ ^ 2 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) * Work.Kernels.DeltaFun z + Work.Kernels.jInvariantFun τ * (12 * Work.Kernels.E4Fun z ^ 3 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) + 1728 * Work.Kernels.DeltaFun z * (5 * Work.Kernels.E4Fun z - 7 * Work.Kernels.E2Fun z ^ 2)) - 1728 * Work.Kernels.E4Fun z ^ 2 * (5 * Work.Kernels.E4Fun z ^ 2 - 7 * Work.Kernels.E4Fun z * Work.Kernels.E2Fun z ^ 2 + 2 * Work.Kernels.E6Fun z * Work.Kernels.E2Fun z)) / Work.Kernels.DeltaFun z)
        + Work.Kernels.phiVec τ 2 * Work.Kernels.fk 10 τ * ((6 * Work.Kernels.jInvariantFun τ * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) * Work.Kernels.DeltaFun z + (1728 * Work.Kernels.E4Fun z * Work.Kernels.DeltaFun z - 6 * Work.Kernels.E4Fun z ^ 3 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2))) / Work.Kernels.DeltaFun z) := by
    rw [hunf,
      Xi24_row0_aux (A := Work.Kernels.E4Fun z) (C := Work.Kernels.E2Fun z) (D := Work.Kernels.DeltaFun z) (j := Work.Kernels.jInvariantFun τ) (jz := Work.Kernels.jInvariantFun z) (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z) hrel,
      Xi24_row1_aux (A := Work.Kernels.E4Fun z) (B := Work.Kernels.E6Fun z) (C := Work.Kernels.E2Fun z) (D := Work.Kernels.DeltaFun z) (j := Work.Kernels.jInvariantFun τ) (jz := Work.Kernels.jInvariantFun z) (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z) hrel,
      Xi24_row2_aux (A := Work.Kernels.E4Fun z) (C := Work.Kernels.E2Fun z) (D := Work.Kernels.DeltaFun z) (j := Work.Kernels.jInvariantFun τ) (jz := Work.Kernels.jInvariantFun z) (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z) hrel]
  rw [hXi]
  have h0 : ‖(6 * Work.Kernels.jInvariantFun τ * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) * Work.Kernels.DeltaFun z + (1728 * Work.Kernels.E2Fun z ^ 2 * Work.Kernels.DeltaFun z - 6 * Work.Kernels.E4Fun z ^ 3 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2))) / Work.Kernels.DeltaFun z‖ ≤ (6 * M * Cδ * Cd + C0) / cdl * ‖Work.Kernels.qParamFun z‖ := by
    rw [norm_div, div_le_iff₀ hDpos]
    have ha : ‖6 * Work.Kernels.jInvariantFun τ * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) * Work.Kernels.DeltaFun z‖ ≤ 6 * M * Cδ * Cd * ‖Work.Kernels.qParamFun z‖ ^ 2 := by
      have h := norm_mul_mul_mul_le (a := (6 : ℂ)) (b := Work.Kernels.jInvariantFun τ) (c := (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2)) (d := Work.Kernels.DeltaFun z)
        (A := 6) (B := M) (C := Cδ * ‖Work.Kernels.qParamFun z‖) (D := Cd * ‖Work.Kernels.qParamFun z‖) (by norm_num) hjτ hσ hΔz
      calc ‖6 * Work.Kernels.jInvariantFun τ * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) * Work.Kernels.DeltaFun z‖ ≤ 6 * M * (Cδ * ‖Work.Kernels.qParamFun z‖) * (Cd * ‖Work.Kernels.qParamFun z‖) := h
        _ = 6 * M * Cδ * Cd * ‖Work.Kernels.qParamFun z‖ ^ 2 := by ring
    have hnum : ‖(6 * Work.Kernels.jInvariantFun τ * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) * Work.Kernels.DeltaFun z + (1728 * Work.Kernels.E2Fun z ^ 2 * Work.Kernels.DeltaFun z - 6 * Work.Kernels.E4Fun z ^ 3 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2)))‖ ≤ (6 * M * Cδ * Cd + C0) * ‖Work.Kernels.qParamFun z‖ ^ 2 := by
      calc ‖(6 * Work.Kernels.jInvariantFun τ * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) * Work.Kernels.DeltaFun z + (1728 * Work.Kernels.E2Fun z ^ 2 * Work.Kernels.DeltaFun z - 6 * Work.Kernels.E4Fun z ^ 3 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2)))‖ ≤ ‖6 * Work.Kernels.jInvariantFun τ * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) * Work.Kernels.DeltaFun z‖ + ‖1728 * Work.Kernels.E2Fun z ^ 2 * Work.Kernels.DeltaFun z - 6 * Work.Kernels.E4Fun z ^ 3 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2)‖ := norm_add_le _ _
        _ ≤ 6 * M * Cδ * Cd * ‖Work.Kernels.qParamFun z‖ ^ 2 + C0 * ‖Work.Kernels.qParamFun z‖ ^ 2 := add_le_add ha hN0b
        _ = (6 * M * Cδ * Cd + C0) * ‖Work.Kernels.qParamFun z‖ ^ 2 := by ring
    calc ‖(6 * Work.Kernels.jInvariantFun τ * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) * Work.Kernels.DeltaFun z + (1728 * Work.Kernels.E2Fun z ^ 2 * Work.Kernels.DeltaFun z - 6 * Work.Kernels.E4Fun z ^ 3 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2)))‖ ≤ (6 * M * Cδ * Cd + C0) * ‖Work.Kernels.qParamFun z‖ ^ 2 := hnum
      _ = ((6 * M * Cδ * Cd + C0) / cdl) * ‖Work.Kernels.qParamFun z‖ * (cdl * ‖Work.Kernels.qParamFun z‖) := by field_simp <;> ring
      _ ≤ ((6 * M * Cδ * Cd + C0) / cdl) * ‖Work.Kernels.qParamFun z‖ * ‖Work.Kernels.DeltaFun z‖ := by
          apply mul_le_mul_of_nonneg_left hDl (by positivity)
  have h1 : ‖(-12 * Work.Kernels.jInvariantFun τ ^ 2 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) * Work.Kernels.DeltaFun z + Work.Kernels.jInvariantFun τ * (12 * Work.Kernels.E4Fun z ^ 3 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) + 1728 * Work.Kernels.DeltaFun z * (5 * Work.Kernels.E4Fun z - 7 * Work.Kernels.E2Fun z ^ 2)) - 1728 * Work.Kernels.E4Fun z ^ 2 * (5 * Work.Kernels.E4Fun z ^ 2 - 7 * Work.Kernels.E4Fun z * Work.Kernels.E2Fun z ^ 2 + 2 * Work.Kernels.E6Fun z * Work.Kernels.E2Fun z)) / Work.Kernels.DeltaFun z‖
      ≤ (12 * M * M * Cδ * Cd + M * CU + 1728 * C4 * C4 * CR) / cdl * ‖Work.Kernels.qParamFun z‖ := by
    rw [norm_div, div_le_iff₀ hDpos]
    have ha : ‖-12 * Work.Kernels.jInvariantFun τ ^ 2 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) * Work.Kernels.DeltaFun z‖ ≤ 12 * M * M * Cδ * Cd * ‖Work.Kernels.qParamFun z‖ ^ 2 := by
      have h := norm_mul_mul_mul_le (a := (-12 : ℂ)) (b := Work.Kernels.jInvariantFun τ ^ 2) (c := (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2)) (d := Work.Kernels.DeltaFun z)
        (A := 12) (B := M * M) (C := Cδ * ‖Work.Kernels.qParamFun z‖) (D := Cd * ‖Work.Kernels.qParamFun z‖) (by norm_num) hj2 hσ hΔz
      calc ‖-12 * Work.Kernels.jInvariantFun τ ^ 2 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) * Work.Kernels.DeltaFun z‖ ≤ 12 * (M * M) * (Cδ * ‖Work.Kernels.qParamFun z‖) * (Cd * ‖Work.Kernels.qParamFun z‖) := h
        _ = 12 * M * M * Cδ * Cd * ‖Work.Kernels.qParamFun z‖ ^ 2 := by ring
    have hb : ‖Work.Kernels.jInvariantFun τ * (12 * Work.Kernels.E4Fun z ^ 3 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) + 1728 * Work.Kernels.DeltaFun z * (5 * Work.Kernels.E4Fun z - 7 * Work.Kernels.E2Fun z ^ 2))‖ ≤ M * CU * ‖Work.Kernels.qParamFun z‖ ^ 2 := by
      rw [norm_mul]
      calc ‖Work.Kernels.jInvariantFun τ‖ * ‖12 * Work.Kernels.E4Fun z ^ 3 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) + 1728 * Work.Kernels.DeltaFun z * (5 * Work.Kernels.E4Fun z - 7 * Work.Kernels.E2Fun z ^ 2)‖ ≤ M * (CU * ‖Work.Kernels.qParamFun z‖ ^ 2) := mul_le_mul hjτ hUb (norm_nonneg _) hM.le
        _ = M * CU * ‖Work.Kernels.qParamFun z‖ ^ 2 := by ring
    have hc : ‖1728 * Work.Kernels.E4Fun z ^ 2 * (5 * Work.Kernels.E4Fun z ^ 2 - 7 * Work.Kernels.E4Fun z * Work.Kernels.E2Fun z ^ 2 + 2 * Work.Kernels.E6Fun z * Work.Kernels.E2Fun z)‖ ≤ 1728 * C4 * C4 * CR * ‖Work.Kernels.qParamFun z‖ ^ 2 := by
      rw [norm_mul, norm_mul]
      calc ‖(1728 : ℂ)‖ * ‖Work.Kernels.E4Fun z ^ 2‖ * ‖5 * Work.Kernels.E4Fun z ^ 2 - 7 * Work.Kernels.E4Fun z * Work.Kernels.E2Fun z ^ 2 + 2 * Work.Kernels.E6Fun z * Work.Kernels.E2Fun z‖
          ≤ 1728 * (C4 * C4) * (CR * ‖Work.Kernels.qParamFun z‖ ^ 2) :=
            mul_le_mul (mul_le_mul (by norm_num) hA2 (norm_nonneg _) (by norm_num)) hRb
              (norm_nonneg _) (by positivity)
        _ = 1728 * C4 * C4 * CR * ‖Work.Kernels.qParamFun z‖ ^ 2 := by ring
    have hnum : ‖(-12 * Work.Kernels.jInvariantFun τ ^ 2 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) * Work.Kernels.DeltaFun z + Work.Kernels.jInvariantFun τ * (12 * Work.Kernels.E4Fun z ^ 3 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) + 1728 * Work.Kernels.DeltaFun z * (5 * Work.Kernels.E4Fun z - 7 * Work.Kernels.E2Fun z ^ 2)) - 1728 * Work.Kernels.E4Fun z ^ 2 * (5 * Work.Kernels.E4Fun z ^ 2 - 7 * Work.Kernels.E4Fun z * Work.Kernels.E2Fun z ^ 2 + 2 * Work.Kernels.E6Fun z * Work.Kernels.E2Fun z))‖
        ≤ (12 * M * M * Cδ * Cd + M * CU + 1728 * C4 * C4 * CR) * ‖Work.Kernels.qParamFun z‖ ^ 2 := by
      calc ‖(-12 * Work.Kernels.jInvariantFun τ ^ 2 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) * Work.Kernels.DeltaFun z + Work.Kernels.jInvariantFun τ * (12 * Work.Kernels.E4Fun z ^ 3 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) + 1728 * Work.Kernels.DeltaFun z * (5 * Work.Kernels.E4Fun z - 7 * Work.Kernels.E2Fun z ^ 2)) - 1728 * Work.Kernels.E4Fun z ^ 2 * (5 * Work.Kernels.E4Fun z ^ 2 - 7 * Work.Kernels.E4Fun z * Work.Kernels.E2Fun z ^ 2 + 2 * Work.Kernels.E6Fun z * Work.Kernels.E2Fun z))‖
          ≤ ‖-12 * Work.Kernels.jInvariantFun τ ^ 2 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) * Work.Kernels.DeltaFun z + Work.Kernels.jInvariantFun τ * (12 * Work.Kernels.E4Fun z ^ 3 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) + 1728 * Work.Kernels.DeltaFun z * (5 * Work.Kernels.E4Fun z - 7 * Work.Kernels.E2Fun z ^ 2))‖ + ‖1728 * Work.Kernels.E4Fun z ^ 2 * (5 * Work.Kernels.E4Fun z ^ 2 - 7 * Work.Kernels.E4Fun z * Work.Kernels.E2Fun z ^ 2 + 2 * Work.Kernels.E6Fun z * Work.Kernels.E2Fun z)‖ :=
            norm_sub_le _ _
        _ ≤ (12 * M * M * Cδ * Cd * ‖Work.Kernels.qParamFun z‖ ^ 2 + M * CU * ‖Work.Kernels.qParamFun z‖ ^ 2)
            + 1728 * C4 * C4 * CR * ‖Work.Kernels.qParamFun z‖ ^ 2 :=
            add_le_add (le_trans (norm_add_le _ _) (add_le_add ha hb)) hc
        _ = (12 * M * M * Cδ * Cd + M * CU + 1728 * C4 * C4 * CR) * ‖Work.Kernels.qParamFun z‖ ^ 2 := by ring
    calc ‖(-12 * Work.Kernels.jInvariantFun τ ^ 2 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) * Work.Kernels.DeltaFun z + Work.Kernels.jInvariantFun τ * (12 * Work.Kernels.E4Fun z ^ 3 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) + 1728 * Work.Kernels.DeltaFun z * (5 * Work.Kernels.E4Fun z - 7 * Work.Kernels.E2Fun z ^ 2)) - 1728 * Work.Kernels.E4Fun z ^ 2 * (5 * Work.Kernels.E4Fun z ^ 2 - 7 * Work.Kernels.E4Fun z * Work.Kernels.E2Fun z ^ 2 + 2 * Work.Kernels.E6Fun z * Work.Kernels.E2Fun z))‖
        ≤ (12 * M * M * Cδ * Cd + M * CU + 1728 * C4 * C4 * CR) * ‖Work.Kernels.qParamFun z‖ ^ 2 := hnum
      _ = ((12 * M * M * Cδ * Cd + M * CU + 1728 * C4 * C4 * CR) / cdl) * ‖Work.Kernels.qParamFun z‖ * (cdl * ‖Work.Kernels.qParamFun z‖) := by
          field_simp <;> ring
      _ ≤ ((12 * M * M * Cδ * Cd + M * CU + 1728 * C4 * C4 * CR) / cdl) * ‖Work.Kernels.qParamFun z‖ * ‖Work.Kernels.DeltaFun z‖ := by
          apply mul_le_mul_of_nonneg_left hDl (by positivity)
  have h2 : ‖(6 * Work.Kernels.jInvariantFun τ * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) * Work.Kernels.DeltaFun z + (1728 * Work.Kernels.E4Fun z * Work.Kernels.DeltaFun z - 6 * Work.Kernels.E4Fun z ^ 3 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2))) / Work.Kernels.DeltaFun z‖ ≤ (6 * M * Cδ * Cd + C2) / cdl * ‖Work.Kernels.qParamFun z‖ := by
    rw [norm_div, div_le_iff₀ hDpos]
    have ha : ‖6 * Work.Kernels.jInvariantFun τ * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) * Work.Kernels.DeltaFun z‖ ≤ 6 * M * Cδ * Cd * ‖Work.Kernels.qParamFun z‖ ^ 2 := by
      have h := norm_mul_mul_mul_le (a := (6 : ℂ)) (b := Work.Kernels.jInvariantFun τ) (c := (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2)) (d := Work.Kernels.DeltaFun z)
        (A := 6) (B := M) (C := Cδ * ‖Work.Kernels.qParamFun z‖) (D := Cd * ‖Work.Kernels.qParamFun z‖) (by norm_num) hjτ hσ hΔz
      calc ‖6 * Work.Kernels.jInvariantFun τ * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) * Work.Kernels.DeltaFun z‖ ≤ 6 * M * (Cδ * ‖Work.Kernels.qParamFun z‖) * (Cd * ‖Work.Kernels.qParamFun z‖) := h
        _ = 6 * M * Cδ * Cd * ‖Work.Kernels.qParamFun z‖ ^ 2 := by ring
    have hnum : ‖(6 * Work.Kernels.jInvariantFun τ * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) * Work.Kernels.DeltaFun z + (1728 * Work.Kernels.E4Fun z * Work.Kernels.DeltaFun z - 6 * Work.Kernels.E4Fun z ^ 3 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2)))‖ ≤ (6 * M * Cδ * Cd + C2) * ‖Work.Kernels.qParamFun z‖ ^ 2 := by
      calc ‖(6 * Work.Kernels.jInvariantFun τ * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) * Work.Kernels.DeltaFun z + (1728 * Work.Kernels.E4Fun z * Work.Kernels.DeltaFun z - 6 * Work.Kernels.E4Fun z ^ 3 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2)))‖ ≤ ‖6 * Work.Kernels.jInvariantFun τ * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) * Work.Kernels.DeltaFun z‖ + ‖1728 * Work.Kernels.E4Fun z * Work.Kernels.DeltaFun z - 6 * Work.Kernels.E4Fun z ^ 3 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2)‖ := norm_add_le _ _
        _ ≤ 6 * M * Cδ * Cd * ‖Work.Kernels.qParamFun z‖ ^ 2 + C2 * ‖Work.Kernels.qParamFun z‖ ^ 2 := add_le_add ha hN2b
        _ = (6 * M * Cδ * Cd + C2) * ‖Work.Kernels.qParamFun z‖ ^ 2 := by ring
    calc ‖(6 * Work.Kernels.jInvariantFun τ * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) * Work.Kernels.DeltaFun z + (1728 * Work.Kernels.E4Fun z * Work.Kernels.DeltaFun z - 6 * Work.Kernels.E4Fun z ^ 3 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2)))‖ ≤ (6 * M * Cδ * Cd + C2) * ‖Work.Kernels.qParamFun z‖ ^ 2 := hnum
      _ = ((6 * M * Cδ * Cd + C2) / cdl) * ‖Work.Kernels.qParamFun z‖ * (cdl * ‖Work.Kernels.qParamFun z‖) := by field_simp <;> ring
      _ ≤ ((6 * M * Cδ * Cd + C2) / cdl) * ‖Work.Kernels.qParamFun z‖ * ‖Work.Kernels.DeltaFun z‖ := by
          apply mul_le_mul_of_nonneg_left hDl (by positivity)
  have g0 : ‖Work.Kernels.phiVec τ 0 * Work.Kernels.fk 14 τ * ((6 * Work.Kernels.jInvariantFun τ * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) * Work.Kernels.DeltaFun z + (1728 * Work.Kernels.E2Fun z ^ 2 * Work.Kernels.DeltaFun z - 6 * Work.Kernels.E4Fun z ^ 3 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2))) / Work.Kernels.DeltaFun z)‖ ≤ M * M * (((6 * M * Cδ * Cd + C0) / cdl) * ‖Work.Kernels.qParamFun z‖) :=
    norm_mul_mul_le hphi0 hfk14 h0
  have g1 : ‖Work.Kernels.phiVec τ 1 * Work.Kernels.fk 12 τ * ((-12 * Work.Kernels.jInvariantFun τ ^ 2 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) * Work.Kernels.DeltaFun z + Work.Kernels.jInvariantFun τ * (12 * Work.Kernels.E4Fun z ^ 3 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) + 1728 * Work.Kernels.DeltaFun z * (5 * Work.Kernels.E4Fun z - 7 * Work.Kernels.E2Fun z ^ 2)) - 1728 * Work.Kernels.E4Fun z ^ 2 * (5 * Work.Kernels.E4Fun z ^ 2 - 7 * Work.Kernels.E4Fun z * Work.Kernels.E2Fun z ^ 2 + 2 * Work.Kernels.E6Fun z * Work.Kernels.E2Fun z)) / Work.Kernels.DeltaFun z)‖ ≤ M * M * (((12 * M * M * Cδ * Cd + M * CU + 1728 * C4 * C4 * CR) / cdl) * ‖Work.Kernels.qParamFun z‖) :=
    norm_mul_mul_le hphi1 hfk12 h1
  have g2 : ‖Work.Kernels.phiVec τ 2 * Work.Kernels.fk 10 τ * ((6 * Work.Kernels.jInvariantFun τ * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) * Work.Kernels.DeltaFun z + (1728 * Work.Kernels.E4Fun z * Work.Kernels.DeltaFun z - 6 * Work.Kernels.E4Fun z ^ 3 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2))) / Work.Kernels.DeltaFun z)‖ ≤ M * M * (((6 * M * Cδ * Cd + C2) / cdl) * ‖Work.Kernels.qParamFun z‖) :=
    norm_mul_mul_le hphi2 hfk10 h2
  have hsplit1 : ‖Work.Kernels.phiVec τ 0 * Work.Kernels.fk 14 τ * ((6 * Work.Kernels.jInvariantFun τ * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) * Work.Kernels.DeltaFun z + (1728 * Work.Kernels.E2Fun z ^ 2 * Work.Kernels.DeltaFun z - 6 * Work.Kernels.E4Fun z ^ 3 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2))) / Work.Kernels.DeltaFun z) + Work.Kernels.phiVec τ 1 * Work.Kernels.fk 12 τ * ((-12 * Work.Kernels.jInvariantFun τ ^ 2 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) * Work.Kernels.DeltaFun z + Work.Kernels.jInvariantFun τ * (12 * Work.Kernels.E4Fun z ^ 3 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) + 1728 * Work.Kernels.DeltaFun z * (5 * Work.Kernels.E4Fun z - 7 * Work.Kernels.E2Fun z ^ 2)) - 1728 * Work.Kernels.E4Fun z ^ 2 * (5 * Work.Kernels.E4Fun z ^ 2 - 7 * Work.Kernels.E4Fun z * Work.Kernels.E2Fun z ^ 2 + 2 * Work.Kernels.E6Fun z * Work.Kernels.E2Fun z)) / Work.Kernels.DeltaFun z) + Work.Kernels.phiVec τ 2 * Work.Kernels.fk 10 τ * ((6 * Work.Kernels.jInvariantFun τ * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) * Work.Kernels.DeltaFun z + (1728 * Work.Kernels.E4Fun z * Work.Kernels.DeltaFun z - 6 * Work.Kernels.E4Fun z ^ 3 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2))) / Work.Kernels.DeltaFun z)‖ ≤ ‖Work.Kernels.phiVec τ 0 * Work.Kernels.fk 14 τ * ((6 * Work.Kernels.jInvariantFun τ * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) * Work.Kernels.DeltaFun z + (1728 * Work.Kernels.E2Fun z ^ 2 * Work.Kernels.DeltaFun z - 6 * Work.Kernels.E4Fun z ^ 3 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2))) / Work.Kernels.DeltaFun z) + Work.Kernels.phiVec τ 1 * Work.Kernels.fk 12 τ * ((-12 * Work.Kernels.jInvariantFun τ ^ 2 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) * Work.Kernels.DeltaFun z + Work.Kernels.jInvariantFun τ * (12 * Work.Kernels.E4Fun z ^ 3 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) + 1728 * Work.Kernels.DeltaFun z * (5 * Work.Kernels.E4Fun z - 7 * Work.Kernels.E2Fun z ^ 2)) - 1728 * Work.Kernels.E4Fun z ^ 2 * (5 * Work.Kernels.E4Fun z ^ 2 - 7 * Work.Kernels.E4Fun z * Work.Kernels.E2Fun z ^ 2 + 2 * Work.Kernels.E6Fun z * Work.Kernels.E2Fun z)) / Work.Kernels.DeltaFun z)‖ + ‖Work.Kernels.phiVec τ 2 * Work.Kernels.fk 10 τ * ((6 * Work.Kernels.jInvariantFun τ * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) * Work.Kernels.DeltaFun z + (1728 * Work.Kernels.E4Fun z * Work.Kernels.DeltaFun z - 6 * Work.Kernels.E4Fun z ^ 3 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2))) / Work.Kernels.DeltaFun z)‖ := norm_add_le _ _
  have hsplit2 : ‖Work.Kernels.phiVec τ 0 * Work.Kernels.fk 14 τ * ((6 * Work.Kernels.jInvariantFun τ * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) * Work.Kernels.DeltaFun z + (1728 * Work.Kernels.E2Fun z ^ 2 * Work.Kernels.DeltaFun z - 6 * Work.Kernels.E4Fun z ^ 3 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2))) / Work.Kernels.DeltaFun z) + Work.Kernels.phiVec τ 1 * Work.Kernels.fk 12 τ * ((-12 * Work.Kernels.jInvariantFun τ ^ 2 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) * Work.Kernels.DeltaFun z + Work.Kernels.jInvariantFun τ * (12 * Work.Kernels.E4Fun z ^ 3 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) + 1728 * Work.Kernels.DeltaFun z * (5 * Work.Kernels.E4Fun z - 7 * Work.Kernels.E2Fun z ^ 2)) - 1728 * Work.Kernels.E4Fun z ^ 2 * (5 * Work.Kernels.E4Fun z ^ 2 - 7 * Work.Kernels.E4Fun z * Work.Kernels.E2Fun z ^ 2 + 2 * Work.Kernels.E6Fun z * Work.Kernels.E2Fun z)) / Work.Kernels.DeltaFun z)‖ ≤ ‖Work.Kernels.phiVec τ 0 * Work.Kernels.fk 14 τ * ((6 * Work.Kernels.jInvariantFun τ * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) * Work.Kernels.DeltaFun z + (1728 * Work.Kernels.E2Fun z ^ 2 * Work.Kernels.DeltaFun z - 6 * Work.Kernels.E4Fun z ^ 3 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2))) / Work.Kernels.DeltaFun z)‖ + ‖Work.Kernels.phiVec τ 1 * Work.Kernels.fk 12 τ * ((-12 * Work.Kernels.jInvariantFun τ ^ 2 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) * Work.Kernels.DeltaFun z + Work.Kernels.jInvariantFun τ * (12 * Work.Kernels.E4Fun z ^ 3 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) + 1728 * Work.Kernels.DeltaFun z * (5 * Work.Kernels.E4Fun z - 7 * Work.Kernels.E2Fun z ^ 2)) - 1728 * Work.Kernels.E4Fun z ^ 2 * (5 * Work.Kernels.E4Fun z ^ 2 - 7 * Work.Kernels.E4Fun z * Work.Kernels.E2Fun z ^ 2 + 2 * Work.Kernels.E6Fun z * Work.Kernels.E2Fun z)) / Work.Kernels.DeltaFun z)‖ := norm_add_le _ _
  refine le_trans (b := M * M * (((6 * M * Cδ * Cd + C0) / cdl) + ((12 * M * M * Cδ * Cd + M * CU + 1728 * C4 * C4 * CR) / cdl) + ((6 * M * Cδ * Cd + C2) / cdl)) * ‖Work.Kernels.qParamFun z‖) ?_ ?_
  · calc ‖Work.Kernels.phiVec τ 0 * Work.Kernels.fk 14 τ * ((6 * Work.Kernels.jInvariantFun τ * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) * Work.Kernels.DeltaFun z + (1728 * Work.Kernels.E2Fun z ^ 2 * Work.Kernels.DeltaFun z - 6 * Work.Kernels.E4Fun z ^ 3 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2))) / Work.Kernels.DeltaFun z) + Work.Kernels.phiVec τ 1 * Work.Kernels.fk 12 τ * ((-12 * Work.Kernels.jInvariantFun τ ^ 2 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) * Work.Kernels.DeltaFun z + Work.Kernels.jInvariantFun τ * (12 * Work.Kernels.E4Fun z ^ 3 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) + 1728 * Work.Kernels.DeltaFun z * (5 * Work.Kernels.E4Fun z - 7 * Work.Kernels.E2Fun z ^ 2)) - 1728 * Work.Kernels.E4Fun z ^ 2 * (5 * Work.Kernels.E4Fun z ^ 2 - 7 * Work.Kernels.E4Fun z * Work.Kernels.E2Fun z ^ 2 + 2 * Work.Kernels.E6Fun z * Work.Kernels.E2Fun z)) / Work.Kernels.DeltaFun z) + Work.Kernels.phiVec τ 2 * Work.Kernels.fk 10 τ * ((6 * Work.Kernels.jInvariantFun τ * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) * Work.Kernels.DeltaFun z + (1728 * Work.Kernels.E4Fun z * Work.Kernels.DeltaFun z - 6 * Work.Kernels.E4Fun z ^ 3 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2))) / Work.Kernels.DeltaFun z)‖ ≤ ‖Work.Kernels.phiVec τ 0 * Work.Kernels.fk 14 τ * ((6 * Work.Kernels.jInvariantFun τ * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) * Work.Kernels.DeltaFun z + (1728 * Work.Kernels.E2Fun z ^ 2 * Work.Kernels.DeltaFun z - 6 * Work.Kernels.E4Fun z ^ 3 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2))) / Work.Kernels.DeltaFun z)‖ + ‖Work.Kernels.phiVec τ 1 * Work.Kernels.fk 12 τ * ((-12 * Work.Kernels.jInvariantFun τ ^ 2 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) * Work.Kernels.DeltaFun z + Work.Kernels.jInvariantFun τ * (12 * Work.Kernels.E4Fun z ^ 3 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) + 1728 * Work.Kernels.DeltaFun z * (5 * Work.Kernels.E4Fun z - 7 * Work.Kernels.E2Fun z ^ 2)) - 1728 * Work.Kernels.E4Fun z ^ 2 * (5 * Work.Kernels.E4Fun z ^ 2 - 7 * Work.Kernels.E4Fun z * Work.Kernels.E2Fun z ^ 2 + 2 * Work.Kernels.E6Fun z * Work.Kernels.E2Fun z)) / Work.Kernels.DeltaFun z)‖ + ‖Work.Kernels.phiVec τ 2 * Work.Kernels.fk 10 τ * ((6 * Work.Kernels.jInvariantFun τ * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) * Work.Kernels.DeltaFun z + (1728 * Work.Kernels.E4Fun z * Work.Kernels.DeltaFun z - 6 * Work.Kernels.E4Fun z ^ 3 * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2))) / Work.Kernels.DeltaFun z)‖ := by linarith [hsplit1, hsplit2]
      _ ≤ M * M * (((6 * M * Cδ * Cd + C0) / cdl) * ‖Work.Kernels.qParamFun z‖)
          + M * M * (((12 * M * M * Cδ * Cd + M * CU + 1728 * C4 * C4 * CR) / cdl) * ‖Work.Kernels.qParamFun z‖)
          + M * M * (((6 * M * Cδ * Cd + C2) / cdl) * ‖Work.Kernels.qParamFun z‖) := by linarith [g0, g1, g2]
      _ = M * M * (((6 * M * Cδ * Cd + C0) / cdl) + ((12 * M * M * Cδ * Cd + M * CU + 1728 * C4 * C4 * CR) / cdl)
          + ((6 * M * Cδ * Cd + C2) / cdl)) * ‖Work.Kernels.qParamFun z‖ := by ring
  · rw [show (M * M * (((6 * M * Cδ * Cd + C0) / cdl) + ((12 * M * M * Cδ * Cd + M * CU + 1728 * C4 * C4 * CR) / cdl)
          + ((6 * M * Cδ * Cd + C2) / cdl)) + 1) * ‖Work.Kernels.qParamFun z‖
        = M * M * (((6 * M * Cδ * Cd + C0) / cdl) + ((12 * M * M * Cδ * Cd + M * CU + 1728 * C4 * C4 * CR) / cdl)
          + ((6 * M * Cδ * Cd + C2) / cdl)) * ‖Work.Kernels.qParamFun z‖ + ‖Work.Kernels.qParamFun z‖ by ring]
    linarith [hq0]

theorem KPlus_slash_cusp_ball (d : ℕ) (hd : d = 8 ∨ d = 24)
    {τ₀ : UpperHalfPlane} {R : ℝ} (hR : 0 < R)
    (hclean : ∀ (t : ℝ) (ht : 0 < t), ∀ τ : UpperHalfPlane, dist τ τ₀ ≤ R →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ z : UpperHalfPlane), dist τ τ₀ ≤ R → 1 ≤ z.im →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z →
      ‖(z : ℂ) ^ (-((2 : ℤ) - (d : ℤ) / 2)) * Work.Kernels.KPlus d τ (ModularGroup.S • z)‖ ≤
        C * (1 + ‖(z : ℂ)‖) ^ (2 : ℕ) * Real.exp (-(Real.pi * z.im)) /
          ‖Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by
  rcases hd with rfl | rfl
  · obtain ⟨C, hC, hX⟩ := Xi8_bound τ₀ R
    have hpi : (Real.pi : ℂ) ^ (-2 : ℤ) ≠ 0 := zpow_ne_zero _ (by exact_mod_cast Real.pi_ne_zero)
    have hcne : (36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I ≠ 0 := by exact mul_ne_zero (mul_ne_zero (by norm_num) hpi) Complex.I_ne_zero
    refine ⟨max (C / ‖(36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I‖) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
      fun τ z hτ hz hne => ?_⟩
    have hJne : Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z ≠ 0 := sub_ne_zero.mpr hne
    have hDz : Work.Kernels.DeltaFun z
        * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) ≠ 0 :=
      mul_ne_zero (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z) hJne
    have hcD : (36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I * (Work.Kernels.DeltaFun z
        * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)) ≠ 0 :=
      mul_ne_zero hcne hDz
    have hkey := Xi8_eq τ z hne
    have hXi : (z : ℂ) ^ 2 * Work.Kernels.KPlus 8 τ (ModularGroup.S • z)
        = Xi8 τ z / ((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I * (Work.Kernels.DeltaFun z
            * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z))) := by
      rw [eq_div_iff hcD]
      rw [mul_comm ((z : ℂ) ^ 2 * Work.Kernels.KPlus 8 τ (ModularGroup.S • z))
        ((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I * (Work.Kernels.DeltaFun z
          * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)))]
      exact hkey
    have hzpow : (z : ℂ) ^ (-((2 : ℤ) - ((8 : ℕ) : ℤ) / 2)) = (z : ℂ) ^ 2 := by
      rw [show -((2 : ℤ) - ((8 : ℕ) : ℤ) / 2) = (2 : ℤ) by norm_num, _root_.zpow_ofNat]
    rw [hzpow, hXi, norm_div, norm_mul]
    have hq := hX τ z hτ hz
    have hqn : ‖Work.Kernels.qParamFun z‖ = Real.exp (-(2 * Real.pi * z.im)) := norm_qParamFun z
    have hqle : Real.exp (-(2 * Real.pi * z.im))
        ≤ (1 + ‖(z : ℂ)‖) ^ 2 * Real.exp (-(Real.pi * z.im)) := by
      have h1 : Real.exp (-(2 * Real.pi * z.im)) ≤ Real.exp (-(Real.pi * z.im)) := by
        rw [Real.exp_le_exp]; nlinarith [Real.pi_pos, z.im_pos]
      have h3 : (1 : ℝ) ≤ 1 + ‖(z : ℂ)‖ := by
        have h := norm_nonneg (z : ℂ); linarith
      have h2 : (1 : ℝ) ≤ (1 + ‖(z : ℂ)‖) ^ 2 := by
        calc (1 : ℝ) = 1 * 1 := by ring
          _ ≤ (1 + ‖(z : ℂ)‖) * (1 + ‖(z : ℂ)‖) :=
              mul_le_mul h3 h3 (by norm_num) (by positivity)
          _ = (1 + ‖(z : ℂ)‖) ^ 2 := by ring
      nlinarith [Real.exp_pos (-(Real.pi * z.im)), h1, h2]
    have hDn0 : (0 : ℝ) ≤ C / ‖(36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I‖ := div_nonneg hC.le (norm_nonneg _)
    have hXn0 : (0 : ℝ) ≤ (1 + ‖(z : ℂ)‖) ^ 2 * Real.exp (-(Real.pi * z.im))
        / ‖Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ :=
      div_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le) (norm_nonneg _)
    calc ‖Xi8 τ z‖ / (‖(36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I‖ * ‖Work.Kernels.DeltaFun z
            * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖)
        ≤ C * ‖Work.Kernels.qParamFun z‖ / (‖(36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I‖ * ‖Work.Kernels.DeltaFun z
            * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖) :=
          div_le_div_of_nonneg_right hq (by positivity)
      _ = C / ‖(36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I‖ * (‖Work.Kernels.qParamFun z‖
            / ‖Work.Kernels.DeltaFun z
                * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖) := by ring
      _ ≤ C / ‖(36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I‖ * ((1 + ‖(z : ℂ)‖) ^ 2 * Real.exp (-(Real.pi * z.im))
            / ‖Work.Kernels.DeltaFun z
                * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖) := by
          apply mul_le_mul_of_nonneg_left _ hDn0
          rw [hqn]
          exact div_le_div_of_nonneg_right hqle (norm_nonneg _)
      _ ≤ max (C / ‖(36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I‖) 1 * ((1 + ‖(z : ℂ)‖) ^ 2 * Real.exp (-(Real.pi * z.im))
            / ‖Work.Kernels.DeltaFun z
                * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hXn0
      _ = max (C / ‖(36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I‖) 1 * (1 + ‖(z : ℂ)‖) ^ (2 : ℕ) * Real.exp (-(Real.pi * z.im))
            / ‖Work.Kernels.DeltaFun z
                * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by ring
  · obtain ⟨C, hC, hX⟩ := Xi24_bound τ₀ R
    have hpi : (Real.pi : ℂ) ^ (-2 : ℤ) ≠ 0 := zpow_ne_zero _ (by exact_mod_cast Real.pi_ne_zero)
    have hcne : (36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I ≠ 0 := by exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (by simp [Work.Kernels.c1728])) hpi) Complex.I_ne_zero
    refine ⟨max (C / ‖(36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I‖) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
      fun τ z hτ hz hne => ?_⟩
    have hJne : Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z ≠ 0 := sub_ne_zero.mpr hne
    have hDz : Work.Kernels.DeltaFun z
        * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) ≠ 0 :=
      mul_ne_zero (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z) hJne
    have hcD : (36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I * (Work.Kernels.DeltaFun z
        * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)) ≠ 0 :=
      mul_ne_zero hcne hDz
    have hkey := Xi24_eq τ z hne
    have hXi : (z : ℂ) ^ 10 * Work.Kernels.KPlus 24 τ (ModularGroup.S • z)
        = Xi24 τ z / ((36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I * (Work.Kernels.DeltaFun z
            * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z))) := by
      rw [eq_div_iff hcD]
      rw [mul_comm ((z : ℂ) ^ 10 * Work.Kernels.KPlus 24 τ (ModularGroup.S • z))
        ((36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I * (Work.Kernels.DeltaFun z
          * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)))]
      exact hkey
    have hzpow : (z : ℂ) ^ (-((2 : ℤ) - ((24 : ℕ) : ℤ) / 2)) = (z : ℂ) ^ 10 := by
      rw [show -((2 : ℤ) - ((24 : ℕ) : ℤ) / 2) = (10 : ℤ) by norm_num, _root_.zpow_ofNat]
    rw [hzpow, hXi, norm_div, norm_mul]
    have hq := hX τ z hτ hz
    have hqn : ‖Work.Kernels.qParamFun z‖ = Real.exp (-(2 * Real.pi * z.im)) := norm_qParamFun z
    have hqle : Real.exp (-(2 * Real.pi * z.im))
        ≤ (1 + ‖(z : ℂ)‖) ^ 2 * Real.exp (-(Real.pi * z.im)) := by
      have h1 : Real.exp (-(2 * Real.pi * z.im)) ≤ Real.exp (-(Real.pi * z.im)) := by
        rw [Real.exp_le_exp]; nlinarith [Real.pi_pos, z.im_pos]
      have h3 : (1 : ℝ) ≤ 1 + ‖(z : ℂ)‖ := by
        have h := norm_nonneg (z : ℂ); linarith
      have h2 : (1 : ℝ) ≤ (1 + ‖(z : ℂ)‖) ^ 2 := by
        calc (1 : ℝ) = 1 * 1 := by ring
          _ ≤ (1 + ‖(z : ℂ)‖) * (1 + ‖(z : ℂ)‖) :=
              mul_le_mul h3 h3 (by norm_num) (by positivity)
          _ = (1 + ‖(z : ℂ)‖) ^ 2 := by ring
      nlinarith [Real.exp_pos (-(Real.pi * z.im)), h1, h2]
    have hDn0 : (0 : ℝ) ≤ C / ‖(36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I‖ := div_nonneg hC.le (norm_nonneg _)
    have hXn0 : (0 : ℝ) ≤ (1 + ‖(z : ℂ)‖) ^ 2 * Real.exp (-(Real.pi * z.im))
        / ‖Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ :=
      div_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le) (norm_nonneg _)
    calc ‖Xi24 τ z‖ / (‖(36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I‖ * ‖Work.Kernels.DeltaFun z
            * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖)
        ≤ C * ‖Work.Kernels.qParamFun z‖ / (‖(36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I‖ * ‖Work.Kernels.DeltaFun z
            * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖) :=
          div_le_div_of_nonneg_right hq (by positivity)
      _ = C / ‖(36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I‖ * (‖Work.Kernels.qParamFun z‖
            / ‖Work.Kernels.DeltaFun z
                * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖) := by ring
      _ ≤ C / ‖(36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I‖ * ((1 + ‖(z : ℂ)‖) ^ 2 * Real.exp (-(Real.pi * z.im))
            / ‖Work.Kernels.DeltaFun z
                * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖) := by
          apply mul_le_mul_of_nonneg_left _ hDn0
          rw [hqn]
          exact div_le_div_of_nonneg_right hqle (norm_nonneg _)
      _ ≤ max (C / ‖(36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I‖) 1 * ((1 + ‖(z : ℂ)‖) ^ 2 * Real.exp (-(Real.pi * z.im))
            / ‖Work.Kernels.DeltaFun z
                * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hXn0
      _ = max (C / ‖(36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I‖) 1 * (1 + ‖(z : ℂ)‖) ^ (2 : ℕ) * Real.exp (-(Real.pi * z.im))
            / ‖Work.Kernels.DeltaFun z
                * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by ring

end

end Work.Asymptotics
