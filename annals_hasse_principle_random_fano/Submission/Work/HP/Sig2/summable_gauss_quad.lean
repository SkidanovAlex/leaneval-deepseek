import Mathlib
import Submission.Work.HP.Sig2.Poisson1D
import Submission.Work.HP.Sig2.GaussPoissonDefs
import Submission.Work.HP.Sig2.summable_exp_quad_lower

namespace Work.HP.Sig2

/-- The quadratic form of a real matrix is homogeneous of degree two. -/
lemma qForm_smul' {κ : Type*} [Fintype κ] (G : Matrix κ κ ℝ) (c : ℝ) (x : κ → ℝ) :
    qForm G (c • x) = c ^ 2 * qForm G x := by
  rw [qForm_eq_dotProduct, qForm_eq_dotProduct, Matrix.mulVec_smul, smul_dotProduct,
    dotProduct_smul]
  simp only [smul_eq_mul]
  ring

/-- If `G : Matrix κ κ ℝ` is positive definite then there is `ε > 0` with
`ε ∑ xᵢ² ≤ xᵀGx` for every `x : κ → ℝ`. -/
lemma posdef_lower_bound {κ : Type*} [Fintype κ] [DecidableEq κ]
    (G : Matrix κ κ ℝ) (hG : G.PosDef) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : κ → ℝ, ε * (∑ i, (x i) ^ 2) ≤ qForm G x := by
  classical
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · refine ⟨1, one_pos, fun x => ?_⟩
    have hx : x = 0 := funext fun i => (hκ.false i).elim
    rw [hx]
    simp [qForm]
  · have hcont : Continuous (qForm G) := by
      change Continuous (fun x : κ → ℝ => ∑ i, ∑ j, x i * G i j * x j)
      fun_prop
    have hSclosed : IsClosed {x : κ → ℝ | ∑ i, (x i) ^ 2 = 1} :=
      isClosed_eq (by fun_prop) continuous_const
    have hSsub : {x : κ → ℝ | ∑ i, (x i) ^ 2 = 1}
        ⊆ Set.univ.pi (fun _ : κ => Set.Icc (-1 : ℝ) 1) := by
      intro x hx
      rw [Set.mem_univ_pi]
      intro i
      rw [Set.mem_Icc]
      have h1 : (x i) ^ 2 ≤ ∑ j, (x j) ^ 2 :=
        Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
      rw [hx] at h1
      constructor <;> nlinarith [sq_nonneg (x i + 1), sq_nonneg (x i - 1)]
    have hScomp : IsCompact {x : κ → ℝ | ∑ i, (x i) ^ 2 = 1} :=
      (isCompact_univ_pi (fun _ : κ => isCompact_Icc)).of_isClosed_subset hSclosed hSsub
    have hSne : ({x : κ → ℝ | ∑ i, (x i) ^ 2 = 1}).Nonempty := by
      obtain ⟨i₀⟩ := hκ
      refine ⟨Pi.single i₀ (1 : ℝ), ?_⟩
      have h1 : ∀ i : κ, (Pi.single i₀ (1 : ℝ) : κ → ℝ) i ^ 2
          = if i = i₀ then (1 : ℝ) else 0 := by
        intro i
        rcases eq_or_ne i i₀ with h | h
        · subst h; simp
        · rw [Pi.single_eq_of_ne h]; simp [h]
      calc ∑ i, (Pi.single i₀ (1 : ℝ) : κ → ℝ) i ^ 2
          = ∑ i, (if i = i₀ then (1 : ℝ) else 0) := Finset.sum_congr rfl (fun i _ => h1 i)
        _ = 1 := by simp
    obtain ⟨x₀, hx₀S, hmin⟩ := hScomp.exists_isMinOn hSne hcont.continuousOn
    have hx₀ne : x₀ ≠ 0 := by
      intro h
      have h1 := hx₀S
      rw [h] at h1
      simp at h1
    have hfpos : 0 < qForm G x₀ := by
      rw [qForm_eq_dotProduct]
      have h1 : 0 < star x₀ ⬝ᵥ G.mulVec x₀ :=
        (Matrix.posDef_iff_dotProduct_mulVec.mp hG).2 hx₀ne
      have h2 : star x₀ = x₀ := funext fun i => star_trivial (x₀ i)
      rwa [h2] at h1
    refine ⟨qForm G x₀, hfpos, fun x => ?_⟩
    by_cases hx : x = 0
    · rw [hx]
      simp [qForm]
    · have hs_pos : 0 < ∑ k, (x k) ^ 2 := by
        obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
          by_contra h
          simp only [not_exists, not_not] at h
          exact hx (funext h)
        exact Finset.sum_pos' (fun j _ => sq_nonneg (x j))
          ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩
      have hsp : (Real.sqrt (∑ k, (x k) ^ 2)) ^ 2 = ∑ k, (x k) ^ 2 := Real.sq_sqrt hs_pos.le
      have hsne : Real.sqrt (∑ k, (x k) ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hs_pos)
      let y : κ → ℝ := (Real.sqrt (∑ k, (x k) ^ 2))⁻¹ • x
      have hy : x = Real.sqrt (∑ k, (x k) ^ 2) • y := by
        simp only [y]
        rw [← smul_assoc, smul_eq_mul, mul_inv_cancel₀ hsne, one_smul]
      have hyS : ∑ i, (y i) ^ 2 = 1 := by
        have h2 : ∀ i, ((Real.sqrt (∑ k, (x k) ^ 2))⁻¹ * x i) ^ 2
            = ((Real.sqrt (∑ k, (x k) ^ 2)) ^ 2)⁻¹ * (x i) ^ 2 := by
          intro i
          rw [mul_pow, inv_pow]
        simp only [y, Pi.smul_apply, smul_eq_mul]
        calc ∑ i, ((Real.sqrt (∑ k, (x k) ^ 2))⁻¹ * x i) ^ 2
            = ∑ i, ((Real.sqrt (∑ k, (x k) ^ 2)) ^ 2)⁻¹ * (x i) ^ 2 :=
              Finset.sum_congr rfl (fun i _ => h2 i)
          _ = ((Real.sqrt (∑ k, (x k) ^ 2)) ^ 2)⁻¹ * ∑ i, (x i) ^ 2 := by
              rw [Finset.mul_sum]
          _ = ((∑ k, (x k) ^ 2))⁻¹ * ∑ i, (x i) ^ 2 := by rw [hsp]
          _ = 1 := inv_mul_cancel₀ (ne_of_gt hs_pos)
      have hscale : qForm G x = (∑ k, (x k) ^ 2) * qForm G y := by
        conv_lhs => rw [hy]
        rw [qForm_smul', hsp]
      have hmin' : qForm G x₀ ≤ qForm G y := hmin hyS
      calc qForm G x₀ * (∑ i, (x i) ^ 2)
          = (∑ i, (x i) ^ 2) * qForm G x₀ := by ring
        _ ≤ (∑ i, (x i) ^ 2) * qForm G y := mul_le_mul_of_nonneg_left hmin' hs_pos.le
        _ = qForm G x := hscale.symm

/-- Quantitative positive definiteness and summability of Gaussian quadratic sums on `ℤ^κ`: for a
positive definite `G : Matrix κ κ ℝ` there is `ε > 0` with `ε ∑ xᵢ² ≤ xᵀGx` for all `x : κ → ℝ`,
and `n ↦ exp(-c · nᵀGn)` is summable on `ℤ^κ` for every `c > 0`. -/
theorem summable_gauss_quad {κ : Type*} [Fintype κ] [DecidableEq κ]
    (G : Matrix κ κ ℝ) (hG : G.PosDef) :
    (∃ ε : ℝ, 0 < ε ∧ ∀ x : κ → ℝ, ε * (∑ i, (x i) ^ 2) ≤ ∑ i, ∑ j, x i * G i j * x j) ∧
    (∀ c : ℝ, 0 < c →
      Summable (fun n : κ → ℤ => Real.exp (-c * (∑ i, ∑ j, (n i : ℝ) * G i j * (n j : ℝ))))) := by
  obtain ⟨ε, hε, hbound⟩ := posdef_lower_bound G hG
  refine ⟨⟨ε, hε, ?_⟩, fun c hc => summable_exp_quad_lower G c ε hε hc hbound⟩
  intro x
  exact hbound x

end Work.HP.Sig2
