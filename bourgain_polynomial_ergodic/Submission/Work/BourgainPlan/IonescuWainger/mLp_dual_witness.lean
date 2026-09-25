import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.riesz_thorin_vec_defs
import Submission.Commons.Analysis.Integral.exists_dual_witness

open scoped BigOperators

namespace Work.BourgainPlan.IonescuWainger

noncomputable section

/-- The tentative extremal vector of a single fibre `v : ι → ℂ`, namely
`(n2 v)⁻¹ • conj v`.  It satisfies `n2 (dwVec v) ≤ 1` and pairs with `v` to give
`∑ i, v i * dwVec v i = n2 v` (a nonnegative real). -/
def dwVec {ι : Type*} [Fintype ι] (v : ι → ℂ) : ι → ℂ :=
  fun i => (((n2 v)⁻¹ : ℝ) : ℂ) * (starRingEnd ℂ) (v i)

lemma n2_conj {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    n2 (fun i => (starRingEnd ℂ) (v i)) = n2 v := by
  unfold n2 n2sq
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [Complex.norm_conj]

lemma dwVec_pair {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    (∑ i, v i * dwVec v i) = ((n2 v : ℝ) : ℂ) := by
  have h1 : (∑ i, v i * (starRingEnd ℂ) (v i)) = ∑ i, ((‖v i‖ ^ 2 : ℝ) : ℂ) :=
    Finset.sum_congr rfl fun i _ => by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hinner : (∑ i, v i * (starRingEnd ℂ) (v i)) = ((n2sq v : ℝ) : ℂ) := by
    rw [h1, n2sq]
    exact (Complex.ofReal_sum Finset.univ (fun i => ‖v i‖ ^ 2)).symm
  have hstep : (∑ i, v i * dwVec v i)
      = (((n2 v)⁻¹ : ℝ) : ℂ) * (∑ i, v i * (starRingEnd ℂ) (v i)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      simp only [dwVec]; ring
  rw [hstep, hinner, ← Complex.ofReal_mul, ← sq_n2]
  congr 1
  rcases eq_or_ne (n2 v) 0 with h | h
  · simp [h]
  · rw [sq, ← mul_assoc, inv_mul_cancel₀ h, one_mul]

lemma dwVec_norm_le {ι : Type*} [Fintype ι] (v : ι → ℂ) : n2 (dwVec v) ≤ 1 := by
  have heq : dwVec v = (((n2 v)⁻¹ : ℝ) : ℂ) • (fun i => (starRingEnd ℂ) (v i)) := rfl
  rw [heq, n2_smul, n2_conj]
  have hnorm : ‖(((n2 v)⁻¹ : ℝ) : ℂ)‖ = (n2 v)⁻¹ := by
    rw [Complex.norm_def, Complex.normSq_ofReal,
      Real.sqrt_mul_self (inv_nonneg.mpr (n2_nonneg v))]
  rw [hnorm]
  rcases eq_or_ne (n2 v) 0 with h | h
  · simp [h]
  · rw [inv_mul_cancel₀ h]

/-- **Dual witness for the mixed `ℓ^p(β; ℓ²(ι))` norm.**  For `1 < p`, every
`u : β → ι → ℂ` (finite `β`, `ι`) admits a `g : β → ι → ℂ` whose mixed conjugate
norm `(∑ b, (n2 (g b)) ^ (p/(p-1)))` is `≤ 1` and which realises the mixed norm of `u`
against the (unconjugated) pairing `∑ b, ∑ i, u b i * g b i`: here
`mLp u p = (∑ b, (n2 (u b)) ^ p) ^ (1/p)` with `n2 v = sqrt (∑ i, ‖v i‖^2)`, so
`mLp u p = (∑ b, (∑ i, ‖u b i‖ ^ 2) ^ (p/2)) ^ (1/p)`.  This is the equality case of
Hölder's inequality: `g b` is proportional to the conjugate of `u b`, scaled so that
`n2 (g b) = ‖λ b‖` for a scalar extremiser `λ` of the sequence `b ↦ n2 (u b)`
(`Commons.Analysis.Integral.exists_dual_witness`); when `u = 0` the choice `g = 0` works.
The upper bound `≤ 1` (rather than `= 1`) makes the statement total in `u = 0`. -/
theorem mLp_dual_witness {β ι : Type*} [Fintype β] [Fintype ι] {p : ℝ} (hp : 1 < p)
    (u : β → ι → ℂ) :
    ∃ g : β → ι → ℂ, (∑ b, (n2 (g b)) ^ (p / (p - 1))) ≤ 1 ∧
      mLp u p ≤ ‖∑ b, ∑ i, u b i * g b i‖ := by
  have hp0 : 0 < p := lt_trans one_pos hp
  have hp1 : 0 < p - 1 := by linarith
  by_cases hu : u = 0
  · subst hu
    refine ⟨0, ?_, ?_⟩
    · have h : (∑ b, (n2 ((0 : β → ι → ℂ) b)) ^ (p / (p - 1))) = 0 := by
        simp only [Pi.zero_apply, n2_zero, Real.zero_rpow (ne_of_gt (div_pos hp0 hp1)),
          Finset.sum_const_zero]
      rw [h]; norm_num
    · have hmlp : mLp (0 : β → ι → ℂ) p = 0 := by
        have hq : (1:ℝ) / p ≠ 0 := ne_of_gt (one_div_pos.mpr hp0)
        simp only [mLp, Pi.zero_apply, n2_zero, Real.zero_rpow (ne_of_gt hp0),
          Finset.sum_const_zero, Real.zero_rpow hq]
      rw [hmlp]
      exact norm_nonneg _
  · have hq1 : 1 < p / (p - 1) := by
      rw [lt_div_iff₀ hp1]; linarith
    have hq0 : 0 < p / (p - 1) := lt_trans one_pos hq1
    have hconj : 1 / p + 1 / (p / (p - 1)) = 1 := by
      rw [one_div_div]
      field_simp
      ring
    have ha : (fun b => ((n2 (u b) : ℝ) : ℂ)) ≠ 0 := by
      intro h
      apply hu
      funext b i
      have hb : ((n2 (u b) : ℝ) : ℂ) = 0 := congr_fun h b
      have hb0 : n2 (u b) = 0 := Complex.ofReal_eq_zero.mp hb
      exact congr_fun ((n2_eq_zero_iff (u b)).mp hb0) i
    obtain ⟨g₀, hg₀norm, hg₀pair⟩ :=
      Commons.Analysis.Integral.exists_dual_witness hp hq1 hconj
        (fun b => ((n2 (u b) : ℝ) : ℂ)) ha
    refine ⟨fun b => g₀ b • dwVec (u b), ?_, ?_⟩
    · have hT : (∑ b, ‖g₀ b‖ ^ (p / (p - 1))) = 1 := by
        have hTnn : 0 ≤ ∑ b, ‖g₀ b‖ ^ (p / (p - 1)) :=
          Finset.sum_nonneg fun b _ => Real.rpow_nonneg (norm_nonneg _) _
        have hexp : 1 / (p / (p - 1)) * (p / (p - 1)) = 1 := by
          rw [one_div, inv_mul_cancel₀ (ne_of_gt hq0)]
        have h := congrArg (fun x : ℝ => x ^ (p / (p - 1))) hg₀norm
        rw [← Real.rpow_mul hTnn, hexp, Real.rpow_one, Real.one_rpow] at h
        exact h
      calc (∑ b, (n2 (g₀ b • dwVec (u b))) ^ (p / (p - 1)))
          ≤ ∑ b, ‖g₀ b‖ ^ (p / (p - 1)) := by
            refine Finset.sum_le_sum fun b _ => ?_
            refine Real.rpow_le_rpow (n2_nonneg _) ?_ (le_of_lt hq0)
            rw [n2_smul]
            have := dwVec_norm_le (u b)
            nlinarith [norm_nonneg (g₀ b)]
        _ = 1 := hT
    · have hfiber : ∀ b, (∑ i, u b i * (g₀ b • dwVec (u b)) i)
          = ((n2 (u b) : ℝ) : ℂ) * g₀ b := by
        intro b
        have hstep : (∑ i, u b i * (g₀ b • dwVec (u b)) i)
            = g₀ b * (∑ i, u b i * dwVec (u b) i) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [Pi.smul_apply, smul_eq_mul]
          ring
        rw [hstep, dwVec_pair]
        ring
      have hpair_eq : (∑ b, ((n2 (u b) : ℝ) : ℂ) * g₀ b)
          = ∑ b, ∑ i, u b i * (g₀ b • dwVec (u b)) i :=
        Finset.sum_congr rfl fun b _ => (hfiber b).symm
      have hmLp_eq : mLp u p
          = (∑ b, ‖((n2 (u b) : ℝ) : ℂ)‖ ^ p) ^ (1 / p) := by
        rw [mLp]
        congr 1
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Complex.norm_def, Complex.normSq_ofReal,
          Real.sqrt_mul_self (n2_nonneg (u b))]
      rw [hmLp_eq, ← hpair_eq]
      exact hg₀pair

end

end Work.BourgainPlan.IonescuWainger
