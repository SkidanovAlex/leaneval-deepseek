import Mathlib
import Submission.Work.TMComp.Schnol.WindowSum

/-!
# Component C15 (`P_Schnol`): the finite-volume selection

Given a vector `X` of norm `1` on the window `[-M, M]` which is supported on the sites of a
finite set `s` and which almost solves `(winMat - E₀) X = 0` (defect `≤ ε`), we produce an
energy `E` with `|E - E₀| ≤ η` and a solution `u` of the almost Mathieu equation on the window
with `|u m| ≤ 1 + |m|` everywhere and with at least `1/(2*Wtot)` of the mass of `u` on `s`.
-/

open scoped ENNReal
open Matrix LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMComp.Schnol

/-- Multiplication of a vector by a constant commutes with `mulVec`. -/
theorem mulVec_const_mul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (v : Fin n → ℂ) :
    A.mulVec (fun i => c * v i) = fun i => c * A.mulVec v i := by
  funext i
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by ring)

theorem winMatSelect (M : ℕ) (α lam θ : ℝ) {E₀ : ℝ} {s : Finset ℤ}
    (hs : ∀ m ∈ s, -(M : ℤ) ≤ m ∧ m ≤ (M : ℤ))
    (X : EuclideanSpace ℂ (Fin (2 * M + 1))) (hX : ‖X‖ = 1)
    (hXsupp : ∀ i : Fin (2 * M + 1), ((i : ℤ) - (M : ℤ)) ∉ s → X.ofLp i = 0)
    {η ε : ℝ} (hε0 : 0 ≤ ε) (hεη : 4 * ε ^ 2 ≤ η ^ 2) (hη : 0 < η)
    (hXeig : ‖(winMat M α lam θ).toEuclideanLin X - (E₀ : ℂ) • X‖ ≤ ε) :
    ∃ (E : ℝ) (u : ℤ → ℂ),
      |E - E₀| ≤ η ∧
      (∀ m : ℤ, ‖u m‖ ≤ 1 + |(m : ℝ)|) ∧
      (1 / (2 * Wtot)) ≤ ∑ m ∈ s, ‖u m‖ ^ 2 ∧
      (∀ m : ℤ, -(M : ℤ) ≤ m → m ≤ (M : ℤ) →
        Work.TMContract.amoAct α lam θ u m = (E : ℂ) * u m) ∧
      (∀ m : ℤ, (m < -(M : ℤ) ∨ (M : ℤ) < m) → u m = 0) := by
  classical
  set hA := winMatHermitian M α lam θ with hAherm
  set b : OrthonormalBasis (Fin (2 * M + 1)) ℂ (EuclideanSpace ℂ (Fin (2 * M + 1))) :=
    hA.eigenvectorBasis with hbdef
  set Ev : Fin (2 * M + 1) → ℝ := hA.eigenvalues with hEdef
  set F : Finset (Fin (2 * M + 1)) :=
    Finset.univ.filter (fun i : Fin (2 * M + 1) => ((i : ℤ) - (M : ℤ)) ∈ s) with hFdef
  set aa : Fin (2 * M + 1) → ℝ := fun j => ∑ i ∈ F, ‖(b j).ofLp i‖ ^ 2 with hadef
  set bb : Fin (2 * M + 1) → ℝ :=
    fun j => ∑ i : Fin (2 * M + 1), wt ((i : ℤ) - (M : ℤ)) * ‖(b j).ofLp i‖ ^ 2 with hbdef
  set G : Finset (Fin (2 * M + 1)) := Finset.univ.filter (fun j => |Ev j - E₀| < η) with hGdef
  set Gb : Finset (Fin (2 * M + 1)) := Finset.univ.filter (fun j => ¬ (|Ev j - E₀| < η))
    with hGbdef
  have hcoord : ∀ i : Fin (2 * M + 1), ∑ j, ‖(b j).ofLp i‖ ^ 2 = 1 :=
    fun i => (onbFacts b X).2.1 i
  have haarith : ∀ j : Fin (2 * M + 1), ∑ i ∈ F, ‖(b j).ofLp i‖ ^ 2 ≤ ∑ i, ‖(b j).ofLp i‖ ^ 2 :=
    fun j => Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ => by positivity)
  -- the energy identity
  have henergy : (∑ j : Fin (2 * M + 1), (Ev j - E₀) ^ 2 * ‖inner ℂ (b j) X‖ ^ 2) ≤ ε ^ 2 := by
    have h2 : ‖(winMat M α lam θ).toEuclideanLin X - (E₀ : ℂ) • X‖ ≤ ε := hXeig
    have h3 := energyIdentity (winMat M α lam θ) hA X E₀
    have h4 : (‖(winMat M α lam θ).toEuclideanLin X - (E₀ : ℂ) • X‖) ^ 2 ≤ ε ^ 2 := by
      nlinarith [h2, hε0, norm_nonneg ((winMat M α lam θ).toEuclideanLin X - (E₀ : ℂ) • X)]
    calc (∑ j : Fin (2 * M + 1), (Ev j - E₀) ^ 2 * ‖inner ℂ (b j) X‖ ^ 2)
        = (∑ j : Fin (2 * M + 1),
            (hA.eigenvalues j - E₀) ^ 2 * ‖inner ℂ (hA.eigenvectorBasis j) X‖ ^ 2) := rfl
      _ = ‖(winMat M α lam θ).toEuclideanLin X - (E₀ : ℂ) • X‖ ^ 2 := h3.symm
      _ ≤ ε ^ 2 := h4
  -- Parseval
  have hparse : (∑ j : Fin (2 * M + 1), ‖inner ℂ (b j) X‖ ^ 2) = 1 := by
    rw [(onbFacts b X).1, hX]
    norm_num
  -- the bad part
  have hbad : (∑ j ∈ Gb, ‖inner ℂ (b j) X‖ ^ 2) ≤ ε ^ 2 / η ^ 2 := by
    have hstep1 : η ^ 2 * (∑ j ∈ Gb, ‖inner ℂ (b j) X‖ ^ 2)
        = ∑ j ∈ Gb, η ^ 2 * ‖inner ℂ (b j) X‖ ^ 2 := Finset.mul_sum ..
    have hstep2 : (∑ j ∈ Gb, η ^ 2 * ‖inner ℂ (b j) X‖ ^ 2)
        ≤ ∑ j ∈ Gb, (Ev j - E₀) ^ 2 * ‖inner ℂ (b j) X‖ ^ 2 := by
      refine Finset.sum_le_sum (fun j hj => ?_)
      have hmem : ¬ (|Ev j - E₀| < η) := (Finset.mem_filter.mp hj).2
      have h1 : η ≤ |Ev j - E₀| := not_lt.mp hmem
      have h2 : η ^ 2 ≤ (Ev j - E₀) ^ 2 := by
        have h3 : η ^ 2 ≤ |Ev j - E₀| ^ 2 := pow_le_pow_left₀ hη.le h1 2
        rwa [sq_abs] at h3
      exact mul_le_mul_of_nonneg_right h2 (by positivity)
    have hstep3 : (∑ j ∈ Gb, (Ev j - E₀) ^ 2 * ‖inner ℂ (b j) X‖ ^ 2)
        ≤ ∑ j, (Ev j - E₀) ^ 2 * ‖inner ℂ (b j) X‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun j _ _ => by positivity)
    have hkey : η ^ 2 * (∑ j ∈ Gb, ‖inner ℂ (b j) X‖ ^ 2) ≤ ε ^ 2 := by
      linarith [hstep1, hstep2, hstep3, henergy]
    have hη2 : (0 : ℝ) < η ^ 2 := by positivity
    refine (le_div_iff₀ hη2).mpr ?_
    linarith [hkey]
  have hgood : 3 / 4 ≤ ∑ j ∈ G, ‖inner ℂ (b j) X‖ ^ 2 := by
    have hsplit : (∑ j ∈ G, ‖inner ℂ (b j) X‖ ^ 2) + ∑ j ∈ Gb, ‖inner ℂ (b j) X‖ ^ 2 = 1 := by
      rw [hGdef, hGbdef, Finset.sum_filter_add_sum_filter_not]
      exact hparse
    have h14 : ε ^ 2 / η ^ 2 ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hεη]
    linarith
  have ha_nonneg : ∀ j, 0 ≤ aa j := fun j => by
    rw [hadef]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hb_nonneg : ∀ j, 0 ≤ bb j := fun j => by
    rw [hbdef]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (wt_nonneg _) (sq_nonneg _))
  -- Cauchy-Schwarz: the coefficient of `X` along the support is bounded by `aa`
  have hCS : ∀ j : Fin (2 * M + 1), ‖inner ℂ (b j) X‖ ^ 2 ≤ aa j := by
    intro j
    have hinner : inner ℂ (b j) X
        = ∑ i : Fin (2 * M + 1), starRingEnd ℂ ((b j).ofLp i) * X.ofLp i := by
      rw [PiLp.inner_apply]
      exact Finset.sum_congr rfl (fun i _ => RCLike.inner_apply' _ _)
    have hF : (∑ i : Fin (2 * M + 1), starRingEnd ℂ ((b j).ofLp i) * X.ofLp i)
        = ∑ i ∈ F, starRingEnd ℂ ((b j).ofLp i) * X.ofLp i := by
      rw [← Finset.sum_subset (Finset.subset_univ F)]
      intro i _ hi
      have hnot : ((i : ℤ) - (M : ℤ)) ∉ s := by
        intro hmem
        exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hmem⟩)
      rw [hXsupp i hnot, mul_zero]
    rw [hinner, hF]
    have hCS' := norm_sum_mul_sq_le F (fun i => starRingEnd ℂ ((b j).ofLp i)) (fun i => X.ofLp i)
    have hnormb : (∑ i ∈ F, ‖starRingEnd ℂ ((b j).ofLp i)‖ ^ 2) = aa j := by
      rw [hadef]
      exact Finset.sum_congr rfl (fun i _ => by rw [Complex.norm_conj])
    have hnormX : (∑ i ∈ F, ‖X.ofLp i‖ ^ 2) ≤ 1 := by
      have h1 : (∑ i ∈ F, ‖X.ofLp i‖ ^ 2) ≤ ∑ i : Fin (2 * M + 1), ‖X.ofLp i‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => by positivity)
      have h2 : (∑ i : Fin (2 * M + 1), ‖X.ofLp i‖ ^ 2) = 1 := by
        rw [(PiLp.norm_sq_eq_of_L2 (fun _ : Fin (2 * M + 1) => ℂ) X).symm, hX]
        norm_num
      linarith [h1, h2.le, h2.ge]
    calc ‖∑ i ∈ F, starRingEnd ℂ ((b j).ofLp i) * X.ofLp i‖ ^ 2
        ≤ (∑ i ∈ F, ‖starRingEnd ℂ ((b j).ofLp i)‖ ^ 2) * (∑ i ∈ F, ‖X.ofLp i‖ ^ 2) := hCS'
      _ ≤ aa j * 1 := by
          rw [hnormb]
          exact mul_le_mul_of_nonneg_left hnormX (ha_nonneg j)
      _ = aa j := mul_one _
  have h1 : 3 / 4 ≤ ∑ j ∈ G, aa j :=
    le_trans hgood (Finset.sum_le_sum fun j _ => hCS j)
  have hsum_bb : (∑ j, bb j) ≤ Wtot := by
    have h1 : (∑ j : Fin (2 * M + 1), bb j) = ∑ i : Fin (2 * M + 1), wt ((i : ℤ) - (M : ℤ)) := by
      rw [hbdef, Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.mul_sum, hcoord i, mul_one]
    rw [h1]
    exact le_trans (le_of_eq (sum_window_eq_sum_fin M wt)) (sum_winFinset_wt_le M)
  have h2 : (1 / (2 * Wtot)) * (∑ j, bb j) ≤ 1 / 2 := by
    have hW : 0 < Wtot := Wtot_pos
    have hle : (1 / (2 * Wtot)) * (∑ j, bb j) ≤ (1 / (2 * Wtot)) * Wtot :=
      mul_le_mul_of_nonneg_left hsum_bb (by have h := Wtot_pos; positivity)
    have h3 : (1 / (2 * Wtot)) * Wtot = 1 / 2 := by
      field_simp
    rw [h3] at hle
    exact hle
  obtain ⟨j₀, hj₀G, hj₀ineq, hj₀pos⟩ :=
    pigeonhole aa bb G (c := 1 / (2 * Wtot)) (by have h := Wtot_pos; positivity) h1 h2 ha_nonneg hb_nonneg
  have hj₀eta : |Ev j₀ - E₀| < η := (Finset.mem_filter.mp hj₀G).2
  have hwt_le : ∀ i : Fin (2 * M + 1), wt ((i : ℤ) - (M : ℤ)) * ‖(b j₀).ofLp i‖ ^ 2 ≤ bb j₀ := by
    intro i
    simp only [hbdef]
    exact Finset.single_le_sum
      (f := fun i' : Fin (2 * M + 1) => wt ((i' : ℤ) - (M : ℤ)) * ‖(b j₀).ofLp i'‖ ^ 2)
      (fun i' _ => mul_nonneg (wt_nonneg _) (sq_nonneg _)) (Finset.mem_univ i)
  have hbbpos : 0 < bb j₀ := by
    have hex : ∃ i ∈ F, 0 < ‖(b j₀).ofLp i‖ ^ 2 := by
      by_contra hc
      have hle : (∑ i ∈ F, ‖(b j₀).ofLp i‖ ^ 2) ≤ 0 := by
        refine Finset.sum_nonpos fun i hi => ?_
        by_contra hpos
        exact hc ⟨i, hi, not_le.mp hpos⟩
      rw [hadef] at hj₀pos
      linarith
    obtain ⟨i, hiF, hipos⟩ := hex
    have hipos' : 0 < ‖(b j₀).ofLp i‖ := by nlinarith [norm_nonneg ((b j₀).ofLp i)]
    nlinarith [hwt_le i, wt_pos ((i : ℤ) - (M : ℤ)), hipos']
  set r : ℝ := (Real.sqrt (bb j₀))⁻¹ with hrdef
  have hrpos : 0 < r := by rw [hrdef]; exact inv_pos.mpr (Real.sqrt_pos.mpr hbbpos)
  have hrsq : r ^ 2 = (bb j₀)⁻¹ := by
    rw [hrdef, inv_pow, Real.sq_sqrt (hb_nonneg j₀)]
  set w : Fin (2 * M + 1) → ℂ := fun i => (r : ℂ) * (b j₀).ofLp i with hwdef
  have hwnorm : ∀ i, ‖w i‖ = r * ‖(b j₀).ofLp i‖ := by
    intro i
    rw [hwdef]
    simp only
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos]
  have hE : (winMat M α lam θ).mulVec w = (Ev j₀ : ℂ) • w := by
    have h1 : (winMat M α lam θ).mulVec (b j₀).ofLp = (Ev j₀ : ℂ) • (b j₀).ofLp := by
      have h := hA.mulVec_eigenvectorBasis j₀
      rw [← hEdef] at h
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ)] at h
      simpa using h
    have hw : w = fun i => (r : ℂ) * (b j₀).ofLp i := rfl
    rw [hw, mulVec_const_mul, h1]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  refine ⟨Ev j₀, ext M w, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_of_lt hj₀eta
  · intro m
    by_cases hm : m ∈ winFinset M
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hm
      rw [ext_eq M w i, hwnorm i]
      have hx2 : ‖(b j₀).ofLp i‖ ^ 2 ≤ bb j₀ * (1 + |(((i : ℤ) - (M : ℤ) : ℤ) : ℝ)|) ^ 2 := by
        have h := hwt_le i
        rw [wt] at h
        have h5 : 0 < (1 + |(((i : ℤ) - (M : ℤ) : ℤ) : ℝ)|)⁻¹ ^ 2 := by positivity
        have h6 : ‖(b j₀).ofLp i‖ ^ 2
            ≤ bb j₀ / ((1 + |(((i : ℤ) - (M : ℤ) : ℤ) : ℝ)|)⁻¹ ^ 2) :=
          (le_div_iff₀ h5).mpr (by rw [mul_comm]; exact h)
        have h7 : bb j₀ / ((1 + |(((i : ℤ) - (M : ℤ) : ℤ) : ℝ)|)⁻¹ ^ 2)
            = bb j₀ * (1 + |(((i : ℤ) - (M : ℤ) : ℤ) : ℝ)|) ^ 2 := by
          field_simp
        linarith [h6, h7.le, h7.ge]
      have hbound : ‖(b j₀).ofLp i‖ ≤ Real.sqrt (bb j₀) * (1 + |(((i : ℤ) - (M : ℤ) : ℤ) : ℝ)|) := by
        have hy : (0 : ℝ) ≤ 1 + |(((i : ℤ) - (M : ℤ) : ℤ) : ℝ)| := by positivity
        have hs := Real.sqrt_le_sqrt hx2
        rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (hb_nonneg j₀), Real.sqrt_sq hy] at hs
        exact hs
      have hsqrt : 0 < Real.sqrt (bb j₀) := Real.sqrt_pos.mpr hbbpos
      calc r * ‖(b j₀).ofLp i‖
          ≤ r * (Real.sqrt (bb j₀) * (1 + |(((i : ℤ) - (M : ℤ) : ℤ) : ℝ)|)) :=
            mul_le_mul_of_nonneg_left hbound hrpos.le
        _ = 1 + |(((i : ℤ) - (M : ℤ) : ℤ) : ℝ)| := by
            rw [hrdef]
            field_simp
    · have hnot : m < -(M : ℤ) ∨ (M : ℤ) < m := by
        by_contra hc
        rw [not_or, not_lt, not_lt] at hc
        exact hm (mem_winFinset.mpr ⟨hc.1, hc.2⟩)
      rcases hnot with h | h
      · rw [ext_eq_zero_of_lt M w h, norm_zero]
        positivity
      · rw [ext_eq_zero_of_gt M w h, norm_zero]
        positivity
  · rw [sum_subset_window M s (fun m hm => mem_winFinset.mpr (hs m hm)) (fun m => ‖ext M w m‖ ^ 2)]
    have hF : ∀ i ∈ F, ‖ext M w ((i : ℤ) - (M : ℤ))‖ ^ 2 = (bb j₀)⁻¹ * ‖(b j₀).ofLp i‖ ^ 2 := by
      intro i _
      rw [ext_eq M w i, hwnorm i, mul_pow, hrsq]
    rw [Finset.sum_congr rfl hF]
    rw [← Finset.mul_sum]
    have hci : (1 / (2 * Wtot)) * bb j₀ ≤ aa j₀ := hj₀ineq
    have hW : 0 < Wtot := Wtot_pos
    have hexp : (bb j₀)⁻¹ * aa j₀ = aa j₀ / bb j₀ := by rw [div_eq_inv_mul]
    rw [hexp]
    rw [le_div_iff₀ hbbpos]
    calc (1 / (2 * Wtot)) * bb j₀ ≤ aa j₀ := hci
      _ = aa j₀ := rfl
  · intro m hm1 hm2
    exact extRecur M α lam θ w hE m hm1 hm2
  · intro m hm
    rcases hm with h | h
    · rw [ext_eq_zero_of_lt M w h]
    · rw [ext_eq_zero_of_gt M w h]

end Work.TMComp.Schnol
