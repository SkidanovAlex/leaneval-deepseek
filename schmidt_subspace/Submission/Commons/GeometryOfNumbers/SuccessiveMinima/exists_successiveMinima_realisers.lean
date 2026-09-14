import Mathlib
import Submission.Commons.GeometryOfNumbers.SuccessiveMinima.gauge_realizers_exclusion
import Submission.Commons.GeometryOfNumbers.Box.finite_int_points_box
import Submission.Commons.LinearAlgebra.Dimension.linearIndependent_mem_of_le_finrank_span
import Submission.Commons.LinearAlgebra.Dimension.intVec_linearIndependent_rat_of_real
import Submission.Commons.LinearAlgebra.Dimension.intVec_mem_span_rat_of_mem_span_real

namespace Commons.GeometryOfNumbers.SuccessiveMinima

open scoped BigOperators TensorProduct Pointwise
open Set Matrix

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-! ## Auxiliary lemmas -/

/-- `‖(r : ℂ)‖ = r` for `r ≥ 0`. -/
private lemma norm_ofReal_of_nonneg {r : ℝ} (hr : 0 ≤ r) : ‖(r : ℂ)‖ = r :=
  (RCLike.norm_ofReal r).trans (abs_of_nonneg hr)

/-- ℚ-linear independence of integer vectors implies ℝ-linear independence. -/
private theorem intVec_real_li_of_rat_li {N : ℕ} {ι : Type*} [Fintype ι]
    (x : ι → Fin N → ℤ)
    (h : LinearIndependent ℚ (fun i => fun k => (x i k : ℚ))) :
    LinearIndependent ℝ (fun i => fun k => (x i k : ℝ)) := by
  set xq : ι → (Fin N → ℚ) := fun i k => (x i k : ℚ) with hxq
  have hxh : (fun i => fun k => (x i k : ℚ)) = xq := rfl
  have h' : LinearIndependent ℚ xq := hxh ▸ h
  have hbase : LinearIndependent ℝ (fun i => (1 : ℝ) ⊗ₜ[ℚ] xq i) :=
    Module.Flat.linearIndependent_one_tmul (R := ℚ) (S := ℝ) (M := Fin N → ℚ) h'
  let e : (ℝ ⊗[ℚ] (Fin N → ℚ)) ≃ₗ[ℝ] (Fin N → ℝ) :=
    TensorProduct.piScalarRight ℚ ℝ ℝ (Fin N)
  have heq : (fun i => e ((1 : ℝ) ⊗ₜ[ℚ] xq i)) = (fun i => fun k => (x i k : ℝ)) := by
    funext i k
    rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
    simp [xq, Algebra.smul_def]
  rw [← heq]
  exact hbase.map' (e : (ℝ ⊗[ℚ] (Fin N → ℚ)) →ₗ[ℝ] (Fin N → ℝ)) (LinearEquiv.ker _)

/-- A point of the box (in real coordinates) has bounded norm. -/
private theorem box_norm_bound {N : ℕ} (L : Fin N → Fin N → ℂ) (hdet : (Matrix.of L).det ≠ 0)
    (M : Fin N → ℝ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ y : Fin N → ℝ,
      (∀ i, ‖∑ k, L i k * (y k : ℂ)‖ ≤ M i) → ‖y‖ ≤ R := by
  classical
  let A : Matrix (Fin N) (Fin N) ℂ := Matrix.of L
  have hAdet : A.det ≠ 0 := by simpa [A] using hdet
  have hdpos : 0 < ‖A.det‖ := norm_pos_iff.mpr hAdet
  set B : Fin N → ℝ := fun k => (∑ i, ‖A.adjugate k i‖ * max (M i) 0) / ‖A.det‖ with hBdef
  have hBnn : ∀ k, 0 ≤ B k := fun k =>
    div_nonneg (Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (le_max_right _ _)))
      hdpos.le
  have hkey : ∀ y : Fin N → ℝ, (∀ i, ‖∑ k, L i k * (y k : ℂ)‖ ≤ M i) → ∀ k, ‖y k‖ ≤ B k := by
    intro y hy k
    set v : Fin N → ℂ := fun k => (y k : ℂ) with hvdef
    have hvi : ∀ i, (A *ᵥ v) i = ∑ k, L i k * (y k : ℂ) := fun i => rfl
    have hz : ∀ i, ‖(A *ᵥ v) i‖ ≤ max (M i) 0 := fun i =>
      le_trans (by rw [hvi i]; exact hy i) (le_max_left _ _)
    have hmul : A.det * v k = ∑ i, A.adjugate k i * (A *ᵥ v) i := by
      have h1 : A.adjugate *ᵥ (A *ᵥ v) = A.det • v := by
        rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
      have h := congr_fun h1 k
      rw [show (A.adjugate *ᵥ (A *ᵥ v)) k = ∑ i, A.adjugate k i * (A *ᵥ v) i from rfl] at h
      rw [show (A.det • v) k = A.det * v k from rfl] at h
      exact h.symm
    have hbound : ‖A.det‖ * ‖v k‖ ≤ ∑ i, ‖A.adjugate k i‖ * max (M i) 0 := by
      calc ‖A.det‖ * ‖v k‖ = ‖A.det * v k‖ := (norm_mul _ _).symm
        _ = ‖∑ i, A.adjugate k i * (A *ᵥ v) i‖ := by rw [hmul]
        _ ≤ ∑ i, ‖A.adjugate k i * (A *ᵥ v) i‖ := norm_sum_le _ _
        _ = ∑ i, ‖A.adjugate k i‖ * ‖(A *ᵥ v) i‖ := by
              apply Finset.sum_congr rfl; intro i _; rw [norm_mul]
        _ ≤ ∑ i, ‖A.adjugate k i‖ * max (M i) 0 := by
              apply Finset.sum_le_sum; intro i _
              exact mul_le_mul_of_nonneg_left (hz i) (norm_nonneg _)
    have hsum : ∑ i, ‖A.adjugate k i‖ * max (M i) 0 = B k * ‖A.det‖ := by
      rw [hBdef]
      exact (div_mul_cancel₀ _ hdpos.ne').symm
    have h2 : ‖v k‖ * ‖A.det‖ ≤ B k * ‖A.det‖ := by
      rw [hsum] at hbound
      simpa [mul_comm] using hbound
    have hvk : ‖v k‖ = ‖y k‖ := by
      rw [hvdef]
      simp only
      exact RCLike.norm_ofReal (y k)
    rw [hvk] at h2
    exact le_of_mul_le_mul_right h2 hdpos
  refine ⟨∑ k, B k, Finset.sum_nonneg (fun k _ => hBnn k), fun y hy => ?_⟩
  rw [pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun k _ => hBnn k))]
  intro k
  exact le_trans (hkey y hy k) (Finset.single_le_sum (fun i _ => hBnn i) (Finset.mem_univ k))

/-- If all the `L`-forms of an integer vector vanish then the vector vanishes. -/
private lemma eq_zero_of_forms_eq_zero {N : ℕ} (L : Fin N → Fin N → ℂ)
    (hdet : (Matrix.of L).det ≠ 0) (y : Fin N → ℤ)
    (h : ∀ i, ∑ k, L i k * (y k : ℂ) = 0) : y = 0 := by
  classical
  let A : Matrix (Fin N) (Fin N) ℂ := Matrix.of L
  have hAdet : A.det ≠ 0 := by simpa [A] using hdet
  have h1 : A *ᵥ (fun k => (y k : ℂ)) = 0 := by
    funext i
    rw [Pi.zero_apply]
    exact h i
  have h2 : A.det • (fun k => (y k : ℂ)) = 0 := by
    have hc := congrArg (fun w => A.adjugate *ᵥ w) h1
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_zero] at hc
    exact hc
  funext k
  have hk := congr_fun h2 k
  simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hk
  have hz : (y k : ℂ) = 0 := (mul_eq_zero.mp hk).resolve_left hAdet
  simpa using hz

/-! ## The main lemma -/

theorem exists_successiveMinima_realisers {N : ℕ} (hN : 1 ≤ N)
    (L : Fin N → Fin N → ℂ) (hdet : (Matrix.of L).det ≠ 0)
    (Q : ℝ) (hQ : 1 ≤ Q) (c : Fin N → ℝ) (lam : ℕ → ℝ)
    (hlam : ∀ j : ℕ, j < N → lam j = sInf {t : ℝ | 0 ≤ t ∧ (j + 1) ≤ Module.finrank ℚ
      (Submodule.span ℚ (Set.image (fun y : Fin N → ℤ => fun k => (y k : ℚ))
        {y : Fin N → ℤ | ∀ i, ‖∑ k, L i k * (y k : ℂ)‖ ≤ t * Q ^ (c i)}))}) :
    ∃ x : Fin N → Fin N → ℤ,
      (∀ j, x j ≠ 0) ∧
      LinearIndependent ℚ (fun j : Fin N => fun k : Fin N => (x j k : ℚ)) ∧
      (∀ j i, ‖∑ k, L i k * (x j k : ℂ)‖ ≤ lam j.val * Q ^ (c i)) ∧
      (∀ (j : Fin N) (t : ℝ), 0 < t → t < lam j.val → ∀ y : Fin N → ℤ,
        (∀ i, ‖∑ k, L i k * (y k : ℂ)‖ ≤ t * Q ^ (c i)) →
        (fun k => (y k : ℚ)) ∈ Submodule.span ℚ
          (Set.range (fun i : {i : Fin N // i < j} => fun k => (x i.1 k : ℚ)))) := by
  classical
  have hQpos : 0 < Q := lt_of_lt_of_le one_pos hQ
  have hQcpos : ∀ i : Fin N, 0 < Q ^ (c i) := fun i => Real.rpow_pos_of_pos hQpos _
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let boxZ : ℝ → Set (Fin N → ℤ) :=
    fun t => {y : Fin N → ℤ | ∀ i, ‖∑ k, L i k * (y k : ℂ)‖ ≤ t * Q ^ (c i)}
  let K : Set (Fin N → ℝ) :=
    {y : Fin N → ℝ | ∀ i, ‖∑ k, L i k * (y k : ℂ)‖ ≤ Q ^ (c i)}
  have hboxZmem : ∀ (t : ℝ) (y : Fin N → ℤ),
      y ∈ boxZ t ↔ ∀ i, ‖∑ k, L i k * (y k : ℂ)‖ ≤ t * Q ^ (c i) := by
    intro t y; simp [boxZ]
  have hKmem : ∀ y : Fin N → ℝ, y ∈ K ↔ ∀ i, ‖∑ k, L i k * (y k : ℂ)‖ ≤ Q ^ (c i) := by
    intro y; simp [K]
  have h0K : (0 : Fin N → ℝ) ∈ K := by
    rw [hKmem]; intro i
    simp
    exact (hQcpos i).le
  -- ## `K` is a symmetric convex body
  have hKconv : Convex ℝ K := by
    intro x hx y hy a b ha hb hab
    rw [hKmem]
    intro i
    have hx' : ‖∑ k, L i k * (x k : ℂ)‖ ≤ Q ^ (c i) := (hKmem x).mp hx i
    have hy' : ‖∑ k, L i k * (y k : ℂ)‖ ≤ Q ^ (c i) := (hKmem y).mp hy i
    have h1 : (∑ k, L i k * ((a • x + b • y) k : ℂ)) =
        (a:ℂ) * (∑ k, L i k * (x k : ℂ)) + (b:ℂ) * (∑ k, L i k * (y k : ℂ)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    rw [h1]
    calc ‖(a:ℂ) * (∑ k, L i k * (x k : ℂ)) + (b:ℂ) * (∑ k, L i k * (y k : ℂ))‖
        ≤ ‖(a:ℂ) * (∑ k, L i k * (x k : ℂ))‖ + ‖(b:ℂ) * (∑ k, L i k * (y k : ℂ))‖ :=
          norm_add_le _ _
      _ ≤ a * Q ^ (c i) + b * Q ^ (c i) := by
          rw [norm_mul, norm_mul, norm_ofReal_of_nonneg ha, norm_ofReal_of_nonneg hb]
          exact add_le_add (mul_le_mul_of_nonneg_left hx' ha) (mul_le_mul_of_nonneg_left hy' hb)
      _ = Q ^ (c i) := by rw [← add_mul, hab, one_mul]
  have hKsym : ∀ x ∈ K, -x ∈ K := by
    intro x hx
    rw [hKmem] at hx ⊢
    intro i
    have h1 : (∑ k, L i k * ((-x) k : ℂ)) = -(∑ k, L i k * (x k : ℂ)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simp only [Pi.neg_apply]
      push_cast
      ring
    rw [h1, norm_neg]; exact hx i
  have hcont : ∀ i : Fin N, Continuous (fun y : Fin N → ℝ => ∑ k, L i k * (y k : ℂ)) := by
    intro i; fun_prop
  have hKclosed : IsClosed K := by
    have hEq : K = ⋂ i, {y : Fin N → ℝ | ‖∑ k, L i k * (y k : ℂ)‖ ≤ Q ^ (c i)} := by
      ext y; simp [K]
    rw [hEq]
    exact isClosed_iInter (fun i => isClosed_le (continuous_norm.comp (hcont i)) continuous_const)
  have hKbdd : Bornology.IsBounded K := by
    obtain ⟨R, _hR0, hR⟩ := box_norm_bound L hdet (fun i => Q ^ (c i))
    exact isBounded_iff_forall_norm_le.mpr ⟨R, fun y hy => hR y ((hKmem y).mp hy)⟩
  have hKint : (interior K).Nonempty := by
    have hopen : IsOpen {y : Fin N → ℝ | ∀ i, ‖∑ k, L i k * (y k : ℂ)‖ < Q ^ (c i)} := by
      have hEq : {y : Fin N → ℝ | ∀ i, ‖∑ k, L i k * (y k : ℂ)‖ < Q ^ (c i)}
          = ⋂ i, {y : Fin N → ℝ | ‖∑ k, L i k * (y k : ℂ)‖ < Q ^ (c i)} := by
        ext y; simp
      rw [hEq]
      exact isOpen_iInter_of_finite
        (fun i => isOpen_lt (continuous_norm.comp (hcont i)) continuous_const)
    have hsub : {y : Fin N → ℝ | ∀ i, ‖∑ k, L i k * (y k : ℂ)‖ < Q ^ (c i)} ⊆ K := by
      intro y hy; rw [hKmem]; intro i; exact le_of_lt (hy i)
    have h0 : (0 : Fin N → ℝ) ∈ {y : Fin N → ℝ | ∀ i, ‖∑ k, L i k * (y k : ℂ)‖ < Q ^ (c i)} := by
      intro i
      simp
      exact hQcpos i
    exact ⟨0, interior_mono hsub (hopen.interior_eq.symm ▸ h0)⟩
  obtain ⟨x₀, hx₀int⟩ := hKint
  have hKint' : (interior K).Nonempty := ⟨x₀, hx₀int⟩
  have h0int : (0 : Fin N → ℝ) ∈ interior K := by
    have h := hKconv.combo_interior_self_mem_interior hx₀int
      (hKsym x₀ (interior_subset hx₀int)) (a := (1/2:ℝ)) (b := (1/2:ℝ))
      (by norm_num) (by norm_num) (by norm_num)
    simpa using h
  have hAbs : Absorbent ℝ K := absorbent_nhds_zero (mem_interior_iff_mem_nhds.mp h0int)
  have h0K' : (0 : Fin N → ℝ) ∈ K := interior_subset h0int
  -- ## the box at scale `t` is `t • K`
  have hbox_iff : ∀ (t : ℝ), 0 ≤ t → ∀ y : Fin N → ℤ,
      (fun k => (y k : ℝ)) ∈ t • K ↔ y ∈ boxZ t := by
    intro t ht y
    constructor
    · rintro ⟨w, hwK, hwy⟩ i
      have hwK' : ‖∑ k, L i k * (w k : ℂ)‖ ≤ Q ^ (c i) := (hKmem w).mp hwK i
      have hk : ∀ k, (y k : ℂ) = (t:ℂ) * (w k : ℂ) := by
        intro k
        have h1 : t * w k = (y k : ℝ) := by
          have := congr_fun hwy k
          simpa only [Pi.smul_apply, smul_eq_mul] using this
        have h2 : ((y k : ℝ) : ℂ) = ((t * w k : ℝ) : ℂ) := by rw [h1]
        have h3 : (y k : ℂ) = ((y k : ℝ) : ℂ) := by push_cast; ring
        rw [h3, h2]; push_cast; ring
      have h1 : (∑ k, L i k * (y k : ℂ)) = (t:ℂ) * (∑ k, L i k * (w k : ℂ)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun k _ => by rw [hk k]; ring)
      calc ‖∑ k, L i k * (y k : ℂ)‖ = t * ‖∑ k, L i k * (w k : ℂ)‖ := by
            rw [h1, norm_mul, norm_ofReal_of_nonneg ht]
        _ ≤ t * Q ^ (c i) := mul_le_mul_of_nonneg_left hwK' ht
    · intro hy
      rcases eq_or_lt_of_le ht with h0 | htpos
      · have ht0 : t = 0 := h0.symm
        subst ht0
        have hy0 : y = 0 := by
          refine eq_zero_of_forms_eq_zero L hdet y (fun i => ?_)
          have h := (hboxZmem 0 y).mp hy i
          simp only [zero_mul] at h
          exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
        subst hy0
        refine ⟨0, h0K, ?_⟩
        ext k; simp
      · refine ⟨fun k => t⁻¹ * (y k : ℝ), ?_, ?_⟩
        · rw [hKmem]
          intro i
          have hy' : ‖∑ k, L i k * (y k : ℂ)‖ ≤ t * Q ^ (c i) := (hboxZmem t y).mp hy i
          have h1 : (∑ k, L i k * ((t⁻¹ * (y k : ℝ) : ℝ) : ℂ)) =
              (t:ℂ)⁻¹ * (∑ k, L i k * (y k : ℂ)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun k _ => ?_)
            push_cast; ring
          rw [h1, norm_mul, ← Complex.ofReal_inv, norm_ofReal_of_nonneg (inv_nonneg.mpr ht)]
          calc t⁻¹ * ‖∑ k, L i k * (y k : ℂ)‖ ≤ t⁻¹ * (t * Q ^ (c i)) :=
                mul_le_mul_of_nonneg_left hy' (inv_nonneg.mpr ht)
            _ = Q ^ (c i) := by field_simp
        · ext k
          simp only [Pi.smul_apply, smul_eq_mul]
          field_simp
  -- ## rank = maximal number of independent lattice points
  have hrank_iff : ∀ (ℓ : ℕ) (t : ℝ),
      (ℓ ≤ Module.finrank ℚ (Submodule.span ℚ
          (Set.image (fun y : Fin N → ℤ => fun k => (y k : ℚ)) (boxZ t))))
      ↔ ∃ w : Fin ℓ → (Fin N → ℤ), (∀ a, w a ∈ boxZ t) ∧
          LinearIndependent ℚ (fun a => fun k => (w a k : ℚ)) := by
    intro ℓ t
    constructor
    · intro h
      obtain ⟨f, hfmem, hfLI⟩ :=
        Commons.LinearAlgebra.Dimension.linearIndependent_mem_of_le_finrank_span
          (K := ℚ) (M := Fin N → ℚ)
          (s := Set.image (fun y : Fin N → ℤ => fun k => (y k : ℚ)) (boxZ t)) h
      choose w hw using hfmem
      refine ⟨w, fun a => (hw a).1, ?_⟩
      have hfe : (fun a k => (w a k : ℚ)) = f := by
        funext a k
        exact congr_fun (hw a).2 k
      rw [hfe]; exact hfLI
    · rintro ⟨w, hwb, hwLI⟩
      have hsub : Set.range (fun a : Fin ℓ => fun k => (w a k : ℚ)) ⊆
          Set.image (fun y : Fin N → ℤ => fun k => (y k : ℚ)) (boxZ t) := by
        rintro z ⟨a, rfl⟩
        exact ⟨w a, hwb a, rfl⟩
      calc ℓ = Module.finrank ℚ
            (Submodule.span ℚ (Set.range (fun a : Fin ℓ => fun k => (w a k : ℚ)))) := by
            rw [finrank_span_eq_card hwLI, Fintype.card_fin]
        _ ≤ _ := Submodule.finrank_mono (Submodule.span_mono hsub)
  -- ## the two definitions of the successive minima agree
  have hlam_gauge : ∀ j : ℕ, j < N → lam j = sInf {t : ℝ | 0 < t ∧
      ∃ w : Fin (j + 1) → (Fin N → ℤ),
        LinearIndependent ℝ (fun a => fun k => (w a k : ℝ)) ∧
        ∀ a, (fun k => (w a k : ℝ)) ∈ t • K} := by
    intro j hj
    have hboxZ0 : boxZ 0 = {0} := by
      ext y
      rw [hboxZmem 0 y]
      constructor
      · intro hy
        refine eq_zero_of_forms_eq_zero L hdet y (fun i => ?_)
        have h := hy i
        simp only [zero_mul] at h
        exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
      · rintro rfl
        intro i
        simp
    have hgoal : sInf {t : ℝ | 0 ≤ t ∧ (j + 1) ≤ Module.finrank ℚ (Submodule.span ℚ
          (Set.image (fun y : Fin N → ℤ => fun k => (y k : ℚ)) (boxZ t)))}
        = sInf {t : ℝ | 0 < t ∧ ∃ w : Fin (j + 1) → (Fin N → ℤ),
          LinearIndependent ℝ (fun a => fun k => (w a k : ℝ)) ∧
          ∀ a, (fun k => (w a k : ℝ)) ∈ t • K} := by
      congr 1
      ext t
      constructor
      · rintro ⟨ht0, hrank⟩
        have htpos : 0 < t := by
          rcases eq_or_lt_of_le ht0 with h0 | hlt
          · exfalso
            have ht0' : t = 0 := h0.symm
            subst ht0'
            have hz : Module.finrank ℚ (Submodule.span ℚ
                (Set.image (fun y : Fin N → ℤ => fun k => (y k : ℚ)) (boxZ 0))) = 0 := by
              have h1 : (Set.image (fun y : Fin N → ℤ => fun k => (y k : ℚ))
                  (boxZ 0)) = {0} := by
                rw [hboxZ0, Set.image_singleton]
                exact congrArg Set.singleton (by funext k; rfl)
              rw [h1]; simp
            rw [hz] at hrank; omega
          · exact hlt
        obtain ⟨w, hwb, hwLI⟩ := (hrank_iff (j + 1) t).mp hrank
        exact ⟨htpos, w, intVec_real_li_of_rat_li w hwLI,
          fun a => (hbox_iff t ht0 (w a)).mpr (hwb a)⟩
      · rintro ⟨htpos, w, hwLI, hwmem⟩
        refine ⟨htpos.le, (hrank_iff (j + 1) t).mpr ⟨w, fun a => ?_, ?_⟩⟩
        · exact (hbox_iff t htpos.le (w a)).mp (hwmem a)
        · exact Commons.LinearAlgebra.Dimension.intVec_linearIndependent_rat_of_real w hwLI
    rw [hlam j hj]
    exact hgoal
  -- ## the realizers
  obtain ⟨v, hvLI, hvb, hexcl⟩ :=
    gauge_realizers_exclusion N K hKconv hKsym hKclosed hKbdd hKint'
  refine ⟨v, ?_, ?_, ?_, ?_⟩
  · intro j hj
    exact hvLI.ne_zero j (by funext k; simp [hj])
  · exact Commons.LinearAlgebra.Dimension.intVec_linearIndependent_rat_of_real v hvLI
  · intro j i
    have hg : gauge K (fun k => (v j k : ℝ)) ≤ lam j.val := by
      have h2 := hvb j
      rw [hlam_gauge j.val j.isLt]
      exact h2
    have hρnn : 0 ≤ lam j.val := le_trans (gauge_nonneg _) hg
    have hmem : ∀ r : ℝ, lam j.val < r → (fun k => (v j k : ℝ)) ∈ r • K := by
      intro r hr
      have h := setOfPred_gauge_le_eq (s := K) (a := lam j.val) hKconv h0K' hAbs hρnn
      have hg' : (fun k => (v j k : ℝ)) ∈ {x : Fin N → ℝ | gauge K x ≤ lam j.val} := hg
      rw [h] at hg'
      exact (Set.mem_iInter.mp (Set.mem_iInter.mp hg' r)) hr
    by_contra hcon
    push Not at hcon
    set q : ℝ := Q ^ (c i) with hqdef
    have hqpos : 0 < q := by rw [hqdef]; exact hQcpos i
    set D : ℝ := ‖∑ k, L i k * (v j k : ℂ)‖ - lam j.val * q with hDdef
    have hDpos : 0 < D := by rw [hDdef]; linarith
    set r : ℝ := lam j.val + D / (2 * q) with hrdef
    have hrgt : lam j.val < r := by
      rw [hrdef]
      have : 0 < D / (2 * q) := div_pos hDpos (by linarith)
      linarith
    obtain ⟨w, hwK, hwx⟩ := hmem r hrgt
    have hrpos : 0 < r := lt_of_le_of_lt hρnn hrgt
    have hwK' : ‖∑ k, L i k * (w k : ℂ)‖ ≤ q := by
      rw [hqdef]; exact (hKmem w).mp hwK i
    have hk : ∀ k, (v j k : ℂ) = (r:ℂ) * (w k : ℂ) := by
      intro k
      have h1 : r * w k = (v j k : ℝ) := by
        have := congr_fun hwx k
        simpa only [Pi.smul_apply, smul_eq_mul] using this
      have h2 : ((v j k : ℝ) : ℂ) = ((r * w k : ℝ) : ℂ) := by rw [h1]
      have h3 : (v j k : ℂ) = ((v j k : ℝ) : ℂ) := by push_cast; ring
      rw [h3, h2]; push_cast; ring
    have h1 : (∑ k, L i k * (v j k : ℂ)) = (r:ℂ) * (∑ k, L i k * (w k : ℂ)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ => by rw [hk k]; ring)
    have h2 : ‖∑ k, L i k * (v j k : ℂ)‖ = r * ‖∑ k, L i k * (w k : ℂ)‖ := by
      rw [h1, norm_mul, norm_ofReal_of_nonneg hrpos.le]
    have h4 : r * q = lam j.val * q + D / 2 := by
      rw [hrdef]; field_simp
    have h5 : r * ‖∑ k, L i k * (w k : ℂ)‖ ≤ r * q :=
      mul_le_mul_of_nonneg_left hwK' hrpos.le
    have h6 : ‖∑ k, L i k * (v j k : ℂ)‖ ≤ r * q := by rw [h2]; exact h5
    linarith [h6, h4, hDdef, hcon]
  · intro j t htpos htlt y hy
    have hboxmem : (fun k => (y k : ℝ)) ∈ t • K := (hbox_iff t htpos.le y).mpr hy
    have hgle : gauge K (fun k => (y k : ℝ)) ≤ t := gauge_le_of_mem htpos.le hboxmem
    have hlt : gauge K (fun k => (y k : ℝ)) <
        sInf {t : ℝ | 0 < t ∧ ∃ w : Fin (j.val + 1) → (Fin N → ℤ),
          LinearIndependent ℝ (fun a => fun k => (w a k : ℝ)) ∧
          ∀ a, (fun k => (w a k : ℝ)) ∈ t • K} := by
      rw [← hlam_gauge j.val j.isLt]
      exact lt_of_le_of_lt hgle htlt
    have hex := hexcl (j.val + 1) (by omega) (by omega) y hlt
    have hle : Submodule.span ℝ (Set.range (fun a : Fin ((j.val + 1) - 1) =>
          (fun k => (v (Fin.castLE (by omega) a) k : ℝ)))) ≤
        Submodule.span ℝ (Set.range (fun i : {i : Fin N // i < j} => fun k => (v i.1 k : ℝ))) :=
      Submodule.span_mono (by
        rintro z ⟨a, rfl⟩
        refine ⟨⟨Fin.castLE (by omega) a, ?_⟩, ?_⟩
        · show (Fin.castLE (by omega) a).val < j.val
          rw [Fin.val_castLE]
          have := a.isLt
          omega
        · exact congrArg (fun zz : Fin N => (fun k => (v zz k : ℝ))) (Fin.ext rfl))
    have hreal : (fun k => (y k : ℝ)) ∈
        Submodule.span ℝ (Set.range (fun i : {i : Fin N // i < j} => fun k => (v i.1 k : ℝ))) :=
      hle hex
    exact Commons.LinearAlgebra.Dimension.intVec_mem_span_rat_of_mem_span_real
      (fun i : {i : Fin N // i < j} => v i.1) y hreal

end Commons.GeometryOfNumbers.SuccessiveMinima
