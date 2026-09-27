import Mathlib
import Submission.Work.EKLComp.EucDefs
import Submission.Work.EKLComp.exists_euclidean_shortest_lattice_vector
import Submission.Work.EKLComp.minkowski_box3
import Submission.Work.EKLComp.exists_bounded_basis_rank2

open Matrix MeasureTheory
namespace Work.EKLComp

noncomputable section
set_option maxHeartbeats 2000000

lemma x3dot3_eq_sum (v w : Fin 3 → ℝ) : dot3 v w = v 0 * w 0 + v 1 * w 1 + v 2 * w 2 := by
  simp [dot3, Fin.sum_univ_three]

lemma x3dot2_eq_sum (v w : Fin 2 → ℝ) : dot2 v w = v 0 * w 0 + v 1 * w 1 := by
  simp [dot2, Fin.sum_univ_two]

lemma x3dot3_self_nonneg (v : Fin 3 → ℝ) : 0 ≤ dot3 v v := by
  rw [dot3]; exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)

lemma x3dot2_self_nonneg (v : Fin 2 → ℝ) : 0 ≤ dot2 v v := by
  rw [dot2]; exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)

lemma x3enorm3_sq (v : Fin 3 → ℝ) : enorm3 v ^ 2 = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
  rw [enorm3, Real.sq_sqrt (x3dot3_self_nonneg v), x3dot3_eq_sum]; ring

lemma x3enorm2_sq (v : Fin 2 → ℝ) : enorm2 v ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
  rw [enorm2, Real.sq_sqrt (x3dot2_self_nonneg v), x3dot2_eq_sum]; ring

lemma x3enorm3_nonneg (v : Fin 3 → ℝ) : 0 ≤ enorm3 v := Real.sqrt_nonneg _
lemma x3enorm2_nonneg (v : Fin 2 → ℝ) : 0 ≤ enorm2 v := Real.sqrt_nonneg _

lemma x3enorm3_sq_decomp (x : Fin 3 → ℝ) :
    enorm3 x ^ 2 = (x 0) ^ 2 + enorm2 (proj23 x) ^ 2 := by
  rw [x3enorm3_sq, x3enorm2_sq]; simp [proj23]; ring

lemma x3enorm2_le_sqrt_two_mul_norm (v : Fin 2 → ℝ) : enorm2 v ≤ Real.sqrt 2 * ‖v‖ := by
  have h1 : |v 0| ≤ ‖v‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm v 0
  have h2 : |v 1| ≤ ‖v‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm v 1
  have h3 : (v 0) ^ 2 ≤ ‖v‖ ^ 2 := by
    have h := mul_self_le_mul_self (abs_nonneg (v 0)) h1
    have h' : |v 0| ^ 2 ≤ ‖v‖ ^ 2 := by simpa [sq, abs_of_nonneg (norm_nonneg v)] using h
    rwa [sq_abs] at h'
  have h4 : (v 1) ^ 2 ≤ ‖v‖ ^ 2 := by
    have h := mul_self_le_mul_self (abs_nonneg (v 1)) h2
    have h' : |v 1| ^ 2 ≤ ‖v‖ ^ 2 := by simpa [sq, abs_of_nonneg (norm_nonneg v)] using h
    rwa [sq_abs] at h'
  have h5 : enorm2 v ^ 2 ≤ (Real.sqrt 2 * ‖v‖) ^ 2 := by
    rw [x3enorm2_sq, mul_pow, Real.sq_sqrt (by norm_num)]
    nlinarith
  have h6 : |enorm2 v| ≤ |Real.sqrt 2 * ‖v‖| := sq_le_sq.mp h5
  rwa [abs_of_nonneg (x3enorm2_nonneg v), abs_of_nonneg (by positivity)] at h6

lemma x3exists_int_round (t a : ℝ) (ha : 0 < a) : ∃ k : ℤ, |t - k * a| ≤ a / 2 := by
  refine ⟨round (t / a), ?_⟩
  have h := abs_sub_round (t / a)
  have h2 : t - (round (t / a) : ℤ) * a = a * (t / a - round (t / a)) := by field_simp
  rw [h2, abs_mul, abs_of_pos ha]
  calc a * |t / a - ↑(round (t / a))| ≤ a * (1 / 2) :=
        mul_le_mul_of_nonneg_left h (le_of_lt ha)
    _ = a / 2 := by ring

lemma x3proj23_eq_zero_iff (x : Fin 3 → ℝ) : proj23 x = 0 ↔ x = x 0 • e3 0 := by
  constructor
  · intro h
    have h1 : x 1 = 0 := by have := congr_fun h 0; simpa [proj23] using this
    have h2 : x 2 = 0 := by have := congr_fun h 1; simpa [proj23] using this
    funext i
    fin_cases i <;> simp [e3, h1, h2]
  · intro h
    funext i
    have h1 : x 1 = 0 := by rw [h]; simp [e3]
    have h2 : x 2 = 0 := by rw [h]; simp [e3]
    fin_cases i <;> simp [proj23, h1, h2]

lemma x3col3_mulVec (N : Matrix (Fin 3) (Fin 3) ℝ) (n : Fin 3 → ℤ) :
    (∑ i, (n i : ℝ) • col3 N i) = N *ᵥ (fun i => (n i : ℝ)) := by
  have h1 : ∀ i : Fin 3, (n i : ℝ) • col3 N i =
      N *ᵥ (Pi.single i ((n i : ℝ)) : Fin 3 → ℝ) := by
    intro i
    have h : (Pi.single i ((n i : ℝ)) : Fin 3 → ℝ) = (n i : ℝ) • Pi.single i 1 := by
      funext j
      by_cases hj : j = i
      · subst hj; simp [Pi.single_eq_same]
      · simp [Pi.single_eq_of_ne hj, Pi.single_eq_of_ne (Ne.symm hj)]
    rw [h, Matrix.mulVec_smul, Matrix.mulVec_single_one]
    rfl
  rw [Finset.sum_congr rfl (fun i _ => h1 i), ← Matrix.mulVec_sum, Finset.univ_sum_single]

lemma x3exists_int_coords_cols (N : Matrix (Fin 3) (Fin 3) ℝ) (x : Fin 3 → ℝ)
    (hx : x ∈ Submodule.span ℤ (Set.range (col3 N))) :
    ∃ n : Fin 3 → ℤ, x = N *ᵥ (fun i => (n i : ℝ)) := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
  refine ⟨c, ?_⟩
  rw [← hc, ← x3col3_mulVec]
  exact Finset.sum_congr rfl fun i _ => (Int.cast_smul_eq_zsmul ℝ (c i) (col3 N i)).symm

lemma x3mem_span_cols_of_eq (N : Matrix (Fin 3) (Fin 3) ℝ) (x : Fin 3 → ℝ) (n : Fin 3 → ℤ)
    (h : x = N *ᵥ (fun i => (n i : ℝ))) :
    x ∈ Submodule.span ℤ (Set.range (col3 N)) := by
  rw [h]
  have h2 : N *ᵥ (fun i => (n i : ℝ)) = ∑ i, n i • col3 N i := by
    rw [← x3col3_mulVec]
    exact Finset.sum_congr rfl fun i _ => Int.cast_smul_eq_zsmul ℝ (n i) (col3 N i)
  rw [h2]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ (n i)
    (Submodule.subset_span (show col3 N i ∈ Set.range (col3 N) from ⟨i, rfl⟩))

lemma x3proj23_add (x y : Fin 3 → ℝ) : proj23 (x + y) = proj23 x + proj23 y := rfl
lemma x3proj23_sub (x y : Fin 3 → ℝ) : proj23 (x - y) = proj23 x - proj23 y := rfl
lemma x3proj23_smul (c : ℝ) (x : Fin 3 → ℝ) : proj23 (c • x) = c • proj23 x := rfl

lemma x3proj23_e3_zero : proj23 (e3 0) = 0 := by
  funext i; fin_cases i <;> simp [proj23, e3]
lemma x3det2_add_left (u₁ u₂ v : Fin 2 → ℝ) : det2 (u₁ + u₂) v = det2 u₁ v + det2 u₂ v := by
  simp [det2]; ring
lemma x3det2_smul_left (c : ℝ) (u v : Fin 2 → ℝ) : det2 (c • u) v = c * det2 u v := by
  simp [det2]; ring
lemma x3det2_add_right (u v₁ v₂ : Fin 2 → ℝ) : det2 u (v₁ + v₂) = det2 u v₁ + det2 u v₂ := by
  simp [det2]; ring
lemma x3det2_smul_right (c : ℝ) (u v : Fin 2 → ℝ) : det2 u (c • v) = c * det2 u v := by
  simp [det2]; ring
lemma x3det2_self (u : Fin 2 → ℝ) : det2 u u = 0 := by simp [det2]; ring
lemma x3det2_zero_left (v : Fin 2 → ℝ) : det2 0 v = 0 := by simp [det2]
lemma x3det2_zero_right (u : Fin 2 → ℝ) : det2 u 0 = 0 := by simp [det2]

lemma x3col_smul (N : Matrix (Fin 3) (Fin 3) ℝ) (c : ℝ) (i : Fin 3) :
    c • col3 N i = N *ᵥ (c • Pi.single i 1) := by
  rw [Matrix.mulVec_smul, Matrix.mulVec_single_one]; rfl

lemma x3single_combine (m n k : ℝ) :
    ((m • Pi.single (1 : Fin 3) 1 + n • Pi.single (2 : Fin 3) 1
      - k • Pi.single (0 : Fin 3) 1 : Fin 3 → ℝ)) =
    (fun i : Fin 3 => if i = 0 then -k else if i = 1 then m else n) := by
  funext i
  fin_cases i <;> simp [Pi.single_eq_same, Pi.single_eq_of_ne]

lemma x3det_expand (N : Matrix (Fin 3) (Fin 3) ℝ) (a : ℝ)
    (h00 : N 0 0 = a) (h10 : N 1 0 = 0) (h20 : N 2 0 = 0) :
    N.det = a * det2 (proj23 (col3 N 1)) (proj23 (col3 N 2)) := by
  have h11 : proj23 (col3 N 1) 0 = N 1 1 := rfl
  have h12 : proj23 (col3 N 1) 1 = N 2 1 := rfl
  have h21 : proj23 (col3 N 2) 0 = N 1 2 := rfl
  have h22 : proj23 (col3 N 2) 1 = N 2 2 := rfl
  rw [Matrix.det_fin_three, det2, h00, h10, h20, h11, h12, h21, h22]
  ring

/-- **The core assembly.**  Given a unimodular matrix `M` whose first column `v` is a
Euclidean-shortest vector of the lattice `M ℤ³` (of norm `a`), together with a linear isometry
`T` sending `v` to `a • e₀`, there is a unimodular integer matrix `A` such that all entries of
`M * A` are bounded by a constant depending only on `a`. -/
def px3C (ρ : ℝ) : ℝ :=
  2 * Real.sqrt 3 + Real.sqrt (3 + (Real.sqrt 2 * (Real.sqrt (1 / ρ) + 2 + 4 / ρ ^ 2)) ^ 2) + 1

/-- `px3C ρ` is positive for `ρ > 0`. -/
theorem px3C_pos (ρ : ℝ) (hρ : 0 < ρ) : 0 < px3C ρ := by
  unfold px3C
  have h1 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have h2 : 0 ≤ Real.sqrt (3 + (Real.sqrt 2 * (Real.sqrt (1 / ρ) + 2 + 4 / ρ ^ 2)) ^ 2) :=
    Real.sqrt_nonneg _
  linarith

theorem core_assembly_uniform
    (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : M.det = 1)
    (v : Fin 3 → ℝ) (hvcol : ∀ i, M i 0 = v i)
    (a : ℝ) (haeq : enorm3 v = a) (hapos : 0 < a)
    (ρ : ℝ) (hρ : 0 < ρ) (hρa : ρ ≤ a) (ha2 : a ≤ 2 * Real.sqrt 3)
    (hmin : ∀ m : Fin 3 → ℤ, m ≠ 0 → a ≤ enorm3 (M *ᵥ (fun i => (m i : ℝ))))
    (T : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ))
    (hTv : T v = a • e3 0)
    (hTnorm : ∀ x : Fin 3 → ℝ, enorm3 (T x) = enorm3 x)
    (hTdet : (LinearMap.toMatrix' T.toLinearMap).det = 1)
    (hTbound : ∀ (y : Fin 3 → ℝ) (i : Fin 3), |(T.symm y) i| ≤ enorm3 y) :
    ∃ A : Matrix (Fin 3) (Fin 3) ℤ, A.det = 1 ∧
      ∀ i j, |(M * (A.map (Int.castRingHom ℝ))) i j| ≤ px3C ρ := by
  -- ### Step 1: the conjugated matrix `N` and its first column
  set Tm : Matrix (Fin 3) (Fin 3) ℝ := LinearMap.toMatrix' T.toLinearMap with hTmdef
  have hTmdet : Tm.det = 1 := by rw [hTmdef]; exact hTdet
  have hTm_apply : ∀ x : Fin 3 → ℝ, Tm *ᵥ x = T x := by
    intro x
    have h1 := LinearMap.congr_fun (Matrix.toLin'_toMatrix' T.toLinearMap) x
    rw [Matrix.toLin'_apply] at h1
    exact h1
  set N : Matrix (Fin 3) (Fin 3) ℝ := Tm * M with hNdef
  have hNdet : N.det = 1 := by rw [hNdef, Matrix.det_mul, hM, mul_one, hTmdet]
  have hMcol0 : M *ᵥ (Pi.single 0 1 : Fin 3 → ℝ) = v := by
    rw [Matrix.mulVec_single_one]; funext i; exact hvcol i
  have hN0vec : N *ᵥ (Pi.single 0 1 : Fin 3 → ℝ) = a • e3 0 := by
    rw [hNdef, ← Matrix.mulVec_mulVec, hTm_apply, hMcol0, hTv]
  have hcol0 : ∀ i : Fin 3, (col3 N 0) i = (a • e3 0) i := by
    intro i
    have := congr_fun hN0vec i
    rwa [Matrix.mulVec_single_one] at this
  have hN00 : N 0 0 = a := by simpa [col3, e3] using hcol0 0
  have hN10 : N 1 0 = 0 := by simpa [col3, e3] using hcol0 1
  have hN20 : N 2 0 = 0 := by simpa [col3, e3] using hcol0 2
  -- ### Step 2: the 2x2 determinant of the projected lattice
  have hdet_expand : N.det = a * det2 (proj23 (col3 N 1)) (proj23 (col3 N 2)) :=
    x3det_expand N a hN00 hN10 hN20
  have hdet2 : det2 (proj23 (col3 N 1)) (proj23 (col3 N 2)) = 1 / a := by
    have h : a * det2 (proj23 (col3 N 1)) (proj23 (col3 N 2)) = 1 := by
      rw [← hdet_expand]; exact hNdet
    rw [eq_div_iff (ne_of_gt hapos), mul_comm]
    exact h
  have hdet2_ne : det2 (proj23 (col3 N 1)) (proj23 (col3 N 2)) ≠ 0 := by
    rw [hdet2]; positivity
  -- ### Step 3: minimality for the conjugated lattice
  have hNmin : ∀ m : Fin 3 → ℤ, m ≠ 0 → a ≤ enorm3 (N *ᵥ (fun i => (m i : ℝ))) := by
    intro m hm
    rw [hNdef, ← Matrix.mulVec_mulVec, hTm_apply, hTnorm]
    exact hmin m hm
  -- ### Step 4: the projected lattice and its lower bound
  set u2 : Fin 2 → ℝ := proj23 (col3 N 1) with hu2
  set v2 : Fin 2 → ℝ := proj23 (col3 N 2) with hv2
  have hdet2uv : det2 u2 v2 = 1 / a := by rw [hu2, hv2]; exact hdet2
  have hdet2uv_ne : det2 u2 v2 ≠ 0 := by rw [hdet2uv]; positivity
  have hindep2 : ∀ m n : ℝ, m • u2 + n • v2 = 0 → m = 0 ∧ n = 0 := by
    intro m n h
    have h1 : m * det2 u2 v2 = 0 := by
      have hc := congr_arg (fun w => det2 w v2) h
      rw [x3det2_add_left, x3det2_smul_left, x3det2_smul_left, x3det2_self, x3det2_zero_left] at hc
      simpa using hc
    have h2 : n * det2 u2 v2 = 0 := by
      have hc := congr_arg (fun w => det2 u2 w) h
      rw [x3det2_add_right, x3det2_smul_right, x3det2_smul_right, x3det2_self, x3det2_zero_right] at hc
      simpa [mul_comm] using hc
    exact ⟨(mul_eq_zero.mp h1).resolve_right hdet2uv_ne, (mul_eq_zero.mp h2).resolve_right hdet2uv_ne⟩
  have hproj_lower : ∀ m n : ℤ, (m ≠ 0 ∨ n ≠ 0) →
      a / 2 ≤ ‖((m : ℝ) • u2 + (n : ℝ) • v2 : Fin 2 → ℝ)‖ := by
    intro m n hmn
    set y : Fin 2 → ℝ := (m : ℝ) • u2 + (n : ℝ) • v2 with hydef
    have hy_ne : y ≠ 0 := by
      intro hy
      have hc : (m : ℝ) = 0 ∧ (n : ℝ) = 0 := hindep2 m n hy
      rcases hmn with h | h
      · exact h (by exact_mod_cast hc.1)
      · exact h (by exact_mod_cast hc.2)
    set x : Fin 3 → ℝ := (m : ℝ) • col3 N 1 + (n : ℝ) • col3 N 2 with hxdef
    have hx_proj : proj23 x = y := by
      rw [hxdef, hydef, hu2, hv2, x3proj23_add, x3proj23_smul, x3proj23_smul]; try rfl
    obtain ⟨k, hk⟩ := x3exists_int_round (x 0) a hapos
    set x' : Fin 3 → ℝ := x - (k : ℝ) • (a • e3 0) with hx'def
    set μ : Fin 3 → ℤ := (fun i => if i = 0 then -k else if i = 1 then m else n) with hμdef
    have hx'int : x' = N *ᵥ (fun i => (μ i : ℝ)) := by
      have h1 : x = N *ᵥ ((m : ℝ) • Pi.single 1 1 + (n : ℝ) • Pi.single 2 1) := by
        rw [hxdef, x3col_smul, x3col_smul, ← Matrix.mulVec_add]
      have h2 : (k : ℝ) • (a • e3 0) = N *ᵥ ((k : ℝ) • Pi.single 0 1) := by
        rw [← hN0vec, ← Matrix.mulVec_smul]
      have h3 : x' = N *ᵥ ((m : ℝ) • Pi.single 1 1 + (n : ℝ) • Pi.single 2 1
          - (k : ℝ) • Pi.single 0 1) := by
        rw [hx'def, h1, h2, ← Matrix.mulVec_sub]
      rw [h3, x3single_combine]
      congr 1
      funext i
      fin_cases i <;> simp [μ]
    have hres0 : x' 0 = x 0 - k * a := by
      rw [hx'def]; simp [e3]; try ring
    have hresproj : proj23 x' = y := by
      have hzero : proj23 ((k : ℝ) • (a • e3 0)) = 0 := by
        funext i
        fin_cases i <;> simp [proj23, e3]
      rw [hx'def, x3proj23_sub, hx_proj, hzero, sub_zero]
    have hne_res : x' ≠ 0 := by
      intro h0
      have h1 : proj23 x' = 0 := by rw [h0]; rfl
      have h2 : y = 0 := by rw [← hresproj]; exact h1
      exact hy_ne h2
    have hμne : μ ≠ 0 := by
      intro h0
      apply hne_res
      have hz : (fun i => ((μ i : ℤ) : ℝ)) = (0 : Fin 3 → ℝ) := by
        rw [h0]; ext i; simp
      rw [hx'int, hz, Matrix.mulVec_zero]
    have hminres : a ≤ enorm3 x' := by
      rw [hx'int]; exact hNmin μ hμne
    have hdecomp := x3enorm3_sq_decomp x'
    rw [hresproj, hres0] at hdecomp
    have hsq : a ^ 2 ≤ (x 0 - k * a) ^ 2 + enorm2 y ^ 2 := by
      have h1 : a ^ 2 ≤ enorm3 x' ^ 2 := sq_le_sq' (by linarith [x3enorm3_nonneg x']) hminres
      rw [hdecomp] at h1
      exact h1
    have hk2 : (x 0 - k * a) ^ 2 ≤ (a / 2) ^ 2 := by
      have h1 : -(a / 2) ≤ x 0 - k * a ∧ x 0 - k * a ≤ a / 2 := abs_le.mp hk
      exact sq_le_sq' h1.1 h1.2
    have hlow : (3 / 4) * a ^ 2 ≤ enorm2 y ^ 2 := by nlinarith
    have hlow2 : Real.sqrt 3 / 2 * a ≤ enorm2 y := by
      have h1 : Real.sqrt ((3 / 4) * a ^ 2) ≤ Real.sqrt (enorm2 y ^ 2) := Real.sqrt_le_sqrt hlow
      rw [Real.sqrt_sq (x3enorm2_nonneg y)] at h1
      have h2 : Real.sqrt ((3 / 4) * a ^ 2) = Real.sqrt 3 / 2 * a := by
        rw [show (3 / 4) * a ^ 2 = (Real.sqrt 3 / 2 * a) ^ 2 by
          rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num)]; ring]
        exact Real.sqrt_sq (by positivity)
      rwa [h2] at h1
    have hnorm := x3enorm2_le_sqrt_two_mul_norm y
    have hsqrt2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hfinal : a / 2 ≤ ‖y‖ := by
      have h1 : (Real.sqrt 3 / (2 * Real.sqrt 2)) * a ≤ ‖y‖ := by
        have h2 : (Real.sqrt 3 / 2) * a / Real.sqrt 2 ≤ ‖y‖ := by
          rw [div_le_iff₀ hsqrt2]
          linarith [hnorm, hlow2]
        have h3 : (Real.sqrt 3 / 2) * a / Real.sqrt 2 =
            (Real.sqrt 3 / (2 * Real.sqrt 2)) * a := by
          field_simp
          try ring
        linarith [h3 ▸ h2]
      have h5 : (1:ℝ)/2 ≤ Real.sqrt 3 / (2 * Real.sqrt 2) := by
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]
        nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num),
          Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 2, Real.sqrt_nonneg 3]
      have h4 : a / 2 ≤ (Real.sqrt 3 / (2 * Real.sqrt 2)) * a := by
        nlinarith [h5, hapos]
      linarith
    rw [hydef] at hfinal
    exact hfinal
  -- ### Step 5: the 2D reduction
  obtain ⟨p, q, r, s, hunimod, hb1, hb2⟩ :=
    exists_bounded_basis_rank2 u2 v2 (a / 2) (by positivity) hdet2uv_ne hproj_lower
  set w1' : Fin 2 → ℝ := (p : ℝ) • u2 + (q : ℝ) • v2 with hw1'def
  set w2' : Fin 2 → ℝ := (r : ℝ) • u2 + (s : ℝ) • v2 with hw2'def
  have hDval : |det2 u2 v2| = 1 / a := by rw [hdet2uv, abs_of_pos (by positivity)]
  set B2 : ℝ := Real.sqrt 2 * (Real.sqrt (1 / ρ) + 2 + 4 / ρ ^ 2) with hB2def
  have hB2pos : 0 < B2 := by
    rw [hB2def]; positivity
  have hbound1 : ‖w1'‖ ≤ Real.sqrt (1 / ρ) + 2 + 4 / ρ ^ 2 := by
    have h1 : 2 * (1 / a) / (a / 2) ≤ 4 / ρ ^ 2 := by
      have he : 2 * (1 / a) / (a / 2) = 4 / a ^ 2 := by field_simp; try ring
      rw [he, div_le_div_iff₀ (by positivity : (0:ℝ) < a ^ 2)
        (by positivity : (0:ℝ) < ρ ^ 2)]
      nlinarith [hρa, hapos, hρ]
    have h2 : Real.sqrt (1 / a) ≤ Real.sqrt (1 / ρ) :=
      Real.sqrt_le_sqrt (by rw [div_le_div_iff₀ hapos hρ]; linarith)
    rw [hDval] at hb1
    linarith
  have hbound2 : ‖w2'‖ ≤ Real.sqrt (1 / ρ) + 2 + 4 / ρ ^ 2 := by
    have h1 : 2 * (1 / a) / (a / 2) ≤ 4 / ρ ^ 2 := by
      have he : 2 * (1 / a) / (a / 2) = 4 / a ^ 2 := by field_simp; try ring
      rw [he, div_le_div_iff₀ (by positivity : (0:ℝ) < a ^ 2)
        (by positivity : (0:ℝ) < ρ ^ 2)]
      nlinarith [hρa, hapos, hρ]
    have h2 : Real.sqrt (1 / a) ≤ Real.sqrt (1 / ρ) :=
      Real.sqrt_le_sqrt (by rw [div_le_div_iff₀ hapos hρ]; linarith)
    rw [hDval] at hb2
    linarith
  have hen1 : enorm2 w1' ≤ B2 := by
    rw [hB2def]
    calc enorm2 w1' ≤ Real.sqrt 2 * ‖w1'‖ := x3enorm2_le_sqrt_two_mul_norm w1'
      _ ≤ Real.sqrt 2 * (Real.sqrt (1 / ρ) + 2 + 4 / ρ ^ 2) :=
          mul_le_mul_of_nonneg_left hbound1 (Real.sqrt_nonneg 2)
  have hen2 : enorm2 w2' ≤ B2 := by
    rw [hB2def]
    calc enorm2 w2' ≤ Real.sqrt 2 * ‖w2'‖ := x3enorm2_le_sqrt_two_mul_norm w2'
      _ ≤ Real.sqrt 2 * (Real.sqrt (1 / ρ) + 2 + 4 / ρ ^ 2) :=
          mul_le_mul_of_nonneg_left hbound2 (Real.sqrt_nonneg 2)
  -- ### Step 6: lifting the two vectors to the lattice
  set W1 : Fin 3 → ℝ := (p : ℝ) • col3 N 1 + (q : ℝ) • col3 N 2 with hW1def
  set W2 : Fin 3 → ℝ := (r : ℝ) • col3 N 1 + (s : ℝ) • col3 N 2 with hW2def
  have hW1proj : proj23 W1 = w1' := by
    rw [hW1def, hw1'def, hu2, hv2, x3proj23_add, x3proj23_smul, x3proj23_smul]; try rfl
  have hW2proj : proj23 W2 = w2' := by
    rw [hW2def, hw2'def, hu2, hv2, x3proj23_add, x3proj23_smul, x3proj23_smul]; try rfl
  obtain ⟨k1, hk1⟩ := x3exists_int_round (W1 0) a hapos
  obtain ⟨k2, hk2⟩ := x3exists_int_round (W2 0) a hapos
  set w1 : Fin 3 → ℝ := W1 - (k1 : ℝ) • (a • e3 0) with hw1def
  set w2 : Fin 3 → ℝ := W2 - (k2 : ℝ) • (a • e3 0) with hw2def
  have hw1proj : proj23 w1 = w1' := by
    have hzero : proj23 ((k1 : ℝ) • (a • e3 0)) = 0 := by
      funext i; fin_cases i <;> simp [proj23, e3]
    rw [hw1def, x3proj23_sub, hW1proj, hzero, sub_zero]
  have hw2proj : proj23 w2 = w2' := by
    have hzero : proj23 ((k2 : ℝ) • (a • e3 0)) = 0 := by
      funext i; fin_cases i <;> simp [proj23, e3]
    rw [hw2def, x3proj23_sub, hW2proj, hzero, sub_zero]
  have hw1_0 : |w1 0| ≤ a / 2 := by
    have h : w1 0 = W1 0 - k1 * a := by rw [hw1def]; simp [e3]; try ring
    rw [h]; exact hk1
  have hw2_0 : |w2 0| ≤ a / 2 := by
    have h : w2 0 = W2 0 - k2 * a := by rw [hw2def]; simp [e3]; try ring
    rw [h]; exact hk2
  have hw1norm : enorm3 w1 ≤ Real.sqrt (3 + B2 ^ 2) := by
    have hd := x3enorm3_sq_decomp w1
    rw [hw1proj] at hd
    have h0 : (w1 0) ^ 2 ≤ 3 := by
      have h1 : (w1 0) ^ 2 ≤ (a / 2) ^ 2 := by
        have := abs_le.mp hw1_0
        exact sq_le_sq' this.1 this.2
      have h2 : (a / 2) ^ 2 ≤ 3 := by
        have h3 : a / 2 ≤ Real.sqrt 3 := by
          rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
          nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num), ha2]
        have h4 : (a / 2) ^ 2 ≤ (Real.sqrt 3) ^ 2 :=
          sq_le_sq' (by linarith [Real.sqrt_nonneg 3, hapos]) h3
        rwa [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)] at h4
      linarith
    have h2 : enorm3 w1 ^ 2 ≤ 3 + B2 ^ 2 := by
      have hle : enorm2 w1' ^ 2 ≤ B2 ^ 2 := by
        have h := pow_le_pow_left₀ (x3enorm2_nonneg w1') hen1 2
        simpa using h
      rw [hd]; linarith
    calc enorm3 w1 = Real.sqrt (enorm3 w1 ^ 2) := (Real.sqrt_sq (x3enorm3_nonneg w1)).symm
      _ ≤ Real.sqrt (3 + B2 ^ 2) := Real.sqrt_le_sqrt h2
  have hw2norm : enorm3 w2 ≤ Real.sqrt (3 + B2 ^ 2) := by
    have hd := x3enorm3_sq_decomp w2
    rw [hw2proj] at hd
    have h0 : (w2 0) ^ 2 ≤ 3 := by
      have h1 : (w2 0) ^ 2 ≤ (a / 2) ^ 2 := by
        have := abs_le.mp hw2_0
        exact sq_le_sq' this.1 this.2
      have h2 : (a / 2) ^ 2 ≤ 3 := by
        have h3 : a / 2 ≤ Real.sqrt 3 := by
          rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
          nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num), ha2]
        have h4 : (a / 2) ^ 2 ≤ (Real.sqrt 3) ^ 2 :=
          sq_le_sq' (by linarith [Real.sqrt_nonneg 3, hapos]) h3
        rwa [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)] at h4
      linarith
    have h2 : enorm3 w2 ^ 2 ≤ 3 + B2 ^ 2 := by
      have hle : enorm2 w2' ^ 2 ≤ B2 ^ 2 := by
        have h := pow_le_pow_left₀ (x3enorm2_nonneg w2') hen2 2
        simpa using h
      rw [hd]; linarith
    calc enorm3 w2 = Real.sqrt (enorm3 w2 ^ 2) := (Real.sqrt_sq (x3enorm3_nonneg w2)).symm
      _ ≤ Real.sqrt (3 + B2 ^ 2) := Real.sqrt_le_sqrt h2
  -- ### Step 7: the explicit change of basis matrix
  set Gmat : Matrix (Fin 3) (Fin 3) ℝ :=
    (fun i j => if j = 0 then (a • e3 0) i else if j = 1 then w1 i else w2 i) with hGmatdef
  set A' : Matrix (Fin 3) (Fin 3) ℤ :=
    (fun i j => if j = 0 then (if i = 0 then (1 : ℤ) else 0)
      else if j = 1 then (if i = 0 then -k1 else if i = 1 then p else q)
      else (if i = 0 then -k2 else if i = 1 then r else s)) with hA'def
  -- the columns of `A'`, as integer vectors
  have hcolA0 : col3 (A'.map (Int.castRingHom ℝ)) 0 =
      (fun k => ((if k = 0 then (1 : ℤ) else 0 : ℤ) : ℝ)) := by
    funext k
    show (A'.map (Int.castRingHom ℝ)) k 0 = ((if k = 0 then (1 : ℤ) else 0 : ℤ) : ℝ)
    fin_cases k <;> (rw [Matrix.map_apply]; dsimp only [A']; simp)
  have hcolA1 : col3 (A'.map (Int.castRingHom ℝ)) 1 =
      (fun k => ((if k = 0 then -k1 else if k = 1 then p else q : ℤ) : ℝ)) := by
    funext k
    show (A'.map (Int.castRingHom ℝ)) k 1 =
      ((if k = 0 then -k1 else if k = 1 then p else q : ℤ) : ℝ)
    fin_cases k <;> (rw [Matrix.map_apply]; dsimp only [A']; simp)
  have hcolA2 : col3 (A'.map (Int.castRingHom ℝ)) 2 =
      (fun k => ((if k = 0 then -k2 else if k = 1 then r else s : ℤ) : ℝ)) := by
    funext k
    show (A'.map (Int.castRingHom ℝ)) k 2 =
      ((if k = 0 then -k2 else if k = 1 then r else s : ℤ) : ℝ)
    fin_cases k <;> (rw [Matrix.map_apply]; dsimp only [A']; simp)
  -- the columns of `N * A'↑` are the vectors `a • e₀`, `w1`, `w2`
  have hcol0rel : N *ᵥ (fun i => ((if i = 0 then (1 : ℤ) else 0 : ℤ) : ℝ)) = a • e3 0 := by
    have h : (fun i : Fin 3 => ((if i = 0 then (1 : ℤ) else 0 : ℤ) : ℝ)) =
        (Pi.single 0 1 : Fin 3 → ℝ) := by
      funext i
      by_cases h : i = 0
      · subst h; simp [Pi.single_eq_same]
      · simp [Pi.single_eq_of_ne h, h]
    rw [h, hN0vec]
  have hw1coords : N *ᵥ (fun i => ((if i = 0 then -k1 else if i = 1 then p else q : ℤ) : ℝ)) = w1 := by
    have h1 : W1 = N *ᵥ (fun i => ((if i = 1 then p else if i = 2 then q else 0 : ℤ) : ℝ)) := by
      rw [hW1def, x3col_smul, x3col_smul, ← Matrix.mulVec_add]
      congr 1
      funext i
      fin_cases i <;> simp [Pi.single_eq_same, Pi.single_eq_of_ne]
    have h2 : (k1 : ℝ) • (a • e3 0) = N *ᵥ (fun i => ((if i = 0 then k1 else 0 : ℤ) : ℝ)) := by
      rw [← hN0vec, ← Matrix.mulVec_smul]
      congr 1
      funext i
      by_cases h : i = 0
      · subst h; simp [Pi.single_eq_same]
      · simp [Pi.single_eq_of_ne h, h]
    rw [hw1def, h1, h2, ← Matrix.mulVec_sub]
    congr 1
    funext i
    fin_cases i <;> simp
  have hw2coords : N *ᵥ (fun i => ((if i = 0 then -k2 else if i = 1 then r else s : ℤ) : ℝ)) = w2 := by
    have h1 : W2 = N *ᵥ (fun i => ((if i = 1 then r else if i = 2 then s else 0 : ℤ) : ℝ)) := by
      rw [hW2def, x3col_smul, x3col_smul, ← Matrix.mulVec_add]
      congr 1
      funext i
      fin_cases i <;> simp [Pi.single_eq_same, Pi.single_eq_of_ne]
    have h2 : (k2 : ℝ) • (a • e3 0) = N *ᵥ (fun i => ((if i = 0 then k2 else 0 : ℤ) : ℝ)) := by
      rw [← hN0vec, ← Matrix.mulVec_smul]
      congr 1
      funext i
      by_cases h : i = 0
      · subst h; simp [Pi.single_eq_same]
      · simp [Pi.single_eq_of_ne h, h]
    rw [hw2def, h1, h2, ← Matrix.mulVec_sub]
    congr 1
    funext i
    fin_cases i <;> simp
  -- `X *ᵥ col_j Y = col_j (X * Y)`
  have hcol_mulVec : ∀ (X Y : Matrix (Fin 3) (Fin 3) ℝ) (j : Fin 3),
      X *ᵥ col3 Y j = col3 (X * Y) j := by
    intro X Y j
    rw [show col3 Y j = Y *ᵥ (Pi.single j 1 : Fin 3 → ℝ) from
      (Matrix.mulVec_single_one Y j).symm]
    rw [Matrix.mulVec_mulVec]
    exact Matrix.mulVec_single_one (X * Y) j
  have hNcol : ∀ j : Fin 3, col3 (N * (A'.map (Int.castRingHom ℝ))) j = col3 Gmat j := by
    intro j
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> simp
    rcases hj with rfl | rfl | rfl
    · rw [← hcol_mulVec, hcolA0, hcol0rel]
      funext i; simp [Gmat, col3]
    · rw [← hcol_mulVec, hcolA1, hw1coords]
      funext i; simp [Gmat, col3]
    · rw [← hcol_mulVec, hcolA2, hw2coords]
      funext i; simp [Gmat, col3]
  have hcolT : ∀ j : Fin 3, T (col3 (M * (A'.map (Int.castRingHom ℝ))) j) = col3 Gmat j := by
    intro j
    calc T (col3 (M * (A'.map (Int.castRingHom ℝ))) j)
        = Tm *ᵥ col3 (M * (A'.map (Int.castRingHom ℝ))) j := (hTm_apply _).symm
      _ = col3 (Tm * (M * (A'.map (Int.castRingHom ℝ)))) j := hcol_mulVec _ _ _
      _ = col3 ((Tm * M) * (A'.map (Int.castRingHom ℝ))) j := by rw [Matrix.mul_assoc]
      _ = col3 (N * (A'.map (Int.castRingHom ℝ))) j := by rw [← hNdef]
      _ = col3 Gmat j := hNcol j
  -- ### Step 8: determinant, sign, and the final bound
  have e00 : A' 0 0 = 1 := by rw [hA'def]; simp
  have e01 : A' 0 1 = -k1 := by rw [hA'def]; simp
  have e02 : A' 0 2 = -k2 := by rw [hA'def]; simp
  have e10 : A' 1 0 = 0 := by rw [hA'def]; simp
  have e11 : A' 1 1 = p := by rw [hA'def]; simp
  have e12 : A' 1 2 = r := by rw [hA'def]; simp
  have e20 : A' 2 0 = 0 := by rw [hA'def]; simp
  have e21 : A' 2 1 = q := by rw [hA'def]; simp
  have e22 : A' 2 2 = s := by rw [hA'def]; simp
  have hA'det : A'.det = p * s - q * r := by
    rw [Matrix.det_fin_three, e00, e01, e02, e10, e11, e12, e20, e21, e22]
    ring
  set E : Matrix (Fin 3) (Fin 3) ℤ :=
    Matrix.diagonal (fun i : Fin 3 => if i = 2 then A'.det else 1) with hEdef
  set A'' : Matrix (Fin 3) (Fin 3) ℤ := A' * E with hA''def
  have hdiag : E.det = A'.det := by
    rw [hEdef, Matrix.det_diagonal, Fin.prod_univ_three]
    simp
  have hA''det : A''.det = 1 := by
    rw [hA''def, Matrix.det_mul, hdiag, hA'det]
    rcases hunimod with h | h <;> rw [h] <;> norm_num
  have henorm_a : enorm3 (a • e3 0) = a := by
    have h1 : enorm3 (a • e3 0) = Real.sqrt (a * a) := by
      rw [enorm3, x3dot3_eq_sum]
      simp [e3]
      try ring_nf
    rw [h1, Real.sqrt_mul_self (le_of_lt hapos)]
  set C : ℝ := 2 * Real.sqrt 3 + Real.sqrt (3 + B2 ^ 2) + 1 with hCdef
  have hCpos : 0 < C := by
    rw [hCdef]
    have := Real.sqrt_nonneg (3 + B2 ^ 2)
    linarith [Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 3)]
  have hcolbound : ∀ j : Fin 3, enorm3 (col3 Gmat j) ≤ C := by
    intro j
    have h0 : col3 Gmat 0 = a • e3 0 := by funext i; simp [Gmat, col3]
    have h1 : col3 Gmat 1 = w1 := by funext i; simp [Gmat, col3]
    have h2 : col3 Gmat 2 = w2 := by funext i; simp [Gmat, col3]
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> simp
    rcases hj with rfl | rfl | rfl
    · rw [h0, henorm_a, hCdef]
      linarith [ha2, Real.sqrt_nonneg (3 + B2 ^ 2), Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 3)]
    · rw [h1, hCdef]
      linarith [hw1norm, Real.sqrt_nonneg 3, Real.sqrt_nonneg (3 + B2 ^ 2)]
    · rw [h2, hCdef]
      linarith [hw2norm, Real.sqrt_nonneg 3, Real.sqrt_nonneg (3 + B2 ^ 2)]
  have hCval : C = px3C ρ := by rw [hCdef, hB2def]; rfl
  refine ⟨A'', hA''det, ?_⟩
  intro i j
  have hsplit : M * (A''.map (Int.castRingHom ℝ)) =
      (M * (A'.map (Int.castRingHom ℝ))) * (E.map (Int.castRingHom ℝ)) := by
    rw [hA''def, Matrix.map_mul, Matrix.mul_assoc]
  have hzero : ∀ k : Fin 3, k ≠ j → (E.map (Int.castRingHom ℝ)) k j = 0 := by
    intro k hk
    rw [Matrix.map_apply, hEdef, Matrix.diagonal_apply_ne _ hk]
    simp
  have hEjj : |(E.map (Int.castRingHom ℝ)) j j| ≤ 1 := by
    rw [Matrix.map_apply, hEdef, Matrix.diagonal_apply_eq]
    by_cases h2 : j = 2
    · rw [if_pos h2, hA'det]
      rcases hunimod with hh | hh <;> rw [hh] <;> norm_num
    · rw [if_neg h2]; norm_num
  have hcol : (M * (A'.map (Int.castRingHom ℝ))) i j = (T.symm (col3 Gmat j)) i := by
    have h := congrArg T.symm (hcolT j)
    rw [LinearEquiv.symm_apply_apply] at h
    exact congrFun h i
  rw [hsplit, Matrix.mul_apply,
    Finset.sum_eq_single j (fun k _ hk => by rw [hzero k hk, mul_zero])
      (fun h => absurd (Finset.mem_univ j) h)]
  rw [hcol, abs_mul]
  calc |(T.symm (col3 Gmat j)) i| * |(E.map (Int.castRingHom ℝ)) j j|
      ≤ enorm3 (col3 Gmat j) * 1 :=
        mul_le_mul (hTbound (col3 Gmat j) i) hEjj (abs_nonneg _)
          (le_trans (abs_nonneg _) (hTbound (col3 Gmat j) i))
    _ ≤ px3C ρ := by rw [mul_one]; exact hCval ▸ hcolbound j


/-- **The core assembly** (existential-constant form, kept for convenience): given a unimodular
matrix `M` whose first column `v` is a Euclidean-shortest vector of the lattice `M ℤ³` (of norm
`a`), together with a linear isometry `T` sending `v` to `a • e₀`, there is a unimodular integer
matrix `A` such that all entries of `M * A` are bounded by a constant depending only on
`a` and `ρ`.  The constant produced by the proof is `px3C ρ`, see `core_assembly_uniform`. -/
theorem core_assembly
    (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : M.det = 1)
    (v : Fin 3 → ℝ) (hvcol : ∀ i, M i 0 = v i)
    (a : ℝ) (haeq : enorm3 v = a) (hapos : 0 < a)
    (ρ : ℝ) (hρ : 0 < ρ) (hρa : ρ ≤ a) (ha2 : a ≤ 2 * Real.sqrt 3)
    (hmin : ∀ m : Fin 3 → ℤ, m ≠ 0 → a ≤ enorm3 (M *ᵥ (fun i => (m i : ℝ))))
    (T : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ))
    (hTv : T v = a • e3 0)
    (hTnorm : ∀ x : Fin 3 → ℝ, enorm3 (T x) = enorm3 x)
    (hTdet : (LinearMap.toMatrix' T.toLinearMap).det = 1)
    (hTbound : ∀ (y : Fin 3 → ℝ) (i : Fin 3), |(T.symm y) i| ≤ enorm3 y) :
    ∃ C : ℝ, 0 < C ∧ ∃ A : Matrix (Fin 3) (Fin 3) ℤ, A.det = 1 ∧
      ∀ i j, |(M * (A.map (Int.castRingHom ℝ))) i j| ≤ C :=
  ⟨px3C ρ, px3C_pos ρ hρ,
    core_assembly_uniform M hM v hvcol a haeq hapos ρ hρ hρa ha2 hmin T hTv hTnorm hTdet hTbound⟩

end

end Work.EKLComp
