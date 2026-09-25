/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Vanishing mean of `∂_{\bar z_k}(bmKernel_j)` over a Euclidean annulus

The kernel `bmDbarKernel k j x = δ_{jk}‖x‖^{-2n} - n \bar x_j x_k ‖x‖^{-2n-2}` is the
`\bar z_k`-derivative of the Bochner–Martinelli kernel `bmKernel j`.  Its mean over a Euclidean
annulus centred at the origin vanishes, which is what makes the derivative of the
Bochner–Martinelli potential a Calderón–Zygmund singular integral.

Two symmetry arguments give this:

* for `k ≠ j` the single-coordinate reflection `x ↦ (…, x_j ↦ -x_j, …)` is a
  measure-preserving bijection of every annulus onto itself and changes the sign of the kernel,
  so the integral equals its own negative;
* for `k = j` the kernel is real and the pointwise identity
  `∑_l bmDbarKernel l l x = 0` together with the permutation symmetry of the annulus
  (`l ↦ k` is realised by swapping the two coordinates) turns the integral into `n` times
  itself.

-/
import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmCZDefs
import Submission.Work.CR.Flat.Cauchy.bmCz.eucRadialBound

noncomputable section

open scoped NNReal ENNReal
open MeasureTheory Set

namespace Work.CR.Flat.Cauchy.bmCz

/-! ### Reflection of a single coordinate -/

/-- Negation of the `j`-th coordinate of `ℂⁿ`, as a measurable equivalence. -/
def negCoordME {n : ℕ} (j : Fin n) : (Fin n → ℂ) ≃ᵐ (Fin n → ℂ) :=
  MeasurableEquiv.piCongrRight (fun i => if i = j then MeasurableEquiv.neg ℂ else MeasurableEquiv.refl ℂ)

lemma negCoordME_coe {n : ℕ} (j : Fin n) :
    ⇑(negCoordME j) = fun x : Fin n → ℂ => fun i => if i = j then -(x i) else x i := by
  funext x i
  by_cases h : i = j <;> simp [negCoordME, MeasurableEquiv.piCongrRight, MeasurableEquiv.neg, h]

/-- Negating a single coordinate preserves product Lebesgue measure on `ℂⁿ`. -/
lemma map_negCoordME_volume {n : ℕ} (j : Fin n) :
    Measure.map (negCoordME j) (volume : Measure (Fin n → ℂ)) = volume := by
  rw [negCoordME_coe]
  let g : Fin n → ℂ → ℂ := fun i => if i = j then Neg.neg else id
  have hfun : (fun x : Fin n → ℂ => fun i => if i = j then -(x i) else x i)
      = fun x i => g i (x i) := by
    funext x i; by_cases h : i = j <;> simp [g, h]
  rw [hfun]
  have hg : ∀ i, Measure.map (g i) (volume : Measure ℂ) = volume := by
    intro i
    by_cases h : i = j
    · have : g i = Neg.neg := by simp only [g, h, ite_true]
      rw [this, Measure.map_neg_eq_self]
    · have : g i = id := by simp only [g, h, ite_false]
      rw [this, Measure.map_id]
  have hgm : ∀ i, AEMeasurable (g i) (volume : Measure ℂ) := by
    intro i
    by_cases h : i = j
    · have : g i = Neg.neg := by simp only [g, h, ite_true]
      rw [this]; exact measurable_neg.aemeasurable
    · have : g i = id := by simp only [g, h, ite_false]
      rw [this]; exact aemeasurable_id
  have key := Measure.pi_map_pi (μ := fun _ : Fin n => (volume : Measure ℂ)) (f := g)
    (hμ := fun i => by rw [hg i]; infer_instance) hgm
  rw [MeasureTheory.volume_pi, key]
  simp only [hg]

/-- The Euclidean norm is unchanged by negating a single coordinate. -/
lemma eucNorm_negCoordME {n : ℕ} (j : Fin n) (x : Fin n → ℂ) :
    eucNorm ((negCoordME j) x) = eucNorm x := by
  rw [negCoordME_coe]
  simp only [eucNorm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : i = j <;> simp [h]

/-- For `k ≠ j` the kernel `bmDbarKernel j k` changes sign under negation of the coordinate `k`. -/
lemma bmDbarKernel_negCoord {n : ℕ} {j k : Fin n} (hjk : j ≠ k) (x : Fin n → ℂ) :
    bmDbarKernel j k ((negCoordME k) x) = - bmDbarKernel j k x := by
  have hk : ((negCoordME k) x) k = -(x k) := by rw [negCoordME_coe]; simp
  have hj : ((negCoordME k) x) j = x j := by rw [negCoordME_coe]; simp [hjk]
  simp only [bmDbarKernel, hj, hk, eucNorm_negCoordME, map_neg, if_neg hjk]
  ring

/-- Off-diagonal vanishing: for `j ≠ k` the mean of `bmDbarKernel j k` over any annulus is `0`. -/
theorem integral_bmDbarKernel_offdiag {n : ℕ} {j k : Fin n} (hjk : j ≠ k) {a b : ℝ} :
    ∫ x in eucShell (n := n) a b, bmDbarKernel j k x = 0 := by
  have hmap : Measure.map (⇑(negCoordME k)) (volume : Measure (Fin n → ℂ)) = volume :=
    map_negCoordME_volume k
  have hpre : ⇑(negCoordME k) ⁻¹' eucShell (n := n) a b = eucShell (n := n) a b := by
    ext x; simp only [Set.mem_preimage, mem_eucShell]
    rw [show eucNorm (⇑(negCoordME k) x) = eucNorm x from eucNorm_negCoordME k x]
  have hpt : ∀ x, bmDbarKernel j k (⇑(negCoordME k) x) = - bmDbarKernel j k x :=
    fun x => bmDbarKernel_negCoord hjk x
  have hsub := (negCoordME k).measurableEmbedding.setIntegral_map (μ := volume)
    (bmDbarKernel j k) (eucShell (n := n) a b)
  rw [hmap, hpre] at hsub
  have hsym : ∫ x in eucShell (n := n) a b, bmDbarKernel j k x
      = - ∫ x in eucShell (n := n) a b, bmDbarKernel j k x := by
    calc ∫ x in eucShell (n := n) a b, bmDbarKernel j k x
        = ∫ x in eucShell (n := n) a b, bmDbarKernel j k (⇑(negCoordME k) x) := hsub
      _ = ∫ x in eucShell (n := n) a b, - bmDbarKernel j k x :=
            setIntegral_congr_fun (measurableSet_eucShell a b) (fun x _ => hpt x)
      _ = - ∫ x in eucShell (n := n) a b, bmDbarKernel j k x := integral_neg _
  have h3 : (∫ x in eucShell (n := n) a b, bmDbarKernel j k x)
      + (∫ x in eucShell (n := n) a b, bmDbarKernel j k x) = 0 := by
    nth_rewrite 1 [hsym]; ring
  have h2 : (∫ x in eucShell (n := n) a b, bmDbarKernel j k x) * 2 = 0 := by
    rw [show ((∫ x in eucShell (n := n) a b, bmDbarKernel j k x)) * 2
        = (∫ x in eucShell (n := n) a b, bmDbarKernel j k x)
          + (∫ x in eucShell (n := n) a b, bmDbarKernel j k x) from by ring]
    exact h3
  exact (mul_eq_zero.mp h2).resolve_right (by norm_num)

/-! ### Permutation of the coordinates -/

/-- Permutation of the coordinates of `ℂⁿ` induced by an equivalence of `Fin n`. -/
def permME {n : ℕ} (σ : Fin n ≃ Fin n) : (Fin n → ℂ) ≃ᵐ (Fin n → ℂ) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℂ) σ

/-- Permuting the coordinates preserves product Lebesgue measure on `ℂⁿ`. -/
lemma map_permME_volume {n : ℕ} (σ : Fin n ≃ Fin n) :
    Measure.map (permME σ) (volume : Measure (Fin n → ℂ)) = volume :=
  (volume_measurePreserving_piCongrLeft (fun _ : Fin n => ℂ) σ).map_eq

lemma permME_apply {n : ℕ} (σ : Fin n ≃ Fin n) (x : Fin n → ℂ) (i : Fin n) :
    (permME σ) x i = x (σ.symm i) := by
  have h := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin n => ℂ) σ x (σ.symm i)
  rwa [Equiv.apply_symm_apply] at h

/-- The Euclidean norm is invariant under permutation of the coordinates. -/
lemma eucNorm_permME {n : ℕ} (σ : Fin n ≃ Fin n) (x : Fin n → ℂ) :
    eucNorm ((permME σ) x) = eucNorm x := by
  simp only [eucNorm]
  congr 1
  rw [show (∑ i, ‖(permME σ) x i‖ ^ 2) = ∑ i, ‖x (σ.symm i)‖ ^ 2 from by
        apply Finset.sum_congr rfl; intro i _; rw [permME_apply]]
  exact Equiv.sum_comp σ.symm (fun i => ‖x i‖ ^ 2)

/-- Covariance of the kernel under a permutation of the coordinates. -/
lemma bmDbarKernel_perm {n : ℕ} (σ : Fin n ≃ Fin n) (k j : Fin n) (x : Fin n → ℂ) :
    bmDbarKernel (σ k) (σ j) ((permME σ) x) = bmDbarKernel k j x := by
  have h1 : ((permME σ) x) (σ j) = x j := by rw [permME_apply, Equiv.symm_apply_apply]
  have h2 : ((permME σ) x) (σ k) = x k := by rw [permME_apply, Equiv.symm_apply_apply]
  have hif : (if σ k = σ j then (1:ℂ) else 0) = (if k = j then (1:ℂ) else 0) := by
    by_cases h : k = j
    · subst h; simp
    · rw [if_neg h, if_neg (fun hh => h (σ.injective hh))]
  simp only [bmDbarKernel, h1, h2, eucNorm_permME, hif]

/-- Change of variables for a permutation of the coordinates on a Euclidean annulus. -/
theorem setIntegral_permME {n : ℕ} (σ : Fin n ≃ Fin n) (g : (Fin n → ℂ) → ℂ) {a b : ℝ} :
    ∫ x in eucShell (n := n) a b, g ((permME σ) x) = ∫ x in eucShell (n := n) a b, g x := by
  have hmap : Measure.map (⇑(permME σ)) (volume : Measure (Fin n → ℂ)) = volume :=
    map_permME_volume σ
  have hpre : (⇑(permME σ)) ⁻¹' eucShell (n := n) a b = eucShell (n := n) a b := by
    ext x; simp only [Set.mem_preimage, mem_eucShell, eucNorm_permME]
  have hsub := (permME σ).measurableEmbedding.setIntegral_map (μ := volume) g
    (eucShell (n := n) a b)
  rw [hmap, hpre] at hsub
  exact hsub.symm

/-! ### The pointwise trace identity -/

/-- On the complement of the origin the diagonal of the kernel sums to zero. -/
lemma bmDbarKernel_diag_sum {n : ℕ} {x : Fin n → ℂ} (hx : eucNorm x ≠ 0) :
    ∑ l, bmDbarKernel l l x = 0 := by
  have hR : (eucNorm x : ℂ) ≠ 0 := by exact_mod_cast hx
  have hnormSq_sum : ∑ l, (Complex.normSq (x l) : ℂ) = ((eucNorm x : ℂ)) ^ 2 := by
    simp only [Complex.normSq_eq_norm_sq]
    rw [← Complex.ofReal_sum, ← Complex.ofReal_pow, eucNorm_sq]
  have hterm : ∀ l : Fin n, bmDbarKernel l l x
      = ((eucNorm x : ℂ) ^ (2*n))⁻¹
        - (n:ℂ) * (Complex.normSq (x l) : ℂ) * ((eucNorm x : ℂ) ^ (2*n+2))⁻¹ := by
    intro l
    have hc : starRingEnd ℂ (x l) * x l = (Complex.normSq (x l) : ℂ) :=
      (Complex.normSq_eq_conj_mul_self (z := x l)).symm
    simp only [bmDbarKernel, div_eq_mul_inv, one_mul, reduceIte]
    rw [show (n : ℂ) * starRingEnd ℂ (x l) * x l
          = (n : ℂ) * (starRingEnd ℂ (x l) * x l) by ring, hc]
  rw [Finset.sum_congr rfl (fun l _ => hterm l)]
  rw [Finset.sum_sub_distrib]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [nsmul_eq_mul]
  have hsum2 : ∑ l : Fin n, (n:ℂ) * (Complex.normSq (x l) : ℂ) * ((eucNorm x : ℂ) ^ (2*n+2))⁻¹
      = (n:ℂ) * (∑ l, (Complex.normSq (x l) : ℂ)) * ((eucNorm x : ℂ) ^ (2*n+2))⁻¹ := by
    rw [show (∑ l : Fin n, (n:ℂ) * (Complex.normSq (x l) : ℂ) * ((eucNorm x : ℂ) ^ (2*n+2))⁻¹)
        = ∑ l : Fin n, ((n:ℂ) * ((eucNorm x : ℂ) ^ (2*n+2))⁻¹) * (Complex.normSq (x l) : ℂ) from by
          apply Finset.sum_congr rfl; intro l _; ring]
    rw [← Finset.mul_sum]
    ring
  rw [hsum2, hnormSq_sum]
  have hR2 : (eucNorm x : ℂ)^2 ≠ 0 := pow_ne_zero 2 hR
  have hW : ((eucNorm x : ℂ) ^ 2) * ((eucNorm x : ℂ) ^ (2*n+2))⁻¹
      = ((eucNorm x : ℂ) ^ (2*n))⁻¹ := by
    rw [show (eucNorm x : ℂ) ^ (2*n+2) = (eucNorm x : ℂ)^(2*n) * (eucNorm x : ℂ)^2 from by
          rw [pow_add]]
    rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ hR2, one_mul]
  rw [show (n:ℂ) * (eucNorm x : ℂ) ^ 2 * ((eucNorm x : ℂ) ^ (2*n+2))⁻¹
      = (n:ℂ) * (((eucNorm x : ℂ) ^ 2) * ((eucNorm x : ℂ) ^ (2*n+2))⁻¹) from by ring, hW,
      sub_self]

/-! ### Integrability on a Euclidean annulus -/

lemma norm_bmDbarKernel_diag_base {n : ℕ} (l : Fin n) {x : Fin n → ℂ} :
    ‖bmDbarKernel l l x‖
      ≤ 1 / (eucNorm x) ^ (2*n) + (n:ℝ) * ‖x l‖^2 / (eucNorm x)^(2*n+2) := by
  have hZ : ‖((eucNorm x : ℂ) ^ (2*n))‖ = (eucNorm x) ^ (2*n) := by
    rw [norm_pow]; simp [abs_of_nonneg (eucNorm_nonneg x)]
  have hW : ‖((eucNorm x : ℂ) ^ (2*n+2))‖ = (eucNorm x) ^ (2*n+2) := by
    rw [norm_pow]; simp [abs_of_nonneg (eucNorm_nonneg x)]
  have hker : bmDbarKernel l l x
      = (1:ℂ) / ((eucNorm x : ℂ) ^ (2*n))
        - (n:ℂ) * starRingEnd ℂ (x l) * x l / ((eucNorm x : ℂ)^(2*n+2)) := by
    simp only [bmDbarKernel, reduceIte]
  rw [hker]
  refine le_trans (norm_sub_le _ _) (le_of_eq ?_)
  rw [norm_div, norm_div, norm_mul, norm_mul, hZ, hW, norm_one, Complex.norm_conj,
    Complex.norm_natCast]
  ring

theorem norm_bmDbarKernel_diag_le {n : ℕ} (l : Fin n) {a b : ℝ} (ha : 0 < a) {x : Fin n → ℂ}
    (hx : x ∈ eucShell a b) :
    ‖bmDbarKernel l l x‖ ≤ 1 / a ^ (2*n) + (n:ℝ) * (max b 0)^2 / a ^ (2*n+2) := by
  have hxa : a ≤ eucNorm x := hx.1
  have hxb : eucNorm x < b := hx.2
  refine le_trans (norm_bmDbarKernel_diag_base l) ?_
  have hxlb : ‖x l‖ ≤ max b 0 :=
    le_trans (le_trans (norm_le_pi_norm x l) (pi_norm_le_eucNorm x))
      (le_trans hxb.le (le_max_left b 0))
  have hp1 : 1 / (eucNorm x) ^ (2*n) ≤ 1 / a ^ (2*n) :=
    one_div_le_one_div_of_le (pow_pos ha _) (pow_le_pow_left₀ ha.le hxa (2*n))
  have hp2 : (n:ℝ) * ‖x l‖^2 / (eucNorm x)^(2*n+2) ≤ (n:ℝ) * (max b 0)^2 / a^(2*n+2) := by
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left
      (div_le_div₀ (sq_nonneg _) (pow_le_pow_left₀ (norm_nonneg _) hxlb 2) (pow_pos ha _)
        (pow_le_pow_left₀ ha.le hxa (2*n+2))) (Nat.cast_nonneg n)
  linarith

lemma measurable_bmDbarKernel_diag {n : ℕ} (l : Fin n) :
    Measurable (fun x : Fin n → ℂ => bmDbarKernel l l x) := by
  have he : Measurable fun x : Fin n → ℂ => (eucNorm x : ℂ) :=
    Complex.continuous_ofReal.measurable.comp continuous_eucNorm.measurable
  have hl : Measurable fun x : Fin n → ℂ => x l := measurable_pi_apply l
  have hc : Measurable fun x : Fin n → ℂ => starRingEnd ℂ (x l) :=
    Complex.continuous_conj.measurable.comp hl
  simp only [bmDbarKernel, reduceIte]
  exact (measurable_const.div (he.pow_const (2*n))).sub
    ((measurable_const.mul hc |>.mul hl).div (he.pow_const (2*n+2)))

theorem integrableOn_bmDbarKernel_diag {n : ℕ} (l : Fin n) {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : Fin n → ℂ => bmDbarKernel l l x) (eucShell (n := n) a b) volume := by
  refine Measure.integrableOn_of_bounded ?_ (measurable_bmDbarKernel_diag l).aestronglyMeasurable
    (M := 1 / a ^ (2*n) + (n:ℝ) * (max b 0)^2 / a ^ (2*n+2)) ?_
  · refine ne_of_lt (lt_of_le_of_lt (measure_mono (fun x hx => eucBall_subset_ball hx.2)) ?_)
    exact MeasureTheory.measure_ball_lt_top
  · rw [MeasureTheory.ae_restrict_iff' (measurableSet_eucShell a b)]
    exact Filter.Eventually.of_forall (fun x hx => norm_bmDbarKernel_diag_le l ha hx)

/-! ### The diagonal case -/

/-- Diagonal vanishing: the mean of `bmDbarKernel k k` over any annulus is `0`. -/
theorem integral_bmDbarKernel_diag {n : ℕ} (hn : 0 < n) {a b : ℝ} (ha : 0 < a) (k : Fin n) :
    ∫ x in eucShell (n := n) a b, bmDbarKernel k k x = 0 := by
  have hperm : ∀ l : Fin n, ∫ x in eucShell (n:=n) a b, bmDbarKernel l l x
      = ∫ x in eucShell (n:=n) a b, bmDbarKernel k k x := by
    intro l
    calc ∫ x in eucShell (n:=n) a b, bmDbarKernel l l x
        = ∫ x in eucShell (n:=n) a b, bmDbarKernel l l ((permME (Equiv.swap k l)) x) :=
            (setIntegral_permME (Equiv.swap k l) (fun x => bmDbarKernel l l x)).symm
      _ = ∫ x in eucShell (n:=n) a b, bmDbarKernel k k x := by
            refine setIntegral_congr_fun (measurableSet_eucShell a b) (fun x _ => ?_)
            have h := bmDbarKernel_perm (Equiv.swap k l) k k x
            rwa [Equiv.swap_apply_left] at h
  have hL : ∑ l : Fin n, (∫ x in eucShell (n:=n) a b, bmDbarKernel l l x)
      = (n:ℂ) * (∫ x in eucShell (n:=n) a b, bmDbarKernel k k x) := by
    rw [Finset.sum_congr rfl (fun l _ => hperm l), Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
  have hsum : ∑ l : Fin n, (∫ x in eucShell (n:=n) a b, bmDbarKernel l l x)
      = ∫ x in eucShell (n:=n) a b, ∑ l, bmDbarKernel l l x := by
    rw [integral_finset_sum]
    intro l _
    exact integrableOn_bmDbarKernel_diag l ha
  have hR : ∫ x in eucShell (n:=n) a b, ∑ l, bmDbarKernel l l x = 0 := by
    have h0 : (fun x : Fin n → ℂ => ∑ l, bmDbarKernel l l x)
        =ᵐ[volume.restrict (eucShell (n:=n) a b)] (fun _ => (0:ℂ)) := by
      rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' (measurableSet_eucShell a b)]
      refine Filter.Eventually.of_forall (fun x hxx => ?_)
      refine bmDbarKernel_diag_sum (fun h => ?_)
      rw [mem_eucShell] at hxx
      rw [h] at hxx
      exact absurd hxx.1 (not_le.mpr ha)
    rw [MeasureTheory.integral_congr_ae h0]
    simp
  have hfinal : (n:ℂ) * (∫ x in eucShell (n:=n) a b, bmDbarKernel k k x) = 0 := by
    rw [← hL, hsum, hR]
  exact (mul_eq_zero.mp hfinal).resolve_left
    (by exact_mod_cast (Nat.pos_iff_ne_zero.mp hn))

/-! ### The theorem -/

theorem bmDbarKernel_shell_eq_zero {n : ℕ} (hn : 0 < n) {j k : Fin n} {a b : ℝ}
    (ha : 0 < a) :
    ∫ x in eucShell a b, bmDbarKernel j k x = 0 := by
  rcases eq_or_ne j k with h | h
  · rw [h]; exact integral_bmDbarKernel_diag hn ha k
  · exact integral_bmDbarKernel_offdiag h

end Work.CR.Flat.Cauchy.bmCz
