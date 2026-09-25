import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Polydisc.dbarCoord_comm

noncomputable section

open scoped NNReal ENNReal Topology
open Set Filter

namespace Work.CR.Flat.Cauchy

open Work.CR.Flat

/-! ## Complex linearity of the real differential of a holomorphic function -/

/-- If the `j`-th `∂̄`-derivative of `u` vanishes at `y`, then the real differential of `u` at `y`
is complex-linear in the `j`-th coordinate direction. -/
lemma fderiv_single_eq_mul {n : ℕ} {u : (Fin n → ℂ) → ℂ} {y : Fin n → ℂ} (j : Fin n)
    (h : dbarCoord j u y = 0) (c : ℂ) :
    fderiv ℝ u y (Pi.single j c) = c * fderiv ℝ u y (Pi.single j 1) := by
  have hX : fderiv ℝ u y (Pi.single j 1)
      + Complex.I * fderiv ℝ u y (Pi.single j Complex.I) = 0 := by
    have h2 := h
    unfold dbarCoord at h2
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 (by norm_num)
    · exact h3
  have hb : fderiv ℝ u y (Pi.single j Complex.I) = Complex.I * fderiv ℝ u y (Pi.single j 1) := by
    have h1 : fderiv ℝ u y (Pi.single j 1)
        = -(Complex.I * fderiv ℝ u y (Pi.single j Complex.I)) := by
      rw [← add_eq_zero_iff_eq_neg]; exact hX
    rw [h1, mul_neg, ← mul_assoc, Complex.I_mul_I]
    simp
  have hsplit : (Pi.single j c : Fin n → ℂ)
      = (c.re : ℝ) • (Pi.single j (1:ℂ) : Fin n → ℂ)
        + (c.im : ℝ) • (Pi.single j (Complex.I) : Fin n → ℂ) := by
    ext k
    by_cases hk : k = j
    · subst hk; simp [Complex.re_add_im]
    · simp [Pi.single_eq_of_ne hk]
  rw [hsplit, map_add, map_smul, map_smul, hb]
  simp only [RCLike.real_smul_eq_coe_mul]
  have hh : (c.re : ℂ) * (fderiv ℝ u y (Pi.single j 1))
      + (c.im : ℂ) * (Complex.I * fderiv ℝ u y (Pi.single j 1))
      = ((c.re : ℂ) + (c.im : ℂ) * Complex.I) * (fderiv ℝ u y (Pi.single j 1)) := by ring
  exact hh.trans (by rw [Complex.re_add_im])

/-- For a holomorphic `u`, the real differential at `y` is complex-linear. -/
lemma fderiv_smul_I {n : ℕ} {u : (Fin n → ℂ) → ℂ} {y : Fin n → ℂ}
    (h : ∀ j, dbarCoord j u y = 0) (w : Fin n → ℂ) :
    fderiv ℝ u y (Complex.I • w) = Complex.I * fderiv ℝ u y w := by
  have h1 : (Complex.I • w : Fin n → ℂ) = ∑ j : Fin n, Pi.single j (Complex.I * w j) := by
    rw [← Finset.univ_sum_single (Complex.I • w)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.smul_apply, smul_eq_mul]
  have h2 : w = ∑ j : Fin n, Pi.single j (w j) := (Finset.univ_sum_single w).symm
  have hL : fderiv ℝ u y (Complex.I • w)
      = ∑ j : Fin n, Complex.I * ((w j) * fderiv ℝ u y (Pi.single j 1)) := by
    rw [h1, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [fderiv_single_eq_mul j (h j) (Complex.I * w j)]
    ring
  have hR : Complex.I * fderiv ℝ u y w
      = ∑ j : Fin n, Complex.I * ((w j) * fderiv ℝ u y (Pi.single j 1)) := by
    have h2' : fderiv ℝ u y w = ∑ j : Fin n, (w j) * fderiv ℝ u y (Pi.single j 1) := by
      conv_lhs => rw [h2]
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => fderiv_single_eq_mul j (h j) (w j)
    rw [h2', Finset.mul_sum]
  rw [hL, hR]


/-! ## The one-variable Cauchy estimate for a slice -/

/-- The `c`-th slice `w ↦ Function.update z c w` has derivative the coordinate inclusion. -/
lemma hasFDerivAt_updateSlice {n : ℕ} (z : Fin n → ℂ) (c : Fin n) (w : ℂ) :
    HasFDerivAt (fun w : ℂ => Function.update z c w)
      (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) c) w := by
  have hfun : (fun w : ℂ => Function.update z c w)
      = fun w : ℂ => Function.update z c 0 +
          (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) c) w := by
    funext v
    rw [ContinuousLinearMap.single_apply]
    ext i
    by_cases h : i = c <;> simp [h]
  rw [hfun]
  exact (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) c)
    (x := w)).const_add (Function.update z c 0)

lemma single_apply_eq {n : ℕ} (c : Fin n) (τ : ℂ) :
    (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) c) τ = Pi.single c τ :=
  congrFun (ContinuousLinearMap.single_apply ℝ (fun _ : Fin n => ℂ) c) τ

/-- **Cauchy estimate for a slice of a holomorphic function.** If `u` is holomorphic and
differentiable on `S`, and the closed `c`-slice of radius `ε` around `z` lies in `S` where
`‖u‖ ≤ B`, then `‖fderiv u z (e_c)‖ ≤ B / ε`. -/
lemma norm_fderiv_single_le {n : ℕ} {u : (Fin n → ℂ) → ℂ} {S : Set (Fin n → ℂ)}
    (hhol : ∀ j, ∀ y ∈ S, dbarCoord j u y = 0) (hdiff : ∀ y ∈ S, DifferentiableAt ℝ u y)
    {z : Fin n → ℂ} {c : Fin n} {ε B : ℝ} (hε : 0 < ε)
    (hball : ∀ w : ℂ, dist w (z c) ≤ ε → Function.update z c w ∈ S)
    (hB : ∀ y ∈ S, ‖u y‖ ≤ B) :
    ‖fderiv ℝ u z (Pi.single c 1)‖ ≤ B / ε := by
  have hderiv : ∀ w : ℂ, Function.update z c w ∈ S →
      fderiv ℝ (fun w : ℂ => u (Function.update z c w)) w
        = (fderiv ℝ u (Function.update z c w)).comp
          (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) c) := fun w hw =>
    ((hdiff _ hw).hasFDerivAt.comp w (hasFDerivAt_updateSlice z c w)).fderiv
  have hcr : ∀ w : ℂ, Function.update z c w ∈ S →
      fderiv ℝ (fun w : ℂ => u (Function.update z c w)) w Complex.I
        = Complex.I * fderiv ℝ (fun w : ℂ => u (Function.update z c w)) w 1 := by
    intro w hw
    have h2 : fderiv ℝ u (Function.update z c w) (Pi.single c Complex.I)
        = Complex.I * fderiv ℝ u (Function.update z c w) (Pi.single c 1) := by
      simpa using fderiv_single_eq_mul c (hhol c _ hw) Complex.I
    rw [hderiv w hw, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      single_apply_eq, single_apply_eq]
    exact h2
  have hgd : ∀ w : ℂ, dist w (z c) < ε →
      DifferentiableAt ℂ (fun w : ℂ => u (Function.update z c w)) w := by
    intro w hw
    have hmem : Function.update z c w ∈ S := hball w (le_of_lt hw)
    exact (differentiableAt_complex_iff_differentiableAt_real).mpr
      ⟨((hdiff _ hmem).hasFDerivAt.comp w (hasFDerivAt_updateSlice z c w)).differentiableAt,
        hcr w hmem⟩
  have hdiffOn : DifferentiableOn ℂ (fun w : ℂ => u (Function.update z c w))
      (Metric.ball (z c) ε) := fun w hw =>
    (hgd w (by rwa [Metric.mem_ball] at hw)).differentiableWithinAt
  have hcont : ContinuousOn (fun w : ℂ => u (Function.update z c w))
      (closure (Metric.ball (z c) ε)) := by
    rw [closure_ball (z c) (ne_of_gt hε)]
    intro w hw
    have hmem : Function.update z c w ∈ S :=
      hball w (by rwa [Metric.mem_closedBall] at hw)
    exact (((hdiff _ hmem).continuousAt).comp (hasFDerivAt_updateSlice z c w).continuousAt).continuousWithinAt
  have hbound : ∀ w ∈ Metric.sphere (z c) ε,
      ‖u (Function.update z c w)‖ ≤ B := by
    intro w hw
    have hmem : Function.update z c w ∈ S :=
      hball w (by rw [Metric.mem_sphere] at hw; exact le_of_eq hw)
    exact hB _ hmem
  have hcau := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hε
    ⟨hdiffOn, hcont⟩ hbound
  have hmem0 : Function.update z c (z c) ∈ S := hball (z c) (by simp [hε.le])
  have hcd : DifferentiableAt ℂ (fun w : ℂ => u (Function.update z c w)) (z c) :=
    hgd (z c) (by simpa using hε)
  have hident : deriv (fun w : ℂ => u (Function.update z c w)) (z c)
      = fderiv ℝ u z (Pi.single c 1) := by
    have h1 : deriv (fun w : ℂ => u (Function.update z c w)) (z c)
        = fderiv ℂ (fun w : ℂ => u (Function.update z c w)) (z c) 1 :=
      fderiv_apply_one_eq_deriv.symm
    have h3 : fderiv ℂ (fun w : ℂ => u (Function.update z c w)) (z c) 1
        = fderiv ℝ (fun w : ℂ => u (Function.update z c w)) (z c) 1 := by
      rw [hcd.fderiv_restrictScalars ℝ]
      rfl
    rw [h1, h3, hderiv (z c) hmem0, ContinuousLinearMap.comp_apply, single_apply_eq,
      Function.update_eq_self c z]
  rw [← hident]
  exact hcau


/-! ## Two elementary lemmas -/

/-- For an `ℝ`-linear map on `ℂⁿ` with values in a complex space which is complex-homogeneous,
the operator norm is bounded by the sum of the norms on the coordinate unit vectors. -/
lemma norm_le_sum_apply_single {n : ℕ} {F : Type*} [SeminormedAddCommGroup F] [NormedSpace ℂ F]
    (L : (Fin n → ℂ) →L[ℝ] F)
    (hL : ∀ (c : ℂ) (v : Fin n → ℂ), L (c • v) = c • L v) :
    ‖L‖ ≤ ∑ c : Fin n, ‖L (Pi.single c (1:ℂ))‖ := by
  refine ContinuousLinearMap.opNorm_le_bound L (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun v => ?_
  have hv : v = ∑ c : Fin n, (v c) • (Pi.single c (1:ℂ) : Fin n → ℂ) := by
    rw [← Finset.univ_sum_single v]
    refine Finset.sum_congr rfl fun c _ => ?_
    ext k
    by_cases hk : k = c
    · subst hk; simp [Pi.single_eq_same]
    · simp [Pi.single_eq_of_ne hk]
  have hLv : L v = ∑ c : Fin n, (v c) • L (Pi.single c (1:ℂ) : Fin n → ℂ) := by
    nth_rewrite 1 [hv]
    rw [map_sum]
    exact Finset.sum_congr rfl fun c _ => hL (v c) _
  calc ‖L v‖ = ‖∑ c : Fin n, (v c) • L (Pi.single c (1:ℂ) : Fin n → ℂ)‖ := by rw [hLv]
    _ ≤ ∑ c : Fin n, ‖(v c) • L (Pi.single c (1:ℂ) : Fin n → ℂ)‖ := norm_sum_le _ _
    _ = ∑ c : Fin n, ‖v c‖ * ‖L (Pi.single c (1:ℂ) : Fin n → ℂ)‖ :=
        Finset.sum_congr rfl fun c _ => norm_smul _ _
    _ ≤ ∑ c : Fin n, ‖v‖ * ‖L (Pi.single c (1:ℂ) : Fin n → ℂ)‖ :=
        Finset.sum_le_sum fun c _ =>
          mul_le_mul_of_nonneg_right (norm_le_pi_norm v c) (norm_nonneg _)
    _ = ∑ c : Fin n, ‖L (Pi.single c (1:ℂ) : Fin n → ℂ)‖ * ‖v‖ :=
        Finset.sum_congr rfl fun c _ => mul_comm _ _
    _ = (∑ c : Fin n, ‖L (Pi.single c (1:ℂ) : Fin n → ℂ)‖) * ‖v‖ := (Finset.sum_mul ..).symm

/-- The iterated derivative (within a set of unique differentiability) of a `C^K` function
is `C^{K-m}`. -/
lemma contDiffOn_iteratedFDerivWithin {n : ℕ} {S : Set (Fin n → ℂ)} (hS : UniqueDiffOn ℝ S)
    {h : (Fin n → ℂ) → ℂ} {K : ℕ} (hh : ContDiffOn ℝ ((K : ℕ) : ℕ∞) h S) :
    ∀ m ≤ K, ContDiffOn ℝ (((K - m : ℕ)) : ℕ∞) (iteratedFDerivWithin ℝ m h S) S := by
  intro m
  induction m with
  | zero =>
    intro _
    rw [show ((K - 0 : ℕ) : ℕ∞) = ((K : ℕ) : ℕ∞) from by simp]
    rw [iteratedFDerivWithin_zero_eq_comp]
    exact (continuousMultilinearCurryFin0 ℝ (Fin n → ℂ) ℂ).symm.contDiff.comp_contDiffOn hh
  | succ m ih =>
    intro hm
    have hm' : m ≤ K := le_trans (Nat.le_succ m) hm
    have hih := ih hm'
    rw [iteratedFDerivWithin_succ_eq_comp_left]
    have hsub : (((K - (m + 1) : ℕ) : ℕ∞) : WithTop ℕ∞) + 1
        ≤ (((K - m : ℕ) : ℕ∞) : WithTop ℕ∞) := by
      have h1 : K - (m + 1) + 1 = K - m := by omega
      rw [← h1]; push_cast; rfl
    have hstep := ContDiffOn.fderivWithin (m := (((K - (m + 1) : ℕ) : ℕ∞) : WithTop ℕ∞))
      (n := (((K - m : ℕ) : ℕ∞) : WithTop ℕ∞)) hih hS hsub
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m+1) => (Fin n → ℂ)) ℂ).symm.contDiff.comp_contDiffOn hstep


/-! ## The recursion for the iterated derivative -/

/-- The `(m+1)`-st iterated derivative of `h` evaluated on a tuple is the derivative of the
`m`-th iterated derivative evaluated on the tail of the tuple, in the direction of its head. -/
lemma iteratedFDeriv_succ_apply {n : ℕ} {h : (Fin n → ℂ) → ℂ} {m : ℕ}
    (w : Fin (m+1) → (Fin n → ℂ)) {y : Fin n → ℂ}
    (hd : DifferentiableAt ℝ (iteratedFDeriv ℝ m h) y) :
    iteratedFDeriv ℝ (m+1) h y w
      = fderiv ℝ (fun y' => iteratedFDeriv ℝ m h y' (Fin.tail w)) y (w 0) := by
  have h1 : iteratedFDeriv ℝ (m+1) h y w
      = (fderiv ℝ (iteratedFDeriv ℝ m h) y) (w 0) (Fin.tail w) := by
    have hh := iteratedFDerivWithin_succ_apply_left (𝕜 := ℝ) (f := h) (s := Set.univ)
      (x := y) (n := m) w
    simp only [iteratedFDerivWithin_univ, fderivWithin_univ] at hh
    exact hh
  have h2 : fderiv ℝ (fun y' => iteratedFDeriv ℝ m h y' (Fin.tail w)) y
      = (ContinuousMultilinearMap.apply ℝ (fun _ : Fin m => (Fin n → ℂ)) ℂ (Fin.tail w)).comp
          (fderiv ℝ (iteratedFDeriv ℝ m h) y) := by
    rw [show (fun y' => iteratedFDeriv ℝ m h y' (Fin.tail w))
        = ⇑(ContinuousMultilinearMap.apply ℝ (fun _ : Fin m => (Fin n → ℂ)) ℂ (Fin.tail w))
          ∘ (iteratedFDeriv ℝ m h) from rfl,
      fderiv_comp y (ContinuousLinearMap.differentiableAt _
        (x := iteratedFDeriv ℝ m h y)) hd,
      ContinuousLinearMap.fderiv]
  rw [h1, h2, ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.apply_apply]

/-! ## Holomorphy of `y ↦ fderiv u y v` for a holomorphic `u` -/

/-- The function `y ↦ fderiv ℝ u y v` is differentiable where `u` is twice differentiable. -/
lemma differentiableAt_fderiv_apply {n : ℕ} {u : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (hu : ContDiffAt ℝ 2 u z) (v : Fin n → ℂ) :
    DifferentiableAt ℝ (fun y => fderiv ℝ u y v) z := by
  have hdu : DifferentiableAt ℝ (fderiv ℝ u) z :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  exact DifferentiableAt.comp z
    (ContinuousLinearMap.differentiableAt (ContinuousLinearMap.apply ℝ ℂ v) (x := fderiv ℝ u z)) hdu

/-- The derivative of `y ↦ fderiv ℝ u y v` at a point where `u` is twice differentiable. -/
lemma fderiv_fderiv_apply {n : ℕ} {u : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (hu : ContDiffAt ℝ 2 u z) (v w : Fin n → ℂ) :
    fderiv ℝ (fun y => fderiv ℝ u y v) z w = ((fderiv ℝ (fderiv ℝ u) z) w) v := by
  have hdu : DifferentiableAt ℝ (fderiv ℝ u) z :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [show (fun y => fderiv ℝ u y v)
        = ⇑(ContinuousLinearMap.apply ℝ ℂ v) ∘ (fderiv ℝ u) from rfl,
      fderiv_comp z (ContinuousLinearMap.differentiableAt (ContinuousLinearMap.apply ℝ ℂ v)
        (x := fderiv ℝ u z)) hdu,
      ContinuousLinearMap.fderiv]
  rfl

/-- The second derivative of a holomorphic function is complex-linear in its second argument. -/
lemma fderiv_fderiv_single_I {n : ℕ} {u : (Fin n → ℂ) → ℂ} {T : Set (Fin n → ℂ)}
    {z : Fin n → ℂ} (hT : T ∈ 𝓝 z) (hu : ContDiffAt ℝ 2 u z)
    (hhol : ∀ j, ∀ y ∈ T, dbarCoord j u y = 0) (jj : Fin n) (w : Fin n → ℂ) :
    ((fderiv ℝ (fderiv ℝ u) z) w) (Pi.single jj Complex.I)
      = Complex.I * (((fderiv ℝ (fderiv ℝ u) z) w) (Pi.single jj 1)) := by
  have hzero : (fun y => fderiv ℝ u y (Pi.single jj Complex.I)
      - Complex.I * fderiv ℝ u y (Pi.single jj 1)) =ᶠ[𝓝 z] 0 := by
    filter_upwards [hT] with y hy
    have h1 : fderiv ℝ u y (Pi.single jj Complex.I)
        = Complex.I * fderiv ℝ u y (Pi.single jj 1) := by
      simpa using fderiv_single_eq_mul jj (hhol jj y hy) Complex.I
    simp [h1]
  have hφ : DifferentiableAt ℝ (fun y => fderiv ℝ u y (Pi.single jj Complex.I)) z :=
    differentiableAt_fderiv_apply hu _
  have hφ' : DifferentiableAt ℝ (fun y => fderiv ℝ u y (Pi.single jj 1)) z :=
    differentiableAt_fderiv_apply hu _
  have hψ : DifferentiableAt ℝ (fun y => Complex.I * fderiv ℝ u y (Pi.single jj 1)) z :=
    DifferentiableAt.comp z
      (ContinuousLinearMap.differentiableAt (ContinuousLinearMap.mul ℝ ℂ Complex.I)
        (x := fderiv ℝ u z (Pi.single jj 1))) hφ'
  have hcalc : fderiv ℝ (fun y => fderiv ℝ u y (Pi.single jj Complex.I)
        - Complex.I * fderiv ℝ u y (Pi.single jj 1)) z w
      = ((fderiv ℝ (fderiv ℝ u) z) w) (Pi.single jj Complex.I)
        - Complex.I * (((fderiv ℝ (fderiv ℝ u) z) w) (Pi.single jj 1)) := by
    rw [show (fun y => fderiv ℝ u y (Pi.single jj Complex.I)
          - Complex.I * fderiv ℝ u y (Pi.single jj 1))
        = (fun y => fderiv ℝ u y (Pi.single jj Complex.I))
          - fun y => Complex.I * fderiv ℝ u y (Pi.single jj 1) from rfl]
    rw [fderiv_sub hφ hψ, ContinuousLinearMap.sub_apply]
    congr 1
    · exact fderiv_fderiv_apply hu _ w
    · rw [fderiv_const_mul hφ' Complex.I, ContinuousLinearMap.smul_apply, smul_eq_mul,
        fderiv_fderiv_apply hu _ w]
  have hfd : (fderiv ℝ (fun y => fderiv ℝ u y (Pi.single jj Complex.I)
      - Complex.I * fderiv ℝ u y (Pi.single jj 1)) z) w = 0 := by
    rw [hzero.fderiv_eq]
    simp
  rw [hcalc] at hfd
  exact sub_eq_zero.mp hfd

/-- **Holomorphy of `y ↦ fderiv u y v`.** If `u` is holomorphic and twice differentiable
around `z`, then every `∂̄`-derivative of `y ↦ fderiv ℝ u y v` vanishes at `z`. -/
lemma dbarCoord_fderiv_apply {n : ℕ} {u : (Fin n → ℂ) → ℂ} {T : Set (Fin n → ℂ)}
    {z : Fin n → ℂ} (hT : T ∈ 𝓝 z) (hu : ContDiffAt ℝ 2 u z)
    (hhol : ∀ j, ∀ y ∈ T, dbarCoord j u y = 0) (k : Fin n) (v : Fin n → ℂ) :
    dbarCoord k (fun y => fderiv ℝ u y v) z = 0 := by
  have hlin := fderiv_fderiv_single_I hT hu hhol k
  have hsymm : ∀ a b, ((fderiv ℝ (fderiv ℝ u) z) a) b = ((fderiv ℝ (fderiv ℝ u) z) b) a :=
    fun a b => (hu.isSymmSndFDerivAt (by simp)).eq a b
  have hderiv : ∀ w, fderiv ℝ (fun y => fderiv ℝ u y v) z w
      = ((fderiv ℝ (fderiv ℝ u) z) w) v := fun w => fderiv_fderiv_apply hu v w
  rw [dbarCoord, hderiv (Pi.single k 1), hderiv (Pi.single k Complex.I)]
  rw [hsymm (Pi.single k Complex.I) v, hlin v, hsymm (Pi.single k 1) v]
  have hII : Complex.I * (Complex.I * ((fderiv ℝ (fderiv ℝ u) z) v) (Pi.single k 1))
      = - ((fderiv ℝ (fderiv ℝ u) z) v) (Pi.single k 1) := by
    rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
  rw [hII]
  ring

/-- For a holomorphic `u`, the real differential is complex-homogeneous. -/
lemma fderiv_smul_of_hol {n : ℕ} {u : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (h : ∀ j, dbarCoord j u z = 0) (c : ℂ) (v : Fin n → ℂ) :
    fderiv ℝ u z (c • v) = c • fderiv ℝ u z v := by
  have hsplit : (c • v : Fin n → ℂ)
      = (c.re : ℝ) • v + (c.im : ℝ) • (Complex.I • v) := by
    funext k
    simp only [Pi.smul_apply, Pi.add_apply]
    rw [Complex.real_smul, Complex.real_smul, smul_eq_mul, smul_eq_mul]
    ring_nf
    rw [mul_comm c (v k), mul_assoc, ← mul_add, Complex.re_add_im]
  rw [hsplit, map_add, map_smul, map_smul, fderiv_smul_I h v]
  rw [Complex.real_smul, Complex.real_smul, smul_eq_mul]
  have hh : (c.re : ℂ) * fderiv ℝ u z v + (c.im : ℂ) * (Complex.I * fderiv ℝ u z v)
      = ((c.re : ℂ) + (c.im : ℂ) * Complex.I) * fderiv ℝ u z v := by ring
  rw [hh, Complex.re_add_im]

/-- `∂̄` depends only on the germ of the function. -/
lemma dbarCoord_congr_eventually {n : ℕ} (a : Fin n) {f g : (Fin n → ℂ) → ℂ} {y : Fin n → ℂ}
    (h : f =ᶠ[𝓝 y] g) : dbarCoord a f y = dbarCoord a g y := by
  unfold dbarCoord
  rw [h.fderiv_eq]

variable {n : ℕ}

theorem holderNorm_le_sup_of_holomorphic {n : ℕ} (hn : 0 < n) {c : Fin n → ℂ}
    {ρi ρo : Fin n → ℝ} (hmono : ∀ j, ρi j < ρo j) (hρo : ∀ j, 0 < ρo j)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : (Fin n → ℂ) → ℂ,
      ContDiffOn ℝ ((k + 1 : ℕ) : ℕ∞) h (polydisc c ρo) →
      (∀ j, ∀ z, dbarCoord j h z = 0) →
      holderNorm k α h (polydisc c ρi)
        ≤ ENNReal.ofReal C *
          (⨆ z ∈ polydisc c ρo, ENNReal.ofReal ‖h z‖) := by
  classical
  -- ## the constant
  set η : Fin n → ℝ := fun j => (ρo j - ρi j) / ((k : ℝ) + 2) with hηdef
  have hηpos : ∀ j, 0 < η j := fun j => div_pos (sub_pos.mpr (hmono j)) (by positivity)
  set T : ℝ := ∑ j : Fin n, (η j)⁻¹ with hTdef
  have hTpos : 0 < T := by
    rw [hTdef]
    exact Finset.sum_pos' (fun j _ => inv_nonneg.mpr (hηpos j).le)
      ⟨⟨0, hn⟩, Finset.mem_univ _, inv_pos.mpr (hηpos ⟨0, hn⟩)⟩
  set R0 : ℝ := ∑ j : Fin n, ρi j with hR0def
  have hR0n : R0 ≤ 2 * |R0| + 1 := by
    have h1 : R0 ≤ |R0| := le_abs_self R0
    have h2 : 0 ≤ |R0| := abs_nonneg R0
    linarith
  set Cc : ℝ := ∑ i ∈ Finset.range (k + 1),
      (T^i + T^(i+1) * (2 * |R0| + 1) ^ (1 - α)) with hCcdef
  have hCcpos : 0 < Cc := by
    rw [hCcdef]
    have hb : ∀ i : ℕ, 0 < T^i + T^(i+1) * (2 * |R0| + 1) ^ (1 - α) := fun i =>
      add_pos_of_pos_of_nonneg (pow_pos hTpos i)
        (mul_nonneg (pow_pos hTpos (i+1)).le (Real.rpow_nonneg (by positivity) _))
    exact Finset.sum_pos' (fun i _ => (hb i).le) ⟨0, Finset.mem_range.mpr (Nat.succ_pos k), hb 0⟩
  refine ⟨Cc, hCcpos, ?_⟩
  intro h hh hhol
  -- ## the per-`h` bound
  have hSopen : IsOpen (polydisc c ρo) := isOpen_polydisc c ρo
  have hSuniq : UniqueDiffOn ℝ (polydisc c ρo) := hSopen.uniqueDiffOn
  have core : ∀ Mb : ℝ, (∀ z ∈ polydisc c ρo, ‖h z‖ ≤ Mb) →
      holderNorm k α h (polydisc c ρi) ≤ ENNReal.ofReal (Cc * Mb) := by
    intro Mb hM
    by_cases hempty : ∃ j, ρi j ≤ 0
    · have hpol : polydisc c ρi = ∅ := by
        ext z
        simp only [mem_polydisc, Set.mem_empty_iff_false, iff_false, not_forall]
        obtain ⟨j, hj⟩ := hempty
        exact ⟨j, not_lt.mpr (le_trans hj (norm_nonneg _))⟩
      rw [hpol]
      have hzero : holderNorm k α h (∅ : Set (Fin n → ℂ)) = 0 := by
        simp [holderNorm, iterDerivNorm, holderSeminorm]
      rw [hzero]
      exact bot_le
    · push_neg at hempty
      have hMnn : 0 ≤ Mb := by
        have hc : c ∈ polydisc c ρo := fun j => by simpa using hρo j
        exact (norm_nonneg (h c)).trans (hM c hc)
      let P : ℕ → Set (Fin n → ℂ) := fun m => polydisc c (fun j => ρo j - (m : ℝ) * η j)
      have hPzero : P 0 = polydisc c ρo := by
        simp only [P, Nat.cast_zero, zero_mul, sub_zero]
      have hPS : ∀ m : ℕ, P m ⊆ polydisc c ρo := by
        intro m z hz j
        have h1 : (0 : ℝ) ≤ (m : ℝ) * η j := mul_nonneg (Nat.cast_nonneg m) (hηpos j).le
        have h2 : ρo j - (m : ℝ) * η j ≤ ρo j := by linarith
        exact lt_of_lt_of_le (hz j) h2
      have hPmono : ∀ m : ℕ, P (m+1) ⊆ P m := by
        intro m z hz j
        have h1 : (m : ℝ) * η j ≤ ((m : ℝ) + 1) * η j := by nlinarith [hηpos j]
        have h2 : ρo j - ((m : ℝ) + 1) * η j ≤ ρo j - (m : ℝ) * η j := by linarith
        exact lt_of_lt_of_le (by simpa [P, Nat.cast_add, Nat.cast_one] using hz j) h2
      have hPinner : polydisc c ρi ⊆ P (k+1) := by
        intro z hz j
        have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
        have h1 : ρo j - ρi j > 0 := sub_pos.mpr (hmono j)
        have he : η j = (ρo j - ρi j) / ((k : ℝ) + 2) := by rw [hηdef]
        have h3 : ((k : ℝ) + 1) * η j ≤ ρo j - ρi j := by
          rw [he, mul_div_assoc', div_le_iff₀ hk2]
          nlinarith
        have h4 : ρi j ≤ ρo j - ((k : ℝ) + 1) * η j := by linarith
        exact lt_of_lt_of_le (hz j) (by simpa [P, Nat.cast_add, Nat.cast_one] using h4)
      have hPball : ∀ (m : ℕ) (z : Fin n → ℂ), z ∈ P (m+1) → ∀ (c' : Fin n) (w : ℂ),
          dist w (z c') ≤ η c' → Function.update z c' w ∈ P m := by
        intro m z hz c' w hw j
        have hz' : ∀ j, ‖z j - c j‖ < ρo j - ((m : ℝ) + 1) * η j := fun j =>
          by simpa [P, Nat.cast_add, Nat.cast_one] using hz j
        by_cases hj : j = c'
        · subst hj
          have h1 : ‖w - z j‖ ≤ η j := by
            rw [dist_eq_norm] at hw; simpa using hw
          have h2 : ‖z j - c j‖ < ρo j - ((m : ℝ) + 1) * η j := hz' j
          have h3 : ‖Function.update z j w j - c j‖ = ‖w - c j‖ := by rw [Function.update_self]
          have h4 : w - c j = (w - z j) + (z j - c j) := by ring
          rw [h3, h4]
          calc ‖(w - z j) + (z j - c j)‖ ≤ ‖w - z j‖ + ‖z j - c j‖ := norm_add_le _ _
            _ < η j + (ρo j - ((m : ℝ) + 1) * η j) := by linarith
            _ = ρo j - (m : ℝ) * η j := by ring
        · rw [Function.update_of_ne hj w z]
          have h2 : ‖z j - c j‖ < ρo j - ((m : ℝ) + 1) * η j := hz' j
          have h5 : ρo j - ((m : ℝ) + 1) * η j < ρo j - (m : ℝ) * η j := by
            have := hηpos j; nlinarith
          exact lt_trans h2 h5
      have hNsmooth : ∀ m ≤ k+1, ContDiffOn ℝ (((k+1-m : ℕ)) : ℕ∞)
          (iteratedFDeriv ℝ m h) (polydisc c ρo) := by
        intro m hm
        have h1 := contDiffOn_iteratedFDerivWithin (S := polydisc c ρo) hSuniq
          (K := k+1) hh m hm
        refine h1.congr fun z hz => ?_
        exact (iteratedFDerivWithin_of_isOpen m hSopen hz).symm
      have hNdiff : ∀ m ≤ k, ∀ y ∈ polydisc c ρo, DifferentiableAt ℝ (iteratedFDeriv ℝ m h) y := by
        intro m hm y hy
        have hm' : m ≤ k + 1 := le_trans hm (Nat.le_succ k)
        have h1 : ContDiffOn ℝ (1 : ℕ∞) (iteratedFDeriv ℝ m h) (polydisc c ρo) :=
          (hNsmooth m hm').of_le (by
            have : 1 ≤ k + 1 - m := by omega
            exact_mod_cast this)
        exact (h1.contDiffAt (hSopen.mem_nhds hy)).differentiableAt one_ne_zero
      have hholB : ∀ m ≤ k, ∀ w : Fin m → (Fin n → ℂ), ∀ a : Fin n,
          ∀ y ∈ polydisc c ρo, dbarCoord a (fun y' => iteratedFDeriv ℝ m h y' w) y = 0 := by
        intro m hm
        induction m with
        | zero =>
          intro w a y hy
          have hw : (fun y' => iteratedFDeriv ℝ 0 h y' w) = h := by
            funext y'
            rw [← iteratedFDerivWithin_univ (𝕜 := ℝ) (f := h) (n := 0)]
            exact iteratedFDerivWithin_zero_apply w
          rw [hw]
          exact hhol a y
        | succ m ih =>
          have hmk : m ≤ k := le_trans (Nat.le_succ m) hm
          have ih' := ih hmk
          intro w a y hy
          have h2 : 2 ≤ k + 1 - m := by omega
          have hfun : (fun y' => iteratedFDeriv ℝ (m+1) h y' w) =ᶠ[𝓝 y]
              (fun y' => fderiv ℝ (fun y'' => iteratedFDeriv ℝ m h y'' (Fin.tail w)) y' (w 0)) := by
            filter_upwards [hSopen.mem_nhds hy] with y' hy'
            exact iteratedFDeriv_succ_apply w (hNdiff m hmk y' hy')
          rw [dbarCoord_congr_eventually a hfun]
          refine dbarCoord_fderiv_apply (hSopen.mem_nhds hy) ?_ ?_ a (w 0)
          · have hcd : ContDiffOn ℝ (2 : ℕ∞)
                (fun y' => iteratedFDeriv ℝ m h y' (Fin.tail w)) (polydisc c ρo) :=
              (ContinuousMultilinearMap.apply ℝ (fun _ : Fin m => (Fin n → ℂ)) ℂ (Fin.tail w)).contDiff.comp_contDiffOn
                ((hNsmooth m (le_trans hmk (Nat.le_succ k))).of_le (by exact_mod_cast h2))
            exact hcd.contDiffAt (hSopen.mem_nhds hy)
          · intro j y' hy'
            exact ih' (Fin.tail w) j y' hy'
      have hlev : ∀ m ≤ k+1, ∀ z ∈ P m, ‖iteratedFDeriv ℝ m h z‖ ≤ Mb * T^m := by
        intro m hm
        induction m with
        | zero =>
          intro z hz
          have hz0 : z ∈ polydisc c ρo := by rw [← hPzero]; exact hz
          rw [pow_zero, mul_one]
          have h1 : ‖iteratedFDeriv ℝ 0 h z‖ = ‖h z‖ := by
            rw [← iteratedFDerivWithin_univ (𝕜 := ℝ) (f := h) (n := 0), norm_iteratedFDerivWithin_zero]
          rw [h1]
          exact hM z hz0
        | succ m ih =>
          have hmk : m ≤ k := by omega
          have ihC := ih (Nat.le_of_succ_le hm)
          intro z hz
          have hcurry : iteratedFDeriv ℝ (m+1) h z
              = (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m+1) => (Fin n → ℂ)) ℂ).symm
                  (fderiv ℝ (iteratedFDeriv ℝ m h) z) := by
            have hh := iteratedFDerivWithin_succ_eq_comp_left (𝕜 := ℝ) (f := h) (s := Set.univ) (n := m)
            simp only [iteratedFDerivWithin_univ, fderivWithin_univ] at hh
            simpa using congrFun hh z
          have hbnd : ∀ w : Fin m → (Fin n → ℂ),
              ‖fderiv ℝ (fun y' => iteratedFDeriv ℝ m h y' w) z‖
                ≤ Mb * T^m * (∏ i, ‖w i‖) * T := by
            intro w
            have hsm : ∀ (a : ℂ) (v : Fin n → ℂ),
                fderiv ℝ (fun y' => iteratedFDeriv ℝ m h y' w) z (a • v)
                  = a • fderiv ℝ (fun y' => iteratedFDeriv ℝ m h y' w) z v :=
              fun a v => fderiv_smul_of_hol
                (fun j => hholB m hmk w j z (hPS (m+1) hz)) a v
            refine le_trans (norm_le_sum_apply_single _ hsm) ?_
            have hstep : ∀ c₀ : Fin n, ‖fderiv ℝ (fun y' => iteratedFDeriv ℝ m h y' w) z
                (Pi.single c₀ (1:ℂ))‖ ≤ Mb * T^m * (∏ i, ‖w i‖) / η c₀ := by
              intro c₀
              refine norm_fderiv_single_le (S := P m) (hhol := ?_) (hdiff := ?_) (hε := hηpos c₀)
                (hball := ?_) (hB := ?_)
              · intro j y hy
                exact hholB m hmk w j y (hPS m hy)
              · intro y hy
                have hcd : ContDiffOn ℝ (((k+1-m : ℕ)) : ℕ∞)
                    (fun y' => iteratedFDeriv ℝ m h y' w) (polydisc c ρo) :=
                  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin m => (Fin n → ℂ)) ℂ w).contDiff.comp_contDiffOn
                    (hNsmooth m (le_trans hmk (Nat.le_succ k)))
                exact ((hcd.of_le (by exact_mod_cast (show 1 ≤ k+1-m by omega))).contDiffAt
                  (hSopen.mem_nhds (hPS m hy))).differentiableAt one_ne_zero
              · intro t ht
                exact hPball m z hz c₀ t ht
              · intro y hy
                refine le_trans (ContinuousMultilinearMap.le_opNorm (iteratedFDeriv ℝ m h y) w) ?_
                have h1 := mul_le_mul_of_nonneg_right (ihC y hy)
                  (Finset.prod_nonneg (s := Finset.univ) fun i _ => norm_nonneg (w i))
                calc ‖iteratedFDeriv ℝ m h y‖ * ∏ i, ‖w i‖ ≤ (Mb * T^m) * ∏ i, ‖w i‖ := h1
                  _ = Mb * T^m * ∏ i, ‖w i‖ := rfl
            calc ∑ c : Fin n, ‖fderiv ℝ (fun y' => iteratedFDeriv ℝ m h y' w) z (Pi.single c (1:ℂ))‖
                ≤ ∑ c : Fin n, Mb * T^m * (∏ i, ‖w i‖) / η c := Finset.sum_le_sum fun c _ => hstep c
              _ = Mb * T^m * (∏ i, ‖w i‖) * T := by
                  rw [hTdef, Finset.mul_sum]
                  refine Finset.sum_congr rfl fun c _ => ?_
                  rw [mul_comm]
                  ring
          have hmain : ‖iteratedFDeriv ℝ (m+1) h z‖ ≤ Mb * T^m * T := by
            refine ContinuousMultilinearMap.opNorm_le_bound (f := iteratedFDeriv ℝ (m+1) h z)
              (M := Mb * T^m * T) (by positivity) fun w => ?_
            rw [iteratedFDeriv_succ_apply w (hNdiff m hmk z (hPS (m+1) hz))]
            calc ‖fderiv ℝ (fun y' => iteratedFDeriv ℝ m h y' (Fin.tail w)) z (w 0)‖
                ≤ ‖fderiv ℝ (fun y' => iteratedFDeriv ℝ m h y' (Fin.tail w)) z‖ * ‖w 0‖ :=
                  ContinuousLinearMap.le_opNorm _ _
              _ ≤ (Mb * T^m * (∏ i, ‖(Fin.tail w) i‖) * T) * ‖w 0‖ :=
                  mul_le_mul_of_nonneg_right (hbnd (Fin.tail w)) (norm_nonneg _)
              _ = (Mb * T^m * T) * ∏ i, ‖w i‖ := by
                  rw [Fin.prod_univ_succ]
                  simp only [Fin.tail_def]
                  ring
          calc ‖iteratedFDeriv ℝ (m+1) h z‖ ≤ Mb * T^m * T := hmain
            _ = Mb * T^(m+1) := by rw [pow_succ]; ring

      have hPanti : ∀ {m m' : ℕ}, m ≤ m' → P m' ⊆ P m := by
        intro m m' hmm z hz j
        have h1 : (m : ℝ) * η j ≤ (m' : ℝ) * η j :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hmm) (hηpos j).le
        have h2 : ρo j - (m' : ℝ) * η j ≤ ρo j - (m : ℝ) * η j := by linarith
        exact lt_of_lt_of_le (hz j) h2
      have hconv : Convex ℝ (polydisc c ρi) := by
        intro x hx y hy a b ha hb hab j
        have hxj : ‖x j - c j‖ < ρi j := hx j
        have hyj : ‖y j - c j‖ < ρi j := hy j
        have hdecomp : (a • x + b • y) j - c j
            = (a : ℂ) * (x j - c j) + (b : ℂ) * (y j - c j) := by
          have h1 : (a • x + b • y) j = (a : ℂ) * x j + (b : ℂ) * y j := by
            simp only [Pi.add_apply, Pi.smul_apply, Complex.real_smul]
          have hhab : ((a : ℂ) + (b : ℂ)) = 1 := by
            rw [← Complex.ofReal_add, hab, Complex.ofReal_one]
          have key : c j = ((a : ℂ) + (b : ℂ)) * c j := by rw [hhab, one_mul]
          rw [h1]
          conv_lhs => rw [key]
          ring
        rw [hdecomp]
        calc ‖(a : ℂ) * (x j - c j) + (b : ℂ) * (y j - c j)‖
            ≤ ‖(a : ℂ) * (x j - c j)‖ + ‖(b : ℂ) * (y j - c j)‖ := norm_add_le _ _
          _ = a * ‖x j - c j‖ + b * ‖y j - c j‖ := by
              rw [norm_mul, norm_mul, show ‖(a:ℂ)‖ = |a| from by simp,
                show ‖(b:ℂ)‖ = |b| from by simp, abs_of_nonneg ha, abs_of_nonneg hb]
          _ < a * ρi j + b * ρi j := by
              rcases eq_or_lt_of_le ha with h0 | hpos
              · have hb1 : b = 1 := by linarith
                rw [← h0, hb1, zero_mul, zero_mul, zero_add, one_mul, one_mul]
                simpa using hyj
              · exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hxj hpos)
                  (mul_le_mul_of_nonneg_left hyj.le hb)
          _ = ρi j := by rw [← add_mul, hab, one_mul]
      have hR0pos : 0 < R0 := by
        rw [hR0def]
        exact Finset.sum_pos' (fun j _ => (hempty j).le) ⟨⟨0, hn⟩, Finset.mem_univ _, hempty ⟨0, hn⟩⟩
      have hdiam : ∀ x ∈ polydisc c ρi, ∀ y ∈ polydisc c ρi, ‖x - y‖ ≤ 2 * |R0| + 1 := by
        intro x hx y hy
        have hxc : ‖x - c‖ ≤ R0 := by
          rw [pi_norm_le_iff_of_nonneg hR0pos.le]
          intro j
          rw [Pi.sub_apply]
          exact le_trans (le_of_lt (hx j))
            (Finset.single_le_sum (fun i _ => (hempty i).le) (Finset.mem_univ j))
        have hyc : ‖y - c‖ ≤ R0 := by
          rw [pi_norm_le_iff_of_nonneg hR0pos.le]
          intro j
          rw [Pi.sub_apply]
          exact le_trans (le_of_lt (hy j))
            (Finset.single_le_sum (fun i _ => (hempty i).le) (Finset.mem_univ j))
        have h1 : x - y = (x - c) + (c - y) := by abel
        rw [h1]
        calc ‖(x - c) + (c - y)‖ ≤ ‖x - c‖ + ‖c - y‖ := norm_add_le _ _
          _ = ‖x - c‖ + ‖y - c‖ := by rw [norm_sub_rev c y]
          _ ≤ R0 + R0 := add_le_add hxc hyc
          _ = 2 * R0 := by ring
          _ ≤ 2 * |R0| + 1 := by
              rw [abs_of_pos hR0pos]; linarith
      have hiter : ∀ i ≤ k, iterDerivNorm i h (polydisc c ρi) ≤ ENNReal.ofReal (Mb * T^i) := by
        intro i hi
        refine iSup₂_le fun z hz => ?_
        refine ENNReal.ofReal_le_ofReal ?_
        rw [iteratedFDerivWithin_of_isOpen i (isOpen_polydisc c ρi) hz]
        exact hlev i (le_trans hi (Nat.le_succ k)) z
          (hPanti (le_trans hi (Nat.le_succ k)) (hPinner hz))
      have hholder : ∀ i ≤ k, holderSeminorm i α h (polydisc c ρi) ≤
          ENNReal.ofReal (Mb * (T^(i+1) * (2 * |R0| + 1) ^ (1 - α))) := by
        intro i hi
        have hik : i + 1 ≤ k + 1 := Nat.succ_le_succ hi
        refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
        refine ENNReal.ofReal_le_ofReal ?_
        have hbd : ∀ z ∈ polydisc c ρi, ‖fderivWithin ℝ (iteratedFDerivWithin ℝ i h (polydisc c ρi))
            (polydisc c ρi) z‖ ≤ Mb * T^(i+1) := by
          intro z hz
          rw [norm_fderivWithin_iteratedFDerivWithin,
            iteratedFDerivWithin_of_isOpen (i+1) (isOpen_polydisc c ρi) hz]
          exact hlev (i+1) hik z (hPanti hik (hPinner hz))
        have hdiff : DifferentiableOn ℝ (iteratedFDerivWithin ℝ i h (polydisc c ρi))
            (polydisc c ρi) := by
          have hmono : ContDiffOn ℝ ((k+1 : ℕ) : ℕ∞) h (polydisc c ρi) :=
            hh.mono fun z hz => polydisc_mono (fun j => (hmono j).le) hz
          have hcd := contDiffOn_iteratedFDerivWithin (S := polydisc c ρi)
            (isOpen_polydisc c ρi).uniqueDiffOn hmono i (le_trans hi (Nat.le_succ k))
          refine hcd.differentiableOn ?_
          have h1 : k + 1 - i ≠ 0 := by omega
          exact_mod_cast h1
        have hmv : ‖iteratedFDerivWithin ℝ i h (polydisc c ρi) x
            - iteratedFDerivWithin ℝ i h (polydisc c ρi) y‖ ≤ (Mb * T^(i+1)) * ‖x - y‖ := by
          have h0 := Convex.norm_image_sub_le_of_norm_fderivWithin_le
            (f := iteratedFDerivWithin ℝ i h (polydisc c ρi)) (C := Mb * T^(i+1))
            hdiff hbd hconv hx hy
          simpa only [norm_sub_rev] using h0
        have hpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
        have hrpow : ‖x - y‖ ^ (1 - α) ≤ (2 * |R0| + 1) ^ (1 - α) :=
          Real.rpow_le_rpow (norm_nonneg _) (hdiam x hx y hy) (sub_nonneg.mpr hα1)
        have hratio : ‖x - y‖ / ‖x - y‖ ^ α = ‖x - y‖ ^ (1 - α) := by
          rw [Real.rpow_sub hpos 1 α, Real.rpow_one]
        calc ‖iteratedFDerivWithin ℝ i h (polydisc c ρi) x
              - iteratedFDerivWithin ℝ i h (polydisc c ρi) y‖ / ‖x - y‖ ^ α
            ≤ (Mb * T^(i+1)) * ‖x - y‖ / ‖x - y‖ ^ α := by
              rw [div_le_div_iff_of_pos_right (Real.rpow_pos_of_pos hpos α)]
              exact hmv
          _ = (Mb * T^(i+1)) * (‖x - y‖ ^ (1 - α)) := by
              rw [mul_div_assoc, hratio]
          _ ≤ (Mb * T^(i+1)) * (2 * |R0| + 1) ^ (1 - α) :=
              mul_le_mul_of_nonneg_left hrpow (by positivity)
          _ = Mb * (T^(i+1) * (2 * |R0| + 1) ^ (1 - α)) := by ring
      -- ### assembly
      have hsum : holderNorm k α h (polydisc c ρi) ≤ ENNReal.ofReal (Mb * Cc) := by
        rw [holderNorm]
        calc ∑ i ∈ Finset.range (k + 1),
              (iterDerivNorm i h (polydisc c ρi) + holderSeminorm i α h (polydisc c ρi))
            ≤ ∑ i ∈ Finset.range (k + 1), (ENNReal.ofReal (Mb * T^i)
              + ENNReal.ofReal (Mb * (T^(i+1) * (2 * |R0| + 1) ^ (1 - α)))) := by
              refine Finset.sum_le_sum fun i hi => ?_
              have hi' : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
              exact add_le_add (hiter i hi') (hholder i hi')
          _ = ENNReal.ofReal (Mb * Cc) := by
              have hstep : ∑ i ∈ Finset.range (k + 1), (ENNReal.ofReal (Mb * T^i)
                    + ENNReal.ofReal (Mb * (T^(i+1) * (2 * |R0| + 1) ^ (1 - α))))
                  = ∑ i ∈ Finset.range (k + 1), ENNReal.ofReal (Mb * T^i
                    + Mb * (T^(i+1) * (2 * |R0| + 1) ^ (1 - α))) := by
                refine Finset.sum_congr rfl fun i _ => ?_
                rw [ENNReal.ofReal_add (mul_nonneg hMnn (pow_nonneg hTpos.le i))
                  (mul_nonneg hMnn (mul_nonneg (pow_nonneg hTpos.le (i+1))
                    (Real.rpow_nonneg (by positivity) _)))]
              rw [hstep, ← ENNReal.ofReal_sum_of_nonneg (f := fun i => Mb * T^i
                + Mb * (T^(i+1) * (2 * |R0| + 1) ^ (1 - α))) (fun i _ => add_nonneg
                (mul_nonneg hMnn (pow_nonneg hTpos.le i))
                (mul_nonneg hMnn (mul_nonneg (pow_nonneg hTpos.le (i+1))
                  (Real.rpow_nonneg (by positivity) _))))]
              congr 1
              rw [hCcdef, Finset.mul_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              ring
      calc holderNorm k α h (polydisc c ρi) ≤ ENNReal.ofReal (Mb * Cc) := hsum
        _ = ENNReal.ofReal (Cc * Mb) := by rw [mul_comm]
  -- ## the final reduction to the case of a finite sup
  rcases eq_or_ne (⨆ z ∈ polydisc c ρo, ENNReal.ofReal ‖h z‖) ⊤ with htop | hne
  · rw [htop]
    have hCcne : ENNReal.ofReal Cc ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact hCcpos
    rw [ENNReal.mul_top hCcne]
    exact le_top
  · have hfin : (⨆ z ∈ polydisc c ρo, ENNReal.ofReal ‖h z‖)
        = ENNReal.ofReal ((⨆ z ∈ polydisc c ρo, ENNReal.ofReal ‖h z‖).toReal) :=
      (ENNReal.ofReal_toReal hne).symm
    have hbound : ∀ z ∈ polydisc c ρo,
        ‖h z‖ ≤ (⨆ z ∈ polydisc c ρo, ENNReal.ofReal ‖h z‖).toReal := by
      intro z hz
      have h1 : ENNReal.ofReal ‖h z‖ ≤ (⨆ z ∈ polydisc c ρo, ENNReal.ofReal ‖h z‖) :=
        le_iSup₂_of_le z hz le_rfl
      rw [hfin] at h1
      exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp h1
    rw [hfin]
    refine le_trans (core _ hbound) (le_of_eq ?_)
    rw [ENNReal.ofReal_mul hCcpos.le]
