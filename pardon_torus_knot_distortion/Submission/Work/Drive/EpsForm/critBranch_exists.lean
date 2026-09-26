import Mathlib

open scoped Topology

namespace Work.Drive.EpsForm

/-- The critical-point equation of the linearly perturbed family `q ↦ f q + t * g q`, as a
function of `(t, p)`: the derivative of `f` perturbed by `t` times the derivative of `g`. -/
noncomputable def critMap (f g : ℝ × ℝ → ℝ) : ℝ × (ℝ × ℝ) → (ℝ × ℝ →L[ℝ] ℝ) :=
  fun tp => fderiv ℝ f tp.2 + tp.1 • fderiv ℝ g tp.2

lemma critMap_apply (f g : ℝ × ℝ → ℝ) (t : ℝ) (p : ℝ × ℝ) :
    critMap f g (t, p) = fderiv ℝ f p + t • fderiv ℝ g p := rfl

/-- The critical points of `q ↦ f q + t * g q` are precisely the zeros of `critMap f g (t, ·)`. -/
lemma critMap_eq_fderiv {f g : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (t : ℝ) (p : ℝ × ℝ) :
    critMap f g (t, p) = fderiv ℝ (fun q : ℝ × ℝ => f q + t * g q) p := by
  have hdf : DifferentiableAt ℝ f p := (hf.differentiable (by norm_num)).differentiableAt
  have hdg : DifferentiableAt ℝ g p := (hg.differentiable (by norm_num)).differentiableAt
  rw [critMap_apply]
  have hsplit : (fun q : ℝ × ℝ => f q + t * g q) = f + fun q : ℝ × ℝ => t * g q := rfl
  rw [hsplit, fderiv_add hdf (hdg.const_mul t), fderiv_const_mul hdg t]

/-- `critMap f g` is `C¹` at `(0, x)` when `f` and `g` are `C²`. -/
lemma critMap_contDiffAt {f g : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (x : ℝ × ℝ) : ContDiffAt ℝ 1 (critMap f g) (0, x) := by
  have h1 : ContDiffAt ℝ 1 (fun tp : ℝ × (ℝ × ℝ) => fderiv ℝ f tp.2) (0, x) :=
    (hf.fderiv_right (m := 1) (n := 2) le_rfl).contDiffAt.comp (0, x) contDiffAt_snd
  have h2 : ContDiffAt ℝ 1 (fun tp : ℝ × (ℝ × ℝ) => fderiv ℝ g tp.2) (0, x) :=
    (hg.fderiv_right (m := 1) (n := 2) le_rfl).contDiffAt.comp (0, x) contDiffAt_snd
  have h3 : ContDiffAt ℝ 1 (fun tp : ℝ × (ℝ × ℝ) => tp.1 • fderiv ℝ g tp.2) (0, x) :=
    ContDiffAt.smul contDiffAt_fst h2
  change ContDiffAt ℝ 1
    (fun tp : ℝ × (ℝ × ℝ) => fderiv ℝ f tp.2 + tp.1 • fderiv ℝ g tp.2) (0, x)
  exact h1.add h3

/-- The partial derivative in `p` of the critical-point equation at `(0, x)` is the Hessian of
`f` at `x`. -/
lemma critMap_partial {f g : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (x : ℝ × ℝ) :
    (fderiv ℝ (critMap f g) (0, x)) ∘L (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))
      = fderiv ℝ (fderiv ℝ f) x := by
  have hc : ContDiffAt ℝ 1 (critMap f g) (0, x) := critMap_contDiffAt hf hg x
  have hd : HasFDerivAt (critMap f g) (fderiv ℝ (critMap f g) (0, x)) (0, x) :=
    (hc.differentiableAt (by norm_num)).hasFDerivAt
  have hcomp : HasFDerivAt (fun p : ℝ × ℝ => critMap f g (0, p))
      ((fderiv ℝ (critMap f g) (0, x)) ∘L (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))) x :=
    hd.comp x (hasFDerivAt_prodMk_right (𝕜 := ℝ) (E := ℝ) (F := ℝ × ℝ) (0 : ℝ) x)
  rw [← hcomp.fderiv]
  have hfun : (fun p : ℝ × ℝ => critMap f g (0, p)) = fderiv ℝ f := by
    funext p
    rw [critMap_apply]
    simp
  rw [hfun]

/-- An injective continuous linear map from `ℝ²` to its dual is invertible. -/
lemma hessian_isInvertible (H : ℝ × ℝ →L[ℝ] (ℝ × ℝ →L[ℝ] ℝ))
    (h : Function.Injective H) : H.IsInvertible := by
  have hfin : Module.finrank ℝ (ℝ × ℝ) = Module.finrank ℝ (ℝ × ℝ →L[ℝ] ℝ) := by
    have h1 : Module.finrank ℝ (ℝ × ℝ) = 2 := by
      rw [Module.finrank_prod, Module.finrank_self]
    have h2 : Module.finrank ℝ (ℝ × ℝ →L[ℝ] ℝ) = 2 := by
      have hh : Module.finrank ℝ (ℝ × ℝ →L[ℝ] ℝ) = Module.finrank ℝ (ℝ × ℝ →ₗ[ℝ] ℝ) :=
        (LinearEquiv.finrank_eq
          (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := ℝ × ℝ) (F' := ℝ))).symm
      rw [hh, Module.finrank_linearMap, Module.finrank_prod, Module.finrank_self]
    rw [h1, h2]
  refine ⟨ContinuousLinearEquiv.ofBijective H ?_ ?_, rfl⟩
  · rw [LinearMap.ker_eq_bot]
    simpa using h
  · rw [LinearMap.range_eq_top]
    simpa using (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp h

/-- **Local branches of the critical points of a linearly perturbed family** (one nondegenerate
critical point `x` of `f`). -/
theorem critBranch_local {f g : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    {x : ℝ × ℝ} (hx0 : fderiv ℝ f x = 0)
    (hx1 : Function.Injective (fderiv ℝ (fderiv ℝ f) x)) :
    ∃ (y : ℝ → ℝ × ℝ) (δ r C : ℝ), 0 < δ ∧ 0 < r ∧ 0 ≤ C ∧ y 0 = x ∧
      (∀ t : ℝ, |t| < δ → fderiv ℝ (fun q : ℝ × ℝ => f q + t * g q) (y t) = 0) ∧
      (∀ t : ℝ, |t| < δ → ∀ p : ℝ × ℝ, ‖p - x‖ < r →
        fderiv ℝ (fun q : ℝ × ℝ => f q + t * g q) p = 0 → p = y t) ∧
      (∀ t : ℝ, |t| < δ → ‖y t - x‖ ≤ C * |t|) := by
  classical
  have hc : ContDiffAt ℝ 1 (critMap f g) (0, x) := critMap_contDiffAt hf hg x
  have hpn : (1 : WithTop ℕ∞) ≠ 0 := by norm_num
  have hInv :
      ((fderiv ℝ (critMap f g) (0, x)) ∘L (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))).IsInvertible := by
    rw [critMap_partial hf hg x]
    exact hessian_isInvertible _ hx1
  let ψ : ℝ → ℝ × ℝ := hc.implicitFunction hpn hInv
  have hψ0 : ψ 0 = x := hc.implicitFunction_apply_self hpn hInv
  have hzero : critMap f g ((0 : ℝ), x) = 0 := by
    rw [critMap_apply, hx0, zero_smul, add_zero]
  -- the critical-point property
  obtain ⟨εc, hεc, hcrit⟩ := Metric.mem_nhds_iff.mp (by
    have h := hc.eventually_apply_implicitFunction hpn hInv
    rw [hzero] at h
    exact h)
  -- uniqueness in a ball
  obtain ⟨εu, hεu, huniq⟩ := Metric.mem_nhds_iff.mp (by
    have h := hc.eventually_apply_eq_iff_implicitFunction hpn hInv
    rwa [hzero] at h)
  -- Lipschitz at `0`
  set L : ℝ →L[ℝ] (ℝ × ℝ) :=
    -((fderiv ℝ (critMap f g) (0, x)) ∘L (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))).inverse ∘L
      ((fderiv ℝ (critMap f g) (0, x)) ∘L (ContinuousLinearMap.inl ℝ ℝ (ℝ × ℝ))) with hL
  have hstrict : HasStrictFDerivAt ψ L 0 := by
    rw [hL]
    exact hc.hasStrictFDerivAt_implicitFunction hpn hInv
  obtain ⟨s, hs, hlip⟩ := hstrict.exists_lipschitzOnWith_of_nnnorm_lt (‖L‖₊ + 1) (by simp)
  obtain ⟨εl, hεl, hεlsub⟩ := Metric.mem_nhds_iff.mp hs
  have hδc : min εc (min εu εl) ≤ εc := min_le_left _ _
  have hδu : min εc (min εu εl) ≤ εu := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδl : min εc (min εu εl) ≤ εl := le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨ψ, min εc (min εu εl), εu, ((‖L‖₊ + 1 : NNReal) : ℝ),
    lt_min hεc (lt_min hεu hεl), hεu, NNReal.coe_nonneg _, hψ0, ?_, ?_, ?_⟩
  · intro t ht
    rw [← critMap_eq_fderiv hf hg t (ψ t)]
    refine hcrit ?_
    simpa [Metric.mem_ball, Real.dist_eq, sub_zero] using lt_of_lt_of_le ht hδc
  · intro t ht p hp hcritp
    have htε : dist ((t : ℝ), p) (((0 : ℝ), x)) < εu := by
      have h1 : dist (t : ℝ) (0 : ℝ) < εu := by
        rw [Real.dist_eq, sub_zero]
        exact lt_of_lt_of_le ht hδu
      rw [Prod.dist_eq]
      exact max_lt h1 hp
    exact ((huniq htε).mp (by
      rw [critMap_eq_fderiv hf hg t p]; exact hcritp)).symm
  · intro t ht
    have htε : |t| < εl := lt_of_lt_of_le ht hδl
    have hts : t ∈ s := hεlsub (by rw [Metric.mem_ball, Real.dist_eq, sub_zero]; exact htε)
    have h0s : (0 : ℝ) ∈ s := mem_of_mem_nhds hs
    have hb := hlip.dist_le_mul t hts 0 h0s
    rw [hψ0, dist_eq_norm, Real.dist_eq, sub_zero] at hb
    exact hb

/-- **Local branches of the critical points of a linearly perturbed family.** -/
theorem critBranch_exists {f g : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (X : Finset (ℝ × ℝ))
    (hX : ∀ x ∈ X, fderiv ℝ f x = 0 ∧ Function.Injective (fderiv ℝ (fderiv ℝ f) x)) :
    ∃ (y : ℝ × ℝ → ℝ → ℝ × ℝ) (δ r C : ℝ), 0 < δ ∧ 0 < r ∧ 0 ≤ C ∧
      (∀ x ∈ X, y x 0 = x) ∧
      (∀ x ∈ X, ∀ t : ℝ, |t| < δ → fderiv ℝ (fun q : ℝ × ℝ => f q + t * g q) (y x t) = 0) ∧
      (∀ x ∈ X, ∀ t : ℝ, |t| < δ → ∀ p : ℝ × ℝ, ‖p - x‖ < r →
        fderiv ℝ (fun q : ℝ × ℝ => f q + t * g q) p = 0 → p = y x t) ∧
      (∀ x ∈ X, ∀ t : ℝ, |t| < δ → ‖y x t - x‖ ≤ C * |t|) := by
  classical
  have hloc : ∀ x : {x // x ∈ X}, ∃ (y : ℝ → ℝ × ℝ) (δ r C : ℝ), 0 < δ ∧ 0 < r ∧ 0 ≤ C ∧
      y 0 = x.1 ∧
      (∀ t : ℝ, |t| < δ → fderiv ℝ (fun q : ℝ × ℝ => f q + t * g q) (y t) = 0) ∧
      (∀ t : ℝ, |t| < δ → ∀ p : ℝ × ℝ, ‖p - x.1‖ < r →
        fderiv ℝ (fun q : ℝ × ℝ => f q + t * g q) p = 0 → p = y t) ∧
      (∀ t : ℝ, |t| < δ → ‖y t - x.1‖ ≤ C * |t|) :=
    fun x => critBranch_local hf hg (hX x.1 x.2).1 (hX x.1 x.2).2
  choose Y D R C hspec using hloc
  by_cases hne : X.Nonempty
  · have hatt : X.attach.Nonempty := by
      obtain ⟨x, hx⟩ := hne
      exact ⟨⟨x, hx⟩, Finset.mem_attach X ⟨x, hx⟩⟩
    refine ⟨fun x => if h : x ∈ X then Y ⟨x, h⟩ else fun _ => x,
      X.attach.inf' hatt D, X.attach.inf' hatt R, X.attach.sup' hatt C,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Finset.lt_inf'_iff]
      exact fun i _ => (hspec i).1
    · rw [Finset.lt_inf'_iff]
      exact fun i _ => (hspec i).2.1
    · obtain ⟨i, hi⟩ := hatt
      exact le_trans (hspec i).2.2.1 (Finset.le_sup' C hi)
    · intro x hx
      simpa [dif_pos hx] using (hspec ⟨x, hx⟩).2.2.2.1
    · intro x hx t ht
      simpa [dif_pos hx] using (hspec ⟨x, hx⟩).2.2.2.2.1 t
        (lt_of_lt_of_le ht (Finset.inf'_le D (Finset.mem_attach X ⟨x, hx⟩)))
    · intro x hx t ht p hp hcritp
      simpa [dif_pos hx] using (hspec ⟨x, hx⟩).2.2.2.2.2.1 t
        (lt_of_lt_of_le ht (Finset.inf'_le D (Finset.mem_attach X ⟨x, hx⟩)))
        p (lt_of_lt_of_le hp (Finset.inf'_le R (Finset.mem_attach X ⟨x, hx⟩)))
        hcritp
    · intro x hx t ht
      have h1 := (hspec ⟨x, hx⟩).2.2.2.2.2.2 t
        (lt_of_lt_of_le ht (Finset.inf'_le D (Finset.mem_attach X ⟨x, hx⟩)))
      have h2 : C ⟨x, hx⟩ ≤ X.attach.sup' hatt C :=
        Finset.le_sup' C (Finset.mem_attach X ⟨x, hx⟩)
      simpa [dif_pos hx] using le_trans h1 (mul_le_mul_of_nonneg_right h2 (abs_nonneg t))
  · refine ⟨fun x _ => x, 1, 1, 0, one_pos, one_pos, le_refl 0, ?_, ?_, ?_, ?_⟩
    · exact fun x hx => absurd ⟨x, hx⟩ hne
    · exact fun x hx => absurd ⟨x, hx⟩ hne
    · exact fun x hx => absurd ⟨x, hx⟩ hne
    · exact fun x hx => absurd ⟨x, hx⟩ hne

end Work.Drive.EpsForm
