import Mathlib
import Submission.Work.Drive.PushDisc.lensCornerSignOfCharts

open scoped ContDiff Manifold

namespace Work.Drive.PushDisc

noncomputable section

open Set Filter

set_option maxHeartbeats 1000000 in
/-- **The corner sign of the framing chart, from the top-edge identity on the *closed*
interval only.**  This is `Work.Drive.PushDisc.lensCornerSignOfCharts` with the hypothesis
`hΔ1` weakened from a global identity to its restriction to `Set.Icc (-1) 1` -- the only
range on which the proof (`lcs_hadamard_one` / `lcs_hadamard_neg_one`) consumes it.  The
weaker form is what the bundled `LWLensDisc` supplies (`hΔ1 : ∀ x, |x| ≤ F.X' → ...`). -/
theorem lensCornerSignOfChartsArc {k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * (k + 1))))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1))))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y : M, Function.Injective (mfderiv
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1))))) f y))
    (Φ : EuclideanSpace ℝ (Fin (2 * (k + 1))) → Work.Drive.Whitney.Mdl k)
    (Θ : Work.Drive.Whitney.Mdl k → EuclideanSpace ℝ (Fin (2 * (k + 1))))
    (hΦsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hΘsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ)
    (hΘΦ : ∀ y : EuclideanSpace ℝ (Fin (2 * (k + 1))), Θ (Φ y) = y)
    (hΦΘ : ∀ ξ : Work.Drive.Whitney.Mdl k, Φ (Θ ξ) = ξ)
    (γ₁ γ₂ : ℝ → M) (p₁ p₂ q₁ q₂ : M)
    (hγ₁ : Continuous γ₁) (hγ₂ : Continuous γ₂)
    (hp₁ : γ₁ 0 = p₁) (hq₁ : γ₁ 1 = q₁) (hp₂ : γ₂ 0 = p₂) (hq₂ : γ₂ 1 = q₂)
    (hfp : f p₁ = f p₂) (hfq : f q₁ = f q₂)
    (hsign : Work.Whitney.OppositeType f γ₁ γ₂ p₁ p₂ q₁ q₂)
    (c₁ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1))))
    (hc₁ : Work.Whitney.IsSmoothChart c₁) (hp₁c₁ : p₁ ∈ c₁.source) (hq₁c₁ : q₁ ∈ c₁.source)
    (hsrc₁ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t ∈ c₁.source)
    (hsh₁ : ∀ x : M, x ∈ c₁.source → (Φ (f x)).2.1 = 0 ∧ (Φ (f x)).2.2.2 = 0)
    (c₂ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1))))
    (hc₂ : Work.Whitney.IsSmoothChart c₂) (hp₂c₂ : p₂ ∈ c₂.source) (hq₂c₂ : q₂ ∈ c₂.source)
    (hsrc₂ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₂ t ∈ c₂.source)
    (harc₂ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      c₂ (γ₂ t) = Work.Drive.PushDisc.splitE k (((2 : ℝ) * t - 1), (0 : EuclideanSpace ℝ (Fin k))))
    (Δ : ℝ × ℝ → Work.Drive.Whitney.Mdl k)
    (hΔ0 : ∀ x : ℝ, Δ (x, 0) = (x, 0, 0, 0))
    (hΔ1 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Δ (x, Work.Drive.PushDisc.arch x)
      = Φ (f (c₂.symm (Work.Drive.PushDisc.splitE k (x, (0 : EuclideanSpace ℝ (Fin k)))))))
    (hd1 : DifferentiableAt ℝ Δ (1, 0)) (hdm1 : DifferentiableAt ℝ Δ (-1, 0)) :
    ∃ T : Work.Drive.Whitney.Mdl k ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (2 + k + k)),
      0 < Work.Drive.PushDisc.frameDet (2 + k + k) T
            (Work.Drive.PushDisc.cornerFrame (fun p => fderiv ℝ Δ p (1, 0))
              (fun p => fderiv ℝ Δ p (0, 1))
              (fun x j => fderiv ℝ (fun w : EuclideanSpace ℝ (Fin k) =>
                Φ (f (c₂.symm (Work.Drive.PushDisc.splitE k (x, w))))) 0
                (EuclideanSpace.single j (1 : ℝ))) 1)
        * Work.Drive.PushDisc.frameDet (2 + k + k) T
            (Work.Drive.PushDisc.cornerFrame (fun p => fderiv ℝ Δ p (1, 0))
              (fun p => fderiv ℝ Δ p (0, 1))
              (fun x j => fderiv ℝ (fun w : EuclideanSpace ℝ (Fin k) =>
                Φ (f (c₂.symm (Work.Drive.PushDisc.splitE k (x, w))))) 0
                (EuclideanSpace.single j (1 : ℝ))) (-1)) := by
  -- (0) the chart coordinates of the two endpoints of the second sheet
  have harcq : c₂ q₂ = splitE k ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))) := by
    have h := harc₂ 1 ⟨zero_le_one, le_refl _⟩
    rw [hq₂] at h
    norm_num at h
    exact h
  have harcp : c₂ p₂ = splitE k ((-1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))) := by
    have h := harc₂ 0 ⟨le_refl _, zero_le_one⟩
    rw [hp₂] at h
    norm_num at h
    exact h
  -- (1) the two jets of the chart representation at the corners
  set Mq : PP k →L[ℝ] Work.Drive.Whitney.Mdl k :=
    (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c₂.symm u)))
      (splitE k ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))))).comp (splitE k).toContinuousLinearMap
    with hMqdef
  set Mp : PP k →L[ℝ] Work.Drive.Whitney.Mdl k :=
    (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c₂.symm u)))
      (splitE k ((-1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))))).comp (splitE k).toContinuousLinearMap
    with hMpdef
  set Lq : PP k →ₗ[ℝ] Work.Drive.Whitney.Mdl k :=
    (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c₂.symm u)))
      (splitE k ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))))).toLinearMap.comp (splitE k).toLinearMap
    with hLqdef
  set Lp : PP k →ₗ[ℝ] Work.Drive.Whitney.Mdl k :=
    (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c₂.symm u)))
      (splitE k ((-1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))))).toLinearMap.comp (splitE k).toLinearMap
    with hLpdef
  have hLqv : ∀ x : PP k, Lq x = Mq x := by
    intro x
    rw [hLqdef, hMqdef]
    rfl
  have hLpv : ∀ x : PP k, Lp x = Mp x := by
    intro x
    rw [hLpdef, hMpdef]
    rfl
  -- (2) the derivatives of the parametrised chart representation
  have hSq : HasFDerivAt (fun q : PP k => Φ (f (c₂.symm (splitE k q)))) Mq
      ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))) := by
    have h := chartSplit_hasFDerivAt hf Φ hΦsm c₂ hc₂ hq₂c₂
    rw [harcq] at h
    rw [← hMqdef] at h
    simpa using h
  have hSp : HasFDerivAt (fun q : PP k => Φ (f (c₂.symm (splitE k q)))) Mp
      ((-1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))) := by
    have h := chartSplit_hasFDerivAt hf Φ hΦsm c₂ hc₂ hp₂c₂
    rw [harcp] at h
    rw [← hMpdef] at h
    simpa using h
  -- (3) the two x-derivatives of the core
  have hBq : HasDerivAt (fun x : ℝ =>
      Φ (f (c₂.symm (splitE k (x, (0 : EuclideanSpace ℝ (Fin k)))))))
      (Lq ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k)))) 1 := by
    have h := (hSq.comp (1 : ℝ)
      (hasFDerivAt_prodMk_left (1 : ℝ) (0 : EuclideanSpace ℝ (Fin k)))).hasDerivAt
    have hval : (Mq ∘SL ContinuousLinearMap.inl ℝ ℝ (EuclideanSpace ℝ (Fin k))) (1 : ℝ)
        = Lq ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))) := by
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, hLqv]
    rw [hval] at h
    simpa only [Function.comp_def] using h
  have hBp : HasDerivAt (fun x : ℝ =>
      Φ (f (c₂.symm (splitE k (x, (0 : EuclideanSpace ℝ (Fin k)))))))
      (Lp ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k)))) (-1) := by
    have h := (hSp.comp (-1 : ℝ)
      (hasFDerivAt_prodMk_left (-1 : ℝ) (0 : EuclideanSpace ℝ (Fin k)))).hasDerivAt
    have hval : (Mp ∘SL ContinuousLinearMap.inl ℝ ℝ (EuclideanSpace ℝ (Fin k))) (1 : ℝ)
        = Lp ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))) := by
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, hLpv]
    rw [hval] at h
    simpa only [Function.comp_def] using h
  -- (4) the frame columns `V (±1)`
  have hVq : ∀ j : Fin k, (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin k) =>
      Φ (f (c₂.symm (splitE k ((1 : ℝ), w))))) 0) (EuclideanSpace.single j (1 : ℝ))
      = Lq ((0 : ℝ), EuclideanSpace.single j (1 : ℝ)) := by
    intro j
    have hcurve : HasFDerivAt (fun w : EuclideanSpace ℝ (Fin k) => ((1 : ℝ), w))
        (ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin k))) 0 :=
      hasFDerivAt_prodMk_right (1 : ℝ) (0 : EuclideanSpace ℝ (Fin k))
    have h := hSq.comp 0 hcurve
    have hfd : fderiv ℝ (fun w : EuclideanSpace ℝ (Fin k) =>
        Φ (f (c₂.symm (splitE k ((1 : ℝ), w))))) 0
        = (Mq ∘SL ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin k))) := by
      have hh := h.fderiv
      simpa only [Function.comp_def] using hh
    rw [hfd]
    have hval : (Mq ∘SL ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin k)))
        (EuclideanSpace.single j (1 : ℝ)) = Lq ((0 : ℝ), EuclideanSpace.single j (1 : ℝ)) := by
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, hLqv]
    exact hval
  have hVp : ∀ j : Fin k, (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin k) =>
      Φ (f (c₂.symm (splitE k ((-1 : ℝ), w))))) 0) (EuclideanSpace.single j (1 : ℝ))
      = Lp ((0 : ℝ), EuclideanSpace.single j (1 : ℝ)) := by
    intro j
    have hcurve : HasFDerivAt (fun w : EuclideanSpace ℝ (Fin k) => ((-1 : ℝ), w))
        (ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin k))) 0 :=
      hasFDerivAt_prodMk_right (-1 : ℝ) (0 : EuclideanSpace ℝ (Fin k))
    have h := hSp.comp 0 hcurve
    have hfd : fderiv ℝ (fun w : EuclideanSpace ℝ (Fin k) =>
        Φ (f (c₂.symm (splitE k ((-1 : ℝ), w))))) 0
        = (Mp ∘SL ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin k))) := by
      have hh := h.fderiv
      simpa only [Function.comp_def] using hh
    rw [hfd]
    have hval : (Mp ∘SL ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin k)))
        (EuclideanSpace.single j (1 : ℝ)) = Lp ((0 : ℝ), EuclideanSpace.single j (1 : ℝ)) := by
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, hLpv]
    exact hval
  -- (5) the Hadamard relations at the two corners
  have hrelq : (fderiv ℝ Δ (1, 0)) (1, 0) - (2 : ℝ) • (fderiv ℝ Δ (1, 0)) (0, 1)
      = Lq ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))) :=
    lcs_relvec_one Δ (Lq ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))))
      (lcs_hadamard_one Δ (fun x : ℝ =>
          Φ (f (c₂.symm (splitE k (x, (0 : EuclideanSpace ℝ (Fin k)))))))
        (Lq ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k)))) (fun x hx => hΔ1 x hx) hd1 hBq)
  have hrelp : (fderiv ℝ Δ (-1, 0)) (1, 0) + (2 : ℝ) • (fderiv ℝ Δ (-1, 0)) (0, 1)
      = Lp ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))) :=
    lcs_relvec_neg_one Δ (Lp ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))))
      (lcs_hadamard_neg_one Δ (fun x : ℝ =>
          Φ (f (c₂.symm (splitE k (x, (0 : EuclideanSpace ℝ (Fin k)))))))
        (Lp ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k)))) (fun x hx => hΔ1 x hx) hdm1 hBp)
  -- (6) the `x`-derivatives of `Δ` on the bottom edge
  have hdxq : (fderiv ℝ Δ (1, 0)) (1, 0) = (1, 0, 0, 0) :=
    lcs_xDeriv_one Δ (fun x _ => hΔ0 x) hd1
  have hdxp : (fderiv ℝ Δ (-1, 0)) (1, 0) = (1, 0, 0, 0) :=
    lcs_xDeriv_neg_one Δ (fun x _ => hΔ0 x) hdm1
  -- (7) the second frame column at the two corners
  have hdyq : (fderiv ℝ Δ (1, 0)) (0, 1)
      = (2 : ℝ)⁻¹ • ((1, 0, 0, 0) - Lq ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k)))) := by
    have h2 : (2 : ℝ) • ((fderiv ℝ Δ (1, 0)) (0, 1))
        = (1, 0, 0, 0) - Lq ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))) := by
      rw [← hrelq, hdxq]
      abel
    have h3 : (2 : ℝ)⁻¹ • ((2 : ℝ) • ((fderiv ℝ Δ (1, 0)) (0, 1)))
        = (2 : ℝ)⁻¹ • ((1, 0, 0, 0) - Lq ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k)))) := by
      rw [h2]
    rwa [smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_smul] at h3
  have hdyp : (fderiv ℝ Δ (-1, 0)) (0, 1)
      = (-(2 : ℝ)⁻¹) • ((1, 0, 0, 0) - Lp ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k)))) := by
    have h2 : (2 : ℝ) • ((fderiv ℝ Δ (-1, 0)) (0, 1))
        = Lp ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))) - (1, 0, 0, 0) := by
      rw [← hrelp, hdxp]
      abel
    have h3 : (2 : ℝ)⁻¹ • ((2 : ℝ) • ((fderiv ℝ Δ (-1, 0)) (0, 1)))
        = (2 : ℝ)⁻¹ • (Lp ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))) - (1, 0, 0, 0)) := by
      rw [h2]
    rw [smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_smul] at h3
    have h4 : (-(2 : ℝ)⁻¹) • ((1, 0, 0, 0) - Lp ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))))
        = (2 : ℝ)⁻¹ • (Lp ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))) - (1, 0, 0, 0)) := by
      rw [neg_smul, smul_sub, smul_sub, neg_sub]
    rw [h3, h4]
  -- (8) the two corner frames in the shape of the determinant lemma
  have harch1 : arch 1 = 0 := by norm_num [arch]
  have harchm1 : arch (-1) = 0 := by norm_num [arch]
  have hframq : cornerFrame (fun p => fderiv ℝ Δ p (1, 0)) (fun p => fderiv ℝ Δ p (0, 1))
      (fun x j => fderiv ℝ (fun w : EuclideanSpace ℝ (Fin k) =>
        Φ (f (c₂.symm (splitE k (x, w))))) 0 (EuclideanSpace.single j (1 : ℝ))) 1
      = Fin.append (Fin.append ![(1, 0, 0, 0),
          (2 : ℝ)⁻¹ • ((1, 0, 0, 0) - Lq ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))))]
        (fun l : Fin k => Lq ((0 : ℝ), EuclideanSpace.single l (1 : ℝ)))) (iotaU k) := by
    simp only [cornerFrame, planeFrame]
    refine fin_append_congr (fin_append_congr ?_ ?_) rfl
    · rw [harch1, hdxq, hdyq]
    · funext l
      exact hVq l
  have hframp : cornerFrame (fun p => fderiv ℝ Δ p (1, 0)) (fun p => fderiv ℝ Δ p (0, 1))
      (fun x j => fderiv ℝ (fun w : EuclideanSpace ℝ (Fin k) =>
        Φ (f (c₂.symm (splitE k (x, w))))) 0 (EuclideanSpace.single j (1 : ℝ))) (-1)
      = Fin.append (Fin.append ![(1, 0, 0, 0),
          (-(2 : ℝ)⁻¹) • ((1, 0, 0, 0) - Lp ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))))]
        (fun l : Fin k => Lp ((0 : ℝ), EuclideanSpace.single l (1 : ℝ)))) (iotaU k) := by
    simp only [cornerFrame, planeFrame]
    refine fin_append_congr (fin_append_congr ?_ ?_) rfl
    · rw [harchm1, hdxp, hdyp]
    · funext l
      exact hVp l
  -- (9) the two corner determinants
  have hdetq : frameDet (2 + k + k) (lcsT k)
      (cornerFrame (fun p => fderiv ℝ Δ p (1, 0)) (fun p => fderiv ℝ Δ p (0, 1))
        (fun x j => fderiv ℝ (fun w : EuclideanSpace ℝ (Fin k) =>
          Φ (f (c₂.symm (splitE k (x, w))))) 0 (EuclideanSpace.single j (1 : ℝ))) 1)
      = -(2 : ℝ)⁻¹ * LinearMap.det ((Yv k).comp Lq) := by
    rw [hframq]
    exact lensCornerDetOfChart Lq ((2 : ℝ)⁻¹)
  have hdetp : frameDet (2 + k + k) (lcsT k)
      (cornerFrame (fun p => fderiv ℝ Δ p (1, 0)) (fun p => fderiv ℝ Δ p (0, 1))
        (fun x j => fderiv ℝ (fun w : EuclideanSpace ℝ (Fin k) =>
          Φ (f (c₂.symm (splitE k (x, w))))) 0 (EuclideanSpace.single j (1 : ℝ))) (-1))
      = (2 : ℝ)⁻¹ * LinearMap.det ((Yv k).comp Lp) := by
    rw [hframp, lensCornerDetOfChart Lp (-(2 : ℝ)⁻¹)]
    ring
  -- (10) the sign of the bigon, transported to our two charts
  obtain ⟨-, -, -, -, c₁', c₂', c₃', c₄', hm₁, hm₂, hm₃, hm₄, haC, hbC, hprod0⟩ := hsign
  have hsub₁ : γ₁ '' Set.Icc (0 : ℝ) 1 ⊆ c₁.source := by
    rintro y ⟨t, ht, rfl⟩
    exact hsrc₁ t ht
  have hsub₂ : γ₂ '' Set.Icc (0 : ℝ) 1 ⊆ c₂.source := by
    rintro y ⟨t, ht, rfl⟩
    exact hsrc₂ t ht
  have hchain₁ : Work.Whitney.IsArcChain γ₁ c₁ c₁ :=
    Work.Whitney.isArcChain_const (hsub₁ ⟨0, ⟨le_refl _, zero_le_one⟩, rfl⟩)
      (hsub₁ ⟨1, ⟨zero_le_one, le_refl _⟩, rfl⟩) hc₁ hsub₁
  have hchain₂ : Work.Whitney.IsArcChain γ₂ c₂ c₂ :=
    Work.Whitney.isArcChain_const (hsub₂ ⟨0, ⟨le_refl _, zero_le_one⟩, rfl⟩)
      (hsub₂ ⟨1, ⟨zero_le_one, le_refl _⟩, rfl⟩) hc₂ hsub₂
  have hprod : Work.Whitney.pairDet f c₁ c₂ p₁ p₂ * Work.Whitney.pairDet f c₁ c₂ q₁ q₂ < 0 :=
    ((Work.Whitney.pairDet_mul_sign_iff_of_isArcChain hf hγ₁ hγ₂ hp₁ hq₁ hp₂ hq₂
      hp₁c₁ hp₂c₂ hq₁c₁ hq₂c₂ hm₁ hm₂ hm₃ hm₄ hchain₁ hchain₂ haC hbC).2).mpr hprod0
  -- (11) the factorisation of the two `pairDet`s
  have hfacP := pairDet_factor_general hf Φ Θ hΦsm hΘsm hΘΦ c₁ c₂ hc₁ hc₂ hp₁c₁ hp₂c₂ hfp hsh₁
  have hfacQ := pairDet_factor_general hf Φ Θ hΦsm hΘsm hΘΦ c₁ c₂ hc₁ hc₂ hq₁c₁ hq₂c₂ hfq hsh₁
  have hJp : LinearMap.det (Yv k ∘ₗ (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) =>
        Φ (f (c₂.symm u))) (c₂ p₂)).toLinearMap ∘ₗ (splitE k).toLinearMap)
      = LinearMap.det ((Yv k).comp Lp) := by
    rw [harcp, hLpdef]
  have hJq : LinearMap.det (Yv k ∘ₗ (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) =>
        Φ (f (c₂.symm u))) (c₂ q₂)).toLinearMap ∘ₗ (splitE k).toLinearMap)
      = LinearMap.det ((Yv k).comp Lq) := by
    rw [harcq, hLqdef]
  rw [hJp] at hfacP
  rw [hJq] at hfacQ
  -- (12) the named factors
  set Jp : ℝ := LinearMap.det ((Yv k).comp Lp) with hJpdef
  set Jq : ℝ := LinearMap.det ((Yv k).comp Lq) with hJqdef
  set Kp : ℝ := LinearMap.det ((Work.Projection.pairEquiv (k + 1)).toLinearMap.comp
    ((fderiv ℝ Θ (Φ (f p₁))).toLinearMap.comp (pairZ' k).symm.toLinearMap)) with hKpdef
  set Kq : ℝ := LinearMap.det ((Work.Projection.pairEquiv (k + 1)).toLinearMap.comp
    ((fderiv ℝ Θ (Φ (f q₁))).toLinearMap.comp (pairZ' k).symm.toLinearMap)) with hKqdef
  set Ep : ℝ := LinearMap.det ((Xu k).comp ((fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) =>
    Φ (f (c₁.symm u))) (c₁ p₁)).toLinearMap.comp (splitE k).toLinearMap)) with hEpdef
  set Eq : ℝ := LinearMap.det ((Xu k).comp ((fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) =>
    Φ (f (c₁.symm u))) (c₁ q₁)).toLinearMap.comp (splitE k).toLinearMap)) with hEqdef
  have hP : Work.Whitney.pairDet f c₁ c₂ p₁ p₂ = Kp * (Ep * Jp) := hfacP
  have hQ : Work.Whitney.pairDet f c₁ c₂ q₁ q₂ = Kq * (Eq * Jq) := hfacQ
  have hKpos := det_pairEquiv_comp_pairZ'_mul_pos Θ Φ hΘsm hΦsm hΘΦ hΦΘ (Φ (f p₁)) (Φ (f q₁))
  have hK : 0 < Kp * Kq := hKpos
  have hEpos := det_firstJet_mul_pos hf himm Φ hΦsm Θ hΘsm hΘΦ c₁ hc₁ hsh₁ hγ₁ hsub₁
  rw [hp₁, hq₁] at hEpos
  have hE : 0 < Ep * Eq := hEpos
  -- (13) the sign of the two `(y,v)`-block determinants
  have hJneg : Jp * Jq < 0 := by
    have h1 : (Kp * (Ep * Jp)) * (Kq * (Eq * Jq)) < 0 := by rw [← hP, ← hQ]; exact hprod
    have h2 : ((Kp * Kq) * (Ep * Eq)) * (Jp * Jq) < 0 := by
      nlinarith only [h1]
    have h3 : 0 < (Kp * Kq) * (Ep * Eq) := mul_pos hK hE
    nlinarith only [h2, h3]
  -- (14) the corner determinant product
  refine ⟨lcsT k, ?_⟩
  rw [hdetq, hdetp]
  nlinarith only [hJneg]
end

end Work.Drive.PushDisc
