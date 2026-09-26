import Mathlib
import Submission.Work.Drive.Mono.SphereFaceDefs
import Submission.Work.Smooth.OneManifold.Plane.Vertex
import Submission.Work.Drive.Mono.not_three_active_faces

open scoped Topology

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion Set



/-- If `f ≤ h` near `p`, `f p = h p` and both are differentiable at `p`, their derivatives agree. -/
theorem fderiv_eq_of_max_of_eventually_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f h : E → ℝ} {p : E}
    (hh : DifferentiableAt ℝ h p) (hf : DifferentiableAt ℝ f p)
    (hle : ∀ᶠ q in 𝓝 p, f q ≤ h q) (heq : f p = h p) :
    fderiv ℝ f p = fderiv ℝ h p := by
  have hmin : IsLocalMin (fun q => h q - f q) p := by
    filter_upwards [hle] with q hq
    linarith
  have h0 := hmin.fderiv_eq_zero
  change fderiv ℝ (h - f) p = 0 at h0
  rw [fderiv_sub hh hf] at h0
  exact (sub_eq_zero.mp h0).symm

theorem isLocallyArc_corner_sphereFace {ψ : Submission.Diffeo} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ} {z : R3} {p : ℝ × ℝ}
    (hp : Work.BoxShrink.Pinch.par ψ p = z)
    (hzsphere : Submission.boxNorm c σ z = s)
    (hzface : inner ℝ v z = inner ℝ v c + u + h)
    (hd1 : fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0)
    (hd2 : fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0)
    (hd3 : ∀ t : ℝ, fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p ≠
        t • fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p) :
    ∃ V : Set (ℝ × ℝ), IsOpen V ∧ p ∈ V ∧
      Work.Smooth.OneManifold.IsLocallyArcP
        (V ∩ {q : ℝ × ℝ | max (Work.Drive.Mono.boxH ψ s c σ q)
          (-(Work.Drive.Mono.planeG ψ c v u h q)) = 0}) := by
  classical
  have hboxp : boxH ψ s c σ p = 0 := by rw [boxH_apply, hp, hzsphere, sub_self]
  have hplaneGp : planeG ψ c v u h p = 0 := by rw [planeG_apply, hp, hzface, sub_self]
  have hboxfun : boxH ψ s c σ
      = fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q) - s := rfl
  have hMne : fderiv ℝ (boxH ψ s c σ) p ≠ 0 := by
    rw [hboxfun, fderiv_sub_const]; exact hd2
  have hboxDiff : DifferentiableAt ℝ (boxH ψ s c σ) p := by
    by_contra hcon
    exact hMne (fderiv_zero_of_not_differentiableAt hcon)
  have hLnot : ∀ t : ℝ, fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p
      ≠ t • fderiv ℝ (boxH ψ s c σ) p := by
    intro t; rw [hboxfun, fderiv_sub_const]; exact hd3 t
  have hactive_fderiv : ∀ (i : Fin 3) (ε : ℝ), (ε = 1 ∨ ε = -1) → faceW ψ s c σ i ε p = 0 →
      fderiv ℝ (faceW ψ s c σ i ε) p = fderiv ℝ (boxH ψ s c σ) p := by
    intro i ε hε hact
    refine fderiv_eq_of_max_of_eventually_le hboxDiff
      ((contDiff_faceW ψ s c σ i ε).differentiable (by simp)).differentiableAt
      (Filter.Eventually.of_forall fun q => faceW_le_boxH ψ s c σ i ε hε q) ?_
    rw [hact, hboxp]
  have hexists_face : ∀ q : ℝ × ℝ, ∃ (i : Fin 3) (ε : ℝ), (ε = 1 ∨ ε = -1) ∧
      faceW ψ s c σ i ε q = boxH ψ s c σ q := by
    intro q
    obtain ⟨i, hi⟩ := Work.Smooth.BoxGeneric.exists_faceNorm_eq_boxNorm c σ
      (Work.BoxShrink.Pinch.par ψ q)
    have hFM : faceMaxW ψ s c σ i q = boxH ψ s c σ q := by
      rw [faceMaxW_eq_faceNorm, hi, boxH_apply]
    rcases le_total (faceW ψ s c σ i 1 q) (faceW ψ s c σ i (-1) q) with hle | hle
    · exact ⟨i, -1, Or.inr rfl, by rw [faceMaxW_apply, max_eq_right hle] at hFM; exact hFM⟩
    · exact ⟨i, 1, Or.inl rfl, by rw [faceMaxW_apply, max_eq_left hle] at hFM; exact hFM⟩
  obtain ⟨i₁, ε₁, hε₁, hact₁'⟩ := hexists_face p
  have hact₁ : faceW ψ s c σ i₁ ε₁ p = 0 := by rw [hact₁', hboxp]
  have hplanefun : planeG ψ c v u h
      = fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q) - (inner ℝ v c + u + h) := rfl
  have hnegplane : fderiv ℝ (fun q : ℝ × ℝ => -(planeG ψ c v u h q)) p
      = - fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p := by
    have h1 : fderiv ℝ (planeG ψ c v u h) p
        = fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p := by
      rw [hplanefun, fderiv_sub_const]
    change fderiv ℝ (- planeG ψ c v u h) p = _
    rw [fderiv_neg, h1]
  have hpair : ∀ t : ℝ, fderiv ℝ (boxH ψ s c σ) p
      ≠ t • fderiv ℝ (fun q : ℝ × ℝ => -(planeG ψ c v u h q)) p := by
    intro t ht
    rw [hnegplane] at ht
    rcases eq_or_ne t 0 with rfl | ht0
    · exact hMne (by simpa using ht)
    · have hL' : fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p
          = (-t⁻¹) • fderiv ℝ (boxH ψ s c σ) p := by
        have h2 : fderiv ℝ (boxH ψ s c σ) p
            = -(t • fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p) := by
          rw [ht, smul_neg]
        have hneg : (-1 : ℝ) • fderiv ℝ (fun q : ℝ × ℝ =>
            inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p
            = - fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p := by
          apply ContinuousLinearMap.ext; intro w; simp
        rw [h2, smul_neg, smul_smul]
        have h3 : (-t⁻¹) * t = -1 := by rw [neg_mul, inv_mul_cancel₀ ht0]
        rw [h3, hneg, neg_neg]
      exact hLnot (-t⁻¹) hL'
  obtain ⟨r, hrM, hrL⟩ := exists_apply_eq_pair_of_forall_ne_smul
    (L := fderiv ℝ (boxH ψ s c σ) p)
    (M := fderiv ℝ (fun q : ℝ × ℝ => -(planeG ψ c v u h q)) p)
    (by rw [hnegplane]; exact neg_ne_zero.mpr hd1) hpair 1 1
  have hrne : r ≠ 0 := by
    intro hr0
    rw [hr0, map_zero] at hrM
    exact one_ne_zero hrM.symm
  have hcd3 : ContDiff ℝ 1 (fun q : ℝ × ℝ => -(planeG ψ c v u h q)) := by
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (Work.BoxShrink.Pinch.par ψ) :=
      Work.BoxShrink.Pinch.par_contDiff ψ
    have h3 : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun q : ℝ × ℝ =>
        inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) :=
      (ContinuousLinearMap.contDiff (innerSL ℝ v)).comp h2
    have h1 : ContDiff ℝ 1 (fun q : ℝ × ℝ =>
        inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) := h3.of_le (by norm_num)
    have h4 : ContDiff ℝ 1 (planeG ψ c v u h) := h1.sub contDiff_const
    exact h4.neg
  have key : ∀ (i₂ : Fin 3) (ε₂ : ℝ), (ε₂ = 1 ∨ ε₂ = -1) → faceW ψ s c σ i₂ ε₂ p = 0 →
      (∀ (i : Fin 3) (ε : ℝ), (ε = 1 ∨ ε = -1) → faceW ψ s c σ i ε p = 0 →
        (i, ε) = (i₁, ε₁) ∨ (i, ε) = (i₂, ε₂)) →
      ∃ V : Set (ℝ × ℝ), IsOpen V ∧ p ∈ V ∧
        Work.Smooth.OneManifold.IsLocallyArcP
          (V ∩ {q : ℝ × ℝ | max (boxH ψ s c σ q) (-(planeG ψ c v u h q)) = 0}) := by
    intro i₂ ε₂ hε₂ hact₂ hother
    have hbox_eq : ∀ᶠ q in 𝓝 p, boxH ψ s c σ q
        = max (faceW ψ s c σ i₁ ε₁ q) (faceW ψ s c σ i₂ ε₂ q) := by
      have hfac : ∀ᶠ q in 𝓝 p, ∀ k : Fin 3 × Bool,
          faceW ψ s c σ k.1 (if k.2 then (1 : ℝ) else -1) q
            ≤ max (faceW ψ s c σ i₁ ε₁ q) (faceW ψ s c σ i₂ ε₂ q) := by
        rw [Filter.eventually_all]
        intro k
        by_cases hk : k.1 = i₁ ∧ (if k.2 then (1 : ℝ) else -1) = ε₁
        · obtain ⟨hk1, hk2⟩ := hk
          rw [hk1, hk2]
          exact Filter.Eventually.of_forall fun q => le_max_left _ _
        by_cases hk2 : k.1 = i₂ ∧ (if k.2 then (1 : ℝ) else -1) = ε₂
        · obtain ⟨hk1, hk2'⟩ := hk2
          rw [hk1, hk2']
          exact Filter.Eventually.of_forall fun q => le_max_right _ _
        · have hεk : (if k.2 then (1 : ℝ) else -1) = 1 ∨ (if k.2 then (1 : ℝ) else -1) = -1 := by
            by_cases h2 : k.2 <;> simp [h2]
          have hltk : faceW ψ s c σ k.1 (if k.2 then (1 : ℝ) else -1) p < 0 := by
            have h1 := faceW_le_boxH ψ s c σ k.1 (if k.2 then (1 : ℝ) else -1) hεk p
            rw [hboxp] at h1
            refine lt_of_le_of_ne h1 ?_
            intro h0
            rcases hother k.1 (if k.2 then (1 : ℝ) else -1) hεk h0 with hh | hh
            · exact hk (by simpa using Prod.ext_iff.mp hh)
            · exact hk2 (by simpa using Prod.ext_iff.mp hh)
          have hmaxp : max (faceW ψ s c σ i₁ ε₁ p) (faceW ψ s c σ i₂ ε₂ p) = 0 := by
            rw [hact₁, hact₂, max_self]
          have hltmax : faceW ψ s c σ k.1 (if k.2 then (1 : ℝ) else -1) p
              < max (faceW ψ s c σ i₁ ε₁ p) (faceW ψ s c σ i₂ ε₂ p) := by
            rw [hmaxp]; exact hltk
          have hmem : {q : ℝ × ℝ | faceW ψ s c σ k.1 (if k.2 then (1 : ℝ) else -1) q
              < max (faceW ψ s c σ i₁ ε₁ q) (faceW ψ s c σ i₂ ε₂ q)} ∈ 𝓝 p :=
            (isOpen_lt (contDiff_faceW ψ s c σ k.1 (if k.2 then (1 : ℝ) else -1)).continuous
              ((contDiff_faceW ψ s c σ i₁ ε₁).continuous.max
                (contDiff_faceW ψ s c σ i₂ ε₂).continuous)).mem_nhds hltmax
          filter_upwards [hmem] with q hq
          exact le_of_lt hq
      filter_upwards [hfac] with q hq
      refine le_antisymm ?_ (max_le (faceW_le_boxH ψ s c σ i₁ ε₁ hε₁ q)
        (faceW_le_boxH ψ s c σ i₂ ε₂ hε₂ q))
      rw [boxH_eq_max_three, faceMaxW_apply, faceMaxW_apply, faceMaxW_apply]
      exact max_le (max_le (max_le (by simpa using hq ⟨0, true⟩) (by simpa using hq ⟨0, false⟩))
        (max_le (by simpa using hq ⟨1, true⟩) (by simpa using hq ⟨1, false⟩)))
        (max_le (by simpa using hq ⟨2, true⟩) (by simpa using hq ⟨2, false⟩))
    obtain ⟨Vs, hVs_open, hpVs, hVs_eq⟩ : ∃ Vs : Set (ℝ × ℝ), IsOpen Vs ∧ p ∈ Vs ∧
        ∀ q ∈ Vs, boxH ψ s c σ q = max (faceW ψ s c σ i₁ ε₁ q) (faceW ψ s c σ i₂ ε₂ q) := by
      obtain ⟨t, ht_nhds, ht_sub⟩ := hbox_eq.exists_mem
      obtain ⟨e, he, hsub⟩ := Metric.mem_nhds_iff.mp ht_nhds
      exact ⟨Metric.ball p e, Metric.isOpen_ball, Metric.mem_ball_self he,
        fun q hq => ht_sub q (hsub hq)⟩
    have hf₁ : fderiv ℝ (faceW ψ s c σ i₁ ε₁) p = fderiv ℝ (boxH ψ s c σ) p :=
      hactive_fderiv i₁ ε₁ hε₁ hact₁
    have hf₂ : fderiv ℝ (faceW ψ s c σ i₂ ε₂) p = fderiv ℝ (boxH ψ s c σ) p :=
      hactive_fderiv i₂ ε₂ hε₂ hact₂
    obtain ⟨V, hV_open, hpV, hloc⟩ := Work.Smooth.OneManifold.isLocallyArc_max_three
      ((contDiff_faceW ψ s c σ i₁ ε₁).of_le (by norm_num))
      ((contDiff_faceW ψ s c σ i₂ ε₂).of_le (by norm_num))
      hcd3 hact₁ hact₂ (by rw [hplaneGp, neg_zero]) hrne
      (by rw [hf₁, hrM]; norm_num) (by rw [hf₂, hrM]; norm_num)
      (by rw [hrL]; norm_num)
    refine ⟨V ∩ Vs, hV_open.inter hVs_open, ⟨hpV, hpVs⟩, ?_⟩
    have hset : V ∩ Vs ∩ {q : ℝ × ℝ | max (boxH ψ s c σ q) (-(planeG ψ c v u h q)) = 0}
        = (V ∩ {q : ℝ × ℝ | max (max (faceW ψ s c σ i₁ ε₁ q) (faceW ψ s c σ i₂ ε₂ q))
            (-(planeG ψ c v u h q)) = 0}) ∩ Vs := by
      ext q
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨⟨hqV, hqVs⟩, hq0⟩
        exact ⟨⟨hqV, by rw [← hVs_eq q hqVs]; exact hq0⟩, hqVs⟩
      · rintro ⟨⟨hqV, hq0⟩, hqVs⟩
        exact ⟨⟨hqV, hqVs⟩, by rw [hVs_eq q hqVs]; exact hq0⟩
    exact Work.Smooth.OneManifold.isLocallyArc_of_eq hset.symm
      (Work.Smooth.OneManifold.isLocallyArc_inter_of_isOpen hloc hVs_open)
  by_cases hsingle : ∀ (i : Fin 3) (ε : ℝ), (ε = 1 ∨ ε = -1) → faceW ψ s c σ i ε p = 0 →
      i = i₁ ∧ ε = ε₁
  · refine key i₁ ε₁ hε₁ hact₁ ?_
    intro i ε hε hact
    exact Or.inl (Prod.ext_iff.mpr ⟨(hsingle i ε hε hact).1, (hsingle i ε hε hact).2⟩)
  · push_neg at hsingle
    obtain ⟨i₂, ε₂, hε₂, hact₂, hne₂₁⟩ := hsingle
    have hne : (i₁, ε₁) ≠ (i₂, ε₂) := by
      intro hh
      have h1 : i₁ = i₂ := by simpa using congrArg Prod.fst hh
      have h2 : ε₁ = ε₂ := by simpa using congrArg Prod.snd hh
      exact hne₂₁ h1.symm h2.symm
    refine key i₂ ε₂ hε₂ hact₂ ?_
    intro i ε hε hact
    by_contra hc
    push_neg at hc
    exact not_three_active_faces hε₁ hε₂ hε hne
      (fun hh => hc.1 hh.symm) (fun hh => hc.2 hh.symm)
      (hactive_fderiv i₁ ε₁ hε₁ hact₁) (hactive_fderiv i₂ ε₂ hε₂ hact₂)
      (hactive_fderiv i ε hε hact) hMne hLnot

end Work.Drive.Mono
