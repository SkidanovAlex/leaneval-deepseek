import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.StrongEps.EpsSlotLipP
import Submission.Work.FTS.StrongEps.PZeroScheme

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

theorem mixed_slice_deriv {ρ : ℝ × ℝ → ℝ} {α T ε : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g₀ : Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam} {z₁ z₂ θ₁ θ₂ C : ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε)
    (hsol : Work.FTS.StrongEps.IsEpsSolP α ρ ε T Φs E g₀ g)
    (hsm : ∀ s ∈ Set.Icc 0 T, Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Galerkin.slice g s))
    (hsmR : ∀ s ∈ Set.Icc 0 T,
      Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s))
    (hmeas : ∀ (k l : ℕ) (z θ : ℝ), (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      MeasureTheory.AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed k l
        (Work.FTS.Galerkin.slice g s) z θ) (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)))
    (hmeasR : ∀ (k l : ℕ) (z θ : ℝ), (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      MeasureTheory.AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed k l
        (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) z θ)
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)))
    (hC0 : 0 ≤ C)
    (hbdd : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (k l : ℕ), k + l ≤ 4 → ∀ q : ℝ × ℝ,
      q ∈ Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ →
        |Work.Spaces.mixed k l (Work.FTS.Galerkin.slice g s) q.1 q.2| ≤ C)
    (hbddR : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (k l : ℕ), k + l ≤ 4 → ∀ q : ℝ × ℝ,
      q ∈ Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ →
        |Work.Spaces.mixed k l (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) q.1 q.2| ≤ C)
    (hboxQ : Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ ⊆ Work.FTS.EllipticEst.Q0)
    {z θ : ℝ} (hzθ : (z, θ) ∈ Set.Ioo z₁ z₂ ×ˢ Set.Ioo θ₁ θ₂)
    {j i : ℕ} (hji : j + i ≤ 4)
    (hcontR : ContinuousOn (fun s : ℝ => Work.Spaces.mixed j i
      (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) z θ) (Set.Icc 0 T))
    {τ : ℝ} (hτ : τ ∈ Set.Ioo 0 T) :
    HasDerivWithinAt (fun s => Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g s) z θ)
      (Work.Spaces.mixed j i (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ) z θ)
      (Set.Icc 0 T) τ := by
  -- ## 0. the interior point `(z,θ)` and the fake time `τ`
  have hτT : τ ∈ Set.Icc (0 : ℝ) T := ⟨hτ.1.le, hτ.2.le⟩
  have hz1 : z₁ < z := hzθ.1.1
  have hz2 : z < z₂ := hzθ.1.2
  have hθ1 : θ₁ < θ := hzθ.2.1
  have hθ2 : θ < θ₂ := hzθ.2.2
  have hzQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    hboxQ ⟨⟨hz1.le, hz2.le⟩, ⟨hθ1.le, hθ2.le⟩⟩
  obtain ⟨hz0, hθ0, hθπ⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzQ
  have hθmem : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθπ⟩
  -- ## 1. the pointwise ODE of the scheme, at every point of the closed box
  have hderAll : ∀ p ∈ Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂, ∀ s ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt (fun u => g p.1 p.2 u)
        (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s p.1 p.2) (Set.Icc 0 T) s := by
    intro p hp s hs
    obtain ⟨hpz, hpθ0, hpθπ⟩ := Work.FTS.EllipticEst.mem_Q0.mp (hboxQ hp)
    exact hsol.2 p.1 p.2 s hpz ⟨hpθ0, hpθπ⟩ hs
  -- ## 2. interval integrability of the right-hand side, from boundedness + measurability
  have hintI : ∀ p ∈ Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂, ∀ a b : ℝ,
      a ∈ Set.Icc (0 : ℝ) T → b ∈ Set.Icc (0 : ℝ) T → a ≤ b →
      IntervalIntegrable (fun s => Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s p.1 p.2)
        volume a b := by
    intro p hp a b ha hb hab
    have hpQ : (p.1, p.2) ∈ Work.FTS.EllipticEst.Q0 := hboxQ hp
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    refine MeasureTheory.IntegrableOn.of_bound ?_ ?_ C ?_
    · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
    · simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] using
        (hmeasR 0 0 p.1 p.2 hpQ).mono_measure
          (MeasureTheory.Measure.restrict_mono (s := Set.Ioc a b) (s' := Set.Icc (0 : ℝ) T)
            (fun t ht => ⟨le_trans ha.1 ht.1.le, le_trans ht.2 hb.2⟩) le_rfl)
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s hs
      rw [Real.norm_eq_abs]
      have hb' := hbddR s ⟨le_trans ha.1 hs.1.le, le_trans hs.2 hb.2⟩ 0 0 (by omega) p hp
      simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] using hb'
  -- ## 3. the fundamental theorem of calculus along the fake time, on the whole box
  have hFTC : ∀ p ∈ Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂, ∀ a ∈ Set.Icc (0 : ℝ) T,
      ∀ b ∈ Set.Icc (0 : ℝ) T,
      g p.1 p.2 b - g p.1 p.2 a
        = ∫ s in a..b, Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s p.1 p.2 := by
    intro p hp a ha b hb
    have key : ∀ a b : ℝ, a ∈ Set.Icc (0 : ℝ) T → b ∈ Set.Icc (0 : ℝ) T → a ≤ b →
        ∫ s in a..b, Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s p.1 p.2
          = g p.1 p.2 b - g p.1 p.2 a := by
      intro a b ha hb hab
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab ?_ ?_ ?_
      · exact (HasDerivWithinAt.continuousOn (s := Set.Icc (0 : ℝ) T)
          (fun s hs => hderAll p hp s hs)).mono
          (Set.Icc_subset_Icc ha.1 hb.2)
      · intro x hx
        have hx0 : (0 : ℝ) < x := lt_of_le_of_lt ha.1 hx.1
        have hxT : x < T := lt_of_lt_of_le hx.2 hb.2
        exact (hderAll p hp x ⟨hx0.le, hxT.le⟩).hasDerivAt (Icc_mem_nhds hx0 hxT)
      · exact hintI p hp a b ha hb hab
    rcases le_total a b with hab | hba
    · exact (key a b ha hb hab).symm
    · have h2 := key b a hb ha hba
      rw [intervalIntegral.integral_symm b a]
      linarith
  -- ## 4. the mixed slot of the difference of two slices is the integral of the mixed slot
  have hFdiff : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g s) z θ
        - Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) z θ
        = ∫ σ in τ..s,
          Work.Spaces.mixed j i (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g σ) z θ := by
    intro s hs
    have hA : ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Galerkin.slice g s))
        Work.FTS.EllipticEst.Q0 :=
      (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp (hsm s hs) 4
    have hB : ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Galerkin.slice g τ))
        Work.FTS.EllipticEst.Q0 :=
      (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp (hsm τ hτT) 4
    have hsub := Work.FTS.StrongEps.mixed_sub_of_contDiffOn_four (j := j) (i := i) hji hz0 hθmem hA hB
    -- locality: replace the difference of the two slices by the interval integral
    have hloc : Work.Spaces.mixed j i (fun z θ =>
          Work.FTS.Galerkin.slice g s z θ - Work.FTS.Galerkin.slice g τ z θ) z θ
        = Work.Spaces.mixed j i (fun z θ =>
            ∫ σ in τ..s, Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g σ z θ) z θ := by
      have hEq := Work.FTS.StrongEps.mixed_congr_of_isOpen
        (V := Set.Ioo z₁ z₂ ×ˢ Set.Ioo θ₁ θ₂) (isOpen_Ioo.prod isOpen_Ioo)
        (f := fun z θ => Work.FTS.Galerkin.slice g s z θ - Work.FTS.Galerkin.slice g τ z θ)
        (g := fun z θ => ∫ σ in τ..s, Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g σ z θ)
        (fun p hp => hFTC p ⟨⟨hp.1.1.le, hp.1.2.le⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩ τ hτT s hs) j i
      simpa only [Function.uncurry] using hEq hzθ
    -- the exchange of `mixed j i` with the interval integral
    have hex : Work.Spaces.mixed j i (fun z θ =>
          ∫ σ in τ..s, Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g σ z θ) z θ
        = ∫ σ in τ..s,
          Work.Spaces.mixed j i (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g σ) z θ := by
      rcases le_total τ s with hts | hst
      · exact Work.FTS.StrongEps.mixed_intervalIntegral_eq
          (H := fun σ => Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g σ)
          (a := τ) (b := s) hτT hs hts hC0 hsmR hmeasR hbddR hboxQ hji z θ hzθ
      · have hfun : (fun z θ => ∫ σ in τ..s, Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g σ z θ)
            = fun z θ => -(∫ σ in s..τ,
                Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g σ z θ) := by
          funext z' θ'
          exact intervalIntegral.integral_symm s τ
        rw [hfun, Work.FTS.StrongEps.mixed_neg]
        rw [Work.FTS.StrongEps.mixed_intervalIntegral_eq
          (H := fun σ => Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g σ)
          (a := s) (b := τ) hs hτT hst hC0 hsmR hmeasR hbddR hboxQ hji z θ hzθ]
        rw [intervalIntegral.integral_symm s τ]
    calc Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g s) z θ
          - Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) z θ
        = Work.Spaces.mixed j i (fun z θ =>
            Work.FTS.Galerkin.slice g s z θ - Work.FTS.Galerkin.slice g τ z θ) z θ := hsub.symm
      _ = Work.Spaces.mixed j i (fun z θ =>
            ∫ σ in τ..s, Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g σ z θ) z θ := hloc
      _ = ∫ σ in τ..s,
            Work.Spaces.mixed j i (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g σ) z θ := hex
  -- ## 5. differentiate the antiderivative in the fake time
  have hmeasA : StronglyMeasurableAtFilter (fun σ : ℝ =>
      Work.Spaces.mixed j i (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g σ) z θ) (𝓝 τ) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
      (hcontR.mono Set.Ioo_subset_Icc_self) τ hτ
  have hcontAt : ContinuousAt (fun σ : ℝ =>
      Work.Spaces.mixed j i (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g σ) z θ) τ :=
    hcontR.continuousAt (Icc_mem_nhds hτ.1 hτ.2)
  have hderivA : HasDerivAt (fun u => ∫ σ in τ..u,
      Work.Spaces.mixed j i (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g σ) z θ)
      (Work.Spaces.mixed j i (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ) z θ) τ :=
    intervalIntegral.integral_hasDerivAt_right IntervalIntegrable.refl hmeasA hcontAt
  have hcongr : (fun s => Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g s) z θ) =ᶠ[𝓝 τ]
      (fun u => Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) z θ
        + ∫ σ in τ..u,
          Work.Spaces.mixed j i (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g σ) z θ) := by
    filter_upwards [isOpen_Ioo.mem_nhds hτ] with u hu
    have h := hFdiff u ⟨hu.1.le, hu.2.le⟩
    rw [← h]
    ring
  have hmain := (hderivA.const_add
    (Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) z θ)).congr_of_eventuallyEq hcongr
  exact hmain.hasDerivWithinAt

end Work.FTS.StrongEps.EpsE4Thr
