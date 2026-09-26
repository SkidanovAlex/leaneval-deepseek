/-
# Agreement of the CKMRV layer with the naive contour integral on the funnel

This file proves `Work.Asymptotics.FunnelAsm.agreement`: for `τ` in the funnel and `r ≠ 0` in the
convergence region `d = 8 ∨ 2 < r²`, at which the contour integrand is integrable, the paper's
layer `paperLayer (Gcusp ℓ d)` equals the naive contour integral `kernelTransform (Kfun ℓ d) τ r`.

The proof uses the decomposition `decomp` (`paperLayer = PSum`, proved in
`Submission/Work/Asymptotics/FunnelAsm/decomp.lean`) together with the telescoping of
`∫_0^∞ = ∫_0^1 + ∫_1^∞` and of `∫_1^∞` at `Im τ ∓ 1`.
-/
import Mathlib
import Submission.Work.Asymptotics.FunnelAsm.funnelDefs
import Submission.Work.Asymptotics.paperLayer_agreement
import Submission.Work.Asymptotics.FunnelAsm.decomp

namespace Work.Asymptotics.FunnelAsm

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology

noncomputable section

theorem agreement (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∀ (τ : UpperHalfPlane) (r : ℝ), Funnel τ → r ≠ 0 → (d = 8 ∨ 2 < r ^ 2) →
      IntegrableOn (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0) →
      paperLayer (Gcusp ℓ d) ℓ d τ r = Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ r := by
  intro τ r hτ hr hreg hInt
  have hY1 : (1 : ℝ) ≤ τ.im - 1 := by have := hτ.2; linarith
  set κ : ℝ → ℂ := fun t => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
      * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) with hκ
  set α : ℝ → ℂ := fun t => Aexp (Gcusp ℓ d) τ t
      * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) with hα
  have hκ0 : IntegrableOn κ (Set.Ioi 0) := hInt
  have hκ1 : IntegrableOn κ (Set.Ioc 0 1) :=
    hκ0.mono_set (Set.Ioc_subset_Ioi_self)
  have hκI1 : IntegrableOn κ (Set.Ioi 1) :=
    hκ0.mono_set (Set.Ioi_subset_Ioi zero_le_one)
  have hκs1 : IntegrableOn κ (Set.Ioc 1 (τ.im - 1)) :=
    hκI1.mono_set (fun t ht => ht.1)
  have hκs2 : IntegrableOn κ (Set.Ioc (τ.im - 1) (τ.im + 1)) :=
    hκI1.mono_set (fun t ht => lt_of_le_of_lt hY1 ht.1)
  have hκs3 : IntegrableOn κ (Set.Ioi (τ.im + 1)) :=
    hκI1.mono_set (Set.Ioi_subset_Ioi (by linarith : (1:ℝ) ≤ τ.im + 1))
  have hα3 : IntegrableOn α (Set.Ioi (τ.im + 1)) := by
    rw [hα]
    exact integrableOn_A_tail ℓ d hd hτ hr hreg
  -- the first split `(0,∞) = (0,1] ∪ (1,∞)`
  have hset0 : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 := by
    ext t
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (⟨h1, h2⟩ | h3)
      · exact h1
      · linarith
    · intro h
      by_cases h2 : t ≤ 1
      · exact Or.inl ⟨h, h2⟩
      · exact Or.inr (lt_of_not_ge h2)
  have hd0 : Disjoint (Set.Ioc (0 : ℝ) 1) (Set.Ioi 1) :=
    Set.disjoint_left.mpr (fun x hx1 hx2 => absurd hx1.2 (not_le.mpr hx2))
  have hsplit0 : ∫ t in Set.Ioi 0, κ t = (∫ t in Set.Ioc 0 1, κ t) + ∫ t in Set.Ioi 1, κ t := by
    rw [← hset0]
    exact MeasureTheory.setIntegral_union hd0 measurableSet_Ioi hκ1 hκI1
  -- the second split of `(1,∞)` at `Im τ ∓ 1`
  have hset : Set.Ioc 1 (τ.im - 1) ∪ Set.Ioc (τ.im - 1) (τ.im + 1) ∪ Set.Ioi (τ.im + 1)
      = Set.Ioi (1 : ℝ) := by
    ext t
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | h3)
      · exact h1
      · linarith
      · linarith
    · intro h
      rcases lt_trichotomy t (τ.im - 1) with hlt | heq | hgt
      · exact Or.inl (Or.inl ⟨h, le_of_lt hlt⟩)
      · exact Or.inl (Or.inl ⟨h, le_of_eq heq⟩)
      · rcases lt_trichotomy t (τ.im + 1) with hlt2 | heq2 | hgt2
        · exact Or.inl (Or.inr ⟨hgt, le_of_lt hlt2⟩)
        · exact Or.inl (Or.inr ⟨hgt, le_of_eq heq2⟩)
        · exact Or.inr hgt2
  have hd12 : Disjoint (Set.Ioc (1:ℝ) (τ.im - 1)) (Set.Ioc (τ.im - 1) (τ.im + 1)) :=
    Set.disjoint_left.mpr (fun x hx1 hx2 => absurd hx1.2 (not_le.mpr hx2.1))
  have hd3 : Disjoint (Set.Ioc (1:ℝ) (τ.im - 1) ∪ Set.Ioc (τ.im - 1) (τ.im + 1))
      (Set.Ioi (τ.im + 1)) :=
    Set.disjoint_left.mpr (fun x hx1 hx2 => by
      have hx2' : τ.im + 1 < x := hx2
      rcases hx1 with hx | hx
      · exact absurd hx.2 (not_le.mpr (lt_trans (by linarith : τ.im - 1 < τ.im + 1) hx2'))
      · exact absurd hx.2 (not_le.mpr hx2'))
  have hsplit1 : ∫ t in Set.Ioi 1, κ t
      = (∫ t in Set.Ioc 1 (τ.im - 1), κ t) + (∫ t in Set.Ioc (τ.im - 1) (τ.im + 1), κ t)
        + ∫ t in Set.Ioi (τ.im + 1), κ t := by
    rw [← hset]
    have hA : ∫ t in Set.Ioc 1 (τ.im - 1) ∪ Set.Ioc (τ.im - 1) (τ.im + 1), κ t
        = (∫ t in Set.Ioc 1 (τ.im - 1), κ t) + ∫ t in Set.Ioc (τ.im - 1) (τ.im + 1), κ t :=
      MeasureTheory.setIntegral_union hd12 measurableSet_Ioc hκs1 hκs2
    have hB : ∫ t in (Set.Ioc 1 (τ.im - 1) ∪ Set.Ioc (τ.im - 1) (τ.im + 1))
          ∪ Set.Ioi (τ.im + 1), κ t
        = (∫ t in Set.Ioc 1 (τ.im - 1) ∪ Set.Ioc (τ.im - 1) (τ.im + 1), κ t)
          + ∫ t in Set.Ioi (τ.im + 1), κ t :=
      MeasureTheory.setIntegral_union hd3 measurableSet_Ioi (hκs1.union hκs2) hκs3
    rw [hB, hA]
  -- the tail identity
  have hsub3 : ∫ t in Set.Ioi (τ.im + 1), κ t
      = (∫ t in Set.Ioi (τ.im + 1), (κ t - α t)) + ∫ t in Set.Ioi (τ.im + 1), α t := by
    have h := integral_sub hκs3 hα3
    rw [h]
    ring
  -- the layer pieces
  have hpre : preT ℓ d τ (r ^ 2) = ∫ t in Set.Ioc 1 (τ.im - 1), κ t := by
    rw [preT, intervalIntegral.integral_of_le hY1]
    exact setIntegral_congr_fun measurableSet_Ioc (fun t _ => by
      show Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t * wgt (r ^ 2) t = κ t
      rw [hκ, wgt_sq])
  have hspike : spikeT ℓ d τ (r ^ 2) = ∫ t in Set.Ioc (τ.im - 1) (τ.im + 1), κ t := by
    rw [spikeT, intervalIntegral.integral_of_le (by linarith : τ.im - 1 ≤ τ.im + 1)]
    exact setIntegral_congr_fun measurableSet_Ioc (fun t _ => by
      show Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t * wgt (r ^ 2) t = κ t
      rw [hκ, wgt_sq])
  have htail : tailT ℓ d τ (r ^ 2) = ∫ t in Set.Ioi (τ.im + 1), (κ t - α t) := by
    rw [tailT]
    exact setIntegral_congr_fun measurableSet_Ioi (fun t _ => by
      show (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t)
        * wgt (r ^ 2) t = κ t - α t
      rw [wgt_sq, show (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
          - Aexp (Gcusp ℓ d) τ t) * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) = κ t - α t
        from by rw [hκ, hα]; ring])
  have hhight : highTailClosed ℓ d τ r
      = sinSq r * ∫ t in Set.Ioi (τ.im + 1), α t :=
    highTailClosed_eq_integral ℓ d hd hτ hr hreg
  have hlow : layerLow ℓ d τ r = sinSq r * ∫ t in Set.Ioc 0 1, κ t := by
    rw [layerLow, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  have hpaper := decomp ℓ d hd τ r hτ hr hreg
  have hkt : Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ r
      = sinSq r * ∫ t in Set.Ioi 0, κ t := by
    rw [Work.Kernels.kernelTransform, sinSq]
  rw [hkt, hpaper]
  simp only [PSum]
  rw [hsplit0, hsplit1, hpre, hspike, htail, hsub3, hhight, hlow]
  ring

end

end Work.Asymptotics.FunnelAsm
