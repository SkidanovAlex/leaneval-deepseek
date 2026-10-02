import Mathlib
import Submission.Work.FatouDeg.Petal.DefsAux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouDeg.Petal

open scoped Topology
open Set Filter Metric MeasureTheory

/-- **Injectivity from a strictly signed derivative on a convex petal.**

`Pet m ρ` is convex (see `convex_Pet`), `phifun m G` is holomorphic on it, and its derivative has
strictly negative real part at every point of it.  Then `phifun m G` is injective on `Pet m ρ`.

Proof: for `z ≠ z'` in `Pet m ρ` the segment between them lies in `Pet m ρ`, and
`phifun m G z - phifun m G z' = (z - z') * ∫₀¹ deriv (phifun m G) (z' + t(z-z')) dt`
(FTC applied to `t ↦ phifun m G (z' + t(z-z'))`, using `hdiff` and that `Pet m ρ` is open).  The
integral has strictly negative real part, hence is nonzero, and `z - z' ≠ 0`. -/
theorem injOnAux (m : ℕ) (hm : 3 ≤ m) (G : Polynomial ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hdiff : DifferentiableOn ℂ (phifun m G) (Pet m ρ))
    (hsign : ∀ z ∈ Pet m ρ, (deriv (phifun m G) z).re < 0) :
    Set.InjOn (phifun m G) (Pet m ρ) := by
  intro z hz z' hz' heq
  by_contra hne
  have hsub : z - z' ≠ 0 := sub_ne_zero.mpr hne
  have hPetOpen : IsOpen (Pet m ρ) := isOpen_Pet m ρ
  have hderiv_cont : ContinuousOn (deriv (phifun m G)) (Pet m ρ) :=
    (hdiff.deriv hPetOpen).continuousOn
  set γ : ℝ → ℂ := fun t => z' + t • (z - z') with hγdef
  have hγ_eq : ∀ t : ℝ, γ t = (1 - t) • z' + t • z := by
    intro t
    simp only [hγdef, Complex.real_smul]
    push_cast
    ring
  have hγ_cont : Continuous γ := by
    simp only [hγdef]
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hγ_mem : ∀ t ∈ Icc (0:ℝ) 1, γ t ∈ Pet m ρ := by
    intro t ht
    rw [hγ_eq t]
    exact convex_Pet m ρ hz' hz (by linarith [ht.1, ht.2]) ht.1 (by ring)
  have hmaps : MapsTo γ (uIcc (0:ℝ) 1) (Pet m ρ) := by
    intro t ht
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    exact hγ_mem t ht
  have hγ1 : γ 1 = z := by
    simp only [hγdef, one_smul]
    ring
  have hγ0 : γ 0 = z' := by
    simp only [hγdef, zero_smul, add_zero]
  have hcont_derivγ : ContinuousOn (fun t : ℝ => deriv (phifun m G) (γ t))
      (uIcc (0:ℝ) 1) :=
    hderiv_cont.comp hγ_cont.continuousOn hmaps
  have hcontF' : ContinuousOn (fun t : ℝ => (z - z') • deriv (phifun m G) (γ t))
      (uIcc (0:ℝ) 1) :=
    (continuousOn_const (c := z - z')).smul hcont_derivγ
  have hintF : IntervalIntegrable (fun t : ℝ => (z - z') • deriv (phifun m G) (γ t))
      volume 0 1 := hcontF'.intervalIntegrable
  have hintg : IntervalIntegrable (fun t : ℝ => deriv (phifun m G) (γ t)) volume 0 1 :=
    hcont_derivγ.intervalIntegrable
  have hderivF : ∀ t ∈ uIcc (0:ℝ) 1,
      HasDerivAt (fun s : ℝ => phifun m G (γ s))
        ((z - z') • deriv (phifun m G) (γ t)) t := by
    intro t ht
    have htIcc : t ∈ Icc (0:ℝ) 1 := by
      rwa [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    have hmem : γ t ∈ Pet m ρ := hγ_mem t htIcc
    have hd : HasDerivAt (phifun m G) (deriv (phifun m G) (γ t)) (γ t) :=
      (hdiff.differentiableAt (hPetOpen.mem_nhds hmem)).hasDerivAt
    have hγd : HasDerivAt γ (z - z') t := by
      simp only [hγdef]
      simpa using ((hasDerivAt_id t).smul_const (z - z')).const_add z'
    exact HasDerivAt.scomp t hd hγd
  -- Fundamental theorem of calculus identity
  have hzero : ∫ t in (0:ℝ)..1, deriv (phifun m G) (γ t) = 0 := by
    have h1 : (z - z') • (∫ t in (0:ℝ)..1, deriv (phifun m G) (γ t)) = 0 := by
      rw [← intervalIntegral.integral_smul (z - z') (fun t => deriv (phifun m G) (γ t))]
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderivF hintF]
      simp only [hγ1, hγ0]
      rw [heq, sub_self]
    exact (smul_eq_zero.mp h1).resolve_left hsub
  have hre_zero : (∫ t in (0:ℝ)..1, deriv (phifun m G) (γ t)).re = 0 := by
    rw [hzero, Complex.zero_re]
  have hre_eq : (∫ t in (0:ℝ)..1, deriv (phifun m G) (γ t)).re
      = ∫ t in (0:ℝ)..1, (deriv (phifun m G) (γ t)).re := by
    rw [intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num),
      intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num)]
    have h := Complex.reCLM.integral_comp_comm
      (μ := volume.restrict (Ioc (0:ℝ) 1)) hintg.1
    simp only [Complex.reCLM_apply] at h
    exact h.symm
  have hcont_re : ContinuousOn (fun t : ℝ => (deriv (phifun m G) (γ t)).re)
      (uIcc (0:ℝ) 1) :=
    Complex.continuous_re.comp_continuousOn hcont_derivγ
  have hneg_int : IntervalIntegrable (fun t : ℝ => -((deriv (phifun m G) (γ t)).re))
      volume 0 1 := hcont_re.neg.intervalIntegrable
  have hneg_pos : ∀ t ∈ Ioo (0:ℝ) 1, 0 < -((deriv (phifun m G) (γ t)).re) := by
    intro t ht
    have htIcc : t ∈ Icc (0:ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    have := hsign (γ t) (hγ_mem t htIcc)
    linarith
  have hlt : ∫ t in (0:ℝ)..1, (deriv (phifun m G) (γ t)).re < 0 := by
    have hpos := intervalIntegral.intervalIntegral_pos_of_pos_on hneg_int hneg_pos
      (show (0:ℝ) < 1 by norm_num)
    rw [intervalIntegral.integral_neg] at hpos
    linarith
  linarith [hre_eq, hre_zero, hlt]

end Work.FatouDeg.Petal
