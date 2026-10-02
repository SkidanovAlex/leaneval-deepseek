import Mathlib
import Submission.Work.ELRig.exists_local_angle_at_lift
import Submission.Work.ELRig.exists_angle_flip
import Submission.Work.ELRig.CylSides
import Submission.Work.ELRig.CylLift
import Submission.Work.ELRig.Sides
import Submission.Work.ELRig.Inputs
import Submission.Work.Top.extAngle_close_of_Phi_close
import Submission.Work.Top.rayPt_injOn

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Classical Filter Set
open scoped _root_.Topology

namespace Work.ELRig

/-- Membership in an open arc of length `< 1`. -/
theorem InArc_of_mem_Ioo {a b x : ℝ} (hb : b - a < 1) (h : x ∈ Set.Ioo a b) :
    Work.EL.InArc x a b := by
  have h1 : 0 < x - a := by linarith [h.1]
  have h2 : x - a < 1 := by linarith [h.2, hb]
  have hfr1 : Int.fract (x - a) = x - a := Int.fract_eq_self.mpr ⟨le_of_lt h1, h2⟩
  have hfr2 : Int.fract (b - a) = b - a :=
    Int.fract_eq_self.mpr ⟨by linarith [h.1, h.2], hb⟩
  rw [Work.EL.InArc, hfr1, Work.EL.arcLen, hfr2]
  exact ⟨h1, by linarith [h.2]⟩

/-- Membership in the near arc `(b, a+1)` in the form `x ∈ (b-1, a)`. -/
theorem InArc_near_of_mem {a b x : ℝ} (hab : a < b) (hb1 : b < a + 1)
    (hx1 : b - 1 < x) (hx2 : x < a) : Work.EL.InArc x b (a + 1) := by
  have h1' : 0 < x - b + 1 := by linarith
  have h2' : x - b + 1 < 1 := by linarith
  have hfr : Int.fract (x - b) = x - b + 1 :=
    Int.fract_eq_iff.mpr ⟨le_of_lt h1', h2', ⟨-1, by push_cast; ring⟩⟩
  have harc : Work.EL.arcLen b (a + 1) = a + 1 - b :=
    Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  rw [Work.EL.InArc, hfr, harc]
  exact ⟨h1', by linarith⟩

/-- Smallness of the external angle of `Ψ` near the lift point. -/
theorem exists_extAngle_close_at_lift {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (L : Work.ELRig.RayCylLift d fl) {s₀ : ℝ} :
    ∃ ε > 0, ∀ z : ℂ, dist z (L.γ₁ s₀) < ε →
      fl.Ψ z ∉ Work.EL.K c ∧
      |Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) (fl.Ψ z) - Work.EL.alpha1| <
        (Work.EL.alpha2 - Work.EL.alpha1) / 2 := by
  have hα : Work.EL.alpha1 < Work.EL.alpha2 := by
    norm_num [Work.EL.alpha1, Work.EL.alpha2]
  have hηpos : 0 < (Work.EL.alpha2 - Work.EL.alpha1) / 2 := by linarith
  obtain ⟨δc, hδcpos, hδc⟩ := Work.Top.extAngle_close_of_Phi_close d.hN
    (θ := Work.EL.alpha1) (R := L.τ s₀)
    (by norm_num [Work.EL.alpha1]) (by norm_num [Work.EL.alpha1]) (L.hτ1 s₀) hηpos
  have hqK : fl.Ψ (L.γ₁ s₀) ∉ Work.EL.K c := by
    rw [L.hΨ₁ s₀]; exact Work.EL.rayPt_notMem_K d.hN (L.hτ1 s₀)
  have hPhiCont : ContinuousOn (Work.EL.dynPhi c d.φ) (Work.EL.K c)ᶜ := by
    rw [continuousOn_iff_continuous_domRestrict]
    have h : (Set.domRestrict (Work.EL.K c)ᶜ (Work.EL.dynPhi c d.φ))
        = fun z => ((d.hN.e z : Work.Top.exteriorDisc) : ℂ) := by
      funext z; exact d.hN.he z
    rw [h]
    exact continuous_subtype_val.comp d.hN.e.continuous
  have hcAt : ContinuousAt (Work.EL.dynPhi c d.φ) (fl.Ψ (L.γ₁ s₀)) :=
    hPhiCont.continuousAt ((Work.ParamRays.isClosed_filledJulia c).isOpen_compl.mem_nhds hqK)
  have hcomp : ContinuousAt (fun z : ℂ => Work.EL.dynPhi c d.φ (fl.Ψ z)) (L.γ₁ s₀) :=
    hcAt.comp fl.Ψ_diff.continuous.continuousAt
  have hval : Work.EL.dynPhi c d.φ (fl.Ψ (L.γ₁ s₀))
      = Work.Top.NakaneData.rayPoint Work.EL.alpha1 (L.τ s₀) := by
    rw [L.hΨ₁ s₀]; exact Work.Top.NakaneData.Phi_rayPt d.hN (L.hτ1 s₀)
  obtain ⟨δs, hδspos, hδs⟩ := Metric.continuousAt_iff.mp hcomp δc hδcpos
  have hKopen : IsOpen (Work.EL.K c)ᶜ := (Work.ParamRays.isClosed_filledJulia c).isOpen_compl
  have hΨc : ContinuousAt fl.Ψ (L.γ₁ s₀) := fl.Ψ_diff.continuous.continuousAt
  have hpre : fl.Ψ ⁻¹' (Work.EL.K c)ᶜ ∈ 𝓝 (L.γ₁ s₀) :=
    hΨc.preimage_mem_nhds (hKopen.mem_nhds hqK)
  obtain ⟨δk, hδkpos, hδksub⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨min δs δk, lt_min hδspos hδkpos, fun z hz => ?_⟩
  have hzs : dist z (L.γ₁ s₀) < δs := lt_of_lt_of_le hz (min_le_left _ _)
  have hzk : dist z (L.γ₁ s₀) < δk := lt_of_lt_of_le hz (min_le_right _ _)
  have hzK : fl.Ψ z ∉ Work.EL.K c := hδksub (by rw [Metric.mem_ball]; exact hzk)
  refine ⟨hzK, ?_⟩
  have h1 := hδs (x := z) hzs
  rw [hval, dist_eq_norm] at h1
  exact hδc (fl.Ψ z) hzK h1

theorem exists_side_flip (hJ : Work.Top.JordanForm) {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (P : Work.EL.CoPair d.hN) (hPa : P.a = Work.EL.alpha1) (hPb : P.b = Work.EL.alpha2)
    (hPy : P.y = d.z₁) (hside : Work.EL.PairSides d.hN P)
    (L : Work.ELRig.RayCylLift d fl) {x₀ : ℝ} (hx : x₀ < -L.R) {s₀ : ℝ} (hs : (L.γ₁ s₀).re = x₀)
    (hcross : deriv (fun t : ℝ => (L.γ₁ t).re) s₀ ≠ 0) :
    ∃ ε > 0, ∀ δ : ℝ, 0 < δ → δ < ε →
      ((x₀ : ℂ) + ((L.γ₁ s₀).im + δ) * Complex.I) ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ →
      ((x₀ : ℂ) + ((L.γ₁ s₀).im - δ) * Complex.I) ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ →
      ((fl.Ψ ((x₀ : ℂ) + ((L.γ₁ s₀).im + δ) * Complex.I) ∈ Work.EL.pairSide P ∧
        fl.Ψ ((x₀ : ℂ) + ((L.γ₁ s₀).im - δ) * Complex.I) ∈ Work.EL.pairSideNear P) ∨
       (fl.Ψ ((x₀ : ℂ) + ((L.γ₁ s₀).im + δ) * Complex.I) ∈ Work.EL.pairSideNear P ∧
        fl.Ψ ((x₀ : ℂ) + ((L.γ₁ s₀).im - δ) * Complex.I) ∈ Work.EL.pairSide P)) := by
  have hx' : (L.γ₁ s₀).re < -L.R := hs ▸ hx
  obtain ⟨D, hDopen, hpD, hDsub, hDK, hDangle, hDfar, hDnear⟩ :=
    exists_local_angle_at_lift d fl L P hPa hPb hPy hside hx'
  obtain ⟨εf, hεfpos, hflip'⟩ := exists_angle_flip hJ d fl L hx hs hcross
  obtain ⟨εs, hεspos, hεs⟩ := exists_extAngle_close_at_lift d fl L (s₀ := s₀)
  have hα : Work.EL.alpha1 < Work.EL.alpha2 := by norm_num [Work.EL.alpha1, Work.EL.alpha2]
  have hα1 : Work.EL.alpha2 < Work.EL.alpha1 + 1 := by norm_num [Work.EL.alpha1, Work.EL.alpha2]
  have hα2 : Work.EL.alpha2 - Work.EL.alpha1 < 1 := by linarith
  obtain ⟨εD, hεDpos, hεDsub⟩ := Metric.isOpen_iff.mp hDopen (L.γ₁ s₀) hpD
  refine ⟨min (min εf (min εs εD)) 1,
    lt_min (lt_min hεfpos (lt_min hεspos hεDpos)) one_pos,
    fun δ hδpos hδε hzp hzm => ?_⟩
  have hδε' : δ < min εf (min εs εD) := lt_of_lt_of_le hδε (min_le_left _ _)
  have hδf : δ < εf := lt_of_lt_of_le hδε' (min_le_left _ _)
  have hδs' : δ < εs := lt_of_lt_of_le hδε'
    (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδD : δ < εD := lt_of_lt_of_le hδε'
    (le_trans (min_le_right _ _) (min_le_right _ _))
  set zp : ℂ := (x₀ : ℂ) + ((L.γ₁ s₀).im + δ) * Complex.I with hzpdef
  set zm : ℂ := (x₀ : ℂ) + ((L.γ₁ s₀).im - δ) * Complex.I with hzmdef
  have hzp_sub : zp - L.γ₁ s₀ = (δ : ℂ) * Complex.I := by
    rw [hzpdef]
    apply Complex.ext <;> simp [Complex.add_re, Complex.mul_re, Complex.mul_im, hs]
  have hzm_sub : zm - L.γ₁ s₀ = -((δ : ℂ) * Complex.I) := by
    rw [hzmdef]
    apply Complex.ext <;> simp [Complex.add_re, Complex.mul_re, Complex.mul_im, hs]
  have hdistzp : dist zp (L.γ₁ s₀) = δ := by
    rw [dist_eq_norm, hzp_sub]; simp [Complex.norm_I, abs_of_pos hδpos]
  have hdistzm : dist zm (L.γ₁ s₀) = δ := by
    rw [dist_eq_norm, hzm_sub]; simp [Complex.norm_I, abs_of_pos hδpos]
  have hzpD : zp ∈ D := hεDsub (by rw [Metric.mem_ball, hdistzp]; exact hδD)
  have hzmD : zm ∈ D := hεDsub (by rw [Metric.mem_ball, hdistzm]; exact hδD)
  have hsmallP : |Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) (fl.Ψ zp)
      - Work.EL.alpha1| < (Work.EL.alpha2 - Work.EL.alpha1) / 2 :=
    (hεs zp (by rw [hdistzp]; exact hδs')).2
  have hsmallM : |Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) (fl.Ψ zm)
      - Work.EL.alpha1| < (Work.EL.alpha2 - Work.EL.alpha1) / 2 :=
    (hεs zm (by rw [hdistzm]; exact hδs')).2
  have hP2 : Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) (fl.Ψ zp) - Work.EL.alpha1
      < (Work.EL.alpha2 - Work.EL.alpha1) / 2 := (abs_lt.mp hsmallP).2
  have hM2 : Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) (fl.Ψ zm) - Work.EL.alpha1
      < (Work.EL.alpha2 - Work.EL.alpha1) / 2 := (abs_lt.mp hsmallM).2
  have hnearP : Work.EL.alpha2 - 1 <
      Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) (fl.Ψ zp) := by
    have h0 := (Work.Top.NakaneData.extAngle_mem_Ico (Work.EL.dynPhi c d.φ) (fl.Ψ zp)).1
    have h2 : Work.EL.alpha2 - 1 < 0 := by norm_num [Work.EL.alpha2]
    linarith
  have hnearM : Work.EL.alpha2 - 1 <
      Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) (fl.Ψ zm) := by
    have h0 := (Work.Top.NakaneData.extAngle_mem_Ico (Work.EL.dynPhi c d.φ) (fl.Ψ zm)).1
    have h2 : Work.EL.alpha2 - 1 < 0 := by norm_num [Work.EL.alpha2]
    linarith
  have hfl := hflip' δ hδpos hδf (by rw [← hzpdef]; exact hzp) (by rw [← hzmdef]; exact hzm)
  rw [← hzpdef, ← hzmdef] at hfl
  rcases (mul_neg_iff.mp hfl) with ⟨hA, hB⟩ | ⟨hC, hD⟩
  · -- θ(zm) < α₁ < θ(zp)
    left
    refine ⟨?_, ?_⟩
    · apply hDfar zp hzpD
      rw [hPa, hPb]
      exact InArc_of_mem_Ioo hα2 ⟨by linarith, by linarith⟩
    · apply hDnear zm hzmD
      rw [hPb, hPa]
      exact InArc_near_of_mem hα hα1 hnearM (by linarith)
  · -- θ(zp) < α₁ < θ(zm)
    right
    refine ⟨?_, ?_⟩
    · apply hDnear zp hzpD
      rw [hPb, hPa]
      exact InArc_near_of_mem hα hα1 hnearP (by linarith)
    · apply hDfar zm hzmD
      rw [hPa, hPb]
      exact InArc_of_mem_Ioo hα2 ⟨by linarith, by linarith⟩

end Work.ELRig
