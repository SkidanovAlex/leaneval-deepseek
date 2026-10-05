import Mathlib
import Submission.Work.RPB.B5.LagData
import Submission.Work.RPB.B5.Defs
import Submission.Work.RPB.B5.collar_region_lag
import Submission.Work.RPB.B5.chart_region_lag
import Submission.Work.RPB.B5.lagPt_contDiff_one
import Submission.Work.RPV.tau_symplectic

/-!
# B5: the assembled family `ℓ = lagPt W Γc Ac rho` is Lagrangian (`Work.RPB.B5.lagData_lag_v2`)

This is the `IsLevelData`-free version of `Work.RPB.B5.lagData_lag`: the data structure
`Work.RPB.B5.LagData CI a` no longer carries a level datum (`Work.RPB.B3.levelData_coversFalse`
shows `Work.RPB.IsLevelData` is unsatisfiable for some `CurveIsotopy`s), so the `lag` field of
the assembled `LagFamily` has to be proved from the chord data alone.  The three ingredients are

* `Work.RPB.B5.collar_region_lag` — the collar region `x < -√2`;
* `Work.RPB.B5.chart_region_lag` — the chart region `-√2 < x < 0`;
* `Work.RPB.B5.lagPt_contDiff_one` — `C¹`-smoothness of `(x,t) ↦ lagPt …τ x t`.

The right half `x > 0` is `tau π` of the reflected left half, so it is handled by the chain rule
together with `Work.RPV.symp_tauLinear`.  The three exceptional lines `x = ±√2, 0` (and, by
reflection, `x = √2`) follow from continuity of the closed pairing `Ω`.
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff

set_option autoImplicit false

noncomputable section

open Filter
open scoped Topology

namespace Work.RPB.B5

/-! ## Unfolding `lagPt` and `basePt` -/

private theorem lagPt_of_nonpos (W : ℝ → ℝ → ℝ → Work.RPV.PS) (Γc : ℝ → ℝ → ℝ → ℂ)
    (Ac : ℝ → ℝ → ℝ → ℝ) (rho : ℝ → ℝ → ℝ → ℝ) {τ x t : ℝ} (hx : x ≤ 0) :
    lagPt W Γc Ac rho τ x t = basePt W Γc Ac rho τ x t := by
  rw [lagPt, if_pos hx]

private theorem lagPt_of_pos (W : ℝ → ℝ → ℝ → Work.RPV.PS) (Γc : ℝ → ℝ → ℝ → ℂ)
    (Ac : ℝ → ℝ → ℝ → ℝ) (rho : ℝ → ℝ → ℝ → ℝ) {τ x t : ℝ} (hx : 0 < x) :
    lagPt W Γc Ac rho τ x t
      = Work.RPV.tau Real.pi (basePt W Γc Ac rho τ (-x) (t - Real.pi)) := by
  rw [lagPt, if_neg (not_le.mpr hx)]

private theorem basePt_of_le (W : ℝ → ℝ → ℝ → Work.RPV.PS) (Γc : ℝ → ℝ → ℝ → ℂ)
    (Ac : ℝ → ℝ → ℝ → ℝ) (rho : ℝ → ℝ → ℝ → ℝ) {τ x t : ℝ}
    (hx : x ≤ -Real.sqrt 2) :
    basePt W Γc Ac rho τ x t = collarPt Γc Ac τ (sig x) t := by
  rw [basePt, if_pos hx]

private theorem basePt_of_gt (W : ℝ → ℝ → ℝ → Work.RPV.PS) (Γc : ℝ → ℝ → ℝ → ℂ)
    (Ac : ℝ → ℝ → ℝ → ℝ) (rho : ℝ → ℝ → ℝ → ℝ) {τ x t : ℝ}
    (hx : -Real.sqrt 2 < x) :
    basePt W Γc Ac rho τ x t = W τ t (rho τ x t) := by
  rw [basePt, if_neg (not_le.mpr hx)]

/-! ## The `τ_π`-reflection of the right half -/

private theorem symp_neg_left (A B : Work.RPV.PS) :
    Work.RPV.symp (-A) B = - Work.RPV.symp A B := by
  have := Work.RPV.symp_smul_left (-1) A B
  simpa using this

/-- If `G` is `C¹` at `(-x, t-π)` and the left-half pairing at `(-x, t-π)` vanishes, then the
right-half point is Lagrangian at `(x,t)`.  This is the chain rule for the linear part
`tauLinear π` of `tau π` (`Work.RPV.symp_tauLinear`), together with the fact that reflecting the
first variable (`y ↦ -y`) only changes the sign. -/
private theorem symp_tau_reflect (G : ℝ × ℝ → Work.RPV.PS) (x t : ℝ)
    (hG : ContDiffAt ℝ 1 G (-x, t - Real.pi))
    (h : Work.RPV.symp (deriv (fun y => G (y, t - Real.pi)) (-x))
          (deriv (fun s => G (-x, s)) (t - Real.pi)) = 0) :
    Work.RPV.symp (deriv (fun y => Work.RPV.tau Real.pi (G (-y, t - Real.pi))) x)
        (deriv (fun s => Work.RPV.tau Real.pi (G (-x, s - Real.pi))) t) = 0 := by
  set L : ℝ × ℝ →L[ℝ] Work.RPV.PS := fderiv ℝ G (-x, t - Real.pi) with hL
  have hF : HasFDerivAt G L (-x, t - Real.pi) := by
    rw [hL]
    exact (hG.differentiableAt (by simp)).hasFDerivAt
  have hτF : HasFDerivAt (fun z : Work.RPV.PS => Work.RPV.tau Real.pi z)
      (Work.RPV.tauLinear Real.pi) (G (-x, t - Real.pi)) := by
    have h1 : HasFDerivAt
        (fun z : Work.RPV.PS => Work.RPV.tauLinear Real.pi z + (((0 : ℝ), Real.pi), (0, 0)))
        (Work.RPV.tauLinear Real.pi) (G (-x, t - Real.pi)) :=
      (Work.RPV.tauLinear Real.pi).hasFDerivAt.add_const _
    rw [show (fun z : Work.RPV.PS => Work.RPV.tau Real.pi z)
        = fun z => Work.RPV.tauLinear Real.pi z + (((0 : ℝ), Real.pi), (0, 0)) from by
          funext z; exact Work.RPV.tau_eq_linear_add Real.pi z]
    exact h1
  have hφx : HasDerivAt (fun y : ℝ => ((-y, t - Real.pi) : ℝ × ℝ)) ((-1 : ℝ), (0 : ℝ)) x := by
    have h1 : HasDerivAt (fun y : ℝ => -y) (-1) x := hasDerivAt_neg x
    have h2 : HasDerivAt (fun _ : ℝ => t - Real.pi) (0 : ℝ) x := hasDerivAt_const x _
    simpa using h1.prodMk h2
  have hGx : HasDerivAt (fun y : ℝ => G (-y, t - Real.pi)) (L ((-1 : ℝ), (0 : ℝ))) x := by
    simpa only [Function.comp_def] using hF.comp_hasDerivAt x hφx
  have hcomp1 : HasDerivAt (fun y : ℝ => Work.RPV.tau Real.pi (G (-y, t - Real.pi)))
      (Work.RPV.tauLinear Real.pi (L ((-1 : ℝ), (0 : ℝ)))) x := by
    simpa only [Function.comp_def] using hτF.comp_hasDerivAt x hGx
  have hφt : HasDerivAt (fun s : ℝ => ((-x, s - Real.pi) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) t := by
    have h1 : HasDerivAt (fun _ : ℝ => -x) (0 : ℝ) t := hasDerivAt_const t _
    have h2 : HasDerivAt (fun s : ℝ => s - Real.pi) (1 : ℝ) t := (hasDerivAt_id t).sub_const _
    simpa using h1.prodMk h2
  have hGt : HasDerivAt (fun s : ℝ => G (-x, s - Real.pi)) (L ((0 : ℝ), (1 : ℝ))) t := by
    simpa only [Function.comp_def] using hF.comp_hasDerivAt t hφt
  have hcomp2 : HasDerivAt (fun s : ℝ => Work.RPV.tau Real.pi (G (-x, s - Real.pi)))
      (Work.RPV.tauLinear Real.pi (L ((0 : ℝ), (1 : ℝ)))) t := by
    simpa only [Function.comp_def] using hτF.comp_hasDerivAt t hGt
  rw [hcomp1.deriv, hcomp2.deriv]
  have hL1 : L ((-1 : ℝ), (0 : ℝ)) = - L ((1 : ℝ), (0 : ℝ)) := by
    have : ((-1 : ℝ), (0 : ℝ)) = - ((1 : ℝ), (0 : ℝ)) := by simp
    rw [this, map_neg]
  have hd1 : L ((1 : ℝ), (0 : ℝ)) = deriv (fun y => G (y, t - Real.pi)) (-x) := by
    have hφ : HasDerivAt (fun y : ℝ => ((y, t - Real.pi) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) (-x) := by
      have h1 : HasDerivAt (fun y : ℝ => y) (1 : ℝ) (-x) := hasDerivAt_id (-x)
      have h2 : HasDerivAt (fun _ : ℝ => t - Real.pi) (0 : ℝ) (-x) := hasDerivAt_const _ _
      simpa using h1.prodMk h2
    rw [← (hF.comp_hasDerivAt (-x) hφ).deriv]
    rfl
  have hd2 : L ((0 : ℝ), (1 : ℝ)) = deriv (fun s => G (-x, s)) (t - Real.pi) := by
    have hφ : HasDerivAt (fun s : ℝ => ((-x, s) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) (t - Real.pi) := by
      have h1 : HasDerivAt (fun _ : ℝ => -x) (0 : ℝ) (t - Real.pi) := hasDerivAt_const _ _
      have h2 : HasDerivAt (fun s : ℝ => s) (1 : ℝ) (t - Real.pi) := hasDerivAt_id _
      simpa using h1.prodMk h2
    rw [← (hF.comp_hasDerivAt (t - Real.pi) hφ).deriv]
    rfl
  rw [hL1, hd1, hd2, Work.RPV.symp_tauLinear Real.pi, symp_neg_left, h, neg_zero]

theorem lagData_lag_v2 (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) (D : Work.RPB.B5.LagData CI a) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ x t,
      Work.RPV.symp (deriv (fun y => Work.RPB.B5.lagPt D.W D.Γc D.Ac D.rho τ y t) x)
        (deriv (fun s => Work.RPB.B5.lagPt D.W D.Γc D.Ac D.rho τ x s) t) = 0 := by
  intro τ hτ x t
  set F : ℝ × ℝ → Work.RPV.PS :=
    fun z => Work.RPB.B5.lagPt D.W D.Γc D.Ac D.rho τ z.1 z.2 with hF
  set Ω : ℝ × ℝ → ℝ := fun p => Work.RPV.symp (deriv (fun y => F (y, p.2)) p.1)
      (deriv (fun s => F (p.1, s)) p.2) with hΩ
  have hFcd : ContDiff ℝ 1 F := lagPt_contDiff_one CI a ha D τ hτ
  -- the two partial derivatives, as `fderiv` evaluations
  have hAeq : (fun p : ℝ × ℝ => deriv (fun y => F (y, p.2)) p.1)
      = fun p => (fderiv ℝ F p) ((1 : ℝ), (0 : ℝ)) := by
    funext p
    show (fderiv ℝ (fun y : ℝ => F (y, p.2)) p.1) 1 = (fderiv ℝ F p) ((1 : ℝ), (0 : ℝ))
    have h1 : HasFDerivAt (fun y : ℝ => ((y, p.2) : ℝ × ℝ)) (ContinuousLinearMap.inl ℝ ℝ ℝ) p.1 :=
      hasFDerivAt_prodMk_left p.1 p.2
    have h2 : HasFDerivAt F (fderiv ℝ F p) p :=
      (hFcd.contDiffAt.differentiableAt (by norm_num)).hasFDerivAt
    have h3 : HasFDerivAt (fun y : ℝ => F (y, p.2))
        ((fderiv ℝ F p) ∘SL (ContinuousLinearMap.inl ℝ ℝ ℝ)) p.1 := by
      simpa only [Function.comp_def] using h2.comp p.1 h1
    rw [h3.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
  have hBeq : (fun p : ℝ × ℝ => deriv (fun s => F (p.1, s)) p.2)
      = fun p => (fderiv ℝ F p) ((0 : ℝ), (1 : ℝ)) := by
    funext p
    show (fderiv ℝ (fun s : ℝ => F (p.1, s)) p.2) 1 = (fderiv ℝ F p) ((0 : ℝ), (1 : ℝ))
    have h1 : HasFDerivAt (fun s : ℝ => ((p.1, s) : ℝ × ℝ)) (ContinuousLinearMap.inr ℝ ℝ ℝ) p.2 :=
      hasFDerivAt_prodMk_right p.1 p.2
    have h2 : HasFDerivAt F (fderiv ℝ F p) p :=
      (hFcd.contDiffAt.differentiableAt (by norm_num)).hasFDerivAt
    have h3 : HasFDerivAt (fun s : ℝ => F (p.1, s))
        ((fderiv ℝ F p) ∘SL (ContinuousLinearMap.inr ℝ ℝ ℝ)) p.2 := by
      simpa only [Function.comp_def] using h2.comp p.2 h1
    rw [h3.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
  have hfd : Continuous (fun q : (ℝ × ℝ) × (ℝ × ℝ) => (fderiv ℝ F q.1) q.2) :=
    hFcd.continuous_fderiv_apply (by norm_num)
  have hAcont : Continuous (fun p : ℝ × ℝ => deriv (fun y => F (y, p.2)) p.1) := by
    rw [hAeq]
    exact hfd.comp (continuous_id.prodMk continuous_const)
  have hBcont : Continuous (fun p : ℝ × ℝ => deriv (fun s => F (p.1, s)) p.2) := by
    rw [hBeq]
    exact hfd.comp (continuous_id.prodMk continuous_const)
  have hΩcont : Continuous Ω := by
    rw [hΩ]
    have hsy : Continuous (fun q : Work.RPV.PS × Work.RPV.PS => Work.RPV.symp q.1 q.2) := by
      simp only [Work.RPV.symp]; fun_prop
    exact hsy.comp (hAcont.prodMk hBcont)
  have hcont_t : Continuous (fun y : ℝ => Ω (y, t)) :=
    hΩcont.comp (continuous_id.prodMk continuous_const)
  -- a left limit of zeros forces the value to be zero
  have key : ∀ y₀ : ℝ, (∀ᶠ y in 𝓝[<] y₀, Ω (y, t) = 0) → Ω (y₀, t) = 0 := by
    intro y₀ hz
    have h1 : Filter.Tendsto (fun y : ℝ => Ω (y, t)) (𝓝[<] y₀) (𝓝 (Ω (y₀, t))) :=
      (hcont_t.continuousAt).continuousWithinAt
    have hzeq : (fun y : ℝ => Ω (y, t)) =ᶠ[𝓝[<] y₀] (fun _ => (0 : ℝ)) := hz
    have h2 : Filter.Tendsto (fun y : ℝ => Ω (y, t)) (𝓝[<] y₀) (𝓝 (0 : ℝ)) :=
      Filter.Tendsto.congr' hzeq.symm tendsto_const_nhds
    exact tendsto_nhds_unique h1 h2
  -- the three open-region identities
  have hsq2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num)
  have hcollar : ∀ y : ℝ, y < -Real.sqrt 2 → Ω (y, t) = 0 := by
    intro y hy
    simp only [hΩ, hF]
    exact collar_region_lag CI a ha D τ hτ y hy t
  have hchart : ∀ y : ℝ, -Real.sqrt 2 < y → y < 0 → Ω (y, t) = 0 := by
    intro y hy1 hy2
    simp only [hΩ, hF]
    exact chart_region_lag CI a ha D τ hτ y ⟨hy1, hy2⟩ t
  -- the right half is the `τ_π`-reflection of the left half
  have htau1 : ∀ y : ℝ, 0 < y → y < Real.sqrt 2 → Ω (y, t) = 0 := by
    intro y hy0 hy2
    have hlt : -Real.sqrt 2 < -y := by linarith
    have hleft : Work.RPV.symp (deriv (fun z => F (z, t - Real.pi)) (-y))
        (deriv (fun s => F (-y, s)) (t - Real.pi)) = 0 := by
      have := chart_region_lag CI a ha D τ hτ (-y) ⟨hlt, by linarith⟩ (t - Real.pi)
      simpa only [hF] using this
    have hG : ContDiffAt ℝ 1 F (-y, t - Real.pi) := hFcd.contDiffAt
    have hkey := symp_tau_reflect F y t hG hleft
    have e1 : (fun y' : ℝ => F (y', t)) =ᶠ[𝓝 y]
        (fun y' => Work.RPV.tau Real.pi (F (-y', t - Real.pi))) := by
      filter_upwards [isOpen_Ioi.mem_nhds hy0] with y' hy'
      have hy'0 : (0 : ℝ) < y' := Set.mem_Ioi.mp hy'
      simp only [hF]
      rw [lagPt_of_pos D.W D.Γc D.Ac D.rho (τ := τ) (x := y') (t := t) hy'0]
      congr 1
      exact (lagPt_of_nonpos D.W D.Γc D.Ac D.rho (τ := τ) (x := -y') (t := t - Real.pi)
        (by linarith)).symm
    have e2 : (fun s : ℝ => F (y, s))
        = fun s => Work.RPV.tau Real.pi (F (-y, s - Real.pi)) := by
      funext s
      simp only [hF]
      rw [lagPt_of_pos D.W D.Γc D.Ac D.rho (τ := τ) (x := y) (t := s) hy0]
      congr 1
      exact (lagPt_of_nonpos D.W D.Γc D.Ac D.rho (τ := τ) (x := -y) (t := s - Real.pi)
        (by linarith)).symm
    simp only [hΩ]
    rw [e1.deriv_eq, e2]
    exact hkey
  have htau2 : ∀ y : ℝ, Real.sqrt 2 < y → Ω (y, t) = 0 := by
    intro y hy
    have hlt : -y < -Real.sqrt 2 := by linarith
    have hleft : Work.RPV.symp (deriv (fun z => F (z, t - Real.pi)) (-y))
        (deriv (fun s => F (-y, s)) (t - Real.pi)) = 0 := by
      have := collar_region_lag CI a ha D τ hτ (-y) hlt (t - Real.pi)
      simpa only [hF] using this
    have hG : ContDiffAt ℝ 1 F (-y, t - Real.pi) := hFcd.contDiffAt
    have hkey := symp_tau_reflect F y t hG hleft
    have hy0 : 0 < y := by linarith
    have e1 : (fun y' : ℝ => F (y', t)) =ᶠ[𝓝 y]
        (fun y' => Work.RPV.tau Real.pi (F (-y', t - Real.pi))) := by
      filter_upwards [isOpen_Ioi.mem_nhds hy0] with y' hy'
      have hy'0 : (0 : ℝ) < y' := Set.mem_Ioi.mp hy'
      simp only [hF]
      rw [lagPt_of_pos D.W D.Γc D.Ac D.rho (τ := τ) (x := y') (t := t) hy'0]
      congr 1
      exact (lagPt_of_nonpos D.W D.Γc D.Ac D.rho (τ := τ) (x := -y') (t := t - Real.pi)
        (by linarith)).symm
    have e2 : (fun s : ℝ => F (y, s))
        = fun s => Work.RPV.tau Real.pi (F (-y, s - Real.pi)) := by
      funext s
      simp only [hF]
      rw [lagPt_of_pos D.W D.Γc D.Ac D.rho (τ := τ) (x := y) (t := s) hy0]
      congr 1
      exact (lagPt_of_nonpos D.W D.Γc D.Ac D.rho (τ := τ) (x := -y) (t := s - Real.pi)
        (by linarith)).symm
    simp only [hΩ]
    rw [e1.deriv_eq, e2]
    exact hkey
  -- the three exceptional lines, by continuity
  have hmem0 : Set.Ioo (-Real.sqrt 2) 0 ∈ 𝓝[<] (0 : ℝ) := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨Set.Ioi (-Real.sqrt 2), isOpen_Ioi.mem_nhds (by simp only [Set.mem_Ioi]; linarith), ?_⟩
    rintro z ⟨hz1, hz2⟩
    exact ⟨hz1, hz2⟩
  have hmem2 : Set.Ioo (0 : ℝ) (Real.sqrt 2) ∈ 𝓝[<] Real.sqrt 2 := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨Set.Ioi (0 : ℝ), isOpen_Ioi.mem_nhds hsq2, ?_⟩
    rintro z ⟨hz1, hz2⟩
    exact ⟨hz1, hz2⟩
  rcases lt_trichotomy x (-Real.sqrt 2) with hx | hx | hx
  · simpa only [hΩ, hF] using hcollar x hx
  · subst hx
    refine key (-Real.sqrt 2) ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact hcollar y hy
  · rcases lt_trichotomy x 0 with hx2 | hx2 | hx2
    · simpa only [hΩ, hF] using hchart x hx hx2
    · subst hx2
      refine key 0 ?_
      filter_upwards [hmem0] with y hy
      exact hchart y hy.1 hy.2
    · rcases lt_trichotomy x (Real.sqrt 2) with hx3 | hx3 | hx3
      · simpa only [hΩ, hF] using htau1 x hx2 hx3
      · subst hx3
        refine key (Real.sqrt 2) ?_
        filter_upwards [hmem2] with y hy
        exact htau1 y hy.1 hy.2
      · simpa only [hΩ, hF] using htau2 x hx3

end Work.RPB.B5
