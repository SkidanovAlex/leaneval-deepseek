/-
# The glue lemmas of the endgame (`mandelbar_not_path_connected`)

Area `Submission/Work/Final/`.  This module writes the concrete glue of
`NOTES_LEAD_mandelbar_arc_top.md` §2.3 that *can* be written from what is delivered:

* the identification of the abstract interface `Work.Top.NakaneData` (used by the endgame) with
  the delivered parameter-ray interface `Work.ParamRays` at `Mb = Mandelbar`, `Φ = Phi`
  (`top_paramRay_eq`, `top_extAngle_eq`, `top_potential_eq`);
* the `hLB` slot of the endgame — filled by the field `noPath` of `FinalInputs` itself (the
  *path* form; the earlier set-form conversion `hLB_of_noApproach` is dropped, see below);
* `hθ` from the Landing input `ParamAngleRepelling` and Goldberg–Milnor B.1
  (`notMem_closure_paramRay_windowAngle`);
* the real-ray clause `hreal` of the endgame: `1/4 ∈ Mandelbar`, `1/4 ∈ closure (R(0))`,
  `c₀ ∉ closure (R(0))` for a non-real `c₀` (`quarter_mem_closure_paramRay_zero`,
  `notMem_closure_paramRay_zero_of_im_ne_zero`);
* the point `p` of `hp` (`exists_limitPoint_windowAngle`), from the delivered step 1 of `FSeed`
  (`Work.FSeed.exists_paramRay_limit`).
-/
import Submission.Work.Final.Defs
import Submission.Work.Final.RootArc
import Submission.Work.ParamRays.paramRay_zero
import Submission.Work.ParamRays.Phi_conj
import Submission.Work.Bottcher.CritBottcherExists

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.Final

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## The abstract interface `Work.Top.NakaneData` versus `Work.ParamRays` -/

/-- The external angle of `Work.Top.NakaneData` at `Φ = Work.ParamRays.Phi` is the external angle
of the parameter-ray interface. -/
theorem top_extAngle_eq (c : ℂ) :
    Work.Top.NakaneData.extAngle Work.ParamRays.Phi c = Work.ParamRays.extAngle c := rfl

/-- The potential of `Work.Top.NakaneData` at `Mb = Mandelbar`, `Φ = Phi` is the potential of the
parameter-ray interface. -/
theorem top_potential_eq (c : ℂ) :
    Work.Top.potential Mandelbar Work.ParamRays.Phi c = Work.ParamRays.potential c := rfl

/-- The parameter ray of the abstract interface `Work.Top.NakaneData` is the parameter ray of
`Work.ParamRays` for the tricorn's own Böttcher coordinate (delivered as
`Work.FSeed.paramRay_eq`). -/
theorem top_paramRay_eq (hN : Work.Top.NakaneData Mandelbar Work.ParamRays.Phi) (θ : ℝ) :
    Work.Top.NakaneData.paramRay hN θ = Work.ParamRays.paramRay θ :=
  Work.FSeed.paramRay_eq hN θ

/-! ## `hLB`

The first version of this area converted the *set* form `c₀ ∉ closure (Mandelbar ∩ Nm)` into the
path form consumed by the endgame (`hLB_of_noApproach`, together with its companion
`not_mem_closure_of_subset`).  Both are **dropped**: `NOTES_LEAD_mandelbar_residuals.md` §0.1
records that the set form is not what the §2.3 argument proves and is very likely false (baby
tricorns accumulate at `c₀` inside `Nm`), while the path form

  `∀ γ : C(unitInterval, ℂ), (∀ t, γ t ∈ Mandelbar) → c₀ ∉ closure (Set.range γ ∩ Nm)`

is *verbatim* the `hLB` that `Work.TopJordan.mandelbar_not_isPathConnected_of_twoSidedPinch`
consumes.  It is the field `noPath` of `Work.Final.FinalInputs` and is passed to the endgame
directly, with no conversion. -/

/-- The mandelbar is nonempty (it contains the period-`1` parabolic parameter `1/4`), so
`¬ IsPathConnected Mandelbar` is not a vacuous statement. -/
theorem mandelbar_nonempty : Mandelbar.Nonempty := by
  exact Set.nonempty_iff_ne_empty.mpr (fun h => by
    have : (1 / 4 : ℂ) ∈ Mandelbar := Work.ParamRays.quarter_mem
    rw [h] at this
    exact this)

/-- **Two-sidedness of the implosion side.**  The `hX` of the endgame (a segment in
`Nm ∩ ball c₀ r` with escaping parameters of both angle windows) implies that `Nm` accumulates
at `c₀`.  Recorded so that the two residuals of `FinalInputs` are consistent with
`ImplosionSide.c_mem_closure`. -/
theorem mem_closure_Nm_of_twoSided {c₀ : ℂ} {Nm : Set ℂ}
    (h : ∀ r > 0, ∃ x y : ℂ, segment ℝ x y ⊆ Nm ∩ Metric.ball c₀ r ∧
      ∃ e₁ ∈ segment ℝ x y, ∃ e₂ ∈ segment ℝ x y, e₁ ∉ Mandelbar ∧ e₂ ∉ Mandelbar ∧
      Work.ParamRays.extAngle e₁ ∈ Set.Ioo (alpha1 - windowEps) (alpha1 + windowEps) ∧
      Work.ParamRays.extAngle e₂ ∈ Set.Ioo (alpha2 - windowEps) (alpha2 + windowEps)) :
    c₀ ∈ closure Nm := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨x, y, hseg, e₁, he₁, -⟩ := h ε hε
  exact ⟨e₁, (hseg he₁).1, by simpa [Metric.mem_ball, dist_comm] using (hseg he₁).2⟩

/-! ## The conversion of `hX` -/

/-- **`hX` of the endgame, in the vocabulary of `Work.ParamRays`.**  Same statement as the
`hX` consumed by `Work.TopJordan.mandelbar_not_isPathConnected_of_twoSidedPinch`, with the external
angle written in the parameter-ray interface (the two agree by `top_extAngle_eq`). -/
theorem hX_of_twoSided {c₀ : ℂ} {Nm : Set ℂ}
    (h : ∀ r > 0, ∃ x y : ℂ, segment ℝ x y ⊆ Nm ∩ Metric.ball c₀ r ∧
      ∃ e₁ ∈ segment ℝ x y, ∃ e₂ ∈ segment ℝ x y, e₁ ∉ Mandelbar ∧ e₂ ∉ Mandelbar ∧
      Work.ParamRays.extAngle e₁ ∈ Set.Ioo (alpha1 - windowEps) (alpha1 + windowEps) ∧
      Work.ParamRays.extAngle e₂ ∈ Set.Ioo (alpha2 - windowEps) (alpha2 + windowEps)) :
    ∀ r > 0, ∃ x y : ℂ, segment ℝ x y ⊆ Nm ∩ Metric.ball c₀ r ∧
      ∃ e₁ ∈ segment ℝ x y, ∃ e₂ ∈ segment ℝ x y, e₁ ∉ Mandelbar ∧ e₂ ∉ Mandelbar ∧
      Work.Top.NakaneData.extAngle Work.ParamRays.Phi e₁ ∈
        Set.Ioo (alpha1 - windowEps) (alpha1 + windowEps) ∧
      Work.Top.NakaneData.extAngle Work.ParamRays.Phi e₂ ∈
        Set.Ioo (alpha2 - windowEps) (alpha2 + windowEps) := by
  intro r hr
  obtain ⟨x, y, hseg, e₁, he₁, e₂, he₂, h₁, h₂, ha₁, ha₂⟩ := h r hr
  exact ⟨x, y, hseg, e₁, he₁, e₂, he₂, h₁, h₂, by rwa [top_extAngle_eq],
    by rwa [top_extAngle_eq]⟩

/-! ## `hθ` -/

/-- **`hθ`** (`NOTES_LEAD_mandelbar_arc_top.md` §2.3): Goldberg–Milnor Lemma B.1 says that a
parameter at which the ray `R_c(θ)` lands at a *repelling* periodic point is not a limit point of
the parameter ray `R(θ)`.  Applied at the window angle `θ = 23/63`, whose dynamical ray lands at a
repelling point (`ParamAngleRepelling`), this is exactly `hθ`. -/
theorem notMem_closure_paramRay_windowAngle {c : ℂ}
    (gm : Work.FSeed.RepellingRayParamStable) (hrep : ParamAngleRepelling c) :
    c ∉ closure (Work.ParamRays.paramRay windowAngle) := by
  obtain ⟨k, y, hrep', hland⟩ := hrep
  exact gm c k y windowAngle hrep' hland

/-- `hθ` in the form consumed by the endgame of `Work.Top`/`Work.TopJordan`. -/
theorem notMem_closure_top_paramRay_windowAngle {c : ℂ}
    (hN : Work.Top.NakaneData Mandelbar Work.ParamRays.Phi)
    (gm : Work.FSeed.RepellingRayParamStable) (hrep : ParamAngleRepelling c) :
    c ∉ closure (Work.Top.NakaneData.paramRay hN windowAngle) := by
  rw [top_paramRay_eq hN windowAngle]
  exact notMem_closure_paramRay_windowAngle gm hrep

/-- The window angle `23/63` is not a limit angle at the period-`1` parabolic parameter `1/4`
either: the ray `R_{1/4}(23/63)` lands at a repelling point of period `6`, and `6 ∤ 2·1`. -/
theorem quarter_notMem_closure_paramRay_windowAngle
    (gm : Work.FSeed.RepellingRayParamStable) (hrep : ParamAngleRepelling (1 / 4 : ℂ)) :
    (1 / 4 : ℂ) ∉ closure (Work.ParamRays.paramRay windowAngle) :=
  notMem_closure_paramRay_windowAngle gm hrep

/-! ## The real-ray clause `hreal` -/

/-- The parameter ray of angle `0` is the real ray above the root `1/4`
(`Work.ParamRays.paramRay_zero`, with the conjugation equivariance of `Phi`). -/
theorem paramRay_zero_eq (hN : Work.ParamRays.NakaneInput) :
    Work.ParamRays.paramRay 0 = {c : ℂ | c.im = 0 ∧ (1 / 4 : ℝ) < c.re} :=
  Work.ParamRays.paramRay_zero hN
    (fun c => by simpa using Work.ParamRays.Phi_conj hN.bottcher c)

/-- `1/4` lies in the closure of the parameter ray `R(0)`: the real parameters `1/4 + t`, `t → 0⁺`,
lie on the ray. -/
theorem quarter_mem_closure_paramRay_zero (hN : Work.ParamRays.NakaneInput) :
    (1 / 4 : ℂ) ∈ closure (Work.ParamRays.paramRay 0) := by
  rw [paramRay_zero_eq hN, Metric.mem_closure_iff]
  intro ε hε
  refine ⟨((1 / 4 + ε / 2 : ℝ) : ℂ), ⟨?_, ?_⟩, ?_⟩
  · simp
  · simp only [Complex.ofReal_re]; linarith
  · have h1 : (1 / 4 : ℂ) - ((1 / 4 + ε / 2 : ℝ) : ℂ) = ((-(ε / 2) : ℝ) : ℂ) := by
      push_cast; ring
    rw [Complex.dist_eq, h1, Complex.norm_real, Real.norm_eq_abs,
      abs_of_neg (by linarith : -(ε / 2) < 0)]
    linarith

/-- A non-real parameter is not in the closure of the parameter ray `R(0)`, which is contained in
the real axis. -/
theorem notMem_closure_paramRay_zero_of_im_ne_zero (hN : Work.ParamRays.NakaneInput) {c : ℂ}
    (h : c.im ≠ 0) : c ∉ closure (Work.ParamRays.paramRay 0) := by
  rw [paramRay_zero_eq hN]
  intro hc
  have hcl : closure {d : ℂ | d.im = 0 ∧ (1 / 4 : ℝ) < d.re} ⊆ {d : ℂ | d.im = 0} :=
    closure_minimal (fun d hd => hd.1) (isClosed_eq Complex.continuous_im continuous_const)
  exact h (hcl hc)

/-! ## The limit point `p` of `hp` -/

/-- **`hp`** (`NOTES_LEAD_mandelbar_arc_top.md` §2.1): the parameter ray of the window angle
`23/63` accumulates at a point `p` of the mandelbar, with `p` **not** on the ray and `p ≠ 1/4`.
The existence of the limit point is the delivered step 1 of `FSeed`
(`Work.FSeed.exists_paramRay_limit`); `p ≠ 1/4` follows from `hθ` at `1/4`. -/
theorem exists_limitPoint_windowAngle
    (hN : Work.Top.NakaneData Mandelbar Work.ParamRays.Phi)
    (gm : Work.FSeed.RepellingRayParamStable) (hrep : ParamAngleRepelling (1 / 4 : ℂ)) :
    ∃ p : ℂ, p ∈ Mandelbar ∧ p ∈ closure (Work.Top.NakaneData.paramRay hN windowAngle) ∧
      (p ≠ (1 / 4 : ℂ) ∧ p ∉ Work.Top.NakaneData.paramRay hN windowAngle) := by
  obtain ⟨p, hpMb, hpcl, hpnr⟩ := Work.FSeed.exists_paramRay_limit hN windowAngle
  refine ⟨p, hpMb, hpcl, ?_, hpnr⟩
  intro hp
  refine quarter_notMem_closure_paramRay_windowAngle gm hrep ?_
  rw [← top_paramRay_eq hN windowAngle]
  rwa [hp] at hpcl

/-! ## The root-arc data, from the `FSeed` input -/

/-- **`RootArc` is non-vacuous**: from the classical input bundle `Work.FSeed.FSeedInput` of the
root of the non-real period-`5` component, there is a parameter of the mandelbar carrying
root-arc data.  This is `Work.FSeed.exists_rootParabolic` (the `FSeed` deliverable) composed with
`Work.Final.exists_rootArc` (the flower, from `FatouCoord`). -/
theorem exists_rootArc_of_FSeedInput (h : Work.FSeed.FSeedInput) :
    ∃ c : ℂ, c ∈ Mandelbar ∧ Nonempty (RootArc c) := by
  obtain ⟨c, hne⟩ := Work.FSeed.exists_rootParabolic h
  exact ⟨c, Work.FSeed.API.mem_Mandelbar hne.some, (exists_rootArc hne.some).map fun A => A⟩

/-- **The same, straight from the root-parabolic structure** (lead addendum
`NOTES_LEAD_mandelbar_noncusp.md` §4.4): if *any* parameter of the tricorn carries
`Work.EL.RootParabolic` — the output shape of the explicit certified-parameter route
(areas SeedCertNum/SeedCertRay), as well as of `Work.FSeed.exists_rootParabolic` — then there is a
parameter of the mandelbar carrying root-arc data.  The body is the same as
`exists_rootArc_of_FSeedInput`: the only ingredient is `Work.Final.exists_rootArc` (the flower),
composed with the mandelbar membership of the root-parabolic structure. -/
theorem exists_rootArc_of_rootParabolic (h : ∃ c : ℂ, Nonempty (Work.EL.RootParabolic c)) :
    ∃ c : ℂ, c ∈ Mandelbar ∧ Nonempty (RootArc c) := by
  obtain ⟨c, hne⟩ := h
  exact ⟨c, Work.FSeed.API.mem_Mandelbar hne.some, (exists_rootArc hne.some).map fun A => A⟩

/-- The same from the pre-classification bundle `Work.FSeed.RootParabolicInput`. -/
theorem exists_rootArc_of_rootParabolicInput {c : ℂ} (h : Work.FSeed.RootParabolicInput c) :
    c ∈ Mandelbar ∧ Nonempty (RootArc c) :=
  ⟨Work.FSeed.API.mem_Mandelbar_input h,
    exists_rootArc (Work.FSeed.rootParabolic_of_input h).some⟩

/-! ## Nakane's classical inputs -/

/-- **The Böttcher-existence field of `NakaneInput` is discharged**: `Work.Bottcher.bottcherExists_crit`
proves that critical Böttcher coordinates exist outside the mandelbar, so the classical content of
`NakaneInput` is only Nakane's homeomorphism theorem and the uniform asymptotic. -/
theorem nakane_of_homeo_asymptotic (h1 : Work.ParamRays.NakaneHomeo)
    (h2 : Work.ParamRays.UniformBottcherAsymptotic) : Work.ParamRays.NakaneInput :=
  ⟨Work.Bottcher.bottcherExists_crit, h2, h1⟩

end Work.Final
