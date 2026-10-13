/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/AesmJfamP.lean` — the joint a.e. strong measurability of
the slots of the projected mollified family

`DiagCurveI_JfamP` (the producer of the `L²`-route bundle for a slot of `x = slice (JfamP ρ ε g)`)
carries the two interface fields

  `haesm  : AESM (fun q => mixed a b (slice (JfamP ρ ε g) q.1) q.2.1 q.2.2) μ`
  `haesmd : AESM (fun q => mixed a b (slice (Pz ∘ J_ε ∘ epsRHSP …) q.1) q.2.1 q.2.2) μ`

with `μ = (volume.restrict (Icc 0 T)).prod mup` — the **horizon-restricted** product measure, which
is the honest hypothesis (`AesmRestrict.lean` explains why the full product is unprovable: the flow
is only constrained on `Icc 0 T`).

This module *produces* the first one (`haesm`) from a single geometric-analytic input, namely the
joint continuity, on the closed slab, of the slots of the **unmollified** flow up to order `a + b`:

  `hcontAll : ∀ j i, j + i ≤ a + b →
     ContinuousOn (fun q => mixed j i (slice g q.1) q.2.1 q.2.2) (Icc 0 T ×ˢ Quad)`

(`j = i = 0` is the continuity of the raw flow `g` itself, `j + i ≥ 1` that of its slots).  The
reduction is the one recorded in `NOTES_EpsE4Thr_session4.md` §5, with the two global steps now
proved as separate lemmas:

* `JepsJoint.Jeps_fam_continuous` — the mollifier of a jointly continuous family is jointly
  continuous (`J_ε` is a parametric integral against the compactly supported `Jker ρ ε`);
* `JepsJoint.aemeasurable_L12_fam` — hence `s ↦ L₁₂ (J_ε (slice g s)) 0` is a.e. strongly
  measurable (`L₁₂` is an iterated integral over a σ-finite measure);
* the remaining steps are local: the *commutation* `mixed a b (J_ε f) = J_ε (mixed a b f)` on the
  open quadrant (`Work.FTS.StrongEps.mixed_Jeps`, which needs only the per-slice smoothness `hsm`),
  the **linearity of `mixed`** in the `Pz`-correction (via the fully general
  `E2pkg.mixed_add_of_contDiffOn` and the unconditional `mixed_const_mul`), and the conjullity of
  the open quadrant for `mup`.

The `mup`-conjullity facts (`ae_mem_openQuadrant_fts`, `Measure.restrict_eq_self_of_ae_mem`) and the
`Measure.ae_prod_iff_ae_ae` bookkeeping are the only measure-theoretic inputs.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongEps.EpsE4Thr.JepsJoint.Jeps_fam_continuous
import Submission.Work.FTS.StrongEps.EpsE4Thr.JepsJoint.aemeasurable_L12_fam
import Submission.Work.FTS.StrongEps.EpsE4Thr.WipEqIntegral
import Submission.Work.FTS.StrongEps.EpsE4Thr.WipSlotIntegrable
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.FTS.StrongEps.JepsSmoothOpen
import Submission.Work.FTS.StrongEps.BumpDefs
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## Linearity of `mixed` under a constant multiple

(The unconditional version: `deriv_const_mul_field` is `deriv (fun y => u * v y) x = u * deriv v x`
for any `v : ℝ → ℝ`, no differentiability hypothesis needed.) -/

private theorem DthIter_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (i : ℕ) :
    Work.Spaces.DthIter i (fun z θ : ℝ => c * f z θ)
      = fun z θ : ℝ => c * Work.Spaces.DthIter i f z θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DthIter_succ, ih, Work.Spaces.DthIter_succ]
      funext z θ
      simp only [Work.Spaces.Dth, Work.Spaces.pth, deriv_const_mul_field]
      ring

private theorem DzIter_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (j : ℕ) :
    Work.Spaces.DzIter j (fun z θ : ℝ => c * f z θ)
      = fun z θ : ℝ => c * Work.Spaces.DzIter j f z θ := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Work.Spaces.DzIter_succ, ih, Work.Spaces.DzIter_succ]
      funext z θ
      simp only [Work.Spaces.Dz, Work.Spaces.pz, deriv_const_mul_field]
      ring

private theorem mixed_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (j i : ℕ) :
    Work.Spaces.mixed j i (fun z θ : ℝ => c * f z θ)
      = fun z θ : ℝ => c * Work.Spaces.mixed j i f z θ := by
  rw [Work.Spaces.mixed, DthIter_const_mul c f i]
  exact DzIter_const_mul c (Work.Spaces.DthIter i f) j

/-! ## The `Pz`-correction of a slot -/

/-- **A mixed slot of the projection `Pz w = w − (L₁₂ w 0 / pzNorm) • bump`.**  Both `w` and
`bump` are smooth on the open quadrant, so the sum splits
(`Work.FTS.CoercivityFix.Transfer.E2pkg.mixed_add_of_contDiffOn` + the constant-multiple rule). -/
theorem mixed_Pz_eq {a b n : ℕ} {w : ℝ → ℝ → ℝ}
    (hw : ContDiffOn ℝ n (Function.uncurry w) Work.FTS.StrongEps.Quad) (hab : a + b ≤ n)
    {z θ : ℝ} (hzθ : (z, θ) ∈ Work.FTS.StrongEps.Quad) :
    Work.Spaces.mixed a b (Pz w) z θ
      = Work.Spaces.mixed a b w z θ
        - (Work.Construction.L12 w 0 / pzNorm) * Work.Spaces.mixed a b bump z θ := by
  have hbump : ContDiffOn ℝ n (Function.uncurry (fun z θ : ℝ => bump z θ))
      Work.FTS.StrongEps.Quad := by
    have hfun : Function.uncurry (fun z θ : ℝ => bump z θ)
        = fun p : ℝ × ℝ => bump p.1 p.2 := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [hfun]
    exact (Work.FTS.StrongEps.contDiff_bump n).contDiffOn
  have hsplit : ContDiffOn ℝ n
      (Function.uncurry (fun z θ : ℝ => -(Work.Construction.L12 w 0 / pzNorm) * bump z θ))
      Work.FTS.StrongEps.Quad := by
    have hfun : Function.uncurry
        (fun z θ : ℝ => -(Work.Construction.L12 w 0 / pzNorm) * bump z θ)
        = fun p : ℝ × ℝ => -(Work.Construction.L12 w 0 / pzNorm) * bump p.1 p.2 := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [hfun]
    exact contDiffOn_const.mul hbump
  have hfun : Pz w = w + fun z θ : ℝ => -(Work.Construction.L12 w 0 / pzNorm) * bump z θ := by
    funext z θ
    rw [Pz_apply]
    simp only [Pi.add_apply]
    ring
  rw [hfun]
  rw [Work.FTS.CoercivityFix.Transfer.E2pkg.mixed_add_of_contDiffOn
    (V := Work.FTS.StrongEps.Quad) Work.FTS.StrongEps.isOpen_Quad hw hsplit b a (by omega)
    (z, θ) hzθ, mixed_const_mul]
  simp only [Prod.fst, Prod.snd]
  ring

/-! ## The joint a.e. strong measurability of the `J_ε`-mollified slots -/

/-- **The slots of the mollified family are jointly a.e. strongly measurable.**  This is the
`J_ε`-half of `DiagCurveI_JfamP`'s `haesm`, before the projection `Pz` is taken. -/
theorem aestronglyMeasurable_mixed_Jeps_fam {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {ε T : ℝ} {g : Fam} {a b : ℕ} (hε : 0 < ε)
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n : ℕ,
      ContDiffOn ℝ n (Function.uncurry (slice g s)) Work.FTS.EllipticEst.Q0)
    (hcont : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      Work.Spaces.mixed a b (slice g q.1) q.2.1 q.2.2)
      (Set.Icc (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad)) :
    MeasureTheory.AEStronglyMeasurable
      (fun q : ℝ × (ℝ × ℝ) => Work.Spaces.mixed a b
        (Work.FTS.StrongEps.Jeps ρ ε (slice g q.1)) q.2.1 q.2.2)
      ((MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)).prod mup) := by
  haveI : SFinite mup := by rw [mup]; infer_instance
  -- the mollifier of a jointly continuous family is jointly continuous
  have hJ : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => Work.FTS.StrongEps.Jeps ρ ε
      (fun z θ => Work.Spaces.mixed a b (slice g q.1) z θ) q.2.1 q.2.2)
      (Set.Icc (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad) :=
    JepsJoint.Jeps_fam_continuous (ρ := ρ) (ε := ε) (T := T)
      (g := fun z θ s => Work.Spaces.mixed a b (slice g s) z θ) hρ hε hcont
  -- `mixed` commutes with `J_ε` on the open quadrant
  have hcont' : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      Work.Spaces.mixed a b (Work.FTS.StrongEps.Jeps ρ ε (slice g q.1)) q.2.1 q.2.2)
      (Set.Icc (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad) := by
    refine hJ.congr (fun q hq => ?_)
    exact Work.FTS.StrongEps.mixed_Jeps ρ hρ hε (hsm q.1 hq.1) hq.2.1 hq.2.2 a b
  -- the slab `Icc 0 T ×ˢ Quad` carries the restricted product measure
  have hμ : (((MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)).prod mup).restrict
      (Set.Icc (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad))
      = (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)).prod mup := by
    refine MeasureTheory.Measure.restrict_eq_self_of_ae_mem ?_
    refine (MeasureTheory.Measure.ae_prod_iff_ae_ae
      (p := fun q : ℝ × (ℝ × ℝ) =>
        q.1 ∈ Set.Icc (0 : ℝ) T ∧ q.2 ∈ Work.FTS.StrongEps.Quad)
      ((measurableSet_Icc.preimage measurable_fst).inter
        (Work.FTS.StrongEps.isOpen_Quad.measurableSet.preimage measurable_snd))).mpr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with s hs
    filter_upwards [ae_mem_openQuadrant_fts] with p hp
    exact ⟨hs, hp⟩
  have h1 : MeasureTheory.AEStronglyMeasurable
      (fun q : ℝ × (ℝ × ℝ) =>
        Work.Spaces.mixed a b (Work.FTS.StrongEps.Jeps ρ ε (slice g q.1)) q.2.1 q.2.2)
      (((MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)).prod mup).restrict
        (Set.Icc (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad)) :=
    hcont'.aestronglyMeasurable
      (measurableSet_Icc.prod Work.FTS.StrongEps.isOpen_Quad.measurableSet)
  rw [hμ] at h1
  exact h1

/-! ## The projected slot -/

/-- **The joint a.e. strong measurability of a slot of `slice (JfamP ρ ε g)`** — the honest
hypothesis `haesm` of `DiagCurveI_JfamP`, produced from the joint continuity of the flow's slots on
the closed slab (the interface item (I) of the level-four chapter). -/
theorem aestronglyMeasurable_mixed_JfamP {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε T : ℝ} {g : Fam} {a b : ℕ} (hε : 0 < ε)
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n : ℕ,
      ContDiffOn ℝ n (Function.uncurry (slice g s)) Work.FTS.EllipticEst.Q0)
    (hcontAll : ∀ j i : ℕ, j + i ≤ a + b → ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      Work.Spaces.mixed j i (slice g q.1) q.2.1 q.2.2)
      (Set.Icc (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad)) :
    MeasureTheory.AEStronglyMeasurable
      (fun q : ℝ × (ℝ × ℝ) => Work.Spaces.mixed a b (slice (JfamP ρ ε g) q.1) q.2.1 q.2.2)
      ((MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)).prod mup) := by
  haveI : SFinite mup := by rw [mup]; infer_instance
  have hcont := hcontAll a b le_rfl
  -- the raw flow is the `(0,0)`-slot
  have hg : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => g q.2.1 q.2.2 q.1)
      (Set.Icc (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad) := by
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right,
      Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero, Work.FTS.Galerkin.slice_apply]
      using hcontAll 0 0 (by omega)
  -- Step 1: the mollified slots
  have hJeps := aestronglyMeasurable_mixed_Jeps_fam (ρ := ρ) (ε := ε) (T := T) (g := g)
    (a := a) (b := b) hρ.moll hε hsm hcont
  -- Step 2: the mollified raw family is jointly continuous, so the `L₁₂`-scalar is measurable
  have hJraw : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      Work.FTS.StrongEps.Jeps ρ ε (slice g q.1) q.2.1 q.2.2)
      (Set.Icc (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad) :=
    JepsJoint.Jeps_fam_continuous (ρ := ρ) (ε := ε) (T := T) (g := g) hρ.moll hε hg
  have hL12 : AEMeasurable (fun s : ℝ =>
      Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε (slice g s)) 0)
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)) :=
    JepsJoint.aemeasurable_L12_fam (T := T)
      (F := fun s z θ => Work.FTS.StrongEps.Jeps ρ ε (slice g s) z θ) hJraw
  have hL12' : MeasureTheory.AEStronglyMeasurable
      (fun q : ℝ × (ℝ × ℝ) => Work.Construction.L12
        (Work.FTS.StrongEps.Jeps ρ ε (slice g q.1)) 0 / pzNorm)
      ((MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)).prod mup) :=
    ((hL12.div_const pzNorm).aestronglyMeasurable).comp_fst
  -- Step 3: the `bump`-correction is a fixed continuous function of the space variable
  have hbump : MeasureTheory.AEStronglyMeasurable
      (fun q : ℝ × (ℝ × ℝ) => Work.Spaces.mixed a b bump q.2.1 q.2.2)
      ((MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)).prod mup) :=
    (Work.Spaces.aesm_of_continuousOn_Qd (fun p : ℝ × ℝ => Work.Spaces.mixed a b bump p.1 p.2)
      ((Work.FTS.EllipticEst.SmoothOpen.mixed (F := bump) Work.FTS.StrongEps.smoothOpen_bump a b
        ).continuousOn)).comp_snd
  -- Step 4: the sum
  have hsum : MeasureTheory.AEStronglyMeasurable
      (fun q : ℝ × (ℝ × ℝ) =>
        Work.Spaces.mixed a b (Work.FTS.StrongEps.Jeps ρ ε (slice g q.1)) q.2.1 q.2.2
          - (Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε (slice g q.1)) 0 / pzNorm)
            * Work.Spaces.mixed a b bump q.2.1 q.2.2)
      ((MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)).prod mup) :=
    hJeps.sub (hL12'.mul hbump)
  -- Step 5: on the conull set `Icc 0 T ×ˢ Quad` the sum is the projected slot
  refine hsum.congr ?_
  have hquad : ∀ᵐ q ∂((MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)).prod mup),
      q.1 ∈ Set.Icc (0 : ℝ) T ∧ q.2 ∈ Work.FTS.StrongEps.Quad := by
    refine (MeasureTheory.Measure.ae_prod_iff_ae_ae
      (p := fun q : ℝ × (ℝ × ℝ) =>
        q.1 ∈ Set.Icc (0 : ℝ) T ∧ q.2 ∈ Work.FTS.StrongEps.Quad)
      ((measurableSet_Icc.preimage measurable_fst).inter
        (Work.FTS.StrongEps.isOpen_Quad.measurableSet.preimage measurable_snd))).mpr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with s hs
    filter_upwards [ae_mem_openQuadrant_fts] with p hp
    exact ⟨hs, hp⟩
  filter_upwards [hquad] with q hq
  exact (mixed_Pz_eq (w := Work.FTS.StrongEps.Jeps ρ ε (slice g q.1))
    ((Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε (hsm q.1 hq.1)).forall (a + b))
    le_rfl hq.2).symm

/-! ## The same for the scheme's right-hand side `xdot = Pz (J_ε (epsRHSP …))` -/

/-- **The joint a.e. strong measurability of a slot of the derivative family
`σ ↦ Pz (J_ε (epsRHSP α ρ ε Φs E g σ))`** — the honest hypothesis `haesmd` of
`DiagCurveI_JfamP`.  It is the `g := (z,θ,σ) ↦ epsRHSP α ρ ε Φs E g σ z θ` instance of
`aestronglyMeasurable_mixed_JfamP`. -/
theorem aestronglyMeasurable_mixed_JfamP_RHS {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {α T ε : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {g : Fam} {a b : ℕ} (hε : 0 < ε)
    (hsmR : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n : ℕ,
      ContDiffOn ℝ n (Function.uncurry (epsRHSP α ρ ε Φs E g s)) Work.FTS.EllipticEst.Q0)
    (hcontAllR : ∀ j i : ℕ, j + i ≤ a + b → ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      Work.Spaces.mixed j i (epsRHSP α ρ ε Φs E g q.1) q.2.1 q.2.2)
      (Set.Icc (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad)) :
    MeasureTheory.AEStronglyMeasurable
      (fun q : ℝ × (ℝ × ℝ) => Work.Spaces.mixed a b
        (Pz (Work.FTS.StrongEps.Jeps ρ ε (epsRHSP α ρ ε Φs E g q.1))) q.2.1 q.2.2)
      ((MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)).prod mup) :=
  aestronglyMeasurable_mixed_JfamP (ρ := ρ) (ε := ε) (T := T)
    (g := fun z θ σ => epsRHSP α ρ ε Φs E g σ z θ) (a := a) (b := b) hρ hε hsmR hcontAllR

/-! ## Consequence of the joint smoothness of the flow on the closed slab -/

/-- **Per-slice smoothness from joint smoothness.**  If the uncurried family is `C^n` on the closed
slab `Icc 0 T ×ˢ Quad`, then each of its slices is `C^n` on the open quadrant. -/
theorem smoothOn_slice_of_joint_smooth {g : Fam} {T s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T) {n : ℕ}
    (hreg : ContDiffOn ℝ n (fun q : ℝ × (ℝ × ℝ) => g q.2.1 q.2.2 q.1)
      (Set.Icc (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad)) :
    ContDiffOn ℝ n (Function.uncurry (slice g s)) Work.FTS.EllipticEst.Q0 := by
  have hmap : ContDiffOn ℝ n (fun p : ℝ × ℝ => (s, p)) Work.FTS.EllipticEst.Q0 :=
    ContDiffOn.prodMk contDiffOn_const contDiffOn_id
  have hmaps : Set.MapsTo (fun p : ℝ × ℝ => (s, p)) Work.FTS.EllipticEst.Q0
      (Set.Icc (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad) := fun p hp => ⟨hs, hp⟩
  refine (hreg.comp hmap hmaps).congr (fun p _ => ?_)
  rcases p with ⟨z, θ⟩
  rfl

/-- **Slicewise-in-time measurability from the joint continuity of the slots.**  This is the
hypothesis `hmeas` of the chain (`ae_hasDerivAt_mixed_JfamP` and friends), produced here from the
single joint-continuity input of the level-four chapter. -/
theorem aestronglyMeasurable_slice_mixed {g : Fam} {T : ℝ} {k l : ℕ}
    (hcont : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      Work.Spaces.mixed k l (slice g q.1) q.2.1 q.2.2)
      (Set.Icc (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad))
    {z θ : ℝ} (hzθ : (z, θ) ∈ Work.FTS.StrongEps.Quad) :
    MeasureTheory.AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed k l (slice g s) z θ)
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)) := by
  have hmap : ContinuousOn (fun s : ℝ => (s, (z, θ))) (Set.Icc (0 : ℝ) T) :=
    ContinuousOn.prodMk continuousOn_id continuousOn_const
  have hmaps : Set.MapsTo (fun s : ℝ => (s, (z, θ))) (Set.Icc (0 : ℝ) T)
      (Set.Icc (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad) := fun s hs => ⟨hs, hzθ⟩
  exact (hcont.comp hmap hmaps).aestronglyMeasurable measurableSet_Icc

end Work.FTS.StrongEps.EpsE4Thr
