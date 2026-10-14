import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.EpsE4Thr.LeafD2.hB_slab_lip
import Submission.Work.FTS.StrongEps.EpsE4Thr.XBallIterExists
import Submission.Work.FTS.TransportS.t2SlotGuarded
import Submission.Work.FTS_EllLimOK.BoxDataH.boxDataH_of_hasPkgH
import Submission.Work.FTS_EllLimOK.FatouH
import Submission.Work.FTS_EllLimOK.FinalCore
import Submission.Work.FTS_EllLimOK.GlueG.exists_ellLimOK3_of_closedG
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.Trace
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.th2EgRate
import Submission.Work.FTS_EllLimOK.ProducerH.H2.Clause1Aux
import Submission.Work.FTS_EllLimOK.ProducerH.H2.Slice
import Submission.Work.FTS_EllLimOK.ProducerH.H2.bounds_rates_theta
import Submission.Work.FTS_EllLimOK.ProducerH.H2.bounds_rates_z
import Submission.Work.FTS_EllLimOK.ProducerH.slotBd_phiTil
import Submission.Work.FTS_EllLimOK.RulingELF
import Submission.Work.FTS_EllLimOK.SmallAssemblyH
import Submission.Work.FTS_RegExport.RXVP.velPkg_proved
import Submission.Work.FTS_RegExport.RXVP3.velPkgOpen_of_vopLower
import Submission.Work.FTS_StreamBdry.SB4.near0Aux
import Submission.Work.Spaces.sin_two_rpow
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.RegDataWired =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `EpsE4Thr/RegDataWired.lean` — the regularity data of the scheme's right-hand side along the
# limit curve, from the `X`-ball invariant **plus** the `τ`-Lipschitz bound of the limit curve

**Why this file exists.**  The lead-installed open leaf `EpsE4Thr.RegDataOfXBall.regData_of_xball`
(LEAF-D2) asks for `RegDataD (Feps …) h₀ δ` from the `X`-ball invariant of the limit slices
(`hlim`) and the Volterra identity (`hvol`) alone.  Those two hypotheses do **not** supply any
`τ`-regularity of the limit curve that could be *measured* through `EpsSq`:

* the two continuity conjuncts reduce (through the proved pointwise gate
  `EpsLocalPStar.profRHS_sub_sup_le_Sq` for the *mollified projected* right-hand side and through
  `EpsLocalPStar.profRHS_pre_sub_pt_le_Sq` for the *pre-mollified* one, used in the routed form of
  `J_ε`) to the single estimate `EpsSq α (slice σ − slice τ) ≤ L' (σ − τ)²`;
* that estimate is *not* a consequence of `hvol` + the gate: evaluating `EpsSq` of the difference
  `∫_τ^σ F_r dr` needs the *honesty* (and measurability in the parameter) of `r ↦ F_r(y)`, which
  the gates (uniform in `r` but only in `EpsSq`-norm) and the pointwise identity `hvol` do not
  provide.  What *does* provide it is the Picard data: `EpsEngine.EpsSq_iter_sub_sq_le` gives the
  estimate for every iterate, and Fatou (`EpsMem_and_EpsSq_le_of_ae_tendsto_mem`) passes it to the
  limit — this is `EpsE4Thr.LeafD2.limEpsSq_lipschitz`, a *strengthened sibling* of
  `XBallLimExists` that takes its hypothesis list verbatim.

The consumer (`EpsE4Thr.XStepAssemblyD`/`XStepAssemblyWired`) has that Picard data (it produces
`hiter` and the gates), so the missing input is available exactly where the leaf is used.  This
module therefore proves the leaf's conclusion from the leaf's hypotheses **plus** the `τ`-Lipschitz
bundle, by assembling the three conjuncts:

* `LeafD2.hAc_slab` — joint continuity of `(z,θ,τ) ↦ Feps (slice (limFam …) τ) (z,θ)`;
* the per-slice clause, from `smoothOpen_Feps_of_classC` (`SmoothOpen` ⟹ `ContDiffOn ℝ 1`);
* `LeafD2.hB_slab_lip` — joint continuity of the spatial `fderiv`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.RegDataWired

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.EpsEngine (XBall Feps)
open Work.FTS.StrongEps.EpsLocalPStar (iter limFam)

set_option autoImplicit false

/-- **LEAF-D2 over the strengthened hypothesis list**: the three `RegDataD` fields of the scheme's
right-hand side along the Picard limit curve, from the hypothesis list of `XBallLimExists` (which
carries the iterate clause `hiter`, hence the `τ`-Lipschitz bound of the limit curve) together with
the limit clause `hlim` and the Volterra identity `hvol`. -/
theorem regData_of_xball_wired {α C₀ Ce Cs M' Cpt L δ R : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Fn} {E : Fn → Fn} {ε : ℝ} {h₀ : Fn}
    (hC₀ : 0 < C₀) (hα : α ∈ Set.Ioc (0 : ℝ) 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α (2 * C₀) Φs E)
    (hM' : 0 ≤ M')
    (hL : 0 < L) (hδ : 0 < δ) (hδL : δ * Real.sqrt L < 1) (hR : 0 < R)
    (hbd : ∀ u : Fn, XBall α ρ ε R (2 * C₀) u →
      Work.FTS.StrongEps.EpsMem α (Feps α ρ ε Φs E u) ∧
        Work.FTS.StrongEps.EpsSq α (Feps α ρ ε Φs E u) ≤ L)
    (hlip : ∀ u v : Fn, XBall α ρ ε R (2 * C₀) u → XBall α ρ ε R (2 * C₀) v →
      Work.FTS.StrongEps.EpsMem α (fun z θ => u z θ - v z θ) →
      Work.FTS.StrongEps.EpsSq α (fun z θ => Feps α ρ ε Φs E u z θ - Feps α ρ ε Φs E v z θ)
        ≤ L * Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ))
    (hCpt : 0 ≤ Cpt)
    (hpt : ∀ u v : Fn, XBall α ρ ε R (2 * C₀) u → XBall α ρ ε R (2 * C₀) v →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Feps α ρ ε Φs E u z θ - Feps α ρ ε Φs E v z θ|
          ≤ Cpt * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)))
    (hsmo : Work.FTS.EllipticEst.SmoothOpen h₀) (hmem : Work.Spaces.HkMem α 6 h₀)
    (hM6 : Work.Spaces.HkSq α 6 h₀ ≤ M')
    (hcl : Work.FTS.ClassC.ClassC α
      (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε h₀)))
    (hball : Work.FTS.Nonlin.Xn α
      (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε h₀)) ≤ C₀ * α ^ 2)
    (hdatmem : Work.FTS.StrongEps.EpsMem α h₀) (hdatsq : Work.FTS.StrongEps.EpsSq α h₀ ≤ R)
    (hiter : ∀ n : ℕ, ∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
      XBall α ρ ε R (2 * C₀) (slice (iter (Feps α ρ ε Φs E) h₀ (n + 1)) τ))
    (hlim : ∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
      XBall α ρ ε R (2 * C₀) (slice (limFam (Feps α ρ ε Φs E) h₀) τ))
    (hvol : ∀ z θ τ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) → τ ∈ Set.Icc 0 δ →
      limFam (Feps α ρ ε Φs E) h₀ z θ τ
        = h₀ z θ + ∫ s in (0 : ℝ)..τ,
            Feps α ρ ε Φs E (slice (limFam (Feps α ρ ε Φs E) h₀) s) z θ) :
    Work.FTS.StrongEps.EpsE4Thr.E4R5.RegDataD (Feps α ρ ε Φs E) h₀ δ := by
  -- ## the `τ`-Lipschitz bound of the limit curve (from the Picard data)
  obtain ⟨L', hL'pos, hLip⟩ :=
    Work.FTS.StrongEps.EpsE4Thr.LeafD2.limEpsSq_lipschitz (α := α) (C₀ := C₀) (Ce := Ce)
      (Cs := Cs) (M' := M') (Cpt := Cpt) (L := L) (δ := δ) (R := R) (ρ := ρ) (Φs := Φs) (E := E)
      (ε := ε) (h₀ := h₀) hC₀ hα hρ hε hε1 hEll hstar hml hM' hL hδ hδL hR hbd hlip hCpt hpt
      hsmo hmem hM6 hcl hball hdatmem hdatsq hiter
  have hLips : ∃ L'' : ℝ, 0 < L'' ∧ ∀ σ ∈ Set.Icc 0 δ, ∀ τ ∈ Set.Icc 0 δ,
      Work.FTS.StrongEps.EpsMem α (fun z θ =>
        slice (limFam (Feps α ρ ε Φs E) h₀) σ z θ
          - slice (limFam (Feps α ρ ε Φs E) h₀) τ z θ) ∧
      Work.FTS.StrongEps.EpsSq α (fun z θ =>
        slice (limFam (Feps α ρ ε Φs E) h₀) σ z θ
          - slice (limFam (Feps α ρ ε Φs E) h₀) τ z θ) ≤ L'' * (σ - τ) ^ 2 :=
    ⟨L', hL'pos, hLip⟩
  refine ⟨?_, ?_, ?_⟩
  · -- ## the joint continuity of the slab integrand
    exact Work.FTS.StrongEps.EpsE4Thr.LeafD2.hAc_slab (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs)
      (R := R) (ε := ε) (δ := δ) (Cpt := Cpt) (ρ := ρ) (Φs := Φs) (E := E) (h₀ := h₀)
      hα hρ hε hε1 hC₀ hEll hstar hml hδ hR hsmo hlim hvol hCpt hpt hLips
  · -- ## the per-slice `C¹` clause
    intro σ hσ
    exact (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp
      (Work.FTS.EpsEngine.smoothOpen_Feps_of_classC (α := α) (Ce := Ce) (Cs := Cs) (ρ := ρ)
        (Φs := Φs) (E := E) (ε := ε) (u := slice (limFam (Feps α ρ ε Φs E) h₀) σ)
        hα hρ hε hEll hstar (hlim σ hσ).classC) 1
  · -- ## the joint continuity of the spatial `fderiv`
    exact Work.FTS.StrongEps.EpsE4Thr.LeafD2.hB_slab_lip (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs)
      (R := R) (ε := ε) (δ := δ) (Cpt := Cpt) (ρ := ρ) (Φs := Φs) (E := E) (h₀ := h₀)
      hα hρ hε hε1 hC₀ hEll hstar hml hδ hR hsmo hlim hvol hCpt hpt hLips

end Work.FTS.StrongEps.EpsE4Thr.RegDataWired
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.XStepAssemblyD =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `EpsE4Thr/XStepAssemblyD.lean` — `XStepInvariant` over the weaker regularity data (PROVED from
# LEAF-D + LEAF-D2)

curric-46 install 2026-10-12 (REVIEW F2).  `XStepInvariant_of_regD` is a copy of
`XStep.XStepInvariant_of_reg` (`EpsE4Thr/XStepAssembly.lean`, untouched) with
`RegFromVolterra … (RegInterface3 …)` — which over-asks `C¹` in the fake time of
`σ ↦ Feps (w_σ)` — replaced by `regFromVolterra'_of_regData … (regData_of_xball …)` (joint
continuity + continuous spatial derivative only).  The iterate/limit clauses and the Volterra
identity come from `XBallIterExists`, `XBallLimExists`, `VolterraLimFam` as before.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E4R5

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.EpsEngine (XBall Feps)
open Work.FTS.StrongEps.EpsLocalPStar (iter limFam)

set_option autoImplicit false


end Work.FTS.StrongEps.EpsE4Thr.E4R5
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.MainH =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_EllLimOK

open Work.FTS.Galerkin (Fn)
open Work.FTS.Regularity (pExp)

set_option autoImplicit false

/-- **Route (b) input.** -/
abbrev RouteB : Prop :=
  ∃ α₁ : ℝ, 0 < α₁ ∧ ∀ α : ℝ, 0 < α → α ≤ α₁ → ∀ g : Fn,
    Work.FTS.ClassC.ClassC α g → ∃ Ψ : Fn, Work.FTS.EllExist.EllClassOk 8 α g Ψ

/-- **The deliverable `core1_1a3` from route (b), modulo the two in-flight inputs.**  The
conclusion is verbatim the conclusion of the lead's `FinalV2.Producers.core1_1a3`; the hypothesis is
the route-(b) input `hb`. -/
theorem core1_1a3_of_routeB (hprod : RulingELF.ProducerH) (hb : RouteB) :
    ∃ Ce : ℝ, 0 < Ce ∧ ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ, 0 < α →
      pExp α ≤ α₀ → ∃ E : Fn →ₗ[ℝ] Fn,
      (∀ g, Work.FTS.ClassC.ClassC (pExp α) g →
        Work.FTS.VocabO.EllPkgGo (pExp α) Ce g (E g) ∧
          Work.FTS.ClassC.EllPkgK (pExp α) 6 Ce g (E g)) ∧
      Work.FTS.FinalV2.EllLimOK3 (pExp α) E := by
  obtain ⟨Ce, hCe, α₀, hα₀, hPkg8⟩ := RulingELF.existsEllSolC8_of_threshold hb
  obtain ⟨αg, hαg, hprod⟩ := hprod
  obtain ⟨αu, hαu, huniq⟩ := Work.FTS_EllLimOK.UniqG.smallUniq3G_fts
  set Θ : ℝ := min (min (min α₀ αg) αu) (1 / 3) with hΘ
  have hΘpos : 0 < Θ :=
    lt_min (lt_min (lt_min hα₀ hαg) hαu) (by norm_num)
  refine ⟨Ce, hCe, Θ, hΘpos, fun α hα hle => ?_⟩
  have h1 : pExp α ≤ α₀ :=
    le_trans hle (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
  have h2 : pExp α ≤ αg :=
    le_trans hle (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have h3 : pExp α ≤ 1 := by
    have h3' : pExp α ≤ 1 / 3 := le_trans hle (min_le_right _ _)
    rw [Work.FTS.Regularity.pExp_eq] at h3' ⊢
    linarith
  have h4 : pExp α ≤ αu := le_trans hle (le_trans (min_le_left _ _) (min_le_right _ _))
  have hp : 0 < pExp α := Work.FTS.Regularity.pExp_pos hα
  obtain ⟨E, hE8⟩ := hPkg8 (pExp α) hp h1
  obtain ⟨Ce', hCe'pos, hPkgH⟩ := hprod (pExp α) hp h2 Ce E hE8
  -- obligation 1
  have hbd : LocalBoundH (pExp α) (max Ce Ce') :=
    localBoundH_of_hasPkgH (α := pExp α) hp h3
  have hfat : FatouDataH (pExp α) (max Ce Ce') :=
    fatouDataH_of_hasPkgH (α := pExp α) hp
  have hboxd : BoxDataH (pExp α) (max Ce Ce') :=
    (Work.FTS_EllLimOK.BoxDataH.boxDataH_of_hasPkgH (α := pExp α) hp h3)
  have hcomp : ClosedCompact3H (pExp α) (max Ce Ce') :=
    ClosedCompact3H_of_bounds_fatou hbd hfat hboxd
  have hPk : Work.FTS_EllLimOK.HasPkgH (pExp α) (max Ce Ce') E := hPkgH
  -- obligation 1 + obligation 2 ⇒ closure
  have huniq' : ClosedUniq3G (pExp α) := huniq (pExp α) hp h4
  have hcl : ClosedE3G (pExp α) E := ClosedE3H_of_compact3_uniq3 hPk hcomp huniq'
  have hsol : ∀ g, Work.FTS.ClassC.ClassC (pExp α) g →
      Work.FTS.StrongGlobal.IsBslSolPos (pExp α) g (E g) :=
    fun g hg => Work.FTS.StrongGlobal.IsBslSol.toPos (HasPkgH.toHasPkg hPk g hg).1.sol
  have hsm : ∀ g, Work.FTS.ClassC.ClassC (pExp α) g →
      ContDiffOn ℝ 3 (Function.uncurry (E g)) Work.Construction.Qd :=
    fun g hg => contDiffOn_of_smoothOpen (HasPkgH.toHasPkg hPk g hg).1.smooth 3
  -- closure ⇒ `EllLimOK3`
  obtain ⟨E', hE'C, hok⟩ :=
    Work.FTS_EllLimOK.GlueG.exists_ellLimOK3_of_closedG E hsol hsm hcl
  refine ⟨E', fun g hg => ?_, (Lead_EllLimOK3_iff _ E').mp hok⟩
  rw [hE'C g hg]
  exact ⟨(hE8 g hg).2.1, (hE8 g hg).2.2⟩


end Work.FTS_EllLimOK
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.H2.ABlock =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH.H2

set_option autoImplicit false

/-! ## Elementary one-variable tools for the two radial blocks

The four statements below are the elementary inputs of `ABlock` (and of its siblings): the
interior Lipschitz bound of an angular slice from a bound on its `θ`-derivative (mean value
theorem), the extension of that bound to the closed interval from the two endpoint values and
the two endpoint rates, the continuity consequence, and the within-derivatives at the endpoints
of `[0,π/2]` from the one-sided limits of the derivative.  They are stated for a fixed radius
`z` so that the pointwise rate bounds of `BoxData` can be fed in at that radius.
-/

private theorem Mf_eq_zero (N0 N1 : ℝ → ℝ) (Ψ : ℝ → ℝ → ℝ) (z : ℝ) :
    Mf N0 N1 Ψ z 0 = N0 z := by
  simp [Mf]

private theorem Mf_eq_pi (N0 N1 : ℝ → ℝ) (Ψ : ℝ → ℝ → ℝ) (z : ℝ) :
    Mf N0 N1 Ψ z (π / 2) = N1 z := by
  have h0 : ¬ ((π : ℝ) / 2 = 0) := ne_of_gt (by positivity)
  simp [Mf, h0]

private theorem Mf_eq_interior {N0 N1 : ℝ → ℝ} {Ψ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Mf N0 N1 Ψ z θ = Work.Spaces.pth (Work.Spaces.pz Ψ) z θ := by
  have h0 : ¬ (θ = 0) := ne_of_gt hθ.1
  have h1 : ¬ (θ = (π : ℝ) / 2) := ne_of_lt hθ.2
  simp only [Mf, if_neg h0, if_neg h1]

/-- Continuity of the `z`-slice of a function `C^∞` on the open quadrant. -/
theorem continuousOn_zslice_m {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    {a b θ : ℝ} (ha : 0 < a) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    ContinuousOn (fun z => F z θ) (Set.Icc a b) :=
  ((hF.curry_z hθ).continuousOn).mono (fun z hz => lt_of_lt_of_le ha hz.1)

/-- The interior Lipschitz bound for an angular slice from a bound on its `θ`-derivative. -/
theorem abs_slice_theta_le_m {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    {z C : ℝ} (hz : 0 < z)
    (hb : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), |Work.Spaces.pth F z θ| ≤ C) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), ∀ θ' ∈ Set.Ioo (0 : ℝ) (π / 2),
      |F z θ - F z θ'| ≤ C * |θ - θ'| := by
  intro θ hθ θ' hθ'
  have hdiff : ∀ t ∈ Set.Ioo (0 : ℝ) (π / 2), DifferentiableAt ℝ (fun θ'' => F z θ'') t :=
    fun t ht => ((hF.curry_θ hz).differentiableOn (by simp)).differentiableAt
      (isOpen_Ioo.mem_nhds ht)
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun θ'' => F z θ'')
    (s := Set.Ioo (0 : ℝ) (π / 2)) (x := θ') (y := θ) (C := C)
    hdiff (fun t ht => by rw [Real.norm_eq_abs]; exact hb t ht)
    (convex_Ioo 0 (π / 2)) hθ' hθ
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
  exact h

/-- The two endpoint values plus the interior Lipschitz bound plus the two endpoint rates give
the Lipschitz bound on the whole closed angular interval. -/
theorem theta_modulus_Icc_m {F : ℝ → ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M) (z : ℝ)
    (h0 : F z 0 = 0) (hpi : F z (π / 2) = 0)
    (hint : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), ∀ θ' ∈ Set.Ioo (0 : ℝ) (π / 2),
      |F z θ - F z θ'| ≤ M * |θ - θ'|)
    (hr0 : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), |F z θ| ≤ M * θ)
    (hr1 : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), |F z θ| ≤ M * (π / 2 - θ)) :
    ∀ θ ∈ Set.Icc (0 : ℝ) (π / 2), ∀ θ' ∈ Set.Icc (0 : ℝ) (π / 2),
      |F z θ - F z θ'| ≤ M * |θ - θ'| := by
  have hpi2 : (0 : ℝ) < π / 2 := by positivity
  have hf0 : ∀ t ∈ Set.Icc (0 : ℝ) (π / 2), |F z t - F z 0| ≤ M * t := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · subst h
      rw [h0, sub_self, abs_zero]
      nlinarith [hM, Real.pi_pos]
    rcases eq_or_lt_of_le ht.2 with hp | hp
    · subst hp
      rw [h0, hpi, sub_zero, abs_zero]
      nlinarith [hM, Real.pi_pos]
    · rw [h0, sub_zero]
      exact hr0 t ⟨h, hp⟩
  have hfpi : ∀ t ∈ Set.Icc (0 : ℝ) (π / 2), |F z t - F z (π / 2)| ≤ M * (π / 2 - t) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · subst h
      rw [h0, hpi, sub_self, abs_zero]
      nlinarith [hM, Real.pi_pos]
    rcases eq_or_lt_of_le ht.2 with hp | hp
    · subst hp
      rw [hpi, sub_self, abs_zero]
      nlinarith [hM, Real.pi_pos]
    · rw [hpi, sub_zero]
      exact hr1 t ⟨h, hp⟩
  intro θ hθ θ' hθ'
  rcases eq_or_lt_of_le hθ.1 with h | h
  · subst h
    rw [abs_sub_comm (F z 0) (F z θ'), zero_sub, abs_neg, abs_of_nonneg hθ'.1]
    exact hf0 θ' hθ'
  rcases eq_or_lt_of_le hθ.2 with hp | hp
  · subst hp
    rw [abs_sub_comm (F z (π / 2)) (F z θ'),
      abs_of_nonneg (show (0 : ℝ) ≤ π / 2 - θ' by linarith [hθ'.2])]
    exact hfpi θ' hθ'
  rcases eq_or_lt_of_le hθ'.1 with h' | h'
  · subst h'
    rw [sub_zero, abs_of_nonneg hθ.1]
    exact hf0 θ hθ
  rcases eq_or_lt_of_le hθ'.2 with hp' | hp'
  · subst hp'
    have h1 : |θ - (π : ℝ) / 2| = π / 2 - θ := by
      rw [abs_of_nonpos (by linarith [hθ.2]), neg_sub]
    rw [h1]
    exact hfpi θ hθ
  exact hint θ ⟨h, hp⟩ θ' ⟨h', hp'⟩

/-- A Lipschitz bound on the closed angular interval gives continuity there. -/
theorem continuousOn_Icc_of_abs_sub_le_m {f : ℝ → ℝ} {M : ℝ}
    (h : ∀ x ∈ Set.Icc (0 : ℝ) (π / 2), ∀ y ∈ Set.Icc (0 : ℝ) (π / 2),
      |f x - f y| ≤ M * |x - y|) :
    ContinuousOn f (Set.Icc (0 : ℝ) (π / 2)) := by
  have hq : (π : ℝ) / 4 ∈ Set.Icc (0 : ℝ) (π / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  by_cases hM : M ≤ 0
  · have hconst : ∀ x ∈ Set.Icc (0 : ℝ) (π / 2), f x = f (π / 4) := by
      intro x hx
      have h1 := h x hx (π / 4) hq
      have h2 : M * |x - π / 4| ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hM (abs_nonneg _)
      have h3 : |f x - f (π / 4)| = 0 := le_antisymm (le_trans h1 h2) (abs_nonneg _)
      exact sub_eq_zero.mp (abs_eq_zero.mp h3)
    exact (continuousOn_const (c := f (π / 4))).congr (fun x hx => hconst x hx)
  · have hMpos : 0 < M := not_le.mp hM
    intro x hx
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    refine ⟨ε / M, by positivity, fun y hy hd => ?_⟩
    have h1 := h y hy x hx
    have h2 : |y - x| < ε / M := by rwa [Real.dist_eq] at hd
    have h3 : M * |y - x| < ε := by
      have h4 := mul_lt_mul_of_pos_left h2 hMpos
      have h5 : M * (ε / M) = ε := mul_div_cancel₀ ε (ne_of_gt hMpos)
      linarith [h4, h5.le]
    rw [Real.dist_eq]
    exact lt_of_le_of_lt h1 h3

/-- Within-derivative at the left endpoint of `[0,T]` from the one-sided limit of the
derivative. -/
theorem hasDerivWithinAt_Icc_left_m {f f' : ℝ → ℝ} {T L : ℝ} (hT : 0 < T)
    (hcont : ContinuousOn f (Set.Icc 0 T))
    (hd : ∀ x ∈ Set.Ioo 0 T, HasDerivAt f (f' x) x)
    (hL : Filter.Tendsto f' (nhdsWithin 0 (Set.Ioi 0)) (nhds L)) :
    HasDerivWithinAt f L (Set.Icc 0 T) 0 := by
  have hdiff : DifferentiableOn ℝ f (Set.Ioo 0 T) :=
    fun x hx => (hd x hx).differentiableAt.differentiableWithinAt
  have hcont0 : ContinuousWithinAt f (Set.Ioo 0 T) 0 :=
    (hcont.continuousWithinAt (Set.left_mem_Icc.mpr hT.le)).mono Set.Ioo_subset_Icc_self
  have hmem : Set.Ioo 0 T ∈ nhdsWithin 0 (Set.Ioi 0) := Ioo_mem_nhdsGT hT
  have hd' : Filter.Tendsto (fun x => deriv f x) (nhdsWithin 0 (Set.Ioi 0)) (nhds L) :=
    hL.congr' (Filter.eventually_of_mem hmem fun x hx => (hd x hx).deriv.symm)
  exact (hasDerivWithinAt_Ici_of_tendsto_deriv hdiff hcont0 hmem hd').mono
    (fun x hx => hx.1)

/-- Within-derivative at the right endpoint of `[0,T]` from the one-sided limit of the
derivative. -/
theorem hasDerivWithinAt_Icc_right_m {f f' : ℝ → ℝ} {T L : ℝ} (hT : 0 < T)
    (hcont : ContinuousOn f (Set.Icc 0 T))
    (hd : ∀ x ∈ Set.Ioo 0 T, HasDerivAt f (f' x) x)
    (hL : Filter.Tendsto f' (nhdsWithin T (Set.Iio T)) (nhds L)) :
    HasDerivWithinAt f L (Set.Icc 0 T) T := by
  have hdiff : DifferentiableOn ℝ f (Set.Ioo 0 T) :=
    fun x hx => (hd x hx).differentiableAt.differentiableWithinAt
  have hcontT : ContinuousWithinAt f (Set.Ioo 0 T) T :=
    (hcont.continuousWithinAt (Set.right_mem_Icc.mpr hT.le)).mono Set.Ioo_subset_Icc_self
  have hmem : Set.Ioo 0 T ∈ nhdsWithin T (Set.Iio T) := Ioo_mem_nhdsLT hT
  have hd' : Filter.Tendsto (fun x => deriv f x) (nhdsWithin T (Set.Iio T)) (nhds L) :=
    hL.congr' (Filter.eventually_of_mem hmem fun x hx => (hd x hx).deriv.symm)
  exact (hasDerivWithinAt_Iic_of_tendsto_deriv hdiff hcontT hmem hd').mono
    (fun x hx => hx.2)

theorem ABlock {α Ce : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hE : Work.FTS_EllLimOK.ProducerH.H2.Ctx α Ce E) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hdata : Work.FTS_EllLimOK.ProducerH.H2.BoxData α Ce E a b)
    (g : Work.FTS.Galerkin.Fn) (hg : Work.FTS.ClassC.ClassC α g)
    {C : ℝ} {L0 N0 L1 N1 : ℝ → ℝ}
    (hLim : Work.FTS_EllLimOK.ProducerH.H2.LimitsAt (E g) (Work.FTS.StrongGlobal.Xn6 α g) C a b
      L0 N0 L1 N1) :
    ContinuousOn (Function.uncurry (Work.Spaces.pz (E g))) (Work.FTS_EllLimOK.cbox a b) ∧
    ContinuousOn (Function.uncurry (Work.Spaces.pz (Work.Spaces.pz (E g))))
      (Work.FTS_EllLimOK.cbox a b) ∧
    (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2),
      HasDerivWithinAt (fun z' => Work.Spaces.pz (E g) z' θ)
        (Work.Spaces.pz (Work.Spaces.pz (E g)) z θ) (Set.Icc a b) z) ∧
    (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2),
      HasDerivWithinAt (fun θ' => Work.Spaces.pz (E g) z θ')
        (Work.FTS_EllLimOK.ProducerH.H2.Mf N0 N1 (E g) z θ) (Set.Icc 0 (π / 2)) θ) := by
  obtain ⟨K, hK, β, hβ, hmod, hrates, hlimr, hhol⟩ := hdata
  obtain ⟨Cb, hCb, hratesb⟩ := hrates
  have hbsl : Work.Elliptic.IsBslSol α g (E g) := (hE g hg).1.1
  have hSm : Work.FTS.EllipticEst.SmoothOpen (E g) := (hE g hg).1.2.1
  have hval0 : ∀ z : ℝ, (E g) z 0 = 0 := hbsl.2.1
  have hval1 : ∀ z : ℝ, (E g) z (π / 2) = 0 := hbsl.2.2.1
  have hX0 : 0 ≤ Work.FTS.StrongGlobal.Xn6 α g := Xn6_nonneg α g
  have hM0 : 0 ≤ Cb * Work.FTS.StrongGlobal.Xn6 α g := mul_nonneg hCb.le hX0
  have hpi2 : (0 : ℝ) < π / 2 := by positivity
  -- the endpoint values of the two radial primitives
  have hpz0 : ∀ z : ℝ, Work.Spaces.pz (E g) z 0 = 0 := by
    intro z
    have hfun : (fun z' => (E g) z' 0) = fun _ => (0 : ℝ) := funext hval0
    rw [Work.Spaces.pz, hfun, deriv_const]
  have hpzpi : ∀ z : ℝ, Work.Spaces.pz (E g) z (π / 2) = 0 := by
    intro z
    have hfun : (fun z' => (E g) z' (π / 2)) = fun _ => (0 : ℝ) := funext hval1
    rw [Work.Spaces.pz, hfun, deriv_const]
  have hpzpz0 : ∀ z : ℝ, Work.Spaces.pz (Work.Spaces.pz (E g)) z 0 = 0 := by
    intro z
    have hfun : (fun z' => Work.Spaces.pz (E g) z' 0) = fun _ => (0 : ℝ) := funext hpz0
    rw [Work.Spaces.pz, hfun, deriv_const]
  have hpzpzpi : ∀ z : ℝ, Work.Spaces.pz (Work.Spaces.pz (E g)) z (π / 2) = 0 := by
    intro z
    have hfun : (fun z' => Work.Spaces.pz (E g) z' (π / 2)) = fun _ => (0 : ℝ) := funext hpzpi
    rw [Work.Spaces.pz, hfun, deriv_const]
  -- the angular Lipschitz bounds on the closed interval
  have hmodpz : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2), ∀ θ' ∈ Set.Icc 0 (π / 2),
      |Work.Spaces.pz (E g) z θ - Work.Spaces.pz (E g) z θ'|
        ≤ (Cb * Work.FTS.StrongGlobal.Xn6 α g) * |θ - θ'| := by
    intro z hz
    refine theta_modulus_Icc_m hM0 z (hpz0 z) (hpzpi z) ?_ ?_ ?_
    · intro θ hθ θ' hθ'
      have hb : ∀ t ∈ Set.Ioo (0 : ℝ) (π / 2),
          |Work.Spaces.pth (Work.Spaces.pz (E g)) z t| ≤ Cb * Work.FTS.StrongGlobal.Xn6 α g := by
        intro t ht
        obtain ⟨_, _, _, h4, _, _, _, _, _, _, _, _, _, _⟩ := hratesb g hg z hz t ht
        exact h4
      exact abs_slice_theta_le_m hSm.pz (lt_of_lt_of_le ha hz.1) hb θ hθ θ' hθ'
    · intro θ hθ
      obtain ⟨_, _, _, _, _, _, _, _, h9, _, _, _, _, _⟩ := hratesb g hg z hz θ hθ
      exact h9
    · intro θ hθ
      obtain ⟨_, _, _, _, _, _, _, _, _, _, h11, _, _, _⟩ := hratesb g hg z hz θ hθ
      exact h11
  have hmodpzpz : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2), ∀ θ' ∈ Set.Icc 0 (π / 2),
      |Work.Spaces.pz (Work.Spaces.pz (E g)) z θ - Work.Spaces.pz (Work.Spaces.pz (E g)) z θ'|
        ≤ (Cb * Work.FTS.StrongGlobal.Xn6 α g) * |θ - θ'| := by
    intro z hz
    refine theta_modulus_Icc_m hM0 z (hpzpz0 z) (hpzpzpi z) ?_ ?_ ?_
    · intro θ hθ θ' hθ'
      have hb : ∀ t ∈ Set.Ioo (0 : ℝ) (π / 2),
          |Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pz (E g))) z t|
            ≤ Cb * Work.FTS.StrongGlobal.Xn6 α g := by
        intro t ht
        obtain ⟨_, _, _, _, _, _, h7, _, _, _, _, _, _, _⟩ := hratesb g hg z hz t ht
        exact h7
      exact abs_slice_theta_le_m hSm.pz.pz (lt_of_lt_of_le ha hz.1) hb θ hθ θ' hθ'
    · intro θ hθ
      obtain ⟨_, _, _, _, _, _, _, _, _, h10, _, _, _, _⟩ := hratesb g hg z hz θ hθ
      exact h10
    · intro θ hθ
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, h12, _, _⟩ := hratesb g hg z hz θ hθ
      exact h12
  -- continuity on the closed box
  have hcontpz : ContinuousOn (Function.uncurry (Work.Spaces.pz (E g))) (cbox a b) := by
    refine Work.FTS_EllLimOK.ProducerH.BoxAux.continuousOn_of_thetaModulus
      (a₀ := a) (b₀ := b) (C := Cb * Work.FTS.StrongGlobal.Xn6 α g) (β := 1) one_pos ?_ ?_
    · intro z hz θ hθ θ' hθ'
      rw [Real.rpow_one]
      exact hmodpz z hz θ hθ θ' hθ'
    · intro θ hθ
      exact continuousOn_zslice_m hSm.pz ha hθ
  have hcontpzpz : ContinuousOn (Function.uncurry (Work.Spaces.pz (Work.Spaces.pz (E g))))
      (cbox a b) := by
    refine Work.FTS_EllLimOK.ProducerH.BoxAux.continuousOn_of_thetaModulus
      (a₀ := a) (b₀ := b) (C := Cb * Work.FTS.StrongGlobal.Xn6 α g) (β := 1) one_pos ?_ ?_
    · intro z hz θ hθ θ' hθ'
      rw [Real.rpow_one]
      exact hmodpzpz z hz θ hθ θ' hθ'
    · intro θ hθ
      exact continuousOn_zslice_m hSm.pz.pz ha hθ
  -- the angular slices of the two primitives are continuous on the closed interval
  have hcontθ : ∀ z ∈ Set.Icc a b,
      ContinuousOn (fun θ' => Work.Spaces.pz (E g) z θ') (Set.Icc 0 (π / 2)) :=
    fun z hz => continuousOn_Icc_of_abs_sub_le_m (fun x hx y hy => hmodpz z hz x hx y hy)
  -- the radial within-derivative
  have hzderiv : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2),
      HasDerivWithinAt (fun z' => Work.Spaces.pz (E g) z' θ)
        (Work.Spaces.pz (Work.Spaces.pz (E g)) z θ) (Set.Icc a b) z := by
    intro z hz θ hθ
    have hz0 : 0 < z := lt_of_lt_of_le ha hz.1
    rcases eq_or_lt_of_le hθ.1 with h | h
    · subst h
      have hfun : (fun z' => Work.Spaces.pz (E g) z' 0) = fun _ => (0 : ℝ) := funext hpz0
      rw [hfun, hpzpz0 z]
      exact hasDerivWithinAt_const z (Set.Icc a b) 0
    rcases eq_or_lt_of_le hθ.2 with hp | hp
    · subst hp
      have hfun : (fun z' => Work.Spaces.pz (E g) z' (π / 2)) = fun _ => (0 : ℝ) := funext hpzpi
      rw [hfun, hpzpzpi z]
      exact hasDerivWithinAt_const z (Set.Icc a b) 0
    · exact ((hSm.pz).hasDerivAt_slice ⟨h, hp⟩ hz0).hasDerivWithinAt
  -- the angular within-derivative
  have hthderiv : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2),
      HasDerivWithinAt (fun θ' => Work.Spaces.pz (E g) z θ')
        (Mf N0 N1 (E g) z θ) (Set.Icc 0 (π / 2)) θ := by
    intro z hz θ hθ
    have hz0 : 0 < z := lt_of_lt_of_le ha hz.1
    have hCd : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ' => Work.Spaces.pz (E g) z θ')
        (Set.Ioo 0 (π / 2)) := (hSm.pz).curry_θ hz0
    have hd : ∀ x ∈ Set.Ioo (0 : ℝ) (π / 2),
        HasDerivAt (fun θ' => Work.Spaces.pz (E g) z θ')
          (Work.Spaces.pth (Work.Spaces.pz (E g)) z x) x := fun x hx =>
      (hCd.differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hx) |>.hasDerivAt
    have hcl : ∀ x ∈ Set.Ioo (0 : ℝ) (π / 2),
        Work.Spaces.pz (Work.Spaces.pth (E g)) z x
          = Work.Spaces.pth (Work.Spaces.pz (E g)) z x := fun x hx =>
      Work.Spaces.pz_pth_comm (((hSm.forall 2)).contDiffAt
        (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
          (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz0, hx.1, hx.2⟩)))
    have hL0 : Filter.Tendsto (fun x => Work.Spaces.pth (Work.Spaces.pz (E g)) z x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (N0 z)) :=
      (hLim.2.2.1 z hz).congr' (Filter.eventually_of_mem (Ioo_mem_nhdsGT hpi2) hcl)
    have hL1 : Filter.Tendsto (fun x => Work.Spaces.pth (Work.Spaces.pz (E g)) z x)
        (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhds (N1 z)) :=
      (hLim.2.2.2.2.2.2.1 z hz).congr' (Filter.eventually_of_mem (Ioo_mem_nhdsLT hpi2) hcl)
    rcases eq_or_lt_of_le hθ.1 with h | h
    · subst h
      rw [Mf_eq_zero]
      exact hasDerivWithinAt_Icc_left_m hpi2 (hcontθ z hz) hd hL0
    rcases eq_or_lt_of_le hθ.2 with hp | hp
    · subst hp
      rw [Mf_eq_pi]
      exact hasDerivWithinAt_Icc_right_m hpi2 (hcontθ z hz) hd hL1
    · rw [Mf_eq_interior ⟨h, hp⟩]
      exact (hd θ ⟨h, hp⟩).hasDerivWithinAt
  exact ⟨hcontpz, hcontpzpz, hzderiv, hthderiv⟩

end Work.FTS_EllLimOK.ProducerH.H2
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.H2.PsiBlock =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH.H2

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- **Continuity of `F` on the closed box from an angular `min θ (π/2-θ)`-rate.**

`F` is continuous on the open quadrant (this is the hypothesis `hint`, at the interior points),
vanishes on the two boundary lines `θ = 0` and `θ = π/2` (hypotheses `h0`, `hpi`) and is
dominated by `C · min θ (π/2-θ)` on the open strip (`hbound`).  The rate controls the two
boundary lines *uniformly in `z`*, which is exactly what is needed for continuity there; the
interior is open. -/
theorem continuousOn_cbox_of_min_rate {F : ℝ → ℝ → ℝ} {a b C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo 0 (π / 2),
      |F z θ| ≤ C * min θ (π / 2 - θ))
    (hint : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo 0 (π / 2),
      ContinuousWithinAt (Function.uncurry F) (Work.FTS_EllLimOK.cbox a b) (z, θ))
    (h0 : ∀ z, F z 0 = 0) (hpi : ∀ z, F z (π / 2) = 0) :
    ContinuousOn (Function.uncurry F) (Work.FTS_EllLimOK.cbox a b) := by
  -- the numerical facts used at both boundary lines
  have hquot : C / (C + 1) < 1 := by
    rw [div_lt_one (by linarith : (0 : ℝ) < C + 1)]
    linarith
  have hfinal : ∀ ε : ℝ, 0 < ε → C * (ε / (C + 1)) < ε := by
    intro ε hε
    have h1 : C * (ε / (C + 1)) = ε * (C / (C + 1)) := by ring
    rw [h1]
    calc ε * (C / (C + 1)) < ε * 1 := mul_lt_mul_of_pos_left hquot hε
      _ = ε := mul_one ε
  intro p hp
  obtain ⟨z, θ⟩ := p
  rw [Work.FTS_EllLimOK.mem_cbox] at hp
  obtain ⟨hz, hθ⟩ := hp
  rcases eq_or_lt_of_le hθ.1 with hθ0 | hθ0
  · -- ## the lower boundary line `θ = 0`
    subst hθ0
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    refine ⟨ε / (C + 1), by positivity, fun q hq hdist => ?_⟩
    obtain ⟨z', θ'⟩ := q
    rw [Work.FTS_EllLimOK.mem_cbox] at hq
    obtain ⟨hz', hθ'⟩ := hq
    have hdd : dist (z', θ') (z, 0) = max |z' - z| |θ' - 0| := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    have hthlt : |θ' - 0| < ε / (C + 1) := by
      rw [hdd] at hdist
      exact lt_of_le_of_lt (le_max_right _ _) hdist
    simp only [Function.uncurry_apply_pair]
    rw [Real.dist_eq]
    rcases eq_or_lt_of_le hθ'.1 with h1 | h1
    · subst h1
      simpa only [h0, sub_zero, abs_zero] using hε
    rcases eq_or_lt_of_le hθ'.2 with h2 | h2
    · subst h2
      simpa only [h0, hpi, sub_zero, abs_zero] using hε
    have hb := hbound z' hz' θ' ⟨h1, h2⟩
    have hstep : |F z' θ'| ≤ C * θ' :=
      le_trans hb (mul_le_mul_of_nonneg_left (min_le_left _ _) hC)
    have hθ'lt : θ' < ε / (C + 1) := by
      rw [sub_zero, abs_of_pos h1] at hthlt
      exact hthlt
    have hCθ : C * θ' < ε := by
      have hmul : C * θ' ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left hθ'lt.le hC
      linarith [hmul, hfinal ε hε]
    rw [h0, sub_zero]
    exact lt_of_le_of_lt hstep hCθ
  · rcases eq_or_lt_of_le hθ.2 with hθp | hθp
    · -- ## the upper boundary line `θ = π/2`
      subst hθp
      rw [Metric.continuousWithinAt_iff]
      intro ε hε
      refine ⟨ε / (C + 1), by positivity, fun q hq hdist => ?_⟩
      obtain ⟨z', θ'⟩ := q
      rw [Work.FTS_EllLimOK.mem_cbox] at hq
      obtain ⟨hz', hθ'⟩ := hq
      have hdd : dist (z', θ') (z, π / 2) = max |z' - z| |θ' - π / 2| := by
        rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      have hthlt : |θ' - π / 2| < ε / (C + 1) := by
        rw [hdd] at hdist
        exact lt_of_le_of_lt (le_max_right _ _) hdist
      simp only [Function.uncurry_apply_pair]
      rw [Real.dist_eq]
      rcases eq_or_lt_of_le hθ'.1 with h1 | h1
      · subst h1
        simpa only [hpi, h0, sub_zero, abs_zero] using hε
      rcases eq_or_lt_of_le hθ'.2 with h2 | h2
      · subst h2
        simpa only [hpi, sub_zero, abs_zero] using hε
      have hb := hbound z' hz' θ' ⟨h1, h2⟩
      have hstep : |F z' θ'| ≤ C * (π / 2 - θ') :=
        le_trans hb (mul_le_mul_of_nonneg_left (min_le_right _ _) hC)
      have hnear : π / 2 - θ' ≤ |θ' - π / 2| := by
        rw [abs_sub_comm]
        exact le_abs_self _
      have hCθ : C * (π / 2 - θ') < ε := by
        have hmul : C * (π / 2 - θ') ≤ C * |θ' - π / 2| :=
          mul_le_mul_of_nonneg_left hnear hC
        have habs : C * |θ' - π / 2| ≤ C * (ε / (C + 1)) :=
          mul_le_mul_of_nonneg_left hthlt.le hC
        linarith [hmul, habs, hfinal ε hε]
      rw [hpi, sub_zero]
      exact lt_of_le_of_lt hstep hCθ
    · -- ## an interior point: `F` is continuous there on the open quadrant
      exact hint z hz θ ⟨hθ0, hθp⟩

theorem PsiBlock {α Ce : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hE : Work.FTS_EllLimOK.ProducerH.H2.Ctx α Ce E) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hdata : Work.FTS_EllLimOK.ProducerH.H2.BoxData α Ce E a b)
    (g : Work.FTS.Galerkin.Fn) (hg : Work.FTS.ClassC.ClassC α g)
    {C : ℝ} {L0 N0 L1 N1 : ℝ → ℝ}
    (hLim : Work.FTS_EllLimOK.ProducerH.H2.LimitsAt (E g) (Work.FTS.StrongGlobal.Xn6 α g) C a b
      L0 N0 L1 N1) :
    ContinuousOn (Function.uncurry (E g)) (Work.FTS_EllLimOK.cbox a b) ∧
    (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2),
      HasDerivWithinAt (fun z' => (E g) z' θ) (Work.Spaces.pz (E g) z θ) (Set.Icc a b) z) ∧
    (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2),
      HasDerivWithinAt (fun θ' => (E g) z θ')
        (Work.FTS_EllLimOK.ProducerH.H2.Bf L0 L1 (E g) z θ) (Set.Icc 0 (π / 2)) θ) := by
  -- ## the class data
  obtain ⟨hO, -, -⟩ := hE g hg
  have hSsm : Work.FTS.EllipticEst.SmoothOpen (E g) := hO.2.1
  have hsol : Work.Elliptic.IsBslSol α g (E g) := hO.1
  have h0v : ∀ z, (E g) z 0 = 0 := hsol.2.1
  have hpiv : ∀ z, (E g) z (π / 2) = 0 := hsol.2.2.1
  -- ## the frozen endpoint limits
  obtain ⟨hT0, _, _, _, hT1, _, _, _, _, _, _, _, _, _⟩ := hLim
  -- ## the angular rate of `E g` (the `j = 0` instance of the pointwise radial bounds)
  obtain ⟨Cp, hCppos, hCp⟩ :=
    Work.FTS_EllLimOK.ProducerH.BoxAux.psiDz_rate hα hα4 hE ha hab.le
  have hrate : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo 0 (π / 2),
      |(E g) z θ| ≤ (Cp * Work.FTS.StrongGlobal.Xn6 α g) * min θ (π / 2 - θ) := by
    intro z hz θ hθ
    have h := hCp g hg 0 (by norm_num) z hz θ hθ
    simpa using h
  refine ⟨?_, ?_, ?_⟩
  · -- ## (1) continuity on the box
    refine continuousOn_cbox_of_min_rate
      (mul_nonneg hCppos.le (Xn6_nonneg α g)) hrate ?_ h0v hpiv
    intro z hz θ hθ
    have hz0 : 0 < z := lt_of_lt_of_le ha hz.1
    have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
      Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz0, hθ.1, hθ.2⟩
    exact ((hSsm.continuousOn.continuousWithinAt hmem).continuousAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)).continuousWithinAt
  · -- ## (2) the `z`-within-derivative of the radial slice
    intro z hz θ hθ
    have hz0 : 0 < z := lt_of_lt_of_le ha hz.1
    rcases eq_or_lt_of_le hθ.1 with h | h
    · subst h
      have hzid : (fun z' => (E g) z' 0) = fun _ => (0 : ℝ) := funext h0v
      have hpz : Work.Spaces.pz (E g) z 0 = 0 := by
        simp only [Work.Spaces.pz]
        rw [hzid]
        simp
      rw [hzid, hpz]
      exact hasDerivWithinAt_const z (Set.Icc a b) (0 : ℝ)
    rcases eq_or_lt_of_le hθ.2 with hp | hp
    · subst hp
      have hzid : (fun z' => (E g) z' (π / 2)) = fun _ => (0 : ℝ) := funext hpiv
      have hpz : Work.Spaces.pz (E g) z (π / 2) = 0 := by
        simp only [Work.Spaces.pz]
        rw [hzid]
        simp
      rw [hzid, hpz]
      exact hasDerivWithinAt_const z (Set.Icc a b) (0 : ℝ)
    · exact (hSsm.hasDerivAt_slice ⟨h, hp⟩ hz0).hasDerivWithinAt
  · -- ## (3) the `θ`-within-derivative of the angular slice
    intro z hz θ hθ
    have hz0 : 0 < z := lt_of_lt_of_le ha hz.1
    have hcont : ContinuousOn (fun θ' => (E g) z θ') (Set.Icc 0 (π / 2)) :=
      sliceContinuousOn hα hα4 hE hg hz0
    have hslice : ContDiffOn ℝ 2 (fun θ' => (E g) z θ') (Set.Ioo 0 (π / 2)) :=
      (hSsm.curry_θ hz0).of_le (by norm_num)
    have hdiff : ∀ x ∈ Set.Ioo (0 : ℝ) (π / 2),
        HasDerivAt (fun θ' => (E g) z θ') (Work.Spaces.pth (E g) z x) x := by
      intro x hx
      exact ((hslice.contDiffAt (isOpen_Ioo.mem_nhds hx)).differentiableAt (by norm_num)).hasDerivAt
    rcases eq_or_lt_of_le hθ.1 with h | h
    · subst h
      rw [Bf_zero]
      exact hasDerivWithinAt_Icc_left (f := fun θ' => (E g) z θ')
        (f' := fun x => Work.Spaces.pth (E g) z x) (T := π / 2) (L := L0 z)
        (by positivity) hcont hdiff (hT0 z hz)
    rcases eq_or_lt_of_le hθ.2 with hp | hp
    · subst hp
      rw [Bf_pi]
      exact hasDerivWithinAt_Icc_right (f := fun θ' => (E g) z θ')
        (f' := fun x => Work.Spaces.pth (E g) z x) (T := π / 2) (L := L1 z)
        (by positivity) hcont hdiff (hT1 z hz)
    · rw [Bf_of_mem_Ioo ⟨h, hp⟩]
      exact (((hslice.contDiffAt (isOpen_Ioo.mem_nhds ⟨h, hp⟩)).differentiableAt
        (by norm_num)).hasDerivAt).hasDerivWithinAt

end Work.FTS_EllLimOK.ProducerH.H2
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.H2.bounds_rates =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH.H2

set_option autoImplicit false

/-- **The full box bound of the L3 producer.**  The fourteen bounds of `bounds_rates` split into
the `∂_z`-clauses (`bounds_rates_z`, from the radial rate `psiDz_rate` divided by `z ≥ a₀`) and the
`∂_θ`-clauses (`bounds_rates_theta`, from the value at the midpoint `θ = π/4` together with the
interpolation inequality and the plain second angular derivatives).  The two constants are simply
added. -/
theorem bounds_rates {α Ce : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hE : Work.FTS_EllLimOK.ProducerH.H2.Ctx α Ce E) {a₀ b₀ : ℝ} (ha₀ : 0 < a₀) (hab : a₀ ≤ b₀)
    {K β : ℝ} (hK : 0 < K) (hβ : 0 < β)
    (hmod : ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α g → ∀ z ∈ Set.Icc a₀ b₀,
      ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |deriv (deriv (fun θ' => (E g) z θ')) θ|
          ≤ K * Work.FTS.StrongGlobal.Xn6 α g * (min θ (Real.pi / 2 - θ)) ^ β) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α g →
      ∀ z ∈ Set.Icc a₀ b₀, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |Work.Spaces.pz (E g) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
        |Work.Spaces.pth (E g) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
        |Work.Spaces.pz (Work.Spaces.pz (E g)) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
        |Work.Spaces.pth (Work.Spaces.pz (E g)) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
        |Work.Spaces.pz (Work.Spaces.pth (E g)) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
        |Work.Spaces.pth (Work.Spaces.pth (E g)) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
        |Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pz (E g))) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
        |Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.pz (E g))) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
        |Work.Spaces.pz (E g) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g * θ ∧
        |Work.Spaces.pz (Work.Spaces.pz (E g)) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g * θ ∧
        |Work.Spaces.pz (E g) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g * (Real.pi / 2 - θ) ∧
        |Work.Spaces.pz (Work.Spaces.pz (E g)) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g * (Real.pi / 2 - θ) ∧
        |Work.Spaces.pth (Work.Spaces.pth (E g)) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g * θ ^ β ∧
        |Work.Spaces.pth (Work.Spaces.pth (E g)) z θ|
          ≤ C * Work.FTS.StrongGlobal.Xn6 α g * (Real.pi / 2 - θ) ^ β := by
  obtain ⟨Cz, _hCzpos, hCz⟩ := bounds_rates_z hα hα4 hE ha₀ hab
  obtain ⟨Ct, _hCtpos, hCt⟩ := bounds_rates_theta hα hα4 hE ha₀ hab hK hβ hmod
  refine ⟨Cz + Ct, by positivity, ?_⟩
  intro g hg z hz θ hθ
  obtain ⟨h1, h3, h9, h10, h11, h12⟩ := hCz g hg z hz θ hθ
  obtain ⟨h2, h4, h5, h6, h7, h8, h13, h14⟩ := hCt g hg z hz θ hθ
  have hX0 : 0 ≤ Work.FTS.StrongGlobal.Xn6 α g := Xn6_nonneg α g
  have hgen : ∀ a f : ℝ, 0 ≤ f → a ≤ Cz * Work.FTS.StrongGlobal.Xn6 α g * f →
      a ≤ (Cz + Ct) * Work.FTS.StrongGlobal.Xn6 α g * f := by
    intro a f hf ha
    calc a ≤ Cz * Work.FTS.StrongGlobal.Xn6 α g * f := ha
      _ ≤ (Cz + Ct) * Work.FTS.StrongGlobal.Xn6 α g * f := by
          apply mul_le_mul_of_nonneg_right _ hf
          exact mul_le_mul_of_nonneg_right (by linarith) hX0
  have hgenT : ∀ a f : ℝ, 0 ≤ f → a ≤ Ct * Work.FTS.StrongGlobal.Xn6 α g * f →
      a ≤ (Cz + Ct) * Work.FTS.StrongGlobal.Xn6 α g * f := by
    intro a f hf ha
    calc a ≤ Ct * Work.FTS.StrongGlobal.Xn6 α g * f := ha
      _ ≤ (Cz + Ct) * Work.FTS.StrongGlobal.Xn6 α g * f := by
          apply mul_le_mul_of_nonneg_right _ hf
          exact mul_le_mul_of_nonneg_right (by linarith) hX0
  have hgen1 : ∀ a : ℝ, a ≤ Cz * Work.FTS.StrongGlobal.Xn6 α g →
      a ≤ (Cz + Ct) * Work.FTS.StrongGlobal.Xn6 α g := fun a ha =>
    le_trans ha (mul_le_mul_of_nonneg_right (by linarith) hX0)
  have hgenT1 : ∀ a : ℝ, a ≤ Ct * Work.FTS.StrongGlobal.Xn6 α g →
      a ≤ (Cz + Ct) * Work.FTS.StrongGlobal.Xn6 α g := fun a ha =>
    le_trans ha (mul_le_mul_of_nonneg_right (by linarith) hX0)
  have hθ0 : 0 ≤ θ := hθ.1.le
  have hπ0 : 0 ≤ Real.pi / 2 - θ := by linarith [hθ.2]
  exact ⟨hgen1 _ h1,
    hgenT1 _ h2,
    hgen1 _ h3,
    hgenT1 _ h4,
    hgenT1 _ h5,
    hgenT1 _ h6,
    hgenT1 _ h7,
    hgenT1 _ h8,
    hgen _ θ hθ0 h9,
    hgen _ θ hθ0 h10,
    hgen _ (Real.pi / 2 - θ) hπ0 h11,
    hgen _ (Real.pi / 2 - θ) hπ0 h12,
    hgenT _ (θ ^ β) (Real.rpow_nonneg hθ0 β) h13,
    hgenT _ ((Real.pi / 2 - θ) ^ β) (Real.rpow_nonneg hπ0 β) h14⟩

end Work.FTS_EllLimOK.ProducerH.H2
end
end
