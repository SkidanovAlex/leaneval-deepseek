import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.StrongEps.EpsE4Thr.XBallLimExists
import Submission.Work.FTS.StrongEps.EpsE4Thr.LeafD2.limEpsSq_lipschitz
import Submission.Work.FTS.StrongEps.EpsE4Thr.LeafD2.hAc_slab
import Submission.Work.FTS.StrongEps.EpsE4Thr.LeafD2.hB_slab_lip
import Submission.Work.FTS.StrongEps.EpsE4Thr.RegFromVolterraD

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
