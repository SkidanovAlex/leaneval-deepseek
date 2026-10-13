/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/DiagCurveI_JfamP.lean` — the producer of the `L²`-route
bundle for a slot of the projected mollified family

This assembles the `DiagCurveI` bundle of a slot `D_z^a D_θ^b` of the projected `P₀`-scheme from
the analytic data of the flow:

* `ρmeas`, `ρnn` — `rhoC_meas_nonneg`;
* `int_diag`, `int_diagd`, `int_cross` — `integrable_cross_slot_rpow` (the diagonal/off-diagonal
  `mup`-integrability of a slot pairing against `w²σ^c`);
* `deriv` — `SlotDerivAll.ae_hasDerivAt_mixed_JfamP` (the a.e. slot chain rule of the projected
  family at every interior fake time);
* `bdd` — `EnergyFinalAssembly.slot_L2_uniform_le` (the uniform `ℋ⁴`-bound of the derivative
  family) together with a uniform `ℋ⁴`-size bound on the right-hand side
  (`HkNorm_epsRHSP_le`).

The three fields that are **not** produced here are exactly the interface obligations recorded in
`NOTES_EpsE4Thr_session4.md` §2/§3:

* `aesm`, `aesmd` — *joint* a.e. strong measurability of `(s,p) ↦ (slot of the family at s)(p)`,
  for the **horizon-restricted** measure `(volume.restrict (Icc 0 T)).prod mup`.  The restriction is
  necessary: the family is only constrained on `Icc 0 T`, so the full product `volume.prod mup`
  would make the hypothesis unprovable (`AesmRestrict.lean` records the exact reason, and
  `AesmRestrict.hasDerivAt_integral_diag_var_ioo_restricted` shows that this weaker hypothesis is
  what the `L²`-route actually consumes).  Note `Set.Icc (0:ℝ)` is really `Set.Icc (0:ℝ) T`;
* `contU` — the `L²`-continuity of the derivative slot at `τ`, which the RHS-Lipschitz estimate
  `EpsLocalPStar/EpsRHSPLipX` supplies.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.SlotDerivAll
import Submission.Work.FTS.StrongEps.EpsE4Thr.EnergyFinalAssembly
import Submission.Work.FTS.StrongEps.EpsE4Thr.rhoC_meas_nonneg
import Submission.Work.FTS.StrongEps.EpsE4Thr.integrable_cross_slot_rpow
import Submission.Work.FTS.StrongEps.EpsE4Thr.AesmJfamP
import Submission.Work.FTS.StrongEps.EpsE4Thr.JepsJoint.mixed_fam_continuous_Icc
import Submission.Work.FTS.StrongEps.EpsE4Thr.JepsJoint.hbdd_of_joint_continuous
import Submission.Work.FTS.StrongEps.PZeroAux.PzJepsHkMem
import Submission.Work.FTS.StrongEps.EpsSqTools.LinAux.LinPartArith
import Submission.Work.FTS.StrongEps.EpsE4Thr.JepsJoint.integrable_jker_fam
import Submission.Work.FTS.StrongEps.EpsE4Thr.SlotHkGen.slot_L2_uniform_le_mixed
import Submission.Work.FTS.StrongEps.EpsE4Thr.SlotHkGen.integrable_cross_slot_rpow_mixed

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
set_option maxHeartbeats 2000000

/-- **The `L²`-route bundle of a slot of the projected mollified family.** -/
theorem DiagCurveI_JfamP {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {α T ε c : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn} {g : Fam} {τ : ℝ} {a b : ℕ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hε : 0 < ε) (hab : a + b ≤ 4)
    (hc : -(Work.Spaces.gam α) ≤ c) (hcη : b = 0 → -(Work.Spaces.eta) ≤ c)
    (hτIoo : τ ∈ Set.Ioo (0 : ℝ) T)
    (hsol : IsEpsSolP α ρ ε T Φs E g₀ g)
    (hreg : ∀ n : ℕ, ContDiffOn ℝ n (fun q : ℝ × (ℝ × ℝ) => g q.2.1 q.2.2 q.1)
      (Set.Icc (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad))
    (hregR : ∀ n : ℕ, ContDiffOn ℝ n (fun q : ℝ × (ℝ × ℝ) =>
      epsRHSP α ρ ε Φs E g q.1 q.2.1 q.2.2)
      (Set.Icc (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad))
    (hmem0 : ∀ s ∈ Set.Icc 0 T, Work.Spaces.HkMem α 4 (slice g s))
    (hmem0R : ∀ s ∈ Set.Icc 0 T, Work.Spaces.HkMem α 4 (epsRHSP α ρ ε Φs E g s))
    (hbdU : ∀ r : ℝ, 0 < r → ∃ C : ℝ, 0 ≤ C ∧ ∀ θ' ∈ Set.Ioo 0 (Real.pi / 2),
      ∀ p : ℝ × ℝ, ‖p‖ ≤ ε → ∀ s ∈ Set.Icc 0 T,
        |epsRHSP α ρ ε Φs E g s (Work.FTS.StrongEps.zShift r p.1)
          (Work.FTS.StrongEps.thShift θ' p.2)| ≤ C)
    (hsliceU : ∀ r : ℝ, 0 < r → ∃ C : ℝ, 0 ≤ C ∧ ∀ θ' ∈ Set.Ioo 0 (Real.pi / 2),
      ∀ p : ℝ × ℝ, ‖p‖ ≤ ε → ∀ s ∈ Set.Icc 0 T,
        |slice g s (Work.FTS.StrongEps.zShift r p.1)
          (Work.FTS.StrongEps.thShift θ' p.2)| ≤ C)
    (hdom : ∃ G : ℝ → ℝ, IntegrableOn G (Set.Ioi 0) ∧
      ∀ r ∈ Set.Ioi 0, ∀ s ∈ Set.Icc 0 T,
        |Work.FM.L12dens Work.Spaces.K
          (Work.FTS.StrongEps.Jeps ρ ε (epsRHSP α ρ ε Φs E g s)) r| ≤ G r)
    (hbdJeps : ∀ (z θ : ℝ), (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℝ × ℝ, ‖p‖ ≤ ε → ∀ s ∈ Set.Icc 0 T,
        |Work.Spaces.mixed a b (epsRHSP α ρ ε Φs E g s)
          (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)| ≤ C)
    (hR : ∃ R : ℝ, 0 ≤ R ∧ ∀ σ ∈ Set.Icc (0 : ℝ) T, Work.Spaces.HkNorm α 4
      (Pz (Work.FTS.StrongEps.Jeps ρ ε (epsRHSP α ρ ε Φs E g σ))) ≤ R)
    (hcontU : Filter.Tendsto (fun σ : ℝ => ∫ p : ℝ × ℝ,
        (Work.Spaces.mixed a b (Pz (Work.FTS.StrongEps.Jeps ρ ε
            (epsRHSP α ρ ε Φs E g σ))) p.1 p.2
          - Work.Spaces.mixed a b (Pz (Work.FTS.StrongEps.Jeps ρ ε
            (epsRHSP α ρ ε Φs E g τ))) p.1 p.2) ^ 2
          * (Work.Spaces.w p.1 ^ 2 * Real.sin (2 * p.2) ^ c) ∂mup) (nhds τ) (nhds 0)) :
    DiagCurveI (fun z θ => Work.Spaces.w z ^ 2 * Real.sin (2 * θ) ^ c)
      (fun s => Work.Spaces.mixed a b (slice (JfamP ρ ε g) s))
      (fun σ => Work.Spaces.mixed a b
        (Pz (Work.FTS.StrongEps.Jeps ρ ε (epsRHSP α ρ ε Φs E g σ)))) τ T := by
  have hρm := rhoC_meas_nonneg c
  have hsm : ∀ s ∈ Set.Icc 0 T, ∀ n : ℕ,
      ContDiffOn ℝ n (Function.uncurry (slice g s)) Work.FTS.EllipticEst.Q0 :=
    fun s hs n => smoothOn_slice_of_joint_smooth hs (hreg n)
  have hsmR : ∀ s ∈ Set.Icc 0 T, ∀ n : ℕ,
      ContDiffOn ℝ n (Function.uncurry (epsRHSP α ρ ε Φs E g s)) Work.FTS.EllipticEst.Q0 :=
    fun s hs n => smoothOn_slice_of_joint_smooth
      (g := fun z θ σ => epsRHSP α ρ ε Φs E g σ z θ) hs (hregR n)
  have hcontAll := fun j i : ℕ =>
    JepsJoint.mixed_fam_continuous_Icc (g := g) (T := T) (j := j) (i := i) hreg
  have hcontAllR := fun j i : ℕ =>
    JepsJoint.mixed_fam_continuous_Icc (g := fun z θ σ => epsRHSP α ρ ε Φs E g σ z θ) (T := T)
      (j := j) (i := i) hregR
  have hmeas := fun (k l : ℕ) (z θ : ℝ) (hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0) =>
    aestronglyMeasurable_slice_mixed (g := g) (T := T) (k := k) (l := l) (z := z) (θ := θ)
      (hcontAll k l) hzθ
  have hmeasR := fun (k l : ℕ) (z θ : ℝ) (hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0) =>
    aestronglyMeasurable_slice_mixed (g := fun z θ σ => epsRHSP α ρ ε Φs E g σ z θ) (T := T)
      (k := k) (l := l) (z := z) (θ := θ) (hcontAllR k l) hzθ
  have hcontR := fun (z θ : ℝ) (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) =>
    (hcontAllR a b).comp (f := fun s : ℝ => (s, (z, θ)))
      (ContinuousOn.prodMk continuousOn_id (continuousOn_const (c := (z, θ))))
      (fun s hs => ⟨hs, ⟨hz, hθ⟩⟩)
  have hbdd := JepsJoint.hbdd_of_joint_continuous (g := g) (T := T) (N := 4)
    (fun j i _ => hcontAll j i)
  have hbddR := JepsJoint.hbdd_of_joint_continuous
    (g := fun z θ σ => epsRHSP α ρ ε Φs E g σ z θ) (T := T) (N := 4)
    (fun j i _ => hcontAllR j i)
  have hαIoc : α ∈ Set.Ioc 0 1 := ⟨hα, hα1⟩
  have hmem := fun s hs => Work.FTS.StrongEps.HkMem_Jeps hρ.moll hαIoc hε (hsm s hs) (hmem0 s hs)
  have hmemR := fun s hs => Work.FTS.StrongEps.HkMem_Jeps hρ.moll hαIoc hε (hsmR s hs) (hmem0R s hs)
  have hsmx := fun s hs => Work.FTS.StrongEps.EpsSqTools.LinAux.smoothOpen_Pz
    (Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε (hsm s hs))
  have hsmd := fun σ hσ => Work.FTS.StrongEps.EpsSqTools.LinAux.smoothOpen_Pz
    (Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε (hsmR σ hσ))
  have hmemx := fun s hs =>
    Work.FTS.StrongEps.PZeroAux.PzJepsHkMem 4 hρ hαIoc hε (hsm s hs) (hmem0 s hs)
  have hmemd := fun σ hσ =>
    Work.FTS.StrongEps.PZeroAux.PzJepsHkMem 4 hρ hαIoc hε (hsmR σ hσ) (hmem0R σ hσ)
  have hg : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => g q.2.1 q.2.2 q.1)
      (Set.Icc (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad) := by
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right,
      Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero, Work.FTS.Galerkin.slice_apply]
      using hcontAll 0 0
  have hint := JepsJoint.integrable_jker_fam hρ.moll hε (U := g) hg
  have hintJeps := fun (z θ : ℝ) (hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0) =>
    JepsJoint.integrable_jker_fam hρ.moll hε
      (U := fun z θ s => Work.Spaces.mixed a b (slice g s) z θ) (hcontAll a b)
      z θ hzθ.1 hzθ.2
  have hsmF : ∀ s ∈ Set.Icc 0 T, Work.FTS.EllipticEst.SmoothOpen (slice g s) :=
    fun s hs => (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr (hsm s hs)
  have hsmFR : ∀ s ∈ Set.Icc 0 T, Work.FTS.EllipticEst.SmoothOpen (epsRHSP α ρ ε Φs E g s) :=
    fun s hs => (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr (hsmR s hs)
  have hτmem : τ ∈ Set.Icc (0 : ℝ) T := ⟨hτIoo.1.le, hτIoo.2.le⟩
  have hderiv := ae_hasDerivAt_mixed_JfamP (j := a) (i := b) hρ hε hab hsol hsm hsmR hsmF hsmFR
    hmem hmemR hmeas hmeasR hbdd hbddR hcontR hint hbdU hsliceU hdom hintJeps hbdJeps
  have hcross : ∀ {f h : ℝ → ℝ → ℝ}, Work.FTS.EllipticEst.SmoothOpen f →
      Work.FTS.EllipticEst.SmoothOpen h → Work.Spaces.HkMem α 4 f → Work.Spaces.HkMem α 4 h →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.Spaces.mixed a b f p.1 p.2
        * Work.Spaces.mixed a b h p.1 p.2
        * (Work.Spaces.w p.1 ^ 2 * Real.sin (2 * p.2) ^ c)) mup := by
    intro f h hf hh hmf hmh
    by_cases hb : b = 0
    · subst hb
      exact integrable_cross_slot_rpow (α := α) (c := c) (a := a) (b := 0) hα (hcη rfl)
        (by omega) hf hh hmf hmh
    · have hb1 : 1 ≤ b := by omega
      exact SlotHkGen.integrable_cross_slot_rpow_mixed (α := α) (c := c) (a := a) (b := b)
        hα hc hb1 hab hf hh hmf hmh
  have hbddK : ∃ K : ℝ, 0 ≤ K ∧ ∀ σ ∈ Set.Icc (0 : ℝ) T,
      ∫ p : ℝ × ℝ, (Work.Spaces.mixed a b (Pz (Work.FTS.StrongEps.Jeps ρ ε
          (epsRHSP α ρ ε Φs E g σ))) p.1 p.2) ^ 2
        * (Work.Spaces.w p.1 ^ 2 * Real.sin (2 * p.2) ^ c) ∂mup ≤ K := by
    by_cases hb : b = 0
    · subst hb
      exact slot_L2_uniform_le (α := α) (c := c) (j := a) (i := 0) hα (hcη rfl) (by omega)
        hsmd hmemd hR
    · have hb1 : 1 ≤ b := by omega
      exact SlotHkGen.slot_L2_uniform_le_mixed (α := α) (c := c) (j := a) (i := b) hα hc hb1 hab
        hsmd hmemd hR
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hderiv, hbddK, hcontU, ?_⟩
  · exact hρm.1.aemeasurable
  · exact hρm.2
  · intro s hs
    refine (hcross
      (f := slice (JfamP ρ ε g) s) (h := slice (JfamP ρ ε g) s)
      (hsmx s hs) (hsmx s hs) (hmemx s hs) (hmemx s hs)).congr
      (Filter.Eventually.of_forall fun p => by ring)
  · intro s hs
    refine (hcross
      (f := Pz (Work.FTS.StrongEps.Jeps ρ ε (epsRHSP α ρ ε Φs E g s)))
      (h := Pz (Work.FTS.StrongEps.Jeps ρ ε (epsRHSP α ρ ε Φs E g s)))
      (hsmd s hs) (hsmd s hs) (hmemd s hs) (hmemd s hs)).congr
      (Filter.Eventually.of_forall fun p => by ring)
  · exact aestronglyMeasurable_mixed_JfamP (ρ := ρ) hρ hε hsm (fun j i _ => hcontAll j i)
  · exact aestronglyMeasurable_mixed_JfamP_RHS (ρ := ρ) (α := α) (T := T) (ε := ε)
      (Φs := Φs) (E := E) (g₀ := g₀) (g := g) hρ hε hsmR (fun j i _ => hcontAllR j i)
  · exact hcross
      (f := Pz (Work.FTS.StrongEps.Jeps ρ ε (epsRHSP α ρ ε Φs E g τ)))
      (h := slice (JfamP ρ ε g) τ) (hsmd τ hτmem) (hsmx τ hτmem)
      (hmemd τ hτmem) (hmemx τ hτmem)

end Work.FTS.StrongEps.EpsE4Thr
