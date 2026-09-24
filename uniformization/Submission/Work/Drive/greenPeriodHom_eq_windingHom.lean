import Mathlib
import Submission.Work.Drive.Interfaces
import Submission.Work.Drive.PhaseBridgeDefs
import Submission.Work.Drive.PhaseBridge
import Submission.Work.SimplyConnected.ABS.modulusLP_branch
import Submission.Work.Analysis.RiemannSurface.isEvenlyCovered_logProj

/-!
# The periods of the conjugate on the loops trivial in `X` are minus `2π` times the winding of `Θ`

This file owns the target `Work.Drive.greenPeriodHom_eq_windingHom`.

Let `X` be a connected Riemann surface, `z₀ : X`, `E : X → ℝ` harmonic on `X ∖ {z₀}` with a unit
logarithmic pole at `z₀`, and `Θ : X → ℂ` continuous, nonvanishing off `z₀`, with a single simple
zero at `z₀` (`hloc`).  Write `P` for the period homomorphism of the conjugate of `E`
(`Work.ModulusLP.greenPeriodHom`) and `W` for the winding homomorphism of `Θ` around `z₀`
(`hW` is its defining property, via the monodromy of the logarithmic étale space of `Θ|_U`).

The theorem says that on the loops `γ` of `U = X ∖ {z₀}` that become trivial in `π₁(X)` the two
homomorphisms agree up to sign: `P γ = ± 2π · W γ`.

The mathematical content is the *cancellation of the two logarithmic singularities at `z₀`*: the
phase function `E* + arg Θ` is single-valued near `z₀` (the pole of `E*` cancels the simple zero of
`Θ`), so the branches of the multivalued phase form a covering space of *all* of `X`
(`Work.Drive.isCoveringMap_phaseProj`); the monodromy of that covering around a loop null-homotopic
in `X` is trivial, and the monodromy of the phase around `γ` is computed — through the bridge
`Work.Drive.phaseBridge` from the conjugate étale space and the log cover to the phase cover — to be
`P γ + 2π W γ`.  Hence `P γ + 2π W γ = 0` and the first alternative holds.

Compare `Work.ModulusLP.greenPeriodHom_two_pi_zmultiples`, which only gives `P γ ∈ 2πℤ` on these
loops: the branch bundle of the modulus records the value of `exp (-(E + iE*))`, which loses exactly
the integer that the log cover of `Θ` supplies.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

noncomputable section

open Filter Set Classical

namespace Work.Drive

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The assembly.**  Same statement as the target `Work.Drive.greenPeriodHom_eq_windingHom`, with
the continuity of the bridge `Work.Drive.phaseBridge` (which is proved separately in
`Submission/Work/Drive/PhaseBridge.lean`) as an explicit hypothesis. -/
theorem greenPeriodHom_eq_windingHom_of_bridge {z₀ : X} {E : X → ℝ}
    (hEharm : Submission.HarmonicOnX E (Set.univ \ {z₀}))
    (hpole : Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {z₀}) z₀ E)
    {Θ : X → ℂ} (hΘ : Continuous Θ) (hΘne : ∀ x : X, x ≠ z₀ → Θ x ≠ 0)
    (hloc : ∃ (u : X → ℂ) (V : Set X), V ∈ nhds z₀ ∧ ContinuousOn u V ∧
      (∀ x ∈ V, u x ≠ 0) ∧
      ∀ x ∈ V, Θ x = ((chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀) * u x)
    (u₀ : Work.Modulus.puncturedOpens z₀)
    {W : Additive (FundamentalGroup (↥(Work.Modulus.puncturedOpens z₀)) u₀) →+ ℤ}
    (hW : ∀ (w₀ : ℂ) (hw₀ : Complex.exp w₀ = Θ u₀.1)
      (γ : FundamentalGroup (↥(Work.Modulus.puncturedOpens z₀)) u₀),
      Work.SimplyConnected.ABS.logCoord (fun u : ↥(Work.Modulus.puncturedOpens z₀) => Θ u.1)
        ((Work.Analysis.RiemannSurface.isCoveringMap_logProj
            (fun u : ↥(Work.Modulus.puncturedOpens z₀) => Θ u.1)
            (hΘ.comp continuous_subtype_val) (fun u => hΘne u.1 u.2)).monodromy γ
          (Work.SimplyConnected.ABS.logPt (fun u : ↥(Work.Modulus.puncturedOpens z₀) => Θ u.1)
            u₀ w₀ hw₀)).1
        = w₀ + (W (Additive.ofMul γ) : ℂ) * (2 * Real.pi * Complex.I))
    (hbridge : @Continuous ↥(phaseFiberProd z₀ Θ) (X × ℝ)
      (phaseFiberProdTopology z₀ E Θ) (phaseTopology z₀ E Θ) (phaseBridge z₀ Θ)) :
    ∀ γ : Additive (FundamentalGroup (↥(Work.Modulus.puncturedOpens z₀)) u₀),
      Work.SimplyConnected.ABS.inclMapP z₀ u₀ (Additive.toMul γ) = 1 →
        Work.ModulusLP.greenPeriodHom hEharm u₀ γ = -(W γ : ℝ) * (2 * Real.pi) ∨
        Work.ModulusLP.greenPeriodHom hEharm u₀ γ = (W γ : ℝ) * (2 * Real.pi) := by
  intro γ hγ
  classical
  -- the phase cover and the two covers over the punctured surface
  have covP : @IsCoveringMap (X × ℝ) X (phaseTopology z₀ E Θ) inferInstance Prod.fst :=
    isCoveringMap_phaseProj hEharm hpole hΘ hΘne hloc
  letI : TopologicalSpace (Punct z₀ × ℝ) := Work.Modulus.greenConjTopology z₀ E
  letI : TopologicalSpace (X × ℝ) := phaseTopology z₀ E Θ
  have covC : @IsCoveringMap (Punct z₀ × ℝ) (Punct z₀)
      (Work.Modulus.greenConjTopology z₀ E) inferInstance Prod.fst :=
    Work.ModulusLP.green_isCoveringMap (z₀ := z₀) (E := E) hEharm
  have covL : IsCoveringMap
      (Work.SimplyConnected.ABS.logProj (fun u : Punct z₀ => Θ u.1)) :=
    Work.Analysis.RiemannSurface.isCoveringMap_logProj (fun u : Punct z₀ => Θ u.1)
      (hΘ.comp continuous_subtype_val) (fun u => hΘne u.1 u.2)
  -- a path representative of the loop
  obtain ⟨γp⟩ := γ
  have hγ' : Work.SimplyConnected.ABS.inclMapP z₀ u₀
      (Additive.toMul (Additive.ofMul (Path.Homotopic.Quotient.mk γp))) = 1 := hγ
  -- the lift in the conjugate étale space
  let e₀c : Punct z₀ × ℝ := (u₀, 0)
  have he₀c : Prod.fst e₀c = u₀ := rfl
  let Γc : C(unitInterval, Punct z₀ × ℝ) := covC.liftPath γp e₀c (γp.source.trans he₀c.symm)
  -- the lift in the logarithmic étale space
  let w₀ : ℂ := Complex.log (Θ u₀.1)
  have hw₀ : Complex.exp w₀ = (fun u : Punct z₀ => Θ u.1) u₀ :=
    Complex.exp_log (hΘne u₀.1 u₀.2)
  let lp : ↥(Work.SimplyConnected.ABS.logProj (fun u : Punct z₀ => Θ u.1) ⁻¹' {u₀}) :=
    Work.SimplyConnected.ABS.logPt (fun u : Punct z₀ => Θ u.1) u₀ w₀ hw₀
  let Γl : C(unitInterval, LogSp (z₀ := z₀) Θ) :=
    covL.liftPath γp lp.1 (γp.source.trans lp.2.symm)
  -- the period of the conjugate is the second coordinate of the conjugate lift
  have hper : Work.ModulusLP.greenPeriodHom hEharm u₀
      (Additive.ofMul (Path.Homotopic.Quotient.mk γp)) = (Γc 1).2 := by
    rw [Work.ModulusLP.greenPeriodHom_apply]
    have h1 : (covC.monodromy (Path.Homotopic.Quotient.mk γp)
        (Submission.conjFiberPt u₀ 0)).1 = Γc 1 := rfl
    have h2 : (Submission.conjFiberPt u₀ 0).1.2 = 0 := rfl
    have h3 : (covC.monodromy (Path.Homotopic.Quotient.mk γp)
        (Submission.conjFiberPt u₀ 0)).1.2 = (Γc 1).2 := congrArg Prod.snd h1
    simp only [Submission.conjPeriod, h3, h2, sub_zero]
  -- the winding number is the imaginary part of the logarithmic coordinate
  have hmonoL : (covL.monodromy (Path.Homotopic.Quotient.mk γp) lp).1 = Γl 1 :=
    Submission.monodromy_mk_liftPath covL γp lp.1 lp.2
  have hΓl1 : (Γl 1).1.2 = w₀ + ((W (Additive.ofMul (Path.Homotopic.Quotient.mk γp)) : ℤ) : ℂ)
      * (2 * Real.pi * Complex.I) := by
    have hWγ := hW w₀ hw₀ (Path.Homotopic.Quotient.mk γp)
    rw [← hWγ, ← hmonoL]
    rfl
  -- the loop in `X` and its null-homotopy
  set incl : C(Punct z₀, X) := ⟨Subtype.val, continuous_subtype_val⟩ with hincl
  set γX : Path u₀.1 u₀.1 := γp.map (f := (Subtype.val : Punct z₀ → X)) continuous_subtype_val
    with hγX
  have hmap : FundamentalGroup.map incl u₀ (Path.Homotopic.Quotient.mk γp)
      = Path.Homotopic.Quotient.mk γX := by
    rw [show (FundamentalGroup.map incl u₀ (Path.Homotopic.Quotient.mk γp))
        = (Path.Homotopic.Quotient.mk γp).map incl from rfl]
    exact (Path.Homotopic.Quotient.mk_map γp incl).symm
  have hγq : FundamentalGroup.map incl u₀ (Path.Homotopic.Quotient.mk γp) = 1 := hγ'
  have hγX1 : Path.Homotopic.Quotient.mk γX = Path.Homotopic.Quotient.mk (Path.refl u₀.1) := by
    rw [← hmap, hγq]
    exact FundamentalGroup.one_def
  have hhom : (γX : C(unitInterval, X)).HomotopicRel
      (ContinuousMap.const unitInterval u₀.1) {0,1} :=
    ⟨(Path.Homotopic.Quotient.eq.mp hγX1).some⟩
  -- the phase path: the image of the pair of lifts under the bridge
  have hpairMem : ∀ s : unitInterval,
      (((Γc s, Γl s) : (Punct z₀ × ℝ) × LogSp (z₀ := z₀) Θ)) ∈ phaseFiberProd z₀ Θ := by
    intro s
    have h1 : (Γc s).1 = γp s := congrFun (covC.liftPath_lifts γp e₀c _) s
    have h2 : (Γl s).1.1 = γp s := congrFun (covL.liftPath_lifts γp lp.1 _) s
    show (Γc s).1 = (Γl s).1.1
    rw [h1, h2]
  let pairCM : C(unitInterval, (Punct z₀ × ℝ) × LogSp (z₀ := z₀) Θ) :=
    ContinuousMap.prodMk Γc Γl
  letI : TopologicalSpace ↥(phaseFiberProd z₀ Θ) := phaseFiberProdTopology z₀ E Θ
  have hpairC : Continuous fun s : unitInterval => (⟨pairCM s, hpairMem s⟩ :
      ↥(phaseFiberProd z₀ Θ)) := Continuous.subtype_mk pairCM.continuous hpairMem
  let pairCM' : C(unitInterval, ↥(phaseFiberProd z₀ Θ)) :=
    ⟨fun s => ⟨pairCM s, hpairMem s⟩, hpairC⟩
  let σ : C(unitInterval, X × ℝ) :=
    ⟨fun s => phaseBridge z₀ Θ (pairCM' s), hbridge.comp pairCM'.continuous⟩
  -- the starting point of the phase path
  let e₀P : X × ℝ := (u₀.1, ((lp.1).1.2).im)
  have hΓc0 : Γc 0 = e₀c := covC.liftPath_zero γp e₀c (γp.source.trans he₀c.symm)
  have hΓl0 : Γl 0 = lp.1 := covL.liftPath_zero γp lp.1 (γp.source.trans lp.2.symm)
  have hσ0 : σ 0 = e₀P := by
    have h1 : phaseBridge z₀ Θ (pairCM' 0)
        = ((Γc 0).1.1, (Γc 0).2 + ((Γl 0).1.2).im) := rfl
    rw [show σ 0 = phaseBridge z₀ Θ (pairCM' 0) from rfl, h1, hΓc0, hΓl0]
    simp only [e₀c, e₀P, zero_add]
  have hσLift : σ = covP.liftPath γX e₀P
      (γX.source.trans (rfl : Prod.fst e₀P = u₀.1).symm) := by
    refine (covP.eq_liftPath_iff' (γ := γX) (e := e₀P)
      (γ_0 := γX.source.trans (rfl : Prod.fst e₀P = u₀.1).symm) (Γ := σ)).mpr ⟨?_, hσ0⟩
    ext s
    have h1 : (Γc s).1 = γp s := congrFun (covC.liftPath_lifts γp e₀c _) s
    have h2 := congrArg (fun u : Punct z₀ => (u : X)) h1
    show Prod.fst (σ s) = γX s
    show ((Γc s).1 : X) = (γp.map (f := (Subtype.val : Punct z₀ → X))
      continuous_subtype_val) s
    rw [h2]
    rfl
  have hσ1 : σ 1 = e₀P := by
    rw [hσLift]
    have h1 := covP.liftPath_apply_one_eq_of_homotopicRel hhom e₀P
      (γX.source.trans (rfl : Prod.fst e₀P = u₀.1).symm)
      (show (ContinuousMap.const unitInterval u₀.1) 0 = Prod.fst e₀P from rfl)
    have h2 : covP.liftPath (ContinuousMap.const unitInterval u₀.1) e₀P
          (show (ContinuousMap.const unitInterval u₀.1) 0 = Prod.fst e₀P from rfl)
        = ContinuousMap.const unitInterval e₀P :=
      covP.liftPath_const (e := e₀P) (x := u₀.1)
        (show (ContinuousMap.const unitInterval u₀.1) 0 = Prod.fst e₀P from rfl)
    rw [h1, h2]
    rfl
  -- read off the coordinates
  have hcoord : (Γc 1).2 + ((Γl 1).1.2).im = w₀.im := by
    have h := congrArg Prod.snd hσ1
    have h2 : (σ 1).2 = (Γc 1).2 + ((Γl 1).1.2).im := rfl
    have h3 : e₀P.2 = w₀.im := rfl
    rw [h2, h3] at h
    exact h
  have him : ((Γl 1).1.2).im
      = w₀.im + ((W (Additive.ofMul (Path.Homotopic.Quotient.mk γp)) : ℤ) : ℝ)
        * (2 * Real.pi) := by
    rw [hΓl1, Complex.add_im]
    congr 1
    rw [show ((W (Additive.ofMul (Path.Homotopic.Quotient.mk γp)) : ℤ) : ℂ)
          * (2 * Real.pi * Complex.I)
        = ((((W (Additive.ofMul (Path.Homotopic.Quotient.mk γp)) : ℤ) : ℝ)
            * (2 * Real.pi) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.mul_I_im, Complex.ofReal_re]
  -- conclusion
  refine Or.inl ?_
  change Work.ModulusLP.greenPeriodHom hEharm u₀ (Additive.ofMul (Path.Homotopic.Quotient.mk γp))
      = -((W (Additive.ofMul (Path.Homotopic.Quotient.mk γp)) : ℤ) : ℝ) * (2 * Real.pi)
  rw [hper]
  linarith [hcoord, him]

/-- **The target theorem.**  The periods of the conjugate of `E` around the loops of
`X ∖ {z₀}` that are null-homotopic in `X` are minus `2π` times the winding number of `Θ`; this is
`Work.Drive.greenPeriodHom_eq_windingHom_of_bridge` with the continuity of the bridge supplied by
`Work.Drive.PhaseBridge`. -/
theorem greenPeriodHom_eq_windingHom {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {z₀ : X} {E : X → ℝ}
    (hEharm : Submission.HarmonicOnX E (Set.univ \ {z₀}))
    (hpole : Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {z₀}) z₀ E)
    {Θ : X → ℂ} (hΘ : Continuous Θ) (hΘne : ∀ x : X, x ≠ z₀ → Θ x ≠ 0)
    (hloc : ∃ (u : X → ℂ) (V : Set X), V ∈ nhds z₀ ∧ ContinuousOn u V ∧
      (∀ x ∈ V, u x ≠ 0) ∧
      ∀ x ∈ V, Θ x = ((chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀) * u x)
    (u₀ : Work.Modulus.puncturedOpens z₀)
    {W : Additive (FundamentalGroup (↥(Work.Modulus.puncturedOpens z₀)) u₀) →+ ℤ}
    (hW : ∀ (w₀ : ℂ) (hw₀ : Complex.exp w₀ = Θ u₀.1)
      (γ : FundamentalGroup (↥(Work.Modulus.puncturedOpens z₀)) u₀),
      Work.SimplyConnected.ABS.logCoord (fun u : ↥(Work.Modulus.puncturedOpens z₀) => Θ u.1)
        ((Work.Analysis.RiemannSurface.isCoveringMap_logProj
            (fun u : ↥(Work.Modulus.puncturedOpens z₀) => Θ u.1)
            (hΘ.comp continuous_subtype_val) (fun u => hΘne u.1 u.2)).monodromy γ
          (Work.SimplyConnected.ABS.logPt (fun u : ↥(Work.Modulus.puncturedOpens z₀) => Θ u.1)
            u₀ w₀ hw₀)).1
        = w₀ + (W (Additive.ofMul γ) : ℂ) * (2 * Real.pi * Complex.I)) :
    ∀ γ : Additive (FundamentalGroup (↥(Work.Modulus.puncturedOpens z₀)) u₀),
      Work.SimplyConnected.ABS.inclMapP z₀ u₀ (Additive.toMul γ) = 1 →
        Work.ModulusLP.greenPeriodHom hEharm u₀ γ = -(W γ : ℝ) * (2 * Real.pi) ∨
        Work.ModulusLP.greenPeriodHom hEharm u₀ γ = (W γ : ℝ) * (2 * Real.pi) :=
  greenPeriodHom_eq_windingHom_of_bridge hEharm hpole hΘ hΘne hloc u₀ hW
    (PhaseBridge (z₀ := z₀) (E := E) (Θ := Θ))

end Work.Drive
