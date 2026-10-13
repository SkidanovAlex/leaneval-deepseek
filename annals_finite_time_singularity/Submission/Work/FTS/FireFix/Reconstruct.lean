/-
# `Work.FTS.FireFix.Reconstruct` — the generic physical reconstruction, with a radius per strip

This module proves **design item 7a** (`FTS_PHYS_BRIDGE.md` §5 item 7):

  `blowupAt_of_physical'`,

the *corrected* form of the delivered `Work.FTS.Physical.blowupAt_of_physical`.  The three
differences are exactly the three corrections of the design that concern this node:

* **a radius per strip**: the hypothesis is
  `hbun : ∀ S ∈ Ioo 0 T, ∃ R, BSAdmissibleStripFull α ω R S`
  instead of a fixed `R` with a *uniform in `t`* support hypothesis `hsupp`; the uniform support
  claim (which the design calls false for a genuine solution) is replaced by the per-strip support
  clause that `BSAdmissibleStrip` already contains.  In particular no `hZ`/`hb` (a uniform
  localisation radius and a bound on the scaling `B`) is needed any more;
* **the pressure**: the design's `PressureReconstructionOn α` (as proved by the `PressureOn`
  area) is consumed through its *exact* hypothesis list, reproduced verbatim below (clauses
  `hωcont`, `hωderiv`, `hωLI`, `hUax` are the four clauses of `PressureReconstructionOn` that are
  *not* implied by the strip bundle, and are therefore taken as hypotheses here — the firing
  theorem `blowupAtTop_of_regPkg'` derives them from the profile data);
* everything else (the strip `C^{1,α}` from the bundles, the decay clause of the datum) is
  *derived*, exactly as in the delivered proof.

The two clauses that the generic theorem *derives* rather than assumes are

* `IsContDiffHolderOn ℝ α (physVel ω).uncurry (univ ×ˢ Icc 0 S)` for every `S < T`, from the
  space-time Schauder estimate `Work.CoreResiduals.BiotSavartSpaceTime` and the per-strip bundle
  (`isContDiffHolderOn_physVel` with the radius chosen per strip);
* the `α`-decay of the datum's vorticity, from the support and bound clauses of the bundle at
  `S = T/2` (`Work.FTS.Physical.BiotSavart.vorticityDecay_of_support`).

Note the `ω` of this theorem is `−physOmega α A B g C` in the application (design correction 1);
this module is sign-agnostic.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.FTS.FireFix.Defs
import Submission.Work.FTS.Physical.Reconstruction
import Submission.Work.FTS.Physical.BiotSavart.contDiffOn_uncurry_ico
import Submission.Work.FTS.Physical.BiotSavart.vorticityDecay_of_support

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.FireFix

open Work.FTS.Physical (physVel)

/-! ## Locality of `C¹` on time strips, with a radius per strip -/

/-- **Locality of `C¹` on time strips.**  If the space-time field `u = physVel ω` is `C¹` on every
compact strip `ℝ³ × [0,S]`, `S < T` — which the space–time Schauder estimate supplies as soon as
each strip carries *some* admissible bundle — then it is `C¹` on the half-open strip
`ℝ³ × [0,T)` demanded by `IsLocalEulerEquationSolution`.

This is `Work.FTS.Physical.BiotSavart.contDiffOn_uncurry_ico` with the radius allowed to depend on
the strip; its proof is copied from there (that lemma's locality step is private). -/
theorem contDiffOn_Ico_of_strips_existsRadius {α : ℝ≥0} (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) < 1)
    {ω : R3 → ℝ → R3} {T : ℝ} (hT : 0 < T)
    (hbun : ∀ S ∈ Set.Ioo 0 T, ∃ R : ℝ,
      Work.CoreResiduals.BSAdmissibleStripFull α ω R S) :
    ContDiffOn ℝ 1 (physVel ω).uncurry (Set.univ ×ˢ Set.Ico (0 : ℝ) T) := by
  have hst := (Work.CoreResiduals.BiotSavart.biotSavartSpaceTime_holds (α := α) hα hα1).2.2
  have hstrips : ∀ S ∈ Set.Ioo 0 T,
      ContDiffOn ℝ 1 (physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 S) := by
    intro S hS
    obtain ⟨R, hb⟩ := hbun S hS
    exact (hst ω R S hS.1 hb).1
  intro x hx
  obtain ⟨a, t⟩ := x
  simp only [Set.mem_prod, Set.mem_univ, true_and] at hx
  set S : ℝ := (t + T) / 2 with hSdef
  have hST : t < S := by simp only [hSdef]; linarith [hx.2]
  have hS : S ∈ Set.Ioo (0 : ℝ) T :=
    ⟨by simp only [hSdef]; linarith [hx.1, hx.2], by simp only [hSdef]; linarith [hx.2]⟩
  have htS : t ∈ Set.Icc (0 : ℝ) S := ⟨hx.1, le_of_lt hST⟩
  have hEv : (Set.univ ×ˢ Set.Icc (0 : ℝ) S)
      =ᶠ[𝓝 ((a, t) : R3 × ℝ)] (Set.univ ×ˢ Set.Ico (0 : ℝ) T) := by
    have hmem : (Set.univ ×ˢ Set.Ioo (-1 : ℝ) S) ∈ 𝓝 ((a, t) : R3 × ℝ) := by
      rw [nhds_prod_eq, Filter.prod_mem_prod_iff]
      exact ⟨univ_mem, Ioo_mem_nhds (by linarith [hx.1]) hST⟩
    filter_upwards [hmem] with y hy
    obtain ⟨b, s⟩ := y
    simp only [Set.mem_prod, Set.mem_univ, true_and, Set.mem_Icc, Set.mem_Ico] at hy ⊢
    exact propext ⟨fun h' => ⟨h'.1, lt_of_le_of_lt h'.2 hS.2⟩,
      fun h' => ⟨h'.1, le_of_lt hy.2⟩⟩
  exact (hstrips S hS (a, t) ⟨Set.mem_univ _, htS⟩).congr_set hEv

/-! ## The generic reconstruction theorem -/

/-- **THE GENERIC PHYSICAL RECONSTRUCTION (design §5 item 7).**  From a physical vorticity `ω`
whose every strip carries *some* full admissible bundle (`hbun`, a radius per strip), which is the
curl of `u = physVel ω` and whose Biot–Savart velocity is divergence-free, odd, with the local
vorticity equation on `Uax` and the four analytic clauses of the pressure input, and whose
sup-norm dominates `c/(T−t)`, the pair `(u, p)` produced by `PressureReconstructionOn α` is a
finite-time blow-up in node N0's interface `Work.FTS.Top.BlowupAt α T`.

Departures from the delivered `Work.FTS.Physical.blowupAt_of_physical` (design §5 item 7):

* the radius is chosen per strip (`hbun`), so no uniform support hypothesis `hsupp` and no `hR` are
  needed — the datum's decay clause is derived from the bundle at `S = T/2`;
* the honest pressure input `PressureReconstructionOn α` replaces the false
  `Work.LWP.PressureReconstruction`; its four non-derivable hypothesis clauses are the hypotheses
  `hωcont`, `hωderiv`, `hωLI`, `hUax` (verbatim from the design's statement of the pressure
  predicate);
* the Biot–Savart inversion `hcurl`/`hdivu` is taken as a hypothesis here (in the application it is
  `Work.FTS.BSSwirl.BiotSavartSwirl` applied slicewise). -/
noncomputable def blowupAt_of_physical' {α : ℝ≥0} (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) < 1)
    {ω : R3 → ℝ → R3} {T : ℝ} (hT : 0 < T)
    (hbun : ∀ S ∈ Set.Ioo 0 T, ∃ R : ℝ,
      Work.CoreResiduals.BSAdmissibleStripFull α ω R S)
    (hcurl : ∀ t ∈ Set.Ico 0 T, ∀ x : R3,
      vorticity (fun y => physVel ω y t) x = ω x t)
    (hdivu : ∀ t ∈ Set.Ico 0 T, div (fun y => physVel ω y t) = 0)
    (hodd : ∀ t ∈ Set.Ico 0 T, IsOdd ((physVel ω) · t))
    (hωcont : ContinuousOn (fun q : R3 × ℝ => timeDeriv ω q.1 q.2)
      (Set.univ ×ˢ Set.Ico (0 : ℝ) T))
    (hωderiv : ∀ x : R3, ∀ t ∈ Set.Ico 0 T,
      HasDerivWithinAt (ω x) (timeDeriv ω x t) (Set.Ici t) t)
    (hωLI : ∀ t ∈ Set.Ioo 0 T, LocallyIntegrable (fun x : R3 => fderiv ℝ (ω · t) x))
    (hUax : ∀ t ∈ Set.Ioo 0 T, ∀ x ∈ Uax,
      ContDiffAt ℝ 2 ((physVel ω) · t) x ∧ ContDiffAt ℝ 1 (ω · t) x ∧
        timeDeriv ω x t + directionalDeriv ω (physVel ω) x t
          = directionalDeriv (physVel ω) ω x t)
    (hcd0 : IsContDiffHolder ℝ α ((physVel ω) · 0))
    (hpress : Work.FTS.PressureOn.PressureReconstructionOn α)
    (hlow : ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Set.Ico 0 T, c / (T - t) ≤ ⨆ x : R3, ‖ω x t‖) :
    Work.FTS.Top.BlowupAt α T := by
  -- the `C^{1,α}` strips of the reconstructed velocity, and its joint `C¹` on `[0,T)`
  have hstrip : ∀ S ∈ Set.Ioo 0 T,
      IsContDiffHolderOn ℝ α (physVel ω).uncurry (Set.univ ×ˢ Set.Icc (0 : ℝ) S) := by
    intro S hS
    obtain ⟨R, hb⟩ := hbun S hS
    exact Work.FTS.Physical.isContDiffHolderOn_physVel hα hα1 hS.1 hb
  have hcont1 : ContDiffOn ℝ 1 (physVel ω).uncurry (Set.univ ×ˢ Set.Ico (0 : ℝ) T) :=
    contDiffOn_Ico_of_strips_existsRadius hα hα1 hT hbun
  -- the per-strip support radius (the support clause of the bundle)
  have hsupp : ∀ S ∈ Set.Ioo 0 T, ∃ R : ℝ,
      ∀ t ∈ Set.Icc (0 : ℝ) S, ∀ x : R3, ω x t ≠ 0 → ‖x‖ ≤ R := by
    intro S hS
    obtain ⟨R, ⟨hR, hsuppR, -⟩, -⟩ := hbun S hS
    refine ⟨R, fun t ht x hx => ?_⟩
    have h := hsuppR t ht x hx
    rwa [Metric.mem_closedBall, dist_zero_right] at h
  -- the pressure, through the design's pressure predicate
  have hex := hpress ω T hstrip hcurl hdivu hsupp hωcont hωderiv hωLI hUax
  -- the decay clause of the datum, from the bundle at `S = T/2`
  have hdecay : ∃ C : ℝ, 0 < C ∧ ∀ x : R3,
      ‖vorticity ((physVel ω) · 0) x‖ ≤ C / (‖x‖ ^ (α : ℝ) + 1) := by
    obtain ⟨R, ⟨hR0, hsuppR, hbdd, -⟩, -⟩ := hbun (T / 2) ⟨by linarith, by linarith⟩
    obtain ⟨M, hM⟩ := hbdd
    have hM0 : 0 ≤ M := le_trans (norm_nonneg _)
      (hM 0 (Set.mem_Icc.mpr ⟨le_rfl, by linarith⟩) 0)
    refine Work.FTS.Physical.BiotSavart.vorticityDecay_of_support (α := α) (R := R) (M := M)
      hR0.le hM0 ?_ ?_
    · intro x hx
      rw [hcurl 0 ⟨le_rfl, hT⟩ x] at hx
      exact hsuppR 0 (Set.mem_Icc.mpr ⟨le_rfl, by linarith⟩) x hx
    · intro x
      rw [hcurl 0 ⟨le_rfl, hT⟩ x]
      exact hM 0 (Set.mem_Icc.mpr ⟨le_rfl, by linarith⟩) x
  refine ⟨physVel ω, hex.choose, hT,
    ⟨hcont1, hex.choose_spec.1, hex.choose_spec.2,
      fun t ht => hdivu t ⟨ht.1.le, ht.2⟩, rfl⟩,
    hdivu 0 ⟨le_rfl, hT⟩, hodd, hcd0, hdecay, hstrip, ?_⟩
  obtain ⟨c, hc, hcl⟩ := hlow
  exact ⟨c, hc, fun t ht => by
    rw [Work.FTS.Physical.vortLInf_physVel_eq hcurl ht]; exact hcl t ht⟩

end Work.FTS.FireFix
