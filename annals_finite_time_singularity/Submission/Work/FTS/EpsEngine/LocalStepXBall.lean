/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/LocalStepXBall.lean` — the local step of the projected
# `ε`-scheme at the **`X`-ball** invariant (the sibling node's class)

The sibling node `Work.FTS.StrongEps.EpsLocalPStar` (`NOTES_route_crux.md` §2′) established that the
right invariant for the Picard iteration of the projected `ε`-scheme is **not** an `ℋ⁶`-ball —
applying the right-hand side costs one derivative, so `HkNorm α 6 (F u) ≤ R` is *false* — but the
`X = (EpsMem, EpsSq)`-ball together with the class-`C` data of the *projected mollified* profile:

    P u := SmoothOpen u ∧ EpsMem α u ∧ EpsSq α u ≤ R
             ∧ ClassC α (Pz (J_ε u)) ∧ Xn α (Pz (J_ε u)) ≤ C₀ α²

(`Xn α = HkNorm α 4`.)  This module

* defines that class as `XBall`,
* produces the engine's per-profile inputs `hcontP`/`hzeroP` for it (`Feps u` is `C^∞` on the open
  quadrant and vanishes off it as soon as `ClassC α (Pz (J_ε u))` holds — no `ℋ⁶`-size clause is
  needed, since `smoothOpen_profRHS_of_classC` reads only the class-`C` data), and
* instantiates `Work.FTS.EpsEngine.exists_sol_of_engine` at `XBall`, with the per-profile data
  derived internally — so the sibling node only has to supply the *invariant* hypotheses
  `hkeepIter`/`hlimP`, the joint `C¹`-regularity `hreg`, and the two gates' data
  (`hbd`/`hlip`/`hpt`, from `EpsRHSPLipX_Sq` + `profRHS_sub_sup_le_Sq`).

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EpsEngine.LocalStepEngine
import Submission.Work.FTS.EpsEngine.SmoothOpenFeps

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.EpsEngine

open Work.FTS.StrongEps

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The `X`-ball invariant of the local step** (`Xn α = HkNorm α 4`): open-quadrant smoothness,
honesty and `EpsSq`-size of the profile, and the class-`C` data and ball clause of its *projected
mollified* image. -/
def XBall (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε R C₀ : ℝ) (u : Fn) : Prop :=
  Work.FTS.EllipticEst.SmoothOpen u ∧ EpsMem α u ∧ EpsSq α u ≤ R ∧
    Work.FTS.ClassC.ClassC α (Pz (Jeps ρ ε u)) ∧ Work.FTS.Nonlin.Xn α (Pz (Jeps ρ ε u))
      ≤ C₀ * α ^ 2

theorem XBall.smoothOpen {α : ℝ} {ρ : ℝ × ℝ → ℝ} {ε R C₀ : ℝ} {u : Fn}
    (h : XBall α ρ ε R C₀ u) : Work.FTS.EllipticEst.SmoothOpen u := h.1

theorem XBall.mem {α : ℝ} {ρ : ℝ × ℝ → ℝ} {ε R C₀ : ℝ} {u : Fn}
    (h : XBall α ρ ε R C₀ u) : EpsMem α u := h.2.1

theorem XBall.sq_le {α : ℝ} {ρ : ℝ × ℝ → ℝ} {ε R C₀ : ℝ} {u : Fn}
    (h : XBall α ρ ε R C₀ u) : EpsSq α u ≤ R := h.2.2.1

theorem XBall.classC {α : ℝ} {ρ : ℝ × ℝ → ℝ} {ε R C₀ : ℝ} {u : Fn}
    (h : XBall α ρ ε R C₀ u) : Work.FTS.ClassC.ClassC α (Pz (Jeps ρ ε u)) := h.2.2.2.1

theorem XBall.ball {α : ℝ} {ρ : ℝ × ℝ → ℝ} {ε R C₀ : ℝ} {u : Fn}
    (h : XBall α ρ ε R C₀ u) : Work.FTS.Nonlin.Xn α (Pz (Jeps ρ ε u)) ≤ C₀ * α ^ 2 := h.2.2.2.2

/-- **`Feps u` is `C^∞` on the open quadrant as soon as `ClassC α (Pz (J_ε u))` holds** — the
class-`C` clause alone (no `ℋ⁶`-size and no `SmoothOpen u`). -/
theorem smoothOpen_Feps_of_classC {α Ce Cs : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {ε : ℝ} {u : Fn}
    (hα : α ∈ Set.Ioc 0 1) (hρ : IsSmoothKernel ρ) (hε : 0 < ε)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hu : Work.FTS.ClassC.ClassC α (Pz (Jeps ρ ε u))) :
    Work.FTS.EllipticEst.SmoothOpen (Feps α ρ ε Φs E u) := by
  have hRHS : Work.FTS.EllipticEst.SmoothOpen
      (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E (Pz (Jeps ρ ε u))) :=
    smoothOpen_profRHS_of_classC hα hEll hstar hu
  have hJ : Work.FTS.EllipticEst.SmoothOpen
      (Jeps ρ ε (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E (Pz (Jeps ρ ε u)))) :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hRHS)
  exact smoothOpen_Pz_of_smoothOpen hJ

/-- **`Feps` vanishes off the open quadrant, unconditionally in the profile** (both `J_ε` and the
projection's correction profile `bump` are supported in `Q0`). -/
theorem Feps_eq_zero_off_Q0 (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (Φs : Fn) (E : Fn → Fn) (w : Fn)
    (q : ℝ × ℝ) (hq : q ∉ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :
    Feps α ρ ε Φs E w q.1 q.2 = 0 := by
  have hq' : ¬(0 < q.1 ∧ q.2 ∈ Set.Ioo 0 (Real.pi / 2)) := fun h => hq ⟨h.1, h.2⟩
  have hbump0 : bump q.1 q.2 = 0 := by
    rw [bump_eq_zero_iff]
    by_cases h1 : 0 < q.1
    · by_cases h2 : q.2 ∈ Set.Ioo 0 (Real.pi / 2)
      · exact absurd ⟨h1, h2⟩ hq'
      · rw [Set.mem_Ioo, not_and_or] at h2
        rcases h2 with h2 | h2
        · exact Or.inr (Or.inr (Or.inl (by linarith [Real.pi_pos])))
        · exact Or.inr (Or.inr (Or.inr (by linarith [Real.pi_pos])))
    · exact Or.inl (by linarith)
  show Pz (Jeps ρ ε (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
    (Pz (Jeps ρ ε w)))) q.1 q.2 = 0
  rw [Pz_apply, Jeps_eq_zero ρ ε _ hq', hbump0]
  ring

/-- **The engine's per-profile inputs at the `X`-ball**: continuity of `Feps u` on the open quadrant
and vanishing off it, for `u ∈ XBall`. -/
theorem continuousOn_Feps_of_XBall {α Ce Cs R C₀ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {ε : ℝ} {u : Fn}
    (hα : α ∈ Set.Ioc 0 1) (hρ : IsSmoothKernel ρ) (hε : 0 < ε)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hu : XBall α ρ ε R C₀ u) :
    ContinuousOn (fun q : ℝ × ℝ => Feps α ρ ε Φs E u q.1 q.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) ∧
      (∀ q : ℝ × ℝ, q ∉ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) →
        Feps α ρ ε Φs E u q.1 q.2 = 0) := by
  have hsmo := smoothOpen_Feps_of_classC (α := α) (Ce := Ce) (Cs := Cs) (ρ := ρ) (Φs := Φs)
    (E := E) (ε := ε) (u := u) hα hρ hε hEll hstar hu.classC
  refine ⟨?_, fun q hq => Feps_eq_zero_off_Q0 α ρ ε Φs E u q hq⟩
  exact (hsmo.forall 0).continuousOn

/-- **The local step of the projected `ε`-scheme for an *arbitrary* class `P`** (the generic form of
`Work.FTS.EpsEngine.exists_sol_of_engine`, whose class is hard-wired to `EpsClass`): the engine
`exists_volterra_v4` runs on `P` as soon as the per-profile data of `Feps` at `P`-profiles and the
invariant hypotheses are supplied; the only extra input (compared with `EpsClass`) is the
`EpsDatumP`-membership of the limit slices, which the `EpsClass` version reads off its own
structure. -/
theorem exists_sol_of_engine_class {α Cpt L δ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {ε : ℝ} {h₀ : Fn} {P : Fn → Prop}
    (hδ : 0 < δ) (hL : 0 < L) (hδL : δ * Real.sqrt L < 1) (hCpt : 0 ≤ Cpt)
    (hP₀ : P h₀)
    (hbd : ∀ u : Fn, P u →
      EpsMem α (Feps α ρ ε Φs E u) ∧ EpsSq α (Feps α ρ ε Φs E u) ≤ L)
    (hlip : ∀ u v : Fn, P u → P v → EpsMem α (fun z θ => u z θ - v z θ) →
      EpsSq α (fun z θ => Feps α ρ ε Φs E u z θ - Feps α ρ ε Φs E v z θ)
        ≤ L * EpsSq α (fun z θ => u z θ - v z θ))
    (hpt : ∀ u v : Fn, P u → P v → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Feps α ρ ε Φs E u z θ - Feps α ρ ε Φs E v z θ|
        ≤ Cpt * Real.sqrt (EpsSq α (fun z θ => u z θ - v z θ)))
    (hcontP : ∀ u : Fn, P u → ContinuousOn (fun q : ℝ × ℝ => Feps α ρ ε Φs E u q.1 q.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hzeroP : ∀ u : Fn, P u → ∀ q : ℝ × ℝ,
      q ∉ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) → Feps α ρ ε Φs E u q.1 q.2 = 0)
    (hkeepIter : ∀ n : ℕ, ∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
      P (slice (Work.FTS.StrongEps.EpsLocalPStar.iter (Feps α ρ ε Φs E) h₀ (n + 1)) τ))
    (hlimP : ∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
      P (slice (Work.FTS.StrongEps.EpsLocalPStar.limFam (Feps α ρ ε Φs E) h₀) τ))
    (hreg : ContDiffOn ℝ 1
      (fun p : ℝ × ℝ × ℝ => Work.FTS.StrongEps.EpsLocalPStar.limFam (Feps α ρ ε Φs E) h₀
        p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 δ))
    (hd : ∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
      EpsDatumP α ρ ε (slice (Work.FTS.StrongEps.EpsLocalPStar.limFam (Feps α ρ ε Φs E) h₀) τ)) :
    ∃ h : Fam, IsEpsSolP α ρ ε δ Φs E h₀ h ∧ EpsRegP α ρ ε δ h := by
  obtain ⟨h0, hder⟩ :=
    exists_volterra_v4 (α := α) (F := Feps α ρ ε Φs E) (h₀ := h₀) (P := P)
      (Cpt := Cpt) (L := L) (δ := δ)
      hδ hL hδL hCpt hP₀ hbd hlip hpt hcontP hzeroP hkeepIter hlimP
  exact ⟨Work.FTS.StrongEps.EpsLocalPStar.limFam (Feps α ρ ε Φs E) h₀,
    IsEpsSolP_of_v4 (α := α) (ε := ε) (δ := δ) (ρ := ρ) (Φs := Φs) (E := E)
      (g₀ := h₀) (h := Work.FTS.StrongEps.EpsLocalPStar.limFam (Feps α ρ ε Φs E) h₀) h0 hder,
    hreg, hd⟩

/-- **The local step of the projected `ε`-scheme at the `X`-ball invariant** (the sibling node's
class): the per-profile data `hcontP`/`hzeroP` of `Feps` are *derived* from the class-`C` clause of
`XBall`, so the consumer only supplies the two gates (`hbd`/`hlip`/`hpt` — from `EpsRHSPLipX_Sq` and
`profRHS_sub_sup_le_Sq`), the invariant clauses (`hkeepIter`/`hlimP`), the joint `C¹`-regularity
`hreg` and the `EpsDatumP`-clauses of the limit slices. -/
theorem exists_sol_of_engine_xball {α C₀ R Ce Cs Cpt L δ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn}
    {E : Fn → Fn} {ε : ℝ} {h₀ : Fn}
    (hα : α ∈ Set.Ioc 0 1) (hρ : IsSmoothKernel ρ) (hε : 0 < ε)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hδ : 0 < δ) (hL : 0 < L) (hδL : δ * Real.sqrt L < 1) (hCpt : 0 ≤ Cpt)
    (hP₀ : XBall α ρ ε R C₀ h₀)
    (hbd : ∀ u : Fn, XBall α ρ ε R C₀ u →
      EpsMem α (Feps α ρ ε Φs E u) ∧ EpsSq α (Feps α ρ ε Φs E u) ≤ L)
    (hlip : ∀ u v : Fn, XBall α ρ ε R C₀ u → XBall α ρ ε R C₀ v →
      EpsMem α (fun z θ => u z θ - v z θ) →
      EpsSq α (fun z θ => Feps α ρ ε Φs E u z θ - Feps α ρ ε Φs E v z θ)
        ≤ L * EpsSq α (fun z θ => u z θ - v z θ))
    (hpt : ∀ u v : Fn, XBall α ρ ε R C₀ u → XBall α ρ ε R C₀ v →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Feps α ρ ε Φs E u z θ - Feps α ρ ε Φs E v z θ|
          ≤ Cpt * Real.sqrt (EpsSq α (fun z θ => u z θ - v z θ)))
    (hkeepIter : ∀ n : ℕ, ∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
      XBall α ρ ε R C₀ (slice (Work.FTS.StrongEps.EpsLocalPStar.iter (Feps α ρ ε Φs E) h₀
        (n + 1)) τ))
    (hlimP : ∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
      XBall α ρ ε R C₀ (slice (Work.FTS.StrongEps.EpsLocalPStar.limFam (Feps α ρ ε Φs E) h₀) τ))
    (hreg : ContDiffOn ℝ 1
      (fun p : ℝ × ℝ × ℝ => Work.FTS.StrongEps.EpsLocalPStar.limFam (Feps α ρ ε Φs E) h₀
        p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 δ))
    (hd : ∀ τ : ℝ, τ ∈ Set.Icc 0 δ → EpsDatumP α ρ ε
      (slice (Work.FTS.StrongEps.EpsLocalPStar.limFam (Feps α ρ ε Φs E) h₀) τ)) :
    ∃ h : Fam, IsEpsSolP α ρ ε δ Φs E h₀ h ∧ EpsRegP α ρ ε δ h := by
  have hcontP : ∀ u : Fn, XBall α ρ ε R C₀ u →
      ContinuousOn (fun q : ℝ × ℝ => Feps α ρ ε Φs E u q.1 q.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    fun u hu => (continuousOn_Feps_of_XBall (α := α) (Ce := Ce) (Cs := Cs) (R := R) (C₀ := C₀)
      (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) (u := u) hα hρ hε hEll hstar hu).1
  have hzeroP : ∀ u : Fn, XBall α ρ ε R C₀ u → ∀ q : ℝ × ℝ,
      q ∉ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) → Feps α ρ ε Φs E u q.1 q.2 = 0 :=
    fun u hu => (continuousOn_Feps_of_XBall (α := α) (Ce := Ce) (Cs := Cs) (R := R) (C₀ := C₀)
      (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) (u := u) hα hρ hε hEll hstar hu).2
  exact exists_sol_of_engine_class (α := α) (Cpt := Cpt) (L := L) (δ := δ) (ρ := ρ)
    (Φs := Φs) (E := E) (ε := ε) (h₀ := h₀) (P := fun u => XBall α ρ ε R C₀ u)
    hδ hL hδL hCpt hP₀ hbd hlip hpt hcontP hzeroP hkeepIter hlimP hreg hd

end Work.FTS.EpsEngine
