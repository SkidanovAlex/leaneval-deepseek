/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/Reduction.lean` — the assembly layer of E4

`Work.FTS.StrongEps.EpsE4Thr` (`Submission/Work/FTS/StrongEps/EpsE4Thr.lean`) asks for

  `EpsUniformMem α ρ Φs E g₀ C₀ K`

for data in the small class (`hvan`, `hd : ∀ ε > 0, EpsDatum α ρ ε g₀`, `Xn α g₀ ≤ α²`,
`Xn₆ α g₀ ≤ K α²`) and the elliptic/modulation packages.  Its two *documented* inputs
(`NOTES_EpsE4_FALSE.md` §3) are

* the **small-ball local step** of the projected scheme — E2a of `NOTES_EpsLocal.md`, i.e. the
  repaired `EpsLocalP` in which the datum is restricted to the *small ball* so that `MuLamOK`
  gives `|muDyn| ≤ 1/2` and the `μ = -1` discontinuity of `epsRHSP` is excluded (`EpsLocalP` is
  **false** as stated for arbitrary data size — see `EpsLocalP.lean` and §9 of
  `NOTES_session11.md`);
* the **sub-horizon a-priori bound** of the projected scheme, `EpsAprioriBddHP` of
  `EpsStructP.lean` — here in the form that carries *both* bounds the bootstrap needs: the
  `ℋ⁶`-size `Xn₆ ≤ M` of the slices and the *small-ball* bound `Xn α ≤ C₀ α²` of the projected
  mollified slices.

This module performs the third, purely bookkeeping, part — the one that belongs to whoever states
`EpsE4Thr`: the restart-and-concatenate induction that turns the two inputs into
`EpsUniformMem`.  It is the `P₀`-analogue of `StrongEpsP.EpsGlue_of_glueP`, with two changes:

* the local step is consumed only at the two data sizes the route needs (the datum's own
  `Xn₆ α g₀` for the first piece, and the a-priori constant `M` at the restarts), and it carries
  the *small-ball* condition — which is what the (false-as-stated) unrestricted `∀ M'`-form of
  `EpsLocalP` cannot allow;
* the *small-ball* and `ℋ⁶` conditions on the restart datum are produced by the a-priori bound,
  so both are available at every restart.

The junction glues are the proved `StrongEpsP.SolGlueP`/`StrongEpsP.RegGlueP`, exactly as in
`EpsGlueP.lean`.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.EpsStructP
import Submission.Work.FTS.StrongEps.PZeroAux.Pz_l12
import Submission.Work.FTS.StrongEps.StrongEpsP.Defs
import Submission.Work.FTS.StrongEps.StrongEpsP.SolGlueP
import Submission.Work.FTS.StrongEps.StrongEpsP.RegGlueP
import Submission.Work.FTS.StrongEps.EpsMem
import Submission.Work.FTS.StrongPersist.Basic
import Submission.Work.FTS.StrongEps.E5L12Datum

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
open Work.FTS.StrongGlobal (Xn6 concat)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The two inputs of `EpsE4Thr` -/

/-- **The small-ball local step of the projected scheme** (the corrected `EpsLocalP`): for every
data size `M' ≥ 0` there is a *single* `δ > 0` which works for **every** datum `h₀` of
`ℋ⁶`-size `≤ M'` whose projected mollified profile lies in the `C₀ α²`-ball of the class `C`.

This is the shape of `EpsLocalP` (`EpsLocalP.lean`) with the extra *small-ball* hypothesis
`Xn α (P₀ (J_ε h₀)) ≤ C₀ α²`, under which `MuLamOK α C₀ Φs E` bounds the modulation
`|muDyn| ≤ 1/2` on the class-`C` profiles met by the flow and the `μ = -1` jump of `epsRHSP`
(`NOTES_session11.md` §9, `NOTES_rhsSlice_lipschitz_H4_blocker.md`) is excluded.  The conclusion
is that of `EpsLocalP` (existence of a `P₀`-solution on `[0,δ]` with its regularity `EpsRegP`)
*without* the `2M'+1`-clause: in this route that size bound is supplied at every restart by
`AprioriP` below. -/
def LocalStepP (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (Φs : Fn) (E : Fn → Fn) (C₀ : ℝ) : Prop :=
  ∀ M' : ℝ, 0 ≤ M' → ∃ δ : ℝ, 0 < δ ∧ ∀ h₀ : Fn,
    EpsDatumP α ρ ε h₀ →
    Work.FTS.Nonlin.Xn α (Pz (Jeps ρ ε h₀)) ≤ C₀ * α ^ 2 →
    Xn6 α h₀ ≤ M' →
    ∃ h : Fam, IsEpsSolP α ρ ε δ Φs E h₀ h ∧ EpsRegP α ρ ε δ h

/-- **The sub-horizon a-priori bound of the projected scheme**: every *regular* `P₀`-solution on
any `[0,T']`, `T' ≤ T`, with datum `g₀` has *both* of its bootstrap bounds — its slices are of
`ℋ⁶`-size `≤ M` and its projected mollified slices are in the `C₀ α²`-ball.

This is `EpsAprioriBddHP` (`EpsStructP.lean`) with the small-ball clause added: it is the form in
which the *barrier* argument ("the level-four energy obeys the `S4` algebra and the level-six
energy obeys `e' ≤ Λ(1+e)`") delivers its conclusion, and it is exactly what the continuation
below consumes at every restart.

**The datum's small-ball condition is an *input*, and it has to be.**  The `τ = 0` instance of
the second conjunct reads `Xn α (Pz (J_ε (slice g 0))) ≤ C₀ α²`, i.e. (by `IsEpsSolP.init`)
`Xn α (Pz (J_ε g₀)) ≤ C₀ α²` — a statement about the *datum* `g₀` alone, which none of
`Xn6 α g₀ ≤ M`, `IsEpsSolP`, `EpsRegP` implies (`EpsRegP`'s `τ = 0` clause is `EpsDatumP α ρ ε g₀`
= `SmoothOpen ∧ HkMem α 6 ∧ ClassC α (Pz (J_ε g₀))`, and `ClassC` carries no *upper* bound on
`Xn`).  Without it the a-priori bound would be claiming the small ball for data of arbitrary
`ℋ⁴`-size, and it is *false* in that generality (the barrier argument needs the datum strictly
inside the barrier).  The condition is exactly what `LocalStepP` also takes, and what the route
supplies at `τ = 0` from `hd` + `h4` (`TauZero.Jeps_smallBall_one_lt` for `1 < C₀`). -/
def AprioriP (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε T : ℝ) (Φs : Fn) (E : Fn → Fn) (g₀ : Fn)
    (C₀ M : ℝ) : Prop :=
  Xn6 α g₀ ≤ M →
    Work.FTS.Nonlin.Xn α (Pz (Jeps ρ ε g₀)) ≤ C₀ * α ^ 2 →
      ∀ T' : ℝ, 0 < T' → T' ≤ T → ∀ g : Fam, IsEpsSolP α ρ ε T' Φs E g₀ g →
        EpsRegP α ρ ε T' g →
        ∀ τ ∈ Set.Icc 0 T', Xn6 α (slice g τ) ≤ M ∧
          Work.FTS.Nonlin.Xn α (slice (JfamP ρ ε g) τ) ≤ C₀ * α ^ 2

def AprioriDecay (α : ℝ) (ρ : ℝ × ℝ → ℝ) (T : ℝ) (Φs : Fn) (E : Fn → Fn) (g₀ : Fn)
    (Maj : ℝ → ℝ) : Prop :=
  MeasureTheory.IntegrableOn (fun z => Maj z / z) (Set.Ioi 0) ∧
    ∀ ε ∈ Set.Ioc 0 1, ∀ g : Fam, IsEpsSolP α ρ ε T Φs E g₀ g → EpsRegP α ρ ε T g →
      ∀ τ ∈ Set.Icc 0 T, EpsDecay α ρ Φs E ε τ g Maj

/-- `AprioriP` implies the frozen `EpsAprioriBddHP` (its `ℋ⁶`-half). -/
theorem AprioriP.toBddHP {α : ℝ} {ρ : ℝ × ℝ → ℝ} {ε T : ℝ} {Φs : Fn} {E : Fn → Fn}
    {g₀ : Fn} {C₀ M : ℝ} (h : AprioriP α ρ ε T Φs E g₀ C₀ M) (hg₀ : Xn6 α g₀ ≤ M)
    (hsmall₀ : Work.FTS.Nonlin.Xn α (Pz (Jeps ρ ε g₀)) ≤ C₀ * α ^ 2) :
    EpsAprioriBddHP α ρ ε T Φs E g₀ M :=
  fun T' hT' hT'le g hsol hreg τ hτ => (h hg₀ hsmall₀ T' hT' hT'le g hsol hreg τ hτ).1

/-- **`EpsDatum` implies `EpsDatumP`**: the two classes differ only in that the class-`C` clause
of the latter is about the *projected* mollified profile, and the projection is the identity on a
profile whose `L₁₂`-zero-mode vanishes — which is the `l12` field of the former's class-`C`
clause. -/
theorem EpsDatum.toDatumP {α : ℝ} {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {h : Fn}
    (hd : EpsDatum α ρ ε h) : EpsDatumP α ρ ε h := by
  obtain ⟨hsm, hmem, hC⟩ := hd
  have hPz : Pz (Jeps ρ ε h) = Jeps ρ ε h :=
    Pz_self_of_l12 (Work.FTS.ClassC.ClassC.l12_zero hC)
  exact ⟨hsm, hmem, by rw [hPz]; exact hC⟩

/-! ## The restart-and-concatenate induction -/

/-- **The continuation for the `P₀`-scheme.**  Given the small-ball local step `LocalStepP`, the
two-clause a-priori bound `AprioriP`, and the datum's small-ball condition, there is a regular
`P₀`-solution on the whole `[0,T]` carrying both bootstrap bounds.

*Proof.*  Restart-and-concatenate: `hor n = min T ((n+1)δ')` are the horizons, each step restarts
at the current slice, the junction glues are `SolGlueP`/`RegGlueP`, and the a-priori bound applied
to the piece just built keeps *both* conditions at size, so the same `δ` serves at every step.
The first piece uses the local step at the *legitimate* threshold `M' = Xn₆ α g₀`. -/
theorem exists_sol_of_localStep_apriori {α ε T C₀ M : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn}
    {E : Fn → Fn} {g₀ : Fn}
    (hT : 0 < T) (hM : 0 ≤ M) (hg₀M : Xn6 α g₀ ≤ M)
    (hsmall₀ : Work.FTS.Nonlin.Xn α (Pz (Jeps ρ ε g₀)) ≤ C₀ * α ^ 2)
    (hd : EpsDatumP α ρ ε g₀) (hstep : LocalStepP α ρ ε Φs E C₀)
    (hapr : AprioriP α ρ ε T Φs E g₀ C₀ M) :
    ∃ g : Fam, IsEpsSolP α ρ ε T Φs E g₀ g ∧ EpsRegP α ρ ε T g ∧
      ∀ τ ∈ Set.Icc 0 T, Xn6 α (slice g τ) ≤ M ∧
        Work.FTS.Nonlin.Xn α (slice (JfamP ρ ε g) τ) ≤ C₀ * α ^ 2 := by
  -- the local step at the two thresholds the route needs
  obtain ⟨δ, hδpos, hδstep⟩ := hstep M hM
  have hM₀ : (0 : ℝ) ≤ Xn6 α g₀ := Work.Spaces.HkNorm_nonneg α 6 g₀
  obtain ⟨δ₀, hδ₀pos, hδ₀step⟩ := hstep (Xn6 α g₀) hM₀
  -- the step length of the iteration
  set δ' : ℝ := min δ δ₀ with hδ'def
  have hδ'pos : 0 < δ' := lt_min hδpos hδ₀pos
  -- a number of steps that covers `[0,T]`
  obtain ⟨N, hN⟩ : ∃ N : ℕ, T ≤ (N : ℝ) * δ' := by
    obtain ⟨N, hN⟩ := exists_nat_gt (T / δ')
    exact ⟨N, by rw [div_lt_iff₀ hδ'pos] at hN; linarith⟩
  -- the horizons of the iteration
  let hor : ℕ → ℝ := fun n => min T (((n : ℝ) + 1) * δ')
  have hhor_pos : ∀ n, 0 < hor n := fun n => lt_min hT (by positivity)
  have hhor_le : ∀ n, hor n ≤ T := fun n => min_le_left _ _
  -- the inductive statement
  have hpoint : ∀ n : ℕ, ∃ g : Fam, IsEpsSolP α ρ ε (hor n) Φs E g₀ g ∧
      EpsRegP α ρ ε (hor n) g ∧
      ∀ τ ∈ Set.Icc 0 (hor n), Xn6 α (slice g τ) ≤ M ∧
        Work.FTS.Nonlin.Xn α (slice (JfamP ρ ε g) τ) ≤ C₀ * α ^ 2 := by
    intro n
    induction n with
    | zero =>
      -- the first piece: the local step at the datum's own size, restricted to `[0,hor 0]`
      have h0 : hor 0 = min T δ' := by
        show min T ((((0 : ℕ) : ℝ) + 1) * δ') = min T δ'
        norm_num
      rw [h0]
      obtain ⟨h, hsol, hreg⟩ := hδ₀step g₀ hd hsmall₀ le_rfl
      have hle₀ : min T δ' ≤ δ₀ := le_trans (min_le_right T δ') (by rw [hδ'def]; exact min_le_right δ δ₀)
      have hsol' : IsEpsSolP α ρ ε (min T δ') Φs E g₀ h :=
        Work.FTS.StrongEps.StrongEpsP.IsEpsSolP.mono hsol hle₀
      have hreg' : EpsRegP α ρ ε (min T δ') h := EpsRegP.mono hreg hle₀
      exact ⟨h, hsol', hreg',
        hapr hg₀M hsmall₀ (min T δ') (lt_min hT hδ'pos) (min_le_left T δ') h hsol' hreg'⟩
    | succ n ih =>
      obtain ⟨g, hsol, hreg, hbnd⟩ := ih
      by_cases hcase : T ≤ ((n : ℝ) + 1) * δ'
      · -- the horizon has already reached `T`; keep the same family
        have hcase' : hor n = T := min_eq_left hcase
        have hnext : hor (n + 1) = T :=
          min_eq_left (by push_cast; linarith)
        have hs : hor (n + 1) = hor n := by rw [hnext, hcase']
        refine ⟨g, ?_, ?_, ?_⟩
        · rw [hs]; exact hsol
        · rw [hs]; exact hreg
        · rw [hs]; exact hbnd
      · -- extend by one step
        have hXn : ((n : ℝ) + 1) * δ' < T := lt_of_not_ge hcase
        have hnn : hor n = ((n : ℝ) + 1) * δ' := min_eq_right (le_of_lt hXn)
        have hnnonneg : 0 ≤ hor n := le_of_lt (hhor_pos n)
        -- the small-ball and size conditions of the restart datum
        have hdd : EpsDatumP α ρ ε (slice g (hor n)) := hreg.2 (hor n) ⟨hnnonneg, le_rfl⟩
        have hsb : Work.FTS.Nonlin.Xn α (Pz (Jeps ρ ε (slice g (hor n)))) ≤ C₀ * α ^ 2 := by
          have h2 := (hbnd (hor n) ⟨hnnonneg, le_rfl⟩).2
          rwa [slice_JfamP] at h2
        have hbd : Xn6 α (slice g (hor n)) ≤ M := (hbnd (hor n) ⟨hnnonneg, le_rfl⟩).1
        obtain ⟨H, hHsol, hHreg⟩ := hδstep (slice g (hor n)) hdd hsb hbd
        have hval : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
            g z θ (hor n) = H z θ 0 := fun z θ _ _ _ => (hHsol.1 z θ).symm
        -- the junction value of the scheme's source term
        set hR : Fn := fun z θ => epsRHSP α ρ ε Φs E g (hor n) z θ with hRdef
        have hderG : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
            HasDerivWithinAt (fun s => g z θ s) (hR z θ) (Set.Icc 0 (hor n)) (hor n) := by
          intro z θ hz hθ hθ'
          exact hsol.2 z θ (hor n) hz ⟨hθ, hθ'⟩ ⟨hnnonneg, le_rfl⟩
        have hderH : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
            HasDerivWithinAt (fun s => H z θ s) (hR z θ) (Set.Icc 0 δ) 0 := by
          intro z θ hz hθ hθ'
          have h1 := hHsol.2 z θ 0 hz ⟨hθ, hθ'⟩ ⟨le_rfl, le_of_lt hδpos⟩
          have h2 : hR z θ = epsRHSP α ρ ε Φs E H 0 z θ := by
            have h3 : epsRHSP α ρ ε Φs E g (hor n) = epsRHSP α ρ ε Φs E H 0 :=
              Work.FTS.StrongEps.StrongEpsP.epsRHSP_congr
                (W := g) (W' := H) (τ := hor n) (τ' := 0)
                (funext fun z => funext fun θ => (hHsol.1 z θ).symm)
            exact congrFun (congrFun h3 z) θ
          rw [h2]; exact h1
        -- the glued family
        have hFsol : IsEpsSolP α ρ ε (hor n + δ) Φs E g₀
            (concat g (shiftFam H (hor n)) (hor n)) :=
          Work.FTS.StrongEps.StrongEpsP.SolGlueP hnnonneg hδpos hsol hHsol
        have hFreg : EpsRegP α ρ ε (hor n + δ) (concat g (shiftFam H (hor n)) (hor n)) :=
          Work.FTS.StrongEps.StrongEpsP.RegGlueP (Φs := Φs) (E := E) hnnonneg hδpos
            hreg hHreg hval hderG hderH
        have hle : hor (n + 1) ≤ hor n + δ := by
          have hnext : hor (n + 1) = min T (((n : ℝ) + 2) * δ') := by
            show min T ((((n + 1 : ℕ) : ℝ) + 1) * δ') = min T (((n : ℝ) + 2) * δ')
            rw [show (((n + 1 : ℕ) : ℝ) + 1) * δ' = ((n : ℝ) + 2) * δ' by push_cast; ring]
          rw [hnext, hnn]
          refine le_trans (min_le_right _ _) ?_
          have hδ'le : δ' ≤ δ := by rw [hδ'def]; exact min_le_left δ δ₀
          have hmul : ((n : ℝ) + 2) * δ' = ((n : ℝ) + 1) * δ' + δ' := by ring
          rw [hmul]
          linarith
        refine ⟨concat g (shiftFam H (hor n)) (hor n), Work.FTS.StrongEps.StrongEpsP.IsEpsSolP.mono hFsol hle,
          EpsRegP.mono hFreg hle, ?_⟩
        exact hapr hg₀M hsmall₀ (hor (n + 1)) (hhor_pos (n + 1)) (hhor_le (n + 1)) _
          (Work.FTS.StrongEps.StrongEpsP.IsEpsSolP.mono hFsol hle) (EpsRegP.mono hFreg hle)
  obtain ⟨g, hsol, hreg, hbnd⟩ := hpoint N
  have hhorN : hor N = T := by
    show min T ((((N : ℕ) : ℝ) + 1) * δ') = T
    exact min_eq_left (by push_cast; linarith)
  exact ⟨g, by rwa [hhorN] at hsol, by rwa [hhorN] at hreg, by rwa [hhorN] at hbnd⟩

/-! ## The assembly of `EpsUniformMem` -/

/-- **`EpsE4Thr` reduces to its two documented inputs.**  Given
* the datum's angular vanishing `hvan` and its regularity `hd`,
* the datum's *small-ball* condition `hsmall : Xn α (J_ε g₀) ≤ C₀ α²` for small `ε`,
* the small-ball local step `LocalStepP` of the projected scheme, and
* the two-clause sub-horizon a-priori bound `AprioriP` at the constant `M ≥ K`,

the conclusion `EpsUniformMem α ρ Φs E g₀ C₀ K` follows. -/
theorem EpsUniformMem_of_localStep_apriori {α C₀ K M : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn}
    {E : Fn → Fn} {g₀ : Fn}
    (hvan : ∀ z, 0 ≤ z → g₀ z 0 = 0 ∧ g₀ z (π / 2) = 0)
    (hρ : IsSmoothKernel ρ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hK : 0 ≤ K) (h6 : Xn6 α g₀ ≤ K * α ^ 2) (hM : K ≤ M)
    (hsmall : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε ∈ Set.Ioc 0 ε₁,
      Work.FTS.Nonlin.Xn α (Jeps ρ ε g₀) ≤ C₀ * α ^ 2)
    (hd : ∀ ε : ℝ, 0 < ε → EpsDatum α ρ ε g₀)
    (hstep : ∀ ε : ℝ, 0 < ε → LocalStepP α ρ ε Φs E C₀)
    (hapr : ∀ ε : ℝ, 0 < ε → ∀ T : ℝ, 0 < T → AprioriP α ρ ε T Φs E g₀ C₀ M)
    (hdec : ∀ T : ℝ, 0 < T → ∃ Maj : ℝ → ℝ, AprioriDecay α ρ T Φs E g₀ Maj) :
    EpsUniformMem α ρ Φs E g₀ C₀ K := by
  obtain ⟨ε₁, hε₁, hsmallb⟩ := hsmall
  refine ⟨hvan, l12_zero_of_epsDatum ⟨hα, hα1⟩ hρ hd, ?_⟩
  intro T hT
  obtain ⟨Maj, hMajint, hMaj⟩ := hdec T hT
  refine ⟨M, hM, min ε₁ 1, lt_min hε₁ one_pos, Maj, hMajint, ?_⟩
  intro ε hε
  have hεpos : 0 < ε := hε.1
  have hεle : ε ≤ min ε₁ 1 := hε.2
  have hPz : Pz (Jeps ρ ε g₀) = Jeps ρ ε g₀ :=
    Pz_self_of_l12 (Work.FTS.ClassC.ClassC.l12_zero (hd ε hεpos).2.2)
  have hsmall₀ : Work.FTS.Nonlin.Xn α (Pz (Jeps ρ ε g₀)) ≤ C₀ * α ^ 2 := by
    rw [hPz]
    exact hsmallb ε ⟨hεpos, le_trans hεle (min_le_left _ _)⟩
  -- the datum's `ℋ⁶`-size, hence the a-priori's bootstrap value
  have hg₀M : Xn6 α g₀ ≤ M := by
    have hα2le : α ^ 2 ≤ 1 := pow_le_one₀ hα.le hα1
    calc Xn6 α g₀ ≤ K * α ^ 2 := h6
      _ ≤ K * 1 := mul_le_mul_of_nonneg_left hα2le hK
      _ = K := mul_one K
      _ ≤ M := hM
  obtain ⟨g, hsol, hreg, hbnd⟩ :=
    exists_sol_of_localStep_apriori hT (le_trans hK hM) hg₀M hsmall₀
      (EpsDatum.toDatumP (hd ε hεpos)) (hstep ε hεpos) (hapr ε hεpos T hT)
  refine ⟨g, hsol, ?_⟩
  intro τ hτ
  have hdP : EpsDatumP α ρ ε (slice g τ) := hreg.2 τ hτ
  have hCmem : Work.Spaces.HkMem α 7 (slice (JfamP ρ ε g) τ) := hdP.2.2.mem
  have hCsm : Work.FTS.EllipticEst.SmoothOpen (slice (JfamP ρ ε g) τ) := hdP.2.2.reg
  have h4 : Work.Spaces.HkMem α 4 (slice (JfamP ρ ε g) τ) :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hCsm hCmem
  exact ⟨hdP.1, h4, hdP.2.1, (hbnd τ hτ).2, (hbnd τ hτ).1, by rw [slice_JfamP]; exact hdP.2.2,
    hreg.1,
    hMaj ε ⟨hεpos, le_trans hεle (min_le_right _ _)⟩ g hsol hreg τ hτ⟩

end Work.FTS.StrongEps.EpsE4Thr
