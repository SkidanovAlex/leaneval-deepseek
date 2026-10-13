/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/HkMemIterAll.lean` — the `(H4)` chapter of the local step:
# the RAW Picard slices are `ℋ^k`-honest

`EpsEngine/NOTES_BallClause.md` §7 and `EpsEngine/NOTES_perz_intervalIntegral.md` §7 record that
the two *ball clauses* of the local step (`Xn_PzJeps_limFam_le_of_tail` for `hlimP`,
`Xn_PzJeps_iter_succ_le` for `hkeepIter`) are reduced to the single residual item

    (H4)   ∀ n, HkMem α 4 (slice (iter F h₀ n) τ)    and    HkMem α 4 (slice (limFam F h₀) τ),

the `ℋ⁴`-honesty of the **raw** (un-projected, un-mollified) Picard slices.  The engine has
`HkMem_iter_succ_of_data` (`EpsEngine/HkMem_iter_succ.lean`, proved): **one** Picard step is
honest, given the interval-integral data of the right-hand side along the curve.  What was
missing is the *iteration* of that step over `n` and the *passage to the limit*.

This module supplies both:

* `RHSData` — the per-curve data of the right-hand side that the step consumes, packaged as a
  structure (the seven hypotheses of `Work.FTS.EpsEngine.HkMem_intervalIntegralPerz`, uniformly
  over the curve `s ↦ slice (iter F h₀ n) s`);
* `HkMem_iter_all` — the induction: `∀ n, HkMem α k (slice (iter F h₀ n) τ)` together with the
  norm bound `≤ HkNorm α k h₀ + B * τ`;
* `HkMem_limFam_of_slot_conv` — the limit, by `Work.FTS.StrongEps.HkMem_of_tendsto` (Fatou); the
  hypotheses are exactly the slot convergence of the iterates to the limit and the per-`z` bound
  (which is uniform in `n` because `HkMem_iter_all` gives it uniformly in `n`).

The two consumers (`EpsEngine/BallLimFam.lean`) then receive (H4) verbatim; the assembly is
`ball_iter_succ_of_HkMem` / `ball_limFam_of_HkMem`, which are one-line applications of the
already-proved ball-clause lemmas.

**What is left of the (H4) chapter** is therefore *only* the production of `RHSData` for the
scheme's right-hand side `F = Feps α ρ ε Φs E` (see `NOTES_HkMemIterAll.md`): the `smo`/`mem`
fields are produced by `EpsRLX.XDataClean` + `PZeroAux.PzJepsHkMem`, the `bd` field by
`EpsSqTools.HkSq_JepsPz_le` + `EpsRLX.ProfRHSEpsData`, and the `perz` field by
`HkIntegrand_perz_RHS` — the last being the *only* place where the trace data
`BdryTraces α 6 (Feps u)` (the class-`C`/flatness item) is consumed.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EpsEngine.HkMem_iter_succ
import Submission.Work.FTS.EpsEngine.BallLimFam
import Submission.Work.FTS.StrongEps.HkMem_of_tendsto

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

open Work.FTS.StrongEps.EpsLocalPStar (iter limFam)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The per-curve data of the right-hand side -/

/-- **The data of the right-hand side along the `n`-th Picard curve** `s ↦ slice (iter F h₀ n) s`:
the seven hypotheses of `Work.FTS.EpsEngine.HkMem_intervalIntegralPerz`, held uniformly over the
curve.  This is the honest residue of (H4)(a) after `NOTES_perz_intervalIntegral.md`. -/
structure RHSData (α : ℝ) (k : ℕ) (T B : ℝ) (F : Fn → Fn) (h₀ : Fn) (n : ℕ) : Prop where
  smo : ∀ s ∈ Set.Icc (0 : ℝ) T,
    Work.FTS.EllipticEst.SmoothOpen (F (slice (iter F h₀ n) s))
  mem : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.Spaces.HkMem α k (F (slice (iter F h₀ n) s))
  bd : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.Spaces.HkNorm α k (F (slice (iter F h₀ n) s)) ≤ B
  meas : ∀ (j i : ℕ), j + i ≤ k → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
    MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => Work.Spaces.mixed j i (F (slice (iter F h₀ n) s)) z θ)
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T))
  joint : MeasureTheory.AEStronglyMeasurable
    (fun p : ℝ × ℝ × ℝ => Work.Spaces.HkIntegrand α k (F (slice (iter F h₀ n) p.1)) p.2.1 p.2.2)
    ((MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)).prod
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
  sup : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ q ∈ K, ∀ (j i : ℕ), j + i ≤ k →
      |Work.Spaces.mixed j i (F (slice (iter F h₀ n) s)) q.1 q.2| ≤ C
  perz : ∀ z ∈ Work.Spaces.Iz, ∃ Cz : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) T,
    (∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (F (slice (iter F h₀ n) s)) z θ) ≤ Cz

/-! ## The induction over the Picard iterates -/

/-- **The smoothness of the increment, from the smoothness of the next slice.**  If the
`(n+1)`-st slice `h₀ + ∫₀^τ F ∘ slice (iter n)` is `SmoothOpen` and so is `h₀`, then the
increment itself is `SmoothOpen` — the `hIsmo` input of `HkMem_iter_succ_of_data`. -/
theorem smoothOpen_increment {F : Fn → Fn} {h₀ : Fn} {τ : ℝ} {n : ℕ}
    (h₀smo : Work.FTS.EllipticEst.SmoothOpen h₀)
    (hsmo : Work.FTS.EllipticEst.SmoothOpen (slice (iter F h₀ (n + 1)) τ)) :
    Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => ∫ s in (0 : ℝ)..τ, F (slice (iter F h₀ n) s) z θ) := by
  have hsub := Work.FTS.EllipticEst.smoothOpen_sub hsmo h₀smo
  have hfun : (fun z θ => slice (iter F h₀ (n + 1)) τ z θ - h₀ z θ)
      = fun z θ => ∫ s in (0 : ℝ)..τ, F (slice (iter F h₀ n) s) z θ := by
    funext z θ
    rw [show slice (iter F h₀ (n + 1)) τ z θ
        = h₀ z θ + ∫ s in (0 : ℝ)..τ, F (slice (iter F h₀ n) s) z θ from by
      rw [Work.FTS.StrongEps.EpsLocalPStar.iter_succ]
      rfl]
    ring
  rwa [hfun] at hsub

/-- **(H4)(a) iterated: every Picard slice is `ℋ^k`-honest**, with the norm bound
`HkNorm α k (slice (iter F h₀ n) τ) ≤ HkNorm α k h₀ + B * τ` (the same `B` for all `n`, from the
uniform right-hand-side data). -/
theorem HkMem_iter_all {α B : ℝ} {F : Fn → Fn} {h₀ : Fn} {k : ℕ} {T τ : ℝ}
    (hτ : 0 ≤ τ) (hτT : τ ≤ T) (hT : 0 ≤ T) (hB : 0 ≤ B)
    (h₀smo : Work.FTS.EllipticEst.SmoothOpen h₀)
    (h₀mem : Work.Spaces.HkMem α k h₀)
    (hsmo : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (slice (iter F h₀ n) τ))
    (hdata : ∀ n : ℕ, RHSData α k T B F h₀ n) :
    ∀ n : ℕ, Work.Spaces.HkMem α k (slice (iter F h₀ n) τ) ∧
      Work.Spaces.HkNorm α k (slice (iter F h₀ n) τ) ≤ Work.Spaces.HkNorm α k h₀ + B * τ := by
  intro n
  induction n with
  | zero =>
      have hE : slice (iter F h₀ 0) τ = h₀ := rfl
      refine ⟨?_, ?_⟩
      · rw [hE]; exact h₀mem
      · rw [hE]
        exact le_add_of_nonneg_right (mul_nonneg hB hτ)
  | succ n ih =>
      exact HkMem_iter_succ_of_data (F := F) (h₀ := h₀) (k := k) (T := T) (τ := τ) (n := n)
        hτ hτT hT hB h₀smo h₀mem (smoothOpen_increment h₀smo (hsmo (n + 1)))
        (hdata n).smo (hdata n).mem (hdata n).bd (hdata n).meas (hdata n).joint (hdata n).sup
        (hdata n).perz

/-! ## The limit -/

/-- **(H4)(b): the limit slice is `ℋ^k`-honest.**  Fatou along the Picard iterates
(`Work.FTS.StrongEps.HkMem_of_tendsto`): the hypotheses are the iterate-wise membership and norm
bound (from `HkMem_iter_all`), the `C^k`-regularity of the iterates and of the limit, the
pointwise **slot** convergence of the iterates to the limit, and the per-`z` bound (uniform in
`n`, which `HkMem_iter_all` supplies). -/
theorem HkMem_limFam_of_slot_conv {α B : ℝ} {F : Fn → Fn} {h₀ : Fn} {k : ℕ} {τ : ℝ}
    (hiter : ∀ n : ℕ, Work.Spaces.HkMem α k (slice (iter F h₀ n) τ))
    (hb : ∀ n : ℕ, Work.Spaces.HkNorm α k (slice (iter F h₀ n) τ) ≤ B)
    (hsmG : ∀ n : ℕ, ContDiffOn ℝ k (Function.uncurry (slice (iter F h₀ n) τ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hsmf : ContDiffOn ℝ k (Function.uncurry (slice (limFam F h₀) τ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hconv : ∀ (j i : ℕ), j + i ≤ k → ∀ z θ : ℝ,
      (z, θ) ∈ (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i (slice (iter F h₀ n) τ) z θ)
        Filter.atTop (nhds (Work.Spaces.mixed j i (slice (limFam F h₀) τ) z θ)))
    (hz : ∀ z ∈ Work.Spaces.Iz, ∃ Bz : ℝ, ∀ n : ℕ,
      (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (slice (iter F h₀ n) τ) z θ) ≤ Bz) :
    Work.Spaces.HkMem α k (slice (limFam F h₀) τ) ∧
      Work.Spaces.HkNorm α k (slice (limFam F h₀) τ) ≤ B :=
  Work.FTS.StrongEps.HkMem_of_tendsto (k := k) (m := k) le_rfl hsmG hsmf hconv hiter hb hz

/-! ## The two ball clauses of the local step, with (H4) supplied -/

/-- **The ball clause of `hkeepIter`**, with the `ℋ⁴`-honesty of the raw slices taken from
`HkMem_iter_all` instead of being a hypothesis. -/
theorem ball_iter_succ_of_HkMem {α ε C₀ Cj B τ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {F : Fn → Fn} {h₀ : Fn} {n : ℕ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hα : α ∈ Set.Ioc 0 1) (hε : 0 < ε)
    (hτ : 0 ≤ τ) (hB : 0 ≤ B) (hCj : 0 ≤ Cj)
    (hgate : ∀ f : Fn, Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.StrongEps.EpsMem α f →
      Work.Spaces.HkSq α 4 (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε f))
        ≤ Cj * Work.FTS.StrongEps.EpsSq α f)
    (hsm0 : Work.FTS.EllipticEst.SmoothOpen h₀)
    (hsmU : Work.FTS.EllipticEst.SmoothOpen (slice (iter F h₀ (n + 1)) τ))
    (hm0 : Work.Spaces.HkMem α 4 h₀)
    (hmU : Work.Spaces.HkMem α 4 (slice (iter F h₀ (n + 1)) τ))
    (hGmeas : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => F (slice (iter F h₀ n) p.1) p.2.1 p.2.2
        * Work.FTS.StrongEps.epsW α p.2.1 p.2.2)
      ((MeasureTheory.volume.restrict (Set.uIoc 0 τ)).prod Work.FTS.StrongEps.EpsLocalPStar.DomM))
    (hGbd : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ)),
      Work.FTS.StrongEps.EpsLocalPStar.epsL2 α (F (slice (iter F h₀ n) s))
        ≤ ENNReal.ofReal B)
    (hxn0 : Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε h₀))
      ≤ C₀ * α ^ 2) :
    Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε
        (slice (iter F h₀ (n + 1)) τ)))
      ≤ C₀ * α ^ 2 + Real.sqrt (Cj * (τ * (τ * B))) :=
  Xn_PzJeps_iter_succ_le (α := α) (ε := ε) (C₀ := C₀) (Cj := Cj) (B := B) (τ := τ)
    (ρ := ρ) (Φs := Φs) (E := E) (F := F) (h₀ := h₀) (n := n)
    hρ hα hε hτ hB hCj hgate hsm0 hsmU hm0 hmU hGmeas hGbd hxn0

/-- **The ball clause of `hlimP`**, with the `ℋ⁴`-honesty of the raw slices and of the limit taken
from (H4) instead of being hypotheses. -/
theorem ball_limFam_of_HkMem {α ε C₀ q : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {F : Fn → Fn} {h₀ : Fn} {τ : ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hα : α ∈ Set.Ioc 0 1) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hxn : ∀ N : ℕ, Work.FTS.Nonlin.Xn α
      (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε (slice (iter F h₀ N) τ)))
        ≤ C₀ * α ^ 2)
    (htail : ∀ N : ℕ, 1 ≤ N →
      Work.FTS.StrongEps.EpsMem α (fun z θ =>
        slice (limFam F h₀) τ z θ - slice (iter F h₀ N) τ z θ) ∧
      Work.FTS.StrongEps.EpsSq α (fun z θ =>
        slice (limFam F h₀) τ z θ - slice (iter F h₀ N) τ z θ) ≤ q ^ N)
    (hsmoN : ∀ N : ℕ, Work.FTS.EllipticEst.SmoothOpen (slice (iter F h₀ N) τ))
    (hsmoW : Work.FTS.EllipticEst.SmoothOpen (slice (limFam F h₀) τ))
    (hmemN : ∀ N : ℕ, Work.Spaces.HkMem α 4 (slice (iter F h₀ N) τ))
    (hmemW : Work.Spaces.HkMem α 4 (slice (limFam F h₀) τ)) :
    Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε
        (slice (limFam F h₀) τ))) ≤ C₀ * α ^ 2 :=
  Xn_PzJeps_limFam_le_of_tail (α := α) (ε := ε) (C₀ := C₀) (q := q)
    (ρ := ρ) (Φs := Φs) (E := E) (F := F) (h₀ := h₀) (τ := τ)
    hρ hα hε hε1 hq0 hq1 hxn htail hsmoN hsmoW hmemN hmemW

end Work.FTS.EpsEngine
