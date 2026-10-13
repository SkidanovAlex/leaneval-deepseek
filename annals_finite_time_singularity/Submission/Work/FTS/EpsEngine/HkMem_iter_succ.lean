/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/HkMem_iter_succ.lean` — (H4)(a): the Picard iterates are
# `ℋ^k`-honest, reduced to the interval-integral lemma + the per-`z` data

`Submission/Work/FTS/EpsEngine/NOTES_perz_intervalIntegral.md` §1–§3 records that

* the residual item `(H4)` of `NOTES_BallClause.md` §7 (`∀ N, HkMem α 4 (slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ N) τ)`,
  and its order-`6` twin for `hd`) is *false* in the naive "Cauchy–Schwarz + uniform `ℋ`-bound"
  form (the workspace's own `E5G/NOTES_slice_lip_HkSq_misstated.md`, machine-checked);
* the honest repair is the interval-integral lemma with a **per-`z` energy bound**
  (`Work.FTS.EpsEngine.HkMem_intervalIntegralPerz`, delegated) plus per-slice honesty `hmem`.

This module performs the assembly step: with the conclusion of that lemma supplied as the explicit
hypothesis `hint` (so that the file is independent of the delegated module), the `(n+1)`-st Picard
iterate is `ℋ^k`-honest with the expected norm bound

    |slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ (n+1)) τ|_{ℋ^k} ≤ |h₀|_{ℋ^k} + B · τ ,

where `B` is the uniform `ℋ^k`-bound of the right-hand side along the `n`-th iterate.  The
hypotheses `hIsmo` (`C^∞` of the increment on the open quadrant) is exactly the `SmoothOpen` clause
of the invariant (proved on the route by the lead's Fubini ruling, `SORuling.smoothOpen_*`).

`Work.FTS.EpsEngine.HkMem_intervalIntegralPerz` (now proved) discharges `hint` verbatim: the
corollary `HkMem_iter_succ_of_data` below is the same statement with the seven hypotheses of that
lemma in place of `hint`.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.StrongEps.EpsE4Thr.HkNorm_triangle
import Submission.Work.FTS.StrongEps.EpsLocalPStar.VolterraAux.Iter
import Submission.Work.FTS.EpsEngine.HkMem_intervalIntegralPerz

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.EpsEngine

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **(H4)(a), assembled.**  If the increment `∫₀^τ F (slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ n) ·)` is `ℋ^k`-honest with
the norm bound `B·τ` (the conclusion of the repaired interval-integral lemma), then so is the
`(n+1)`-st Picard iterate. -/
theorem HkMem_iter_succ {α B : ℝ} {F : Fn → Fn} {h₀ : Fn} {k : ℕ} {T τ : ℝ} {n : ℕ}
    (hτ : 0 ≤ τ) (hτT : τ ≤ T) (hB : 0 ≤ B)
    (h₀smo : Work.FTS.EllipticEst.SmoothOpen h₀)
    (h₀mem : Work.Spaces.HkMem α k h₀)
    (hIsmo : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => ∫ s in (0 : ℝ)..τ, F (slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ n) s) z θ))
    (hint : Work.Spaces.HkMem α k
        (fun z θ => ∫ s in (0 : ℝ)..τ, F (slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ n) s) z θ) ∧
      Work.Spaces.HkNorm α k
        (fun z θ => ∫ s in (0 : ℝ)..τ, F (slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ n) s) z θ) ≤ B * τ) :
    Work.Spaces.HkMem α k (slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ (n + 1)) τ) ∧
      Work.Spaces.HkNorm α k (slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ (n + 1)) τ)
        ≤ Work.Spaces.HkNorm α k h₀ + B * τ := by
  have hslice : slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ (n + 1)) τ
      = fun z θ => h₀ z θ + ∫ s in (0 : ℝ)..τ, F (slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ n) s) z θ := by
    funext z θ
    simp only [Work.FTS.Galerkin.slice_apply, Work.FTS.StrongEps.EpsLocalPStar.iter_succ]
  rw [hslice]
  obtain ⟨hmemI, hbdI⟩ := hint
  have h₀c : ∀ m : ℕ, ContDiffOn ℝ m (Function.uncurry h₀) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp h₀smo
  have hIc : ∀ m : ℕ, ContDiffOn ℝ m
      (Function.uncurry (fun z θ => ∫ s in (0 : ℝ)..τ, F (slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ n) s) z θ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hIsmo
  refine ⟨Work.FTS.EllipticEst.HkMem_add_open h₀smo hIsmo h₀mem hmemI, ?_⟩
  refine (Work.FTS.StrongEps.EpsE4Thr.HkNorm_triangle α k h₀c hIc h₀mem hmemI).trans ?_
  exact add_le_add le_rfl hbdI

/-- **(H4)(a) with the interval-integral lemma plugged in.**  The same conclusion as
`HkMem_iter_succ`, with `hint` discharged by `Work.FTS.EpsEngine.HkMem_intervalIntegralPerz` applied
to the family `H s = F (slice (iter F h₀ n) s)`. -/
theorem HkMem_iter_succ_of_data {α B : ℝ} {F : Fn → Fn} {h₀ : Fn} {k : ℕ} {T τ : ℝ} {n : ℕ}
    (hτ : 0 ≤ τ) (hτT : τ ≤ T) (hT : 0 ≤ T) (hB : 0 ≤ B)
    (h₀smo : Work.FTS.EllipticEst.SmoothOpen h₀)
    (h₀mem : Work.Spaces.HkMem α k h₀)
    (hIsmo : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => ∫ s in (0 : ℝ)..τ, F (slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ n) s) z θ))
    (hHsm : ∀ s ∈ Set.Icc 0 T,
      Work.FTS.EllipticEst.SmoothOpen (F (slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ n) s)))
    (hHmem : ∀ s ∈ Set.Icc 0 T,
      Work.Spaces.HkMem α k (F (slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ n) s)))
    (hHbd : ∀ s ∈ Set.Icc 0 T,
      Work.Spaces.HkNorm α k (F (slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ n) s)) ≤ B)
    (hmeas : ∀ (j i : ℕ), j + i ≤ k → ∀ z θ : ℝ,
      (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      MeasureTheory.AEStronglyMeasurable
        (fun s : ℝ => Work.Spaces.mixed j i
          (F (slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ n) s)) z θ)
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)))
    (hjoint : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => Work.Spaces.HkIntegrand α k
        (F (slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ n) p.1)) p.2.1 p.2.2)
      ((MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)).prod
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))))
    (hsup : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ q ∈ K, ∀ (j i : ℕ), j + i ≤ k →
        |Work.Spaces.mixed j i
          (F (slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ n) s)) q.1 q.2| ≤ C)
    (hperz : ∀ z ∈ Work.Spaces.Iz, ∃ Cz : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) T,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k
        (F (slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ n) s)) z θ) ≤ Cz) :
    Work.Spaces.HkMem α k (slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ (n + 1)) τ) ∧
      Work.Spaces.HkNorm α k (slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ (n + 1)) τ)
        ≤ Work.Spaces.HkNorm α k h₀ + B * τ := by
  obtain ⟨hmemI, hbdI⟩ :=
    HkMem_intervalIntegralPerz (α := α) (B := B) (k := k) (T := T) (a := 0) (b := τ)
      (H := fun s z θ => F (slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ n) s) z θ)
      hτ hT ⟨le_rfl, hT⟩ ⟨hτ, hτT⟩ hHsm hHmem hHbd hmeas hjoint hsup hperz
  have hbdI' : Work.Spaces.HkNorm α k
      (fun z θ => ∫ s in (0 : ℝ)..τ, F (slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ n) s) z θ)
      ≤ B * τ := by
    simpa only [sub_zero] using hbdI
  exact HkMem_iter_succ (F := F) (h₀ := h₀) (k := k) (T := T) (τ := τ) (n := n)
    hτ hτT hB h₀smo h₀mem hIsmo ⟨hmemI, hbdI'⟩

end Work.FTS.EpsEngine
