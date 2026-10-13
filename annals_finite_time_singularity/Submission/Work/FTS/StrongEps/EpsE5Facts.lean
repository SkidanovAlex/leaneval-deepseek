/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE5Facts.lean` — the interface-free clauses of `E5`

`E5` (`exists_limH`) produces, for every horizon `T`, the limit package `EpsLimPkg` of the
`ε`-scheme.  Its clauses split into two groups:

* the clauses that are read off the **extraction** (`ConvLev0H6`/`ConvLocUnifH6` of the
  approximating sequence) without any further analytic input — these live here, each stated with
  exactly the hypotheses the eventual assembly supplies;
* the clauses whose *source* is a statement-level obligation of the interface `EpsUniformMem`
  (the boundary vanishing of the datum, the per-`z` bound of the level-four slices, the smoothness
  of the slices, the pointwise identification of the right-hand side) — these are listed in
  `NOTES_session10.md` §2 and are *not* asserted here.

## What is here

* `EpsLimBd6` — the `ℋ⁶`-bound of the limit is the one carried by the extraction
  (`ConvLev0H6.hkNorm_le`), never re-derived by an energy estimate on the limit slice.
* `EpsLimBd4` — the `ℋ⁴`-bound of the limit (the proved `Xn_le_of_convLocUnif`).
* `EpsLimMem4` — the honest `ℋ⁴`-membership of the limit from the slot convergence plus the
  **per-`z` bound** of the approximants (the provable form of the `mem4` clause: `HkMem` is a
  per-`z` condition and local uniform convergence + a uniform `ℋ⁶`-bound only give it for a.e.
  `z`; see `NOTES_session7.md` §3.1 and `NOTES_session9.md` §3.2).
* `clampFam` and its API — the **boundary clamp** of a limit family: writing the limit as `F τ`
  on the open quadrant and as the datum on the angular boundary makes the `EpsLimPkg` clauses
  `init` and `vanish` hold *by definition* (given the datum's boundary vanishing), while every
  other clause is about the open quadrant or is an integral/a.e.-statement, hence transported by
  `HkSq_congr_open`/`HkMem_congr_Q0` (the clamp changes the profile only off the open quadrant).

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsConv
import Submission.Work.FTS.StrongEps.ConvLev0Defs
import Submission.Work.FTS.StrongEps.HkMem_of_tendsto
import Submission.Work.FTS.StrongEps.Xn_le_of_convLocUnif
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## The clauses read off the extraction -/

/-- **`bd6`**: the uniform `ℋ⁶`-bound of the limit is the one of the approximating sequence.

The clause of `EpsLimPkg` is `∃ B, ∀ τ, Xn6 α (slice g τ) ≤ B`; `Xn6 = HkNorm α 6`, so the
extraction package carries it directly.  Nothing is re-derived on the limit slice (the design
forbids an `Xn6`/`IP6` estimate on a limit). -/
theorem EpsLimBd6 {α B : ℝ} {G : ℕ → Fn} {f : Fn} (h : ConvLev0H6 α B G f) :
    Work.FTS.StrongGlobal.Xn6 α f ≤ B :=
  h.hkNorm_le

/-- **`bd4`**: the uniform `ℋ⁴`-bound of the limit, from the uniform `ℋ⁴`-bound of the
approximants (lower semicontinuity of the `ℋ⁴`-energy along locally uniform slot convergence).
This is the proved `Xn_le_of_convLocUnif` under the name used by the assembly. -/
theorem EpsLimBd4 {α B C₀ : ℝ} {G : ℕ → Fn} {f : Fn}
    (hconv : ConvLocUnifH6 α B G f)
    (hmem : ∀ n : ℕ, Work.Spaces.HkMem α 4 (G n))
    (hbsq : ∀ n : ℕ, Work.FTS.Nonlin.Xn α (G n) ≤ C₀ * α ^ 2) :
    Work.FTS.Nonlin.Xn α f ≤ C₀ * α ^ 2 :=
  Xn_le_of_convLocUnif hconv hmem hbsq

/-- **`mem4`**: the honest `ℋ⁴`-membership of the limit, from the slot convergence, the
`ℋ⁶`-membership and uniform `ℋ⁶`-bound of the approximants, and the **per-`z` bound**

  `∀ z ∈ Iz, ∃ Bz, ∀ n, ∫_θ HkIntegrand α 4 (G n) z θ ≤ Bz`

of the approximating sequence.  The per-`z` hypothesis is *not* removable: `HkMem` is a per-`z`
condition while Fatou only gives it a.e. in `z`, and a uniform `ℋ⁶`-bound does not control the
per-`z` slice integrals (the family `G n (z,θ) = ψ n z · θ^{a n}`, `a n ↓ (γ-1)/2`, is the sharp
witness — see `NOTES_session9.md` §3.2). -/
theorem EpsLimMem4 {α B : ℝ} {G : ℕ → Fn} {f : Fn}
    (hconv : ConvLocUnifH6 α B G f)
    (hsm : ∀ n : ℕ, ∀ k : ℕ,
      ContDiffOn ℝ k (Function.uncurry (G n)) Work.FTS.EllipticEst.Q0)
    (hmem : ∀ n : ℕ, Work.Spaces.HkMem α 6 (G n))
    (hb : ∀ n : ℕ, Work.Spaces.HkNorm α 6 (G n) ≤ B)
    (hz : ∀ z ∈ Work.Spaces.Iz, ∃ Bz : ℝ, ∀ n : ℕ,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 (G n) z θ) ≤ Bz) :
    Work.Spaces.HkMem α 4 f ∧ Work.Spaces.HkNorm α 4 f ≤ B := by
  refine HkMem_of_tendsto (k := 4) (m := 6) (by norm_num)
    (fun n => hsm n 4) hconv.contDiffOn ?_ hmem hb hz
  intro j i hji z θ hzθ
  have hK : IsCompact ({(z, θ)} : Set (ℝ × ℝ)) := isCompact_singleton
  have hKQ : ({(z, θ)} : Set (ℝ × ℝ)) ⊆ Work.FTS.EllipticEst.Q0 := by
    intro p hp
    rw [Set.mem_singleton_iff] at hp
    subst hp
    exact hzθ
  exact (hconv.conv {(z, θ)} hK hKQ j i hji).tendsto_at (Set.mem_singleton _)

/-! ## The clamped limit family — `init` and `vanish` by definition -/

/-- **The boundary clamp of a limit family.**  `F : ℝ → Fn` is the profile of the limit at each
fake time (on the open quadrant) and `g₀` supplies the angular boundary values.

Every clause of `EpsLimPkg` other than `init`/`vanish` is a statement about the open quadrant
`Qd`/`Q0`, or an a.e./integral statement; the clamp changes the profile only off the open
quadrant, so all of them transport (`clampFam_hkSq`, `clampFam_hkMem`, `clampFam_contDiffOn`,
`clampFam_contDiffOn_one`).  This is what makes the two boundary clauses free once the datum
vanishes on the angular boundary — and the datum's vanishing is a *necessary* hypothesis
(`NOTES_session9.md` §8). -/
def clampFam (F : ℝ → Fn) (g₀ : Fn) : Fam := fun z θ τ =>
  if θ ∈ Set.Ioo 0 (π / 2) then F τ z θ else g₀ z θ

/-- On the open angular interval the clamp is the limit family. -/
theorem clampFam_of_mem {F : ℝ → Fn} {g₀ : Fn} {z θ τ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    clampFam F g₀ z θ τ = F τ z θ := if_pos hθ

/-- Off the open angular interval the clamp is the datum. -/
theorem clampFam_of_not_mem {F : ℝ → Fn} {g₀ : Fn} {z θ τ : ℝ}
    (hθ : θ ∉ Set.Ioo 0 (π / 2)) : clampFam F g₀ z θ τ = g₀ z θ := if_neg hθ

/-- The clamp agrees with the plain limit profile on the open quadrant. -/
theorem clampFam_agreeOnQ (F : ℝ → Fn) (g₀ : Fn) (τ : ℝ) :
    Work.FTS.EllipticEst.AgreeOnQ (slice (clampFam F g₀) τ) (F τ) :=
  fun z θ _ hθ hlt => clampFam_of_mem ⟨hθ, hlt⟩

/-- The `ℋᵏ`-square is unchanged by the clamp (it only sees the open quadrant). -/
theorem clampFam_hkSq (α : ℝ) (k : ℕ) (F : ℝ → Fn) (g₀ : Fn) (τ : ℝ) :
    Work.Spaces.HkSq α k (slice (clampFam F g₀) τ) = Work.Spaces.HkSq α k (F τ) :=
  Work.FTS.EllipticEst.HkSq_congr_open α k (fun z θ _ hθ hlt => clampFam_of_mem ⟨hθ, hlt⟩)

/-- The `ℋᵏ`-norm is unchanged by the clamp. -/
theorem clampFam_hkNorm (α : ℝ) (k : ℕ) (F : ℝ → Fn) (g₀ : Fn) (τ : ℝ) :
    Work.Spaces.HkNorm α k (slice (clampFam F g₀) τ) = Work.Spaces.HkNorm α k (F τ) := by
  rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, clampFam_hkSq]

/-- The `ℋᵏ`-membership is unchanged by the clamp. -/
theorem clampFam_hkMem (α : ℝ) (k : ℕ) {F : ℝ → Fn} {g₀ : Fn} {τ : ℝ}
    (h : Work.Spaces.HkMem α k (F τ)) : Work.Spaces.HkMem α k (slice (clampFam F g₀) τ) :=
  Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α k h
    (fun z _ θ hθ => (clampFam_of_mem hθ).symm)

/-- **`init` for the clamped family**: the datum is attained at `τ = 0`. -/
theorem clampFam_init {F : ℝ → Fn} {g₀ : Fn}
    (hF : ∀ z θ, θ ∈ Set.Ioo 0 (π / 2) → F 0 z θ = g₀ z θ) :
    ∀ z θ, clampFam F g₀ z θ 0 = g₀ z θ := by
  intro z θ
  by_cases hθ : θ ∈ Set.Ioo 0 (π / 2)
  · rw [clampFam_of_mem hθ]
    exact hF z θ hθ
  · rw [clampFam_of_not_mem hθ]

/-- **`vanish` for the clamped family**, from the datum's boundary vanishing. -/
theorem clampFam_vanish {F : ℝ → Fn} {g₀ : Fn}
    (h0 : ∀ z, 0 ≤ z → g₀ z 0 = 0 ∧ g₀ z (π / 2) = 0) :
    ∀ τ z, 0 ≤ z → clampFam F g₀ z 0 τ = 0 ∧ clampFam F g₀ z (π / 2) τ = 0 := by
  intro τ z hz
  have h0' : (0 : ℝ) ∉ Set.Ioo 0 (π / 2) := fun h => absurd h.1 (lt_irrefl 0)
  have h1' : (π / 2 : ℝ) ∉ Set.Ioo 0 (π / 2) := fun h => absurd h.2 (lt_irrefl (π / 2))
  rw [clampFam_of_not_mem h0', clampFam_of_not_mem h1']
  exact h0 z hz

/-- The clamp is `C⁴` in space wherever the limit profile is. -/
theorem clampFam_contDiffOn {F : ℝ → Fn} {g₀ : Fn} {τ : ℝ}
    (h : ContDiffOn ℝ 4 (Function.uncurry (F τ)) Work.FTS.EllipticEst.Q0) :
    ContDiffOn ℝ 4 (Function.uncurry (slice (clampFam F g₀) τ)) Work.FTS.EllipticEst.Q0 :=
  h.congr (fun p hp => clampFam_of_mem hp.2)

/-- The clamp is jointly `C¹` wherever the limit family is. -/
theorem clampFam_contDiffOn_one {F : ℝ → Fn} {g₀ : Fn}
    (h : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => F p.2.2 p.1 p.2.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Ioi 0)) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => clampFam F g₀ p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Ioi 0) :=
  h.congr (fun p hp => clampFam_of_mem (z := p.1) (θ := p.2.1) (τ := p.2.2) hp.2.1)

/-- Continuity in the fake time transports to the clamp on the open quadrant. -/
theorem clampFam_continuousOn {F : ℝ → Fn} {g₀ : Fn} {z θ : ℝ} {T : ℝ}
    (h : ContinuousOn (fun τ => F τ z θ) (Set.Icc 0 T)) :
    ContinuousOn (fun τ => clampFam F g₀ z θ τ) (Set.Icc 0 T) := by
  by_cases hθ : θ ∈ Set.Ioo 0 (π / 2)
  · exact h.congr (fun τ _ => clampFam_of_mem hθ)
  · simp only [clampFam_of_not_mem hθ]
    exact continuousOn_const

end Work.FTS.StrongEps
