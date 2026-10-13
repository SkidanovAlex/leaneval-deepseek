/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/E5Clauses.lean` — the clauses of `EpsLimPkg` read off the limit

`EpsExtract` produces, for every horizon `T`, a subsequence `φ` and a limit curve `F` with the
convergence package `ConvLocUnifH6 α B (slice (G (φ n)) τ) (F τ)` at **every** `τ ∈ Icc 0 T`.
The limit *family* of `EpsLimPkg` is then the **quadrant clamp**

  `clampQ F g₀ z θ τ = if z ∈ Ioi 0 then (if θ ∈ Ioo 0 (π/2) then F τ z θ else g₀ z θ) else g₀ z θ`

(`E5Clamp.lean`), which makes the two boundary clauses `init` and `vanish` hold by construction;
every other clause is about the open quadrant, so it transports along the clamp
(`clampQ_hkNorm`, `clampQ_hkMem`, `clampQ_contDiffOn`, `clampQ_contDiffOn_one`,
`clampQ_continuousOn`).

This module collects, in one place, the clauses of `EpsLimPkg` that follow from the extraction
alone — i.e. the ones that need **no** analytic input beyond the convergence package:

* `E5_init`, `E5_vanish` — the datum and the angular vanishing;
* `E5_c4` — `C⁴` in space;
* `E5_bd6` — the uniform `ℋ⁶`-bound carried through from the approximants;
* `E5_cont` — continuity in the fake time (from the extraction plus the τ-Lipschitz property);
* `E5_bd4` — the uniform `ℋ⁴`-bound (lower semicontinuity, with the `ℋ⁴`-bound of the
  *converging* sequence as the input);
* `E5_mem4` — the honest `ℋ⁴`-membership (the proved `EpsLimMem4`, whose per-`z` input is the
  one genuinely non-Fatou hypothesis).

The remaining clauses (`law`, `eqT`, `c1`, `dbd`, `limApprox`, uniqueness) have their own modules:
`E5Law.lean` proves `law`; the rest are listed in `NOTES_session13.md` §3.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.E5Clamp
import Submission.Work.FTS.StrongEps.E5Extract
import Submission.Work.FTS.StrongEps.EpsLimCont

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
set_option linter.unusedVariables false

/-! ## The two boundary clauses -/

/-- **`init`.**  The clamp attains the datum at `τ = 0`, because the *approximants* do: at
`τ = 0` every `slice (G k) 0` is the datum (`IsEpsSolP.init`), so the limit `F 0` agrees with
`g₀` on the open quadrant, and the clamp agrees with the datum off it. -/
theorem E5_init {α B T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {ε : ℕ → ℝ} {G : ℕ → Fam} {φ : ℕ → ℕ} {F : ℝ → Fn}
    (hsol : ∀ k : ℕ, IsEpsSolP α ρ (ε k) T Φs E g₀ (G k))
    (hconv0 : ConvLocUnifH6 α B (fun n => slice (G (φ n)) 0) (F 0)) :
    ∀ z θ, clampQ F g₀ z θ 0 = g₀ z θ := by
  refine clampQ_init ?_
  intro z θ hz hθ
  have hK : ({(z, θ)} : Set (ℝ × ℝ)) ⊆ Work.FTS.EllipticEst.Q0 := by
    intro p hp
    rw [Set.mem_singleton_iff] at hp
    subst hp
    exact Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have hpt : Filter.Tendsto (fun n : ℕ => slice (G (φ n)) 0 z θ) Filter.atTop
      (𝓝 (F 0 z θ)) := by
    have h1 := (hconv0.conv {(z, θ)} isCompact_singleton hK 0 0 (by norm_num)).tendsto_at
      (Set.mem_singleton _)
    simpa only [Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_zero,
      Work.FTS.Galerkin.slice_apply] using h1
  have hconst : (fun n : ℕ => slice (G (φ n)) 0 z θ) = fun _ : ℕ => g₀ z θ := by
    funext n
    exact (hsol (φ n)).1 z θ
  rw [hconst] at hpt
  exact tendsto_nhds_unique hpt tendsto_const_nhds

/-- **`vanish`.**  The clamp vanishes on the two angular boundary lines for `z ≥ 0` as soon as
the datum does — which is the first conjunct of `EpsUniformMem` (and a *necessary* condition,
`EpsLimNecessary.ExistsLimH.datum_vanish`). -/
theorem E5_vanish {F : ℝ → Fn} {g₀ : Fn}
    (hvan : ∀ z, 0 ≤ z → g₀ z 0 = 0 ∧ g₀ z (π / 2) = 0) :
    ∀ τ z, 0 ≤ z → clampQ F g₀ z 0 τ = 0 ∧ clampQ F g₀ z (π / 2) τ = 0 :=
  clampQ_vanish hvan

/-! ## The space-regularity clause -/

/-- **`c4`.**  The clamped limit family is `C⁴` in space at every `τ ∈ Icc 0 T`. -/
theorem E5_c4 {α B T : ℝ} {g₀ : Fn} {G : ℕ → Fam} {φ : ℕ → ℕ} {F : ℝ → Fn}
    (hconv : ∀ τ ∈ Set.Icc (0 : ℝ) T,
      ConvLocUnifH6 α B (fun n => slice (G (φ n)) τ) (F τ)) :
    ∀ τ ∈ Set.Icc (0 : ℝ) T,
      ContDiffOn ℝ 4 (Function.uncurry (slice (clampQ F g₀) τ))
        Work.FTS.EllipticEst.Q0 :=
  fun τ hτ => clampQ_contDiffOn (hconv τ hτ).contDiffOn

/-! ## The two norm clauses -/

/-- **`bd6`.**  The uniform `ℋ⁶`-bound of the limit is the one carried by the extraction; nothing
is re-derived on the limit slice. -/
theorem E5_bd6 {α B T : ℝ} {g₀ : Fn} {G : ℕ → Fam} {φ : ℕ → ℕ} {F : ℝ → Fn}
    (hconvL : ∀ τ ∈ Set.Icc (0 : ℝ) T,
      ConvLev0H6 α B (fun n => slice (G (φ n)) τ) (F τ)) :
    ∃ B' : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.StrongGlobal.Xn6 α (slice (clampQ F g₀) τ) ≤ B' := by
  refine ⟨B, fun τ hτ => ?_⟩
  have h := clampQ_hkNorm α 6 F g₀ τ
  show Work.Spaces.HkNorm α 6 (slice (clampQ F g₀) τ) ≤ B
  rw [h]
  exact (hconvL τ hτ).hkNorm_le

/-- **`bd4`.**  The uniform `ℋ⁴`-bound of the limit, by lower semicontinuity of the `ℋ⁴`-energy
along the slotwise local uniform convergence (`Xn_le_of_convLocUnif`).  The input is the uniform
`ℋ⁴`-bound and membership of the **converging** sequence — this is the clause that the `P₀`
projection perturbs (see `NOTES_session13.md` §2). -/
theorem E5_bd4 {α B C₀ T : ℝ} {g₀ : Fn} {G : ℕ → Fam} {φ : ℕ → ℕ} {F : ℝ → Fn}
    (hconv : ∀ τ ∈ Set.Icc (0 : ℝ) T,
      ConvLocUnifH6 α B (fun n => slice (G (φ n)) τ) (F τ))
    (hmem : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ n : ℕ,
      Work.Spaces.HkMem α 4 (slice (G (φ n)) τ))
    (hb : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ n : ℕ,
      Work.FTS.Nonlin.Xn α (slice (G (φ n)) τ) ≤ C₀ * α ^ 2) :
    ∀ τ ∈ Set.Icc (0 : ℝ) T, Work.FTS.Nonlin.Xn α (slice (clampQ F g₀) τ) ≤ C₀ * α ^ 2 := by
  intro τ hτ
  have h := clampQ_hkNorm α 4 F g₀ τ
  show Work.Spaces.HkNorm α 4 (slice (clampQ F g₀) τ) ≤ C₀ * α ^ 2
  rw [h]
  exact EpsLimBd4 (hconv τ hτ) (hmem τ hτ) (hb τ hτ)

/-- **`mem4`.**  The honest `ℋ⁴`-membership of the limit slice, from the proved `EpsLimMem4`
(whose per-`z` bound is *not* removable — `HkMem` is a per-`z` condition while Fatou gives it only
a.e. in `z`). -/
theorem E5_mem4 {α B : ℝ} (g₀ : Fn) {G : ℕ → Fn} {F : ℝ → Fn} {τ : ℝ}
    (hconv : ConvLocUnifH6 α B G (F τ))
    (hsm : ∀ n : ℕ, ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry (G n)) Work.FTS.EllipticEst.Q0)
    (hmem : ∀ n : ℕ, Work.Spaces.HkMem α 6 (G n))
    (hb : ∀ n : ℕ, Work.Spaces.HkNorm α 6 (G n) ≤ B)
    (hz : ∀ z ∈ Work.Spaces.Iz, ∃ Bz : ℝ, ∀ n : ℕ,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 (G n) z θ) ≤ Bz) :
    Work.Spaces.HkMem α 4 (slice (clampQ F g₀) τ) ∧
      Work.Spaces.HkNorm α 4 (slice (clampQ F g₀) τ) ≤ B := by
  obtain ⟨hm, hb'⟩ := EpsLimMem4 hconv hsm hmem hb hz
  have h := clampQ_hkNorm α 4 F g₀ τ
  refine ⟨clampQ_hkMem α 4 hm, ?_⟩
  show Work.Spaces.HkNorm α 4 (slice (clampQ F g₀) τ) ≤ B
  rw [h]; exact hb'

/-! ## The fake-time continuity of the limit family -/

/-- **`cont`.**  Continuity in the fake time, at every point of the open quadrant: the
τ-Lipschitz property of the approximants passes to the limit (`EpsLimCont`), and the clamp is
constant off the open angular interval. -/
theorem E5_cont {α B T : ℝ} {g₀ : Fn} {G : ℕ → Fam} {F : ℝ → Fn}
    (hconvL : ∀ τ ∈ Set.Icc (0 : ℝ) T,
      ConvLev0H6 α B (fun n => slice (G n) τ) (F τ))
    (hlip : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ p ∈ K, ∀ τ ∈ Set.Icc (0 : ℝ) T,
        ∀ τ' ∈ Set.Icc (0 : ℝ) T,
          |slice (G n) τ p.1 p.2 - slice (G n) τ' p.1 p.2| ≤ C * |τ - τ'|) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      ContinuousOn (fun τ => clampQ F g₀ z θ τ) (Set.Icc (0 : ℝ) T) := by
  intro z θ hzθ
  exact clampQ_continuousOn hzθ.1 ⟨hzθ.2.1, hzθ.2.2⟩ (EpsLimCont hconvL hlip z θ hzθ)

end Work.FTS.StrongEps
