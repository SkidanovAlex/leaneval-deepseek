import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.RegPkgGal.Defs
import Submission.Work.FTS.RegPkgGal.Basic
import Submission.Work.FTS.RegPkgGal.RVocab
import Submission.Work.FTS.RegPkgGal.R5.dtg_eq_rhs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.RegPkgGal.R5f.jet_dtg_of_rhs` — the fake-time jet `∂_τg̃` from the a-priori
# regularity of the right-hand side

`R5.dtg_eq_rhs` identifies the fake-time derivative of the extension `g̃ = extG g` with the
right-hand side `dynLin α g τ + dynRHS α Φ g τ` **on the open quadrant** `Qd = (0,∞) × (0,π/2)`.
This file turns that identification into the `Jet` of the derivative on the **closed** domain
`z ≥ 0`, `θ ∈ Iθ = [0,π/2]`, `τ ∈ [0,S]`, given the a-priori regularity of the right-hand side
itself:

* `hRHS` — the right-hand side is a `Jet α S N0` (bounded and jointly `α`-Hölder on the closed
  domain);
* `hRz0`, `hRθ0`, `hRθπ` — it vanishes at `z = 0` and on the two angular boundary lines.

The point is that the *closed* domain is `Qd ∪ {z = 0} ∪ {θ = 0} ∪ {θ = π/2}`, so only the three
boundary pieces have to be added to the identification:

* **`z = 0`**: `g̃ 0 θ τ = 0` for *every* `τ` (the `z ≤ 0` branch of `extG` wins), so the
  derivative is `0`, which is the value of the right-hand side by `hRz0`;
* **`θ = 0` or `θ = π/2`, `z > 0`**: `RegPkgMin.vanish` makes the slice `s ↦ g z θ s` vanish on
  the whole half-line `s ≥ 0`; consequently both branches of `extG g z θ ·` vanish —
  the value branch by `vanish`, the Taylor branch because `g z θ 0 = 0` *and*
  `deriv (fun s => g z θ s) 0 = 0` (`deriv_eq_zero_of_eq_zero_on_Ici`: a function which vanishes
  on `[0,∞)` has zero derivative at `0`, either because its two-sided derivative, if it exists,
  must agree with its (vanishing) right derivative, or because it is not differentiable at `0`
  at all, in which case `deriv` is `0` by convention).  Hence the derivative is `0` there too,
  the value given by `hRθ0`/`hRθπ`.

Everything else is a verbatim re-run of `R5.dtg_eq_rhs`, with the elliptic law dropped
(`dtg_eq_rhs_of_isDynEqOn` below needs only the one-sided equation `IsDynEqOn`, not the packaged
`IsDynGSolWith`), and then the `Jet` of the derivative is the `Jet` of the right-hand side by
pointwise rewriting.
-/

namespace Work.FTS.RegPkgGal.R5f

open Set Filter Topology
open scoped Real Topology

/-- **A function which vanishes on `[0,∞)` has zero derivative at `0`.**

If `f` is differentiable at `0`, its two-sided derivative must agree with its right derivative,
which is `0` (compute `derivWithin f (Ici 0) 0` from the vanishing of `f` on `Ici 0` and from the
`HasDerivWithinAt` form of `f`'s derivative); if it is not differentiable, `deriv` is `0` by
convention (`deriv_zero_of_not_differentiableAt`). -/
theorem deriv_eq_zero_of_eq_zero_on_Ici {f : ℝ → ℝ}
    (hf : ∀ s : ℝ, 0 ≤ s → f s = 0) : deriv f 0 = 0 := by
  by_cases h : DifferentiableAt ℝ f 0
  · have h1 : derivWithin f (Set.Ici 0) 0 = deriv f 0 :=
      h.hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici 0)
    have h2 : derivWithin f (Set.Ici 0) 0 = 0 :=
      ((hasDerivWithinAt_const (0 : ℝ) (Set.Ici 0) (0 : ℝ)).congr
        (fun y hy => hf y hy) (hf 0 le_rfl)).derivWithin (uniqueDiffWithinAt_Ici 0)
    rw [h1] at h2
    exact h2
  · exact deriv_zero_of_not_differentiableAt h

/-- **The extension vanishes identically at the angular endpoints.**  If the slice
`s ↦ g z θ s` vanishes on the whole half-line `s ≥ 0` (which is what `RegPkgMin.vanish` gives at
`θ = 0` and `θ = π/2`) and `z > 0`, then `s ↦ g̃ z θ s = extG g z θ s` vanishes identically: the
value branch by hypothesis, and the Taylor branch because `g z θ 0 = 0` and
`deriv (fun s => g z θ s) 0 = 0` (`deriv_eq_zero_of_eq_zero_on_Ici`). -/
theorem extG_eq_zero_of_eq_zero_on_Ici {g : ℝ → ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hg : ∀ s : ℝ, 0 ≤ s → g z θ s = 0) : ∀ s : ℝ, extG g z θ s = 0 := by
  have hd : deriv (fun s => g z θ s) 0 = 0 := deriv_eq_zero_of_eq_zero_on_Ici hg
  intro s
  rcases lt_or_ge s 0 with hs | hs
  · rw [extG_of_neg hz hs, hg 0 le_rfl, hd]
    ring
  · rw [extG_of_pos hz hs, hg s hs]

/-- **The identification `∂_τg̃ = dynLin + dynRHS` on the open quadrant, from the one-sided
equation alone.**  This is `R5.dtg_eq_rhs` with the elliptic-law component of the packaged
predicate dropped: only `hsol` (the half-line equation) and the two-sided `τ = 0` identity `h0`
carry the derivative, exactly as in the sibling lemma, which it re-uses verbatim through
`R5.hasDerivAt_extG_of_zero` and `R5.hasDerivAt_extG_of_pos`. -/
theorem dtg_eq_rhs_of_isDynEqOn {α S : ℝ}
    {g Φ : ℝ → ℝ → ℝ → ℝ}
    (hsol : Work.FTS.Galerkin.IsDynEqOn (Work.FTS.Regularity.pExp α) Φ g)
    (h0 : ∀ z θ : ℝ, 0 < z → (z, θ) ∈ Work.Construction.Qd →
      HasDerivAt (fun s => g z θ s)
        (Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) g 0 z θ
          + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) Φ g 0 z θ) 0) :
    ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 < z → (z, θ) ∈ Work.Construction.Qd →
      deriv (fun s => extG g z θ s) τ
        = Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) g τ z θ
          + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) Φ g τ z θ := by
  intro τ hτ z θ hz hQd
  have hLeq : HasDerivWithinAt (fun s => g z θ s)
      (Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) g τ z θ
        + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) Φ g τ z θ) (Set.Ici 0) τ :=
    hsol z θ τ hτ.1 hQd
  rcases eq_or_lt_of_le hτ.1 with hzero | hpos
  · subst hzero
    exact (Work.FTS.RegPkgGal.R5.hasDerivAt_extG_of_zero hz (h0 z θ hz hQd)).deriv
  · exact (Work.FTS.RegPkgGal.R5.hasDerivAt_extG_of_pos hz hpos
      (hLeq.hasDerivAt (Ici_mem_nhds hpos))).deriv

/-- **The pointwise identification of `∂_τg̃` with the right-hand side on the closed domain.**

On the open quadrant this is `dtg_eq_rhs_of_isDynEqOn`; on the three boundary pieces (`z = 0` and
the two angular lines) the derivative is `0` — because `g̃` vanishes identically there as a
function of `τ` — and the right-hand side is `0` by `hRz0`/`hRθ0`/`hRθπ`. -/
theorem deriv_extG_eq_rhs_of_jet {α S : ℝ} {g Φ : ℝ → ℝ → ℝ → ℝ}
    (hmin : Work.FTS.RegPkgGal.RegPkgMin (Work.FTS.Regularity.pExp α) g)
    (hsol : Work.FTS.Galerkin.IsDynEqOn (Work.FTS.Regularity.pExp α) Φ g)
    (h0 : ∀ z θ : ℝ, 0 < z → (z, θ) ∈ Work.Construction.Qd →
      HasDerivAt (fun s => g z θ s)
        (Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) g 0 z θ
          + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) Φ g 0 z θ) 0)
    (hRz0 : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ,
      Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) g τ 0 θ
        + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) Φ g τ 0 θ = 0)
    (hRθ0 : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ,
      Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) g τ z 0
        + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) Φ g τ z 0 = 0)
    (hRθπ : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ,
      Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) g τ z (Real.pi / 2)
        + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) Φ g τ z (Real.pi / 2) = 0) :
    ∀ z θ τ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → τ ∈ Set.Icc 0 S →
      deriv (fun s => extG g z θ s) τ
        = Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) g τ z θ
          + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) Φ g τ z θ := by
  intro z θ τ hz hθ hτ
  rcases eq_or_lt_of_le hz with hz0 | hzpos
  · -- `z = 0`: the extension is identically `0` in `τ`
    subst hz0
    have hzero : (fun s => extG g 0 θ s) = fun _ => (0 : ℝ) :=
      funext (fun s => extG_of_nonpos (le_refl (0 : ℝ)))
    rw [hzero, deriv_const]
    exact (hRz0 τ hτ θ hθ).symm
  · rcases eq_or_ne θ 0 with hθ0 | hθ0
    · -- `θ = 0`: `vanish` makes the slice vanish on `[0,∞)`, hence the extension identically
      subst hθ0
      have hgg : ∀ s : ℝ, 0 ≤ s → g z 0 s = 0 := fun s hs => (hmin.vanish s hs z hzpos.le).1
      rw [funext (extG_eq_zero_of_eq_zero_on_Ici hzpos hgg), deriv_const]
      exact (hRθ0 τ hτ z).symm
    · rcases eq_or_ne θ (Real.pi / 2) with hθπ | hθπ
      · -- `θ = π/2`: same
        subst hθπ
        have hgg : ∀ s : ℝ, 0 ≤ s → g z (Real.pi / 2) s = 0 :=
          fun s hs => (hmin.vanish s hs z hzpos.le).2
        rw [funext (extG_eq_zero_of_eq_zero_on_Ici hzpos hgg), deriv_const]
        exact (hRθπ τ hτ z).symm
      · -- interior point of the quadrant: the identification of `R5`
        have hθpos : 0 < θ := lt_of_le_of_ne hθ.1 (Ne.symm hθ0)
        have hθlt : θ < Real.pi / 2 := lt_of_le_of_ne hθ.2 hθπ
        exact dtg_eq_rhs_of_isDynEqOn hsol h0 τ hτ z θ hzpos ⟨hzpos, hθpos, hθlt⟩

theorem jet_dtg_of_rhs {α S N0 : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hS : 0 < S)
    {g Φ : ℝ → ℝ → ℝ → ℝ}
    (hmin : Work.FTS.RegPkgGal.RegPkgMin (Work.FTS.Regularity.pExp α) g)
    (hsol : Work.FTS.Galerkin.IsDynEqOn (Work.FTS.Regularity.pExp α) Φ g)
    (h0 : ∀ z θ : ℝ, 0 < z → (z, θ) ∈ Work.Construction.Qd →
      HasDerivAt (fun s => g z θ s)
        (Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) g 0 z θ
          + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) Φ g 0 z θ) 0)
    (hRHS : Work.FTS.Regularity.Jet α S N0
      (fun z θ τ => Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) g τ z θ
        + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) Φ g τ z θ))
    (hRz0 : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ,
      Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) g τ 0 θ
        + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) Φ g τ 0 θ = 0)
    (hRθ0 : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ,
      Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) g τ z 0
        + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) Φ g τ z 0 = 0)
    (hRθπ : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ,
      Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) g τ z (Real.pi / 2)
        + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) Φ g τ z (Real.pi / 2) = 0) :
    ∃ Nd : ℝ, Work.FTS.Regularity.Jet α S Nd
      (fun z θ τ => deriv (fun s => Work.FTS.RegPkgGal.extG g z θ s) τ) := by
  -- the derivative is the right-hand side pointwise on the closed domain, so it inherits the
  -- whole `Jet` of `hRHS`
  refine ⟨N0, hRHS.1, ?_, ?_⟩
  · intro z θ τ hz hθ hτ
    show |deriv (fun s => Work.FTS.RegPkgGal.extG g z θ s) τ| ≤ N0
    rw [deriv_extG_eq_rhs_of_jet hmin hsol h0 hRz0 hRθ0 hRθπ z θ τ hz hθ hτ]
    exact hRHS.2.1 z θ τ hz hθ hτ
  · intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    show |deriv (fun s => Work.FTS.RegPkgGal.extG g z θ s) τ
        - deriv (fun s => Work.FTS.RegPkgGal.extG g z' θ' s) τ'|
      ≤ N0 * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α
    rw [deriv_extG_eq_rhs_of_jet hmin hsol h0 hRz0 hRθ0 hRθπ z θ τ hz hθ hτ,
      deriv_extG_eq_rhs_of_jet hmin hsol h0 hRz0 hRθ0 hRθπ z' θ' τ' hz' hθ' hτ']
    exact hRHS.2.2 z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'

end Work.FTS.RegPkgGal.R5f
