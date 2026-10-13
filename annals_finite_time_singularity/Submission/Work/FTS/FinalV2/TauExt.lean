import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.StrongGlobal.dynRHS_congr

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.FinalV2.TauExt` — REVIEW FIX-2 transfer lemma (curric-46 lead install, 2026-10-10)

`Sol`, `DynOK` and `LimApprox` read a family `g` only at fake times `τ ≥ 0` (slices at `τ ≥ 0`,
`HasDerivWithinAt … (Ici 0)`, `ContDiffOn` on `τ > 0`, `deriv` at `τ > 0`), so they transfer from
`g` to its right-Taylor extension `tauExt g`, which agrees with `g` on `τ ≥ 0`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS.FinalV2

open Work.FTS.Galerkin (Fn Fam slice IsDynGSolWith)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS.Final

set_option autoImplicit false

variable {α C₀ : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}

theorem muDyn_tauExt {τ : ℝ} (hτ : 0 ≤ τ) :
    Work.FTS.Galerkin.muDyn α (PsiCan Φs E (tauExt g)) (tauExt g) τ
      = Work.FTS.Galerkin.muDyn α (PsiCan Φs E g) g τ :=
  Work.FTS.StrongGlobal.muDyn_congr (slice_tauExt g hτ)

theorem gdot_tauExt {τ : ℝ} (hτ : 0 < τ) :
    Work.FTS.Galerkin.gdot (tauExt g) τ = Work.FTS.Galerkin.gdot g τ := by
  funext z θ
  simp only [Work.FTS.Galerkin.gdot]
  exact Filter.EventuallyEq.deriv_eq
    (Filter.eventually_of_mem (Ici_mem_nhds hτ) (fun s hs => tauExt_of_nonneg g hs))

theorem regPkgMin_tauExt (h : Work.FTS.StrongGlobal.RegPkgMin α g) :
    Work.FTS.StrongGlobal.RegPkgMin α (tauExt g) where
  c1 := h.c1.congr (fun p hp => tauExt_of_nonneg g (le_of_lt hp.2.2))
  c4 := fun τ hτ => by rw [slice_tauExt g hτ]; exact h.c4 τ hτ
  cont := fun z θ hzθ => (h.cont z θ hzθ).congr (eqOn_tauExt g z θ)
  mem4 := fun τ hτ => by rw [slice_tauExt g hτ]; exact h.mem4 τ hτ
  dbd := fun S hS => by
    obtain ⟨Cd, hCd⟩ := h.dbd S hS
    exact ⟨Cd, fun τ hτ hτS => by rw [gdot_tauExt hτ]; exact hCd τ hτ hτS⟩
  vanish := fun τ hτ z hz => by
    rw [tauExt_of_nonneg g hτ, tauExt_of_nonneg g hτ]; exact h.vanish τ hτ z hz

theorem dynOK_tauExt (h : DynOK α C₀ g) : DynOK α C₀ (tauExt g) :=
  ⟨regPkgMin_tauExt h.1, fun τ hτ => by rw [slice_tauExt g hτ]; exact h.2 τ hτ⟩

theorem limApprox_tauExt (h : LimApprox α C₀ Φs E g) : LimApprox α C₀ Φs E (tauExt g) := by
  intro T hT
  obtain ⟨gn, B, L, h1, h2, h3, h4⟩ := h T hT
  refine ⟨gn, B, L, h1, h2, fun τ hτ => ?_, fun τ hτ => ?_⟩
  · rw [slice_tauExt g hτ.1]; exact h3 τ hτ
  · rw [muDyn_tauExt hτ.1]; exact h4 τ hτ

theorem sol_tauExt (h : Sol α Φs E g) : Sol α Φs E (tauExt g) := by
  refine ⟨fun τ hτ => ?_, fun z θ τ hτ hzθ => ?_⟩
  · rw [Work.FTS.StrongGlobal.Ftau_congr (slice_tauExt g hτ),
      Work.FTS.StrongGlobal.slice_PsiCan_congr (slice_tauExt g hτ)]
    exact h.1 τ hτ
  · have hd := h.2 z θ τ hτ hzθ
    rw [Work.FTS.StrongGlobal.dynLin_congr (slice_tauExt g hτ),
      Work.FTS.StrongGlobal.dynRHS_congr (slice_tauExt g hτ)]
    exact hd.congr (fun s hs => tauExt_of_nonneg g hs) (tauExt_of_nonneg g hτ)

/-- **REVIEW FIX-2, the transfer lemma** (PROVED): the strong solution and its enriched package
pass to the right-Taylor extension. -/
theorem sol_dynOK'_tauExt (hS : Sol α Φs E g) (hOK : DynOK' α C₀ Φs E g) :
    Sol α Φs E (tauExt g) ∧ DynOK' α C₀ Φs E (tauExt g) :=
  ⟨sol_tauExt hS, dynOK_tauExt hOK.1, limApprox_tauExt hOK.2⟩

end Work.FTS.FinalV2
