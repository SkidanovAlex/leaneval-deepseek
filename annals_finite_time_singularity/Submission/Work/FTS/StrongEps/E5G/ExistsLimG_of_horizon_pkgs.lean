import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.E5G.Defs
import Submission.Work.FTS.StrongEps.EpsLimitDefsG
import Submission.Work.FTS.StrongEps.E5Clamp
import Submission.Work.FTS.StrongEps.E5G.Coherence
import Submission.Work.FTS.EllipticEst.HkSq_congr_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5G

open scoped Real Topology
open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The glue of the per-horizon packages

The hypotheses of `ExistsLimG_of_horizon_pkgs` provide, for every horizon `Tn N`, a limit package
for the *clamped* limit curve `clampQ (F N) g₀` of that horizon, and the coherence `hcoh` of the
curves `F N` on the overlaps of the horizons.  This file builds the single global family

  `g := clampQ (fun τ => F (ι τ) τ) g₀`  (`ι τ` a horizon index covering `τ`),

and shows that on every horizon `[0,T]` it agrees with the curve of any covering piece; then every
clause of `EpsLimPkg` transports, because `EpsLimPkg` only ever looks at the family on `[0,T]`
(the `dbd`-clause looks at the honest `τ`-derivative, which is a local notion, so agreement on
`[0,T]` at an *interior* time `τ ∈ (0,T)` already suffices). -/

/-- **`gdot` only sees the family near the evaluation time.**  If two families agree on the closed
interval `[0,T]` and `τ` is an interior point of it, then their `τ`-derivatives at `τ` agree. -/
theorem gdot_eq_of_agreeOn_Icc {g g' : Fam} {T τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T)
    (h : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ z θ, g z θ s = g' z θ s) :
    Work.FTS.Galerkin.gdot g τ = Work.FTS.Galerkin.gdot g' τ := by
  funext z θ
  exact Filter.EventuallyEq.deriv_eq
    (Filter.eventually_of_mem (Icc_mem_nhds hτ.1 hτ.2) (fun s hs => h s hs z θ))

/-- **The clamped curves of the covering pieces agree on the horizon.**  Let `ι` be any map from
times to horizon indices with `τ ≤ Ts (ι τ)`, `N` a piece covering `[0,T]` (`T ≤ Ts N`), and `Fs`
a family of curves coherent on the overlaps of the horizons (the hypothesis `hcoh` of
`ExistsLimG_of_horizon_pkgs`).  Then on `[0,T]` the clamped curve of the *selected* horizon `ι s`
coincides with the clamped curve of the piece `N`. -/
theorem clampQ_horizon_agree {Fs : ℕ → ℝ → Fn} {g₀ : Fn} {Ts : ℕ → ℝ} {ι : ℝ → ℕ} {T : ℝ}
    {N : ℕ} (hι : ∀ τ : ℝ, τ ≤ Ts (ι τ)) (hTN : T ≤ Ts N)
    (hcoh : ∀ m n : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) (min (Ts m) (Ts n)), ∀ z θ,
      (z, θ) ∈ Work.Construction.Qd → Fs m τ z θ = Fs n τ z θ) :
    ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ z θ,
      clampQ (fun τ => Fs (ι τ) τ) g₀ z θ s = clampQ (Fs N) g₀ z θ s := by
  intro s hs z θ
  by_cases hzb : z ∈ Set.Ioi (0 : ℝ)
  · by_cases hθb : θ ∈ Set.Ioo (0 : ℝ) (π / 2)
    · rw [clampQ_of_mem (F := fun τ => Fs (ι τ) τ) hzb hθb,
        clampQ_of_mem (F := Fs N) hzb hθb]
      exact hcoh (ι s) N s ⟨hs.1, le_min (hι s) (le_trans hs.2 hTN)⟩ z θ ⟨hzb, hθb⟩
    · rw [clampQ_of_not_mem_θ (F := fun τ => Fs (ι τ) τ) hzb hθb,
        clampQ_of_not_mem_θ (F := Fs N) hzb hθb]
  · rw [clampQ_of_not_mem_z (F := fun τ => Fs (ι τ) τ) hzb,
      clampQ_of_not_mem_z (F := Fs N) hzb]

/-- **The limit package is a property of the family on `[0,T]`.**  If two families have the same
slices at every `τ ∈ [0,T]`, then one carries `EpsLimPkg` on `[0,T]` iff the other does.

Every clause of `EpsLimPkg` is a statement about the slices `slice g τ`, `τ ∈ [0,T]`
(`init`/`law`/`eqT`/`c4`/`mem4`/`bd4`/`vanish`/`limApprox` read the slice at a single `τ`, `c1` and
`cont` read a whole interval of them), except `dbd`, which reads the honest `τ`-derivative
`gdot g τ` at `τ ∈ (0,T)`; there the equality of the *functions* on `[0,T]` is a neighbourhood
property of the interior point `τ`, hence the derivatives agree (`gdot_eq_of_agreeOn_Icc`). -/
theorem EpsLimPkg_congr_of_slice_eqOn {α C₀ K Cd T : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {g g' : Fam} (hT : 0 < T)
    (h : ∀ τ ∈ Set.Icc (0 : ℝ) T, slice g τ = slice g' τ)
    (hp : EpsLimPkg α C₀ K Cd T Φs E g₀ g) :
    EpsLimPkg α C₀ K Cd T Φs E g₀ g' := by
  have hpt : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ z θ, g z θ τ = g' z θ τ :=
    fun τ hτ z θ => congrFun (congrFun (h τ hτ) z) θ
  have hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
  refine
    { init := fun z θ => (hpt 0 hzero z θ).symm.trans (hp.init z θ)
      law := fun τ h1 h2 => ?_
      eqT := fun τ h1 h2 z θ hzθ => ?_
      c1 := hp.c1.congr (fun p hp' => ?_)
      c4 := fun τ h1 h2 => by
        simpa only [← h τ ⟨h1, h2⟩] using hp.c4 τ h1 h2
      cont := fun z θ hzθ => (hp.cont z θ hzθ).congr (fun τ hτ => (hpt τ hτ z θ).symm)
      mem4 := fun τ h1 h2 => by
        simpa only [← h τ ⟨h1, h2⟩] using hp.mem4 τ h1 h2
      bd4 := fun τ h1 h2 => by
        simpa only [← h τ ⟨h1, h2⟩] using hp.bd4 τ h1 h2
      bd6 := by
        obtain ⟨B, hB⟩ := hp.bd6
        exact ⟨B, fun τ h1 h2 => by
          simpa only [← h τ ⟨h1, h2⟩] using hB τ h1 h2⟩
      vanish := fun τ h1 h2 z hz => ?_
      dbd := fun τ h1 h2 => ?_
      limApprox := fun T' h1 h2 => ?_ }
  · -- `law`
    have hτ : τ ∈ Set.Icc (0 : ℝ) T := ⟨h1, h2⟩
    rw [← Work.FTS.StrongGlobal.Ftau_congr (h τ hτ),
      ← Work.FTS.StrongGlobal.slice_PsiCan_congr (h τ hτ)]
    exact hp.law τ h1 h2
  · -- `eqT`
    have hτ : τ ∈ Set.Icc (0 : ℝ) T := ⟨h1, h2⟩
    have hfun : ∀ s ∈ Set.Icc (0 : ℝ) T, g' z θ s = g z θ s :=
      fun s hs => (hpt s hs z θ).symm
    have hg := (hp.eqT τ h1 h2 z θ hzθ).congr hfun (hfun τ hτ)
    rwa [rhsFun_congr (h τ hτ)] at hg
  · -- `c1`
    exact (hpt p.2.2 ⟨le_of_lt hp'.2.2.1, le_of_lt hp'.2.2.2⟩ p.1 p.2.1).symm
  · -- `vanish`
    have hτ : τ ∈ Set.Icc (0 : ℝ) T := ⟨h1, h2⟩
    obtain ⟨h0, h1'⟩ := hp.vanish τ h1 h2 z hz
    exact ⟨by rwa [hpt τ hτ z 0] at h0, by rwa [hpt τ hτ z (π / 2)] at h1'⟩
  · -- `dbd`
    have hgd : Work.FTS.Galerkin.gdot g' τ = Work.FTS.Galerkin.gdot g τ :=
      gdot_eq_of_agreeOn_Icc (g := g') (g' := g) ⟨h1, h2⟩
        (fun s hs z θ => (hpt s hs z θ).symm)
    rw [hgd]
    exact hp.dbd τ h1 h2
  · -- `limApprox`
    obtain ⟨gn, B, L, hb, hlip, hjet, hmu⟩ := hp.limApprox T' h1 h2
    refine ⟨gn, B, L, hb, hlip, ?_, ?_⟩
    · intro τ hτ j i hji z θ hzθ
      have hτ' : τ ∈ Set.Icc (0 : ℝ) T := ⟨hτ.1, le_trans hτ.2 h2⟩
      simpa only [h τ hτ'] using hjet τ hτ j i hji z θ hzθ
    · intro τ hτ
      have hτ' : τ ∈ Set.Icc (0 : ℝ) T := ⟨hτ.1, le_trans hτ.2 h2⟩
      simpa only [Work.FTS.StrongGlobal.muDyn_congr (h τ hτ')] using hmu τ hτ

/-- **E5 (new form) from the per-horizon packages.**  From a monotone covering family of horizons
`Tn` and, at every horizon, a limit package for the clamped limit curve of that horizon — the
curves being coherent on the overlaps — one gets a *single* global family carrying the package on
every horizon.

The family is `clampQ (fun τ => F (ι τ) τ) g₀` where `ι τ` is a horizon covering `τ` (chosen from
`hcov` at `|τ| + 1`, so that it is defined for every real `τ`); on every horizon `[0,T]` it
coincides with the piece covering `T`, by coherence (`clampQ_horizon_agree`), and the package
transports (`EpsLimPkg_congr_of_slice_eqOn`). -/
theorem ExistsLimG_of_horizon_pkgs {α C₀ K : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g₀ : Work.FTS.Galerkin.Fn}
    {Tn : ℕ → ℝ} {F : ℕ → ℝ → Work.FTS.Galerkin.Fn}
    (hTn : ∀ N : ℕ, 0 < Tn N) (hmono : Monotone Tn)
    (hcov : ∀ T : ℝ, 0 < T → ∃ N : ℕ, T ≤ Tn N)
    (hcoh : ∀ m n : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) (min (Tn m) (Tn n)), ∀ z θ : ℝ,
      (z, θ) ∈ Work.Construction.Qd → F m τ z θ = F n τ z θ)
    (hpkg : ∀ N : ℕ, ∀ T : ℝ, 0 < T → T ≤ Tn N →
      ∃ Cd : ℝ, 0 < Cd ∧
        Work.FTS.StrongEps.EpsLimPkg α C₀ K Cd T Φs E g₀ (Work.FTS.StrongEps.clampQ (F N) g₀)) :
    ∃ g : Work.FTS.Galerkin.Fam, ∀ T : ℝ, 0 < T → ∃ Cd : ℝ, 0 < Cd ∧
      Work.FTS.StrongEps.EpsLimPkg α C₀ K Cd T Φs E g₀ g := by
  classical
  -- a horizon index covering every time: chosen at `|τ| + 1`, so that it is defined (and the
  -- covering property holds) for *every* real `τ`, not only for `τ ≥ 0`.
  have hpos : ∀ τ : ℝ, 0 < |τ| + 1 := fun τ => by have := abs_nonneg τ; linarith
  let ι : ℝ → ℕ := fun τ => Classical.choose (hcov (|τ| + 1) (hpos τ))
  have hι : ∀ τ : ℝ, τ ≤ Tn (ι τ) := fun τ =>
    le_trans (by have := le_abs_self τ; linarith)
      (Classical.choose_spec (hcov (|τ| + 1) (hpos τ)))
  refine ⟨Work.FTS.StrongEps.clampQ (fun τ => F (ι τ) τ) g₀, fun T hT => ?_⟩
  obtain ⟨N, hTN⟩ := hcov T hT
  obtain ⟨Cd, hCd, hpk⟩ := hpkg N (Tn N) (hTn N) le_rfl
  refine ⟨Cd, hCd, ?_⟩
  have hpkT : Work.FTS.StrongEps.EpsLimPkg α C₀ K Cd T Φs E g₀
      (Work.FTS.StrongEps.clampQ (F N) g₀) :=
    Work.FTS.StrongEps.EpsLimPkg.mono hTN hpk hT.le
  refine EpsLimPkg_congr_of_slice_eqOn hT (fun s hs => ?_) hpkT
  funext z θ
  simpa only [Work.FTS.Galerkin.slice_apply] using
    (clampQ_horizon_agree (Fs := F) (Ts := Tn) (ι := ι) (N := N) hι hTN hcoh s hs z θ).symm

end Work.FTS.StrongEps.E5G
