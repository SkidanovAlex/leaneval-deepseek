import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS.Final.Assembly
import Submission.Work.FTS.Final.ExtG.dynOK_extG
import Submission.Work.FTS.FinalV2.Sanitize

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.FinalV2.Defs` — the corrected input bundle `Inputs'` (curric-46 lead install, 2026-10-10)

Design `cbc/fts_final_redesign.md` (+ `.lean`), corrected by `cbc/fts_final_redesign_REVIEW.md`.
NEW files only: the old `Work.FTS.Final.Inputs` (`Final/Assembly.lean`) is untouched.

* `psiCut`, `psiFire` — the stream function handed to the firing (G1): `PhiOdd (psiCut PsiCan)`,
  equal to `PsiCan` on `θ > 0`, odd in `θ` unconditionally (`psiFire_odd`, proved).
* `LimApprox`, `DynOK'` — the enriched output of `global_strong2` (G2).
* `EllLimOK3` — order-3 limit closure (1a′); `MuLipC` — class-C Lipschitz bound of `muDyn` (1c).
* `tauExt` — **REVIEW FIX-2**: the right-Taylor extension of `g` to `τ < 0`,
  `tauExt g z θ τ = g z θ 0 + τ · derivWithin (g z θ ·) (Ici 0) 0` for `τ < 0`, `= g` for `τ ≥ 0`.
  The adapter (`FinalV2.Adapter`) fires on `extG (tauExt g)` instead of `extG g`, so that the
  `τ < 0` data that `RegPkgGal` (R1, `R5Parts.h0`) reads are right-sided data of `g` at `τ = 0`
  and hence producible. Conjunct (7′) is accordingly stated on `extG (tauExt g)`.
  The transfer of `Sol`/`DynOK'` to `tauExt g` is `FinalV2.TauExt.sol_dynOK'_tauExt`.
* `Inputs'` — the corrected bundle.

**RegExport REVIEW F1 (2026-10-10).** (4′) keeps the initial-value clause
`∀ z θ, gg z θ 0 = g₀ z θ` (`global_strong2'` outputs it), and (7′) is replaced by (7″): it assumes
the datum `hdat : ∃ L β, 1 ≤ L ∧ g(·,·,0) = locG6 (pExp α) L β` and concludes on the SANITISED
family `extG (gS α (tauExt g))` (`FinalV2.Sanitize`). Without `hdat`, (7′) was unprovable (`hInit`
and the `τ = 0` bounds of `St1Class` are facts about the datum).

**StreamBdry REVIEW FIX-A (2026-10-10).** (9′) is replaced by (9″): it additionally assumes
`∀ S > 0, RegPkg' α S A B (extG G)` for a family `G` agreeing with `g` on `z > 0, θ ∈ Iθ, τ ≥ 0`
(the adapter passes `G := gS α g` and its `hRegG`). Without the support datum (9′) is false
(`g₀ = 0` witness). No growth inputs. Producer: `FinalV2.hid9''` ← `StreamBdryIface.hid9''_of_parts`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS.FinalV2

open Work.FTS.Galerkin (Fn Fam slice IsDynGSolWith)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS.Physical (PhysClock)
open Work.FTS.Final
open Work.FTS.FinalClock
open Work.FTS.Regularity (pExp)
open Work.FTS.RegPkgGal (extG)

set_option autoImplicit false

/-- The constant family of a profile. -/
def cst (f : Fn) : Fam := fun z θ _ => f z θ

/-- Cut the stream function to `θ > 0` (value `0` on `θ ≤ 0`). -/
def psiCut (Ψ : Fam) : Fam := fun z θ τ => if 0 < θ then Ψ z θ τ else 0

/-- **G1: the stream function handed to the firing** — the odd extension in `θ` of the cut
canonical stream function. It equals `PsiCan Φs E g` on `θ > 0`, is `0` at `θ = 0` for *every*
`z`, and is odd in `θ` unconditionally. -/
def psiFire (Φs : Fn) (E : Fn → Fn) (g : Fam) : Fam :=
  Work.FTS.BSIdent.PhiOdd (psiCut (PsiCan Φs E g))

theorem psiFire_odd (Φs : Fn) (E : Fn → Fn) (g : Fam) (z θ τ : ℝ) :
    psiFire Φs E g z (-θ) τ = - psiFire Φs E g z θ τ :=
  Work.FTS.BSIdent.PhiOdd_neg_theta (fun z τ => by simp [psiCut]) z θ τ

theorem psiFire_of_pos {Φs : Fn} {E : Fn → Fn} {g : Fam} {z θ τ : ℝ} (hθ : 0 < θ) :
    psiFire Φs E g z θ τ = PsiCan Φs E g z θ τ := by
  simp [psiFire, Work.FTS.BSIdent.PhiOdd_of_nonneg hθ.le, psiCut, hθ]

/-- **G2: the approximation clause of the strong solution.** On every horizon `[0,T]` the
solution is the limit of class-C families (the mollified ε-iterates `J_εₙ g_εₙ`) with the uniform
`ℋ⁴`-smallness, a uniform `ℋ⁶` bound, a uniform `ℋ⁴`-Lipschitz modulus in `τ`, `C⁴`-jet
convergence on `Qd`, and convergence of the modulation. Every clause is produced inside E5's own
proof (the jets and `muDyn` convergence are what passing to the limit in `law`/`eqT` uses; the
Lipschitz modulus is the level-4 RHS bound of the scheme priced by `Xn6`). -/
def LimApprox (α C₀ : ℝ) (Φs : Fn) (E : Fn → Fn) (g : Fam) : Prop :=
  ∀ T : ℝ, 0 < T → ∃ (gn : ℕ → Fam) (B L : ℝ),
    (∀ n, ∀ τ ∈ Icc (0 : ℝ) T, Work.FTS.ClassC.ClassC α (slice (gn n) τ) ∧
      Work.FTS.Nonlin.Xn α (slice (gn n) τ) ≤ C₀ * α ^ 2 ∧
      Work.FTS.StrongGlobal.Xn6 α (slice (gn n) τ) ≤ B) ∧
    (∀ n, ∀ τ ∈ Icc (0 : ℝ) T, ∀ τ' ∈ Icc (0 : ℝ) T,
      Work.FTS.Nonlin.Xn α (slice (gn n) τ - slice (gn n) τ') ≤ L * |τ - τ'|) ∧
    (∀ τ ∈ Icc (0 : ℝ) T, ∀ j i : ℕ, j + i ≤ 4 → ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Tendsto (fun n => Work.Spaces.mixed j i (slice (gn n) τ) z θ) atTop
        (𝓝 (Work.Spaces.mixed j i (slice g τ) z θ))) ∧
    (∀ τ ∈ Icc (0 : ℝ) T,
      Tendsto (fun n => Work.FTS.Galerkin.muDyn α (PsiCan Φs E (gn n)) (gn n) τ) atTop
        (𝓝 (Work.FTS.Galerkin.muDyn α (PsiCan Φs E g) g τ)))

/-- **The enriched output of `global_strong2`** (G2): `DynOK` plus the approximation clause. -/
def DynOK' (α C₀ : ℝ) (Φs : Fn) (E : Fn → Fn) (g : Fam) : Prop :=
  DynOK α C₀ g ∧ LimApprox α C₀ Φs E g

/-- **(1a′) EllLimOK at order 3**: as `StrongEps.EllLimOK`, but the limit stream function is `C³`
on `Qd` and the jets converge to order `3`. -/
def EllLimOK3 (α : ℝ) (E : Fn → Fn) : Prop :=
  ∀ (fn : ℕ → Fn) (f : Fn) (B : ℝ),
    (∀ n, Work.FTS.ClassC.ClassC α (fn n)) →
    (∀ n, Work.FTS.StrongGlobal.Xn6 α (fn n) ≤ B) →
    ContDiffOn ℝ 4 (Function.uncurry f) Work.Construction.Qd →
    (∀ j i : ℕ, j + i ≤ 4 → ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Tendsto (fun n => Work.Spaces.mixed j i (fn n) z θ) atTop
        (𝓝 (Work.Spaces.mixed j i f z θ))) →
    Work.FTS.StrongGlobal.IsBslSolPos α f (E f) ∧
    ContDiffOn ℝ 3 (Function.uncurry (E f)) Work.Construction.Qd ∧
    ∀ j i : ℕ, j + i ≤ 3 → ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Tendsto (fun n => Work.Spaces.mixed j i (E (fn n)) z θ) atTop
        (𝓝 (Work.Spaces.mixed j i (E f) z θ))

theorem EllLimOK3.toEllLimOK {α : ℝ} {E : Fn → Fn} (h : EllLimOK3 α E) :
    Work.FTS.StrongEps.EllLimOK α E := by
  intro fn f B hC hB h4 hj
  obtain ⟨hlaw, -, hconv⟩ := h fn f B hC hB h4 hj
  exact ⟨hlaw, fun j i hji z θ hzθ => hconv j i (by omega) z θ hzθ⟩

/-- **(1c) the class-C Lipschitz bound of the modulation** (owner FTS_MuLamOK; same estimates as
`MuLamOK_proved`, applied to the class-C difference `f - f'` with `E` linear). -/
def MuLipC (α C₀ : ℝ) (Φs : Fn) (E : Fn → Fn) : Prop :=
  ∃ L : ℝ, 0 ≤ L ∧ ∀ f f' : Fn, Work.FTS.ClassC.ClassC α f → Work.FTS.ClassC.ClassC α f' →
    Work.FTS.Nonlin.Xn α f ≤ C₀ * α ^ 2 → Work.FTS.Nonlin.Xn α f' ≤ C₀ * α ^ 2 →
    |Work.FTS.Galerkin.muDyn α (PsiCan Φs E (cst f)) (cst f) 0
      - Work.FTS.Galerkin.muDyn α (PsiCan Φs E (cst f')) (cst f') 0|
      ≤ L * Work.FTS.Nonlin.Xn α (f - f')

/-! ## REVIEW FIX-2: the right-Taylor extension in `τ` -/

/-- **The right-Taylor extension of `g` to negative fake time**: `g` itself for `τ ≥ 0`, and the
first-order jet `g z θ 0 + τ · ∂_τ⁺ g(z,θ,0)` (one-sided derivative within `Ici 0`) for `τ < 0`.
Every object of the strong route reads `g` only at `τ ≥ 0`, so `tauExt g` carries the same data
(`FinalV2.TauExt.sol_dynOK'_tauExt`); unlike the raw `g`, its `τ < 0` values are determined. -/
def tauExt (g : Fam) : Fam := fun z θ τ =>
  if τ < 0 then g z θ 0 + τ * derivWithin (fun s => g z θ s) (Ici 0) 0 else g z θ τ

theorem tauExt_of_nonneg (g : Fam) {z θ τ : ℝ} (hτ : 0 ≤ τ) : tauExt g z θ τ = g z θ τ := by
  simp [tauExt, not_lt.mpr hτ]

theorem tauExt_of_neg (g : Fam) {z θ τ : ℝ} (hτ : τ < 0) :
    tauExt g z θ τ = g z θ 0 + τ * derivWithin (fun s => g z θ s) (Ici 0) 0 := by
  simp [tauExt, hτ]

theorem slice_tauExt (g : Fam) {τ : ℝ} (hτ : 0 ≤ τ) : slice (tauExt g) τ = slice g τ := by
  funext z θ; exact tauExt_of_nonneg g hτ

theorem eqOn_tauExt (g : Fam) (z θ : ℝ) :
    Set.EqOn (fun s => tauExt g z θ s) (fun s => g z θ s) (Ici 0) :=
  fun _ hs => tauExt_of_nonneg g hs

/-- `tauExt` is idempotent (the one-sided derivative at `0` only reads `τ ≥ 0`). -/
theorem tauExt_tauExt (g : Fam) : tauExt (tauExt g) = tauExt g := by
  funext z θ τ
  by_cases hτ : τ < 0
  · rw [tauExt_of_neg _ hτ, tauExt_of_neg _ hτ, tauExt_of_nonneg g le_rfl,
      derivWithin_congr (eqOn_tauExt g z θ) (tauExt_of_nonneg g le_rfl)]
  · rw [tauExt_of_nonneg _ (not_lt.mp hτ), tauExt_of_nonneg _ (not_lt.mp hτ)]

/-! ## §Inputs' — the corrected bundle -/

/-- `Sol αG Φs E g`: the dynamic solution predicate of the strong route. -/
abbrev Sol (αG : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) : Prop :=
  IsDynGSolWith (IsBslSolPos αG) αG (PsiCan Φs E g) g

structure Inputs' (α : ℝ) : Prop where
  hα : 0 < α
  hα13 : α ≤ 1 / 3
  press : PressureReconstructionOn ⟨α, hα.le⟩
  core : ∃ (Ce Cs Cg C₀ K : ℝ) (ρ : ℝ × ℝ → ℝ) (E : Fn →ₗ[ℝ] Fn) (Φs : Fn),
    0 < Ce ∧ 0 ≤ Cg ∧ 0 < C₀ ∧ 0 < K ∧ α * (600 * Cg * C₀) ≤ 1 ∧
    -- (0)
    Work.FTS.StrongEps.IsSmoothKernel ρ ∧
    -- (1)
    (∀ g : Fn, Work.FTS.ClassC.ClassC (pExp α) g →
      EllPkgGo (pExp α) Ce g (E g) ∧ Work.FTS.ClassC.EllPkgK (pExp α) 6 Ce g (E g)) ∧
    -- (1a′) order-3 limit closure
    EllLimOK3 (pExp α) E ∧
    -- (1b)
    Work.FTS.StrongEps.MuLamOK (pExp α) C₀ Φs E ∧
    -- (1c) NEW
    MuLipC (pExp α) C₀ Φs E ∧
    -- (2)
    StarPkgo2 (pExp α) Cs Φs ∧
    -- (3) + `hvan` (2026-10-10 lead edit: θ-end vanishing of the datum, exactly the hypothesis
    -- `hvan` of `StrongEps.EpsUniform_of_data`; supplied for `locG6` by `FinalV2.LocVanish`)
    (∀ (K' : ℝ) (g₀ : Fn), Work.FTS.Nonlin.RegQ (pExp α) 6 g₀ →
      (∀ z, 0 ≤ z → g₀ z 0 = 0 ∧ g₀ z (π / 2) = 0) →
      (∀ ε : ℝ, 0 < ε → Work.FTS.StrongEps.EpsDatum (pExp α) ρ ε g₀) →
      Work.FTS.Nonlin.Xn (pExp α) g₀ ≤ (pExp α) ^ 2 →
      Work.FTS.StrongGlobal.Xn6 (pExp α) g₀ ≤ K' * (pExp α) ^ 2 →
      Work.FTS.StrongEps.EpsUniformMem (pExp α) ρ Φs E g₀ C₀ K') ∧
    -- (3a′) unchanged
    (∀ L β : ℝ, 1 ≤ L → Work.FTS.Nonlin.RegQ (pExp α) 6 (Work.FTS.LocData6.locG6 (pExp α) L β) →
      Work.Construction.L12 (Work.FTS.LocData6.locG6 (pExp α) L β) 0 = 0 →
      ∀ ε : ℝ, 0 < ε → Work.FTS.StrongEps.EpsDatum (pExp α) ρ ε
        (Work.FTS.LocData6.locG6 (pExp α) L β)) ∧
    -- (4′) global_strong2 with the enriched output
    (∀ (g₀ : Fn) (K' : ℝ), Work.FTS.StrongEps.EpsUniformMem (pExp α) ρ Φs E g₀ C₀ K' →
      ∃ gg : Fam, Sol (pExp α) Φs E gg ∧ (∀ z θ, gg z θ 0 = g₀ z θ) ∧
        DynOK' (pExp α) C₀ Φs E gg) ∧
    -- (5′) sup bound of the extension, against the uniform bound
    (∀ g : Fam, DynOK' (pExp α) C₀ Φs E g →
      ∀ τ : ℝ, 0 ≤ τ → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        |extG g z θ τ| ≤ Cg * (C₀ * (pExp α) ^ 2)) ∧
    -- (6′) modulation: bound, continuity, α-Hölder on every [0,S]
    (∀ g : Fam, Sol (pExp α) Φs E g → DynOK' (pExp α) C₀ Φs E g →
      (∀ τ : ℝ, 0 ≤ τ → |Work.FTS.Galerkin.muDyn (pExp α) (PsiCan Φs E g) g τ| ≤ 1 / 2) ∧
      ContinuousOn (Work.FTS.Galerkin.muDyn (pExp α) (PsiCan Φs E g) g) (Set.Ici 0) ∧
      (∀ S : ℝ, 0 < S → ∃ L : ℝ, 0 ≤ L ∧ ∀ τ ∈ Icc (0 : ℝ) S, ∀ τ' ∈ Icc (0 : ℝ) S,
        |Work.FTS.Galerkin.muDyn (pExp α) (PsiCan Φs E g) g τ
          - Work.FTS.Galerkin.muDyn (pExp α) (PsiCan Φs E g) g τ'| ≤ L * |τ - τ'| ^ α)) ∧
    -- (7″) RegPkg' of the extension of the SANITISED right-Taylor τ-extension, given the datum
    -- (REVIEW FIX-2 + RegExport REVIEW F1)
    (∀ g : Fam, Sol (pExp α) Φs E g → DynOK' (pExp α) C₀ Φs E g →
      (∃ L β : ℝ, 1 ≤ L ∧ ∀ z θ, g z θ 0 = Work.FTS.LocData6.locG6 (pExp α) L β z θ) →
      ∀ S : ℝ, 0 < S →
        RegPkg' α S (ampA (maxMu (pExp α) (PsiCan Φs E g) g))
          (ampB (maxMu (pExp α) (PsiCan Φs E g) g)) (extG (gS α (tauExt g)))) ∧
    -- (8′) meridian equation: profile of `extG g`, stream function `psiFire`
    (∀ (g : Fam) (A B : ℝ → ℝ) (C : PhysClock),
      Sol (pExp α) Φs E g → DynOK' (pExp α) C₀ Φs E g →
      ClockData (pExp α) (PsiCan Φs E g) g A B C →
      MeridianEqOn (Work.FTS.Physical.merProfile α A B (extG g) C)
        (Work.FTS.MeridianDyn.merPsi (pExp α) A B (psiFire Φs E g) C) C.T) ∧
    -- (9″) Biot–Savart identification, given the firing family's `RegPkg'` and its agreement
    -- with `g` on the open quadrant (StreamBdry REVIEW FIX-A: no growth inputs)
    (∀ (g G : Fam) (A B : ℝ → ℝ) (C : PhysClock),
      Sol (pExp α) Φs E g → DynOK' (pExp α) C₀ Φs E g →
      ClockData (pExp α) (PsiCan Φs E g) g A B C →
      (∀ S : ℝ, 0 < S → RegPkg' α S A B (extG G)) →
      (∀ z θ τ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ τ → G z θ τ = g z θ τ) →
      ∀ t ∈ Set.Ioo (0 : ℝ) C.T, ∀ x ∈ Uax,
        Work.FTS.Physical.physVel
          (fun x s => - Work.FTS.Physical.physOmega α A B (extG g) C x s) x t
          = Work.Cyl.psiField
              (fun r z => Work.FTS.MeridianDyn.merPsi (pExp α) A B (psiFire Φs E g) C r z t) x) ∧
    -- (10′) C³ of the meridian stream function off the axis and the plane
    (∀ (g : Fam) (A B : ℝ → ℝ) (C : PhysClock),
      Sol (pExp α) Φs E g → DynOK' (pExp α) C₀ Φs E g →
      ClockData (pExp α) (PsiCan Φs E g) g A B C →
      ∀ t ∈ Set.Ioo (0 : ℝ) C.T, ∀ r z : ℝ, 0 < r → z ≠ 0 →
        ContDiffAt ℝ 3 (fun p : ℝ × ℝ =>
          Work.FTS.MeridianDyn.merPsi (pExp α) A B (psiFire Φs E g) C p.1 p.2 t) (r, z))

end Work.FTS.FinalV2
