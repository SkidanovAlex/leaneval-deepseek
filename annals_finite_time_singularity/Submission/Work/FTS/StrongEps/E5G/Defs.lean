/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/E5G/Defs.lean` — the vocabulary of the *global* E5 construction

`exists_limG` (`StrongEps/exists_limG.lean`, the C1–C5 ruling §5) produces **one** family `g` which
satisfies `EpsLimPkg` on every horizon.  The construction has three layers:

* **the tower** — `EpsUniformMem` gives, for every horizon `Tn n = n + 1`, a threshold `ε₁(n)` and a
  solution for every `ε ≤ ε₁(n)`; fixing a single positive sequence `e k ↓ 0` below all thresholds
  (for `k ≥ n`) turns this into a two-index family `G n k` of solutions at horizon `Tn n` and datum
  `e k` (`E5G/Tower.lean`, `TowerAt` below);
* **the nested extraction** — at horizon `Tn n` the sequence `k ↦ G n (ψ n k + n)` is extracted
  along a strictly increasing `ψ n`, with the nesting `ψ (n+1) = ψ n ∘ (strictly increasing)`, so
  that the limit curves of the different horizons are coherent (`E5G/Nest.lean`);
* **the per-horizon assembly** — each `EpsLimPkg` clause at horizon `T` is read off the extraction
  at a horizon `Tn N ≥ T` (`E5G/Pkg.lean`).

Coherence of the limit curves uses the fixed-`ε` uniqueness **D1**
(`Work.FTS.StrongEps.IsEpsSolP_eq_of_epsClass`): the tower solutions at the same datum `e k` agree
on the overlap of their horizons, hence so do their limits.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EpsLimitDefsG
import Submission.Work.FTS.StrongEps.EpsMem
import Submission.Work.FTS.StrongEps.EpsMemRegP
import Submission.Work.FTS.StrongEps.E5ExtractMem
import Submission.Work.FTS.EpsEngine.EpsClass
import Submission.Work.FTS.StrongEps.IsEpsSolP_eq_of_epsClass

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5G

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The horizon of the `n`-th piece: `Tn n = n + 1`.  (A local copy of `Assembly.Tn`, so that the
new chapter does not import the old E5 cone.) -/
def Tn (n : ℕ) : ℝ := (n : ℝ) + 1

theorem Tn_pos (n : ℕ) : 0 < Tn n := by
  simp only [Tn]
  exact lt_of_lt_of_le zero_lt_one (by norm_num)

theorem Tn_mono : Monotone Tn := fun m n h => by
  simp only [Tn]
  exact add_le_add (Nat.cast_le.mpr h) le_rfl

/-- The piece index of a fake time: `⌊τ⌋₊`. -/
def pidx (τ : ℝ) : ℕ := Nat.floor τ

theorem lt_Tn_pidx (τ : ℝ) (_hτ : 0 ≤ τ) : τ < Tn (pidx τ) := by
  have h := Nat.lt_floor_add_one τ
  simpa only [Tn, pidx] using h

/-- **The per-horizon solution data of the tower**.  `TowerAt α C₀ ρ Φs E g₀ n ε K' g` bundles
everything that `EpsUniformMem` provides at the horizon `Tn n` for the datum `ε`: the scheme's
solution, its τ-regularity and, at every fake time of `[0, Tn n]`, the interface clauses (smoothness,
the two `ℋ⁴`/`ℋ⁶`-memberships, the two ball bounds, the class-`C` clause and the joint `C¹`). -/
structure TowerAt (α C₀ : ℝ) (ρ : ℝ × ℝ → ℝ) (Φs : Fn) (E : Fn → Fn) (g₀ : Fn)
    (n : ℕ) (ε K' : ℝ) (g : Fam) : Prop where
  hsol : IsEpsSolP α ρ ε (Tn n) Φs E g₀ g
  hsm : ∀ τ ∈ Set.Icc 0 (Tn n), Work.FTS.EllipticEst.SmoothOpen (slice g τ)
  hmem4p : ∀ τ ∈ Set.Icc 0 (Tn n), Work.Spaces.HkMem α 4 (slice (JfamP ρ ε g) τ)
  hmem6 : ∀ τ ∈ Set.Icc 0 (Tn n), Work.Spaces.HkMem α 6 (slice g τ)
  hb4 : ∀ τ ∈ Set.Icc 0 (Tn n), Work.FTS.Nonlin.Xn α (slice (JfamP ρ ε g) τ) ≤ C₀ * α ^ 2
  hb6 : ∀ τ ∈ Set.Icc 0 (Tn n), Work.FTS.StrongGlobal.Xn6 α (slice g τ) ≤ K'
  hC : ∀ τ ∈ Set.Icc 0 (Tn n), Work.FTS.ClassC.ClassC α (slice (JfamP ρ ε g) τ)
  hjoint : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
    (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 (Tn n))

/-- `TowerAt` restricts to a shorter fake-time interval. -/
theorem TowerAt.mono {α C₀ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {n : ℕ} {ε K' T : ℝ} {g : Fam} (h : TowerAt α C₀ ρ Φs E g₀ n ε K' g) (hT : T ≤ Tn n) :
    IsEpsSolP α ρ ε (Tn n) Φs E g₀ g ∧
      (∀ τ ∈ Set.Icc 0 T, Work.FTS.EllipticEst.SmoothOpen (slice g τ)) ∧
      (∀ τ ∈ Set.Icc 0 T, Work.Spaces.HkMem α 4 (slice (JfamP ρ ε g) τ)) ∧
      (∀ τ ∈ Set.Icc 0 T, Work.Spaces.HkMem α 6 (slice g τ)) ∧
      (∀ τ ∈ Set.Icc 0 T, Work.FTS.Nonlin.Xn α (slice (JfamP ρ ε g) τ) ≤ C₀ * α ^ 2) ∧
      (∀ τ ∈ Set.Icc 0 T, Work.FTS.StrongGlobal.Xn6 α (slice g τ) ≤ K') ∧
      (∀ τ ∈ Set.Icc 0 T, Work.FTS.ClassC.ClassC α (slice (JfamP ρ ε g) τ)) ∧
      ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 T) :=
  ⟨h.hsol, fun τ hτ => h.hsm τ ⟨hτ.1, le_trans hτ.2 hT⟩,
    fun τ hτ => h.hmem4p τ ⟨hτ.1, le_trans hτ.2 hT⟩,
    fun τ hτ => h.hmem6 τ ⟨hτ.1, le_trans hτ.2 hT⟩,
    fun τ hτ => h.hb4 τ ⟨hτ.1, le_trans hτ.2 hT⟩,
    fun τ hτ => h.hb6 τ ⟨hτ.1, le_trans hτ.2 hT⟩,
    fun τ hτ => h.hC τ ⟨hτ.1, le_trans hτ.2 hT⟩,
    h.hjoint.mono (by
      intro q hq
      exact ⟨hq.1, hq.2.1, hq.2.2.1, le_trans hq.2.2.2 hT⟩)⟩

/-- **`TowerAt` gives the τ-regularity class `EpsRegP`** used by the extraction: the joint `C¹` is
`hjoint`, and every slice is an `EpsDatumP` (its class-`C` conjunct is the *projected* slice, which
is `TowerAt.hC` after `slice_JfamP`). -/
theorem TowerAt.toEpsRegP {α C₀ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {n : ℕ} {ε K' : ℝ} {g : Fam} (h : TowerAt α C₀ ρ Φs E g₀ n ε K' g) :
    EpsRegP α ρ ε (Tn n) g :=
  ⟨h.hjoint, fun τ hτ =>
    ⟨h.hsm τ hτ, h.hmem6 τ hτ, by simpa only [slice_JfamP] using h.hC τ hτ⟩⟩

/-- **The class-`C` clause of `TowerAt` as `EpsClass`** (the input of the fixed-`ε` uniqueness D1):
at the same datum `ε` and with the horizon-`n` level-`6` bound, every slice of a tower solution
lies in `EpsClass α ρ ε C₀ B` for any `B` dominating `K'`. -/
theorem TowerAt.epsClass {α C₀ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {n : ℕ} {ε K' B T : ℝ} {g : Fam} (h : TowerAt α C₀ ρ Φs E g₀ n ε K' g)
    (hB : K' ≤ B) (hT : T ≤ Tn n) :
    ∀ τ ∈ Set.Icc 0 T, Work.FTS.EpsEngine.EpsClass α ρ ε C₀ B (slice g τ) := by
  intro τ hτ
  have hτ' : τ ∈ Set.Icc 0 (Tn n) := ⟨hτ.1, le_trans hτ.2 hT⟩
  exact ⟨h.hsm τ hτ', h.hmem6 τ hτ', le_trans (h.hb6 τ hτ') hB,
    by simpa only [slice_JfamP] using h.hC τ hτ', h.hb4 τ hτ'⟩

end Work.FTS.StrongEps.E5G
