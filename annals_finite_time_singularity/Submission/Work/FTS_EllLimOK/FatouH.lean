/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.FatouH` — the limit data over the installed honest hypothesis `HasPkgH`

The lead's ruling of 2026-10-11 (`sources/ftsV2/fts_ellimok_ruling.md`, review
`fts_ellimok_ruling_REVIEW.md`) replaces the refuted `HasPkgF` by

```
HasPkgH α Ce E := HasPkg α Ce E ∧ PkgCos α E ∧ PkgMemSqH α Ce E ∧ PkgBoxH α E
```

(`RulingELF.lean`), whose producers `L1`/`L2`/`L3` are to be built from route (b)
(`∀ g ∈ ClassC, ∃ Ψ, EllClassOk 8 α g Ψ`, the new hypothesis of `FinalV2.Producers.core1_1a3`).

This module restates the three sequence-level predicates of the closure over `HasPkgH`:

* **`LocalBoundH`** — the pointwise jet bounds, now with a **constant** right-hand side (the
  `1/(1+z)` rate of `Defs3.LocalBound4` is false for class-`C` sources with `z^{-s}` tails,
  `s ∈ (1/2,1)`).  Proved here from `HasPkg ∧ PkgCos` via `PkgJets.pkg_pointwise_jets` (whose only
  extra input is the pinning datum, supplied by `Pinning.hpin_of_pkgCos`).
* **`FatouDataH`** — the uniform `ℋ⁰`-memberships of `E (fn n)` and `E (fn n)/cos θ` with one
  common `HkSq` bound and one common **`z`-local** (`C(1+1/z)`) `θ`-slice bound.  Proved here from
  `PkgMemSqH`.
* **`BoxDataH`** — the closed-box data: on every box `[a,b] × [0,π/2]` (`0 < a ≤ b`) the sequence
  converges to a limit that is `C²` on the box and vanishes on the two angular boundary lines.
  Produced from `PkgBoxH` (a *Hölder* equicontinuity argument, replacing the false
  `PkgStrip`/`PkgCorner` pair); that producer is a separate module.
* **`ClosedCompact3H`** — obligation 1 over `HasPkgH`; proved in
  `ClosedCompact3H_of_bounds_fatou`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_EllLimOK.RulingELF
import Submission.Work.FTS_EllLimOK.PkgJets.pkg_pointwise_jets
import Submission.Work.FTS_EllLimOK.Pinning.hpin_of_pkgCos
import Submission.Work.FTS_EllLimOK.FatouG

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The predicates

(`HasPkgH`, `PkgMemSqH`, `PkgBoxH` are stated in `RulingELF` — the installed copy of the lead's
ruling; the abbreviations below let the rest of the area use the shorter names.) -/

/-- The honest repaired hypothesis of the ruling. -/
abbrev HasPkgH (α Ce : ℝ) (E : Fn →ₗ[ℝ] Fn) : Prop := RulingELF.HasPkgH α Ce E

/-- **The pointwise jet bounds with a constant right-hand side**, along every `LimSeq4`, for every
operator carrying `HasPkgH`. -/
def LocalBoundH (α Ce : ℝ) : Prop :=
  ∀ E : Fn →ₗ[ℝ] Fn, HasPkgH α Ce E → ∀ (fn : ℕ → Fn) (f : Fn), LimSeq4 α fn f →
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ j i : ℕ, j + i ≤ 4 → ∀ z θ : ℝ,
      (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.mixed j i (E (fn n)) z θ| ≤ C

/-- **The sequence-level `ℋ⁰`/`θ`-slice data**: one `HkSq` bound and one `z`-local `θ`-slice bound
for the two quantities `E (fn n)` and `E (fn n)/cos θ`. -/
def FatouDataH (α Ce : ℝ) : Prop :=
  ∀ E : Fn →ₗ[ℝ] Fn, HasPkgH α Ce E → ∀ (fn : ℕ → Fn) (f : Fn), LimSeq4 α fn f →
    ∃ C : ℝ, 0 < C ∧
      (∀ n : ℕ, Work.Spaces.HkMem α 0 (E (fn n)) ∧
        Work.Spaces.HkSq α 0 (E (fn n)) ≤ C ∧
        (∀ z ∈ Work.Spaces.Iz,
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (E (fn n)) z θ)
            ≤ C * (1 + 1 / z))) ∧
      (∀ n : ℕ, Work.Spaces.HkMem α 0 (fun z θ => E (fn n) z θ / Real.cos θ) ∧
        Work.Spaces.HkSq α 0 (fun z θ => E (fn n) z θ / Real.cos θ) ≤ C ∧
        (∀ z ∈ Work.Spaces.Iz,
          (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 0 (fun z θ => E (fn n) z θ / Real.cos θ) z θ)
              ≤ C * (1 + 1 / z)))

/-- **The closed-box data**: on every box `[a,b] × [0,π/2]` (`0 < a < b`) the sequence along a
`LimSeq4` converges to a limit `G` that is `C²` on the box and vanishes on the two angular
boundary lines.  (The *non-degenerate* boxes only: on the degenerate box `cbox a a` the
`iteratedFDerivWithin`-bounds of `PkgBoxH` are underivable — see its docstring — and the degenerate
case of `BoxReg` is recovered inside `ClosedCompact3H_of_bounds_fatou` by `ContDiffOn.mono` from
`cbox a (a+1)`.) -/
def BoxDataH (α Ce : ℝ) : Prop :=
  ∀ E : Fn →ₗ[ℝ] Fn, HasPkgH α Ce E → ∀ (fn : ℕ → Fn) (f : Fn), LimSeq4 α fn f →
    ∀ a b : ℝ, 0 < a → a < b → ∃ G : Fn,
      ContDiffOn ℝ 2 (Function.uncurry G) (cbox a b) ∧
      (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2),
        Filter.Tendsto (fun n => E (fn n) z θ) Filter.atTop (𝓝 (G z θ))) ∧
      (∀ z ∈ Set.Icc a b, G z 0 = 0 ∧ G z (π / 2) = 0)

/-- **Obligation 1 (compactness) over `HasPkgH`.** -/
def ClosedCompact3H (α Ce : ℝ) : Prop :=
  ∀ E : Fn →ₗ[ℝ] Fn, HasPkgH α Ce E → ∀ (fn : ℕ → Fn) (f : Fn), LimSeq4 α fn f →
    ∃ Ψ : Fn, IsJetLimit3G α E fn f Ψ

/-- **The small-`α` shapes.** -/
def SmallLocalBoundH : Prop :=
  ∃ α₁ : ℝ, 0 < α₁ ∧ ∀ α : ℝ, 0 < α → α ≤ α₁ → ∀ Ce : ℝ, LocalBoundH α Ce

def SmallFatouDataH : Prop :=
  ∃ α₁ : ℝ, 0 < α₁ ∧ ∀ α : ℝ, 0 < α → α ≤ α₁ → ∀ Ce : ℝ, FatouDataH α Ce

def SmallBoxDataH : Prop :=
  ∃ α₁ : ℝ, 0 < α₁ ∧ ∀ α : ℝ, 0 < α → α ≤ α₁ → ∀ Ce : ℝ, BoxDataH α Ce

def SmallCompact3H : Prop :=
  ∃ α₁ : ℝ, 0 < α₁ ∧ ∀ α : ℝ, 0 < α → α ≤ α₁ → ∀ Ce : ℝ, ClosedCompact3H α Ce

/-! ## The two derivations that need no new analysis -/

theorem HasPkgH.toHasPkg {α Ce : ℝ} {E : Fn →ₗ[ℝ] Fn} (h : HasPkgH α Ce E) :
    HasPkg α Ce E := h.1

theorem HasPkgH.cos {α Ce : ℝ} {E : Fn →ₗ[ℝ] Fn} (h : HasPkgH α Ce E) :
    PkgCos α E := h.2.1

theorem HasPkgH.memSq {α Ce : ℝ} {E : Fn →ₗ[ℝ] Fn} (h : HasPkgH α Ce E) :
    RulingELF.PkgMemSqH α Ce E := h.2.2.1

theorem HasPkgH.box {α Ce : ℝ} {E : Fn →ₗ[ℝ] Fn} (h : HasPkgH α Ce E) :
    RulingELF.PkgBoxH α E := h.2.2.2

/-- **The pointwise jet bounds hold over `HasPkgH`**: `PkgJets.pkg_pointwise_jets` needs only
`HasPkg`, `LimSeq4` and the pinning datum, and the pinning datum comes from `PkgCos` alone
(`Pinning.hpin_of_pkgCos`). -/
theorem localBoundH_of_hasPkgH {α Ce : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    LocalBoundH α Ce := by
  intro E hE fn f hL
  exact Work.FTS_EllLimOK.PkgJets.pkg_pointwise_jets hα hα1 hE.toHasPkg hL
    (fun n z hz => Work.FTS_EllLimOK.Pinning.hpin_of_pkgCos hα hα1 hE.toHasPkg hE.cos
      (fn n) (hL.classC n) z hz)

theorem smallLocalBoundH : SmallLocalBoundH :=
  ⟨1, one_pos, fun α hα hα1 Ce => localBoundH_of_hasPkgH hα hα1⟩

/-- **The sequence-level `ℋ⁰`/`θ`-slice data hold over `HasPkgH`**: `PkgMemSqH` gives the two
memberships with `HkSq ≤ Ce·Xn6²` and the `z`-local slice bound `≤ Ce(1+1/z)·Xn6²`, and along a
`LimSeq4` the source norms are uniformly bounded, so one constant works for the whole sequence. -/private theorem fatouDataH_clause {α Ce B : ℝ} {E : Fn →ₗ[ℝ] Fn} {fn : ℕ → Fn}
    (hm : RulingELF.PkgMemSqH α Ce E) (hclass : ∀ n, Work.FTS.ClassC.ClassC α (fn n))
    (hB : ∀ n, Work.FTS.StrongGlobal.Xn6 α (fn n) ≤ B) (Ξ : ℕ → Fn)
    (hΞ : ∀ n, Ξ n = E (fn n) ∨ Ξ n = fun z θ => E (fn n) z θ / Real.cos θ) :
    ∀ n : ℕ, Work.Spaces.HkMem α 0 (Ξ n) ∧
      Work.Spaces.HkSq α 0 (Ξ n) ≤ |Ce| * (max B 0) ^ 2 * 2 + 1 ∧
      ∀ z ∈ Work.Spaces.Iz,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (Ξ n) z θ)
          ≤ (|Ce| * (max B 0) ^ 2 * 2 + 1) * (1 + 1 / z) := by
  intro n
  have hcx0 : 0 ≤ |Ce| * (max B 0) ^ 2 := mul_nonneg (abs_nonneg Ce) (sq_nonneg _)
  have hCX : |Ce| * (max B 0) ^ 2 ≤ |Ce| * (max B 0) ^ 2 * 2 + 1 := by linarith
  have hCpos : (0 : ℝ) < |Ce| * (max B 0) ^ 2 * 2 + 1 := by linarith
  have hBn : Work.FTS.StrongGlobal.Xn6 α (fn n) ≤ max B 0 :=
    le_trans (hB n) (le_max_left _ _)
  have hsq : Work.FTS.StrongGlobal.Xn6 α (fn n) ^ 2 ≤ (max B 0) ^ 2 := by
    nlinarith [Work.Spaces.HkNorm_nonneg α 6 (fn n)]
  obtain ⟨hmem, hbnd, hslice⟩ := hm (fn n) (hclass n) (Ξ n) (hΞ n)
  have hCeb : Ce * Work.FTS.StrongGlobal.Xn6 α (fn n) ^ 2 ≤ |Ce| * (max B 0) ^ 2 := by
    calc Ce * Work.FTS.StrongGlobal.Xn6 α (fn n) ^ 2
        ≤ |Ce| * Work.FTS.StrongGlobal.Xn6 α (fn n) ^ 2 :=
          mul_le_mul_of_nonneg_right (le_abs_self Ce) (sq_nonneg _)
      _ ≤ |Ce| * (max B 0) ^ 2 := mul_le_mul_of_nonneg_left hsq (abs_nonneg Ce)
  refine ⟨hmem, le_trans hbnd (le_trans hCeb hCX), fun z hz => ?_⟩
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
  · subst h0
    have hzero : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (Ξ n) 0 θ) = 0 := by
      rw [show (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (Ξ n) 0 θ)
            = ∫ θ in Work.Spaces.Iθ, (0 : ℝ) from
          MeasureTheory.setIntegral_congr_fun measurableSet_Icc
            (fun θ _ => Work.FTS.LocData.HkIntegrand_zero_fst α 0 (Ξ n) θ)]
      simp
    rw [hzero]
    simpa using hCpos.le
  · have h1z : (0 : ℝ) ≤ 1 + 1 / z := by positivity
    have hslice' : Ce * (1 + 1 / z) * Work.FTS.StrongGlobal.Xn6 α (fn n) ^ 2
        ≤ (|Ce| * (max B 0) ^ 2 * 2 + 1) * (1 + 1 / z) := by
      calc Ce * (1 + 1 / z) * Work.FTS.StrongGlobal.Xn6 α (fn n) ^ 2
          = (Ce * Work.FTS.StrongGlobal.Xn6 α (fn n) ^ 2) * (1 + 1 / z) := by ring
        _ ≤ (|Ce| * (max B 0) ^ 2) * (1 + 1 / z) := mul_le_mul_of_nonneg_right hCeb h1z
        _ ≤ (|Ce| * (max B 0) ^ 2 * 2 + 1) * (1 + 1 / z) :=
            mul_le_mul_of_nonneg_right hCX h1z
    exact le_trans (hslice z hz0) hslice'

/-- **The sequence-level `ℋ⁰`/`θ`-slice data hold over `HasPkgH`**: `PkgMemSqH` gives the two
memberships with `HkSq ≤ Ce·Xn6²` and the `z`-local slice bound `≤ Ce(1+1/z)·Xn6²`, and along a
`LimSeq4` the source norms are uniformly bounded, so one constant works for the whole sequence. -/
theorem fatouDataH_of_hasPkgH {α Ce : ℝ} (hα : 0 < α) : FatouDataH α Ce := by
  intro E hE fn f hL
  obtain ⟨B, hB⟩ := hL.bound
  refine ⟨|Ce| * (max B 0) ^ 2 * 2 + 1, by positivity, ?_, ?_⟩
  · exact fatouDataH_clause hE.memSq hL.classC hB (fun n => E (fn n)) (fun n => Or.inl rfl)
  · exact fatouDataH_clause hE.memSq hL.classC hB
      (fun n z θ => E (fn n) z θ / Real.cos θ) (fun n => Or.inr rfl)


theorem smallFatouDataH : SmallFatouDataH :=
  ⟨1, one_pos, fun α hα _ Ce => fatouDataH_of_hasPkgH hα⟩

end Work.FTS_EllLimOK
