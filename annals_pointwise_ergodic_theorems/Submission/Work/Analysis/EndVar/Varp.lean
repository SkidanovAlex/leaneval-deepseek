import Submission.Work.Analysis.EndVar.Statements

/-!
# Theorem `varp`: the variational paraproduct estimates

This module records the paper's Theorem `varp` (Krause--Mirek--Tao, *Pointwise ergodic theorems
for non-conventional bilinear polynomial averages*, Annals 195 (2022), §4) in the §5 notation of
`Work.Analysis.EndVar.Defs`, and names the reduction **(A) from `varp`** that the §5 assembly
consumes:

* `lmax l₁ l₂ s₁ s₂ = max (max l₁ l₂) (max s₁ s₂)` — the exponent of the gain of Theorem `varp`;
* `VarpStatement Pj P d C₀ p₁ p₂ p r` — **Theorem `varp`**: the paraproduct pieces
  `F^{u,l₁,s₁}_N f`, `G^{u,l₂,s₂}_N g` of the halved averages, restricted to the index set
  `I^{l,s₁,s₂}` (`inIndexSet`), satisfy the variational estimate with the exponential gain
  `2^{-c max(l,s₁,s₂)}`;
* `majorArcPartR` — the major-arc part `R` of the halved average as a function of the *real*
  scale, as it appears in `MajorArcVarEstimate`.

The reduction `majorArcVarEstimate_of_varp` (the last page of §5: the arithmetic dyadic
decomposition, the continuous dyadic decomposition, and the geometric summation
`sum_two_rpow_neg_max_le`) is proved in
`Submission/Work/Analysis/EndVar/majorArcVarEstimate_of_varp.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Analysis.EndVar

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal PNat BigOperators
open PointwiseErgodicTheorems
open Submission.PointwiseErgodicTheorems
open Work.Analysis.Paraproduct (IWProjections)

/-- The exponent of the gain of Theorem `varp`: `max (max l₁ l₂) (max s₁ s₂)`. -/
def lmax (l₁ l₂ : ℕ) (s₁ s₂ : ℤ) : ℤ := max (max (l₁ : ℤ) (l₂ : ℤ)) (max s₁ s₂)

/--
> **SUPERSEDED — use `Work.KMTContract.VarpStatementΛ`.**  The constant `C : ℝ≥0` here is
> uniform in the lacunarity parameter `Λ`; as `Λ → 1⁺` a finite `Λ`-lacunary set can contain any
> finite set of integers, so a `Λ`-uniform bound would give the full variational estimate, which
> Krause--Mirek--Tao list as open question 2.  The paper's constant depends on `λ = Λ`.  The
> contract's `VarpStatementΛ` (module `Submission/Work/KMTContract/VarpLambda.lean`) uses
> `C : ℝ≥0 → ℝ≥0` and reproves the §5 reductions on it
> (`majorArcVarEstimate_of_varpΛ`, `exists_varEstHalfFin_of_varpΛ_minorArc`).
> See `Submission/Work/KMTContract/QUARANTINE.md` and `ROUTE_LEAD.md` §0 F2.

**Theorem `varp` (variational paraproduct estimates)**, in the §5 notation.

There are a rate `c > 0` and a constant `C` such that for every `Λ`-lacunary sequence `a` of
scales `≥ 1`, every height parameters `l₁, l₂`, every `u`, every `s₁, s₂` and all `f, g`, the
paraproduct pieces of the halved averages, restricted to the index set
`I^{max(l₁,l₂),s₁,s₂} = {N : max(l₁,l₂), s₁, s₂ ≤ l_{(N)}}`, obey

`‖ (Ã_N(F^{u,l₁,s₁}_N f, G^{u,l₂,s₂}_N g))_{N ∈ I} ‖_{ℓ^p(ℤ;V^r)} ≤ C 2^{-c max(l,s₁,s₂)}
  ‖f‖_{ℓ^{p₁}} ‖g‖_{ℓ^{p₂}}`.

(The paper needs this only for `u = ⌊C₂ 2^{2ρl}⌋` with `l = max(l₁,l₂)`; we state it for all `u`,
which is the form used by the §5 assembly.  The paper's extra factor `⟨max(l,s₁,s₂)⟩^{O(1)}` and
the `2^{O(ρl)}` of the small-scale estimate are absorbed into `C` after the interpolation of
`(all-all-weak)` to `(all-all)`.) -/
def VarpStatement (Pj : IWProjections) (P : ℤ[X]) (d C₀ : ℕ)
    (p₁ p₂ p : ℝ≥0∞) (r : ℝ≥0) : Prop :=
  ∃ (c : ℝ) (C : ℝ≥0), 0 < c ∧
    ∀ (a : ℕ → ℝ≥0) (Λ : ℝ≥0) (l₁ l₂ u : ℕ) (s₁ s₂ : ℤ) (f g : ℤ → ℂ),
      1 < Λ → Lacunary Λ a → (∀ n, 1 ≤ a n) →
      eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ =>
          if inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) s₁ s₂ (Nat.floor (a n)) then
            AhalfR TZ (a n) X P
              (Fpiece Pj u l₁ s₁ (Nat.floor (a n)) f)
              (Gpiece Pj (d : ℤ) u l₂ s₂ (Nat.floor (a n)) g) x
          else 0))
        p Measure.count
      ≤ (C : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ) ^ (-(c * (lmax l₁ l₂ s₁ s₂ : ℝ)))) *
          eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count

/-- The major-arc part of the halved average as a function of the real scale, matching the family
`R` of `MajorArcVarEstimate`. -/
def majorArcPartR (Pj : IWProjections) (P : ℤ[X]) (d C₀ : ℕ) :
    ℝ≥0 → (ℤ → ℂ) → (ℤ → ℂ) → (ℤ → ℂ) :=
  fun N f g => majorArcPart Pj P d C₀ (Nat.floor N) f g

/-- Measurability of the major arc part, given that the projections preserve measurability.  This
is what discharges the `hmeasR` hypothesis of `varEstHalfFin_of_majorArcFam`. -/
lemma aemeasurable_majorArcPartR (Pj : IWProjections) (P : ℤ[X]) (d C₀ : ℕ) (N : ℝ≥0)
    (f g : ℤ → ℂ)
    (hf : ∀ (l : ℕ) (k : ℤ), AEMeasurable (Pj.proj l k f) Measure.count)
    (hg : ∀ (l : ℕ) (k : ℤ), AEMeasurable (Pj.proj l k g) Measure.count) :
    AEMeasurable (majorArcPartR Pj P d C₀ N f g) Measure.count :=
  aemeasurable_AhalfR measurePreserving_TZ (Nat.floor N) X P (hf _ _) (hg _ _)

/-- The `s₁, s₂` summation of the last page of §5: the geometric weights
`2^{-8ρ max(l,s₁,s₂)}` sum to at most `2^{-ρl}` over `s₁, s₂ ∈ [-u, l]`. -/
theorem sum_rpow_neg_lmax_le {ρ : ℝ} (hρ : 0 < ρ) (u l : ℕ)
    (hu : (u : ℝ) + (l : ℝ) + 1 ≤ (2 : ℝ) ^ (2 * ρ * (l : ℝ))) :
    ∑ s₁ ∈ Finset.Icc (-(u : ℤ)) (l : ℤ), ∑ s₂ ∈ Finset.Icc (-(u : ℤ)) (l : ℤ),
        (2 : ℝ) ^ (-(8 * ρ * (lmax l l s₁ s₂ : ℝ)))
      ≤ (2 : ℝ) ^ (-(ρ * (l : ℝ))) := by
  have h := sum_two_rpow_neg_max_le (ρ := ρ) hρ u l hu
  refine le_of_eq ?_ |>.trans h
  refine Finset.sum_congr rfl (fun s₁ _ => Finset.sum_congr rfl (fun s₂ _ => ?_))
  have : lmax l l s₁ s₂ = max (l : ℤ) (max s₁ s₂) := by simp [lmax]
  rw [this]

end

end Work.Analysis.EndVar
