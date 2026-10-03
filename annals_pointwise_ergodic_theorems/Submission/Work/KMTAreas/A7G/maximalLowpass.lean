import Mathlib
import Submission.Work.KMTAreas.A7Lpd.bandSquareAll
import Submission.Work.KMTAreas.A7Lpd.lacunaryMaxAux
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Work.KMTAreas.A7G

noncomputable section

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators

/-!
# The values-supremum (Ionescu--Wainger maximal) estimate for the low-pass family

This module proves `Work.KMTAreas.A7G.maximalLowpass`:

`∃ Cρ > 0, ∃ C > 0, ∀ l m₀, GoodMajorArcs ρ Cρ l (-(m₀)) → ∀ f : ℤ → ℂ,`
`  ‖ sup_n |Π_{≤l,≤-(m₀+n)} f| ‖_{ℓ^p(ℤ)} ≤ C (1+l) ‖f‖_{ℓ^p(ℤ)},   1 < p < ∞.`

## The reduction

Write `T_n = lpf ρ l m₀ n f = Π_{≤l,≤-(m₀+n)} f` and `Δ_n = T_{n+1} − T_n`.  The finite
telescoping `T_K = T_0 − Σ_{n<K}Δ_n` gives, pointwise,

`sup_n |T_n f(x)| ≤ |T_0 f(x)| + sup_K |Σ_{n<K} Δ_n f(x)|`

(`supPart_le_first_add_partSum` below).  The right-hand side is bounded in `ℓᵖ` by

* the **uniform single-scale bound** `Work.KMTAreas.A7.kmtProj_lp_bound_uniform`
  (`‖Π_{≤l,≤k} f‖_{ℓᵖ} ≤ C‖f‖_{ℓᵖ}` with `C` independent of `l, k`), and
* the **lacunary maximal (Men'shov/Lépingle) piece** `Work.KMTAreas.A7Hi2.lacunaryMaxPiece`,
  which bounds `‖sup_K|Σ_{n<K}Δ_n f|‖_{ℓᵖ}` by `C‖(Σ_n|Δ_n f|²)^{1/2}‖_{ℓᵖ} + C‖f‖_{ℓᵖ}` with an
  `l`-free constant, in terms of the `ℝ≥0∞`-valued band square function `Work.KMTAreas.A7Hi.sqFun`;
* the **band square-function bound** `Work.KMTAreas.A7Lpd.bandSquareUnif`
  (`‖(Σ_n|Δ_n f|²)^{1/2}‖_{ℓᵖ} ≤ C‖f‖_{ℓᵖ}`, from the uniform-in-signs Mikhlin bound for the
  annuli plus Khintchine, again with an `l`-free constant).

The constant is `C_S + C_M(C_B + 1)`, which is `l`-free, hence in particular at most
`(C_S + C_M(C_B + 1))(1+l)`.

## Status

The single open input is `Work.KMTAreas.A7Hi2.lacunaryMaxPiece` (the shared crux of the `A7`
low-frequency chapter).  It is the *weakest* of the sibling statements of that crux (`∃ Cρ > 0`,
the `+C‖f‖` term, partial sums rather than the chain part), and it is **the root** of the chapter's
dependency order: the sibling `A7Hi2.lacunaryMaxPieceProved` is *downstream* of this file
(`lacunaryMaxPieceProved → reverseLPAnnuli → perKLeSqFunGeTwo → A7G.maximalLowpass →
A7Hi2.lacunaryMaxPiece`), so it cannot be imported here, and it is *this* stub that must be closed
for `A7G.maximalLowpass` to be complete.  The tree's proved reductions
`lacunaryMaxPieceProved_of_{chainPartSqFun,varPartSqFun,fibreMz,iwMaximal,chainPartBound,varBound,
varRhoAll,tower_and_defect}` mean that *any* of the equivalent crux statements lands it.  Everything
in this file other than that import is complete and axiom-clean.

For `f ∉ ℓᵖ` the right-hand side of the statement is `⊤`, so only `f ∈ ℓᵖ` matters; for such `f`
every value of the walk is honest (the defining `tsum` is absolutely convergent by Hölder), so the
junk-value defect of the unconditional `tsum` in `kmtProj` is not an issue here.
-/

/-- The `ℝ≥0∞`-form of an `eLpNorm`: `‖ ‖g‖ₑ ‖_p = ‖g‖_p`. -/
lemma eLpNorm_enorm_eq {g : ℤ → ℂ} {p : ENNReal} (h0 : p ≠ 0) (ht : p ≠ ⊤) :
    MeasureTheory.eLpNorm (fun x : ℤ => ‖g x‖ₑ) p MeasureTheory.Measure.count
      = MeasureTheory.eLpNorm g p MeasureTheory.Measure.count := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) h0 ht,
    MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) h0 ht]
  simp only [enorm_eq_self]

/-- **Telescoping plus the partial-sum supremum.**  The values supremum of the low-pass family
`n ↦ T_n f = Π_{≤l,≤-(m₀+n)} f` is dominated pointwise by its first value together with the
supremum over `K` of the partial sums of the annuli `Δ_n = T_{n+1} − T_n`. -/
lemma supPart_le_first_add_partSum (ρ : ℝ) (l m₀ : ℕ) (f : ℤ → ℂ) (x : ℤ) (r : NNReal) :
    Work.KMTAreas.A7Hi.supPart r (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l m₀ n f x)
      ≤ ‖Work.KMTAreas.A7Hi.lpf ρ l m₀ 0 f x‖ₑ
        + (⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
            (Work.KMTAreas.A7Hi.lpf ρ l m₀ (i + 1) f x
              - Work.KMTAreas.A7Hi.lpf ρ l m₀ i f x))‖ₑ) := by
  have hbase : Work.KMTAreas.A7Hi.supPart r
        (fun n : ℕ => Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((n : ℕ) : ℤ))) f x)
      ≤ ‖Work.KMTContract.kmtProj ρ l (-(m₀ : ℤ)) f x‖ₑ
        + (⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
            (Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((i : ℕ) : ℤ))) f x
              - Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (((i + 1 : ℕ)) : ℤ))) f x))‖ₑ) := by
    refine iSup_le fun n => ?_
    set T : ℕ → ℂ := fun k =>
      Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (k : ℤ))) f x with hT
    have htel : (∑ i ∈ Finset.range n,
          (Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((i : ℕ) : ℤ))) f x
            - Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (((i + 1 : ℕ)) : ℤ))) f x))
        = T 0 - T n := by
      rw [hT]
      simpa using Work.KMTAreas.A7Lpd.sum_range_kmtProj_sub ρ l m₀ f x n
    change ‖T n‖ₑ ≤ ‖Work.KMTContract.kmtProj ρ l (-(m₀ : ℤ)) f x‖ₑ + _
    have h0 : Work.KMTContract.kmtProj ρ l (-(m₀ : ℤ)) f x = T 0 := by
      rw [hT]; norm_num
    have hTn : T n = T 0 - ∑ i ∈ Finset.range n, (T i - T (i + 1)) := by
      rw [htel]; ring
    have hkey : ‖T n‖ₑ ≤ ‖T 0‖ₑ + ⨆ K : ℕ, ‖∑ i ∈ Finset.range K, (T i - T (i + 1))‖ₑ := by
      rw [hTn]
      exact le_trans (enorm_sub_le) (add_le_add le_rfl
        (le_iSup (fun K : ℕ => ‖∑ i ∈ Finset.range K, (T i - T (i + 1))‖ₑ) n))
    simpa only [h0] using hkey
  refine hbase.trans (add_le_add le_rfl ?_)
  have hfun : (fun K : ℕ => ‖(∑ i ∈ Finset.range K,
        (Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((i : ℕ) : ℤ))) f x
          - Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (((i + 1 : ℕ)) : ℤ))) f x))‖ₑ)
      = fun K : ℕ => ‖(∑ i ∈ Finset.range K,
        (Work.KMTAreas.A7Hi.lpf ρ l m₀ (i + 1) f x
          - Work.KMTAreas.A7Hi.lpf ρ l m₀ i f x))‖ₑ := by
    funext K
    have hterm : (∑ i ∈ Finset.range K,
          (Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((i : ℕ) : ℤ))) f x
            - Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (((i + 1 : ℕ)) : ℤ))) f x))
        = -(∑ i ∈ Finset.range K,
          (Work.KMTAreas.A7Hi.lpf ρ l m₀ (i + 1) f x
            - Work.KMTAreas.A7Hi.lpf ρ l m₀ i f x)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      show Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((i : ℕ) : ℤ))) f x
          - Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (((i + 1 : ℕ)) : ℤ))) f x
        = -(Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (((i + 1 : ℕ)) : ℤ))) f x
          - Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((i : ℕ) : ℤ))) f x)
      ring
    rw [hterm, enorm_neg]
  rw [hfun]

end

end Work.KMTAreas.A7G
