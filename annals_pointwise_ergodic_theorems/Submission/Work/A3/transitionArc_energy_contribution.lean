import Mathlib
import Submission.Work.A3.expSum_arcCover_setIntegral_le
import Submission.Work.A3.measurableSet_transitionArcSet

/-!
# The `2s`-th moment of the exponential sum over the transition arcs (Area A3)

This module is the assembly step turning the *pointwise* transition-arc bound

`‖expSum Q N (a/q + β)‖ ≤ C q^{-δ} mArcKernel N d β`   (transition range of `β`)

into the *energy* estimate over the transition arcs

`∫_{transitionArcSet Q N γ ∩ [0,1]} ‖expSum Q N θ‖^{2s} ≤ C'^{2s} N^{2s-d}`,  `d = Q.natDegree`.

The two ingredients are:

* `Work.A3.expSum_arcCover_setIntegral_le` — the abstract summation: whenever a set `A` is covered,
  at every point of `A ∩ [0,1]`, by *some* arc of the shape `q ≤ M`, `-1 ≤ a ≤ q+1`,
  `‖expSum Q N θ‖ ≤ C q^{-δ} mArcKernel N d (θ - a/q)`, then
  `∫_{A ∩ [0,1]} ‖expSum Q N‖^{2s} ≤ C'^{2s} N^{2s-d}` with `C'` *independent of `A` and of `M`*
  (the `q`-sum `∑_q (q+3) q^{-2sδ}` converges precisely because `sδ > 1`);
* `transitionArc_witness_cover` (below) — the arithmetic normalisation of the witness: if
  `θ ∈ transitionArcSet Q N γ ∩ [0,1]` with `0 ≤ γ ≤ 1`, then the *given* witness `(q,a)` of the
  definition has `q ≤ ⌊N^γ⌋`, `-1 ≤ a ≤ q+1` (because the arc radius `1/(q N^{d/2})` is at most
  `1/q`, and `a/q` is within `1/q` of `θ ∈ [0,1]`), and it satisfies the transition hypothesis, so
  the pointwise bound applies verbatim.

Nothing else is used: the transition range itself is *not* needed for the summation, only for the
pointwise input, which is carried as the hypothesis `htrans` (it is the content of
`A3/transitionArc_bound`).
-/

set_option linter.unusedVariables false

namespace Work.A3

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators

noncomputable section

/-- **The witness of a transition arc lies in the index range `[-1, q+1]`, and the pointwise
transition bound applies to it.**

Let `0 ≤ γ ≤ 1` and let `htrans` be the pointwise estimate of the transition range
(`Work.A3.transitionArc_bound`).  Then for every `θ` in a transition arc with `θ ∈ [0,1]`
there are `q ∈ ℕ`, `a ∈ ℤ` with

* `1 ≤ q` and `q ≤ ⌊N^γ⌋` (so that `(q,a)` is an index of the finite double sum used by
  `Work.A3.expSum_arcCover_setIntegral_le`),
* `-1 ≤ a ≤ q + 1` (the number of such `a` is `q + 3`),
* `‖expSum Q N θ‖ ≤ C q^{-δ} mArcKernel N d (θ - a/q)`.

The point is that the *given* witness may be used: the transition arcs have radius
`1/(q N^{d/2}) ≤ 1/q`, and `θ ∈ [0,1]` then forces `a/q ∈ [-1/q, 1+1/q]`; and the transition
hypothesis of `htrans` is one of the defining properties of `transitionArcSet`. -/
lemma transitionArc_witness_cover (Q : Polynomial ℤ) {γ δ C : ℝ} (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (htrans : ∀ (N : ℕ) (a q : ℤ) (β : ℝ), 1 ≤ N → 1 ≤ q → IsCoprime a (q : ℤ) →
      (q : ℝ) ≤ (N : ℝ) →
      |β| * (N : ℝ) ^ Polynomial.natDegree Q
        ≤ ((N : ℝ) / (q : ℝ)) ^ ((Polynomial.natDegree Q : ℝ) / (Polynomial.natDegree Q + 1)) / 100 →
      ‖Work.A3.expSum Q N ((a : ℝ) / (q : ℝ) + β)‖
        ≤ C * (q : ℝ) ^ (-δ) * Work.A3.mArcKernel N (Polynomial.natDegree Q) β) :
    ∀ (N : ℕ), 1 ≤ N → ∀ θ ∈ Work.A3.transitionArcSet Q N γ ∩ Set.Icc (0 : ℝ) 1,
      ∃ q : ℕ, ∃ a : ℤ, 1 ≤ q ∧ q ≤ Nat.floor ((N : ℝ) ^ γ) ∧
        a ∈ Finset.Icc (-1) ((q : ℤ) + 1) ∧
        ‖Work.A3.expSum Q N θ‖ ≤ C * (q : ℝ) ^ (-δ) *
          Work.A3.mArcKernel N (Polynomial.natDegree Q) (θ - (a : ℝ) / (q : ℝ)) := by
  intro N hN θ hθ
  obtain ⟨hθA, hθIcc⟩ := hθ
  obtain ⟨q, a, hq1, hcop, hqγ, harc, htrβ⟩ := hθA
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hqpos : (0 : ℝ) < (q : ℝ) := lt_of_lt_of_le zero_lt_one hq1R
  -- the denominator is at most `N^γ`, hence `q ≤ ⌊N^γ⌋`
  have hqfloor : q ≤ Nat.floor ((N : ℝ) ^ γ) := Nat.le_floor hqγ
  -- `q ≤ N`, the hypothesis of the pointwise transition bound
  have hqN : (q : ℝ) ≤ (N : ℝ) := by
    calc (q : ℝ) ≤ (N : ℝ) ^ γ := hqγ
      _ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 hγ1
      _ = (N : ℝ) := Real.rpow_one _
  -- the arc radius `1/(q N^{d/2})` is at most `1/q`
  have hdeg : (0 : ℝ) ≤ (Q.natDegree : ℝ) / 2 := by positivity
  have hNpow : (1 : ℝ) ≤ (N : ℝ) ^ ((Q.natDegree : ℝ) / 2) := by
    calc (1 : ℝ) = (1 : ℝ) ^ ((Q.natDegree : ℝ) / 2) := (Real.one_rpow _).symm
      _ ≤ (N : ℝ) ^ ((Q.natDegree : ℝ) / 2) := Real.rpow_le_rpow zero_le_one hN1 hdeg
  have hrle : 1 / ((q : ℝ) * (N : ℝ) ^ ((Q.natDegree : ℝ) / 2)) ≤ 1 / (q : ℝ) := by
    refine one_div_le_one_div_of_le hqpos ?_
    calc (q : ℝ) = (q : ℝ) * 1 := (mul_one _).symm
      _ ≤ (q : ℝ) * (N : ℝ) ^ ((Q.natDegree : ℝ) / 2) :=
          mul_le_mul_of_nonneg_left hNpow hqpos.le
  have harc' : |θ - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) := harc.trans hrle
  -- the numerator lies in `[-1, q+1]`
  have ha_ge : (-1 : ℤ) ≤ a := by
    have hlt := (abs_le.mp harc').2
    have h1 : -((1 : ℝ) / (q : ℝ)) ≤ (a : ℝ) / (q : ℝ) := by
      linarith [hlt, hθIcc.1]
    have h2 : -((1 : ℝ) / (q : ℝ)) * (q : ℝ) ≤ (a : ℝ) := (le_div_iff₀ hqpos).mp h1
    have h3 : -((1 : ℝ) / (q : ℝ)) * (q : ℝ) = -1 := by field_simp
    rw [h3] at h2
    exact_mod_cast h2
  have ha_le : a ≤ (q : ℤ) + 1 := by
    have hlt := (abs_le.mp harc').1
    have h1 : (a : ℝ) / (q : ℝ) ≤ 1 + 1 / (q : ℝ) := by
      linarith [hlt, hθIcc.2]
    have h2 : (a : ℝ) ≤ (1 + 1 / (q : ℝ)) * (q : ℝ) := (div_le_iff₀ hqpos).mp h1
    have h3 : (1 + 1 / (q : ℝ)) * (q : ℝ) = (q : ℝ) + 1 := by field_simp
    rw [h3] at h2
    have hcast : (((q : ℤ) + 1 : ℤ) : ℝ) = (q : ℝ) + 1 := by push_cast; ring
    rw [← hcast] at h2
    exact_mod_cast h2
  -- the pointwise transition bound at the witness
  have hcore := htrans N a (q : ℤ) (θ - (a : ℝ) / (q : ℝ)) hN (by exact_mod_cast hq1) hcop hqN htrβ
  have hcore' : ‖Work.A3.expSum Q N θ‖ ≤ C * (q : ℝ) ^ (-δ) *
      Work.A3.mArcKernel N (Polynomial.natDegree Q) (θ - (a : ℝ) / (q : ℝ)) := by
    have h1 : ((q : ℤ) : ℝ) = (q : ℝ) := by push_cast; ring
    rw [h1] at hcore
    rw [show (a : ℝ) / (q : ℝ) + (θ - (a : ℝ) / (q : ℝ)) = θ by ring] at hcore
    exact hcore
  exact ⟨q, a, hq1, hqfloor, Finset.mem_Icc.mpr ⟨ha_ge, ha_le⟩, hcore'⟩

theorem transitionArc_energy_contribution (Q : Polynomial ℤ) (hd : 2 ≤ Polynomial.natDegree Q)
    {γ δ : ℝ} (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (hδ : 0 < δ) {C : ℝ} (hC : 0 < C) {s : ℕ} (hs : 1 ≤ s)
    (hδs : 1 < (s : ℝ) * δ) (hds : Polynomial.natDegree Q < 2 * s)
    (htrans : ∀ (N : ℕ) (a q : ℤ) (β : ℝ), 1 ≤ N → 1 ≤ q → IsCoprime a (q : ℤ) →
      (q : ℝ) ≤ (N : ℝ) →
      |β| * (N : ℝ) ^ Polynomial.natDegree Q
        ≤ ((N : ℝ) / (q : ℝ)) ^ ((Polynomial.natDegree Q : ℝ) / (Polynomial.natDegree Q + 1)) / 100 →
      ‖Work.A3.expSum Q N ((a : ℝ) / (q : ℝ) + β)‖
        ≤ C * (q : ℝ) ^ (-δ) * Work.A3.mArcKernel N (Polynomial.natDegree Q) β) :
    ∃ C' > 0, ∀ N : ℕ, 1 ≤ N →
      ∫ θ in Work.A3.transitionArcSet Q N γ ∩ Set.Icc (0 : ℝ) 1,
          ‖Work.A3.expSum Q N θ‖ ^ (2 * s)
        ≤ C' ^ (2 * s) * (N : ℝ) ^ (2 * s - Polynomial.natDegree Q) := by
  obtain ⟨C', hC'pos, hC'⟩ := expSum_arcCover_setIntegral_le Q hd hC hδ hs hδs hds
  refine ⟨C', hC'pos, fun N hN => ?_⟩
  refine hC' N (Nat.floor ((N : ℝ) ^ γ)) (Work.A3.transitionArcSet Q N γ) hN
    (measurableSet_transitionArcSet Q N γ) (fun θ hθ => ?_)
  exact transitionArc_witness_cover Q hγ hγ1 htrans N hN θ hθ

end

end Work.A3
