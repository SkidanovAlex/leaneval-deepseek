/-
# Theorem 1: transport of the Duffin–Schaeffer theorem to the challenge's `𝒜 ψ`

`Submission/Work/NumberTheory/DuffinSchaeffer/MathlibForm.lean` contains the
Koukoulopoulos–Maynard theorem in Mathlib's circle formulation.  The challenge states it
for the set `𝒜 ψ ⊆ ℝ` of `α ∈ [0,1]` admitting infinitely many *coprime* solutions of
`|α - a/q| ≤ ψ(q)/q`.

The transport is done here in two steps:

* if the radii `ψ(q)/q` do not tend to `0`, then `W ψ = [0,1]` (Gallagher/density, proved
  by the previous run in `Submission.DS`), so the measure is `1`;
* if they do, clip `ψ` to `min (ψ q) (q/2)`, which changes it only off a finite set and
  therefore preserves both `W` and the divergence of the series, and apply the
  (already proved) small-radii transport `Work.DS.volume_W_eq_one_of_radii_le_half`.
-/

import Submission.Work.DS.volume_W_eq_one_of_radii_le_half

open scoped Nat ENNReal NNReal MeasureTheory Topology
open Set Filter MeasureTheory
open MeasureTheory.Measure
open DuffinSchaefferConjecture

namespace Submission.Main

/-- `clip ψ q = min (ψ q) (q/2)`: the function whose radii `ψ(q)/q` are `≤ 1/2`. -/
noncomputable def clip (ψ : ℕ+ → ℝ≥0) : ℕ+ → ℝ≥0 := fun q => min (ψ q) ((q : ℝ≥0) / 2)

lemma clip_le_self (ψ : ℕ+ → ℝ≥0) (q : ℕ+) : clip ψ q ≤ ψ q := min_le_left _ _

/-- `clip ψ` has all radii at most `1/2`. -/
lemma clip_radii_le_half (ψ : ℕ+ → ℝ≥0) (q : ℕ+) : (clip ψ q / (q : NNReal) : NNReal) ≤ 1 / 2 :=
  Submission.DS.clip_le_half ψ q

/-- A bounded initial segment of `ℕ+` is finite. -/
lemma finite_pnat_lt (N : ℕ) : ({q : ℕ+ | (q : ℕ) < N} : Set ℕ+).Finite := by
  have himg : (fun q : ℕ+ => (q : ℕ)) '' {q : ℕ+ | (q : ℕ) < N} ⊆ {n : ℕ | n < N} := by
    rintro n ⟨q, hq, rfl⟩
    exact hq
  have hfin : ((fun q : ℕ+ => (q : ℕ)) '' {q : ℕ+ | (q : ℕ) < N}).Finite :=
    (Set.finite_lt_nat N).subset himg
  refine Set.Finite.of_finite_image hfin ?_
  intro x _ y _ h
  exact PNat.coe_injective h

/-- If the radii tend to `0`, then `clip ψ` agrees with `ψ` on a cofinite set. -/
lemma clip_eventually_eq (ψ : ℕ+ → ℝ≥0)
    (hdec : Tendsto (Submission.DS.radSeq ψ) atTop (nhds (0 : ℝ))) :
    ∀ᶠ q in Filter.cofinite, clip ψ q = ψ q := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hdec (1 / 2 : ℝ) (by norm_num)
  rw [Filter.eventually_cofinite]
  refine (finite_pnat_lt N).subset ?_
  intro q hq
  by_contra hlt
  have hqN : N ≤ (q : ℕ) := not_lt.mp hlt
  have hlt' : |Submission.DS.radSeq ψ (q : ℕ)| < 1 / 2 := by
    simpa [Real.dist_eq] using hN (q : ℕ) hqN
  have hlt2 : Submission.DS.radSeq ψ (q : ℕ) < 1 / 2 := lt_of_le_of_lt (le_abs_self _) hlt'
  rw [Submission.DS.radSeq_eq_coe] at hlt2
  have h1 : ψ q / (q : NNReal) < (1 / 2 : NNReal) := by exact_mod_cast hlt2
  have hqpos : (0 : NNReal) < (q : NNReal) := by exact_mod_cast PNat.pos q
  have hqne : (q : NNReal) ≠ 0 := ne_of_gt hqpos
  have h2 : ψ q / (q : NNReal) * (q : NNReal) < (1 / 2 : NNReal) * (q : NNReal) :=
    mul_lt_mul_of_pos_right h1 hqpos
  rw [div_mul_cancel₀ _ hqne] at h2
  have h3 : ψ q ≤ (q : NNReal) / 2 := by
    have : (1 / 2 : NNReal) * (q : NNReal) = (q : NNReal) / 2 := by ring
    linarith [h2, this.le, this.ge]
  exact hq (min_eq_left h3)

/-- The series divergence is preserved by clipping: the two functions differ only on the
finite set `{q | ψ q > q/2}` (finite in the decaying regime). -/
lemma not_summable_clip (ψ : ℕ+ → ℝ≥0)
    (hdec : Tendsto (Submission.DS.radSeq ψ) atTop (nhds (0 : ℝ)))
    (hdiv : ¬ Summable fun q : ℕ+ => (ψ q * φ q) / q) :
    ¬ Summable fun q : ℕ+ => (clip ψ q * φ q) / q := by
  intro hs
  have hco : (fun q : ℕ+ => (((clip ψ q * φ q) / q : NNReal) : ℝ)) =ᶠ[Filter.cofinite]
      (fun q : ℕ+ => (((ψ q * φ q) / q : NNReal) : ℝ)) :=
    (clip_eventually_eq ψ hdec).mono fun q hq => by simp only [hq]
  have hsR : Summable (fun q : ℕ+ => (((clip ψ q * φ q) / q : NNReal) : ℝ)) :=
    (NNReal.summable_coe (L := SummationFilter.unconditional ℕ+)
      (f := fun q : ℕ+ => (clip ψ q * φ q) / q)).mpr hs
  have hψR : Summable (fun q : ℕ+ => (((ψ q * φ q) / q : NNReal) : ℝ)) :=
    (summable_congr_cofinite hco).mp hsR
  exact hdiv ((NNReal.summable_coe (L := SummationFilter.unconditional ℕ+)
    (f := fun q : ℕ+ => (ψ q * φ q) / q)).mp hψR)

/-- **Theorem 1, measure part**, in the `W`-formulation. -/
theorem volume_W_eq_one_of_divergence (ψ : ℕ+ → ℝ≥0)
    (hdiv : ¬ Summable fun q : ℕ+ => (ψ q * φ q) / q) :
    volume (Submission.DS.W ψ) = 1 := by
  by_cases hdec : Tendsto (Submission.DS.radSeq ψ) atTop (nhds (0 : ℝ))
  · have hclip : volume (Submission.DS.W (clip ψ)) = 1 :=
      Work.DS.volume_W_eq_one_of_radii_le_half (clip ψ) (clip_radii_le_half ψ)
        (not_summable_clip ψ hdec hdiv)
    rwa [Submission.DS.W_of_eventually_eq (clip_eventually_eq ψ hdec)] at hclip
  · exact Submission.DS.volume_W_eq_one_of_not_decay ψ hdec

/-- **Theorem 1, measure part**: divergence of `Σ ψ(q)φ(q)/q` forces `volume (𝒜 ψ) = 1`. -/
theorem volume_A_eq_one_of_divergence (ψ : ℕ+ → ℝ≥0)
    (hdiv : ¬ Summable fun q : ℕ+ => (ψ q * φ q) / q) :
    volume (𝒜 ψ) = 1 := by
  rw [Submission.DS.A_eq_W]
  exact volume_W_eq_one_of_divergence ψ hdiv

end Submission.Main
