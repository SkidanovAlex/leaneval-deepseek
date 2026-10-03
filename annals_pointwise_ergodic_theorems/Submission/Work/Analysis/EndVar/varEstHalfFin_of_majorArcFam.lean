import Mathlib
import Submission.Work.Analysis.EndVar.Statements
import Submission.Port.Aesm

/-!
# The §5 assembly of Krause--Mirek--Tao in family form

This module proves `varEstHalfFin_of_majorArcFam`, the assembly step of §5 of

* B. Krause, M. Mirek, T. Tao, *Pointwise ergodic theorems for non-conventional bilinear
  polynomial averages*, Annals of Math. 195 (3) 2022,

in the form in which the two inputs of the §5 reduction are the two properties
`Work.Analysis.EndVar.MajorArcVarEstimate` (the variational estimate for a family `R` of
major-arc parts) and `Work.Analysis.EndVar.MajorArcApproximation` (the halved averages are
approximated by their major-arc parts with a summable `ℓ^p` error).

The conclusion is the *finite* (clamped) form `VarEstHalfFin TZ count P p₁ p₂ p r` of the
variational estimate, with constant `Cv Λ + 4 C Λ`: the constant `Cv Λ` comes from the
variational estimate for the major-arc parts (via the clamping lemma
`MajorArcVarEstimate.clamped`), and the constant `4 C Λ` from the summable approximation error.

The proof is the formal bookkeeping of §5 and uses three elementary ingredients:

* the pointwise decomposition `V^r(u) ≤ V^r(w) + V^r(u - w)` of the variational norm;
* Minkowski's inequality for `eLpNorm` in the form `eLpNorm_add_le`;
* the clamped-difference estimate `eLpNorm_variationalNorm_comp_min_sub_le` below, which turns
  the pointwise clamped bound `variationalNorm_clamp_sub_le` into an `L^p` bound
  `∑_{n ≤ K} 4 ‖u n - w n‖_{ℓ^p}`.  The clamped family `n ↦ u (min n K)` is constant for
  `n ≥ K`, so the whole variational norm of the difference is carried by the first `K + 1`
  scales, and the final `2‖u K - w K‖ₑ` term of the pointwise bound is absorbed into the
  `∑_{n ≤ K} 4 Cerr Λ n ≤ 4 C Λ` budget (note the index `K` is counted *twice* in the pointwise
  bound, but only once — with a factor `4` — in the sum).
-/

namespace Work.Analysis.EndVar

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal PNat BigOperators
open PointwiseErgodicTheorems
open Submission.PointwiseErgodicTheorems

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-- The extended norm of the complex number `4`. -/
private lemma enorm_four : ‖(4 : ℂ)‖ₑ = (4 : ℝ≥0∞) := by
  rw [enorm_eq_nnnorm, Complex.nnnorm_ofNat, ENNReal.coe_ofNat]

/-- `‖4 z‖ₑ = 4 ‖z‖ₑ` for `z : ℂ`. -/
private lemma enorm_four_smul (z : ℂ) : ‖(4 : ℂ) • z‖ₑ = 4 * ‖z‖ₑ := by
  rw [enorm_smul, enorm_four]

/-- The `L^p` norm of `x ↦ ‖4 d x‖ₑ` is `4` times the `L^p` norm of `d`. -/
private lemma eLpNorm_four_smul (d : ℤ → ℂ) (p : ℝ≥0∞) :
    eLpNorm (fun x : ℤ => ‖(4 : ℂ) • d x‖ₑ) p Measure.count = 4 * eLpNorm d p Measure.count := by
  have h : (fun x : ℤ => ‖(4 : ℂ) • d x‖ₑ) = (fun x : ℤ => ‖((4 : ℂ) • d) x‖ₑ) := by
    funext x; rw [Pi.smul_apply]
  rw [h, eLpNorm_enorm (hf := by pw_aesm), eLpNorm_const_smul, enorm_four]

/-- **The `L^p` form of the clamped-difference bound.**  If `u` and `w` are families which are
constant for `n ≥ K` (with values `u K`, `w K`), then the variational norm of the difference
`n ↦ u n - w n` is carried by the first `K + 1` scales:

`‖V^r(u - w)‖_{ℓ^p} ≤ ∑_{n ≤ K} 4 ‖u n - w n‖_{ℓ^p}`.

This is `Work.Analysis.EndVar.variationalNorm_clamp_sub_le` (which gives the pointwise bound
`∑_{n < K} 4‖u n - w n‖ₑ + 2‖u K - w K‖ₑ`) together with the elementary inequality
`2‖u K - w K‖ₑ ≤ 4‖u K - w K‖ₑ` which lets the last term be charged to the sum at `n = K`. -/
lemma eLpNorm_variationalNorm_comp_min_sub_le {r : ℝ≥0} (hr : 1 ≤ r) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u w : ℕ → ℤ → ℂ} {K : ℕ}
    (hu : ∀ n, K ≤ n → u n = u K) (hw : ∀ n, K ≤ n → w n = w K)
    (hmeas : ∀ n, n ≤ K → AEStronglyMeasurable (fun x : ℤ => u n x - w n x) Measure.count) :
    eLpNorm (fun x : ℤ => variationalNorm r (fun n => u n x - w n x)) p Measure.count
      ≤ ∑ n ∈ Finset.range (K + 1), 4 * eLpNorm (fun x : ℤ => u n x - w n x) p Measure.count := by
  have hpt : ∀ x : ℤ, variationalNorm r (fun n => u n x - w n x)
      ≤ ∑ n ∈ Finset.range (K + 1), ‖(4 : ℂ) • (u n x - w n x)‖ₑ := by
    intro x
    refine (variationalNorm_clamp_sub_le hr (fun n => u n x) (fun n => w n x) K
      (fun n hn => congrFun (hu n hn) x) (fun n hn => congrFun (hw n hn) x)).trans ?_
    rw [Finset.sum_range_succ]
    rw [Finset.sum_congr rfl (fun n _ => (enorm_four_smul (u n x - w n x)).symm)]
    refine add_le_add le_rfl ?_
    rw [enorm_four_smul]
    gcongr
    norm_num
  have hmono : eLpNorm (fun x : ℤ => variationalNorm r (fun n => u n x - w n x)) p Measure.count
      ≤ eLpNorm (fun x : ℤ => ∑ n ∈ Finset.range (K + 1), ‖(4 : ℂ) • (u n x - w n x)‖ₑ)
          p Measure.count :=
    eLpNorm_mono_enorm (hf := by pw_aesm) hpt
  have hsum : eLpNorm (fun x : ℤ => ∑ n ∈ Finset.range (K + 1), ‖(4 : ℂ) • (u n x - w n x)‖ₑ)
        p Measure.count
      ≤ ∑ n ∈ Finset.range (K + 1), 4 * eLpNorm (fun x : ℤ => u n x - w n x) p Measure.count := by
    have hfun : (fun x : ℤ => ∑ n ∈ Finset.range (K + 1), ‖(4 : ℂ) • (u n x - w n x)‖ₑ)
        = ∑ n ∈ Finset.range (K + 1), (fun x : ℤ => ‖(4 : ℂ) • (u n x - w n x)‖ₑ) := by
      funext x; rw [Finset.sum_apply]
    rw [hfun]
    refine (eLpNorm_sum_le hp).trans (le_of_eq ?_)
    · refine Finset.sum_congr rfl (fun n _ => eLpNorm_four_smul _ _)
  exact hmono.trans hsum

/-- **The §5 assembly, in the form of the two inputs (A) and (B).**  A major-arc variational
estimate (A) plus a summable major-arc approximation (B) for a family `R` of major-arc parts
gives the finite variational estimate `VarEstHalfFin` for the halved averages, with constant
`Cv Λ + 4 C Λ`. -/
theorem varEstHalfFin_of_majorArcFam {P : Polynomial ℤ} {p₁ p₂ p : ENNReal} {r : NNReal}
    {Cv : NNReal → NNReal} {Cerr : NNReal → ℕ → NNReal} {C : NNReal → NNReal}
    (R : NNReal → (ℤ → ℂ) → (ℤ → ℂ) → (ℤ → ℂ))
    (hA : Work.Analysis.EndVar.MajorArcVarEstimate R p₁ p₂ p r Cv)
    (hB : Work.Analysis.EndVar.MajorArcApproximation P R p₁ p₂ p Cerr C)
    (h1p : 1 ≤ p) (hr : 1 ≤ r)
    (hmeasR : ∀ (N : NNReal) (f g : ℤ → ℂ), AEMeasurable (R N f g) MeasureTheory.Measure.count) :
    Submission.PointwiseErgodicTheorems.VarEstHalfFin Submission.PointwiseErgodicTheorems.TZ
      MeasureTheory.Measure.count P p₁ p₂ p r (fun Λ => Cv Λ + 4 * C Λ) := by
  intro K f g hf hg a Λ hΛ ha ha1
  rw [MeasureTheory.Lp.enorm_toLp hf, MeasureTheory.Lp.enorm_toLp hg]
  -- The pointwise splitting of the variational norm of the clamped average.
  have hpt : ∀ x : ℤ, variationalNorm r (fun n => AhalfR TZ (a (min n K)) X P f g x)
      ≤ variationalNorm r (fun n => R (a (min n K)) f g x)
        + variationalNorm r (fun n =>
            AhalfR TZ (a (min n K)) X P f g x - R (a (min n K)) f g x) := by
    intro x
    have hdecomp : (fun n => AhalfR TZ (a (min n K)) X P f g x)
        = (fun n => R (a (min n K)) f g x)
          + (fun n => AhalfR TZ (a (min n K)) X P f g x - R (a (min n K)) f g x) := by
      funext n; simp only [Pi.add_apply]; ring
    rw [hdecomp]
    exact variationalNorm_add_le hr _ _
  -- (A) the variational estimate for the major-arc parts, clamped.
  have hmajor : eLpNorm (fun x : ℤ => variationalNorm r (fun n => R (a (min n K)) f g x))
        p Measure.count
      ≤ (Cv Λ : ℝ≥0∞) * eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count :=
    MajorArcVarEstimate.clamped hA a Λ K f g hΛ ha ha1
  -- (B) the clamped difference is carried by the first `K + 1` scales, whose error is summable.
  have hdiff : eLpNorm (fun x : ℤ => variationalNorm r (fun n =>
        AhalfR TZ (a (min n K)) X P f g x - R (a (min n K)) f g x)) p Measure.count
      ≤ 4 * (C Λ : ℝ≥0∞) * eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count := by
    refine (eLpNorm_variationalNorm_comp_min_sub_le hr h1p
      (u := fun n x => AhalfR TZ (a (min n K)) X P f g x)
      (w := fun n x => R (a (min n K)) f g x)
      (hu := fun n hn => by funext x; rw [min_eq_right hn, min_self])
      (hw := fun n hn => by funext x; rw [min_eq_right hn, min_self])
      (hmeas := fun n _ => (measurable_of_countable _).aestronglyMeasurable)).trans ?_
    have hstep : ∀ n ∈ Finset.range (K + 1),
        4 * eLpNorm (fun x : ℤ =>
            AhalfR TZ (a (min n K)) X P f g x - R (a (min n K)) f g x) p Measure.count
        ≤ 4 * ((Cerr Λ n : ℝ≥0∞) * eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count) := by
      intro n hn
      have hn' : n ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      have hh : eLpNorm (fun x : ℤ => AhalfR TZ (a n) X P f g x - R (a n) f g x)
            p Measure.count
          ≤ (Cerr Λ n : ℝ≥0∞) * eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count :=
        (hB a Λ f g hΛ ha ha1).1 n
      rw [min_eq_left hn']
      exact mul_le_mul_right hh 4
    refine (Finset.sum_le_sum hstep).trans ?_
    have h1 : ∑ n ∈ Finset.range (K + 1), 4 * ((Cerr Λ n : ℝ≥0∞) * eLpNorm f p₁ Measure.count
          * eLpNorm g p₂ Measure.count)
        = 4 * eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count
          * ∑ n ∈ Finset.range (K + 1), (Cerr Λ n : ℝ≥0∞) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun n _ => by ring)
    have h2 : ∑ n ∈ Finset.range (K + 1), (Cerr Λ n : ℝ≥0∞) ≤ (C Λ : ℝ≥0∞) := by
      exact_mod_cast (hB a Λ f g hΛ ha ha1).2 (K + 1)
    calc ∑ n ∈ Finset.range (K + 1), 4 * ((Cerr Λ n : ℝ≥0∞) * eLpNorm f p₁ Measure.count
            * eLpNorm g p₂ Measure.count)
        = 4 * eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count
            * ∑ n ∈ Finset.range (K + 1), (Cerr Λ n : ℝ≥0∞) := h1
      _ ≤ 4 * eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count * (C Λ : ℝ≥0∞) := by
          gcongr
      _ = 4 * (C Λ : ℝ≥0∞) * eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count := by ring
  -- Minkowski's inequality combines the two pieces.
  calc eLpNorm (fun x : ℤ => variationalNorm r (fun n => AhalfR TZ (a (min n K)) X P f g x))
        p Measure.count
      ≤ eLpNorm (fun x : ℤ => variationalNorm r (fun n => R (a (min n K)) f g x)
          + variationalNorm r (fun n =>
              AhalfR TZ (a (min n K)) X P f g x - R (a (min n K)) f g x)) p Measure.count :=
        eLpNorm_mono_enorm (hf := by pw_aesm) hpt
    _ ≤ eLpNorm (fun x : ℤ => variationalNorm r (fun n => R (a (min n K)) f g x)) p Measure.count
          + eLpNorm (fun x : ℤ => variationalNorm r (fun n =>
              AhalfR TZ (a (min n K)) X P f g x - R (a (min n K)) f g x)) p Measure.count :=
        eLpNorm_add_le h1p
    _ ≤ (Cv Λ : ℝ≥0∞) * eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count
          + 4 * (C Λ : ℝ≥0∞) * eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count :=
        add_le_add hmajor hdiff
    _ = ((Cv Λ + 4 * C Λ : NNReal) : ℝ≥0∞) * eLpNorm f p₁ Measure.count
          * eLpNorm g p₂ Measure.count := by
        push_cast; ring

end

end Work.Analysis.EndVar
