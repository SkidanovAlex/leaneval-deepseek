/-
# The variational norm of a general family, in `Lᵖ`

`Work.KMTAreas.A7.VarNormTsumLp` is the `ℓ¹`-of-`Lᵖ` bound for the variational norm of an
arbitrary family `u : ℕ → ℤ → ℂ`:

  `‖V^r(u)‖_{Lᵖ(ℤ)} ≤ ∑' n, 4 ‖u n‖_{Lᵖ(ℤ)}   (1 ≤ r, 1 ≤ p)`.

The pointwise input is the spike decomposition already available in the workspace as
`variationalNorm_le_sum_enorm` (for finitely supported families): writing `u n x` as the
pointwise sum over `k` of the spikes `k ↦ (if n = k then u k x else 0)`, subadditivity of the
variational norm over a countable pointwise sum (`variationalNorm_tsum_le`) bounds the
variational norm of the whole family by the sum of the variational norms of the spikes, and
each spike contributes at most `4 ‖u k x‖ₑ` (`variationalNorm_spike_le`).

The passage to `Lᵖ` is Minkowski's inequality for countable sums of `ℝ≥0∞`-valued functions,
`eLpNorm_tsum_le_tsum_eLpNorm` (`Submission/LpMinkowski.lean`).
-/
import Mathlib
import Submission.Work.Analysis.EndVar.Sums
import Submission.Port.Aesm

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped ENNReal NNReal BigOperators

/-- The extended norm of the complex number `4`. -/
private lemma enorm_four : ‖(4 : ℂ)‖ₑ = (4 : ℝ≥0∞) := by
  rw [enorm_eq_nnnorm, Complex.nnnorm_ofNat, ENNReal.coe_ofNat]

/-- Pointwise form of the `ℓ¹`-of-`sup` bound for the variational norm: for every sequence
`a : ℕ → ℂ`, `V^r(a) ≤ ∑'_k 4 ‖a k‖ₑ` (`r ≥ 1`).

Indeed `a` is the pointwise sum of its columns, each column being the single spike
`k ↦ (if n = k then a k else 0)`, whose variational norm is at most `4 ‖a k‖ₑ`; the
variational norm is subadditive over such a countable pointwise sum. -/
private lemma variationalNorm_le_tsum_enorm {r : ℝ≥0} (hr : 1 ≤ r) (a : ℕ → ℂ) :
    PointwiseErgodicTheorems.variationalNorm r a ≤ ∑' k : ℕ, 4 * ‖a k‖ₑ := by
  classical
  set b : ℕ → ℕ → ℂ := fun k n => if n = k then a k else 0 with hb
  have hb0 : ∀ n, ∃ K, ∀ k ≥ K, b k n = 0 := fun n =>
    ⟨n + 1, fun k hk => by simp only [hb]; exact if_neg (by omega)⟩
  have hsum : (fun n => ∑' k, b k n) = a := by
    funext n
    rw [tsum_eq_single (b := n) (fun k hk => by simp only [hb]; exact if_neg (Ne.symm hk))]
    simp only [hb, if_pos rfl]
  calc PointwiseErgodicTheorems.variationalNorm r a
      = PointwiseErgodicTheorems.variationalNorm r (fun n => ∑' k, b k n) := by rw [hsum]
    _ ≤ ∑' k, PointwiseErgodicTheorems.variationalNorm r (fun n => b k n) :=
        Submission.PointwiseErgodicTheorems.variationalNorm_tsum_le hr hb0
    _ ≤ ∑' k, 4 * ‖a k‖ₑ := ENNReal.tsum_le_tsum fun k =>
        (by simpa only [hb] using
          Submission.PointwiseErgodicTheorems.variationalNorm_spike_le hr k (a k))

/-- **The `Lᵖ` bound for the variational norm of an arbitrary family.**  For `1 ≤ r` and `1 ≤ p`,
`‖V^r(u)‖_{Lᵖ(ℤ)} ≤ ∑'_n 4 ‖u n‖_{Lᵖ(ℤ)}`: the variational norm of a family of functions on `ℤ`
is dominated, in `Lᵖ` over the counting measure, by the `ℓ¹`-sum of the `Lᵖ` norms of its
members. -/
theorem VarNormTsumLp {r : NNReal} (hr : 1 ≤ r) {p : ENNReal} (hp : 1 ≤ p) (u : ℕ → ℤ → ℂ) :
    MeasureTheory.eLpNorm (fun x : ℤ =>
        PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u n x))
      p MeasureTheory.Measure.count
    ≤ ∑' n : ℕ, 4 * MeasureTheory.eLpNorm (fun x : ℤ => u n x) p MeasureTheory.Measure.count := by
  -- the pointwise spike decomposition
  have hpt : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u n x)
      ≤ ∑' k : ℕ, 4 * ‖u k x‖ₑ := fun x => variationalNorm_le_tsum_enorm hr (fun k => u k x)
  -- Minkowski for the countable sum
  have hmink := Submission.PointwiseErgodicTheorems.eLpNorm_tsum_le_tsum_eLpNorm
    (μ := Measure.count) (p := p) hp (f := fun k : ℕ => fun x : ℤ => 4 * ‖u k x‖ₑ)
    (fun k => (measurable_of_countable (fun x : ℤ => 4 * ‖u k x‖ₑ)).aemeasurable)
  -- the norm of a single term
  have hterm : ∀ k : ℕ,
      eLpNorm (fun x : ℤ => 4 * ‖u k x‖ₑ) p Measure.count
        = 4 * eLpNorm (fun x : ℤ => u k x) p Measure.count := by
    intro k
    calc eLpNorm (fun x : ℤ => 4 * ‖u k x‖ₑ) p Measure.count
        = eLpNorm (fun x : ℤ => ‖(4 : ℂ) * u k x‖ₑ) p Measure.count := by
          rw [show (fun x : ℤ => 4 * ‖u k x‖ₑ) = (fun x : ℤ => ‖(4 : ℂ) * u k x‖ₑ) from
            funext fun x => by rw [enorm_mul, enorm_four]]
      _ = eLpNorm (fun x : ℤ => (4 : ℂ) * u k x) p Measure.count := eLpNorm_enorm (hf := by pw_aesm) _
      _ = ‖(4 : ℂ)‖ₑ * eLpNorm (fun x : ℤ => u k x) p Measure.count :=
          eLpNorm_const_smul (4 : ℂ) (fun x : ℤ => u k x) p Measure.count
      _ = 4 * eLpNorm (fun x : ℤ => u k x) p Measure.count := by rw [enorm_four]
  calc eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u n x))
        p Measure.count
      ≤ eLpNorm (fun x : ℤ => ∑' k : ℕ, 4 * ‖u k x‖ₑ) p Measure.count :=
        eLpNorm_mono_enorm (hf := by pw_aesm) fun x => by simpa only [enorm_eq_self] using hpt x
    _ ≤ ∑' k : ℕ, eLpNorm (fun x : ℤ => 4 * ‖u k x‖ₑ) p Measure.count := hmink
    _ = ∑' k : ℕ, 4 * eLpNorm (fun x : ℤ => u k x) p Measure.count := tsum_congr hterm

end Work.KMTAreas.A7
