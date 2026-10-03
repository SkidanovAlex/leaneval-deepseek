import Mathlib
import Submission.Work.KMTAreas.A7Hi.variationalNorm_tsum_le
import Submission.Work.KMTAreas.A7.LoMixedAux
import Submission.Port.Aesm

/-!
# The `ℓ¹` slice-kernel bound for the variational norm

Let `c : ℤ → ℤ → ℂ` be an `ℓ¹` kernel, and let `h k : ℕ → ℤ → ℂ` be two families of sequences
whose `r`-variational norms (in the first variable) are finite at every point.  The bilinear
"slice kernel" operator

  `(h, k) ↦ (x ↦ n ↦ ∑'_i ∑'_j c i j * h n (x - i) * k n (x - j))`

satisfies the `ℓ¹(ℤ) = ℓ¹ × ℓ² → ℓ¹` inequality

  `‖V^r(∑_{i,j} c_{ij} h(x-i) k(x-j))‖_{ℓ¹(ℤ)}
      ≤ 2 ‖c‖_{ℓ¹(ℤ²)} ‖V^r h‖_{ℓ²(ℤ)} ‖V^r k‖_{ℓ²(ℤ)}.`

The proof has three steps.

* **Pointwise bound.**  The `r`-variational norm is subadditive over countable linear
  combinations (`Work.KMTAreas.A7Hi.variationalNorm_tsum_le`) and submultiplicative for the
  pointwise product with constant `1` (`Work.KMTAreas.A7.variationalNorm_mul_le_one`); applying
  the first twice (once in `i`, once in `j`) gives, for every `x`,
  `V^r(∑_{i,j} c_{ij} h(x-i) k(x-j)) ≤ ∑_{i,j} ‖c_{ij}‖ (V^r h)(x-i) (V^r k)(x-j)`.
  (The constant `2` of the statement is then absorbed by `1 ≤ 2`.)
* **Cauchy–Schwarz.**  For a fixed lattice point the `ℓ¹`-norm of `x ↦ H(x-i) K(x-j)` is at
  most `‖H‖_{ℓ²} ‖K‖_{ℓ²}` (Hölder with `p = q = 2`, plus translation invariance of the counting
  measure).
* **Summation.**  Minkowski for countable sums of `ℝ≥0∞`-valued functions
  (`Submission.PointwiseErgodicTheorems.eLpNorm_tsum_le_tsum_eLpNorm`) turns the `ℓ¹`-norm of the
  `(i,j)`-sum in the pointwise bound into the sum of the `ℓ¹`-norms of the summands.
-/

open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Work.Analysis.Variational

noncomputable section

/-! ## 1. Translation invariance of the `L²`-norm for the counting measure on `ℤ` -/

/-- The counting measure on `ℤ` is invariant under translations, hence the `L²`-seminorm of a
function of `x` is unchanged under `x ↦ x + c`. -/
lemma eLpNorm_two_comp_add (F : ℤ → ℝ≥0∞) (c : ℤ) :
    eLpNorm (fun x : ℤ => F (x + c)) 2 Measure.count
      = eLpNorm F 2 Measure.count := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) (p := 2) (by norm_num) (by norm_num),
     MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) (p := 2) (by norm_num) (by norm_num)]
  congr 1
  exact MeasureTheory.lintegral_add_right_eq_self (μ := Measure.count)
    (f := fun y : ℤ => ‖F y‖ₑ ^ ((2 : ENNReal).toReal)) c

/-- The `L²`-seminorm for the counting measure on `ℤ` is invariant under `x ↦ x - i`. -/
lemma eLpNorm_two_comp_sub (F : ℤ → ℝ≥0∞) (i : ℤ) :
    eLpNorm (fun x : ℤ => F (x - i)) 2 Measure.count
      = eLpNorm F 2 Measure.count := by
  have h := eLpNorm_two_comp_add F (-i)
  simpa only [sub_eq_add_neg] using h

/-! ## 2. Hölder / Cauchy–Schwarz for the counting measure -/

/-- The `L²`-seminorm of an `ℝ≥0∞`-valued function is the square root of the integral of its
square. -/
lemma eLpNorm_two_eq_lintegral (F : ℤ → ℝ≥0∞) :
    eLpNorm F 2 Measure.count
      = (∫⁻ x : ℤ, F x ^ (2 : ℝ) ∂Measure.count) ^ ((1 : ℝ) / 2) := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) (p := 2) (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, enorm_eq_self]

/-- Hölder's inequality with `p = q = 2` for the counting measure on `ℤ`, in the `L¹`- vs
`L²`-form used in the Cauchy–Schwarz step. -/
lemma eLpNorm_mul_le_two (F G : ℤ → ℝ≥0∞) :
    eLpNorm (fun x : ℤ => F x * G x) 1 Measure.count
      ≤ eLpNorm F 2 Measure.count * eLpNorm G 2 Measure.count := by
  have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ := Measure.count) (p := 2) (q := 2)
    Real.HolderConjugate.two_two (measurable_of_countable F).aemeasurable
    (measurable_of_countable G).aemeasurable
  simp only [Pi.mul_apply] at hCS
  rw [eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm), eLpNorm_two_eq_lintegral F, eLpNorm_two_eq_lintegral G]
  exact (le_of_eq (lintegral_congr fun x => by simp)).trans hCS

/-! ## 3. The pointwise variational bound -/

/-- **Pointwise slice-kernel bound.**  For every `x`, the `r`-variational norm of the sequence
`n ↦ ∑'_i ∑'_j c i j * h n (x - i) * k n (x - j)` is bounded by the `‖c‖`-weighted sum of the
products of the pointwise variational norms of `h` and `k`. -/
lemma variationalNorm_bilinear_slice_le {r : NNReal} (hr : 1 ≤ r)
    (c : ℤ → ℤ → ℂ) (h k : ℕ → ℤ → ℂ) (x : ℤ) :
    PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => ∑' i : ℤ, ∑' j : ℤ, c i j * h n (x - i) * k n (x - j))
      ≤ ∑' p : ℤ × ℤ, ‖c p.1 p.2‖ₑ *
          (PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => h n (x - p.1)) *
           PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => k n (x - p.2))) := by
  set G : ℤ → ℕ → ℂ := fun i n => ∑' j : ℤ, c i j * (h n (x - i) * k n (x - j)) with hG
  have hinner : ∀ i : ℤ,
      PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => G i n)
        ≤ ∑' j : ℤ, ‖c i j‖ₑ *
            (PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => h n (x - i)) *
             PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => k n (x - j))) := by
    intro i
    refine (Work.KMTAreas.A7Hi.variationalNorm_tsum_le r hr (fun j : ℤ => c i j)
      (fun j n => h n (x - i) * k n (x - j))).trans ?_
    refine ENNReal.tsum_le_tsum fun j => ?_
    refine mul_le_mul' le_rfl ?_
    exact Work.KMTAreas.A7.variationalNorm_mul_le_one r hr (fun n : ℕ => h n (x - i))
      (fun n : ℕ => k n (x - j))
  have houter : PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => ∑' i : ℤ, G i n)
      ≤ ∑' i : ℤ, PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => G i n) := by
    have h := Work.KMTAreas.A7Hi.variationalNorm_tsum_le r hr (fun _ : ℤ => (1 : ℂ)) G
    simpa only [enorm_one, one_mul] using h
  have hgoal : (fun n : ℕ => ∑' i : ℤ, ∑' j : ℤ, c i j * h n (x - i) * k n (x - j))
      = (fun n : ℕ => ∑' i : ℤ, G i n) := by
    funext n
    exact tsum_congr fun i => tsum_congr fun j => by rw [mul_assoc]
  calc PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => ∑' i : ℤ, ∑' j : ℤ, c i j * h n (x - i) * k n (x - j))
      = PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => ∑' i : ℤ, G i n) := by
        rw [hgoal]
    _ ≤ ∑' i : ℤ, PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => G i n) := houter
    _ ≤ ∑' i : ℤ, ∑' j : ℤ, ‖c i j‖ₑ *
          (PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => h n (x - i)) *
           PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => k n (x - j))) :=
        ENNReal.tsum_le_tsum hinner
    _ = ∑' p : ℤ × ℤ, ‖c p.1 p.2‖ₑ *
          (PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => h n (x - p.1)) *
           PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => k n (x - p.2))) :=
        (ENNReal.tsum_prod (f := fun a b => ‖c a b‖ₑ *
          (PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => h n (x - a)) *
           PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => k n (x - b))))).symm

/-! ## 4. The `ℓ¹` bound for the slice kernel -/

/-- **The `ℓ¹` slice-kernel bound.**  For a nonnegative kernel `a` on `ℤ × ℤ` and nonnegative
functions `F, G` on `ℤ`,

  `‖x ↦ ∑'_p a p · F(x - p₁) · G(x - p₂)‖_{ℓ¹(ℤ)}
      ≤ ‖a‖_{ℓ¹(ℤ²)} · ‖F‖_{ℓ²(ℤ)} · ‖G‖_{ℓ²(ℤ)}`.

The `ℓ¹`-norm of the sum is first bounded by the sum of the `ℓ¹`-norms of the summands
(Minkowski for countable sums), each summand is `a p` times the `ℓ¹`-norm of
`x ↦ F(x - p₁) G(x - p₂)` which is bounded by `‖F‖₂ ‖G‖₂` (Hölder plus translation
invariance), and the resulting series is `‖a‖₁ ‖F‖₂ ‖G‖₂`. -/
lemma eLpNorm_slice_kernel_le (a : ℤ × ℤ → ℝ≥0∞) (F G : ℤ → ℝ≥0∞) :
    eLpNorm (fun x : ℤ => ∑' p : ℤ × ℤ, a p * (F (x - p.1) * G (x - p.2)))
        1 Measure.count
      ≤ (∑' p : ℤ × ℤ, a p) * eLpNorm F 2 Measure.count * eLpNorm G 2 Measure.count := by
  have hsingle : ∀ p : ℤ × ℤ,
      eLpNorm (fun x : ℤ => a p * (F (x - p.1) * G (x - p.2))) 1 Measure.count
        = a p * eLpNorm (fun x : ℤ => F (x - p.1) * G (x - p.2)) 1 Measure.count := by
    intro p
    rw [eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm), eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm)]
    rw [show (∫⁻ x : ℤ, ‖a p * (F (x - p.1) * G (x - p.2))‖ₑ ∂Measure.count)
          = ∫⁻ x : ℤ, a p * ‖F (x - p.1) * G (x - p.2)‖ₑ ∂Measure.count from
        lintegral_congr fun x => by simp]
    rw [lintegral_const_mul]
    exact measurable_of_countable _
  calc eLpNorm (fun x : ℤ => ∑' p : ℤ × ℤ, a p * (F (x - p.1) * G (x - p.2)))
        1 Measure.count
      ≤ ∑' p : ℤ × ℤ,
          eLpNorm (fun x : ℤ => a p * (F (x - p.1) * G (x - p.2))) 1 Measure.count :=
        Submission.PointwiseErgodicTheorems.eLpNorm_tsum_le_tsum_eLpNorm (p := 1) le_rfl
          (f := fun p : ℤ × ℤ => fun x : ℤ => a p * (F (x - p.1) * G (x - p.2)))
          (fun p => (measurable_of_countable _).aemeasurable)
    _ = ∑' p : ℤ × ℤ,
          a p * eLpNorm (fun x : ℤ => F (x - p.1) * G (x - p.2)) 1 Measure.count :=
        tsum_congr hsingle
    _ ≤ ∑' p : ℤ × ℤ, a p * (eLpNorm F 2 Measure.count * eLpNorm G 2 Measure.count) := by
        refine ENNReal.tsum_le_tsum fun p => mul_le_mul' le_rfl ?_
        refine (eLpNorm_mul_le_two (fun x : ℤ => F (x - p.1))
          (fun x : ℤ => G (x - p.2))).trans ?_
        rw [eLpNorm_two_comp_sub F p.1, eLpNorm_two_comp_sub G p.2]
    _ = (∑' p : ℤ × ℤ, a p) * (eLpNorm F 2 Measure.count * eLpNorm G 2 Measure.count) :=
        ENNReal.tsum_mul_right
    _ = (∑' p : ℤ × ℤ, a p) * eLpNorm F 2 Measure.count * eLpNorm G 2 Measure.count := by
        rw [mul_assoc]

/-! ## 5. The theorem -/

theorem SliceKernelL1 (r : NNReal) (hr : 1 ≤ r)
    (c : ℤ → ℤ → ℂ) (hc : Summable fun p : ℤ × ℤ => ‖c p.1 p.2‖)
    (h k : ℕ → ℤ → ℂ)
    (hh : ∀ y : ℤ, PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => h n y) < ⊤)
    (hk : ∀ y : ℤ, PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => k n y) < ⊤) :
    MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => ∑' i : ℤ, ∑' j : ℤ, c i j * h n (x - i) * k n (x - j)))
      1 MeasureTheory.Measure.count
      ≤ 2 * (∑' p : ℤ × ℤ, ‖c p.1 p.2‖ₑ) *
          MeasureTheory.eLpNorm (fun y : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => h n y)) 2 MeasureTheory.Measure.count *
          MeasureTheory.eLpNorm (fun y : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => k n y)) 2 MeasureTheory.Measure.count := by
  set H : ℤ → ℝ≥0∞ := fun y => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => h n y)
    with hH
  set K : ℤ → ℝ≥0∞ := fun y => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => k n y)
    with hK
  have hpt : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => ∑' i : ℤ, ∑' j : ℤ, c i j * h n (x - i) * k n (x - j))
      ≤ ∑' p : ℤ × ℤ, ‖c p.1 p.2‖ₑ * (H (x - p.1) * K (x - p.2)) :=
    fun x => variationalNorm_bilinear_slice_le hr c h k x
  have h1 : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => ∑' i : ℤ, ∑' j : ℤ, c i j * h n (x - i) * k n (x - j)))
      1 MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ => ∑' p : ℤ × ℤ,
            ‖c p.1 p.2‖ₑ * (H (x - p.1) * K (x - p.2))) 1 MeasureTheory.Measure.count :=
    MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) fun x => by simpa only [enorm_eq_self] using hpt x
  have h2 : MeasureTheory.eLpNorm (fun x : ℤ => ∑' p : ℤ × ℤ,
          ‖c p.1 p.2‖ₑ * (H (x - p.1) * K (x - p.2))) 1 MeasureTheory.Measure.count
      ≤ (∑' p : ℤ × ℤ, ‖c p.1 p.2‖ₑ) * MeasureTheory.eLpNorm H 2 MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm K 2 MeasureTheory.Measure.count :=
    eLpNorm_slice_kernel_le (fun p : ℤ × ℤ => ‖c p.1 p.2‖ₑ) H K
  have h3 : (∑' p : ℤ × ℤ, ‖c p.1 p.2‖ₑ) * MeasureTheory.eLpNorm H 2 MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm K 2 MeasureTheory.Measure.count
      ≤ 2 * (∑' p : ℤ × ℤ, ‖c p.1 p.2‖ₑ)
          * MeasureTheory.eLpNorm H 2 MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm K 2 MeasureTheory.Measure.count := by
    have hS : (∑' p : ℤ × ℤ, ‖c p.1 p.2‖ₑ) ≤ 2 * (∑' p : ℤ × ℤ, ‖c p.1 p.2‖ₑ) := by
      simpa using mul_le_mul' (show (1 : ℝ≥0∞) ≤ 2 by norm_num)
        (le_refl (∑' p : ℤ × ℤ, ‖c p.1 p.2‖ₑ))
    exact mul_le_mul' (mul_le_mul' hS le_rfl) le_rfl
  exact (h1.trans h2).trans (by simpa only [hH, hK] using h3)

end

end Work.Analysis.Variational
