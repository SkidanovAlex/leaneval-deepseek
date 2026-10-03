import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Submission.Work.Analysis.EndVar.Varp
import Submission.Work.Analysis.EndVar.Sums

/-!
# The minor arc reduction (B): `improv` and the IW projections

This module supplies the second input of the §5 assembly: the *summable major-arc approximation*

`‖ Ã_{a n}(f,g) − R_{a n}(f,g) ‖_{ℓ^p} ≤ Cerr Λ n ‖f‖_{ℓ^{p₁}} ‖g‖_{ℓ^{p₂}}`,
`∑_{n < K} Cerr Λ n ≤ C Λ`,

for the major-arc part `R = majorArcPartR Pj P d C₀`, with the error weight
`Cerr Λ n = C · ⟨log₂ (Λ ^ n)⟩^{-10}`.

The mathematical content of §5 is split here into two pieces:

* **the analytic input** `MinorArcInput`: the *single-scale* minor arc estimate in the `ℓ^p` form
  needed, for the two minor-arc parts `f − Π₁ f` and `g − Π₂ g` obtained by subtracting the
  Ionescu--Wainger projections.  This is where `improv`, the projection properties `iw-prop`(i)
  and the interpolation `Work.Analysis.Interpolation` enter;
* **the elementary reduction** `majorArcApproximation_of_minorArc` (proved): bilinearity of `Ã_N`
  plus the summability of the weights `⟨log₂ (Λ^n)⟩^{-10}` (`sum_heightWeight_le_weightSumBound`,
  `Sums.lean`) turn `MinorArcInput` into `MajorArcApproximation`.

The route from `improv` to `MinorArcInput` (the named target `ImprovToApprox`) is:

1. bilinearity gives `Ã_N(f,g) − Ã_N(Π₁ f, Π₂ g) = Ã_N(f − Π₁ f, g) + Ã_N(Π₁ f, g − Π₂ g)`;
2. `improv` applied to `f − Π₁ f` uses `iw-prop`(ii): the Fourier transform of
   `f − Π_{≤l_{(N)}, ≤-Log N+l_{(N)}} f` vanishes on `M_{≤l_{(N)}, ≤-Log N+l_{(N)}-1}`, which is
   contained in the major arcs of Theorem `improv`; the `ℓ^p`-boundedness `iw-prop`(i) turns the
   `ℓ²` norm of `Π₁ f` back into that of `f`;
3. `l_{(N)} = C₀ LogLog N` converts the exponential gain `2^{-c l_{(N)}}` into
   `(Log N)^{-cC₀}`, so that for `C₀, C₁` large the weight is `≤ (Log N)^{-10}`;
4. Stein's multilinear interpolation (`Work.Analysis.Interpolation`) upgrades the `(2,2,1)`
   endpoint to the `(p₁,p₂,p)` exponents of Theorem 1.17, at the cost of the factor
   `⟨LogLog N⟩^{O(1)}` absorbed by taking `C₀` large (see `HANDOFF.md`).
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

/-! ## Bilinearity of the halved average -/

lemma AhalfR_add_left (N : ℝ≥0) (P₁ P₂ : ℤ[X]) (f₁ f₂ g : ℤ → ℂ) :
    AhalfR TZ N P₁ P₂ (f₁ + f₂) g = AhalfR TZ N P₁ P₂ f₁ g + AhalfR TZ N P₁ P₂ f₂ g := by
  funext x
  simp only [AhalfR, Ahalf, Ablock, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]

lemma AhalfR_add_right (N : ℝ≥0) (P₁ P₂ : ℤ[X]) (f g₁ g₂ : ℤ → ℂ) :
    AhalfR TZ N P₁ P₂ f (g₁ + g₂) = AhalfR TZ N P₁ P₂ f g₁ + AhalfR TZ N P₁ P₂ f g₂ := by
  funext x
  simp only [AhalfR, Ahalf, Ablock, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma AhalfR_sub_left (N : ℝ≥0) (P₁ P₂ : ℤ[X]) (f₁ f₂ g : ℤ → ℂ) :
    AhalfR TZ N P₁ P₂ (f₁ - f₂) g = AhalfR TZ N P₁ P₂ f₁ g - AhalfR TZ N P₁ P₂ f₂ g := by
  funext x
  simp only [AhalfR, Ahalf, Ablock, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, mul_sub]

lemma AhalfR_sub_right (N : ℝ≥0) (P₁ P₂ : ℤ[X]) (f g₁ g₂ : ℤ → ℂ) :
    AhalfR TZ N P₁ P₂ f (g₁ - g₂) = AhalfR TZ N P₁ P₂ f g₁ - AhalfR TZ N P₁ P₂ f g₂ := by
  funext x
  simp only [AhalfR, Ahalf, Ablock, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- The two-sided subtraction identity for `Ã`, the form in which the §5 splitting is used. -/
lemma AhalfR_sub₂ (N : ℝ≥0) (P₁ P₂ : ℤ[X]) (f₁ f₂ g₁ g₂ : ℤ → ℂ) :
    AhalfR TZ N P₁ P₂ f₁ g₁ - AhalfR TZ N P₁ P₂ f₂ g₂
      = AhalfR TZ N P₁ P₂ (f₁ - f₂) g₁ + AhalfR TZ N P₁ P₂ f₂ (g₁ - g₂) := by
  rw [AhalfR_sub_left, AhalfR_sub_right]; abel

/-- `Ã` at a natural scale is the real-scale `Ã`, so that the floor of the real scale may be
replaced by the natural scale. -/
lemma AhalfR_coe_nat_floor (N : ℝ≥0) (P₁ P₂ : ℤ[X]) (f g : ℤ → ℂ) :
    AhalfR TZ (Nat.floor N : ℝ≥0) P₁ P₂ f g = AhalfR TZ N P₁ P₂ f g := by
  funext x
  rw [AhalfR_eq, AhalfR_eq, Nat.floor_natCast]

/-! ## The minor arc projections -/

/-- The Ionescu--Wainger projection `Π_{≤ l_{(N)}, ≤ -Log N + l_{(N)}}` applied to `f`. -/
def majorArcProj₁ (Pj : IWProjections) (C₀ N : ℕ) (f : ℤ → ℂ) : ℤ → ℂ :=
  Pj.proj (heightScale C₀ N) (-(logN N) + (heightScale C₀ N : ℤ)) f

/-- The Ionescu--Wainger projection `Π_{≤ l_{(N)}, ≤ -d Log N + d l_{(N)}}` applied to `g`. -/
def majorArcProj₂ (Pj : IWProjections) (d C₀ N : ℕ) (g : ℤ → ℂ) : ℤ → ℂ :=
  Pj.proj (heightScale C₀ N)
    (-((d : ℤ) * logN N) + (d : ℤ) * (heightScale C₀ N : ℤ)) g

/-- The definition of the major arc part in terms of the two projections. -/
lemma majorArcPart_eq_AhalfR (Pj : IWProjections) (P : ℤ[X]) (d C₀ N : ℕ) (f g : ℤ → ℂ) :
    majorArcPart Pj P d C₀ N f g
      = AhalfR TZ N X P (majorArcProj₁ Pj C₀ N f) (majorArcProj₂ Pj d C₀ N g) := rfl

/-- The major-arc part at a real scale, expressed through the `Ã` at the natural scale. -/
lemma majorArcPartR_eq (Pj : IWProjections) (P : ℤ[X]) (d C₀ : ℕ) (N : ℝ≥0) (f g : ℤ → ℂ) :
    majorArcPartR Pj P d C₀ N f g
      = AhalfR TZ N X P (majorArcProj₁ Pj C₀ (Nat.floor N) f)
          (majorArcProj₂ Pj d C₀ (Nat.floor N) g) := by
  rw [majorArcPartR, majorArcPart_eq_AhalfR, AhalfR_coe_nat_floor]

/-! ## The analytic input and the elementary reduction -/

/-- **The single-scale minor arc estimate in the form needed by §5.**  There is a constant `C`
such that for every scale `N ≥ 1` the two minor-arc parts of the halved average are bounded by
`C ⟨log₂ N⟩^{-10}` times the `ℓ^{p₁} ⊗ ℓ^{p₂}` norm of the original `f, g`.

The projection boundedness `iw-prop`(i) is already absorbed into `C`; the estimate for the second
part is stated with `‖f‖_{p₁}‖g‖_{p₂}` on the right (rather than `‖Π₁ f‖`), which is exactly the
form produced by `improv` + interpolation. -/
def MinorArcInput (Pj : IWProjections) (P : ℤ[X]) (d C₀ : ℕ)
    (p₁ p₂ p : ℝ≥0∞) : Prop :=
  ∃ C : ℝ≥0, ∀ (N : ℝ≥0) (f g : ℤ → ℂ), 1 ≤ N →
    (eLpNorm (fun x : ℤ => AhalfR TZ N X P
        (fun m => f m - majorArcProj₁ Pj C₀ (Nat.floor N) f m) g x) p Measure.count
      ≤ (C : ℝ≥0∞) * (heightWeight 10 N : ℝ≥0∞)
          * eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count) ∧
    (eLpNorm (fun x : ℤ => AhalfR TZ N X P (majorArcProj₁ Pj C₀ (Nat.floor N) f)
        (fun m => g m - majorArcProj₂ Pj d C₀ (Nat.floor N) g m) x) p Measure.count
      ≤ (C : ℝ≥0∞) * (heightWeight 10 N : ℝ≥0∞)
          * eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count)

/-- **The elementary half of (B).**  Bilinearity of the halved average and the summability of the
weights `⟨log₂ (Λ^n)⟩^{-10}` turn the single-scale minor arc input `MinorArcInput` into the
major-arc approximation `MajorArcApproximation` for `majorArcPartR`, with
`Cerr Λ n = 2 C ⟨log₂ (Λ^n)⟩^{-10}` and `C Λ = 2 C · weightSumBound Λ`. -/
theorem majorArcApproximation_of_minorArc {Pj : IWProjections} {P : Polynomial ℤ} {d C₀ : ℕ}
    {p₁ p₂ p : ℝ≥0∞} (h1p : 1 ≤ p) (h : MinorArcInput Pj P d C₀ p₁ p₂ p) :
    ∃ (Cerr : ℝ≥0 → ℕ → ℝ≥0) (C : ℝ≥0 → ℝ≥0),
      MajorArcApproximation P (majorArcPartR Pj P d C₀) p₁ p₂ p Cerr C := by
  obtain ⟨C, hC⟩ := h
  refine ⟨fun Λ n => 2 * C * heightWeight 10 (Λ ^ n), fun Λ => 2 * C * powWeightBound Λ, ?_⟩
  intro a Λ f g hΛ ha ha1
  have hpow : ∀ n, Λ ^ n ≤ a n := fun n => pow_le_of_lacunary hΛ ha ha1 n
  refine ⟨?_, ?_⟩
  · intro n
    have hbound := hC (a n) f g (ha1 n)
    have hmajor : majorArcPartR Pj P d C₀ (a n) f g
        = AhalfR TZ (a n) X P (majorArcProj₁ Pj C₀ (Nat.floor (a n)) f)
            (majorArcProj₂ Pj d C₀ (Nat.floor (a n)) g) := by
      rw [majorArcPartR_eq]
    have hsplit : (fun x : ℤ => AhalfR TZ (a n) X P f g x
          - majorArcPartR Pj P d C₀ (a n) f g x)
        = (fun x : ℤ => AhalfR TZ (a n) X P
              (fun m => f m - majorArcProj₁ Pj C₀ (Nat.floor (a n)) f m) g x)
          + (fun x : ℤ => AhalfR TZ (a n) X P (majorArcProj₁ Pj C₀ (Nat.floor (a n)) f)
              (fun m => g m - majorArcProj₂ Pj d C₀ (Nat.floor (a n)) g m) x) := by
      funext x
      rw [hmajor]
      simp only [Pi.add_apply]
      exact congrFun (AhalfR_sub₂ (a n) X P f (majorArcProj₁ Pj C₀ (Nat.floor (a n)) f) g
        (majorArcProj₂ Pj d C₀ (Nat.floor (a n)) g)) x
    have hmeas1 : AEStronglyMeasurable (fun x : ℤ => AhalfR TZ (a n) X P
        (fun m => f m - majorArcProj₁ Pj C₀ (Nat.floor (a n)) f m) g x) Measure.count :=
      (measurable_of_countable _).aestronglyMeasurable
    have hmeas2 : AEStronglyMeasurable (fun x : ℤ => AhalfR TZ (a n) X P
        (majorArcProj₁ Pj C₀ (Nat.floor (a n)) f)
        (fun m => g m - majorArcProj₂ Pj d C₀ (Nat.floor (a n)) g m) x) Measure.count :=
      (measurable_of_countable _).aestronglyMeasurable
    have hw : (heightWeight 10 (a n) : ℝ≥0∞) ≤ (heightWeight 10 (Λ ^ n) : ℝ≥0∞) := by
      exact_mod_cast heightWeight_antitone 10 (by norm_num) (hpow n)
    calc eLpNorm (fun x : ℤ => AhalfR TZ (a n) X P f g x
            - majorArcPartR Pj P d C₀ (a n) f g x) p Measure.count
        = eLpNorm ((fun x : ℤ => AhalfR TZ (a n) X P
              (fun m => f m - majorArcProj₁ Pj C₀ (Nat.floor (a n)) f m) g x)
            + (fun x : ℤ => AhalfR TZ (a n) X P (majorArcProj₁ Pj C₀ (Nat.floor (a n)) f)
              (fun m => g m - majorArcProj₂ Pj d C₀ (Nat.floor (a n)) g m) x))
            p Measure.count := by rw [hsplit]
      _ ≤ eLpNorm (fun x : ℤ => AhalfR TZ (a n) X P
              (fun m => f m - majorArcProj₁ Pj C₀ (Nat.floor (a n)) f m) g x) p Measure.count
            + eLpNorm (fun x : ℤ => AhalfR TZ (a n) X P
              (majorArcProj₁ Pj C₀ (Nat.floor (a n)) f)
              (fun m => g m - majorArcProj₂ Pj d C₀ (Nat.floor (a n)) g m) x)
              p Measure.count := eLpNorm_add_le h1p
      _ ≤ (C : ℝ≥0∞) * (heightWeight 10 (Λ ^ n) : ℝ≥0∞)
              * eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count
            + (C : ℝ≥0∞) * (heightWeight 10 (Λ ^ n) : ℝ≥0∞)
              * eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count := by
          refine add_le_add ?_ ?_
          · exact hbound.1.trans (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hw bot_le) bot_le) bot_le)
          · exact hbound.2.trans (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hw bot_le) bot_le) bot_le)
      _ = ((2 * C * heightWeight 10 (Λ ^ n) : ℝ≥0) : ℝ≥0∞)
              * eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count := by
          push_cast; ring
  · intro K
    calc ∑ n ∈ Finset.range K, (2 * C * heightWeight 10 (Λ ^ n) : ℝ≥0)
        = 2 * C * ∑ n ∈ Finset.range K, heightWeight 10 (Λ ^ n) := by
          rw [Finset.mul_sum]
      _ ≤ 2 * C * powWeightBound Λ :=
          mul_le_mul_of_nonneg_left (sum_heightWeight_pow_le hΛ K) (by positivity)

/-- The error weight of the §5 minor-arc reduction: `Cerr Λ n = C · ⟨log₂ (Λ ^ n)⟩^{-10}`. -/
def approxErrorWeight (C : ℝ≥0) (Λ : ℝ≥0) (n : ℕ) : ℝ≥0 :=
  C * heightWeight 10 (Λ ^ n)

end

end Work.Analysis.EndVar
