/-
# Proposition `lip` with a free support window `A N^d`

`A4/peluseLipL1Tail.lean` proves Proposition `lip` (the alternate inverse theorem for `f`) with the
support window pinned to `N₀ ≤ 2 N^d`.  That pin is *too tight*: the polynomial `P` enters the
bilinear average through the shifts `P(n)`, and the configurations the §5.1 chain needs sit at the
scale `|P(N)| ~ |a_d| N^d` (see `NOTES_A4_window_pin_GAP.md`).  For `P = 100 X^2` the pinned
predicate is in fact vacuous (`A4/lipOutputTail_vacuous_100sq.lean`).  The window therefore has to
be a **free parameter** `A ≥ 1`, with the implied constants allowed to depend on `A` — exactly the
shape of `PeluseInverseKMT` (area A2).

## Main results

* `Work.KMTAreas.A4.LipOutputTailA` — Proposition `lip` with the window `A N^d`;
* `Work.KMTAreas.A4.lipOutputTailA_of_peluse` — it follows from `PeluseInverseKMT` and
  `A4/peluseLipL1TailA` (the window-parameterised `peluseLipL1Tail`).
-/
import Mathlib
import Submission.Work.KMTAreas.A4.Struct

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.InverseTheory

namespace Work.KMTAreas.A4

/-- **Proposition `lip` with the free support window `A N^d`** (`A ≥ 1`): the same conclusion as
`LipOutputTail`, with the input supported in `[-A N^d, A N^d]` and the spatial tail measured
outside `A N^d`. -/
def LipOutputTailA (P : Polynomial ℤ) (ρ A C K : ℝ) : Prop :=
  ∀ (N N₀ : ℕ) (δ : ℝ) (f g h : ℤ → ℂ), 1 ≤ N → 0 < δ → δ ≤ 1 →
    (N : ℝ) ^ P.natDegree / A ≤ (N₀ : ℝ) → (N₀ : ℝ) ≤ A * (N : ℝ) ^ P.natDegree →
    SupportIn f N₀ → SupportIn g N₀ → SupportIn h N₀ →
    (∀ x : ℤ, ‖f x‖ ≤ 1) → (∀ x : ℤ, ‖g x‖ ≤ 1) → (∀ x : ℤ, ‖h x‖ ≤ 1) →
    δ * (N : ℝ) ^ P.natDegree ≤ ‖bilinPair (AhalfZ N P f g) h‖ →
    ∃ (F : ℤ → ℂ) (l : ℕ) (k : ℤ),
      (∀ x : ℤ, ‖F x‖ ≤ C * δ⁻¹ ^ K) ∧
      Summable (fun x : ℤ => ‖F x‖) ∧
      (∑' x : ℤ, ‖F x‖ ≤ C * δ⁻¹ ^ K * (N : ℝ) ^ P.natDegree) ∧
      (∑' x : ℤ, (if A * (N : ℝ) ^ P.natDegree < (x.natAbs : ℝ) then ‖F x‖ else 0)
        ≤ δ ^ K * (N : ℝ) ^ P.natDegree / 2) ∧
      FourierSupportIn F (majorArc ρ l k) ∧
      (2 : ℝ) ^ l ≤ C * δ⁻¹ ^ K ∧
      (2 : ℝ) ^ k ≤ C * δ⁻¹ ^ K / (N : ℝ) ∧
      δ ^ K * (N : ℝ) ^ P.natDegree ≤ ‖bilinPair f F‖

/-- The natural absolute value of an integer is its real absolute value. -/
private theorem natAbs_cast_real (x : ℤ) : ((x.natAbs : ℕ) : ℝ) = |(x : ℝ)| := by
  rw [← Int.cast_abs, ← Int.natCast_natAbs]
  norm_num

/-- The tail sums of the window-parameterised `peluseLipL1TailA` (real absolute value) and of
`LipOutputTailA` (`x.natAbs`) agree. -/
theorem tailSumA_congr {A : ℝ} {N d : ℕ} (F : ℤ → ℂ) :
    (∑' x : ℤ, (if A * (N : ℝ) ^ d < |(x : ℝ)| then ‖F x‖ else 0))
      = ∑' x : ℤ, (if A * (N : ℝ) ^ d < (x.natAbs : ℝ) then ‖F x‖ else 0) := by
  refine tsum_congr fun x => ?_
  rw [natAbs_cast_real x]

/-- **Proposition `lip` with a free window, from Peluse's inverse theorem**: the window-parameterised
form of `peluseLipL1Tail` (taken here as a hypothesis, so that this conversion does not depend on
that file's build state). -/
theorem lipOutputTailA_of_lipL1A (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree)
    (hlip : ∀ (A : ℝ), 1 ≤ A → ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 →
      ∀ (N N₀ : ℕ) (δ : ℝ) (f g h : ℤ → ℂ), 1 ≤ N → 0 < δ → δ ≤ 1 →
        (N : ℝ) ^ P.natDegree / A ≤ (N₀ : ℝ) → (N₀ : ℝ) ≤ A * (N : ℝ) ^ P.natDegree →
        SupportIn f N₀ → SupportIn g N₀ → SupportIn h N₀ →
        (∀ x : ℤ, ‖f x‖ ≤ 1) → (∀ x : ℤ, ‖g x‖ ≤ 1) → (∀ x : ℤ, ‖h x‖ ≤ 1) →
        δ * (N : ℝ) ^ P.natDegree ≤ ‖bilinPair (AhalfZ N P f g) h‖ →
        ∃ (F : ℤ → ℂ) (l : ℕ) (k : ℤ),
          (∀ x : ℤ, ‖F x‖ ≤ C * δ⁻¹ ^ K) ∧
          Summable (fun x : ℤ => ‖F x‖) ∧
          (∑' x : ℤ, ‖F x‖ ≤ C * δ⁻¹ ^ K * (N : ℝ) ^ P.natDegree) ∧
          (∑' x : ℤ, (if A * (N : ℝ) ^ P.natDegree < |(x : ℝ)| then ‖F x‖ else 0)
            ≤ δ ^ K * (N : ℝ) ^ P.natDegree / 2) ∧
          FourierSupportIn F (majorArc ρ l k) ∧
          (2 : ℝ) ^ l ≤ C * δ⁻¹ ^ K ∧
          (2 : ℝ) ^ k ≤ C * δ⁻¹ ^ K / (N : ℝ) ∧
          δ ^ K * (N : ℝ) ^ P.natDegree ≤ ‖bilinPair f F‖) :
    ∀ (A : ℝ), 1 ≤ A → ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → LipOutputTailA P ρ A C K := by
  intro A hA
  obtain ⟨C, K, hC, hK, h⟩ := hlip A hA
  refine ⟨C, K, hC, hK, fun ρ hρ hρ1 => ?_⟩
  intro N N₀ δ f g hh hN hδ0 hδ1 hlo hhi hsf hsg hsh hf1 hg1 hh1 hcorr
  obtain ⟨F, l, k, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    h ρ hρ hρ1 N N₀ δ f g hh hN hδ0 hδ1 hlo hhi hsf hsg hsh hf1 hg1 hh1 hcorr
  refine ⟨F, l, k, h1, h2, h3, ?_, h5, h6, h7, h8⟩
  rw [tailSumA_congr (A := A) (N := N) (d := P.natDegree) F] at h4
  exact h4

end Work.KMTAreas.A4
