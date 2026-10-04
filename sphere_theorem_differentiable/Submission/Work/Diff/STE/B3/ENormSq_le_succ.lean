import Mathlib
import Submission.Work.Diff.STE.B3.ENormSq_le_CSq
import Submission.Work.Diff.STE.B3.CSq_le_ENormSq_of_periodization
import Submission.Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `ENormSq_le_succ`: the `Hᵐ` energy of a periodisation is controlled by the `Hᵐ⁺¹` energy

For a smooth function `R` supported in the open unit cube and its periodisation
`P z = ∑' m, R (z + iVec m)`, the physical energy at order `m` is bounded by a constant times the
energy at order `m + 1`.  This is the elementary endpoint of the Sobolev gain in the energy method:
each extra derivative bought by the Poincaré/vanishing-on-the-hyperplane argument is paid for by one
order of differentiability, and since the weight `⟨k⟩ = wt k` is `≥ 1`, the weighted coefficient
mass is monotone in the order.

The proof composes three results already in the workspace:

* `Work.Diff.STE.ENormSq_le_CSq_of_contDiff_periodic m`:
  `ENormSq m P ≤ C₁ · CSq m (fourierCoeff P)`;
* `CSq_le_CSq_succ` (below): `CSq m c ≤ CSq (m+1) c`, using `wt k ≥ 1`;
* `CSq_le_ENormSq_of_periodization (m+1)`: `CSq (m+1) (fourierCoeff P) ≤ C₂ · ENormSq (m+1) P`
  (the `+1` is essential: the comparison needs the vanishing of `P` on a half-integer hyperplane
  to control the mean by the first derivative).
-/

namespace Work.Diff.STE.B3

/-- **Monotonicity of `CSq` in the order.**  The weights satisfy `wt k ≥ 1`, so raising the weight
to a higher power can only increase the weighted `ℓ²` mass.  Only summability *at the higher order*
is needed: the lower-order series is then summable by comparison. -/
lemma CSq_le_CSq_succ {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ℕ) (c : (ι → ℤ) → ℂ)
    (hs' : Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ (s + 1) * ‖c k‖ ^ 2)) :
    Work.Diff.STE.CSq s c ≤ Work.Diff.STE.CSq (s + 1) c := by
  have hle : ∀ k : ι → ℤ, (Work.Diff.STE.wt k) ^ s * ‖c k‖ ^ 2
      ≤ (Work.Diff.STE.wt k) ^ (s + 1) * ‖c k‖ ^ 2 := fun k =>
    mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (Work.Diff.STE.wt_one_le k) (Nat.le_succ s)) (sq_nonneg _)
  have hs : Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s * ‖c k‖ ^ 2) :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) s) (sq_nonneg _))
      hle hs'
  simp only [Work.Diff.STE.CSq]
  exact Summable.tsum_le_tsum hle hs hs'

theorem ENormSq_le_succ {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R P : (ι → ℝ) → ℂ),
      ContDiff ℝ (⊤ : ℕ∞) R →
      Function.support R ⊆ Set.pi Set.univ (fun _ : ι => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) →
      ContDiff ℝ (⊤ : ℕ∞) P → Work.Diff.STE.Periodic1 P →
      (∀ z : ι → ℝ, P z = ∑' m' : ι → ℤ, R (z + Work.Diff.STE.iVec m')) →
      Work.Diff.STE.ENormSq m P ≤ C * Work.Diff.STE.ENormSq (m + 1) P := by
  obtain ⟨C₁, hC₁nn, hC₁⟩ := Work.Diff.STE.ENormSq_le_CSq_of_contDiff_periodic (ι := ι) m
  obtain ⟨C₂, hC₂nn, hC₂⟩ := CSq_le_ENormSq_of_periodization (ι := ι) (m + 1) (by omega)
  refine ⟨C₁ * C₂, mul_nonneg hC₁nn hC₂nn, ?_⟩
  intro R P hR hsupp hP hper hrepr
  have hsum := Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff P hP hper (m + 1)
  have hmono : Work.Diff.STE.CSq m (Work.Diff.STE.fourierCoeff P)
      ≤ Work.Diff.STE.CSq (m + 1) (Work.Diff.STE.fourierCoeff P) :=
    CSq_le_CSq_succ m (Work.Diff.STE.fourierCoeff P) hsum
  have h₂ := hC₂ R P hR hsupp hP hper hrepr
  calc Work.Diff.STE.ENormSq m P
      ≤ C₁ * Work.Diff.STE.CSq m (Work.Diff.STE.fourierCoeff P) := hC₁ P hP hper
    _ ≤ C₁ * Work.Diff.STE.CSq (m + 1) (Work.Diff.STE.fourierCoeff P) :=
        mul_le_mul_of_nonneg_left hmono hC₁nn
    _ ≤ C₁ * (C₂ * Work.Diff.STE.ENormSq (m + 1) P) := mul_le_mul_of_nonneg_left h₂ hC₁nn
    _ = (C₁ * C₂) * Work.Diff.STE.ENormSq (m + 1) P := by ring

end Work.Diff.STE.B3
