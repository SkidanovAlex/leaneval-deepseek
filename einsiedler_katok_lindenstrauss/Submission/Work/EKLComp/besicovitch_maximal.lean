import Mathlib

/-!
# The Besicovitch maximal inequality (EKL (10), Lindenstrauss '06 Thm A.1)

This file proves the maximal inequality consumed by the construction of the set `X₂`/`X₃`
in Einsiedler–Katok–Lindenstrauss, "Smallness of exceptional set to Littlewood's conjecture".

The input `hcover` is the (one-dimensional) Besicovitch covering theorem: from a family of balls
with centres ranging over a set `A ⊆ ℝ` and bounded positive radii one can select `N` subfamilies
of pairwise disjoint closed balls whose open balls cover `A` (this is supplied by
`Work.EKLComp.besicovitch_intervals`).

The point of the argument is the classical maximal-inequality step: for every centre `a ∈ A` the
closed ball `closedBall a (r a)` has small `lam`-measure compared with the integral of `H` over it,
and the covering splits `A` into `N` disjoint families, so

  `c * lam A ≤ N * ∫⁻ H ∂lam`.
-/

open MeasureTheory

namespace Work.EKLComp

theorem besicovitch_maximal (N : ℕ)
    (hcover : ∀ (A : Set ℝ) (r : A → ℝ), (∀ a, 0 < r a) → (∃ ρ : ℝ, ∀ a, r a ≤ ρ) →
      ∃ s : Fin N → Set A,
        (∀ i, (s i).PairwiseDisjoint fun a => Metric.closedBall (a : ℝ) (r a)) ∧
        A ⊆ ⋃ i, ⋃ a ∈ s i, Metric.ball (a : ℝ) (r a))
    (lam : MeasureTheory.Measure ℝ) (H : ℝ → ENNReal) (c : ENNReal)
    (A : Set ℝ) (r : ℝ → ℝ) (hA : ∀ a ∈ A, 0 < r a) (hbdd : ∃ ρ : ℝ, ∀ a ∈ A, r a ≤ ρ)
    (hbad : ∀ a ∈ A, c * lam (Metric.closedBall a (r a))
      < ∫⁻ t in Metric.closedBall a (r a), H t ∂lam) :
    c * lam A ≤ (N : ENNReal) * ∫⁻ t, H t ∂lam := by
  -- The Besicovitch covering theorem, applied to the restriction of `r` to `A`.
  obtain ⟨s, hdisj, hcov⟩ := hcover A (fun a : A => r (a : ℝ)) (fun a => hA (a : ℝ) a.2)
      (by obtain ⟨ρ, hρ⟩ := hbdd; exact ⟨ρ, fun a => hρ (a : ℝ) a.2⟩)
  -- The selected balls, as a function of a point of `A`.
  let F : A → Set ℝ := fun b => Metric.closedBall (b : ℝ) (r (b : ℝ))
  have hdisj' : ∀ i, (s i).PairwiseDisjoint F := hdisj
  -- Each family `s i` is countable: it is a pairwise disjoint family of closed balls in the
  -- separable space `ℝ`, and `r b > 0` keeps their interiors nonempty.
  have hcount : ∀ i, (s i).Countable := by
    intro i
    apply (hdisj' i).countable_of_nonempty_interior
    intro b hb
    have hbpos : 0 < r (b : ℝ) := hA (b : ℝ) b.2
    exact ⟨(b : ℝ),
      Metric.ball_subset_interior_closedBall
        (Metric.mem_ball.mpr (by rw [dist_self]; exact hbpos))⟩
  -- The estimate for a single one of the `N` disjoint subfamilies.
  have key : ∀ i : Fin N, c * lam (⋃ b ∈ s i, F b) ≤ ∫⁻ t, H t ∂lam := by
    intro i
    have hc := hcount i
    have hd := hdisj' i
    have hm : ∀ b ∈ s i, MeasurableSet (F b) :=
      fun b hb => Metric.isClosed_closedBall.measurableSet
    have step1 : lam (⋃ b ∈ s i, F b) = ∑' p : ↥(s i), lam (F p) :=
      measure_biUnion hc hd hm
    calc c * lam (⋃ b ∈ s i, F b)
        = c * ∑' p : ↥(s i), lam (F p) := by rw [step1]
        _ = ∑' p : ↥(s i), c * lam (F p) := by rw [ENNReal.tsum_mul_left]
        _ ≤ ∑' p : ↥(s i), ∫⁻ t in F p, H t ∂lam := by
              apply ENNReal.tsum_le_tsum; intro p
              exact le_of_lt (hbad ((p : A) : ℝ) (p : A).2)
        _ = ∫⁻ t in ⋃ b ∈ s i, F b, H t ∂lam := (lintegral_biUnion hc hm hd H).symm
        _ ≤ ∫⁻ t in (Set.univ : Set ℝ), H t ∂lam := lintegral_mono_set (Set.subset_univ _)
        _ = ∫⁻ t, H t ∂lam := by rw [Measure.restrict_univ]
  -- The covering statement: `A` is contained in the union of the closed balls.
  have hAU : A ⊆ ⋃ i : Fin N, ⋃ b ∈ s i, F b := by
    intro x hx
    rcases Set.mem_iUnion.mp (hcov hx) with ⟨i, hi⟩
    rcases Set.mem_iUnion₂.mp hi with ⟨b, hb, hxb⟩
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_biUnion hb (Metric.ball_subset_closedBall hxb)⟩
  calc c * lam A
      ≤ c * lam (⋃ i : Fin N, ⋃ b ∈ s i, F b) := mul_le_mul_right (measure_mono hAU) c
      _ ≤ c * ∑ i : Fin N, lam (⋃ b ∈ s i, F b) :=
            mul_le_mul_right (measure_iUnion_fintype_le lam (fun i => ⋃ b ∈ s i, F b)) c
      _ = ∑ i : Fin N, c * lam (⋃ b ∈ s i, F b) := by rw [Finset.mul_sum]
      _ ≤ ∑ i : Fin N, ∫⁻ t, H t ∂lam := Finset.sum_le_sum (fun i _ => key i)
      _ = (N : ENNReal) * ∫⁻ t, H t ∂lam := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end Work.EKLComp
