import Mathlib
import Submission.Commons.NumberTheory.Linnik.completedL_zeroCount
import Submission.Commons.NumberTheory.Linnik.partialFraction_tail
import Submission.Commons.NumberTheory.Linnik.divisor_eq_closedBall_subset
import Submission.Commons.NumberTheory.Linnik.partialSum_tiny
import Submission.Commons.NumberTheory.Linnik.farSum_weight_bound
import Submission.Commons.NumberTheory.Linnik.completedL_ballZeroCount

open Complex DirichletCharacter Metric
open scoped Real BigOperators
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section

namespace Commons.NumberTheory.Linnik

/-!
# `partialSum_far_bound` — far-away zeros of the completed Dirichlet L-function

For a primitive non-trivial character `χ mod N` put `Λ := completedLFunction χ`.
Let `D_T(u)` be the divisor coefficient of `Λ` at `u` in the closed ball `|s| ≤ T`
(= the multiplicity of `u` as a zero of `Λ`, when `u` is a zero, and `0` otherwise:
`Λ` is entire since `χ ≠ 1`).  We prove

`∃ c, ∀ R ≥ 2, ∀ w (‖w‖ = R), ∀ T ≥ R+1`:
`Σᶠ_u D_T(u) · (if 1 < ‖w-u‖ then ‖w‖/(‖u‖·‖w-u‖) else 0) ≤ c·(ℓ(R)² + 1)`

with `ℓ(R) = log(R+2) + log N + 2`.  (No decay in `T` is needed — the right-hand side is
independent of `T` because the far shells `|u| ~ 2^k R` contribute geometrically.)

**Proof organisation.**

1. `partialSum_tiny` (child, Commons): the zeros in the unit disk `‖u‖ < 1` contribute at
   most a constant `K(χ)`: there are finitely many of them, none is `0` (`Λ(0) ≠ 0`), and
   each has weight `‖w‖/(‖u‖·‖w−u‖) ≤ 2/‖u‖` because `‖w−u‖ ≥ R − ‖u‖ ≥ R/2`.

2. `farSum_weight_bound` (child, Commons): a *pure analysis* lemma.  Given any finite set
   `S` of points with `‖u‖ ≥ 1` and non-negative integer multiplicities `m`, satisfying the
   ball-count bound `∀ a, ∀ ρ ≥ 1`: `Σ_{u ∈ S, ‖u−a‖ ≤ ρ} m(u) ≤ C(ρ+1)·(log(‖a‖+ρ+2)+q+2)`,
   one has `Σ_{u ∈ S, 1<‖w−u‖} m(u)·R/(‖u‖·‖w−u‖) ≤ c·((log(R+2)+q+2)²+1)` for
   `2 ≤ R = ‖w‖`.  The proof splits `u` into the low shells `1 ≤ ‖u‖ ≤ R/4` (weight
   `≤ (4/3)/‖u‖`, centre-`0` dyadic annuli), the middle band `R/4 ≤ ‖u‖ ≤ 4R` (weight
   `≤ 4/‖w−u‖`, dyadic annuli about `w`) and the far shells `‖u‖ ≥ 4R` (weight
   `≤ 4R/(3‖u‖²)`, geometric decay).

3. This file instantiates (2) with `S` = the (finite) support of `D_T` outside the unit
   disk, `m = D_T`, `q = log N`; the ball-count hypothesis is discharged by
   `completedL_ballZeroCount` (`Commons.NumberTheory.Linnik`), which bounds the divisor sum
   on any closed ball of radius ≥ 1.  The unit-disk part is (1).  Both bounds are combined
   into a single constant `c`.
-/
theorem partialSum_far_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    ∃ c : ℝ, ∀ R : ℝ, 2 ≤ R → ∀ w : ℂ, ‖w‖ = R → ∀ T : ℝ, R + 1 ≤ T →
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 T)) u : ℤ) : ℝ) *
          (if 1 < ‖w - u‖ then ‖w‖ / (‖u‖ * ‖w - u‖) else 0)) ≤
        c * ((Real.log (R + 2) + Real.log (N : ℝ) + 2) ^ 2 + 1) := by
  classical
  let Λ : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  have hΛdiff : Differentiable ℂ Λ := by simpa [Λ] using (differentiable_completedLFunction hχ)
  have hΛan : ∀ U : Set ℂ, AnalyticOnNhd ℂ Λ U := by
    intro U z hz
    exact hΛdiff.analyticAt z
  have hΛmer : ∀ U : Set ℂ, MeromorphicOn Λ U := fun U => (hΛan U).meromorphicOn
  have hdiv_nonneg : ∀ U : Set ℂ, ∀ u : ℂ, 0 ≤ ((MeromorphicOn.divisor Λ U) u : ℤ) := by
    intro U u
    exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hΛan U) u
  have hlogN0 : 0 ≤ Real.log (N : ℝ) := logN_nonneg (N := N)
  -- ball-count constant (arbitrary centre, radius ≥ 1)
  rcases completedL_ballZeroCount χ hχ hχprim with ⟨C0, hC0⟩
  let C : ℝ := max C0 0
  have hC0nonneg : 0 ≤ C := by dsimp [C]; exact le_max_right C0 0
  have hC0le : C0 ≤ C := by dsimp [C]; exact le_max_left C0 0
  have hCcount : ∀ a : ℂ, ∀ ρ : ℝ, 1 ≤ ρ →
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (closedBall a ρ)) u : ℤ) : ℝ)) ≤
        C * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) := by
    intro a ρ hρ
    have h1 := hC0 a ρ hρ
    have hρ0 : 0 ≤ ρ + 1 := by linarith
    have hL0 : 0 ≤ Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2 := by
      have h1 : 0 ≤ Real.log (‖a‖ + ρ + 2) := by
        refine Real.log_nonneg ?_
        nlinarith [norm_nonneg a]
      linarith
    calc
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (closedBall a ρ)) u : ℤ) : ℝ))
          ≤ C0 * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) := h1
      _ ≤ C * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC0le hρ0) hL0
  -- constants supplied by the two delegated sub-lemmas
  rcases farSum_weight_bound (q := Real.log (N : ℝ)) hlogN0 (C := C) hC0nonneg with ⟨c1, hc1nn, hfar1⟩
  rcases partialSum_tiny χ hχ hχprim with ⟨K, hKnn, htiny⟩
  let c : ℝ := K + c1
  have hc0 : 0 ≤ c := by dsimp [c]; linarith
  refine ⟨c, ?_⟩
  intro R hR w hw T hT
  let L : ℝ := Real.log (R + 2) + Real.log (N : ℝ) + 2
  have hX1 : 1 ≤ L ^ 2 + 1 := by nlinarith [sq_nonneg L]
  have hc1nn0 : 0 ≤ c1 := hc1nn
  -- support of the divisor on the closed ball 0 T
  let D : ℂ → ℤ := fun u => MeromorphicOn.divisor Λ (closedBall (0 : ℂ) T) u
  have hfin : D.support.Finite := by
    dsimp [D]
    exact (MeromorphicOn.divisor Λ (closedBall (0 : ℂ) T)).finiteSupport
      (isCompact_closedBall (0 : ℂ) T)
  let S : Finset ℂ := hfin.toFinset
  have hS_mem : ∀ u : ℂ, u ∈ S ↔ D u ≠ 0 := by
    intro u
    dsimp [S]
    rw [Set.Finite.mem_toFinset]
    rfl
  have hS_ball : ∀ u : ℂ, u ∈ S → ‖u‖ ≤ T := by
    intro u hu
    have hd : D u ≠ 0 := (hS_mem u).mp hu
    have huB : u ∈ closedBall (0 : ℂ) T :=
      (MeromorphicOn.divisor Λ (closedBall (0 : ℂ) T)).supportWithinDomain (by simpa [D] using hd)
    simpa [Metric.mem_closedBall, dist_eq_norm] using huB
  have hD_nonneg : ∀ u : ℂ, 0 ≤ (D u : ℤ) := by
    intro u
    dsimp [D]
    exact hdiv_nonneg (closedBall (0 : ℂ) T) u
  -- the weighted summand
  let wgt : ℂ → ℝ := fun u => if 1 < ‖w - u‖ then ‖w‖ / (‖u‖ * ‖w - u‖) else 0
  let g : ℂ → ℝ := fun u => (((D u : ℤ) : ℝ) * wgt u)
  have hg_support : Function.support g ⊆ (S : Set ℂ) := by
    intro u hu
    rw [Function.mem_support] at hu
    have hD : D u ≠ 0 := by
      intro hz
      apply hu
      dsimp [g]
      simp [hz]
    exact (hS_mem u).mpr hD
  have hFinsum : (∑ᶠ u : ℂ, g u) = ∑ u ∈ S, g u := by
    exact finsum_eq_sum_of_support_subset g hg_support
  -- split the summand region into ‖u‖ < 1 and 1 ≤ ‖u‖
  let S1 : Finset ℂ := S.filter (fun u : ℂ => ‖u‖ < 1)
  let S2 : Finset ℂ := S.filter (fun u : ℂ => ¬ ‖u‖ < 1)
  have hSum_split : (∑ u ∈ S, g u) = (∑ u ∈ S1, g u) + (∑ u ∈ S2, g u) := by
    exact (Finset.sum_filter_add_sum_filter_not S (fun u : ℂ => ‖u‖ < 1) g).symm
  -- ---- tiny part: ‖u‖ < 1
  let ht : ℂ → ℝ := fun u =>
      (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 T)) u : ℤ) : ℝ) *
          (if ‖u‖ < 1 ∧ 1 < ‖w - u‖ then ‖w‖ / (‖u‖ * ‖w - u‖) else 0)
  have ht_eq_D : ∀ u : ℂ, ht u = (((D u : ℤ) : ℝ) *
      (if ‖u‖ < 1 ∧ 1 < ‖w - u‖ then ‖w‖ / (‖u‖ * ‖w - u‖) else 0)) := by
    intro u
    dsimp [ht, D, Λ]
  have ht_nonneg : ∀ u : ℂ, 0 ≤ ht u := by
    intro u
    dsimp [ht]
    have hD0 : 0 ≤ (((D u : ℤ) : ℝ)) := by exact_mod_cast (hD_nonneg u)
    have hv0 : 0 ≤ (if ‖u‖ < 1 ∧ 1 < ‖w - u‖ then ‖w‖ / (‖u‖ * ‖w - u‖) else (0 : ℝ)) := by
      split_ifs
      · exact div_nonneg (norm_nonneg w) (mul_nonneg (norm_nonneg u) (norm_nonneg (w - u)))
      · simp
    exact mul_nonneg hD0 hv0
  have htiny_finsum : (∑ᶠ u : ℂ, ht u) ≤ K := by
    exact (htiny R hR w hw T hT)
  have hht_support : Function.support ht ⊆ (S : Set ℂ) := by
    intro u hu
    rw [Function.mem_support] at hu
    have hD : D u ≠ 0 := by
      intro hz
      apply hu
      rw [ht_eq_D u]
      simp [hz]
    exact (hS_mem u).mpr hD
  have hht_finsum_eq : (∑ᶠ u : ℂ, ht u) = ∑ u ∈ S, ht u := by
    exact finsum_eq_sum_of_support_subset ht hht_support
  have htiny1 : (∑ u ∈ S1, g u) ≤ K := by
    calc
      (∑ u ∈ S1, g u) = ∑ u ∈ S1, ht u := by
          refine Finset.sum_congr rfl ?_
          intro u hu
          have hlt : ‖u‖ < 1 := (Finset.mem_filter.mp hu).2
          dsimp [g, wgt]
          rw [ht_eq_D u]
          simp [hlt]
      _ ≤ ∑ u ∈ S, ht u := by
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ S) (by
            intro u huS hnot
            exact ht_nonneg u)
      _ = ∑ᶠ u : ℂ, ht u := hht_finsum_eq.symm
      _ ≤ K := htiny_finsum
  -- ---- far part: 1 ≤ ‖u‖
  have hS2_ge : ∀ u ∈ S2, 1 ≤ ‖u‖ := by
    intro u hu
    have hnlt : ¬ ‖u‖ < 1 := (Finset.mem_filter.mp hu).2
    exact le_of_not_gt hnlt
  have hm2 : ∀ u ∈ S2, 0 ≤ (D u : ℤ) := by
    intro u hu
    exact hD_nonneg u
  have hcount2 : ∀ a : ℂ, ∀ ρ : ℝ, 1 ≤ ρ →
      (∑ u ∈ S2.filter (fun u => ‖u - a‖ ≤ ρ), (((D u : ℤ) : ℝ))) ≤
        C * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) := by
    intro a ρ hρ
    -- for every zero in the ball of radius T the divisor coefficient agrees with the
    -- divisor on the (arbitrary) closed ball `closedBall a ρ` containing it
    have hEq : ∀ u ∈ S.filter (fun u => ‖u - a‖ ≤ ρ),
        D u = MeromorphicOn.divisor Λ (closedBall a ρ) u := by
      intro u hu
      have huS : u ∈ S := (Finset.mem_filter.mp hu).1
      have hdist : ‖u - a‖ ≤ ρ := (Finset.mem_filter.mp hu).2
      have huT : ‖u‖ ≤ T := hS_ball u huS
      have hu1 : u ∈ closedBall (0 : ℂ) T := by simpa [Metric.mem_closedBall, dist_eq_norm] using huT
      have hu2 : u ∈ closedBall a ρ := by simpa [Metric.mem_closedBall, dist_eq_norm] using hdist
      have heq := divisor_eq_closedBall_subset (f := Λ) (a := (0 : ℂ)) (b := a) (ra := T) (rb := ρ)
        (hf := hΛan (closedBall (0 : ℂ) T ∪ closedBall a ρ)) hu1 hu2
      dsimp [D]
      exact heq
    have hsubset : S2.filter (fun u => ‖u - a‖ ≤ ρ) ⊆ S.filter (fun u => ‖u - a‖ ≤ ρ) := by
      exact Finset.filter_subset_filter _ (Finset.filter_subset _ S)
    have hpartial : (∑ u ∈ S2.filter (fun u => ‖u - a‖ ≤ ρ), (((D u : ℤ) : ℝ))) ≤
        (∑ u ∈ S.filter (fun u => ‖u - a‖ ≤ ρ),
          (((MeromorphicOn.divisor Λ (closedBall a ρ)) u : ℤ) : ℝ)) := by
      calc
        (∑ u ∈ S2.filter (fun u => ‖u - a‖ ≤ ρ), (((D u : ℤ) : ℝ)))
            = ∑ u ∈ S2.filter (fun u => ‖u - a‖ ≤ ρ),
                (((MeromorphicOn.divisor Λ (closedBall a ρ)) u : ℤ) : ℝ) := by
                refine Finset.sum_congr rfl ?_
                intro u hu
                have huS2 : u ∈ S2 := (Finset.mem_filter.mp hu).1
                have huS : u ∈ S := (Finset.mem_filter.mp huS2).1
                have hu' : u ∈ S.filter (fun u => ‖u - a‖ ≤ ρ) :=
                  Finset.mem_filter.mpr ⟨huS, (Finset.mem_filter.mp hu).2⟩
                rw [hEq u hu']
        _ ≤ ∑ u ∈ S.filter (fun u => ‖u - a‖ ≤ ρ),
                (((MeromorphicOn.divisor Λ (closedBall a ρ)) u : ℤ) : ℝ) := by
                exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
                  intro u hu hnot
                  exact_mod_cast (hdiv_nonneg (closedBall a ρ) u))
    have hSρfin : (MeromorphicOn.divisor Λ (closedBall a ρ)).support.Finite := by
      exact (MeromorphicOn.divisor Λ (closedBall a ρ)).finiteSupport (isCompact_closedBall a ρ)
    let Sρ : Finset ℂ := hSρfin.toFinset
    have hSρ_mem : ∀ u : ℂ, u ∈ Sρ ↔ MeromorphicOn.divisor Λ (closedBall a ρ) u ≠ 0 := by
      intro u
      dsimp [Sρ]
      rw [Set.Finite.mem_toFinset]
      rfl
    have hS_ball_sub : S.filter (fun u => ‖u - a‖ ≤ ρ) ⊆ Sρ := by
      intro u hu
      have huS : u ∈ S := (Finset.mem_filter.mp hu).1
      have hDnz : D u ≠ 0 := (hS_mem u).mp huS
      have hEq2 : D u = MeromorphicOn.divisor Λ (closedBall a ρ) u := hEq u hu
      have hdnz : MeromorphicOn.divisor Λ (closedBall a ρ) u ≠ 0 := by
        rw [← hEq2]
        exact hDnz
      exact (hSρ_mem u).mpr hdnz
    have htotal_le : (∑ u ∈ S.filter (fun u => ‖u - a‖ ≤ ρ),
          (((MeromorphicOn.divisor Λ (closedBall a ρ)) u : ℤ) : ℝ)) ≤
        (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (closedBall a ρ)) u : ℤ) : ℝ)) := by
      have hf2 : (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (closedBall a ρ)) u : ℤ) : ℝ)) =
          ∑ u ∈ Sρ, (((MeromorphicOn.divisor Λ (closedBall a ρ)) u : ℤ) : ℝ) := by
        refine finsum_eq_sum_of_support_subset _ ?_
        intro u hu
        rw [Function.mem_support] at hu
        have hd : MeromorphicOn.divisor Λ (closedBall a ρ) u ≠ 0 := by
          intro hz
          apply hu
          simp [hz]
        exact (hSρ_mem u).mpr hd
      calc
        (∑ u ∈ S.filter (fun u => ‖u - a‖ ≤ ρ),
              (((MeromorphicOn.divisor Λ (closedBall a ρ)) u : ℤ) : ℝ))
            ≤ ∑ u ∈ Sρ, (((MeromorphicOn.divisor Λ (closedBall a ρ)) u : ℤ) : ℝ) := by
                exact Finset.sum_le_sum_of_subset_of_nonneg hS_ball_sub (by
                  intro u hu hnot
                  exact_mod_cast (hdiv_nonneg (closedBall a ρ) u))
        _ = ∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (closedBall a ρ)) u : ℤ) : ℝ) := hf2.symm
    exact le_trans (le_trans hpartial htotal_le) (hCcount a ρ hρ)
  have hfarb := hfar1 S2 D hS2_ge hm2 hcount2 R hR w hw
  have hfar2 : (∑ u ∈ S2, g u) ≤ c1 * (L ^ 2 + 1) := by
    calc
      (∑ u ∈ S2, g u)
          = ∑ u ∈ S2, (if 1 < ‖w - u‖ then (((D u : ℤ) : ℝ) * (R / (‖u‖ * ‖w - u‖))) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro u hu
          by_cases h : 1 < ‖w - u‖ <;> simp [g, wgt, h, hw]
      _ = ∑ u ∈ S2.filter (fun u => 1 < ‖w - u‖),
          (((D u : ℤ) : ℝ) * (R / (‖u‖ * ‖w - u‖))) := by
          rw [← Finset.sum_filter]
      _ ≤ c1 * ((Real.log (R + 2) + Real.log (N : ℝ) + 2) ^ 2 + 1) := by
          simpa [L] using hfarb
  -- ---- combine
  have hfin1 : (∑ u ∈ S1, g u) + (∑ u ∈ S2, g u) ≤ K + c1 * (L ^ 2 + 1) := by
    exact add_le_add htiny1 hfar2
  have hfin2 : K + c1 * (L ^ 2 + 1) ≤ (K + c1) * (L ^ 2 + 1) := by
    have hX0 : 0 ≤ L ^ 2 + 1 := by nlinarith
    have hK : K ≤ K * (L ^ 2 + 1) := by
      have hK0 : 0 ≤ K := hKnn
      nlinarith [mul_le_mul_of_nonneg_left hX1 hK0]
    calc
      K + c1 * (L ^ 2 + 1) ≤ K * (L ^ 2 + 1) + c1 * (L ^ 2 + 1) := by linarith
      _ = (K + c1) * (L ^ 2 + 1) := by ring
  calc
    (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 T)) u : ℤ) : ℝ) *
        (if 1 < ‖w - u‖ then ‖w‖ / (‖u‖ * ‖w - u‖) else 0))
        = ∑ᶠ u : ℂ, g u := by
            simp [g, wgt, D, Λ]
    _ = ∑ u ∈ S, g u := hFinsum
    _ = (∑ u ∈ S1, g u) + (∑ u ∈ S2, g u) := hSum_split
    _ ≤ K + c1 * (L ^ 2 + 1) := hfin1
    _ ≤ (K + c1) * (L ^ 2 + 1) := hfin2
    _ = c * ((Real.log (R + 2) + Real.log (N : ℝ) + 2) ^ 2 + 1) := by
        dsimp [c, L]

end Commons.NumberTheory.Linnik
