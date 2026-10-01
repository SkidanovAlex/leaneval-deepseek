import Mathlib
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_DhK_Defs
import Submission.Commons.NumberTheory.Linnik.zeroSum_invSq_bound
import Submission.Work.LinnikAreas.xiC_ballCount_order
import Submission.Work.LinnikAreas.xiCZeroInvSqTailBound
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_DhExplicit_XiStrip

namespace Work.LinnikAreas.DhExplicit

open scoped Classical BigOperators

/-!
# Summability of the multiplicity-weighted inverse-square zero sum of `ζ_K = ζ · L(·,χ)`

`Work.LinnikAreas.DhK.kMult χ u = ord_u(Ξ) + ord_u(Λ(·,χ))` is the multiplicity of `u` as a
non-trivial zero of the Dedekind zeta function `ζ_K = ζ · L(·,χ)` of the quadratic field attached
to a real primitive `χ` (`Ξ = DhK.Xi` the entire completion of `ζ`, `Λ = completedLFunction χ`
the completed `L`-function).  We show that the inverse-square weighted sum

`∑'_u kMult χ u · 1/(1 + ‖u‖²)`

converges, by splitting the summand into its two nonnegative halves and bounding the finite
partial sums of each.

* The `Ξ`-half: the zeros of `Ξ` of norm at most `2` are controlled by the Riemann–von Mangoldt
  ball count `Work.LinnikAreas.xiC_ballCount_order` (`Ξ` is definitionally the function
  `Work.LinnikAreas.xiC`), and those of norm larger than `2` by the dyadic inverse-square tail
  estimate `Work.LinnikAreas.xiCZeroInvSqTailBound`, using `1/(1+‖u‖²) ≤ 1/‖u‖²`.
* The `Λ`-half: the uniform (in the radius) inverse-square divisor bound
  `Commons.NumberTheory.Linnik.zeroSum_invSq_bound` taken at the centre `s = 0` bounds the divisor
  sum of `Λ` over the ball `closedBall 0 R` by `C (log q + log 2 + 2)`; any finite set `S` lies in
  such a ball for `R = max 1 (∑_{u∈S}(‖u‖+1))`, where the ball divisor of the entire function `Λ`
  computes the vanishing orders.

Both halves give a uniform bound on the finite partial sums of a nonnegative family, whence
`summable_of_sum_le`; `Summable.add` and `Nat.cast_add` assemble the two.
-/

/-- `DhK.Xi` and `Work.LinnikAreas.xiC` are the very same entire function (definitionally). -/
lemma kMultInvSqSummable_Xi_eq_xiC : Work.LinnikAreas.DhK.Xi = Work.LinnikAreas.xiC := rfl

/-- **Uniform bound for the `Ξ`-half.**  The finite partial sums of the multiplicity-weighted
inverse-square sum of the vanishing orders of `Ξ` are uniformly bounded.

The zeros of norm at most `2` are counted by `xiC_ballCount_order` at `R = 2` (after identifying
`Ξ = xiC`), and those of norm larger than `2` by `xiCZeroInvSqTailBound`, the kernel
`1/(1+‖u‖²)` being dominated by `1/‖u‖²`. -/
lemma xiMultInvSqSum_le :
    ∃ C : ℝ, ∀ S : Finset ℂ,
      ∑ u ∈ S, (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℝ) * (1 / (1 + ‖u‖ ^ 2)) ≤ C := by
  classical
  obtain ⟨C₂, hC₂pos, htail⟩ := Work.LinnikAreas.xiCZeroInvSqTailBound
  obtain ⟨c, hcpos, hcount⟩ := Work.LinnikAreas.xiC_ballCount_order
  set C₁ : ℝ := c * 2 * (Real.log (2 + 2) + 2) with hC₁def
  refine ⟨C₁ + C₂ + 1, ?_⟩
  intro S
  rw [← Finset.sum_filter_add_sum_filter_not S (fun u : ℂ => ‖u‖ ≤ 2)
        (fun u => (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℝ) * (1 / (1 + ‖u‖ ^ 2)))]
  -- The part carried by the zeros of norm at most `2`.
  have h1 : (∑ u ∈ S.filter (fun u : ℂ => ‖u‖ ≤ 2),
        (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℝ) * (1 / (1 + ‖u‖ ^ 2))) ≤ C₁ := by
    have hle : ∀ u ∈ S.filter (fun u : ℂ => ‖u‖ ≤ 2),
        (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℝ) * (1 / (1 + ‖u‖ ^ 2)) ≤
          (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℝ) := by
      intro u _
      have hw : (1 : ℝ) / (1 + ‖u‖ ^ 2) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [sq_nonneg ‖u‖]
      calc (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℝ) * (1 / (1 + ‖u‖ ^ 2))
          ≤ (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left hw (by positivity)
        _ = (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℝ) := by ring
    refine le_trans (Finset.sum_le_sum hle) ?_
    calc ∑ u ∈ S.filter (fun u : ℂ => ‖u‖ ≤ 2),
            (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℝ)
        = ∑ u ∈ S.filter (fun u : ℂ => ‖u‖ ≤ 2),
            (analyticOrderNatAt Work.LinnikAreas.xiC u : ℝ) :=
          Finset.sum_congr rfl (fun u _ => by rw [kMultInvSqSummable_Xi_eq_xiC])
      _ ≤ c * 2 * (Real.log (2 + 2) + 2) :=
          hcount 2 le_rfl _ (fun u hu => (Finset.mem_filter.mp hu).2)
      _ = C₁ := by rw [hC₁def]
  -- The part carried by the zeros of norm larger than `2`.
  have h2 : (∑ u ∈ S.filter (fun u : ℂ => ¬ ‖u‖ ≤ 2),
        (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℝ) * (1 / (1 + ‖u‖ ^ 2))) ≤ C₂ := by
    have hle : ∀ u ∈ S.filter (fun u : ℂ => ¬ ‖u‖ ≤ 2),
        (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℝ) * (1 / (1 + ‖u‖ ^ 2)) ≤
          (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℝ) / ‖u‖ ^ 2 := by
      intro u hu
      have hgt : 2 < ‖u‖ := lt_of_not_ge (Finset.mem_filter.mp hu).2
      have hpos : (0 : ℝ) < ‖u‖ ^ 2 := by positivity
      have hweight : (1 : ℝ) / (1 + ‖u‖ ^ 2) ≤ 1 / ‖u‖ ^ 2 :=
        one_div_le_one_div_of_le hpos (by linarith [sq_nonneg ‖u‖])
      calc (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℝ) * (1 / (1 + ‖u‖ ^ 2))
          ≤ (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℝ) * (1 / ‖u‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hweight (by positivity)
        _ = (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℝ) / ‖u‖ ^ 2 := by ring
    refine le_trans (Finset.sum_le_sum hle) ?_
    rw [Finset.sum_congr rfl (fun u _ => by rw [kMultInvSqSummable_Xi_eq_xiC])]
    exact htail _ (fun u hu => lt_of_not_ge (Finset.mem_filter.mp hu).2)
  linarith

/-- **Uniform bound for the `Λ`-half.**  The finite partial sums of the multiplicity-weighted
inverse-square sum of the vanishing orders of `Λ(·,χ) = completedLFunction χ` are uniformly
bounded, for `χ` a non-principal primitive character mod `q`.

Taking `s = 0` in the uniform inverse-square divisor bound
`Commons.NumberTheory.Linnik.zeroSum_invSq_bound`, and enclosing an arbitrary finite set `S` in
the ball `closedBall 0 R` with `R = max 1 (∑_{u∈S}(‖u‖+1))` — on which the ball divisor of the
entire function `Λ` computes the vanishing orders — bounds every finite partial sum. -/
lemma completedLMultInvSqSum_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) :
    ∃ C : ℝ, ∀ S : Finset ℂ,
      ∑ u ∈ S, (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ)
        * (1 / (1 + ‖u‖ ^ 2)) ≤ C := by
  classical
  obtain ⟨C, hCpos, hCb⟩ := Commons.NumberTheory.Linnik.zeroSum_invSq_bound χ hχ hprim
  refine ⟨C * (Real.log (q : ℝ) + Real.log 2 + 2), fun S => ?_⟩
  set R : ℝ := max 1 (∑ u ∈ S, (‖u‖ + 1)) with hRdef
  have hSR : ∀ u ∈ S, ‖u‖ ≤ R := by
    intro u hu
    have h2 : ‖u‖ + 1 ≤ ∑ v ∈ S, (‖v‖ + 1) :=
      Finset.single_le_sum (f := fun v : ℂ => ‖v‖ + 1) (fun v _ => by positivity) hu
    have h3 : ‖u‖ ≤ ∑ v ∈ S, (‖v‖ + 1) := by linarith
    exact le_trans h3 (le_max_right _ _)
  have hΛan : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall (0 : ℂ) R) :=
    Commons.NumberTheory.Linnik.completedLFunction_analyticOnNhd χ hχ _
  set D : ℂ → ℝ := fun u => (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall (0 : ℂ) R)) u : ℤ) : ℝ) with hDdef
  have hDnn : ∀ u : ℂ, 0 ≤ D u := by
    intro u
    by_cases hu : u ∈ Metric.closedBall (0 : ℂ) R
    · exact Commons.NumberTheory.Linnik.divisor_real_nonneg_of_analyticOnNhd hΛan hu
    · have hz : MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall (0 : ℂ) R) u = 0 := by
        rw [MeromorphicOn.divisor_def, if_neg]
        exact fun h => hu h.2
      simp only [hDdef, hz, Int.cast_zero, le_refl]
  have hDfin : Function.HasFiniteSupport D := by
    have h := Commons.NumberTheory.Linnik.divisor_real_finiteSupport χ hχ (0 : ℂ) R
    simpa only [hDdef] using h
  have hgnn : ∀ u : ℂ, 0 ≤ D u * (1 / (1 + ‖(0 : ℂ) - u‖ ^ 2)) :=
    fun u => mul_nonneg (hDnn u) (by positivity)
  have hsum_le : ∑ u ∈ S, D u * (1 / (1 + ‖(0 : ℂ) - u‖ ^ 2))
      ≤ ∑ᶠ u : ℂ, D u * (1 / (1 + ‖(0 : ℂ) - u‖ ^ 2)) := by
    have hgsupp : Function.support (fun u : ℂ => D u * (1 / (1 + ‖(0 : ℂ) - u‖ ^ 2)))
        ⊆ ↑(hDfin.toFinset ∪ S) := by
      intro u hu
      rw [Function.mem_support] at hu
      rw [Finset.mem_coe, Finset.mem_union]
      by_cases hS : u ∈ S
      · exact Or.inr hS
      · refine Or.inl ?_
        rw [hDfin.mem_toFinset]
        intro h0
        exact hu (by rw [h0, zero_mul])
    rw [finsum_eq_sum_of_support_subset _ hgsupp]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
      (fun i _ _ => hgnn i)
  have hval : ∀ u ∈ S,
      D u = (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ) := by
    intro u hu
    simp only [hDdef]
    have hu' : u ∈ Metric.closedBall (0 : ℂ) R := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact hSR u hu
    rw [Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast hΛan hu']
    push_cast
    ring
  calc ∑ u ∈ S, (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ)
          * (1 / (1 + ‖u‖ ^ 2))
      = ∑ u ∈ S, D u * (1 / (1 + ‖(0 : ℂ) - u‖ ^ 2)) := by
        refine Finset.sum_congr rfl (fun u hu => ?_)
        rw [← hval u hu, zero_sub, norm_neg]
    _ ≤ ∑ᶠ u : ℂ, D u * (1 / (1 + ‖(0 : ℂ) - u‖ ^ 2)) := hsum_le
    _ ≤ C * (Real.log (q : ℝ) + Real.log 2 + 2) := by
        have h := hCb (0 : ℂ) R
        have habs : ∀ u : ℂ, |(((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall (0 : ℂ) R)) u : ℤ) : ℝ)| =
            (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall (0 : ℂ) R)) u : ℤ) : ℝ) := by
          intro u
          exact abs_of_nonneg (by simpa only [hDdef] using hDnn u)
        simp only [habs, norm_zero, add_zero] at h
        simp only [hDdef]
        exact h

/-- The multiplicity-weighted inverse-square zero sum of the completed Dedekind zeta function
`ζ_K = ζ · L(·,χ)` is summable: for `χ` a non-principal primitive character mod `q`,

`∑'_u kMult χ u / (1 + ‖u‖²) < ∞`,

where `kMult χ u = analyticOrderNatAt Ξ u + analyticOrderNatAt (completedLFunction χ) u`
(`Ξ = Work.LinnikAreas.DhK.Xi`, definitionally the same function as `Work.LinnikAreas.xiC`) is the
multiplicity of `u` as a non-trivial zero of `ζ_K`.

MODULES TO IMPORT: `Submission.Work.LinnikAreas.DhK.Defs`,
`Submission.Commons.NumberTheory.Linnik.zeroSum_invSq_bound`,
`Submission.Work.LinnikAreas.xiC_ballCount_order`,
`Submission.Work.LinnikAreas.xiCZeroInvSqTailBound`,
`Submission.Work.LinnikAreas.DhExplicit.XiStrip`
(do NOT import `Submission.Commons.NumberTheory.Zeta.xiE_partialFraction_eq`,
`Submission.Commons.NumberTheory.Linnik.completedL_pf_identity_rect`,
`Submission.Work.LinnikAreas.summable_zeroMult_norm_mul` or
`Submission.Work.LinnikAreas.zetaZeroSumInvSq` — they declare `Commons.NumberTheory.Linnik.pfP`
a second time and are incompatible with `P3.CompletedDerivPF`, already in the environment.)

PROOF ROUTE: split `kMult = (Ξ part) + (Λ part)`.
- `Λ` part: `Commons.NumberTheory.Linnik.zeroSum_invSq_bound` bounds
  `Σᶠ_{‖u‖≤R} |divisor Λ (ball 0 R) u| · 1/(1+‖s-u‖²)` uniformly in `R` by
  `C(log q + log(2+‖s‖) + 2)`; taking `s = 0` and using that any finite set is contained in a
  large ball gives a uniform bound on the finite sums `Σ_{u∈S} ord_Λ(u)/(1+‖u‖²)`, hence
  summability by `summable_of_sum_le` (Mathlib).
- `Ξ` part: copy the (short, readable) proof of `Work.LinnikAreas.zetaZeroSumInvSq` (that module
  is in an incompatible import world, but its proof can be read and reproduced) using
  `Commons.Analysis.InfiniteSum.summable_of_finset_tail_bound` with
  - the small part: the zeros of `Ξ` in the closed ball of radius `2` are finite
    (`Work.LinnikAreas.DhK.Xi_divisor_support_finite 2`), and their total multiplicity is bounded
    by `Work.LinnikAreas.xiC_ballCount_order` at `R = 2`;
  - the tail part: `Work.LinnikAreas.xiCZeroInvSqTailBound` for sets with `2 < ‖u‖`, together
    with `1/(1+‖u‖²) ≤ 1/‖u‖²` and `analyticOrderNatAt xiC = analyticOrderNatAt Xi` (rfl).
Then add the two summable families pointwise.
(There is also a `Submission.Work.LinnikAreas.DhK.kMultInvSqBound` module in the workspace with the
same shape of conclusion; it may be used instead if it is sorry-free and its imports are
compatible.) -/
theorem kMultInvSqSummable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) :
    Summable (fun u : ℂ => ((Work.LinnikAreas.DhK.kMult χ u : ℕ) : ℝ) * (1 / (1 + ‖u‖ ^ 2))) := by
  obtain ⟨C₁, h₁⟩ := xiMultInvSqSum_le
  obtain ⟨C₂, h₂⟩ := completedLMultInvSqSum_le χ hχ hprim
  have hs1 : Summable (fun u : ℂ =>
      (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℝ) * (1 / (1 + ‖u‖ ^ 2))) :=
    summable_of_sum_le (c := C₁) (fun u => by positivity) h₁
  have hs2 : Summable (fun u : ℂ =>
      (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ)
        * (1 / (1 + ‖u‖ ^ 2))) :=
    summable_of_sum_le (c := C₂) (fun u => by positivity) h₂
  refine (hs1.add hs2).congr (fun u => ?_)
  simp only [Work.LinnikAreas.DhK.kMult, Nat.cast_add, add_mul]

end Work.LinnikAreas.DhExplicit
