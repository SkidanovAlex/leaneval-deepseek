import Mathlib
import Submission.Work.LinnikAreas.Density4.Defs
import Submission.Work.LinnikAreas2.PsiDefs2
import Submission.Work.LinnikAreas.Density4.Kbound_discharge
import Submission.Work.LinnikAreas2.d1_of_area1
import Submission.Work.LinnikAreas2.acoef_pair_summable
import Submission.Work.LinnikAreas2.acoef_diag_bound
import Submission.Work.LinnikAreas2.acoef_offdiag_bound

namespace Work.LinnikAreas2

open scoped BigOperators
open DirichletCharacter Complex

noncomputable section

/-! ## Auxiliary `tsum` bookkeeping -/

/-- A finite sum of summable `ℂ`-valued sequences is summable. -/
lemma summable_finset_sum {α : Type*} {s : Finset α} {f : α → ℕ → ℂ}
    (h : ∀ a ∈ s, Summable (f a)) : Summable (fun n => ∑ a ∈ s, f a n) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih (fun b hb => h b (Finset.mem_insert_of_mem hb)))

/-- Interchange of a `tsum` with a double finite sum. -/
lemma tsum_univ_univ {ι : Type*} [Fintype ι] (F : ℕ → ι → ι → ℂ)
    (h : ∀ i j, Summable (fun n => F n i j)) :
    (∑' n : ℕ, ∑ i, ∑ j, F n i j) = ∑ i, ∑ j, ∑' n : ℕ, F n i j := by
  classical
  rw [Summable.tsum_finsetSum (s := (Finset.univ : Finset ι))
      (f := fun i n => ∑ j, F n i j)
      (fun i _ => summable_finset_sum (s := (Finset.univ : Finset ι)) (fun j _ => h i j))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact Summable.tsum_finsetSum (s := (Finset.univ : Finset ι)) (f := fun j n => F n i j)
    (fun j _ => h i j)

/-! ## The abstract `ℓ²` operator/duality bound -/

/-- **The `ℓ²` operator bound behind HB (11.15).**  Given a family `A n i` whose Gram entries
`G i j = Σ'_n A n i · conj (A n j)` have a controlled diagonal (`G i i ≤ 1 + c₁`) and controlled
off-diagonal (`‖G i j‖ ≤ c₂ √(w i w j)`), the associated operator
`C ↦ (n ↦ Σ_i A n i C i)` is bounded on `ℓ²` by `(1+c₁) + c₂ Σ_i w i`. -/
lemma l2_operator_bound {ι : Type*} [Fintype ι] (A : ℕ → ι → ℂ) (C : ι → ℂ) (wc : ι → ℝ)
    {c1 c2 : ℝ} (hwc : ∀ i, 0 ≤ wc i) (hc2 : 0 ≤ c2)
    (hsum : ∀ i j, Summable (fun n : ℕ => A n i * star (A n j)))
    (hd : ∀ i, (∑' n : ℕ, ‖A n i‖^2) ≤ 1 + c1)
    (hob : ∀ i j, i ≠ j →
      ‖∑' n : ℕ, A n i * star (A n j)‖ ≤ c2 * Real.sqrt (wc i * wc j)) :
    (∑' n : ℕ, ‖∑ i, A n i * C i‖^2)
      ≤ (1 + c1) * (∑ i, ‖C i‖^2) + c2 * (∑ i, wc i) * (∑ i, ‖C i‖^2) := by
  classical
  set G : ι → ι → ℂ := fun i j => ∑' n : ℕ, A n i * star (A n j) with hG
  -- The diagonal entry is the real number `Σ'_n ‖A n i‖²`.
  have hGii : ∀ i, G i i = (((∑' n : ℕ, ‖A n i‖^2 : ℝ)) : ℂ) := by
    intro i
    show (∑' n : ℕ, A n i * star (A n i)) = _
    rw [Complex.ofReal_tsum]
    refine tsum_congr (fun n => ?_)
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    simp only [starRingEnd_apply]
  have hGnii : ∀ i, ‖G i i‖ ≤ 1 + c1 := by
    intro i
    rw [hGii i, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (tsum_nonneg fun n => by positivity)]
    exact hd i
  -- Expansion of the quadratic form as the Gram bilinear form.
  have hZ : (((∑' n : ℕ, ‖∑ i, A n i * C i‖^2 : ℝ)) : ℂ)
      = ∑ i, ∑ j, (C i * star (C j)) * G i j := by
    rw [Complex.ofReal_tsum]
    rw [show (∑' n : ℕ, ((‖∑ i, A n i * C i‖^2 : ℝ) : ℂ))
          = ∑' n : ℕ, ∑ i, ∑ j, (A n i * star (A n j)) * (C i * star (C j)) from
        tsum_congr (fun n => ?_)]
    · rw [tsum_univ_univ (fun n i j => (A n i * star (A n j)) * (C i * star (C j)))
          (fun i j => (hsum i j).mul_right _)]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      show (∑' n : ℕ, (A n i * star (A n j)) * (C i * star (C j))) = (C i * star (C j)) * G i j
      rw [show (∑' n : ℕ, (A n i * star (A n j)) * (C i * star (C j)))
            = ∑' n : ℕ, (C i * star (C j)) * (A n i * star (A n j)) from
          tsum_congr (fun n => by ring)]
      rw [tsum_mul_left]
    · rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
      simp only [starRingEnd_apply]
      rw [star_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [star_mul']
      ring
  have hreal : (∑' n : ℕ, ‖∑ i, A n i * C i‖^2)
      = (∑ i, ∑ j, (C i * star (C j)) * G i j).re := by
    rw [← hZ]
    simp
  -- Bound the quadratic form by the absolute-value Gram sum.
  set b : ι → ι → ℝ := fun i j => ‖C i‖ * ‖C j‖ * ‖G i j‖ with hb
  set s : ι → ℝ := fun i => ‖C i‖ * Real.sqrt (wc i) with hs
  have hub : (∑' n : ℕ, ‖∑ i, A n i * C i‖^2) ≤ ∑ i, ∑ j, b i j := by
    rw [hreal]
    calc (∑ i, ∑ j, (C i * star (C j)) * G i j).re
        ≤ ‖∑ i, ∑ j, (C i * star (C j)) * G i j‖ := Complex.re_le_norm _
      _ ≤ ∑ i, ‖∑ j, (C i * star (C j)) * G i j‖ := norm_sum_le _ _
      _ ≤ ∑ i, ∑ j, ‖(C i * star (C j)) * G i j‖ :=
            Finset.sum_le_sum (fun i _ => norm_sum_le _ _)
      _ = ∑ i, ∑ j, b i j := by
            simp only [hb]
            refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
            rw [norm_mul, norm_mul, show ‖star (C j)‖ = ‖C j‖ from Complex.norm_conj (C j)]
  -- Per-row bound: the diagonal gets `1 + c₁`, the off-diagonal gets `c₂`.
  have hper : ∀ i, ∑ j, b i j ≤ (1 + c1) * ‖C i‖^2 + c2 * s i * (∑ j, s j) := by
    intro i
    have hsplit : ∑ j, b i j = b i i + ∑ j ∈ Finset.univ.erase i, b i j := by
      rw [← Finset.sum_erase_add Finset.univ (fun j => b i j) (Finset.mem_univ i), add_comm]
    rw [hsplit]
    have h1 : b i i ≤ (1 + c1) * ‖C i‖^2 := by
      simp only [hb]
      rw [show ‖C i‖ * ‖C i‖ * ‖G i i‖ = ‖C i‖ ^ 2 * ‖G i i‖ by ring]
      calc ‖C i‖ ^ 2 * ‖G i i‖ ≤ ‖C i‖ ^ 2 * (1 + c1) :=
            mul_le_mul_of_nonneg_left (hGnii i) (by positivity)
        _ = (1 + c1) * ‖C i‖ ^ 2 := by ring
    have h2 : ∑ j ∈ Finset.univ.erase i, b i j ≤ c2 * s i * (∑ j, s j) := by
      have hstep : ∀ j ∈ Finset.univ.erase i, b i j ≤ c2 * s i * s j := by
        intro j hj
        have hji : i ≠ j := Ne.symm (Finset.mem_erase.mp hj).1
        simp only [hb, hs]
        calc ‖C i‖ * ‖C j‖ * ‖G i j‖
            ≤ ‖C i‖ * ‖C j‖ * (c2 * Real.sqrt (wc i * wc j)) :=
              mul_le_mul_of_nonneg_left (hob i j hji) (by positivity)
          _ = c2 * (‖C i‖ * Real.sqrt (wc i)) * (‖C j‖ * Real.sqrt (wc j)) := by
              rw [Real.sqrt_mul (hwc i) (wc j)]; ring
      calc ∑ j ∈ Finset.univ.erase i, b i j ≤ ∑ j ∈ Finset.univ.erase i, c2 * s i * s j :=
            Finset.sum_le_sum hstep
        _ = c2 * s i * (∑ j ∈ Finset.univ.erase i, s j) := by
            rw [Finset.mul_sum]
        _ ≤ c2 * s i * (∑ j, s j) := by
            refine mul_le_mul_of_nonneg_left ?_ (by simp only [hs]; positivity)
            refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
              (fun j _ _ => ?_)
            simp only [hs]; positivity
    linarith [h1, h2]
  -- Sum the rows.
  have hsum' : (∑ i, ∑ j, b i j)
      ≤ (1 + c1) * (∑ i, ‖C i‖^2) + c2 * (∑ i, s i) * (∑ j, s j) := by
    calc ∑ i, ∑ j, b i j
        ≤ ∑ i, ((1 + c1) * ‖C i‖^2 + c2 * s i * (∑ j, s j)) :=
          Finset.sum_le_sum (fun i _ => hper i)
      _ = (1 + c1) * (∑ i, ‖C i‖^2) + c2 * (∑ i, s i) * (∑ j, s j) := by
          rw [Finset.sum_add_distrib]
          have hA : (∑ i, (1 + c1) * ‖C i‖ ^ 2) = (1 + c1) * ∑ i, ‖C i‖ ^ 2 := by
            rw [Finset.mul_sum]
          have hB : (∑ i, c2 * s i * (∑ j, s j)) = c2 * (∑ i, s i) * (∑ j, s j) := by
            calc (∑ i, c2 * s i * (∑ j, s j))
                = (∑ i, c2 * s i) * (∑ j, s j) :=
                  (Finset.sum_mul (Finset.univ : Finset ι) (fun i => c2 * s i)
                    (∑ j, s j)).symm
              _ = c2 * (∑ i, s i) * (∑ j, s j) := by
                  rw [(Finset.mul_sum (Finset.univ : Finset ι) s c2).symm]
          rw [hA, hB]
  -- Cauchy–Schwarz.
  have hcs : (∑ i, s i) * (∑ j, s j) ≤ (∑ i, ‖C i‖^2) * (∑ i, wc i) := by
    have hmain := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
      (fun i => ‖C i‖) (fun i => Real.sqrt (wc i))
    simp only [hs] at hmain ⊢
    have hsquares : (∑ i, Real.sqrt (wc i) ^ 2) = (∑ i, wc i) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Real.sq_sqrt (hwc i)]
    rw [hsquares] at hmain
    have hsq : (∑ i, ‖C i‖ * Real.sqrt (wc i)) * (∑ j, ‖C j‖ * Real.sqrt (wc j))
        = (∑ i, ‖C i‖ * Real.sqrt (wc i)) ^ 2 := by ring
    rw [hsq]
    exact hmain
  calc (∑' n : ℕ, ‖∑ i, A n i * C i‖^2)
      ≤ ∑ i, ∑ j, b i j := hub
    _ ≤ (1 + c1) * (∑ i, ‖C i‖^2) + c2 * (∑ i, s i) * (∑ j, s j) := hsum'
    _ ≤ (1 + c1) * (∑ i, ‖C i‖^2) + c2 * ((∑ i, ‖C i‖^2) * (∑ i, wc i)) := by
          have h := mul_le_mul_of_nonneg_left hcs hc2
          have hrw : c2 * (∑ i, s i) * (∑ j, s j)
              = c2 * ((∑ i, s i) * (∑ j, s j)) := by ring
          rw [hrw]
          linarith [h]
    _ = (1 + c1) * (∑ i, ‖C i‖^2) + c2 * (∑ i, wc i) * (∑ i, ‖C i‖^2) := by ring

theorem hb15_operator_bound {q : ℕ} [NeZero q] {u w x : ℝ} {N : ℕ}
    {chi : Fin N → DirichletCharacter ℂ q} {rho : Fin N → ℂ} {wc : Fin N → ℝ} {c1 c2 : ℝ}
    (hwc : ∀ j, 0 ≤ wc j) (hc2 : 0 ≤ c2)
    (hwt : ∀ n : ℕ, 0 ≤ Work.LinnikAreas2.WT q u x n)
    (hdiag : ∀ j : Fin N, wc j * (∑' n : ℕ,
        ((∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM ((q:ℝ)^w) d : ℝ))^2
          * (n:ℝ)^(1 - 2*(rho j).re) * Work.LinnikAreas2.WT q u x n) ≤ 1 + c1)
    (hoff : ∀ j k : Fin N, j ≠ k → ‖∑' n : ℕ,
        ((((∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM ((q:ℝ)^w) d : ℝ)) : ℂ))^2
          * ((chi j * (chi k)⁻¹) (n : ZMod q))
          * ((n : ℂ) ^ ((1 : ℂ) - rho j - (starRingEnd ℂ (rho k))))
          * (((Work.LinnikAreas2.WT q u x n : ℝ)) : ℂ)‖ ≤ c2)
    (C : Fin N → ℂ) :
    (∑' n : ℕ, ‖∑ j : Fin N,
        Work.LinnikAreas2.acoef q u w x (chi j) (rho j) (wc j) n * C j‖ ^ 2)
      ≤ (1 + c1) * (∑ j : Fin N, ‖C j‖ ^ 2)
        + c2 * (∑ j : Fin N, wc j) * (∑ j : Fin N, ‖C j‖ ^ 2) := by
  classical
  refine l2_operator_bound
    (fun n (i : Fin N) => Work.LinnikAreas2.acoef q u w x (chi i) (rho i) (wc i) n)
    C wc hwc hc2 ?_ ?_ ?_
  · intro i j
    exact acoef_pair_summable (chi i) (chi j) (rho i) (rho j) (wc i) (wc j)
  · intro i
    exact acoef_diag_bound (chi i) (rho i) (hwc i) hwt (hdiag i)
  · intro i j hij
    exact acoef_offdiag_bound (chi i) (chi j) (rho i) (rho j) (hwc i) (hwc j) (hoff i j hij)

end

end Work.LinnikAreas2
