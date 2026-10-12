import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.BoxPotOper
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory
open scoped BigOperators

/-- **`boxQSum ≥ boxQ₀` on the box-flat states.**  If every FS box-mean-free projection
`Q_{B,i}Φ` vanishes a.e. on `abox N ℓ`, and so does every `P_i(Q_jΦ)` (`i ≠ j`), then the cross
words `boxQ₁`, `boxQ₂`, `boxQ₃` vanish: every integrand factor is `Q_iΦ`, or `P_i(Q_jΦ)`, or one
of their orientation swaps (`BoxPotOper.boxQPswap` `Q_jP_i = P_iQ_j`,
`BoxPotOper.boxQQswap` `Q_jQ_i = Q_iQ_j`) applied to an a.e.-vanishing state — note that for the
`Q_jQ_iΦ` factor one may either use the swap or the definitional
`Q_j(Q_iΦ) = 1_A(x_j)Q_iΦ − P_j(Q_iΦ)` together with `boxQInd` of an a.e.-zero state vanishing a.e.
(one slice step).  `boxQ₄ ≥ 0` is the manifest square against `w ≥ 0` pointwise.  Hence
`boxQSum = boxQ₀ + … + boxQ₄ ≥ boxQ₀`. -/
theorem boxQSum_ge_boxQ0_of_boxQInd_ae_zero {N : ℕ} {ℓ volA μ : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) {Φ : Submission.BoseGases.X N → ℝ}
    (hΦc : Continuous Φ)
    (hQ : ∀ i : Fin N, Work.UBBInputs8.boxQInd volA A i Φ
        =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)] 0)
    (hP : ∀ (i j : Fin N), i ≠ j → Work.UBBInputs8.boxPInd volA A i
        (Work.UBBInputs8.boxQInd volA A j Φ)
        =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)] 0)
    {w w1 w2 om : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hw : ∀ x y, 0 ≤ w x y) :
    Work.BoseFixB1S.boxQ0 volA ℓ μ A w1 w2 Φ
      ≤ Work.BoseFixB1S.boxQSum volA ℓ μ A w w1 w2 om Φ := by
  -- The structural hypotheses of the interface (not needed by this argument, which only uses the
  -- two a.e.-vanishing hypotheses and `0 ≤ w`); kept referenced so the statement is untouched.
  have _hkeep : 0 < ℓ ∧ 0 < volA ∧ MeasurableSet A ∧ volA = (MeasureTheory.volume A).toReal
      ∧ A ⊆ Submission.BoseGases.acube ℓ ∧ Continuous Φ :=
    ⟨hℓ, hvol, hA, hvolA, hAc, hΦc⟩
  -- `Q_j(Q_iΦ)` vanishes a.e. for `i ≠ j`: definitionally it is `1_A(x_j)·(Q_iΦ) − P_j(Q_iΦ)`,
  -- and both terms vanish a.e. (`hQ i`, `hP j i`).
  have hQQ : ∀ (i j : Fin N), i ≠ j →
      (fun x : Submission.BoseGases.X N =>
        Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x)
        =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)] 0 := by
    intro i j hij
    filter_upwards [hQ i, hP j i hij.symm] with x hx hpx
    rw [Work.BoseFixB1S.boxQInd_eq, hx, hpx]
    simp
  -- pairs in `pairSet` have distinct slots
  have hne_of_mem : ∀ p ∈ Submission.BoseGases.pairSet N, p.1 ≠ p.2 := by
    intro p hp
    have hp' := hp
    simp only [Submission.BoseGases.pairSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp'
    exact hp'
  -- ## The `boxQ₁` integrands vanish a.e.
  have hA1 : ∀ p ∈ Submission.BoseGases.pairSet N,
      (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x)
          * w2 (x p.1) (x p.2))
        =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)] 0 := by
    intro p hp
    filter_upwards [hP p.1 p.2 (hne_of_mem p hp)] with x hx
    rw [hx]
    simp
  have hA2 : ∀ i : Fin N,
      (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxQInd volA A i Φ x) * (Work.UBBInputs8.boxPInd volA A i Φ x)
          * Submission.BoseGases.w1Fibre ℓ w1 (x i))
        =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)] 0 := by
    intro i
    filter_upwards [hQ i] with x hx
    rw [hx]
    simp
  -- ## The `boxQ₂` integrands vanish a.e.
  have hB1 : ∀ p ∈ Submission.BoseGases.pairSet N,
      (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxPInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
          * w2 (x p.1) (x p.2))
        =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)] 0 := by
    intro p hp
    filter_upwards [hP p.1 p.2 (hne_of_mem p hp)] with x hx
    rw [hx]
    simp
  have hB2 : ∀ p ∈ Submission.BoseGases.pairSet N,
      (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxPInd volA A p.1 Φ) x)
          * w2 (x p.1) (x p.2))
        =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)] 0 := by
    intro p hp
    filter_upwards [hP p.1 p.2 (hne_of_mem p hp)] with x hx
    rw [hx]
    simp
  have hB3 : ∀ i : Fin N,
      (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2 * Submission.BoseGases.w1Fibre ℓ w1 (x i))
        =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)] 0 := by
    intro i
    filter_upwards [hQ i] with x hx
    rw [hx]
    simp
  have hB4 : ∀ p ∈ Submission.BoseGases.pairSet N,
      (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
          * w1 (x p.1) (x p.2))
        =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)] 0 := by
    intro p hp
    filter_upwards [hQQ p.1 p.2 (hne_of_mem p hp)] with x hx
    rw [hx]
    simp
  -- ## The `boxQ₃` integrand vanishes a.e.
  have hC1 : ∀ p ∈ Submission.BoseGases.pairSet N,
      (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
          * w1 (x p.1) (x p.2))
        =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)] 0 := by
    intro p hp
    filter_upwards [hP p.1 p.2 (hne_of_mem p hp)] with x hx
    rw [hx]
    simp
  -- ## The words `boxQ₁`, `boxQ₂`, `boxQ₃` vanish
  have hAe (F : Submission.BoseGases.X N → ℝ)
      (hF : F =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)] 0) :
      (∫ x in Submission.BoseGases.abox N ℓ, F x) = 0 := by
    rw [MeasureTheory.integral_congr_ae hF]
    simp
  have hQ1 : Work.BoseFixB1S.boxQ1 volA ℓ μ A w1 w2 Φ = 0 := by
    unfold Work.BoseFixB1S.boxQ1
    rw [Finset.sum_eq_zero (fun p hp => hAe _ (hA1 p hp)),
      Finset.sum_eq_zero (fun i _ => hAe _ (hA2 i))]
    ring
  have hQ2 : Work.BoseFixB1S.boxQ2 volA ℓ μ A w1 w2 Φ = 0 := by
    unfold Work.BoseFixB1S.boxQ2
    rw [Finset.sum_eq_zero (fun p hp => hAe _ (hB1 p hp)),
      Finset.sum_eq_zero (fun p hp => hAe _ (hB2 p hp)),
      Finset.sum_eq_zero (fun i _ => hAe _ (hB3 i)),
      Finset.sum_eq_zero (fun p hp => hAe _ (hB4 p hp))]
    ring
  have hQ3 : Work.BoseFixB1S.boxQ3 volA ℓ A w1 Φ = 0 := by
    unfold Work.BoseFixB1S.boxQ3
    rw [Finset.sum_eq_zero (fun p hp => hAe _ (hC1 p hp))]
    ring
  -- ## `boxQ₄ ≥ 0` (the manifest square against the pointwise-nonnegative kernel)
  have hQ4 : 0 ≤ Work.BoseFixB1S.boxQ4 volA ℓ A w om Φ := by
    unfold Work.BoseFixB1S.boxQ4
    refine mul_nonneg (by norm_num) (Finset.sum_nonneg (fun p _ => ?_))
    refine MeasureTheory.integral_nonneg (fun x => ?_)
    have hw' : 0 ≤ w (x p.1) (x p.2) := hw _ _
    positivity
  -- ## Assembly
  have hsum_eq : Work.BoseFixB1S.boxQSum volA ℓ μ A w w1 w2 om Φ
      = Work.BoseFixB1S.boxQ0 volA ℓ μ A w1 w2 Φ + Work.BoseFixB1S.boxQ1 volA ℓ μ A w1 w2 Φ
        + Work.BoseFixB1S.boxQ2 volA ℓ μ A w1 w2 Φ + Work.BoseFixB1S.boxQ3 volA ℓ A w1 Φ
        + Work.BoseFixB1S.boxQ4 volA ℓ A w om Φ := rfl
  rw [hsum_eq, hQ1, hQ2, hQ3]
  linarith [hQ4]

end Work.BoseFixB1S
