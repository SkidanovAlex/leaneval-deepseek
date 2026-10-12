import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1.BoxD1Pair
import Submission.Work.BoseFixB1.WinPair.WinChiFacts
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1

open MeasureTheory Filter

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- On the box the restricted window `winChi ℓ χ` coincides with `χ`, provided `χ` vanishes
off `A ⊆ acube ℓ`. -/
lemma winChi_eq_of_supp_subset {ℓ : ℝ} {A : Set E3} (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {χ : E3 → ℝ} (hχsupp : ∀ z, z ∉ A → χ z = 0) (z : E3) :
    winChi ℓ χ z = χ z := by
  by_cases hz : z ∈ Submission.BoseGases.acube ℓ
  · exact winChi_of_mem hz
  · rw [winChi_eq_zero hz, hχsupp z (fun h => hz (hAc h))]

-- NOTE for the prover: the model to follow is `Work.BoseFixB1.WinPair.integrable_winDens_mul`
-- (`Submission/Work/BoseFixB1/WinPair/winPairForm_eq_densityIntegral.lean`), which is this
-- statement with `wScaled s (g₀ v h)` in place of `W` and `winDens` in place of `boxPairDens`.
-- In particular `winChi ℓ χ = χ` pointwise here, because `χ` vanishes off `A ⊆ acube ℓ`
-- (`hχsupp`, `hAc`), so `hInt` transfers to the plain-`χ` joint integrand.
theorem integrable_W_mul_boxPairDens {N : ℕ} {ℓ volA : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hℓ : 0 < ℓ) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχsupp : ∀ z, z ∉ A → χ z = 0)
    {Φ : Submission.BoseGases.X (N + 2) → ℝ} {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    {i j : Fin (N + 2)} (hij : i ≠ j)
    (hInt : MeasureTheory.Integrable (Function.uncurry (fun y u : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseFixB1.winChi ℓ χ y * W u * Work.BoseFixB1.winChi ℓ χ (y - u)
        * Work.BoseFixB1.boxPairFibreFun volA ℓ A Φ i j y (y - u)))
      (MeasureTheory.volume.prod MeasureTheory.volume)) :
    MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
      W u * Work.BoseFixB1.boxPairDens volA ℓ A χ Φ i j u) MeasureTheory.volume := by
  have hwin : ∀ z : E3, winChi ℓ χ z = χ z := winChi_eq_of_supp_subset hAc hχsupp
  -- Fubini: the marginal of the jointly integrable substitution integrand
  have h0 : MeasureTheory.Integrable (fun u : E3 => ∫ y,
      winChi ℓ χ y * W u * winChi ℓ χ (y - u)
        * boxPairFibreFun volA ℓ A Φ i j y (y - u)) MeasureTheory.volume :=
    hInt.integral_prod_right
  refine h0.congr ?_
  filter_upwards with u
  rw [boxPairDens]
  -- pull the `u`-dependent constant `W u` out of the inner integral
  have h2 : (∫ y, winChi ℓ χ y * W u * winChi ℓ χ (y - u)
        * boxPairFibreFun volA ℓ A Φ i j y (y - u))
      = W u * ∫ y, winChi ℓ χ y * winChi ℓ χ (y - u)
        * boxPairFibreFun volA ℓ A Φ i j y (y - u) := by
    rw [show (∫ y, winChi ℓ χ y * W u * winChi ℓ χ (y - u)
          * boxPairFibreFun volA ℓ A Φ i j y (y - u))
        = ∫ y, W u * (winChi ℓ χ y * winChi ℓ χ (y - u)
            * boxPairFibreFun volA ℓ A Φ i j y (y - u)) from
      MeasureTheory.integral_congr_ae (Eventually.of_forall fun y => by ring)]
    rw [MeasureTheory.integral_const_mul]
  rw [h2]
  congr 1
  -- shift the `y`-integral by `u` (translation invariance of Lebesgue measure)
  have hshift : (∫ y, winChi ℓ χ y * winChi ℓ χ (y - u)
        * boxPairFibreFun volA ℓ A Φ i j y (y - u))
      = ∫ z, winChi ℓ χ (z + u) * winChi ℓ χ z
        * boxPairFibreFun volA ℓ A Φ i j (z + u) z := by
    rw [← MeasureTheory.integral_add_right_eq_self
      (fun w : E3 => winChi ℓ χ w * winChi ℓ χ (w - u)
        * boxPairFibreFun volA ℓ A Φ i j w (w - u)) u]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [add_sub_cancel_right]
  rw [hshift]
  -- `winChi ℓ χ = χ` pointwise
  have hchi : (∫ z, winChi ℓ χ (z + u) * winChi ℓ χ z
        * boxPairFibreFun volA ℓ A Φ i j (z + u) z)
      = ∫ z, χ (z + u) * χ z
        * boxPairFibreFun volA ℓ A Φ i j (z + u) z := by
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [hwin (z + u), hwin z]
  rw [hchi]
  -- the full-space integral collapses onto `A`, since `χ` vanishes off `A`
  exact (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun z hz => by rw [hχsupp z hz]; ring)).symm

end Work.BoseFixB1
