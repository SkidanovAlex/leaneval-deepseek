import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstDefs
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstAux.ZetaBound
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.PhiStar.Honesty.CptApp.Est.MixedSlotAux
import Submission.Work.FTS.PhiStar.Honesty.CptApp.Est.MixedSlotCore

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.CptApp.Est

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000


/-- **The moment group.** The single product `D_z^j μ · D_θ^i ρ · Wt` is bounded in square by
`Good`: the radial factor is one term of the first sum of the third group of `Good`, and the
angular factor is one term of `rhoProf`. -/
theorem ems_moment_sq_le (α : ℝ) (k n : ℕ) (F : ℝ → ℝ → ℝ) {i j : ℕ} (hi : i ≤ k) (hj : j ≤ k)
    {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.DzIter j (fun z _ : ℝ => mu n F z) z 0
        * Work.Spaces.DthIter i (fun _ θ : ℝ => rho θ) 0 θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ Good α k n F z θ := by
  have hgnn : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  have hWt2 := ems_Wt_sq (α := α) (z := z) (θ := θ) hgnn
  have hM : (Work.Spaces.DzIter j (fun z _ : ℝ => mu n F z) z 0) ^ 2
      ≤ ∑ m ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter m (fun z' _ : ℝ => mu n F z') z 0) ^ 2 :=
    Finset.single_le_sum (f := fun m => (Work.Spaces.DzIter m (fun z' _ : ℝ => mu n F z') z 0) ^ 2)
      (fun m _ => sq_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  have hR : (Work.Spaces.DthIter i (fun _ θ : ℝ => rho θ) 0 θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) ≤ rhoProf α k θ := by
    rw [rhoProf]
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun i' => (Work.Spaces.DthIter i' (fun _ θ' : ℝ => rho θ') 0 θ) ^ 2
        * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            + (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
      (fun i' _ => mul_nonneg (sq_nonneg _)
        (add_nonneg (Real.rpow_nonneg hgnn _) (Real.rpow_nonneg hgnn _)))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi)))
    exact mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (Real.rpow_nonneg hgnn _)) (sq_nonneg _)
  calc (Work.Spaces.DzIter j (fun z _ : ℝ => mu n F z) z 0
        * Work.Spaces.DthIter i (fun _ θ : ℝ => rho θ) 0 θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.DzIter j (fun z _ : ℝ => mu n F z) z 0) ^ 2
          * ((Work.Spaces.DthIter i (fun _ θ : ℝ => rho θ) 0 θ) ^ 2
              * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
        rw [show (Work.Spaces.DzIter j (fun z _ : ℝ => mu n F z) z 0
              * Work.Spaces.DthIter i (fun _ θ : ℝ => rho θ) 0 θ * Work.Spaces.Wt α z θ) ^ 2
            = (Work.Spaces.DzIter j (fun z _ : ℝ => mu n F z) z 0) ^ 2
              * (Work.Spaces.DthIter i (fun _ θ : ℝ => rho θ) 0 θ
                  * Work.Spaces.Wt α z θ) ^ 2 from by ring,
          mul_pow, hWt2]
        ring
    _ ≤ (∑ m ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter m (fun z' _ : ℝ => mu n F z') z 0) ^ 2)
          * ((Work.Spaces.DthIter i (fun _ θ : ℝ => rho θ) 0 θ) ^ 2
              * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :=
        mul_le_mul_of_nonneg_right hM
          (mul_nonneg (mul_nonneg (sq_nonneg _) hw2)
            (Real.rpow_nonneg hgnn _))
    _ = (∑ m ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter m (fun z' _ : ℝ => mu n F z') z 0) ^ 2)
          * ((Work.Spaces.w z) ^ 2
              * ((Work.Spaces.DthIter i (fun _ θ : ℝ => rho θ) 0 θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := by ring
    _ ≤ (∑ m ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter m (fun z' _ : ℝ => mu n F z') z 0) ^ 2)
          * ((Work.Spaces.w z) ^ 2 * rhoProf α k θ) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hR hw2)
          (Finset.sum_nonneg fun m _ => sq_nonneg _)
    _ ≤ Good α k n F z θ := by
        rw [Good]
        refine le_add_of_nonneg_left (add_nonneg (omegaPart_nonneg α k n F z θ) ?_)
        exact mul_nonneg (thShrink_nonneg n θ) (hkZsum_nonneg α k F z hθ)


theorem ems_Wt_eq_zero_of_z_eq_zero (α θ : ℝ) : Work.Spaces.Wt α 0 θ = 0 := by
  rw [Work.Spaces.Wt, ems_w_zero, zero_mul]

theorem ems_Wt_eq_zero_of_sin_eq_zero {α z θ : ℝ} (hα : 0 < α)
    (hs : Real.sin (2 * θ) = 0) : Work.Spaces.Wt α z θ = 0 := by
  rw [Work.Spaces.Wt, ems_wTheta_zero_of_sin_eq_zero (ne_of_gt (Work.Spaces.gam_pos hα)) hs,
    mul_zero]

/-- **Assembly.**  From the Leibniz expansion of `mixed j i (err n F)` and the two
coefficient bounds, the pointwise estimate follows: the `(ζχ-1)F`-group is bounded by
`C₁·Good` (the `Ω_n`/`thShrink` dichotomy), the moment group by `Good`, and the two are
combined with `(x-y)² ≤ 2x² + 2y²`; the boundary cases (`z = 0` or `sin 2θ = 0`) are trivial
because `Wt` vanishes there. -/
theorem ems_final_of (k : ℕ) (Base : ℝ) (hBase : 1 ≤ Base)
    (hCoeffInd : ∀ (n a b : ℕ), 2 ≤ n → 1 ≤ a + b → a ≤ k → b ≤ k → ∀ z θ : ℝ,
      (Work.Spaces.mixed b a (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
          * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ) ^ 2
        ≤ Base * Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ)
    (hCoeffTs : ∀ (n a b : ℕ), 2 ≤ n → 1 ≤ a → a ≤ k → b ≤ k → ∀ z θ : ℝ,
      (Work.Spaces.mixed b a (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
          * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ) ^ 2
        ≤ Base * Work.FTS.PhiStar.Honesty.CptApp.thShrink n θ)
    (hexp : ∀ (n : ℕ), 2 ≤ n → ∀ (F : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen F →
      ∀ (j i : ℕ) (z θ : ℝ), 0 < z → 0 < θ → θ < Real.pi / 2 →
        Work.Spaces.mixed j i (Work.FTS.PhiStar.Honesty.CptApp.err n F) z θ
          = (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
                ((i.choose a : ℝ) * (j.choose b : ℝ))
                  * (Work.Spaces.mixed b a (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
                        * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ
                     * Work.Spaces.mixed (j - b) (i - a) F z θ))
              - Work.Spaces.DzIter j
                  (fun z _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z) z 0
                * Work.Spaces.DthIter i
                    (fun _ θ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.rho θ) 0 θ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (n : ℕ) (F : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 → 3 ≤ n →
        Work.FTS.EllipticEst.SmoothOpen F →
        ∀ (i j : ℕ), 1 ≤ i → i + j ≤ k → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
          (Work.Spaces.mixed j i (Work.FTS.PhiStar.Honesty.CptApp.err n F) z θ
              * Work.Spaces.Wt α z θ) ^ 2
            ≤ C * Work.FTS.PhiStar.Honesty.CptApp.Good α k n F z θ := by
  obtain ⟨C1, hC1pos, hC1⟩ := ems_prod_sq_le k Base hBase hCoeffInd hCoeffTs
  refine ⟨2 * C1 + 2, by linarith, ?_⟩
  intro α n F hα hα1 hn3 hF i j hi hij z hz θ hθ
  have hmemz : z ∈ Work.Spaces.Iz := hz
  have hmemθ : θ ∈ Work.Spaces.Iθ := hθ
  have hz' : (0 : ℝ) ≤ z := by
    rw [Work.Spaces.Iz, Set.mem_Ici] at hz; exact hz
  have hθ' : 0 ≤ θ ∧ θ ≤ Real.pi / 2 := by
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ; exact hθ
  have hn2 : 2 ≤ n := by omega
  have hG : 0 ≤ Good α k n F z θ := Good_nonneg α k n F hmemθ
  by_cases hWt0 : Work.Spaces.Wt α z θ = 0
  · rw [hWt0, mul_zero, sq, mul_zero]
    exact mul_nonneg (by linarith) hG
  · have hz0 : 0 < z := by
      rcases lt_or_eq_of_le hz' with h | h
      · exact h
      · exact absurd (by rw [← h]; exact ems_Wt_eq_zero_of_z_eq_zero α θ) hWt0
    have hθ0 : 0 < θ := by
      rcases lt_or_eq_of_le hθ'.1 with h | h
      · exact h
      · exact absurd (by rw [← h]; exact ems_Wt_eq_zero_of_sin_eq_zero hα (by norm_num)) hWt0
    have hθ1 : θ < Real.pi / 2 := by
      rcases lt_or_eq_of_le hθ'.2 with h | h
      · exact h
      · exact absurd (by rw [h]; exact ems_Wt_eq_zero_of_sin_eq_zero hα (by
          rw [show 2 * (Real.pi / 2) = Real.pi from by ring, Real.sin_pi])) hWt0
    have hexp' := hexp n hn2 F hF j i z θ hz0 hθ0 hθ1
    have hS1 := hC1 α n F hα hn2 i j hi hij z hmemz θ hmemθ
    have hS2 : (Work.Spaces.DzIter j (fun z _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z)
            z 0
          * Work.Spaces.DthIter i (fun _ θ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.rho θ) 0 θ
          * Work.Spaces.Wt α z θ) ^ 2 ≤ Good α k n F z θ :=
      ems_moment_sq_le α k n F (by omega) (by omega) hmemθ
    set X : ℝ := (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
        ((i.choose a : ℝ) * (j.choose b : ℝ))
          * (Work.Spaces.mixed b a (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
                * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ
             * Work.Spaces.mixed (j - b) (i - a) F z θ)) * Work.Spaces.Wt α z θ with hX
    set Y : ℝ := (Work.Spaces.DzIter j
          (fun z _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z) z 0
        * Work.Spaces.DthIter i (fun _ θ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.rho θ) 0 θ)
        * Work.Spaces.Wt α z θ with hY
    have hX2 : X ^ 2 ≤ C1 * Good α k n F z θ := by rw [hX]; exact hS1
    have hY2 : Y ^ 2 ≤ Good α k n F z θ := by rw [hY]; exact hS2
    have hXY : ((∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            ((i.choose a : ℝ) * (j.choose b : ℝ))
              * (Work.Spaces.mixed b a (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
                    * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ
                 * Work.Spaces.mixed (j - b) (i - a) F z θ))
          - Work.Spaces.DzIter j
              (fun z _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z) z 0
            * Work.Spaces.DthIter i (fun _ θ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.rho θ) 0 θ)
          * Work.Spaces.Wt α z θ = X - Y := by
      rw [hX, hY]; ring
    rw [hexp', hXY]
    calc (X - Y) ^ 2 ≤ 2 * X ^ 2 + 2 * Y ^ 2 := by nlinarith [sq_nonneg (X + Y)]
      _ ≤ 2 * (C1 * Good α k n F z θ) + 2 * Good α k n F z θ := by linarith
      _ = (2 * C1 + 2) * Good α k n F z θ := by ring

end Work.FTS.PhiStar.Honesty.CptApp.Est
