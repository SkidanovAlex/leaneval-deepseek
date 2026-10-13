import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Series.BslOp.Bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **Termwise differentiation of the mode series.**  Under the six pointwise bounds, the first and
second `z`-derivatives, the first and second `θ`-derivatives and the `θ`-derivative of
`tan θ · psiSeries` are the corresponding termwise series. -/
theorem deriv_series (α : ℝ) (ψ : ℝ → ℝ) (hα : 0 < α)
    (hInt : (∀ m : ℕ, ContinuousOn (fun t => cmode m (RemSource α ψ) t) (Set.Ioi 0)) ∧
      (∀ m : ℕ, MeasureTheory.IntegrableOn
        (fun t => cmode m (RemSource α ψ) t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
        (Set.Ioo 0 1)) ∧
      (∀ m : ℕ, MeasureTheory.IntegrableOn
        (fun t => cmode m (RemSource α ψ) t * t ^ (-(2 * (m : ℝ) / α) - 1))
        (Set.Ioi 1)) ∧
      ContinuousOn (VocabO.phiA α) (Set.Ioi 0) ∧
      (∀ m : ℕ, MeasureTheory.IntegrableOn
        (fun t => VocabO.phiA α t * t ^ ((2 * (m : ℝ) + 5) / α - 1)) (Set.Ioo 0 1)) ∧
      (∀ m : ℕ, MeasureTheory.IntegrableOn
        (fun t => VocabO.phiA α t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 1)))
    (hmaj : ∀ D : ℝ, Summable fun m : ℕ => D * majPow m)
    (z : ℝ) (hz : 0 < z) (θ : ℝ) (hθ : 0 < θ) (hθ2 : θ < π / 2)
    (D : ℝ)
    (hB0 : ∀ m : ℕ, ∀ y : ℝ, 0 < y →
      |acoeff α m (RemSource α ψ) y| * |Gegenbauer.eFam m θ| ≤ D * majPow m)
    (hB1 : ∀ m : ℕ, ∀ y : ℝ, 0 < y →
      |deriv (acoeff α m (RemSource α ψ)) y| * |Gegenbauer.eFam m θ| ≤ D * majPow m)
    (hB2 : ∀ m : ℕ, ∀ y : ℝ, 0 < y →
      |deriv (deriv (acoeff α m (RemSource α ψ))) y| * |Gegenbauer.eFam m θ| ≤ D * majPow m)
    (hB3 : ∀ m : ℕ, ∀ y : ℝ, 0 < y → y ≤ (θ + π / 2) / 2 →
      |acoeff α m (RemSource α ψ) z| * |deriv (Gegenbauer.eFam m) y| ≤ D * majPow m)
    (hB4 : ∀ m : ℕ, ∀ y : ℝ, 0 < y → y ≤ (θ + π / 2) / 2 →
      |acoeff α m (RemSource α ψ) z| * |iteratedDeriv 2 (Gegenbauer.eFam m) y| ≤ D * majPow m)
    (hB5 : ∀ m : ℕ, ∀ y : ℝ, 0 < y → y ≤ (θ + π / 2) / 2 →
      |acoeff α m (RemSource α ψ) z|
        * |deriv (fun θ' => Real.tan θ' * Gegenbauer.eFam m θ') y| ≤ D * majPow m) :
    Spaces.pz (fun z θ => psiSeries α (RemSource α ψ) z θ) z θ
        = ∑' m : ℕ, deriv (acoeff α m (RemSource α ψ)) z * Gegenbauer.eFam m θ ∧
      Spaces.pzIter 2 (fun z θ => psiSeries α (RemSource α ψ) z θ) z θ
        = ∑' m : ℕ, deriv (deriv (acoeff α m (RemSource α ψ))) z * Gegenbauer.eFam m θ ∧
      Spaces.pth (fun z θ => psiSeries α (RemSource α ψ) z θ) z θ
        = ∑' m : ℕ, acoeff α m (RemSource α ψ) z * deriv (Gegenbauer.eFam m) θ ∧
      Spaces.pthIter 2 (fun z θ => psiSeries α (RemSource α ψ) z θ) z θ
        = ∑' m : ℕ, acoeff α m (RemSource α ψ) z * iteratedDeriv 2 (Gegenbauer.eFam m) θ ∧
      Spaces.pth (fun z' θ' => Real.tan θ' * psiSeries α (RemSource α ψ) z' θ') z θ
        = ∑' m : ℕ, acoeff α m (RemSource α ψ) z
            * deriv (fun θ' => Real.tan θ' * Gegenbauer.eFam m θ') θ ∧
      (Elliptic.Lzero (fun z θ => psiSeries α (RemSource α ψ) z θ) z θ
        = -Spaces.pthIter 2 (fun z θ => psiSeries α (RemSource α ψ) z θ) z θ
          + Spaces.pth (fun z' θ' => Real.tan θ' * psiSeries α (RemSource α ψ) z' θ') z θ
          - 6 * psiSeries α (RemSource α ψ) z θ) := by
  have hθu_eq : (θ + Real.pi / 2) / 2 = (θ + π / 2) / 2 := rfl
  set θu : ℝ := (θ + π / 2) / 2 with hθu
  have hθu_lt : θu < π / 2 := by rw [hθu]; linarith [hθ2]
  have hcθ : 0 < Real.cos θu :=
    Real.cos_pos_of_mem_Ioo ⟨by rw [hθu]; linarith [Real.pi_pos], hθu_lt⟩
  have hdiffA : ∀ m : ℕ,
      (∀ y, 0 < y → HasDerivAt (gammaFun α m) (rgiD1 α m (VocabO.phiA α) y) y) ∧
      (∀ y, 0 < y →
        HasDerivAt (deriv (gammaFun α m)) (deriv (rgiD1 α m (VocabO.phiA α)) y) y) :=
    fun m => hasDerivAt_gammaFun hα m hInt.2.2.2.1 (hInt.2.2.2.2.1 m) (hInt.2.2.2.2.2 m)
  have hderA : ∀ m : ℕ,
      (∀ y, 0 < y → HasDerivAt (acoeff α m (RemSource α ψ))
        (α ^ 2 * bmode m ψ * rgiD1 α m (VocabO.phiA α) y) y) ∧
      (∀ y, 0 < y → HasDerivAt (deriv (acoeff α m (RemSource α ψ)))
        (α ^ 2 * bmode m ψ * deriv (rgiD1 α m (VocabO.phiA α)) y) y) :=
    fun m => hasDerivAt_acoeff m (hdiffA m).1 (hdiffA m).2
  -- summability of the majorant and of the mode families
  have hsum_maj : Summable fun m : ℕ => D * majPow m := hmaj D
  have hsum_of : ∀ (E : ℝ) (f : ℕ → ℝ), (∀ m, |f m| ≤ E * majPow m) → Summable f := by
    intro E f hf
    refine Summable.of_norm_bounded (hmaj E) fun m => ?_
    rw [Real.norm_eq_abs]
    exact hf m
  -- the derivative identities
  have hz_sub : Set.Ioo (z / 2) (2 * z) ⊆ Set.Ioi 0 := by
    intro y hy; exact lt_trans (by linarith [hz]) hy.1
  have hθ_sub : Set.Ioo (θ / 2) θu ⊆ Set.Ioi 0 := by
    intro y hy; exact lt_trans (by linarith [hθ]) hy.1
  have hθub : ∀ y ∈ Set.Ioo (θ / 2) θu, y ≤ θu := fun y hy => le_of_lt hy.2
  have hθle : θ ≤ (θ + π / 2) / 2 := by linarith [hθ2]
  have hZ1 : ∀ y ∈ Set.Ioo (z / 2) (2 * z),
      HasDerivAt (fun y' => psiSeries α (RemSource α ψ) y' θ)
        (∑' m : ℕ, deriv (acoeff α m (RemSource α ψ)) y * Gegenbauer.eFam m θ) y := by
    intro y hy
    have hmain : HasDerivAt
        (fun y' => ∑' m : ℕ, acoeff α m (RemSource α ψ) y' * Gegenbauer.eFam m θ)
        (∑' m : ℕ, deriv (acoeff α m (RemSource α ψ)) y * Gegenbauer.eFam m θ) y := by
      refine hasDerivAt_tsum_of_isPreconnected (𝕜 := ℝ) (F := ℝ)
        (u := fun m => D * majPow m)
        (g := fun m y' => acoeff α m (RemSource α ψ) y' * Gegenbauer.eFam m θ)
        (g' := fun m y' => deriv (acoeff α m (RemSource α ψ)) y' * Gegenbauer.eFam m θ)
        hsum_maj isOpen_Ioo isPreconnected_Ioo ?_ ?_
        (y₀ := z) ⟨by linarith [hz], by linarith [hz]⟩ ?_ hy
      · intro m y' hy'
        refine (((hderA m).1 y' (hz_sub hy')).mul_const (Gegenbauer.eFam m θ)).congr_deriv ?_
        rw [deriv_acoeff m (hdiffA m).1 y' (hz_sub hy')]
      · intro m y' hy'
        rw [Real.norm_eq_abs, abs_mul]
        exact hB1 m y' (hz_sub hy')
      · exact hsum_of D _ (fun m => by rw [abs_mul]; exact hB0 m z hz)
    have heq : (fun y' => psiSeries α (RemSource α ψ) y' θ)
        = fun y' => ∑' m : ℕ, acoeff α m (RemSource α ψ) y' * Gegenbauer.eFam m θ := rfl
    rw [heq]
    exact hmain
  have hZ2 : ∀ y ∈ Set.Ioo (z / 2) (2 * z),
      HasDerivAt (fun y' => ∑' m : ℕ,
          deriv (acoeff α m (RemSource α ψ)) y' * Gegenbauer.eFam m θ)
        (∑' m : ℕ, deriv (deriv (acoeff α m (RemSource α ψ))) y
          * Gegenbauer.eFam m θ) y := by
    intro y hy
    refine hasDerivAt_tsum_of_isPreconnected (𝕜 := ℝ) (F := ℝ)
      (u := fun m => D * majPow m)
      (g := fun m y' => deriv (acoeff α m (RemSource α ψ)) y' * Gegenbauer.eFam m θ)
      (g' := fun m y' => deriv (deriv (acoeff α m (RemSource α ψ))) y'
        * Gegenbauer.eFam m θ)
      hsum_maj isOpen_Ioo isPreconnected_Ioo ?_ ?_
      (y₀ := z) ⟨by linarith [hz], by linarith [hz]⟩ ?_ hy
    · intro m y' hy'
      refine (((hderA m).2 y' (hz_sub hy')).mul_const (Gegenbauer.eFam m θ)).congr_deriv ?_
      rw [deriv_deriv_acoeff m (hdiffA m).1 (hdiffA m).2 y' (hz_sub hy')]
    · intro m y' hy'
      rw [Real.norm_eq_abs, abs_mul]
      exact hB2 m y' (hz_sub hy')
    · exact hsum_of D _ (fun m => by rw [abs_mul]; exact hB1 m z hz)
  have hT1 : ∀ y ∈ Set.Ioo (θ / 2) θu,
      HasDerivAt (fun y' => psiSeries α (RemSource α ψ) z y')
        (∑' m : ℕ, acoeff α m (RemSource α ψ) z * deriv (Gegenbauer.eFam m) y) y := by
    intro y hy
    have hmain : HasDerivAt
        (fun y' => ∑' m : ℕ, acoeff α m (RemSource α ψ) z * Gegenbauer.eFam m y')
        (∑' m : ℕ, acoeff α m (RemSource α ψ) z * deriv (Gegenbauer.eFam m) y) y := by
      refine hasDerivAt_tsum_of_isPreconnected (𝕜 := ℝ) (F := ℝ)
        (u := fun m => D * majPow m)
        (g := fun m y' => acoeff α m (RemSource α ψ) z * Gegenbauer.eFam m y')
        (g' := fun m y' => acoeff α m (RemSource α ψ) z * deriv (Gegenbauer.eFam m) y')
        hsum_maj isOpen_Ioo isPreconnected_Ioo ?_ ?_
        (y₀ := θ) ⟨by linarith [hθ], by rw [hθu]; linarith [hθ2]⟩ ?_ hy
      · intro m y' hy'
        have hd : HasDerivAt (fun θ' => Gegenbauer.eFam m θ')
            (deriv (Gegenbauer.eFam m) y') y' :=
          ((contDiff_eFam m).differentiable (by norm_num)).differentiableAt.hasDerivAt
        exact hd.const_mul _
      · intro m y' hy'
        rw [Real.norm_eq_abs, abs_mul]
        exact hB3 m y' (hθ_sub hy') (hθub y' hy')
      · exact hsum_of D _ (fun m => by rw [abs_mul]; exact hB0 m z hz)
    have heq : (fun y' => psiSeries α (RemSource α ψ) z y')
        = fun y' => ∑' m : ℕ, acoeff α m (RemSource α ψ) z * Gegenbauer.eFam m y' := rfl
    rw [heq]
    exact hmain
  have hT2 : ∀ y ∈ Set.Ioo (θ / 2) θu,
      HasDerivAt (fun y' => ∑' m : ℕ,
          acoeff α m (RemSource α ψ) z * deriv (Gegenbauer.eFam m) y')
        (∑' m : ℕ, acoeff α m (RemSource α ψ) z * iteratedDeriv 2 (Gegenbauer.eFam m) y) y := by
    intro y hy
    refine hasDerivAt_tsum_of_isPreconnected (𝕜 := ℝ) (F := ℝ)
      (u := fun m => D * majPow m)
      (g := fun m y' => acoeff α m (RemSource α ψ) z * deriv (Gegenbauer.eFam m) y')
      (g' := fun m y' => acoeff α m (RemSource α ψ) z
        * iteratedDeriv 2 (Gegenbauer.eFam m) y')
      hsum_maj isOpen_Ioo isPreconnected_Ioo ?_ ?_
      (y₀ := θ) ⟨by linarith [hθ], by rw [hθu]; linarith [hθ2]⟩ ?_ hy
    · intro m y' hy'
      have hd : HasDerivAt (fun θ' => deriv (Gegenbauer.eFam m) θ')
          (deriv (deriv (Gegenbauer.eFam m)) y') y' :=
        ((ContDiff.deriv' (n := 2) (contDiff_eFam m)).differentiable
          (by norm_num)).differentiableAt.hasDerivAt
      have h := hd.const_mul (acoeff α m (RemSource α ψ) z)
      simpa only [iteratedDeriv_two_apply, mul_comm] using h
    · intro m y' hy'
      rw [Real.norm_eq_abs, abs_mul]
      exact hB4 m y' (hθ_sub hy') (hθub y' hy')
    · exact hsum_of D _ (fun m => by
        rw [abs_mul]
        exact hB3 m θ (by linarith [hθ]) hθle)
  have hT3 : ∀ y ∈ Set.Ioo (θ / 2) θu,
      HasDerivAt (fun y' => ∑' m : ℕ,
          Real.tan y' * (acoeff α m (RemSource α ψ) z * Gegenbauer.eFam m y'))
        (∑' m : ℕ, acoeff α m (RemSource α ψ) z
          * deriv (fun θ' => Real.tan θ' * Gegenbauer.eFam m θ') y) y := by
    intro y hy
    have hy0 : 0 < y := hθ_sub hy
    refine hasDerivAt_tsum_of_isPreconnected (𝕜 := ℝ) (F := ℝ)
      (u := fun m => D * majPow m)
      (g := fun m y' => Real.tan y' * (acoeff α m (RemSource α ψ) z
        * Gegenbauer.eFam m y'))
      (g' := fun m y' => acoeff α m (RemSource α ψ) z
        * deriv (fun θ' => Real.tan θ' * Gegenbauer.eFam m θ') y')
      hsum_maj isOpen_Ioo isPreconnected_Ioo ?_ ?_
      (y₀ := θ) ⟨by linarith [hθ], by rw [hθu]; linarith [hθ2]⟩ ?_ hy
    · intro m y' hy'
      have hy0' : 0 < y' := hθ_sub hy'
      have hne' : Real.cos y' ≠ 0 := ne_of_gt (lt_of_lt_of_le hcθ
        (Real.cos_le_cos_of_nonneg_of_le_pi (le_of_lt hy0') (by linarith [Real.pi_pos, hθ2])
          (le_of_lt hy'.2)))
      have htan : HasDerivAt Real.tan (1 / Real.cos y' ^ 2) y' := Real.hasDerivAt_tan hne'
      have he : HasDerivAt (fun θ' => Gegenbauer.eFam m θ') (deriv (Gegenbauer.eFam m) y') y' :=
        ((contDiff_eFam m).differentiable (by norm_num)).differentiableAt.hasDerivAt
      have hdd : HasDerivAt (fun θ' => Real.tan θ' * Gegenbauer.eFam m θ')
          (deriv (fun θ' => Real.tan θ' * Gegenbauer.eFam m θ') y') y' :=
        (htan.mul he).differentiableAt.hasDerivAt
      have h := hdd.const_mul (acoeff α m (RemSource α ψ) z)
      simpa only [mul_assoc, mul_comm, mul_left_comm] using h
    · intro m y' hy'
      rw [Real.norm_eq_abs, abs_mul]
      exact hB5 m y' (hθ_sub hy') (hθub y' hy')
    · refine hsum_of (|Real.tan θ| * D + 1) _ (fun m => ?_)
      rw [abs_mul, abs_mul]
      calc |Real.tan θ| * (|acoeff α m (RemSource α ψ) z| * |Gegenbauer.eFam m θ|)
          ≤ |Real.tan θ| * (D * majPow m) :=
            mul_le_mul_of_nonneg_left (hB0 m z hz) (abs_nonneg _)
        _ ≤ (|Real.tan θ| * D + 1) * majPow m := by
            have h := majPow_nonneg m
            nlinarith [abs_nonneg (Real.tan θ)]
  have hzt' : z ∈ Set.Ioo (z / 2) (2 * z) := ⟨by linarith [hz], by linarith [hz]⟩
  have hθt' : θ ∈ Set.Ioo (θ / 2) θu := ⟨by linarith [hθ], by rw [hθu]; linarith [hθ2]⟩
  have hPz : Spaces.pz (fun z θ => psiSeries α (RemSource α ψ) z θ) z θ
      = ∑' m : ℕ, deriv (acoeff α m (RemSource α ψ)) z * Gegenbauer.eFam m θ :=
    (hZ1 z hzt').deriv
  have hPz2 : Spaces.pzIter 2 (fun z θ => psiSeries α (RemSource α ψ) z θ) z θ
      = ∑' m : ℕ, deriv (deriv (acoeff α m (RemSource α ψ))) z * Gegenbauer.eFam m θ := by
    have hderiv : deriv (fun y => deriv (fun y' => psiSeries α (RemSource α ψ) y' θ) y) z
        = deriv (fun y => ∑' m : ℕ,
            deriv (acoeff α m (RemSource α ψ)) y * Gegenbauer.eFam m θ) z := by
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [isOpen_Ioo.mem_nhds hzt'] with y hy
      exact (hZ1 y hy).deriv
    show deriv (fun y => deriv (fun y' => psiSeries α (RemSource α ψ) y' θ) y) z = _
    rw [hderiv]
    exact (hZ2 z hzt').deriv
  have hPt : Spaces.pth (fun z θ => psiSeries α (RemSource α ψ) z θ) z θ
      = ∑' m : ℕ, acoeff α m (RemSource α ψ) z * deriv (Gegenbauer.eFam m) θ :=
    (hT1 θ hθt').deriv
  have hPt2 : Spaces.pthIter 2 (fun z θ => psiSeries α (RemSource α ψ) z θ) z θ
      = ∑' m : ℕ, acoeff α m (RemSource α ψ) z * iteratedDeriv 2 (Gegenbauer.eFam m) θ := by
    have hderiv : deriv (fun y => deriv (fun y' => psiSeries α (RemSource α ψ) z y') y) θ
        = deriv (fun y => ∑' m : ℕ,
            acoeff α m (RemSource α ψ) z * deriv (Gegenbauer.eFam m) y) θ := by
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [isOpen_Ioo.mem_nhds hθt'] with y hy
      exact (hT1 y hy).deriv
    show deriv (fun y => deriv (fun y' => psiSeries α (RemSource α ψ) z y') y) θ = _
    rw [hderiv]
    exact (hT2 θ hθt').deriv
  have hPtan : Spaces.pth (fun z' θ' => Real.tan θ' * psiSeries α (RemSource α ψ) z' θ') z θ
      = ∑' m : ℕ, acoeff α m (RemSource α ψ) z
          * deriv (fun θ' => Real.tan θ' * Gegenbauer.eFam m θ') θ := by
    have hfun : (fun θ' => Real.tan θ' * psiSeries α (RemSource α ψ) z θ')
        = fun θ' => ∑' m : ℕ,
            Real.tan θ' * (acoeff α m (RemSource α ψ) z * Gegenbauer.eFam m θ') := by
      funext θ'
      rw [show psiSeries α (RemSource α ψ) z θ'
          = ∑' m : ℕ, acoeff α m (RemSource α ψ) z * Gegenbauer.eFam m θ' from rfl]
      exact (tsum_mul_left (a := Real.tan θ')
        (f := fun m : ℕ => acoeff α m (RemSource α ψ) z * Gegenbauer.eFam m θ')).symm
    show deriv (fun θ' => Real.tan θ' * psiSeries α (RemSource α ψ) z θ') θ = _
    rw [hfun]
    exact (hT3 θ hθt').deriv
  have hLzero : Elliptic.Lzero (fun z θ => psiSeries α (RemSource α ψ) z θ) z θ
      = -Spaces.pthIter 2 (fun z θ => psiSeries α (RemSource α ψ) z θ) z θ
        + Spaces.pth (fun z' θ' => Real.tan θ' * psiSeries α (RemSource α ψ) z' θ') z θ
        - 6 * psiSeries α (RemSource α ψ) z θ := by
    rw [Elliptic.Lzero_eq_deriv]
    rfl
  exact ⟨hPz, hPz2, hPt, hPt2, hPtan, hLzero⟩

end Work.FTS.PhiStar.Series
