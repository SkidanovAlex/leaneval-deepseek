import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.RowAdzBase

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.N0pair6Aux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

noncomputable section

/-! ## The pointwise bounds of the slots of the Leibniz expansion -/

/-- The `(0,0)`-slot, dominated by the level-seven integrand. -/
theorem rowA_slot_dom_00 {α K : ℝ} (hα : 0 < α) (hK : 0 ≤ K)
    {f A : ℝ → ℝ → ℝ} {a b : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ)
    (hAbd : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → ∀ j i : ℕ, i + j ≤ 6 →
      |Work.Spaces.mixed j i A z θ| ≤ K * (if i = 0 then 1 else Real.sin (2 * θ)))
    (hab : a + b ≤ 6)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    |rowA_piece f A ρ a b 0 0 (z, θ)| ≤ K * Work.Spaces.HkIntegrand α 7 f z θ := by
  have hρnn : 0 ≤ ρ z θ := (Work.FTS.TransportS.IsLeafW_le α hα hρ).1 z θ hz hθ.1 hθ.2
  have hA : |A z θ| ≤ K := by
    have h := hAbd z θ hz hθ.1 hθ.2 0 0 (by norm_num)
    simpa using h
  have hG : ρ z θ * (Work.Spaces.mixed (b + 1) a f z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 7 f z θ :=
    Work.FTS.StrongPersist.H6Pair6Aux.domLeaf_all hα hρ (b' := b + 1) (n := 7) hθ (by omega)
  have hH : ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 7 f z θ :=
    (Work.FTS.StrongPersist.H6Pair6Aux.domLeaf_all hα hρ (b' := b) (n := 6) hθ hab).trans
      (Work.FTS.StrongPersist.H6Pair6Aux.HkIntegrand_mono α (by norm_num) f z θ)
  show |ρ z θ * Work.Spaces.mixed 0 0 A z θ * Work.Spaces.mixed (b - 0 + 1) (a - 0) f z θ
      * Work.Spaces.mixed b a f z θ| ≤ K * Work.Spaces.HkIntegrand α 7 f z θ
  rw [Nat.sub_zero, Nat.sub_zero, Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero]
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hρnn]
  calc ρ z θ * |A z θ| * |Work.Spaces.mixed (b + 1) a f z θ| * |Work.Spaces.mixed b a f z θ|
      ≤ ρ z θ * K * |Work.Spaces.mixed (b + 1) a f z θ| * |Work.Spaces.mixed b a f z θ| :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA hρnn) (abs_nonneg _))
          (abs_nonneg _)
    _ = K * (ρ z θ * (|Work.Spaces.mixed (b + 1) a f z θ|
          * |Work.Spaces.mixed b a f z θ|)) := by ring
    _ ≤ K * (ρ z θ * ((Work.Spaces.mixed (b + 1) a f z θ) ^ 2
          + (Work.Spaces.mixed b a f z θ) ^ 2) / 2) :=
        mul_le_mul_of_nonneg_left (rowA_mul_abs_le hρnn) hK
    _ = K * ((ρ z θ * (Work.Spaces.mixed (b + 1) a f z θ) ^ 2
          + ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2) / 2) := by ring
    _ ≤ K * ((Work.Spaces.HkIntegrand α 7 f z θ + Work.Spaces.HkIntegrand α 7 f z θ) / 2) := by
        refine mul_le_mul_of_nonneg_left ?_ hK
        linarith [hG, hH]
    _ = K * Work.Spaces.HkIntegrand α 7 f z θ := by ring

/-- The `(0,j)`-slot with `j ≥ 1`. -/
theorem rowA_slot_dom_i0pos {α K : ℝ} (hα : 0 < α) (hK : 0 ≤ K)
    {f A : ℝ → ℝ → ℝ} {a b j : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ)
    (hAbd : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → ∀ j i : ℕ, i + j ≤ 6 →
      |Work.Spaces.mixed j i A z θ| ≤ K * (if i = 0 then 1 else Real.sin (2 * θ)))
    (hab : a + b ≤ 6) (hjb : j ≤ b) (hj : 1 ≤ j)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    |rowA_piece f A ρ a b 0 j (z, θ)| ≤ K * Work.Spaces.HkIntegrand α 6 f z θ := by
  have hρnn : 0 ≤ ρ z θ := (Work.FTS.TransportS.IsLeafW_le α hα hρ).1 z θ hz hθ.1 hθ.2
  have hX : |Work.Spaces.mixed j 0 A z θ| ≤ K := by
    have h := hAbd z θ hz hθ.1 hθ.2 j 0 (by omega)
    simpa using h
  have hG : ρ z θ * (Work.Spaces.mixed (b - j + 1) a f z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
    Work.FTS.StrongPersist.H6Pair6Aux.domLeaf_all hα hρ (b' := b - j + 1) (n := 6) hθ (by omega)
  have hH : ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
    Work.FTS.StrongPersist.H6Pair6Aux.domLeaf_all hα hρ (b' := b) (n := 6) hθ hab
  show |ρ z θ * Work.Spaces.mixed j 0 A z θ * Work.Spaces.mixed (b - j + 1) (a - 0) f z θ
      * Work.Spaces.mixed b a f z θ| ≤ K * Work.Spaces.HkIntegrand α 6 f z θ
  rw [Nat.sub_zero, Work.Spaces.mixed_zero_right]
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hρnn]
  calc ρ z θ * |Work.Spaces.mixed j 0 A z θ|
        * |Work.Spaces.mixed (b - j + 1) a f z θ| * |Work.Spaces.mixed b a f z θ|
      ≤ ρ z θ * K * |Work.Spaces.mixed (b - j + 1) a f z θ| * |Work.Spaces.mixed b a f z θ| :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hX hρnn) (abs_nonneg _))
          (abs_nonneg _)
    _ = K * (ρ z θ * (|Work.Spaces.mixed (b - j + 1) a f z θ|
          * |Work.Spaces.mixed b a f z θ|)) := by ring
    _ ≤ K * (ρ z θ * ((Work.Spaces.mixed (b - j + 1) a f z θ) ^ 2
          + (Work.Spaces.mixed b a f z θ) ^ 2) / 2) :=
        mul_le_mul_of_nonneg_left (rowA_mul_abs_le hρnn) hK
    _ = K * ((ρ z θ * (Work.Spaces.mixed (b - j + 1) a f z θ) ^ 2
          + ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2) / 2) := by ring
    _ ≤ K * ((Work.Spaces.HkIntegrand α 6 f z θ + Work.Spaces.HkIntegrand α 6 f z θ) / 2) := by
        refine mul_le_mul_of_nonneg_left ?_ hK
        linarith [hG, hH]
    _ = K * Work.Spaces.HkIntegrand α 6 f z θ := by ring

/-- The `(i,j)`-slot with `i ≥ 1`. -/
theorem rowA_slot_dom_ipos {α K : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hK : 0 ≤ K)
    {f A : ℝ → ℝ → ℝ} {a b i j : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ)
    (hAbd : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → ∀ j i : ℕ, i + j ≤ 6 →
      |Work.Spaces.mixed j i A z θ| ≤ K * (if i = 0 then 1 else Real.sin (2 * θ)))
    (hab : a + b ≤ 6) (hia : i ≤ a) (hjb : j ≤ b) (hi : 1 ≤ i)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    |rowA_piece f A ρ a b i j (z, θ)| ≤ K * Work.Spaces.HkIntegrand α 6 f z θ := by
  have hij6 : i + j ≤ 6 := by omega
  have ha1 : 1 ≤ a := le_trans hi hia
  have hρnn : 0 ≤ ρ z θ := (Work.FTS.TransportS.IsLeafW_le α hα hρ).1 z θ hz hθ.1 hθ.2
  have hX : |Work.Spaces.mixed j i A z θ| ≤ K * Real.sin (2 * θ) := by
    have h := hAbd z θ hz hθ.1 hθ.2 j i hij6
    rwa [if_neg (by omega : i ≠ 0)] at h
  have hσpos : 0 < Real.sin (2 * θ) := rowA_sin_two_pos hθ
  have hσle1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hρη : ρ z θ * Real.sin (2 * θ)
      ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    have h1 := Work.FTS.StrongPersist.H6Pair6Aux.sigma_mul_leaf_le (z := z) hα hρ hθ
    have h2 : (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1))
        ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      refine Real.rpow_le_rpow_of_exponent_ge hσpos hσle1 ?_
      have hge : Work.Spaces.gam α - 1 ≤ Work.Spaces.eta := by
        rw [Work.Spaces.gam, Work.Spaces.eta]; linarith
      linarith
    calc ρ z θ * Real.sin (2 * θ) = Real.sin (2 * θ) * ρ z θ := by ring
      _ ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1)) := h1
      _ ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := h2
  have hG : (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      * (Work.Spaces.mixed (b - j + 1) (a - i) f z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
    by_cases hai : a - i = 0
    · have h : Work.FTS.TransportS.leafEta z θ
            * (Work.Spaces.mixed (b - j + 1) 0 f z θ) ^ 2
            ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
        Work.FTS.StrongPersist.H6Pair6Aux.domLeaf_all hα
          (hleaf := (Or.inl rfl : Work.FTS.TransportS.IsLeafW α 0
            Work.FTS.TransportS.leafEta))
          (b' := b - j + 1) (n := 6) hθ (by omega)
      rw [hai]
      simpa only [Work.FTS.TransportS.leafEta] using h
    · have hai1 : 1 ≤ a - i := by omega
      have hle : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
        rowA_sin_rpow_eta_le_gam hα hθ
      have h1 : (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            * (Work.Spaces.mixed (b - j + 1) (a - i) f z θ) ^ 2
          ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed (b - j + 1) (a - i) f z θ) ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hle (sq_nonneg _)) (sq_nonneg _)
      refine h1.trans ?_
      have h : Work.FTS.TransportS.leafGam α z θ
            * (Work.Spaces.mixed (b - j + 1) (a - i) f z θ) ^ 2
            ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
        Work.FTS.StrongPersist.H6Pair6Aux.domLeaf_all hα
          (hleaf := (Or.inr (Or.inr ⟨hai1, rfl⟩) : Work.FTS.TransportS.IsLeafW α (a - i)
            (Work.FTS.TransportS.leafGam α)))
          (b' := b - j + 1) (n := 6) hθ (by omega)
      simpa only [Work.FTS.TransportS.leafGam] using h
  have hH : (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      * (Work.Spaces.mixed b a f z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
    have hle : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := rowA_sin_rpow_eta_le_gam hα hθ
    have h1 : (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          * (Work.Spaces.mixed b a f z θ) ^ 2
        ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed b a f z θ) ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle (sq_nonneg _)) (sq_nonneg _)
    refine h1.trans ?_
    have h : Work.FTS.TransportS.leafGam α z θ
          * (Work.Spaces.mixed b a f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
      Work.FTS.StrongPersist.H6Pair6Aux.domLeaf_all hα
        (hleaf := (Or.inr (Or.inr ⟨ha1, rfl⟩) : Work.FTS.TransportS.IsLeafW α a
          (Work.FTS.TransportS.leafGam α))) (b' := b) (n := 6) hθ hab
    simpa only [Work.FTS.TransportS.leafGam] using h
  have hx0 : 0 ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt hσpos) _)
  show |ρ z θ * Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j + 1) (a - i) f z θ
      * Work.Spaces.mixed b a f z θ| ≤ K * Work.Spaces.HkIntegrand α 6 f z θ
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hρnn]
  calc ρ z θ * |Work.Spaces.mixed j i A z θ|
        * |Work.Spaces.mixed (b - j + 1) (a - i) f z θ| * |Work.Spaces.mixed b a f z θ|
      ≤ ρ z θ * (K * Real.sin (2 * θ))
        * |Work.Spaces.mixed (b - j + 1) (a - i) f z θ| * |Work.Spaces.mixed b a f z θ| :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hX hρnn) (abs_nonneg _))
          (abs_nonneg _)
    _ = K * ((ρ z θ * Real.sin (2 * θ))
          * (|Work.Spaces.mixed (b - j + 1) (a - i) f z θ|
            * |Work.Spaces.mixed b a f z θ|)) := by ring
    _ ≤ K * (((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          * (|Work.Spaces.mixed (b - j + 1) (a - i) f z θ|
            * |Work.Spaces.mixed b a f z θ|)) := by
        refine mul_le_mul_of_nonneg_left ?_ hK
        exact mul_le_mul_of_nonneg_right hρη (by positivity)
    _ ≤ K * (((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          * ((Work.Spaces.mixed (b - j + 1) (a - i) f z θ) ^ 2
            + (Work.Spaces.mixed b a f z θ) ^ 2) / 2) := by
        refine mul_le_mul_of_nonneg_left ?_ hK
        exact rowA_mul_abs_le hx0
    _ = K * (((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            * (Work.Spaces.mixed (b - j + 1) (a - i) f z θ) ^ 2
          + (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            * (Work.Spaces.mixed b a f z θ) ^ 2) / 2) := by ring
    _ ≤ K * ((Work.Spaces.HkIntegrand α 6 f z θ + Work.Spaces.HkIntegrand α 6 f z θ) / 2) := by
        refine mul_le_mul_of_nonneg_left ?_ hK
        linarith [hG, hH]
    _ = K * Work.Spaces.HkIntegrand α 6 f z θ := by ring

/-- The uniform pointwise slot domination for the slots with `(i,j) ≠ (0,0)`. -/
theorem rowA_slot_dom {α K : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hK : 0 ≤ K)
    {f A : ℝ → ℝ → ℝ} {a b i j : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ)
    (hAbd : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → ∀ j i : ℕ, i + j ≤ 6 →
      |Work.Spaces.mixed j i A z θ| ≤ K * (if i = 0 then 1 else Real.sin (2 * θ)))
    (hab : a + b ≤ 6) (hia : i ≤ a) (hjb : j ≤ b) (hij : 1 ≤ i + j)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    |rowA_piece f A ρ a b i j (z, θ)| ≤ K * Work.Spaces.HkIntegrand α 6 f z θ := by
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · subst hi0
    have hj1 : 1 ≤ j := by omega
    exact rowA_slot_dom_i0pos hα hK hρ hAbd hab hjb hj1 hz hθ
  · exact rowA_slot_dom_ipos hα hα1 hK hρ hAbd hab hia hjb hipos hz hθ

end

end Work.FTS.StrongPersist.H6Rows.N0pair6Aux
