import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.Stability.Cutoff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Stability

/-- **The `dist`/`HolderWith` bridge.**  A pointwise bound of the form
`dist (f x) (f y) ≤ C * (dist x y) ^ α` with real exponent `α ≥ 0` upgrades to `HolderWith C α f`
(which is stated with `edist` and the `ennreal` power).  This is the form in which all the concrete
estimates of this layer are produced. -/
lemma holderWith_of_dist_le {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {C α : NNReal} {f : X → Y}
    (h : ∀ x y, dist (f x) (f y) ≤ (C : ℝ) * dist x y ^ (α : ℝ)) : HolderWith C α f := by
  intro x y
  rw [edist_nndist, edist_nndist]
  rw [← ENNReal.coe_rpow_of_nonneg (nndist x y) α.coe_nonneg, ← ENNReal.coe_mul,
    ENNReal.coe_le_coe]
  rw [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_rpow, coe_nndist, coe_nndist]
  exact h x y

/-- Let `A : ℝ³ → (ℝ³ →L[ℝ] ℝ)` be Lipschitz, bounded by `B ≥ 0`, and vanish outside the ball of
radius `R ≥ 0`, and let `w : ℝ³ → E` be Lipschitz.  Then `S x = (A x).smulRight (w x)` is bounded
(it vanishes for `‖x‖ > R`, and on the ball `‖w x‖ ≤ ‖w 0‖ + Kw R`) and Lipschitz
(`‖S x - S y‖ ≤ B Kw d + KA M d`, assuming w.l.o.g. that the point at distance `≤ R` is the one
used to bound `w`; if both points are outside the ball then `S x = S y = 0`), hence `α`-Hölder for
`α ≤ 1` by `HolderOfBoundedLipschitz`. -/
theorem HolderSmulRightOfSupport {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : Work.Cyl.R3 → Work.Cyl.R3 →L[ℝ] ℝ} {w : Work.Cyl.R3 → E} {R B : ℝ} {KA Kw : NNReal}
    {α : NNReal}
    (hα : α ≤ 1) (hR : 0 ≤ R) (hB : 0 ≤ B) (hA : LipschitzWith KA A)
    (hAb : ∀ x, ‖A x‖ ≤ B) (hA0 : ∀ x, R < ‖x‖ → A x = 0) (hw : LipschitzWith Kw w) :
    Holder α (fun x => (A x).smulRight (w x)) := by
  let M : ℝ := ‖w 0‖ + (Kw : ℝ) * R
  have hM0 : 0 ≤ M := add_nonneg (norm_nonneg _) (mul_nonneg Kw.coe_nonneg hR)
  have hKw : (0 : ℝ) ≤ (Kw : ℝ) := Kw.coe_nonneg
  have hKA : (0 : ℝ) ≤ (KA : ℝ) := KA.coe_nonneg
  -- `w` is bounded by `M` on the ball of radius `R`
  have hwbd : ∀ x : Work.Cyl.R3, ‖x‖ ≤ R → ‖w x‖ ≤ M := by
    intro x hx
    have h1 : ‖w x - w 0‖ ≤ (Kw : ℝ) * ‖x‖ := by
      have h := hw.dist_le_mul x 0
      rwa [dist_eq_norm, dist_eq_norm, sub_zero] at h
    calc ‖w x‖ = ‖w 0 + (w x - w 0)‖ := by rw [add_sub_cancel]
      _ ≤ ‖w 0‖ + ‖w x - w 0‖ := norm_add_le _ _
      _ ≤ ‖w 0‖ + (Kw : ℝ) * R := by
            have h2 : (Kw : ℝ) * ‖x‖ ≤ (Kw : ℝ) * R := mul_le_mul_of_nonneg_left hx hKw
            linarith
      _ = M := rfl
  -- `S` is bounded by `B * M`
  have hSbd : ∀ x : Work.Cyl.R3, ‖(A x).smulRight (w x)‖ ≤ B * M := by
    intro x
    by_cases hx : ‖x‖ ≤ R
    · rw [ContinuousLinearMap.norm_smulRight_apply]
      exact mul_le_mul (hAb x) (hwbd x hx) (norm_nonneg _) hB
    · rw [hA0 x (lt_of_not_ge hx), ContinuousLinearMap.zero_smulRight, norm_zero]
      exact mul_nonneg hB hM0
  -- the Lipschitz bound for `S`, with the bound on `w` taken at the point inside the ball
  have hlip : ∀ p q : Work.Cyl.R3, ‖p‖ ≤ R →
      dist ((A p).smulRight (w p)) ((A q).smulRight (w q)) ≤
        ((KA : ℝ) * M + B * (Kw : ℝ)) * dist p q := by
    intro p q hp
    have hApq : ‖A p - A q‖ ≤ (KA : ℝ) * dist p q := by
      have h := hA.dist_le_mul p q
      rwa [dist_eq_norm] at h
    have hwpq : ‖w p - w q‖ ≤ (Kw : ℝ) * dist p q := by
      have h := hw.dist_le_mul p q
      rwa [dist_eq_norm] at h
    have hdec : (A p).smulRight (w p) - (A q).smulRight (w q)
        = ((A p) - (A q)).smulRight (w p) + (A q).smulRight (w p - w q) := by
      ext v
      simp only [ContinuousLinearMap.smulRight_apply, sub_apply, add_apply]
      rw [sub_smul, smul_sub]
      abel
    calc dist ((A p).smulRight (w p)) ((A q).smulRight (w q))
        = ‖((A p) - (A q)).smulRight (w p) + (A q).smulRight (w p - w q)‖ := by
          rw [dist_eq_norm, hdec]
      _ ≤ ‖((A p) - (A q)).smulRight (w p)‖ + ‖(A q).smulRight (w p - w q)‖ := norm_add_le _ _
      _ = ‖A p - A q‖ * ‖w p‖ + ‖A q‖ * ‖w p - w q‖ := by
          rw [ContinuousLinearMap.norm_smulRight_apply, ContinuousLinearMap.norm_smulRight_apply]
      _ ≤ ((KA : ℝ) * dist p q) * M + B * ((Kw : ℝ) * dist p q) :=
          add_le_add (mul_le_mul hApq (hwbd p hp) (norm_nonneg _)
              (mul_nonneg hKA dist_nonneg))
            (mul_le_mul (hAb q) hwpq (norm_nonneg _) hB)
      _ = ((KA : ℝ) * M + B * (Kw : ℝ)) * dist p q := by ring
  -- `min (K₁ d) K₂ ≤ max K₁ K₂ * d ^ α` gives `α`-Hölder
  refine ⟨⟨max ((KA : ℝ) * M + B * (Kw : ℝ)) (2 * (B * M)), ?_⟩, ?_⟩
  · exact le_trans (add_nonneg (mul_nonneg hKA hM0) (mul_nonneg hB hKw)) (le_max_left _ _)
  · refine holderWith_of_dist_le ?_
    intro x y
    show dist ((A x).smulRight (w x)) ((A y).smulRight (w y)) ≤
      max ((KA : ℝ) * M + B * (Kw : ℝ)) (2 * (B * M)) * dist x y ^ (α : ℝ)
    have hA1 : dist ((A x).smulRight (w x)) ((A y).smulRight (w y)) ≤
        ((KA : ℝ) * M + B * (Kw : ℝ)) * dist x y := by
      by_cases hx : ‖x‖ ≤ R
      · exact hlip x y hx
      · by_cases hy : ‖y‖ ≤ R
        · calc dist ((A x).smulRight (w x)) ((A y).smulRight (w y))
              = dist ((A y).smulRight (w y)) ((A x).smulRight (w x)) := dist_comm _ _
            _ ≤ ((KA : ℝ) * M + B * (Kw : ℝ)) * dist y x := hlip y x hy
            _ = ((KA : ℝ) * M + B * (Kw : ℝ)) * dist x y := by rw [dist_comm]
        · -- both points outside the ball: `S` vanishes at both
          have hAx : A x = 0 := hA0 x (lt_of_not_ge hx)
          have hAy : A y = 0 := hA0 y (lt_of_not_ge hy)
          rw [hAx, hAy, ContinuousLinearMap.zero_smulRight, ContinuousLinearMap.zero_smulRight,
            dist_self]
          exact mul_nonneg (add_nonneg (mul_nonneg hKA hM0) (mul_nonneg hB hKw)) dist_nonneg
    have hA2 : dist ((A x).smulRight (w x)) ((A y).smulRight (w y)) ≤ 2 * (B * M) := by
      calc dist ((A x).smulRight (w x)) ((A y).smulRight (w y))
          = ‖(A x).smulRight (w x) - (A y).smulRight (w y)‖ := dist_eq_norm _ _
        _ ≤ ‖(A x).smulRight (w x)‖ + ‖(A y).smulRight (w y)‖ := norm_sub_le _ _
        _ ≤ B * M + B * M := add_le_add (hSbd x) (hSbd y)
        _ = 2 * (B * M) := by ring
    rcases lt_or_ge (dist x y) 1 with hd | hd
    · -- `dist x y ≤ 1`: the Lipschitz bound is the better one, and `d ≤ d ^ α`
      calc dist ((A x).smulRight (w x)) ((A y).smulRight (w y))
          ≤ ((KA : ℝ) * M + B * (Kw : ℝ)) * dist x y := hA1
        _ ≤ ((KA : ℝ) * M + B * (Kw : ℝ)) * dist x y ^ (α : ℝ) :=
            mul_le_mul_of_nonneg_left
              (Real.self_le_rpow_of_le_one dist_nonneg hd.le (by exact_mod_cast hα))
              (add_nonneg (mul_nonneg hKA hM0) (mul_nonneg hB hKw))
        _ ≤ max ((KA : ℝ) * M + B * (Kw : ℝ)) (2 * (B * M)) * dist x y ^ (α : ℝ) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg dist_nonneg _)
    · -- `1 ≤ dist x y`: the boundedness bound is the better one, and `1 ≤ d ^ α`
      calc dist ((A x).smulRight (w x)) ((A y).smulRight (w y)) ≤ 2 * (B * M) := hA2
        _ ≤ max ((KA : ℝ) * M + B * (Kw : ℝ)) (2 * (B * M)) * dist x y ^ (α : ℝ) := by
            have h1 : (1 : ℝ) ≤ dist x y ^ (α : ℝ) := Real.one_le_rpow hd α.coe_nonneg
            have h2 : max ((KA : ℝ) * M + B * (Kw : ℝ)) (2 * (B * M)) ≤
                max ((KA : ℝ) * M + B * (Kw : ℝ)) (2 * (B * M)) * dist x y ^ (α : ℝ) :=
              le_mul_of_one_le_right (le_trans (add_nonneg (mul_nonneg hKA hM0)
                (mul_nonneg hB hKw)) (le_max_left _ _)) h1
            exact le_trans (le_max_right _ _) h2

end Work.Stability
