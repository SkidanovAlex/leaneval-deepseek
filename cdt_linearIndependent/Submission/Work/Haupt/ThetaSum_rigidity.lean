import Mathlib
import Submission.Work.Haupt.thetaCore
import Submission.Work.Haupt.ThetaSum_analytic
import Submission.Work.Haupt.ThetaSum_pentagonal
import Submission.Work.Haupt.circleIntegral_scale_of_functional
import Submission.Work.Haupt.circleIntegral_independent_of_differentiableOn
import Submission.Work.Haupt.moments_eq_zero_imp_eq_zero

/-!
# Rigidity of the `q`-difference equation `F (x² z) = F z / (x z)`

A function `F` holomorphic on the punctured plane `ℂ \ {0}` which satisfies
`F (x ^ 2 * z) = F z / (x * z)` for every `z ≠ 0`, where `0 < ‖x‖ < 1`, is a scalar multiple
of the two-sided theta series `ThetaSum x z = ∑' n : ℤ, x ^ (n^2) * z^n`.

The proof is a Laurent-coefficient computation, in integral form.  For `f : ℂ → ℂ` and
`n : ℤ` put

  `rigidMom f n = ∮ t in C(0, 1), t ^ (-(n + 1)) * f t`,

the `n`-th Laurent moment of `f` on the unit circle.  The functional equation yields

  `rigidMom f (n + 1) = x ^ (2n+1) * rigidMom f n`   (`rigidMom_rec`)

by the change of variables `t ↦ x² t` on the circle (`circleIntegral_scale_of_functional`),
combined with the independence of the moment of the radius
(`circleIntegral_independent_of_differentiableOn`); hence

  `rigidMom f n = x ^ (n ^ 2) * rigidMom f 0`   (`rigidMom_pow`)

for every `n : ℤ`.  A holomorphic function on `ℂ \ {0}` whose moments all vanish is zero
(`moments_eq_zero_imp_eq_zero`), so the linear functional `rigidMom · 0` is injective on the
space of solutions of the functional equation; that space is therefore at most
one-dimensional.  As `ThetaSum x` is a solution whose value at the pentagonal point `-X`
(where `x = X ^ 3`) is a nonzero product, every solution is a multiple of `ThetaSum x`.
-/

namespace Work.Haupt

open scoped BigOperators

noncomputable section

/-! ## The functional equation of the theta series -/

/-- The `q`-difference equation `ThetaSum x (x ^ 2 * z) = ThetaSum x z / (x * z)` of the
two-sided theta series, obtained from the index shift `n ↦ n + 1`. -/
theorem rigidThetaSum_fe (x : ℂ) (hx0 : x ≠ 0) :
    ∀ z : ℂ, z ≠ 0 → ThetaSum x (x ^ 2 * z) = ThetaSum x z / (x * z) := by
  intro z hz
  have h1 : ThetaSum x (x ^ 2 * z)
      = ∑' n : ℤ, x ^ ((n + 1) ^ 2 - 1) * z ^ n := by
    rw [ThetaSum]
    refine tsum_congr (fun n => ?_)
    have hx2 : (x ^ 2 : ℂ) ^ n = x ^ ((2 : ℤ) * n) := by
      rw [show (x : ℂ) ^ 2 = x ^ (2 : ℤ) from (zpow_natCast x 2).symm, zpow_mul]
    rw [mul_zpow, hx2, ← mul_assoc, ← zpow_add₀ hx0]
    congr 1
    ring_nf
  have h2 : (∑' n : ℤ, x ^ ((n + 1) ^ 2 - 1) * z ^ n)
      = x⁻¹ * ∑' n : ℤ, x ^ ((n + 1) ^ 2) * z ^ n := by
    rw [← tsum_mul_left]
    refine tsum_congr (fun n => ?_)
    rw [show x⁻¹ * (x ^ ((n + 1) ^ 2) * z ^ n)
          = x ^ (-1 : ℤ) * x ^ ((n + 1) ^ 2) * z ^ n from by
          rw [show x⁻¹ = x ^ (-1 : ℤ) from (zpow_neg_one x).symm]; ring,
        ← zpow_add₀ hx0]
    congr 1
    ring_nf
  have h3 : (∑' n : ℤ, x ^ ((n + 1) ^ 2) * z ^ n) = z⁻¹ * ThetaSum x z := by
    have hz1 : ∀ k : ℤ, z⁻¹ * (x ^ k ^ 2 * z ^ k) = x ^ k ^ 2 * z ^ (k - 1) := by
      intro k
      rw [show z⁻¹ * (x ^ k ^ 2 * z ^ k) = x ^ k ^ 2 * (z ^ (-1 : ℤ) * z ^ k) from by
            rw [show z⁻¹ = z ^ (-1 : ℤ) from (zpow_neg_one z).symm]; ring,
          ← zpow_add₀ hz]
      congr 1
      ring_nf
    have hR : z⁻¹ * ThetaSum x z = ∑' k : ℤ, x ^ k ^ 2 * z ^ (k - 1) := by
      rw [ThetaSum, ← tsum_mul_left]
      exact tsum_congr hz1
    rw [hR, ← (Equiv.addRight (1 : ℤ)).tsum_eq (fun k : ℤ => x ^ k ^ 2 * z ^ (k - 1))]
    simp only [Equiv.coe_addRight]
    refine tsum_congr (fun n => ?_)
    rw [show n + 1 - 1 = n by ring]
  calc ThetaSum x (x ^ 2 * z)
      = ∑' n : ℤ, x ^ ((n + 1) ^ 2 - 1) * z ^ n := h1
    _ = x⁻¹ * ∑' n : ℤ, x ^ ((n + 1) ^ 2) * z ^ n := h2
    _ = x⁻¹ * (z⁻¹ * ThetaSum x z) := by rw [h3]
    _ = ThetaSum x z / (x * z) := by rw [div_eq_mul_inv, mul_inv]; ring

/-! ## Laurent moments on the unit circle -/

/-- The `n`-th Laurent moment `∮ t in C(0,1), t ^ (-(n + 1)) * f t` of `f`. -/
def rigidMom (f : ℂ → ℂ) (n : ℤ) : ℂ := ∮ t in C(0, 1), t ^ (-(n + 1)) * f t

lemma circleIntegrable_rigidMom {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f {z : ℂ | z ≠ 0})
    (n : ℤ) : CircleIntegrable (fun t : ℂ => t ^ (-(n + 1)) * f t) 0 1 := by
  refine ContinuousOn.circleIntegrable (by norm_num : (0 : ℝ) ≤ 1) ?_
  refine ((continuousOn_zpow₀ (-(n + 1))).mul hf.continuousOn).mono ?_
  intro z hz
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  rintro rfl
  simp at hz

lemma rigidMom_sub {f g : ℂ → ℂ} (n : ℤ)
    (hf : CircleIntegrable (fun t : ℂ => t ^ (-(n + 1)) * f t) 0 1)
    (hg : CircleIntegrable (fun t : ℂ => t ^ (-(n + 1)) * g t) 0 1) :
    rigidMom (fun z => f z - g z) n = rigidMom f n - rigidMom g n := by
  have h1 : (fun t : ℂ => t ^ (-(n + 1)) * ((fun z : ℂ => f z - g z) t))
      = (fun t : ℂ => t ^ (-(n + 1)) * f t - t ^ (-(n + 1)) * g t) := by
    funext t
    ring
  unfold rigidMom
  rw [h1, circleIntegral.integral_sub hf hg]

lemma rigidMom_const_mul (c : ℂ) (f : ℂ → ℂ) (n : ℤ) :
    rigidMom (fun z => c * f z) n = c * rigidMom f n := by
  have h1 : (fun t : ℂ => t ^ (-(n + 1)) * ((fun z : ℂ => c * f z) t))
      = (fun t : ℂ => c * (t ^ (-(n + 1)) * f t)) := by
    funext t
    ring
  unfold rigidMom
  rw [h1, circleIntegral.integral_const_mul]

/-! ## The moment recursion -/

/-- The scaling relation of the moments: the functional equation shifts the index by one
and multiplies by `x ^ (2n+1)`. -/
lemma rigidMom_rec {x : ℂ} (hx0 : x ≠ 0) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {z : ℂ | z ≠ 0})
    (hfe : ∀ z : ℂ, z ≠ 0 → f (x ^ 2 * z) = f z / (x * z)) (n : ℤ) :
    rigidMom f (n + 1) = x ^ (2 * n + 1) * rigidMom f n := by
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have h1 : rigidMom f n
      = x ^ (-(2 * n + 1)) * (∮ u in C(0, 1 / ‖x‖ ^ 2), u ^ (-(n + 2)) * f u) := by
    unfold rigidMom
    exact circleIntegral_scale_of_functional x hx0 hfe n (by norm_num)
  have h2 : (∮ u in C(0, 1 / ‖x‖ ^ 2), u ^ (-(n + 2)) * f u)
      = (∮ u in C(0, 1), u ^ (-(n + 2)) * f u) := by
    have h := circleIntegral_independent_of_differentiableOn hf (n + 1)
      (ρ := 1 / ‖x‖ ^ 2) (ρ' := 1) (by positivity) (by norm_num)
    simpa [show n + 1 + 1 = n + 2 by ring] using h
  have h3 : (∮ u in C(0, 1), u ^ (-(n + 2)) * f u) = rigidMom f (n + 1) := by
    unfold rigidMom
    rw [show -(n + 1 + 1) = -(n + 2) by ring]
  have h : rigidMom f n = x ^ (-(2 * n + 1)) * rigidMom f (n + 1) := by
    rw [h1, h2, h3]
  have hxinv : x ^ (2 * n + 1) * x ^ (-(2 * n + 1)) = 1 := by
    rw [← zpow_add₀ hx0, show 2 * n + 1 + -(2 * n + 1) = 0 by ring, zpow_zero]
  calc rigidMom f (n + 1)
      = x ^ (2 * n + 1) * (x ^ (-(2 * n + 1)) * rigidMom f (n + 1)) := by
        rw [← mul_assoc, hxinv, one_mul]
    _ = x ^ (2 * n + 1) * rigidMom f n := by rw [← h]

/-- Every moment of a solution of the functional equation is determined by the `0`-th one:
`rigidMom f n = x ^ (n ^ 2) * rigidMom f 0`. -/
lemma rigidMom_pow {x : ℂ} (hx0 : x ≠ 0) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {z : ℂ | z ≠ 0})
    (hfe : ∀ z : ℂ, z ≠ 0 → f (x ^ 2 * z) = f z / (x * z)) (n : ℤ) :
    rigidMom f n = x ^ (n ^ 2) * rigidMom f 0 := by
  refine Int.induction_on n ?_ ?_ ?_
  · simp
  · intro i ih
    have h := rigidMom_rec hx0 hf hfe (i : ℤ)
    rw [h, ih, ← mul_assoc, ← zpow_add₀ hx0]
    congr 1
    ring_nf
  · intro i ih
    have h := rigidMom_rec hx0 hf hfe (-(i : ℤ) - 1)
    have h' : rigidMom f (-(i : ℤ))
        = x ^ (-(2 * (i : ℤ) + 1)) * rigidMom f (-(i : ℤ) - 1) := by
      have hh := h
      rw [show -(i : ℤ) - 1 + 1 = -(i : ℤ) by ring,
        show 2 * (-(i : ℤ) - 1) + 1 = -(2 * (i : ℤ) + 1) by ring] at hh
      exact hh
    have hxinv : x ^ (2 * (i : ℤ) + 1) * x ^ (-(2 * (i : ℤ) + 1)) = 1 := by
      rw [← zpow_add₀ hx0, show 2 * (i : ℤ) + 1 + -(2 * (i : ℤ) + 1) = 0 by ring, zpow_zero]
    have h2 : rigidMom f (-(i : ℤ) - 1)
        = x ^ (2 * (i : ℤ) + 1) * rigidMom f (-(i : ℤ)) := by
      calc rigidMom f (-(i : ℤ) - 1)
          = x ^ (2 * (i : ℤ) + 1) *
              (x ^ (-(2 * (i : ℤ) + 1)) * rigidMom f (-(i : ℤ) - 1)) := by
            rw [← mul_assoc, hxinv, one_mul]
        _ = x ^ (2 * (i : ℤ) + 1) * rigidMom f (-(i : ℤ)) := by rw [← h']
    rw [h2, ih, ← mul_assoc, ← zpow_add₀ hx0]
    congr 1
    ring_nf

/-- A solution of the functional equation all of whose moments vanish is zero. -/
lemma rigidMom_zero_imp_eq_zero {x : ℂ} (hx0 : x ≠ 0) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {z : ℂ | z ≠ 0})
    (hfe : ∀ z : ℂ, z ≠ 0 → f (x ^ 2 * z) = f z / (x * z))
    (h0 : rigidMom f 0 = 0) : ∀ z : ℂ, z ≠ 0 → f z = 0 := by
  refine moments_eq_zero_imp_eq_zero hf ?_
  intro n ρ hρ
  rw [circleIntegral_independent_of_differentiableOn hf n (ρ := ρ) (ρ' := 1) hρ (by norm_num)]
  have hm : (∮ t in C(0, 1), t ^ (-(n + 1)) * f t) = rigidMom f n := rfl
  rw [hm, rigidMom_pow hx0 hf hfe n, h0, mul_zero]

/-! ## The pentagonal point -/

/-- The pentagonal product `∏' n, (1 - X ^ (2n+2))` does not vanish for `‖X‖ < 1`. -/
lemma rigidPentagonalProd_ne_zero (X : ℂ) (hX : ‖X‖ < 1) :
    (∏' n : ℕ, (1 - X ^ (2 * n + 2))) ≠ 0 := by
  have hX2 : ‖X ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg X) hX (by norm_num)
  have hs : Summable (fun n : ℕ => X ^ (2 * (n + 1))) := by
    have h : Summable (fun n : ℕ => (X ^ 2) ^ (n + 1)) :=
      (summable_nat_add_iff 1).2 (summable_geometric_of_norm_lt_one hX2)
    exact h.congr (fun n => by rw [pow_mul])
  have key : ∀ m : ℕ, m ≠ 0 → X ^ m ≠ 1 := by
    intro m hm h1
    have hc := congrArg norm h1
    rw [norm_pow, norm_one] at hc
    have hlt : ‖X‖ ^ m < 1 := pow_lt_one₀ (norm_nonneg X) hX hm
    rw [hc] at hlt
    exact lt_irrefl 1 hlt
  rw [show (∏' n : ℕ, (1 - X ^ (2 * n + 2)))
        = ∏' n : ℕ, (1 + -(X ^ (2 * (n + 1)))) from
      tprod_congr (fun n => by rw [show 2 * (n + 1) = 2 * n + 2 by ring]; ring)]
  exact tprod_one_add_ne_zero_of_summable (f := fun n : ℕ => -(X ^ (2 * (n + 1))))
    (fun n h => by
      have h1 : X ^ (2 * (n + 1)) = 1 := by
        have h' := add_eq_zero_iff_eq_neg.mp h
        simpa using h'.symm
      exact key (2 * (n + 1)) (by positivity) h1) hs.neg.norm

/-- Every complex number of norm `< 1` has a cube root of norm `< 1`. -/
lemma rigidCubeRoot (x : ℂ) (hx : ‖x‖ < 1) : ∃ X : ℂ, X ^ 3 = x ∧ ‖X‖ < 1 := by
  obtain ⟨X, hX⟩ := IsAlgClosed.exists_pow_nat_eq x (n := 3) (by norm_num)
  refine ⟨X, hX, ?_⟩
  have h3 : ‖X‖ ^ 3 < 1 ^ 3 := by
    rw [one_pow, ← norm_pow, hX]
    exact hx
  exact lt_of_pow_lt_pow_left₀ 3 (by norm_num) h3

/-! ## Rigidity -/

/-- The core of the rigidity argument: any two solutions of the same `q`-difference equation
are proportional.  It is enough that one solution is nonzero somewhere inside `ℂ \ {0}`. -/
theorem rigid_aux (x : ℂ) (hx0 : x ≠ 0) (hxn : ‖x‖ < 1) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F {z : ℂ | z ≠ 0})
    (hFE : ∀ z : ℂ, z ≠ 0 → F (x ^ 2 * z) = F z / (x * z))
    {Y : ℂ} (hY : Y ≠ 0) (hval : ThetaSum x (-Y) ≠ 0) :
    ∃ c : ℂ, ∀ z : ℂ, z ≠ 0 → F z = c * ThetaSum x z := by
  have hGd : DifferentiableOn ℂ (ThetaSum x) {z : ℂ | z ≠ 0} := ThetaSum_analytic x hxn
  have hGf : ∀ z : ℂ, z ≠ 0 → ThetaSum x (x ^ 2 * z) = ThetaSum x z / (x * z) :=
    rigidThetaSum_fe x hx0
  have hG0 : rigidMom (ThetaSum x) 0 ≠ 0 := by
    intro h0
    exact hval (rigidMom_zero_imp_eq_zero hx0 hGd hGf h0 (-Y) (neg_ne_zero.mpr hY))
  refine ⟨rigidMom F 0 / rigidMom (ThetaSum x) 0, fun z hz => ?_⟩
  have hHd : DifferentiableOn ℂ
      (fun w : ℂ => F w - rigidMom F 0 / rigidMom (ThetaSum x) 0 * ThetaSum x w)
      {z : ℂ | z ≠ 0} := hF.sub (hGd.const_mul _)
  have hHf : ∀ w : ℂ, w ≠ 0 →
      (fun w : ℂ => F w - rigidMom F 0 / rigidMom (ThetaSum x) 0 * ThetaSum x w) (x ^ 2 * w)
        = (fun w : ℂ => F w - rigidMom F 0 / rigidMom (ThetaSum x) 0 * ThetaSum x w) w
            / (x * w) := by
    intro w hw
    show F (x ^ 2 * w) - rigidMom F 0 / rigidMom (ThetaSum x) 0 * ThetaSum x (x ^ 2 * w)
      = (F w - rigidMom F 0 / rigidMom (ThetaSum x) 0 * ThetaSum x w) / (x * w)
    rw [hFE w hw, hGf w hw, sub_div]
    ring
  have hH0 : rigidMom
      (fun w : ℂ => F w - rigidMom F 0 / rigidMom (ThetaSum x) 0 * ThetaSum x w) 0 = 0 := by
    rw [rigidMom_sub (n := 0) (circleIntegrable_rigidMom hF 0)
      (circleIntegrable_rigidMom (hGd.const_mul _) 0)]
    rw [rigidMom_const_mul]
    rw [div_mul_cancel₀ _ hG0, sub_self]
  exact sub_eq_zero.mp (rigidMom_zero_imp_eq_zero hx0 hHd hHf hH0 z hz)

theorem ThetaSum_rigidity (x : ℂ) (hx : ‖x‖ < 1) (hx0 : x ≠ 0) (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F {z : ℂ | z ≠ 0})
    (hFE : ∀ z : ℂ, z ≠ 0 → F (x ^ 2 * z) = F z / (x * z)) :
    ∃ c : ℂ, ∀ z : ℂ, z ≠ 0 → F z = c * ThetaSum x z := by
  obtain ⟨X, hX3, hX⟩ := rigidCubeRoot x hx
  have hX0 : X ≠ 0 := fun h => hx0 (by rw [← hX3, h]; norm_num)
  refine rigid_aux x hx0 hx hF hFE hX0 ?_
  rw [← hX3, ThetaSum_pentagonal X hX]
  exact rigidPentagonalProd_ne_zero X hX

end

end Work.Haupt
