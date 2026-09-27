import Mathlib
import Submission.Work.Whitney.CutPush.germ_setup
import Submission.Work.Whitney.CutPush.smallPerturbation_diffeo
import Submission.Work.Whitney.CutPush.norm_sub_le_of_fderiv_close

/-!
# The germ-extension lemma (germ recipe, step (c))

STATUS: **proved.**  `Work.Whitney.CutPush.exists_global_diffeo_of_germ`:

> a `C^∞` map `Φ : ℝ^N → ℝ^N` whose derivative at `0` is injective agrees with a global `C^∞`
> diffeomorphism `Φ'` of `ℝ^N` (with global `C^∞` inverse `Ψ'`) on a ball around `0`.

The proof is the assembly (c) of `NOTES_hasFingerData_S33.md` §15 on top of the four proved bricks

* `exists_germ_setup` (the numerical front: `Ae, C, c, r, χ` with the cutoff bounds, the prescribed
  derivative estimate on `‖y‖ < 3 r` and the side condition
  `‖(Ae.symm : E →L)‖ * (c * (3 * C + 1)) < 1 / 2`),
* `norm_sub_le_of_fderiv_close` (mean value bound on the support),
* `exists_global_diffeo_of_small_perturbation` (a `K`-Lipschitz `C^∞` `V` with `K < 1` gives the
  global diffeomorphism `y ↦ y + V y` with smooth inverse),

together with the single new scalar estimate of this file, `hGlip`: the product
`G z := χ z • W z` of the cutoff with the first-order remainder `W := Φ - Φ 0 - Ae ·` is
`c (3C + 1)`-Lipschitz.  That estimate is a four-case check (`‖z‖ < 3 r` or not); in the two mixed
cases the vanishing clause `3 r ≤ ‖z‖ → χ z = 0` is what makes the Lipschitz bound of `χ` usable at
the pair `(z, z')`.

**Tactic notes.**  `field_simp` in this Mathlib closes the goal outright when the residual identity
is polynomial, so appending `ring` raises `No goals to be solved`; `field_simp` alone is correct.
-/

open scoped ContDiff Topology NNReal

namespace Work.Whitney.CutPush

theorem exists_global_diffeo_of_germ {N : ℕ}
    (Φ : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hd : Function.Injective (fderiv ℝ Φ 0)) :
    ∃ (Φ' Ψ' : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)) (r : ℝ),
      0 < r ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ' ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ' ∧
      (∀ y, Ψ' (Φ' y) = y) ∧ (∀ y, Φ' (Ψ' y) = y) ∧
      (∀ y : EuclideanSpace ℝ (Fin N), ‖y‖ < r → Φ' y = Φ y) := by
  classical
  obtain ⟨Ae, C, c, r, χ, hc, hr, hC, hAe, hχ, hb, h1χ, h0χ, hlipχ, hnum, hder⟩ :=
    exists_germ_setup Φ hΦ hd
  -- ## the first-order remainder
  let W : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) := fun z => Φ z - Φ 0 - Ae z
  have hWval : ∀ z : EuclideanSpace ℝ (Fin N), W z = Φ z - Φ 0 - Ae z := fun z => rfl
  have hWc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W := by
    rw [show W = fun z : EuclideanSpace ℝ (Fin N) => Φ z - Φ 0 - Ae z from rfl]
    exact (hΦ.sub contDiff_const).sub
      (ContinuousLinearMap.contDiff (Ae : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)))
  have hW0 : W 0 = 0 := by
    rw [hWval 0]
    simp
  have hr3 : (0 : ℝ) < 3 * r := by linarith
  have hWlip : ∀ x y : EuclideanSpace ℝ (Fin N), ‖x‖ < 3 * r → ‖y‖ < 3 * r →
      ‖W x - W y‖ ≤ c * ‖x - y‖ :=
    norm_sub_le_of_fderiv_close W hWc c (3 * r) hr3 hder
  have hWb : ∀ y : EuclideanSpace ℝ (Fin N), ‖y‖ < 3 * r → ‖W y‖ ≤ c * (3 * r) := by
    intro y hy
    have h0 : ‖(0 : EuclideanSpace ℝ (Fin N))‖ < 3 * r := by simpa using hr3
    have h := hWlip 0 y h0 hy
    have h2 : ‖W y‖ ≤ c * ‖y‖ := by simpa [hW0] using h
    exact le_trans h2 (mul_le_mul_of_nonneg_left (by linarith [norm_nonneg y]) hc.le)
  -- ## scalar bookkeeping
  have hcn : (0 : ℝ) ≤ c := hc.le
  have hAnn : ∀ x y : EuclideanSpace ℝ (Fin N), (0 : ℝ) ≤ (C / r) * ‖x - y‖ :=
    fun x y => mul_nonneg (div_nonneg hC hr.le) (norm_nonneg _)
  have hkey : ∀ x y : EuclideanSpace ℝ (Fin N),
      ((C / r) * ‖x - y‖) * (c * (3 * r)) = 3 * C * c * ‖x - y‖ := by
    intro x y
    field_simp
  have hcoef : 3 * C * c ≤ c * (3 * C + 1) := by nlinarith [hC, hcn]
  have hfin : ∀ s : ℝ, 0 ≤ s → c * s + 3 * C * c * s ≤ c * (3 * C + 1) * s := by
    intro s hs
    have h1 : c * s + 3 * C * c * s = (c + 3 * C * c) * s := by ring
    have h2 : c + 3 * C * c ≤ c * (3 * C + 1) := by nlinarith [hC, hcn]
    rw [h1]
    exact mul_le_mul_of_nonneg_right h2 hs
  -- ## the Lipschitz estimate for the product `χ • W`
  have hGlip : ∀ x y : EuclideanSpace ℝ (Fin N),
      ‖χ x • W x - χ y • W y‖ ≤ c * (3 * C + 1) * ‖x - y‖ := by
    intro x y
    by_cases hx : ‖x‖ < 3 * r
    · by_cases hy : ‖y‖ < 3 * r
      · -- both inside the support of `χ`
        have hdec : χ x • W x - χ y • W y =
            χ x • (W x - W y) + (χ x - χ y) • W y := by module
        have hchi : |χ x| ≤ 1 :=
          abs_le.mpr ⟨by linarith [(hb x).1], (hb x).2⟩
        have h1 : ‖χ x • (W x - W y)‖ ≤ 1 * (c * ‖x - y‖) := by
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul hchi (hWlip x y hx hy) (norm_nonneg _) (by norm_num)
        have hchi' : |χ x - χ y| ≤ (C / r) * ‖x - y‖ := by
          simpa [Real.norm_eq_abs] using hlipχ x y
        have h2 : ‖(χ x - χ y) • W y‖ ≤ ((C / r) * ‖x - y‖) * (c * (3 * r)) := by
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul hchi' (hWb y hy) (norm_nonneg _) (hAnn x y)
        calc ‖χ x • W x - χ y • W y‖
            = ‖χ x • (W x - W y) + (χ x - χ y) • W y‖ := by rw [hdec]
          _ ≤ ‖χ x • (W x - W y)‖ + ‖(χ x - χ y) • W y‖ := norm_add_le _ _
          _ ≤ 1 * (c * ‖x - y‖) + ((C / r) * ‖x - y‖) * (c * (3 * r)) := add_le_add h1 h2
          _ = c * ‖x - y‖ + 3 * C * c * ‖x - y‖ := by rw [one_mul, hkey x y]
          _ ≤ c * (3 * C + 1) * ‖x - y‖ := hfin (‖x - y‖) (norm_nonneg _)
      · -- `x` inside, `y` outside: `χ y = 0`
        have hy3 : 3 * r ≤ ‖y‖ := not_lt.mp hy
        have hχy : χ y = 0 := h0χ y hy3
        have hchi : χ x ≤ (C / r) * ‖x - y‖ := by
          have h1 : |χ x| ≤ (C / r) * ‖x - y‖ := by
            simpa [hχy, Real.norm_eq_abs] using hlipχ x y
          exact le_trans (le_abs_self _) h1
        have hval : ‖χ x • W x - χ y • W y‖ = χ x * ‖W x‖ := by
          rw [hχy, zero_smul, sub_zero, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (hb x).1]
        rw [hval]
        calc χ x * ‖W x‖ ≤ ((C / r) * ‖x - y‖) * (c * (3 * r)) :=
              mul_le_mul hchi (hWb x hx) (norm_nonneg _) (hAnn x y)
          _ = 3 * C * c * ‖x - y‖ := hkey x y
          _ ≤ c * (3 * C + 1) * ‖x - y‖ := mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
    · have hx3 : 3 * r ≤ ‖x‖ := not_lt.mp hx
      have hχx : χ x = 0 := h0χ x hx3
      by_cases hy : ‖y‖ < 3 * r
      · -- `x` outside, `y` inside
        have hchi : χ y ≤ (C / r) * ‖x - y‖ := by
          have h1 : |χ y| ≤ (C / r) * ‖x - y‖ := by
            have h' : ‖χ y - χ x‖ ≤ (C / r) * ‖x - y‖ := by simpa [norm_sub_rev] using hlipχ y x
            simpa [hχx, Real.norm_eq_abs] using h'
          exact le_trans (le_abs_self _) h1
        have hval : ‖χ x • W x - χ y • W y‖ = χ y * ‖W y‖ := by
          rw [hχx, zero_smul, zero_sub, norm_neg, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (hb y).1]
        rw [hval]
        calc χ y * ‖W y‖ ≤ ((C / r) * ‖x - y‖) * (c * (3 * r)) :=
              mul_le_mul hchi (hWb y hy) (norm_nonneg _) (hAnn x y)
          _ = 3 * C * c * ‖x - y‖ := hkey x y
          _ ≤ c * (3 * C + 1) * ‖x - y‖ := mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
      · -- both outside: `χ` vanishes at both
        have hy3 : 3 * r ≤ ‖y‖ := not_lt.mp hy
        have hχy : χ y = 0 := h0χ y hy3
        rw [hχx, hχy, zero_smul, zero_smul, sub_zero, norm_zero]
        exact mul_nonneg (mul_nonneg hcn (by linarith)) (norm_nonneg _)
  -- ## the interpolated perturbation `V = Ae⁻¹ ∘ (χ • W)`
  let V : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) := fun y => Ae.symm (χ y • W y)
  have hVval : ∀ z : EuclideanSpace ℝ (Fin N), V z = Ae.symm (χ z • W z) := fun z => rfl
  have hVc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V := by
    rw [show V = fun y : EuclideanSpace ℝ (Fin N) => Ae.symm (χ y • W y) from rfl]
    exact (ContinuousLinearMap.contDiff
      (Ae.symm : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))).comp (hχ.smul hWc)
  have hkn : (0 : ℝ) ≤
      ‖(Ae.symm : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))‖ *
        (c * (3 * C + 1)) :=
    mul_nonneg (norm_nonneg _) (mul_nonneg hcn (by linarith))
  let K : ℝ≥0 := ⟨_, hkn⟩
  have hKval : (K : ℝ) =
      ‖(Ae.symm : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))‖ *
        (c * (3 * C + 1)) := rfl
  have hK1 : K < 1 := by
    have h1 : (K : ℝ) < 1 := by
      rw [hKval]
      linarith
    exact_mod_cast h1
  have hVlip : LipschitzWith K V := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [dist_eq_norm, dist_eq_norm]
    show ‖V x - V y‖ ≤ (K : ℝ) * ‖x - y‖
    have hdec : V x - V y = Ae.symm (χ x • W x - χ y • W y) := by
      rw [hVval x, hVval y]
      exact (map_sub (Ae.symm : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))
        (χ x • W x) (χ y • W y)).symm
    rw [hKval]
    calc ‖V x - V y‖
        = ‖Ae.symm (χ x • W x - χ y • W y)‖ := by rw [hdec]
      _ ≤ ‖(Ae.symm : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))‖ *
            ‖χ x • W x - χ y • W y‖ :=
          ContinuousLinearMap.le_opNorm (Ae.symm : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) (χ x • W x - χ y • W y)
      _ ≤ ‖(Ae.symm : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))‖ *
            (c * (3 * C + 1) * ‖x - y‖) :=
          mul_le_mul_of_nonneg_left (hGlip x y) (norm_nonneg _)
      _ = (‖(Ae.symm : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))‖ *
            (c * (3 * C + 1))) * ‖x - y‖ := by ring
  obtain ⟨Φv, Ψv, hΦvc, hΨvc, hleft, hright, hΦv⟩ :=
    exists_global_diffeo_of_small_perturbation V hVc K hK1 hVlip
  -- ## conjugation by the linear part `Ψ₀ y = Φ 0 + Ae y`
  let Ψ₀ : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) := fun y => Φ 0 + Ae y
  let Ψ₀i : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) := fun z => Ae.symm (z - Φ 0)
  have hΨ₀val : ∀ y : EuclideanSpace ℝ (Fin N), Ψ₀ y = Φ 0 + Ae y := fun y => rfl
  have hΨ₀ival : ∀ z : EuclideanSpace ℝ (Fin N), Ψ₀i z = Ae.symm (z - Φ 0) := fun z => rfl
  have hΨ₀c : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ₀ := by
    rw [show Ψ₀ = fun y : EuclideanSpace ℝ (Fin N) => Φ 0 + Ae y from rfl]
    exact contDiff_const.add
      (ContinuousLinearMap.contDiff (Ae : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)))
  have hΨ₀ic : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ₀i := by
    rw [show Ψ₀i = fun z : EuclideanSpace ℝ (Fin N) => Ae.symm (z - Φ 0) from rfl]
    exact (ContinuousLinearMap.contDiff
      (Ae.symm : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))).comp
      (contDiff_id.sub contDiff_const)
  have hΨ₀left : ∀ y : EuclideanSpace ℝ (Fin N), Ψ₀i (Ψ₀ y) = y := by
    intro y
    rw [hΨ₀val y, hΨ₀ival]
    rw [show Φ 0 + Ae y - Φ 0 = Ae y by abel]
    exact ContinuousLinearEquiv.symm_apply_apply Ae y
  have hΨ₀right : ∀ z : EuclideanSpace ℝ (Fin N), Ψ₀ (Ψ₀i z) = z := by
    intro z
    rw [hΨ₀ival z, hΨ₀val]
    rw [ContinuousLinearEquiv.apply_symm_apply]
    abel
  refine ⟨Ψ₀ ∘ Φv, Ψv ∘ Ψ₀i, r, hr, hΨ₀c.comp hΦvc, hΨvc.comp hΨ₀ic, ?_, ?_, ?_⟩
  · intro y
    show Ψv (Ψ₀i (Ψ₀ (Φv y))) = y
    rw [hΨ₀left, hleft y]
  · intro z
    show Ψ₀ (Φv (Ψv (Ψ₀i z))) = z
    rw [hright, hΨ₀right z]
  · intro y hy
    have hχ1 : χ y = 1 := h1χ y hy.le
    have hVy : V y = Ae.symm (W y) := by
      rw [hVval y, hχ1, one_smul]
    show Φ 0 + Ae (Φv y) = Φ y
    rw [hΦv y, hVy]
    show Φ 0 + Ae (y + Ae.symm (W y)) = Φ y
    rw [map_add, ContinuousLinearEquiv.apply_symm_apply]
    rw [hWval y]
    abel

end Work.Whitney.CutPush
