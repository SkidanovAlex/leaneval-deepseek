import Mathlib

/-!
# A small Lipschitz perturbation of the identity is a global diffeomorphism of `ℝ^N`

`Work.Whitney.CutPush.exists_global_diffeo_of_small_perturbation`: if `V : ℝ^N → ℝ^N` is `C^∞` and
`K`-Lipschitz with `K < 1`, then `y ↦ y + V y` is a diffeomorphism of `ℝ^N` whose inverse is again
`C^∞`.

This is the reusable half of "a local diffeomorphism germ of `ℝ^N` extends to a global
diffeomorphism" (`Work.Whitney.CutPush.exists_global_diffeo_of_germ`): after conjugating by the
linear part one is left with a compactly supported perturbation `V` of the identity which is small
in the `C¹` sense on the support, hence a strict contraction, and the present file converts that
contraction into the global diffeomorphism and its smooth inverse.  The construction is

* injectivity of `y ↦ y + V y` from the lower bound `(1-K) ‖x - y‖ ≤ ‖(y + V y) - (x + V x)‖`;
* surjectivity from the fixed point of `y ↦ z - V y` (a contraction, `ContractingWith.fixedPoint`);
* the inverse is `(1-K)⁻¹`-Lipschitz, hence the map is a homeomorphism;
* the derivative `1 + fderiv ℝ V a` is invertible at every point (it is injective because
  `‖T v‖ ≤ K ‖v‖` with `K < 1`), so `Homeomorph.contDiff_symm` gives the smoothness of the inverse.
-/

open scoped ContDiff NNReal

namespace Work.Whitney.CutPush

/-- **A small Lipschitz perturbation of the identity is a global diffeomorphism.** -/
theorem exists_global_diffeo_of_small_perturbation {N : ℕ}
    (V : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (K : ℝ≥0) (hK : K < 1) (hlip : LipschitzWith K V) :
    ∃ (Φ' Ψ' : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ' ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ' ∧
      (∀ y, Ψ' (Φ' y) = y) ∧ (∀ y, Φ' (Ψ' y) = y) ∧
      (∀ y, Φ' y = y + V y) := by
  classical
  have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hK1 : (K : ℝ) < 1 := by exact_mod_cast hK
  have hpos : (0 : ℝ) < 1 - (K : ℝ) := by linarith [hK1]
  let F : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) := fun y => y + V y
  have hFc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F := by
    rw [show F = fun y : EuclideanSpace ℝ (Fin N) => y + V y from rfl]
    fun_prop
  have hlip' : ∀ x y : EuclideanSpace ℝ (Fin N),
      ‖V x - V y‖ ≤ (K : ℝ) * ‖x - y‖ := by
    intro x y
    simpa [dist_eq_norm] using hlip.dist_le_mul x y
  -- the lower bound
  have hlower : ∀ x y : EuclideanSpace ℝ (Fin N),
      (1 - (K : ℝ)) * ‖x - y‖ ≤ ‖F x - F y‖ := by
    intro x y
    have h2 : F x - F y = (x - y) + (V x - V y) := by
      simp only [F]
      abel
    rw [h2, show (1 - (K : ℝ)) * ‖x - y‖ = ‖x - y‖ - (K : ℝ) * ‖x - y‖ from by ring]
    have h3 : ‖x - y‖ ≤ ‖(x - y) + (V x - V y)‖ + ‖V x - V y‖ := by
      have h := norm_add_le ((x - y) + (V x - V y)) (-(V x - V y))
      rw [show (x - y) + (V x - V y) + -(V x - V y) = x - y by abel, norm_neg] at h
      exact h
    linarith [hlip' x y]
  have hinj : Function.Injective F := by
    intro x y hxy
    have h1 := hlower x y
    rw [hxy, sub_self, norm_zero] at h1
    have h2 : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y), hpos]
    exact sub_eq_zero.mp (norm_eq_zero.mp h2)
  -- surjectivity: the fixed point of `y ↦ z - V y`
  have hsurj : Function.Surjective F := by
    intro z
    have hcon : ContractingWith K (fun y : EuclideanSpace ℝ (Fin N) => z - V y) := by
      refine ⟨hK, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
      rw [dist_eq_norm, dist_eq_norm]
      have h : ‖(z - V x) - (z - V y)‖ = ‖V x - V y‖ := by
        rw [show (z - V x) - (z - V y) = -(V x - V y) by abel, norm_neg]
      rw [h, ← dist_eq_norm]
      exact hlip.dist_le_mul x y
    set y := ContractingWith.fixedPoint (fun y : EuclideanSpace ℝ (Fin N) => z - V y) hcon with hy
    have hfix := ContractingWith.fixedPoint_isFixedPt (f := fun y : EuclideanSpace ℝ (Fin N) => z - V y) hcon
    have hfix' : V y = z - y := by
      have h1 : z - V y = y := hfix
      have h2 : z = y + V y := sub_eq_iff_eq_add.mp h1
      rw [h2]
      abel
    refine ⟨y, ?_⟩
    show y + V y = z
    rw [hfix']
    abel
  have hbij : Function.Bijective F := ⟨hinj, hsurj⟩
  let e : EuclideanSpace ℝ (Fin N) ≃ EuclideanSpace ℝ (Fin N) := Equiv.ofBijective F hbij
  have he : ∀ y : EuclideanSpace ℝ (Fin N), e y = F y := fun y => Equiv.ofBijective_apply F hbij y
  have hsymm_left : ∀ y : EuclideanSpace ℝ (Fin N), e.symm (e y) = y := fun y => e.symm_apply_apply y
  -- the inverse satisfies the same lower bound, hence is continuous
  have hinv : ∀ z w : EuclideanSpace ℝ (Fin N),
      (1 - (K : ℝ)) * ‖e.symm z - e.symm w‖ ≤ ‖z - w‖ := by
    intro z w
    have h1 := hlower (e.symm z) (e.symm w)
    rw [show F (e.symm z) = z from by rw [← he]; exact e.apply_symm_apply z,
      show F (e.symm w) = w from by rw [← he]; exact e.apply_symm_apply w] at h1
    exact h1
  have hcont_inv : Continuous e.symm := by
    rw [Metric.continuous_iff]
    intro z ε hε
    refine ⟨(1 - (K : ℝ)) * ε, by positivity, fun w hw => ?_⟩
    rw [dist_eq_norm] at hw ⊢
    have h2 : (1 - (K : ℝ)) * ‖e.symm w - e.symm z‖ < (1 - (K : ℝ)) * ε :=
      lt_of_le_of_lt (hinv w z) hw
    nlinarith [h2, hpos, norm_nonneg (e.symm w - e.symm z)]
  let H : EuclideanSpace ℝ (Fin N) ≃ₜ EuclideanSpace ℝ (Fin N) :=
    { toEquiv := e
      continuous_toFun := hFc.continuous
      continuous_invFun := hcont_inv }
  -- the derivative of `F` at a point, as a linear equivalence
  have hder_equiv : ∀ a : EuclideanSpace ℝ (Fin N),
      ∃ A : EuclideanSpace ℝ (Fin N) ≃L[ℝ] EuclideanSpace ℝ (Fin N),
        (A : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))
          = 1 + fderiv ℝ V a := by
    intro a
    have hTa : ‖fderiv ℝ V a‖ ≤ (K : ℝ) := norm_fderiv_le_of_lipschitz ℝ hlip
    have hbound : ∀ u : EuclideanSpace ℝ (Fin N),
        (1 - (K : ℝ)) * ‖u‖ ≤ ‖(1 + fderiv ℝ V a) u‖ := by
      intro u
      have hone : (1 + fderiv ℝ V a) u = u + fderiv ℝ V a u := by simp
      rw [hone, show (1 - (K : ℝ)) * ‖u‖ = ‖u‖ - (K : ℝ) * ‖u‖ from by ring]
      have h2 : ‖u‖ ≤ ‖u + fderiv ℝ V a u‖ + ‖fderiv ℝ V a u‖ := by
        have h := norm_add_le (u + fderiv ℝ V a u) (-(fderiv ℝ V a u))
        rw [show u + fderiv ℝ V a u + -(fderiv ℝ V a u) = u by abel, norm_neg] at h
        exact h
      have h3 : ‖fderiv ℝ V a u‖ ≤ (K : ℝ) * ‖u‖ :=
        le_trans (ContinuousLinearMap.le_opNorm _ _)
          (mul_le_mul_of_nonneg_right hTa (norm_nonneg u))
      linarith
    have hinjT : Function.Injective
        (1 + fderiv ℝ V a : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) := by
      intro v w hvw
      have hsub : (1 + fderiv ℝ V a) (v - w) = 0 := by rw [map_sub, hvw, sub_self]
      have h2 : (1 - (K : ℝ)) * ‖v - w‖ ≤ 0 := by
        have h3 := hbound (v - w)
        rw [hsub, norm_zero] at h3
        exact h3
      have h4 : ‖v - w‖ = 0 := by nlinarith [norm_nonneg (v - w), hpos]
      exact sub_eq_zero.mp (norm_eq_zero.mp h4)
    have hker : (1 + fderiv ℝ V a : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)).ker
        = ⊥ := LinearMap.ker_eq_bot.mpr hinjT
    have hsurj' : (1 + fderiv ℝ V a : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)).range
        = ⊤ := LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp hinjT)
    exact ⟨ContinuousLinearEquiv.ofBijective (1 + fderiv ℝ V a) hker hsurj',
      DFunLike.coe_injective
        (ContinuousLinearEquiv.coeFn_ofBijective (1 + fderiv ℝ V a) hker hsurj')⟩
  have hder : ∀ a : EuclideanSpace ℝ (Fin N),
      HasFDerivAt (⇑H)
        ((hder_equiv a).choose : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) a := by
    intro a
    have h1 : HasFDerivAt F
        ((hder_equiv a).choose : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) a := by
      rw [(hder_equiv a).choose_spec]
      exact (hasFDerivAt_id a).add
        ((hV.contDiffAt (x := a)).differentiableAt hne).hasFDerivAt
    exact h1
  have hinv_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (⇑H.symm) :=
    Homeomorph.contDiff_symm H (f₀' := fun a => (hder_equiv a).choose) hder hFc
  exact ⟨F, ⇑H.symm, hFc, hinv_smooth, fun y => H.symm_apply_apply y, fun y => H.apply_symm_apply y,
    fun y => rfl⟩

end Work.Whitney.CutPush
