import Mathlib

namespace Work.Drive.Whitney

/-- **Kato's step lemma (idempotent form).**

If `P` and `Q` are idempotent continuous endomorphisms of a finite-dimensional real
space (here `EuclideanSpace ℝ (Fin m)`) with `‖P - Q‖ < 1`, then the "Kato map"
`S := Q * P + (1 - Q) * (1 - P)` is a bijection, it intertwines the ranges of `P` and
`Q` (`range (S ∘ P) = range Q`), and it fixes `Q` on the fixed-point set of `P`
(`P v = v → S v = Q v`).

The key algebraic identities are `S * P = Q * P = Q * S` (both `(1 - P) * P` and
`Q * (1 - Q)` vanish), so `S` maps `im P` onto `im Q` and `ker P` onto `ker Q`.
Injectivity is proved by splitting a vector `x` as `P x + (1 - P) x`: from `S x = 0`
one gets `Q (P x) = 0` and `(1 - Q) ((1 - P) x) = 0`, whence `P x = (P - Q) (P x)` and
`(1 - P) x = -((P - Q) ((1 - P) x))`; since `‖P - Q‖ < 1` both summands vanish.
Finiteness of `m` upgrades injectivity to bijectivity, and `Q = S * P * S⁻¹`
identifies the two ranges. -/
theorem katoStepBijective {m : ℕ}
    {P Q : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hP : P * P = P) (hQ : Q * Q = Q) (h : ‖P - Q‖ < 1) :
    Function.Bijective (fun v : EuclideanSpace ℝ (Fin m) => (Q * P + (1 - Q) * (1 - P)) v) ∧
      LinearMap.range (((Q * P + (1 - Q) * (1 - P) : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)).comp (P : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)))
        = LinearMap.range (Q : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ∧
      (∀ v : EuclideanSpace ℝ (Fin m), P v = v → (Q * P + (1 - Q) * (1 - P)) v = Q v) := by
  set S : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) := Q * P + (1 - Q) * (1 - P) with hS
  -- The basic vanishing identities coming from idempotency of `P` and `Q`.
  have hP1P : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hP, sub_self]
  have hP1mP : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hP, sub_self]
  have hQ1mQ : Q * (1 - Q) = 0 := by rw [mul_sub, mul_one, hQ, sub_self]
  have hSP : S * P = Q * P := by
    have h1 : (Q * P) * P = Q * P := by rw [mul_assoc, hP]
    have h2 : ((1 - Q) * (1 - P)) * P = 0 := by rw [mul_assoc, hP1P, mul_zero]
    rw [hS, add_mul, h1, h2, add_zero]
  have hQSP : Q * S = Q * P := by
    have h1 : Q * (Q * P) = Q * P := by rw [← mul_assoc, hQ]
    have h2 : Q * ((1 - Q) * (1 - P)) = 0 := by rw [← mul_assoc, hQ1mQ, zero_mul]
    rw [hS, mul_add, h1, h2, add_zero]
  have hQS : Q * S = S * P := by rw [hQSP, hSP]
  -- Pointwise expansion of `S`.
  have hexpand : ∀ x : EuclideanSpace ℝ (Fin m), S x = Q (P x) + (1 - Q) ((1 - P) x) := by
    intro x
    rw [hS, ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply]
  -- `S` is injective.
  have hker : ∀ x : EuclideanSpace ℝ (Fin m), S x = 0 → x = 0 := by
    intro x hx
    rw [hexpand x] at hx
    -- Apply `Q` to `S x = 0`; the term `Q * (1 - Q)` vanishes, so `Q (P x) = 0`.
    have hQu : Q (P x) = 0 := by
      have hcong : Q (Q (P x) + (1 - Q) ((1 - P) x)) = Q 0 := by rw [hx]
      rw [map_add, map_zero] at hcong
      have hQQ : Q (Q (P x)) = Q (P x) := by rw [← ContinuousLinearMap.mul_apply, hQ]
      have hQ1w : Q ((1 - Q) ((1 - P) x)) = 0 := by
        rw [← ContinuousLinearMap.mul_apply, hQ1mQ, ContinuousLinearMap.zero_apply]
      rw [hQQ, hQ1w, add_zero] at hcong
      exact hcong
    have hQw : (1 - Q) ((1 - P) x) = 0 := by
      rw [hQu, zero_add] at hx
      exact hx
    -- The `im P` component is a fixed point of `x ↦ (P - Q) x`.
    have hu_eq : P x = (P - Q) (P x) := by
      have hh : (P - Q) (P x) = P x := by
        rw [ContinuousLinearMap.sub_apply, ← ContinuousLinearMap.mul_apply, hP, hQu, sub_zero]
      exact hh.symm
    have hu0 : P x = 0 := by
      by_contra hne
      have hle : ‖P x‖ ≤ ‖P - Q‖ * ‖P x‖ := by
        calc ‖P x‖ = ‖(P - Q) (P x)‖ := congrArg norm hu_eq
          _ ≤ ‖P - Q‖ * ‖P x‖ := ContinuousLinearMap.le_opNorm _ _
      have hpos : 0 < ‖P x‖ := norm_pos_iff.mpr hne
      have hlt : ‖P - Q‖ * ‖P x‖ < 1 * ‖P x‖ := mul_lt_mul_of_pos_right h hpos
      rw [one_mul] at hlt
      linarith
    -- The `ker P` component is minus a fixed point of `x ↦ (P - Q) x`.
    have hQw' : Q ((1 - P) x) = (1 - P) x := by
      have hh := hQw
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply] at hh
      exact (sub_eq_zero.mp hh).symm
    have hPw : P ((1 - P) x) = 0 := by
      rw [← ContinuousLinearMap.mul_apply, hP1mP, ContinuousLinearMap.zero_apply]
    have hw_eq : (1 - P) x = -((P - Q) ((1 - P) x)) := by
      have hh : (P - Q) ((1 - P) x) = -((1 - P) x) := by
        rw [ContinuousLinearMap.sub_apply, hPw, hQw', zero_sub]
      rw [hh, neg_neg]
    have hw0 : (1 - P) x = 0 := by
      by_contra hne
      have hle : ‖(1 - P) x‖ ≤ ‖P - Q‖ * ‖(1 - P) x‖ := by
        calc ‖(1 - P) x‖ = ‖-((P - Q) ((1 - P) x))‖ := congrArg norm hw_eq
          _ = ‖(P - Q) ((1 - P) x)‖ := norm_neg _
          _ ≤ ‖P - Q‖ * ‖(1 - P) x‖ := ContinuousLinearMap.le_opNorm _ _
      have hpos : 0 < ‖(1 - P) x‖ := norm_pos_iff.mpr hne
      have hlt : ‖P - Q‖ * ‖(1 - P) x‖ < 1 * ‖(1 - P) x‖ := mul_lt_mul_of_pos_right h hpos
      rw [one_mul] at hlt
      linarith
    have hsum : x = P x + (1 - P) x := by
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
      abel
    rw [hsum, hu0, hw0, add_zero]
  have hinj : Function.Injective (fun v : EuclideanSpace ℝ (Fin m) => S v) := by
    intro a b hab
    change S a = S b at hab
    have h0 : S (a - b) = 0 := by rw [map_sub, hab, sub_self]
    exact sub_eq_zero.mp (hker (a - b) h0)
  -- Injectivity plus finite-dimensionality gives bijectivity.
  have hsurj : Function.Surjective (fun v : EuclideanSpace ℝ (Fin m) => S v) := by
    have hinj' : Function.Injective ⇑(((S : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) := hinj
    exact (LinearMap.injective_iff_surjective (f := ((S : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)))).mp hinj'
  have hbij : Function.Bijective (fun v : EuclideanSpace ℝ (Fin m) => S v) := ⟨hinj, hsurj⟩
  have hSPmap : ∀ x : EuclideanSpace ℝ (Fin m), S (P x) = Q (P x) := by
    intro x
    calc S (P x) = (S * P) x := by rw [ContinuousLinearMap.mul_apply]
      _ = (Q * P) x := by rw [hSP]
      _ = Q (P x) := by rw [ContinuousLinearMap.mul_apply]
  -- `range (S ∘ P) = range Q`, from `Q = S * P * S⁻¹`.
  have hrange : LinearMap.range (((S : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)).comp (P : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)))
        = LinearMap.range (Q : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) := by
    apply le_antisymm
    · intro y hy
      rw [LinearMap.mem_range] at hy ⊢
      obtain ⟨x, hx⟩ := hy
      refine ⟨P x, ?_⟩
      rw [LinearMap.comp_apply] at hx
      change Q (P x) = y
      rw [← hSPmap x]
      exact hx
    · intro y hy
      rw [LinearMap.mem_range] at hy ⊢
      obtain ⟨z, hz⟩ := hy
      obtain ⟨x, hx⟩ := hsurj z
      refine ⟨x, ?_⟩
      rw [LinearMap.comp_apply]
      change S (P x) = y
      rw [← ContinuousLinearMap.mul_apply, ← hQS, ContinuousLinearMap.mul_apply]
      have hx' : S x = z := hx
      rw [hx']
      exact hz
  refine ⟨hbij, hrange, ?_⟩
  -- `S` agrees with `Q` on the fixed-point set of `P`.
  intro v hv
  rw [hexpand v, hv]
  have h1 : (1 - P) v = 0 := by rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, hv, sub_self]
  rw [h1, map_zero, add_zero]

end Work.Drive.Whitney
