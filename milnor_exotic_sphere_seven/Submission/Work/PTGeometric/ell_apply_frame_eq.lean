import Mathlib
import Submission.Work.PTGeometric.AmbientPerturbation

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The frame identity of the Grassmannian charts: `ℓ (Q (ℓ† (S⁻¹ t))) = t`

Let `Q` be the orthogonal projection onto a plane `V = im Q ⊆ ℝⁿ` of rank `k` (i.e. `Q ∈ Gr n k`,
the set of orthogonal projections of trace `k`) and let `ℓ : ℝⁿ → ℝᵏ` be injective on `V`.  Then

  `S := ℓ ∘ Q ∘ ℓ† : ℝᵏ → ℝᵏ`

is invertible, and `v ↦ Q (ℓ† (S⁻¹ v))` is the `ℓ`-adapted frame of the plane: applying `ℓ` to it
returns the identity.

This is the algebraic heart of the chart family of `Work.PTGeometric.AmbCharts` (see
`Submission/Work/PTGeometric/README.md` §12): the adapted frame over a chart is
`e j y = P y (ℓ† ((Λ y)⁻¹ (EuclideanSpace.single j 1)))` with `Λ = ℓ ∘ P ∘ ℓ†`, and the
`ell_frame` field is precisely this identity, together with the standard-basis sum
`∑ j, t j • EuclideanSpace.single j 1 = t`.

The proof: `S` is positive semidefinite, because
`⟪S v, v⟫ = ⟪Q (ℓ† v), ℓ† v⟫ = ⟪Q (ℓ† v), Q (ℓ† v)⟫` (`Q` self-adjoint and idempotent), so
`S v = 0` forces `Q (ℓ† v) = 0`, i.e. `ℓ† v ∈ (im Q)ᵖ`; hence `⟪v, ℓ z⟫ = ⟪ℓ† v, z⟫ = 0` for all
`z ∈ im Q`, and `ℓ (im Q) = ℝᵏ` because `ℓ` is injective on the `k`-dimensional plane `im Q` (the
rank count `finrank (im Q) = trace Q = k`) and `dim ℝᵏ = k`.  So `S` is injective, hence (finite
dimension) invertible, and `S (S⁻¹ t) = t`.
-/

set_option maxHeartbeats 800000

open scoped InnerProduct

namespace Work.PTGeometric

theorem ell_apply_frame_eq {n k : ℕ} (ℓ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin k)) (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hQ : Q ∈ Work.PTGeometric.Gr n k) (hinj : ∀ z : EuclideanSpace ℝ (Fin n), Q z = z → ℓ z = 0 → z = 0) (t : EuclideanSpace ℝ (Fin k)) : ℓ (Q (ℓ.adjoint ((ContinuousLinearMap.inverse (ℓ.comp (Q.comp ℓ.adjoint))) t))) = t := by
  have hQadj : Q.adjoint = Q := hQ.1
  have hQidem : Q * Q = Q := hQ.2.1
  -- `Q` is idempotent as a plain function
  have hcomp : ∀ x : Amb n, Q (Q x) = Q x := by
    intro x
    have h : (Q * Q : Amb n →L[ℝ] Amb n) x = Q x := by rw [hQidem]
    simpa using h
  -- idempotency of `Q` as a linear map, and the rank count `finrank (im Q) = trace Q = k`
  have hQidem_lin : (Q : Amb n →ₗ[ℝ] Amb n) * (Q : Amb n →ₗ[ℝ] Amb n)
      = (Q : Amb n →ₗ[ℝ] Amb n) := by
    refine LinearMap.ext fun y => ?_
    rw [Module.End.mul_eq_comp, LinearMap.comp_apply]
    exact hcomp y
  have hQfin : Module.finrank ℝ (LinearMap.range (Q : Amb n →ₗ[ℝ] Amb n)) = k := by
    have hproj : LinearMap.IsProj (LinearMap.range (Q : Amb n →ₗ[ℝ] Amb n))
        (Q : Amb n →ₗ[ℝ] Amb n) :=
      (LinearMap.isProj_range_iff_isIdempotentElem (Q : Amb n →ₗ[ℝ] Amb n)).mpr hQidem_lin
    have h1 : LinearMap.trace ℝ (Amb n) (Q : Amb n →ₗ[ℝ] Amb n)
        = (Module.finrank ℝ (LinearMap.range (Q : Amb n →ₗ[ℝ] Amb n)) : ℝ) := hproj.trace
    have h2 : LinearMap.trace ℝ (Amb n) (Q : Amb n →ₗ[ℝ] Amb n) = (k : ℝ) := hQ.2.2
    have h3 : (Module.finrank ℝ (LinearMap.range (Q : Amb n →ₗ[ℝ] Amb n)) : ℝ) = (k : ℝ) := by
      rw [← h1, h2]
    exact Nat.cast_injective h3
  -- `S := ℓ ∘ Q ∘ ℓ†` is injective
  have hSinj0 : ∀ v : Amb k, (ℓ.comp (Q.comp ℓ.adjoint)) v = 0 → v = 0 := by
    intro v hv
    have step1 : inner ℝ (Q (ℓ.adjoint v)) (ℓ.adjoint v)
        = inner ℝ (Q (Q (ℓ.adjoint v))) (ℓ.adjoint v) :=
      (congrArg (fun u => inner ℝ u (ℓ.adjoint v)) (hcomp (ℓ.adjoint v))).symm
    have step2 : inner ℝ (Q (Q (ℓ.adjoint v))) (ℓ.adjoint v)
        = inner ℝ (Q (ℓ.adjoint v)) (Q.adjoint (ℓ.adjoint v)) :=
      (ContinuousLinearMap.adjoint_inner_right Q (Q (ℓ.adjoint v)) (ℓ.adjoint v)).symm
    have step3 : inner ℝ (Q (ℓ.adjoint v)) (Q.adjoint (ℓ.adjoint v))
        = inner ℝ (Q (ℓ.adjoint v)) (Q (ℓ.adjoint v)) :=
      congrArg (fun A : Amb n →L[ℝ] Amb n => inner ℝ (Q (ℓ.adjoint v)) (A (ℓ.adjoint v))) hQadj
    -- the quadratic form of `S` is the square of `Q (ℓ† v)`
    have hquad : inner ℝ ((ℓ.comp (Q.comp ℓ.adjoint)) v) v
        = inner ℝ (Q (ℓ.adjoint v)) (Q (ℓ.adjoint v)) := by
      calc inner ℝ ((ℓ.comp (Q.comp ℓ.adjoint)) v) v
          = inner ℝ (ℓ (Q (ℓ.adjoint v))) v := rfl
        _ = inner ℝ (Q (ℓ.adjoint v)) (ℓ.adjoint v) :=
              (ContinuousLinearMap.adjoint_inner_right ℓ (Q (ℓ.adjoint v)) v).symm
        _ = inner ℝ (Q (Q (ℓ.adjoint v))) (ℓ.adjoint v) := step1
        _ = inner ℝ (Q (ℓ.adjoint v)) (Q.adjoint (ℓ.adjoint v)) := step2
        _ = inner ℝ (Q (ℓ.adjoint v)) (Q (ℓ.adjoint v)) := step3
    have hQlv : Q (ℓ.adjoint v) = 0 := by
      have hz : inner ℝ (Q (ℓ.adjoint v)) (Q (ℓ.adjoint v)) = 0 := by
        rw [← hquad, hv]
        simp
      exact inner_self_eq_zero.mp hz
    -- for `z` in the plane, `⟪ℓ† v, z⟫ = 0`
    have hD : ∀ z : Amb n, Q z = z → inner ℝ (ℓ.adjoint v) z = 0 := by
      intro z hz
      calc inner ℝ (ℓ.adjoint v) z
          = inner ℝ (ℓ.adjoint v) (Q z) := by rw [hz]
        _ = inner ℝ (Q.adjoint (ℓ.adjoint v)) z :=
              (ContinuousLinearMap.adjoint_inner_left Q z (ℓ.adjoint v)).symm
        _ = inner ℝ (Q (ℓ.adjoint v)) z := by rw [hQadj]
        _ = 0 := by rw [hQlv, inner_zero_left]
    -- the restriction of `ℓ` to the plane is an isomorphism onto `ℝᵏ`
    let V : Submodule ℝ (Amb n) := LinearMap.range (Q : Amb n →ₗ[ℝ] Amb n)
    let ℓV : V →ₗ[ℝ] Amb k := (ℓ : Amb n →ₗ[ℝ] Amb k).comp V.subtype
    have hinjV : Function.Injective ℓV := by
      intro x y hxy
      have hxy' : ℓ (x : Amb n) = ℓ (y : Amb n) := hxy
      have hmem : (x : Amb n) - (y : Amb n) ∈ V := V.sub_mem x.2 y.2
      obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hmem
      have hu' : Q u = (x : Amb n) - (y : Amb n) := hu
      have hQz : Q ((x : Amb n) - (y : Amb n)) = (x : Amb n) - (y : Amb n) := by
        rw [← hu']
        exact hcomp u
      have hℓz : ℓ ((x : Amb n) - (y : Amb n)) = 0 := by
        rw [map_sub, hxy', sub_self]
      have hz0 : (x : Amb n) - (y : Amb n) = 0 := hinj _ hQz hℓz
      exact Subtype.ext (sub_eq_zero.mp hz0)
    have hfin : Module.finrank ℝ (LinearMap.range ℓV) = k := by
      rw [LinearMap.finrank_range_of_inj hinjV]
      exact hQfin
    have hF : Module.finrank ℝ (Amb k) = k := by
      rw [finrank_euclideanSpace]
      simp
    have htop : LinearMap.range ℓV = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by rw [hfin, hF])
    have hsurj : Function.Surjective ℓV := LinearMap.range_eq_top.mp htop
    -- hence `v = 0`
    have hFzero : ∀ w : Amb k, inner ℝ v w = 0 := by
      intro w
      obtain ⟨x, hx⟩ := hsurj w
      have hx' : ℓ (x : Amb n) = w := hx
      have hxV : Q (x : Amb n) = (x : Amb n) := by
        obtain ⟨u, hu⟩ := LinearMap.mem_range.mp x.2
        have hu' : Q u = (x : Amb n) := hu
        rw [← hu']
        exact hcomp u
      calc inner ℝ v w
          = inner ℝ v (ℓ (x : Amb n)) := by rw [hx']
        _ = inner ℝ (ℓ.adjoint v) (x : Amb n) :=
              (ContinuousLinearMap.adjoint_inner_left ℓ (x : Amb n) v).symm
        _ = 0 := hD (x : Amb n) hxV
    exact inner_self_eq_zero.mp (by rw [← hFzero v])
  have hinjS : Function.Injective (ℓ.comp (Q.comp ℓ.adjoint)) := by
    intro v w hvw
    have h : (ℓ.comp (Q.comp ℓ.adjoint)) (v - w) = 0 := by
      rw [map_sub, hvw, sub_self]
    exact sub_eq_zero.mp (hSinj0 (v - w) h)
  -- finite dimension: injective `⇒` invertible, and apply the inverse
  have hker : (ℓ.comp (Q.comp ℓ.adjoint)).ker = ⊥ := LinearMap.ker_eq_bot.mpr hinjS
  have hrange : (ℓ.comp (Q.comp ℓ.adjoint)).range = ⊤ :=
    (LinearMap.ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank
      (rfl : Module.finrank ℝ (Amb k) = Module.finrank ℝ (Amb k))).mp hker
  have hf : (ℓ.comp (Q.comp ℓ.adjoint)).IsInvertible :=
    ⟨ContinuousLinearEquiv.ofBijective (ℓ.comp (Q.comp ℓ.adjoint)) hker hrange,
      ContinuousLinearEquiv.coe_ofBijective _ _ _⟩
  change (ℓ.comp (Q.comp ℓ.adjoint)) ((ℓ.comp (Q.comp ℓ.adjoint)).inverse t) = t
  exact ContinuousLinearMap.IsInvertible.self_apply_inverse hf t

end Work.PTGeometric
