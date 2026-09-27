import Mathlib
import Submission.Work.Mostow.homoExtAux

/-!
# The absolute determinant of a conformal linear map

Let `E n` be Euclidean `n`-space, `u ψ : E n` unit vectors, `s > 0` and `L : E n →L[ℝ] E n` a
continuous linear map with

* `L u = ψ`,
* `L` maps `uᗮ` into `ψᗮ`,
* `L` scales every vector of `uᗮ` by the factor `1/s` in norm.

Then `L` is block diagonal with respect to the orthogonal decompositions
`E n = ℝ∙u ⊕ uᗮ = ℝ∙ψ ⊕ ψᗮ`: it is a similarity of ratio `1` on the line `ℝ∙u` and a similarity
of ratio `1/s` on the hyperplane `uᗮ`.  Consequently

`|L.det| = (1/s) ^ (n - 1) = s ^ (-(n : ℝ) + 1)`.

The proof computes the determinant of the self-adjoint operator `T = L⋆ L`, which fixes `u` and
acts as the scalar `1/s²` on `uᗮ` (both obtained from the norm hypothesis via polarisation);
`T` therefore acts invertibly on the quotient `E n ⧸ ℝ∙u` as `1/s²`, and its determinant is
`(1/s²) ^ (n - 1)`.  Finally `det T = |det L|²` by the norm-determinant identity, and the
`s`-exponent is rewritten in terms of real powers.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

theorem conformalAbsDet (n : ℕ) (hn : 1 ≤ n)
    (u ψ : Submission.Mostow.E n) (hu : ‖u‖ = 1) (hψ : ‖ψ‖ = 1)
    (s : ℝ) (hs : 0 < s) (L : Submission.Mostow.E n →L[ℝ] Submission.Mostow.E n)
    (hLu : L u = ψ)
    (horth : ∀ v : Submission.Mostow.E n, inner ℝ u v = 0 → inner ℝ ψ (L v) = 0)
    (hnorm : ∀ v : Submission.Mostow.E n, inner ℝ u v = 0 → ‖L v‖ = ‖v‖ / s) :
    |L.det| = s ^ (-(n : ℝ) + 1) := by
  have hsne : s ≠ 0 := ne_of_gt hs
  have hu_ne : u ≠ 0 := by intro h; rw [h, norm_zero] at hu; exact one_ne_zero hu.symm
  have huu : inner ℝ u u = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have hψψ : inner ℝ ψ ψ = 1 := by rw [real_inner_self_eq_norm_sq, hψ]; norm_num
  have hLu' : (L : E n →ₗ[ℝ] E n) u = ψ := hLu
  have horth' : ∀ v : E n, inner ℝ u v = 0 → inner ℝ ψ ((L : E n →ₗ[ℝ] E n) v) = 0 := horth
  have hnorm' : ∀ v : E n, inner ℝ u v = 0 → ‖(L : E n →ₗ[ℝ] E n) v‖ = ‖v‖ / s := hnorm
  -- `T = L⋆ L` fixes `u`
  have hTu0 : (LinearMap.adjoint (L : E n →ₗ[ℝ] E n) ∘ₗ (L : E n →ₗ[ℝ] E n)) u = u := by
    show LinearMap.adjoint (L : E n →ₗ[ℝ] E n) ((L : E n →ₗ[ℝ] E n) u) = u
    rw [hLu']
    apply ext_inner_right ℝ
    intro w
    rw [LinearMap.adjoint_inner_left]
    have hw : inner ℝ u (w - inner ℝ u w • u) = 0 := by
      rw [inner_sub_right, inner_smul_right, huu, mul_one, sub_self]
    have hLw : (L : E n →ₗ[ℝ] E n) w =
        inner ℝ u w • ψ + (L : E n →ₗ[ℝ] E n) (w - inner ℝ u w • u) := by
      conv_lhs => rw [show w = inner ℝ u w • u + (w - inner ℝ u w • u) from by rw [add_sub_cancel]]
      rw [map_add, map_smul, hLu']
    rw [hLw, inner_add_right, inner_smul_right, hψψ, mul_one, horth' _ hw, add_zero]
  -- `T = L⋆ L` is the scalar `1/s²` on `uᗮ`
  have hTv0 : ∀ v : E n, inner ℝ u v = 0 →
      (LinearMap.adjoint (L : E n →ₗ[ℝ] E n) ∘ₗ (L : E n →ₗ[ℝ] E n)) v = (1/s^2) • v := by
    have hpol : ∀ v w : E n, inner ℝ u v = 0 → inner ℝ u w = 0 →
        inner ℝ ((L : E n →ₗ[ℝ] E n) v) ((L : E n →ₗ[ℝ] E n) w) = (1/s^2) * inner ℝ v w := by
      intro v w hv hw
      have hvw : inner ℝ u (v + w) = 0 := by rw [inner_add_right, hv, hw, add_zero]
      rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
          real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two]
      rw [← map_add, hnorm' (v+w) hvw, hnorm' v hv, hnorm' w hw]
      field_simp
    intro v hv
    show LinearMap.adjoint (L : E n →ₗ[ℝ] E n) ((L : E n →ₗ[ℝ] E n) v) = (1/s^2) • v
    apply ext_inner_right ℝ
    intro w
    rw [LinearMap.adjoint_inner_left, real_inner_smul_left]
    have hw : inner ℝ u (w - inner ℝ u w • u) = 0 := by
      rw [inner_sub_right, inner_smul_right, huu, mul_one, sub_self]
    have hLw : (L : E n →ₗ[ℝ] E n) w =
        inner ℝ u w • ψ + (L : E n →ₗ[ℝ] E n) (w - inner ℝ u w • u) := by
      conv_lhs => rw [show w = inner ℝ u w • u + (w - inner ℝ u w • u) from by rw [add_sub_cancel]]
      rw [map_add, map_smul, hLu']
    have hvψ : inner ℝ ((L : E n →ₗ[ℝ] E n) v) ψ = 0 := by
      rw [real_inner_comm]; exact horth' v hv
    have hvw : inner ℝ v (w - inner ℝ u w • u) = inner ℝ v w := by
      rw [inner_sub_right, inner_smul_right, ← real_inner_comm v u, hv, mul_zero, sub_zero]
    rw [hLw, inner_add_right, inner_smul_right, hvψ, mul_zero, zero_add, hpol v _ hv hw, hvw]
  set T : E n →ₗ[ℝ] E n := LinearMap.adjoint (L : E n →ₗ[ℝ] E n) ∘ₗ (L : E n →ₗ[ℝ] E n) with hTdef
  have hTu : T u = u := by rw [hTdef]; exact hTu0
  have hTv : ∀ v : E n, inner ℝ u v = 0 → T v = (1/s^2) • v := by
    intro v hv; rw [hTdef]; exact hTv0 v hv
  -- block decomposition of `T` with respect to the line `ℝ∙u`
  have hle : (ℝ ∙ u) ≤ (ℝ ∙ u).comap T := by
    rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_comap, Submodule.mem_span_singleton]
    exact ⟨1, by rw [one_smul]; exact hTu.symm⟩
  have hdetmul := LinearMap.det_eq_det_mul_det (ℝ ∙ u) T hle
  have hres : T.restrict hle = LinearMap.id := by
    apply LinearMap.ext
    intro x
    rw [LinearMap.restrict_apply, LinearMap.id_apply]
    apply Subtype.ext
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp x.2
    change T (x : E n) = (x : E n)
    rw [← ha, map_smul, hTu]
  have hmapQ : (ℝ ∙ u).mapQ (ℝ ∙ u) T hle =
      (1/s^2) • (LinearMap.id : (E n ⧸ (ℝ ∙ u)) →ₗ[ℝ] (E n ⧸ (ℝ ∙ u))) := by
    apply LinearMap.ext
    intro x
    refine Submodule.Quotient.induction_on (p := (ℝ ∙ u)) x ?_
    intro y
    rw [Submodule.mapQ_apply, LinearMap.smul_apply, LinearMap.id_apply,
      ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    have hy : y = inner ℝ u y • u + (y - inner ℝ u y • u) := by rw [add_sub_cancel]
    have hvy : inner ℝ u (y - inner ℝ u y • u) = 0 := by
      rw [inner_sub_right, inner_smul_right, huu, mul_one, sub_self]
    have hTy : T y = inner ℝ u y • u + (1/s^2) • (y - inner ℝ u y • u) := by
      conv_lhs => rw [hy]
      rw [map_add, map_smul, hTu, hTv _ hvy]
    have vec_id : ∀ (a : ℝ) (z : E n), a • u + (1/s^2) • (z - a • u) - (1/s^2) • z
        = ((1 - 1/s^2) * a) • u := by intro a z; module
    have hsub : T y - (1/s^2) • y = ((1 - 1/s^2) * inner ℝ u y) • u := by
      rw [hTy]; exact vec_id (inner ℝ u y) y
    rw [hsub]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
  have hfin : Module.finrank ℝ (E n ⧸ (ℝ ∙ u)) = n - 1 := by
    have h1 : Module.finrank ℝ (↥(ℝ ∙ u)) = 1 := finrank_span_singleton hu_ne
    have h2 := Submodule.finrank_quotient_add_finrank (ℝ ∙ u)
    rw [h1, finrank_euclideanSpace_fin] at h2
    omega
  have hdetT : T.det = (1/s^2)^(n-1) := by
    rw [hdetmul, hres, LinearMap.det_id, hmapQ, LinearMap.det_smul, LinearMap.det_id, hfin]
    ring
  -- `det T = |det L|²`
  have hsq : |L.det|^2 = (1/s^2)^(n-1) := by
    have h := LinearMap.normDet_sq (L : E n →ₗ[ℝ] E n)
    have h2 := LinearMap.normDet_eq_norm_det (L : E n →ₗ[ℝ] E n)
    rw [h2, Real.norm_eq_abs] at h
    rw [← hdetT]
    rw [show T.det = LinearMap.det (LinearMap.adjoint (L : E n →ₗ[ℝ] E n) ∘ₗ (L : E n →ₗ[ℝ] E n))
        from by rw [hTdef]]
    simpa using h
  have hs1 : |L.det| = (1/s)^(n-1) := by
    have h3 : ((1/s)^(n-1))^2 = (1/s^2)^(n-1) := by
      rw [show (1:ℝ)/s^2 = ((1:ℝ)/s)^2 by rw [div_pow, one_pow], ← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [← Real.sqrt_sq (abs_nonneg L.det), hsq, ← h3, Real.sqrt_sq (pow_nonneg (by positivity) _)]
  rw [hs1]
  have hn1 : (n : ℝ) = ((n - 1 : ℕ) : ℝ) + 1 := by
    have h := Nat.cast_sub hn (R := ℝ) (m := 1) (n := n)
    push_cast at h ⊢
    linarith
  have hexp : -(n : ℝ) + 1 = -(((n - 1 : ℕ) : ℝ)) := by rw [hn1]; ring
  rw [hexp, Real.rpow_neg (le_of_lt hs), Real.rpow_natCast, one_div, inv_pow]

end Work.Mostow
