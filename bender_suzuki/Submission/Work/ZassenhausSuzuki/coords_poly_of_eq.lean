import Mathlib
import Submission.Work.ZassenhausSuzuki.TitsAux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Work.ZassenhausSuzuki

/-! ## The field-level content of `coords_poly_of_eq`

The group equation `heq` (an equality in Higman's group `A(K,θ)`) has two coordinate
consequences.  The `b`-coordinate is the informative one: after substituting
`la⁻¹ = al·(1+ν)`, `lb⁻¹ = 1+ν⁻¹` and the relation `al·θal·(1+θν) = θν` (which is
`hs` combined with `htν`) it collapses to

`hB' : (1+ν)·(ν⁻²ξ⁻¹+ν⁻¹) = (1+ν⁻¹)·θν·(ν²(νξ)⁻¹+ν)`.

The `a`-coordinate supplies the (independent) equation `hA` that rules out `ξ = 0`
(`xi_ne_zero_aux`).  For `ξ ≠ 0` the equation `hB'` is equivalent, after multiplying
by `ξ` and cancelling `1+ν`, to the `ξ`-linear relation

`eq1 : ξ·(ν⁻¹+θν) = ν⁻²+θν`,

applying `θ` to which (`eq2`) and multiplying by `hξ` gives the Suzuki identity. -/

/-- **Field step 0.**  `ξ ≠ 0`.  Here the `a`-coordinate equation `hA` is needed: with
`ξ = 0` it reads `al·(1+ν)·ν⁻¹ = (1+ν⁻¹)·ν + 1 = ν`, i.e. `al·(1+ν) = ν²`; applying `θ`
and combining with `halt : al·θal·(1+θν) = θν` gives `al·θν = 1`, while `hξ` gives
`ν·θν = 1`; hence `al = ν` and `ν·(1+ν) = ν²`, forcing `ν = 0`, contrary to `hν0`. -/
theorem coords_poly_xi_ne_zero_aux {K : Type*} [Field K] [CharP K 2] (θ : K ≃+* K) {ν ξ al : K}
    (hν0 : ν ≠ 0)
    (hξ : ξ * θ ξ = 1 + ν⁻¹ * θ ν⁻¹)
    (halt : al * θ al * (1 + θ ν) = θ ν)
    (hA : al * (1 + ν) * (ν⁻¹ ^ 2 * ξ⁻¹ + ν⁻¹)
        = (1 + ν⁻¹) * (ν ^ 2 * (ν * ξ)⁻¹ + ν) + 1) :
    ξ ≠ 0 := by
  intro hξ0
  have hq : θ ν ≠ 0 := (map_ne_zero θ).mpr hν0
  have hνq : ν * θ ν = 1 := by
    have h := hξ
    rw [map_inv₀] at h
    rw [hξ0, map_zero, mul_zero] at h
    have h1 : ν⁻¹ * (θ ν)⁻¹ = 1 := by
      have h2 : (1 : K) + ν⁻¹ * (θ ν)⁻¹ = 0 := h.symm
      have h3 : ν⁻¹ * (θ ν)⁻¹ = -1 := by linear_combination h2
      rwa [CharTwo.neg_eq] at h3
    have h4 : (ν * θ ν)⁻¹ = 1 := by rw [mul_inv]; exact h1
    rwa [inv_eq_one] at h4
  have hal1 : al * (1 + ν) = ν ^ 2 := by
    have h := hA
    rw [hξ0] at h
    simp only [inv_zero, mul_zero, zero_add] at h
    linear_combination (norm := (field_simp; try ring_nf; try (simp only [CharTwo.two_eq_zero,
      mul_zero, sub_zero, add_zero, zero_add, neg_zero, CharTwo.add_self_eq_zero]); try ring)) ν * h
  have hth : θ al * (1 + θ ν) = (θ ν) ^ 2 := by
    have h := congrArg θ hal1
    simpa only [map_mul, map_add, map_one, map_pow] using h
  have hal2 : al * θ ν = 1 := by
    have hal2' : al * (θ ν) ^ 2 = θ ν := by
      linear_combination (norm := ring) halt - al * hth
    have : θ ν * (al * θ ν) = θ ν * 1 := by
      linear_combination (norm := ring) hal2'
    exact mul_left_cancel₀ hq this
  have hal4 : al = ν := by
    have : al * θ ν = ν * θ ν := by rw [hal2, hνq]
    exact mul_right_cancel₀ hq this
  have hzero : ν = 0 := by
    have h := hal1
    rw [hal4] at h
    linear_combination (norm := (try ring_nf; try (simp only [CharTwo.two_eq_zero, mul_zero,
      sub_zero, add_zero, zero_add, neg_zero, CharTwo.add_self_eq_zero]); try ring)) h
  exact hν0 hzero

/-- **Field step 1.**  For `ξ ≠ 0`, the `b`-coordinate equation forces the `ξ`-linear
relation `ξ·(ν⁻¹+θν) = ν⁻²+θν`. -/
theorem coords_poly_eq1_aux {K : Type*} [Field K] [CharP K 2] (θ : K ≃+* K) {ν ξ : K}
    (hν0 : ν ≠ 0) (h1ν : 1 + ν ≠ 0) (hξne : ξ ≠ 0)
    (hB' : (1 + ν) * (ν⁻¹ ^ 2 * ξ⁻¹ + ν⁻¹)
        = (1 + ν⁻¹) * (θ ν) * (ν ^ 2 * (ν * ξ)⁻¹ + ν)) :
    ξ * (ν⁻¹ + θ ν) = ν⁻¹ ^ 2 + θ ν := by
  have h := hB'
  field_simp at h
  have hD : 1 + ν * ξ = ν ^ 2 * (θ ν) * (1 + ξ) := by
    have hh : (1 + ν) * (1 + ν * ξ) = (1 + ν) * (ν ^ 2 * (θ ν) * (1 + ξ)) := by
      linear_combination (norm := ring) h
    exact mul_left_cancel₀ h1ν hh
  have hDp : ν⁻¹ ^ 2 + ν⁻¹ * ξ = (θ ν) * (1 + ξ) := by
    linear_combination (norm := (field_simp; ring)) (ν⁻¹ ^ 2) * hD
  have heq1 : ξ * (ν⁻¹ + θ ν) = ν⁻¹ ^ 2 + θ ν := by
    linear_combination (norm := (try ring_nf; try (simp only [CharTwo.two_eq_zero, mul_zero,
      sub_zero, add_zero, zero_add, neg_zero, CharTwo.add_self_eq_zero]); try ring)) hDp
  exact heq1

/-- **Field step 2.**  From `eq1 : ξ·(ν⁻¹+θν) = ν⁻²+θν` and `hξ : ξ·θξ = 1+ν⁻¹θν⁻¹`
one concludes the Suzuki field identity.  `eq1` and its `θ`-image are multiplied and
`ξ·θξ` is replaced by `hξ`; the resulting equation is exactly `(νθν)²` times the goal. -/
theorem coords_poly_final_aux {K : Type*} [Field K] [CharP K 2] (θ : K ≃+* K) {ν ξ : K}
    (hν0 : ν ≠ 0)
    (hξ : ξ * θ ξ = 1 + ν⁻¹ * θ ν⁻¹)
    (heq1 : ξ * (ν⁻¹ + θ ν) = ν⁻¹ ^ 2 + θ ν) :
    (1 + ν ^ 2 * θ ν) * (1 + (θ ν) ^ 2 * θ (θ ν))
      = (1 + ν * θ ν) ^ 2 * (1 + θ ν * θ (θ ν)) := by
  have hq : θ ν ≠ 0 := (map_ne_zero θ).mpr hν0
  have hξ' : ξ * θ ξ = 1 + ν⁻¹ * (θ ν)⁻¹ := by
    rw [map_inv₀] at hξ; exact hξ
  have eq2 : θ ξ * ((θ ν)⁻¹ + θ (θ ν)) = (θ ν)⁻¹ ^ 2 + θ (θ ν) := by
    have h := congrArg θ heq1
    simp only [map_mul, map_add, map_inv₀, map_pow] at h
    convert h using 2 <;> ring
  have hmul : ξ * θ ξ * (ν⁻¹ + θ ν) * ((θ ν)⁻¹ + θ (θ ν))
      = (ν⁻¹ ^ 2 + θ ν) * ((θ ν)⁻¹ ^ 2 + θ (θ ν)) := by
    rw [← heq1, ← eq2]; ring
  have hE : (1 + ν⁻¹ * (θ ν)⁻¹) * (ν⁻¹ + θ ν) * ((θ ν)⁻¹ + θ (θ ν))
      = (ν⁻¹ ^ 2 + θ ν) * ((θ ν)⁻¹ ^ 2 + θ (θ ν)) := by
    rw [← hξ']; exact hmul
  have h2 := congrArg (fun t => t * (ν * θ ν) ^ 2) hE
  linear_combination (norm := (field_simp; ring_nf; simp only [CharTwo.two_eq_zero,
    show (4 : K) = 0 from (CharP.cast_eq_zero_iff K 2 4).mpr (by norm_num),
    mul_zero, zero_mul, sub_zero, add_zero, zero_add, neg_zero])) h2

/-- **HB III XI 11.13 (b), coordinate form.**  Combining the two coordinate equations
of the group relation `heq` with the field hypotheses yields the Suzuki polynomial
identity `(1+ν²θν)(1+(θν)²θ²ν) = (1+νθν)²(1+θνθ²ν)`, i.e. `θ²ν = ν²`. -/
theorem coords_poly_of_eq {K : Type*} [Field K] [CharP K 2] (θ : K ≃+* K)
    {ν ξ la lb al s : K}
    (hν1 : ν ≠ 1)
    (hs : s = al * θ al)
    (hla : la * (1 + ν) = al⁻¹)
    (hlb : lb * (1 + ν⁻¹) = 1)
    (htν : θ ν * (1 + s) = s)
    (hξ : ξ * θ ξ = 1 + ν⁻¹ * θ ν⁻¹)
    (heq : Work.ZassenhausSuzuki.SzA.hLam θ la⁻¹
        (Work.ZassenhausSuzuki.Xval θ ν ξ)
      = Work.ZassenhausSuzuki.SzA.hLam θ lb⁻¹
          (Work.ZassenhausSuzuki.Xval θ ν⁻¹ (ν * ξ)) * (⟨1, 0⟩ : Work.ZassenhausSuzuki.SzA K θ)) :
    (1 + ν ^ 2 * θ ν) * (1 + (θ ν) ^ 2 * θ (θ ν))
      = (1 + ν * θ ν) ^ 2 * (1 + θ ν * θ (θ ν)) := by
  by_cases hν0 : ν = 0
  · subst hν0; simp
  have h1ν : (1 : K) + ν ≠ 0 := by
    intro h1; apply hν1
    have h2 : ν = -1 := by linear_combination h1
    rw [h2]; exact CharTwo.neg_eq 1
  have hq : θ ν ≠ 0 := (map_ne_zero θ).mpr hν0
  have hla' : la⁻¹ = al * (1 + ν) := by
    have h := congrArg Inv.inv hla
    simp only [mul_inv, inv_inv] at h
    calc la⁻¹ = la⁻¹ * ((1 + ν)⁻¹ * (1 + ν)) := by rw [inv_mul_cancel₀ h1ν, mul_one]
      _ = (la⁻¹ * (1 + ν)⁻¹) * (1 + ν) := by rw [mul_assoc]
      _ = al * (1 + ν) := by rw [h]
  have hlb' : lb⁻¹ = 1 + ν⁻¹ := inv_eq_of_mul_eq_one_right hlb
  have halt : al * θ al * (1 + θ ν) = θ ν := by
    have h := htν
    rw [hs, mul_add, mul_one] at h
    linear_combination (norm := (try ring_nf; try (simp only [CharTwo.two_eq_zero, mul_zero,
      sub_zero, add_zero, zero_add, neg_zero, CharTwo.add_self_eq_zero]); try ring)) -h
  -- the two coordinate equations of `heq`
  have hA := congrArg SzA.a heq
  simp only [SzA.mul_a, SzA.hLam_a, Xval_a, inv_inv] at hA
  rw [hla', hlb'] at hA
  have hB := congrArg SzA.b heq
  simp only [SzA.mul_b, SzA.mul_a, SzA.one_a, SzA.one_b, SzA.hLam_a, SzA.hLam_b,
    Xval_a, Xval_b, map_one, mul_one, mul_zero, zero_add, add_zero, inv_inv] at hB
  rw [hla', hlb'] at hB
  simp only [map_mul, map_add, map_one, map_inv₀] at hB
  -- simplify the `b`-coordinate to `hB'`
  have hL : al * (1 + ν) * (θ al * (1 + θ ν)) * ((θ ν)⁻¹ * (ν⁻¹ ^ 2 * ξ⁻¹ + ν⁻¹))
      = (1 + ν) * (ν⁻¹ ^ 2 * ξ⁻¹ + ν⁻¹) := by
    linear_combination (norm := (try ring_nf; try (simp only [CharTwo.two_eq_zero, mul_zero,
      sub_zero, add_zero, zero_add, neg_zero, CharTwo.add_self_eq_zero]); try ring))
      ((1 + ν) * (ν⁻¹ ^ 2 * ξ⁻¹ + ν⁻¹) * (θ ν)⁻¹) * halt
      + ((1 + ν) * (ν⁻¹ ^ 2 * ξ⁻¹ + ν⁻¹)) * (inv_mul_cancel₀ hq)
  have hR : (1 + ν⁻¹) * (1 + (θ ν)⁻¹) * (θ ν * (ν ^ 2 * (ν * ξ)⁻¹ + ν))
        + (1 + ν⁻¹) * (ν ^ 2 * (ν * ξ)⁻¹ + ν)
      = (1 + ν⁻¹) * (θ ν) * (ν ^ 2 * (ν * ξ)⁻¹ + ν) := by
    linear_combination (norm := (try ring_nf; try (simp only [CharTwo.two_eq_zero, mul_zero,
      sub_zero, add_zero, zero_add, neg_zero, CharTwo.add_self_eq_zero]); try ring))
      ((1 + ν⁻¹) * (ν ^ 2 * (ν * ξ)⁻¹ + ν)) * (inv_mul_cancel₀ hq)
  have hB' : (1 + ν) * (ν⁻¹ ^ 2 * ξ⁻¹ + ν⁻¹)
      = (1 + ν⁻¹) * (θ ν) * (ν ^ 2 * (ν * ξ)⁻¹ + ν) := by
    rw [hL, hR] at hB
    exact hB
  have hξne : ξ ≠ 0 := coords_poly_xi_ne_zero_aux θ hν0 hξ halt hA
  exact coords_poly_final_aux θ hν0 hξ (coords_poly_eq1_aux θ hν0 h1ν hξne hB')

end Work.ZassenhausSuzuki
