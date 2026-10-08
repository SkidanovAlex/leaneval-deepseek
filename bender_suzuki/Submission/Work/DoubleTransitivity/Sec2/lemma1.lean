import Mathlib
import Submission.Work.DoubleTransitivity.Basic
import Submission.Work.DoubleTransitivity.App1.Defs
import Submission.Work.DoubleTransitivity.Sec1.unique_fixed
import Submission.Work.DoubleTransitivity.Sec2.prop1a_unique

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.DoubleTransitivity.Sec2.lemma1`

Peterfalvi, *Le théorème de Bender–Suzuki I*, Ch. I §2 **Lemma 1** (p. 152):

> Let `X` be a subgroup of odd order of `H ∈ Ω`, `u ∈ Inv(H)` and `t ∈ Inv(G∖H)`.
> Then `|u^X| ≥ |J(X,t)|`.

In the vocabulary of this development: `X ≤ H`, `u` an involution of `H`, `t` an involution
outside `H`; the assertion is

`(invertedBy X t).ncard ≤ (conjOrbit X u).ncard`.

The proof is the one of the source.  It suffices to show that

`x ↦ x⁻¹ * u * x` is injective on `J(X,t) = invertedBy X t`,

since its image visibly lies in `u^X = conjOrbit X u`.  So let `x, y ∈ J(X,t)` with
`x⁻¹ux = y⁻¹uy`.  Because `t` inverts every element of `J(X,t)`, both `a = x t` and `b = y t`
are involutions of `G`, and conjugating the equality `x⁻¹ux = y⁻¹uy` by `t` (note
`(xt)⁻¹ u (xt) = t (x⁻¹ux) t`) gives

`a⁻¹ u a = b⁻¹ u b =: w`.

Finally `u` and `w` fix no common point of `Ω`: `u` is an involution of `H`, so its unique fixed
point is `pt H`, whereas `w ∈ H` would give `x⁻¹ u x ∈ H ⊓ H^t`, an intersection of odd order
containing the conjugate `x⁻¹ux` of the involution `u` — impossible since `t ∉ H`.  Hence
Peterfalvi I §2 Prop. 1 (a) (`prop1a_unique`) applies to the pair `(u, w)`: the involution
conjugating `u` to `w` is unique, so `a = b`, i.e. `x t = y t` and `x = y`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Submission.Blueprint

namespace Work.DoubleTransitivity.Sec2

/-- Conjugating an involution again gives an involution. -/
private theorem orderOf_conj_inv_eq_two {G : Type} [Group G] {u a : G} (hu : orderOf u = 2) :
    orderOf (a⁻¹ * u * a) = 2 := by
  simpa [MulAut.conj_apply, hu] using MulEquiv.orderOf_eq (MulAut.conj a⁻¹) u

theorem lemma1 {G : Type} [Group G] [Finite G] {H : Subgroup G} (hH : IsBender H)
    (hne : H ≠ ⊤) {X : Subgroup G} (hX : X ≤ H) (hodd : Odd (Nat.card ↥X))
    {u : G} (hu : u ∈ Submission.Blueprint.involutions (H : Set G))
    {t : G} (ht : orderOf t = 2) (htH : t ∉ H) :
    (Submission.Blueprint.invertedBy X t).ncard ≤ (conjOrbit X u).ncard := by
  classical
  have huH : u ∈ H := hu.1
  have hu2 : orderOf u = 2 := hu.2
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have htin : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  -- `x ↦ x⁻¹ * u * x` is injective on `J(X,t)`
  have hinj : Set.InjOn (fun x : G => x⁻¹ * u * x)
      (Submission.Blueprint.invertedBy X t) := by
    intro x hx y hy hxy
    have hxy' : x⁻¹ * u * x = y⁻¹ * u * y := hxy
    have hxX : x ∈ X := hx.1
    have hyX : y ∈ X := hy.1
    have hxH : x ∈ H := hX hxX
    have hyH : y ∈ H := hX hyX
    have hxinv : t * x * t⁻¹ = x⁻¹ := hx.2
    have hyinv : t * y * t⁻¹ = y⁻¹ := hy.2
    -- `t` inverts `x` and `y`, hence `x * t` and `y * t` are involutions different from `1`
    have htx : t * x = x⁻¹ * t := by
      calc t * x = (t * x * t⁻¹) * t := by group
        _ = x⁻¹ * t := by rw [hxinv]
    have hxt2 : orderOf (x * t) = 2 := by
      refine orderOf_eq_prime ?_ ?_
      · rw [pow_two]
        calc (x * t) * (x * t) = x * (t * x) * t := by group
          _ = x * (x⁻¹ * t) * t := by rw [htx]
          _ = 1 := by simp [ht2]
      · intro h
        have hxt : t = x⁻¹ := by
          calc t = x⁻¹ * (x * t) := by group
            _ = x⁻¹ * 1 := by rw [h]
            _ = x⁻¹ := mul_one _
        exact htH (by rw [hxt]; exact hX (X.inv_mem hxX))
    have hty : t * y = y⁻¹ * t := by
      calc t * y = (t * y * t⁻¹) * t := by group
        _ = y⁻¹ * t := by rw [hyinv]
    have hyt2 : orderOf (y * t) = 2 := by
      refine orderOf_eq_prime ?_ ?_
      · rw [pow_two]
        calc (y * t) * (y * t) = y * (t * y) * t := by group
          _ = y * (y⁻¹ * t) * t := by rw [hty]
          _ = 1 := by simp [ht2]
      · intro h
        have hyt : t = y⁻¹ := by
          calc t = y⁻¹ * (y * t) := by group
            _ = y⁻¹ * 1 := by rw [h]
            _ = y⁻¹ := mul_one _
        exact htH (by rw [hyt]; exact hX (X.inv_mem hyX))
    -- conjugating by `t` turns `x⁻¹ux = y⁻¹uy` into `(xt)⁻¹u(xt) = (yt)⁻¹u(yt)`
    have hconj : (x * t)⁻¹ * u * (x * t) = (y * t)⁻¹ * u * (y * t) := by
      calc (x * t)⁻¹ * u * (x * t) = t * (x⁻¹ * u * x) * t := by
            rw [mul_inv_rev, htin]; group
        _ = t * (y⁻¹ * u * y) * t := by rw [hxy']
        _ = (y * t)⁻¹ * u * (y * t) := by rw [mul_inv_rev, htin]; group
    -- the common conjugate is an involution
    have hw2 : orderOf ((x * t)⁻¹ * u * (x * t)) = 2 := orderOf_conj_inv_eq_two hu2
    -- `u` and it fix no common point of `Ω`
    have hno : ¬ ∃ ω : Omega H, u • ω = ω ∧ ((x * t)⁻¹ * u * (x * t)) • ω = ω := by
      rintro ⟨ω, huω, hwω⟩
      have hu_pt : u • pt H = pt H := by rw [smul_pt, mk_one_eq_iff]; exact huH
      have hω : ω = pt H := Sec1.eq_of_smul_eq_of_orderOf_eq_two hH hu2 huω hu_pt
      rw [hω, smul_pt] at hwω
      have hwH : (x * t)⁻¹ * u * (x * t) ∈ H := mk_one_eq_iff.mp hwω
      -- hence `x⁻¹ * u * x ∈ H ⊓ conj t H`, contradicting the Bender property
      have hcH : x⁻¹ * u * x ∈ H := H.mul_mem (H.mul_mem (H.inv_mem hxH) huH) hxH
      have hcw : t⁻¹ * (x⁻¹ * u * x) * t = (x * t)⁻¹ * u * (x * t) := by
        rw [mul_inv_rev, htin]; group
      have hc_conj : x⁻¹ * u * x ∈ conj t H :=
        (mem_conj t (x⁻¹ * u * x) H).mpr (by rw [hcw]; exact hwH)
      have hc2 : orderOf (x⁻¹ * u * x) = 2 := orderOf_conj_inv_eq_two hu2
      have hdvd : 2 ∣ Nat.card ↥(H ⊓ conj t H) :=
        dvd_trans (by rw [Nat.card_zpowers, hc2])
          (Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr ⟨hcH, hc_conj⟩))
      exact hH.2 t htH hdvd
    -- uniqueness of the involution conjugating `u` to `w` (Peterfalvi I §2 Prop. 1 (a))
    obtain ⟨v, hv1, hv2⟩ := prop1a_unique hH hu2 hw2 hno
    have h1 : x * t = v := hv2 (x * t) ⟨hxt2, rfl⟩
    have h2 : y * t = v := hv2 (y * t) ⟨hyt2, hconj.symm⟩
    exact mul_right_cancel (h1.trans h2.symm)
  -- the image of the injection lies in `u^X`
  have himg : (fun x : G => x⁻¹ * u * x) '' (Submission.Blueprint.invertedBy X t)
      ⊆ conjOrbit X u := by
    rintro v ⟨x, hx, hvx⟩
    exact ⟨x, hx.1, hvx⟩
  calc (Submission.Blueprint.invertedBy X t).ncard
      = ((fun x : G => x⁻¹ * u * x) '' (Submission.Blueprint.invertedBy X t)).ncard :=
        hinj.ncard_image.symm
    _ ≤ (conjOrbit X u).ncard := Set.ncard_le_ncard himg

end Work.DoubleTransitivity.Sec2
