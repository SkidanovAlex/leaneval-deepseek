import Mathlib
import Submission.Work.Thom.Orientation.Mpun_gaugeEnd_neg

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism.FrameSigns

open Work.Thom

/-!
# The orientation character of a negative-determinant gauge

`Work.Thom.gaugeEnd D hD` is the gauge automorphism `(y, v) ↦ (y, D y v)` of the trivial bundle
`Y × ℝⁿ`.  Its pullback acts on the punctured relative cohomology
`H^n(Y × ℝⁿ, Y × (ℝⁿ ∖ 0); ℤ)`, and `Work.Thom.Orientation.Mpun_gaugeEnd_neg` computes this action
on the model class `Work.Thom.Mpun n Y`: it is `-1` when `det (D y) < 0` for all `y`.

Here we lift that statement from the model class to *every* class: by the Thom isomorphism
`Work.Thom.Mpun_isModel`, every class of `H^n(Y × ℝⁿ, Y × (ℝⁿ ∖ 0); ℤ)` is of the form
`π^*(a) ⌣ Mpun n Y` with `a ∈ H⁰(Y; ℤ)`, and the pullback of the gauge is a ring map for the mixed
cup product (`Work.Thom.mixedCupC_pairNatural`) which fixes `π^*(a)` (the gauge is the identity on
the base) and sends `Mpun n Y` to `-Mpun n Y`.

The only bookkeeping is the degree cast `n = 0 + n` implicit in the degree-`0` instance of the Thom
isomorphism; it is handled by `RelCohCast` and its compatibility with negation.
-/

/-- Casting a relative class along an equality of degrees, with the *base* of the pair held fixed
(which pins the motive of the `Eq.rec` and makes the casts syntactically comparable, unlike a bare
`▸`). -/
abbrev RelCohCast {B : Type} [TopologicalSpace B] (A : Set B) {a b : ℕ} (h : a = b)
    (x : RelCoh ℤ a B A) : RelCoh ℤ b B A := h ▸ x

/-- Casting along an equality of degrees commutes with negation. -/
lemma RelCohCast_neg {B : Type} [TopologicalSpace B] (A : Set B) {a b : ℕ} (h : a = b)
    (x : RelCoh ℤ a B A) : RelCohCast A h (-x) = -(RelCohCast A h x) := by
  cases h
  rfl

/-- **The orientation character of the punctured model class, for every class**: a gauge whose
determinant is negative everywhere acts on the whole of `H^n(Y × ℝⁿ, Y × (ℝⁿ ∖ 0); ℤ)` by `-1`.

The membership proof `hM` is a free argument (all proofs of it are definitionally equal). -/
theorem relCohMap_gaugeEnd_neg_apply {n : ℕ} (hn : 1 ≤ n) {Y : Type} [TopologicalSpace Y]
    (D : Y → Gauge n) (hD : Continuous D)
    (hdet : ∀ y, LinearMap.det (D y).toLinearMap < 0)
    (hM : ∀ p ∈ Punct Y n, gaugeEnd D hD p ∈ Punct Y n)
    (ξ : RelCoh ℤ n (Y × EuclideanSpace ℝ (Fin n)) (Punct Y n)) :
    (relCohMap (gaugeEnd D hD) (Punct Y n) (Punct Y n) hM ℤ n).hom ξ = -ξ := by
  -- the Thom isomorphism: write `ξ` as `π^*(a) ⌣ Mpun n Y`, up to the degree cast `n = 0 + n`
  obtain ⟨a, ha⟩ := (Mpun_isModel n Y 0).2 (RelCohCast (Punct Y n) (Nat.zero_add n).symm ξ)
  -- the gauge is the identity on the base, so it fixes `π^*(a)`
  have hcomp : (projFstA Y n).comp (gaugeEnd D hD) = projFstA Y n := by
    ext p
    rfl
  have hx : (CohMap (gaugeEnd D hD) ℤ 0).hom ((CohMap (projFstA Y n) ℤ 0).hom a)
      = (CohMap (projFstA Y n) ℤ 0).hom a := by
    rw [CohMap_comp_apply (gaugeEnd D hD) (projFstA Y n) ℤ 0 a, CohMap_congr hcomp ℤ 0]
  -- and it acts on the model class by `-1` (`Work.Thom.Orientation.Mpun_gaugeEnd_neg`)
  have hMpun : (relCohMap (gaugeEnd D hD) (Punct Y n) (Punct Y n) hM ℤ n).hom (Mpun n Y)
      = - Mpun n Y :=
    Work.Thom.Orientation.Mpun_gaugeEnd_neg n hn D hD hdet
  -- naturality of the mixed cup product under the gauge
  have hnat := mixedCupC_pairNatural (gaugeEnd D hD) (Punct Y n) (Punct Y n) hM 0 n
    ((CohMap (projFstA Y n) ℤ 0).hom a) (Mpun n Y)
  have hL : (relCohMap (gaugeEnd D hD) (Punct Y n) (Punct Y n) hM ℤ (0 + n)).hom
      ((mixedCupC ℤ (Punct Y n) 0 n) ((CohMap (projFstA Y n) ℤ 0).hom a) (Mpun n Y))
      = - (mixedCupC ℤ (Punct Y n) 0 n) ((CohMap (projFstA Y n) ℤ 0).hom a) (Mpun n Y) := by
    rw [hnat, hx, hMpun]
    simp
  -- the two degree casts
  have hcast : (relCohMap (gaugeEnd D hD) (Punct Y n) (Punct Y n) hM ℤ (0 + n)).hom
        (RelCohCast (Punct Y n) (Nat.zero_add n).symm ξ)
      = RelCohCast (Punct Y n) (Nat.zero_add n).symm
        ((relCohMap (gaugeEnd D hD) (Punct Y n) (Punct Y n) hM ℤ n).hom ξ) :=
    relCohMap_cast (gaugeEnd D hD) (Punct Y n) (Punct Y n) hM (h := (Nat.zero_add n).symm) ξ
  have hcastneg : RelCohCast (Punct Y n) (Nat.zero_add n).symm (-ξ)
      = -(RelCohCast (Punct Y n) (Nat.zero_add n).symm ξ) :=
    RelCohCast_neg (Punct Y n) (Nat.zero_add n).symm ξ
  -- the computation, in degree `0 + n`
  have hmain : RelCohCast (Punct Y n) (Nat.zero_add n).symm
        ((relCohMap (gaugeEnd D hD) (Punct Y n) (Punct Y n) hM ℤ n).hom ξ)
      = - (RelCohCast (Punct Y n) (Nat.zero_add n).symm ξ) := by
    rw [← hcast, ← ha]
    exact hL
  have hmain' : RelCohCast (Punct Y n) (Nat.zero_add n).symm
        ((relCohMap (gaugeEnd D hD) (Punct Y n) (Punct Y n) hM ℤ n).hom ξ)
      = RelCohCast (Punct Y n) (Nat.zero_add n).symm (-ξ) := by
    rw [hmain, hcastneg]
  -- undo the degree cast
  exact eq_of_cast_eq
    (α := fun k => RelCoh ℤ k (Y × EuclideanSpace ℝ (Fin n)) (Punct Y n))
    (h := (Nat.zero_add n).symm) hmain'

theorem gaugeOrientationNeg {n : ℕ} (hn : 1 ≤ n) {Y : Type} [TopologicalSpace Y]
    (D : Y → Work.Thom.Gauge n) (hD : Continuous D)
    (hdet : ∀ y, LinearMap.det (D y).toLinearMap < 0) :
    ∀ ξ : Work.Thom.RelCoh ℤ n (Y × EuclideanSpace ℝ (Fin n)) (Work.Thom.Punct Y n),
      (Work.Thom.relCohMap (Work.Thom.gaugeEnd D hD) (Work.Thom.Punct Y n) (Work.Thom.Punct Y n)
        (Work.Thom.gaugeEnd_mem D hD (fun y => Work.Thom.gaugeEnd_bijective_of_det_ne_zero (D y)
          (ne_of_lt (hdet y)))) ℤ n).hom ξ = -ξ := by
  intro ξ
  exact relCohMap_gaugeEnd_neg_apply hn D hD hdet
    (Work.Thom.gaugeEnd_mem D hD (fun y => Work.Thom.gaugeEnd_bijective_of_det_ne_zero (D y)
      (ne_of_lt (hdet y)))) ξ

end Work.ThomBordism.FrameSigns
