import Mathlib
import Submission.Work.ATOM.Defs
import Submission.Work.ATOM.ZS.Unred.LocallyConstantIndicator
import Submission.Work.ATOM.ZS.Unred.LCZ_iso

/-!
# Point classes of a finite light profinite set are linearly independent (morphism form)

The point classes `ℤ[∗] → ℤ[R]`, `j ↦ zmap (ptAt (r j))`, of distinct points of a finite light
profinite set are linearly independent: this file proves that every relation
`∑ j, c j • zmap (ptAt (r j)) = 0` in `Hom(ℤ[∗], ℤ[R])` has all coefficients equal to `0`.

## The argument

For a fixed index `i`, the point `r i` has a *locally constant indicator function*
`ptIndicator R (r i) : LocallyConstant ↥R ℤ` (locally constant because `R` is finite, hence
discrete), and `Work.ATOM.ZS.Unred.LocallyConstantIndicator` produces a "coefficient extraction"
morphism `φ : ℤ[R] ⟶ ℤ[∗]` with `zmap (ptAt t) ≫ φ = ptIndicator R (r i) t • 𝟙` for all `t`.

Composing the relation with `φ` (`Preadditive.sum_comp`, `Preadditive.zsmul_comp`) and keeping
only the `i`-th term of the resulting sum (`Finset.sum_eq_single`, with
`ptIndicator_of_ne`/`ptIndicator_self`) yields

`c i • 𝟙 (ℤ[∗]) = 0`   in `End(ℤ[∗])`.

It remains to deduce `c i = 0`.  Since `ℤ[∗] ≅ LCZ` (the locally constant `ℤ`-valued sheaf)
carries the canonical generator `e₁ = homFreeEquiv ∗ 𝟙` to the constant function `1`
(`Work.ATOM.ZS.Unred.LCZhom`, `LCZhom_e1`), it suffices to know that
`LCZ(∗) = LocallyConstant ↥∗ ℤ ≅ ℤ`, i.e. that the "evaluate at the unique point" functional
`LocallyConstant.evalₗ ℤ ∗ : LocallyConstant ↥∗ ℤ →ₗ[ℤ] ℤ` is injective on the constant function
`1`: this is `h10`–`h12` below (`evalₗ_apply`, `map_smul`, `map_zero`).

The transport `End(ℤ[∗]) → ℤ[∗](∗)` uses `homFreeEquiv_comp` together with
`Work.ATOM.ZS.Unred.smul_id_section` (the endomorphism `n • 𝟙` acts as multiplication by `n` on
sections); the corresponding statement for `n = 0` is `homFreeEquiv_zero_self`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed
open Opposite

noncomputable section

namespace Work.ANALYTIC

/-- The locally constant indicator function of a point of a finite light profinite set. -/
private noncomputable def ptIndicator (R : LightProfinite.{0}) [Finite ↥R] (s : ↥R) :
    LocallyConstant ↥R.toTop ℤ :=
  (LocallyConstant.const ↥R.toTop (1 : ℤ)).indicator
    (isClopen_discrete ({x : ↥R | x = s} : Set ↥R))

/-- The indicator of a point takes the value `1` at that point. -/
private theorem ptIndicator_self (R : LightProfinite.{0}) [Finite ↥R] (s : ↥R) :
    ptIndicator R s s = 1 := by
  classical
  rw [ptIndicator, LocallyConstant.indicator_apply_eq_if]
  simp

/-- The indicator of a point takes the value `0` away from that point. -/
private theorem ptIndicator_of_ne {R : LightProfinite.{0}} [Finite ↥R] {s t : ↥R} (h : t ≠ s) :
    ptIndicator R s t = 0 := by
  classical
  rw [ptIndicator, LocallyConstant.indicator_apply_eq_if]
  simp [h]

/-- `homFreeEquiv` computed on a multiple of the identity of `ℤ[∗]`: it is the multiple of the
canonical generator `e₁ = homFreeEquiv ∗ 𝟙`. -/
private theorem homFreeEquiv_smul_id_self (n : ℤ) :
    Work.ATOM.homFreeEquiv Work.ATOM.pt (Work.ATOM.zfree Work.ATOM.pt)
        (n • 𝟙 (Work.ATOM.zfree Work.ATOM.pt)) = n • Work.ATOM.ZS.Unred.e1 := by
  rw [← Category.id_comp (n • 𝟙 (Work.ATOM.zfree Work.ATOM.pt)),
    Work.ATOM.ZS.Unred.homFreeEquiv_comp (𝟙 (Work.ATOM.zfree Work.ATOM.pt))
      (n • 𝟙 (Work.ATOM.zfree Work.ATOM.pt))]
  exact Work.ATOM.ZS.Unred.smul_id_section (Work.ATOM.zfree Work.ATOM.pt) Work.ATOM.pt n
    Work.ATOM.ZS.Unred.e1

/-- `homFreeEquiv` sends the zero morphism `ℤ[∗] ⟶ ℤ[∗]` to the zero section. -/
private theorem homFreeEquiv_zero_self :
    Work.ATOM.homFreeEquiv Work.ATOM.pt (Work.ATOM.zfree Work.ATOM.pt)
        (0 : Work.ATOM.zfree Work.ATOM.pt ⟶ Work.ATOM.zfree Work.ATOM.pt) = 0 := by
  have h := Work.ATOM.ZS.Unred.homFreeEquiv_comp
    (0 : Work.ATOM.zfree Work.ATOM.pt ⟶ Work.ATOM.zfree Work.ATOM.pt)
    (0 : Work.ATOM.zfree Work.ATOM.pt ⟶ Work.ATOM.zfree Work.ATOM.pt)
  rw [CategoryTheory.Limits.zero_comp] at h
  rw [h, show (0 : Work.ATOM.zfree Work.ATOM.pt ⟶ Work.ATOM.zfree Work.ATOM.pt).hom = 0 from rfl,
    CategoryTheory.NatTrans.app_zero]
  simp

theorem zfree_finite_point_independent_mor (R : LightProfinite.{0}) [Finite ↥R] (m : ℕ)
    (r : Fin m → ↥R) (hr : Function.Injective r) (c : Fin m → ℤ)
    (h : ∑ j, c j • (Work.ATOM.zmap (Work.ATOM.ptAt (r j))) = 0) : ∀ j, c j = 0 := by
  intro i
  obtain ⟨φ, hφ⟩ :=
    Work.ATOM.ZS.Unred.LocallyConstantIndicator R (ptIndicator R (r i))
  -- Compose the relation with `φ`.
  have h2 : (∑ j, c j • (Work.ATOM.zmap (Work.ATOM.ptAt (r j)))) ≫ φ = 0 := by
    rw [h, CategoryTheory.Limits.zero_comp]
  -- The composition distributes over the sum, and each summand is evaluated by `hφ`.
  have h3 : ∑ j, c j • (ptIndicator R (r i) (r j) • 𝟙 (Work.ATOM.zfree Work.ATOM.pt)) = 0 := by
    rw [← h2, CategoryTheory.Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [CategoryTheory.Preadditive.zsmul_comp, hφ (r j)]
  -- Only the `i`-th term survives.
  have h5 : c i • 𝟙 (Work.ATOM.zfree Work.ATOM.pt) = 0 := by
    have hsum : ∑ j, c j • (ptIndicator R (r i) (r j) • 𝟙 (Work.ATOM.zfree Work.ATOM.pt))
        = c i • 𝟙 (Work.ATOM.zfree Work.ATOM.pt) := by
      rw [Finset.sum_eq_single i]
      · rw [ptIndicator_self, one_smul]
      · intro j _ hj
        rw [ptIndicator_of_ne (fun hh => hj (hr hh))]
        simp
      · intro hi; exact absurd (Finset.mem_univ i) hi
    rw [← hsum]; exact h3
  -- Transport to the canonical generator `e₁` of `ℤ[∗](∗)`.
  have h6 : c i • Work.ATOM.ZS.Unred.e1 = 0 := by
    have h8 := congrArg (Work.ATOM.homFreeEquiv Work.ATOM.pt (Work.ATOM.zfree Work.ATOM.pt)) h5
    rw [homFreeEquiv_zero_self, homFreeEquiv_smul_id_self] at h8
    exact h8
  -- Transport along the identification `ℤ[∗] ≅ LCZ` to the constant function `1`.
  have h9 : c i • Work.ATOM.ZS.Unred.oneLCZ = 0 := by
    have hz := congrArg (Work.ATOM.ZS.Unred.LCZhom.hom.app (op Work.ATOM.pt)) h6
    rw [map_zsmul, Work.ATOM.ZS.Unred.LCZhom_e1, map_zero] at hz
    exact hz
  -- `LCZ(∗) = LocallyConstant ↥∗ ℤ ≅ ℤ`, by evaluation at the unique point.
  have h10 : (LocallyConstant.evalₗ ℤ (PUnit.unit : ↥Work.ATOM.pt.toTop))
      Work.ATOM.ZS.Unred.oneLCZ = 1 := by
    rw [LocallyConstant.evalₗ_apply]
    simp
  have h11 : (LocallyConstant.evalₗ ℤ (PUnit.unit : ↥Work.ATOM.pt.toTop))
      (c i • Work.ATOM.ZS.Unred.oneLCZ)
      = c i • (LocallyConstant.evalₗ ℤ (PUnit.unit : ↥Work.ATOM.pt.toTop))
          Work.ATOM.ZS.Unred.oneLCZ := map_smul _ _ _
  have h12 : (LocallyConstant.evalₗ ℤ (PUnit.unit : ↥Work.ATOM.pt.toTop))
      (c i • Work.ATOM.ZS.Unred.oneLCZ) = 0 := by
    rw [h9]
    exact LinearMap.map_zero _
  rw [h11, h10] at h12
  simpa using h12

end Work.ANALYTIC
