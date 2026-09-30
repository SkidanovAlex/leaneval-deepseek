import Mathlib
import Submission.Work.Pi6.EFACTS.qzAux
import Submission.Work.Pi6.UCT.finiteDualQZ
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# `qzFive`: a group whose `ℚ/ℤ`-dual is `ZMod k` is itself `ZMod k`

`Work.Pi6.EFACTS.qzFive` is the last algebraic step of the `π₆(S³) ≅ ℤ/12` computation:
an abelian group `A` whose character module `A⋆ = Hom_ℤ(A, ℚ/ℤ)` (`ℚ/ℤ = AddCircle (1 : ℚ)`) is the
cyclic group `ZMod k` (`k > 0`) is itself isomorphic to `ZMod k`.

The proof does *not* need the torsion hypothesis (`htor`): as soon as `A⋆` is cyclic, everything is
forced.  Write `φ : A⋆ ≃ₗ[ℤ] ZMod k` for the given isomorphism.

* **The evaluation `A ↪ A⋆⋆` is injective.**  An element `a ≠ 0` of an abelian group is detected by
  a character into `ℚ/ℤ` (`QZ.exists_linearMap_apply_ne_zero`, i.e. `ℚ/ℤ` is a cogenerator),
  which is exactly injectivity of `LinearMap.applyₗ : A →ₗ[ℤ] (A →ₗ[ℤ] ℚ/ℤ) →ₗ[ℤ] ℚ/ℤ`.
* **Transporting along `φ`**: `A⋆⋆ = Hom(A⋆, ℚ/ℤ) ≅ Hom(ZMod k, ℚ/ℤ) ≅ ZMod k`, the first
  isomorphism being `LinearEquiv.congrLeft _ ℤ φ.symm` (precomposition with `φ.symm`) and the
  second `QZ.zmodDual`.  Composing with the evaluation embeds `A` into the finite group `ZMod k`,
  so `A` is finite.
* **Finite case.**  For a finite abelian group `A ≅ Hom_ℤ(A, ℚ/ℤ)`
  (`Work.Pi6.UCT.finiteDualQZ`), so `A ≅ A⋆ ≅ ZMod k`.

The torsion hypothesis is thus used nowhere (it is kept because the statement is frozen).
-/

namespace Work.Pi6.EFACTS

open Work.Pi6.EFACTS

theorem qzFive {A : Type} [AddCommGroup A] (htor : ∀ a : A, ∃ N : ℕ, 0 < N ∧ N • a = 0)
    (k : ℕ) (hk : 0 < k) (h : Nonempty ((A →ₗ[ℤ] AddCircle (1 : ℚ)) ≃ₗ[ℤ] ZMod k)) :
    Nonempty (A ≃ₗ[ℤ] ZMod k) := by
  have : NeZero k := ⟨hk.ne'⟩
  obtain ⟨φ⟩ := h
  obtain ⟨ZD⟩ := QZ.zmodDual k hk
  -- Injectivity of the double-dual evaluation `a ↦ (f ↦ f a)`.
  have hev : Function.Injective
      (LinearMap.applyₗ (R := ℤ) (M := A) (M₂ := AddCircle (1 : ℚ))
        : A →ₗ[ℤ] ((A →ₗ[ℤ] AddCircle (1 : ℚ)) →ₗ[ℤ] AddCircle (1 : ℚ))) := by
    intro a b hab
    -- All characters agree on `a - b`, hence `a - b = 0` by separation of points.
    have hdiff : ∀ f : A →ₗ[ℤ] AddCircle (1 : ℚ), f (a - b) = 0 := by
      intro f
      have h := congrArg
        (fun g : (A →ₗ[ℤ] AddCircle (1 : ℚ)) →ₗ[ℤ] AddCircle (1 : ℚ) => g f) hab
      have h' : f a = f b := by simpa using h
      rw [map_sub, h', sub_self]
    have h0 : a - b = 0 := by
      by_contra hne
      obtain ⟨f, hf⟩ := QZ.exists_linearMap_apply_ne_zero hne
      exact hf (hdiff f)
    exact sub_eq_zero.mp h0
  -- Transport the double dual of `A` to the double dual of `ZMod k` along `φ`, then use that the
  -- dual of `ZMod k` is `ZMod k`.
  let W : ((A →ₗ[ℤ] AddCircle (1 : ℚ)) →ₗ[ℤ] AddCircle (1 : ℚ)) ≃ₗ[ℤ]
      (ZMod k →ₗ[ℤ] AddCircle (1 : ℚ)) :=
    (LinearEquiv.congrLeft (AddCircle (1 : ℚ)) ℤ φ.symm).symm
  let e : A →ₗ[ℤ] ZMod k := ZD.toLinearMap.comp (W.toLinearMap.comp
    (LinearMap.applyₗ (R := ℤ) (M := A) (M₂ := AddCircle (1 : ℚ))))
  have he : Function.Injective e := ZD.injective.comp (W.injective.comp hev)
  -- `A` embeds into the finite group `ZMod k`.
  have : Finite A := Finite.of_injective e he
  -- A finite abelian group is its own `ℚ/ℤ`-dual.
  obtain ⟨θ⟩ := Work.Pi6.UCT.finiteDualQZ A
  exact ⟨θ.trans φ⟩

end Work.Pi6.EFACTS
