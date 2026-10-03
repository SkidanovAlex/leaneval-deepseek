import Mathlib

namespace Work.ORLocInd

universe u v

/-- **Invariance of the HNN extension under an isomorphism of the data.**
If `e : G ≃* G'` carries `A` onto `A'` and `B` onto `B'` (witnessed by `eA`, `eB`, compatible with
`e`) and conjugates the identifying isomorphism `φ : A ≃* B` to `φ' : A' ≃* B'` (hypothesis `hφ`),
then the HNN extensions `HNNExtension G A B φ` and `HNNExtension G' A' B' φ'` are isomorphic.

The isomorphism is built from the universal property of the HNN extension
(`HNNExtension.lift`); the two maps obtained by lifting `e` and `e.symm` are mutually inverse by
`HNNExtension.hom_ext`. -/
theorem hnnExtension_congr {G : Type u} [Group G] {G' : Type v} [Group G']
    (e : G ≃* G') (A B : Subgroup G) (A' B' : Subgroup G') (φ : A ≃* B) (φ' : A' ≃* B')
    (eA : A ≃* A') (eB : B ≃* B')
    (heA : ∀ a : A, ((eA a : A') : G') = e (a : G))
    (heB : ∀ b : B, ((eB b : B') : G') = e (b : G))
    (hφ : ∀ a : A, φ' (eA a) = eB (φ a)) :
    Nonempty (HNNExtension G A B φ ≃* HNNExtension G' A' B' φ') := by
  -- The forward map: lift `e` to the HNN extension, sending `t` to `t`.
  have hx₁ : ∀ a : A,
      (HNNExtension.t : HNNExtension G' A' B' φ') * (HNNExtension.of.comp e.toMonoidHom) (a : G)
      = (HNNExtension.of.comp e.toMonoidHom) (φ a : G) * HNNExtension.t := by
    intro a
    show (HNNExtension.t : HNNExtension G' A' B' φ') * HNNExtension.of (e (a : G))
        = HNNExtension.of (e ((φ a : B) : G)) * HNNExtension.t
    have hA : ((eA a : A') : G') = e (a : G) := heA a
    have hB : ((eB (φ a) : B') : G') = e ((φ a : B) : G) := heB (φ a)
    have key := HNNExtension.t_mul_of (φ := φ') (eA a)
    rw [hA] at key
    rw [hφ a, hB] at key
    exact key
  -- The backward map: lift `e.symm` to the HNN extension, sending `t` to `t`.
  have hx₂ : ∀ a' : A',
      (HNNExtension.t : HNNExtension G A B φ) * (HNNExtension.of.comp e.symm.toMonoidHom) (a' : G')
      = (HNNExtension.of.comp e.symm.toMonoidHom) (φ' a' : G') * HNNExtension.t := by
    intro a'
    show (HNNExtension.t : HNNExtension G A B φ) * HNNExtension.of (e.symm (a' : G'))
        = HNNExtension.of (e.symm (φ' a' : G')) * HNNExtension.t
    set a : A := eA.symm a' with ha
    have hAa : eA a = a' := by rw [ha]; exact eA.apply_symm_apply a'
    have h2 : (a' : G') = e (a : G) := by rw [← hAa]; exact heA a
    have ha' : (a : G) = e.symm (a' : G') := by rw [h2]; simp
    have hp1 : φ' a' = eB (φ a) := by rw [← hAa, hφ a]
    have hp2 : (φ' a' : G') = e ((φ a : B) : G) := by rw [hp1, heB (φ a)]
    have hphi : ((φ a : B) : G) = e.symm (φ' a' : G') := by rw [hp2]; simp
    rw [← ha', ← hphi]
    exact HNNExtension.t_mul_of (φ := φ) a
  let F : HNNExtension G A B φ →* HNNExtension G' A' B' φ' :=
    HNNExtension.lift (HNNExtension.of.comp e.toMonoidHom) HNNExtension.t hx₁
  let F' : HNNExtension G' A' B' φ' →* HNNExtension G A B φ :=
    HNNExtension.lift (HNNExtension.of.comp e.symm.toMonoidHom) HNNExtension.t hx₂
  have hF_of : ∀ g : G, F (HNNExtension.of g) = HNNExtension.of (e g) := by
    intro g
    dsimp only [F]
    exact HNNExtension.lift_of (HNNExtension.of.comp e.toMonoidHom) HNNExtension.t hx₁ g
  have hF'_of : ∀ g : G', F' (HNNExtension.of g) = HNNExtension.of (e.symm g) := by
    intro g
    dsimp only [F']
    exact HNNExtension.lift_of (HNNExtension.of.comp e.symm.toMonoidHom) HNNExtension.t hx₂ g
  have hF_t : F HNNExtension.t = HNNExtension.t := by
    dsimp only [F]
    exact HNNExtension.lift_t (HNNExtension.of.comp e.toMonoidHom) HNNExtension.t hx₁
  have hF'_t : F' HNNExtension.t = HNNExtension.t := by
    dsimp only [F']
    exact HNNExtension.lift_t (HNNExtension.of.comp e.symm.toMonoidHom) HNNExtension.t hx₂
  have hleft : F'.comp F = MonoidHom.id _ := by
    apply HNNExtension.hom_ext
    · ext g
      change F' (F (HNNExtension.of g)) = HNNExtension.of g
      rw [hF_of, hF'_of]
      simp
    · change F' (F HNNExtension.t) = HNNExtension.t
      rw [hF_t, hF'_t]
  have hright : F.comp F' = MonoidHom.id _ := by
    apply HNNExtension.hom_ext
    · ext g
      change F (F' (HNNExtension.of g)) = HNNExtension.of g
      rw [hF'_of, hF_of]
      simp
    · change F (F' HNNExtension.t) = HNNExtension.t
      rw [hF'_t, hF_t]
  refine ⟨MulEquiv.mk
    { toFun := F
      invFun := F'
      left_inv := fun x => by change (F'.comp F) x = x; rw [hleft]; rfl
      right_inv := fun x => by change (F.comp F') x = x; rw [hright]; rfl }
    (fun x y => map_mul F x y)⟩

end Work.ORLocInd
