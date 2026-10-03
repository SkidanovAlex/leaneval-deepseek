import Mathlib

namespace Work.OROneRel

universe u

/-- The HNN extension depends only on its data: if the associated subgroups are equal and the
conjugation isomorphisms agree on the common elements, the two extensions are isomorphic by a map
fixing the base and the stable letter. -/
theorem exists_hnnExtension_iso_of_data {G : Type u} [Group G] {H : Subgroup G}
    {A A' B B' : Subgroup ↥H} (hA : A = A') (hB : B = B')
    (φ : A ≃* B) (φ' : A' ≃* B')
    (hφ : ∀ (x : ↥H) (hx : x ∈ A) (hx' : x ∈ A'),
      ((φ ⟨x, hx⟩ : B) : ↥H) = ((φ' ⟨x, hx'⟩ : B') : ↥H)) :
    ∃ E : HNNExtension ↥H A B φ ≃* HNNExtension ↥H A' B' φ',
      (∀ h : ↥H, E (HNNExtension.of h) = HNNExtension.of h) ∧
      E HNNExtension.t = HNNExtension.t := by
  -- The two relations `t * of a = of (φ a) * t` and `t * of a' = of (φ' a') * t` agree because
  -- `φ` and `φ'` agree after composing with the inclusions into `↥H`.
  have hc : ∀ a : A, (HNNExtension.t : HNNExtension ↥H A' B' φ') * HNNExtension.of (a : ↥H)
      = HNNExtension.of (((φ a : B)) : ↥H) * (HNNExtension.t : HNNExtension ↥H A' B' φ') := by
    intro a
    let a' : A' := ⟨(a : ↥H), by rw [← hA]; exact a.2⟩
    have hval : (a' : ↥H) = (a : ↥H) := rfl
    have hphi : (((φ' a' : B')) : ↥H) = (((φ a : B)) : ↥H) := by
      have h := hφ (a : ↥H) a.2 a'.2
      exact h.symm
    have hrel := HNNExtension.t_mul_of (φ := φ') a'
    rw [hval, hphi] at hrel
    exact hrel
  have hc' : ∀ a' : A', (HNNExtension.t : HNNExtension ↥H A B φ) * HNNExtension.of (a' : ↥H)
      = HNNExtension.of (((φ' a' : B')) : ↥H) * (HNNExtension.t : HNNExtension ↥H A B φ) := by
    intro a'
    let a : A := ⟨(a' : ↥H), by rw [hA]; exact a'.2⟩
    have hval : (a : ↥H) = (a' : ↥H) := rfl
    have hphi : (((φ a : B)) : ↥H) = (((φ' a' : B')) : ↥H) := by
      have h := hφ (a' : ↥H) a.2 a'.2
      exact h
    have hrel := HNNExtension.t_mul_of (φ := φ) a
    rw [hval, hphi] at hrel
    exact hrel
  -- The two mutually inverse comparison maps, both fixing the base and the stable letter.
  let F : (HNNExtension ↥H A B φ) →* (HNNExtension ↥H A' B' φ') :=
    HNNExtension.lift (HNNExtension.of (φ := φ') : ↥H →* HNNExtension ↥H A' B' φ')
      (HNNExtension.t (φ := φ') : HNNExtension ↥H A' B' φ') hc
  let F' : (HNNExtension ↥H A' B' φ') →* (HNNExtension ↥H A B φ) :=
    HNNExtension.lift (HNNExtension.of (φ := φ) : ↥H →* HNNExtension ↥H A B φ)
      (HNNExtension.t (φ := φ) : HNNExtension ↥H A B φ) hc'
  have hleft : F'.comp F = MonoidHom.id _ := by
    apply HNNExtension.hom_ext
    · ext g
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, F, F', HNNExtension.lift_of]
    · simp only [MonoidHom.comp_apply, MonoidHom.id_apply, F, F', HNNExtension.lift_t]
  have hright : F.comp F' = MonoidHom.id _ := by
    apply HNNExtension.hom_ext
    · ext g
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, F, F', HNNExtension.lift_of]
    · simp only [MonoidHom.comp_apply, MonoidHom.id_apply, F, F', HNNExtension.lift_t]
  refine ⟨MonoidHom.toMulEquiv F F' hleft hright, ?_, ?_⟩
  · intro h
    change F (HNNExtension.of (φ := φ) h) = HNNExtension.of (φ := φ') h
    simp only [F, HNNExtension.lift_of]
  · change F (HNNExtension.t (φ := φ)) = HNNExtension.t (φ := φ')
    simp only [F, HNNExtension.lift_t]

end Work.OROneRel
