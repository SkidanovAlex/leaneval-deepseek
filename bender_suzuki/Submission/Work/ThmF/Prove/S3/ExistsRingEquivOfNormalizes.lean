import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.Prove.S3

/-- Conjugation by a unit: `(u * a * u') * (u * b * u') = u * (a * b) * u'` whenever `u' * u = 1`. -/
private lemma conj_mul_eq {R : Type*} [Semiring R] {u u' : R} (hu' : u' * u = 1) (a b : R) :
    (u * a * u') * (u * b * u') = u * (a * b) * u' := by
  calc (u * a * u') * (u * b * u')
      = u * a * (u' * u) * b * u' := by noncomm_ring
    _ = u * a * 1 * b * u' := by rw [hu']
    _ = u * (a * b) * u' := by noncomm_ring

/-- Conjugation by a unit is injective on the left: if `u * a * u' = u * b * u'` and `u' * u = 1`
then `a = b`. -/
private lemma conj_inj {R : Type*} [Semiring R] {u u' : R} (hu' : u' * u = 1)
    {a b : R} (h : u * a * u' = u * b * u') : a = b := by
  have h2 : u' * (u * a * u') * u = u' * (u * b * u') * u := by rw [h]
  have ha : u' * (u * a * u') * u = a := by
    rw [show u' * (u * a * u') * u = (u' * u) * (a * (u' * u)) by noncomm_ring]
    rw [hu', one_mul, mul_one]
  have hb : u' * (u * b * u') * u = b := by
    rw [show u' * (u * b * u') * u = (u' * u) * (b * (u' * u)) by noncomm_ring]
    rw [hu', one_mul, mul_one]
  rw [ha, hb] at h2
  exact h2

theorem exists_ringEquiv_of_normalizes {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {E : Type*} [Field E] [Algebra F E] (φ : E →ₐ[F] Module.End F V) (hφ : Function.Injective φ)
    (u u' : Module.End F V) (hu : u * u' = 1) (hu' : u' * u = 1)
    (hnorm : ∀ x : E, ∃ y : E, φ y = u * φ x * u') [Finite E] :
    ∃ σ : E ≃+* E, ∀ x : E, φ (σ x) = u * φ x * u' := by
  classical
  -- The conjugation `x ↦ u * φ x * u'` lands in `φ '' E` by hypothesis; pick a preimage.
  let σf : E → E := fun x => Classical.choose (hnorm x)
  have hσ : ∀ x, φ (σf x) = u * φ x * u' := fun x => Classical.choose_spec (hnorm x)
  -- `σf` is multiplicative and additive, by injectivity of `φ` and the unit relations.
  have hmul : ∀ x y, σf (x * y) = σf x * σf y := by
    intro x y
    apply hφ
    rw [hσ (x * y), map_mul, map_mul, hσ x, hσ y]
    rw [conj_mul_eq hu' (φ x) (φ y)]
  have hadd : ∀ x y, σf (x + y) = σf x + σf y := by
    intro x y
    apply hφ
    rw [hσ (x + y), map_add, map_add, hσ x, hσ y]
    rw [mul_add, add_mul]
  -- `σf` is injective (conjugation by the unit `u` is injective), hence bijective on the finite `E`.
  have hinj : Function.Injective σf := by
    intro x y hxy
    apply hφ
    apply conj_inj hu'
    rw [← hσ x, ← hσ y, hxy]
  have hsurj : Function.Surjective σf := Finite.injective_iff_surjective.mp hinj
  refine ⟨RingEquiv.mk (Equiv.ofBijective σf ⟨hinj, hsurj⟩) ?_ ?_, ?_⟩
  · intro x y
    exact hmul x y
  · intro x y
    exact hadd x y
  · intro x
    exact hσ x

end Work.ThmF.Prove.S3
