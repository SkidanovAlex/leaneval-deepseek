import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.pairGCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.setIntegral_insertCoord_slice`

The one-slot slice identity for the box `Λ(ℓ) = boxL ℓ` (the centred cube of side `ℓ`,
`Work.BoseK15.corpusBox.boxL ℓ`, which equals `Submission.BoseGases.acube ℓ` for `ℓ > 0`):

    ∫_{w ∈ Λ(ℓ)} ∫_{x' ∈ Λ(ℓ)^{{k // k ≠ i}}} f (insertCoord i w x')
      = ∫_{x ∈ Λ(ℓ)^n} f x .

**Route.**  `volume` on a finite product of Euclidean spaces *is* the product measure
(`MeasureTheory.volume_pi`), so restricting it to the box turns it into `Measure.pi` of the
restricted cube measures (`MeasureTheory.Measure.restrict_pi_pi`) and both sides of the identity
are integrals against a product of copies of the same finite measure
`μ = (volume : Measure E3).restrict (boxL ℓ)`.

The coordinate-insertion map is the measurable equivalence

    `insertSliceEquiv i : E3 × ({k : Fin n // k ≠ i} → E3) ≃ᵐ (Fin n → E3)`,
    `(w, x') ↦ insertCoord i w x'`  (inverse `x ↦ (x i, x ∘ Subtype.val)`)

and it carries `μ.prod (Measure.pi fun _ => μ)` to `Measure.pi (fun _ : Fin n => μ)`: the two
measures are `Measure.pi`s, so it suffices to test them on the π-system of measurable boxes,
where the statement reduces to `Measure.prod_prod` + `Measure.pi_pi` together with the product
decomposition `prod_univ_eq_mul_prod_subtype_ne`
(`Fintype.prod_subtype_mul_prod_subtype` plus the singleton product over `{k // ¬(k ≠ i)}`).

The iterated integral over `μ.prod (Measure.pi _)` is then `MeasureTheory.integral_prod` (Fubini),
the transport along the equivalence is `MeasurePreserving.integral_comp'`, and integrability of
`f` — continuous on the whole space, integrated against the finite measure carried by the compact
box — is `ContinuousOn.integrableOn_compact`.

`sorry`-free.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn
local notation "boxL" => Work.BoseK15.corpusBox.boxL

/-! ## 1. The coordinate-insertion equivalence -/

/-- The measurable equivalence `(w, x') ↦ insertCoord i w x'` between the sliced box
`Λ(ℓ) × Λ(ℓ)^{{k // k ≠ i}}` and the full box `Λ(ℓ)^n`. -/
def insertSliceEquiv {n : ℕ} (i : Fin n) : (E3 × ({k : Fin n // k ≠ i} → E3)) ≃ᵐ (Fin n → E3) where
  toEquiv :=
    { toFun := fun z => insertCoord i z.1 z.2
      invFun := fun x => (x i, fun k => x k.1)
      left_inv := by
        rintro ⟨w, x'⟩
        refine Prod.ext ?_ ?_
        · simp [insertCoord]
        · funext k
          simp [insertCoord, dif_neg k.2]
      right_inv := by
        intro x
        funext k
        by_cases hk : k = i
        · subst hk; simp [insertCoord]
        · simp [insertCoord, hk] }
  measurable_toFun := by
    show Measurable (fun z : E3 × ({k : Fin n // k ≠ i} → E3) => insertCoord i z.1 z.2)
    rw [measurable_pi_iff]
    intro k
    by_cases hk : k = i
    · have h1 : (fun z : E3 × ({k : Fin n // k ≠ i} → E3) => insertCoord i z.1 z.2 k)
          = fun z => z.1 := by
        funext z; simp [insertCoord, hk]
      rw [h1]; exact measurable_fst
    · have h1 : (fun z : E3 × ({k : Fin n // k ≠ i} → E3) => insertCoord i z.1 z.2 k)
          = fun z => z.2 (⟨k, hk⟩ : {k : Fin n // k ≠ i}) := by
        funext z; simp [insertCoord, hk]
      rw [h1]
      exact (measurable_pi_apply (⟨k, hk⟩ : {k : Fin n // k ≠ i})).comp measurable_snd
  measurable_invFun := by
    show Measurable (fun x : Fin n → E3 => (x i, fun k : {k : Fin n // k ≠ i} => x k.1))
    refine (measurable_pi_apply i).prodMk ?_
    rw [measurable_pi_iff]
    intro k
    exact measurable_pi_apply k.1

@[simp] lemma insertSliceEquiv_apply {n : ℕ} (i : Fin n)
    (z : E3 × ({k : Fin n // k ≠ i} → E3)) :
    insertSliceEquiv i z = insertCoord i z.1 z.2 := rfl

/-! ## 2. The product decomposition -/

/-- Splitting the product over `Fin n` at the index `i`: the factor at `i` times the product
over the complementary subtype. -/
lemma prod_univ_eq_mul_prod_subtype_ne {M : Type*} [CommMonoid M] {n : ℕ} (i : Fin n)
    (f : Fin n → M) :
    ∏ k, f k = f i * ∏ k : {k : Fin n // k ≠ i}, f k.1 := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun k : Fin n => k ≠ i) f]
  have hki : ∀ a : {k : Fin n // ¬(k ≠ i)}, a.1 = i := fun a => by
    by_contra h; exact a.2 h
  have : Subsingleton {k : Fin n // ¬(k ≠ i)} :=
    ⟨fun a b => Subtype.ext (by rw [hki a, hki b])⟩
  rw [Fintype.prod_subsingleton (f := fun k : {k : Fin n // ¬(k ≠ i)} => f k.1) ⟨i, by simp⟩]
  exact mul_comm _ _

/-! ## 3. The measure-preserving property -/

/-- The coordinate-insertion equivalence carries `μ.prod (Measure.pi fun _ => μ)` to
`Measure.pi (fun _ : Fin n => μ)` for `μ = volume.restrict (boxL ℓ)`. -/
lemma measurePreserving_insertSliceEquiv {n : ℕ} (i : Fin n) (ℓ : ℝ) :
    MeasurePreserving (insertSliceEquiv i)
      (((volume : Measure E3).restrict (boxL ℓ)).prod
        (Measure.pi (fun _ : {k : Fin n // k ≠ i} => (volume : Measure E3).restrict (boxL ℓ))))
      (Measure.pi (fun _ : Fin n => (volume : Measure E3).restrict (boxL ℓ))) := by
  refine MeasurePreserving.mk (insertSliceEquiv i).measurable ?_
  refine (Measure.pi_eq (fun s hs => ?_)).symm
  rw [Measure.map_apply (insertSliceEquiv i).measurable
    (MeasurableSet.pi Set.countable_univ (fun k _ => hs k))]
  have hpre : (insertSliceEquiv i) ⁻¹' (Set.univ.pi s)
      = s i ×ˢ (Set.univ.pi (fun k : {k : Fin n // k ≠ i} => s k.1)) := by
    ext z
    simp only [Set.mem_preimage, insertSliceEquiv_apply, Set.mem_pi, Set.mem_univ, true_implies,
      Set.mem_prod]
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · simpa [insertCoord] using h i
      · intro k
        simpa only [insertCoord, dif_neg k.2] using h k.1
    · rintro ⟨h1, h2⟩ k
      by_cases hk : k = i
      · subst hk; simpa [insertCoord] using h1
      · simpa only [insertCoord, dif_neg hk] using h2 ⟨k, hk⟩
  rw [hpre, Measure.prod_prod, Measure.pi_pi,
    prod_univ_eq_mul_prod_subtype_ne i
      (fun k => (volume : Measure E3).restrict (boxL ℓ) (s k))]

/-! ## 4. The slice identity -/

theorem setIntegral_insertCoord_slice {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n)
    {f : Work.BoseDict.Xn n → ℝ} (hf : Continuous f) :
    (∫ w in Work.BoseK15.corpusBox.boxL ℓ,
        ∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ, f (insertCoord i w x'))
      = ∫ x in Submission.BoseGases.abox n ℓ, f x := by
  have hν : (volume : Measure ({k : Fin n // k ≠ i} → E3)).restrict
        (boxPiSet ({k : Fin n // k ≠ i}) ℓ)
      = Measure.pi (fun _ : {k : Fin n // k ≠ i} => (volume : Measure E3).restrict (boxL ℓ)) := by
    rw [show (volume : Measure ({k : Fin n // k ≠ i} → E3))
          = Measure.pi (fun _ : {k : Fin n // k ≠ i} => (volume : Measure E3)) from volume_pi]
    show (Measure.pi (fun _ : {k : Fin n // k ≠ i} => (volume : Measure E3))).restrict
        (Set.univ.pi (fun _ : {k : Fin n // k ≠ i} => boxL ℓ)) = _
    rw [Measure.restrict_pi_pi]
  have hμn : (volume : Measure (Xn n)).restrict (Submission.BoseGases.abox n ℓ)
      = Measure.pi (fun _ : Fin n => (volume : Measure E3).restrict (boxL ℓ)) := by
    have hbox : Submission.BoseGases.abox n ℓ
        = Set.univ.pi (fun _ : Fin n => boxL ℓ) := by
      rw [Submission.BoseGases.abox_eq_pi_acube]
      simp only [← corpusBox_boxL_eq_acube hℓ]
    rw [hbox, show (volume : Measure (Xn n))
          = Measure.pi (fun _ : Fin n => (volume : Measure E3)) from volume_pi]
    rw [Measure.restrict_pi_pi]
  have hmp := measurePreserving_insertSliceEquiv (n := n) i ℓ
  have hFb : Integrable f
      (Measure.pi (fun _ : Fin n => (volume : Measure E3).restrict (boxL ℓ))) := by
    have hK : IsCompact (Submission.BoseGases.abox n ℓ) := by
      rw [Submission.BoseGases.abox_eq_pi_acube]
      exact isCompact_univ_pi (fun _ => Submission.BoseGases.acube_compact hℓ)
    have h1 : Integrable f ((volume : Measure (Xn n)).restrict (Submission.BoseGases.abox n ℓ)) :=
      hf.continuousOn.integrableOn_compact hK
    rwa [hμn] at h1
  have hInt : Integrable (fun z : E3 × ({k : Fin n // k ≠ i} → E3) => f (insertCoord i z.1 z.2))
      (((volume : Measure E3).restrict (boxL ℓ)).prod
        (Measure.pi (fun _ : {k : Fin n // k ≠ i} => (volume : Measure E3).restrict (boxL ℓ)))) :=
    (hmp.integrable_comp hFb.aestronglyMeasurable).mpr hFb
  calc
    (∫ w in boxL ℓ, ∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ, f (insertCoord i w x'))
        = ∫ w : E3, (∫ x' : ({k : Fin n // k ≠ i} → E3), f (insertCoord i w x')
            ∂(Measure.pi (fun _ : {k : Fin n // k ≠ i} => (volume : Measure E3).restrict (boxL ℓ))))
            ∂((volume : Measure E3).restrict (boxL ℓ)) := by rw [hν]
    _ = ∫ z : E3 × ({k : Fin n // k ≠ i} → E3), f (insertCoord i z.1 z.2)
            ∂(((volume : Measure E3).restrict (boxL ℓ)).prod
              (Measure.pi (fun _ : {k : Fin n // k ≠ i} =>
                (volume : Measure E3).restrict (boxL ℓ)))) :=
          (MeasureTheory.integral_prod _ hInt).symm
    _ = ∫ x : Xn n, f x
            ∂(Measure.pi (fun _ : Fin n => (volume : Measure E3).restrict (boxL ℓ))) :=
          MeasureTheory.MeasurePreserving.integral_comp' (f := insertSliceEquiv i) hmp f
    _ = ∫ x in Submission.BoseGases.abox n ℓ, f x := by rw [← hμn]

end Work.BoseBoxFock
