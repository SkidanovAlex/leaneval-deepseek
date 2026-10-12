import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.boxSmoothAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.boxPiSet_proj` — the projection (marginal) identity for the product box

For an injection `τ : K → J` of finite index types and a continuous
`F : (K → ℝ³) → ℝ`,

    ∫ a in boxPiSet J ℓ, F (fun k => a (τ k))
      = ℓ ^ (3 * (card J - card K)) * ∫ p in boxPiSet K ℓ, F p .

The product box is the `Measure.pi` of the box measure `boxMeas ℓ = volume ↾ boxL ℓ`
(`restrict_boxPiSet`, proved here from Mathlib's `Measure.restrict_pi_pi`), and the volume of
the box is `ℓ³` (`volume_corpusBox_boxL`).  Writing `D = J \ range τ`, the injection `τ` extends
to a bijection `e : K ⊕ D ≃ J`, hence (Mathlib's `measurePreserving_piCongrLeft`) the
`Measure.pi` over `J` pulls back to the `Measure.pi` over `K ⊕ D`; the latter splits as a product
(`measurePreserving_sumPiEquivProdPi`), and integrating the `K`-marginal against the second
factor contributes the total mass `(boxMeas ℓ univ)^{card D} = ℓ^{3·card D}`.

The main statement is `boxPiSet_proj`; the measure-theoretic heart is `integral_pi_proj`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The elementary box facts -/

/-- The volume of the box `Λ(ℓ) = ℓ • unitCell = boxL ℓ` is `ℓ³`. -/
theorem volume_corpusBox_boxL {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (volume : Measure E3) (Work.BoseK15.corpusBox.boxL ℓ) = ENNReal.ofReal (ℓ ^ 3) := by
  rw [corpusBox_boxL_eq_acube hℓ]
  exact Submission.BoseGases.acube_volume ℓ hℓ.le

/-- The box measure `volume ↾ boxL ℓ` is finite (`boxL ℓ` has volume `ℓ³`). -/
theorem isFiniteMeasure_restrict_boxL {ℓ : ℝ} (hℓ : 0 < ℓ) :
    IsFiniteMeasure ((volume : Measure E3).restrict (Work.BoseK15.corpusBox.boxL ℓ)) := by
  constructor
  rw [Measure.restrict_apply' (Work.BoseK15.corpusBox.boxL_measurableSet ℓ), Set.univ_inter,
    volume_corpusBox_boxL hℓ]
  exact ENNReal.ofReal_lt_top

/-- The volume of the product box, as a restricted product measure: the restriction of the
product volume to `boxPiSet ι ℓ = ∏_{i ∈ ι} boxL ℓ` is the product of the box measures. -/
theorem restrict_boxPiSet (ι : Type*) [Fintype ι] {ℓ : ℝ} :
    (volume : Measure (ι → E3)).restrict (boxPiSet ι ℓ)
      = Measure.pi (fun _ : ι => (volume : Measure E3).restrict
          (Work.BoseK15.corpusBox.boxL ℓ)) := by
  rw [show boxPiSet ι ℓ = Set.pi Set.univ (fun _ : ι => Work.BoseK15.corpusBox.boxL ℓ)
      from rfl,
    MeasureTheory.volume_pi, MeasureTheory.Measure.restrict_pi_pi]

/-! ## 2. The measure-theoretic projection identity -/

/-- **The projection identity for the product measure.**  For a finite measure `ν` on `ℝ³`, an
injection `τ : K → J` of finite types and a continuous `F` on `K → ℝ³`,

    ∫ a ∂(ν^⊗J), F (a ∘ τ) = (ν univ)^{card J − card K} · ∫ p ∂(ν^⊗K), F p .

Writing `D = {j // j ∉ range τ}`, the injection `τ` extends to a bijection `e : K ⊕ D ≃ J`; the
change of variables `a ↦ a ∘ e.symm` is measure preserving (`measurePreserving_piCongrLeft`), so
the left-hand side is `∫ x ∂(ν^⊗(K⊕D)), F (x ∘ inl)`; the sum index splits as a product
(`measurePreserving_sumPiEquivProdPi`), and the `K`-marginal is integrated against the second
factor by `Measure.map_fst_prod` and `integral_smul_measure`. -/
theorem integral_pi_proj {K J : Type*} [Fintype K] [Fintype J] [DecidableEq J]
    (ν : Measure E3) [IsFiniteMeasure ν] (τ : K → J) (hτ : Function.Injective τ)
    (F : (K → E3) → ℝ) (hF : Continuous F) :
    (∫ a, F (fun k => a (τ k)) ∂(Measure.pi (fun _ : J => ν)))
      = (ν Set.univ).toReal ^ (Fintype.card J - Fintype.card K)
          * ∫ p, F p ∂(Measure.pi (fun _ : K => ν)) := by
  classical
  -- the complement of the range of `τ`
  let D := {j : J // j ∉ Set.range τ}
  have hDfin : Fintype D := inferInstance
  have hinj : Function.Injective (Sum.elim τ (Subtype.val : D → J)) := by
    intro a b hab
    cases a with
    | inl k =>
      cases b with
      | inl k' => exact congrArg Sum.inl (hτ hab)
      | inr d => exact absurd ⟨k, hab⟩ d.2
    | inr d =>
      cases b with
      | inl k => exact absurd ⟨k, hab.symm⟩ d.2
      | inr d' => exact congrArg Sum.inr (Subtype.ext hab)
  have hsurj : Function.Surjective (Sum.elim τ (Subtype.val : D → J)) := by
    intro j
    by_cases hj : j ∈ Set.range τ
    · obtain ⟨k, rfl⟩ := hj; exact ⟨Sum.inl k, rfl⟩
    · exact ⟨Sum.inr ⟨j, hj⟩, rfl⟩
  let e : K ⊕ D ≃ J := Equiv.ofBijective (Sum.elim τ (Subtype.val : D → J)) ⟨hinj, hsurj⟩
  have he : ∀ k : K, e (Sum.inl k) = τ k := fun k => Equiv.ofBijective_apply _ _ (Sum.inl k)
  have hcard : Fintype.card D = Fintype.card J - Fintype.card K := by
    have h1 : Fintype.card (K ⊕ D) = Fintype.card K + Fintype.card D := Fintype.card_sum
    have h2 : Fintype.card (K ⊕ D) = Fintype.card J := Fintype.card_congr e
    omega
  -- step 1: reindex `J` as `K ⊕ D`
  have hφ₁ : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : J => E3) e)
      (Measure.pi (fun _ : K ⊕ D => ν)) (Measure.pi (fun _ : J => ν)) :=
    measurePreserving_piCongrLeft (fun _ : J => ν) e
  have hcomp : ∀ x : K ⊕ D → E3,
      (fun k : K => (MeasurableEquiv.piCongrLeft (fun _ : J => E3) e) x (τ k))
        = fun k : K => x (Sum.inl k) := by
    intro x
    funext k
    rw [← he k]
    exact MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : J => E3) e x (Sum.inl k)
  have hstep1 : (∫ a, F (fun k => a (τ k)) ∂(Measure.pi (fun _ : J => ν)))
      = ∫ x, F (fun k => x (Sum.inl k)) ∂(Measure.pi (fun _ : K ⊕ D => ν)) := by
    rw [← MeasurePreserving.integral_comp hφ₁ (MeasurableEquiv.measurableEmbedding _)
      (fun a => F (fun k => a (τ k)))]
    apply integral_congr_ae
    filter_upwards with x
    simp only [hcomp x]
  -- step 2: split the sum index as a product
  have hφ₂ : MeasurePreserving (MeasurableEquiv.sumPiEquivProdPi (fun _ : K ⊕ D => E3))
      (Measure.pi (fun _ : K ⊕ D => ν))
      ((Measure.pi fun _ : K => ν).prod (Measure.pi fun _ : D => ν)) :=
    measurePreserving_sumPiEquivProdPi (fun _ : K ⊕ D => ν)
  have hstep2 : (∫ x, F (fun k => x (Sum.inl k)) ∂(Measure.pi (fun _ : K ⊕ D => ν)))
      = ∫ q, F q.1 ∂((Measure.pi fun _ : K => ν).prod (Measure.pi fun _ : D => ν)) := by
    rw [← MeasurePreserving.integral_comp hφ₂ (MeasurableEquiv.measurableEmbedding _)
      (fun q => F q.1)]
    apply integral_congr_ae
    filter_upwards with x
    have hq : (MeasurableEquiv.sumPiEquivProdPi (fun _ : K ⊕ D => E3) x).1
        = fun k : K => x (Sum.inl k) := by
      rw [MeasurableEquiv.coe_sumPiEquivProdPi, Equiv.sumPiEquivProdPi_apply]
    simp only [hq]
  -- step 3: integrate the `K`-marginal against the second factor
  have hstep3 : (∫ q, F q.1 ∂((Measure.pi fun _ : K => ν).prod (Measure.pi fun _ : D => ν)))
      = ((Measure.pi (fun _ : D => ν)) Set.univ).toReal
          * ∫ p, F p ∂(Measure.pi (fun _ : K => ν)) := by
    have hfst : (∫ q, F q.1 ∂((Measure.pi fun _ : K => ν).prod (Measure.pi fun _ : D => ν)))
        = ∫ y, F y ∂Measure.map Prod.fst
            ((Measure.pi fun _ : K => ν).prod (Measure.pi fun _ : D => ν)) :=
      (MeasureTheory.integral_map (φ := Prod.fst) (f := F)
        measurable_fst.aemeasurable hF.aestronglyMeasurable).symm
    rw [hfst, MeasureTheory.Measure.map_fst_prod, MeasureTheory.integral_smul_measure,
      smul_eq_mul]
  -- the total mass of the complement factors
  have hPD : ((Measure.pi fun _ : D => ν) Set.univ).toReal
      = (ν Set.univ).toReal ^ (Fintype.card J - Fintype.card K) := by
    rw [Measure.pi_univ]
    simp only [Finset.prod_const, Finset.card_univ]
    rw [ENNReal.toReal_pow, ← hcard]
  rw [hstep1, hstep2, hstep3, hPD]

/-! ## 3. The target -/

theorem boxPiSet_proj {K J : Type*} [Fintype K] [Fintype J] {ℓ : ℝ} (hℓ : 0 < ℓ)
    (τ : K → J) (hτ : Function.Injective τ)
    (F : (K → EuclideanSpace ℝ (Fin 3)) → ℝ) (hF : Continuous F) :
    (∫ a in Work.BoseBoxFock.boxPiSet J ℓ, F (fun k => a (τ k)))
      = ℓ ^ (3 * (Fintype.card J - Fintype.card K))
          * ∫ p in Work.BoseBoxFock.boxPiSet K ℓ, F p := by
  classical
  haveI hfin : IsFiniteMeasure ((volume : Measure E3).restrict
      (Work.BoseK15.corpusBox.boxL ℓ)) := isFiniteMeasure_restrict_boxL hℓ
  have hvol : (((volume : Measure E3).restrict (Work.BoseK15.corpusBox.boxL ℓ)) Set.univ).toReal
      = ℓ ^ 3 := by
    rw [Measure.restrict_apply' (Work.BoseK15.corpusBox.boxL_measurableSet ℓ), Set.univ_inter,
      volume_corpusBox_boxL hℓ, ENNReal.toReal_ofReal (by positivity)]
  rw [restrict_boxPiSet J, restrict_boxPiSet K,
    integral_pi_proj ((volume : Measure E3).restrict (Work.BoseK15.corpusBox.boxL ℓ)) τ hτ F hF,
    hvol, ← pow_mul]

end Work.BoseBoxFock
