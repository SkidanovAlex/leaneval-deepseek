import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.Defs
import Submission.Work.BoseBoxFock.integral_fibre_two
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.fibre_kernel_free` — splitting off one slot from a kernel integral

For a kernel `K` acting on a single slot, a "many-body" function `M` of the configuration and the
kernel variable, and an integrable pairing `(x, y) ↦ K (x i) y * M x y` on
`(Fin n → ℝ³) × ℝ³`, the integral

    `∫ x, ∫ y, K (x i) y * M x y`

can be computed slot-by-slot: first freeze the `i`-th coordinate to a value `w : ℝ³`, integrate the
remaining `n - 1` coordinates, and only then integrate over `w`:

    `= ∫ w, ∫ y, K w y * ∫ x', M (·[i ↦ w]) y`.

The proof is the fibre decomposition of the Lebesgue integral
(`Work.BoseBoxFock.integral_fibre_one`) together with Fubini in the two remaining variables.  The
integrability input needed for that second Fubini exchange is transported from the hypothesis along
the measure preserving equivalence which peels the `i`-th coordinate off the configuration space
(`peelEquiv` below, an instance of `MeasurableEquiv.piEquivPiSubtypeProd` followed by the
identification of the (unique) one-point factor with `ℝ³`), composed with the reassociation
`(ℝ³ × X') × ℝ³ ≃ᵐ ℝ³ × (X' × ℝ³)`.
-/

namespace Work.BoseBoxFock

open MeasureTheory

set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

noncomputable section

local notation "𝔼" => EuclideanSpace ℝ (Fin 3)

/-! ## Peeling one coordinate off the configuration space -/

/-- The measurable equivalence splitting a configuration into its `a`-th coordinate and the
remaining coordinates. -/
private def peelEquiv (ι : Type*) [Fintype ι] [DecidableEq ι] (a : ι) :
    (ι → 𝔼) ≃ᵐ 𝔼 × ({k : ι // k ≠ a} → 𝔼) := by
  letI : Unique {k : ι // k = a} := uniqueOfSubsingleton ⟨a, rfl⟩
  exact (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => 𝔼) (fun k : ι => k = a)).trans
    ((MeasurableEquiv.funUnique {k : ι // k = a} 𝔼).prodCongr (MeasurableEquiv.refl _))

private theorem peelEquiv_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι) (x : ι → 𝔼) :
    peelEquiv ι a x = (x a, fun k : {k : ι // k ≠ a} => x k.1) := by
  simp only [peelEquiv, MeasurableEquiv.trans_apply, MeasurableEquiv.piEquivPiSubtypeProd_apply,
    MeasurableEquiv.prodCongr, MeasurableEquiv.funUnique]
  rfl

private theorem peelEquiv_fun_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι) :
    ⇑(peelEquiv ι a) = fun x : ι → 𝔼 =>
      Prod.map (⇑(MeasurableEquiv.funUnique {k : ι // k = a} 𝔼)) id
        (⇑(MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => 𝔼) (fun k : ι => k = a)) x) := by
  funext x
  rw [peelEquiv, MeasurableEquiv.trans_apply]
  rfl

private theorem peelEquiv_symm_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι)
    (p : 𝔼 × ({k : ι // k ≠ a} → 𝔼)) :
    (peelEquiv ι a).symm p = fibreIns a p.1 p.2 := by
  refine (Equiv.symm_apply_eq (peelEquiv ι a).toEquiv).mpr ?_
  change p = peelEquiv ι a (fibreIns a p.1 p.2)
  rw [peelEquiv_apply]
  refine Prod.ext ?_ ?_
  · simp only [fibreIns]
    rw [dif_pos trivial]
  · funext k
    simp only [fibreIns]
    rw [dif_neg k.2]

private theorem measurePreserving_peelEquiv {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι) :
    MeasurePreserving (peelEquiv ι a) (volume : Measure (ι → 𝔼))
      (volume : Measure (𝔼 × ({k : ι // k ≠ a} → 𝔼))) := by
  letI : Unique {k : ι // k = a} := uniqueOfSubsingleton ⟨a, rfl⟩
  letI : Fintype {k : ι // k = a} := Subtype.fintype (fun k : ι => k = a)
  have h₁ := volume_preserving_piEquivPiSubtypeProd (fun _ : ι => 𝔼) (fun k : ι => k = a)
  have h₂ := volume_preserving_piUnique (fun _ : {k : ι // k = a} => 𝔼)
  have h₃ := h₂.prod (MeasurePreserving.id (volume : Measure ({k : ι // ¬(k = a)} → 𝔼)))
  refine (h₃.comp h₁).congr (peelEquiv ι a).measurable ?_
  filter_upwards with x
  exact congrFun (peelEquiv_fun_eq (ι := ι) a) x

/-! ## The Fubini exchange -/

/-- The Fubini-type rearrangement: the iterated integral of `G` over the configuration and over the
kernel variable equals the integral over the frozen `a`-th coordinate, the kernel variable, and the
remaining coordinates. -/
private theorem fubini_fibre_aux {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι)
    {G : (ι → 𝔼) → 𝔼 → ℂ}
    (hG : Integrable (Function.uncurry G) ((volume : Measure (ι → 𝔼)).prod volume)) :
    (∫ x : ι → 𝔼, ∫ y : 𝔼, G x y)
      = ∫ w : 𝔼, ∫ y : 𝔼, ∫ x' : {k : ι // k ≠ a} → 𝔼, G (fibreIns a w x') y := by
  classical
  -- Integrability of the re-associated triple integrand, transported from `hG` along `peelEquiv`
  -- and the reassociation of the product measure.
  have hae : ∀ᵐ w ∂(volume : Measure 𝔼), Integrable
      (fun r : ({k : ι // k ≠ a} → 𝔼) × 𝔼 => G (fibreIns a w r.1) r.2)
      ((volume : Measure ({k : ι // k ≠ a} → 𝔼)).prod (volume : Measure 𝔼)) := by
    have hmp₁ : MeasurePreserving (Prod.map (⇑(peelEquiv ι a).symm) (id : 𝔼 → 𝔼))
        ((volume : Measure (𝔼 × ({k : ι // k ≠ a} → 𝔼))).prod (volume : Measure 𝔼))
        ((volume : Measure (ι → 𝔼)).prod (volume : Measure 𝔼)) :=
      (MeasurePreserving.symm (peelEquiv ι a) (measurePreserving_peelEquiv (ι := ι) a)).prod
        (MeasurePreserving.id (volume : Measure 𝔼))
    have key₁ : Integrable
        (fun q : (𝔼 × ({k : ι // k ≠ a} → 𝔼)) × 𝔼 => G (fibreIns a q.1.1 q.1.2) q.2)
        ((volume : Measure ((𝔼 × ({k : ι // k ≠ a} → 𝔼)) × 𝔼))) := by
      refine ((hmp₁.integrable_comp hG.aestronglyMeasurable).mpr hG).congr ?_
      filter_upwards with q
      rw [Function.comp_apply, Prod.map_apply, id_eq, peelEquiv_symm_apply,
        Function.uncurry_apply_pair]
    have key₂ : Integrable
        (fun q : 𝔼 × (({k : ι // k ≠ a} → 𝔼) × 𝔼) => G (fibreIns a q.1 q.2.1) q.2.2)
        ((volume : Measure 𝔼).prod
          ((volume : Measure ({k : ι // k ≠ a} → 𝔼)).prod (volume : Measure 𝔼))) := by
      have hpa := volume_preserving_prodAssoc (α₁ := 𝔼) (β₁ := ({k : ι // k ≠ a} → 𝔼))
        (γ₁ := 𝔼)
      have hg : AEStronglyMeasurable
          (fun q : 𝔼 × (({k : ι // k ≠ a} → 𝔼) × 𝔼) => G (fibreIns a q.1 q.2.1) q.2.2)
          ((volume : Measure 𝔼).prod
            ((volume : Measure ({k : ι // k ≠ a} → 𝔼)).prod (volume : Measure 𝔼))) :=
        (hpa.aestronglyMeasurable_comp_iff
          MeasurableEquiv.prodAssoc.measurableEmbedding).mp key₁.aestronglyMeasurable
      exact (hpa.integrable_comp hg).mp key₁
    exact key₂.prod_right_ae
  have hH : Integrable (fun x : ι → 𝔼 => ∫ y : 𝔼, G x y) (volume : Measure (ι → 𝔼)) := by
    simpa only [Function.uncurry_apply_pair] using hG.integral_prod_left
  refine (integral_fibre_one (ι := ι) a hH).trans ?_
  beta_reduce
  refine integral_congr_ae ?_
  filter_upwards [hae] with w hw
  exact integral_integral_swap hw

theorem fibre_kernel_free {n : ℕ} {i : Fin n}
    {K : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ}
    {M : (Fin n → EuclideanSpace ℝ (Fin 3)) → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hG : MeasureTheory.Integrable
      (fun z : (Fin n → EuclideanSpace ℝ (Fin 3)) × EuclideanSpace ℝ (Fin 3) =>
        K (z.1 i) z.2 * M z.1 z.2)) :
    (∫ x : Fin n → EuclideanSpace ℝ (Fin 3), ∫ y : EuclideanSpace ℝ (Fin 3), K (x i) y * M x y)
      = ∫ w : EuclideanSpace ℝ (Fin 3), ∫ y : EuclideanSpace ℝ (Fin 3), K w y *
          (∫ x' : {k : Fin n // k ≠ i} → EuclideanSpace ℝ (Fin 3),
            M (fun k => if h : k = i then w else x' ⟨k, h⟩) y) := by
  classical
  refine (fubini_fibre_aux (ι := Fin n) i (G := fun x y => K (x i) y * M x y) hG).trans ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have hwi : ∀ x' : {k : Fin n // k ≠ i} → 𝔼, (fibreIns i w x') i = w := fun x' => by
    simp [fibreIns]
  simp only [hwi]
  exact integral_const_mul _ _

end

end Work.BoseBoxFock
