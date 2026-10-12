import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.B13Aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.ae_fibreIns_compl`

Almost-everywhere triviality of a null set in the *last* coordinate of the one-slot fibre.

For a pair of slots `p : Fin n × Fin n` and a null set `N` of full configurations
`Fin n → ℝ³`, the configurations obtained by inserting `w` in the slot `p.2` and keeping the
remaining coordinates `x' : Fib1 p` fixed avoid `N` for almost every `w` and almost every `x'`.

The proof is the Fubini (Tonelli) theorem for the measure preserving identification

    `E3 × Fib1 p ≃ᵐ (Fin n → E3)`,   `(w, x') ↦ fibreIns p.2 w x'`,

whose inverse is the coordinate-reading map `y ↦ (y p.2, fun k => y k)`.  Concretely:

* `peelEquiv` is Mathlib's splitting of `ι → E3` as `E3 × ({k // k ≠ a} → E3)` along the
  coordinate `a` (`piEquivPiSubtypeProd` followed by the identification of the one-point fibre
  `{k // k = a} → E3` with `E3`), and it is measure preserving
  (`volume_preserving_piEquivPiSubtypeProd` and `volume_preserving_piUnique`);
* its inverse is exactly `fibreIns a`, so the insertion map is measure preserving;
* hence the preimage of a null set has vanishing product measure, and the product a.e. lemma
  `Measure.ae_prod_iff_ae_ae` turns this into the stated almost-everywhere statement.

Everything here is `sorry`-free.
-/

noncomputable section

open MeasureTheory

set_option linter.style.haveILetI false

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {n : ℕ}

/-! ## The coordinate-splitting equivalence and its inverse `fibreIns` -/

/-- Splitting off the coordinate `a` as a factor `E3`. -/
private def peelEquiv (ι : Type*) [Fintype ι] [DecidableEq ι] (a : ι) :
    (ι → E3) ≃ᵐ E3 × ({k : ι // k ≠ a} → E3) := by
  letI : Unique {k : ι // k = a} := uniqueOfSubsingleton ⟨a, rfl⟩
  exact (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => E3) (fun k : ι => k = a)).trans
    ((MeasurableEquiv.funUnique {k : ι // k = a} E3).prodCongr (MeasurableEquiv.refl _))

private theorem peelEquiv_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι) (x : ι → E3) :
    peelEquiv ι a x = (x a, fun k : {k : ι // k ≠ a} => x k.1) := by
  simp only [peelEquiv, MeasurableEquiv.trans_apply, MeasurableEquiv.piEquivPiSubtypeProd_apply,
    MeasurableEquiv.prodCongr, MeasurableEquiv.funUnique]
  rfl

private theorem peelEquiv_symm_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι)
    (q : E3 × ({k : ι // k ≠ a} → E3)) :
    (peelEquiv ι a).symm q = fibreIns a q.1 q.2 := by
  refine (Equiv.symm_apply_eq (peelEquiv ι a).toEquiv).mpr ?_
  change q = peelEquiv ι a (fibreIns a q.1 q.2)
  rw [peelEquiv_apply]
  refine Prod.ext ?_ ?_
  · simp only [fibreIns]
    rw [dif_pos trivial]
  · funext k
    simp only [fibreIns]
    rw [dif_neg k.2]

private theorem peelEquiv_fun_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι) :
    ⇑(peelEquiv ι a) = fun x : ι → E3 =>
      Prod.map (⇑(MeasurableEquiv.funUnique {k : ι // k = a} E3)) id
        (⇑(MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => E3) (fun k : ι => k = a)) x) := by
  funext x
  rw [peelEquiv_apply, MeasurableEquiv.piEquivPiSubtypeProd_apply, Prod.map_apply,
    MeasurableEquiv.funUnique_apply]
  rfl

private theorem measurePreserving_peelEquiv {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι) :
    MeasurePreserving (peelEquiv ι a) (volume : Measure (ι → E3))
      (volume : Measure (E3 × ({k : ι // k ≠ a} → E3))) := by
  letI : Unique {k : ι // k = a} := uniqueOfSubsingleton ⟨a, rfl⟩
  letI : Fintype {k : ι // k = a} := Subtype.fintype (fun k : ι => k = a)
  have h₁ := volume_preserving_piEquivPiSubtypeProd (fun _ : ι => E3) (fun k : ι => k = a)
  have h₂ := volume_preserving_piUnique (fun _ : {k : ι // k = a} => E3)
  have h₃ := h₂.prod (MeasurePreserving.id (volume : Measure ({k : ι // ¬(k = a)} → E3)))
  refine (h₃.comp h₁).congr (peelEquiv ι a).measurable ?_
  filter_upwards with x
  exact congrFun (peelEquiv_fun_eq (ι := ι) a) x

/-- The coordinate insertion `(w, x') ↦ fibreIns a w x'` is measure preserving: it is the inverse
of the measure preserving splitting `peelEquiv`. -/
theorem measurePreserving_fibreIns {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι) :
    MeasurePreserving (fun q : E3 × ({k : ι // k ≠ a} → E3) => fibreIns a q.1 q.2)
      (volume : Measure (E3 × ({k : ι // k ≠ a} → E3))) (volume : Measure (ι → E3)) :=
  MeasurePreserving.symm (peelEquiv ι a) (measurePreserving_peelEquiv (ι := ι) a) |>.congr
    (measurable_pi_iff.mpr (fun k => by
      by_cases h : k = a
      · simpa only [fibreIns, dif_pos h] using measurable_fst
      · have hk : Measurable (fun q : E3 × ({k : ι // k ≠ a} → E3) => q.2 ⟨k, h⟩) :=
          (measurable_pi_apply (⟨k, h⟩ : {k : ι // k ≠ a})).comp measurable_snd
        simpa only [fibreIns, dif_neg h] using hk))
    (Filter.Eventually.of_forall fun q => peelEquiv_symm_apply a q)

/-! ## The a.e. statement -/

theorem ae_fibreIns_compl {n : ℕ} (p : Fin n × Fin n) {N : Set (Fin n → EuclideanSpace ℝ (Fin 3))} (hN : MeasurableSet N) (h0 : MeasureTheory.volume N = 0) : ∀ᵐ w : EuclideanSpace ℝ (Fin 3), ∀ᵐ x' : Work.BoseBoxFock.Fib1 p, fibreIns p.2 w x' ∉ N := by
  classical
  have hT : Measurable (fun q : E3 × Fib1 p => fibreIns p.2 q.1 q.2) :=
    measurable_fibreIns_prod p
  -- the insertion map is measure preserving from the product measure
  have hvol : (volume : Measure (E3 × Fib1 p))
      = (volume : Measure E3).prod (volume : Measure (Fib1 p)) :=
    MeasureTheory.Measure.volume_eq_prod E3 (Fib1 p)
  have hmp : MeasurePreserving (fun q : E3 × Fib1 p => fibreIns p.2 q.1 q.2)
      ((volume : Measure E3).prod (volume : Measure (Fib1 p)))
      (volume : Measure (Fin n → E3)) := by
    rw [← hvol]
    exact measurePreserving_fibreIns (ι := Fin n) p.2
  -- the bad set has vanishing product measure
  have hzero : ((volume : Measure E3).prod (volume : Measure (Fib1 p)))
      ((fun q : E3 × Fib1 p => fibreIns p.2 q.1 q.2) ⁻¹' N) = 0 := by
    rw [hmp.measure_preimage hN.nullMeasurableSet, h0]
  -- hence it is trivial for almost every point of the product
  have hae : ∀ᵐ q ∂((volume : Measure E3).prod (volume : Measure (Fib1 p))),
      q ∉ (fun q : E3 × Fib1 p => fibreIns p.2 q.1 q.2) ⁻¹' N := by
    rw [MeasureTheory.ae_iff]
    have hset : {a : E3 × Fib1 p | ¬ a ∉ (fun q : E3 × Fib1 p => fibreIns p.2 q.1 q.2) ⁻¹' N}
        = (fun q : E3 × Fib1 p => fibreIns p.2 q.1 q.2) ⁻¹' N := by
      ext a
      simp
    rw [hset, hzero]
  -- product a.e. lemma
  exact (MeasureTheory.Measure.ae_prod_iff_ae_ae (μ := (volume : Measure E3))
    (ν := (volume : Measure (Fib1 p)))
    (p := fun q : E3 × Fib1 p => q ∉ (fun q : E3 × Fib1 p => fibreIns p.2 q.1 q.2) ⁻¹' N)
    (hN.preimage hT).compl).mp hae

end Work.BoseBoxFock
