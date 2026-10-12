import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.DvApriori.Band.Collapse
import Submission.Work.BoseFixB2.DvApriori.Band.integrableOn_mul_of_continuous_of_integrable
import Submission.Work.BoseFixB2.DvApriori.Band.jointProj_pairing_eq_zero_of_free_ne
import Submission.Work.BoseFixB2.DvApriori.Band.projOn_comp_jointProj
import Submission.Work.BoseFixB2.DvApriori.Band.sum_secProj_eq_sum_triples
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB2.DvApriori.Band.Universal`

The **band identity for a single few-slot term**: for a weight `W` that is constant along
all slots outside a slot set `A` (and merely integrable),

    Σᵢ ⟨1_{n₊=i}Φ, W 1_{n₊=i+1}Φ⟩
      = Σ_{U,V ⊆ A, |V| = |U|+1} ⟨E_U^A Φ, W E_V^A Φ⟩,

where `E_U^A = projOn ℓ A U` is the projection onto the pattern `U` of the slots of `A`.

The proof chains the corpus-free ingredients:

* `sum_secProj_eq_sum_triples` — expand `secProj` and re-index the pairs `(S,T)` with
  `|T| = |S|+1` into the triples `(R,U,V)`, killing the off-diagonal pairs with
  `jointProj_pairing_eq_zero_of_free_ne` (the "one free slot" orthogonality);
* `sum_jointProj_pairing` — the free-slot collapse `Σ_R∫(X_R η)W(X_R ζ) = ∫ηWζ`
  (`sum_slotProd_pairing`) transported from `slotProd` to `jointProj`
  (`projOn_comp_jointProj`).
-/

namespace Work.BoseFixB2.DvApriori

open Submission.BoseGases MeasureTheory

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section


/-- **The free-slot collapse in `jointProj` form**: for a weight constant along the free
slots `J` (with `A ⊔ J = [n]`), the sum over the patterns `R ⊆ J` of the pairings of the
joint sector projections collapses to the pairing of the `A`-projections. -/
theorem sum_jointProj_pairing {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {A J U V : Finset ℕ}
    (hAJ : A ∪ J = Finset.range n) (hdisj : Disjoint A J)
    (hU : U ⊆ A) (hV : V ⊆ A) {W : Submission.BoseGases.X n → ℝ}
    (hWin : ∀ (j : ℕ) (hj : j < n), j ∈ J →
      ∀ (x : Submission.BoseGases.X n) (z : EuclideanSpace ℝ (Fin 3)),
        W (Function.update x ⟨j, hj⟩ z) = W x)
    (hWi : IntegrableOn W (abox n ℓ)) {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ) :
    (∑ R ∈ J.powerset, ∫ x in abox n ℓ,
        jointProj ℓ (R ∪ U) Φ x * W x * jointProj ℓ (R ∪ V) Φ x)
      = ∫ x in abox n ℓ, projOn ℓ A U Φ x * W x * projOn ℓ A V Φ x := by
  have hJ : J ⊆ Finset.range n := fun j hj => by
    rw [← hAJ]; exact Finset.mem_union_right A hj
  have hkey := sum_slotProd_pairing (ℓ := ℓ) hℓ (slotList n J)
    (slotList_nodup n J) (fun j hj => slotList_lt hj)
    (W := W) (η := projOn ℓ A U Φ) (ζ := projOn ℓ A V Φ)
    (fun j hj hjlt => hWin j hjlt (mem_slotList.mp hj).2)
    hWi (projOn_continuous hℓ A U hΦ) (projOn_continuous hℓ A V hΦ)
  rw [slotList_toFinset hJ] at hkey
  rw [← hkey]
  refine Finset.sum_congr rfl (fun R hR => ?_)
  have hR' : R ⊆ J := Finset.mem_powerset.mp hR
  have e1 : slotProd ℓ (slotList n J) R (projOn ℓ A U Φ) = jointProj ℓ (R ∪ U) Φ :=
    Work.BoseFixB2.DvApriori.Band.projOn_comp_jointProj hℓ hAJ hdisj hU hR' hΦ
  have e2 : slotProd ℓ (slotList n J) R (projOn ℓ A V Φ) = jointProj ℓ (R ∪ V) Φ :=
    Work.BoseFixB2.DvApriori.Band.projOn_comp_jointProj hℓ hAJ hdisj hV hR' hΦ
  rw [e1, e2]

/-- **The band identity for a single few-slot term.** -/
theorem band_sum_eq_sum_projOn {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Finset.range n) {W : Submission.BoseGases.X n → ℝ}
    (hWint : IntegrableOn W (abox n ℓ))
    (hWin : ∀ (j : ℕ) (hj : j < n), j ∉ A →
      ∀ (x : Submission.BoseGases.X n) (z : EuclideanSpace ℝ (Fin 3)),
        W (Function.update x ⟨j, hj⟩ z) = W x)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    (∑ i ∈ Finset.range n, ∫ x in abox n ℓ,
        Work.BoseFixB2.secProj ℓ i Φ x * W x * Work.BoseFixB2.secProj ℓ (i+1) Φ x)
      = ∑ U ∈ A.powerset,
          ∑ V ∈ A.powerset.filter (fun V => V.card = U.card + 1),
            ∫ x in abox n ℓ, projOn ℓ A U Φ x * W x * projOn ℓ A V Φ x := by
  have hΦc : Continuous Φ := hΦ.continuous
  have hJ : (Finset.range n \ A) ∪ A = Finset.range n := by
    ext j; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_range]
    constructor
    · rintro (⟨hj, _⟩ | hj); exacts [hj, Finset.mem_range.mp (hA hj)]
    · intro hj; by_cases h : j ∈ A
      · exact Or.inr h
      · exact Or.inl ⟨hj, h⟩
  have hdisj : Disjoint (Finset.range n \ A) A := Finset.disjoint_sdiff.symm
  rw [Work.BoseFixB2.DvApriori.Band.sum_secProj_eq_sum_triples hℓ hA hWint hΦ (fun S T hS hT hST =>
    Work.BoseFixB2.DvApriori.Band.jointProj_pairing_eq_zero_of_free_ne hℓ hA
      (fun j hj hjA x z => hWin j hj hjA x z) hS hT hST hΦ
      (Work.BoseFixB2.DvApriori.Band.integrableOn_mul_of_continuous_of_integrable hℓ
        (Work.BoseFixB2.Sector.jointProj_continuous hℓ S hΦc)
        (Work.BoseFixB2.Sector.jointProj_continuous hℓ T hΦc) hWint))]
  have hswap : (∑ R ∈ (Finset.range n \ A).powerset, ∑ U ∈ A.powerset,
        ∑ V ∈ A.powerset.filter (fun V => V.card = U.card + 1),
          ∫ x in Submission.BoseGases.abox n ℓ,
            Work.BoseFixB2.jointProj ℓ (R ∪ U) Φ x * W x
              * Work.BoseFixB2.jointProj ℓ (R ∪ V) Φ x)
      = ∑ U ∈ A.powerset, ∑ V ∈ A.powerset.filter (fun V => V.card = U.card + 1),
          ∑ R ∈ (Finset.range n \ A).powerset,
            ∫ x in Submission.BoseGases.abox n ℓ,
              Work.BoseFixB2.jointProj ℓ (R ∪ U) Φ x * W x
                * Work.BoseFixB2.jointProj ℓ (R ∪ V) Φ x := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun U hU => ?_)
    exact Finset.sum_comm
  rw [hswap]
  refine Finset.sum_congr rfl (fun U hU => Finset.sum_congr rfl (fun V hV => ?_))
  exact sum_jointProj_pairing (A := A) (J := Finset.range n \ A) hℓ
    (by rw [Finset.union_comm]; exact hJ) hdisj.symm
    (Finset.mem_powerset.mp hU) (Finset.mem_powerset.mp ((Finset.mem_filter.mp hV).1))
    (fun j hj hjJ x z => hWin j hj (fun h => (Finset.mem_sdiff.mp hjJ).2 h) x z) hWint hΦc

end

end Work.BoseFixB2.DvApriori
