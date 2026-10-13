import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Deleg.i1Paper_weakMixedDefs
import Submission.Work.FTS.EllipticEst.Deleg.mixedTrunc.QuadBasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Deleg.mixedTrunc

set_option linter.unusedVariables false

/-- **The collar bound on a single `θ`-slice.**

`CollarBound Cw` is a *schema*: it bounds the `ψ_δ''`-moment of any `f : ℝ → ℝ` of class `C¹` on
`(0,π/2)` whose endpoint rates are controlled by the partial `σ`-energies of `deriv f`.  This
lemma is the instance of that schema at the slice `f = Uz u z = z ∂_z u(z,·)`, whose derivative is
the mixed slot `Vz u z = z ∂_z∂_θ u(z,·)` (`hder`): the `deriv f`-integrability and the two rate
hypotheses are transported across the pointwise identity `deriv (Uz u z) = Vz u z` on
`(0,π/2)`, which holds on every set on which the quantities occur (the collar intervals
`(0,δ)` and `(π/2-δ,π/2)` both lie inside `(0,π/2)` because `4δ ≤ π/2`).

This is the per-slice input of `Work.FTS.EllipticEst.Deleg.mixedTruncPairLe`. -/
theorem sliceCollarLe (Cw : ℝ) (hC : Work.FTS.EllipticEst.Deleg.CollarBound Cw)
    (u : ℝ → ℝ → ℝ) (K z δ : ℝ) (hK : 0 < K) (hδ : 0 < δ) (hδ2 : 4 * δ ≤ Real.pi / 2)
    (hz : 0 < z)
    (hsmooth : ContDiffOn ℝ 1 (fun θ => Work.FTS.EllipticEst.AeColl.Uz u z θ)
      (Set.Ioo 0 (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.AeColl.Vz u z θ) ^ 2
        * Work.FTS.EllipticEst.AeColl.sigθ θ) (Set.Ioo 0 (Real.pi / 2)))
    (hder : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      deriv (fun θ' => Work.FTS.EllipticEst.AeColl.Uz u z θ') θ
        = Work.FTS.EllipticEst.AeColl.Vz u z θ)
    (hr1 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Work.FTS.EllipticEst.AeColl.Uz u z θ) ^ 2 ≤ K * θ ^ (1 + Work.Spaces.eta)
        * (∫ t in Set.Ioo 0 θ, (Work.FTS.EllipticEst.AeColl.Vz u z t) ^ 2
            * Work.FTS.EllipticEst.AeColl.sigθ t))
    (hr2 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Work.FTS.EllipticEst.AeColl.Uz u z θ) ^ 2 ≤ K * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta)
        * (∫ t in Set.Ioo θ (Real.pi / 2), (Work.FTS.EllipticEst.AeColl.Vz u z t) ^ 2
            * Work.FTS.EllipticEst.AeColl.sigθ t)) :
    |∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.AeColl.sigθ θ
        * deriv (deriv (Work.FTS.EllipticEst.AeColl.psiD δ)) θ
        * (Work.FTS.EllipticEst.AeColl.Uz u z θ) ^ 2|
      ≤ Cw * K * ((∫ θ in Set.Ioo 0 δ, Work.FTS.EllipticEst.AeColl.sigθ θ
            * (Work.FTS.EllipticEst.AeColl.Vz u z θ) ^ 2)
          + (∫ θ in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
              Work.FTS.EllipticEst.AeColl.sigθ θ * (Work.FTS.EllipticEst.AeColl.Vz u z θ) ^ 2)) := by
  -- the two angular weights are the same function
  have hsig : ∀ θ : ℝ, Work.FTS.EllipticEst.AngSecond.sig θ
      = Work.FTS.EllipticEst.AeColl.sigθ θ := fun θ => rfl
  -- `deriv (Uz u z) = Vz u z` on the whole open angular interval (`hder`): transport the three
  -- `deriv f`-hypotheses of `CollarBound`
  have hint' : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun θ' => Work.FTS.EllipticEst.AeColl.Uz u z θ') θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2)) :=
    hint.congr_fun (fun θ hθ => by rw [hder θ hθ, hsig θ]) measurableSet_Ioo
  have hr1' : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ((fun θ' => Work.FTS.EllipticEst.AeColl.Uz u z θ') θ) ^ 2
        ≤ K * θ ^ (1 + Work.Spaces.eta)
        * (∫ t in Set.Ioo 0 θ, (deriv (fun θ' => Work.FTS.EllipticEst.AeColl.Uz u z θ') t) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig t) := by
    intro θ hθ
    have hcongr : (∫ t in Set.Ioo 0 θ,
          (deriv (fun θ' => Work.FTS.EllipticEst.AeColl.Uz u z θ') t) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig t)
        = ∫ t in Set.Ioo 0 θ, (Work.FTS.EllipticEst.AeColl.Vz u z t) ^ 2
            * Work.FTS.EllipticEst.AeColl.sigθ t :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun t ht => by
        rw [hder t ⟨ht.1, lt_trans ht.2 hθ.2⟩, hsig t])
    rw [hcongr]
    exact hr1 θ hθ
  have hr2' : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ((fun θ' => Work.FTS.EllipticEst.AeColl.Uz u z θ') θ) ^ 2
        ≤ K * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta)
        * (∫ t in Set.Ioo θ (Real.pi / 2),
            (deriv (fun θ' => Work.FTS.EllipticEst.AeColl.Uz u z θ') t) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig t) := by
    intro θ hθ
    have hcongr : (∫ t in Set.Ioo θ (Real.pi / 2),
          (deriv (fun θ' => Work.FTS.EllipticEst.AeColl.Uz u z θ') t) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig t)
        = ∫ t in Set.Ioo θ (Real.pi / 2), (Work.FTS.EllipticEst.AeColl.Vz u z t) ^ 2
            * Work.FTS.EllipticEst.AeColl.sigθ t :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun t ht => by
        rw [hder t ⟨lt_trans hθ.1 ht.1, ht.2⟩, hsig t])
    rw [hcongr]
    exact hr2 θ hθ
  -- apply the schema to the slice
  have h := hC K hK δ hδ hδ2 (fun θ' => Work.FTS.EllipticEst.AeColl.Uz u z θ')
    hsmooth hint' hr1' hr2'
  -- the two collar terms: the collar intervals sit inside `(0,π/2)`, so `deriv (Uz u z) = Vz u z`
  have hδlt : δ < Real.pi / 2 := by linarith [hδ2, hδ]
  have hcol1 : (∫ θ in Set.Ioo 0 δ, Work.FTS.EllipticEst.AngSecond.sig θ
        * (deriv (fun θ' => Work.FTS.EllipticEst.AeColl.Uz u z θ') θ) ^ 2)
      = ∫ θ in Set.Ioo 0 δ, Work.FTS.EllipticEst.AeColl.sigθ θ
          * (Work.FTS.EllipticEst.AeColl.Vz u z θ) ^ 2 :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => by
      rw [hder θ ⟨hθ.1, lt_trans hθ.2 hδlt⟩, hsig θ])
  have hcol2 : (∫ θ in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
        Work.FTS.EllipticEst.AngSecond.sig θ
        * (deriv (fun θ' => Work.FTS.EllipticEst.AeColl.Uz u z θ') θ) ^ 2)
      = ∫ θ in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
          Work.FTS.EllipticEst.AeColl.sigθ θ
          * (Work.FTS.EllipticEst.AeColl.Vz u z θ) ^ 2 :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => by
      rw [hder θ ⟨by linarith [hθ.1, hδlt], hθ.2⟩, hsig θ])
  rw [hcol1, hcol2] at h
  exact h

end Work.FTS.EllipticEst.Deleg.mixedTrunc
