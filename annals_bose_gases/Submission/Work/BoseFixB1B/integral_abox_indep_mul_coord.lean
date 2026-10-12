import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB2.Pot.lintegral_coord_abox
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.integral_abox_indep_mul_coord`

Peeling the coordinate `i` out of a box integral of a function which factorises as
`g x · h (x i)`, where `g` does not depend on the coordinate `i`.

The measure-theoretic heart is the general "peel one slot out of a product measure"
identity `peel_slot_pi`: for a finite measure `ν` on `β` and a slot `j : Fin (k+1)`,

    ∫ x, (∫ z, G (Function.update x j z) ∂ν) ∂(Measure.pi (fun _ => ν))
      = (ν univ).toReal * ∫ y, G y ∂(Measure.pi (fun _ => ν)) ,

obtained from the measure-preserving split `MeasurableEquiv.piFinSuccAbove j`
(`measurePreserving_piFinSuccAbove`) together with two applications of Fubini
(`integral_prod_symm`); the slot-`j` coordinate integrates out to the total mass `ν univ`.

Specialising `ν = volume ↾ acube ℓ` (so `(ν univ).toReal = ℓ³`, `acube_volume`) and using the
product structure `volume ↾ abox (m+1) ℓ = Measure.pi (fun _ => volume ↾ acube ℓ)`
(`restrict_abox_eq_pi`) gives the target: with `G y = g y * h (y i)` the independence
`hindep` evaluates the inner integral to `g x * ∫_{acube ℓ} h`, and pulling this constant out
of the outer integral (`integral_mul_const`) identifies the left side as
`(∫_{abox} g) * (∫_{acube} h) = ℓ³ * ∫_{abox} g x * h (x i)`, which is the claim.
-/

open MeasureTheory
open scoped ENNReal

namespace Work.BoseFixB1B

/-- **Peel one slot out of a product measure.**

For a finite σ-finite measure `ν` on `β`, a slot `j : Fin (k+1)` and an integrable
`G : (Fin (k+1) → β) → ℝ`,

    ∫ x, (∫ z, G (update x j z) ∂ν) ∂(Measure.pi (fun _ => ν))
      = (ν univ).toReal * ∫ y, G y ∂(Measure.pi (fun _ => ν)) .

The coordinate `j` of `x` does not occur in `G (update x j z)`, so it integrates to the total
mass of `ν`; the remaining integral is the full product integral. -/
theorem peel_slot_pi {β : Type*} [MeasurableSpace β] (ν : Measure β)
    [SigmaFinite ν] [IsFiniteMeasure ν] {k : ℕ} (j : Fin (k + 1))
    {G : (Fin (k + 1) → β) → ℝ}
    (hG : Integrable G (Measure.pi (fun _ : Fin (k + 1) => ν))) :
    (∫ x, (∫ z, G (Function.update x j z) ∂ν) ∂(Measure.pi (fun _ : Fin (k + 1) => ν)))
      = (ν Set.univ).toReal * ∫ y, G y ∂(Measure.pi (fun _ : Fin (k + 1) => ν)) := by
  classical
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => β) j
  have he : e = MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => β) j := rfl
  have hmp : MeasurePreserving e (Measure.pi (fun _ : Fin (k + 1) => ν))
      (ν.prod (Measure.pi (fun _ : Fin k => ν))) :=
    measurePreserving_piFinSuccAbove (α := fun _ : Fin (k + 1) => β)
      (μ := fun _ : Fin (k + 1) => ν) j
  have hmp' : MeasurePreserving (e.symm) (ν.prod (Measure.pi (fun _ : Fin k => ν)))
      (Measure.pi (fun _ : Fin (k + 1) => ν)) := MeasurePreserving.symm e hmp
  have hemb : MeasurableEmbedding (e.symm) := MeasurableEquiv.measurableEmbedding e.symm
  have hK : Integrable (fun p : β × (Fin k → β) => G (e.symm p))
      (ν.prod (Measure.pi (fun _ : Fin k => ν))) :=
    (hmp'.integrable_comp_emb hemb (g := G)).mpr hG
  have hE : ((e.symm : β × (Fin k → β) → (Fin (k + 1) → β)))
      = fun f => Fin.insertNth j f.1 f.2 := by
    rw [he]
    funext f mm
    simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply]
  have hpoint : ∀ (p : β × (Fin k → β)) (z : β),
      Function.update (e.symm p) j z = e.symm (z, p.2) := by
    rintro ⟨a, y⟩ z
    rw [hE]
    exact Fin.update_insertNth (α := fun _ : Fin (k + 1) => β) j a z y
  have h1 : (∫ x, (∫ z, G (Function.update x j z) ∂ν)
        ∂(Measure.pi (fun _ : Fin (k + 1) => ν)))
      = ∫ p : β × (Fin k → β), (∫ z, G (e.symm (z, p.2)) ∂ν)
        ∂(ν.prod (Measure.pi (fun _ : Fin k => ν))) := by
    have h := hmp'.integral_comp hemb (fun x => ∫ z, G (Function.update x j z) ∂ν)
    rw [← h]
    simp only [hpoint]
  have hKw : Integrable (fun w : Fin k → β => ∫ z, G (e.symm (z, w)) ∂ν)
      (Measure.pi (fun _ : Fin k => ν)) := hK.integral_prod_right
  have hT : Integrable (fun p : β × (Fin k → β) => ∫ z, G (e.symm (z, p.2)) ∂ν)
      (ν.prod (Measure.pi (fun _ : Fin k => ν))) := by
    simpa using hKw.comp_snd ν
  have h2 : (∫ p : β × (Fin k → β), (∫ z, G (e.symm (z, p.2)) ∂ν)
        ∂(ν.prod (Measure.pi (fun _ : Fin k => ν))))
      = (ν Set.univ).toReal * ∫ p : β × (Fin k → β), G (e.symm p)
        ∂(ν.prod (Measure.pi (fun _ : Fin k => ν))) := by
    rw [integral_prod_symm _ hT]
    have hc : ∀ w : Fin k → β, (∫ _a : β, (∫ z, G (e.symm (z, w)) ∂ν) ∂ν)
        = (ν Set.univ).toReal * (∫ z, G (e.symm (z, w)) ∂ν) := by
      intro w
      rw [integral_const, Measure.real_def]
      rfl
    simp only [hc]
    rw [integral_const_mul, ← integral_prod_symm _ hK]
  calc
    (∫ x, (∫ z, G (Function.update x j z) ∂ν) ∂(Measure.pi (fun _ : Fin (k + 1) => ν)))
        = ∫ p : β × (Fin k → β), (∫ z, G (e.symm (z, p.2)) ∂ν)
            ∂(ν.prod (Measure.pi (fun _ : Fin k => ν))) := h1
    _ = (ν Set.univ).toReal * ∫ p : β × (Fin k → β), G (e.symm p)
            ∂(ν.prod (Measure.pi (fun _ : Fin k => ν))) := h2
    _ = (ν Set.univ).toReal * ∫ y, G y ∂(Measure.pi (fun _ : Fin (k + 1) => ν)) := by
        rw [hmp'.integral_comp hemb G]

theorem integral_abox_indep_mul_coord {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n)
    {g : Submission.BoseGases.X n → ℝ} {h : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hindep : ∀ (x : Submission.BoseGases.X n) (a : EuclideanSpace ℝ (Fin 3)),
      g (Function.update x i a) = g x)
    (hInt : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n => g x * h (x i)) (Submission.BoseGases.abox n ℓ))
    (hIntg : MeasureTheory.IntegrableOn g (Submission.BoseGases.abox n ℓ))
    (hInth : MeasureTheory.IntegrableOn h (Submission.BoseGases.acube ℓ)) :
    ∫ x in Submission.BoseGases.abox n ℓ, g x * h (x i)
      = ((∫ x in Submission.BoseGases.abox n ℓ, g x) / ℓ ^ 3)
          * (∫ a in Submission.BoseGases.acube ℓ, h a) := by
  rcases n with _ | m
  · exact (i.elim0 : False).elim
  · have hfin : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
        (Submission.BoseGases.acube ℓ)) :=
      ⟨by
        rw [Measure.restrict_apply_univ, Submission.BoseGases.acube_volume ℓ hℓ.le]
        exact ENNReal.ofReal_lt_top⟩
    haveI := hfin
    have hG : Integrable (fun y : Submission.BoseGases.X (m + 1) => g y * h (y i))
        (Measure.pi (fun _ : Fin (m + 1) =>
          (volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
            (Submission.BoseGases.acube ℓ))) := by
      rw [← Submission.BoseGases.restrict_abox_eq_pi (m + 1) ℓ]
      exact hInt
    have hpeel := peel_slot_pi
      (β := EuclideanSpace ℝ (Fin 3))
      (ν := (volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
        (Submission.BoseGases.acube ℓ))
      (k := m) (j := i)
      (G := fun y : Submission.BoseGases.X (m + 1) => g y * h (y i)) (hG := hG)
    have hpeel' : (∫ x in Submission.BoseGases.abox (m + 1) ℓ,
          ∫ z in Submission.BoseGases.acube ℓ,
            g (Function.update x i z) * h ((Function.update x i z) i))
        = ℓ ^ 3 * ∫ y in Submission.BoseGases.abox (m + 1) ℓ, g y * h (y i) := by
      have hvol : (((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Submission.BoseGases.acube ℓ)) Set.univ).toReal = ℓ ^ 3 := by
        rw [Measure.restrict_apply_univ, Submission.BoseGases.acube_volume ℓ hℓ.le,
          ENNReal.toReal_ofReal (by positivity)]
      rw [Submission.BoseGases.restrict_abox_eq_pi (m + 1) ℓ]
      simpa only [hvol] using hpeel
    have hinner : ∀ x : Submission.BoseGases.X (m + 1),
        (∫ z in Submission.BoseGases.acube ℓ,
            g (Function.update x i z) * h ((Function.update x i z) i))
          = g x * (∫ z in Submission.BoseGases.acube ℓ, h z) := by
      intro x
      have hpt : ∀ z : EuclideanSpace ℝ (Fin 3),
          g (Function.update x i z) * h ((Function.update x i z) i) = g x * h z := by
        intro z
        rw [hindep x z, Function.update_self i z x]
      simp only [hpt]
      exact integral_const_mul (g x) h
    have hLHS : (∫ x in Submission.BoseGases.abox (m + 1) ℓ,
          ∫ z in Submission.BoseGases.acube ℓ,
            g (Function.update x i z) * h ((Function.update x i z) i))
        = (∫ x in Submission.BoseGases.abox (m + 1) ℓ, g x)
            * (∫ z in Submission.BoseGases.acube ℓ, h z) := by
      have h1 : (fun x : Submission.BoseGases.X (m + 1) =>
            ∫ z in Submission.BoseGases.acube ℓ,
              g (Function.update x i z) * h ((Function.update x i z) i))
          = fun x => g x * (∫ z in Submission.BoseGases.acube ℓ, h z) :=
        funext hinner
      rw [h1]
      exact integral_mul_const _ g
    have key : ℓ ^ 3 * (∫ y in Submission.BoseGases.abox (m + 1) ℓ, g y * h (y i))
        = (∫ y in Submission.BoseGases.abox (m + 1) ℓ, g y)
            * (∫ z in Submission.BoseGases.acube ℓ, h z) := by
      rw [← hpeel']
      exact hLHS
    have hℓ3 : (ℓ : ℝ) ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hℓ)
    calc (∫ x in Submission.BoseGases.abox (m + 1) ℓ, g x * h (x i))
        = (ℓ ^ 3 * (∫ x in Submission.BoseGases.abox (m + 1) ℓ, g x * h (x i))) / ℓ ^ 3 :=
          (mul_div_cancel_left₀ _ hℓ3).symm
      _ = ((∫ x in Submission.BoseGases.abox (m + 1) ℓ, g x)
              * (∫ z in Submission.BoseGases.acube ℓ, h z)) / ℓ ^ 3 := by rw [key]
      _ = ((∫ x in Submission.BoseGases.abox (m + 1) ℓ, g x) / ℓ ^ 3)
              * (∫ z in Submission.BoseGases.acube ℓ, h z) := by
          rw [← div_mul_eq_mul_div]

end Work.BoseFixB1B
