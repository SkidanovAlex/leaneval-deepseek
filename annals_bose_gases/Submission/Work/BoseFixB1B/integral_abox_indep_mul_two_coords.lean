import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1B.integral_abox_indep_mul_coord
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.integral_abox_indep_mul_two_coords`

Peeling **two** coordinates out of a box integral of a function which factorises as
`g x · h (x i) (x j)`, where `g` does not depend on the coordinates `i ≠ j`:

    ∫_{abox n ℓ} g x · h (x i) (x j)
      = ((∫_{abox n ℓ} g) / ℓ⁶) · (∫_{acube ℓ × acube ℓ} h) .

This is the two-slot counterpart of `Work.BoseFixB1B.integral_abox_indep_mul_coord`
(which peels a single slot and contributes `ℓ³`); the extra slot contributes a second
factor `ℓ³`, hence `ℓ⁶`.

The measure-theoretic heart is the generic two-slot product-measure peel
`peel_two_slots_pi`: for a finite measure `ν` on `β` and distinct slots `i ≠ j : Fin (k+2)`,

    ∫ x, ∫ z, ∫ w, G (update (update x i z) j w) ∂ν ∂ν ∂(π ν)
      = (ν univ).toReal² · ∫ y, G y ∂(π ν) .

It is obtained by applying the already proved one-slot peel `peel_slot_pi` twice: the
intermediate function `x ↦ ∫ z, G (update x j z)` is integrable by the companion lemma
`peel_slot_integrable` (a byproduct of the same measure-preserving-equivalence argument
as `peel_slot_pi`), and each application contributes the total mass `(ν univ).toReal`.

Specialising `ν = volume ↾ acube ℓ` (so `(ν univ).toReal = ℓ³`, `acube_volume`) and using
`restrict_abox_eq_pi` to identify `volume ↾ abox n ℓ` with the product `Measure.pi (fun _ => ν)`
gives the identity; the pointwise evaluation of the double update
`(update (update x i z) j w) i = z`, `(update (update x i z) j w) j = w` together with the
independence `hindep` of `g` reduces the inner double integral to `g x · ∫_{acube×acube} h`,
and `setIntegral_prod` converts `∫_{acube×acube} h` into the iterated form.
-/

open MeasureTheory

namespace Work.BoseFixB1B

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Integrability of a peeled slot.**

For a finite σ-finite measure `ν` on `β`, a slot `j : Fin (k+1)` and an integrable
`G : (Fin (k+1) → β) → ℝ`, the function `x ↦ ∫ z, G (update x j z) ∂ν` is integrable with
respect to the product measure `Measure.pi (fun _ => ν)`.

This is the integrability half of `peel_slot_pi`: the peeled function is the pullback (along
the measure-preserving equivalence `piFinSuccAbove j`) of the partial integral
`w ↦ ∫ z, G (e.symm (z, w))`, which is integrable by Fubini (`Integrable.integral_prod_right`). -/
theorem peel_slot_integrable {β : Type*} [MeasurableSpace β] (ν : Measure β)
    [SigmaFinite ν] [IsFiniteMeasure ν] {k : ℕ} (j : Fin (k + 1))
    {G : (Fin (k + 1) → β) → ℝ}
    (hG : Integrable G (Measure.pi (fun _ : Fin (k + 1) => ν))) :
    Integrable (fun x => ∫ z, G (Function.update x j z) ∂ν)
      (Measure.pi (fun _ : Fin (k + 1) => ν)) := by
  classical
  have hmp : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => β) j)
      (Measure.pi (fun _ : Fin (k + 1) => ν)) (ν.prod (Measure.pi (fun _ : Fin k => ν))) :=
    measurePreserving_piFinSuccAbove (α := fun _ : Fin (k + 1) => β)
      (μ := fun _ : Fin (k + 1) => ν) j
  have hmp' : MeasurePreserving ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => β) j).symm)
      (ν.prod (Measure.pi (fun _ : Fin k => ν))) (Measure.pi (fun _ : Fin (k + 1) => ν)) :=
    MeasurePreserving.symm _ hmp
  have hemb : MeasurableEmbedding
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => β) j).symm) :=
    MeasurableEquiv.measurableEmbedding _
  have hE : ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => β) j).symm
      : β × (Fin k → β) → (Fin (k + 1) → β))
      = fun f => Fin.insertNth j f.1 f.2 := by
    funext f mm
    simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply]
  have hpoint : ∀ (p : β × (Fin k → β)) (z : β),
      Function.update ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => β) j).symm p) j z
        = (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => β) j).symm (z, p.2) := by
    rintro ⟨a, y⟩ z
    rw [hE]
    exact Fin.update_insertNth (α := fun _ : Fin (k + 1) => β) j a z y
  have hK : Integrable (fun p : β × (Fin k → β) =>
      G ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => β) j).symm p))
      (ν.prod (Measure.pi (fun _ : Fin k => ν))) :=
    (hmp'.integrable_comp_emb hemb (g := G)).mpr hG
  have hKw : Integrable (fun w : Fin k → β =>
      ∫ z, G ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => β) j).symm (z, w)) ∂ν)
      (Measure.pi (fun _ : Fin k => ν)) := hK.integral_prod_right
  have hT : Integrable (fun p : β × (Fin k → β) =>
      ∫ z, G ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => β) j).symm (z, p.2)) ∂ν)
      (ν.prod (Measure.pi (fun _ : Fin k => ν))) := hKw.comp_snd ν
  have hT2 : Integrable (fun p : β × (Fin k → β) =>
      ∫ z, G (Function.update
        ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => β) j).symm p) j z) ∂ν)
      (ν.prod (Measure.pi (fun _ : Fin k => ν))) := by
    refine hT.congr (Filter.Eventually.of_forall (fun p => ?_))
    exact integral_congr_ae (Filter.Eventually.of_forall (fun z => congrArg G (hpoint p z).symm))
  exact (hmp'.integrable_comp_emb hemb
    (g := fun x => ∫ z, G (Function.update x j z) ∂ν)).mp hT2

/-- **Peel two slots out of a product measure.**

For a finite σ-finite measure `ν` on `β`, distinct slots `i ≠ j : Fin (k+2)` and an integrable
`G : (Fin (k+2) → β) → ℝ`,

    ∫ x, ∫ z, ∫ w, G (update (update x i z) j w) ∂ν ∂ν ∂(π ν)
      = (ν univ).toReal² · ∫ y, G y ∂(π ν) .

Proof: the one-slot peel `peel_slot_pi` for the slot `j` gives
`∫ x, B x = (ν univ).toReal · ∫ G` for `B x = ∫ z, G (update x j z)`; applying
`peel_slot_pi` once more — with the slot `i`, legitimate by `peel_slot_integrable` — to `B`
gives `∫ x, ∫ z, B (update x i z) = (ν univ).toReal · ∫ x, B x`, and
`B (update x i z) = ∫ w, G (update (update x i z) j w)`. -/
theorem peel_two_slots_pi {β : Type*} [MeasurableSpace β] (ν : Measure β)
    [SigmaFinite ν] [IsFiniteMeasure ν] {k : ℕ} {i j : Fin (k + 2)} (_hij : i ≠ j)
    {G : (Fin (k + 2) → β) → ℝ}
    (hG : Integrable G (Measure.pi (fun _ : Fin (k + 2) => ν))) :
    (∫ x, (∫ z, (∫ w, G (Function.update (Function.update x i z) j w) ∂ν) ∂ν)
        ∂(Measure.pi (fun _ : Fin (k + 2) => ν)))
      = (ν Set.univ).toReal ^ 2 * ∫ y, G y ∂(Measure.pi (fun _ : Fin (k + 2) => ν)) := by
  have hBint : Integrable (fun x : Fin (k + 2) → β => ∫ z, G (Function.update x j z) ∂ν)
      (Measure.pi (fun _ : Fin (k + 2) => ν)) := peel_slot_integrable ν j hG
  have h1 := peel_slot_pi ν i
    (G := fun x : Fin (k + 2) → β => ∫ z, G (Function.update x j z) ∂ν) hBint
  have h2 := peel_slot_pi ν j (G := G) hG
  simp only [] at h1
  rw [h2] at h1
  rw [← mul_assoc, ← pow_two] at h1
  exact h1

/-- **Two-coordinate peel of the centred box.**

The box integral over `abox n ℓ` of `g x · h (x i) (x j)`, where `g` does not depend on the
(distinct) coordinates `i` and `j`, factorises as `(∫_{abox} g) / ℓ⁶` times the double integral
of `h` over `acube ℓ × acube ℓ`. -/
theorem integral_abox_indep_mul_two_coords {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin n}
    (hij : i ≠ j) {g : Submission.BoseGases.X n → ℝ} {h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hindep : ∀ (x : Submission.BoseGases.X n) (a b : EuclideanSpace ℝ (Fin 3)),
      g (Function.update (Function.update x i a) j b) = g x)
    (hInt : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => g x * h (x i) (x j))
      (Submission.BoseGases.abox n ℓ))
    (hIntg : MeasureTheory.IntegrableOn g (Submission.BoseGases.abox n ℓ))
    (hInth : MeasureTheory.IntegrableOn
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => h p.1 p.2)
      (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ)) :
    ∫ x in Submission.BoseGases.abox n ℓ, g x * h (x i) (x j)
      = ((∫ x in Submission.BoseGases.abox n ℓ, g x) / ℓ ^ 6)
          * (∫ p in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ,
              h p.1 p.2) := by
  classical
  rcases n with _ | _ | m
  · exact i.elim0
  · have h01 : i = j := Fin.ext (by
      rw [show i.val = 0 from Nat.lt_one_iff.mp i.isLt,
          show j.val = 0 from Nat.lt_one_iff.mp j.isLt])
    exact (hij h01).elim
  · haveI hfin : IsFiniteMeasure ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) :=
      ⟨by rw [Measure.restrict_apply_univ, Submission.BoseGases.acube_volume ℓ hℓ.le]
          exact ENNReal.ofReal_lt_top⟩
    have hvol :
        (((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) Set.univ).toReal = ℓ ^ 3 := by
      rw [Measure.restrict_apply_univ, Submission.BoseGases.acube_volume ℓ hℓ.le,
        ENNReal.toReal_ofReal (by positivity)]
    set G : Submission.BoseGases.X (m + 2) → ℝ := fun x => g x * h (x i) (x j) with hGdef
    have hGint : Integrable G (Measure.pi
        (fun _ : Fin (m + 2) => (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))) := by
      rw [← Submission.BoseGases.restrict_abox_eq_pi (m + 2) ℓ]
      exact hInt
    have hpeel := peel_two_slots_pi
      (ν := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))
      (k := m) (i := i) (j := j) hij (G := G) hGint
    have hpeel' : (∫ x in Submission.BoseGases.abox (m + 2) ℓ, ∫ z in Submission.BoseGases.acube ℓ,
          ∫ w in Submission.BoseGases.acube ℓ, G (Function.update (Function.update x i z) j w))
        = ℓ ^ 6 * ∫ x in Submission.BoseGases.abox (m + 2) ℓ, G x := by
      have hh := hpeel
      rw [← Submission.BoseGases.restrict_abox_eq_pi (m + 2) ℓ] at hh
      have hpow : (((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) Set.univ).toReal ^ 2
          = ℓ ^ 6 := by
        rw [hvol]; ring
      rw [hpow] at hh
      exact hh
    have hpt : ∀ (x : Submission.BoseGases.X (m + 2)) (z w : E3),
        G (Function.update (Function.update x i z) j w) = g x * h z w := by
      intro x z w
      have h1 : (Function.update (Function.update x i z) j w) i = z := by
        rw [Function.update_apply, if_neg hij, Function.update_apply, if_pos rfl]
      have h2 : (Function.update (Function.update x i z) j w) j = w := by
        rw [Function.update_apply, if_pos rfl]
      rw [hGdef]
      simp only []
      rw [hindep x z w, h1, h2]
    have hc : (∫ z in Submission.BoseGases.acube ℓ, ∫ w in Submission.BoseGases.acube ℓ, h z w)
        = ∫ p in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ, h p.1 p.2 := by
      rw [← MeasureTheory.setIntegral_prod (fun p : E3 × E3 => h p.1 p.2) hInth]
      rw [MeasureTheory.Measure.volume_eq_prod E3 E3]
    have hinner : ∀ x : Submission.BoseGases.X (m + 2),
        (∫ z in Submission.BoseGases.acube ℓ, ∫ w in Submission.BoseGases.acube ℓ,
            G (Function.update (Function.update x i z) j w))
          = g x * (∫ p in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ, h p.1 p.2) := by
      intro x
      have step1 : (∫ z in Submission.BoseGases.acube ℓ, ∫ w in Submission.BoseGases.acube ℓ,
            G (Function.update (Function.update x i z) j w))
          = ∫ z in Submission.BoseGases.acube ℓ, ∫ w in Submission.BoseGases.acube ℓ, g x * h z w :=
        integral_congr_ae (Filter.Eventually.of_forall (fun z =>
          integral_congr_ae (Filter.Eventually.of_forall (fun w => hpt x z w))))
      have h2 : (∫ z in Submission.BoseGases.acube ℓ, ∫ w in Submission.BoseGases.acube ℓ, g x * h z w)
          = ∫ z in Submission.BoseGases.acube ℓ,
              g x * (∫ w in Submission.BoseGases.acube ℓ, h z w) :=
        integral_congr_ae
          (Filter.Eventually.of_forall (fun z => integral_const_mul (g x) (fun w => h z w)))
      rw [step1, h2, integral_const_mul, hc]
    have hLHS : (∫ x in Submission.BoseGases.abox (m + 2) ℓ, ∫ z in Submission.BoseGases.acube ℓ,
          ∫ w in Submission.BoseGases.acube ℓ, G (Function.update (Function.update x i z) j w))
        = (∫ x in Submission.BoseGases.abox (m + 2) ℓ, g x)
            * (∫ p in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ, h p.1 p.2) := by
      have h1 : (fun x : Submission.BoseGases.X (m + 2) => ∫ z in Submission.BoseGases.acube ℓ,
            ∫ w in Submission.BoseGases.acube ℓ, G (Function.update (Function.update x i z) j w))
          = fun x => g x
              * (∫ p in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ, h p.1 p.2) :=
        funext hinner
      rw [h1]
      exact integral_mul_const _ g
    have key : ℓ ^ 6 * (∫ x in Submission.BoseGases.abox (m + 2) ℓ, G x)
        = (∫ x in Submission.BoseGases.abox (m + 2) ℓ, g x)
            * (∫ p in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ, h p.1 p.2) := by
      rw [← hpeel']
      exact hLHS
    have hℓ6 : (ℓ : ℝ) ^ 6 ≠ 0 := pow_ne_zero 6 (ne_of_gt hℓ)
    calc ∫ x in Submission.BoseGases.abox (m + 2) ℓ, g x * h (x i) (x j)
        = ∫ x in Submission.BoseGases.abox (m + 2) ℓ, G x := by rw [hGdef]
      _ = (ℓ ^ 6 * (∫ x in Submission.BoseGases.abox (m + 2) ℓ, G x)) / ℓ ^ 6 :=
            (mul_div_cancel_left₀ _ hℓ6).symm
      _ = (((∫ x in Submission.BoseGases.abox (m + 2) ℓ, g x)
            * (∫ p in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ, h p.1 p.2))) / ℓ ^ 6 := by
            rw [key]
      _ = ((∫ x in Submission.BoseGases.abox (m + 2) ℓ, g x) / ℓ ^ 6)
            * (∫ p in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ, h p.1 p.2) := by
            rw [← div_mul_eq_mul_div]

end Work.BoseFixB1B
