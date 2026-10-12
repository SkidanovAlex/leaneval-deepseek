import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.ae_upd2_res_compl
import Submission.Work.BoseBoxFock.lintegral_insSplit
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Elementary facts about the two-slot fibre vocabulary of `B13Aux` -/

/-- The restriction of a full configuration to the coordinates other than `p.1`, `p.2`. -/
theorem res_projFib {n : ℕ} (p : Fin n × Fin n) (x : Fin n → E3) :
    res p (fun k : I1 p => x k.1) = resFull p x := by
  funext k
  rfl

/-- Replacing the slots `p.1`, `p.2` of a configuration is the `upd2` of its restriction. -/
theorem upd2_resFull_eq_update {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    (x : Fin n → E3) (y u : E3) :
    upd2 p y u (resFull p x) = Function.update (Function.update x p.1 y) p.2 u := by
  rw [← res_projFib p x]
  rw [← update_update_fibreIns (hp := hp) (x p.2) y u (fun k : I1 p => x k.1)]
  rw [fibreIns_restrict_eq_update p.2 x (x p.2), Function.update_eq_self p.2 x]

/-! ## Quasi-measure-preservation of the two projections used below -/

/-- The projection to the coordinates other than `p.2` is quasi-measure-preserving. -/
theorem qmp_projFib {n : ℕ} (p : Fin n × Fin n) :
    Measure.QuasiMeasurePreserving
      (fun x : Fin n → E3 => fun k : I1 p => x k.1)
      (volume : Measure (Fin n → E3)) (volume : Measure (Fib1 p)) := by
  have h : Measure.QuasiMeasurePreserving
      (fun x : Fin n → E3 => (peelE (ι := Fin n) p.2 x).2)
      (volume : Measure (Fin n → E3)) (volume : Measure (Fib1 p)) :=
    MeasureTheory.QuasiMeasurePreserving.snd
      (measurePreserving_peelE (ι := Fin n) p.2).quasiMeasurePreserving
  refine h.congr (measurable_pi_iff.mpr (fun k => measurable_pi_apply k.1)) ?_
  filter_upwards with x
  rw [peelE_apply]

/-- The map `((u,y),x) ↦ (y, (x|_≠p.2, u))` is quasi-measure-preserving. -/
theorem qmp_reshape {n : ℕ} (p : Fin n × Fin n) :
    Measure.QuasiMeasurePreserving
      (fun z : (E3 × E3) × (Fin n → E3) => (z.1.2, ((fun k : I1 p => z.2 k.1), z.1.1)))
      (volume : Measure ((E3 × E3) × (Fin n → E3)))
      (volume : Measure (E3 × (Fib1 p × E3))) := by
  have hρ₁ : Measure.QuasiMeasurePreserving
      (Prod.map id (fun x : Fin n → E3 => fun k : I1 p => x k.1))
      (volume : Measure ((E3 × E3) × (Fin n → E3)))
      (volume : Measure ((E3 × E3) × Fib1 p)) :=
    MeasureTheory.QuasiMeasurePreserving.prodMap
      (Measure.QuasiMeasurePreserving.id (volume : Measure (E3 × E3))) (qmp_projFib p)
  have hρ₂ : MeasurePreserving (fun q : (E3 × E3) × Fib1 p => (q.1.2, (q.2, q.1.1)))
      (volume : Measure ((E3 × E3) × Fib1 p)) (volume : Measure (E3 × (Fib1 p × E3))) := by
    have h₁ : MeasurePreserving (⇑(MeasurableEquiv.prodComm (α := E3 × E3) (β := Fib1 p)))
        (volume : Measure ((E3 × E3) × Fib1 p)) (volume : Measure (Fib1 p × (E3 × E3))) :=
      ⟨MeasurableEquiv.prodComm.measurable, Measure.prod_swap⟩
    have h₂ : MeasurePreserving
        (⇑(MeasurableEquiv.prodAssoc (α := Fib1 p) (β := E3) (γ := E3)).symm)
        (volume : Measure (Fib1 p × (E3 × E3))) (volume : Measure ((Fib1 p × E3) × E3)) :=
      (volume_preserving_prodAssoc (α₁ := Fib1 p) (β₁ := E3) (γ₁ := E3)).symm
        (MeasurableEquiv.prodAssoc (α := Fib1 p) (β := E3) (γ := E3))
    have h₃ : MeasurePreserving (⇑(MeasurableEquiv.prodComm (α := Fib1 p × E3) (β := E3)))
        (volume : Measure ((Fib1 p × E3) × E3)) (volume : Measure (E3 × (Fib1 p × E3))) :=
      ⟨MeasurableEquiv.prodComm.measurable, Measure.prod_swap⟩
    convert h₃.comp (h₂.comp h₁) using 1
    funext q
    rfl
  exact hρ₂.quasiMeasurePreserving.comp hρ₁

/-! ## The a.e. statement for the two-slot insertion -/

/-- **The two-slot insertion composed with `Θ` is insensitive to a.e. modifications of `Θ`.**

For a.e. `(u, y, x)` the configuration obtained from `x` by overwriting the slots `p.1`, `p.2`
with `y`, `u` lies outside a fixed null set of configurations. -/
theorem theta_update_ae_eq {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    {Θ Θ' : (Fin n → E3) → ℂ} (hΘ : Θ =ᵐ[(volume : Measure (Fin n → E3))] Θ') :
    (fun z : (E3 × E3) × (Fin n → E3) =>
        Θ (Function.update (Function.update z.2 p.1 z.1.2) p.2 z.1.1))
      =ᵐ[(volume : Measure ((E3 × E3) × (Fin n → E3)))]
      (fun z => Θ' (Function.update (Function.update z.2 p.1 z.1.2) p.2 z.1.1)) := by
  classical
  set N : Set (Fin n → E3) :=
    toMeasurable (volume : Measure (Fin n → E3)) {x | Θ x ≠ Θ' x} with hNdef
  have hN : MeasurableSet N := measurableSet_toMeasurable _ _
  have hNsub : {x : Fin n → E3 | Θ x ≠ Θ' x} ⊆ N := subset_toMeasurable _ _
  have hN0 : (volume : Measure (Fin n → E3)) N = 0 := by
    rw [hNdef, measure_toMeasurable]
    exact MeasureTheory.ae_iff.mp hΘ
  have hbase := ae_upd2_res_compl p hp hN hN0
  have hmeas : Measurable (fun q : E3 × (Fib1 p × E3) => upd2 p q.1 q.2.2 (res p q.2.1)) := by
    refine measurable_pi_iff.mpr (fun k => ?_)
    by_cases h2 : k = p.2
    · have hfun : (fun q : E3 × (Fib1 p × E3) => upd2 p q.1 q.2.2 (res p q.2.1) k) =
          fun q => q.2.2 := by
        funext q
        rw [h2]
        exact upd2_apply_p2 q.1 q.2.2 (res p q.2.1)
      rw [hfun]
      exact measurable_snd.snd
    · by_cases h1 : k = p.1
      · have hfun : (fun q : E3 × (Fib1 p × E3) => upd2 p q.1 q.2.2 (res p q.2.1) k) =
            fun q => q.1 := by
          funext q
          rw [h1]
          exact upd2_apply_p1 hp q.1 q.2.2 (res p q.2.1)
        rw [hfun]
        exact measurable_fst
      · have hfun : (fun q : E3 × (Fib1 p × E3) => upd2 p q.1 q.2.2 (res p q.2.1) k) =
            fun q => res p q.2.1 ⟨k, h2, h1⟩ := by
          funext q
          exact upd2_apply_ne h2 h1
        rw [hfun]
        exact (measurable_pi_apply (⟨k, h2, h1⟩ : I2 p)).comp
          ((measurable_res p).comp measurable_snd.fst)
  have hset : MeasurableSet {q : E3 × (Fib1 p × E3) | upd2 p q.1 q.2.2 (res p q.2.1) ∉ N} :=
    hN.compl.preimage hmeas
  have hprod : ∀ᵐ q ∂(volume : Measure (E3 × (Fib1 p × E3))),
      upd2 p q.1 q.2.2 (res p q.2.1) ∉ N :=
    (Measure.ae_prod_iff_ae_ae (p := fun q : E3 × (Fib1 p × E3) =>
        upd2 p q.1 q.2.2 (res p q.2.1) ∉ N) hset).mpr hbase
  have hpull : ∀ᵐ z ∂(volume : Measure ((E3 × E3) × (Fin n → E3))),
      upd2 p z.1.2 z.1.1 (res p (fun k : I1 p => z.2 k.1)) ∉ N :=
    (qmp_reshape p).ae hprod
  filter_upwards [hpull] with z hz
  rw [res_projFib p z.2] at hz
  rw [← upd2_resFull_eq_update p hp z.2 z.1.2 z.1.1]
  by_contra hne
  exact hz (hNsub hne)

/-! ## The target -/

theorem LHS_ae_congr {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    {Θ Θ' : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ}
    {A A' : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hΘ : Θ =ᵐ[MeasureTheory.volume] Θ') (hA : A =ᵐ[MeasureTheory.volume] A') :
    (∫ u : EuclideanSpace ℝ (Fin 3), ∫ y : EuclideanSpace ℝ (Fin 3),
        ‖∫ x : Fin n → EuclideanSpace ℝ (Fin 3),
          (starRingEnd ℂ) (Θ x) * A (x p.1) * A (x p.2)
            * Θ (Function.update (Function.update x p.1 y) p.2 u)‖ ^ 2)
      = ∫ u : EuclideanSpace ℝ (Fin 3), ∫ y : EuclideanSpace ℝ (Fin 3),
          ‖∫ x : Fin n → EuclideanSpace ℝ (Fin 3),
            (starRingEnd ℂ) (Θ' x) * A' (x p.1) * A' (x p.2)
              * Θ' (Function.update (Function.update x p.1 y) p.2 u)‖ ^ 2 := by
  classical
  set F : (E3 × E3) × (Fin n → E3) → ℂ := fun z =>
    (starRingEnd ℂ) (Θ z.2) * A (z.2 p.1) * A (z.2 p.2)
      * Θ (Function.update (Function.update z.2 p.1 z.1.2) p.2 z.1.1) with hF
  set F' : (E3 × E3) × (Fin n → E3) → ℂ := fun z =>
    (starRingEnd ℂ) (Θ' z.2) * A' (z.2 p.1) * A' (z.2 p.2)
      * Θ' (Function.update (Function.update z.2 p.1 z.1.2) p.2 z.1.1) with hF'
  have hsnd : Measure.QuasiMeasurePreserving
      (Prod.snd : (E3 × E3) × (Fin n → E3) → (Fin n → E3))
      (volume : Measure ((E3 × E3) × (Fin n → E3)))
      (volume : Measure (Fin n → E3)) :=
    Measure.quasiMeasurePreserving_snd
  have hev1 : Measure.QuasiMeasurePreserving
      (fun z : (E3 × E3) × (Fin n → E3) => z.2 p.1)
      (volume : Measure ((E3 × E3) × (Fin n → E3))) (volume : Measure E3) :=
    (Measure.quasiMeasurePreserving_eval (μ := fun _ : Fin n => (volume : Measure E3)) p.1).comp
      hsnd
  have hev2 : Measure.QuasiMeasurePreserving
      (fun z : (E3 × E3) × (Fin n → E3) => z.2 p.2)
      (volume : Measure ((E3 × E3) × (Fin n → E3))) (volume : Measure E3) :=
    (Measure.quasiMeasurePreserving_eval (μ := fun _ : Fin n => (volume : Measure E3)) p.2).comp
      hsnd
  have hθ : (fun z : (E3 × E3) × (Fin n → E3) => Θ z.2)
      =ᵐ[volume] (fun z => Θ' z.2) := hsnd.ae hΘ
  have hA1 : (fun z : (E3 × E3) × (Fin n → E3) => A (z.2 p.1))
      =ᵐ[volume] (fun z => A' (z.2 p.1)) := hev1.ae hA
  have hA2 : (fun z : (E3 × E3) × (Fin n → E3) => A (z.2 p.2))
      =ᵐ[volume] (fun z => A' (z.2 p.2)) := hev2.ae hA
  have hθΨ := theta_update_ae_eq p hp hΘ
  have hFF : F =ᵐ[volume] F' := by
    filter_upwards [hθ, hA1, hA2, hθΨ] with z e0 e1 e2 e3
    simp only [hF, hF']
    rw [e0, e1, e2, e3]
  have hpoint : ∀ᵐ q ∂(volume : Measure (E3 × E3)),
      ∀ᵐ x ∂(volume : Measure (Fin n → E3)), F (q, x) = F' (q, x) :=
    Measure.ae_ae_of_ae_prod hFF
  have hK : ∀ᵐ q ∂(volume : Measure (E3 × E3)),
      ‖∫ x, F (q, x)‖ ^ 2 = ‖∫ x, F' (q, x)‖ ^ 2 := by
    filter_upwards [hpoint] with q hq
    rw [integral_congr_ae hq]
  have hKy : ∀ᵐ u ∂(volume : Measure E3), ∀ᵐ y ∂(volume : Measure E3),
      ‖∫ x, F ((u, y), x)‖ ^ 2 = ‖∫ x, F' ((u, y), x)‖ ^ 2 :=
    Measure.ae_ae_of_ae_prod hK
  have hInt : (∫ u : E3, ∫ y : E3, ‖∫ x, F ((u, y), x)‖ ^ 2)
      = ∫ u : E3, ∫ y : E3, ‖∫ x, F' ((u, y), x)‖ ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [hKy] with u hu
    exact integral_congr_ae hu
  simp only [hF, hF'] at hInt
  exact hInt

end Work.BoseBoxFock
