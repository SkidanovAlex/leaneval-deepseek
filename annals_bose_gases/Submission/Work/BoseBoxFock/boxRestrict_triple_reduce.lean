import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.blockIIDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The triple reduction of `boxRestrictR` into the box

`Work.BoseBoxFock.boxRestrictR ℓ Ψ = Ψ · 1_{abox n ℓ}` is the (real) box restriction of a state.
This module proves the elementary measure-theoretic identity that lets one move the two box
restrictions of a *slotted* integrand onto the integration domains: for `p.1 ≠ p.2`,

    ∫ x ∫ y ∫ u, 1_abox(x)·Ψ x · q x y u · 1_abox(x[p.1↦y][p.2↦u])·Ψ(x[p.1↦y][p.2↦u])
      = ∫_{x ∈ abox} ∫_{y ∈ acube} ∫_{u ∈ acube}, Ψ x · q x y u · Ψ(x[p.1↦y][p.2↦u]) .

The point is that for `x ∈ abox` the twice-updated configuration `x[p.1↦y][p.2↦u]` lies in the box
**iff** `y ∈ acube ℓ` and `u ∈ acube ℓ` (the slots `p.1 ≠ p.2` are distinct, and all other slots are
already in the box), so the indicator `1_abox(x[p.1↦y][p.2↦u])` factors as
`1_acube(y) · 1_acube(u)` and each factor can be absorbed into the corresponding integral
(`integral_indicator`).

This is the `(S1)` triple-reduction step of the box ↔ model dictionary: it shows that the
`Q₂`-type triples computed with `boxRestrictR` are exactly the box-`Ψ` triples of the corpus.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

set_option linter.unusedVariables false

/-- `∫ (1_s)·g = ∫_s g` for a measurable set `s`. -/
theorem boxReduce_integral_indicator_one_mul {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} (hs : MeasurableSet s) (g : α → ℝ) :
    (∫ x, s.indicator (fun _ => (1 : ℝ)) x * g x ∂μ) = ∫ x in s, g x ∂μ := by
  rw [← MeasureTheory.integral_indicator (μ := μ) (f := g) hs]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ s
  · simp [Set.indicator_of_mem, hx]
  · simp [Set.indicator_of_notMem, hx]

/-- The real box restriction, written as the box indicator times the state. -/
theorem boxReduce_boxRestrictR_eq {n : ℕ} (ℓ : ℝ) (Φ : Submission.BoseGases.X n → ℝ)
    (x : Submission.BoseGases.X n) :
    boxRestrictR ℓ Φ x
      = (Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) x * Φ x := by
  rw [boxRestrictR]
  ring

/-- **The box restriction only sees the box**: `∫ boxRestrictR ℓ Φ · G = ∫_{abox} Φ · G`. -/
theorem boxReduce_boxRestrict_integral {n : ℕ} (ℓ : ℝ)
    (Φ G : Submission.BoseGases.X n → ℝ) :
    (∫ x, boxRestrictR ℓ Φ x * G x)
      = ∫ x in Submission.BoseGases.abox n ℓ, Φ x * G x := by
  rw [show (fun x => boxRestrictR ℓ Φ x * G x)
      = fun x => (Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) x * (Φ x * G x)
      from by
    funext x
    rw [boxReduce_boxRestrictR_eq]
    ring]
  exact boxReduce_integral_indicator_one_mul (Submission.BoseGases.abox_measurable n ℓ) _

/-- Membership of the twice-updated configuration: for `x` in the box and distinct slots
`p.1 ≠ p.2`, the configuration `x[p.1↦y][p.2↦u]` is in the box iff `y` and `u` are in the cube. -/
theorem boxReduce_mem_abox_update_update {n : ℕ} {ℓ : ℝ} {p : Fin n × Fin n} (hp : p.1 ≠ p.2)
    {x : Submission.BoseGases.X n} (hx : x ∈ Submission.BoseGases.abox n ℓ)
    (y u : EuclideanSpace ℝ (Fin 3)) :
    Function.update (Function.update x p.1 y) p.2 u ∈ Submission.BoseGases.abox n ℓ
      ↔ y ∈ Submission.BoseGases.acube ℓ ∧ u ∈ Submission.BoseGases.acube ℓ := by
  rw [Submission.BoseGases.mem_abox_iff]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h1 : (Function.update (Function.update x p.1 y) p.2 u) p.1 = y := by
        simp [hp]
      rw [← h1]
      exact h p.1
    · have h2 : (Function.update (Function.update x p.1 y) p.2 u) p.2 = u := by
        simp
      rw [← h2]
      exact h p.2
  · rintro ⟨hy, hu⟩ k
    rw [Function.update_apply]
    by_cases hk : k = p.2
    · rw [if_pos hk]; exact hu
    · rw [if_neg hk, Function.update_apply]
      by_cases hk' : k = p.1
      · rw [if_pos hk']; exact hy
      · rw [if_neg hk']
        exact (Submission.BoseGases.mem_abox_iff n ℓ x).mp hx k

theorem boxRestrict_triple_reduce {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Ψ : Submission.BoseGases.X n → ℝ}
    {q : Submission.BoseGases.X n → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    {p : Fin n × Fin n} (hp : p.1 ≠ p.2) :
    (∫ x : Submission.BoseGases.X n, ∫ y : EuclideanSpace ℝ (Fin 3),
        ∫ u : EuclideanSpace ℝ (Fin 3),
          Work.BoseBoxFock.boxRestrictR ℓ Ψ x * q x y u
            * Work.BoseBoxFock.boxRestrictR ℓ Ψ (Function.update (Function.update x p.1 y) p.2 u))
      = ∫ x in Submission.BoseGases.abox n ℓ, ∫ y in Submission.BoseGases.acube ℓ,
          ∫ u in Submission.BoseGases.acube ℓ, Ψ x * q x y u
            * Ψ (Function.update (Function.update x p.1 y) p.2 u) := by
  -- Step 1: the two `boxRestrictR` factors of the inner integrand do not depend on `u` (resp. `y`),
  -- so they pull out of the inner integrals.
  have hstep1 : (fun x : Submission.BoseGases.X n => ∫ y : EuclideanSpace ℝ (Fin 3),
        ∫ u : EuclideanSpace ℝ (Fin 3),
          boxRestrictR ℓ Ψ x * q x y u
            * boxRestrictR ℓ Ψ (Function.update (Function.update x p.1 y) p.2 u))
      = fun x => boxRestrictR ℓ Ψ x
        * (∫ y, ∫ u, q x y u
            * boxRestrictR ℓ Ψ (Function.update (Function.update x p.1 y) p.2 u)) := by
    funext x
    have hy : (fun y : EuclideanSpace ℝ (Fin 3) => ∫ u : EuclideanSpace ℝ (Fin 3),
          boxRestrictR ℓ Ψ x * q x y u
            * boxRestrictR ℓ Ψ (Function.update (Function.update x p.1 y) p.2 u))
        = fun y => boxRestrictR ℓ Ψ x
          * (∫ u, q x y u
              * boxRestrictR ℓ Ψ (Function.update (Function.update x p.1 y) p.2 u)) := by
      funext y
      have hu : (fun u : EuclideanSpace ℝ (Fin 3) =>
            boxRestrictR ℓ Ψ x * q x y u
              * boxRestrictR ℓ Ψ (Function.update (Function.update x p.1 y) p.2 u))
          = fun u => boxRestrictR ℓ Ψ x
            * (q x y u
              * boxRestrictR ℓ Ψ (Function.update (Function.update x p.1 y) p.2 u)) := by
        funext u
        ring
      rw [hu, MeasureTheory.integral_const_mul]
    rw [hy, MeasureTheory.integral_const_mul]
  rw [hstep1]
  -- Step 2: the outer box restriction, i.e. restrict `x` to the box.
  rw [boxReduce_boxRestrict_integral]
  refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable n ℓ) ?_
  intro x hx
  try simp only []
  -- Step 3: pointwise on the box the update-indicator factors into the two cube indicators.
  have hfac : ∀ y u : EuclideanSpace ℝ (Fin 3),
      boxRestrictR ℓ Ψ (Function.update (Function.update x p.1 y) p.2 u)
        = (Submission.BoseGases.acube ℓ).indicator (fun _ => (1 : ℝ)) y
          * ((Submission.BoseGases.acube ℓ).indicator (fun _ => (1 : ℝ)) u
              * Ψ (Function.update (Function.update x p.1 y) p.2 u)) := by
    intro y u
    rw [boxRestrictR]
    by_cases hy : y ∈ Submission.BoseGases.acube ℓ
    · by_cases hu : u ∈ Submission.BoseGases.acube ℓ
      · rw [Set.indicator_of_mem ((boxReduce_mem_abox_update_update hp hx y u).mpr ⟨hy, hu⟩),
            Set.indicator_of_mem hy, Set.indicator_of_mem hu]
        ring
      · rw [Set.indicator_of_notMem
              (fun h => hu ((boxReduce_mem_abox_update_update hp hx y u).mp h).2),
            Set.indicator_of_notMem hu]
        ring
    · rw [Set.indicator_of_notMem
            (fun h => hy ((boxReduce_mem_abox_update_update hp hx y u).mp h).1),
          Set.indicator_of_notMem hy]
      ring
  -- The two slot integrations reduce to the cube integrations.
  have hinner : (∫ y, ∫ u, q x y u
        * boxRestrictR ℓ Ψ (Function.update (Function.update x p.1 y) p.2 u))
      = ∫ y in Submission.BoseGases.acube ℓ, ∫ u in Submission.BoseGases.acube ℓ,
          q x y u * Ψ (Function.update (Function.update x p.1 y) p.2 u) := by
    have h1 : (fun y : EuclideanSpace ℝ (Fin 3) => ∫ u,
          q x y u * boxRestrictR ℓ Ψ (Function.update (Function.update x p.1 y) p.2 u))
        = fun y => (Submission.BoseGases.acube ℓ).indicator (fun _ => (1 : ℝ)) y
          * (∫ u, q x y u
              * ((Submission.BoseGases.acube ℓ).indicator (fun _ => (1 : ℝ)) u
                  * Ψ (Function.update (Function.update x p.1 y) p.2 u))) := by
      funext y
      have h2 : (fun u : EuclideanSpace ℝ (Fin 3) =>
            q x y u * boxRestrictR ℓ Ψ (Function.update (Function.update x p.1 y) p.2 u))
          = fun u => (Submission.BoseGases.acube ℓ).indicator (fun _ => (1 : ℝ)) y
            * (q x y u
              * ((Submission.BoseGases.acube ℓ).indicator (fun _ => (1 : ℝ)) u
                  * Ψ (Function.update (Function.update x p.1 y) p.2 u))) := by
        funext u
        rw [hfac y u]
        ring
      rw [h2, MeasureTheory.integral_const_mul]
    rw [h1]
    try simp only []
    rw [boxReduce_integral_indicator_one_mul (Submission.BoseGases.acube_measurable ℓ)]
    try simp only []
    refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ) ?_
    intro y hy
    try simp only []
    have h3 : (fun u : EuclideanSpace ℝ (Fin 3) =>
          q x y u * ((Submission.BoseGases.acube ℓ).indicator (fun _ => (1 : ℝ)) u
              * Ψ (Function.update (Function.update x p.1 y) p.2 u)))
        = fun u => (Submission.BoseGases.acube ℓ).indicator (fun _ => (1 : ℝ)) u
            * (q x y u * Ψ (Function.update (Function.update x p.1 y) p.2 u)) := by
      funext u
      ring
    rw [h3, boxReduce_integral_indicator_one_mul (Submission.BoseGases.acube_measurable ℓ)]
  -- The exterior factor `Ψ x` is a constant of the two slot integrations.
  have hpsi : (∫ y in Submission.BoseGases.acube ℓ,
        ∫ u in Submission.BoseGases.acube ℓ,
          Ψ x * q x y u * Ψ (Function.update (Function.update x p.1 y) p.2 u))
      = Ψ x * (∫ y in Submission.BoseGases.acube ℓ,
          ∫ u in Submission.BoseGases.acube ℓ,
            q x y u * Ψ (Function.update (Function.update x p.1 y) p.2 u)) := by
    have h4 : (fun y : EuclideanSpace ℝ (Fin 3) =>
          ∫ u in Submission.BoseGases.acube ℓ,
            Ψ x * q x y u * Ψ (Function.update (Function.update x p.1 y) p.2 u))
        = fun y => Ψ x * (∫ u in Submission.BoseGases.acube ℓ,
            q x y u * Ψ (Function.update (Function.update x p.1 y) p.2 u)) := by
      funext y
      have h5 : (fun u : EuclideanSpace ℝ (Fin 3) =>
            Ψ x * q x y u * Ψ (Function.update (Function.update x p.1 y) p.2 u))
          = fun u => Ψ x * (q x y u * Ψ (Function.update (Function.update x p.1 y) p.2 u))
          := by
        funext u
        ring
      rw [h5, MeasureTheory.integral_const_mul]
    rw [h4, MeasureTheory.integral_const_mul]
  rw [hinner]
  exact hpsi.symm

end Work.BoseBoxFock
