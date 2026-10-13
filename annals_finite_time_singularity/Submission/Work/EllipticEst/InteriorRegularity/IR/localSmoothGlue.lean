import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.InteriorRegularity.IR

open MeasureTheory Metric Set

/-- Restricting an almost-everywhere equality (with respect to a restricted measure) to a
smaller set. -/
private lemma ae_eq_restrict_of_subset {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s t : Set α} (hst : s ⊆ t) {β : Type*} {f g : α → β}
    (h : f =ᵐ[μ.restrict t] g) : f =ᵐ[μ.restrict s] g := by
  rw [Filter.EventuallyEq] at h ⊢
  exact ae_restrict_of_ae_restrict_of_subset hst h

/-- **Local smoothness glues.** If an open set `V` of a finite-dimensional real inner product
space is covered by balls on which `U` agrees almost everywhere with a `C^∞` function, then `U`
agrees almost everywhere on `V` with a single function `Φ` that is `C^∞` on `V`.

The proof has three ingredients:
* overlapping local representatives are *equal* (not merely a.e. equal) on the overlap, because
  they are both continuous there and `volume` gives positive measure to non-empty open sets;
* hence the pointwise formula `Φ x = G x x` (using the chosen representative at `x`) defines a
  function which agrees with the representative `G x` on the whole ball around `x`, giving the
  smoothness;
* the remaining almost-everywhere statement is reduced to a countable subcover of `V` by the
  local balls, which exists because `E` is second countable, hence hereditarily Lindelöf. -/
theorem localSmoothGlue {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {V : Set E} (hV : IsOpen V) {U : E → ℂ}
    (hloc : ∀ x ∈ V, ∃ r : ℝ, 0 < r ∧ Metric.ball x r ⊆ V ∧
      ∃ g : E → ℂ, (∀ n : ℕ, ContDiffOn ℝ n g (Metric.ball x r)) ∧
        U =ᵐ[MeasureTheory.volume.restrict (Metric.ball x r)] g) :
    ∃ Φ : E → ℂ, (∀ n : ℕ, ContDiffOn ℝ n Φ V) ∧
      U =ᵐ[MeasureTheory.volume.restrict V] Φ := by
  classical
  -- Step 1: bundle the local data into a single existential.
  have key : ∀ x ∈ V, ∃ (r : ℝ) (g : E → ℂ), 0 < r ∧ Metric.ball x r ⊆ V ∧
      (∀ n : ℕ, ContDiffOn ℝ n g (Metric.ball x r)) ∧
      U =ᵐ[volume.restrict (Metric.ball x r)] g := by
    intro x hx
    obtain ⟨r, hr, hrV, g, hg, hae⟩ := hloc x hx
    exact ⟨r, g, hr, hrV, hg, hae⟩
  -- Step 2: choose a radius and a representative at each point of `V`.
  let R : ∀ x : E, x ∈ V → ℝ := fun x hx => Classical.choose (key x hx)
  let G : ∀ x : E, x ∈ V → E → ℂ :=
    fun x hx => Classical.choose (Classical.choose_spec (key x hx))
  have Rfact : ∀ x (hx : x ∈ V), 0 < R x hx ∧ Metric.ball x (R x hx) ⊆ V ∧
      (∀ n : ℕ, ContDiffOn ℝ n (G x hx) (Metric.ball x (R x hx))) ∧
      U =ᵐ[volume.restrict (Metric.ball x (R x hx))] (G x hx) := by
    intro x hx
    exact Classical.choose_spec (Classical.choose_spec (key x hx))
  -- Step 3: two local representatives agree *everywhere* on the overlap of their balls.
  have cons : ∀ x (hx : x ∈ V) (y : E) (hy : y ∈ V), y ∈ Metric.ball x (R x hx) →
      (G y hy) y = (G x hx) y := by
    intro x hx y hy hyb
    have hxR := Rfact x hx
    have hyR := Rfact y hy
    have hO : IsOpen (Metric.ball y (R y hy) ∩ Metric.ball x (R x hx)) :=
      isOpen_ball.inter isOpen_ball
    have hmem : y ∈ Metric.ball y (R y hy) ∩ Metric.ball x (R x hx) :=
      ⟨mem_ball_self hyR.1, hyb⟩
    have h1 : G y hy =ᵐ[volume.restrict (Metric.ball y (R y hy) ∩ Metric.ball x (R x hx))]
        G x hx :=
      (ae_eq_restrict_of_subset inter_subset_left hyR.2.2.2).symm.trans
        (ae_eq_restrict_of_subset inter_subset_right hxR.2.2.2)
    exact Measure.eqOn_open_of_ae_eq h1 hO
      ((hyR.2.2.1 0).continuousOn.mono inter_subset_left)
      ((hxR.2.2.1 0).continuousOn.mono inter_subset_right) hmem
  -- Step 4: the global candidate.
  let Φ : E → ℂ := fun z => if hz : z ∈ V then (G z hz) z else 0
  have Pho : ∀ x (hx : x ∈ V) (y : E) (hy : y ∈ V), y ∈ Metric.ball x (R x hx) →
      Φ y = (G x hx) y := by
    intro x hx y hy hyb
    have h1 : Φ y = (G y hy) y := dite_eq_left hy
    rw [h1]
    exact cons x hx y hy hyb
  -- Step 5: `Φ` is `C^n` on `V` for every `n`.
  have hsm : ∀ n : ℕ, ContDiffOn ℝ n Φ V := by
    intro n
    refine contDiffOn_of_locally_contDiffOn fun x hx => ?_
    refine ⟨Metric.ball x (R x hx), isOpen_ball, mem_ball_self (Rfact x hx).1, ?_⟩
    refine ((Rfact x hx).2.2.1 n).mono inter_subset_right |>.congr fun y hy => ?_
    exact Pho x hx y hy.1 hy.2
  -- Step 6: the almost-everywhere statement, via a countable subcover of `V`.
  obtain ⟨s, hsc, hscov⟩ :=
    (HereditarilyLindelofSpace.isLindelof V).elim_countable_subcover
      (fun x : V => Metric.ball (x : E) (R (x : E) x.2))
      (fun _ => isOpen_ball)
      (fun y hy => mem_iUnion.mpr ⟨⟨y, hy⟩, mem_ball_self (Rfact y hy).1⟩)
  have hbad : ∀ x ∈ s,
      volume ({z | U z ≠ Φ z} ∩ Metric.ball (x : E) (R (x : E) x.2)) = 0 := by
    intro x _
    have h0 : (volume.restrict (Metric.ball (x : E) (R (x : E) x.2)))
        {z | ¬(U z = (G (x : E) x.2) z)} = 0 :=
      ae_iff.mp (Rfact (x : E) x.2).2.2.2
    rw [Measure.restrict_apply' isOpen_ball.measurableSet] at h0
    refine measure_mono_null ?_ h0
    intro z hz
    exact ⟨fun hEq => hz.1 (hEq.trans (Pho (x : E) x.2 z ((Rfact (x : E) x.2).2.1 hz.2) hz.2).symm),
      hz.2⟩
  have hunion : volume (⋃ x ∈ s,
      {z | U z ≠ Φ z} ∩ Metric.ball (x : E) (R (x : E) x.2)) = 0 :=
    (measure_biUnion_null_iff hsc).mpr hbad
  have hsub : {z | U z ≠ Φ z} ∩ V ⊆
      ⋃ x ∈ s, ({z | U z ≠ Φ z} ∩ Metric.ball (x : E) (R (x : E) x.2)) := by
    intro z hz
    obtain ⟨x, hxs, hxz⟩ := mem_iUnion₂.mp (hscov hz.2)
    exact mem_iUnion₂.mpr ⟨x, hxs, hz.1, hxz⟩
  have hfin : volume ({z | U z ≠ Φ z} ∩ V) = 0 := measure_mono_null hsub hunion
  refine ⟨Φ, hsm, ?_⟩
  rw [Filter.EventuallyEq, ae_iff, Measure.restrict_apply' hV.measurableSet]
  exact hfin

end Work.EllipticEst.InteriorRegularity.IR
