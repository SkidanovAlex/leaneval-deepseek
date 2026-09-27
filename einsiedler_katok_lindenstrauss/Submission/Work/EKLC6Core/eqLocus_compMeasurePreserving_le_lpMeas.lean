import Mathlib

namespace Work.EKLC6Core

open MeasureTheory Filter
open scoped MeasureTheory

/-- Conversely, an `L²` function fixed by the Koopman operator of `T` is a.e. measurable for the
σ-algebra of `T`-invariant sets. -/
theorem eqLocus_compMeasurePreserving_le_lpMeas {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) (T : X → X) (hmp : MeasureTheory.MeasurePreserving T μ μ)
    (g : MeasureTheory.Lp ℝ 2 μ) (hg : MeasureTheory.Lp.compMeasurePreserving T hmp g = g) :
    g ∈ MeasureTheory.lpMeas ℝ ℝ (MeasurableSpace.invariants T) 2 μ := by
  rw [MeasureTheory.mem_lpMeas_iff_aestronglyMeasurable]
  -- `g` is a.e. invariant under `T`
  have h1 := MeasureTheory.Lp.coeFn_compMeasurePreserving (E := ℝ) (p := 2) g hmp
  have h2 : (MeasureTheory.Lp.compMeasurePreserving T hmp g : X → ℝ) = (g : X → ℝ) := by
    rw [hg]
  have hae : (g : X → ℝ) ∘ T =ᵐ[μ] (g : X → ℝ) := by
    have h1' : (MeasureTheory.Lp.compMeasurePreserving T hmp g : X → ℝ) =ᵐ[μ]
        (g : X → ℝ) ∘ T := h1
    rw [h2] at h1'
    exact h1'.symm
  -- the almost everywhere limit of `g` along the forward orbit of `x`
  let H : X → ℝ := fun x => liminf (fun n : ℕ => (g : X → ℝ) (T^[n] x)) atTop
  -- `H` is exactly `T`-invariant, since `liminf` only depends on the tail of the sequence
  have hHT : H ∘ T = H := by
    funext x
    show liminf (fun n : ℕ => (g : X → ℝ) (T^[n] (T x))) atTop
        = liminf (fun n : ℕ => (g : X → ℝ) (T^[n] x)) atTop
    have hshift : (fun n : ℕ => (g : X → ℝ) (T^[n] (T x))) =
        (fun n : ℕ => (g : X → ℝ) (T^[n] x)) ∘ (fun n : ℕ => n + 1) := by
      funext n
      simp only [Function.comp_apply]
      rw [Function.iterate_succ_apply]
    rw [hshift, Filter.liminf_comp, Filter.map_add_atTop_eq_nat 1]
  -- `H` is measurable
  have hHmeas : Measurable H := by
    show Measurable (fun x => liminf (fun n : ℕ => (g : X → ℝ) (T^[n] x)) atTop)
    apply Measurable.liminf
    intro n
    exact ((Lp.stronglyMeasurable g).measurable).comp (hmp.measurable.iterate n)
  -- hence `H` is measurable for the σ-algebra of invariant sets
  have hHinv : Measurable[MeasurableSpace.invariants T] H := by
    rw [MeasurableSpace.measurable_invariants_dom]
    refine ⟨hHmeas, fun s _ => ?_⟩
    rw [hHT]
  have hHsm : StronglyMeasurable[MeasurableSpace.invariants T] H :=
    stronglyMeasurable_iff_measurable.mpr hHinv
  -- `H` agrees with `g` almost everywhere
  have heq : (g : X → ℝ) =ᵐ[μ] H := by
    have hstep : ∀ n : ℕ, (fun x => (g : X → ℝ) (T^[n+1] x)) =ᵐ[μ]
        (fun x => (g : X → ℝ) (T^[n] x)) := by
      intro n
      have hh := (hmp.iterate n).quasiMeasurePreserving.ae_eq_comp hae
      filter_upwards [hh] with x hx
      simpa only [Function.comp_apply, Function.iterate_succ_apply'] using hx
    have hall : ∀ᶠ x in MeasureTheory.ae μ,
        ∀ n : ℕ, (g : X → ℝ) (T^[n+1] x) = (g : X → ℝ) (T^[n] x) :=
      eventually_countable_forall.2 hstep
    filter_upwards [hall] with x hx
    show (g : X → ℝ) x = H x
    have hconst : (fun n : ℕ => (g : X → ℝ) (T^[n] x)) = fun _ : ℕ => (g : X → ℝ) x := by
      funext n
      induction n with
      | zero => rfl
      | succ k ih => rw [hx k, ih]
    show (g : X → ℝ) x = liminf (fun n : ℕ => (g : X → ℝ) (T^[n] x)) atTop
    rw [hconst, Filter.liminf_const]
  exact ⟨H, hHsm, heq⟩

end Work.EKLC6Core
