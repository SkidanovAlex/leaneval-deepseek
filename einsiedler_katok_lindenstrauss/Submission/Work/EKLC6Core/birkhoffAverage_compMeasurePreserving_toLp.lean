import Mathlib

/-!
# The Birkhoff average of the Koopman operator is the Birkhoff average of the function

Let `T : X → X` be measure preserving for `μ`.  The *Koopman* (composition) operator
`K := Lp.compMeasurePreserving T hmp : L²(μ) →+ L²(μ)`, `K g = g ∘ T`, is an isometry of `L²(μ)`.
This file identifies the `n`-th Birkhoff average of `K` acting on `MemLp.toLp f hf` with the
`n`-th Birkhoff average of `f` along `T`, as elements of `L²(μ)` (i.e. up to `μ`-a.e. equality).

The proof is by a direct computation of the coercions back to functions:
* `MeasureTheory.Lp.coeFn_compMeasurePreserving` : `K g =ᵐ[μ] g ∘ T`;
* by induction, `K^[i] g =ᵐ[μ] g ∘ T^[i]` (`coeFn_iterate_compMeasurePreserving`), using that
  `T^[i]` is measure preserving;
* `MeasureTheory.Lp.coeFn_smul` and `MeasureTheory.Lp.coeFn_finsetSum` commute the coercions out
  of the scalar multiplication and the finite sum defining the Birkhoff average
  (`coeFn_birkhoffAverage_compMeasurePreserving`).
-/

open MeasureTheory Filter

namespace Work.EKLC6Core

/-- The `i`-th iterate of the Koopman operator `g ↦ g ∘ T` of a measure preserving map `T`,
applied to `g ∈ L²(μ)`, is the (a.e. class of the) function `x ↦ g (T^[i] x)`. -/
lemma coeFn_iterate_compMeasurePreserving {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) (T : X → X) (hmp : MeasureTheory.MeasurePreserving T μ μ)
    (g : MeasureTheory.Lp ℝ 2 μ) (i : ℕ) :
    ⇑(((⇑(MeasureTheory.Lp.compMeasurePreserving T hmp))^[i]) g)
      =ᵐ[μ] fun x => ⇑g (T^[i] x) := by
  induction i with
  | zero => exact EventuallyEq.of_eq (by funext x; rfl)
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    refine (MeasureTheory.Lp.coeFn_compMeasurePreserving _ hmp).trans ?_
    refine (ih.comp_tendsto hmp.quasiMeasurePreserving.tendsto_ae).trans ?_
    exact EventuallyEq.of_eq (by
      funext x
      simp [Function.comp_apply, Function.iterate_succ_apply])

/-- The `n`-th Birkhoff average of the Koopman operator `Lp.compMeasurePreserving T hmp`
applied to `g ∈ L²(μ)`, viewed as a function, is a.e. the `n`-th Birkhoff average of `⇑g`
along `T`. -/
lemma coeFn_birkhoffAverage_compMeasurePreserving {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) (T : X → X) (hmp : MeasureTheory.MeasurePreserving T μ μ)
    (g : MeasureTheory.Lp ℝ 2 μ) (n : ℕ) :
    ⇑(birkhoffAverage ℝ (⇑(MeasureTheory.Lp.compMeasurePreserving T hmp)) id n g)
      =ᵐ[μ] fun x => birkhoffAverage ℝ T (⇑g) n x := by
  have hZ : ⇑(∑ i ∈ Finset.range n,
        (⇑(MeasureTheory.Lp.compMeasurePreserving T hmp))^[i] g)
      =ᵐ[μ] fun x => ∑ i ∈ Finset.range n, ⇑g (T^[i] x) := by
    refine (MeasureTheory.Lp.coeFn_finsetSum _ _).trans ?_
    filter_upwards [(Finset.eventually_all (Finset.range n)).2
      (fun i _ => coeFn_iterate_compMeasurePreserving μ T hmp g i)] with x hx
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl (fun i hi => hx i hi)
  have h1 : ⇑(birkhoffAverage ℝ (⇑(MeasureTheory.Lp.compMeasurePreserving T hmp)) id n g)
      =ᵐ[μ] fun x => (n:ℝ)⁻¹ • (∑ i ∈ Finset.range n, ⇑g (T^[i] x)) := by
    rw [birkhoffAverage, birkhoffSum]
    simp only [id_eq]
    refine (MeasureTheory.Lp.coeFn_smul _ _).trans ?_
    refine (hZ.const_smul _).trans ?_
    exact EventuallyEq.of_eq (by funext x; rfl)
  exact h1.trans (EventuallyEq.of_eq (by
    funext x
    simp [birkhoffAverage, birkhoffSum, smul_eq_mul]))

/-- The `n`-th Birkhoff average of `f` along `T`, viewed as an element of `L²`, is the `n`-th
Birkhoff average of the Koopman operator applied to `f`. -/
theorem birkhoffAverage_compMeasurePreserving_toLp {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) (T : X → X) (hmp : MeasureTheory.MeasurePreserving T μ μ)
    (f : X → ℝ) (hf : MeasureTheory.MemLp f 2 μ) (n : ℕ) :
    ((birkhoffAverage ℝ (⇑(MeasureTheory.Lp.compMeasurePreserving T hmp)) id n
        (MeasureTheory.MemLp.toLp f hf) : MeasureTheory.Lp ℝ 2 μ) : X → ℝ)
      =ᵐ[μ] fun x => birkhoffAverage ℝ T f n x := by
  have hmain := coeFn_birkhoffAverage_compMeasurePreserving μ T hmp
    (MeasureTheory.MemLp.toLp f hf) n
  have hc : (fun x => (n:ℝ)⁻¹ • (∑ k ∈ Finset.range n,
        ⇑(MeasureTheory.MemLp.toLp f hf) (T^[k] x)))
      =ᵐ[μ] fun x => (n:ℝ)⁻¹ • (∑ k ∈ Finset.range n, f (T^[k] x)) := by
    filter_upwards [(Finset.eventually_all (Finset.range n)).2 (fun k _ =>
      (MeasureTheory.MemLp.coeFn_toLp hf).comp_tendsto
        ((hmp.iterate k).quasiMeasurePreserving.tendsto_ae))] with x hx
    congr 1
    exact Finset.sum_congr rfl (fun k hk => hx k hk)
  have hb : (fun x => birkhoffAverage ℝ T (⇑(MeasureTheory.MemLp.toLp f hf)) n x)
      =ᵐ[μ] (fun x => (n:ℝ)⁻¹ • (∑ k ∈ Finset.range n,
        ⇑(MeasureTheory.MemLp.toLp f hf) (T^[k] x))) :=
    EventuallyEq.of_eq (by funext x; simp [birkhoffAverage, birkhoffSum])
  have hd : (fun x => (n:ℝ)⁻¹ • (∑ k ∈ Finset.range n, f (T^[k] x)))
      =ᵐ[μ] (fun x => birkhoffAverage ℝ T f n x) :=
    EventuallyEq.of_eq (by funext x; simp [birkhoffAverage, birkhoffSum, smul_eq_mul])
  exact hmain.trans (hb.trans (hc.trans hd))

end Work.EKLC6Core
