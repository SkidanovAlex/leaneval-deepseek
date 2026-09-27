import Mathlib
import Submission.Work.EKLComp.MaxLeafDefs
import Submission.Work.EKLComp.Endgame_dense_rat
import Submission.Work.EKLCompLeaf.measurable_nu

/-!
# Measurability of the bad set of the leafwise maximal inequality

The set whose measurability is required is

`{x | ENNReal.ofReal α * ν x (ballU hij r) < ∫⁻ g in ballU hij r, ENNReal.ofReal (f (g • x)) ∂(ν x)}`

for a *weakly* measurable family of locally finite measures `ν` (measurability of
`x ↦ ∫ f dν x` for every compactly supported continuous `f`) and a measurable `f`.

Two ingredients:

* `x ↦ ν x K` is measurable for compact `K`: this is the Urysohn/outer-regularity argument of
  `Work.EKLCompLeaf.measurable_apply_isCompact` (proved from the weak measurability of `ν` and
  local finiteness alone).
* the parametrised lintegral `x ↦ ∫⁻ g in K, F x g ∂(ν x)` is measurable for jointly measurable
  `F`.  This is `measurable_setLIntegral_restrict_compact` below: the restricted measures
  `x ↦ (ν x)|_K` form a measurable kernel `κ₀` (`Measurable.measure_of_isPiSystem` applied to the
  π-system of closed sets, where `ν x (s ∩ K)` is measurable by the previous item), its
  normalisation `κ x = (ν x K + 1)⁻¹ • (ν x)|_K` is a *finite* kernel with uniform bound `1`, so
  `Measurable.lintegral_kernel_prod_right` applies, and the factor `ν x K + 1` is measurable.
-/

set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open Work.EKLContract

namespace Work.EKLComp

noncomputable section

variable {τ : Type*} [MeasurableSpace τ]

/-- Measurability of the parametrised lintegral over a compact set, against a weakly measurable
family of locally finite measures on `SL₃(ℝ)`. -/
theorem measurable_setLIntegral_restrict_compact
    {ν : τ → Measure SL3}
    (hmeas : ∀ f : CompactlySupportedContinuousMap SL3 ℝ,
      Measurable (fun x => ∫ g, f g ∂(ν x)))
    (hfin : ∀ x : τ, IsFiniteMeasureOnCompacts (ν x))
    {K : Set SL3} (hK : IsCompact K) (F : τ → SL3 → ℝ≥0∞)
    (hF : Measurable (Function.uncurry F)) :
    Measurable (fun x => ∫⁻ g in K, F x g ∂(ν x)) := by
  classical
  have hKval : Measurable (fun x : τ => ν x K) :=
    Work.EKLCompLeaf.measurable_apply_isCompact hmeas hfin hK
  -- (1) the restricted measure, as a function of `x`, is measurable.
  have hκ₀ : Measurable (fun x : τ => (ν x).restrict K) := by
    haveI : ∀ a : τ, IsFiniteMeasure ((ν a).restrict K) := fun a => ⟨by
      rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
      exact (hfin a).lt_top_of_isCompact hK⟩
    refine Measurable.measure_of_isPiSystem (μ := fun x : τ => (ν x).restrict K)
      borel_eq_generateFrom_isClosed isPiSystem_isClosed ?_ ?_
    · intro s hs
      have hcomp : IsCompact (s ∩ K) :=
        hK.of_isClosed_subset (hs.inter hK.isClosed) Set.inter_subset_right
      have h := Work.EKLCompLeaf.measurable_apply_isCompact hmeas hfin hcomp
      have hfun : (fun x : τ => ((ν x).restrict K) s) = fun x => ν x (s ∩ K) := by
        funext x; rw [Measure.restrict_apply hs.measurableSet]
      rw [hfun]
      exact h
    · have hfun : (fun x : τ => ((ν x).restrict K) Set.univ) = fun x => ν x K := by
        funext x; rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
      rw [hfun]
      exact hKval
  -- (2) the normalised restricted measure is a kernel with a uniform bound.
  let c : τ → ℝ≥0∞ := fun x => (ν x K + 1)⁻¹
  have hc : Measurable c := (Measurable.add hKval measurable_const).inv
  let κ : Kernel τ SL3 := ⟨fun x => c x • (ν x).restrict K, by
    refine Measure.measurable_of_measurable_coe _ (fun s hs => ?_)
    have h2 : Measurable (fun x : τ => ((ν x).restrict K) s) :=
      (Measure.measurable_coe hs).comp hκ₀
    have h3 : (fun x : τ => (c x • (ν x).restrict K) s)
        = fun x => c x * ((ν x).restrict K) s := by
      funext x; rw [Measure.smul_apply, smul_eq_mul]
    rw [h3]
    exact hc.mul h2⟩
  have hfinK : IsFiniteKernel κ := ⟨⟨1, ENNReal.one_lt_top, fun x => by
    show (c x • (ν x).restrict K) Set.univ ≤ 1
    rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter]
    have h0 : (ν x K + 1 : ℝ≥0∞) ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le zero_lt_one le_add_self)
    have htop : (ν x K + 1 : ℝ≥0∞) ≠ ⊤ :=
      (ENNReal.add_lt_top.mpr ⟨(hfin x).lt_top_of_isCompact hK, ENNReal.one_lt_top⟩).ne
    calc c x * ν x K ≤ c x * (ν x K + 1) := by
          gcongr
          exact le_self_add
      _ = 1 := by
          rw [show c x = (ν x K + 1)⁻¹ from rfl]
          exact ENNReal.inv_mul_cancel h0 htop⟩⟩
  haveI := hfinK
  have hy : Measurable (fun x => ∫⁻ g, F x g ∂(κ x)) :=
    Measurable.lintegral_kernel_prod_right hF
  -- (3) undo the normalisation.
  have key : ∀ x : τ, ∫⁻ g, F x g ∂(κ x) = c x * ∫⁻ g in K, F x g ∂(ν x) := by
    intro x
    show ∫⁻ g, F x g ∂(c x • (ν x).restrict K) = c x * ∫⁻ g in K, F x g ∂(ν x)
    rw [lintegral_smul_measure, smul_eq_mul]
  have hgoal : (fun x => ∫⁻ g in K, F x g ∂(ν x))
      = fun x => (ν x K + 1) * ∫⁻ g, F x g ∂(κ x) := by
    funext x
    rw [key x, ← mul_assoc, show (ν x K + 1) * c x = 1 from by
      rw [show c x = (ν x K + 1)⁻¹ from rfl]
      exact ENNReal.mul_inv_cancel
        (ne_of_gt (lt_of_lt_of_le zero_lt_one le_add_self))
        ((ENNReal.add_lt_top.mpr ⟨(hfin x).lt_top_of_isCompact hK, ENNReal.one_lt_top⟩).ne),
      one_mul]
  rw [hgoal]
  exact (Measurable.add hKval measurable_const).mul hy

theorem measurableSet_badENN (i j : Fin 3) (hij : i ≠ j)
    (ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3)
    (hν : ∀ f : CompactlySupportedContinuousMap Work.EKLContract.SL3 ℝ,
      Measurable (fun x => ∫ g, f g ∂(ν x)))
    (hfin : ∀ x, MeasureTheory.IsFiniteMeasureOnCompacts (ν x))
    (f : Work.EKLContract.X3 → ℝ) (hf : Measurable f) (α r : ℝ) :
    MeasurableSet {x : Work.EKLContract.X3 | Work.EKLComp.BadENN i j hij ν f x α r} := by
  have hK : IsCompact (ballU hij r) := isCompact_Icc.image (continuous_uij hij)
  have hFs : Measurable
      (Function.uncurry (fun (x : X3) (g : SL3) => ENNReal.ofReal (f (g • x)))) := by
    show Measurable (fun p : X3 × SL3 => ENNReal.ofReal (f (p.2 • p.1)))
    exact (hf.comp (continuous_smul.comp
      (continuous_snd.prodMk continuous_fst)).measurable).ennreal_ofReal
  show MeasurableSet {x : X3 |
    ENNReal.ofReal α * ν x (ballU hij r)
      < ∫⁻ g in ballU hij r, ENNReal.ofReal (f (g • x)) ∂(ν x)}
  exact measurableSet_lt
    ((Work.EKLCompLeaf.measurable_apply_isCompact hν hfin hK).const_mul _)
    (measurable_setLIntegral_restrict_compact hν hfin hK _ hFs)

end

end Work.EKLComp
