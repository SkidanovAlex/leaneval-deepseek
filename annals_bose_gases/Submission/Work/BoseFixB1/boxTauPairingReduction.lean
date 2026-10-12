import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1.BoxTauPairingDefs
import Submission.Work.BoseFixB1.boxOpG_adjoint
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1
open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal
open _root_.BoseGases Submission.BoseGases
set_option autoImplicit false
set_option maxHeartbeats 1000000
local notation "E3" => EuclideanSpace ℝ (Fin 3)

lemma integrableOn_fibre_of_measurable_bounded {N : ℕ} {ℓ : ℝ} {A : Set E3}
    (hA : MeasurableSet A) (hℓ : 0 < ℓ) (hAc : A ⊆ acube ℓ) {W : X N → ℝ}
    (hWm : Measurable W) {CW : ℝ} (hWb : ∀ x ∈ abox N ℓ, |W x| ≤ CW)
    {x : X N} (hx : x ∈ abox N ℓ) (i : Fin N) :
    IntegrableOn (fun z => W (Function.update x i z)) A volume := by
  refine IntegrableOn.of_bound (Work.BoseFixB1S.volume_A_lt_top hℓ hAc)
    ((hWm.comp (continuous_const.update i continuous_id).measurable).aestronglyMeasurable) (max CW 0) ?_
  filter_upwards [ae_restrict_mem hA] with z hz
  have hmem : Function.update x i z ∈ abox N ℓ := by
    intro j
    rw [Function.update_apply]
    by_cases hj : j = i
    · rw [if_pos hj]; exact hAc hz
    · rw [if_neg hj]; exact hx j
  calc ‖W (Function.update x i z)‖ = |W (Function.update x i z)| := Real.norm_eq_abs _
    _ ≤ CW := hWb _ hmem
    _ ≤ max CW 0 := le_max_left _ _

lemma integral_fibre_ofReal_add_I {N : ℕ} {A : Set E3} {W Z : X N → ℝ} {x : X N} {i : Fin N}
    (hW : IntegrableOn (fun z => W (Function.update x i z)) A volume)
    (hZ : IntegrableOn (fun z => Z (Function.update x i z)) A volume) :
    (∫ z in A, (((W (Function.update x i z) : ℝ) : ℂ)
        + Complex.I * ((Z (Function.update x i z) : ℝ) : ℂ)))
      = ((∫ z in A, W (Function.update x i z) : ℝ) : ℂ)
        + Complex.I * ((∫ z in A, Z (Function.update x i z) : ℝ) : ℂ) := by
  have hJ : (∫ z in A, (((W (Function.update x i z) : ℝ) : ℂ)
        + Complex.I * ((Z (Function.update x i z) : ℝ) : ℂ)))
      = (∫ z in A, ((W (Function.update x i z) : ℝ) : ℂ))
        + (∫ z in A, Complex.I * ((Z (Function.update x i z) : ℝ) : ℂ)) :=
    integral_add hW.ofReal (hZ.ofReal.const_mul Complex.I)
  rw [hJ]
  have hW' : (∫ z in A, ((W (Function.update x i z) : ℝ) : ℂ))
      = ((∫ z in A, W (Function.update x i z) : ℝ) : ℂ) := integral_ofReal
  have hZ' : (∫ z in A, ((Z (Function.update x i z) : ℝ) : ℂ))
      = ((∫ z in A, Z (Function.update x i z) : ℝ) : ℂ) := integral_ofReal
  rw [integral_const_mul, hW', hZ']

lemma boxTauDagGenC_state_add_I {N : ℕ} {ℓ : ℝ} (volA : ℝ) (A : Set E3) (hA : MeasurableSet A)
    (hℓ : 0 < ℓ) (hAc : A ⊆ acube ℓ) {m : E3 → ℂ} {W Z : X N → ℝ}
    (hWm : Measurable W) {CW : ℝ} (hWb : ∀ x ∈ abox N ℓ, |W x| ≤ CW)
    (hZm : Measurable Z) {CZ : ℝ} (hZb : ∀ x ∈ abox N ℓ, |Z x| ≤ CZ) :
    ∀ x ∈ abox N ℓ,
      boxTauDagGenC volA A m (fun y => (W y : ℂ) + Complex.I * (Z y : ℂ)) x
        = boxTauDagGenC volA A m (fun y => (W y : ℂ)) x
          + Complex.I * boxTauDagGenC volA A m (fun y => (Z y : ℂ)) x := by
  intro x hx
  have hL : boxTauDagGenC volA A m (fun y => (W y : ℂ) + Complex.I * (Z y : ℂ)) x
      = (Real.sqrt volA)⁻¹ * (∑ i : Fin N, A.indicator (fun _ => (1 : ℂ)) (x i) * m (x i)
          * ∫ z in A, (((W (Function.update x i z) : ℝ) : ℂ)
            + Complex.I * ((Z (Function.update x i z) : ℝ) : ℂ))) := rfl
  have hR1 : boxTauDagGenC volA A m (fun y => (W y : ℂ)) x
      = (Real.sqrt volA)⁻¹ * (∑ i : Fin N, A.indicator (fun _ => (1 : ℂ)) (x i) * m (x i)
          * ((∫ z in A, W (Function.update x i z) : ℝ) : ℂ)) := by
    rw [show boxTauDagGenC volA A m (fun y => (W y : ℂ)) x
        = (Real.sqrt volA)⁻¹ * (∑ i : Fin N, A.indicator (fun _ => (1 : ℂ)) (x i) * m (x i)
            * ∫ z in A, ((W (Function.update x i z) : ℝ) : ℂ)) from rfl]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show (∫ z in A, ((W (Function.update x i z) : ℝ) : ℂ))
        = ((∫ z in A, W (Function.update x i z) : ℝ) : ℂ) from integral_ofReal]
  have hR2 : boxTauDagGenC volA A m (fun y => (Z y : ℂ)) x
      = (Real.sqrt volA)⁻¹ * (∑ i : Fin N, A.indicator (fun _ => (1 : ℂ)) (x i) * m (x i)
          * ((∫ z in A, Z (Function.update x i z) : ℝ) : ℂ)) := by
    rw [show boxTauDagGenC volA A m (fun y => (Z y : ℂ)) x
        = (Real.sqrt volA)⁻¹ * (∑ i : Fin N, A.indicator (fun _ => (1 : ℂ)) (x i) * m (x i)
            * ∫ z in A, ((Z (Function.update x i z) : ℝ) : ℂ)) from rfl]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show (∫ z in A, ((Z (Function.update x i z) : ℝ) : ℂ))
        = ((∫ z in A, Z (Function.update x i z) : ℝ) : ℂ) from integral_ofReal]
  have hfib : ∀ i : Fin N, (∫ z in A, (((W (Function.update x i z) : ℝ) : ℂ)
        + Complex.I * ((Z (Function.update x i z) : ℝ) : ℂ)))
      = ((∫ z in A, W (Function.update x i z) : ℝ) : ℂ)
        + Complex.I * ((∫ z in A, Z (Function.update x i z) : ℝ) : ℂ) :=
    fun i => integral_fibre_ofReal_add_I
      (integrableOn_fibre_of_measurable_bounded hA hℓ hAc hWm hWb hx i)
      (integrableOn_fibre_of_measurable_bounded hA hℓ hAc hZm hZb hx i)
  have hsum : (∑ i : Fin N, A.indicator (fun _ => (1 : ℂ)) (x i) * m (x i)
        * ∫ z in A, (((W (Function.update x i z) : ℝ) : ℂ)
          + Complex.I * ((Z (Function.update x i z) : ℝ) : ℂ)))
      = (∑ i : Fin N, A.indicator (fun _ => (1 : ℂ)) (x i) * m (x i)
          * ((∫ z in A, W (Function.update x i z) : ℝ) : ℂ))
        + Complex.I * (∑ i : Fin N, A.indicator (fun _ => (1 : ℂ)) (x i) * m (x i)
          * ((∫ z in A, Z (Function.update x i z) : ℝ) : ℂ)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hfib i]
    ring
  rw [hL, hR1, hR2, hsum]
  ring

/-! ## mode linearity -/

lemma boxTauDagGenC_smul_mode {N : ℕ} (volA : ℝ) (A : Set E3) (c : ℂ) (g : E3 → ℂ)
    (Φ : X N → ℂ) :
    boxTauDagGenC volA A (fun z => c * g z) Φ = c • boxTauDagGenC volA A g Φ := by
  funext x
  simp only [boxTauDagGenC, Pi.smul_apply, smul_eq_mul]
  have h1 : (∑ i : Fin N, A.indicator (fun _ => (1 : ℂ)) (x i) * (c * g (x i))
        * ∫ z in A, Φ (Function.update x i z))
      = c * (∑ i : Fin N, A.indicator (fun _ => (1 : ℂ)) (x i) * g (x i)
        * ∫ z in A, Φ (Function.update x i z)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [h1]
  ring

lemma boxTauDagGen_smul_mode {N : ℕ} (volA : ℝ) (A : Set E3) (c : ℝ) (g : E3 → ℝ)
    (Ψ : X N → ℝ) :
    boxTauDagGen volA A (fun z => c * g z) Ψ = c • boxTauDagGen volA A g Ψ := by
  funext x
  simp only [boxTauDagGen, Pi.smul_apply, smul_eq_mul]
  have h1 : (∑ i : Fin N, A.indicator (fun _ => (1 : ℝ)) (x i) * (c * g (x i))
        * ∫ z in A, Ψ (Function.update x i z))
      = c * (∑ i : Fin N, A.indicator (fun _ => (1 : ℝ)) (x i) * g (x i)
        * ∫ z in A, Ψ (Function.update x i z)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [h1]
  ring

lemma boxTauDagGenC_add_mode {N : ℕ} (volA : ℝ) (A : Set E3) (g₁ g₂ : E3 → ℂ)
    (Φ : X N → ℂ) :
    boxTauDagGenC volA A (fun z => g₁ z + g₂ z) Φ
      = boxTauDagGenC volA A g₁ Φ + boxTauDagGenC volA A g₂ Φ := by
  funext x
  simp only [boxTauDagGenC, Pi.add_apply]
  have h1 : (∑ i : Fin N, A.indicator (fun _ => (1 : ℂ)) (x i) * (g₁ (x i) + g₂ (x i))
        * ∫ z in A, Φ (Function.update x i z))
      = (∑ i : Fin N, A.indicator (fun _ => (1 : ℂ)) (x i) * g₁ (x i)
          * ∫ z in A, Φ (Function.update x i z))
        + ∑ i : Fin N, A.indicator (fun _ => (1 : ℂ)) (x i) * g₂ (x i)
          * ∫ z in A, Φ (Function.update x i z) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [h1]
  ring

end Work.BoseFixB1

namespace Work.BoseFixB1
open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal
open _root_.BoseGases Submission.BoseGases
set_option autoImplicit false
set_option maxHeartbeats 4000000
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- `boxTauDagGenC` at a real mode and the complexification of a REAL state is the complexification
of the real creation operator. -/
lemma boxTauDagGenC_ofReal_state {N : ℕ} (volA : ℝ) (A : Set E3)
    {f : E3 → ℝ} {W : X N → ℝ} :
    boxTauDagGenC volA A (fun z => (f z : ℂ)) (fun y => (W y : ℂ))
      = fun x => ((boxTauDagGen volA A f W x : ℝ) : ℂ) := by
  funext x
  have hL : boxTauDagGenC volA A (fun z => (f z : ℂ)) (fun y => (W y : ℂ)) x
      = (Real.sqrt volA)⁻¹ * (∑ i : Fin N, A.indicator (fun _ => (1 : ℂ)) (x i) * (f (x i) : ℂ)
          * ∫ z in A, ((W (Function.update x i z) : ℝ) : ℂ)) := rfl
  have hR : boxTauDagGen volA A f W x
      = (Real.sqrt volA)⁻¹ * (∑ i : Fin N, A.indicator (fun _ => (1 : ℝ)) (x i) * f (x i)
          * ∫ z in A, W (Function.update x i z)) := rfl
  rw [hL, hR, Complex.ofReal_mul, Complex.ofReal_sum]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [show (∫ z in A, ((W (Function.update x i z) : ℝ) : ℂ))
      = ((∫ z in A, W (Function.update x i z) : ℝ) : ℂ) from integral_ofReal]
  have hind : A.indicator (fun _ => (1 : ℂ)) (x i)
      = ((A.indicator (fun _ => (1 : ℝ)) (x i) : ℝ) : ℂ) := by
    by_cases hz : x i ∈ A <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hz]
  rw [hind]
  push_cast
  ring

/-- **Mode-splitting with a real state**: the complexified creation operator at `f + i·g` applied to
the complexification of a real state is `Y_f Φ + i·Y_g Φ`. -/
lemma boxTauDagGenC_mode_ofReal {N : ℕ} (volA : ℝ) (A : Set E3)
    {f g : E3 → ℝ} {Φ : X N → ℝ} :
    boxTauDagGenC volA A (fun z => (f z : ℂ) + Complex.I * (g z : ℂ)) (fun y => (Φ y : ℂ))
      = fun x => ((boxTauDagGen volA A f Φ x : ℝ) : ℂ)
          + Complex.I * ((boxTauDagGen volA A g Φ x : ℝ) : ℂ) := by
  funext x
  have hL : boxTauDagGenC volA A (fun z => (f z : ℂ) + Complex.I * (g z : ℂ)) (fun y => (Φ y : ℂ)) x
      = (Real.sqrt volA)⁻¹ * (∑ i : Fin N, A.indicator (fun _ => (1 : ℂ)) (x i)
          * ((f (x i) : ℂ) + Complex.I * (g (x i) : ℂ))
          * ∫ z in A, ((Φ (Function.update x i z) : ℝ) : ℂ)) := rfl
  have hR1 : boxTauDagGen volA A f Φ x
      = (Real.sqrt volA)⁻¹ * (∑ i : Fin N, A.indicator (fun _ => (1 : ℝ)) (x i) * f (x i)
          * ∫ z in A, Φ (Function.update x i z)) := rfl
  have hR2 : boxTauDagGen volA A g Φ x
      = (Real.sqrt volA)⁻¹ * (∑ i : Fin N, A.indicator (fun _ => (1 : ℝ)) (x i) * g (x i)
          * ∫ z in A, Φ (Function.update x i z)) := rfl
  have hsum : (∑ i : Fin N, A.indicator (fun _ => (1 : ℂ)) (x i)
        * ((f (x i) : ℂ) + Complex.I * (g (x i) : ℂ))
        * ∫ z in A, ((Φ (Function.update x i z) : ℝ) : ℂ))
      = (∑ i : Fin N, ((A.indicator (fun _ => (1 : ℝ)) (x i) * f (x i)
            * ∫ z in A, Φ (Function.update x i z) : ℝ) : ℂ))
        + Complex.I * (∑ i : Fin N, ((A.indicator (fun _ => (1 : ℝ)) (x i) * g (x i)
            * ∫ z in A, Φ (Function.update x i z) : ℝ) : ℂ)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show (∫ z in A, ((Φ (Function.update x i z) : ℝ) : ℂ))
        = ((∫ z in A, Φ (Function.update x i z) : ℝ) : ℂ) from integral_ofReal]
    have hind : A.indicator (fun _ => (1 : ℂ)) (x i)
        = ((A.indicator (fun _ => (1 : ℝ)) (x i) : ℝ) : ℂ) := by
      by_cases hz : x i ∈ A <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hz]
    rw [hind]
    push_cast
    ring
  rw [hL, hR1, hR2, Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_sum,
    Complex.ofReal_sum, hsum]
  ring

end Work.BoseFixB1

namespace Work.BoseFixB1
open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal
open _root_.BoseGases Submission.BoseGases
set_option autoImplicit false
set_option maxHeartbeats 4000000
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The pointwise pairing reduction.**  With the two real (smooth, mean-free) modes `u, v` of the
windowed exponential and `Ψ` real, the genuine double creation at `g = u + i·v` and `ḡ = u − i·v`
collapses onto the two real same-mode creations. -/
lemma star_boxWinModeC (volA : ℝ) (A : Set E3) {χ : E3 → ℝ} {p : E3}
    (hχc : Continuous χ) (hχs : HasCompactSupport χ) (z : E3) :
    star (boxWinModeC volA A χ p z)
      = (A.indicator (fun _ => (1 : ℝ)) z : ℂ)
          * ((boxWinModeReSmooth volA A χ p z : ℂ)
            - Complex.I * (boxWinModeImSmooth volA A χ p z : ℂ)) := by
  have hgs := boxWinModeCSmooth_eq volA A hχc hχs p z
  by_cases hz : z ∈ A
  · have hstar : star (boxWinModeCSmooth volA A χ p z)
        = (boxWinModeReSmooth volA A χ p z : ℂ)
          - Complex.I * (boxWinModeImSmooth volA A χ p z : ℂ) := by
      rw [hgs, star_add, star_mul, Complex.star_def, Complex.conj_ofReal, Complex.conj_ofReal,
        Complex.conj_I]
      ring
    rw [boxWinModeC_eq_indicator_smooth, Set.indicator_of_mem hz, one_mul, hstar,
      Set.indicator_of_mem hz, Complex.ofReal_one, one_mul]
  · rw [boxWinModeC_eq_indicator_smooth, Set.indicator_of_notMem hz, zero_mul, star_zero,
      Set.indicator_of_notMem hz, zero_mul]

lemma boxTauDagGenC_star_modeC_eq {N : ℕ} (volA : ℝ) (A : Set E3) {χ : E3 → ℝ} {p : E3}
    (hχc : Continuous χ) (hχs : HasCompactSupport χ) (Φ : X N → ℂ) :
    boxTauDagGenC volA A (fun z => star (boxWinModeC volA A χ p z)) Φ
      = boxTauDagGenC volA A (fun z => (boxWinModeReSmooth volA A χ p z : ℂ)
          - Complex.I * (boxWinModeImSmooth volA A χ p z : ℂ)) Φ := by
  rw [show (fun z => star (boxWinModeC volA A χ p z))
      = fun z => A.indicator (fun _ => (1 : ℂ)) z
          * ((boxWinModeReSmooth volA A χ p z : ℂ)
            - Complex.I * (boxWinModeImSmooth volA A χ p z : ℂ)) from
    funext fun z => star_boxWinModeC volA A hχc hχs z]
  exact boxTauDagGenC_indicator_mode volA A _ Φ


lemma pointwise_pair_reduction {N : ℕ} {ℓ volA : ℝ} {A : Set E3} (hA : MeasurableSet A)
    (hℓ : 0 < ℓ) (hAc : A ⊆ acube ℓ)
    {χ : E3 → ℝ} (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    {Ψ : X (N + 2) → ℝ} (p : E3)
    (hcomm : ∀ x ∈ abox (N + 2) ℓ,
        boxTauDagGen volA A (boxWinModeImSmooth volA A χ p)
            (boxTauDagGen volA A (boxWinModeReSmooth volA A χ p) Ψ) x
          = boxTauDagGen volA A (boxWinModeReSmooth volA A χ p)
            (boxTauDagGen volA A (boxWinModeImSmooth volA A χ p) Ψ) x)
    (hWm : Measurable (boxTauDagGen volA A (boxWinModeReSmooth volA A χ p) Ψ))
    {CW : ℝ}
    (hWb : ∀ x ∈ abox (N + 2) ℓ,
      |boxTauDagGen volA A (boxWinModeReSmooth volA A χ p) Ψ x| ≤ CW)
    (hZm : Measurable (boxTauDagGen volA A (boxWinModeImSmooth volA A χ p) Ψ))
    {CZ : ℝ}
    (hZb : ∀ x ∈ abox (N + 2) ℓ,
      |boxTauDagGen volA A (boxWinModeImSmooth volA A χ p) Ψ x| ≤ CZ) :
    ∀ x ∈ abox (N + 2) ℓ,
      (Ψ x : ℂ) * boxTauDagGenC volA A (fun z => star (boxWinModeC volA A χ p z))
          (boxTauDagGenC volA A (boxWinModeC volA A χ p) (fun y => (Ψ y : ℂ))) x
        = ((Ψ x * (boxTauDagGen volA A (boxWinModeReSmooth volA A χ p)
              (boxTauDagGen volA A (boxWinModeReSmooth volA A χ p) Ψ) x
            + boxTauDagGen volA A (boxWinModeImSmooth volA A χ p)
              (boxTauDagGen volA A (boxWinModeImSmooth volA A χ p) Ψ) x) : ℝ) : ℂ) := by
  intro x hx
  -- abbreviations
  have hmodeC : boxTauDagGenC volA A (boxWinModeC volA A χ p) (fun y => (Ψ y : ℂ))
      = fun y : X (N + 2) => ((boxTauDagGen volA A (boxWinModeReSmooth volA A χ p) Ψ y : ℝ) : ℂ)
          + Complex.I * ((boxTauDagGen volA A (boxWinModeImSmooth volA A χ p) Ψ y : ℝ) : ℂ) := by
    rw [boxTauDagGenC_modeC_eq_smooth volA A χ p (fun y => (Ψ y : ℂ)),
      show boxWinModeCSmooth volA A χ p
          = fun z => (boxWinModeReSmooth volA A χ p z : ℂ)
              + Complex.I * (boxWinModeImSmooth volA A χ p z : ℂ) from
        funext fun z => boxWinModeCSmooth_eq volA A hχc hχs p z]
    exact boxTauDagGenC_mode_ofReal (volA := volA) (A := A) (f := boxWinModeReSmooth volA A χ p)
      (g := boxWinModeImSmooth volA A χ p) (Φ := Ψ)
  have hstarMode : ∀ Φ : X (N + 2) → ℂ,
      boxTauDagGenC volA A (fun z => star (boxWinModeC volA A χ p z)) Φ
      = boxTauDagGenC volA A (fun z => (boxWinModeReSmooth volA A χ p z : ℂ)
          + Complex.I * ((-1 : ℂ) * (boxWinModeImSmooth volA A χ p z : ℂ))) Φ := by
    intro Φ
    rw [boxTauDagGenC_star_modeC_eq volA A hχc hχs]
    refine boxTauDagGenC_congr_mode volA A (fun z => ?_) Φ
    show (boxWinModeReSmooth volA A χ p z : ℂ)
        - Complex.I * (boxWinModeImSmooth volA A χ p z : ℂ)
      = (boxWinModeReSmooth volA A χ p z : ℂ)
        + Complex.I * ((-1 : ℂ) * (boxWinModeImSmooth volA A χ p z : ℂ))
    ring
  -- the mode split: D_m = D_{uℂ} + (I·(-1)) • D_{vℂ}
  have hsplit : ∀ (W : X (N + 2) → ℝ),
      boxTauDagGenC volA A (fun z => (boxWinModeReSmooth volA A χ p z : ℂ)
          + Complex.I * ((-1 : ℂ) * (boxWinModeImSmooth volA A χ p z : ℂ)))
        (fun y => (W y : ℂ))
      = fun x : X (N + 2) => ((boxTauDagGen volA A (boxWinModeReSmooth volA A χ p) W x : ℝ) : ℂ)
          + (Complex.I * (-1)) * ((boxTauDagGen volA A (boxWinModeImSmooth volA A χ p) W x : ℝ) : ℂ) := by
    intro W
    have h1 : boxTauDagGenC volA A (fun z => (boxWinModeReSmooth volA A χ p z : ℂ)
          + Complex.I * ((-1 : ℂ) * (boxWinModeImSmooth volA A χ p z : ℂ))) (fun y => (W y : ℂ))
        = boxTauDagGenC volA A (fun z => (boxWinModeReSmooth volA A χ p z : ℂ)) (fun y => (W y : ℂ))
          + boxTauDagGenC volA A (fun z => Complex.I * ((-1 : ℂ) * (boxWinModeImSmooth volA A χ p z : ℂ)))
              (fun y => (W y : ℂ)) :=
      boxTauDagGenC_add_mode volA A _ _ _
    have h2 : boxTauDagGenC volA A (fun z => (boxWinModeReSmooth volA A χ p z : ℂ))
          (fun y => (W y : ℂ))
        = fun x : X (N + 2) => ((boxTauDagGen volA A (boxWinModeReSmooth volA A χ p) W x : ℝ) : ℂ) :=
      boxTauDagGenC_ofReal_state volA A
    have h3 : boxTauDagGenC volA A
          (fun z => Complex.I * ((-1 : ℂ) * (boxWinModeImSmooth volA A χ p z : ℂ)))
          (fun y => (W y : ℂ))
        = Complex.I • boxTauDagGenC volA A
            (fun z => (-1 : ℂ) * (boxWinModeImSmooth volA A χ p z : ℂ)) (fun y => (W y : ℂ)) :=
      boxTauDagGenC_smul_mode volA A Complex.I _ _
    have h4 : boxTauDagGenC volA A
          (fun z => (-1 : ℂ) * (boxWinModeImSmooth volA A χ p z : ℂ)) (fun y => (W y : ℂ))
        = (-1 : ℂ) • boxTauDagGenC volA A (fun z => (boxWinModeImSmooth volA A χ p z : ℂ))
            (fun y => (W y : ℂ)) :=
      boxTauDagGenC_smul_mode volA A (-1) _ _
    have h5 : boxTauDagGenC volA A (fun z => (boxWinModeImSmooth volA A χ p z : ℂ))
          (fun y => (W y : ℂ))
        = fun x : X (N + 2) => ((boxTauDagGen volA A (boxWinModeImSmooth volA A χ p) W x : ℝ) : ℂ) :=
      boxTauDagGenC_ofReal_state volA A
    rw [h1, h2, h3, h4, h5]
    funext y
    show ((boxTauDagGen volA A (boxWinModeReSmooth volA A χ p) W y : ℝ) : ℂ)
        + Complex.I * ((-1 : ℂ) * ((boxTauDagGen volA A (boxWinModeImSmooth volA A χ p) W y : ℝ) : ℂ))
      = ((boxTauDagGen volA A (boxWinModeReSmooth volA A χ p) W y : ℝ) : ℂ)
        + (Complex.I * (-1)) * ((boxTauDagGen volA A (boxWinModeImSmooth volA A χ p) W y : ℝ) : ℂ)
    ring
  -- the state linearity
  have hst : boxTauDagGenC volA A (fun z => (boxWinModeReSmooth volA A χ p z : ℂ)
        + Complex.I * ((-1 : ℂ) * (boxWinModeImSmooth volA A χ p z : ℂ)))
      (fun y => ((boxTauDagGen volA A (boxWinModeReSmooth volA A χ p) Ψ y : ℝ) : ℂ)
        + Complex.I * ((boxTauDagGen volA A (boxWinModeImSmooth volA A χ p) Ψ y : ℝ) : ℂ)) x
      = boxTauDagGenC volA A (fun z => (boxWinModeReSmooth volA A χ p z : ℂ)
            + Complex.I * ((-1 : ℂ) * (boxWinModeImSmooth volA A χ p z : ℂ)))
          (fun y => ((boxTauDagGen volA A (boxWinModeReSmooth volA A χ p) Ψ y : ℝ) : ℂ)) x
        + Complex.I * boxTauDagGenC volA A (fun z => (boxWinModeReSmooth volA A χ p z : ℂ)
            + Complex.I * ((-1 : ℂ) * (boxWinModeImSmooth volA A χ p z : ℂ)))
          (fun y => ((boxTauDagGen volA A (boxWinModeImSmooth volA A χ p) Ψ y : ℝ) : ℂ)) x :=
    boxTauDagGenC_state_add_I (volA := volA) (A := A) hA hℓ hAc
      (m := fun z => (boxWinModeReSmooth volA A χ p z : ℂ)
        + Complex.I * ((-1 : ℂ) * (boxWinModeImSmooth volA A χ p z : ℂ)))
      hWm hWb hZm hZb x hx
  rw [hmodeC, hstarMode, hst,
    congrFun (hsplit (boxTauDagGen volA A (boxWinModeReSmooth volA A χ p) Ψ)) x,
    congrFun (hsplit (boxTauDagGen volA A (boxWinModeImSmooth volA A χ p) Ψ)) x,
    hcomm x hx]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring




/-! ## Measurability and box-boundedness of `boxTauDagGen` -/

lemma boxTauDagGen_measurable_bound {N : ℕ} {ℓ : ℝ} {A : Set E3} (hA : MeasurableSet A)
    (hℓ : 0 < ℓ) (hAc : A ⊆ acube ℓ) (volA : ℝ)
    {u : E3 → ℝ} (hu : Continuous u) {Cu : ℝ} (hub : ∀ z ∈ acube ℓ, |u z| ≤ Cu)
    {W : X (N + 2) → ℝ} (hWm : Measurable W) {CW : ℝ}
    (hWb : ∀ x ∈ abox (N + 2) ℓ, |W x| ≤ CW) :
    Measurable (boxTauDagGen volA A u W) ∧
      ∃ C : ℝ, ∀ x ∈ abox (N + 2) ℓ, |boxTauDagGen volA A u W x| ≤ C := by
  constructor
  · rw [boxTauDagGen_eq_boxOpG]
    unfold boxOpG
    refine Measurable.const_mul ?_ _
    refine Finset.measurable_sum _ (fun i _ => ?_)
    have h1 : Measurable (fun x : X (N + 2) => A.indicator (fun _ => (1 : ℝ)) (x i)) :=
      (measurable_const.indicator hA).comp (measurable_pi_apply i)
    have h2 : Measurable (fun x : X (N + 2) =>
        u (x i) * ∫ z in A, (fun _ => (1 : ℝ)) z * W (Function.update x i z)) :=
      measurable_slotZ (N := N + 1) hA (f := fun _ => (1 : ℝ)) continuous_const hu hWm i
    convert h1.mul h2 using 1
    funext x
    simp only [Pi.mul_apply]
    ring
  · have hAfin : (volume : Measure E3) A < ⊤ := Work.BoseFixB1S.volume_A_lt_top hℓ hAc
    refine ⟨|(Real.sqrt volA)⁻¹| *
      ((N + 2 : ℝ) * (max Cu 0 * (max CW 0 * (volume A).toReal))), fun x hx => ?_⟩
    have hterm : ∀ i : Fin (N + 2),
        |A.indicator (fun _ => (1 : ℝ)) (x i) * u (x i)
            * ∫ z in A, W (Function.update x i z)|
          ≤ max Cu 0 * (max CW 0 * (volume A).toReal) := by
      intro i
      have h1 : |A.indicator (fun _ => (1 : ℝ)) (x i) * u (x i)| ≤ max Cu 0 := by
        by_cases hxi : x i ∈ A
        · rw [Set.indicator_of_mem hxi, one_mul]
          exact le_trans (hub (x i) (hAc hxi)) (le_max_left _ _)
        · rw [Set.indicator_of_notMem hxi, zero_mul, abs_zero]
          exact le_max_right _ _
      have h2 : |∫ z in A, W (Function.update x i z)| ≤ max CW 0 * (volume A).toReal := by
        have hb : ∀ z ∈ A, ‖W (Function.update x i z)‖ ≤ max CW 0 := by
          intro z hz
          rw [Real.norm_eq_abs]
          have hmem : Function.update x i z ∈ abox (N + 2) ℓ := by
            intro j; rw [Function.update_apply]
            by_cases hj : j = i
            · rw [if_pos hj]; exact hAc hz
            · rw [if_neg hj]; exact hx j
          exact le_trans (hWb _ hmem) (le_max_left _ _)
        have hbnd := norm_setIntegral_le_of_norm_le_const hAfin hb
        simpa [MeasureTheory.Measure.real, Real.norm_eq_abs] using hbnd
      rw [abs_mul]
      exact mul_le_mul h1 h2 (abs_nonneg _) (le_max_right _ _)
    have hdef : boxTauDagGen volA A u W x
        = (Real.sqrt volA)⁻¹ * ∑ i : Fin (N + 2),
            A.indicator (fun _ => (1 : ℝ)) (x i) * u (x i)
              * ∫ z in A, W (Function.update x i z) := rfl
    rw [hdef, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    calc |∑ i : Fin (N + 2), A.indicator (fun _ => (1 : ℝ)) (x i) * u (x i)
            * ∫ z in A, W (Function.update x i z)|
        ≤ ∑ i : Fin (N + 2), |A.indicator (fun _ => (1 : ℝ)) (x i) * u (x i)
            * ∫ z in A, W (Function.update x i z)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin (N + 2), (max Cu 0 * (max CW 0 * (volume A).toReal)) :=
          Finset.sum_le_sum (fun i _ => hterm i)
      _ = (N + 2 : ℝ) * (max Cu 0 * (max CW 0 * (volume A).toReal)) := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

lemma integral_boxWinModeReSmooth_eq_zero {ℓ volA : ℝ} {A : Set E3} (hℓ : 0 < ℓ)
    (hAc : A ⊆ acube ℓ) (hvolA : volA = (volume A).toReal) (hvolpos : 0 < volA)
    {χ : E3 → ℝ} (hχc : Continuous χ) (hχs : HasCompactSupport χ) (p : E3) :
    ∫ z in A, boxWinModeReSmooth volA A χ p z = 0 := by
  haveI : IsFiniteMeasure (volume.restrict A) :=
    ⟨by simpa using Work.BoseFixB1S.volume_A_lt_top hℓ hAc⟩
  have hint : IntegrableOn (fun z => χ z * Real.cos (inner ℝ p z)) A volume :=
    ((hχc.mul (Real.continuous_cos.comp (continuous_const.inner continuous_id))).integrable_of_hasCompactSupport
      (hχs.mul_right (f' := fun z => Real.cos (inner ℝ p z)))).integrableOn
  rw [show (∫ z in A, boxWinModeReSmooth volA A χ p z)
      = ∫ z in A, (χ z * Real.cos (inner ℝ p z)
          - volA⁻¹ * ∫ w in A, χ w * Real.cos (inner ℝ p w)) from rfl]
  rw [integral_sub hint (integrable_const _)]
  have hc : (∫ z in A, volA⁻¹ * ∫ w in A, χ w * Real.cos (inner ℝ p w))
      = ∫ w in A, χ w * Real.cos (inner ℝ p w) := by
    have hv : volA ≠ 0 := hvolpos.ne'
    rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def, smul_eq_mul, ← hvolA]
    field_simp
  rw [hc, sub_self]

lemma integral_boxWinModeImSmooth_eq_zero {ℓ volA : ℝ} {A : Set E3} (hℓ : 0 < ℓ)
    (hAc : A ⊆ acube ℓ) (hvolA : volA = (volume A).toReal) (hvolpos : 0 < volA)
    {χ : E3 → ℝ} (hχc : Continuous χ) (hχs : HasCompactSupport χ) (p : E3) :
    ∫ z in A, boxWinModeImSmooth volA A χ p z = 0 := by
  haveI : IsFiniteMeasure (volume.restrict A) :=
    ⟨by simpa using Work.BoseFixB1S.volume_A_lt_top hℓ hAc⟩
  have hint : IntegrableOn (fun z => χ z * Real.sin (inner ℝ p z)) A volume :=
    ((hχc.mul (Real.continuous_sin.comp (continuous_const.inner continuous_id))).integrable_of_hasCompactSupport
      (hχs.mul_right (f' := fun z => Real.sin (inner ℝ p z)))).integrableOn
  rw [show (∫ z in A, boxWinModeImSmooth volA A χ p z)
      = ∫ z in A, - (χ z * Real.sin (inner ℝ p z)
          - volA⁻¹ * ∫ w in A, χ w * Real.sin (inner ℝ p w)) from rfl]
  rw [integral_neg, integral_sub hint (integrable_const _)]
  have hc : (∫ z in A, volA⁻¹ * ∫ w in A, χ w * Real.sin (inner ℝ p w))
      = ∫ w in A, χ w * Real.sin (inner ℝ p w) := by
    have hv : volA ≠ 0 := hvolpos.ne'
    rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def, smul_eq_mul, ← hvolA]
    field_simp
  rw [hc, sub_self, neg_zero]

lemma integrableOn_createdSlot_meas {n : ℕ} {a : ℝ} (ha : 0 < a)
    {A : Set E3} (hAm : MeasurableSet A) (hAc : A ⊆ acube a)
    {f : E3 → ℝ} (hf : Continuous f)
    {Φ : X (n + 1) → ℝ} (hΦm : Measurable Φ) {CΦ : ℝ}
    (hΦb : ∀ x ∈ abox (n + 1) a, |Φ x| ≤ CΦ)
    {Ψ : X (n + 1) → ℝ} (hΨm : Measurable Ψ) {CΨ : ℝ}
    (hΨb : ∀ x ∈ abox (n + 1) a, |Ψ x| ≤ CΨ) (i : Fin (n + 1)) :
    IntegrableOn (fun x : X (n + 1) =>
        A.indicator (fun _ => (1 : ℝ)) (x i) * f (x i) * Φ x
          * (∫ z in A, Ψ (Function.update x i z)))
      (abox (n + 1) a) volume := by
  obtain ⟨Mf, hMf⟩ := (acube_compact ha).exists_bound_of_continuousOn hf.continuousOn
  have hAfin : (volume : Measure E3) A < ⊤ := Work.BoseFixB1S.volume_A_lt_top ha hAc
  have hvol0 : 0 ≤ ((volume : Measure E3) A).toReal := ENNReal.toReal_nonneg
  refine IntegrableOn.of_bound (abox_lt_top (n + 1) a ha.le) ?_
    (|Mf| * (|CΦ| * (|CΨ| * |((volume : Measure E3) A).toReal|))) ?_
  · have h1 : Measurable (fun x : X (n + 1) => A.indicator (fun _ => (1 : ℝ)) (x i)) :=
      (measurable_const.indicator hAm).comp (measurable_pi_apply i)
    have h2 : Measurable (fun x : X (n + 1) => f (x i)) :=
      hf.measurable.comp (measurable_pi_apply i)
    have h3 : Measurable (fun x : X (n + 1) => ∫ z in A, Ψ (Function.update x i z)) :=
      Work.BoseFixB1S.measurable_fibreMean A hAm i hΨm
    exact (((h1.mul h2).mul hΦm).mul h3).aestronglyMeasurable
  · rw [ae_restrict_iff' (abox_measurable (n + 1) a)]
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    rw [Real.norm_eq_abs]
    simp only [abs_mul]
    have hInd : |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := by
      by_cases hxi : x i ∈ A <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hxi]
    have hfbound : |f (x i)| ≤ |Mf| :=
      le_trans (by simpa only [Real.norm_eq_abs] using hMf (x i) (hx i)) (le_abs_self Mf)
    have hΦbound : |Φ x| ≤ |CΦ| := le_trans (hΦb x hx) (le_abs_self CΦ)
    have hInner : |∫ z in A, Ψ (Function.update x i z)| ≤ |CΨ| * |((volume : Measure E3) A).toReal| := by
      have h1 : ‖∫ z in A, Ψ (Function.update x i z)‖ ≤ CΨ * (((volume : Measure E3) A).toReal) := by
        refine norm_setIntegral_le_of_norm_le_const hAfin ?_
        intro z hz
        have h := hΨb (Function.update x i z) (boxOpG_one_update_mem_abox hAc hx i hz)
        simpa only [Real.norm_eq_abs] using h
      rw [Real.norm_eq_abs] at h1
      refine le_trans h1 ?_
      rw [abs_of_nonneg hvol0]
      exact mul_le_mul_of_nonneg_right (le_abs_self CΨ) hvol0
    calc |A.indicator (fun _ => (1 : ℝ)) (x i)| * |f (x i)| * |Φ x|
          * |∫ z in A, Ψ (Function.update x i z)|
        ≤ 1 * |Mf| * |CΦ| * (|CΨ| * |((volume : Measure E3) A).toReal|) := by
          refine mul_le_mul (mul_le_mul (mul_le_mul hInd hfbound (abs_nonneg _) (by norm_num))
            hΦbound (abs_nonneg _) (by positivity)) hInner (abs_nonneg _) (by positivity)
      _ = |Mf| * (|CΦ| * (|CΨ| * |((volume : Measure E3) A).toReal|)) := by ring

lemma integrableOn_integratedSlot_meas {n : ℕ} {a : ℝ} (ha : 0 < a)
    {A : Set E3} (hAm : MeasurableSet A) (hAc : A ⊆ acube a)
    {f : E3 → ℝ} (hf : Continuous f)
    {Φ : X (n + 1) → ℝ} (hΦm : Measurable Φ) {CΦ : ℝ}
    (hΦb : ∀ x ∈ abox (n + 1) a, |Φ x| ≤ CΦ)
    {Ψ : X (n + 1) → ℝ} (hΨm : Measurable Ψ) {CΨ : ℝ}
    (hΨb : ∀ x ∈ abox (n + 1) a, |Ψ x| ≤ CΨ) (i : Fin (n + 1)) :
    IntegrableOn (fun x : X (n + 1) =>
        A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x
          * (∫ z in A, f z * Φ (Function.update x i z)))
      (abox (n + 1) a) volume := by
  obtain ⟨Mf, hMf⟩ := (acube_compact ha).exists_bound_of_continuousOn hf.continuousOn
  have hAfin : (volume : Measure E3) A < ⊤ := Work.BoseFixB1S.volume_A_lt_top ha hAc
  have hvol0 : 0 ≤ ((volume : Measure E3) A).toReal := ENNReal.toReal_nonneg
  refine IntegrableOn.of_bound (abox_lt_top (n + 1) a ha.le) ?_
    (|CΨ| * (|Mf| * (|CΦ| * |((volume : Measure E3) A).toReal|))) ?_
  · have h1 : Measurable (fun x : X (n + 1) => A.indicator (fun _ => (1 : ℝ)) (x i)) :=
      (measurable_const.indicator hAm).comp (measurable_pi_apply i)
    have hinner : Measurable (fun x : X (n + 1) =>
        ∫ z in A, f z * Φ (Function.update x i z)) := by
      have h := Work.BoseFixB1S.measurable_fibreMean A hAm i
        (Ψ := fun y : X (n + 1) => f (y i) * Φ y)
        ((hf.measurable.comp (measurable_pi_apply i)).mul hΦm)
      have hfun : (fun x : X (n + 1) =>
            ∫ z in A, f ((Function.update x i z) i) * Φ (Function.update x i z))
          = fun x : X (n + 1) => ∫ z in A, f z * Φ (Function.update x i z) := by
        funext x
        apply integral_congr_ae
        filter_upwards with z
        rw [Function.update_self]
      rwa [hfun] at h
    exact ((h1.mul hΨm).mul hinner).aestronglyMeasurable
  · rw [ae_restrict_iff' (abox_measurable (n + 1) a)]
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    rw [Real.norm_eq_abs]
    simp only [abs_mul]
    have hInd : |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := by
      by_cases hxi : x i ∈ A <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hxi]
    have hΨbound : |Ψ x| ≤ |CΨ| := le_trans (hΨb x hx) (le_abs_self CΨ)
    have hInner : |∫ z in A, f z * Φ (Function.update x i z)|
        ≤ |Mf| * (|CΦ| * |((volume : Measure E3) A).toReal|) := by
      have h1 : ‖∫ z in A, f z * Φ (Function.update x i z)‖
          ≤ (|Mf| * |CΦ|) * (((volume : Measure E3) A).toReal) := by
        refine norm_setIntegral_le_of_norm_le_const hAfin (C := |Mf| * |CΦ|) ?_
        intro z hz
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul
          (le_trans (by simpa only [Real.norm_eq_abs] using hMf z (hAc hz)) (le_abs_self Mf))
          (le_trans (hΦb (Function.update x i z) (boxOpG_one_update_mem_abox hAc hx i hz))
            (le_abs_self CΦ))
          (abs_nonneg (Φ (Function.update x i z))) (abs_nonneg Mf)
      rw [Real.norm_eq_abs] at h1
      refine le_trans h1 ?_
      rw [abs_of_nonneg hvol0]
      exact le_of_eq (mul_assoc _ _ _)
    calc |A.indicator (fun _ => (1 : ℝ)) (x i)| * |Ψ x|
          * |∫ z in A, f z * Φ (Function.update x i z)|
        ≤ 1 * |CΨ| * (|Mf| * (|CΦ| * |((volume : Measure E3) A).toReal|)) := by
          refine mul_le_mul (mul_le_mul hInd hΨbound (abs_nonneg _) (by norm_num)) hInner
            (abs_nonneg _) (by positivity)
      _ = |CΨ| * (|Mf| * (|CΦ| * |((volume : Measure E3) A).toReal|)) := by ring

theorem boxOpG_adjoint_meas {N : ℕ} {a : ℝ} (ha : 0 < a)
    {A : Set E3} (hAm : MeasurableSet A) (hAc : A ⊆ acube a)
    {f : E3 → ℝ} (hf : Continuous f)
    {Φ : X (N + 1) → ℝ} (hΦm : Measurable Φ) {CΦ : ℝ}
    (hΦb : ∀ x ∈ abox (N + 1) a, |Φ x| ≤ CΦ)
    {Ψ : X (N + 1) → ℝ} (hΨm : Measurable Ψ) {CΨ : ℝ}
    (hΨb : ∀ x ∈ abox (N + 1) a, |Ψ x| ≤ CΨ) :
    ∫ x in abox (N + 1) a, Φ x * boxOpG A f (fun _ => (1 : ℝ)) Ψ x
      = ∫ x in abox (N + 1) a, boxOpG A (fun _ => (1 : ℝ)) f Φ x * Ψ x := by
  have hLint : ∀ i : Fin (N + 1), IntegrableOn
      (fun x : X (N + 1) => A.indicator (fun _ => (1 : ℝ)) (x i) * f (x i) * Φ x
          * (∫ z in A, Ψ (Function.update x i z))) (abox (N + 1) a) volume :=
    fun i => integrableOn_createdSlot_meas ha hAm hAc hf hΦm hΦb hΨm hΨb i
  have hRint : ∀ i : Fin (N + 1), IntegrableOn
      (fun x : X (N + 1) => A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x
          * (∫ z in A, f z * Φ (Function.update x i z))) (abox (N + 1) a) volume :=
    fun i => integrableOn_integratedSlot_meas ha hAm hAc hf hΦm hΦb hΨm hΨb i
  have hL : (∫ x in abox (N + 1) a, Φ x * boxOpG A f (fun _ => (1 : ℝ)) Ψ x)
      = ∑ i : Fin (N + 1), ∫ r in abox N a,
          (∫ y in A, f y * Φ (kcInsN N i (y, r))) * (∫ z in A, Ψ (kcInsN N i (z, r))) := by
    have hpt : (fun x : X (N + 1) => Φ x * boxOpG A f (fun _ => (1 : ℝ)) Ψ x)
        = fun x : X (N + 1) => ∑ i : Fin (N + 1),
            (A.indicator (fun _ => (1 : ℝ)) (x i) * f (x i) * Φ x
              * (∫ z in A, Ψ (Function.update x i z))) := by
      funext x
      rw [boxOpG]
      have hinner : ∀ i : Fin (N + 1),
          (∫ z in A, (fun _ => (1 : ℝ)) z * Ψ (Function.update x i z))
            = ∫ z in A, Ψ (Function.update x i z) := by
        intro i
        apply integral_congr_ae
        filter_upwards with z
        simp
      simp only [hinner]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    rw [hpt]
    rw [MeasureTheory.integral_finsetSum (s := Finset.univ)
      (f := fun (i : Fin (N + 1)) (x : X (N + 1)) =>
        A.indicator (fun _ => (1 : ℝ)) (x i) * f (x i) * Φ x
          * (∫ z in A, Ψ (Function.update x i z))) (fun i _ => hLint i)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact boxOpG_one_peel_createdSlot hAm hAc i (hLint i)
  have hR : (∫ x in abox (N + 1) a, boxOpG A (fun _ => (1 : ℝ)) f Φ x * Ψ x)
      = ∑ i : Fin (N + 1), ∫ r in abox N a,
          (∫ y in A, Ψ (kcInsN N i (y, r))) * (∫ z in A, f z * Φ (kcInsN N i (z, r))) := by
    have hpt : (fun x : X (N + 1) => boxOpG A (fun _ => (1 : ℝ)) f Φ x * Ψ x)
        = fun x : X (N + 1) => ∑ i : Fin (N + 1),
            (A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x
              * (∫ z in A, f z * Φ (Function.update x i z))) := by
      funext x
      rw [boxOpG, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [mul_one]
      ring
    rw [hpt]
    rw [MeasureTheory.integral_finsetSum (s := Finset.univ)
      (f := fun (i : Fin (N + 1)) (x : X (N + 1)) =>
        A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x
          * (∫ z in A, f z * Φ (Function.update x i z))) (fun i _ => hRint i)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact boxOpG_one_peel_integratedSlot hAm hAc i (hRint i)
  rw [hL, hR]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  apply integral_congr_ae
  filter_upwards with r
  exact mul_comm _ _

end Work.BoseFixB1

namespace Work.BoseFixB1
open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal
open _root_.BoseGases Submission.BoseGases
set_option autoImplicit false
set_option maxHeartbeats 4000000
local notation "E3" => EuclideanSpace ℝ (Fin 3)

lemma boxOpG_smul_state {M : ℕ} (c : ℝ) (A : Set E3) (f h : E3 → ℝ) (Φ : X M → ℝ) :
    boxOpG A f h (c • Φ) = c • boxOpG A f h Φ := by
  funext x
  unfold boxOpG
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [show (∫ z in A, h z * (c * Φ (Function.update x i z)))
      = c * ∫ z in A, h z * Φ (Function.update x i z) from by
    rw [show (fun z => h z * (c * Φ (Function.update x i z)))
        = fun z => c * (h z * Φ (Function.update x i z)) from by funext z; ring]
    rw [integral_const_mul]]
  ring

lemma boxTauDagGen_pairing_integral {N : ℕ} {ℓ volA : ℝ} {A : Set E3} (hA : MeasurableSet A)
    (hℓ : 0 < ℓ) (hAc : A ⊆ acube ℓ) (hvolpos : 0 < volA)
    {u : E3 → ℝ} (hu : Continuous u) {Ψ : X (N + 2) → ℝ} (hΨ : Continuous Ψ) :
    (∫ x in abox (N + 2) ℓ, Ψ x * boxTauDagGen volA A u (boxTauDagGen volA A u Ψ) x)
      = boxModeRGen ℓ volA A u Ψ := by
  have hspos : 0 < Real.sqrt volA := Real.sqrt_pos_of_pos hvolpos
  obtain ⟨Cu, hCu⟩ := (acube_compact hℓ).exists_bound_of_continuousOn hu.continuousOn
  have hub : ∀ z ∈ acube ℓ, |u z| ≤ Cu := fun z hz => by
    rw [← Real.norm_eq_abs]; exact hCu z hz
  have hΨm : Measurable Ψ := hΨ.measurable
  obtain ⟨CΨ, hΨb⟩ := (abox_compact (N + 2) hℓ).exists_bound_of_continuousOn hΨ.continuousOn
  have hΨbn : ∀ x ∈ abox (N + 2) ℓ, |Ψ x| ≤ CΨ := fun x hx => by
    rw [← Real.norm_eq_abs]; exact hΨb x hx
  obtain ⟨hYm, CY, hYb⟩ := boxTauDagGen_measurable_bound hA hℓ hAc volA hu hub hΨm hΨbn
  -- the creation operator is `(√volA)⁻¹` times a `boxOpG`
  have hYscaled : boxTauDagGen volA A u Ψ
      = (Real.sqrt volA)⁻¹ • boxOpG A u (fun _ => (1 : ℝ)) Ψ := by
    rw [boxTauDagGen_eq_boxOpG]
    funext x
    rfl
  -- step 1: the pointwise reduction of the left integrand
  have hpt : ∀ x : X (N + 2),
      Ψ x * boxTauDagGen volA A u (boxTauDagGen volA A u Ψ) x
        = ((Real.sqrt volA)⁻¹ * (Real.sqrt volA)⁻¹) *
            (Ψ x * boxOpG A u (fun _ => (1 : ℝ)) (boxOpG A u (fun _ => (1 : ℝ)) Ψ) x) := by
    intro x
    have h1 : boxTauDagGen volA A u (boxTauDagGen volA A u Ψ) x
        = (Real.sqrt volA)⁻¹ * boxOpG A u (fun _ => (1 : ℝ)) (boxTauDagGen volA A u Ψ) x :=
      congrFun (boxTauDagGen_eq_boxOpG volA A u (boxTauDagGen volA A u Ψ)) x
    have h2 : boxOpG A u (fun _ => (1 : ℝ)) (boxTauDagGen volA A u Ψ)
        = (Real.sqrt volA)⁻¹ • boxOpG A u (fun _ => (1 : ℝ))
            (boxOpG A u (fun _ => (1 : ℝ)) Ψ) := by
      rw [hYscaled]
      exact boxOpG_smul_state _ A _ _ _
    rw [h1, congrFun h2 x]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  -- step 2: adjointness with the merely measurable state `boxOpG A u 1 Ψ`
  have hZm : Measurable (boxOpG A u (fun _ => (1 : ℝ)) Ψ) := by
    have h1 : Measurable (fun x : X (N + 2) =>
        (Real.sqrt volA)⁻¹ * boxOpG A u (fun _ => (1 : ℝ)) Ψ x) := by
      rw [← boxTauDagGen_eq_boxOpG volA A u Ψ]
      exact hYm
    have h2 : boxOpG A u (fun _ => (1 : ℝ)) Ψ
        = fun x => ((Real.sqrt volA)⁻¹)⁻¹ *
            ((Real.sqrt volA)⁻¹ * boxOpG A u (fun _ => (1 : ℝ)) Ψ x) := by
      funext x
      rw [← mul_assoc, inv_mul_cancel₀ (inv_ne_zero (ne_of_gt hspos)), one_mul]
    rw [h2]
    exact h1.const_mul ((Real.sqrt volA)⁻¹)⁻¹
  have hZb : ∀ x ∈ abox (N + 2) ℓ,
      |boxOpG A u (fun _ => (1 : ℝ)) Ψ x| ≤ Real.sqrt volA * CY := by
    intro x hx
    have h := hYb x hx
    rw [boxTauDagGen_eq_boxOpG] at h
    have h2 : (Real.sqrt volA)⁻¹ * |boxOpG A u (fun _ => (1 : ℝ)) Ψ x| ≤ CY := by
      have h' : |(Real.sqrt volA)⁻¹| * |boxOpG A u (fun _ => (1 : ℝ)) Ψ x| ≤ CY := by
        rwa [abs_mul] at h
      rwa [abs_of_pos (inv_pos.mpr hspos)] at h'
    have h3 : Real.sqrt volA * ((Real.sqrt volA)⁻¹ * |boxOpG A u (fun _ => (1 : ℝ)) Ψ x|)
        ≤ Real.sqrt volA * CY := mul_le_mul_of_nonneg_left h2 hspos.le
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hspos), one_mul] at h3
    exact h3
  have hadj : (∫ x in abox (N + 2) ℓ, Ψ x * boxOpG A u (fun _ => (1 : ℝ))
        (boxOpG A u (fun _ => (1 : ℝ)) Ψ) x)
      = ∫ x in abox (N + 2) ℓ, boxOpG A (fun _ => (1 : ℝ)) u Ψ x
          * boxOpG A u (fun _ => (1 : ℝ)) Ψ x :=
    boxOpG_adjoint_meas hℓ hA hAc hu hΨm hΨbn hZm hZb
  -- step 3: the same normal form from the `boxModeRGen` side
  have hpt2 : ∀ x : X (N + 2),
      (Real.sqrt volA)⁻¹ * boxOpG A (fun _ => (1 : ℝ)) u Ψ x *
          ((Real.sqrt volA)⁻¹ * boxOpG A u (fun _ => (1 : ℝ)) Ψ x)
      = ((Real.sqrt volA)⁻¹ * (Real.sqrt volA)⁻¹) *
        (boxOpG A (fun _ => (1 : ℝ)) u Ψ x * boxOpG A u (fun _ => (1 : ℝ)) Ψ x) := by
    intro x
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
    hadj, boxModeRGen, boxTauAnnGen_eq_boxOpG, boxTauDagGen_eq_boxOpG,
    integral_congr_ae (Filter.Eventually.of_forall hpt2), integral_const_mul]

lemma boxOpG_eq_sum_slotOp {M : ℕ} (A : Set E3) (g : E3 → ℝ) (Φ : X M → ℝ) :
    boxOpG A g (fun _ => (1 : ℝ)) Φ
      = fun y => ∑ i : Fin M, A.indicator (fun _ => (1 : ℝ)) (y i) * g (y i)
          * ∫ z in A, Φ (Function.update y i z) := by
  funext y
  simp only [boxOpG]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  simp

/-- membership of double updates in the box -/
lemma update2_mem_abox {M : ℕ} {ℓ : ℝ} {A : Set E3} (hAc : A ⊆ acube ℓ)
    {x : X M} (hx : x ∈ abox M ℓ) {z w : E3} (hz : z ∈ A) (hw : w ∈ A)
    (i j : Fin M) : Function.update (Function.update x i z) j w ∈ abox M ℓ := by
  intro k
  rw [Function.update_apply, Function.update_apply]
  by_cases hkj : k = j
  · rw [if_pos hkj]; exact hAc hw
  · rw [if_neg hkj]
    by_cases hki : k = i
    · rw [if_pos hki]; exact hAc hz
    · rw [if_neg hki]; exact hx k

lemma integrableOn_slot_fibre {M : ℕ} {ℓ : ℝ} {A : Set E3} (hA : MeasurableSet A)
    (hℓ : 0 < ℓ) (hAc : A ⊆ acube ℓ) {v : E3 → ℝ} (hv : Continuous v) {Cv : ℝ}
    (hvb : ∀ z ∈ acube ℓ, |v z| ≤ Cv) {Ψ : X M → ℝ} (hΨ : Continuous Ψ) {CΨ : ℝ}
    (hΨb : ∀ y ∈ abox M ℓ, |Ψ y| ≤ CΨ) {x : X M} (hx : x ∈ abox M ℓ) (i j : Fin M) :
    IntegrableOn (fun z : E3 =>
        A.indicator (fun _ => (1 : ℝ)) ((Function.update x i z) j) * v ((Function.update x i z) j)
          * (∫ w in A, Ψ (Function.update (Function.update x i z) j w))) A volume := by
  have hAfin : (volume : Measure E3) A < ⊤ := Work.BoseFixB1S.volume_A_lt_top hℓ hAc
  have hvol0 : 0 ≤ ((volume : Measure E3) A).toReal := ENNReal.toReal_nonneg
  refine IntegrableOn.of_bound hAfin ?_ (max Cv 0 * (max CΨ 0 * ((volume : Measure E3) A).toReal)) ?_
  · have h1 : Measurable (fun z : E3 =>
        A.indicator (fun _ => (1 : ℝ)) ((Function.update x i z) j)) :=
      (measurable_const.indicator hA).comp (by fun_prop)
    have h2 : Measurable (fun z : E3 => v ((Function.update x i z) j)) :=
      hv.measurable.comp (by fun_prop)
    have h3 : Measurable (fun z : E3 =>
        ∫ w in A, Ψ (Function.update (Function.update x i z) j w)) :=
      (Work.BoseFixB1S.measurable_fibreMean A hA j hΨ.measurable).comp (by fun_prop)
    exact ((h1.mul h2).mul h3).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem hA] with z hz
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have h1 : |A.indicator (fun _ => (1 : ℝ)) ((Function.update x i z) j)| ≤ 1 := by
      by_cases h : (Function.update x i z) j ∈ A <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
    have h2 : |v ((Function.update x i z) j)| ≤ max Cv 0 := by
      refine le_trans (hvb _ ?_) (le_max_left _ _)
      rw [Function.update_apply]
      by_cases hji : j = i
      · rw [if_pos hji]; exact hAc hz
      · rw [if_neg hji]; exact hx j
    have h3 : |∫ w in A, Ψ (Function.update (Function.update x i z) j w)| ≤ max CΨ 0 * ((volume : Measure E3) A).toReal := by
      have hb : ∀ w ∈ A, ‖Ψ (Function.update (Function.update x i z) j w)‖ ≤ max CΨ 0 := by
        intro w hw
        rw [Real.norm_eq_abs]
        exact le_trans (hΨb _ (update2_mem_abox hAc hx hz hw i j)) (le_max_left _ _)
      have hbnd := norm_setIntegral_le_of_norm_le_const hAfin hb
      simpa [MeasureTheory.Measure.real, Real.norm_eq_abs] using hbnd
    calc |A.indicator (fun _ => (1 : ℝ)) ((Function.update x i z) j)|
            * |v ((Function.update x i z) j)|
            * |∫ w in A, Ψ (Function.update (Function.update x i z) j w)|
        ≤ 1 * max Cv 0 * (max CΨ 0 * ((volume : Measure E3) A).toReal) := by
          refine mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)) h3 (abs_nonneg _)
            (by positivity)
      _ = max Cv 0 * (max CΨ 0 * ((volume : Measure E3) A).toReal) := by ring


/-- The per-slot expansion: the `i`-th slot of `Y_v = boxOpG A v 1` applied to a state that is
itself a sum of slots.  The diagonal slot vanishes by mean-freeness of `v`, the off-diagonal slots
give the two-slot integrals. -/
lemma slot_inner_expansion {M : ℕ} {ℓ : ℝ} {A : Set E3} (hA : MeasurableSet A) (hℓ : 0 < ℓ)
    (hAc : A ⊆ acube ℓ) {v : E3 → ℝ} (hv : Continuous v) {Cv : ℝ}
    (hvb : ∀ z ∈ acube ℓ, |v z| ≤ Cv) (hvm : ∫ z in A, v z = 0)
    {Ψ : X M → ℝ} (hΨ : Continuous Ψ) {CΨ : ℝ}
    (hΨb : ∀ y ∈ abox M ℓ, |Ψ y| ≤ CΨ) {x : X M} (hx : x ∈ abox M ℓ) (i : Fin M) :
    (∫ z in A, (fun y : X M => ∑ j : Fin M, A.indicator (fun _ => (1 : ℝ)) (y j) * v (y j)
          * ∫ w in A, Ψ (Function.update y j w)) (Function.update x i z))
      = ∑ j ∈ Finset.univ.erase i, A.indicator (fun _ => (1 : ℝ)) (x j) * v (x j)
          * ∫ z in A, ∫ w in A, Ψ (Function.update (Function.update x i z) j w) := by
  rw [show (∫ z in A, (fun y : X M => ∑ j : Fin M, A.indicator (fun _ => (1 : ℝ)) (y j) * v (y j)
          * ∫ w in A, Ψ (Function.update y j w)) (Function.update x i z))
      = ∫ z in A, ∑ j : Fin M, A.indicator (fun _ => (1 : ℝ)) ((Function.update x i z) j)
          * v ((Function.update x i z) j)
          * ∫ w in A, Ψ (Function.update (Function.update x i z) j w) from rfl]
  rw [MeasureTheory.integral_finsetSum _ (fun j _ =>
    integrableOn_slot_fibre hA hℓ hAc hv hvb hΨ hΨb hx i j)]
  rw [(Finset.sum_erase_add _ _ (Finset.mem_univ i)).symm]
  -- the diagonal slot vanishes
  have hdiag : (∫ z in A, A.indicator (fun _ => (1 : ℝ)) ((Function.update x i z) i)
        * v ((Function.update x i z) i)
        * (∫ w in A, Ψ (Function.update (Function.update x i z) i w))) = 0 := by
    have hinner : (fun z : E3 => A.indicator (fun _ => (1 : ℝ)) ((Function.update x i z) i)
          * v ((Function.update x i z) i)
          * (∫ w in A, Ψ (Function.update (Function.update x i z) i w)))
        = fun z : E3 => (A.indicator (fun _ => (1 : ℝ)) z * v z)
          * (∫ w in A, Ψ (Function.update x i w)) := by
      funext z
      rw [Function.update_self]
      congr 1
      apply integral_congr_ae
      filter_upwards with w
      rw [update_update_same x i z w]
    rw [hinner, integral_mul_const]
    rw [show (∫ z in A, A.indicator (fun _ => (1 : ℝ)) z * v z) = ∫ z in A, v z from by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hA] with z hz
      rw [Set.indicator_of_mem hz, one_mul]]
    rw [hvm, zero_mul]
  rw [hdiag, add_zero]
  -- the off-diagonal slots
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  have hji' : i ≠ j := fun h => hji h.symm
  have hterm : (fun z : E3 => A.indicator (fun _ => (1 : ℝ)) ((Function.update x i z) j)
        * v ((Function.update x i z) j)
        * (∫ w in A, Ψ (Function.update (Function.update x i z) j w)))
      = fun z : E3 => (A.indicator (fun _ => (1 : ℝ)) (x j) * v (x j))
        * (∫ w in A, Ψ (Function.update (Function.update x i z) j w)) := by
    funext z
    rw [Function.update_apply, if_neg hji]
  rw [hterm, integral_const_mul]

/-- Fubini for the two-slot integral over `A`. -/
lemma pair_integral_swap_A {A : Set E3} {f : E3 → E3 → ℝ}
    (hf : Integrable (Function.uncurry f) ((volume.restrict A).prod (volume.restrict A))) :
    (∫ z in A, ∫ w in A, f z w) = ∫ w in A, ∫ z in A, f z w :=
  MeasureTheory.integral_integral_swap hf

/-- **The creation operators commute (on the box).** -/
lemma boxOpG_comm_cre_box {M : ℕ} {ℓ : ℝ} {A : Set E3} (hA : MeasurableSet A) (hℓ : 0 < ℓ)
    (hAc : A ⊆ acube ℓ) {u v : E3 → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hum : ∫ z in A, u z = 0) (hvm : ∫ z in A, v z = 0)
    {Ψ : X M → ℝ} (hΨ : Continuous Ψ) :
    ∀ x ∈ abox M ℓ, boxOpG A u (fun _ => (1 : ℝ)) (boxOpG A v (fun _ => (1 : ℝ)) Ψ) x
      = boxOpG A v (fun _ => (1 : ℝ)) (boxOpG A u (fun _ => (1 : ℝ)) Ψ) x := by
  intro x hx
  obtain ⟨Cu, hCu⟩ := (acube_compact hℓ).exists_bound_of_continuousOn hu.continuousOn
  obtain ⟨Cv, hCv⟩ := (acube_compact hℓ).exists_bound_of_continuousOn hv.continuousOn
  obtain ⟨CΨ, hCΨ⟩ := (abox_compact M hℓ).exists_bound_of_continuousOn hΨ.continuousOn
  have hub : ∀ z ∈ acube ℓ, |u z| ≤ Cu := fun z hz => by
    rw [← Real.norm_eq_abs]; exact hCu z hz
  have hvb : ∀ z ∈ acube ℓ, |v z| ≤ Cv := fun z hz => by
    rw [← Real.norm_eq_abs]; exact hCv z hz
  have hΨb : ∀ y ∈ abox M ℓ, |Ψ y| ≤ CΨ := fun y hy => by
    rw [← Real.norm_eq_abs]; exact hCΨ y hy
  have hL : boxOpG A u (fun _ => (1 : ℝ)) (boxOpG A v (fun _ => (1 : ℝ)) Ψ) x
      = ∑ i : Fin M, A.indicator (fun _ => (1 : ℝ)) (x i) * u (x i)
          * (∑ j ∈ Finset.univ.erase i, A.indicator (fun _ => (1 : ℝ)) (x j) * v (x j)
              * ∫ z in A, ∫ w in A, Ψ (Function.update (Function.update x i z) j w)) := by
    rw [boxOpG_eq_sum_slotOp A u (boxOpG A v (fun _ => (1 : ℝ)) Ψ),
      boxOpG_eq_sum_slotOp A v Ψ]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    congr 1
    exact slot_inner_expansion hA hℓ hAc hv hvb hvm hΨ hΨb hx i
  have hR : boxOpG A v (fun _ => (1 : ℝ)) (boxOpG A u (fun _ => (1 : ℝ)) Ψ) x
      = ∑ i : Fin M, A.indicator (fun _ => (1 : ℝ)) (x i) * v (x i)
          * (∑ j ∈ Finset.univ.erase i, A.indicator (fun _ => (1 : ℝ)) (x j) * u (x j)
              * ∫ z in A, ∫ w in A, Ψ (Function.update (Function.update x i z) j w)) := by
    rw [boxOpG_eq_sum_slotOp A v (boxOpG A u (fun _ => (1 : ℝ)) Ψ),
      boxOpG_eq_sum_slotOp A u Ψ]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    congr 1
    exact slot_inner_expansion hA hℓ hAc hu hub hum hΨ hΨb hx i
  -- the two-slot integrals are symmetric (Fubini)
  have hI : ∀ i j : Fin M, i ≠ j →
      (∫ z in A, ∫ w in A, Ψ (Function.update (Function.update x i z) j w))
        = ∫ z in A, ∫ w in A, Ψ (Function.update (Function.update x j z) i w) := by
    intro i j hij
    have hint2 : Integrable (Function.uncurry (fun z w : E3 =>
        Ψ (Function.update (Function.update x i z) j w)))
        ((volume.restrict A).prod (volume.restrict A)) := by
      have hAfin : (volume : Measure E3) A < ⊤ := Work.BoseFixB1S.volume_A_lt_top hℓ hAc
      haveI : IsFiniteMeasure (((volume : Measure E3).restrict A).prod
          ((volume : Measure E3).restrict A)) := by
        constructor
        rw [Measure.prod_restrict, Measure.restrict_apply_univ, Measure.prod_prod]
        exact ENNReal.mul_lt_top hAfin hAfin
      refine Integrable.of_bound ?_ (max CΨ 0) ?_
      · exact (hΨ.measurable.comp (by fun_prop)).aestronglyMeasurable
      · rw [Measure.prod_restrict]
        filter_upwards [MeasureTheory.ae_restrict_mem (hA.prod hA)] with p hp
        rw [Real.norm_eq_abs]
        exact le_trans (hΨb _ (update2_mem_abox hAc hx hp.1 hp.2 i j)) (le_max_left _ _)
    calc (∫ z in A, ∫ w in A, Ψ (Function.update (Function.update x i z) j w))
        = ∫ w in A, ∫ z in A, Ψ (Function.update (Function.update x i z) j w) :=
          pair_integral_swap_A hint2
      _ = ∫ z in A, ∫ w in A, Ψ (Function.update (Function.update x i w) j z) := rfl
      _ = ∫ z in A, ∫ w in A, Ψ (Function.update (Function.update x j z) i w) := by
          apply integral_congr_ae
          filter_upwards with z
          apply integral_congr_ae
          filter_upwards with w
          rw [Function.update_comm hij w z x]
  -- put both sides into the off-diagonal double-sum form
  have hL2 : (∑ i : Fin M, A.indicator (fun _ => (1 : ℝ)) (x i) * u (x i)
        * (∑ j ∈ Finset.univ.erase i, A.indicator (fun _ => (1 : ℝ)) (x j) * v (x j)
            * ∫ z in A, ∫ w in A, Ψ (Function.update (Function.update x i z) j w)))
      = ∑ i : Fin M, ∑ j ∈ Finset.univ.erase i,
          (A.indicator (fun _ => (1 : ℝ)) (x i) * u (x i))
            * (A.indicator (fun _ => (1 : ℝ)) (x j) * v (x j)
              * ∫ z in A, ∫ w in A, Ψ (Function.update (Function.update x i z) j w)) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
  have hR2 : (∑ i : Fin M, A.indicator (fun _ => (1 : ℝ)) (x i) * v (x i)
        * (∑ j ∈ Finset.univ.erase i, A.indicator (fun _ => (1 : ℝ)) (x j) * u (x j)
            * ∫ z in A, ∫ w in A, Ψ (Function.update (Function.update x i z) j w)))
      = ∑ i : Fin M, ∑ j ∈ Finset.univ.erase i,
          (A.indicator (fun _ => (1 : ℝ)) (x i) * v (x i))
            * (A.indicator (fun _ => (1 : ℝ)) (x j) * u (x j)
              * ∫ z in A, ∫ w in A, Ψ (Function.update (Function.update x i z) j w)) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
  rw [hL, hL2, hR, hR2]
  -- termwise: the `(i,j)` term of the LHS is the `(j,i)` term of the RHS
  have hpair : ∀ i j : Fin M, i ≠ j →
      (A.indicator (fun _ => (1 : ℝ)) (x i) * u (x i))
          * (A.indicator (fun _ => (1 : ℝ)) (x j) * v (x j)
            * ∫ z in A, ∫ w in A, Ψ (Function.update (Function.update x i z) j w))
        = (A.indicator (fun _ => (1 : ℝ)) (x j) * v (x j))
          * (A.indicator (fun _ => (1 : ℝ)) (x i) * u (x i)
            * ∫ z in A, ∫ w in A, Ψ (Function.update (Function.update x j z) i w)) := by
    intro i j hij
    rw [hI i j hij]
    ring
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j hj =>
    hpair i j (Finset.mem_erase.mp hj).1.symm))]
  exact (sum_erase_swap (fun i j : Fin M =>
    (A.indicator (fun _ => (1 : ℝ)) (x j) * v (x j))
      * (A.indicator (fun _ => (1 : ℝ)) (x i) * u (x i)
        * ∫ z in A, ∫ w in A, Ψ (Function.update (Function.update x j z) i w))))


/-- **The commutator at the box creation operators** (the `boxTauDagGen` normalisation, on the
box).  The two prefactors `(√volA)⁻¹` cancel, so this is the `boxOpG` statement scaled. -/
lemma boxTauDagGen_comm_smooth {N : ℕ} {ℓ volA : ℝ} {A : Set E3} (hA : MeasurableSet A)
    (hℓ : 0 < ℓ) (hAc : A ⊆ acube ℓ) {u v : E3 → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hum : ∫ z in A, u z = 0) (hvm : ∫ z in A, v z = 0)
    {Ψ : X (N + 2) → ℝ} (hΨ : Continuous Ψ) :
    ∀ x ∈ abox (N + 2) ℓ, boxTauDagGen volA A u (boxTauDagGen volA A v Ψ) x
      = boxTauDagGen volA A v (boxTauDagGen volA A u Ψ) x := by
  intro x hx
  have hcomm := boxOpG_comm_cre_box hA hℓ hAc hu hv hum hvm hΨ x hx
  have hYv : boxTauDagGen volA A v Ψ
      = (Real.sqrt volA)⁻¹ • boxOpG A v (fun _ => (1 : ℝ)) Ψ := by
    rw [boxTauDagGen_eq_boxOpG]
    funext y
    rfl
  have e1 : boxTauDagGen volA A u (boxTauDagGen volA A v Ψ) x
      = ((Real.sqrt volA)⁻¹ * (Real.sqrt volA)⁻¹)
        * boxOpG A u (fun _ => (1 : ℝ)) (boxOpG A v (fun _ => (1 : ℝ)) Ψ) x := by
    rw [show boxTauDagGen volA A u (boxTauDagGen volA A v Ψ) x
        = (Real.sqrt volA)⁻¹ * boxOpG A u (fun _ => (1 : ℝ)) (boxTauDagGen volA A v Ψ) x from
      congrFun (boxTauDagGen_eq_boxOpG volA A u (boxTauDagGen volA A v Ψ)) x]
    rw [hYv, boxOpG_smul_state]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have e2 : boxTauDagGen volA A v (boxTauDagGen volA A u Ψ) x
      = ((Real.sqrt volA)⁻¹ * (Real.sqrt volA)⁻¹)
        * boxOpG A v (fun _ => (1 : ℝ)) (boxOpG A u (fun _ => (1 : ℝ)) Ψ) x := by
    rw [show boxTauDagGen volA A v (boxTauDagGen volA A u Ψ) x
        = (Real.sqrt volA)⁻¹ * boxOpG A v (fun _ => (1 : ℝ)) (boxTauDagGen volA A u Ψ) x from
      congrFun (boxTauDagGen_eq_boxOpG volA A v (boxTauDagGen volA A u Ψ)) x]
    rw [show boxTauDagGen volA A u Ψ
        = (Real.sqrt volA)⁻¹ • boxOpG A u (fun _ => (1 : ℝ)) Ψ from by
      rw [boxTauDagGen_eq_boxOpG]; funext y; rfl]
    rw [boxOpG_smul_state]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [e1, e2, hcomm]

/-! ## The reduction, with the analytic inputs as hypotheses -/

theorem boxTauPairingReduction_core {N : ℕ} {ℓ volA : ℝ} {A : Set E3}
    (hA : MeasurableSet A) (hℓ : 0 < ℓ) (hAc : A ⊆ acube ℓ)
    {χ : E3 → ℝ} (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    {Ψ : X (N + 2) → ℝ} (hΨc : Continuous Ψ) (p : E3)
    (hcomm : ∀ x ∈ abox (N + 2) ℓ,
        boxTauDagGen volA A (boxWinModeImSmooth volA A χ p)
            (boxTauDagGen volA A (boxWinModeReSmooth volA A χ p) Ψ) x
          = boxTauDagGen volA A (boxWinModeReSmooth volA A χ p)
            (boxTauDagGen volA A (boxWinModeImSmooth volA A χ p) Ψ) x)
    (hpairu : (∫ x in abox (N + 2) ℓ, Ψ x *
        boxTauDagGen volA A (boxWinModeReSmooth volA A χ p)
          (boxTauDagGen volA A (boxWinModeReSmooth volA A χ p) Ψ) x)
      = boxModeRGen ℓ volA A (boxWinModeReSmooth volA A χ p) Ψ)
    (hpairv : (∫ x in abox (N + 2) ℓ, Ψ x *
        boxTauDagGen volA A (boxWinModeImSmooth volA A χ p)
          (boxTauDagGen volA A (boxWinModeImSmooth volA A χ p) Ψ) x)
      = boxModeRGen ℓ volA A (boxWinModeImSmooth volA A χ p) Ψ) :
    (∫ x in abox (N + 2) ℓ,
        (Ψ x : ℂ) * boxTauDagGenC volA A
          (fun z => star (boxWinModeC volA A χ p z))
          (boxTauDagGenC volA A (boxWinModeC volA A χ p)
            (fun y => (Ψ y : ℂ))) x)
      = ((boxModeRGen ℓ volA A (boxWinModeReGen volA A χ p) Ψ
          + boxModeRGen ℓ volA A (boxWinModeImGen volA A χ p) Ψ
          : ℝ) : ℂ) := by
  have husc : Continuous (boxWinModeReSmooth volA A χ p) :=
    continuous_boxWinModeReSmooth volA A hχc p
  have hvsc : Continuous (boxWinModeImSmooth volA A χ p) :=
    continuous_boxWinModeImSmooth volA A hχc p
  have hΨm : Measurable Ψ := hΨc.measurable
  obtain ⟨CΨ, hΨb⟩ := (abox_compact (N + 2) hℓ).exists_bound_of_continuousOn hΨc.continuousOn
  have hΨbn : ∀ x ∈ abox (N + 2) ℓ, |Ψ x| ≤ CΨ := fun x hx => by
    rw [← Real.norm_eq_abs]; exact hΨb x hx
  obtain ⟨Cu, hCu⟩ := (acube_compact hℓ).exists_bound_of_continuousOn husc.continuousOn
  have hub : ∀ z ∈ acube ℓ, |boxWinModeReSmooth volA A χ p z| ≤ Cu := fun z hz => by
    rw [← Real.norm_eq_abs]; exact hCu z hz
  obtain ⟨Cv, hCv⟩ := (acube_compact hℓ).exists_bound_of_continuousOn hvsc.continuousOn
  have hvb : ∀ z ∈ acube ℓ, |boxWinModeImSmooth volA A χ p z| ≤ Cv := fun z hz => by
    rw [← Real.norm_eq_abs]; exact hCv z hz
  obtain ⟨hYm, CY, hYb⟩ := boxTauDagGen_measurable_bound hA hℓ hAc volA husc hub hΨm hΨbn
  obtain ⟨hYYm, CYY, hYYb⟩ := boxTauDagGen_measurable_bound hA hℓ hAc volA husc hub hYm hYb
  obtain ⟨hZm, CZ, hZb⟩ := boxTauDagGen_measurable_bound hA hℓ hAc volA hvsc hvb hΨm hΨbn
  obtain ⟨hZZm, CZZ, hZZb⟩ := boxTauDagGen_measurable_bound hA hℓ hAc volA hvsc hvb hZm hZb
  have hpoint := pointwise_pair_reduction (volA := volA) (A := A) hA hℓ hAc hχc hχs p
    hcomm hYm hYb hZm hZb
  have hboxmeas : MeasurableSet (abox (N + 2) ℓ) := abox_measurable (N + 2) ℓ
  have hInt1 : IntegrableOn (fun x : X (N + 2) => Ψ x *
      boxTauDagGen volA A (boxWinModeReSmooth volA A χ p)
        (boxTauDagGen volA A (boxWinModeReSmooth volA A χ p) Ψ) x) (abox (N + 2) ℓ) volume :=
    Work.BoseFixB1S.integrableOn_mul_of_bound hℓ hΨm hYYm hΨbn hYYb
  have hInt2 : IntegrableOn (fun x : X (N + 2) => Ψ x *
      boxTauDagGen volA A (boxWinModeImSmooth volA A χ p)
        (boxTauDagGen volA A (boxWinModeImSmooth volA A χ p) Ψ) x) (abox (N + 2) ℓ) volume :=
    Work.BoseFixB1S.integrableOn_mul_of_bound hℓ hΨm hZZm hΨbn hZZb
  have hstep1 : (∫ x in abox (N + 2) ℓ,
        (Ψ x : ℂ) * boxTauDagGenC volA A
          (fun z => star (boxWinModeC volA A χ p z))
          (boxTauDagGenC volA A (boxWinModeC volA A χ p)
            (fun y => (Ψ y : ℂ))) x)
      = ∫ x in abox (N + 2) ℓ,
          Complex.ofReal (Ψ x * (boxTauDagGen volA A (boxWinModeReSmooth volA A χ p)
                (boxTauDagGen volA A (boxWinModeReSmooth volA A χ p) Ψ) x
              + boxTauDagGen volA A (boxWinModeImSmooth volA A χ p)
                (boxTauDagGen volA A (boxWinModeImSmooth volA A χ p) Ψ) x)) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hboxmeas] with x hx
    exact hpoint x hx
  have hstep2 : (∫ x in abox (N + 2) ℓ,
          Complex.ofReal (Ψ x * (boxTauDagGen volA A (boxWinModeReSmooth volA A χ p)
                (boxTauDagGen volA A (boxWinModeReSmooth volA A χ p) Ψ) x
              + boxTauDagGen volA A (boxWinModeImSmooth volA A χ p)
                (boxTauDagGen volA A (boxWinModeImSmooth volA A χ p) Ψ) x)))
      = Complex.ofReal (∫ x in abox (N + 2) ℓ,
          Ψ x * (boxTauDagGen volA A (boxWinModeReSmooth volA A χ p)
                (boxTauDagGen volA A (boxWinModeReSmooth volA A χ p) Ψ) x
              + boxTauDagGen volA A (boxWinModeImSmooth volA A χ p)
                (boxTauDagGen volA A (boxWinModeImSmooth volA A χ p) Ψ) x)) :=
    integral_ofReal
  have hstep3 : (∫ x in abox (N + 2) ℓ,
          Ψ x * (boxTauDagGen volA A (boxWinModeReSmooth volA A χ p)
                (boxTauDagGen volA A (boxWinModeReSmooth volA A χ p) Ψ) x
              + boxTauDagGen volA A (boxWinModeImSmooth volA A χ p)
                (boxTauDagGen volA A (boxWinModeImSmooth volA A χ p) Ψ) x))
      = (∫ x in abox (N + 2) ℓ, Ψ x *
            boxTauDagGen volA A (boxWinModeReSmooth volA A χ p)
              (boxTauDagGen volA A (boxWinModeReSmooth volA A χ p) Ψ) x)
          + ∫ x in abox (N + 2) ℓ, Ψ x *
            boxTauDagGen volA A (boxWinModeImSmooth volA A χ p)
              (boxTauDagGen volA A (boxWinModeImSmooth volA A χ p) Ψ) x := by
    rw [show (∫ x in abox (N + 2) ℓ,
          Ψ x * (boxTauDagGen volA A (boxWinModeReSmooth volA A χ p)
                (boxTauDagGen volA A (boxWinModeReSmooth volA A χ p) Ψ) x
              + boxTauDagGen volA A (boxWinModeImSmooth volA A χ p)
                (boxTauDagGen volA A (boxWinModeImSmooth volA A χ p) Ψ) x))
        = ∫ x in abox (N + 2) ℓ, (Ψ x *
            boxTauDagGen volA A (boxWinModeReSmooth volA A χ p)
              (boxTauDagGen volA A (boxWinModeReSmooth volA A χ p) Ψ) x
          + Ψ x *
            boxTauDagGen volA A (boxWinModeImSmooth volA A χ p)
              (boxTauDagGen volA A (boxWinModeImSmooth volA A χ p) Ψ) x) from by
      apply integral_congr_ae
      filter_upwards with x
      ring]
    exact integral_add hInt1 hInt2
  rw [hstep1, hstep2, hstep3]
  congr 1
  rw [hpairu, hpairv, ← boxModeRGen_reGen_eq_smooth hA ℓ volA χ p Ψ,
    ← boxModeRGen_imGen_eq_smooth hA ℓ volA χ p Ψ]

/-- **The box `τ`-side pairing reduction.** -/
theorem boxTauPairingReduction {N : ℕ} {ℓ volA : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) (hℓ : 0 < ℓ) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hvolpos : 0 < volA)
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχc : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχs : HasCompactSupport χ) (hχsupp : ∀ z, z ∉ A → χ z = 0)
    {Ψ : Submission.BoseGases.X (N + 2) → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (p : EuclideanSpace ℝ (Fin 3)) :
    (∫ x in Submission.BoseGases.abox (N + 2) ℓ,
        (Ψ x : ℂ) * Work.BoseFixB1.boxTauDagGenC volA A
          (fun z => star (Work.BoseFixB1.boxWinModeC volA A χ p z))
          (Work.BoseFixB1.boxTauDagGenC volA A (Work.BoseFixB1.boxWinModeC volA A χ p)
            (fun y => (Ψ y : ℂ))) x)
      = ((Work.BoseFixB1.boxModeRGen ℓ volA A (Work.BoseFixB1.boxWinModeReGen volA A χ p) Ψ
          + Work.BoseFixB1.boxModeRGen ℓ volA A (Work.BoseFixB1.boxWinModeImGen volA A χ p) Ψ
          : ℝ) : ℂ) := by
  have hχcont : Continuous χ := hχc.continuous
  have hΨcont : Continuous Ψ := hΨ.continuous
  have hum := integral_boxWinModeReSmooth_eq_zero hℓ hAc hvolA hvolpos hχcont hχs p
  have hvm := integral_boxWinModeImSmooth_eq_zero hℓ hAc hvolA hvolpos hχcont hχs p
  exact boxTauPairingReduction_core hA hℓ hAc hχcont hχs hΨcont p
    (fun x hx => (boxTauDagGen_comm_smooth hA hℓ hAc
      (continuous_boxWinModeReSmooth volA A hχcont p)
      (continuous_boxWinModeImSmooth volA A hχcont p) hum hvm hΨcont x hx).symm)
    (boxTauDagGen_pairing_integral hA hℓ hAc hvolpos
      (continuous_boxWinModeReSmooth volA A hχcont p) hΨcont)
    (boxTauDagGen_pairing_integral hA hℓ hAc hvolpos
      (continuous_boxWinModeImSmooth volA A hχcont p) hΨcont)

end Work.BoseFixB1
