/-
# The angular slice Cauchy–Schwarz bound for the zero-mode comparison

For a function `Φ : ℝ → ℝ → ℝ` and a slice `z`, the `θ`-energy of the slice is

`sliceEnergy Φ z = ∫_{Iθ} Φ(z,θ)² sin(2θ)^{-(2+η)}`,

i.e. the `L²`-norm of `θ ↦ Φ(z,θ)·sin(2θ)^{-(1+η/2)}` on the angular interval
`Iθ = [0,π/2]`.  Writing the integrand of a set integral `∫_E |Φ(z,θ)|` as the product

`|Φ(z,θ)| = (|Φ(z,θ)| sin(2θ)^{-(1+η/2)}) · sin(2θ)^{(1+η/2)}`

and applying Cauchy–Schwarz in `L²(E)` gives the slice bound

`∫_E |Φ(z,θ)| ≤ √(sliceEnergy Φ z) · √(∫_E sin(2θ)^{2+η})`

for every `E ⊆ Iθ`, as long as the weighted square is integrable
(the hypothesis `hint`, written in the divided form `(Φ/sin 2θ)² sin(2θ)^{-η}` used elsewhere
in the development).

The only point to be careful about is the two endpoints `θ = 0`, `θ = π/2`, where `sin(2θ)`
vanishes: there the two weighted squares are `0` (the negative powers of `0` are `0`), so the
identity `(x/sin 2θ)² sin(2θ)^{-η} = x² sin(2θ)^{-(2+η)}` holds *everywhere* on `Iθ` (a
two-case algebraic computation), while the product identity
`√(x² sin(2θ)^{-(2+η)}) √(sin(2θ)^{2+η}) = |x|` needs `sin(2θ) ≠ 0` and is therefore only
available almost everywhere — the two endpoints form a null set.
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.cs_integral
import Submission.Work.Construction.Defs
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroModeDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EComparison

/-! ## Two algebraic lemmas about the weight `sin(2θ)^{-p}` -/

/-- For `0 ≤ c` and `2 + e ≠ 0`, `(x/c)² c^{-e} = x² c^{-(2+e)}`.  The endpoint case `c = 0`
is harmless: both sides vanish because `0^y = 0` for `y ≠ 0`. -/
private lemma div_sq_mul_rpow_eq {x c e : ℝ} (hc : 0 ≤ c) (he2 : 2 + e ≠ 0) :
    (x / c) ^ 2 * c ^ (-e) = x ^ 2 * c ^ (-(2 + e)) := by
  rcases eq_or_lt_of_le hc with h | h
  · subst h
    rw [div_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul,
      Real.zero_rpow (neg_ne_zero.mpr he2), mul_zero]
  · have hsplit : c ^ (-(2 + e)) = c ^ (-(2 : ℝ)) * c ^ (-e) := by
      rw [show -(2 + e) = -(2 : ℝ) + -e by ring, Real.rpow_add h]
    have hc2 : c ^ (-(2 : ℝ)) = (c ^ 2)⁻¹ := by
      rw [Real.rpow_neg (le_of_lt h)]
      exact congrArg Inv.inv (Real.rpow_natCast c 2)
    have hxc : (x / c) ^ 2 = x ^ 2 * (c ^ 2)⁻¹ := by rw [div_pow, div_eq_mul_inv]
    rw [hsplit, hc2, hxc]
    ring

/-- For `0 < c` the two square roots multiply to `|x|`:
`√((x/c)² c^{-e}) · √(c^{2+e}) = |x|`. -/
private lemma sqrt_mul_sqrt_eq_abs {x c e : ℝ} (hc : 0 < c) :
    Real.sqrt ((x / c) ^ 2 * c ^ (-e)) * Real.sqrt (c ^ (2 + e)) = |x| := by
  have hHnn : 0 ≤ (x / c) ^ 2 * c ^ (-e) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt hc) _)
  have hprod : (x / c) ^ 2 * c ^ (-e) * c ^ (2 + e) = x ^ 2 := by
    have h1 : c ^ (-e) * c ^ (2 + e) = c ^ 2 := by
      rw [← Real.rpow_add hc, show -e + (2 + e) = (2 : ℝ) by ring]
      exact Real.rpow_natCast c 2
    calc (x / c) ^ 2 * c ^ (-e) * c ^ (2 + e)
        = (x / c) ^ 2 * (c ^ (-e) * c ^ (2 + e)) := by ring
      _ = (x / c) ^ 2 * c ^ 2 := by rw [h1]
      _ = x ^ 2 := by rw [← mul_pow, div_mul_cancel₀ x (ne_of_gt hc)]
  rw [← Real.sqrt_mul hHnn, hprod, Real.sqrt_sq_eq_abs]

/-! ## `sin(2θ) > 0` almost everywhere on any `E ⊆ Iθ` -/

/-- On any `E ⊆ Iθ` the function `θ ↦ sin(2θ)` is almost everywhere positive (the only zeros
in `Iθ` are the endpoints `0` and `π/2`). -/
private lemma ae_sin_two_pos {E : Set ℝ} (hE : E ⊆ Work.Spaces.Iθ) :
    ∀ᵐ θ ∂(volume.restrict E), 0 < Work.Construction.s2 θ := by
  have hpair : volume ({0, Real.pi / 2} : Set ℝ) = 0 := by
    rw [show ({0, Real.pi / 2} : Set ℝ) = {0} ∪ {Real.pi / 2} by
      ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]]
    exact measure_union_null Real.volume_singleton Real.volume_singleton
  have hsub : {θ : ℝ | ¬ (θ ∈ E → θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))}
      ⊆ ({0, Real.pi / 2} : Set ℝ) := by
    intro θ hθ
    rw [Set.mem_ofPred_eq, not_imp, Set.mem_Ioo] at hθ
    obtain ⟨hEθ, hJ⟩ := hθ
    have hIθ : θ ∈ Work.Spaces.Iθ := hE hEθ
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hIθ
    rw [not_and_or, not_lt, not_lt] at hJ
    rcases hJ with h | h
    · exact Or.inl (le_antisymm h hIθ.1)
    · exact Or.inr (le_antisymm hIθ.2 h)
  have h1 : ∀ᵐ θ ∂volume, θ ∈ E → θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    rw [MeasureTheory.ae_iff]
    exact measure_mono_null hsub hpair
  have hJ : ∀ᵐ θ ∂(volume.restrict E), θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    rw [MeasureTheory.ae_restrict_iff (p := fun θ => θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
      measurableSet_Ioo]
    exact h1
  filter_upwards [hJ] with θ hθ
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-! ## The slice bound -/

theorem slice_abs_le_sqrt_sliceEnergy {Φ : ℝ → ℝ → ℝ} {z : ℝ} {E : Set ℝ}
    (hE : E ⊆ Work.Spaces.Iθ)
    (hint : MeasureTheory.IntegrableOn (fun θ => (Φ z θ / Work.Construction.s2 θ) ^ 2
        * (Work.Construction.s2 θ) ^ (-Work.Spaces.eta)) Work.Spaces.Iθ) :
    ∫ θ in E, |Φ z θ| ≤ Real.sqrt (Work.FTS.StrongEps.EComparison.sliceEnergy Φ z)
      * Real.sqrt (∫ θ in E, (Work.Construction.s2 θ) ^ (2 + Work.Spaces.eta)) := by
  -- the three weights appearing in the argument
  let H : ℝ → ℝ := fun θ => (Φ z θ / Work.Construction.s2 θ) ^ 2
    * (Work.Construction.s2 θ) ^ (-Work.Spaces.eta)
  let Q : ℝ → ℝ := fun θ => (Work.Construction.s2 θ) ^ (2 + Work.Spaces.eta)
  let P : ℝ → ℝ := fun θ => Φ z θ ^ 2
    * (Work.Construction.s2 θ) ^ (-(2 + Work.Spaces.eta))
  have heta2 : 2 + Work.Spaces.eta ≠ 0 := by rw [Work.Spaces.eta]; norm_num
  -- `sin(2θ) ≥ 0` on `Iθ`
  have hs2nn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Work.Construction.s2 θ := by
    intro θ hθ
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
    exact Real.sin_nonneg_of_mem_Icc
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hHnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ H θ := fun θ hθ =>
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hs2nn θ hθ) _)
  have hQnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Q θ := fun θ hθ =>
    Real.rpow_nonneg (hs2nn θ hθ) _
  -- almost everywhere statements on `volume.restrict E`
  have hEae : ∀ᵐ θ ∂(volume.restrict E), θ ∈ Work.Spaces.Iθ := by
    rw [MeasureTheory.ae_restrict_iff (p := fun θ => θ ∈ Work.Spaces.Iθ) measurableSet_Icc]
    exact Eventually.of_forall hE
  have hHae : ∀ᵐ θ ∂(volume.restrict E), 0 ≤ H θ :=
    hEae.mono fun θ hθ => hHnn θ hθ
  have hQae : ∀ᵐ θ ∂(volume.restrict E), 0 ≤ Q θ :=
    hEae.mono fun θ hθ => hQnn θ hθ
  have hspos : ∀ᵐ θ ∂(volume.restrict E), 0 < Work.Construction.s2 θ := ae_sin_two_pos hE
  -- `H = P` on `Iθ`
  have hHP : ∀ θ ∈ Work.Spaces.Iθ, H θ = P θ := fun θ hθ =>
    div_sq_mul_rpow_eq (hs2nn θ hθ) heta2
  have hHint : MeasureTheory.IntegrableOn H Work.Spaces.Iθ := hint
  have hHaeP : H =ᵐ[volume.restrict Work.Spaces.Iθ] P := by
    filter_upwards [MeasureTheory.ae_restrict_mem (s := Work.Spaces.Iθ) measurableSet_Icc]
      with θ hθ
    exact hHP θ hθ
  have hPint : MeasureTheory.IntegrableOn P Work.Spaces.Iθ := hHint.congr hHaeP
  have hHintE : MeasureTheory.IntegrableOn H E := hHint.mono_set hE
  -- `∫_{Iθ} H = sliceEnergy Φ z`
  have hSE : ∫ θ in Work.Spaces.Iθ, H θ = sliceEnergy Φ z := by
    rw [integral_congr_ae hHaeP]
    show (∫ θ in Work.Spaces.Iθ,
        Φ z θ ^ 2 * (Work.Construction.s2 θ) ^ (-(2 + Work.Spaces.eta)))
      = sliceEnergy Φ z
    simp only [sliceEnergy, rootWeight, Work.Construction.s2_eq]
  -- integrability of `Q` on `E`
  have hQcont : Continuous Q := by
    have h1 : Continuous fun x : ℝ => x ^ (2 + Work.Spaces.eta) :=
      Real.continuous_rpow_const (by rw [Work.Spaces.eta]; norm_num)
    exact h1.comp (Real.continuous_sin.comp (continuous_const.mul continuous_id))
  have hQint : MeasureTheory.IntegrableOn Q Work.Spaces.Iθ :=
    ContinuousOn.integrableOn_compact (K := Work.Spaces.Iθ) isCompact_Icc hQcont.continuousOn
  have hQintE : MeasureTheory.IntegrableOn Q E := hQint.mono_set hE
  -- `L²`-membership of the two square roots on `E`
  have hu_meas : AEStronglyMeasurable (fun θ => Real.sqrt (H θ)) (volume.restrict E) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hHintE.aestronglyMeasurable
  have hv_meas : AEStronglyMeasurable (fun θ => Real.sqrt (Q θ)) (volume.restrict E) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hQintE.aestronglyMeasurable
  have hu_sq : Integrable (fun θ => Real.sqrt (H θ) ^ 2) (volume.restrict E) :=
    hHintE.congr (hHae.mono fun θ hθ => (Real.sq_sqrt hθ).symm)
  have hv_sq : Integrable (fun θ => Real.sqrt (Q θ) ^ 2) (volume.restrict E) :=
    hQintE.congr (hQae.mono fun θ hθ => (Real.sq_sqrt hθ).symm)
  have hu_lp : MemLp (fun θ => Real.sqrt (H θ)) 2 (volume.restrict E) :=
    (memLp_two_iff_integrable_sq hu_meas).mpr hu_sq
  have hv_lp : MemLp (fun θ => Real.sqrt (Q θ)) 2 (volume.restrict E) :=
    (memLp_two_iff_integrable_sq hv_meas).mpr hv_sq
  have hcs := Work.Spaces.cs_integral hu_lp hv_lp
  -- the pointwise product identity, almost everywhere
  have hprod_ae : (fun θ => Real.sqrt (H θ) * Real.sqrt (Q θ))
      =ᵐ[volume.restrict E] (fun θ => |Φ z θ|) := by
    filter_upwards [hspos] with θ hθ
    exact sqrt_mul_sqrt_eq_abs (x := Φ z θ) (c := Work.Construction.s2 θ)
      (e := Work.Spaces.eta) hθ
  have hHsq : (∫ θ in E, Real.sqrt (H θ) ^ 2) = ∫ θ in E, H θ :=
    integral_congr_ae (hHae.mono fun θ hθ => Real.sq_sqrt hθ)
  have hQsq : (∫ θ in E, Real.sqrt (Q θ) ^ 2) = ∫ θ in E, Q θ :=
    integral_congr_ae (hQae.mono fun θ hθ => Real.sq_sqrt hθ)
  have hcsE : (∫ θ in E, Real.sqrt (H θ) * Real.sqrt (Q θ)) ^ 2
      ≤ (∫ θ in E, H θ) * (∫ θ in E, Q θ) := by
    rw [← hHsq, ← hQsq]
    exact hcs
  have hEHnn : 0 ≤ ∫ θ in E, H θ := integral_nonneg_of_ae hHae
  have hstep : ∫ θ in E, Real.sqrt (H θ) * Real.sqrt (Q θ)
      ≤ Real.sqrt (∫ θ in E, H θ) * Real.sqrt (∫ θ in E, Q θ) :=
    calc ∫ θ in E, Real.sqrt (H θ) * Real.sqrt (Q θ)
        ≤ Real.sqrt ((∫ θ in E, H θ) * (∫ θ in E, Q θ)) := Real.le_sqrt_of_sq_le hcsE
      _ = Real.sqrt (∫ θ in E, H θ) * Real.sqrt (∫ θ in E, Q θ) :=
          Real.sqrt_mul hEHnn _
  -- comparison of `∫_E H` with the slice energy
  have hmono : ∫ θ in E, H θ ≤ ∫ θ in Work.Spaces.Iθ, H θ :=
    MeasureTheory.setIntegral_mono_set hHint
      (by
        filter_upwards [MeasureTheory.ae_restrict_mem (s := Work.Spaces.Iθ) measurableSet_Icc]
          with θ hθ
        exact hHnn θ hθ)
      (Eventually.of_forall hE)
  calc ∫ θ in E, |Φ z θ|
      = ∫ θ in E, Real.sqrt (H θ) * Real.sqrt (Q θ) := integral_congr_ae hprod_ae.symm
    _ ≤ Real.sqrt (∫ θ in E, H θ) * Real.sqrt (∫ θ in E, Q θ) := hstep
    _ ≤ Real.sqrt (sliceEnergy Φ z) * Real.sqrt (∫ θ in E, Q θ) := by
        refine mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _)
        rw [hSE] at hmono
        exact hmono

end Work.FTS.StrongEps.EComparison
