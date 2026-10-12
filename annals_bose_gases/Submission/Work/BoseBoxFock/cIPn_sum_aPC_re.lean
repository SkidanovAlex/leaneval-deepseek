import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.BombNExcDefs
import Submission.Work.BoseBoxFock.abox_integral_peel_complex
import Submission.Work.BoseBoxFock.slotCountsComplex

/-!
# `Work.BoseBoxFock.cIPn_sum_aPC_re`

The box-side identity of the `nExc` row of the BF3b dictionary: the second-quantised
`⟨Θ, Σ_j Q_j Θ⟩` pairing of a state `Θ` with its slot-complements `Q_j Θ = Θ − P_j Θ`
equals the excited count `n₊(Θ) = Σ_j ‖Q_j Θ‖²`.

The mathematics is the orthogonality `⟨P_j Θ, Q_j Θ⟩ = 0` of the slot projections on the
box `abox d ℓ`, i.e. the peel
`∫_{abox} conj(P_j Θ) · Q_j Θ = ∫_{r} ... = 0` (the fibre `Q_j Θ(·[j↦y])` has zero cube
mean, while `P_j Θ` is constant in the slot).

The state `Θ` is only assumed `MemLp Θ ⊤` and supported in the box; the two facts that
make the argument work for such a general state are

* `ae_update_eq_of_ae_eq` — modifying `Θ` on a null set does not change `aPC j Θ` a.e.,
  proved from the measure-theoretic crux `prod_update_preimage_null` (the insertion map
  `x ↦ x[j↦y]` pulls a null set back to a null set of the product measure);
* `integral_aQC_update_eq_zero` — the definitional fibre-mean identity, valid even when
  the fibre integral is a junk value `0`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace Work.BoseBoxFock

open Work.BoseDict

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. Structural facts about the complex slot mean `aPC` -/

/-- `P_j` is constant in the `j`-th slot (no continuity of the state is needed). -/
theorem aPC_const_in_coord {N : ℕ} (ℓ : ℝ) (j : Fin N) (Θ : Xn N → ℂ) (x : Xn N) (z : Sp) :
    aPC ℓ j Θ (Function.update x j z) = aPC ℓ j Θ x := by
  unfold aPC
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with y
  congr 1
  ext k
  by_cases hk : k = j <;> simp [hk]

/-- The fibre mean of the complementary slot vanishes: `∫_{acube} Q_j Θ(x[j↦y]) dy = 0`.

This is a definitional identity (the cube mean of `P_j Θ` reproduces `P_j Θ x`); it holds
for every state, with the convention that the integral of a non-integrable function is the
junk value `0`. -/
theorem integral_aQC_update_eq_zero {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : Fin N)
    (G : Xn N → ℂ) (x : Xn N) :
    ∫ y in Submission.BoseGases.acube ℓ, aQC ℓ j G (Function.update x j y) = 0 := by
  set μ' : Measure Sp := (volume : Measure Sp).restrict (Submission.BoseGases.acube ℓ) with hμ'
  haveI : IsFiniteMeasure μ' :=
    ⟨by rw [hμ', Measure.restrict_apply_univ]; exact Submission.BoseGases.acube_lt_top ℓ hℓ.le⟩
  set K : ℂ := ∫ z in Submission.BoseGases.acube ℓ, G (Function.update x j z) with hK
  have hc : ((1 / ℓ ^ 3 : ℝ) : ℂ) * ((ℓ ^ 3 : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, one_div, inv_mul_cancel₀ (by positivity : (ℓ:ℝ)^3 ≠ 0),
      Complex.ofReal_one]
  have haPC : ∀ y, aPC ℓ j G (Function.update x j y) = ((1 / ℓ ^ 3 : ℝ) : ℂ) * K := by
    intro y
    unfold aPC
    rw [hK]
    congr 1
    apply integral_congr_ae
    filter_upwards with z
    congr 1
    ext k
    by_cases hk : k = j <;> simp [hk]
  rw [show (fun y => aQC ℓ j G (Function.update x j y))
      = fun y => G (Function.update x j y) - ((1 / ℓ ^ 3 : ℝ) : ℂ) * K from by
    funext y; rw [aQC_apply, haPC y]]
  set F : Sp → ℂ := fun y => G (Function.update x j y) - ((1 / ℓ ^ 3 : ℝ) : ℂ) * K with hF
  by_cases hint : Integrable F μ'
  · have hconst : Integrable (fun _ : Sp => ((1 / ℓ ^ 3 : ℝ) : ℂ) * K) μ' := integrable_const _
    have hsum : (fun y => F y + ((1 / ℓ ^ 3 : ℝ) : ℂ) * K) = fun y => G (Function.update x j y) := by
      funext y; rw [hF]; ring
    have h2 := MeasureTheory.integral_add hint hconst
    rw [hsum] at h2
    have h3 : (∫ y : Sp, ((1 / ℓ ^ 3 : ℝ) : ℂ) * K ∂μ')
        = ((1 / ℓ ^ 3 : ℝ) : ℂ) * K * ((ℓ ^ 3 : ℝ) : ℂ) := by
      rw [MeasureTheory.integral_const, hμ', Submission.BoseGases.real_volume_acube ℓ hℓ.le,
        Complex.real_smul]
      exact mul_comm (((ℓ ^ 3 : ℝ) : ℂ)) (((1 / ℓ ^ 3 : ℝ) : ℂ) * K)
    rw [h3] at h2
    have hKval : (∫ y : Sp, G (Function.update x j y) ∂μ') = K := by rw [hK]
    have hKL : ((1 / ℓ ^ 3 : ℝ) : ℂ) * K * ((ℓ ^ 3 : ℝ) : ℂ) = K := by
      rw [mul_assoc, mul_comm K ((ℓ ^ 3 : ℝ) : ℂ), ← mul_assoc, hc, one_mul]
    have h4 : K = (∫ y : Sp, F y ∂μ') + K := by
      have h2' : (∫ y : Sp, G (Function.update x j y) ∂μ') = (∫ y : Sp, F y ∂μ') + K := by
        rw [h2, hKL]
      calc K = (∫ y : Sp, G (Function.update x j y) ∂μ') := hKval.symm
        _ = (∫ y : Sp, F y ∂μ') + K := h2'
    have h7 : (∫ y : Sp, F y ∂μ') + K = (0 : ℂ) + K := by rw [zero_add]; exact h4.symm
    exact add_right_cancel h7
  · exact integral_undef hint

/-! ## 2. The measure-theoretic crux: inserting `y` in slot `j` of a null set -/

/-- **The crux.**  For a measurable null set `D` of `n+1`-particle configurations, the set of
pairs `(x,y)` with `x[j↦y] ∈ D` is null for the product of the two Lebesgue measures. -/
theorem prod_update_preimage_null {n : ℕ} (j : Fin (n+1)) {D : Set (Xn (n+1))}
    (hDm : MeasurableSet D) (hD0 : (volume : Measure (Xn (n+1))) D = 0) :
    ((volume : Measure (Xn (n+1))).prod (volume : Measure Sp))
      {p : Xn (n+1) × Sp | Function.update p.1 j p.2 ∈ D} = 0 := by
  set S : Set (Xn (n+1) × Sp) := {p | Function.update p.1 j p.2 ∈ D} with hSdef
  have hS_meas : MeasurableSet S := hDm.preimage (by fun_prop)
  set E : Set (Sp × Xn n) := (⇑(Submission.BoseGases.kcInsN n j)) ⁻¹' D with hEdef
  have hE_meas : MeasurableSet E := hDm.preimage (Submission.BoseGases.kcInsN n j).measurable
  have hE0 : (volume : Measure (Sp × Xn n)) E = 0 := by
    have hmp := Submission.BoseGases.kc_mp_insN n j
    rw [hEdef, ← Measure.map_apply (Submission.BoseGases.kcInsN n j).measurable hDm,
      hmp.map_eq, hD0]
  have hEy : ∀ᵐ y ∂(volume : Measure Sp),
      (volume : Measure (Xn n)) {r : Xn n | (y,r) ∈ E} = 0 := by
    have h1 : (∫⁻ y : Sp, (volume : Measure (Xn n)) (Prod.mk y ⁻¹' E)
        ∂(volume : Measure Sp)) = 0 := by
      rw [← Measure.prod_apply hE_meas]; exact hE0
    exact (lintegral_eq_zero_iff (f := fun y : Sp => (volume : Measure (Xn n)) (Prod.mk y ⁻¹' E))
      (measurable_measure_prodMk_left hE_meas)).mp h1
  have hkey : ∀ y : Sp, (volume : Measure (Xn (n+1))) {x : Xn (n+1) | Function.update x j y ∈ D}
      = (volume : Measure Sp) Set.univ * (volume : Measure (Xn n)) {r : Xn n | (y,r) ∈ E} := by
    intro y
    have hmp := Submission.BoseGases.kc_mp_insN n j
    have hset : (⇑(Submission.BoseGases.kcInsN n j)) ⁻¹' {x : Xn (n+1) | Function.update x j y ∈ D}
        = (Set.univ : Set Sp) ×ˢ {r : Xn n | (y,r) ∈ E} := by
      ext q
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ, true_and]
      rw [hEdef, Set.mem_preimage]
      have hq : (Submission.BoseGases.kcInsN n j) q
          = (Submission.BoseGases.kcInsN n j) (q.1, q.2) := rfl
      rw [hq, Submission.BoseGases.update_kcInsN j q.1 y q.2]
    have hA : MeasurableSet {x : Xn (n+1) | Function.update x j y ∈ D} := hDm.preimage (by fun_prop)
    have hmap2 := Measure.map_apply (f := ⇑(Submission.BoseGases.kcInsN n j))
      (μ := (volume.prod volume)) (Submission.BoseGases.kcInsN n j).measurable hA
    have hmm : (Measure.map (⇑(Submission.BoseGases.kcInsN n j)) (volume.prod volume))
        = (volume : Measure (Xn (n+1))) := hmp.map_eq
    rw [← hmm, hmap2, hset, Measure.prod_prod]
  have hA_meas : MeasurableSet (Prod.swap ⁻¹' S) := hS_meas.preimage measurable_swap
  have hswap : ((volume : Measure (Xn (n+1))).prod (volume : Measure Sp)) S
      = ((volume : Measure Sp).prod (volume : Measure (Xn (n+1)))) (Prod.swap ⁻¹' S) := by
    have h2 := Measure.prod_swap (μ := (volume : Measure Sp)) (ν := (volume : Measure (Xn (n+1))))
    rw [← h2, Measure.map_apply measurable_swap hS_meas]
  rw [hswap, Measure.prod_apply hA_meas]
  refine (lintegral_eq_zero_iff (f := fun y : Sp =>
      (volume : Measure (Xn (n+1))) (Prod.mk y ⁻¹' (Prod.swap ⁻¹' S)))
      (measurable_measure_prodMk_left hA_meas)).mpr ?_
  filter_upwards [hEy] with y hy
  have h1 : Prod.mk y ⁻¹' (Prod.swap ⁻¹' S) = {x : Xn (n+1) | Function.update x j y ∈ D} := by
    ext x; simp [S]
  show (volume : Measure (Xn (n+1))) (Prod.mk y ⁻¹' (Prod.swap ⁻¹' S)) = 0
  rw [h1, hkey y, hy, mul_zero]

/-- **Null sets are invisible to the fibre integral.**  If `Θ =ᵐ g` then the fibres of `Θ`
and `g` agree a.e. in the slot variable, for a.e. configuration in the box. -/
theorem ae_update_eq_of_ae_eq {n : ℕ} {ℓ : ℝ} (j : Fin (n+1)) {Θ g : Xn (n+1) → ℂ}
    (h : Θ =ᵐ[(volume : Measure (Xn (n+1)))] g) :
    ∀ᵐ x ∂(volume.restrict (Submission.BoseGases.abox (n+1) ℓ)),
      ∀ᵐ y ∂(volume.restrict (Submission.BoseGases.acube ℓ)),
      Θ (Function.update x j y) = g (Function.update x j y) := by
  have hD : (volume : Measure (Xn (n+1))) {x | ¬ (Θ x = g x)} = 0 := ae_iff.mp h
  obtain ⟨D', hsub, hD'm, hD'0⟩ := exists_measurable_superset_of_null hD
  have hprod : ((volume : Measure (Xn (n+1))).prod (volume : Measure Sp))
      {p : Xn (n+1) × Sp | Function.update p.1 j p.2 ∈ D'} = 0 :=
    prod_update_preimage_null j hD'm hD'0
  have hae : ∀ᵐ p ∂((volume : Measure (Xn (n+1))).prod (volume : Measure Sp)),
      ¬ (Function.update p.1 j p.2 ∈ D') := by
    rw [ae_iff]
    simpa using hprod
  have hle : ((volume.restrict (Submission.BoseGases.abox (n+1) ℓ)).prod
      (volume.restrict (Submission.BoseGases.acube ℓ)))
      ≤ ((volume : Measure (Xn (n+1))).prod (volume : Measure Sp)) :=
    Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  have hae2 : ∀ᵐ p ∂((volume.restrict (Submission.BoseGases.abox (n+1) ℓ)).prod
      (volume.restrict (Submission.BoseGases.acube ℓ))), ¬ (Function.update p.1 j p.2 ∈ D') :=
    (ae_mono hle) hae
  have hmeas : MeasurableSet {z : Xn (n+1) × Sp | ¬ (Function.update z.1 j z.2 ∈ D')} :=
    (hD'm.preimage (by fun_prop)).compl
  have hiter : ∀ᵐ x ∂(volume.restrict (Submission.BoseGases.abox (n+1) ℓ)),
      ∀ᵐ y ∂(volume.restrict (Submission.BoseGases.acube ℓ)),
      ¬ (Function.update x j y ∈ D') :=
    (Measure.ae_prod_iff_ae_ae (μ := volume.restrict (Submission.BoseGases.abox (n+1) ℓ))
      (ν := volume.restrict (Submission.BoseGases.acube ℓ)) hmeas).mp hae2
  filter_upwards [hiter] with x hx
  filter_upwards [hx] with y hy
  by_contra hcon
  exact hy (hsub hcon)

/-- **`aPC` is insensitive to null modifications of the state.** -/
theorem ae_aPC_congr {n : ℕ} {ℓ : ℝ} (j : Fin (n+1)) {Θ g' : Xn (n+1) → ℂ}
    (h : Θ =ᵐ[(volume : Measure (Xn (n+1)))] g') :
    ∀ᵐ x ∂(volume.restrict (Submission.BoseGases.abox (n+1) ℓ)),
      aPC ℓ j Θ x = aPC ℓ j g' x := by
  filter_upwards [ae_update_eq_of_ae_eq (ℓ := ℓ) j h] with x hx
  unfold aPC
  congr 1
  exact MeasureTheory.integral_congr_ae hx

/-! ## 3. Measurability and a priori bounds of `aPC` -/

/-- `aPC` of an (`L^∞`) state is a.e. bounded.

(The name carries the `_xn` suffix to keep this chapter's module import-compatible with
`Work.BoseBoxFock.boxRealise_regular`, which declares a same-named lemma for
`Sp → ℂ`; the two chapters are otherwise independent.) -/
theorem exists_ae_bound_of_memLp_top_xn {N : ℕ} {f : Xn N → ℂ}
    (hf : MemLp f (⊤ : ENNReal) (volume : Measure (Xn N))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ x ∂(volume : Measure (Xn N)), ‖f x‖ ≤ C := by
  have h1 : eLpNormEssSup f (volume : Measure (Xn N)) < ⊤ := by
    rw [← eLpNorm_exponent_top hf.aestronglyMeasurable]; exact hf.eLpNorm_lt_top
  obtain ⟨C, hC⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp h1
  rw [Filter.eventually_map] at hC
  exact ⟨C, C.coe_nonneg, Filter.Eventually.mono hC fun x hx => by exact_mod_cast hx⟩

/-- `aPC` of a strongly measurable state is a.e. strongly measurable. -/
theorem aPC_aestronglyMeasurable_of_stronglyMeasurable {N : ℕ} {ℓ : ℝ} (j : Fin N)
    {f : Xn N → ℂ} (hf : StronglyMeasurable f) :
    AEStronglyMeasurable (aPC ℓ j f) (volume : Measure (Xn N)) := by
  have hjoint : AEStronglyMeasurable (fun p : Xn N × Sp => f (Function.update p.1 j p.2))
      ((volume : Measure (Xn N)).prod
        ((volume : Measure Sp).restrict (Submission.BoseGases.acube ℓ))) :=
    (hf.comp_measurable (by fun_prop : Measurable
      fun p : Xn N × Sp => Function.update p.1 j p.2)).aestronglyMeasurable
  have h1 := hjoint.integral_prod_right'
  have h2 : AEStronglyMeasurable
      (fun x : Xn N => ((1 / ℓ ^ 3 : ℝ) : ℂ)
        * ∫ y : Sp, f (Function.update x j y)
          ∂((volume : Measure Sp).restrict (Submission.BoseGases.acube ℓ))) volume :=
    h1.const_mul _
  exact h2

/-- If a state is everywhere bounded by `C ≥ 0`, so is its slot mean. -/
theorem norm_aPC_le {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : Fin N) {f : Xn N → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ x, ‖f x‖ ≤ C) : ∀ x, ‖aPC ℓ j f x‖ ≤ C := by
  intro x
  set μ' : Measure Sp := (volume : Measure Sp).restrict (Submission.BoseGases.acube ℓ) with hμ'
  haveI : IsFiniteMeasure μ' :=
    ⟨by rw [hμ', Measure.restrict_apply_univ]; exact Submission.BoseGases.acube_lt_top ℓ hℓ.le⟩
  have h1 : ‖∫ y : Sp, f (Function.update x j y) ∂μ'‖ ≤ C * ℓ ^ 3 := by
    have := MeasureTheory.norm_integral_le_of_norm_le_const
      (f := fun y : Sp => f (Function.update x j y))
      (C := C) (μ := μ') (ae_of_all _ fun y => hf _)
    rwa [hμ', Submission.BoseGases.real_volume_acube ℓ hℓ.le] at this
  have hc : ‖(((1 / ℓ ^ 3 : ℝ)) : ℂ)‖ = 1 / ℓ ^ 3 := by
    have h1 : ‖(((1 / ℓ ^ 3 : ℝ)) : ℂ)‖ ^ 2 = (1 / ℓ ^ 3) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal, sq]
    have h3 : 0 ≤ ‖(((1 / ℓ ^ 3 : ℝ)) : ℂ)‖ := norm_nonneg _
    have h4 : 0 ≤ 1 / ℓ ^ 3 := by positivity
    nlinarith
  have h2 : ‖aPC ℓ j f x‖ = (1 / ℓ ^ 3) * ‖∫ y : Sp, f (Function.update x j y) ∂μ'‖ := by
    unfold aPC
    rw [hμ', norm_mul, hc]
  rw [h2]
  have h3 : (1 / ℓ ^ 3) * (C * ℓ ^ 3) ≤ C := by
    rw [one_div]
    have hpos : (0:ℝ) < ℓ ^ 3 := by positivity
    rw [inv_mul_le_iff₀ hpos]
    nlinarith
  linarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ 1 / ℓ ^ 3)]

/-! ## 4. The orthogonality `⟨P_j Θ, Q_j Θ⟩ = 0` -/

/-- **The orthogonality.**  For any state `Θ` (with integrability of the pairing), the slot
mean is orthogonal to the slot complement on the box. -/
theorem integral_conj_aPC_mul_aQC_eq_zero {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : Fin (n+1))
    {Θ : Xn (n+1) → ℂ}
    (hF : IntegrableOn (fun x => conj (aPC ℓ j Θ x) * (Θ x - aPC ℓ j Θ x))
      (Submission.BoseGases.abox (n+1) ℓ) volume) :
    ∫ x in Submission.BoseGases.abox (n+1) ℓ,
      conj (aPC ℓ j Θ x) * (Θ x - aPC ℓ j Θ x) = 0 := by
  rw [abox_integral_peel_complex (ℓ := ℓ) j _ hF]
  have hfib : ∀ r : Xn n, (∫ y in Submission.BoseGases.acube ℓ,
      conj (aPC ℓ j Θ (Submission.BoseGases.kcInsN n j (y, r)))
        * (Θ (Submission.BoseGases.kcInsN n j (y, r))
            - aPC ℓ j Θ (Submission.BoseGases.kcInsN n j (y, r)))) = 0 := by
    intro r
    have hconst : ∀ y, aPC ℓ j Θ (Submission.BoseGases.kcInsN n j (y, r))
        = aPC ℓ j Θ (Submission.BoseGases.kcInsN n j (0, r)) := by
      intro y
      rw [← Submission.BoseGases.update_kcInsN (n := n) j (0 : Sp) y r]
      exact aPC_const_in_coord ℓ j Θ (Submission.BoseGases.kcInsN n j (0, r)) y
    calc (∫ y in Submission.BoseGases.acube ℓ,
          conj (aPC ℓ j Θ (Submission.BoseGases.kcInsN n j (y, r)))
            * (Θ (Submission.BoseGases.kcInsN n j (y, r))
                - aPC ℓ j Θ (Submission.BoseGases.kcInsN n j (y, r))))
        = ∫ y in Submission.BoseGases.acube ℓ,
            conj (aPC ℓ j Θ (Submission.BoseGases.kcInsN n j (0, r)))
              * (Θ (Submission.BoseGases.kcInsN n j (y, r))
                  - aPC ℓ j Θ (Submission.BoseGases.kcInsN n j (y, r))) := by
          apply integral_congr_ae
          filter_upwards with y
          rw [hconst y]
      _ = conj (aPC ℓ j Θ (Submission.BoseGases.kcInsN n j (0, r)))
            * ∫ y in Submission.BoseGases.acube ℓ,
                (Θ (Submission.BoseGases.kcInsN n j (y, r))
                  - aPC ℓ j Θ (Submission.BoseGases.kcInsN n j (y, r))) :=
          MeasureTheory.integral_const_mul _ _
      _ = 0 := by
          have hzero : (∫ y in Submission.BoseGases.acube ℓ,
                (Θ (Submission.BoseGases.kcInsN n j (y, r))
                  - aPC ℓ j Θ (Submission.BoseGases.kcInsN n j (y, r)))) = 0 := by
            have hK := integral_aQC_update_eq_zero (ℓ := ℓ) hℓ j Θ
              (Submission.BoseGases.kcInsN n j (0, r))
            simpa only [aQC_apply, Submission.BoseGases.update_kcInsN] using hK
          rw [hzero, mul_zero]
  simp only [hfib, integral_zero]

/-- The norm of a real number viewed as a complex number. -/
theorem norm_ofReal_complex_abs (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  have h : ‖(r : ℂ)‖ ^ 2 = r ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal, sq]
  rw [← Real.sqrt_sq_eq_abs, ← h, Real.sqrt_sq (norm_nonneg _)]

theorem cIPn_sum_aPC_re {d : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (Θ : Work.BoseDict.Xn d → ℂ)
    (hΘm : MeasureTheory.MemLp Θ (⊤ : ENNReal))
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox d ℓ) :
    (Work.BoseDict.cIPn d Θ (fun x => ∑ j : Fin d, (Θ x - Work.BoseBoxFock.aPC ℓ j Θ x))).re
      = Work.BoseBoxFock.cnPlusC ℓ Θ := by
  cases d with
  | zero =>
    simp only [Work.BoseDict.cIPn, cnPlusC, Finset.univ_eq_empty, Finset.sum_empty,
      mul_zero, integral_zero, Complex.zero_re]
  | succ n =>
    set B : Set (Xn (n+1)) := Submission.BoseGases.abox (n+1) ℓ with hB
    set μB : Measure (Xn (n+1)) := (volume : Measure (Xn (n+1))).restrict B with hμB
    have hB_lt : (volume : Measure (Xn (n+1))) B < ⊤ :=
      Submission.BoseGases.abox_lt_top (n+1) ℓ hℓ.le
    -- ## a good (strongly measurable, everywhere bounded) representative of `Θ`
    have hAESM : AEStronglyMeasurable Θ (volume : Measure (Xn (n+1))) := hΘm.aestronglyMeasurable
    set g : Xn (n+1) → ℂ := hAESM.mk Θ with hgdef
    have hg_sm : StronglyMeasurable g := hAESM.stronglyMeasurable_mk
    have hg_eq : Θ =ᵐ[(volume : Measure (Xn (n+1)))] g := hAESM.ae_eq_mk
    obtain ⟨C₀, hC₀nn, hC₀⟩ := exists_ae_bound_of_memLp_top_xn hΘm
    set C : ℝ := max C₀ 0 with hCdef
    have hC : 0 ≤ C := le_max_right _ _
    have hC₀C : C₀ ≤ C := le_max_left _ _
    have hgC : ∀ᵐ x ∂(volume : Measure (Xn (n+1))), ‖g x‖ ≤ C := by
      filter_upwards [hC₀, hg_eq] with x h1 h2
      rw [← h2]; exact le_trans h1 hC₀C
    set g' : Xn (n+1) → ℂ := {x | ‖g x‖ ≤ C}.indicator g with hg'def
    have hset_meas : MeasurableSet {x : Xn (n+1) | ‖g x‖ ≤ C} :=
      measurableSet_le (continuous_norm.measurable.comp hg_sm.measurable) measurable_const
    have hg'_sm : StronglyMeasurable g' := hg_sm.indicator hset_meas
    have hg'_bound : ∀ x, ‖g' x‖ ≤ C := by
      intro x
      by_cases hx : x ∈ {x : Xn (n+1) | ‖g x‖ ≤ C}
      · rw [hg'def, Set.indicator_of_mem (show x ∈ {x : Xn (n+1) | ‖g x‖ ≤ C} from hx)]
        exact hx
      · rw [hg'def, Set.indicator_of_notMem (show ¬ (x ∈ {x : Xn (n+1) | ‖g x‖ ≤ C}) from hx)]
        simpa using hC
    have hg'_eq : g' =ᵐ[(volume : Measure (Xn (n+1)))] g := by
      filter_upwards [hgC] with x hx
      rw [hg'def, Set.indicator_of_mem (show x ∈ {x : Xn (n+1) | ‖g x‖ ≤ C} from hx)]
    have hΘg' : Θ =ᵐ[(volume : Measure (Xn (n+1)))] g' := hg_eq.trans hg'_eq.symm
    -- ## the `a.e.` facts on the box
    have haPC_eq : ∀ j : Fin (n+1), ∀ᵐ x ∂μB, aPC ℓ j Θ x = aPC ℓ j g' x :=
      fun j => ae_aPC_congr j hΘg'
    have hAESM_P : ∀ j : Fin (n+1), AEStronglyMeasurable (aPC ℓ j Θ) μB := fun j =>
      ((aPC_aestronglyMeasurable_of_stronglyMeasurable (ℓ := ℓ) j hg'_sm).restrict).congr
        (Filter.EventuallyEq.symm (haPC_eq j))
    have hbnd_P : ∀ j : Fin (n+1), ∀ᵐ x ∂μB, ‖aPC ℓ j Θ x‖ ≤ C := fun j =>
      Filter.Eventually.mono (haPC_eq j) fun x hx => hx ▸ norm_aPC_le hℓ j hC hg'_bound x
    have hbnd_Θ : ∀ᵐ x ∂μB, ‖Θ x‖ ≤ C := by
      have h1 : ∀ᵐ x ∂(volume : Measure (Xn (n+1))), ‖Θ x‖ ≤ C :=
        Filter.Eventually.mono hC₀ fun x hx => le_trans hx hC₀C
      exact ae_mono (Measure.restrict_le_self (s := B)) h1
    have hAESM_Θ : AEStronglyMeasurable Θ μB := hAESM.restrict
    -- ## integrability of the three ingredients
    have hIntQ : ∀ j : Fin (n+1),
        IntegrableOn (fun x => conj (aPC ℓ j Θ x) * (Θ x - aPC ℓ j Θ x)) B volume := by
      intro j
      refine IntegrableOn.of_bound hB_lt ?_ (C * (C + C)) ?_
      · exact (hAESM_P j).star.mul (hAESM_Θ.sub (hAESM_P j))
      · filter_upwards [hbnd_Θ, hbnd_P j] with x h1 h2
        have h3 : ‖Θ x - aPC ℓ j Θ x‖ ≤ C + C := by
          calc ‖Θ x - aPC ℓ j Θ x‖ ≤ ‖Θ x‖ + ‖aPC ℓ j Θ x‖ := norm_sub_le _ _
            _ ≤ C + C := add_le_add h1 h2
        calc ‖conj (aPC ℓ j Θ x) * (Θ x - aPC ℓ j Θ x)‖
            = ‖aPC ℓ j Θ x‖ * ‖Θ x - aPC ℓ j Θ x‖ := by rw [norm_mul, Complex.norm_conj]
          _ ≤ C * (C + C) := mul_le_mul h2 h3 (norm_nonneg _) hC
    have hIntF : ∀ j : Fin (n+1),
        IntegrableOn (fun x => conj (Θ x) * (Θ x - aPC ℓ j Θ x)) B volume := by
      intro j
      refine IntegrableOn.of_bound hB_lt ?_ (C * (C + C)) ?_
      · exact hAESM_Θ.star.mul (hAESM_Θ.sub (hAESM_P j))
      · filter_upwards [hbnd_Θ, hbnd_P j] with x h1 h2
        have h3 : ‖Θ x - aPC ℓ j Θ x‖ ≤ C + C := by
          calc ‖Θ x - aPC ℓ j Θ x‖ ≤ ‖Θ x‖ + ‖aPC ℓ j Θ x‖ := norm_sub_le _ _
            _ ≤ C + C := add_le_add h1 h2
        calc ‖conj (Θ x) * (Θ x - aPC ℓ j Θ x)‖
            = ‖Θ x‖ * ‖Θ x - aPC ℓ j Θ x‖ := by rw [norm_mul, Complex.norm_conj]
          _ ≤ C * (C + C) := mul_le_mul h1 h3 (norm_nonneg _) hC
    have hIntA : ∀ j : Fin (n+1),
        IntegrableOn (fun x => ((‖Θ x - aPC ℓ j Θ x‖ ^ 2 : ℝ) : ℂ)) B volume := by
      intro j
      refine IntegrableOn.of_bound hB_lt ?_ ((2 * C) ^ 2) ?_
      · exact Complex.continuous_ofReal.comp_aestronglyMeasurable
          ((hAESM_Θ.sub (hAESM_P j)).norm.pow 2)
      · filter_upwards [hbnd_Θ, hbnd_P j] with x h1 h2
        have h3 : ‖Θ x - aPC ℓ j Θ x‖ ≤ 2 * C := by
          calc ‖Θ x - aPC ℓ j Θ x‖ ≤ ‖Θ x‖ + ‖aPC ℓ j Θ x‖ := norm_sub_le _ _
            _ ≤ C + C := add_le_add h1 h2
            _ = 2 * C := by ring
        rw [norm_ofReal_complex_abs]
        have h4 : ‖Θ x - aPC ℓ j Θ x‖ ^ 2 ≤ (2 * C) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h3 2
        rw [abs_of_nonneg (sq_nonneg _)]
        exact h4
    -- ## the orthogonality `⟨P_j Θ, Q_j Θ⟩ = 0`
    have horth : ∀ j : Fin (n+1),
        (∫ x in B, conj (aPC ℓ j Θ x) * (Θ x - aPC ℓ j Θ x)) = 0 :=
      fun j => integral_conj_aPC_mul_aQC_eq_zero hℓ j (hIntQ j)
    -- ## the per-slot identity
    have key : ∀ j : Fin (n+1), (∫ x in B, conj (Θ x) * (Θ x - aPC ℓ j Θ x)).re
        = ∫ x in B, ‖Θ x - aPC ℓ j Θ x‖ ^ 2 := by
      intro j
      have hpoint : ∀ x, conj (Θ x) * (Θ x - aPC ℓ j Θ x)
          = conj (aPC ℓ j Θ x) * (Θ x - aPC ℓ j Θ x)
            + ((‖Θ x - aPC ℓ j Θ x‖ ^ 2 : ℝ) : ℂ) := by
        intro x
        have h1 : conj (Θ x) = conj (aPC ℓ j Θ x) + conj (Θ x - aPC ℓ j Θ x) := by
          have h2 := map_sub (starRingEnd ℂ) (Θ x) (aPC ℓ j Θ x)
          rw [h2]; ring
        rw [h1, add_mul, Complex.conj_mul', ← Complex.ofReal_pow]
      have hsplit : (∫ x in B, conj (Θ x) * (Θ x - aPC ℓ j Θ x))
          = (∫ x in B, conj (aPC ℓ j Θ x) * (Θ x - aPC ℓ j Θ x))
            + (∫ x in B, ((‖Θ x - aPC ℓ j Θ x‖ ^ 2 : ℝ) : ℂ)) := by
        rw [← MeasureTheory.integral_add (hIntQ j) (hIntA j)]
        exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint)
      have hif : (∫ x in B, ((‖Θ x - aPC ℓ j Θ x‖ ^ 2 : ℝ) : ℂ))
          = ((∫ x in B, ‖Θ x - aPC ℓ j Θ x‖ ^ 2 : ℝ) : ℂ) := integral_ofReal
      rw [hsplit, Complex.add_re, horth j, Complex.zero_re, zero_add, hif,
        Complex.ofReal_re]
    -- ## assembly
    have hsuppF : ∀ x ∉ B, conj (Θ x) * (∑ j : Fin (n+1), (Θ x - aPC ℓ j Θ x)) = 0 := by
      intro x hx
      have hx0 : Θ x = 0 := by
        by_contra h
        exact hx (hΘs h)
      rw [hx0, map_zero, zero_mul]
    have hmain : (∫ x : Xn (n+1),
          conj (Θ x) * (∑ j : Fin (n+1), (Θ x - aPC ℓ j Θ x))).re
        = ∑ j : Fin (n+1), ∫ x in B, ‖Θ x - aPC ℓ j Θ x‖ ^ 2 := by
      rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hsuppF]
      have hsplit : (fun x => conj (Θ x) * (∑ j : Fin (n+1), (Θ x - aPC ℓ j Θ x)))
          = fun x => ∑ j : Fin (n+1), conj (Θ x) * (Θ x - aPC ℓ j Θ x) := by
        funext x; rw [Finset.mul_sum]
      rw [hsplit]
      rw [MeasureTheory.integral_finsetSum _ (fun j _ => hIntF j)]
      rw [Complex.re_sum]
      exact Finset.sum_congr rfl fun j _ => key j
    rw [show Work.BoseDict.cIPn (n+1) Θ
          (fun x => ∑ j : Fin (n+1), (Θ x - aPC ℓ j Θ x))
        = ∫ x : Xn (n+1), conj (Θ x) * (∑ j : Fin (n+1), (Θ x - aPC ℓ j Θ x)) from rfl,
      hmain]
    rw [cnPlusC]
    rfl

end Work.BoseBoxFock
