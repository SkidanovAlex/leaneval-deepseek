import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PB3Aux2
import Submission.Work.BoseBoxFock.pb3_fubini_abox_boxL
import Submission.Work.BoseBoxFock.pb3_slice_peel_real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pb3_mass_ident` — the slot-`j` mass identity of block III

**The identity.**  For `ℓ > 0` and any measurable, bounded `G : Λ(ℓ)^n → ℝ` (in the application
`G y = ‖Q_j P_i Θ (y)‖²`, the *slot-`j` excited* part of the *slot-`i` box mean* of the state `Θ`),

    ∫_{x ∈ Λ(ℓ)^n} ∫_{u ∈ ℝ³} χ_ℓ(u)² · G (x[j ↦ u])
      = ℓ³ · ∫_{x ∈ Λ(ℓ)^n} χ_ℓ(x_j)² · G x .

It is the change of variables that rewrites the `Q_j P_i` fibre mass as a box mass: the *left*
side integrates the fibre over the `j`-th slot, the *right* side is `ℓ³` times the
`χ_ℓ(x_j)²`-weighted box integral, and `ℓ³ = |Λ(ℓ)|` is exactly the volume of the slot that the
fibre integration spends.

**Proof (the assembly in this file).**  With `G` measurable and bounded:

* the `u`-integral is supported in `boxL ℓ = acube ℓ` (`chiScale_eq_zero_of_notMem_boxL`), so its
  domain can be cut down to the box (`hM1`, `integral_chiScale_sq_mul_eq_setIntegral`);
* Fubini over the *finite* measures `volume ↾ abox n ℓ` and `volume ↾ boxL ℓ`
  (`hM2`, the delegated brick `pb3_fubini_abox_boxL`) exchanges the two integrals;
* `∫ x in abox, G (x[j ↦ u]) = ℓ³ · ∫_{x'} G (insertCoord j u x')` — the "constant in the slot"
  slice identity (`hM4`, `abox_integral_update_eq_mul_slice`), obtained by peeling the `j`-th slot
  (the delegated brick `pb3_slice_peel_real`) together with
  `∫ w in boxL, c = volume.real (boxL ℓ) · c = ℓ³ · c`;
* pulling the constants `χ_ℓ(u)²` and `ℓ³` out of the remaining integrals (`hM3`, `hM5`) and peeling
  the `j`-th slot of the *right* side (`hM6`) puts both sides into the *same* normal form
  `ℓ³ ∫_{u ∈ boxL} χ_ℓ(u)² ∫_{x'} G (insertCoord j u x')`.

The state hypotheses `hΘm`, `hΘb` are used only to make `G` measurable and bounded (via the corpus's
`norm_aPC_le`); the support hypothesis `hΘs` is not needed by the identity.

The two delegated bricks are `Work.BoseBoxFock.pb3_slice_peel_real` (the real-valued slice peel
with an integrability hypothesis) and `Work.BoseBoxFock.pb3_fubini_abox_boxL` (Fubini over the two
finite boxes), both imported above.
-/

namespace Work.BoseBoxFock

noncomputable section

open MeasureTheory
open scoped BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn
local notation "boxL" => Work.BoseK15.corpusBox.boxL

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

/-! ## 1. Elementary box facts -/

/-- The box `abox n ℓ` has finite volume. -/
theorem pb3_volume_abox_ne_top {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (volume : Measure (Xn n)) (Submission.BoseGases.abox n ℓ) ≠ ⊤ := by
  rw [Submission.BoseGases.abox_volume n ℓ hℓ.le]
  exact ENNReal.ofReal_ne_top

/-- `chiScale ℓ` is supported in the corpus box, hence so is its square: the `u`-integral of `hM1`
below can be taken over `boxL ℓ`. -/
theorem integral_chiScale_sq_mul_eq_setIntegral {ℓ : ℝ} (hℓ : 0 < ℓ) (h : E3 → ℝ) :
    (∫ u : E3, (Submission.BoseGases.chiScale ℓ u) ^ 2 * h u)
      = ∫ u in boxL ℓ, (Submission.BoseGases.chiScale ℓ u) ^ 2 * h u :=
  (setIntegral_eq_integral_of_forall_compl_eq_zero (s := boxL ℓ)
    (f := fun u => (Submission.BoseGases.chiScale ℓ u) ^ 2 * h u)
    (fun u hu => by rw [chiScale_eq_zero_of_notMem_boxL hℓ hu]; ring)).symm

/-- **The slot-`j` slice identity**: integrating a function of `x[j ↦ u]` over the box gives `ℓ³`
times the integral of its slice form over the complementary box. -/
theorem abox_integral_update_eq_mul_slice {n : ℕ} (j : Fin n) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {g : Xn n → ℝ} (gm : Measurable g) (gb : ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C) (u : E3) :
    (∫ x in Submission.BoseGases.abox n ℓ, g (Function.update x j u))
      = ℓ ^ 3 * ∫ x' in boxPiSet ({k : Fin n // k ≠ j}) ℓ, g (insertCoord j u x') := by
  obtain ⟨C, hC⟩ := gb
  have hupd : Measurable (fun x : Xn n => Function.update x j u) := by
    rw [measurable_pi_iff]
    intro k
    by_cases hk : k = j
    · have h1 : (fun x : Xn n => Function.update x j u k) = fun _ => u := by
        funext x; rw [Function.update_apply, if_pos hk]
      rw [h1]; exact measurable_const
    · have h1 : (fun x : Xn n => Function.update x j u k) = fun x => x k := by
        funext x; rw [Function.update_apply, if_neg hk]
      rw [h1]; exact measurable_pi_apply k
  have hInt : IntegrableOn (fun x : Xn n => g (Function.update x j u))
      (Submission.BoseGases.abox n ℓ) volume :=
    IntegrableOn.of_bound (pb3_volume_abox_ne_top hℓ).lt_top (gm.comp hupd).aestronglyMeasurable C
      (Filter.Eventually.of_forall (fun x => hC _))
  rw [pb3_slice_peel_real j hℓ hInt]
  have hpt : ∀ (w : E3) (x' : {k : Fin n // k ≠ j} → E3),
      Function.update (insertCoord j w x') j u = insertCoord j u x' := by
    intro w x'
    funext k
    by_cases hk : k = j
    · simp [insertCoord, hk]
    · simp [insertCoord, hk]
  have hsub : (fun w : E3 => ∫ x' in boxPiSet ({k : Fin n // k ≠ j}) ℓ,
        g (Function.update (insertCoord j w x') j u))
      = fun _ : E3 => ∫ x' in boxPiSet ({k : Fin n // k ≠ j}) ℓ, g (insertCoord j u x') := by
    funext w
    have h2 : (fun x' : {k : Fin n // k ≠ j} → E3 =>
          g (Function.update (insertCoord j w x') j u))
        = fun x' => g (insertCoord j u x') := by
      funext x'
      rw [hpt w x']
    rw [h2]
  rw [hsub, setIntegral_const, volume_real_boxL hℓ, smul_eq_mul]

/-! ## 2. The main identity for a general measurable bounded state function -/

/-- **The mass identity** in the form in which the block-III row uses it: for any measurable,
bounded `G` on the box,

    ∫_{x ∈ abox} ∫_{u} χ_ℓ(u)² G (x[j ↦ u]) = ℓ³ ∫_{x ∈ abox} χ_ℓ(x_j)² G x . -/
theorem pb3_mass_ident_aux {n : ℕ} (j : Fin n) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {G : Xn n → ℝ} (Gm : Measurable G) (Gb : ∃ C : ℝ, ∀ x, ‖G x‖ ≤ C) :
    (∫ x in Submission.BoseGases.abox n ℓ, ∫ u : E3,
        (Submission.BoseGases.chiScale ℓ u) ^ 2 * G (Function.update x j u))
      = ℓ ^ 3 * ∫ x in Submission.BoseGases.abox n ℓ,
          (Submission.BoseGases.chiScale ℓ (x j)) ^ 2 * G x := by
  obtain ⟨Cg, hCg⟩ := Gb
  let D : ℝ := (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹
  have hDa : ∀ u : E3, (Submission.BoseGases.chiScale ℓ u) ^ 2 ≤ D ^ 2 := by
    intro u
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (Submission.BoseGases.abs_chiScale_le ℓ u) 2
  have hboundF : ∀ (x : Xn n) (u : E3),
      ‖(Submission.BoseGases.chiScale ℓ u) ^ 2 * G (Function.update x j u)‖ ≤ D ^ 2 * Cg := by
    intro x u
    rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _)]
    exact mul_le_mul (hDa u) (hCg _) (norm_nonneg _) (sq_nonneg D)
  -- hM1 : the `u`-integral is supported in the box
  have hM1 : (∫ x in Submission.BoseGases.abox n ℓ, ∫ u : E3,
        (Submission.BoseGases.chiScale ℓ u) ^ 2 * G (Function.update x j u))
      = ∫ x in Submission.BoseGases.abox n ℓ, ∫ u in boxL ℓ,
          (Submission.BoseGases.chiScale ℓ u) ^ 2 * G (Function.update x j u) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x =>
      integral_chiScale_sq_mul_eq_setIntegral hℓ (fun u => G (Function.update x j u)))
  -- hM2 : Fubini over the two finite boxes
  haveI : IsFiniteMeasure ((volume : Measure (Xn n)).restrict (Submission.BoseGases.abox n ℓ)) := by
    rw [isFiniteMeasure_restrict]
    exact pb3_volume_abox_ne_top hℓ
  haveI : IsFiniteMeasure ((volume : Measure E3).restrict (boxL ℓ)) := by
    rw [isFiniteMeasure_restrict, corpusBox_boxL_eq_acube hℓ,
      Submission.BoseGases.acube_volume ℓ hℓ.le]
    exact ENNReal.ofReal_ne_top
  have hupd2 : Measurable (fun p : Xn n × E3 => Function.update p.1 j p.2) := by
    rw [measurable_pi_iff]
    intro k
    by_cases hk : k = j
    · have h1 : (fun p : Xn n × E3 => Function.update p.1 j p.2 k) = fun p => p.2 := by
        funext p; rw [Function.update_apply, if_pos hk]
      rw [h1]; exact measurable_snd
    · have h1 : (fun p : Xn n × E3 => Function.update p.1 j p.2 k) = fun p => p.1 k := by
        funext p; rw [Function.update_apply, if_neg hk]
      rw [h1]; exact (measurable_pi_apply k).comp measurable_fst
  have hFm : Measurable (Function.uncurry (fun (x : Xn n) (u : E3) =>
      (Submission.BoseGases.chiScale ℓ u) ^ 2 * G (Function.update x j u))) :=
    (((Submission.BoseGases.chiScale_continuous ℓ).measurable.comp measurable_snd).pow_const 2).mul
      (Gm.comp hupd2)
  have hM2 : (∫ x in Submission.BoseGases.abox n ℓ, ∫ u in boxL ℓ,
        (Submission.BoseGases.chiScale ℓ u) ^ 2 * G (Function.update x j u))
      = ∫ u in boxL ℓ, ∫ x in Submission.BoseGases.abox n ℓ,
          (Submission.BoseGases.chiScale ℓ u) ^ 2 * G (Function.update x j u) :=
    pb3_fubini_abox_boxL hℓ hFm hboundF
  -- hM3 : pull `χ²` out of the inner integral
  have hM3 : (∫ u in boxL ℓ, ∫ x in Submission.BoseGases.abox n ℓ,
        (Submission.BoseGases.chiScale ℓ u) ^ 2 * G (Function.update x j u))
      = ∫ u in boxL ℓ, (Submission.BoseGases.chiScale ℓ u) ^ 2 *
          (∫ x in Submission.BoseGases.abox n ℓ, G (Function.update x j u)) :=
    integral_congr_ae (Filter.Eventually.of_forall fun u => integral_const_mul _ _)
  -- hM4 : the slot-peel of the inner integral
  have hM4 : (∫ u in boxL ℓ, (Submission.BoseGases.chiScale ℓ u) ^ 2 *
        (∫ x in Submission.BoseGases.abox n ℓ, G (Function.update x j u)))
      = ∫ u in boxL ℓ, (Submission.BoseGases.chiScale ℓ u) ^ 2 *
          (ℓ ^ 3 * ∫ x' in boxPiSet ({k : Fin n // k ≠ j}) ℓ, G (insertCoord j u x')) := by
    have hfun : (fun u : E3 => (Submission.BoseGases.chiScale ℓ u) ^ 2 *
          (∫ x in Submission.BoseGases.abox n ℓ, G (Function.update x j u)))
        = fun u : E3 => (Submission.BoseGases.chiScale ℓ u) ^ 2 *
            (ℓ ^ 3 * ∫ x' in boxPiSet ({k : Fin n // k ≠ j}) ℓ, G (insertCoord j u x')) := by
      funext u
      rw [abox_integral_update_eq_mul_slice j hℓ Gm ⟨Cg, hCg⟩ u]
    rw [hfun]
  -- hM5 : pull `ℓ³` out
  have hM5 : (∫ u in boxL ℓ, (Submission.BoseGases.chiScale ℓ u) ^ 2 *
        (ℓ ^ 3 * ∫ x' in boxPiSet ({k : Fin n // k ≠ j}) ℓ, G (insertCoord j u x')))
      = ℓ ^ 3 * ∫ u in boxL ℓ, (Submission.BoseGases.chiScale ℓ u) ^ 2 *
          (∫ x' in boxPiSet ({k : Fin n // k ≠ j}) ℓ, G (insertCoord j u x')) := by
    have hfun : (fun u : E3 => (Submission.BoseGases.chiScale ℓ u) ^ 2 *
          (ℓ ^ 3 * ∫ x' in boxPiSet ({k : Fin n // k ≠ j}) ℓ, G (insertCoord j u x')))
        = fun u : E3 => ℓ ^ 3 * ((Submission.BoseGases.chiScale ℓ u) ^ 2 *
            ∫ x' in boxPiSet ({k : Fin n // k ≠ j}) ℓ, G (insertCoord j u x')) := by
      funext u; ring
    rw [hfun, integral_const_mul]
  -- hM6 : the same normal form from the right-hand side
  have hb6 : ∀ x : Xn n, ‖(Submission.BoseGases.chiScale ℓ (x j)) ^ 2 * G x‖ ≤ D ^ 2 * Cg := by
    intro x
    rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _)]
    exact mul_le_mul (hDa (x j)) (hCg x) (norm_nonneg _) (sq_nonneg D)
  have hM6 : (∫ x in Submission.BoseGases.abox n ℓ,
        (Submission.BoseGases.chiScale ℓ (x j)) ^ 2 * G x)
      = ∫ u in boxL ℓ, (Submission.BoseGases.chiScale ℓ u) ^ 2 *
          (∫ x' in boxPiSet ({k : Fin n // k ≠ j}) ℓ, G (insertCoord j u x')) := by
    have hInt6 : IntegrableOn (fun x : Xn n => (Submission.BoseGases.chiScale ℓ (x j)) ^ 2 * G x)
        (Submission.BoseGases.abox n ℓ) volume :=
      IntegrableOn.of_bound (pb3_volume_abox_ne_top hℓ).lt_top
        ((((Submission.BoseGases.chiScale_continuous ℓ).measurable.comp
          (measurable_pi_apply j)).pow_const 2).mul Gm).aestronglyMeasurable (D ^ 2 * Cg)
        (Filter.Eventually.of_forall hb6)
    rw [pb3_slice_peel_real j hℓ hInt6]
    have hsub : (fun w : E3 => ∫ x' in boxPiSet ({k : Fin n // k ≠ j}) ℓ,
          (Submission.BoseGases.chiScale ℓ (insertCoord j w x' j)) ^ 2 *
            G (insertCoord j w x'))
        = fun w : E3 => (Submission.BoseGases.chiScale ℓ w) ^ 2 *
            ∫ x' in boxPiSet ({k : Fin n // k ≠ j}) ℓ, G (insertCoord j w x') := by
      funext w
      have h2 : (fun x' : {k : Fin n // k ≠ j} → E3 =>
            (Submission.BoseGases.chiScale ℓ (insertCoord j w x' j)) ^ 2 *
              G (insertCoord j w x'))
          = fun x' => (Submission.BoseGases.chiScale ℓ w) ^ 2 * G (insertCoord j w x') := by
        funext x'
        rw [insertCoord_self]
      rw [h2, integral_const_mul]
    rw [hsub]
  rw [hM1, hM2, hM3, hM4, hM5, hM6]

/-! ## 3. The target statement -/

theorem pb3_mass_ident {n : ℕ} {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} (i j : Fin n)
    (hij : i ≠ j) {Θ : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ}
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ)) :
    (∫ x in Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ), ∫ u : EuclideanSpace ℝ (Fin 3),
        (Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) u) ^ 2
          * ‖Work.BoseBoxFock.aQC (Work.BoseBoxFock.ellH v μ) j
              (Work.BoseBoxFock.aPC (Work.BoseBoxFock.ellH v μ) i Θ)
              (Function.update x j u)‖ ^ 2)
      = (Work.BoseBoxFock.ellH v μ) ^ 3 *
        ∫ x in Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ),
          (Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) (x j)) ^ 2
            * ‖Work.BoseBoxFock.aQC (Work.BoseBoxFock.ellH v μ) j
                (Work.BoseBoxFock.aPC (Work.BoseBoxFock.ellH v μ) i Θ) x‖ ^ 2 := by
  have hℓ : 0 < ellH v μ := ellH_pos v μ
  obtain ⟨C₀, hC₀⟩ := hΘb
  let C : ℝ := max C₀ 0
  have hC0 : 0 ≤ C := le_max_right _ _
  have hCb : ∀ x, ‖Θ x‖ ≤ C := fun x => le_trans (hC₀ x) (le_max_left _ _)
  have hPC : Measurable (aPC (ellH v μ) i Θ) := aPC_measurable' i hΘm
  have hbPC : ∀ y, ‖aPC (ellH v μ) i Θ y‖ ≤ C := norm_aPC_le hℓ i hC0 hCb
  refine pb3_mass_ident_aux (G := fun y => ‖aQC (ellH v μ) j (aPC (ellH v μ) i Θ) y‖ ^ 2)
    j hℓ ?_ ?_
  · have h2 : aQC (ellH v μ) j (aPC (ellH v μ) i Θ)
        = fun y : Xn n => aPC (ellH v μ) i Θ y
            - aPC (ellH v μ) j (aPC (ellH v μ) i Θ) y := by
      funext y; rw [aQC_apply]
    rw [h2]
    exact ((hPC.sub (aPC_measurable' j hPC)).norm).pow_const 2
  · refine ⟨(2 * C) ^ 2, fun y => ?_⟩
    have h3 : ‖aQC (ellH v μ) j (aPC (ellH v μ) i Θ) y‖ ≤ 2 * C := by
      rw [aQC_apply]
      calc ‖aPC (ellH v μ) i Θ y - aPC (ellH v μ) j (aPC (ellH v μ) i Θ) y‖
          ≤ ‖aPC (ellH v μ) i Θ y‖ + ‖aPC (ellH v μ) j (aPC (ellH v μ) i Θ) y‖ := norm_sub_le _ _
        _ ≤ C + C := add_le_add (hbPC y) (norm_aPC_le hℓ j hC0 hbPC y)
        _ = 2 * C := by ring
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) h3 2

end

end Work.BoseBoxFock
