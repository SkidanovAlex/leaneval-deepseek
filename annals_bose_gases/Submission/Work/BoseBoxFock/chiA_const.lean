import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.chiRowDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.chiA_const` — the constant weight is invisible in `chiA`

`chiA n ℓ w Φ = 2Σ_{i≠j}∫_{abox}(PᵢΦ)·w(x_i)·(QᵢPⱼΦ)` is *quadratic* in the pair structure, and a
constant weight contributes nothing: the reason is the structural pairing lemma
`aP_mul_aQ_box`

    ∫_{abox N ℓ} (PᵢΦ)·(QᵢΨ) = 0      (`Φ`, `Ψ` continuous),

i.e. the mean of `QᵢΨ` over the `i`-th cube vanishes while `PᵢΦ` does not depend on the `i`-th
coordinate.  Formally (and without any peel), self-adjointness of `Pᵢ` over the box
(`aP_sym_box`) turns `∫(PᵢΦ)(PᵢΨ)` into `∫Φ·(Pᵢ(PᵢΨ)) = ∫Φ·(PᵢΨ)` (`aP_idem`) and
`∫(PᵢΦ)Ψ` into `∫Φ·(PᵢΨ)`; the two are equal, so the difference
`∫(PᵢΦ)(Ψ − PᵢΨ) = ∫(PᵢΦ)(QᵢΨ)` vanishes.

Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option maxHeartbeats 800000

local notation "Sp" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

/-- The product of two fibre means is integrable on the centred box.  (Both factors are bounded on
the box by `aP_abs_le` and are a.e. strongly measurable by `aP_aestronglyMeasurable`.) -/
lemma integrableOn_aP_mul_aP {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {Φ Ψ : X N → ℝ}
    (hΦc : Continuous Φ) (hΨc : Continuous Ψ) :
    IntegrableOn (fun x : X N => aP ℓ i Φ x * aP ℓ i Ψ x) (abox N ℓ) volume := by
  obtain ⟨B, hB⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn (s := abox N ℓ) (f := Φ)
    hΦc.continuousOn
  obtain ⟨B', hB'⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn (s := abox N ℓ) (f := Ψ)
    hΨc.continuousOn
  have hB0 : 0 ≤ B := by
    have hb := hB (0 : X N) (zero_mem_abox hℓ.le)
    exact le_trans (norm_nonneg (Φ (0 : X N))) hb
  have hB'0 : 0 ≤ B' := by
    have hb := hB' (0 : X N) (zero_mem_abox hℓ.le)
    exact le_trans (norm_nonneg (Ψ (0 : X N))) hb
  refine IntegrableOn.of_bound (s := abox N ℓ)
    (f := fun x : X N => aP ℓ i Φ x * aP ℓ i Ψ x) (C := B * B')
    (abox_compact N hℓ).measure_lt_top
    ((aP_aestronglyMeasurable hℓ i hΦc).mul (aP_aestronglyMeasurable hℓ i hΨc)) ?_
  rw [ae_restrict_iff' (abox_measurable N ℓ)]
  exact ae_of_all volume (by
    intro x hx
    have h1 : |aP ℓ i Φ x| ≤ B :=
      aP_abs_le hℓ i hΦc hB0 (fun y hy => by simpa [Real.norm_eq_abs] using hB y hy) x hx
    have h2 : |aP ℓ i Ψ x| ≤ B' :=
      aP_abs_le hℓ i hΨc hB'0 (fun y hy => by simpa [Real.norm_eq_abs] using hB' y hy) x hx
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul h1 h2 (abs_nonneg _) hB0)

/-- **The `P`–`Q` pairing over the centred box vanishes**: `∫_{abox N ℓ}(PᵢΦ)·(QᵢΨ) = 0` for
continuous `Φ`, `Ψ`.  (`QᵢΨ = Ψ − PᵢΨ` has vanishing `i`-th fibre mean while `PᵢΦ` is independent
of the `i`-th coordinate; the proof below uses self-adjointness of `Pᵢ` instead of a peel.) -/
lemma aP_mul_aQ_box {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {Φ Ψ : X N → ℝ}
    (hΦc : Continuous Φ) (hΨc : Continuous Ψ) :
    (∫ x in abox N ℓ, aP ℓ i Φ x * aQ ℓ i Ψ x) = 0 := by
  have hRc : Continuous (aP ℓ i Ψ) := aP_continuous hℓ i hΨc
  have hI1 : IntegrableOn (fun x : X N => aP ℓ i Φ x * Ψ x) (abox N ℓ) volume := by
    simpa only [mul_comm] using integrableOn_mul_aP hℓ i hΨc hΦc
  have hI2 : IntegrableOn (fun x : X N => aP ℓ i Φ x * aP ℓ i Ψ x) (abox N ℓ) volume :=
    integrableOn_aP_mul_aP hℓ i hΦc hΨc
  have hkey : (∫ x in abox N ℓ, aP ℓ i Φ x * aP ℓ i Ψ x)
      = ∫ x in abox N ℓ, aP ℓ i Φ x * Ψ x := by
    calc
      (∫ x in abox N ℓ, aP ℓ i Φ x * aP ℓ i Ψ x)
          = ∫ x in abox N ℓ, Φ x * aP ℓ i (aP ℓ i Ψ) x := aP_sym_box hℓ i hΦc hRc
      _ = ∫ x in abox N ℓ, Φ x * aP ℓ i Ψ x := by
            apply integral_congr_ae
            filter_upwards with x
            rw [aP_idem hℓ i hΨc]
      _ = ∫ x in abox N ℓ, aP ℓ i Φ x * Ψ x := (aP_sym_box hℓ i hΦc hΨc).symm
  calc
    (∫ x in abox N ℓ, aP ℓ i Φ x * aQ ℓ i Ψ x)
        = ∫ x in abox N ℓ, (aP ℓ i Φ x * Ψ x - aP ℓ i Φ x * aP ℓ i Ψ x) := by
          apply integral_congr_ae
          filter_upwards with x
          unfold aQ
          ring
    _ = (∫ x in abox N ℓ, aP ℓ i Φ x * Ψ x)
          - (∫ x in abox N ℓ, aP ℓ i Φ x * aP ℓ i Ψ x) := integral_sub hI1 hI2
    _ = 0 := by rw [hkey]; ring

/-- **Constants are invisible in `chiA`.**  Every entry of the double sum is
`c·∫_{abox}(PᵢΦ)·(QᵢPⱼΦ) = 0` by `aP_mul_aQ_box` (the second slot is `PⱼΦ`, continuous by
`aP_continuous`). -/
theorem chiA_const {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ) (c : ℝ) :
    Work.BoseBoxFock.chiA n ℓ (fun _ : EuclideanSpace ℝ (Fin 3) => c) Φ = 0 := by
  have hzero : ∀ i j : Fin n,
      (if i = j then (0 : ℝ) else
        ∫ x in abox n ℓ, (aP ℓ i Φ x) * (fun _ : Sp => c) (x i) *
          (aQ ℓ i (fun y : X n => aP ℓ j Φ y) x)) = 0 := by
    intro i j
    by_cases hij : i = j
    · rw [if_pos hij]
    · rw [if_neg hij]
      have hcontj : Continuous (aP ℓ j Φ) := aP_continuous hℓ j hΦc
      have hpq : (∫ x in abox n ℓ, aP ℓ i Φ x *
            aQ ℓ i (fun y : X n => aP ℓ j Φ y) x) = 0 :=
        aP_mul_aQ_box hℓ i hΦc hcontj
      have hconst : (fun x : X n => (aP ℓ i Φ x) * (fun _ : Sp => c) (x i) *
            (aQ ℓ i (fun y : X n => aP ℓ j Φ y) x))
          = fun x : X n => c * (aP ℓ i Φ x *
              aQ ℓ i (fun y : X n => aP ℓ j Φ y) x) := by
        funext x
        change aP ℓ i Φ x * c * aQ ℓ i (fun y : X n => aP ℓ j Φ y) x
          = c * (aP ℓ i Φ x * aQ ℓ i (fun y : X n => aP ℓ j Φ y) x)
        ring
      rw [hconst, MeasureTheory.integral_const_mul, hpq, mul_zero]
  unfold chiA
  have hsum : (∑ i : Fin n, ∑ j : Fin n,
      (if i = j then (0 : ℝ) else
        ∫ x in abox n ℓ, (aP ℓ i Φ x) * (fun _ : Sp => c) (x i) *
          (aQ ℓ i (fun y : X n => aP ℓ j Φ y) x))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    exact hzero i j
  rw [hsum, mul_zero]

end Work.BoseBoxFock
