/-
# `Work.FTS.LocData6.HkSq_zfar_Fstar_le6` — the `L⁻¹`-decay of the far part `zfar L F_*` in `ℋ⁶`

The far part of the reference profile is

  `zfar L F_* = (1 - χ(·/L))·F_* = ((α/c)·zfarR L z)·Γ(θ)`   (`LocDataExt.zfar_Fstar_eq`),

so it is *separable*: the angular picture is the fixed profile `Γ`, and the radial picture is
`(α/c)·zfarR L`, which vanishes below `z = L` (the cut-off) and decays like `A/z` above it (the
jets of `FM.Fstar`).  This module turns those two inputs into the far-tail bound

  `HkSq α 6 (zfar L F_*) ≤ C·α/L`   for all `L ≥ 1`,

i.e. the `L⁻¹`-decay of the far datum in `ℋ⁶` — the `hC₀` input of `LocData6.Small6Aux`.

## Structure of the proof

* **The radial input.**  From the order-`6` jet bound `|D_z^j (zfarR L) z| ≤ A/z` on `z ≥ L`
  (below `L` the cut-off makes every jet of `zfarR L` vanish locally), the weighted derivative
  satisfies `((D_z^j ρ) z·w z)² ≤ R/(1+z)²` with `R = (α/c)²A²·64`: for `z ≥ L ≥ 1` one has
  `w²/z² = (1+z)⁴/z⁶ ≤ 64/(1+z)²`.
* **The pointwise majorant.**  The generic separable majorant
  `LocDataExt.HkIntegrand_sepGam_le` at `k = 6` (which needs exactly the radial bound and the
  angular bound `(D_θ^i Γ)² ≤ Rθ·Γ²`) turns the radial input into

    `HkIntegrand α 6 (zfar L F_*) z θ ≤ ((7 + 49Rθ)·(α/c)²A²·64)·angMaj α θ/(1+z)²`.
* **The integral.**  Integrating over `θ ∈ Iθ` and using `(1+z)² ≥ z²` for `z ≥ L ≥ 1` gives
  the far-tail dominance `FarTailDom α 6 M L F_*` for `M = √(K·∫_{Iθ}angMaj)`, whence
  `Work.Stability.HkSqZfar` gives `HkSq α 6 (zfar L F_*) ≤ K·(∫ angMaj)/L`.
* **The constants.**  `Work.Spaces.c_bounds` gives `c α ≥ 1/10`, so `(α/c)² ≤ 100α²`, and
  `α ≤ 1` gives `α² ≤ α`; hence `K·∫ angMaj ≤ (7 + 49Rθ)·100A²·64·(∫ angMaj)·α`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.LocData6.Defs
import Submission.Work.FTS.LocDataExt.Majorant5
import Submission.Work.FTS.LocDataExt.Defs
import Submission.Work.Stability.HkSqZfar
import Submission.Work.FTS.LocData.angMaj_mem
import Submission.Work.Spaces.c_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData6

set_option maxHeartbeats 1600000

/-! ## The two pointwise inputs -/

/-- `(a·X)² ≤ a²·R` from `X² ≤ R` (for an arbitrary real `a`, since `a² ≥ 0`). -/
private theorem sq_mul_le_sq {a X R : ℝ} (h : X ^ 2 ≤ R) : (a * X) ^ 2 ≤ a ^ 2 * R := by
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_left h (sq_nonneg a)

/-- **The radial input of the order-`6` majorant**: the `D_z`-jets of the far factor
`(α/c)·zfarR L` are bounded by `(α/c)²A²·64/(1+z)²` after multiplication with the radial weight
`w` and squaring.

For `z ≥ L` this is the jet bound `hAz` together with `w(z)²/z² ≤ 64/(1+z)²` (which uses
`z ≥ L ≥ 1`); for `z < L` the cut-off vanishes on a neighbourhood of `z`, so every jet of
`zfarR L` vanishes at `z`. -/
private theorem hB_zfar6_pos (α L : ℝ) {A : ℝ} (_hA : 0 ≤ A) (hL : 1 ≤ L)
    (hAz : ∀ j ≤ 6, ∀ z ∈ Set.Ici L, ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ| ≤ A / z) :
    ∀ j ≤ 6, ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      (Work.Spaces.DzIter j (fun z _ => (α / Work.Spaces.c α) * Work.FTS.LocDataExt.zfarR L z)
          z θ * Work.Spaces.w z) ^ 2
        ≤ ((α / Work.Spaces.c α) ^ 2 * A ^ 2 * 64) / (1 + z) ^ 2 := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  intro j hj z hz θ
  have hmain : ((Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ)
        * Work.Spaces.w z) ^ 2 ≤ A ^ 2 * 64 / (1 + z) ^ 2 := by
    by_cases hzL : z < L
    · -- below `L` the cut-off vanishes on a neighbourhood of `z`
      have hzabs : |z| < L := by rw [abs_of_nonneg hz]; exact hzL
      have hev : ∀ᶠ z' in 𝓝 z, Work.FTS.LocDataExt.zfarR L z' = 0 := by
        filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds hzabs] with z' hz'
        rw [Work.FTS.LocDataExt.zfarR_apply, Work.Stability.chi_eq_one (by
          rw [abs_div, abs_of_pos hLpos, div_le_one hLpos]
          exact le_of_lt hz')]
        ring
      have hzero : Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ = 0 :=
        Work.FTS.LocData.ZFBase.DzIter_eq_zero_of_eventually_zero
          (hev.mono (fun z' hz' => fun _ => hz')) j
      rw [hzero]
      have hnn : 0 ≤ A ^ 2 * 64 / (1 + z) ^ 2 :=
        div_nonneg (mul_nonneg (sq_nonneg A) (by norm_num)) (sq_nonneg _)
      simpa using hnn
    · -- above `L` use the jet bound and `w²/z² ≤ 64/(1+z)²`
      push Not at hzL
      have hzpos : 0 < z := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hL) hzL
      have h1 := hAz j hj z hzL θ
      have h2 : ((Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ)
            * Work.Spaces.w z) ^ 2 ≤ (A / z * Work.Spaces.w z) ^ 2 := by
        rw [mul_pow, mul_pow]
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        have h3 := pow_le_pow_left₀ (abs_nonneg _) h1 2
        rwa [sq_abs] at h3
      refine h2.trans ?_
      have hnum : (1 + z) ^ 4 / z ^ 6 ≤ 64 / (1 + z) ^ 2 := by
        rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 6)
          (by positivity : (0 : ℝ) < (1 + z) ^ 2)]
        have h : (1 + z) ^ 6 ≤ 64 * z ^ 6 := by
          have h1' : 1 + z ≤ 2 * z := by linarith
          calc (1 + z) ^ 6 ≤ (2 * z) ^ 6 := pow_le_pow_left₀ (by linarith) h1' 6
            _ = 64 * z ^ 6 := by ring
        nlinarith [h]
      calc (A / z * Work.Spaces.w z) ^ 2 = A ^ 2 * ((1 + z) ^ 4 / z ^ 6) := by
            rw [Work.Spaces.w]
            field_simp
        _ ≤ A ^ 2 * (64 / (1 + z) ^ 2) := mul_le_mul_of_nonneg_left hnum (sq_nonneg A)
        _ = A ^ 2 * 64 / (1 + z) ^ 2 := by ring
  rw [Work.FTS.LocDataExt.DzIter_const_mul]
  have hstep : ((α / Work.Spaces.c α)
        * (Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ
            * Work.Spaces.w z)) ^ 2
      ≤ (α / Work.Spaces.c α) ^ 2 * (A ^ 2 * 64 / (1 + z) ^ 2) :=
    sq_mul_le_sq hmain
  calc ((α / Work.Spaces.c α)
        * Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ
        * Work.Spaces.w z) ^ 2
      = ((α / Work.Spaces.c α)
          * (Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ
              * Work.Spaces.w z)) ^ 2 := by ring
    _ ≤ (α / Work.Spaces.c α) ^ 2 * (A ^ 2 * 64 / (1 + z) ^ 2) := hstep
    _ = (α / Work.Spaces.c α) ^ 2 * A ^ 2 * 64 / (1 + z) ^ 2 := by ring

/-- **The pointwise `ℋ⁶`-majorant of the far part** `zfar L F_*`, from the order-`6` jet bound
of `zfarR L` and the angular bound `(D_θ^iΓ)² ≤ Rθ·Γ²`: the `ℋ⁶`-integrand is dominated by
`((7 + 49Rθ)·(α/c)²A²·64)·angMaj α θ/(1+z)²`.

This is the generic separable majorant `LocDataExt.HkIntegrand_sepGam_le` at `k = 6` applied to
the factorisation `LocDataExt.zfar_Fstar_eq`. -/
private theorem maj_zfar_Fstar6 (α : ℝ) (hα : 0 < α) {A Rθ : ℝ}
    (hA : 0 ≤ A) (hRθ : 0 ≤ Rθ)
    (hAz : ∀ L : ℝ, 1 ≤ L → ∀ j : ℕ, j ≤ 6 → ∀ z ∈ Set.Ici L, ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ| ≤ A / z)
    (hΓ : ∀ i ≤ 6, ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
        ≤ Rθ * (Work.Spaces.Gam α θ) ^ 2) :
    ∀ L : ℝ, 1 ≤ L → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
        ≤ ((7 : ℝ) + 49 * Rθ) * ((α / Work.Spaces.c α) ^ 2 * A ^ 2 * 64)
            * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2 := by
  intro L hL z hz θ hθ
  have hB := hB_zfar6_pos α L hA hL (fun j hj z hz θ => hAz L hL j hj z hz θ)
  have hmain := Work.FTS.LocDataExt.HkIntegrand_sepGam_le α hα 6
    (ρ := fun z => (α / Work.Spaces.c α) * Work.FTS.LocDataExt.zfarR L z)
    (R := (α / Work.Spaces.c α) ^ 2 * A ^ 2 * 64) (Rθ := Rθ)
    (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg A)) (by norm_num)) hRθ hB hΓ hz hθ
  rw [Work.FTS.LocDataExt.zfar_Fstar_eq α L]
  simpa using hmain

/-! ## The far-tail bound -/

theorem HkSq_zfar_Fstar_le6 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {A Rθ : ℝ}
    (hA : 0 ≤ A) (hRθ : 0 ≤ Rθ)
    (hAz : ∀ L : ℝ, 1 ≤ L → ∀ j : ℕ, j ≤ 6 → ∀ z ∈ Set.Ici L, ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ| ≤ A / z)
    (hΓ : ∀ i ≤ 6, ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
        ≤ Rθ * (Work.Spaces.Gam α θ) ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 1 ≤ L →
      Work.Spaces.HkSq α 6 (Work.Stability.zfar L (Work.Construction.Fstar α)) ≤ C * α / L := by
  set Ang : ℝ := ∫ θ in Work.Spaces.Iθ, Work.FTS.LocData.angMaj α θ with hAngdef
  have hAng0 : 0 ≤ Ang := by
    rw [hAngdef]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => Work.FTS.LocData.angMaj_nonneg hθ)
  have hc10 : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hRθ0 : (0 : ℝ) ≤ (7 : ℝ) + 49 * Rθ := by linarith
  refine ⟨((7 : ℝ) + 49 * Rθ) * (100 * A ^ 2 * 64) * Ang, ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg hRθ0 (by positivity)) hAng0
  · intro L hL
    have hLpos : 0 < L := by linarith
    set K : ℝ := ((7 : ℝ) + 49 * Rθ) * ((α / Work.Spaces.c α) ^ 2 * A ^ 2 * 64) with hKdef
    have hK0 : 0 ≤ K := by
      rw [hKdef]
      exact mul_nonneg hRθ0 (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg A)) (by norm_num))
    have hmaj := maj_zfar_Fstar6 α hα hA hRθ hAz hΓ
    have hslice : ∀ z ∈ Work.Spaces.Iz,
        IntegrableOn (fun θ => K * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2) Work.Spaces.Iθ :=
      (Work.FTS.LocData.integrableOn_angMaj_majorant α K hα hα1).1
    have hmajint : ∀ z ∈ Work.Spaces.Iz, L ≤ z →
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6
            (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ) ≤ K * Ang / z ^ 2 := by
      intro z hz hzL
      have hpt : ∀ θ ∈ Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6
          (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
            ≤ K * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2 := by
        intro θ hθ
        rw [hKdef]
        exact hmaj L hL z hz θ hθ
      have hle : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6
            (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ)
          ≤ ∫ θ in Work.Spaces.Iθ, K * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2 := by
        refine MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 6 _ z θ)
          (hslice z hz) ?_
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
        exact hpt θ hθ
      have hval : (∫ θ in Work.Spaces.Iθ, K * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2)
          = K * Ang / (1 + z) ^ 2 := by
        rw [show (fun θ => K * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2)
            = fun θ => (K / (1 + z) ^ 2) * Work.FTS.LocData.angMaj α θ from by
          funext θ; ring]
        rw [MeasureTheory.integral_const_mul, hAngdef]
        ring
      have hzpos : 0 < z := lt_of_lt_of_le hLpos hzL
      have hden : z ^ 2 ≤ (1 + z) ^ 2 := by nlinarith [hzpos]
      have hz2 : (0 : ℝ) < z ^ 2 := by positivity
      have hstep : K * Ang / (1 + z) ^ 2 ≤ K * Ang / z ^ 2 := by
        have hB : ((1 + z) ^ 2)⁻¹ ≤ (z ^ 2)⁻¹ := by
          have h := one_div_le_one_div_of_le hz2 hden
          simpa [one_div] using h
        calc K * Ang / (1 + z) ^ 2 = (K * Ang) * ((1 + z) ^ 2)⁻¹ := by ring
          _ ≤ (K * Ang) * (z ^ 2)⁻¹ := mul_le_mul_of_nonneg_left hB (mul_nonneg hK0 hAng0)
          _ = K * Ang / z ^ 2 := by ring
      linarith [hle, hval.le, hval.ge, hstep]
    -- the far-tail dominance, then `HkSqZfar`
    have hMnn : (0 : ℝ) ≤ K * Ang := mul_nonneg hK0 hAng0
    have hdom : Work.Stability.FarTailDom α 6 (Real.sqrt (K * Ang)) L
        (Work.Construction.Fstar α) := by
      intro z hz hzL
      rw [Real.sq_sqrt hMnn]
      exact hmajint z hz hzL
    have hkey := Work.Stability.HkSqZfar (α := α) (k := 6) (M := Real.sqrt (K * Ang))
      (Z := L) (f := Work.Construction.Fstar α) hLpos (Real.sqrt_nonneg _) hdom
    rw [Real.sq_sqrt hMnn] at hkey
    refine hkey.trans ?_
    -- the constants: `K ≤ (7 + 49Rθ)·100A²·64·α`
    have hA2 : (0 : ℝ) ≤ A ^ 2 := sq_nonneg A
    have hα2 : α ^ 2 ≤ α := by nlinarith [hα, hα1]
    have hq : (α / Work.Spaces.c α) ^ 2 ≤ 100 * α := by
      have hc10' : (1 : ℝ) / Work.Spaces.c α ≤ 10 := by
        rw [div_le_iff₀ hcpos]
        linarith
      have hc100 : ((1 : ℝ) / Work.Spaces.c α) ^ 2 ≤ 100 := by
        have h1 : (0 : ℝ) ≤ 1 / Work.Spaces.c α := by positivity
        have h2 : ((1 : ℝ) / Work.Spaces.c α) ^ 2 ≤ (10 : ℝ) ^ 2 :=
          pow_le_pow_left₀ h1 hc10' 2
        have h3 : (10 : ℝ) ^ 2 = 100 := by norm_num
        rwa [h3] at h2
      have he : (α / Work.Spaces.c α) ^ 2
          = α ^ 2 * ((1 : ℝ) / Work.Spaces.c α) ^ 2 := by
        rw [div_pow]
        ring
      have h3 : α ^ 2 * ((1 : ℝ) / Work.Spaces.c α) ^ 2 ≤ α ^ 2 * 100 :=
        mul_le_mul_of_nonneg_left hc100 (sq_nonneg α)
      have h4 : (α / Work.Spaces.c α) ^ 2 ≤ α ^ 2 * 100 := by
        rw [he]
        exact h3
      nlinarith [h4, hα2, hα.le]
    have hstep : (α / Work.Spaces.c α) ^ 2 * A ^ 2 * 64 ≤ (100 * α) * A ^ 2 * 64 := by
      have h1 : (α / Work.Spaces.c α) ^ 2 * A ^ 2 ≤ (100 * α) * A ^ 2 :=
        mul_le_mul_of_nonneg_right hq hA2
      exact mul_le_mul_of_nonneg_right h1 (by norm_num)
    have hKle : K ≤ ((7 : ℝ) + 49 * Rθ) * (100 * A ^ 2 * 64) * α := by
      rw [hKdef]
      have hfin := mul_le_mul_of_nonneg_left hstep hRθ0
      calc ((7 : ℝ) + 49 * Rθ) * ((α / Work.Spaces.c α) ^ 2 * A ^ 2 * 64)
          ≤ ((7 : ℝ) + 49 * Rθ) * ((100 * α) * A ^ 2 * 64) := hfin
        _ = ((7 : ℝ) + 49 * Rθ) * (100 * A ^ 2 * 64) * α := by ring
    have hKAng : K * Ang ≤ ((7 : ℝ) + 49 * Rθ) * (100 * A ^ 2 * 64) * Ang * α := by
      have h := mul_le_mul_of_nonneg_right hKle hAng0
      calc K * Ang ≤ (((7 : ℝ) + 49 * Rθ) * (100 * A ^ 2 * 64) * α) * Ang := h
        _ = ((7 : ℝ) + 49 * Rθ) * (100 * A ^ 2 * 64) * Ang * α := by ring
    exact div_le_div_of_nonneg_right hKAng (le_of_lt hLpos)

end Work.FTS.LocData6
