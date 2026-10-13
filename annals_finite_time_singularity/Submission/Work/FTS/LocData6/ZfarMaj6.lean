/-
# `Work.FTS.LocData6.ZfarMaj6` — the order-`6` radial bound and pointwise majorant of the far
summand of the localised datum

`zfarR L z = (1 - χ(z/L))·FM.Fstar z` is the radial factor of the far part of the localised
profile (`LocDataExt/Defs.lean`), so that

  `zfar L F_* = (α/c)·Γ(θ)·zfarR L z`  and the far summand of `locG` is
  `fun z θ => (-(α/c)·zfarR L z)·Γ(θ)`.

This module proves, from the **order-`6` jet bound of `zfarR L`** (which the sibling module
`LocData6.zfarR_jet_le6_of_jets` derives from the cut-off and profile jets),

* `hB_zfar6` — the radial input of the generic separable majorant
  (`LocDataExt.HkIntegrand_sepGam_le`) at order `6`:
  `((D_z^j (-(α/c)·zfarR L)) z · w z)² ≤ ((α/c)²A²·64)/(1+z)²`;
* `HkIntegrand_zfar6_le` — the resulting pointwise majorant of the `ℋ⁶`-integrand of the far
  summand, by `K·angMaj α θ/(1+z)²` with `K = (7 + 49·Rθ)·(α/c)²A²·64`.

Both are *conditional* on the jet bound and on the angular bound `(D_θ^iΓ)² ≤ Rθ·Γ²`, so that
this module is independent of the order-`6` angular and radial jet lemmas; the assembly
instantiates them.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Order.Lattice
import Submission.Work.FTS.LocData6.Defs
import Submission.Work.FTS.LocDataExt.Zfar5

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData6

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The radial bound of the far summand** `-(α/c)·zfarR L z` at order `6`: from the jet bound
`|D_z^j (zfarR L) z| ≤ A/z` on `z ≥ L` (below `L` the cut-off kills the whole expression). -/
theorem hB_zfar6 (α L : ℝ) {A : ℝ} (hA : 0 ≤ A) (hL : 1 ≤ L)
    (hAz : ∀ j ≤ 6, ∀ z ∈ Set.Ici L, ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ| ≤ A / z) :
    ∀ j ≤ 6, ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      (Work.Spaces.DzIter j (fun z _ => -(α / Work.Spaces.c α) * Work.FTS.LocDataExt.zfarR L z)
          z θ * Work.Spaces.w z) ^ 2
        ≤ ((α / Work.Spaces.c α) ^ 2 * A ^ 2 * 64) / (1 + z) ^ 2 := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  intro j hj z hz θ
  rw [Work.FTS.LocDataExt.DzIter_const_mul]
  have hsplit : ((-(α / Work.Spaces.c α)
        * Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ)
        * Work.Spaces.w z) ^ 2
      = (α / Work.Spaces.c α) ^ 2
        * ((Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ)
            * Work.Spaces.w z) ^ 2 := by
    ring
  rw [hsplit]
  have hmain : ((Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ)
        * Work.Spaces.w z) ^ 2 ≤ A ^ 2 * 64 / (1 + z) ^ 2 := by
    by_cases hzL : z < L
    · -- the cut-off vanishes near `z`
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
      have : 0 ≤ A ^ 2 * 64 / (1 + z) ^ 2 :=
        div_nonneg (mul_nonneg (sq_nonneg A) (by norm_num)) (sq_nonneg _)
      simpa using this
    · push_neg at hzL
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
          have h1 : 1 + z ≤ 2 * z := by linarith
          calc (1 + z) ^ 6 ≤ (2 * z) ^ 6 := pow_le_pow_left₀ (by linarith) h1 6
            _ = 64 * z ^ 6 := by ring
        nlinarith [h]
      calc (A / z * Work.Spaces.w z) ^ 2 = A ^ 2 * ((1 + z) ^ 4 / z ^ 6) := by
            rw [Work.Spaces.w]
            field_simp <;> ring
        _ ≤ A ^ 2 * (64 / (1 + z) ^ 2) := mul_le_mul_of_nonneg_left hnum (sq_nonneg A)
        _ = A ^ 2 * 64 / (1 + z) ^ 2 := by ring
  calc (α / Work.Spaces.c α) ^ 2
        * ((Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ)
            * Work.Spaces.w z) ^ 2
      ≤ (α / Work.Spaces.c α) ^ 2 * (A ^ 2 * 64 / (1 + z) ^ 2) :=
        mul_le_mul_of_nonneg_left hmain (sq_nonneg _)
    _ = (α / Work.Spaces.c α) ^ 2 * A ^ 2 * 64 / (1 + z) ^ 2 := by ring

/-- **The pointwise `ℋ⁶`-majorant of the far summand of the localised datum**: with the order-`6`
jet bound of `zfarR L` and the angular bound `(D_θ^iΓ)² ≤ Rθ·Γ²`, the `ℋ⁶`-integrand of
`(-(α/c)·zfarR L)·Γ` is dominated by `((7 + 49·Rθ)·(α/c)²A²·64)·angMaj α θ/(1+z)²`. -/
theorem HkIntegrand_zfar6_le (α L : ℝ) (hα : 0 < α) (hL : 1 ≤ L) {A Rθ : ℝ}
    (hA : 0 ≤ A) (hRθ : 0 ≤ Rθ)
    (hAz : ∀ j ≤ 6, ∀ z ∈ Set.Ici L, ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ| ≤ A / z)
    (hΓ : ∀ i ≤ 6, ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
        ≤ Rθ * (Work.Spaces.Gam α θ) ^ 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6
        (fun z θ => (-(α / Work.Spaces.c α) * Work.FTS.LocDataExt.zfarR L z)
          * Work.Spaces.Gam α θ) z θ
        ≤ K * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2 := by
  refine ⟨((7 : ℝ) + 49 * Rθ) * ((α / Work.Spaces.c α) ^ 2 * A ^ 2 * 64), by positivity,
    fun z hz θ hθ => ?_⟩
  have hB := hB_zfar6 α L hA hL hAz
  exact Work.FTS.LocDataExt.HkIntegrand_sepGam_le α hα 6
    (ρ := fun z => -(α / Work.Spaces.c α) * Work.FTS.LocDataExt.zfarR L z)
    (R := (α / Work.Spaces.c α) ^ 2 * A ^ 2 * 64) (Rθ := Rθ) (by positivity) hRθ
    (fun j hj z hz' θ' => hB j hj z hz' θ') hΓ hz hθ

end Work.FTS.LocData6
