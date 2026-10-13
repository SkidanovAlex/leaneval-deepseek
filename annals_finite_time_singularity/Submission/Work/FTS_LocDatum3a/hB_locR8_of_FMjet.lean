/-
# `Work.FTS_LocDatum3a.hB_locR8_of_FMjet` — the radial bound of `locR` from a profile jet bound

This is the *safe-side* version of `Work.FTS_LocDatum3a.hB_locR8`: instead of importing the
profile jet bound `FTS_LocDatum3a/FM_Fstar_jet_le8` (which transitively imports
`Submission.Work.FTS.LocData.FstarAux` and thereby introduces a second, colliding
`Work.FTS.LocData.T1`), the profile bound

  `|D_z^j (FM.Fstar) z| ≤ CF / z`  for `1 ≤ z`, `j ≤ 8`

is taken as a hypothesis `hF`.  Everything else is the template proof of
`Submission/Work/FTS_LocDatum3a/hB_locR8.lean`, with the two summands of

  `locR α L β z = -(α/c)·zfarR L z + β·bumpZ z`

estimated separately:

* the far summand `-(α/c)·zfarR L` decays like `A/z`: on `[L, 2L]` the Leibniz bound
  `zfarR_jet_le8_of_jets` applies, beyond `2L` the cut-off factor is `1` so `zfarR L = FM.Fstar`
  near `z` and `DzIter_z_congr_of_eventuallyEq` transfers `hF`; below `L` the whole thing vanishes.
  Since `w z = (1+z)²/z²`, the `A/z` bound becomes `A²·64/(1+z)²` using `(1+z)^6 ≤ 64 z^6` for
  `z ≥ 1`.
* the bump summand `β·bumpZ` is supported in `[3/4, 7/4]` with bounded jets
  (`DzIter_bumpZ_bound8`), where `w z² ≤ (1771561/1296)/(1+z)²` (`w_sq_le_on_support`).

The two are glued with `(a+b)² ≤ 2a² + 2b²` after splitting the `D_z`-jets with
`DzIter_add_of_contDiffOn`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.LocDataExt.Defs
import Submission.Work.FTS.LocDataExt.SepFactor
import Submission.Work.FTS.LocDataExt.Zfar5
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.LocData.HlocFactor
import Submission.Work.FTS.LocData.DzIter_bumpZ_bound
import Submission.Work.FTS_LocDatum3a.oneSubChi_jet_le8
import Submission.Work.FTS_LocDatum3a.zfarR_jet_le8_of_jets
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_LocDatum3a

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Aiding lemmas -/

/-- A function of `z` alone, viewed as a function of `(z,θ)`, is jointly `C^n` on the strip
`(-1,∞) × ℝ` as soon as its `z`-slice is `C^n` on `(-1,∞)` (the `θ`-variable is a dummy, so no
restriction on `θ` is needed). -/
theorem contDiffOn_uncurry_zOnly_FMjet {n : ℕ} {φ : ℝ → ℝ}
    (h : ContDiffOn ℝ n φ (Set.Ioi (-1))) :
    ContDiffOn ℝ n (Function.uncurry (fun z (_ : ℝ) => φ z)) (Set.Ioi (-1) ×ˢ Set.univ) := by
  have hfun : Function.uncurry (fun z (_ : ℝ) => φ z) = fun p : ℝ × ℝ => φ p.1 := by
    funext p; rfl
  rw [hfun]
  exact h.comp contDiffOn_fst (fun p hp => hp.1)

/-! ## The `D_z`-jets of `zfarR L` on `[L,∞)`, at order `8` -/

/-- **The `D_z`-jets of the far factor decay like `1/z` on `[L,∞)`.**  On `[L,2L]` the Leibniz
bound `zfarR_jet_le8_of_jets` applies; beyond `2L` the cut-off factor is `1`, so `zfarR L`
agrees with `FM.Fstar` on a neighbourhood of `z` and the profile bound `hCvM` transfers by
`DzIter_z_congr_of_eventuallyEq`. -/
theorem zfarR_jet_le8_Ici_FMjet {Cu Cv : ℝ} (hCu1 : 1 ≤ Cu) (hCv : 0 < Cv)
    (hCu : ∀ L : ℝ, 1 ≤ L → ∀ c : ℕ, c ≤ 8 → ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      |Work.Spaces.DzIter c (fun z _ => (1 : ℝ) - Work.Stability.chi (z / L)) z θ| ≤ Cu)
    (hCvM : ∀ a : ℕ, a ≤ 8 → ∀ z : ℝ, 1 ≤ z → ∀ θ : ℝ,
      |Work.Spaces.DzIter a (fun z _ => Work.FM.Fstar z) z θ| ≤ Cv / z) :
    ∀ L : ℝ, 1 ≤ L → ∀ j : ℕ, j ≤ 8 → ∀ z ∈ Set.Ici L, ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ|
        ≤ max (256 * Cu * Cv) Cv / z := by
  intro L hL j hj z hz θ
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hzpos : 0 < z := lt_of_lt_of_le hLpos hz
  by_cases h : z ≤ 2 * L
  · have h1 := zfarR_jet_le8_of_jets hCu1 hCv hCu hCvM L hL j hj z ⟨hz, h⟩ θ
    exact h1.trans (div_le_div_of_nonneg_right (le_max_left _ _) (le_of_lt hzpos))
  · push_neg at h
    have hev : ∀ᶠ z' in 𝓝 z, Work.FTS.LocDataExt.zfarR L z' = Work.FM.Fstar z' := by
      filter_upwards [(isOpen_lt continuous_const continuous_id).mem_nhds h] with z' hz'
      exact Work.FTS.LocDataExt.zfarR_eq_FM_Fstar_of_ge hLpos (le_of_lt hz')
    rw [Work.FTS.LocDataExt.DzIter_z_congr_of_eventuallyEq hev j θ]
    have h1 := hCvM j hj z (by linarith) θ
    exact h1.trans (div_le_div_of_nonneg_right (le_max_right _ _) (le_of_lt hzpos))

/-- **The unconditional order-`8` jet bound of the far factor on `[L,∞)`**: there is `A > 0`
such that `|D_z^j (zfarR L) z| ≤ A/z` for every `L ≥ 1`, `j ≤ 8`, `z ≥ L` and `θ`, assuming the
profile jet bound. -/
theorem zfarR_jet_le8_clean_Ici_FMjet {CF : ℝ} (hCF : 0 < CF)
    (hF : ∀ j : ℕ, j ≤ 8 → ∀ z : ℝ, 1 ≤ z → ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FM.Fstar z) z θ| ≤ CF / z) :
    ∃ A : ℝ, 0 < A ∧ ∀ L : ℝ, 1 ≤ L → ∀ j : ℕ, j ≤ 8 → ∀ z ∈ Set.Ici L, ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ| ≤ A / z := by
  obtain ⟨Cu, hCu1, hCu⟩ := oneSubChi_jet_le8
  exact ⟨max (256 * Cu * CF) CF, lt_of_lt_of_le hCF (le_max_right _ _),
    zfarR_jet_le8_Ici_FMjet hCu1 hCF hCu hF⟩

/-- **The radial bound of the far summand** `-(α/c)·zfarR L` at order `8`: from the jet bound
`|D_z^j (zfarR L) z| ≤ A/z` on `z ≥ L` (below `L` the cut-off kills the whole expression). -/
theorem hB_zfar8_FMjet (α L : ℝ) {A : ℝ} (hA : 0 ≤ A) (hL : 1 ≤ L)
    (hAz : ∀ j ≤ 8, ∀ z ∈ Set.Ici L, ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ| ≤ A / z) :
    ∀ j ≤ 8, ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
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

/-! ## The bump `bumpZ` at order `8` -/

/-- The `D_z`-jets of the bump `bumpZ = χ(4·-5)` up to order `8` are bounded. -/
theorem DzIter_bumpZ_bound8_FMjet :
    ∃ C : ℝ, ∀ c : ℕ, c ≤ 8 → ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      |Work.Spaces.DzIter c (fun z _ => Work.FTS.LocData.bumpZ z) z θ| ≤ C := by
  classical
  refine ⟨∑ c ∈ Finset.range 9,
    Classical.choose (Work.FTS.LocData.exists_bound_T1_iterate_bumpZ c), ?_⟩
  intro c hc z _ θ
  have hM : ∀ d : ℕ, 0 ≤ Classical.choose (Work.FTS.LocData.exists_bound_T1_iterate_bumpZ d) ∧
      ∀ w : ℝ, |(Work.FTS.LocData.T1^[d]) Work.FTS.LocData.bumpZ w|
        ≤ Classical.choose (Work.FTS.LocData.exists_bound_T1_iterate_bumpZ d) :=
    fun d => Classical.choose_spec (Work.FTS.LocData.exists_bound_T1_iterate_bumpZ d)
  rw [Work.FTS.LocData.DzIter_bumpZ_eq c θ z]
  have h1 : |(Work.FTS.LocData.T1^[c]) Work.FTS.LocData.bumpZ z|
      ≤ Classical.choose (Work.FTS.LocData.exists_bound_T1_iterate_bumpZ c) := (hM c).2 z
  have h2 : Classical.choose (Work.FTS.LocData.exists_bound_T1_iterate_bumpZ c)
      ≤ ∑ d ∈ Finset.range 9,
          Classical.choose (Work.FTS.LocData.exists_bound_T1_iterate_bumpZ d) :=
    Finset.single_le_sum (fun d _ => (hM d).1) (Finset.mem_range.mpr (by omega))
  linarith

/-- The radial bound needed by the assembly for the bump `bumpZ`, at order `8`. -/
theorem hB_bumpZ8_FMjet :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ j ≤ 8, ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      (Work.Spaces.DzIter j (fun z _ => Work.FTS.LocData.bumpZ z) z θ * Work.Spaces.w z) ^ 2
        ≤ R / (1 + z) ^ 2 := by
  obtain ⟨D, hD⟩ := DzIter_bumpZ_bound8_FMjet
  have hD0 : 0 ≤ D := by
    have h := hD 0 (by norm_num) 0 (by simp [Work.Spaces.Iz]) 0
    have h1 : |Work.Spaces.DzIter 0 (fun z _ => Work.FTS.LocData.bumpZ z) 0 0| = 0 := by
      rw [Work.FTS.LocData.DzIter_bumpZ_eq 0 0 0, Function.iterate_zero_apply,
        Work.FTS.LocData.bumpZ_zero, abs_zero]
    linarith [h1 ▸ h]
  refine ⟨D ^ 2 * (1771561 / 1296 : ℝ), by positivity, fun j hj z hz θ => ?_⟩
  by_cases hsupp : z ∈ Set.Icc (3 / 4 : ℝ) (7 / 4)
  · have hw := Work.FTS.LocData.w_sq_le_on_support hsupp
    have h1 : (Work.Spaces.DzIter j (fun z _ => Work.FTS.LocData.bumpZ z) z θ) ^ 2 ≤ D ^ 2 := by
      have h := hD j hj z hz θ
      have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
      rwa [sq_abs] at h2
    rw [mul_pow]
    calc (Work.Spaces.DzIter j (fun z _ => Work.FTS.LocData.bumpZ z) z θ) ^ 2
          * (Work.Spaces.w z) ^ 2
        ≤ D ^ 2 * ((1771561 / 1296 : ℝ) / (1 + z) ^ 2) :=
          mul_le_mul h1 hw (sq_nonneg _) (by positivity)
      _ = D ^ 2 * (1771561 / 1296 : ℝ) / (1 + z) ^ 2 := by ring
  · rw [Work.FTS.LocData.DzIter_bumpZ_eq j θ z,
      Work.FTS.LocData.T1_iterate_bumpZ_eq_zero hsupp j]
    have hD2 : 0 ≤ D ^ 2 * (1771561 / 1296 : ℝ) / (1 + z) ^ 2 :=
      div_nonneg (mul_nonneg (sq_nonneg D) (by norm_num)) (sq_nonneg _)
    simpa using hD2

/-! ## The target -/

theorem hB_locR8_of_FMjet (α L β : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hL : 1 ≤ L)
    {CF : ℝ} (hCF : 0 < CF)
    (hF : ∀ j : ℕ, j ≤ 8 → ∀ z : ℝ, 1 ≤ z → ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FM.Fstar z) z θ| ≤ CF / z) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ j ≤ 8, ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      (Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.locR α L β z) z θ
          * Work.Spaces.w z) ^ 2 ≤ R / (1 + z) ^ 2 := by
  classical
  obtain ⟨A, hApos, hAz⟩ := zfarR_jet_le8_clean_Ici_FMjet hCF hF
  obtain ⟨R₂, hR₂0, hR₂⟩ := hB_bumpZ8_FMjet
  have hzfar := hB_zfar8_FMjet α L (le_of_lt hApos) hL (hAz L hL)
  have hRnn : 0 ≤ 2 * (((α / Work.Spaces.c α) ^ 2 * A ^ 2 * 64) + β ^ 2 * R₂) + 1 := by
    have h1 : 0 ≤ (α / Work.Spaces.c α) ^ 2 * A ^ 2 * 64 := by positivity
    have h2 : 0 ≤ β ^ 2 * R₂ := mul_nonneg (sq_nonneg β) hR₂0
    linarith
  refine ⟨_, hRnn, fun j hj z hz θ => ?_⟩
  -- the two summands of `locR`
  have hsub : (fun z (_ : ℝ) => -(α / Work.Spaces.c α) * Work.FTS.LocDataExt.zfarR L z)
      + (fun z (_ : ℝ) => β * Work.FTS.LocData.bumpZ z)
      = fun z (_ : ℝ) => Work.FTS.LocDataExt.locR α L β z := by
    funext z θ
    simp only [Pi.add_apply, Work.FTS.LocDataExt.locR_apply]
  -- joint smoothness of the two summands on a strip containing `(z,θ)`
  have hφ1 : ContDiffOn ℝ 8
      (fun z : ℝ => -(α / Work.Spaces.c α) * Work.FTS.LocDataExt.zfarR L z)
      (Set.Ioi (-1)) :=
    ((ContDiffOn.const_smul (-(α / Work.Spaces.c α))
      (Work.FTS.LocDataExt.contDiffOn_zfarR L)).congr
        (fun z _ => by simp [smul_eq_mul])).of_le (WithTop.coe_le_coe.mpr le_top)
  have hφ2 : ContDiffOn ℝ 8 (fun z : ℝ => β * Work.FTS.LocData.bumpZ z) (Set.Ioi (-1)) :=
    ((ContDiffOn.const_smul β (Work.FTS.LocData.BumpZ_contDiff.contDiffOn)).congr
      (fun z _ => by simp [smul_eq_mul])).of_le (WithTop.coe_le_coe.mpr le_top)
  have hmem : (z, θ) ∈ Set.Ioi (-1) ×ˢ Set.univ :=
    ⟨show -1 < z by have hz0 : (0 : ℝ) ≤ z := hz; linarith, trivial⟩
  have hadd := Work.FTS.CoercivityFix.Transfer.E2pkg.DzIter_add_of_contDiffOn
    (f₁ := fun z (_ : ℝ) => -(α / Work.Spaces.c α) * Work.FTS.LocDataExt.zfarR L z)
    (f₂ := fun z (_ : ℝ) => β * Work.FTS.LocData.bumpZ z)
    (V := Set.Ioi (-1) ×ˢ Set.univ) (n := 8) (isOpen_Ioi.prod isOpen_univ)
    (contDiffOn_uncurry_zOnly_FMjet hφ1) (contDiffOn_uncurry_zOnly_FMjet hφ2) j hj (z, θ) hmem
  have hloc : Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.locR α L β z) z θ
      = Work.Spaces.DzIter j
          (fun z _ => -(α / Work.Spaces.c α) * Work.FTS.LocDataExt.zfarR L z) z θ
        + Work.Spaces.DzIter j (fun z _ => β * Work.FTS.LocData.bumpZ z) z θ := by
    rw [← hsub]
    exact hadd
  -- the two bounds
  have hzfb := hzfar j hj z hz θ
  have hbmp : (Work.Spaces.DzIter j (fun z _ => β * Work.FTS.LocData.bumpZ z) z θ
      * Work.Spaces.w z) ^ 2 ≤ β ^ 2 * R₂ / (1 + z) ^ 2 := by
    rw [Work.FTS.LocDataExt.DzIter_const_mul]
    rw [show (β * Work.Spaces.DzIter j (fun z _ => Work.FTS.LocData.bumpZ z) z θ
          * Work.Spaces.w z) ^ 2
        = β ^ 2 * ((Work.Spaces.DzIter j (fun z _ => Work.FTS.LocData.bumpZ z) z θ
            * Work.Spaces.w z) ^ 2) from by ring]
    calc β ^ 2 * ((Work.Spaces.DzIter j (fun z _ => Work.FTS.LocData.bumpZ z) z θ
            * Work.Spaces.w z) ^ 2)
        ≤ β ^ 2 * (R₂ / (1 + z) ^ 2) := mul_le_mul_of_nonneg_left (hR₂ j hj z hz θ) (sq_nonneg β)
      _ = β ^ 2 * R₂ / (1 + z) ^ 2 := by ring
  -- put the two together
  rw [hloc]
  set X := Work.Spaces.DzIter j
    (fun z _ => -(α / Work.Spaces.c α) * Work.FTS.LocDataExt.zfarR L z) z θ with hX
  set Y := Work.Spaces.DzIter j (fun z _ => β * Work.FTS.LocData.bumpZ z) z θ with hY
  have hden : (0 : ℝ) < (1 + z) ^ 2 := by
    have hz0 : (0 : ℝ) ≤ z := hz
    positivity
  have hsq : ((X + Y) * Work.Spaces.w z) ^ 2
      ≤ 2 * (X * Work.Spaces.w z) ^ 2 + 2 * (Y * Work.Spaces.w z) ^ 2 := by
    nlinarith [sq_nonneg (X * Work.Spaces.w z - Y * Work.Spaces.w z)]
  calc ((X + Y) * Work.Spaces.w z) ^ 2
      ≤ 2 * (X * Work.Spaces.w z) ^ 2 + 2 * (Y * Work.Spaces.w z) ^ 2 := hsq
    _ ≤ 2 * (((α / Work.Spaces.c α) ^ 2 * A ^ 2 * 64) / (1 + z) ^ 2)
        + 2 * (β ^ 2 * R₂ / (1 + z) ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left hzfb (by norm_num))
          (mul_le_mul_of_nonneg_left hbmp (by norm_num))
    _ = (2 * ((α / Work.Spaces.c α) ^ 2 * A ^ 2 * 64 + β ^ 2 * R₂)) / (1 + z) ^ 2 := by ring
    _ ≤ (2 * (((α / Work.Spaces.c α) ^ 2 * A ^ 2 * 64) + β ^ 2 * R₂) + 1) / (1 + z) ^ 2 :=
        div_le_div_of_nonneg_right (by linarith) (le_of_lt hden)

end Work.FTS_LocDatum3a
