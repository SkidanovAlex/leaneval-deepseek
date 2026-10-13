/-
# `Work.FTS.FireFix.PhysData` — the physical data of the reconstruction, fired from `RegPkg'`

This module produces, out of the corrected regularity package `RegPkgGal.RegPkg'` of the
self-similar profile, the four pieces of *data* that the firing theorem needs about the physical
vorticity of the reconstruction — with the sign convention of design correction 1, i.e. for

  `ω := −physOmega α A B g C`.

The four pieces are

* `physOmega_bundle` — **a full admissible strip bundle per physical strip**: for every
  `S' ∈ (0, C.T)` there is `R > 0` with `BSAdmissibleStripFull α ω R S'`.  The fake-time bundle is
  `Prime.PhysVortBundle.physVort_bundle` at the fake strip `[0, τ(S')]`, transported along the
  inverse clock by `Work.FTS.Physical.BiotSavart.bsAdmissibleStripFull_comp_clock` with the clock
  data `Prime.RegPkgClockData.regPkg_clock_data`, and finally negated by
  `Work.FTS.FireFix.BSAdmissibleStripFull_neg`;
* `neg_physOmega_isOdd` — **the velocity is odd at every time**: the slice `ω(·,t)` is the swirl
  field `W(ρ(x),θ(x)) • e_θ(x)` with `W(ρ,·)` odd in the angle (the `θ`-oddness of the profile),
  so `Work.FTS.Physical.isOdd_physVel_of_swirlShape` applies;
* `neg_physOmega_curl_div` — **the curl and divergence clauses**, from the swirl Biot–Savart law
  `Work.FTS.BSSwirl.BiotSavartSwirl` (`hBS`), applied slicewise to the bundle's `HolderWith` and
  support clauses.  This is where the *false* `Work.LWP.BiotSavartLaw` (proved false in Lean, see
  `FTS_NOTBSL.lean.txt`) is replaced;
* `neg_physOmega_datum_holder` — **the `C^{1,α}` datum**, by restricting the jointly `C^{1,α}`
  strip statement to the time slice `t = 0`
  (`Prime.physVel_isContDiffHolder.isContDiffHolder_slice`).

## The factor `2` of the clock

Design correction 2 imposes `C.A = 2·A` (`hAeq`).  The derivative datum of the clock transport is
therefore `d t = (C.A (τ(t)))⁻¹ = (1/2)·(A (τ(t)))⁻¹`, which is bounded and `α`-Hölder because the
corresponding statement for `(A (τ(·)))⁻¹` is (`Prime.RegPkgClockData.regPkg_clock_data`); the
passage is `clock_deriv_data` below.
-/
import Mathlib.Analysis.Calculus.Gradient.Basic
import Submission.Work.FTS.FireFix.Defs
import Submission.Work.FTS.FireFix.BundleNeg
import Submission.Work.FTS.FireFix.Prime.PhysVortBundle
import Submission.Work.FTS.FireFix.Prime.RegPkgClockData
import Submission.Work.FTS.FireFix.Prime.physVel_isContDiffHolder
import Submission.Work.FTS.Physical.BiotSavart
import Submission.Work.FTS.Physical.BiotSavart.bsAdmissibleStripFull_comp_clock
import Submission.Work.FTS.Physical.BiotSavart.isOdd_physVel_of_swirlShape
import Submission.Work.FTS.Physical.Clock.clockInv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.FireFix


/-! ## The clock data at the amplitude normalisation `C.A = 2A` -/

/-- **The derivative datum of the clock transport.**  If `C.A = 2·A` on the fake-time half-line
(design correction 2), then `d t := (C.A (τ(t)))⁻¹` is bounded and `α`-Hölder on `[0,S']` whenever
`τ = Work.FTS.Physical.clockInv C` maps `[0,S']` into `[0,Sel]` and is Lipschitz — the hypotheses of
`bsAdmissibleStripFull_comp_clock`.  The content is that `d = (1/2)·(A ∘ τ)⁻¹`, and the statement
for `(A ∘ τ)⁻¹` is `Prime.RegPkgClockData.regPkg_clock_data`. -/
theorem clock_deriv_data {α S Sel S' : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    {C : Work.FTS.Physical.PhysClock} (hreg : Work.FTS.RegPkgGal.RegPkg' α Sel A B g)
    (hAeq : ∀ τ : ℝ, 0 ≤ τ → C.A τ = 2 * A τ)
    (hmem : ∀ t ∈ Set.Icc (0 : ℝ) S', Work.FTS.Physical.clockInv C t ∈ Set.Icc (0 : ℝ) Sel)
    (hlip : ∃ L : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) S', ∀ t' ∈ Set.Icc (0 : ℝ) S',
      |Work.FTS.Physical.clockInv C t - Work.FTS.Physical.clockInv C t'| ≤ L * |t - t'|) :
    (∃ L : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) S', |(C.A (Work.FTS.Physical.clockInv C t))⁻¹| ≤ L) ∧
      (∃ L : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) S', ∀ t' ∈ Set.Icc (0 : ℝ) S',
        |(C.A (Work.FTS.Physical.clockInv C t))⁻¹ - (C.A (Work.FTS.Physical.clockInv C t'))⁻¹| ≤ L * |t - t'| ^ α) := by
  obtain ⟨hbddA, hholdA⟩ :=
    Prime.regPkg_clock_data (α := α) (S := Sel) (T := S') hreg hmem
      (fun t _ => rfl) hlip
  have hAτ : ∀ t ∈ Set.Icc (0 : ℝ) S', C.A (Work.FTS.Physical.clockInv C t) = 2 * A (Work.FTS.Physical.clockInv C t) :=
    fun t ht => hAeq _ (hmem t ht).1
  refine ⟨?_, ?_⟩
  · obtain ⟨L, hL⟩ := hbddA
    refine ⟨L / 2, fun t ht => ?_⟩
    have h1 : (C.A (Work.FTS.Physical.clockInv C t))⁻¹ = ((2 : ℝ) * A (Work.FTS.Physical.clockInv C t))⁻¹ := by rw [hAτ t ht]
    rw [h1, _root_.mul_inv_rev, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹)]
    calc |(A (Work.FTS.Physical.clockInv C t))⁻¹| * (2 : ℝ)⁻¹
        ≤ L * (2 : ℝ)⁻¹ := mul_le_mul_of_nonneg_right (hL t ht) (by norm_num)
      _ = L / 2 := by ring
  · obtain ⟨L, hL⟩ := hholdA
    refine ⟨L / 2, fun t ht t' ht' => ?_⟩
    have h1 : (C.A (Work.FTS.Physical.clockInv C t))⁻¹ = ((2 : ℝ) * A (Work.FTS.Physical.clockInv C t))⁻¹ := by rw [hAτ t ht]
    have h2 : (C.A (Work.FTS.Physical.clockInv C t'))⁻¹ = ((2 : ℝ) * A (Work.FTS.Physical.clockInv C t'))⁻¹ := by rw [hAτ t' ht']
    have h3 : (C.A (Work.FTS.Physical.clockInv C t))⁻¹
          - (C.A (Work.FTS.Physical.clockInv C t'))⁻¹
        = ((A (Work.FTS.Physical.clockInv C t))⁻¹
            - (A (Work.FTS.Physical.clockInv C t'))⁻¹) * (2 : ℝ)⁻¹ := by
      rw [h1, h2, _root_.mul_inv_rev, _root_.mul_inv_rev]; ring
    rw [h3, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹)]
    calc |(A (Work.FTS.Physical.clockInv C t))⁻¹ - (A (Work.FTS.Physical.clockInv C t'))⁻¹|
            * (2 : ℝ)⁻¹
        ≤ (L * |t - t'| ^ α) * (2 : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right (hL t ht t' ht') (by norm_num)
      _ = L / 2 * |t - t'| ^ α := by ring

/-! ## The per-strip admissible bundles of the (negated) physical vorticity -/

/-- **THE PER-STRIP BUNDLE OF THE PHYSICAL VORTICITY (sign of correction 1).**  For every physical
strip `S' ∈ (0, C.T)` there is a radius `R > 0` such that the negated physical vorticity
`x ↦ −physOmega α A B g C x t` satisfies the full admissible-strip bundle `BSAdmissibleStripFull`
on `[0,S']`.

This is the design's correction 3: the *single* radius is replaced by one radius per strip, read
off `Prime.PhysVortBundle.physVort_bundle` at the fake strip `[0, Work.FTS.Physical.clockInv C S']` and transported
along the clock.  No uniform-in-`τ` support hypothesis (`hZ`) and no bound on the scaling (`hb`) is
needed. -/
theorem physOmega_bundle {α : ℝ≥0} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ} {C : Work.FTS.Physical.PhysClock}
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.RegPkgGal.RegPkg' (α : ℝ) S A B g)
    (hAeq : ∀ τ : ℝ, 0 ≤ τ → C.A τ = 2 * A τ) :
    ∀ S' ∈ Set.Ioo 0 C.T, ∃ R : ℝ,
      Work.CoreResiduals.BSAdmissibleStripFull α
        (fun x t => - Work.FTS.Physical.physOmega (α : ℝ) A B g C x t) R S' := by
  intro S' hS'
  have hS'pos : 0 < S' := hS'.1
  have hS'T : S' < C.T := hS'.2
  have hS'mem : S' ∈ Set.Ico 0 C.T := ⟨hS'pos.le, hS'T⟩
  set Sel : ℝ := Work.FTS.Physical.clockInv C S' with hSeldef
  have hSelpos : 0 < Sel := by rw [hSeldef]; exact Work.FTS.Physical.clockInv_pos_of_pos C hS'
  have hsel : Work.FTS.RegPkgGal.RegPkg' (α : ℝ) Sel A B g := hreg Sel hSelpos
  obtain ⟨R', hR'pos, hbunsel⟩ := Prime.physVort_bundle hsel
  rw [Work.FTS.Physical.nnreal_mk_coe_eq α] at hbunsel
  -- the clock maps `[0,S']` into `[0,Sel]`
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) S', Work.FTS.Physical.clockInv C t ∈ Set.Icc (0 : ℝ) Sel := by
    intro t ht
    have htT : t ∈ Set.Ico 0 C.T := ⟨ht.1, lt_of_le_of_lt ht.2 hS'T⟩
    refine ⟨Work.FTS.Physical.clockInv_nonneg C htT, ?_⟩
    rw [hSeldef]
    exact Work.FTS.Physical.clockInv_mono C htT hS'mem ht.2
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) S',
      HasDerivAt (Work.FTS.Physical.clockInv C) ((C.A (Work.FTS.Physical.clockInv C t))⁻¹) t := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · rw [← h0]
      simpa using Work.FTS.Physical.clockInv_hasDerivAt_zero C
    · exact Work.FTS.Physical.clockInv_hasDerivAt C ⟨h0, lt_of_le_of_lt ht.2 hS'T⟩
  -- the a priori bound on the derivative
  obtain ⟨a₀, _a₁, ha₀pos, ha⟩ := hsel.hAb
  have hbddA : ∀ t ∈ Set.Icc (0 : ℝ) S', |(A (Work.FTS.Physical.clockInv C t))⁻¹| ≤ max (a₀⁻¹) 0 := by
    intro t ht
    have hAt : a₀ ≤ A (Work.FTS.Physical.clockInv C t) := (ha _ (hmem t ht)).1
    have hApos : 0 < A (Work.FTS.Physical.clockInv C t) := lt_of_lt_of_le ha₀pos hAt
    rw [abs_of_pos (inv_pos.mpr hApos)]
    exact le_trans (by simpa [one_div] using one_div_le_one_div_of_le ha₀pos hAt)
      (le_max_left (a₀⁻¹) 0)
  have hbddC : ∀ t ∈ Set.Icc (0 : ℝ) S',
      |(C.A (Work.FTS.Physical.clockInv C t))⁻¹| ≤ max (a₀⁻¹) 0 / 2 := by
    intro t ht
    have h1 : (C.A (Work.FTS.Physical.clockInv C t))⁻¹
        = ((2 : ℝ) * A (Work.FTS.Physical.clockInv C t))⁻¹ := by
      rw [hAeq _ (hmem t ht).1]
    rw [h1, _root_.mul_inv_rev, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹)]
    calc |(A (Work.FTS.Physical.clockInv C t))⁻¹| * (2 : ℝ)⁻¹
        ≤ max (a₀⁻¹) 0 * (2 : ℝ)⁻¹ := mul_le_mul_of_nonneg_right (hbddA t ht) (by norm_num)
      _ = max (a₀⁻¹) 0 / 2 := by ring
  have hlip : ∃ L : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) S', ∀ t' ∈ Set.Icc (0 : ℝ) S',
      |Work.FTS.Physical.clockInv C t - Work.FTS.Physical.clockInv C t'| ≤ L * |t - t'| :=
    Prime.lipschitz_of_hasDerivAt_bounded
      (div_nonneg (le_max_right (a₀⁻¹) 0) (by norm_num)) hderiv hbddC
  -- the two clauses of the derivative datum at the amplitude `C.A = 2A`
  obtain ⟨hdbb, hdhold⟩ := clock_deriv_data (S := Sel) (C := C) hsel hAeq hmem hlip
  have htrans := Work.FTS.Physical.BiotSavart.bsAdmissibleStripFull_comp_clock
    (α := α) hSelpos hS'pos hbunsel hmem hderiv hlip hdbb hdhold
  exact ⟨R', BSAdmissibleStripFull_neg htrans⟩

end Work.FTS.FireFix
