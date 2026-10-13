/-
# `L3MulDz` — the `ℋ³`-bound for the product `h · D_z f`

The target: there is a universal `C > 0` such that for `0 < α ≤ 1`, `h` of class
`Work.FTS.EllipticEst.SmoothOpen` (`C^∞` on the open quadrant `Q0 = (0,∞) × (0,π/2)`) and of
class `𝒲^{4,∞}` (`Work.Spaces.WlInfMem α 4 h`), and `f` of class `SmoothOpen` and `ℋ⁴`
(`Work.Spaces.HkMem α 4 f`), the product `h · D_z f` lies in `ℋ³` and

  `|h · D_z f|²_{ℋ³} ≤ C/(γ-1) · |h|²_{𝒲^{4,∞}} · |f|²_{ℋ⁴}`.

This is the radial sibling of the `D_θ`-statement `L3MulDth`: the product rule of the paper
with the coefficient `h` priced by the weighted norm `𝒲^{4,∞}`.

## The route

`D_z f = z ∂_z f` raises the `f`-side order by one, so `ℋ³`-control of the product only needs
the `ℋ⁴`-slots of `f` — provided one never asks for more than *four* `f`-derivatives, i.e.
provided one treats the slots individually instead of applying a level-four product rule to
`h` and `D_z f` (the latter would require `HkMem α 4 (D_z f)`, which `HkMem α 4 f` does not
give: `HkIntegrand α 4 (D_z f)` sees `D_z^5 f`).

1. `majorant_dz`: summing the Leibniz expansions of the four pure radial slots and the (at
   most sixteen) mixed slots of `HkIntegrand α 3 (h·D_z f)` gives the pointwise majorant
   `HkIntegrand α 3 (h·D_z f) z θ ≤ (4 C_z + 16 C_m)·|h|²_{𝒲^{4,∞}}·GmajW α f z θ`
   on `Iz × Iθ`, where `C_z` and `C_m` price the radial resp. mixed slots (the two delegated
   lemmas `SlotZ`/`SlotM`).  On the angular boundary `sin 2θ = 0` and at `z = 0` the integrand
   vanishes identically.
2. `GmajW α f = HkIntegrand α 4 f + (HgInt α f + (γ-1)^{-1}∑_{d<4}Aang α f d)·TW α` is exactly
   the majorant whose `(z,θ)`-integral is `(1 + 700(1 + 4(γ-1)^{-1}))|f|²_{ℋ⁴}`
   (`Work.FTS.OpenPkg.WProdWin.GmajW_z_integral_le`): in the mixed slots in which all
   `θ`-derivatives fall on `h` the remaining *pure radial* slot `D_z^m f` (`m ≤ 3`) is only
   `w`-weighted, and the mean term `HgInt` (resp. `Aang`) accounts for its angular behaviour.
3. Integrating the majorant gives the membership `HkMem α 3 (h·D_z f)` and
   `HkSq α 3 (h·D_z f) ≤ (4 C_z + 16 C_m)(1 + 700(1 + 4(γ-1)^{-1}))|h|²_{𝒲^{4,∞}}|f|²_{ℋ⁴}`;
   `(γ-1)^{-1} = 10/α ≥ 1` turns the bracket into `C/(γ-1)`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.OpenPkg.WProdWin.Basic
import Submission.Work.FTS.OpenPkg.WProdWin.dzIter_w_mean_le
import Submission.Work.FTS.OpenPkg.DzIter_le_WlInf_open
import Submission.Work.FTS.OpenPkg.Mixed_le_WlInf_open
import Submission.Work.Spaces.H_le_Wt
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed
import Submission.Work.FTS.H2.WPQ.Defs
import Submission.Work.FTS.StrongPersist.L3Rhs.L3MulDzAux
import Submission.Work.FTS.StrongPersist.L3Rhs.L3MulDzBackup
import Submission.Work.FTS.StrongPersist.L3Rhs.L3MulDzBackupM

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs

open Work.FTS.Galerkin (Fn)
open Work.Spaces (HkMem HkSq HkNorm Dz Dth mixed DzIter DthIter HkIntegrand Wt w gam eta)
open Work.FTS.OpenPkg.WProdWin

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Vanishing of the `ℋᵏ`-integrand on the angular boundary

At `sin(2θ) = 0` both weights of `HkIntegrand` vanish (the `1/sin(2θ)^{η/2}` of the radial
block through Lean's division by zero, and `Wt = w·sin(2θ)^{-γ/2}` through `0^{negative}`), so
the integrand vanishes for *every* datum. -/
theorem HkIntegrand_eq_zero_of_sin_two {α : ℝ} (hα : 0 < α) (k : ℕ) (F : ℝ → ℝ → ℝ)
    {z θ : ℝ} (hs : Real.sin (2 * θ) = 0) : HkIntegrand α k F z θ = 0 := by
  rw [HkIntegrand]
  have hsin : (Real.sin (2 * θ)) ^ (eta / 2) = 0 := by
    rw [hs, Real.zero_rpow (by norm_num [eta])]
  have hgam : 0 < gam α := by rw [gam]; linarith
  have hWt : Wt α z θ = 0 := by
    rw [Wt, Work.Spaces.wTheta, hs,
      Real.zero_rpow (neg_ne_zero.mpr (ne_of_gt (div_pos hgam (by norm_num)))), mul_zero]
  have h1 : (∑ i ∈ Finset.range (k + 1),
      (DzIter i F z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hsin, div_zero, mul_zero, zero_pow (by norm_num)]
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      (if 1 ≤ i ∧ i + j ≤ k then (mixed j i F z θ * Wt α z θ) ^ 2 else 0)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    split_ifs with hc
    · rw [hWt, mul_zero, zero_pow (by norm_num)]
    · rfl
  rw [h1, h2, add_zero]

/-! ## The two slot predicates -/

/-- The radial slots of the product `h·D_z f`, with an explicit constant. -/
def SlotZ (C : ℝ) : Prop :=
  ∀ (α : ℝ) (h f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen h → Work.Spaces.WlInfMem α 4 h →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    ∀ i : ℕ, i ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
    (DzIter i (fun z θ => h z θ * Dz f z θ) z θ
        * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2
      ≤ C * (Work.Spaces.WlInf α 4 h) ^ 2 * HkIntegrand α 4 f z θ

/-- The mixed slots of the product `h·D_z f`, with an explicit constant. -/
def SlotM (C : ℝ) : Prop :=
  ∀ (α : ℝ) (h f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen h → Work.Spaces.WlInfMem α 4 h →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    ∀ I J : ℕ, 1 ≤ I → I + J ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
    (mixed J I (fun z θ => h z θ * Dz f z θ) z θ * Wt α z θ) ^ 2
      ≤ C * (Work.Spaces.WlInf α 4 h) ^ 2 * GmajW α f z θ

/-! ## Summing the slots -/

/-- **The pointwise majorant of `HkIntegrand α 3 (h·D_z f)`.**  Each of the four radial slots
costs `C_z |h|²_{𝒲^{4,∞}} HkIntegrand α 4 f` and each of the sixteen (mostly vanishing) mixed
slots costs at most `C_m |h|²_{𝒲^{4,∞}} GmajW α f`; on the angular boundary and at `z = 0` the
integrand vanishes, so the inequality holds on all of `Iz × Iθ`. -/
theorem majorant_dz {Cz Cm : ℝ} (hCz : 0 < Cz) (hCm : 0 < Cm)
    (hzslot : SlotZ Cz) (hmslot : SlotM Cm)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {h f : ℝ → ℝ → ℝ}
    (hsmh : Work.FTS.EllipticEst.SmoothOpen h) (hWm : Work.Spaces.WlInfMem α 4 h)
    (hsmf : Work.FTS.EllipticEst.SmoothOpen f) (hfm : Work.Spaces.HkMem α 4 f) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      HkIntegrand α 3 (fun z θ => h z θ * Dz f z θ) z θ
        ≤ (4 * Cz + 16 * Cm) * (Work.Spaces.WlInf α 4 h) ^ 2 * GmajW α f z θ := by
  set W : ℝ := Work.Spaces.WlInf α 4 h with hWdef
  set X : ℝ → ℝ → ℝ := fun z θ => h z θ * Dz f z θ with hXdef
  intro z hz θ hθ
  have hW : 0 ≤ W := Work.Spaces.WlInf_nonneg α 4 h hWm
  have hC0 : (0 : ℝ) < 4 * Cz + 16 * Cm := by linarith
  have hG : 0 ≤ GmajW α f z θ := GmajW_nonneg hα f hθ
  have hbase : ∀ z' : ℝ, 0 ≤ (4 * Cz + 16 * Cm) * W ^ 2 * GmajW α f z' θ :=
    fun z' => mul_nonneg (mul_nonneg hC0.le (sq_nonneg W))
      (GmajW_nonneg hα f hθ)
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
  · rw [show z = 0 from hz0.symm, Work.Spaces.HkIntegrand_zero_z]
    exact hbase 0
  · by_cases hθi : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
    · have hGle : HkIntegrand α 4 f z θ ≤ GmajW α f z θ :=
        Work.FTS.OpenPkg.WProdWin.HkIntegrand_le_GmajW hα f hθ
      have hsum1 : (∑ i ∈ Finset.range (3 + 1),
            (DzIter i X z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2)
          ≤ 4 * (Cz * W ^ 2 * HkIntegrand α 4 f z θ) := by
        calc (∑ i ∈ Finset.range (3 + 1),
              (DzIter i X z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2)
            ≤ ∑ _i ∈ Finset.range (3 + 1),
                (Cz * W ^ 2 * HkIntegrand α 4 f z θ) := by
              refine Finset.sum_le_sum fun i hi => ?_
              have hi3 : i ≤ 3 := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
              exact hzslot α h f hα hα1 hsmh hWm hsmf hfm i hi3 z θ hzpos hθi.1 hθi.2
          _ = 4 * (Cz * W ^ 2 * HkIntegrand α 4 f z θ) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              norm_num
      have hsum2 : (∑ i ∈ Finset.range (3 + 1), ∑ j ∈ Finset.range (3 + 1),
            (if 1 ≤ i ∧ i + j ≤ 3 then (mixed j i X z θ * Wt α z θ) ^ 2 else 0))
          ≤ 16 * (Cm * W ^ 2 * GmajW α f z θ) := by
        calc (∑ i ∈ Finset.range (3 + 1), ∑ j ∈ Finset.range (3 + 1),
              (if 1 ≤ i ∧ i + j ≤ 3 then (mixed j i X z θ * Wt α z θ) ^ 2 else 0))
            ≤ ∑ _i ∈ Finset.range (3 + 1), ∑ _j ∈ Finset.range (3 + 1),
                (Cm * W ^ 2 * GmajW α f z θ) := by
              refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
              by_cases hc : 1 ≤ i ∧ i + j ≤ 3
              · rw [if_pos hc]
                exact hmslot α h f hα hα1 hsmh hWm hsmf hfm i j hc.1 hc.2 z θ
                  hzpos hθi.1 hθi.2
              · rw [if_neg hc]
                exact mul_nonneg (mul_nonneg (le_of_lt hCm) (sq_nonneg W)) hG
          _ = 16 * (Cm * W ^ 2 * GmajW α f z θ) := by
              simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              ring
      rw [HkIntegrand]
      refine le_trans (add_le_add hsum1 hsum2) ?_
      have h1 : 4 * (Cz * W ^ 2 * HkIntegrand α 4 f z θ)
          ≤ 4 * (Cz * W ^ 2 * GmajW α f z θ) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hGle (mul_nonneg (le_of_lt hCz) (sq_nonneg W)))
          (by norm_num)
      calc 4 * (Cz * W ^ 2 * HkIntegrand α 4 f z θ) + 16 * (Cm * W ^ 2 * GmajW α f z θ)
          ≤ 4 * (Cz * W ^ 2 * GmajW α f z θ) + 16 * (Cm * W ^ 2 * GmajW α f z θ) :=
            add_le_add h1 le_rfl
        _ = (4 * Cz + 16 * Cm) * W ^ 2 * GmajW α f z θ := by ring
    · have hsin : Real.sin (2 * θ) = 0 :=
        Work.Spaces.sin_two_eq_zero_of_not_Ioo hθ hθi
      rw [HkIntegrand_eq_zero_of_sin_two hα 3 X hsin]
      exact hbase z

/-! ## The estimate -/

/-- **`L3MulDz` from the two slot estimates.**  The pointwise majorant is integrated: the
`z`-integral of `GmajW α f` is `≤ (1 + 700(1 + 4(γ-1)^{-1}))|f|²_{ℋ⁴}`, and
`(γ-1)^{-1} = 10/α ≥ 1`, which produces the stated constant `C/(γ-1)`. -/
theorem L3MulDz_of_slots (Cz Cm : ℝ) (hCz : 0 < Cz) (hCm : 0 < Cm)
    (hzslot : SlotZ Cz) (hmslot : SlotM Cm) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (h f : Fn), 0 < α → α ≤ 1 →
        Work.FTS.EllipticEst.SmoothOpen h → Work.Spaces.WlInfMem α 4 h →
        Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
        Work.Spaces.HkMem α 3 (fun z θ => h z θ * Dz f z θ) ∧
        HkSq α 3 (fun z θ => h z θ * Dz f z θ)
          ≤ C / (gam α - 1) * (Work.Spaces.WlInf α 4 h) ^ 2 * HkSq α 4 f := by
  refine ⟨(4 * Cz + 16 * Cm) * 3501, by positivity, ?_⟩
  intro α h f hα hα1 hsmh hWm hsmf hfm
  set W : ℝ := Work.Spaces.WlInf α 4 h with hWdef
  set X : ℝ → ℝ → ℝ := fun z θ => h z θ * Dz f z θ with hXdef
  set K : ℝ := 4 * Cz + 16 * Cm with hKdef
  set Kg : ℝ := 1 + 700 * (1 + 4 * (gam α - 1)⁻¹) with hKgdef
  have hW : 0 ≤ W := Work.Spaces.WlInf_nonneg α 4 h hWm
  have hK : 0 < K := by rw [hKdef]; linarith
  have hγpos : 0 < gam α - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
  have hγinv : 0 ≤ (gam α - 1)⁻¹ := inv_nonneg.mpr hγpos.le
  have hmaj := majorant_dz hCz hCm hzslot hmslot hα hα1 hsmh hWm hsmf hfm
  have hXsm : Work.FTS.EllipticEst.SmoothOpen X :=
    smoothOpen_mul hsmh (Work.FTS.EllipticEst.SmoothOpen.Dz hsmf)
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.IntegrableOn (fun θ => HkIntegrand α 3 X z θ) Work.Spaces.Iθ := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
    · have hzero : (fun θ => HkIntegrand α 3 X 0 θ) = fun _ : ℝ => (0 : ℝ) :=
        funext fun θ => Work.Spaces.HkIntegrand_zero_z α 3 X θ
      rw [show z = 0 from hz0.symm, hzero]
      exact integrableOn_zero
    · refine Integrable.mono'
        ((GmajW_integrableOn_theta hα hα1 hfm hz).const_mul (K * W ^ 2)) ?_ ?_
      · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _
          (hXsm.continuousOn_HkIntegrand α 3) hzpos
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
        rw [Real.norm_of_nonneg (Work.Spaces.HkIntegrand_nonneg α 3 X z θ)]
        exact hmaj z hz θ hθ
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, HkIntegrand α 3 X z θ) ≤ K * W ^ 2 * (Kg * HgInt α f z) := by
    intro z hz
    have hint : MeasureTheory.IntegrableOn (fun θ => (K * W ^ 2) * GmajW α f z θ)
        Work.Spaces.Iθ := (GmajW_integrableOn_theta hα hα1 hfm hz).const_mul _
    have h1 : (∫ θ in Work.Spaces.Iθ, HkIntegrand α 3 X z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, (K * W ^ 2) * GmajW α f z θ :=
      integral_mono_of_nonneg
        (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 3 X z θ) hint
        (ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hmaj z hz θ hθ))
    rw [MeasureTheory.integral_const_mul] at h1
    have h2 : (∫ θ in Work.Spaces.Iθ, GmajW α f z θ) ≤ Kg * HgInt α f z := by
      simpa only [hKgdef] using GmajW_theta_integral_le hα hα1 hfm hz
    calc (∫ θ in Work.Spaces.Iθ, HkIntegrand α 3 X z θ)
        ≤ (K * W ^ 2) * (∫ θ in Work.Spaces.Iθ, GmajW α f z θ) := h1
      _ ≤ (K * W ^ 2) * (Kg * HgInt α f z) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hK.le (sq_nonneg W))
  have hbdd : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, HkIntegrand α 3 X z θ) ≤ (K * W ^ 2 * Kg) * HgInt α f z := by
    intro z hz
    refine le_trans (hinner z hz) (le_of_eq ?_)
    ring
  have hdom : MeasureTheory.IntegrableOn (fun z => (K * W ^ 2 * Kg) * HgInt α f z)
      Work.Spaces.Iz := hfm.2.const_mul _
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, HkIntegrand α 3 X z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h := (Work.Spaces.aesm_of_continuousOn_Qd
      (fun p : ℝ × ℝ => HkIntegrand α 3 X p.1 p.2)
      (hXsm.continuousOn_HkIntegrand α 3)).integral_prod_right'
    have hfun : (fun z => ∫ θ, HkIntegrand α 3 X z θ
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        = (fun z => ∫ θ in Work.Spaces.Iθ, HkIntegrand α 3 X z θ) := rfl
    rw [← hfun]
    exact h
  have hzg : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, HkIntegrand α 3 X z θ) Work.Spaces.Iz := by
    refine Integrable.mono' hdom haesm ?_
    filter_upwards [ae_restrict_mem
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)] with z hz
    rw [Real.norm_of_nonneg
      (integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 3 X z θ)]
    exact hbdd z hz
  refine ⟨⟨hslice, hzg⟩, ?_⟩
  have hHknn : 0 ≤ HkSq α 4 f :=
    integral_nonneg fun z => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ
  have hSq : HkSq α 3 X ≤ (K * W ^ 2 * Kg) * HkSq α 4 f := by
    have h1 : HkSq α 3 X ≤ ∫ z in Work.Spaces.Iz, (K * W ^ 2 * Kg) * HgInt α f z := by
      rw [HkSq]
      exact setIntegral_mono_of_nonneg
        (fun z _ => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 3 X z θ)
        (fun z hz => hbdd z hz) hdom
    rw [MeasureTheory.integral_const_mul, Work.FTS.OpenPkg.WProdWin.HgInt_z_integral] at h1
    exact h1
  have hγ1 : (1 : ℝ) ≤ (gam α - 1)⁻¹ := by
    rw [Work.Spaces.gam_sub_one, one_le_inv₀ (by linarith : (0 : ℝ) < α / 10)]
    linarith
  have hKg_le : Kg ≤ 3501 * (gam α - 1)⁻¹ := by
    rw [hKgdef]
    nlinarith [hγ1]
  have hstep : K * W ^ 2 * Kg ≤ K * W ^ 2 * (3501 * (gam α - 1)⁻¹) :=
    mul_le_mul_of_nonneg_left hKg_le (mul_nonneg hK.le (sq_nonneg W))
  calc HkSq α 3 X ≤ (K * W ^ 2 * Kg) * HkSq α 4 f := hSq
    _ ≤ (K * W ^ 2 * (3501 * (gam α - 1)⁻¹)) * HkSq α 4 f :=
        mul_le_mul_of_nonneg_right hstep hHknn
    _ = ((4 * Cz + 16 * Cm) * 3501) / (gam α - 1) * W ^ 2 * HkSq α 4 f := by
        rw [hKdef]; ring

theorem L3MulDz : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (h f : Work.FTS.Galerkin.Fn), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen h → Work.Spaces.WlInfMem α 4 h →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      Work.Spaces.HkMem α 3 (fun z θ => h z θ * Work.Spaces.Dz f z θ) ∧
      Work.Spaces.HkSq α 3 (fun z θ => h z θ * Work.Spaces.Dz f z θ)
        ≤ C / (Work.Spaces.gam α - 1) * (Work.Spaces.WlInf α 4 h) ^ 2
            * Work.Spaces.HkSq α 4 f := by
  obtain ⟨Cz, hCz, hzslot⟩ := L3MulDzBackup.zslot_dz_le_b
  obtain ⟨Cm, hCm, hmslot⟩ := L3MulDzBackupM.mslot_dz_le_b
  exact L3MulDz_of_slots Cz Cm hCz hCm hzslot hmslot

end Work.FTS.StrongPersist.L3Rhs
