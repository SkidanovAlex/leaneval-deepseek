/-
# `Work.FTS_RegExport.RXB.l12_aux` — assembly lemmas for the zero-mode passage to the limit

Auxiliary material for `Work.FTS_RegExport.RXB.l12_zero_lim_proved` (item RX-B of the
`FTS_RegExport` design): the zero mode of `L₁₂` passes to the limit along the class-C
approximants supplied by `Work.FTS.FinalV2.LimApprox`.

The mathematical content is assembled here from two analytic inputs about a datum
`f` which is `C^∞` on the open quadrant, honestly in `ℋ⁴` and with vanishing boundary traces:

* `SupBnd α C` : the interior `L^∞`–`ℋ⁴` bound `(f z θ)² ≤ C·HkSq α 4 f` (Elgindi's
  Corollary `SecondDerivativesBounded`); used to dominate the angular slices in the
  convergence of `L₁₂dens`;
* `DensBnd α C` : the weighted density bound `|L₁₂dens f s| ≤ C·(√s/(1+s)²)·HkNorm α 4 f`,
  which turns the uniform `ℋ⁴`-bound of the approximants into an `L¹(ds)` majorant.

The statements `sup_bound_all_alpha` and `l12dens_weighted_bound` for the two inputs live in
sibling modules of this directory.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.StrongEps.L12_tendsto_of_dominated
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.MeridianDyn.Bridge.ProfDerivData_of_regPkg_closed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXB

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## The majorant weight `√s/(1+s)²` is integrable on `(0,∞)` -/

theorem integrableOn_sqrt_div_sq :
    MeasureTheory.IntegrableOn (fun s : ℝ => Real.sqrt s / (1 + s) ^ 2) (Set.Ioi 0) := by
  have hfcont : ContinuousOn (fun s : ℝ => Real.sqrt s / (1 + s) ^ 2) (Set.Ioi 0) := by
    refine ContinuousOn.div Real.continuous_sqrt.continuousOn
      ((continuous_const.add continuous_id).continuousOn.pow 2) ?_
    intro s hs
    have h0 : (0:ℝ) < s := hs
    positivity
  -- `√s/(1+s)² ≤ 1` on `(0,1]`
  have h1 : MeasureTheory.IntegrableOn (fun s : ℝ => Real.sqrt s / (1 + s) ^ 2) (Set.Ioc 0 1) := by
    refine MeasureTheory.Integrable.mono'
      (MeasureTheory.integrableOn_const (s := Set.Ioc (0:ℝ) 1) (C := (1:ℝ)) measure_Ioc_lt_top.ne) ?_ ?_
    · exact (hfcont.mono (fun s hs => hs.1)).aestronglyMeasurable measurableSet_Ioc
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc ?_
      intro s hs
      have hs0 : (0:ℝ) < s := hs.1
      have hpos : (0:ℝ) < (1 + s) ^ 2 := by positivity
      have hle : Real.sqrt s ≤ (1 + s) ^ 2 := by
        have h1s : (1:ℝ) + s ≤ (1 + s) ^ 2 := by nlinarith
        have h2s : Real.sqrt s ≤ 1 + s := by
          rw [Real.sqrt_le_iff]
          exact ⟨by nlinarith, by linarith⟩
        linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact (div_le_one hpos).mpr hle
  -- `√s/(1+s)² ≤ s^{-3/2}` on `(1,∞)`
  have h2 : MeasureTheory.IntegrableOn (fun s : ℝ => Real.sqrt s / (1 + s) ^ 2) (Set.Ioi 1) := by
    refine MeasureTheory.Integrable.mono'
      ((integrableOn_Ioi_rpow_iff (s := -(3/2:ℝ)) (t := (1:ℝ))
        (by norm_num)).mpr (by norm_num)) ?_ ?_
    · exact (hfcont.mono (fun s hs => lt_trans (by norm_num) hs)).aestronglyMeasurable measurableSet_Ioi
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
      intro s hs
      have hs1 : (1:ℝ) < s := hs
      have hs0 : (0:ℝ) < s := lt_trans (by norm_num) hs1
      have hpos : (0:ℝ) < (1 + s) ^ 2 := by positivity
      have hs2 : (0:ℝ) < s ^ 2 := by positivity
      have hle : Real.sqrt s / (1 + s) ^ 2 ≤ s ^ (-(3/2:ℝ)) := by
        have hsq : s ^ 2 ≤ (1 + s) ^ 2 := by nlinarith
        calc Real.sqrt s / (1 + s) ^ 2 ≤ Real.sqrt s / s ^ 2 :=
              div_le_div_of_nonneg_left (Real.sqrt_nonneg s) hs2 hsq
          _ = s ^ (-(3/2:ℝ)) := by
              rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast s 2, ← Real.rpow_sub hs0]
              norm_num
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hle
  have hunion : Set.Ioc (0:ℝ) 1 ∪ Set.Ioi (1:ℝ) = Set.Ioi (0:ℝ) := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (⟨h0, _⟩ | h1) <;> linarith
    · intro hx
      by_cases h : x ≤ 1
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr (lt_of_not_ge h)
  rw [← hunion]
  exact h1.union h2


/-! ## The two analytic inputs, as predicates -/

/-- **The interior `L^∞`–`ℋ⁴` bound** (Elgindi's Corollary `SecondDerivativesBounded`): for a
datum which is `C^∞` on the open quadrant, honestly in `ℋ⁴` and with vanishing boundary traces,
the pointwise value is controlled by the `ℋ⁴`-size. -/
def SupBnd (α C : ℝ) : Prop :=
  ∀ f : Work.FTS.Galerkin.Fn, Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    Work.FTS.Nonlin.BdryTraces α 4 f →
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → (f z θ) ^ 2 ≤ C * Work.Spaces.HkSq α 4 f

/-- **The weighted bound on the zero mode of `L₁₂`**: the density `L₁₂dens f s` is dominated by
the (integrable on `(0,∞)`) weight `√s/(1+s)²` times the `ℋ⁴`-norm of `f`. -/
def DensBnd (α C : ℝ) : Prop :=
  ∀ f : Work.FTS.Galerkin.Fn, Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    Work.FTS.Nonlin.BdryTraces α 4 f →
    ∀ s : ℝ, 0 < s →
      |Work.Construction.L12dens f s|
        ≤ C * (Real.sqrt s / (1 + s) ^ 2) * Work.Spaces.HkNorm α 4 f

/-! ## The angular dominated convergence of the `L₁₂`-density -/

theorem continuous_K : Continuous Work.Spaces.K :=
  show Continuous (fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2) from by fun_prop

/-- **Convergence of the `L₁₂`-density of a converging sequence.**  If the profiles `fn n` carry
the interior class data with a uniform `ℋ⁴`-bound `Λ` and the *sup bound* `SupBnd α C`, and if
`fn n → F` pointwise on the open quadrant, then `L₁₂dens (fn n) s → L₁₂dens F s` at every
`s > 0` (dominated convergence in the angular variable). -/
theorem tendsto_L12dens_of_sup_bound {α C Λ : ℝ} (hΛ : 0 ≤ Λ) (hC : 0 < C)
    (hsup : SupBnd α C) {fn : ℕ → Work.FTS.Galerkin.Fn} {F : Work.FTS.Galerkin.Fn}
    (hcls : ∀ n, Work.FTS.EllipticEst.SmoothOpen (fn n) ∧ Work.Spaces.HkMem α 4 (fn n) ∧
      Work.FTS.Nonlin.BdryTraces α 4 (fn n))
    (hN : ∀ n, Work.Spaces.HkNorm α 4 (fn n) ≤ Λ)
    (hjet : ∀ s θ : ℝ, 0 < s → 0 < θ → θ < Real.pi / 2 →
      Tendsto (fun n => fn n s θ) atTop (𝓝 (F s θ)))
    {s : ℝ} (hs : 0 < s) :
    Tendsto (fun n => Work.FM.L12dens Work.Spaces.K (fn n) s) atTop
      (𝓝 (Work.FM.L12dens Work.Spaces.K F s)) := by
  have haeθ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (Real.pi / 2) := by
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc]
    filter_upwards [MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
      (b := Real.pi / 2)] with θ h
    exact fun hmem => h.mpr hmem
  -- the uniform pointwise bound on the slices
  have hpt : ∀ (n : ℕ) (θ : ℝ), θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |fn n s θ| ≤ Real.sqrt C * Λ := by
    intro n θ hθ
    have hs2 : (fn n s θ) ^ 2 ≤ C * Work.Spaces.HkSq α 4 (fn n) :=
      hsup (fn n) (hcls n).1 (hcls n).2.1 (hcls n).2.2 s θ hs hθ.1 hθ.2
    have hsq : Work.Spaces.HkSq α 4 (fn n) = (Work.Spaces.HkNorm α 4 (fn n)) ^ 2 := by
      rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 (fn n))]
    have hle : Work.Spaces.HkSq α 4 (fn n) ≤ Λ ^ 2 := by
      rw [hsq]
      exact sq_le_sq' (by linarith [Work.Spaces.HkNorm_nonneg α 4 (fn n), hN n]) (hN n)
    have habs : |fn n s θ| = Real.sqrt ((fn n s θ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    rw [habs]
    calc Real.sqrt ((fn n s θ) ^ 2) ≤ Real.sqrt (C * Work.Spaces.HkSq α 4 (fn n)) :=
          Real.sqrt_le_sqrt hs2
      _ ≤ Real.sqrt (C * Λ ^ 2) := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hle hC.le)
      _ = Real.sqrt C * Λ := by
          rw [Real.sqrt_mul hC.le, Real.sqrt_sq hΛ]
  have hbound : ∀ n, ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      ‖Work.Spaces.K θ * fn n s θ / s‖ ≤ Real.sqrt C * Λ / s * |Work.Spaces.K θ| := by
    intro n
    filter_upwards [haeθ] with θ hθ
    have h1 : |fn n s θ| ≤ Real.sqrt C * Λ := hpt n θ hθ
    have h3 : |fn n s θ| / s ≤ Real.sqrt C * Λ / s := div_le_div_of_nonneg_right h1 hs.le
    rw [norm_div, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_of_nonneg hs.le]
    calc |Work.Spaces.K θ| * |fn n s θ| / s
        = |Work.Spaces.K θ| * (|fn n s θ| / s) := by ring
      _ ≤ |Work.Spaces.K θ| * (Real.sqrt C * Λ / s) :=
          mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
      _ = Real.sqrt C * Λ / s * |Work.Spaces.K θ| := by ring
  have hmeas : ∀ n, AEStronglyMeasurable (fun θ => Work.Spaces.K θ * fn n s θ / s)
      (volume.restrict Work.Spaces.Iθ) := by
    intro n
    refine Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.K p.2 * fn n p.1 p.2 / s) ?_ hs
    refine ContinuousOn.div ?_ continuousOn_const ?_
    · exact ((continuous_K.comp continuous_snd).continuousOn).mul
        ((hcls n).1.forall 1).continuousOn
    · intro p _
      exact ne_of_gt hs
  have hint : Integrable (fun θ => Real.sqrt C * Λ / s * |Work.Spaces.K θ|)
      (volume.restrict Work.Spaces.Iθ) := by
    have h := ContinuousOn.integrableOn_compact (μ := volume) isCompact_Icc
      ((continuous_abs.comp continuous_K).continuousOn (s := Work.Spaces.Iθ))
    exact h.const_mul _
  have hlim : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      Tendsto (fun n => Work.Spaces.K θ * fn n s θ / s) atTop
        (𝓝 (Work.Spaces.K θ * F s θ / s)) := by
    filter_upwards [haeθ] with θ hθ
    exact (((hjet s θ hs hθ.1 hθ.2).const_mul (Work.Spaces.K θ))).div_const s
  have hmain := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := volume.restrict Work.Spaces.Iθ)
    (F := fun n θ => Work.Spaces.K θ * fn n s θ / s)
    (f := fun θ => Work.Spaces.K θ * F s θ / s)
    (fun θ => Real.sqrt C * Λ / s * |Work.Spaces.K θ|) hmeas hint hbound hlim
  simpa only [Work.FM.L12dens, Work.Spaces.Iθ] using hmain


/-! ## The main assembly -/

/-- **`RX-B`: the zero mode of `L₁₂` passes to the limit.**  Given the two analytic inputs
`SupBnd` (interior `L^∞`–`ℋ⁴` bound) and `DensBnd` (weighted bound on the zero mode) at every
`α > 0`, every `τ ≥ 0` has `L₁₂(slice g τ)(0) = 0` for a family `g` which is the pointwise limit
of class-C approximants with a uniform `ℋ⁴`-bound (`LimApprox`). -/
theorem l12_zero_lim_of_bounds {αG C₀ : ℝ} (hα : 0 < αG) {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hsupAll : ∀ α : ℝ, 0 < α → ∃ C : ℝ, 0 < C ∧ SupBnd α C)
    (hdenAll : ∀ α : ℝ, 0 < α → ∃ C : ℝ, 0 < C ∧ DensBnd α C)
    (hA : Work.FTS.FinalV2.LimApprox αG C₀ Φs E g) :
    ∀ τ : ℝ, 0 ≤ τ → Work.Construction.L12 (Work.FTS.Galerkin.slice g τ) 0 = 0 := by
  intro τ hτ
  obtain ⟨Csup, hCsup, hsup⟩ := hsupAll αG hα
  obtain ⟨Cden, hCden, hden⟩ := hdenAll αG hα
  obtain ⟨gn, B, L, hcls, hlip, hjet, hmu⟩ := hA (max τ 1 + 1) (by
    have := le_max_right τ 1
    linarith)
  have hτT : τ ∈ Set.Icc (0:ℝ) (max τ 1 + 1) := by
    refine ⟨hτ, ?_⟩
    have := le_max_left τ 1
    linarith
  -- the class data of the approximants
  have hclass : ∀ n, Work.FTS.ClassC.ClassC αG (Work.FTS.Galerkin.slice (gn n) τ) :=
    fun n => (hcls n τ hτT).1
  have hN : ∀ n, Work.Spaces.HkNorm αG 4 (Work.FTS.Galerkin.slice (gn n) τ) ≤ C₀ * αG ^ 2 :=
    fun n => (hcls n τ hτT).2.1
  have hΛ : 0 ≤ C₀ * αG ^ 2 :=
    le_trans (Work.Spaces.HkNorm_nonneg αG 4 _) (hN 0)
  have hcls' : ∀ n, Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Galerkin.slice (gn n) τ) ∧
      Work.Spaces.HkMem αG 4 (Work.FTS.Galerkin.slice (gn n) τ) ∧
      Work.FTS.Nonlin.BdryTraces αG 4 (Work.FTS.Galerkin.slice (gn n) τ) := fun n =>
    ⟨(hclass n).reg,
     Work.FTS.OpenPkg.HkMem_mono_open (hclass n).reg 4 (by norm_num) (hclass n).mem,
     Work.FTS.ClassC.bdryTraces_mono (by norm_num) (hclass n).tr⟩
  have hjet' : ∀ s θ : ℝ, 0 < s → 0 < θ → θ < Real.pi / 2 →
      Tendsto (fun n => Work.FTS.Galerkin.slice (gn n) τ s θ) atTop
        (𝓝 (Work.FTS.Galerkin.slice g τ s θ)) := by
    intro s θ hs hθ hθ'
    have h := hjet τ hτT 0 0 (by norm_num) s θ ⟨hs, hθ, hθ'⟩
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero,
      Work.Spaces.DzIter_zero] using h
  have hzero : ∀ n, Work.Construction.L12 (Work.FTS.Galerkin.slice (gn n) τ) 0 = 0 :=
    fun n => (hclass n).l12_zero
  -- the `L¹(ds)` majorant
  set M : ℝ → ℝ := fun s => Cden * (Real.sqrt s / (1 + s) ^ 2) * (C₀ * αG ^ 2) with hMdef
  have hMint : MeasureTheory.IntegrableOn M (Set.Ioi 0) := by
    have h : MeasureTheory.IntegrableOn
        (fun s : ℝ => (Cden * (C₀ * αG ^ 2)) * (Real.sqrt s / (1 + s) ^ 2)) (Set.Ioi 0) :=
      integrableOn_sqrt_div_sq.const_mul (Cden * (C₀ * αG ^ 2))
    have hfun : (fun s : ℝ => (Cden * (C₀ * αG ^ 2)) * (Real.sqrt s / (1 + s) ^ 2)) = M := by
      funext s
      simp only [hMdef]
      ring
    rwa [hfun] at h
  -- the dominated convergence theorem in the radial variable
  have hmeas : ∀ n, AEStronglyMeasurable
      (fun s => Work.FM.L12dens Work.Spaces.K (Work.FTS.Galerkin.slice (gn n) τ) s)
      (volume.restrict (Set.Ioi 0)) := by
    intro n
    refine ContinuousOn.aestronglyMeasurable (fun z hz => ?_) measurableSet_Ioi
    exact (Work.FTS.MeridianDyn.Bridge.continuousAt_L12dens_of_smoothOpen_Hk
      (hcls' n).1 (hcls' n).2.1 hz).continuousWithinAt
  have hconv : ∀ᵐ s ∂(volume.restrict (Set.Ioi 0)),
      Tendsto (fun n => Work.FM.L12dens Work.Spaces.K (Work.FTS.Galerkin.slice (gn n) τ) s)
        atTop (𝓝 (Work.FM.L12dens Work.Spaces.K (Work.FTS.Galerkin.slice g τ) s)) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun s hs =>
      tendsto_L12dens_of_sup_bound hΛ hCsup hsup hcls' hN hjet' hs)
  have hbdd : ∀ᵐ s ∂(volume.restrict (Set.Ioi 0)), ∀ n,
      ‖Work.FM.L12dens Work.Spaces.K (Work.FTS.Galerkin.slice (gn n) τ) s‖ ≤ M s := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun s hs n => ?_)
    have h1 : |Work.Construction.L12dens (Work.FTS.Galerkin.slice (gn n) τ) s|
        ≤ Cden * (Real.sqrt s / (1 + s) ^ 2)
          * Work.Spaces.HkNorm αG 4 (Work.FTS.Galerkin.slice (gn n) τ) :=
      hden _ (hcls' n).1 (hcls' n).2.1 (hcls' n).2.2 s hs
    have h2 : Cden * (Real.sqrt s / (1 + s) ^ 2)
          * Work.Spaces.HkNorm αG 4 (Work.FTS.Galerkin.slice (gn n) τ)
        ≤ M s := by
      rw [hMdef]
      exact mul_le_mul_of_nonneg_left (hN n)
        (by positivity)
    rw [Real.norm_eq_abs]
    exact le_trans h1 h2
  have hlim := Work.FTS.StrongEps.L12_tendsto_of_dominated
    (f := fun n => Work.FTS.Galerkin.slice (gn n) τ) (g := Work.FTS.Galerkin.slice g τ)
    (M := M) (ρ := 0) hmeas hconv hbdd hMint
  have h0 : Tendsto (fun n => Work.Construction.L12 (Work.FTS.Galerkin.slice (gn n) τ) 0)
      atTop (𝓝 (0:ℝ)) := by
    have hfun : (fun n => Work.Construction.L12 (Work.FTS.Galerkin.slice (gn n) τ) 0)
        = fun _ => (0:ℝ) := funext hzero
    rw [hfun]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hlim h0

end Work.FTS_RegExport.RXB
