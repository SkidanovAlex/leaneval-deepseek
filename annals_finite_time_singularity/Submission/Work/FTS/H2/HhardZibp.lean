import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.H2.T2Defs
import Submission.Work.FTS.H2.T2HardAux
import Submission.Work.FTS.H2.T2SliceHard
import Submission.Work.FTS.H2.T2SliceAux
import Submission.Work.FTS.H2.SupMixedNB
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.H2.hard_sq_prod_mixed
import Submission.Work.FTS.H2.Hhard_slice_eq
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.HkSq_mixed_le
import Submission.Work.Spaces.SmoothCompact_Aux
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.Spaces.HardyZ
import Submission.Work.Coercivity.pz_mul_w

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false

/-! ## The radial integration-by-parts proof of the hard-part bound -/

def ZU (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  ∑ k : Fin 5, Thard g k z θ ^ 2 * sghard α k θ

def ZG (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (1 / 2) * (f z θ * z * (Spaces.w z) ^ 2 * ZU α g z θ)

def ZE (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (1 / 2) * (Spaces.Dz f z θ * (Spaces.w z) ^ 2
      + f z θ * ((Spaces.w z) ^ 2 * ((z - 3) / (1 + z)))) * ZU α g z θ

theorem ZU_nonneg {α : ℝ} {g : ℝ → ℝ → ℝ} {z θ : ℝ} (hθ : θ ∈ Spaces.Iθ) :
    0 ≤ ZU α g z θ :=
  Finset.sum_nonneg fun k _ => mul_nonneg (sq_nonneg _) (sghard_nonneg α k hθ)

theorem Thard_smoothNbhd {g : ℝ → ℝ → ℝ} (hsmg : Spaces.SmoothNbhd g) (k : Fin 5) :
    Spaces.SmoothNbhd (Thard g k) := by
  rw [Thard_eq_mixed]
  exact Spaces.smoothNbhd_mixed hsmg (4 - k.val) k.val

theorem hasDerivAt_ZU {α : ℝ} {g : ℝ → ℝ → ℝ} (hsmg : Spaces.SmoothNbhd g) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Spaces.Iθ) :
    HasDerivAt (fun z' => ZU α g z' θ)
      (∑ k : Fin 5, 2 * Thard g k z θ * Spaces.pz (Thard g k) z θ * sghard α k θ) z := by
  have hderiv : ∀ k : Fin 5,
      HasDerivAt (fun z' => Thard g k z' θ ^ 2 * sghard α k θ)
        (2 * Thard g k z θ * Spaces.pz (Thard g k) z θ * sghard α k θ) z := by
    intro k
    have hk := Spaces.hardyZ_hasDerivAt_slice (Thard g k) (Thard_smoothNbhd hsmg k) hθ
      (Spaces.hardyZ_mem_Ioi 0 z le_rfl hz.le)
    have h2 := (hk.pow 2).mul_const (sghard α k θ)
    simpa only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one] using h2
  have hsum := HasDerivAt.sum (u := Finset.univ) (fun k _ => hderiv k)
  have hfun : (∑ i : Fin 5, fun z' => Thard g i z' θ ^ 2 * sghard α i θ)
      = fun z' => ZU α g z' θ := by
    funext z'
    simp only [Finset.sum_apply, ZU]
  rwa [hfun] at hsum

theorem deriv_ZU {α : ℝ} {g : ℝ → ℝ → ℝ} (hsmg : Spaces.SmoothNbhd g) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Spaces.Iθ) :
    deriv (fun z' => ZU α g z' θ) z
      = ∑ k : Fin 5, 2 * Thard g k z θ * Spaces.pz (Thard g k) z θ * sghard α k θ :=
  (hasDerivAt_ZU hsmg hz hθ).deriv

/-- `Hhard` is `½ f z w² ZU'`. -/
theorem Hhard_eq_half (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Hhard α f g z θ
      = f z θ * z * (Spaces.w z) ^ 2 * (1 / 2)
          * ∑ k : Fin 5, 2 * Thard g k z θ * Spaces.pz (Thard g k) z θ * sghard α k θ := by
  have hsum1 : (∑ k : Fin 5,
        2 * Thard g k z θ * Spaces.pz (Thard g k) z θ * sghard α k θ)
      = 2 * ∑ k : Fin 5, Thard g k z θ * Spaces.pz (Thard g k) z θ * sghard α k θ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hsum2 : (∑ k : Fin 5,
        Spaces.pz (Thard g k) z θ * Thard g k z θ * (Spaces.w z) ^ 2 * sghard α k θ)
      = (Spaces.w z) ^ 2 * ∑ k : Fin 5,
          Thard g k z θ * Spaces.pz (Thard g k) z θ * sghard α k θ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [Hhard, hsum1, hsum2]
  ring

theorem hasDerivAt_zw2 {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun z' => z' * (Spaces.w z') ^ 2)
      ((Spaces.w z) ^ 2 * ((z - 3) / (1 + z))) z := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hz1 : (1 : ℝ) + z ≠ 0 := by linarith
  refine ((hasDerivAt_id z).mul ((Work.Coercivity.hasDerivAt_w hz0).pow 2)).congr_deriv ?_
  simp only [Pi.pow_apply, Pi.mul_apply, id_eq, one_mul]
  rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
  simp only [Spaces.w]
  field_simp
  ring

theorem abs_ratio_le_three (z : ℝ) (hz : 0 < z) : |(z - 3) / (1 + z)| ≤ 3 := by
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  rw [abs_div, abs_of_pos hz1, div_le_iff₀ hz1, abs_le]
  constructor <;> linarith

theorem abs_deriv_zw2_le (z : ℝ) (hz : 0 < z) :
    |deriv (fun z' => z' * (Spaces.w z') ^ 2) z| ≤ 3 * (Spaces.w z) ^ 2 := by
  rw [(hasDerivAt_zw2 hz).deriv, abs_mul, abs_of_nonneg (sq_nonneg _)]
  calc (Spaces.w z) ^ 2 * |(z - 3) / (1 + z)|
      ≤ (Spaces.w z) ^ 2 * 3 :=
        mul_le_mul_of_nonneg_left (abs_ratio_le_three z hz) (sq_nonneg _)
    _ = 3 * (Spaces.w z) ^ 2 := by ring

/-- **The pointwise identity**: on the quadrant, `Hhard` is `∂_z G - E`. -/
theorem ZG_deriv {α : ℝ} {f g : ℝ → ℝ → ℝ} (hsmf : Spaces.SmoothNbhd f)
    (hsmg : Spaces.SmoothNbhd g) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Spaces.Iθ) :
    deriv (fun z' => ZG α f g z' θ) z = Hhard α f g z θ + ZE α f g z θ := by
  have hf : HasDerivAt (fun z' => f z' θ) (Spaces.pz f z θ) z :=
    Spaces.hardyZ_hasDerivAt_slice f hsmf hθ (Spaces.hardyZ_mem_Ioi 0 z le_rfl hz.le)
  have hzw := hasDerivAt_zw2 hz
  have hU := hasDerivAt_ZU (α := α) (g := g) hsmg hz hθ
  have hprod : HasDerivAt
      (fun z' => (1 / 2) * (f z' θ * (z' * (Spaces.w z') ^ 2) * ZU α g z' θ))
      ((1 / 2) * ((Spaces.pz f z θ * (z * (Spaces.w z) ^ 2)
          + f z θ * ((Spaces.w z) ^ 2 * ((z - 3) / (1 + z)))) * ZU α g z θ
        + (f z θ * (z * (Spaces.w z) ^ 2))
          * (∑ k : Fin 5, 2 * Thard g k z θ * Spaces.pz (Thard g k) z θ
              * sghard α k θ))) z :=
    ((hf.mul hzw).mul hU).const_mul (1 / 2)
  have hGf : (fun z' => ZG α f g z' θ)
      = fun z' => (1 / 2) * (f z' θ * (z' * (Spaces.w z') ^ 2) * ZU α g z' θ) := by
    funext z'
    simp only [ZG]
    ring
  rw [hGf, hprod.deriv, Hhard_eq_half, ZE, Spaces.Dz]
  ring

/-! ## The bound on the correction term -/

theorem ZE_bound {α : ℝ} {f g : ℝ → ℝ → ℝ} {M z θ : ℝ} (hM : 0 ≤ M) (hz : 0 ≤ z)
    (hθ : θ ∈ Spaces.Iθ) (hf : |f z θ| ≤ M) (hDf : |Spaces.Dz f z θ| ≤ M) :
    |ZE α f g z θ| ≤ 2 * M * (Spaces.w z) ^ 2 * ZU α g z θ := by
  have hU := ZU_nonneg (α := α) (g := g) (z := z) hθ
  have hw2 : 0 ≤ (Spaces.w z) ^ 2 := sq_nonneg _
  have hratio : |(z - 3) / (1 + z)| ≤ 3 := by
    have hz1 : (0 : ℝ) < 1 + z := by linarith
    rw [abs_div, abs_of_pos hz1, div_le_iff₀ hz1, abs_le]
    constructor <;> linarith
  have hinner : |Spaces.Dz f z θ * (Spaces.w z) ^ 2
      + f z θ * ((Spaces.w z) ^ 2 * ((z - 3) / (1 + z)))|
      ≤ 4 * M * (Spaces.w z) ^ 2 := by
    calc |Spaces.Dz f z θ * (Spaces.w z) ^ 2
          + f z θ * ((Spaces.w z) ^ 2 * ((z - 3) / (1 + z)))|
        ≤ |Spaces.Dz f z θ * (Spaces.w z) ^ 2|
          + |f z θ * ((Spaces.w z) ^ 2 * ((z - 3) / (1 + z)))| := abs_add_le _ _
      _ = |Spaces.Dz f z θ| * (Spaces.w z) ^ 2
          + |f z θ| * ((Spaces.w z) ^ 2 * |(z - 3) / (1 + z)|) := by
          simp only [abs_mul, abs_of_nonneg hw2]
      _ ≤ M * (Spaces.w z) ^ 2 + M * ((Spaces.w z) ^ 2 * 3) := by
          refine add_le_add (mul_le_mul_of_nonneg_right hDf hw2) ?_
          exact mul_le_mul hf (mul_le_mul_of_nonneg_left hratio hw2)
            (mul_nonneg hw2 (abs_nonneg _)) hM
      _ = 4 * M * (Spaces.w z) ^ 2 := by ring
  have hEfabs : |ZE α f g z θ|
      = (1 / 2) * |Spaces.Dz f z θ * (Spaces.w z) ^ 2
          + f z θ * ((Spaces.w z) ^ 2 * ((z - 3) / (1 + z)))| * ZU α g z θ := by
    rw [ZE, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2), abs_of_nonneg hU]
  rw [hEfabs]
  have hb : |Spaces.Dz f z θ * (Spaces.w z) ^ 2
      + f z θ * ((Spaces.w z) ^ 2 * ((z - 3) / (1 + z)))| * ZU α g z θ
      ≤ (4 * M * (Spaces.w z) ^ 2) * ZU α g z θ :=
    mul_le_mul_of_nonneg_right hinner hU
  calc (1 / 2) * |Spaces.Dz f z θ * (Spaces.w z) ^ 2
          + f z θ * ((Spaces.w z) ^ 2 * ((z - 3) / (1 + z)))| * ZU α g z θ
      = (1 / 2) * (|Spaces.Dz f z θ * (Spaces.w z) ^ 2
          + f z θ * ((Spaces.w z) ^ 2 * ((z - 3) / (1 + z)))| * ZU α g z θ) := by ring
    _ ≤ (1 / 2) * ((4 * M * (Spaces.w z) ^ 2) * ZU α g z θ) :=
        mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = 2 * M * (Spaces.w z) ^ 2 * ZU α g z θ := by ring

/-! ## Integrability of the model angular weights -/

theorem integrableOn_sin_two_rpow {a : ℝ} (ha : -1 < a) (ha1 : a ≤ 1) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ a) Spaces.Iθ := by
  rcases lt_or_ge (0 : ℝ) a with hpos | hle
  · refine MeasureTheory.Integrable.mono'
      (MeasureTheory.integrableOn_const (s := Spaces.Iθ) (C := (1 : ℝ))
        (by rw [Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)) ?_ ?_
    · exact ((Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const a)
        |>.aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem
        (show MeasurableSet Spaces.Iθ from measurableSet_Icc)] with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Spaces.sin_two_nonneg_of_Iθ hθ) a)]
      exact Real.rpow_le_one (Spaces.sin_two_nonneg_of_Iθ hθ) (Real.sin_le_one _) hpos.le
  · exact (Spaces.sin_two_rpow a ha hle).1

/-- The angular dominator of the hard slots. -/
def ZD (α θ : ℝ) : ℝ :=
  (Real.sin (2 * θ)) ^ (-(Spaces.eta)) + (Real.sin (2 * θ)) ^ (1 - Spaces.gam α)
    + (Real.sin (2 * θ)) ^ (2 - Spaces.gam α)

theorem ZD_nonneg (α : ℝ) {θ : ℝ} (hθ : θ ∈ Spaces.Iθ) : 0 ≤ ZD α θ :=
  add_nonneg (add_nonneg (Real.rpow_nonneg (Spaces.sin_two_nonneg_of_Iθ hθ) _)
    (Real.rpow_nonneg (Spaces.sin_two_nonneg_of_Iθ hθ) _))
    (Real.rpow_nonneg (Spaces.sin_two_nonneg_of_Iθ hθ) _)

theorem integrableOn_ZD {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    MeasureTheory.IntegrableOn (ZD α) Spaces.Iθ := by
  have h1 : (-1 : ℝ) < -(Spaces.eta) := by rw [Spaces.eta]; norm_num
  have h1' : -(Spaces.eta) ≤ (1 : ℝ) := by rw [Spaces.eta]; norm_num
  have h2 : (-1 : ℝ) < 1 - Spaces.gam α := by rw [Spaces.gam]; linarith
  have h2' : 1 - Spaces.gam α ≤ (1 : ℝ) := by rw [Spaces.gam]; linarith
  have h3 : (-1 : ℝ) < 2 - Spaces.gam α := by rw [Spaces.gam]; linarith
  have h3' : 2 - Spaces.gam α ≤ (1 : ℝ) := by rw [Spaces.gam]; linarith
  exact ((integrableOn_sin_two_rpow h1 h1').add (integrableOn_sin_two_rpow h2 h2')).add
    (integrableOn_sin_two_rpow h3 h3')

/-! ## The structural `sin(2θ)`-bounds for the slots -/

theorem slot0_bound {g : ℝ → ℝ → ℝ} (hsmg : Spaces.SmoothNbhd g) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Set.Icc 0 R, ∀ θ ∈ Spaces.Iθ,
      |Thard g 0 z θ| ≤ C ∧ |Spaces.pz (Thard g 0) z θ| ≤ C := by
  have hsmA : Spaces.SmoothNbhd (Thard g 0) := Thard_smoothNbhd hsmg 0
  have hb1 : BddAbove (Spaces.boxSet R (Thard g 0)) :=
    Spaces.bddAbove_boxSup_of_continuousOn (Spaces.continuousOn_box_of_contDiffOn hsmA)
  have hb2 : BddAbove (Spaces.boxSet R (Spaces.pz (Thard g 0))) :=
    Spaces.bddAbove_boxSup_of_continuousOn (Spaces.continuousOn_box_of_contDiffOn hsmA.pz)
  have h1 : 0 ≤ Spaces.boxSup R (Thard g 0) := Spaces.boxSup_nonneg hR hb1
  have h2 : 0 ≤ Spaces.boxSup R (Spaces.pz (Thard g 0)) := Spaces.boxSup_nonneg hR hb2
  refine ⟨Spaces.boxSup R (Thard g 0) + Spaces.boxSup R (Spaces.pz (Thard g 0)),
    add_nonneg h1 h2, ?_⟩
  intro z hz θ hθ
  exact ⟨le_trans (Spaces.le_boxSup hb1 hz hθ) (le_add_of_nonneg_right h2),
    le_trans (Spaces.le_boxSup hb2 hz hθ) (le_add_of_nonneg_left h1)⟩

theorem slotN_bound {g : ℝ → ℝ → ℝ} (hsmg : Spaces.SmoothNbhd g) {R : ℝ} (hR : 0 ≤ R)
    (k : Fin 5) (hk : k.val ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Set.Icc 0 R, ∀ θ ∈ Spaces.Iθ,
      |Thard g k z θ| ≤ C * Real.sin (2 * θ) ∧
        |Spaces.pz (Thard g k) z θ| ≤ C * Real.sin (2 * θ) := by
  set i' : ℕ := k.val - 1 with hi'
  have hkv : k.val = i' + 1 := by omega
  set X : ℝ → ℝ → ℝ :=
    Spaces.DzIter (4 - (i' + 1)) (Spaces.pth (Spaces.DthIter i' g)) with hX
  have hsmX : Spaces.SmoothNbhd X := by
    rw [hX]
    exact Spaces.smoothNbhd_DzIter
      (Spaces.SmoothNbhd.pth (Spaces.smoothNbhd_DthIter hsmg i')) (4 - (i' + 1))
  have hbX : BddAbove (Spaces.boxSet R X) :=
    Spaces.bddAbove_boxSup_of_continuousOn (Spaces.continuousOn_box_of_contDiffOn hsmX)
  have hbXp : BddAbove (Spaces.boxSet R (Spaces.pz X)) :=
    Spaces.bddAbove_boxSup_of_continuousOn (Spaces.continuousOn_box_of_contDiffOn hsmX.pz)
  have h1 : 0 ≤ Spaces.boxSup R X := Spaces.boxSup_nonneg hR hbX
  have h2 : 0 ≤ Spaces.boxSup R (Spaces.pz X) := Spaces.boxSup_nonneg hR hbXp
  refine ⟨Spaces.boxSup R X + Spaces.boxSup R (Spaces.pz X), add_nonneg h1 h2, ?_⟩
  have hTh : Thard g k = Spaces.mixed (4 - (i' + 1)) (i' + 1) g := by
    funext z θ
    rw [Thard_eq_mixed, hkv]
  intro z hz θ hθ
  have hsin : 0 ≤ Real.sin (2 * θ) := Spaces.sin_two_nonneg_of_Iθ hθ
  have hXb : |X z θ| ≤ Spaces.boxSup R X := Spaces.le_boxSup hbX hz hθ
  have hXpb : |Spaces.pz X z θ| ≤ Spaces.boxSup R (Spaces.pz X) := Spaces.le_boxSup hbXp hz hθ
  have hfac : Thard g k z θ = Real.sin (2 * θ) * X z θ := by
    rw [hTh, Work.FTS.H2.mixed_sin_factor (4 - (i' + 1)) i' g, hX]
  have hfacp : Spaces.pz (Thard g k) z θ = Real.sin (2 * θ) * Spaces.pz X z θ := by
    rw [hTh, Work.FTS.H2.pz_mixed_sin_factor (4 - (i' + 1)) i' g z θ, hX]
  constructor
  · rw [hfac, abs_mul, abs_of_nonneg hsin]
    calc Real.sin (2 * θ) * |X z θ|
        ≤ Real.sin (2 * θ) * (Spaces.boxSup R X + Spaces.boxSup R (Spaces.pz X)) :=
          mul_le_mul_of_nonneg_left (le_trans hXb (le_add_of_nonneg_right h2)) hsin
      _ = (Spaces.boxSup R X + Spaces.boxSup R (Spaces.pz X)) * Real.sin (2 * θ) := by ring
  · rw [hfacp, abs_mul, abs_of_nonneg hsin]
    calc Real.sin (2 * θ) * |Spaces.pz X z θ|
        ≤ Real.sin (2 * θ) * (Spaces.boxSup R X + Spaces.boxSup R (Spaces.pz X)) :=
          mul_le_mul_of_nonneg_left (le_trans hXpb (le_add_of_nonneg_left h1)) hsin
      _ = (Spaces.boxSup R X + Spaces.boxSup R (Spaces.pz X)) * Real.sin (2 * θ) := by ring

/-! ## A cruder dominator and the master bound for `ZU` -/

/-- A cruder angular dominator: `η < 1` and `γ > 1` make the first two terms integrable and
`sin(2θ)^{2-γ} ≤ 1` replaces the third. -/
def ZDom (α θ : ℝ) : ℝ :=
  (Real.sin (2 * θ)) ^ (-(Spaces.eta)) + (Real.sin (2 * θ)) ^ (1 - Spaces.gam α) + 1

theorem ZDom_nonneg (α : ℝ) {θ : ℝ} (hθ : θ ∈ Spaces.Iθ) : 0 ≤ ZDom α θ :=
  add_nonneg (add_nonneg (Real.rpow_nonneg (Spaces.sin_two_nonneg_of_Iθ hθ) _)
    (Real.rpow_nonneg (Spaces.sin_two_nonneg_of_Iθ hθ) _)) zero_le_one

theorem integrableOn_ZD2 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    MeasureTheory.IntegrableOn (ZDom α) Spaces.Iθ := by
  have h1 : (-1 : ℝ) < -(Spaces.eta) := by rw [Spaces.eta]; norm_num
  have h1' : -(Spaces.eta) ≤ (1 : ℝ) := by rw [Spaces.eta]; norm_num
  have h2 : (-1 : ℝ) < 1 - Spaces.gam α := by rw [Spaces.gam]; linarith
  have h2' : 1 - Spaces.gam α ≤ (1 : ℝ) := by rw [Spaces.gam]; linarith
  exact ((integrableOn_sin_two_rpow h1 h1').add (integrableOn_sin_two_rpow h2 h2')).add
    (MeasureTheory.integrableOn_const (s := Spaces.Iθ) (C := (1 : ℝ))
      (by rw [Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top))

theorem slot_bound {g : ℝ → ℝ → ℝ} (hsmg : Spaces.SmoothNbhd g) {R : ℝ} (hR : 0 ≤ R)
    (k : Fin 5) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Set.Icc 0 R, ∀ θ ∈ Spaces.Iθ,
      |Thard g k z θ| ≤ C * (Real.sin (2 * θ)) ^ (if k.val = 0 then (0:ℝ) else 1) ∧
      |Spaces.pz (Thard g k) z θ|
        ≤ C * (Real.sin (2 * θ)) ^ (if k.val = 0 then (0:ℝ) else 1) := by
  by_cases hk : k.val = 0
  · obtain ⟨C, hC, hb⟩ := slot0_bound hsmg hR
    have hk0 : k = 0 := Fin.ext hk
    subst hk0
    refine ⟨C, hC, fun z hz θ hθ => ?_⟩
    rw [if_pos (show (0 : Fin 5).val = 0 from rfl), Real.rpow_zero, mul_one]
    exact ⟨(hb z hz θ hθ).1, (hb z hz θ hθ).2⟩
  · obtain ⟨C, hC, hb⟩ := slotN_bound hsmg hR k hk
    refine ⟨C, hC, fun z hz θ hθ => ?_⟩
    rw [if_neg hk, Real.rpow_one]
    exact ⟨(hb z hz θ hθ).1, (hb z hz θ hθ).2⟩

theorem ZU_dom_bounds {α : ℝ} {g : ℝ → ℝ → ℝ} (hsmg : Spaces.SmoothNbhd g) (hα : 0 < α)
    (hα1 : α ≤ 1) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Set.Icc 0 R, 0 < z → ∀ θ ∈ Spaces.Iθ,
      ZU α g z θ ≤ C * ZDom α θ ∧ |deriv (fun z' => ZU α g z' θ) z| ≤ C * ZDom α θ := by
  choose Ck hCk using fun k : Fin 5 => slot_bound hsmg hR k
  set K : ℝ := ∑ k : Fin 5, Ck k + 1 with hKdef
  have hKnn : 0 ≤ K := by
    rw [hKdef]
    exact add_nonneg (Finset.sum_nonneg fun k _ => (hCk k).1) zero_le_one
  have hKC : ∀ k : Fin 5, Ck k ≤ K := by
    intro k
    rw [hKdef]
    exact le_trans (Finset.single_le_sum (f := fun i => Ck i)
      (fun i _ => (hCk i).1) (Finset.mem_univ k)) (by linarith)
  refine ⟨10 * K ^ 2 + 1, by positivity, ?_⟩
  intro z hz hzpos θ hθ
  have hsin : 0 ≤ Real.sin (2 * θ) := Spaces.sin_two_nonneg_of_Iθ hθ
  have hDom : 0 ≤ ZDom α θ := ZDom_nonneg (α := α) hθ
  have hgam2 : (0 : ℝ) < 2 - Spaces.gam α := by rw [Spaces.gam]; linarith
  have hident2 : (Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))
      = (Real.sin (2 * θ)) ^ (2 - Spaces.gam α) :=
    sq_mul_rpow_neg (Real.sin (2 * θ)) (Spaces.gam α) hsin (by rw [Spaces.gam]; linarith)
  have hident1 : Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))
      = (Real.sin (2 * θ)) ^ (1 - Spaces.gam α) := by
    have hne : (1 : ℝ) + -(Spaces.gam α) ≠ 0 := by
      have h1 := Spaces.gam_sub_one α
      intro hh
      linarith
    calc Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))
        = (Real.sin (2 * θ)) ^ (1:ℝ) * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) := by
          rw [Real.rpow_one]
      _ = (Real.sin (2 * θ)) ^ ((1:ℝ) + -(Spaces.gam α)) :=
          (Real.rpow_add' (x := Real.sin (2 * θ)) (y := (1:ℝ)) (z := -(Spaces.gam α))
            hsin hne).symm
      _ = (Real.sin (2 * θ)) ^ (1 - Spaces.gam α) := by
          rw [show (1:ℝ) + -(Spaces.gam α) = 1 - Spaces.gam α by ring]
  have hKb : ∀ k : Fin 5,
      |Thard g k z θ| ≤ K * (Real.sin (2 * θ)) ^ (if k.val = 0 then (0:ℝ) else 1) ∧
      |Spaces.pz (Thard g k) z θ|
        ≤ K * (Real.sin (2 * θ)) ^ (if k.val = 0 then (0:ℝ) else 1) := by
    intro k
    have hb := (hCk k).2 z hz θ hθ
    exact ⟨le_trans hb.1 (mul_le_mul_of_nonneg_right (hKC k) (Real.rpow_nonneg hsin _)),
      le_trans hb.2 (mul_le_mul_of_nonneg_right (hKC k) (Real.rpow_nonneg hsin _))⟩
  have hterm1 : ∀ k : Fin 5, Thard g k z θ ^ 2 * sghard α k θ ≤ K ^ 2 * ZDom α θ := by
    intro k
    rcases eq_or_ne k.val 0 with hk0 | hk0
    · have hs : sghard α k θ = (Real.sin (2 * θ)) ^ (-(Spaces.eta)) := by
        have hk0' : k = 0 := Fin.ext hk0
        subst hk0'
        exact sghard_apply_zero α θ
      have h1 : |Thard g k z θ| ≤ K := by
        have h := (hKb k).1
        rw [if_pos hk0, Real.rpow_zero, mul_one] at h
        exact h
      have hsq : Thard g k z θ ^ 2 ≤ K ^ 2 := by
        have h := pow_le_pow_left₀ (abs_nonneg (Thard g k z θ)) h1 2
        rwa [sq_abs] at h
      rw [hs]
      calc Thard g k z θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.eta))
          ≤ K ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.eta)) :=
            mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hsin _)
        _ ≤ K ^ 2 * ZDom α θ := by
            refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg K)
            rw [ZDom]
            linarith [Real.rpow_nonneg hsin (1 - Spaces.gam α)]
    · have hs : sghard α k θ = (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) :=
        sghard_apply_ne α k hk0 θ
      have h1 : |Thard g k z θ| ≤ K * Real.sin (2 * θ) := by
        have h := (hKb k).1
        rw [if_neg hk0, Real.rpow_one] at h
        exact h
      have hsq : Thard g k z θ ^ 2 ≤ (K * Real.sin (2 * θ)) ^ 2 := by
        have h := pow_le_pow_left₀ (abs_nonneg (Thard g k z θ)) h1 2
        rwa [sq_abs] at h
      rw [hs]
      calc Thard g k z θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))
          ≤ (K * Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) :=
            mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hsin _)
        _ = K ^ 2 * ((Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))) := by
            rw [mul_pow]
            ring
        _ = K ^ 2 * (Real.sin (2 * θ)) ^ (2 - Spaces.gam α) := by rw [hident2]
        _ ≤ K ^ 2 * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg K)
            exact Real.rpow_le_one hsin (Real.sin_le_one _) hgam2.le
        _ ≤ K ^ 2 * ZDom α θ := by
            refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg K)
            rw [ZDom]
            linarith [Real.rpow_nonneg hsin (-(Spaces.eta)),
              Real.rpow_nonneg hsin (1 - Spaces.gam α)]
  have hterm2 : ∀ k : Fin 5,
      2 * (|Thard g k z θ| * |Spaces.pz (Thard g k) z θ|) * sghard α k θ
        ≤ 2 * K ^ 2 * ZDom α θ := by
    intro k
    rcases eq_or_ne k.val 0 with hk0 | hk0
    · have hs : sghard α k θ = (Real.sin (2 * θ)) ^ (-(Spaces.eta)) := by
        have hk0' : k = 0 := Fin.ext hk0
        subst hk0'
        exact sghard_apply_zero α θ
      have h1 : |Thard g k z θ| ≤ K := by
        have h := (hKb k).1
        rw [if_pos hk0, Real.rpow_zero, mul_one] at h
        exact h
      have h2 : |Spaces.pz (Thard g k) z θ| ≤ K := by
        have h := (hKb k).2
        rw [if_pos hk0, Real.rpow_zero, mul_one] at h
        exact h
      have hmul : |Thard g k z θ| * |Spaces.pz (Thard g k) z θ| ≤ K ^ 2 := by
        calc |Thard g k z θ| * |Spaces.pz (Thard g k) z θ| ≤ K * K :=
              mul_le_mul h1 h2 (abs_nonneg _) hKnn
          _ = K ^ 2 := by ring
      rw [hs]
      calc 2 * (|Thard g k z θ| * |Spaces.pz (Thard g k) z θ|)
            * (Real.sin (2 * θ)) ^ (-(Spaces.eta))
          ≤ 2 * K ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.eta)) := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hsin _)
            nlinarith [sq_nonneg K]
        _ ≤ 2 * K ^ 2 * ZDom α θ := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rw [ZDom]
            linarith [Real.rpow_nonneg hsin (1 - Spaces.gam α)]
    · have hs : sghard α k θ = (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) :=
        sghard_apply_ne α k hk0 θ
      have h1 : |Thard g k z θ| ≤ K * Real.sin (2 * θ) := by
        have h := (hKb k).1
        rw [if_neg hk0, Real.rpow_one] at h
        exact h
      have h2 : |Spaces.pz (Thard g k) z θ| ≤ K * Real.sin (2 * θ) := by
        have h := (hKb k).2
        rw [if_neg hk0, Real.rpow_one] at h
        exact h
      have hmul : |Thard g k z θ| * |Spaces.pz (Thard g k) z θ|
          ≤ (K * Real.sin (2 * θ)) ^ 2 := by
        have hk2 : 0 ≤ K * Real.sin (2 * θ) := mul_nonneg hKnn hsin
        calc |Thard g k z θ| * |Spaces.pz (Thard g k) z θ|
            ≤ (K * Real.sin (2 * θ)) * (K * Real.sin (2 * θ)) :=
              mul_le_mul h1 h2 (abs_nonneg _) hk2
          _ = (K * Real.sin (2 * θ)) ^ 2 := by ring
      rw [hs]
      calc 2 * (|Thard g k z θ| * |Spaces.pz (Thard g k) z θ|)
            * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))
          ≤ 2 * (K * Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hsin _)
            nlinarith [sq_nonneg (K * Real.sin (2 * θ))]
        _ = 2 * K ^ 2 * ((Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))) := by
            rw [mul_pow]
            ring
        _ = 2 * K ^ 2 * (Real.sin (2 * θ)) ^ (2 - Spaces.gam α) := by rw [hident2]
        _ ≤ 2 * K ^ 2 * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact Real.rpow_le_one hsin (Real.sin_le_one _) hgam2.le
        _ ≤ 2 * K ^ 2 * ZDom α θ := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rw [ZDom]
            linarith [Real.rpow_nonneg hsin (-(Spaces.eta)),
              Real.rpow_nonneg hsin (1 - Spaces.gam α)]
  constructor
  · calc ZU α g z θ = ∑ k : Fin 5, Thard g k z θ ^ 2 * sghard α k θ := rfl
      _ ≤ ∑ _k : Fin 5, K ^ 2 * ZDom α θ := Finset.sum_le_sum fun k _ => hterm1 k
      _ = 5 * (K ^ 2 * ZDom α θ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
      _ ≤ (10 * K ^ 2 + 1) * ZDom α θ := by nlinarith [hDom, sq_nonneg K]
  · calc |deriv (fun z' => ZU α g z' θ) z|
        = |∑ k : Fin 5, 2 * Thard g k z θ * Spaces.pz (Thard g k) z θ * sghard α k θ| := by
          rw [deriv_ZU hsmg hzpos hθ]
      _ ≤ ∑ k : Fin 5, |2 * Thard g k z θ * Spaces.pz (Thard g k) z θ * sghard α k θ| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k : Fin 5,
            2 * (|Thard g k z θ| * |Spaces.pz (Thard g k) z θ|) * sghard α k θ := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
            abs_of_nonneg (sghard_nonneg α k hθ)]
          ring
      _ ≤ ∑ _k : Fin 5, 2 * K ^ 2 * ZDom α θ := Finset.sum_le_sum fun k _ => hterm2 k
      _ = 5 * (2 * K ^ 2 * ZDom α θ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
      _ ≤ (10 * K ^ 2 + 1) * ZDom α θ := by nlinarith [hDom, sq_nonneg K]

/-! ## The `θ`-integrability of the slots -/

theorem meas_sghard (α : ℝ) (k : Fin 5) : Measurable (fun θ : ℝ => sghard α k θ) := by
  by_cases hk : k.val = 0
  · have hk0 : k = 0 := Fin.ext hk
    subst hk0
    have h : Measurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Spaces.eta))) :=
      (Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const _
    simpa only [sghard_apply_zero, Function.comp_apply, Pi.mul_apply] using h
  · rw [funext (fun θ => sghard_apply_ne α k hk θ)]
    have h : Measurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Spaces.gam α))) :=
      (Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const _
    simpa only [Function.comp_apply, Pi.mul_apply] using h

theorem aesm_ZU_slice {α : ℝ} {g : ℝ → ℝ → ℝ} (hsmg : Spaces.SmoothNbhd g) {z : ℝ}
    (hz : z ∈ Spaces.Iz) :
    AEStronglyMeasurable (fun θ => ZU α g z θ) (volume.restrict Spaces.Iθ) := by
  have h : (fun θ => ZU α g z θ)
      = fun θ => ∑ k : Fin 5, Thard g k z θ ^ 2 * sghard α k θ := rfl
  rw [h]
  refine Finset.aestronglyMeasurable_sum Finset.univ
    (f := fun k (θ : ℝ) => Thard g k z θ ^ 2 * sghard α k θ) fun k _ => ?_
  refine (((continuousOn_slice (Thard_smoothNbhd hsmg k) hz).aestronglyMeasurable
    measurableSet_Icc).pow 2).mul ?_
  exact (meas_sghard α k).aestronglyMeasurable

theorem ZU_integrable_theta {α : ℝ} {g : ℝ → ℝ → ℝ} (hsmg : Spaces.SmoothNbhd g)
    (hα : 0 < α) (hα1 : α ≤ 1) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => ZU α g z θ) Spaces.Iθ := by
  obtain ⟨C, hC, hbd⟩ := ZU_dom_bounds (α := α) (g := g) hsmg hα hα1 (R := z) hz.le
  refine MeasureTheory.Integrable.mono' ((integrableOn_ZD2 hα hα1).const_mul C)
    (aesm_ZU_slice hsmg hz.le) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem
    (show MeasurableSet Spaces.Iθ from measurableSet_Icc)] with θ hθ
  rw [Real.norm_eq_abs, abs_of_nonneg (ZU_nonneg (α := α) (g := g) hθ)]
  exact (hbd z ⟨hz.le, le_refl z⟩ hz θ hθ).1

end Work.FTS.H2
