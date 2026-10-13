/-
# `Work.FTS_LocDatum3a.hB_locR8` — the pointwise radial bound of the radial factor `locR`

The radial factor of the localised order-`8` datum splits as

  `locR α L β z = -(α/c)·zfarR L z + β·bumpZ z`

(`Work.FTS.LocDataExt.locR_apply`): a far summand, whose `D_z`-jets decay like `1/z` (the
Leibniz bound `zfarR_jet_le8_of_jets` on `[L,2L]`, and the jets of the profile beyond `2L`,
where `zfarR L` agrees with `FM.Fstar`), and a compactly supported bump summand, whose
`D_z`-jets are bounded and vanish off `[3/4, 7/4]`.  The weight `w z = (1+z)²/z²` is decreasing,
so on the support of the bump the two combine into the far-field shape `R/(1+z)²`, and the
statement follows by splitting the two summands (`(a+b)² ≤ 2a² + 2b²`, smooth additivity of
`D_z`-iterates via `E2pkg.DzIter_add_of_contDiffOn`).

The order-`8` jet bound of the profile `F_*(z) = 2z/(1+z)²` is proved from scratch here
(`GkerT`, `hasDerivAt_GkerT`, the Stirling expansion `DzIter_eq_sum_scoef` and the Bell-number
bound `bell j ≤ 9000`), so that this module only depends on the `DzIter_bumpZ_bound` half of the
`LocData` chapter (`Work.FTS.LocData.FstarAux` declares a clashing `Work.FTS.LocData.T1`).

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.LocDataExt.Defs
import Submission.Work.FTS.LocDataExt.SepFactor
import Submission.Work.FTS.LocDataExt.Zfar5
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.DzIter_le_of_pzIter
import Submission.Work.Spaces.scoef
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

/-! ## 1. The order-`8` jet bound of the profile `F_*(z) = 2z/(1+z)²`

The `k`-th derivative of the profile has the closed form
`∂_z^k F_* = 2(-1)^k k! (z-k)/(1+z)^(k+2)` (`GkerT`); the Stirling expansion of `D_z^b`
(`Work.Spaces.DzIter_eq_sum_scoef`) then bounds every `D_z`-jet by `bell b` times the
`z^j ∂_z^j`-bound, which decays like `1/z`. -/

/-- **The closed form of the `k`-th derivative of the profile** `F_*(z) = 2z/(1+z)²`:
`GkerT k z = 2·(-1)^k·k!·(z-k)/(1+z)^(k+2)`.  This is a local copy of
`Work.FTS.LocData.Gker` (whose module declares a `T1` clashing with the one of
`DzIter_bumpZ_bound`), proved independently here. -/
noncomputable def GkerT (k : ℕ) (z : ℝ) : ℝ :=
  2 * (-1 : ℝ) ^ k * (k.factorial : ℝ) * (z - k) / (1 + z) ^ (k + 2)

@[simp] theorem GkerT_apply (k : ℕ) (z : ℝ) :
    GkerT k z = 2 * (-1 : ℝ) ^ k * (k.factorial : ℝ) * (z - k) / (1 + z) ^ (k + 2) := rfl

/-- `GkerT 0` is the profile itself. -/
theorem GkerT_zero (z : ℝ) : GkerT 0 z = Work.FM.Fstar z := by
  simp only [GkerT_apply, Work.FM.Fstar]
  norm_num

/-- The unfolded form of the one-step recursion: `∂_z (2(-1)^k k!(z-k)/(1+z)^(k+2)) =
2(-1)^(k+1)(k+1)!(z-k-1)/(1+z)^(k+3)` off the pole `z = -1`. -/
theorem hasDerivAt_GkerT_aux (k : ℕ) {z : ℝ} (hz : 1 + z ≠ 0) :
    HasDerivAt (fun w : ℝ => 2 * (-1 : ℝ) ^ k * (k.factorial : ℝ) * (w - (k : ℝ))
        / (1 + w) ^ (k + 2))
      (2 * (-1 : ℝ) ^ (k + 1) * ((k + 1).factorial : ℝ) * (z - ((k : ℝ) + 1))
        / (1 + z) ^ (k + 3)) z := by
  have hnum : HasDerivAt (fun w : ℝ => 2 * (-1 : ℝ) ^ k * (k.factorial : ℝ) * (w - (k : ℝ)))
      (2 * (-1 : ℝ) ^ k * (k.factorial : ℝ)) z := by
    have h : HasDerivAt (fun w : ℝ => w - (k : ℝ)) 1 z := (hasDerivAt_id z).sub_const _
    simpa [smul_eq_mul, mul_assoc] using h.const_mul (2 * (-1) ^ k * (k.factorial : ℝ))
  have hden : HasDerivAt (fun w : ℝ => (1 + w) ^ (k + 2))
      (((k : ℝ) + 2) * (1 + z) ^ (k + 1)) z := by
    have hsub : k + 2 - 1 = k + 1 := by omega
    have h0 : HasDerivAt ((fun w : ℝ => 1 + w) ^ (k + 2))
        (((k : ℝ) + 2) * (1 + z) ^ (k + 1)) z := by
      have h1 := (((hasDerivAt_id (x := z)).const_add (1 : ℝ)).pow (k + 2))
      refine h1.congr_deriv ?_
      rw [hsub]
      simp only [id_eq, Nat.cast_add, mul_one]
      ring
    refine (h0.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards with w; simp
    · ring
  have hp : (1 + z) ^ (k + 2) ≠ 0 := pow_ne_zero _ hz
  refine (hnum.fun_div hden hp).congr_deriv ?_
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  field_simp
  ring

/-- **The one-step recursion of the closed forms**: `∂_z (GkerT k) = GkerT (k+1)` off the pole
`z = -1`. -/
theorem hasDerivAt_GkerT (k : ℕ) {z : ℝ} (hz : 1 + z ≠ 0) :
    HasDerivAt (GkerT k) (GkerT (k + 1) z) z := by
  have hfun : GkerT k
      = fun w : ℝ => 2 * (-1 : ℝ) ^ k * (k.factorial : ℝ) * (w - (k : ℝ)) / (1 + w) ^ (k + 2) :=
    rfl
  rw [hfun]
  refine (hasDerivAt_GkerT_aux k hz).congr_deriv ?_
  simp only [GkerT_apply, Nat.cast_add, Nat.cast_one]

/-- **The `pzIter`s of the profile are the closed forms `GkerT`.** -/
theorem pzIter_Fstar_eq_GkerT (k : ℕ) {z : ℝ} (hz : z ∈ Set.Ioi (-1)) (θ : ℝ) :
    Work.Spaces.pzIter k (fun z _ => Work.FM.Fstar z) z θ = GkerT k z := by
  induction k generalizing z with
  | zero => exact (GkerT_zero z).symm
  | succ k ih =>
      have hzlt : (-1 : ℝ) < z := hz
      have hne : (1 : ℝ) + z ≠ 0 := by linarith
      have hev : (fun w : ℝ => Work.Spaces.pzIter k (fun z _ => Work.FM.Fstar z) w θ)
          =ᶠ[𝓝 z] GkerT k := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
        exact ih hw
      rw [Work.Spaces.pzIter_succ, Work.Spaces.pz, Filter.EventuallyEq.deriv_eq hev]
      exact (hasDerivAt_GkerT k hne).deriv

/-- **The far-field decay of `z^k·GkerT k z`**, for `z ≥ 1` and every order `k`:
`|z^k·GkerT k z| ≤ 2·k!·(k+1)/z`. -/
theorem abs_zpow_mul_GkerT_le (k : ℕ) {z : ℝ} (hz : 1 ≤ z) :
    |z ^ k * GkerT k z| ≤ 2 * (k.factorial : ℝ) * ((k : ℝ) + 1) / z := by
  have hz0 : (0 : ℝ) < z := by linarith
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  have hfac : (0 : ℝ) ≤ (k.factorial : ℝ) := by positivity
  have hzpow : (0 : ℝ) ≤ z ^ k := pow_nonneg hz0.le k
  have hden : (0 : ℝ) < (1 + z) ^ (k + 2) := pow_pos hz1 _
  have hkR : |z - (k : ℝ)| ≤ ((k : ℝ) + 1) * z := by
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    rw [abs_le]
    constructor <;> nlinarith [hz]
  have hsign : z ^ k * GkerT k z =
      (-1 : ℝ) ^ k * (2 * (k.factorial : ℝ) * z ^ k * (z - (k : ℝ)) / (1 + z) ^ (k + 2)) := by
    rw [GkerT_apply]
    ring
  rw [hsign, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [abs_div, abs_of_pos hden, abs_mul, abs_mul, abs_mul, abs_of_nonneg hfac,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hzpow]
  have step1 : 2 * (k.factorial : ℝ) * z ^ k * |z - (k : ℝ)| / (1 + z) ^ (k + 2)
      ≤ 2 * (k.factorial : ℝ) * z ^ k * (((k : ℝ) + 1) * z) / (1 + z) ^ (k + 2) := by
    gcongr
  have step2 : 2 * (k.factorial : ℝ) * z ^ k * (((k : ℝ) + 1) * z) / (1 + z) ^ (k + 2)
      ≤ 2 * (k.factorial : ℝ) * ((k : ℝ) + 1) / z := by
    rw [div_le_div_iff₀ hden hz0]
    have h1 : 2 * (k.factorial : ℝ) * z ^ k * (((k : ℝ) + 1) * z) * z
        = 2 * (k.factorial : ℝ) * ((k : ℝ) + 1) * z ^ (k + 2) := by
      rw [pow_add]
      ring
    rw [h1]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz0.le (by linarith) (k + 2))
      (by positivity)
  linarith

/-- The `z`-slices of the profile are smooth on `(-1,∞)` (the only pole of `2z/(1+z)²` is
`z = -1`). -/
theorem contDiffOn_Fstar_self : ContDiffOn ℝ ⊤ (fun z : ℝ => Work.FM.Fstar z) (Set.Ioi (-1)) := by
  have hnum : ContDiffOn ℝ ⊤ (fun z : ℝ => 2 * z) (Set.Ioi (-1)) :=
    contDiffOn_const.mul contDiffOn_id
  have hden : ContDiffOn ℝ ⊤ (fun z : ℝ => (1 + z) ^ 2) (Set.Ioi (-1)) :=
    (contDiffOn_const.add contDiffOn_id).pow 2
  have hne : ∀ z : ℝ, z ∈ Set.Ioi (-1) → (1 + z) ^ 2 ≠ 0 := by
    intro z hz
    have hlt : (-1 : ℝ) < z := hz
    exact pow_ne_zero 2 (by linarith)
  refine (hnum.div hden hne).congr ?_
  intro z _
  simp only [Pi.div_apply, Work.FM.Fstar]

/-- For a function of `z` alone, every `D_z`-iterate is independent of `θ`. -/
theorem DzIter_zonly_theta_indep_self (Φ : ℝ → ℝ) (b : ℕ) (z θ θ' : ℝ) :
    Work.Spaces.DzIter b (fun z _ => Φ z) z θ = Work.Spaces.DzIter b (fun z _ => Φ z) z θ' := by
  induction b generalizing z with
  | zero => rfl
  | succ b ih =>
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [show (fun z' => Work.Spaces.DzIter b (fun z _ => Φ z) z' θ)
          = (fun z' => Work.Spaces.DzIter b (fun z _ => Φ z) z' θ') from
        funext fun z' => ih z']

/-- The iterated plain derivative of a function of `z` alone, as a `pzIter`. -/
theorem pzIter_zonly_eq_deriv_iter_self (Φ : ℝ → ℝ) (k : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter k (fun z _ => Φ z) z θ = deriv^[k] Φ z := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      simp only [Work.Spaces.pzIter_succ, Work.Spaces.pz]
      congr 1
      funext z'
      exact ih z'

/-- **The far-field bound for every `D_z`-iterate of the profile**: for `z ≥ 1` and every order
`b`, `|D_z^b F_*(z)| ≤ bell b · 2·b!·(b+1)/z`. -/
theorem DzIter_Fstar_le_general_self (b : ℕ) {z : ℝ} (hz : 1 ≤ z) (θ : ℝ) :
    |Work.Spaces.DzIter b (fun z _ => Work.FM.Fstar z) z θ|
      ≤ (Work.Spaces.bell b : ℝ) * (2 * (b.factorial : ℝ) * ((b : ℝ) + 1) / z) := by
  have hzmem : z ∈ Set.Ioi (-1) := by simp only [Set.mem_Ioi]; linarith
  have hsm : ∀ θ ∈ Work.Spaces.Iθ, ContDiffOn ℝ ⊤
      (fun z => (fun z _ => Work.FM.Fstar z) z θ) (Set.Ioi (-1)) :=
    fun θ _ => contDiffOn_Fstar_self
  have h0I : (0 : ℝ) ∈ Work.Spaces.Iθ := by
    simp only [Work.Spaces.Iθ, Set.mem_Icc]; exact ⟨le_rfl, by positivity⟩
  rw [DzIter_zonly_theta_indep_self (fun z => Work.FM.Fstar z) b z θ 0]
  rw [Work.Spaces.DzIter_eq_sum_scoef hsm b z hzmem 0 h0I]
  refine Work.Spaces.abs_sum_scoef_mul_le b (2 * (b.factorial : ℝ) * ((b : ℝ) + 1) / z)
    (fun k => z ^ k * Work.Spaces.pzIter k (fun z _ => Work.FM.Fstar z) z 0) ?_
  intro k hk
  rw [pzIter_zonly_eq_deriv_iter_self (fun z => Work.FM.Fstar z) k z 0]
  have hker : deriv^[k] (fun z : ℝ => Work.FM.Fstar z) z = GkerT k z := by
    rw [← pzIter_zonly_eq_deriv_iter_self (fun z => Work.FM.Fstar z) k z 0]
    exact pzIter_Fstar_eq_GkerT k hzmem 0
  rw [hker]
  refine (abs_zpow_mul_GkerT_le k hz).trans ?_
  have hkfac : (k.factorial : ℝ) ≤ (b.factorial : ℝ) := by exact_mod_cast Nat.factorial_le hk
  have hk1 : (k : ℝ) + 1 ≤ (b : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hk
  gcongr

/-- The Bell numbers of the rows `j ≤ 8` are at most `9000` (`B_8 = 4140`). -/
theorem bell_le_9000_of_le_eight (j : ℕ) (hj : j ≤ 8) : Work.Spaces.bell j ≤ 9000 := by
  interval_cases j <;> decide

/-- **The `D_z`-jets of the profile decay like `1/z`, up to order `8`.** -/
theorem FM_Fstar_jet_le8_self :
    ∃ CF : ℝ, 0 < CF ∧ ∀ j ≤ 8, ∀ z : ℝ, 1 ≤ z → ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FM.Fstar z) z θ| ≤ CF / z := by
  refine ⟨6531840000, by norm_num, fun j hj z hz θ => ?_⟩
  have hzpos : (0 : ℝ) < z := by linarith
  refine (DzIter_Fstar_le_general_self j hz θ).trans ?_
  have hbell : (Work.Spaces.bell j : ℝ) ≤ 9000 := by
    exact_mod_cast bell_le_9000_of_le_eight j hj
  have hfac : ((j.factorial : ℕ) : ℝ) ≤ 40320 := by
    have h := Nat.factorial_le hj
    have h8 : (Nat.factorial 8 : ℕ) = 40320 := by decide
    rw [h8] at h
    exact_mod_cast h
  have hj1 : (j : ℝ) + 1 ≤ 9 := by
    have h : j + 1 ≤ 8 + 1 := Nat.succ_le_succ hj
    have hR : ((j + 1 : ℕ) : ℝ) ≤ ((8 + 1 : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at hR
    linarith
  have hfac0 : (0 : ℝ) ≤ ((j.factorial : ℕ) : ℝ) := by positivity
  have hj10 : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
  have hnum : 2 * ((j.factorial : ℕ) : ℝ) * ((j : ℝ) + 1) ≤ 725760 := by
    have h1 : ((j.factorial : ℕ) : ℝ) * ((j : ℝ) + 1) ≤ 40320 * 9 :=
      mul_le_mul hfac hj1 hj10 (by norm_num)
    nlinarith [h1]
  have hB : 2 * ((j.factorial : ℕ) : ℝ) * ((j : ℝ) + 1) / z ≤ 725760 / z :=
    div_le_div_of_nonneg_right hnum hzpos.le
  have hBnn : 0 ≤ 2 * ((j.factorial : ℕ) : ℝ) * ((j : ℝ) + 1) / z := by positivity
  calc (Work.Spaces.bell j : ℝ) * (2 * ((j.factorial : ℕ) : ℝ) * ((j : ℝ) + 1) / z)
      ≤ 9000 * (725760 / z) := mul_le_mul hbell hB hBnn (by norm_num)
    _ = 6531840000 / z := by ring

/-! ## 2. Smoothness of a function of `z` alone on the strip `(-1,∞) × ℝ` -/

/-- A function of `z` alone, viewed as a function of `(z,θ)`, is jointly `C^n` on `(-1,∞) × ℝ`
as soon as its `z`-slice is `C^n` on `(-1,∞)` (the `θ`-variable is a dummy, so no restriction
on `θ` is needed). -/
theorem contDiffOn_uncurry_zOnly {n : ℕ} {φ : ℝ → ℝ}
    (h : ContDiffOn ℝ n φ (Set.Ioi (-1))) :
    ContDiffOn ℝ n (Function.uncurry (fun z (_ : ℝ) => φ z)) (Set.Ioi (-1) ×ˢ Set.univ) := by
  have hfun : Function.uncurry (fun z (_ : ℝ) => φ z) = fun p : ℝ × ℝ => φ p.1 := by
    funext p; rfl
  rw [hfun]
  exact h.comp contDiffOn_fst (fun p hp => hp.1)

/-! ## 3. The `D_z`-jets of `zfarR L` on `[L,∞)`, at order `8` -/

/-- **The `D_z`-jets of the far factor decay like `1/z` on `[L,∞)`.**  On `[L,2L]` the Leibniz
bound `zfarR_jet_le8_of_jets` applies; beyond `2L` the cut-off factor is `1`, so `zfarR L`
agrees with `FM.Fstar` on a neighbourhood of `z` and the profile bound transfers by
`DzIter_z_congr_of_eventuallyEq`. -/
theorem zfarR_jet_le8_Ici {Cu Cv : ℝ} (hCu1 : 1 ≤ Cu) (hCv : 0 < Cv)
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
such that `|D_z^j (zfarR L) z| ≤ A/z` for every `L ≥ 1`, `j ≤ 8`, `z ≥ L` and `θ`. -/
theorem zfarR_jet_le8_clean_Ici :
    ∃ A : ℝ, 0 < A ∧ ∀ L : ℝ, 1 ≤ L → ∀ j : ℕ, j ≤ 8 → ∀ z ∈ Set.Ici L, ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ| ≤ A / z := by
  obtain ⟨Cu, hCu1, hCu⟩ := oneSubChi_jet_le8
  obtain ⟨Cv, hCvpos, hCvle⟩ := FM_Fstar_jet_le8_self
  exact ⟨max (256 * Cu * Cv) Cv, lt_of_lt_of_le hCvpos (le_max_right _ _),
    zfarR_jet_le8_Ici hCu1 hCvpos hCu hCvle⟩

/-- **The radial bound of the far summand** `-(α/c)·zfarR L` at order `8`: from the jet bound
`|D_z^j (zfarR L) z| ≤ A/z` on `z ≥ L` (below `L` the cut-off kills the whole expression). -/
theorem hB_zfar8 (α L : ℝ) {A : ℝ} (hA : 0 ≤ A) (hL : 1 ≤ L)
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

/-! ## 4. The bump `bumpZ` at order `8` -/

/-- The `D_z`-jets of the bump `bumpZ = χ(4·-5)` up to order `8` are bounded. -/
theorem DzIter_bumpZ_bound8 :
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
theorem hB_bumpZ8 :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ j ≤ 8, ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      (Work.Spaces.DzIter j (fun z _ => Work.FTS.LocData.bumpZ z) z θ * Work.Spaces.w z) ^ 2
        ≤ R / (1 + z) ^ 2 := by
  obtain ⟨D, hD⟩ := DzIter_bumpZ_bound8
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

/-! ## 5. The target -/

theorem hB_locR8 (α L β : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hL : 1 ≤ L) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ j ≤ 8, ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      (Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.locR α L β z) z θ
          * Work.Spaces.w z) ^ 2 ≤ R / (1 + z) ^ 2 := by
  classical
  obtain ⟨A, hApos, hAz⟩ := zfarR_jet_le8_clean_Ici
  obtain ⟨R₂, hR₂0, hR₂⟩ := hB_bumpZ8
  have hzfar := hB_zfar8 α L (le_of_lt hApos) hL (hAz L hL)
  refine ⟨2 * (((α / Work.Spaces.c α) ^ 2 * A ^ 2 * 64) + β ^ 2 * R₂) + 1, by positivity,
    fun j hj z hz θ => ?_⟩
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
        (fun z _ => by simp [smul_eq_mul])).of_le (by simp)
  have hφ2 : ContDiffOn ℝ 8 (fun z : ℝ => β * Work.FTS.LocData.bumpZ z) (Set.Ioi (-1)) :=
    ((ContDiffOn.const_smul β (Work.FTS.LocData.BumpZ_contDiff.contDiffOn)).congr
      (fun z _ => by simp [smul_eq_mul])).of_le (by simp)
  have hz0 : (0 : ℝ) ≤ z := hz
  have hmem : (z, θ) ∈ Set.Ioi (-1) ×ˢ Set.univ := by
    refine ⟨?_, trivial⟩
    show (-1 : ℝ) < z
    linarith
  have hadd := Work.FTS.CoercivityFix.Transfer.E2pkg.DzIter_add_of_contDiffOn
    (f₁ := fun z (_ : ℝ) => -(α / Work.Spaces.c α) * Work.FTS.LocDataExt.zfarR L z)
    (f₂ := fun z (_ : ℝ) => β * Work.FTS.LocData.bumpZ z)
    (V := Set.Ioi (-1) ×ˢ Set.univ) (n := 8) (isOpen_Ioi.prod isOpen_univ)
    (contDiffOn_uncurry_zOnly hφ1) (contDiffOn_uncurry_zOnly hφ2) j hj (z, θ) hmem
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
  have hden : (0 : ℝ) < (1 + z) ^ 2 := pow_pos (by linarith) 2
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
