/-
# `H6Pair6Aux/Rl0Pieces` — the `N₀` zero-mode estimate from its three analytic pieces

Target (the piece of the paper's Proposition `muestimate` of tex 1508--1526 that involves only
the explicit profile `F_*` and the perturbation `g`):

`|L₁₂(N₀ α (F_*+g) g)(0)| ≤ K α^{-9}(1+M)^4`   for `H6Adm α g`, `HkMem α 7 g`, `Xn α g ≤ M`.

The estimate is the level-six analogue of the *proved* level-four row
`Work.FTS.Nonlinear.Pieces.rl0_bound`: `|L₁₂(N₀)(0)| ≤ K(α² + √α·|g|_{ℋ⁴} + α^{-3/2}|g|²_{ℋ⁴})`,
whose proof is purely `ℋ⁴`-based (it consumes only the two arithmetic facts
`|L₁₂(g)(z)| ≤ 3|g|_{ℋ⁴}` and the pointwise bound of `N₀` by the `ℋ⁴`-integrand of `g`).

Here the two analytic inputs are *hypotheses*, so that the (long, but purely bookkeeping)
assembly below can be checked independently of them:

* `hsup` : `|L₁₂(g)(z)| ≤ 3|g|_{ℋ⁴}` for every `z ≥ 0` (`SmoothOpen` + `HkMem α 4`);
* `hcont`: joint continuity of `N₀` on the open quadrant;
* `hpt` : the pointwise bound
  `(N₀ α (F_*+g) g r θ)² w r ≤ 7 (A₀ · HkIntegrand α 4 g r θ + B₀ · (1/(1+r))²)`.

The assembly is:

1. the weighted angular energy of `N₀` is dominated a.e. by `r ↦ 7(A₀ Ψ r + (π/2)B₀ (1/(1+r))²)`
   (`hpt` integrated in `θ`), and its a.e. strong measurability / slice integrability follow from
   `hcont`;
2. `|L₁₂(X)(0)| ≤ 3 √(∫_{r>0} Φ r)` for any such domination (`OpenPkg.l12zero_of_weight_bound`,
   which is `Work.FTS.Nonlinear.Pieces.L12_zero_le_weak` + the Hardy comparison
   `∫ (∫_θ X²) w ≤ HkSq α 4 X`);
3. `∫_{r>0} Φ ≤ 10⁷ α^{-9}(1+X)⁴` from `A₀ ≤ 90 X²/α² + 16α²`, `B₀ ≤ 25600α⁴ + 90000α²X²`,
   `∫_{r>0}(1/(1+r))² ≤ 2`, `π ≤ 4` and the monotonicity of `α ↦ α^{e}` for `e < 0` (all powers
   are pushed into `α^{-9}`);
4. `3 √(10⁷ α^{-9}(1+X)⁴) ≤ 10⁵ α^{-9}(1+M)⁴` (the `√10⁷ ≤ 10⁴`, `α^{-9/2} ≤ α^{-9}`,
   `(1+X)² ≤ (1+X)⁴` and `X ≤ M` losses).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.Basic
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.Rl0Defs
import Submission.Work.FTS.Nonlinear.Pieces.rowsAux
import Submission.Work.FTS.OpenPkg.l12zero_field
import Submission.Work.FTS.H2.InvOneAddSq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- `1 ≤ t^{-γ}` for `0 < t ≤ 1`, `0 ≤ γ` (the `α`-power monotonicity used by the arithmetic). -/
theorem one_le_rpow_neg' {t γ : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) (hg : 0 ≤ γ) :
    1 ≤ t ^ (-γ) := by
  rw [Real.rpow_neg h0.le]
  exact (one_le_inv₀ (Real.rpow_pos_of_pos h0 γ)).mpr (Real.rpow_le_one h0.le h1 hg)

/-- **The `N₀` zero-mode estimate from its three analytic pieces.**

`hsup` is the pointwise `L₁₂` bound `|L₁₂ g z| ≤ 3|g|_{ℋ⁴}` (the sibling
`Work.FTS.StrongPersist.H6Pair6Aux.l12_supAbs_open`), `hcont` the joint continuity of `N₀` on the
open quadrant (`...contN0_open`) and `hpt` the pointwise domination of `N₀²` by the `ℋ⁴`-integrand
of `g` (`...N0_sq_w_open`).  The conclusion is the requested uniform bound with the explicit
constant `K = 10⁵`, valid for `α ∈ (0,1]`. -/
theorem h6pair_N0_zero_of_pieces
    (hsup : ∀ {α : ℝ} {g : Fn}, 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
      ∀ z : ℝ, 0 ≤ z → |Work.Construction.L12 g z| ≤ 3 * Work.FTS.Nonlin.Xn α g)
    (hcont : ∀ {α : ℝ} {g : Fn}, 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
      ContinuousOn (Function.uncurry (Work.Construction.N0 α (Work.Construction.Ftot α g) g))
        (Set.Ioi 0 ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hpt : ∀ {α : ℝ} {g : Fn}, 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen g →
      (∀ z : ℝ, 0 ≤ z → |Work.Construction.L12 g z| ≤ 3 * Work.FTS.Nonlin.Xn α g) →
      ∀ r ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        (Work.Construction.N0 α (Work.Construction.Ftot α g) g r θ) ^ 2 * Work.Spaces.w r
          ≤ 7 * (A₀ α (Work.FTS.Nonlin.Xn α g) * Work.Spaces.HkIntegrand α 4 g r θ
              + B₀ α (Work.FTS.Nonlin.Xn α g) * (1 / (1 + r)) ^ 2)) :
    ∃ K α₂ : ℝ, 0 < K ∧ 0 < α₂ ∧
      ∀ α ∈ Set.Ioc 0 α₂, ∀ (f : Fn) (M : ℝ),
        H6Adm α f → Work.Spaces.HkMem α 7 f → Work.FTS.Nonlin.Xn α f ≤ M →
        |Work.Construction.L12 (Work.Construction.N0 α
            (fun z θ => Work.Construction.Fstar α z θ + f z θ) f) 0|
          ≤ K * α ^ (-(9 : ℝ)) * (1 + M) ^ 4 := by
  refine ⟨10 ^ 5, 1, by norm_num, by norm_num, ?_⟩
  intro α hαI f M hAdm _hmem7 hM
  have hα : 0 < α := hαI.1
  have hα1 : α ≤ 1 := hαI.2
  have hso : Work.FTS.EllipticEst.SmoothOpen f := hAdm.reg.1
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.StrongPersist.HkMem_four_of_six hso hAdm.reg.2
  have hL12g : ∀ z : ℝ, 0 ≤ z → |Work.Construction.L12 f z| ≤ 3 * Work.FTS.Nonlin.Xn α f :=
    hsup hα hα1 hso hmem4
  have hptf := hpt hα hα1 hso hL12g
  have hcontf := hcont hα hα1 hso hmem4
  set X : ℝ := Work.FTS.Nonlin.Xn α f with hX
  have hX0 : 0 ≤ X := by rw [hX]; exact Work.Spaces.HkNorm_nonneg α 4 f
  have hX2 : 0 ≤ X ^ 2 := by positivity
  have hX4 : 0 ≤ X ^ 4 := by positivity
  set Ψ : ℝ → ℝ := fun r => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ with hΨ
  have hΨint : MeasureTheory.IntegrableOn Ψ (Set.Ioi (0 : ℝ)) :=
    hmem4.2.mono_set Set.Ioi_subset_Ici_self
  set Φ : ℝ → ℝ := fun r =>
    7 * (A₀ α X * Ψ r + ((Real.pi / 2) * B₀ α X) * (1 / (1 + r)) ^ 2) with hΦ
  -- ## the weighted angular energy of `N₀` is dominated by `Φ`
  have hbd : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      (∫ θ in Work.Spaces.Iθ,
          (Work.Construction.N0 α (Work.Construction.Ftot α f) f r θ) ^ 2)
          * ((1 + r) / r) ^ 2
        ≤ Φ r := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : (0 : ℝ) < r := hr
    have hzr : r ∈ Work.Spaces.Iz := by simpa only [Work.Spaces.Iz, Set.mem_Ici] using hr0.le
    have hW1 : 1 ≤ Work.Spaces.w r := by
      rw [Work.Spaces.w, one_le_div (pow_pos hr0 2)]
      nlinarith
    have hweq : ((1 + r) / r) ^ 2 = Work.Spaces.w r := by rw [Work.Spaces.w, div_pow]
    have hΦr : Φ r = 7 * (A₀ α X * Ψ r + ((Real.pi / 2) * B₀ α X) * (1 / (1 + r)) ^ 2) := by
      rw [hΦ]
    rw [hweq, ← MeasureTheory.integral_mul_const, hΦr]
    have hIoo2 : MeasureTheory.volume.restrict Work.Spaces.Iθ
        = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm
    have hstep : (∫ θ in Work.Spaces.Iθ,
          (Work.Construction.N0 α (Work.Construction.Ftot α f) f r θ) ^ 2
            * Work.Spaces.w r)
        ≤ ∫ θ in Work.Spaces.Iθ,
          7 * (A₀ α X * Work.Spaces.HkIntegrand α 4 f r θ
            + B₀ α X * (1 / (1 + r)) ^ 2) := by
      refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
      · exact Filter.Eventually.of_forall (fun θ =>
          mul_nonneg (sq_nonneg _) (le_trans zero_le_one hW1))
      · refine (((hmem4.1 r hzr).const_mul (A₀ α X)).add ?_).const_mul 7
        refine MeasureTheory.integrableOn_const ?_
        rw [Work.Spaces.Iθ, Real.volume_Icc]
        exact ENNReal.ofReal_ne_top
      · rw [hIoo2]
        exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
          (fun θ hθ => by simpa only [hX] using hptf r hr θ hθ)
    refine hstep.trans ?_
    have hintA : MeasureTheory.IntegrableOn
        (fun θ => A₀ α X * Work.Spaces.HkIntegrand α 4 f r θ) Work.Spaces.Iθ :=
      (hmem4.1 r hzr).const_mul (A₀ α X)
    have hintB : MeasureTheory.IntegrableOn
        (fun θ => B₀ α X * (1 / (1 + r)) ^ 2) Work.Spaces.Iθ := by
      refine MeasureTheory.integrableOn_const ?_
      rw [Work.Spaces.Iθ, Real.volume_Icc]
      exact ENNReal.ofReal_ne_top
    have hvalPsi : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ) = Ψ r := rfl
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hintA hintB,
      MeasureTheory.integral_const_mul, Work.FTS.Nonlinear.Pieces.integral_const_Iθ_ra, hvalPsi]
    exact le_of_eq (by ring)
  -- ## the slice integrability of the squared `N₀`
  have hsl : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn
        (fun θ => (Work.Construction.N0 α (Work.Construction.Ftot α f) f r θ) ^ 2)
        Work.Spaces.Iθ := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : (0 : ℝ) < r := hr
    have hzr : r ∈ Work.Spaces.Iz := by simpa only [Work.Spaces.Iz, Set.mem_Ici] using hr0.le
    have hW1 : 1 ≤ Work.Spaces.w r := by
      rw [Work.Spaces.w, one_le_div (pow_pos hr0 2)]
      nlinarith
    have hIoo2 : MeasureTheory.volume.restrict Work.Spaces.Iθ
        = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm
    have hslice : MeasureTheory.AEStronglyMeasurable
        (fun θ => Work.Construction.N0 α (Work.Construction.Ftot α f) f r θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcontf hr
    have hmaj : MeasureTheory.Integrable
        (fun θ => 7 * (A₀ α X * Work.Spaces.HkIntegrand α 4 f r θ
          + B₀ α X * (1 / (1 + r)) ^ 2))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      refine (((hmem4.1 r hzr).const_mul (A₀ α X)).add ?_).const_mul 7
      refine MeasureTheory.integrableOn_const ?_
      rw [Work.Spaces.Iθ, Real.volume_Icc]
      exact ENNReal.ofReal_ne_top
    refine MeasureTheory.Integrable.mono' hmaj (hslice.pow 2) ?_
    rw [hIoo2]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc (Work.Construction.N0 α (Work.Construction.Ftot α f) f r θ) ^ 2
        ≤ (Work.Construction.N0 α (Work.Construction.Ftot α f) f r θ) ^ 2
          * Work.Spaces.w r := by
          nlinarith [hW1,
            sq_nonneg (Work.Construction.N0 α (Work.Construction.Ftot α f) f r θ)]
      _ ≤ 7 * (A₀ α X * Work.Spaces.HkIntegrand α 4 f r θ
          + B₀ α X * (1 / (1 + r)) ^ 2) := by
          simpa only [hX] using hptf r hr θ hθ
  -- ## a.e. strong measurability of the weighted angular energy of `N₀`
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun r => (∫ θ in Work.Spaces.Iθ,
          (Work.Construction.N0 α (Work.Construction.Ftot α f) f r θ) ^ 2) * ((1 + r) / r) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    Work.FTS.Nonlinear.Pieces.aesm_weighted_energy_of_continuousOn hcontf
  -- ## integrability of the majorant `Φ`
  have hΦint : MeasureTheory.IntegrableOn Φ (Set.Ioi (0 : ℝ)) := by
    have h1 : MeasureTheory.IntegrableOn (fun r => A₀ α X * Ψ r) (Set.Ioi (0 : ℝ)) :=
      hΨint.const_mul (A₀ α X)
    have h2 : MeasureTheory.IntegrableOn
        (fun r => ((Real.pi / 2) * B₀ α X) * (1 / (1 + r)) ^ 2) (Set.Ioi (0 : ℝ)) :=
      Work.FTS.H2.InvOneAddSq.1.const_mul ((Real.pi / 2) * B₀ α X)
    exact (h1.add h2).const_mul 7
  -- ## the zero-mode bound
  have hmain := Work.FTS.OpenPkg.l12zero_of_weight_bound
    (f := fun z θ => Work.Construction.N0 α (Work.Construction.Ftot α f) f z θ)
    hsl hmeas hΦint hbd
  -- ## the size of `Φ`
  have hΨval : (∫ r in Set.Ioi (0 : ℝ), Ψ r) = X ^ 2 := by
    have h1 : (∫ r in Set.Ioi (0 : ℝ), Ψ r) = Work.Spaces.HkSq α 4 f := by
      rw [hΨ, Work.Spaces.HkSq, Work.Spaces.Iz]
      exact MeasureTheory.setIntegral_congr_set MeasureTheory.Ioi_ae_eq_Ici
    have h2 : X ^ 2 = Work.Spaces.HkSq α 4 f := by
      rw [hX, Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm,
        Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 f)]
    rw [h1, h2]
  have hc2 : (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2) ≤ 2 := Work.FTS.H2.InvOneAddSq.2
  have hci0 : (0 : ℝ) ≤ ∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2 :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioi (fun r _ => by positivity)
  set A : ℝ := α ^ (-(9 : ℝ)) with hA
  have hApos : 0 < A := by rw [hA]; exact Real.rpow_pos_of_pos hα _
  have hA0 : 0 ≤ A := le_of_lt hApos
  have hA1 : 1 ≤ A := by rw [hA]; exact one_le_rpow_neg' hα hα1 (by norm_num)
  have h_inv2 : (α ^ 2)⁻¹ ≤ A := by
    rw [← one_div, div_le_iff₀ (pow_pos hα 2), hA, ← Real.rpow_natCast α 2,
      ← Real.rpow_add hα (-(9 : ℝ)) ((2 : ℕ) : ℝ)]
    rw [show (-(9 : ℝ)) + ((2 : ℕ) : ℝ) = -(7 : ℝ) by norm_num]
    exact one_le_rpow_neg' hα hα1 (by norm_num)
  have h_sq : α ^ 2 ≤ A := by
    have h := Real.rpow_le_rpow_of_exponent_ge hα hα1 (show (-(9 : ℝ)) ≤ (2 : ℝ) by norm_num)
    rw [hA, ← Real.rpow_natCast α 2]
    exact h
  have h_4 : α ^ 4 ≤ A := by
    have h := Real.rpow_le_rpow_of_exponent_ge hα hα1 (show (-(9 : ℝ)) ≤ (4 : ℝ) by norm_num)
    rw [hA, ← Real.rpow_natCast α 4]
    exact h
  have h1X : (1 : ℝ) ≤ 1 + X := by linarith
  have hX4le : X ^ 4 ≤ (1 + X) ^ 4 := pow_le_pow_left₀ hX0 (by linarith : X ≤ 1 + X) 4
  have hX2le : X ^ 2 ≤ (1 + X) ^ 4 := by
    have h1 : X ^ 2 ≤ (1 + X) ^ 2 := pow_le_pow_left₀ hX0 (by linarith : X ≤ 1 + X) 2
    have h2 : (1 + X) ^ 2 ≤ (1 + X) ^ 4 := pow_le_pow_right₀ h1X (by norm_num)
    linarith
  have h1le : (1 : ℝ) ≤ (1 + X) ^ 4 := one_le_pow₀ h1X
  have h01X : (0 : ℝ) ≤ 1 + X := by linarith
  have hAle : A ≤ (1 + X) ^ 4 * A := by
    simpa using mul_le_mul_of_nonneg_right h1le hA0
  have hInt_le : (∫ r in Set.Ioi (0 : ℝ), Φ r) ≤ 10 ^ 7 * A * (1 + X) ^ 4 := by
    set M' : ℝ := 25600 * α ^ 4 + 90000 * (α ^ 2 * X ^ 2) with hM'def
    have hM'0 : 0 ≤ M' := by rw [hM'def]; positivity
    have h1 : MeasureTheory.IntegrableOn (fun r => A₀ α X * Ψ r) (Set.Ioi (0 : ℝ)) :=
      hΨint.const_mul (A₀ α X)
    have h2 : MeasureTheory.IntegrableOn
        (fun r => ((Real.pi / 2) * B₀ α X) * (1 / (1 + r)) ^ 2) (Set.Ioi (0 : ℝ)) :=
      Work.FTS.H2.InvOneAddSq.1.const_mul ((Real.pi / 2) * B₀ α X)
    have hΦval : (∫ r in Set.Ioi (0 : ℝ), Φ r)
        = 7 * (A₀ α X * X ^ 2 + ((Real.pi / 2) * B₀ α X)
            * (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2)) := by
      rw [hΦ, MeasureTheory.integral_const_mul, MeasureTheory.integral_add h1 h2,
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, hΨval]
    rw [hΦval]
    have hπ4 : Real.pi ≤ 4 := le_of_lt Real.pi_lt_four
    -- the two summands
    have hT1 : A₀ α X * X ^ 2 ≤ 90 * (X ^ 4 / α ^ 2) + 16 * (α ^ 2 * X ^ 2) := by
      have h := mul_le_mul_of_nonneg_right (A₀_le (X := X) hα hα1) hX2
      have he : (90 * X ^ 2 / α ^ 2 + 16 * α ^ 2) * X ^ 2
          = 90 * (X ^ 4 / α ^ 2) + 16 * (α ^ 2 * X ^ 2) := by ring
      linarith [h, he.le, he.ge]
    have hT2 : B₀ α X * (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2) ≤ 2 * M' := by
      rw [hM'def]
      have h1' : B₀ α X * (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2)
          ≤ (25600 * α ^ 4 + 90000 * α ^ 2 * X ^ 2)
            * (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2) :=
        mul_le_mul_of_nonneg_right (B₀_le α X) hci0
      have h2' : (25600 * α ^ 4 + 90000 * α ^ 2 * X ^ 2)
            * (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2)
          ≤ (25600 * α ^ 4 + 90000 * α ^ 2 * X ^ 2) * 2 :=
        mul_le_mul_of_nonneg_left hc2 (by positivity)
      have he : (25600 * α ^ 4 + 90000 * α ^ 2 * X ^ 2) * 2
          = 2 * (25600 * α ^ 4 + 90000 * (α ^ 2 * X ^ 2)) := by ring
      linarith [h1', h2', he.le, he.ge]
    have hπB : ((Real.pi / 2) * B₀ α X) * (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2)
        ≤ 4 * M' := by
      calc ((Real.pi / 2) * B₀ α X) * (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2)
          = (Real.pi / 2) * (B₀ α X * (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2)) := by
            ring
        _ ≤ (Real.pi / 2) * (2 * M') := mul_le_mul_of_nonneg_left hT2 (by positivity)
        _ = Real.pi * M' := by ring
        _ ≤ 4 * M' := mul_le_mul_of_nonneg_right hπ4 hM'0
    -- the termwise bounds, with the `α`-powers pushed into `A`
    have hp1 : 90 * (X ^ 4 / α ^ 2) ≤ 90 * ((1 + X) ^ 4 * A) := by
      have h1' : X ^ 4 / α ^ 2 ≤ X ^ 4 * A := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left h_inv2 hX4
      calc 90 * (X ^ 4 / α ^ 2) ≤ 90 * (X ^ 4 * A) :=
            mul_le_mul_of_nonneg_left h1' (by norm_num)
        _ ≤ 90 * ((1 + X) ^ 4 * A) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hX4le hA0) (by norm_num)
    have hp2 : 16 * (α ^ 2 * X ^ 2) ≤ 16 * ((1 + X) ^ 4 * A) := by
      have h1' : α ^ 2 * X ^ 2 ≤ X ^ 2 * A := by
        rw [mul_comm (α ^ 2) (X ^ 2)]
        exact mul_le_mul_of_nonneg_left h_sq hX2
      calc 16 * (α ^ 2 * X ^ 2) ≤ 16 * (X ^ 2 * A) :=
            mul_le_mul_of_nonneg_left h1' (by norm_num)
        _ ≤ 16 * ((1 + X) ^ 4 * A) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hX2le hA0) (by norm_num)
    have hM'le : M' ≤ 25600 * ((1 + X) ^ 4 * A) + 90000 * ((1 + X) ^ 4 * A) := by
      have ha : α ^ 4 ≤ (1 + X) ^ 4 * A := le_trans h_4 hAle
      have hb : α ^ 2 * X ^ 2 ≤ (1 + X) ^ 4 * A := by
        refine le_trans ?_ (mul_le_mul_of_nonneg_right hX2le hA0)
        rw [mul_comm (α ^ 2) (X ^ 2)]
        exact mul_le_mul_of_nonneg_left h_sq hX2
      rw [hM'def]
      exact add_le_add (mul_le_mul_of_nonneg_left ha (by norm_num))
        (mul_le_mul_of_nonneg_left hb (by norm_num))
    have h4M : 4 * M' ≤ 4 * (25600 * ((1 + X) ^ 4 * A) + 90000 * ((1 + X) ^ 4 * A)) :=
      mul_le_mul_of_nonneg_left hM'le (by norm_num)
    have hbound : 7 * (A₀ α X * X ^ 2 + ((Real.pi / 2) * B₀ α X)
          * (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2))
        ≤ 7 * (90 * ((1 + X) ^ 4 * A) + 16 * ((1 + X) ^ 4 * A)
            + 4 * (25600 * ((1 + X) ^ 4 * A) + 90000 * ((1 + X) ^ 4 * A))) := by
      have hsum : A₀ α X * X ^ 2 + ((Real.pi / 2) * B₀ α X)
            * (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2)
          ≤ (90 * (X ^ 4 / α ^ 2) + 16 * (α ^ 2 * X ^ 2)) + 4 * M' := by
        linarith [hT1, hπB]
      have hsum2 : (90 * (X ^ 4 / α ^ 2) + 16 * (α ^ 2 * X ^ 2)) + 4 * M'
          ≤ 90 * ((1 + X) ^ 4 * A) + 16 * ((1 + X) ^ 4 * A)
            + 4 * (25600 * ((1 + X) ^ 4 * A) + 90000 * ((1 + X) ^ 4 * A)) := by
        linarith [hp1, hp2, h4M]
      exact mul_le_mul_of_nonneg_left (le_trans hsum hsum2) (by norm_num)
    refine hbound.trans ?_
    have hfin : 7 * (90 * ((1 + X) ^ 4 * A) + 16 * ((1 + X) ^ 4 * A)
          + 4 * (25600 * ((1 + X) ^ 4 * A) + 90000 * ((1 + X) ^ 4 * A)))
        = (7 * (90 + 16 + 4 * (25600 + 90000))) * ((1 + X) ^ 4 * A) := by ring
    rw [hfin]
    have hc : 7 * (90 + 16 + 4 * (25600 + 90000)) ≤ (10 : ℝ) ^ 7 := by norm_num
    have hBnn : 0 ≤ (1 + X) ^ 4 * A := mul_nonneg (pow_nonneg h01X 4) hA0
    calc (7 * (90 + 16 + 4 * (25600 + 90000))) * ((1 + X) ^ 4 * A)
        ≤ (10 : ℝ) ^ 7 * ((1 + X) ^ 4 * A) := mul_le_mul_of_nonneg_right hc hBnn
      _ = 10 ^ 7 * A * (1 + X) ^ 4 := by ring
  -- ## the square root and the final constant
  have hΦ0 : 0 ≤ ∫ r in Set.Ioi (0 : ℝ), Φ r := by
    refine MeasureTheory.setIntegral_nonneg measurableSet_Ioi (fun r _ => ?_)
    have hΨr0 : 0 ≤ Ψ r := by
      rw [hΨ]
      exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 4 f r θ)
    have h1 : (0 : ℝ) ≤ A₀ α X * Ψ r := mul_nonneg (A₀_nonneg α X) hΨr0
    have h2 : (0 : ℝ) ≤ ((Real.pi / 2) * B₀ α X) * (1 / (1 + r)) ^ 2 :=
      mul_nonneg (mul_nonneg (by positivity) (B₀_nonneg α X)) (sq_nonneg _)
    rw [hΦ]
    exact mul_nonneg (by norm_num) (add_nonneg h1 h2)
  have hsqrt : |Work.Construction.L12
      (Work.Construction.N0 α (Work.Construction.Ftot α f) f) 0|
      ≤ 3 * Real.sqrt (10 ^ 7 * A * (1 + X) ^ 4) := by
    refine hmain.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact Real.sqrt_le_sqrt hInt_le
  have hbig0 : (0 : ℝ) ≤ 10 ^ 4 * A * (1 + X) ^ 4 := by positivity
  have hsqrtle : Real.sqrt (10 ^ 7 * A * (1 + X) ^ 4) ≤ 10 ^ 4 * A * (1 + X) ^ 4 := by
    rw [Real.sqrt_le_left hbig0]
    have hAB : 1 ≤ A * (1 + X) ^ 4 := by
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ A * (1 + X) ^ 4 := mul_le_mul hA1 h1le (by norm_num) hA0
    have hAB0 : 0 ≤ A * (1 + X) ^ 4 := mul_nonneg hA0 (pow_nonneg h01X 4)
    have hle1 : 1 ≤ 10 * (A * (1 + X) ^ 4) := by linarith
    have hc0 : 0 ≤ (10 : ℝ) ^ 7 * (A * (1 + X) ^ 4) := by positivity
    have hstep := mul_le_mul_of_nonneg_left hle1 hc0
    have hstep' : (10 : ℝ) ^ 7 * (A * (1 + X) ^ 4)
        ≤ (10 : ℝ) ^ 7 * (A * (1 + X) ^ 4) * (10 * (A * (1 + X) ^ 4)) := by
      simpa only [mul_one] using hstep
    calc 10 ^ 7 * A * (1 + X) ^ 4 = (10 : ℝ) ^ 7 * (A * (1 + X) ^ 4) := by ring
      _ ≤ (10 : ℝ) ^ 7 * (A * (1 + X) ^ 4) * (10 * (A * (1 + X) ^ 4)) := hstep'
      _ = (10 ^ 4 * A * (1 + X) ^ 4) ^ 2 := by ring
  have hM1 : (1 : ℝ) ≤ 1 + M := by linarith [le_trans hX0 hM]
  have hXM : (1 + X) ^ 4 ≤ (1 + M) ^ 4 :=
    pow_le_pow_left₀ h01X (by linarith [hM]) 4
  calc |Work.Construction.L12
        (Work.Construction.N0 α (Work.Construction.Ftot α f) f) 0|
      ≤ 3 * Real.sqrt (10 ^ 7 * A * (1 + X) ^ 4) := hsqrt
    _ ≤ 3 * (10 ^ 4 * A * (1 + X) ^ 4) := mul_le_mul_of_nonneg_left hsqrtle (by norm_num)
    _ ≤ 10 ^ 5 * A * (1 + M) ^ 4 := by
        have hnn : 0 ≤ A * (1 + X) ^ 4 := mul_nonneg hA0 (pow_nonneg h01X 4)
        have h3 : 3 * (10 ^ 4 * A * (1 + X) ^ 4) ≤ 10 ^ 5 * A * (1 + X) ^ 4 := by
          calc 3 * (10 ^ 4 * A * (1 + X) ^ 4) = (3 * 10 ^ 4) * (A * (1 + X) ^ 4) := by ring
            _ ≤ (10 : ℝ) ^ 5 * (A * (1 + X) ^ 4) :=
                mul_le_mul_of_nonneg_right (by norm_num) hnn
            _ = 10 ^ 5 * A * (1 + X) ^ 4 := by ring
        have h4 : 10 ^ 5 * A * (1 + X) ^ 4 ≤ 10 ^ 5 * A * (1 + M) ^ 4 := by
          have h5 : 0 ≤ 10 ^ 5 * A := by positivity
          have h6 := mul_le_mul_of_nonneg_left hXM h5
          calc 10 ^ 5 * A * (1 + X) ^ 4 = (10 ^ 5 * A) * (1 + X) ^ 4 := by ring
            _ ≤ (10 ^ 5 * A) * (1 + M) ^ 4 := h6
            _ = 10 ^ 5 * A * (1 + M) ^ 4 := by ring
        linarith [h3, h4]

end Work.FTS.StrongPersist.H6Pair6Aux
