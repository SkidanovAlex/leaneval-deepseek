import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.MinImports
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EpsMem
import Submission.Work.FTS.StrongEps.EpsODE
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsNstarBlock
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_MuLamOK.Rows.Rl2Open
import Submission.Work.FTS_MuLipC.RowN.PvAesmOpen
import Submission.Work.FTS_RegExport.RXB.sup_bound_all_alpha
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_RegExport.RXT.starVop
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.NonlinRows.NRow15T2Aux.Bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNPV2.row19 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Row 19 of the `N4` table: the `V(Φ̃_*)·D_zF_*` piece

The piece is `N₃^{**} = -2α · V(Φ̃_*) · D_zF_*` (`Work.FTS.Nonlin.N3ss`,
`Work.FTS.Nonlinear.Pieces.RNP.Vs = Vop (PhiTs α Φs)`, `...Gs = Dz (Fstar α)`), and the claim is
`|N₃^{**}|_{ℋ⁴} ≤ K α³`.

The design's `𝒲^{4,∞}`-route (`WtoHQ` + the weighted product rule) is one order short of what
`StarPkg` provides (see `RNP/NOTES_row19.md`).  The proof below instead uses the *split*

  `V = V₀ + W`,   `V₀(θ) := V(0,θ)`,  `W := V - V₀`,

together with the two halves of the row that are available in the workspace:

* `RNP/row19/HkSq_VsW_mul_Gs_le` — the honest estimate for the part `W·D_zF_*` that vanishes at
  `z = 0`: `HkSq α 4 (W·D_zF_*) ≤ K₁ (max Cs 0)² α⁴` (from the `𝒲^{4,∞}`-fields of `StarPkg`
  and the Lipschitz bound `|W| ≤ M z`);
* `RNP/row19/HkSqZero` — the degenerate case: if `V(0,·)` does not vanish identically then the
  `ℋ⁴`-integrand of `V·D_zF_*` has a `z^{-2}` singularity, so the (Bochner) integral `HkSq` is
  `0` (`integral_undef`).

The two cases are glued by `HkSq_congr_open` (which sees only the open quadrant, where
`V = W` when `V₀ ≡ 0`), and the result is converted into the `ℋ⁴`-norm through
`Xn α (N₃^{**}) = 2α · Xn α (V·D_zF_*)` and `HkNorm = √HkSq`. -/
namespace Work.FTS.Nonlinear.Pieces.RNPV2

open Work.FTS.Nonlinear.Pieces.RNP (Vs Gs)

theorem row19 {α₂ Ci Ct Ce Cs : ℝ} (hN : Work.FTS.Nonlin.N4Norm Ci α₂) : ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn}, Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.StarPkg α Cs Φs → Work.FTS.Nonlin.EllPkgG α Ce g Φg → 0 < α → α ≤ 1 → α ≤ α₂ → Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N3ss α Φs) ≤ K * α ^ 3 := by
  obtain ⟨K₁, hK₁, hVsW⟩ := Work.FTS.Nonlinear.Pieces.RNP.row19.HkSq_VsW_mul_Gs_le
  refine ⟨2 * Real.sqrt K₁ * (max Cs 0 + 1), ?_, ?_⟩
  · have h1 : 0 < Real.sqrt K₁ := Real.sqrt_pos_of_pos hK₁
    have h2 : 0 < max Cs 0 + 1 := by
      have := le_max_right Cs (0 : ℝ); linarith
    exact mul_pos (mul_pos (by norm_num) h1) h2
  · intro α g Φs Φg _hGal hStar _hEll hα hα1 _hαα₂
    -- the `ℋ⁴`-square of `V(Φ̃_*)·D_zF_*`
    have hsq : Work.Spaces.HkSq α 4 (fun z θ => Vs α Φs z θ * Gs α z θ)
        ≤ K₁ * (max Cs 0) ^ 2 * α ^ 4 := by
      by_cases h0 : ∃ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Vs α Φs 0 θ ≠ 0
      · -- `V(0,·) ≢ 0`: the integrand has a `z^{-2}` singularity, so `HkSq` is the junk value `0`
        rw [Work.FTS.Nonlinear.Pieces.RNP.row19.HkSqZero hα hStar h0]
        positivity
      · have h0' : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Vs α Φs 0 θ = 0 := by
          intro θ hθ
          by_contra hne
          exact h0 ⟨θ, hθ, hne⟩
        -- `V = V₀ + W` with `V₀ ≡ 0` on the open quadrant, so `V·D_zF_* = W·D_zF_*` there
        rw [Work.FTS.EllipticEst.HkSq_congr_open α 4
          (f := fun z θ => Vs α Φs z θ * Gs α z θ)
          (g := fun z θ => Work.FTS.Nonlinear.Pieces.RNP.row19.VsW α Φs z θ * Gs α z θ)
          (fun z θ _ hθ1 hθ2 => by
            have hz0 : Vs α Φs 0 θ = 0 := h0' θ ⟨hθ1, hθ2⟩
            rw [Work.FTS.Nonlinear.Pieces.RNP.row19.VsW_apply]
            change Vs α Φs z θ * Gs α z θ
              = (Vs α Φs z θ - Vs α Φs 0 θ) * Gs α z θ
            rw [hz0, sub_zero])]
        exact hVsW hStar hα hα1
    -- pass to the norm
    have hnorm : Work.FTS.Nonlin.Xn α (fun z θ => Vs α Φs z θ * Gs α z θ)
        ≤ Real.sqrt K₁ * max Cs 0 * α ^ 2 := by
      rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm]
      refine (Real.sqrt_le_sqrt hsq).trans (le_of_eq ?_)
      have harg : K₁ * (max Cs 0) ^ 2 * α ^ 4
          = (Real.sqrt K₁ * max Cs 0 * α ^ 2) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hK₁.le]
        ring
      rw [harg, Real.sqrt_sq (mul_nonneg (mul_nonneg (Real.sqrt_nonneg K₁)
        (le_max_right Cs 0)) (sq_nonneg α))]
    calc Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N3ss α Φs)
        = 2 * α * Work.FTS.Nonlin.Xn α (fun z θ => Vs α Φs z θ * Gs α z θ) :=
          Work.FTS.Nonlinear.Pieces.RNP.xn_N3ss_of_nonneg hα.le Φs
      _ ≤ 2 * α * (Real.sqrt K₁ * max Cs 0 * α ^ 2) :=
          mul_le_mul_of_nonneg_left hnorm (by linarith)
      _ = 2 * Real.sqrt K₁ * max Cs 0 * α ^ 3 := by ring
      _ ≤ 2 * Real.sqrt K₁ * (max Cs 0 + 1) * α ^ 3 := by
          have hmax : max Cs 0 ≤ max Cs 0 + 1 := by linarith [le_max_right Cs (0 : ℝ)]
          have h2 : (0 : ℝ) ≤ 2 * Real.sqrt K₁ := by positivity
          have h3 : (0 : ℝ) ≤ α ^ 3 := by positivity
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmax h2) h3

end Work.FTS.Nonlinear.Pieces.RNPV2
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.RadGreenFarTools =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace Work.FTS.PhiStar.Honesty

open Work.FTS.EllExist.Honesty (G1 G2 G1f)
open Work.FTS.PhiStar.RadialWAux (radP radQ)

/-! ### Elementary tools -/
/-- Weighted AM–GM: `2|XY| ≤ l·X² + (1/l)·Y²` for `l > 0`. -/
theorem radFar_two_mul_abs_mul_le_inv {l X Y : ℝ} (hl : 0 < l) :
    2 * |X * Y| ≤ l * X ^ 2 + (1 / l) * Y ^ 2 := by
  rw [abs_mul]
  have h := two_mul_le_add_sq (l * |X|) (|Y|)
  have h' : (l * |X|) ^ 2 + |Y| ^ 2 = l ^ 2 * X ^ 2 + Y ^ 2 := by
    rw [mul_pow, sq_abs, sq_abs]
  have h3 : 2 * (|X| * |Y|) * l ≤ l ^ 2 * X ^ 2 + Y ^ 2 := by
    have h'' : 2 * (l * |X|) * |Y| = 2 * (|X| * |Y|) * l := by ring
    linarith [h, h']
  have h5' : (1 / l) * Y ^ 2 * l = Y ^ 2 := by
    rw [one_div, mul_assoc, mul_comm (Y ^ 2) l, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hl),
      one_mul]
  have h5 : (l * X ^ 2 + (1 / l) * Y ^ 2) * l = l ^ 2 * X ^ 2 + Y ^ 2 := by
    rw [add_mul, h5']
    ring
  have h4 : 2 * (|X| * |Y|) * l ≤ (l * X ^ 2 + (1 / l) * Y ^ 2) * l := by
    rw [h5]
    exact h3
  exact le_of_mul_le_mul_right h4 hl

/-- Weighted AM–GM with two prescribed coefficients: `2|XY| ≤ l·X² + m·Y²` when `l > 0`,
`m > 0` and `l·m = 1`. -/
theorem radFar_amgm {l m X Y : ℝ} (hl : 0 < l) (hm : 0 < m) (hlm : l * m = 1) :
    2 * |X * Y| ≤ l * X ^ 2 + m * Y ^ 2 := by
  have h := radFar_two_mul_abs_mul_le_inv hl (X := X) (Y := Y)
  have h1l : 1 / l = m := by
    rw [div_eq_iff (ne_of_gt hl), mul_comm]
    exact hlm.symm
  rwa [h1l] at h



/-- Measurability of `z ↦ w z ^ 2` on `(1,∞)`. -/
theorem radFar_aestronglyMeasurable_w_sq :
    AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      (volume.restrict (Set.Ioi 1)) := by
  refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
  refine (ContinuousOn.div ?_ ?_ ?_).pow 2
  · exact ((continuous_const.add continuous_id).pow 2).continuousOn
  · exact (continuous_id.pow 2).continuousOn
  · intro z hz
    exact pow_ne_zero 2 (ne_of_gt (lt_trans one_pos (Set.mem_Ioi.mp hz)))

/-- The weight on `(1,∞)` is bounded by `16`. -/
theorem radFar_ae_norm_w_sq_le :
    ∀ᵐ z ∂(volume.restrict (Set.Ioi 1)),
      ‖(fun z : ℝ => (Work.Spaces.w z) ^ 2) z‖ ≤ 16 := by
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine ae_of_all _ fun z hz => ?_
  have hz1 : (1 : ℝ) ≤ z := le_of_lt hz
  have h0 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  rw [Real.norm_of_nonneg h0]
  exact Work.FTS.EllExist.Honesty.w_sq_le_sixteen_of_one_le hz1

/-- Multiplying an integrable function on `(1,∞)` by the bounded weight `w²` keeps it integrable. -/
theorem radFar_integrableOn_mul_w_sq {g : ℝ → ℝ}
    (hg : MeasureTheory.IntegrableOn g (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn (fun z : ℝ => g z * (Work.Spaces.w z) ^ 2) (Set.Ioi 1) :=
  (Integrable.bdd_mul hg radFar_aestronglyMeasurable_w_sq radFar_ae_norm_w_sq_le).congr
    (ae_of_all _ fun z => by ring)

/-- **Uniform interval bounds on `(1,∞)` give integrability**: for a nonnegative continuous `f` on
`(0,∞)` with `∫_1^y f ≤ T` for every `y > 1`, the function `f` is integrable on `(1,∞)`. -/
theorem radFar_integrableOn_Ioi_one_of_sq_interval_bound {f : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hfnn : ∀ z : ℝ, 0 ≤ f z)
    (hcont : ContinuousOn f (Set.Ioi 0))
    (hb : ∀ y : ℝ, 1 < y → (∫ z in (1 : ℝ)..y, f z) ≤ T) :
    MeasureTheory.IntegrableOn f (Set.Ioi 1) := by
  refine (integrableOn_Ioi_one_of_interval_bounds (f := f) (T := T) ?_ ?_ ?_).1
  · intro z hz
    exact hfnn z
  · intro i
    have hsub : Set.Icc (1 : ℝ) ((i : ℝ) + 1) ⊆ Set.Ioi (0 : ℝ) := by
      intro z hz
      have hz1 : (1 : ℝ) ≤ z := hz.1
      show (0 : ℝ) < z
      linarith
    exact ((hcont.mono hsub).integrableOn_compact isCompact_Icc).mono_set
      Set.Ioc_subset_Icc_self
  · intro i
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · subst h0
      have hempty : Set.Ioc (1 : ℝ) (((0 : ℕ) : ℝ) + 1) = ∅ := by
        rw [Set.Ioc_eq_empty_iff]
        norm_num
      rw [hempty]
      rw [MeasureTheory.setIntegral_empty]
      exact hT
    · have hpos : (0 : ℝ) < (i : ℝ) := by exact_mod_cast h0
      have hle : (1 : ℝ) < (i : ℝ) + 1 := by linarith
      rw [← intervalIntegral.integral_of_le hle.le]
      exact hb _ hle

/-- The energy identity for a solution of `z A' = s·A + d`: `(z·A²)' = (1 + 2s)·A² + 2d·A`. -/
theorem radFar_hasDerivAt_mul_sq {A : ℝ → ℝ} {s : ℝ} {d : ℝ → ℝ}
    (h : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt A ((s * A z + d z) / z) z) :
    ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun y : ℝ => y * (A y) ^ 2)
      ((1 + 2 * s) * (A z) ^ 2 + 2 * d z * A z) z := by
  intro z hz
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hd := h z hz
  have hprod : HasDerivAt (fun y : ℝ => y * (A y) ^ 2)
      (1 * (A z) ^ 2 + z * (2 * (A z) * ((s * A z + d z) / z))) z := by
    have hh := (hasDerivAt_id z).mul (hd.pow 2)
    have hfun : (fun y : ℝ => y * (A y) ^ 2) = (id * A ^ 2 : ℝ → ℝ) := by
      funext y
      simp only [Pi.mul_apply, Pi.pow_apply, id_eq]
    refine (hh.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq hfun)).congr_deriv ?_
    simp only [Pi.pow_apply, id_eq]
    ring
  refine hprod.congr_deriv ?_
  field_simp
  ring

end Work.FTS.PhiStar.Honesty
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.DiffAux.MainSetup =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.DiffAux

open Work.FTS.StrongEps (Quad zShift thShift Jker Jeps sin_two_pos)

set_option autoImplicit false
set_option maxHeartbeats 4000000

variable {ρ : ℝ × ℝ → ℝ} {ε c δ : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}

/-! ## The two auxiliary measures -/

/-- The measure on the profile variables `(z,θ)`. -/
abbrev μX : Measure (ℝ × ℝ) := (volume.restrict Work.Spaces.Iz).prod
  (volume.restrict Work.Spaces.Iθ)

/-- The measure on the shift variables `(p,t)`. -/
abbrev μY : Measure ((ℝ × ℝ) × ℝ) := volume.prod (volume.restrict (Set.Icc (0 : ℝ) 1))

theorem lintegral_μX_eq {G : ℝ × ℝ → ℝ≥0∞}
    (hG : AEMeasurable G ((volume.prod volume).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))) :
    (lintegral μX (fun x => G x)) = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, G (z, θ) := by
  have hμ : μX = (volume.prod volume).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Measure.prod_restrict (μ := volume) (ν := volume) (s := Work.Spaces.Iz)
      (t := Work.Spaces.Iθ)
  rw [hμ]
  exact MeasureTheory.setLIntegral_prod (fun x : ℝ × ℝ => G x) hG

theorem lintegral_μY_eq {G : (ℝ × ℝ) × ℝ → ℝ≥0∞}
    (hG : AEMeasurable G ((volume.prod volume).restrict (Set.univ ×ˢ Set.Icc (0 : ℝ) 1))) :
    (lintegral μY (fun y => G y)) = ∫⁻ p : ℝ × ℝ, ∫⁻ t in Set.Icc (0 : ℝ) 1, G (p, t) := by
  have hμ : μY = (volume.prod volume).restrict (Set.univ ×ˢ Set.Icc (0 : ℝ) 1) := by
    show volume.prod (volume.restrict (Set.Icc (0 : ℝ) 1)) = _
    rw [← Measure.prod_restrict (μ := volume) (ν := volume) (s := Set.univ)
      (t := Set.Icc (0 : ℝ) 1), Measure.restrict_univ]
  rw [hμ]
  simpa only [Measure.restrict_univ] using
    (MeasureTheory.setLIntegral_prod (fun y : (ℝ × ℝ) × ℝ => G y) hG)

/-- The "iterated to product" conversion for the shift variables. -/
theorem lintegral_iterated_eq_prodY {F : ℝ × ℝ → ℝ → ℝ≥0∞}
    (hF : AEMeasurable (fun y : (ℝ × ℝ) × ℝ => F y.1 y.2) μY) :
    (∫⁻ p : ℝ × ℝ, ∫⁻ t in Set.Icc (0 : ℝ) 1, F p t) = lintegral μY (fun y => F y.1 y.2) := by
  rw [← lintegral_μY_eq (G := fun y => F y.1 y.2) (by
    rw [← Measure.prod_restrict (μ := volume) (ν := volume) (s := Set.univ)
      (t := Set.Icc (0 : ℝ) 1), Measure.restrict_univ]
    exact hF)]

/-! ## Bookkeeping lemmas -/

/-- A finite sum of `lintegral`s is at most the `lintegral` of the sum.  (No measurability
hypothesis: this is the inequality direction supplied by `le_lintegral_add`.) -/
theorem lintegral_finsetSum_le {ι : Type*} {γ : Type*} [MeasurableSpace γ] (μ : Measure γ)
    (s : Finset ι) (F : ι → γ → ℝ≥0∞) :
    (∑ i ∈ s, ∫⁻ x, F i x ∂μ) ≤ ∫⁻ x, ∑ i ∈ s, F i x ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    have h1 : (∑ i ∈ insert a s, ∫⁻ x, F i x ∂μ)
        = ∫⁻ x, F a x ∂μ + ∑ i ∈ s, ∫⁻ x, F i x ∂μ := by
      rw [Finset.sum_insert has]
    have h2 : (∫⁻ x, ∑ i ∈ insert a s, F i x ∂μ)
        = ∫⁻ x, (F a x + ∑ i ∈ s, F i x) ∂μ := by
      congr 1
      funext x
      rw [Finset.sum_insert has]
    rw [h1, h2]
    exact (add_le_add le_rfl ih).trans
      (MeasureTheory.le_lintegral_add (μ := μ) (F a) (fun x => ∑ i ∈ s, F i x))

/-- `ofReal` of an integral is at most the `lintegral` of `ofReal`. -/
theorem ofReal_integral_le_lintegral {γ : Type*} [MeasurableSpace γ] (μ : Measure γ)
    {F : γ → ℝ} (hnn : ∀ x, 0 ≤ F x) :
    ENNReal.ofReal (∫ x, F x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (F x) ∂μ := by
  by_cases h : Integrable F μ
  · rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal h (Eventually.of_forall hnn)]
  · rw [MeasureTheory.integral_undef h, ENNReal.ofReal_zero]
    exact bot_le

/-- Continuity of a finite sum of continuous functions. -/
theorem continuousOn_finsetSum {ι : Type*} (s : Finset ι) {F : ι → ℝ × ℝ → ℝ}
    {t : Set (ℝ × ℝ)} (h : ∀ i ∈ s, ContinuousOn (F i) t) :
    ContinuousOn (fun x => ∑ i ∈ s, F i x) t := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using continuousOn_const
  | insert a s has ih =>
    have h1 : ContinuousOn (F a) t := h a (Finset.mem_insert_self a s)
    have h2 : ContinuousOn (fun x => ∑ i ∈ s, F i x) t :=
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    refine (h1.add h2).congr fun x _ => ?_
    simp only [Pi.add_apply, Finset.sum_insert has]

/-! ## Continuity on the quadrant -/

theorem continuousOn_w : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.w q.1) Quad := by
  have h1 : ContinuousOn (fun q : ℝ × ℝ => (1 + q.1) ^ 2) Quad :=
    (continuous_const.add continuous_fst).continuousOn.pow 2
  have h2 : ContinuousOn (fun q : ℝ × ℝ => q.1 ^ 2) Quad :=
    continuous_fst.continuousOn.pow 2
  exact h1.div h2 fun q hq => pow_ne_zero 2 (ne_of_gt hq.1)

theorem continuousOn_wE : ContinuousOn (fun q : ℝ × ℝ => wE q.1 q.2) Quad := by
  have h2 : ContinuousOn (fun q : ℝ × ℝ =>
      (Real.sin (2 * q.2)) ^ (Work.Spaces.eta / 2)) Quad :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn.rpow_const
      (fun q hq => Or.inl (ne_of_gt (sin_two_pos hq.2)))
  exact (continuousOn_w).div h2 fun q hq =>
    ne_of_gt (Real.rpow_pos_of_pos (sin_two_pos hq.2) _)

theorem continuousOn_wTheta {α : ℝ} : ContinuousOn (fun q : ℝ × ℝ =>
    (Real.sin (2 * q.2)) ^ (-(Work.Spaces.gam α / 2))) Quad :=
  (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn.rpow_const
    (fun q hq => Or.inl (ne_of_gt (sin_two_pos hq.2)))

theorem continuousOn_Wt {α : ℝ} :
    ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.Wt α q.1 q.2) Quad := by
  have h := continuousOn_w.mul (continuousOn_wTheta (α := α))
  refine h.congr fun q _ => ?_
  simp only [Pi.mul_apply, Work.Spaces.Wt, Work.Spaces.wTheta]

theorem continuousOn_DzIter (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad)
    (m : ℕ) : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.DzIter m f q.1 q.2) Quad := by
  simpa only [Work.Spaces.mixed_zero_right] using HkSqAux.continuousOn_mixed_Quad hf m 0

theorem continuousOn_mixed (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad)
    (j i : ℕ) : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.mixed j i f q.1 q.2) Quad :=
  HkSqAux.continuousOn_mixed_Quad hf j i

/-- The level-`k` shadow is continuous on the open quadrant. -/
theorem continuousOn_shadow {α : ℝ} (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) :
    ContinuousOn (fun q : ℝ × ℝ => shadow α k f q.1 q.2) Quad := by
  have h : ContinuousOn (fun q : ℝ × ℝ =>
      (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter (i + 1) f q.1 q.2 * wE q.1 q.2) ^ 2)
        + 1 / 4 * (∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.mixed i 1 f q.1 q.2 * Work.Spaces.Wt α q.1 q.2) ^ 2)
        + (∑ q' ∈ slots k,
            (Work.Spaces.mixed (q'.2 + 1) q'.1 f q.1 q.2 * Work.Spaces.Wt α q.1 q.2) ^ 2)
        + 1 / 4 * (∑ q' ∈ slots k,
            (Work.Spaces.mixed q'.2 (q'.1 + 1) f q.1 q.2 * Work.Spaces.Wt α q.1 q.2) ^ 2)) Quad := by
    refine ContinuousOn.add (ContinuousOn.add (ContinuousOn.add ?_ ?_) ?_) ?_
    · exact continuousOn_finsetSum _ fun i _ =>
        ((continuousOn_DzIter hf (i + 1)).mul continuousOn_wE).pow 2
    · exact (continuousOn_finsetSum _ fun i _ =>
        ((continuousOn_mixed hf i 1).mul continuousOn_Wt).pow 2).const_mul _
    · exact continuousOn_finsetSum _ fun q _ =>
        ((continuousOn_mixed hf (q.2 + 1) q.1).mul continuousOn_Wt).pow 2
    · exact (continuousOn_finsetSum _ fun q _ =>
        ((continuousOn_mixed hf q.2 (q.1 + 1)).mul continuousOn_Wt).pow 2).const_mul _
  simpa only [shadow] using h

/-! ## Measurability in the shift variables -/

theorem shift_mem_Quad {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (y : (ℝ × ℝ) × ℝ) :
    (zShift z (y.2 * y.1.1), thShift θ (y.2 * y.1.2)) ∈ Quad :=
  ⟨zShift_pos hz, thShift_mem hθ⟩

/-- A function continuous on the quadrant, composed with the shift, is continuous on the support
of the kernel. -/
theorem continuousOn_shift_comp {A : ℝ → ℝ → ℝ}
    (hA : ContinuousOn (fun q : ℝ × ℝ => A q.1 q.2) Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ContinuousOn (fun y : (ℝ × ℝ) × ℝ => A (zShift z (y.2 * y.1.1))
      (thShift θ (y.2 * y.1.2))) (Metric.closedBall (0 : ℝ × ℝ) ε ×ˢ Set.univ) := by
  have hg : ContinuousOn (fun y : (ℝ × ℝ) × ℝ =>
      (zShift z (y.2 * y.1.1), thShift θ (y.2 * y.1.2)))
      (Metric.closedBall (0 : ℝ × ℝ) ε ×ˢ Set.univ) := by
    refine ContinuousOn.prodMk ?_ ?_
    · show ContinuousOn (fun y : (ℝ × ℝ) × ℝ => z * Real.exp (-(y.2 * y.1.1))) _
      fun_prop
    · show ContinuousOn (fun y : (ℝ × ℝ) × ℝ =>
        Real.arctan (Real.tan θ * Real.exp (-(y.2 * y.1.2)))) _
      fun_prop
  exact hA.comp hg (fun y _ => shift_mem_Quad hz hθ y)

/-- The composition of a function continuous on the quadrant with the shift is a.e. measurable
for the shift measure `μY`. -/
theorem aemeasurable_μY_comp {A : ℝ → ℝ → ℝ}
    (hρ : IsMollKernel ρ) (hε : 0 < ε)
    (hA : ContinuousOn (fun q : ℝ × ℝ => A q.1 q.2) Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    AEMeasurable (fun y : (ℝ × ℝ) × ℝ => ENNReal.ofReal (Jker ρ ε y.1)
      * ENNReal.ofReal (A (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2)))) μY := by
  set K : Set ((ℝ × ℝ) × ℝ) := Metric.closedBall (0 : ℝ × ℝ) ε ×ˢ Set.univ with hK
  have hKmeas : MeasurableSet K := (Metric.isClosed_closedBall.prod isClosed_univ).measurableSet
  have hKae : AEMeasurable (fun y : (ℝ × ℝ) × ℝ =>
      ENNReal.ofReal (Jker ρ ε y.1)) (μY.restrict K) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (((Jker_continuous hρ ε).measurable.comp measurable_fst).aemeasurable)
  have hAae : AEMeasurable (fun y : (ℝ × ℝ) × ℝ => ENNReal.ofReal
      (A (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2)))) (μY.restrict K) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (((continuousOn_shift_comp (ε := ε) hA hz hθ).aemeasurable hKmeas))
  have hΦae : AEMeasurable (fun y : (ℝ × ℝ) × ℝ => ENNReal.ofReal (Jker ρ ε y.1)
      * ENNReal.ofReal (A (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))))
      (μY.restrict K) := hKae.mul hAae
  have hind := (aemeasurable_indicator_iff hKmeas).mpr hΦae
  have hEq : K.indicator (fun y : (ℝ × ℝ) × ℝ => ENNReal.ofReal (Jker ρ ε y.1)
      * ENNReal.ofReal (A (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))))
      = fun y : (ℝ × ℝ) × ℝ => ENNReal.ofReal (Jker ρ ε y.1)
      * ENNReal.ofReal (A (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))) := by
    funext y
    by_cases hy : y ∈ K
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy]
      have hnotmem : y.1 ∉ Metric.closedBall (0 : ℝ × ℝ) ε := fun h => hy ⟨h, trivial⟩
      rw [Jker_eq_zero_of_not_mem hρ hε hnotmem, ENNReal.ofReal_zero, zero_mul]
  rw [hEq] at hind
  exact hind

/-- The bracket form of the shift measurability. -/
theorem aemeasurable_μY_bracket {g W : ℝ → ℝ → ℝ}
    (hρ : IsMollKernel ρ) (hε : 0 < ε)
    (hWc : ContinuousOn (fun q : ℝ × ℝ => W q.1 q.2) Quad)
    (hDz : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.Dz g q.1 q.2) Quad)
    (hDth : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.Dth g q.1 q.2) Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    AEMeasurable (fun y : (ℝ × ℝ) × ℝ => ENNReal.ofReal (Jker ρ ε y.1)
      * ENNReal.ofReal (bracket g W z θ y.1 y.2)) μY := by
  have hA : ContinuousOn (fun q : ℝ × ℝ =>
      (W q.1 q.2 * Work.Spaces.Dz g q.1 q.2) ^ 2
        + 1 / 4 * (W q.1 q.2 * Work.Spaces.Dth g q.1 q.2) ^ 2) Quad :=
    ((hWc.mul hDz).pow 2).add (((hWc.mul hDth).pow 2).const_mul _)
  exact aemeasurable_μY_comp (A := fun u v =>
    (W u v * Work.Spaces.Dz g u v) ^ 2 + 1 / 4 * (W u v * Work.Spaces.Dth g u v) ^ 2)
    hρ hε hA hz hθ

/-- The pointwise difference estimate, in the `μY` form. -/
theorem slot_ofReal_le {g W : ℝ → ℝ → ℝ}
    (hρ : IsMollKernel ρ) (hε : 0 < ε) (hc : 0 ≤ c)
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Quad)
    (hWc : ContinuousOn (fun q : ℝ × ℝ => W q.1 q.2) Quad)
    (hDz : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.Dz g q.1 q.2) Quad)
    (hDth : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.Dth g q.1 q.2) Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hWnn : 0 ≤ W z θ)
    (hW : ∀ q : ℝ × ℝ, W z θ ≤ Real.exp (c * (|q.1| + |q.2|)) * W (zShift z q.1) (thShift θ q.2)) :
    ENNReal.ofReal ((W z θ * (Jeps ρ ε g z θ - g z θ)) ^ 2)
      ≤ ENNReal.ofReal (2 * ε ^ 2 * Real.exp (4 * c * ε))
        * lintegral μY (fun y => ENNReal.ofReal (Jker ρ ε y.1)
            * ENNReal.ofReal (bracket g W z θ y.1 y.2)) := by
  have h := ofReal_Jeps_sub_sq_le (ρ := ρ) (ε := ε) (g := g) (W := W) hρ hε hc hg hWc hDz hDth
    hz hθ hWnn hW
  have hconv : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p)
        * ∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (bracket g W z θ p t))
      = ∫⁻ p : ℝ × ℝ, ∫⁻ t in Set.Icc (0 : ℝ) 1,
          ENNReal.ofReal (Jker ρ ε p) * ENNReal.ofReal (bracket g W z θ p t) := by
    refine lintegral_congr fun p => ?_
    rw [← MeasureTheory.lintegral_const_mul' (ENNReal.ofReal (Jker ρ ε p)) _
      ENNReal.ofReal_ne_top]
  rw [hconv, lintegral_iterated_eq_prodY
    (aemeasurable_μY_bracket hρ hε hWc hDz hDth hz hθ)] at h
  exact h

/-! ## Measurability in the profile variables, and Tonelli -/

theorem measure_quad_compl : μX (Quadᶜ) = 0 := by
  have hsub : Quadᶜ ⊆ (Set.Ioi (0 : ℝ))ᶜ ×ˢ (Set.univ : Set ℝ) ∪
      (Set.univ : Set ℝ) ×ˢ (Set.Ioo (0 : ℝ) (π / 2))ᶜ := by
    intro x hx
    simp only [Quad, Set.mem_compl_iff, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo, not_and,
      Set.mem_union, Set.mem_univ, and_true, true_and] at hx ⊢
    tauto
  have hIz : (volume.restrict Work.Spaces.Iz) (Set.Ioi (0 : ℝ))ᶜ = 0 := by
    rw [Measure.restrict_apply measurableSet_Ioi.compl]
    refine measure_mono_null ?_ (measure_singleton (0 : ℝ))
    intro x hx
    simp only [Work.Spaces.Iz, Set.mem_inter_iff, Set.mem_Ici, Set.mem_compl_iff,
      Set.mem_Ioi, Set.mem_singleton_iff] at hx ⊢
    exact le_antisymm (not_lt.mp hx.1) hx.2
  have hIθ : (volume.restrict Work.Spaces.Iθ) (Set.Ioo (0 : ℝ) (π / 2))ᶜ = 0 := by
    rw [Measure.restrict_apply measurableSet_Ioo.compl]
    refine measure_mono_null ?_ (measure_union_null (measure_singleton 0)
      (measure_singleton (π / 2)))
    intro x hx
    simp only [Work.Spaces.Iθ, Set.mem_inter_iff, Set.mem_Icc, Set.mem_compl_iff,
      Set.mem_Ioo, Set.mem_union, Set.mem_singleton_iff] at hx ⊢
    obtain ⟨hxn, hxI⟩ := hx
    rcases lt_or_ge (0 : ℝ) x with h | h
    · rcases lt_or_ge x (π / 2) with h2 | h2
      · exact absurd ⟨h, h2⟩ hxn
      · exact Or.inr (le_antisymm hxI.2 h2)
    · exact Or.inl (le_antisymm h hxI.1)
  have h1 : μX ((Set.Ioi (0 : ℝ))ᶜ ×ˢ (Set.univ : Set ℝ) ∪
      (Set.univ : Set ℝ) ×ˢ (Set.Ioo (0 : ℝ) (π / 2))ᶜ) = 0 := by
    rw [measure_union_null_iff]
    refine ⟨?_, ?_⟩
    · rw [μX, Measure.prod_prod, hIz, zero_mul]
    · rw [μX, Measure.prod_prod, hIθ, mul_zero]
  exact measure_mono_null hsub h1

theorem measure_quad_compl_pair : (μX.prod μY) {q : (ℝ × ℝ) × ((ℝ × ℝ) × ℝ) | q.1 ∈ Quad}ᶜ = 0 := by
  have hset : {q : (ℝ × ℝ) × ((ℝ × ℝ) × ℝ) | q.1 ∈ Quad}ᶜ
      = Quadᶜ ×ˢ (Set.univ : Set ((ℝ × ℝ) × ℝ)) := by
    ext q
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, and_true]
  rw [hset, Measure.prod_prod, measure_quad_compl, zero_mul]

/-- The shadow, composed with the shift in the profile variables, is measurable for `μX` (for
every fixed shift variable). -/
theorem aemeasurable_μX_comp {A : ℝ → ℝ → ℝ}
    (hA : ContinuousOn (fun q : ℝ × ℝ => A q.1 q.2) Quad) (y : (ℝ × ℝ) × ℝ) :
    AEMeasurable (fun x : ℝ × ℝ =>
      ENNReal.ofReal (A (zShift x.1 (y.2 * y.1.1)) (thShift x.2 (y.2 * y.1.2)))) μX := by
  have hcont : ContinuousOn (fun x : ℝ × ℝ =>
      A (zShift x.1 (y.2 * y.1.1)) (thShift x.2 (y.2 * y.1.2))) Quad := by
    have hg : ContinuousOn (fun x : ℝ × ℝ =>
        (zShift x.1 (y.2 * y.1.1), thShift x.2 (y.2 * y.1.2))) Quad := by
      refine ContinuousOn.prodMk ?_ ?_
      · show ContinuousOn (fun x : ℝ × ℝ => x.1 * Real.exp (-(y.2 * y.1.1))) Quad
        fun_prop
      · show ContinuousOn (fun x : ℝ × ℝ =>
          Real.arctan (Real.tan x.2 * Real.exp (-(y.2 * y.1.2)))) Quad
        refine Real.continuous_arctan.comp_continuousOn ?_
        refine ContinuousOn.mul ?_ (Real.continuous_exp.comp_continuousOn (by fun_prop))
        exact Real.continuousOn_tan.comp continuousOn_snd
          (fun x hx => (Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.2.1, Real.pi_pos],
            hx.2.2⟩).ne')
    exact hA.comp hg (fun x hx => ⟨zShift_pos hx.1, thShift_mem hx.2⟩)
  have hQae : Quad =ᵐ[μX] Set.univ := by
    filter_upwards [compl_mem_ae_iff.mpr measure_quad_compl] with x hx
    refine propext ⟨fun _ => trivial, fun _ => ?_⟩
    simpa only [Set.mem_compl_iff, not_not] using hx
  have heq : μX = μX.restrict Quad :=
    ((Measure.restrict_congr_set hQae).trans Measure.restrict_univ).symm
  rw [heq]
  exact (ENNReal.continuous_ofReal.comp_continuousOn hcont).aemeasurable
    isOpen_Quad.measurableSet

/-- The joint measurability needed for Tonelli's theorem. -/
theorem aemeasurable_pair_comp {A : ℝ → ℝ → ℝ}
    (hρ : IsMollKernel ρ) (hε : 0 < ε)
    (hA : ContinuousOn (fun q : ℝ × ℝ => A q.1 q.2) Quad) :
    AEMeasurable (fun q : (ℝ × ℝ) × ((ℝ × ℝ) × ℝ) => ENNReal.ofReal (Jker ρ ε q.2.1)
      * ENNReal.ofReal (A (zShift q.1.1 (q.2.2 * q.2.1.1))
          (thShift q.1.2 (q.2.2 * q.2.1.2)))) (μX.prod μY) := by
  set S : Set ((ℝ × ℝ) × ((ℝ × ℝ) × ℝ)) := {q | q.1 ∈ Quad} with hS
  have hSmeas : MeasurableSet S := (isOpen_Quad.preimage continuous_fst).measurableSet
  have hshift : ContinuousOn (fun q : (ℝ × ℝ) × ((ℝ × ℝ) × ℝ) =>
      (zShift q.1.1 (q.2.2 * q.2.1.1), thShift q.1.2 (q.2.2 * q.2.1.2))) S := by
    refine ContinuousOn.prodMk ?_ ?_
    · show ContinuousOn (fun q : (ℝ × ℝ) × ((ℝ × ℝ) × ℝ) =>
        q.1.1 * Real.exp (-(q.2.2 * q.2.1.1))) S
      fun_prop
    · show ContinuousOn (fun q : (ℝ × ℝ) × ((ℝ × ℝ) × ℝ) =>
        Real.arctan (Real.tan q.1.2 * Real.exp (-(q.2.2 * q.2.1.2)))) S
      refine Real.continuous_arctan.comp_continuousOn ?_
      refine ContinuousOn.mul ?_ (Real.continuous_exp.comp_continuousOn (by fun_prop))
      exact Real.continuousOn_tan.comp continuousOn_fst.snd
        (fun q hq => (Real.cos_pos_of_mem_Ioo ⟨by linarith [hq.2.1, Real.pi_pos],
          hq.2.2⟩).ne')
  have hAsm : ContinuousOn (fun q : (ℝ × ℝ) × ((ℝ × ℝ) × ℝ) =>
      A (zShift q.1.1 (q.2.2 * q.2.1.1)) (thShift q.1.2 (q.2.2 * q.2.1.2))) S :=
    hA.comp hshift (fun q hq => ⟨zShift_pos hq.1, thShift_mem hq.2⟩)
  have h1 : AEMeasurable (fun q : (ℝ × ℝ) × ((ℝ × ℝ) × ℝ) =>
      ENNReal.ofReal (Jker ρ ε q.2.1)) ((μX.prod μY).restrict S) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (((Jker_continuous hρ ε).measurable.comp measurable_snd.fst).aemeasurable)
  have h2 : AEMeasurable (fun q : (ℝ × ℝ) × ((ℝ × ℝ) × ℝ) =>
      ENNReal.ofReal (A (zShift q.1.1 (q.2.2 * q.2.1.1))
        (thShift q.1.2 (q.2.2 * q.2.1.2)))) ((μX.prod μY).restrict S) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hAsm.aemeasurable hSmeas)
  have hAe : AEMeasurable (fun q : (ℝ × ℝ) × ((ℝ × ℝ) × ℝ) =>
      ENNReal.ofReal (Jker ρ ε q.2.1)
      * ENNReal.ofReal (A (zShift q.1.1 (q.2.2 * q.2.1.1))
          (thShift q.1.2 (q.2.2 * q.2.1.2)))) ((μX.prod μY).restrict S) := h1.mul h2
  have hSae : S =ᵐ[μX.prod μY] Set.univ := by
    filter_upwards [compl_mem_ae_iff.mpr measure_quad_compl_pair] with q hq
    refine propext ⟨fun _ => trivial, fun _ => ?_⟩
    rw [hS]
    simpa only [Set.mem_compl_iff, not_not, Set.mem_ofPred_eq] using hq
  have hcongr : μX.prod μY = (μX.prod μY).restrict S :=
    ((Measure.restrict_congr_set hSae).trans Measure.restrict_univ).symm
  rw [hcongr]
  exact hAe

/-- **Tonelli's theorem for the difference estimate.** -/
theorem lintegral_swap4 {F : ℝ × ℝ → (ℝ × ℝ) × ℝ → ℝ≥0∞}
    (hF : AEMeasurable (fun q : (ℝ × ℝ) × ((ℝ × ℝ) × ℝ) => F q.1 q.2) (μX.prod μY)) :
    (lintegral μX (fun x => lintegral μY (fun y => F x y))) =
      lintegral μY (fun y => lintegral μX (fun x => F x y)) :=
  MeasureTheory.lintegral_lintegral_swap hF


end Work.FTS.StrongEps.DiffAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Work.epsUniformMem_Jeps_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Work

open Work.FTS.Galerkin (Fn Fam slice)


end Work.FTS.StrongEps.EpsE4Work
end
-- ===== merged: Submission.Work.FTS.StrongEps.Gdot =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice dynLin dynRHS gdot)

set_option autoImplicit false








end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.GlueParts.Box =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.GlueParts

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

open Work.FTS.StrongGlobal (P3 concat uncurry3)

/-! ## Boxes, and unique differentiability of the closed fake-time intervals -/






/-- The closed interval `Icc a b` (`a < b`) is a set of unique differentiability at each of its
points. -/
theorem uniqueDiffWithinAt_Icc {a b x : ℝ} (hab : a < b) (hx : x ∈ Set.Icc a b) :
    UniqueDiffWithinAt ℝ (Set.Icc a b) x :=
  uniqueDiffWithinAt_convex (convex_Icc a b) ⟨(a + b) / 2, by
    rw [interior_Icc]; exact ⟨by linarith, by linarith⟩⟩ (subset_closure hx)




end Work.FTS.StrongEps.GlueParts
end
-- ===== merged: Submission.Work.FTS.StrongEps.GlueParts.FirstStep =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.unusedVariables false

namespace Work.FTS.StrongEps.GlueParts


end Work.FTS.StrongEps.GlueParts
end
-- ===== merged: Submission.Work.FTS.StrongEps.GlueParts.Induction =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

open Work.FTS.StrongGlobal (P3 Xn6 concat)


end Work.FTS.StrongEps
end
-- ===== merged: Submission.Work.FTS.StrongEps.GlueParts.JunctionDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.GlueParts

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

open Work.FTS.StrongGlobal (P3 concat uncurry3)

/-! ## The pieces of the fake-time axis -/

/-- The target piece `[0, t+δ]` over the open quadrant. -/
def AT (t δ : ℝ) : Set P3 := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 (t + δ)

/-- The piece `[0,t]` over the open quadrant. -/
def AG (t : ℝ) : Set P3 := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 t


/-- The piece `[t,t+δ]` over the open quadrant. -/
def BT (t δ : ℝ) : Set P3 := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc t (t + δ)






end Work.FTS.StrongEps.GlueParts
end
-- ===== merged: Submission.Work.FTS.StrongEps.GlueParts.SolGlue =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.GlueParts

open scoped Real Topology
open Set Filter

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Auxiliary facts -/


/-- Differentiation of a shifted function: `s ↦ f (s - a)` has the derivative of `f` at `s - a`,
on the shifted interval `[a, a+c]`. -/
theorem hasDerivWithinAt_comp_sub_Icc {f : ℝ → ℝ} {f' : ℝ} {x a c : ℝ}
    (h : HasDerivWithinAt f f' (Set.Icc 0 c) (x - a)) :
    HasDerivWithinAt (fun y : ℝ => f (y - a)) f' (Set.Icc a (a + c)) x := by
  have hg : HasDerivWithinAt (fun y : ℝ => y - a) 1 (Set.Icc a (a + c)) x :=
    ((hasDerivAt_id (x := x)).sub_const a).hasDerivWithinAt
  have hst : MapsTo (fun y : ℝ => y - a) (Set.Icc a (a + c)) (Set.Icc 0 c) :=
    fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hcomp := h.comp x hg hst
  have heq : (f ∘ fun y : ℝ => y - a) = (fun y : ℝ => f (y - a)) := funext fun y => rfl
  rw [heq, mul_one] at hcomp
  exact hcomp





/-! ## The glue -/


end Work.FTS.StrongEps.GlueParts
end
-- ===== merged: Submission.Work.FTS.StrongEps.GlueParts.contDiffOn_shiftFam =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.GlueParts

/-- The fake-time shift `shiftFam H t = fun z θ τ => H z θ (τ - t)` of a jointly `C¹` family on
the slab `τ ∈ [0,δ]` is jointly `C¹` on the shifted slab `τ ∈ [t, t+δ]` (composition with the
affine map `(z,θ,τ) ↦ (z,θ,τ-t)`, via `ContDiffOn.comp`). -/
theorem contDiffOn_shiftFam {H : Work.FTS.Galerkin.Fam} {t δ : ℝ}
    (hH : ContDiffOn ℝ 1 (Work.FTS.StrongGlobal.uncurry3 H)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 δ)) :
    ContDiffOn ℝ 1 (Work.FTS.StrongGlobal.uncurry3 (Work.FTS.StrongEps.shiftFam H t))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc t (t + δ)) := by
  -- The affine reparametrisation `φ (z,θ,τ) = (z,θ,τ-t)`; it maps the shifted slab into the
  -- original one, and `uncurry3 (shiftFam H t) = uncurry3 H ∘ φ`.
  have hφ : ContDiffOn ℝ 1 (fun p : Work.FTS.StrongGlobal.P3 => (p.1, p.2.1, p.2.2 - t))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc t (t + δ)) := by fun_prop
  have hmaps : Set.MapsTo (fun p : Work.FTS.StrongGlobal.P3 => (p.1, p.2.1, p.2.2 - t))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc t (t + δ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 δ) := by
    rintro ⟨z, θ, τ⟩ ⟨hz, hθ, hτ⟩
    simp only [Set.mem_Icc] at hτ
    simp only [Set.mem_Icc, Set.mem_Ioi, Set.mem_Ioo, Set.mem_prod]
    exact ⟨hz, hθ, ⟨by linarith [hτ.1], by linarith [hτ.2]⟩⟩
  exact hH.comp hφ hmaps

end Work.FTS.StrongEps.GlueParts
end
-- ===== merged: Submission.Work.FTS.StrongEps.StepFacts.SlotBounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.StepFacts

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The `z`-routed mixed top slot (`1 ≤ j`, `1 ≤ i`, `i + j = m`). -/
theorem slot_z_le (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) {ε α c z θ : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) {m : ℕ} (hm : 2 ≤ m) {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) Work.FTS.StrongEps.Quad) (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hW : ∀ p : ℝ × ℝ, Work.Spaces.Wt α z θ ≤ Real.exp (c * (|p.1| + |p.2|))
      * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))
    {j i : ℕ} (hj : 1 ≤ j) (hi : 1 ≤ i) (hij : i + j = m) :
    ENNReal.ofReal ((Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε u) z θ
        * Work.Spaces.Wt α z θ) ^ 2)
      ≤ ENNReal.ofReal (Mmax ρ ε) * Jint ρ ε α c u m z θ := by
  have hroute := mixed_Jeps_route_z ρ hρ hε hu hz hθ j i hj
  have hslot := (slot_route_bounds ρ hρ hε hu).1 hz hθ hj hi hroute hW
  have hK : (0 : ℝ) ≤ ∫ p : ℝ × ℝ,
      |deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1| :=
    integral_nonneg fun p => abs_nonneg _
  have hKK : (∫ p : ℝ × ℝ, |deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1|)
      ≤ Mmax ρ ε := by
    have h1 : (∫ p : ℝ × ℝ, |deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1|)
        = M1 ρ ε := by
      rw [M1]
      exact MeasureTheory.integral_congr_ae
        (Eventually.of_forall fun p => (K1_eq_abs_deriv ρ hρ hε p).symm)
    rw [h1]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hF : ∀ p : ℝ × ℝ, 0 ≤
      |deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1|
      * Real.exp (2 * c * (|p.1| + |p.2|))
      * (Work.Spaces.mixed (j - 1) i u (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2)
        * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2)) ^ 2 :=
    fun p => mul_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le) (sq_nonneg _)
  have hF' : ∀ p : ℝ × ℝ, 0 ≤ Psi ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|))
      * Work.Spaces.HkIntegrand α (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2) :=
    fun p => mul_nonneg (mul_nonneg (Psi_nonneg ρ hρ hε p) (Real.exp_pos _).le)
      (Work.Spaces.HkIntegrand_nonneg α (m - 1) u _ _)
  have hFF : ∀ p : ℝ × ℝ,
      |deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1|
      * Real.exp (2 * c * (|p.1| + |p.2|))
      * (Work.Spaces.mixed (j - 1) i u (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2)
        * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2)) ^ 2
      ≤ Psi ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|))
      * Work.Spaces.HkIntegrand α (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2) := by
    intro p
    have h1 : |deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1|
        ≤ Psi ρ ε p :=
      (K1_eq_abs_deriv ρ hρ hε p).ge.trans (K1_le_Psi ρ hρ.moll.nonneg hε p)
    have h2 : (Work.Spaces.mixed (j - 1) i u (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2)
        * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2)) ^ 2
        ≤ Work.Spaces.HkIntegrand α (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2) :=
      Work.Spaces.sq_le_HkIntegrand_mixed α (m - 1) u _ _ i (j - 1) hi (by omega)
    calc |deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1|
          * Real.exp (2 * c * (|p.1| + |p.2|))
          * (Work.Spaces.mixed (j - 1) i u (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2)
            * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2)) ^ 2
        ≤ Psi ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|))
          * (Work.Spaces.mixed (j - 1) i u (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2)
            * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2)) ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le) (sq_nonneg _)
      _ ≤ Psi ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|))
          * Work.Spaces.HkIntegrand α (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2) :=
          mul_le_mul_of_nonneg_left h2
            (mul_nonneg (Psi_nonneg ρ hρ hε p) (Real.exp_pos _).le)
  refine ((ENNReal.ofReal_le_ofReal hslot).trans
    (ofReal_mul_integral_le_lintegral hK (Mmax_nonneg ρ ε) hKK hF hF' hFF)).trans ?_
  exact mul_le_mul_right (lintegral_prod_eq_Jint ρ hρ hε) _

/-- The pure `D_z^m`-slot (the `i = 0` case of the top `z`-slot). -/
theorem zslot_le (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) {ε α c z θ : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) {m : ℕ} (hm : 2 ≤ m) {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) Work.FTS.StrongEps.Quad) (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hW : ∀ p : ℝ × ℝ,
      Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
        ≤ Real.exp (c * (|p.1| + |p.2|))
          * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p.1)
              / (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2))
                ^ (Work.Spaces.eta / 2))) :
    ENNReal.ofReal ((Work.Spaces.DzIter m (Work.FTS.StrongEps.Jeps ρ ε u) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ ENNReal.ofReal (Mmax ρ ε) * Jint ρ ε α c u m z θ := by
  have hcomm : Work.Spaces.DzIter m (Work.FTS.StrongEps.Jeps ρ ε u) z θ
      = ∫ p : ℝ × ℝ, deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1
          * Work.Spaces.DzIter (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2) := by
    have h := mixed_Jeps_route_z ρ hρ hε hu hz hθ m 0 (by omega)
    simpa only [Work.Spaces.mixed_zero_right] using h
  have hslot := (slot_route_bounds ρ hρ hε hu).2.1 hz hθ (j := m) (by omega) hcomm hW
  have hK : (0 : ℝ) ≤ ∫ p : ℝ × ℝ,
      |deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1| :=
    integral_nonneg fun p => abs_nonneg _
  have hKK : (∫ p : ℝ × ℝ, |deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1|)
      ≤ Mmax ρ ε := by
    have h1 : (∫ p : ℝ × ℝ, |deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1|)
        = M1 ρ ε := by
      rw [M1]
      exact MeasureTheory.integral_congr_ae
        (Eventually.of_forall fun p => (K1_eq_abs_deriv ρ hρ hε p).symm)
    rw [h1]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hF : ∀ p : ℝ × ℝ, 0 ≤
      |deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1|
      * Real.exp (2 * c * (|p.1| + |p.2|))
      * (Work.Spaces.DzIter (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2)
        * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p.1)
            / (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2))
              ^ (Work.Spaces.eta / 2))) ^ 2 :=
    fun p => mul_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le) (sq_nonneg _)
  have hF' : ∀ p : ℝ × ℝ, 0 ≤ Psi ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|))
      * Work.Spaces.HkIntegrand α (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2) :=
    fun p => mul_nonneg (mul_nonneg (Psi_nonneg ρ hρ hε p) (Real.exp_pos _).le)
      (Work.Spaces.HkIntegrand_nonneg α (m - 1) u _ _)
  have hFF : ∀ p : ℝ × ℝ,
      |deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1|
      * Real.exp (2 * c * (|p.1| + |p.2|))
      * (Work.Spaces.DzIter (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2)
        * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p.1)
            / (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2))
              ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ Psi ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|))
      * Work.Spaces.HkIntegrand α (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2) := by
    intro p
    have h1 : |deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1|
        ≤ Psi ρ ε p :=
      (K1_eq_abs_deriv ρ hρ hε p).ge.trans (K1_le_Psi ρ hρ.moll.nonneg hε p)
    have h2 : (Work.Spaces.DzIter (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2)
        * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p.1)
            / (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2))
              ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ Work.Spaces.HkIntegrand α (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2) :=
      Work.Spaces.sq_le_HkIntegrand_z α (m - 1) u _ _ (m - 1) le_rfl
    calc |deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1|
          * Real.exp (2 * c * (|p.1| + |p.2|))
          * (Work.Spaces.DzIter (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2)
            * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p.1)
                / (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2))
                  ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ Psi ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|))
          * (Work.Spaces.DzIter (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2)
            * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p.1)
                / (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2))
                  ^ (Work.Spaces.eta / 2))) ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le) (sq_nonneg _)
      _ ≤ Psi ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|))
          * Work.Spaces.HkIntegrand α (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2) :=
          mul_le_mul_of_nonneg_left h2
            (mul_nonneg (Psi_nonneg ρ hρ hε p) (Real.exp_pos _).le)
  refine ((ENNReal.ofReal_le_ofReal hslot).trans
    (ofReal_mul_integral_le_lintegral hK (Mmax_nonneg ρ ε) hKK hF hF' hFF)).trans ?_
  exact mul_le_mul_right (lintegral_prod_eq_Jint ρ hρ hε) _

/-- The `θ`-routed top slot `D_θ^m` (`m ≥ 2`). -/
theorem slot_theta_le (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) {ε α c z θ : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) {m : ℕ} (hm : 2 ≤ m) {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) Work.FTS.StrongEps.Quad) (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hW : ∀ p : ℝ × ℝ, Work.Spaces.Wt α z θ ≤ Real.exp (c * (|p.1| + |p.2|))
      * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) :
    ENNReal.ofReal ((Work.Spaces.DthIter m (Work.FTS.StrongEps.Jeps ρ ε u) z θ
        * Work.Spaces.Wt α z θ) ^ 2)
      ≤ ENNReal.ofReal (Mmax ρ ε) * Jint ρ ε α c u m z θ := by
  have hcomm : Work.Spaces.DthIter m (Work.FTS.StrongEps.Jeps ρ ε u) z θ
      = 2 * ∫ p : ℝ × ℝ, deriv (fun t : ℝ => Work.FTS.StrongEps.Jker ρ ε (p.1, t)) p.2
          * Work.Spaces.DthIter (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2) :=
    DthIter_Jeps_route_theta ρ hρ hε hu hz hθ m (by omega)
  have hslot := (slot_route_bounds ρ hρ hε hu).2.2 hz hθ (i := m) (by omega) hcomm hW
  have hK0 : 0 ≤ (∫ p : ℝ × ℝ,
      |deriv (fun t : ℝ => Work.FTS.StrongEps.Jker ρ ε (p.1, t)) p.2|) :=
    integral_nonneg fun p => abs_nonneg _
  have hK : (0 : ℝ) ≤ 4 * (∫ p : ℝ × ℝ,
      |deriv (fun t : ℝ => Work.FTS.StrongEps.Jker ρ ε (p.1, t)) p.2|) := by
    linarith
  have hKK : 4 * (∫ p : ℝ × ℝ, |deriv (fun t : ℝ => Work.FTS.StrongEps.Jker ρ ε (p.1, t)) p.2|)
      ≤ Mmax ρ ε := by
    have h1 : (∫ p : ℝ × ℝ, |deriv (fun t : ℝ => Work.FTS.StrongEps.Jker ρ ε (p.1, t)) p.2|)
        = M2 ρ ε := by
      rw [M2]
      exact MeasureTheory.integral_congr_ae
        (Eventually.of_forall fun p => (K2_eq_abs_deriv ρ hρ hε p).symm)
    rw [h1]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hF : ∀ p : ℝ × ℝ, 0 ≤
      |deriv (fun t : ℝ => Work.FTS.StrongEps.Jker ρ ε (p.1, t)) p.2|
      * Real.exp (2 * c * (|p.1| + |p.2|))
      * (Work.Spaces.DthIter (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2)
        * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2)) ^ 2 :=
    fun p => mul_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le) (sq_nonneg _)
  have hF' : ∀ p : ℝ × ℝ, 0 ≤ Psi ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|))
      * Work.Spaces.HkIntegrand α (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2) :=
    fun p => mul_nonneg (mul_nonneg (Psi_nonneg ρ hρ hε p) (Real.exp_pos _).le)
      (Work.Spaces.HkIntegrand_nonneg α (m - 1) u _ _)
  have hFF : ∀ p : ℝ × ℝ,
      |deriv (fun t : ℝ => Work.FTS.StrongEps.Jker ρ ε (p.1, t)) p.2|
      * Real.exp (2 * c * (|p.1| + |p.2|))
      * (Work.Spaces.DthIter (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2)
        * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2)) ^ 2
      ≤ Psi ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|))
      * Work.Spaces.HkIntegrand α (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2) := by
    intro p
    have h1 : |deriv (fun t : ℝ => Work.FTS.StrongEps.Jker ρ ε (p.1, t)) p.2|
        ≤ Psi ρ ε p :=
      (K2_eq_abs_deriv ρ hρ hε p).ge.trans (K2_le_Psi ρ hρ.moll.nonneg hε p)
    have h2 : (Work.Spaces.DthIter (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2)
        * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2)) ^ 2
        ≤ Work.Spaces.HkIntegrand α (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2) := by
      have h := Work.Spaces.sq_le_HkIntegrand_mixed α (m - 1) u
        (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
        (m - 1) 0 (by omega) (le_refl (m - 1))
      simpa only [Work.Spaces.mixed_zero_left] using h
    calc |deriv (fun t : ℝ => Work.FTS.StrongEps.Jker ρ ε (p.1, t)) p.2|
          * Real.exp (2 * c * (|p.1| + |p.2|))
          * (Work.Spaces.DthIter (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2)
            * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2)) ^ 2
        ≤ Psi ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|))
          * (Work.Spaces.DthIter (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2)
            * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2)) ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le) (sq_nonneg _)
      _ ≤ Psi ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|))
          * Work.Spaces.HkIntegrand α (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2) :=
          mul_le_mul_of_nonneg_left h2
            (mul_nonneg (Psi_nonneg ρ hρ hε p) (Real.exp_pos _).le)
  refine ((ENNReal.ofReal_le_ofReal hslot).trans
    (ofReal_mul_integral_le_lintegral hK (Mmax_nonneg ρ ε) hKK hF hF' hFF)).trans ?_
  exact mul_le_mul_right (lintegral_prod_eq_Jint ρ hρ hε) _

end Work.FTS.StrongEps.StepFacts
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.StrongEpsP.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.StrongEpsP

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongGlobal (Xn6 concat)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The projected right-hand side is the unprojected one at the projected family -/



/-! ## The projected family is slice-determined -/

/-- `JfamP` depends on a family only through its slice, at possibly different fake times. -/
theorem slice_JfamP_congr {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {W W' : Fam} {τ τ' : ℝ}
    (h : slice W τ = slice W' τ') :
    slice (JfamP ρ ε W) τ = slice (JfamP ρ ε W') τ' := by
  simp only [slice_JfamP]
  rw [h]


/-! ## Slice-determination and junction compatibility of the projected right-hand side -/

/-- The projected profile right-hand side depends on a family only through its slice at the (same
or a different) fake time. -/
theorem epsWP_congr {α : ℝ} {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {Φs : Fn} {E : Fn → Fn}
    {W W' : Fam} {τ τ' : ℝ} (h : slice W τ = slice W' τ') :
    epsWP α ρ ε Φs E W τ = epsWP α ρ ε Φs E W' τ' :=
  epsRHSu_congr (α := α) (ρ := ρ) (ε := ε) (Φs := Φs) (E := E)
    (W := JfamP ρ ε W) (W' := JfamP ρ ε W') (τ := τ) (τ' := τ') (slice_JfamP_congr h)

/-- The projected scheme's right-hand side depends on a family only through its slice. -/
theorem epsRHSP_congr {α : ℝ} {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {Φs : Fn} {E : Fn → Fn}
    {W W' : Fam} {τ τ' : ℝ} (h : slice W τ = slice W' τ') :
    epsRHSP α ρ ε Φs E W τ = epsRHSP α ρ ε Φs E W' τ' := by
  simp only [epsRHSP]
  rw [epsWP_congr (Φs := Φs) (E := E) h]



/-! ## Elementary consequences of the projected scheme -/

/-- A `P₀`-solution on `[0,T']` is one on every shorter interval `[0,T]`. -/
theorem IsEpsSolP.mono {α ε T T' : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {g : Fam} (h : IsEpsSolP α ρ ε T' Φs E g₀ g) (hTT' : T ≤ T') :
    IsEpsSolP α ρ ε T Φs E g₀ g :=
  ⟨h.1, fun z θ τ hz hθ hτ =>
    (h.2 z θ τ hz hθ ⟨hτ.1, hτ.2.trans hTT'⟩).mono fun s hs => ⟨hs.1, hs.2.trans hTT'⟩⟩



/-! ## The slices of the projected mollified concatenation -/







end Work.FTS.StrongEps.StrongEpsP
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.h6pair_N0_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux

theorem h6pair_N0_zero : ∃ K α₂ : ℝ, 0 < K ∧ 0 < α₂ ∧
    ∀ α ∈ Set.Ioc 0 α₂, ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ),
      Work.FTS.StrongPersist.H6Adm α f → Work.Spaces.HkMem α 7 f →
      Work.FTS.Nonlin.Xn α f ≤ M →
      |Work.Construction.L12 (Work.Construction.N0 α
          (fun z θ => Work.Construction.Fstar α z θ + f z θ) f) 0|
        ≤ K * α ^ (-(9 : ℝ)) * (1 + M) ^ 4 := by
  refine h6pair_N0_zero_of_pieces ?_ ?_ ?_
  · intro α g hα hα1 hso hmem
    exact l12_supAbs_open hα hα1 hso hmem
  · intro α g hα hα1 hso hmem
    exact contN0_open hα hα1 hso hmem
  · intro α g hα hα1 hso hL12g
    exact N0_sq_w_open hα hα1 hso hL12g

end Work.FTS.StrongPersist.H6Pair6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.N3ssPriced =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.L3Rhs

open Work.FTS.NonlinRows

/-- **Priced row 19**: the `ℋ⁴`-honesty and the `α³`-bound of the star piece `N₃^{**} = -2α · 𝒱(Φ̃_*) · D_zF_*`, with the constant *uniform* in `Cs` (linear loss in `1 + |Cs|`).

This is the priced form of `Work.FTS.NonlinRows.NRow19T2`: that result states
`∃ K, 0 < K ∧ ∀ …, Ctx2 … → HkMem α 4 (N3ss α Φs) ∧ Xn α (N3ss α Φs) ≤ K * α ^ 3`, where
`Ctx2` = `0 < α ∧ α ≤ 1 ∧ α ≤ α₂ ∧ GalClass α g ∧ StarPkgo2 α Cs Φs ∧ EllPkgGo α Ce g Φg`.
Its proof *constructs* the explicit constant `2 * Cw * CZ19 C2 * max Cs 0 + 1` (`Cw` = constant
of `Work.FTS.NonlinRows.wtoHQ_of_pointwise_open`, `CZ19`, `C2` fixed positive constants of
`Work.FTS.NonlinRows.NRow19T2Parts`), and its body uses nothing but `0 < α`, `α ≤ 1`,
`StarPkgo α Cs Φs` and the two `𝒲^{4,∞}` facts about
`A19 α Φs = ((z+1)/z) · 𝒱(Φ̃_*)` (the field `StarPkgo2.VzW` is exactly
`WlInfMem α 4 (A19 α Φs) ∧ WlInf α 4 (A19 α Φs) ≤ Cs * α`).  So the proof is a copy of that
proof with `g`, `Φg`, `hgal`, `hell` dropped and `C = 2 * Cw * CZ19 C2 + 1`, using
`max Cs 0 ≤ 1 + |Cs|`. -/
theorem N3ssPriced : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ (Cs : ℝ) (Φs : Work.FTS.Galerkin.Fn),
    Work.FTS.VocabO2.StarPkgo2 α Cs Φs →
    Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N3ss α Φs) ∧
    Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N3ss α Φs) ≤ C * (1 + |Cs|) * α ^ 3 := by
  obtain ⟨Cw, hCw, hwto⟩ := Work.FTS.NonlinRows.wtoHQ_of_pointwise_open
  obtain ⟨C2, hC2pos, hC2⟩ := Work.FTS.Nonlinear.Open.Row19Prep.H2b_weight_le
  have hCZpos : 0 < CZ19 C2 := by
    rw [CZ19]
    have h1 : (0 : ℝ) < 10 ^ 20 := by norm_num
    have h2 : (0 : ℝ) < 1 + C2 := by linarith [hC2pos]
    have h3 : (0 : ℝ) < 1 + TB19 := by linarith [TB19_nonneg]
    exact mul_pos (mul_pos h1 h2) h3
  refine ⟨2 * Cw * CZ19 C2 + 1, ?_, ?_⟩
  · have h : (0 : ℝ) < 2 * Cw * CZ19 C2 :=
      mul_pos (mul_pos (by norm_num) hCw) hCZpos
    linarith
  · intro α hαI Cs Φs hs2
    obtain ⟨hα, hα1⟩ := hαI
    have hs : Work.FTS.VocabO.StarPkgo α Cs Φs := hs2.toStarPkgo
    have hAsm : Work.FTS.EllipticEst.SmoothOpen (A19 α Φs) := smoothOpen_A19 hα hα1 hs
    have hAmem : Work.Spaces.WlInfMem α 4 (A19 α Φs) := hs2.VzW.1
    have hAle : Work.Spaces.WlInf α 4 (A19 α Φs) ≤ Cs * α := hs2.VzW.2
    have hL0 : 0 ≤ Work.Spaces.WlInf α 4 (A19 α Φs) := WlInf_nonneg' α 4 _ hAmem
    have hC2nn : 0 ≤ C2 := hC2pos.le
    have hW0 : 0 ≤ CZ19 C2 * α * Work.Spaces.WlInf α 4 (A19 α Φs) :=
      mul_nonneg (mul_nonneg hCZpos.le hα.le) hL0
    have hsm : Work.FTS.EllipticEst.SmoothOpen (Z19 α Φs) := smoothOpen_Z19 hα hα1 hs
    have hmain := hwto α (Z19 α Φs) (CZ19 C2 * α * Work.Spaces.WlInf α 4 (A19 α Φs))
      hα hα1 hW0 hsm (Z19_eta_bound hα hα1 hAsm hAmem hC2 hC2nn)
      (Z19_gam_bound hα hα1 hAsm hAmem hC2 hC2nn)
    have hAG : ∀ z θ : ℝ, 0 < z →
        Work.FTS.Nonlinear.Pieces.RNP.Vs α Φs z θ * Work.FTS.Nonlinear.Pieces.RNP.Gs α z θ
          = Z19 α Φs z θ := fun z θ hz => (Z19_eq_Vs_Gs hα z hz θ).symm
    have hmemZ : Work.Spaces.HkMem α 4 (Z19 α Φs) := hmain.1
    have hmemVG : Work.Spaces.HkMem α 4
        (fun z θ => Work.FTS.Nonlinear.Pieces.RNP.Vs α Φs z θ
          * Work.FTS.Nonlinear.Pieces.RNP.Gs α z θ) :=
      Work.Coercivity.HkMem_congr_Ioi α 4 hmemZ (fun z hz θ _ => (hAG z θ hz).symm)
    have hsqeq : Work.Spaces.HkSq α 4 (fun z θ => Work.FTS.Nonlinear.Pieces.RNP.Vs α Φs z θ
          * Work.FTS.Nonlinear.Pieces.RNP.Gs α z θ) = Work.Spaces.HkSq α 4 (Z19 α Φs) :=
      Work.FTS.EllipticEst.HkSq_congr_open α 4
        (f := fun z θ => Work.FTS.Nonlinear.Pieces.RNP.Vs α Φs z θ
          * Work.FTS.Nonlinear.Pieces.RNP.Gs α z θ) (g := Z19 α Φs)
        (fun z θ hz _ _ => hAG z θ hz)
    have hXneq : Work.FTS.Nonlin.Xn α (fun z θ => Work.FTS.Nonlinear.Pieces.RNP.Vs α Φs z θ
          * Work.FTS.Nonlinear.Pieces.RNP.Gs α z θ) = Work.FTS.Nonlin.Xn α (Z19 α Φs) := by
      simp only [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm, hsqeq]
    constructor
    · have hN3 : Work.FTS.Nonlin.N3ss α Φs
          = fun z θ => (-2 * α) * (Work.FTS.Nonlinear.Pieces.RNP.Vs α Φs z θ
              * Work.FTS.Nonlinear.Pieces.RNP.Gs α z θ) := by
        funext z θ
        simp only [Work.FTS.Nonlin.N3ss, Work.FTS.Nonlinear.Pieces.RNP.Vs,
          Work.FTS.Nonlinear.Pieces.RNP.Gs]
        ring
      rw [hN3]
      exact Work.FTS.LocData.HkMem_const_mul α 4 (-2 * α) hmemVG
    · have hN3x := Work.FTS.Nonlinear.Pieces.RNP.xn_N3ss_of_nonneg hα.le Φs
      rw [hN3x, hXneq]
      have h1 : Work.FTS.Nonlin.Xn α (Z19 α Φs)
          ≤ Cw * (CZ19 C2 * α * Work.Spaces.WlInf α 4 (A19 α Φs)) := hmain.2
      have h2 : Cw * (CZ19 C2 * α * Work.Spaces.WlInf α 4 (A19 α Φs))
          ≤ Cw * (CZ19 C2 * α * (Cs * α)) := by
        refine mul_le_mul_of_nonneg_left ?_ hCw.le
        exact mul_le_mul_of_nonneg_left hAle (mul_nonneg hCZpos.le hα.le)
      have h3 : 2 * α * (Cw * (CZ19 C2 * α * (Cs * α)))
          = 2 * Cw * CZ19 C2 * Cs * α ^ 3 := by ring
      have hA0 : (0 : ℝ) ≤ 2 * Cw * CZ19 C2 :=
        (mul_pos (mul_pos (by norm_num) hCw) hCZpos).le
      have hα3 : (0 : ℝ) ≤ α ^ 3 := by positivity
      have hfin : 2 * Cw * CZ19 C2 * Cs * α ^ 3
          ≤ (2 * Cw * CZ19 C2 + 1) * (1 + |Cs|) * α ^ 3 := by
        have hCs : Cs ≤ 1 + |Cs| := by
          have hle := le_abs_self Cs
          linarith
        have h1 : 2 * Cw * CZ19 C2 * Cs ≤ 2 * Cw * CZ19 C2 * (1 + |Cs|) :=
          mul_le_mul_of_nonneg_left hCs hA0
        have h2 : 2 * Cw * CZ19 C2 * (1 + |Cs|)
            ≤ (2 * Cw * CZ19 C2 + 1) * (1 + |Cs|) := by
          refine mul_le_mul_of_nonneg_right ?_ ?_
          · linarith
          · have hle := abs_nonneg Cs
            linarith
        exact mul_le_mul_of_nonneg_right (le_trans h1 h2) hα3
      calc 2 * α * Work.FTS.Nonlin.Xn α (Z19 α Φs)
          ≤ 2 * α * (Cw * (CZ19 C2 * α * Work.Spaces.WlInf α 4 (A19 α Φs))) :=
            mul_le_mul_of_nonneg_left h1 (mul_nonneg (by norm_num) hα.le)
        _ ≤ 2 * α * (Cw * (CZ19 C2 * α * (Cs * α))) :=
            mul_le_mul_of_nonneg_left h2 (mul_nonneg (by norm_num) hα.le)
        _ = 2 * Cw * CZ19 C2 * Cs * α ^ 3 := h3
        _ ≤ (2 * Cw * CZ19 C2 + 1) * (1 + |Cs|) * α ^ 3 := hfin

end Work.FTS.StrongPersist.L3Rhs
end
