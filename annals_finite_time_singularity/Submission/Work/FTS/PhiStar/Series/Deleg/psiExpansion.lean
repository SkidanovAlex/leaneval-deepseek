import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.PhiStar.Gegenbauer.FamNormValue
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_complete
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstTendsto
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.RegPkgGal.RVocab
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.thetaHardyLeft
import Submission.Work.FTS.StrongPersist.SP6.RadialSlot6
import Submission.Work.FTS.StrongPersist.SupOpenH2Z
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_RegExport.RXT.radial_noDecay_le
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2W.FstarDzIterFourPsiAe
import Submission.Work.Spaces.ThetaAgmon.agmon_interval
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.PhiStar.AngU.WtBoundU =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology BigOperators

namespace Work.FTS.PhiStar.AngU

open Work.FTS.PhiStar.FlatWAux Work.FTS.PhiStar.Gegenbauer Work.FTS.PhiStar.Series

/-- **The `U`-form of the angular bound.**  The resummed angular profiles
`Wt ψ j = Σ_m b_m λ_m^{-j} Q_m` (`j ≥ 1`) and `Wt ψ 0 = ψ / sin 2θ` are bounded on `(0, π/2)`.

The hypothesis on the modes is only the *zeroth order* bound `|Q_m| ≤ C (2m+1)²` (the sibling
`FlatWAux.WtBound` assumes, and only uses, exactly this instance of a full `l ≤ 8` derivative
hypothesis), and the bound on `ψ / sin 2θ` is the `FlatW 7` bound with constant `Cf`.  Both
constants are allowed to be nonnegative (rather than positive), which is what the callers have. -/
theorem WtBoundU (Cd CQ0 Cf : ℝ) (hCd : 0 ≤ Cd) (hCQ0 : 0 ≤ CQ0) (hCf : 0 ≤ Cf) :
    ∃ Kw : ℕ → ℝ, (∀ j : ℕ, 0 ≤ Kw j) ∧ ∀ (ψ : ℝ → ℝ),
      (∀ m : ℕ, 1 ≤ m → |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))) →
      (∀ m : ℕ, 1 ≤ m → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
        |Work.FTS.PhiStar.FlatWAux.Qm m θ| ≤ CQ0 * (2 * (m : ℝ) + 1) ^ 2) →
      Work.FTS.VocabO2.FlatW 7 (fun z θ => ψ θ / Work.Construction.s2 θ) Cf →
      ∀ j : ℕ, j ≤ Work.FTS.PhiStar.FlatWAux.J → ∀ θ : ℝ,
        θ ∈ Set.Ioo 0 (Real.pi / 2) → |Work.FTS.PhiStar.FlatWAux.Wt ψ j θ| ≤ Kw j := by
  -- the summable angular series majorant and its value `T`
  set T : ℝ := ∑' m : ℕ,
    (2 * (m : ℝ) + 1) / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)) with hTdef
  have hlamnn : ∀ m : ℕ, 0 ≤ Gegenbauer.lam m := by
    intro m; simp only [Gegenbauer.lam]; positivity
  have hTnn : 0 ≤ T := by
    rw [hTdef]
    exact tsum_nonneg (fun m => div_nonneg (by positivity)
      (mul_nonneg (hlamnn m) (Real.sqrt_nonneg _)))
  have hbase : Summable (fun m : ℕ => Cd * CQ0 *
      ((2 * (m : ℝ) + 1) / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))) :=
    WtDerivAux.summable_lam_sqrt.mul_left (Cd * CQ0)
  refine ⟨fun _ => max Cf (Cd * CQ0 * T),
    fun j => le_trans hCf (le_max_left _ _), ?_⟩
  intro ψ hdec hQ0 hflat j hj θ hθ
  rcases j with _ | k
  · -- `j = 0`: `Wt ψ 0 = ψ / sin 2θ` is bounded by the `FlatW` hypothesis
    have h := (hflat 1 θ one_pos hθ.1 hθ.2).1 0 (by norm_num)
    simp only [pow_zero, one_mul, Work.Spaces.pzIter_zero] at h
    exact le_trans h (le_max_left _ _)
  · -- `j = k + 1`: the resummed series, bounded termwise by the summable majorant
    have hpt : ∀ m : ℕ,
        |Work.FTS.PhiStar.Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ (k + 1) * Qm m θ|
        ≤ Cd * CQ0 * ((2 * (m : ℝ) + 1)
            / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))) := by
      intro m
      rcases Nat.eq_zero_or_pos m with hm | hm
      · -- `m = 0`: the summand vanishes since `λ_0 = 0`
        subst hm
        have hzero : ((Gegenbauer.lam 0)⁻¹) ^ (k + 1) = 0 := by
          rw [show Gegenbauer.lam 0 = 0 by norm_num [Gegenbauer.lam], inv_zero]
          exact zero_pow (Nat.succ_ne_zero k)
        rw [hzero, mul_zero, zero_mul, abs_zero]
        simp [Gegenbauer.lam]
      · -- `m ≥ 1`
        have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        have hlam_pos : 0 < Gegenbauer.lam m := by
          simp only [Gegenbauer.lam]; push_cast; nlinarith
        have hlam1 : 1 ≤ Gegenbauer.lam m := by
          simp only [Gegenbauer.lam]; push_cast; nlinarith
        have hNpos : 0 < 2 * (m : ℝ) + 1 := by positivity
        have hinvnn : 0 ≤ ((Gegenbauer.lam m)⁻¹) ^ (k + 1) :=
          pow_nonneg (inv_nonneg.mpr hlam_pos.le) _
        have hinv_le : ((Gegenbauer.lam m)⁻¹) ^ (k + 1) ≤ (Gegenbauer.lam m)⁻¹ := by
          rw [pow_succ]
          calc (Gegenbauer.lam m)⁻¹ ^ k * (Gegenbauer.lam m)⁻¹
              ≤ 1 * (Gegenbauer.lam m)⁻¹ :=
                mul_le_mul_of_nonneg_right
                  (pow_le_one₀ (inv_nonneg.mpr hlam_pos.le)
                    ((inv_le_one₀ hlam_pos).mpr hlam1))
                  (inv_nonneg.mpr hlam_pos.le)
            _ = (Gegenbauer.lam m)⁻¹ := one_mul _
        have hQm : |Qm m θ| ≤ CQ0 * (2 * (m : ℝ) + 1) ^ 2 := hQ0 m hm θ hθ
        have hb : |Work.FTS.PhiStar.Series.bmode m ψ|
            ≤ Cd / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)) := hdec m hm
        rw [abs_mul, abs_mul, abs_of_nonneg hinvnn]
        calc |Work.FTS.PhiStar.Series.bmode m ψ| * ((Gegenbauer.lam m)⁻¹) ^ (k + 1)
              * |Qm m θ|
            ≤ (Cd / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
                * (Gegenbauer.lam m)⁻¹ * (CQ0 * (2 * (m : ℝ) + 1) ^ 2) := by
              gcongr
          _ = Cd * CQ0 * ((2 * (m : ℝ) + 1) ^ 2
                / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1))) := by
              ring
          _ ≤ Cd * CQ0 * ((2 * (m : ℝ) + 1)
                / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))) := by
              have hNL : (2 * (m : ℝ) + 1) / Gegenbauer.lam m ≤ 1 := by
                rw [div_le_one hlam_pos]; simp only [Gegenbauer.lam]; push_cast; nlinarith
              have hkey : (2 * (m : ℝ) + 1) ^ 2
                    / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1))
                  ≤ (2 * (m : ℝ) + 1)
                    / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)) := by
                have hsplit : (2 * (m : ℝ) + 1) ^ 2
                      / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1))
                    = ((2 * (m : ℝ) + 1) / Gegenbauer.lam m)
                      * ((2 * (m : ℝ) + 1)
                        / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))) := by
                  ring
                rw [hsplit]
                exact mul_le_of_le_one_left (by positivity) hNL
              exact mul_le_mul_of_nonneg_left hkey (mul_nonneg hCd hCQ0)
    have hsum : Summable (fun m : ℕ =>
        Work.FTS.PhiStar.Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ (k + 1) * Qm m θ) :=
      Summable.of_norm_bounded hbase (fun m => by rw [Real.norm_eq_abs]; exact hpt m)
    have hWt : Wt ψ (k + 1) θ
        = ∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ (k + 1)
            * Qm m θ := rfl
    rw [hWt]
    calc |∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ (k + 1)
            * Qm m θ|
        = ‖∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ (k + 1)
            * Qm m θ‖ := by rw [Real.norm_eq_abs]
      _ ≤ ∑' m : ℕ, ‖Work.FTS.PhiStar.Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ (k + 1)
            * Qm m θ‖ := norm_tsum_le_tsum_norm hsum.norm
      _ = ∑' m : ℕ, |Work.FTS.PhiStar.Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ (k + 1)
            * Qm m θ| := by simp only [Real.norm_eq_abs]
      _ ≤ ∑' m : ℕ, Cd * CQ0 * ((2 * (m : ℝ) + 1)
            / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))) :=
            Summable.tsum_le_tsum hpt hsum.norm hbase
      _ = Cd * CQ0 * T := by rw [tsum_mul_left, hTdef]
      _ ≤ max Cf (Cd * CQ0 * T) := le_max_right _ _

end Work.FTS.PhiStar.AngU
end
-- ===== merged: Submission.Work.FTS.PhiStar.AngU.chia_base_boundU =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.AngU

open scoped Real Topology
open Filter Set

/-- `NbUU Cd Ms b = Cd + ∑_{a<b} C(b-1,a)·Ms·Cd`: the bound produced by the Leibniz expansion of
`Lop^[b] W = Lop^[b-1] (s2 · W')` from `|W'| ≤ Cd` and `|Lop^a s2| ≤ Ms`. -/
private def NbUU (Cd Ms : ℝ) (b : ℕ) : ℝ :=
  Cd + ∑ a ∈ Finset.range b, ((b - 1).choose a : ℝ) * (Ms * Cd)

private lemma NbUU_nonneg {Cd Ms : ℝ} (hCd : 0 ≤ Cd) (hMs : 0 ≤ Ms) (b : ℕ) :
    0 ≤ NbUU Cd Ms b := by
  refine add_nonneg hCd (Finset.sum_nonneg (fun a _ => ?_))
  exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hMs hCd)

private lemma NbUU_zero (Cd Ms : ℝ) : NbUU Cd Ms 0 = Cd := by
  simp [NbUU]

private lemma NbUU_succ (Cd Ms : ℝ) (b : ℕ) :
    NbUU Cd Ms (b + 1)
      = Cd + ∑ a ∈ Finset.range (b + 1), ((b.choose a : ℝ) * (Ms * Cd)) := by
  simp only [NbUU, Nat.add_sub_cancel]

/-- The `U`-form of `chia_base_bound`: the bounds on `Lop`-iterates of `chia ψ 0` are derived
directly from the hypotheses on `ψ / sin 2θ` and its `Lop`-derivatives, without passing through
`FlatW`. -/
theorem chia_base_boundU (Cd Ms : ℝ) (hCd : 0 ≤ Cd) (hMs : 0 ≤ Ms) :
    ∃ B : ℕ → ℝ, (∀ i : ℕ, 0 ≤ B i) ∧ ∀ (ψ : ℝ → ℝ),
      (∀ n : ℕ, ContDiffOn ℝ n ψ (Set.Ioo 0 (Real.pi / 2))) →
      (∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) → |ψ θ / Work.Construction.s2 θ| ≤ Cd) →
      (∀ d : ℕ, d ≤ 6 → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
        |(Work.Spaces.Lop^[d]) (deriv (fun θ' => ψ θ' / Work.Construction.s2 θ')) θ| ≤ Cd) →
      (∀ r : ℕ, r ≤ 6 → ∀ θ : ℝ, |(Work.Spaces.Lop^[r]) Work.Construction.s2 θ| ≤ Ms) →
      ∀ i : ℕ, i ≤ 6 → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
        |(Work.Spaces.Lop^[i]) (Work.FTS.PhiStar.FlatWAux.chia ψ 0) θ| ≤ B i := by
  refine ⟨fun i => ∑ a ∈ Finset.range (i + 1),
      (i.choose a : ℝ) * (Ms * NbUU Cd Ms (i - a)),
    fun i => Finset.sum_nonneg (fun a _ =>
      mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hMs (NbUU_nonneg hCd hMs _))), ?_⟩
  intro ψ hsm hWbd0 hW'bd0 hMsb
  have hIoo : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  -- the `z`-free angular profile `W = ψ / sin 2θ`
  set W : ℝ → ℝ := fun θ => ψ θ / Work.Construction.s2 θ with hWdef
  -- `sin 2θ > 0` and `s2 ≠ 0` on the open interval
  have hsinpos : ∀ x : ℝ, 0 < x → x < Real.pi / 2 → 0 < Real.sin (2 * x) := by
    intro x hx1 hx2
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hs2ne : ∀ x : ℝ, x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.Construction.s2 x ≠ 0 := by
    intro x hx
    rw [show Work.Construction.s2 x = Real.sin (2 * x) from rfl]
    exact ne_of_gt (hsinpos x hx.1 hx.2)
  -- smoothness of `s2` and of `W` at every order
  have hs2smN : ∀ n : ℕ,
      ContDiffOn ℝ n Work.Construction.s2 (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    intro n
    rw [show Work.Construction.s2 = (fun θ : ℝ => Real.sin (2 * θ)) from rfl]
    fun_prop
  have hs2sm : ContDiffOn ℝ 9 Work.Construction.s2 (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hs2smN 9
  have hWsmN : ∀ n : ℕ, ContDiffOn ℝ n W (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    intro n
    rw [hWdef]
    exact ContDiffOn.div (hsm n) (hs2smN n) (fun x hx => hs2ne x hx)
  have hWsm : ContDiffOn ℝ 9 W (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hWsmN 9
  have hW'sm : ContDiffOn ℝ 9 (deriv W) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (hWsmN 10).deriv_of_isOpen hIoo (by norm_num)
  -- the two inputs, directly from the hypotheses
  have hWbd : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |W θ| ≤ Cd := by
    intro θ hθ
    simpa only [hWdef] using hWbd0 θ hθ
  have hW'bd : ∀ i : ℕ, i ≤ 6 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |(Work.Spaces.Lop^[i]) (deriv W) θ| ≤ Cd := by
    intro i hi θ hθ
    simpa only [hWdef] using hW'bd0 i hi θ hθ
  -- bounds on the `Lop`-iterates of `s2`
  have hMs2 : ∀ a : ℕ, a ≤ 6 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |(Work.Spaces.Lop^[a]) Work.Construction.s2 θ| ≤ Ms := by
    intro a ha θ _
    exact hMsb a ha θ
  -- bounds on the `Lop`-iterates of `W`, by the Leibniz rule applied to `Lop W = s2 · W'`
  have hLopW : ∀ b : ℕ, b ≤ 6 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |(Work.Spaces.Lop^[b]) W θ| ≤ NbUU Cd Ms b := by
    intro b hb θ hθ
    rcases Nat.eq_zero_or_pos b with hb0 | hbpos
    · subst hb0
      rw [NbUU_zero, Function.iterate_zero_apply]
      exact hWbd θ hθ
    · obtain ⟨b', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hbpos)
      have hLeib := Work.FTS.PhiStar.LinvFlat.LI_Lop_iter_mul_eqOn_9 hIoo hs2sm hW'sm b'
        (by omega) hθ
      have heq : (Work.Spaces.Lop^[b' + 1]) W θ
          = ∑ a ∈ Finset.range (b' + 1), ((b'.choose a : ℝ) *
              ((Work.Spaces.Lop^[a]) Work.Construction.s2 θ
                * (Work.Spaces.Lop^[b' - a]) (deriv W) θ)) := by
        rw [Function.iterate_succ_apply]
        exact hLeib
      have hmain : |(Work.Spaces.Lop^[b' + 1]) W θ|
          ≤ ∑ a ∈ Finset.range (b' + 1), (b'.choose a : ℝ) * (Ms * Cd) := by
        rw [heq]
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun a ha => ?_))
        have ha6 : a ≤ 6 := by
          have := Finset.mem_range.mp ha
          omega
        have hb'a6 : b' - a ≤ 6 := by omega
        have hXY : |(Work.Spaces.Lop^[a]) Work.Construction.s2 θ
            * (Work.Spaces.Lop^[b' - a]) (deriv W) θ| ≤ Ms * Cd := by
          rw [abs_mul]
          exact mul_le_mul (hMs2 a ha6 θ hθ) (hW'bd (b' - a) hb'a6 θ hθ)
            (abs_nonneg _) hMs
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (b'.choose a))]
        exact mul_le_mul_of_nonneg_left hXY (Nat.cast_nonneg _)
      rw [NbUU_succ]
      exact le_trans hmain (le_add_of_nonneg_left hCd)
  -- the main expansion: `Lop^[i] (chia ψ 0) = Lop^[i] (s2 · W)` by Leibniz
  have hchia : ∀ i : ℕ, i ≤ 6 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |(Work.Spaces.Lop^[i]) (Work.FTS.PhiStar.FlatWAux.chia ψ 0) θ|
        ≤ ∑ a ∈ Finset.range (i + 1), (i.choose a : ℝ) * (Ms * NbUU Cd Ms (i - a)) := by
    intro i hi θ hθ
    have hch : Work.FTS.PhiStar.FlatWAux.chia ψ 0 = Work.Construction.s2 * W := by
      rw [Work.FTS.PhiStar.FlatWAux.chia_eq, Work.FTS.PhiStar.FlatWAux.Wt_zero, hWdef]
      rfl
    have hexp : (Work.Spaces.Lop^[i]) (Work.FTS.PhiStar.FlatWAux.chia ψ 0) θ
        = ∑ a ∈ Finset.range (i + 1), ((i.choose a : ℝ) *
            ((Work.Spaces.Lop^[a]) Work.Construction.s2 θ * (Work.Spaces.Lop^[i - a]) W θ)) := by
      rw [hch]
      exact Work.FTS.PhiStar.LinvFlat.LI_Lop_iter_mul_eqOn_9 hIoo hs2sm hWsm i (by omega) hθ
    rw [hexp]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun a ha => ?_))
    have ha6 : a ≤ 6 := by
      have := Finset.mem_range.mp ha
      omega
    have hia6 : i - a ≤ 6 := by omega
    have hXY : |(Work.Spaces.Lop^[a]) Work.Construction.s2 θ
        * (Work.Spaces.Lop^[i - a]) W θ| ≤ Ms * NbUU Cd Ms (i - a) := by
      rw [abs_mul]
      exact mul_le_mul (hMs2 a ha6 θ hθ) (hLopW (i - a) hia6 θ hθ) (abs_nonneg _) hMs
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (i.choose a))]
    exact mul_le_mul_of_nonneg_left hXY (Nat.cast_nonneg _)
  intro i hi θ hθ
  exact hchia i hi θ hθ

end Work.FTS.PhiStar.AngU
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.ModeZDeriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.FlatWAux

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# `Work.FTS.PhiStar.FlatWAux.ModeZDeriv`

Termwise `z`-differentiation of the mode series of `psiSeries α (RemSource α ψ)`
(the obligation `P1` of `FlatWAux/NOTES.md`); the route is recorded in `NOTES_ModeZDeriv.md`.

* `resc α m z = (z+1)/z · radGreen α m (phiA α) z` — the rescaled radial mode;
* `sliceSum` / `sliceMode` — the `θ`-slices of the rescaled series and of its `m`-th summand;
* `modeF` — the summand written through `bmode`;
* `iteratedDeriv_tsum_of_majorant` — the M-test for iterated derivatives of a `tsum`.

The only analytic input is the smoothness of `resc α m` on `(0,∞)` (`ModeRescaledSmooth`),
which is used for the differentiability of the individual modes.
-/

/-! ## The rescaled mode functions -/

/-- `resc α m z = (z+1)/z · radGreen α m (phiA α) z`, the rescaled radial mode. -/
private def resc (α : ℝ) (m : ℕ) : ℝ → ℝ :=
  fun z => (z + 1) / z * Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z

/-- The `θ`-slice of the rescaled mode series. -/
private def sliceSum (α : ℝ) (ψ : ℝ → ℝ) (θ : ℝ) : ℝ → ℝ :=
  fun y => (y + 1) / y
    * Work.FTS.PhiStar.Series.psiSeries α (Work.FTS.PhiStar.RemSource α ψ) y θ

/-- The `θ`-slice of the `m`-th summand of the rescaled mode series. -/
private def sliceMode (α : ℝ) (ψ : ℝ → ℝ) (θ : ℝ) (m : ℕ) : ℝ → ℝ :=
  fun y => (y + 1) / y
    * (Work.FTS.PhiStar.Series.acoeff α m (Work.FTS.PhiStar.RemSource α ψ) y
      * Work.FTS.PhiStar.Gegenbauer.eFam m θ)

/-- The same summand, written through `bmode` and `resc`. -/
private def modeF (α : ℝ) (ψ : ℝ → ℝ) (θ : ℝ) (m : ℕ) : ℝ → ℝ :=
  fun y => (α ^ 2 * Work.FTS.PhiStar.Series.bmode m ψ
    * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * resc α m y

private theorem sliceMode_eq_modeF (α : ℝ) (ψ : ℝ → ℝ) (θ : ℝ) (m : ℕ) :
    sliceMode α ψ θ m = modeF α ψ θ m := by
  funext y
  simp only [sliceMode, modeF, resc]
  rw [Work.FTS.PhiStar.Series.acoeff_RemSource]
  ring

private theorem sliceSum_eq_tsum (α : ℝ) (ψ : ℝ → ℝ) (θ : ℝ) :
    sliceSum α ψ θ = fun y => ∑' m : ℕ, modeF α ψ θ m y := by
  funext y
  simp only [sliceSum, modeF, resc, Work.FTS.PhiStar.Series.psiSeries]
  rw [← tsum_mul_left]
  refine tsum_congr (fun m => ?_)
  rw [Work.FTS.PhiStar.Series.acoeff_RemSource]
  ring

/-! ## Iterated derivatives of a `C^n` function on `(0,∞)` -/

private theorem continuousOn_iteratedDeriv_of_Ioi {f : ℝ → ℝ} {n m : ℕ}
    (hf : ContDiffOn ℝ n f (Set.Ioi 0)) (hmn : m ≤ n) :
    ContinuousOn (iteratedDeriv m f) (Set.Ioi 0) := by
  have h := ((contDiffOn_nat_iff_continuousOn_differentiableOn_deriv
    (isOpen_Ioi.uniqueDiffOn) (n := n) (f := f)).mp hf).1 m hmn
  exact h.congr (fun x hx => (iteratedDerivWithin_of_isOpen isOpen_Ioi hx).symm)

private theorem differentiableOn_iteratedDeriv_of_Ioi {f : ℝ → ℝ} {n m : ℕ}
    (hf : ContDiffOn ℝ n f (Set.Ioi 0)) (hmn : m < n) :
    DifferentiableOn ℝ (iteratedDeriv m f) (Set.Ioi 0) := by
  have h := ((contDiffOn_nat_iff_continuousOn_differentiableOn_deriv
    (isOpen_Ioi.uniqueDiffOn) (n := n) (f := f)).mp hf).2 m hmn
  exact h.congr (fun x hx => (iteratedDerivWithin_of_isOpen isOpen_Ioi hx).symm)

/-! ## Smoothness of the rescaled radial mode on `(0,∞)` -/

/-- A tail integral of a function of class `C^n` on `(0,∞)` is of class `C^n` there; if the
integrand is integrable on no tail, every integral is the junk value `0` (the dichotomy follows
from the continuity of the integrand on `(0,∞)`: two tails differ by a compact interval). -/
private theorem contDiffOn_Ioi_integral_all (n : ℕ) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ n f (Set.Ioi 0)) :
    ContDiffOn ℝ n (fun z => ∫ t in Set.Ioi z, f t) (Set.Ioi 0) := by
  have hcont : ContinuousOn f (Set.Ioi 0) := hf.continuousOn
  by_cases h1 : MeasureTheory.IntegrableOn f (Set.Ioi (1 : ℝ))
  · have hall : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn f (Set.Ioi z) := by
      intro z hz
      rcases le_or_gt 1 z with hle | hlt
      · exact h1.mono_set (Set.Ioi_subset_Ioi hle)
      · rw [← Set.Ioc_union_Ioi_eq_Ioi (le_of_lt hlt)]
        refine IntegrableOn.union ?_ h1
        exact IntegrableOn.mono_set
          (ContinuousOn.integrableOn_Icc (hcont.mono (fun x hx => lt_of_lt_of_le hz hx.1)))
          Set.Ioc_subset_Icc_self
    exact Work.FTS.EllExist.Honesty.Pieces.tailIntegral_contDiffOn n hf (hall 1 one_pos)
  · have hzero : (fun z => ∫ t in Set.Ioi z, f t) = fun _ => (0 : ℝ) := by
      funext z
      apply MeasureTheory.integral_undef
      intro hint
      have hInt : MeasureTheory.IntegrableOn f (Set.Ioi z) := hint
      apply h1
      rcases le_or_gt z 1 with hle | hlt
      · exact hInt.mono_set (Set.Ioi_subset_Ioi hle)
      · rw [← Set.Ioc_union_Ioi_eq_Ioi (le_of_lt hlt)]
        refine IntegrableOn.union ?_ hInt
        exact IntegrableOn.mono_set
          (ContinuousOn.integrableOn_Icc (hcont.mono (fun x hx => lt_of_lt_of_le one_pos hx.1)))
          Set.Ioc_subset_Icc_self
    rw [hzero]
    exact contDiffOn_const

/-- **The rescaled radial mode is smooth on `(0,∞)`** for every real `α`: the two integrals
defining `radGreen α m (phiA α)` are a primitive and a tail integral of functions that are `C^∞`
there, and the prefactors `z^{s^±}`, `(z+1)/z` are `C^∞` on `(0,∞)`. -/
private theorem resc_contDiffOn (α : ℝ) (m : ℕ) (n : ℕ) :
    ContDiffOn ℝ n (resc α m) (Set.Ioi 0) := by
  have hc : ContDiffOn ℝ n (Work.FTS.VocabO.phiA α) (Set.Ioi 0) :=
    fun z hz => (Work.FTS.PhiStar.contDiffAt_phiA_of α (n : WithTop ℕ∞) hz).contDiffWithinAt
  have hf1 : ContDiffOn ℝ n
      (fun t : ℝ => Work.FTS.VocabO.phiA α t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioi 0) :=
    hc.mul (contDiffOn_id.rpow_const_of_ne (p := (2 * (m : ℝ) + 5) / α - 1)
      (fun x hx => ne_of_gt hx))
  have hf2 : ContDiffOn ℝ n
      (fun t : ℝ => Work.FTS.VocabO.phiA α t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 0) :=
    hc.mul (contDiffOn_id.rpow_const_of_ne (p := -(2 * (m : ℝ) / α) - 1)
      (fun x hx => ne_of_gt hx))
  have hA : ContDiffOn ℝ n
      (fun z => ∫ t in (0 : ℝ)..z, Work.FTS.VocabO.phiA α t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioi 0) :=
    Work.FTS.EllExist.Honesty.Pieces.primitive_contDiffOn n hf1
  have hB : ContDiffOn ℝ n
      (fun z => ∫ t in Set.Ioi z, Work.FTS.VocabO.phiA α t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 0) :=
    contDiffOn_Ioi_integral_all n hf2
  have hza : ContDiffOn ℝ n (fun z : ℝ => z ^ (-(2 * (m : ℝ) + 5) / α)) (Set.Ioi 0) :=
    contDiffOn_id.rpow_const_of_ne (p := -(2 * (m : ℝ) + 5) / α) (fun x hx => ne_of_gt hx)
  have hzb : ContDiffOn ℝ n (fun z : ℝ => z ^ (2 * (m : ℝ) / α)) (Set.Ioi 0) :=
    contDiffOn_id.rpow_const_of_ne (p := 2 * (m : ℝ) / α) (fun x hx => ne_of_gt hx)
  have hmain : ContDiffOn ℝ n (fun z : ℝ => 1 / (α * (4 * (m : ℝ) + 5)) *
      (z ^ (-(2 * (m : ℝ) + 5) / α)
          * (∫ t in (0 : ℝ)..z, Work.FTS.VocabO.phiA α t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
        + z ^ (2 * (m : ℝ) / α)
          * (∫ t in Set.Ioi z, Work.FTS.VocabO.phiA α t * t ^ (-(2 * (m : ℝ) / α) - 1))))
      (Set.Ioi 0) :=
    contDiffOn_const.mul ((hza.mul hA).add (hzb.mul hB))
  have hG : ContDiffOn ℝ n
      (fun z => Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z) (Set.Ioi 0) :=
    hmain.congr (fun z _ => rfl)
  have hfac : ContDiffOn ℝ n (fun z : ℝ => (z + 1) / z) (Set.Ioi 0) :=
    (contDiffOn_id.add contDiffOn_const).div contDiffOn_id (fun z hz => ne_of_gt hz)
  exact (hfac.mul hG).congr (fun z _ => rfl)

/-! ## The M-test for iterated derivatives of a `tsum` -/

/-- **Termwise `k`-fold differentiation of a series.**  On an open preconnected set `t` on which
the iterated derivatives of each term are differentiable and dominated by summable majorants
`u j`, the iterated derivative of the sum is the sum of the iterated derivatives. -/
private theorem iteratedDeriv_tsum_of_majorant {k : ℕ} {t : Set ℝ} (ht : IsOpen t)
    (h't : IsPreconnected t) {f : ℕ → ℝ → ℝ} {u : ℕ → ℕ → ℝ}
    (hu : ∀ j : ℕ, j ≤ k → Summable (u j))
    (hdiff : ∀ j : ℕ, j < k → ∀ m : ℕ, DifferentiableOn ℝ (iteratedDeriv j (f m)) t)
    (hb : ∀ j : ℕ, j ≤ k → ∀ m : ℕ, ∀ y : ℝ, y ∈ t → |iteratedDeriv j (f m) y| ≤ u j m) :
    ∀ j : ℕ, j ≤ k → ∀ y : ℝ, y ∈ t →
      iteratedDeriv j (fun y' => ∑' m : ℕ, f m y') y = ∑' m : ℕ, iteratedDeriv j (f m) y := by
  intro j
  induction j with
  | zero =>
    intro _ y _
    simp only [iteratedDeriv_zero]
  | succ n ih =>
    intro hn1 y hy
    have hn : n ≤ k := Nat.le_of_succ_le hn1
    have hnk : n < k := Nat.lt_of_succ_le hn1
    have hIH : ∀ y' ∈ t, iteratedDeriv n (fun y' => ∑' m : ℕ, f m y') y'
        = ∑' m : ℕ, iteratedDeriv n (f m) y' := ih hn
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv n (fun y' => ∑' m : ℕ, f m y') =ᶠ[𝓝 y]
        fun y' => ∑' m : ℕ, iteratedDeriv n (f m) y' := by
      filter_upwards [ht.mem_nhds hy] with y' hy'
      exact hIH y' hy'
    rw [hev.deriv_eq]
    have hder : HasDerivAt (fun y' => ∑' m : ℕ, iteratedDeriv n (f m) y')
        (∑' m : ℕ, iteratedDeriv (n + 1) (f m) y) y := by
      refine hasDerivAt_tsum_of_isPreconnected (𝕜 := ℝ) (F := ℝ) (u := u (n + 1))
        (g := fun m y' => iteratedDeriv n (f m) y')
        (g' := fun m y' => iteratedDeriv (n + 1) (f m) y')
        (hu (n + 1) hn1) ht h't ?_ ?_ (y₀ := y) hy ?_ hy
      · intro m y' hy'
        have hd : DifferentiableAt ℝ (iteratedDeriv n (f m)) y' :=
          (hdiff n hnk m).differentiableAt (ht.mem_nhds hy')
        have h := hd.hasDerivAt
        rwa [← iteratedDeriv_succ] at h
      · intro m y' hy'
        rw [Real.norm_eq_abs]
        exact hb (n + 1) hn1 m y' hy'
      · refine Summable.of_norm_bounded (hu n hn) (fun m => ?_)
        rw [Real.norm_eq_abs]
        exact hb n hn m y hy
    exact hder.deriv

/-! ## The arithmetic of the majorant -/

private lemma four_mul_sq_le_lam {m : ℕ} (hm : 1 ≤ m) :
    4 * (m : ℝ) ^ 2 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := by
  have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  simp only [Work.FTS.PhiStar.Gegenbauer.lam]
  nlinarith

private lemma sqrt_two_mul_add_one_ge {m : ℕ} (hm : 1 ≤ m) :
    (3 : ℝ) / 2 ≤ Real.sqrt (2 * (m : ℝ) + 1) := by
  have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  rw [Real.le_sqrt (by norm_num) (by linarith)]
  nlinarith

private lemma majorant_le {m : ℕ} (hm : 1 ≤ m) :
    (2 * (m : ℝ) + 1) / (Work.FTS.PhiStar.Gegenbauer.lam m
        * Real.sqrt (2 * (m : ℝ) + 1) * Work.FTS.PhiStar.Gegenbauer.lam m)
      ≤ (((m : ℝ) + 1) ^ 2)⁻¹ := by
  have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlam4 : 4 * (m : ℝ) ^ 2 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := four_mul_sq_le_lam hm
  have hlamp : 0 < Work.FTS.PhiStar.Gegenbauer.lam m := by
    simp only [Work.FTS.PhiStar.Gegenbauer.lam]
    nlinarith
  have hs : (3 : ℝ) / 2 ≤ Real.sqrt (2 * (m : ℝ) + 1) := sqrt_two_mul_add_one_ge hm
  have hsp : 0 < Real.sqrt (2 * (m : ℝ) + 1) := Real.sqrt_pos_of_pos (by linarith)
  have hden : 0 < Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)
      * Work.FTS.PhiStar.Gegenbauer.lam m := by positivity
  rw [show (((m : ℝ) + 1) ^ 2)⁻¹ = 1 / ((m : ℝ) + 1) ^ 2 from by rw [one_div]]
  rw [div_le_div_iff₀ hden (by positivity : (0 : ℝ) < ((m : ℝ) + 1) ^ 2)]
  simp only [one_mul]
  have hm2 : 2 * (m : ℝ) + 1 ≤ 3 * (m : ℝ) := by linarith
  have hs2 : ((m : ℝ) + 1) ^ 2 ≤ (2 * (m : ℝ)) ^ 2 := by nlinarith
  have hstep1 : (2 * (m : ℝ) + 1) * ((m : ℝ) + 1) ^ 2
      ≤ (3 * (m : ℝ)) * (2 * (m : ℝ)) ^ 2 :=
    mul_le_mul hm2 hs2 (by positivity) (by positivity)
  have hstep2 : (3 * (m : ℝ)) * (2 * (m : ℝ)) ^ 2 = 12 * (m : ℝ) ^ 3 := by ring
  have hstep3 : 12 * (m : ℝ) ^ 3 ≤ 24 * (m : ℝ) ^ 4 := by nlinarith
  have hstep4 : 24 * (m : ℝ) ^ 4
      ≤ Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)
        * Work.FTS.PhiStar.Gegenbauer.lam m := by
    have h2 : (4 * (m : ℝ) ^ 2) * ((3 : ℝ) / 2) ≤ Work.FTS.PhiStar.Gegenbauer.lam m
        * Real.sqrt (2 * (m : ℝ) + 1) :=
      mul_le_mul hlam4 hs (by norm_num) (le_of_lt hlamp)
    calc 24 * (m : ℝ) ^ 4 = (4 * (m : ℝ) ^ 2) * ((3 : ℝ) / 2) * (4 * (m : ℝ) ^ 2) := by ring
      _ ≤ (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
            * Work.FTS.PhiStar.Gegenbauer.lam m :=
          mul_le_mul h2 hlam4 (by positivity) (by positivity)
  linarith

private lemma summable_inv_sq_shift : Summable (fun m : ℕ => (((m : ℝ) + 1) ^ 2)⁻¹) := by
  have h : Summable (fun m : ℕ => ((m : ℝ) + 1) ^ (-(2 : ℝ))) := by
    have h0 : Summable (fun n : ℕ => ((n : ℝ)) ^ (-(2 : ℝ))) :=
      (Real.summable_nat_rpow).mpr (by norm_num)
    have h1 := (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ)) ^ (-(2 : ℝ))) 1).mpr h0
    simpa only [Nat.cast_add, Nat.cast_one] using h1
  refine h.congr (fun m => ?_)
  rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ (m : ℝ) + 1)]
  norm_num

/-! ## The core identity -/

private theorem core (α : ℝ) (ψ : ℝ → ℝ) (z θ : ℝ) (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hgr : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ' : ℝ), θ' ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ'| ≤ C * (2 * (m : ℝ) + 1))
    (hrb : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ k : ℕ, k ≤ 7 → ∀ z' : ℝ, 0 < z' →
      |(z' + 1) ^ k * iteratedDeriv k (resc α m) z'| ≤ C / Work.FTS.PhiStar.Gegenbauer.lam m)
    (hS : ∀ (m n : ℕ), ContDiffOn ℝ n (resc α m) (Set.Ioi 0)) :
    ∀ k : ℕ, k ≤ 7 →
      iteratedDeriv k (sliceSum α ψ θ) z = ∑' m : ℕ, iteratedDeriv k (sliceMode α ψ θ m) z := by
  obtain ⟨Cb, hCb, hdec'⟩ := hdec
  obtain ⟨Ce, hCe, hgr'⟩ := hgr
  obtain ⟨Cr, hCr, hrb'⟩ := hrb
  have hθIθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  set V : ℝ := α ^ 2 * (Cb * Ce * Cr) with hV
  have hVnn : 0 ≤ V := by rw [hV]; positivity
  have hz2 : 0 < z / 2 := by linarith
  have ht : IsOpen (Set.Ioo (z / 2) (2 * z)) := isOpen_Ioo
  have h't : IsPreconnected (Set.Ioo (z / 2) (2 * z)) := isPreconnected_Ioo
  have hzt : z ∈ Set.Ioo (z / 2) (2 * z) := ⟨by linarith, by linarith⟩
  have hsub : Set.Ioo (z / 2) (2 * z) ⊆ Set.Ioi 0 := by
    intro y hy
    exact lt_of_lt_of_le hz2 (le_of_lt hy.1)
  -- the iterated derivatives of the modes factor through `resc`
  have hconst_mode : ∀ (m j : ℕ) (y : ℝ), y ∈ Set.Ioi 0 →
      iteratedDeriv j (modeF α ψ θ m) y
        = (α ^ 2 * Work.FTS.PhiStar.Series.bmode m ψ
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * iteratedDeriv j (resc α m) y := by
    intro m j y hy
    rw [show modeF α ψ θ m = (fun x => (α ^ 2 * Work.FTS.PhiStar.Series.bmode m ψ
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * resc α m x) from rfl]
    exact iteratedDeriv_const_mul _ ((hS m j).contDiffAt (isOpen_Ioi.mem_nhds hy))
  -- the `m = 0` term only needs a compact bound
  have hB : ∀ j : ℕ, ∃ B : ℝ, ∀ y ∈ Set.Ioo (z / 2) (2 * z),
      |iteratedDeriv j (modeF α ψ θ 0) y| ≤ B := by
    intro j
    have hcont : ContinuousOn (iteratedDeriv j (resc α 0)) (Set.Ioi 0) :=
      continuousOn_iteratedDeriv_of_Ioi (hS 0 (j + 1)) (Nat.le_succ j)
    have hcc : Set.Icc (z / 2) (2 * z) ⊆ Set.Ioi 0 := by
      intro y hy
      exact lt_of_lt_of_le hz2 hy.1
    obtain ⟨C0, hC0⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc (hcont.mono hcc)
    refine ⟨|α ^ 2 * Work.FTS.PhiStar.Series.bmode 0 ψ
        * Work.FTS.PhiStar.Gegenbauer.eFam 0 θ| * max C0 0 + 1, ?_⟩
    intro y hy
    have hy0 : y ∈ Set.Ioi (0 : ℝ) := hsub hy
    have hycc : y ∈ Set.Icc (z / 2) (2 * z) := ⟨le_of_lt hy.1, le_of_lt hy.2⟩
    have hbd : |iteratedDeriv j (resc α 0) y| ≤ C0 := by
      have h := hC0 y hycc
      rwa [Real.norm_eq_abs] at h
    rw [hconst_mode 0 j y hy0, abs_mul]
    calc |α ^ 2 * Work.FTS.PhiStar.Series.bmode 0 ψ
            * Work.FTS.PhiStar.Gegenbauer.eFam 0 θ| * |iteratedDeriv j (resc α 0) y|
        ≤ |α ^ 2 * Work.FTS.PhiStar.Series.bmode 0 ψ
            * Work.FTS.PhiStar.Gegenbauer.eFam 0 θ| * max C0 0 :=
          mul_le_mul_of_nonneg_left (le_max_of_le_left hbd) (abs_nonneg _)
      _ ≤ |α ^ 2 * Work.FTS.PhiStar.Series.bmode 0 ψ
            * Work.FTS.PhiStar.Gegenbauer.eFam 0 θ| * max C0 0 + 1 := by linarith
  choose B hBspec using hB
  set U : ℕ → ℕ → ℝ := fun j m =>
    (if m = 0 then B j else 0) + V * (((m : ℝ) + 1) ^ 2)⁻¹ with hUdef
  have hU_sum : ∀ j : ℕ, Summable (U j) := by
    intro j
    rw [hUdef]
    refine Summable.add ?_ (summable_inv_sq_shift.mul_left V)
    refine summable_of_ne_finset_zero (s := ({0} : Finset ℕ)) (fun b hb => ?_)
    simp only [Finset.mem_singleton] at hb
    simp [hb]
  -- the pointwise bound of the majorant
  have hU_bound : ∀ j : ℕ, j ≤ 7 → ∀ m : ℕ, ∀ y : ℝ, y ∈ Set.Ioo (z / 2) (2 * z) →
      |iteratedDeriv j (modeF α ψ θ m) y| ≤ U j m := by
    intro j hj m y hy
    have hy0 : 0 < y := lt_of_lt_of_le hz2 (le_of_lt hy.1)
    have hypos : y ∈ Set.Ioi (0 : ℝ) := hy0
    rw [hconst_mode m j y hypos, abs_mul]
    change |α ^ 2 * Work.FTS.PhiStar.Series.bmode m ψ
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ| * |iteratedDeriv j (resc α m) y|
      ≤ (if m = 0 then B j else 0) + V * (((m : ℝ) + 1) ^ 2)⁻¹
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      rw [if_pos rfl]
      have hle : |α ^ 2 * Work.FTS.PhiStar.Series.bmode 0 ψ
            * Work.FTS.PhiStar.Gegenbauer.eFam 0 θ| * |iteratedDeriv j (resc α 0) y|
          ≤ B j := by
        have h := hBspec j y hy
        rwa [hconst_mode 0 j y hy0, abs_mul] at h
      calc |α ^ 2 * Work.FTS.PhiStar.Series.bmode 0 ψ
              * Work.FTS.PhiStar.Gegenbauer.eFam 0 θ| * |iteratedDeriv j (resc α 0) y|
          ≤ B j := hle
        _ ≤ B j + V * ((((0 : ℕ) : ℝ) + 1) ^ 2)⁻¹ := by
            have h2 : (0 : ℝ) ≤ V * ((((0 : ℕ) : ℝ) + 1) ^ 2)⁻¹ := by positivity
            linarith
    · rw [if_neg (Nat.pos_iff_ne_zero.mp hm), zero_add]
      have hk' : |iteratedDeriv j (resc α m) y| ≤ Cr / Work.FTS.PhiStar.Gegenbauer.lam m := by
        have hpow : (1 : ℝ) ≤ (y + 1) ^ j := one_le_pow₀ (by linarith)
        have h1 : |iteratedDeriv j (resc α m) y|
            ≤ |(y + 1) ^ j * iteratedDeriv j (resc α m) y| := by
          calc |iteratedDeriv j (resc α m) y| = 1 * |iteratedDeriv j (resc α m) y| := by ring
            _ ≤ (y + 1) ^ j * |iteratedDeriv j (resc α m) y| :=
                mul_le_mul_of_nonneg_right hpow (abs_nonneg _)
            _ = |(y + 1) ^ j * iteratedDeriv j (resc α m) y| := by
                rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (y + 1) ^ j by positivity)]
        exact le_trans h1 (hrb' m hm j hj y hy0)
      have hbm : |Work.FTS.PhiStar.Series.bmode m ψ|
          ≤ Cb / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)) :=
        hdec' m hm
      have hem : |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ Ce * (2 * (m : ℝ) + 1) :=
        hgr' m θ hθIθ
      have hlamp : 0 < Work.FTS.PhiStar.Gegenbauer.lam m := by
        simp only [Work.FTS.PhiStar.Gegenbauer.lam]
        have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        nlinarith
      have hlamnn : 0 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := le_of_lt hlamp
      have hsnn : 0 ≤ Real.sqrt (2 * (m : ℝ) + 1) := Real.sqrt_nonneg _
      have hm2nn : (0 : ℝ) ≤ 2 * (m : ℝ) + 1 := by positivity
      have hc1 : |α ^ 2 * Work.FTS.PhiStar.Series.bmode m ψ
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ|
          ≤ α ^ 2 * (Cb / (Work.FTS.PhiStar.Gegenbauer.lam m
              * Real.sqrt (2 * (m : ℝ) + 1))) * (Ce * (2 * (m : ℝ) + 1)) := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ α ^ 2)]
        exact mul_le_mul (mul_le_mul_of_nonneg_left hbm (by positivity)) hem
          (abs_nonneg _)
          (mul_nonneg (by positivity)
            (div_nonneg (le_of_lt hCb) (mul_nonneg hlamnn hsnn)))
      have hprod : |α ^ 2 * Work.FTS.PhiStar.Series.bmode m ψ
              * Work.FTS.PhiStar.Gegenbauer.eFam m θ| * |iteratedDeriv j (resc α m) y|
          ≤ V * ((2 * (m : ℝ) + 1) / (Work.FTS.PhiStar.Gegenbauer.lam m
              * Real.sqrt (2 * (m : ℝ) + 1) * Work.FTS.PhiStar.Gegenbauer.lam m)) := by
        calc |α ^ 2 * Work.FTS.PhiStar.Series.bmode m ψ
                * Work.FTS.PhiStar.Gegenbauer.eFam m θ| * |iteratedDeriv j (resc α m) y|
            ≤ (α ^ 2 * (Cb / (Work.FTS.PhiStar.Gegenbauer.lam m
                * Real.sqrt (2 * (m : ℝ) + 1))) * (Ce * (2 * (m : ℝ) + 1)))
                * (Cr / Work.FTS.PhiStar.Gegenbauer.lam m) :=
              mul_le_mul hc1 hk' (abs_nonneg _)
                (mul_nonneg (mul_nonneg (by positivity)
                  (div_nonneg (le_of_lt hCb) (mul_nonneg hlamnn hsnn)))
                  (mul_nonneg (le_of_lt hCe) hm2nn))
          _ = V * ((2 * (m : ℝ) + 1) / (Work.FTS.PhiStar.Gegenbauer.lam m
                * Real.sqrt (2 * (m : ℝ) + 1) * Work.FTS.PhiStar.Gegenbauer.lam m)) := by
              rw [hV]
              field_simp
      have hmaj := majorant_le hm
      calc |α ^ 2 * Work.FTS.PhiStar.Series.bmode m ψ
              * Work.FTS.PhiStar.Gegenbauer.eFam m θ| * |iteratedDeriv j (resc α m) y|
          ≤ V * ((2 * (m : ℝ) + 1) / (Work.FTS.PhiStar.Gegenbauer.lam m
              * Real.sqrt (2 * (m : ℝ) + 1) * Work.FTS.PhiStar.Gegenbauer.lam m)) := hprod
        _ ≤ V * (((m : ℝ) + 1) ^ 2)⁻¹ := mul_le_mul_of_nonneg_left hmaj hVnn
  intro k hk
  have hdiff_arg : ∀ j : ℕ, j < k → ∀ m : ℕ,
      DifferentiableOn ℝ (iteratedDeriv j (modeF α ψ θ m)) (Set.Ioo (z / 2) (2 * z)) := by
    intro j hj m
    have h1 : DifferentiableOn ℝ (fun y => (α ^ 2 * Work.FTS.PhiStar.Series.bmode m ψ
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * iteratedDeriv j (resc α m) y)
        (Set.Ioo (z / 2) (2 * z)) :=
      ((differentiableOn_iteratedDeriv_of_Ioi (hS m (j + 1)) (Nat.lt_succ_self j)).const_mul
        (α ^ 2 * Work.FTS.PhiStar.Series.bmode m ψ
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ)).mono hsub
    exact h1.congr (fun y hy => hconst_mode m j y (hsub hy))
  have hmain := iteratedDeriv_tsum_of_majorant (t := Set.Ioo (z / 2) (2 * z)) ht h't
    (f := modeF α ψ θ) (u := U) (fun j _ => hU_sum j) hdiff_arg
    (fun j hj m y hy => hU_bound j (le_trans hj hk) m y hy) k le_rfl z hzt
  rw [sliceSum_eq_tsum]
  simp only [sliceMode_eq_modeF]
  exact hmain

theorem ModeZDeriv (α : ℝ) (ψ : ℝ → ℝ) (z θ : ℝ) (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hgr : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ' : ℝ), θ' ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ'| ≤ C * (2 * (m : ℝ) + 1))
    (hrb : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ k : ℕ, k ≤ 7 → ∀ z' : ℝ, 0 < z' →
      |(z' + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
          * Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z'') z'|
        ≤ C / Work.FTS.PhiStar.Gegenbauer.lam m) :
    ∀ k : ℕ, k ≤ 7 →
      (z + 1) ^ k * Work.Spaces.pzIter k
          (fun z' θ' => (z' + 1) / z' * Work.FTS.PhiStar.Series.psiSeries α
            (Work.FTS.PhiStar.RemSource α ψ) z' θ') z θ
        = ∑' m : ℕ, (z + 1) ^ k * Work.Spaces.pzIter k
            (fun z' θ' => (z' + 1) / z'
              * (Work.FTS.PhiStar.Series.acoeff α m (Work.FTS.PhiStar.RemSource α ψ) z'
                * Work.FTS.PhiStar.Gegenbauer.eFam m θ')) z θ := by
  intro k hk
  have hS : ∀ (m n : ℕ), ContDiffOn ℝ n (resc α m) (Set.Ioi 0) := fun m n => resc_contDiffOn α m n
  have hrb' : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ k : ℕ, k ≤ 7 → ∀ z' : ℝ, 0 < z' →
      |(z' + 1) ^ k * iteratedDeriv k (resc α m) z'|
        ≤ C / Work.FTS.PhiStar.Gegenbauer.lam m := by
    obtain ⟨C, hC, h⟩ := hrb
    exact ⟨C, hC, fun m hm k hk z' hz' => h m hm k hk z' hz'⟩
  have hcore := core α ψ z θ hz hθ hdec hgr hrb' hS k hk
  have hLHS : Work.Spaces.pzIter k (fun z' θ' => (z' + 1) / z'
      * Work.FTS.PhiStar.Series.psiSeries α (Work.FTS.PhiStar.RemSource α ψ) z' θ') z θ
      = iteratedDeriv k (sliceSum α ψ θ) z := by
    rw [Work.Spaces.pzIter_eq_iteratedDeriv]
    exact congrArg (fun g => iteratedDeriv k g z) (by funext y; simp only [sliceSum])
  have hRHS : ∀ m : ℕ, Work.Spaces.pzIter k (fun z' θ' => (z' + 1) / z'
      * (Work.FTS.PhiStar.Series.acoeff α m (Work.FTS.PhiStar.RemSource α ψ) z'
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ')) z θ
      = iteratedDeriv k (sliceMode α ψ θ m) z := by
    intro m
    rw [Work.Spaces.pzIter_eq_iteratedDeriv]
    exact congrArg (fun g => iteratedDeriv k g z) (by funext y; simp only [sliceMode])
  simp only [hLHS, hRHS]
  rw [hcore, tsum_mul_left]

end Work.FTS.PhiStar.FlatWAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.Deleg.psiExpansion =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators MeasureTheory
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series.Deleg

set_option autoImplicit false

private abbrev mcoeff (ψ : ℝ → ℝ) : ℕ → ℝ :=
  fun m => Work.FTS.PhiStar.Series.cmode m (fun _ θ' => ψ θ') 0

private abbrev modeMajor (ψ : ℝ → ℝ) (C : ℝ) : ℕ → ℝ :=
  fun m => (if m = 0 then |mcoeff ψ 0| * Real.sqrt 6 else 0)
    + (5 * C / 4) * ((m : ℝ) ^ (3 / 2 : ℝ))⁻¹

private abbrev modeSum (ψ : ℝ → ℝ) : ℕ → ℝ → ℝ :=
  fun m θ => mcoeff ψ m * Work.FTS.PhiStar.Gegenbauer.eFam m θ

private abbrev seriesSum (ψ : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => ∑' m : ℕ, modeSum ψ m θ

/-- `0` is negligible. -/
private lemma ae_ne_zero : ∀ᵐ θ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), θ ≠ (0 : ℝ) := by
  rw [MeasureTheory.ae_iff]
  simpa using (MeasureTheory.measure_singleton (0 : ℝ) :
    (MeasureTheory.volume : MeasureTheory.Measure ℝ) ({0} : Set ℝ) = 0)

/-- `π/2` is negligible. -/
private lemma ae_ne_pi_half : ∀ᵐ θ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
    θ ≠ Real.pi / 2 := by
  rw [MeasureTheory.ae_iff]
  simpa using (MeasureTheory.measure_singleton (Real.pi / 2) :
    (MeasureTheory.volume : MeasureTheory.Measure ℝ) ({Real.pi / 2} : Set ℝ) = 0)

/-- A property holding on the open interval holds a.e. on `Iθ`. -/
private lemma ae_mem_Ioo_Iθ :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  rw [Work.Spaces.Iθ, MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  filter_upwards [ae_ne_zero, ae_ne_pi_half] with θ h0 h1 hIcc
  rw [Set.mem_Icc] at hIcc
  exact ⟨lt_of_le_of_ne hIcc.1 (Ne.symm h0), lt_of_le_of_ne hIcc.2 h1⟩

/-- The `(N+1)`-st partial sum of the angular mode series. -/
private abbrev modePart (b : ℕ → ℝ) : ℕ → ℝ → ℝ :=
  fun N θ => ∑ m ∈ Finset.range (N + 1), b m * Work.FTS.PhiStar.Gegenbauer.eFam m θ

/-- **The `L²`-limit of the partial sums is the pointwise limit, a.e.**  If the partial sums
`∑_{m ≤ N} b m e_m` are bounded by `M` on the open interval, converge pointwise there to `S`,
and `∫ (ψ - ∑_{m ≤ N} b m e_m)² cos θ → 0`, while `ψ` is bounded by `M` on `Iθ` and
`S` is continuous on the open interval, then `S = ψ` a.e. on `(0,π/2)`. -/
private theorem ae_eq_of_residual (b : ℕ → ℝ) (ψ S : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hψbound : ∀ θ ∈ Set.Icc 0 (Real.pi / 2), |ψ θ| ≤ M)
    (hPbound : ∀ (N : ℕ) (θ : ℝ), θ ∈ Set.Ioo 0 (Real.pi / 2) → |modePart b N θ| ≤ M)
    (hcontS : ContinuousOn S (Set.Ioo 0 (Real.pi / 2)))
    (hmeas : MeasureTheory.AEStronglyMeasurable ψ (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hconv : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Filter.Tendsto (fun N : ℕ => modePart b N θ) Filter.atTop (nhds (S θ)))
    (hlim : Filter.Tendsto (fun N : ℕ => ∫ θ in Work.Spaces.Iθ,
        (ψ θ - modePart b N θ) ^ 2 * Real.cos θ) Filter.atTop (nhds 0)) :
    S =ᵐ[MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))] ψ := by
  have hcospos : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 < Real.cos θ := fun θ hθ =>
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
  -- `S` is a.e. strongly measurable on `Iθ` (it is continuous on the open interval)
  have hS_ae : MeasureTheory.AEStronglyMeasurable S
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    obtain ⟨g, hg, hgeq⟩ := hcontS.aestronglyMeasurable measurableSet_Ioo
    refine ⟨g, hg, ?_⟩
    show ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), S θ = g θ
    rw [Work.Spaces.Iθ, MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    have h1 : ∀ᵐ θ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
        θ ∈ Set.Ioo 0 (Real.pi / 2) → S θ = g θ :=
      (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mp hgeq
    filter_upwards [h1, ae_ne_zero, ae_ne_pi_half] with θ hθ1 h0 h1' hIcc
    refine hθ1 ?_
    rw [Set.mem_Icc] at hIcc
    exact ⟨lt_of_le_of_ne hIcc.1 (Ne.symm h0), lt_of_le_of_ne hIcc.2 h1'⟩
  -- continuity of each mode and of the partial sums
  have hcontE : ∀ m : ℕ, Continuous (fun θ : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m θ) := by
    intro m
    have h := (Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous
    exact Real.continuous_cos.mul (h.comp Real.continuous_sin)
  have hcontP : ∀ N : ℕ, Continuous (fun θ : ℝ => modePart b N θ) := by
    intro N
    refine continuous_finsetSum (Finset.range (N + 1)) (fun m _ => ?_)
    exact continuous_const.mul (hcontE m)
  -- the dominating function is integrable
  have hbdInt : MeasureTheory.Integrable (fun θ : ℝ => (2 * M) ^ 2 * Real.cos θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    ContinuousOn.integrableOn_compact isCompact_Icc
      ((continuous_const.mul Real.continuous_cos).continuousOn)
  -- a.e. strong measurability of the residuals
  have hmeasF : ∀ N : ℕ, MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => (ψ θ - modePart b N θ) ^ 2 * Real.cos θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro N
    have hq : AEMeasurable (fun θ : ℝ => modePart b N θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      (hcontP N).measurable.aemeasurable
    have hm : AEMeasurable (fun θ : ℝ => (ψ θ - modePart b N θ) ^ 2 * Real.cos θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      ((hmeas.aemeasurable.sub hq).pow_const 2).mul Real.continuous_cos.measurable.aemeasurable
    rwa [aestronglyMeasurable_iff_aemeasurable]
  -- the a.e. domination
  have hbound_ae : ∀ N : ℕ, ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ‖(ψ θ - modePart b N θ) ^ 2 * Real.cos θ‖ ≤ (2 * M) ^ 2 * Real.cos θ := by
    intro N
    filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
    have hcos : 0 ≤ Real.cos θ := le_of_lt (hcospos θ hθ)
    have h1 : |ψ θ| ≤ M := hψbound θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have h2 : |modePart b N θ| ≤ M := hPbound N θ hθ
    have h3 : |ψ θ - modePart b N θ| ≤ 2 * M := by
      calc |ψ θ - modePart b N θ| = |ψ θ + -(modePart b N θ)| := by ring_nf
        _ ≤ |ψ θ| + |-(modePart b N θ)| := abs_add_le _ _
        _ = |ψ θ| + |modePart b N θ| := by rw [abs_neg]
        _ ≤ 2 * M := by linarith
    have hsq : (ψ θ - modePart b N θ) ^ 2 ≤ (2 * M) ^ 2 := by
      calc (ψ θ - modePart b N θ) ^ 2 = |ψ θ - modePart b N θ| ^ 2 := (sq_abs _).symm
        _ ≤ (2 * M) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h3 2
    calc ‖(ψ θ - modePart b N θ) ^ 2 * Real.cos θ‖
        = |(ψ θ - modePart b N θ) ^ 2 * Real.cos θ| := Real.norm_eq_abs _
      _ = (ψ θ - modePart b N θ) ^ 2 * Real.cos θ := by
            rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hcos)]
      _ ≤ (2 * M) ^ 2 * Real.cos θ := mul_le_mul_of_nonneg_right hsq hcos
  -- the a.e. pointwise convergence
  have hlim_ae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Filter.Tendsto (fun N : ℕ => (ψ θ - modePart b N θ) ^ 2 * Real.cos θ) Filter.atTop
        (nhds ((ψ θ - S θ) ^ 2 * Real.cos θ)) := by
    filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
    exact (((tendsto_const_nhds.sub (hconv θ hθ)).pow 2).mul tendsto_const_nhds)
  -- dominated convergence
  have hdct := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (F := fun N θ => (ψ θ - modePart b N θ) ^ 2 * Real.cos θ)
    (f := fun θ => (ψ θ - S θ) ^ 2 * Real.cos θ)
    (fun θ => (2 * M) ^ 2 * Real.cos θ) hmeasF hbdInt hbound_ae hlim_ae
  have hint0 : ∫ θ in Work.Spaces.Iθ, (ψ θ - S θ) ^ 2 * Real.cos θ = 0 :=
    tendsto_nhds_unique hdct hlim
  -- integrability of the limit residual
  have hSbound : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |S θ| ≤ M := by
    intro θ hθ
    refine abs_le.mpr ⟨?_, ?_⟩
    · exact ge_of_tendsto (hconv θ hθ)
        (Eventually.of_forall (fun N => (abs_le.mp (hPbound N θ hθ)).1))
    · exact le_of_tendsto (hconv θ hθ)
        (Eventually.of_forall (fun N => (abs_le.mp (hPbound N θ hθ)).2))
  have hf_int : MeasureTheory.Integrable (fun θ : ℝ => (ψ θ - S θ) ^ 2 * Real.cos θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine hbdInt.mono' ?_ ?_
    · have hm : AEMeasurable (fun θ : ℝ => (ψ θ - S θ) ^ 2 * Real.cos θ)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        ((hmeas.aemeasurable.sub hS_ae.aemeasurable).pow_const 2).mul
          Real.continuous_cos.measurable.aemeasurable
      rwa [aestronglyMeasurable_iff_aemeasurable]
    · filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
      have hcos : 0 ≤ Real.cos θ := le_of_lt (hcospos θ hθ)
      have h1 : |ψ θ| ≤ M := hψbound θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      have h2 : |S θ| ≤ M := hSbound θ hθ
      have h3 : |ψ θ - S θ| ≤ 2 * M := by
        calc |ψ θ - S θ| = |ψ θ + -S θ| := by ring_nf
          _ ≤ |ψ θ| + |-S θ| := abs_add_le _ _
          _ = |ψ θ| + |S θ| := by rw [abs_neg]
          _ ≤ 2 * M := by linarith
      have hsq : (ψ θ - S θ) ^ 2 ≤ (2 * M) ^ 2 := by
        calc (ψ θ - S θ) ^ 2 = |ψ θ - S θ| ^ 2 := (sq_abs _).symm
          _ ≤ (2 * M) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h3 2
      calc ‖(ψ θ - S θ) ^ 2 * Real.cos θ‖
          = |(ψ θ - S θ) ^ 2 * Real.cos θ| := Real.norm_eq_abs _
        _ = (ψ θ - S θ) ^ 2 * Real.cos θ := by
              rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hcos)]
        _ ≤ (2 * M) ^ 2 * Real.cos θ := mul_le_mul_of_nonneg_right hsq hcos
  -- the residual vanishes a.e.
  have hnonneg : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      0 ≤ (ψ θ - S θ) ^ 2 * Real.cos θ := by
    filter_upwards [MeasureTheory.ae_restrict_mem (s := Work.Spaces.Iθ) measurableSet_Icc]
      with θ hθ
    exact mul_nonneg (sq_nonneg _)
      (Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩)
  have hfae : (fun θ : ℝ => (ψ θ - S θ) ^ 2 * Real.cos θ)
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae hnonneg hf_int).mp hint0
  have hfae' : (fun θ : ℝ => (ψ θ - S θ) ^ 2 * Real.cos θ)
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))] 0 :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self hfae
  filter_upwards [hfae', MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ hmem
  have hc : Real.cos θ ≠ 0 := ne_of_gt (hcospos θ hmem)
  have hsq : (ψ θ - S θ) ^ 2 = 0 := (mul_eq_zero.mp hθ).resolve_right hc
  have hzero : ψ θ - S θ = 0 := sq_eq_zero_iff.mp hsq
  linarith


private theorem psiExpansion_aux (α : ℝ) (ψ : ℝ → ℝ) (hα : 0 < α) (hα5 : α ≤ 1 / 5)
    (hψ : Work.FTS.PhiStar.AngModel α ψ)
    (hdecay : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.cmode m (fun _ θ => ψ θ) 0|
        ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hbound : ∀ m : ℕ, ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ|
        ≤ Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)))
    (hModeRatio : ∀ m : ℕ, 1 ≤ m →
      Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3))
          / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
        ≤ (5 / 4) * ((m : ℝ) ^ (3 / 2 : ℝ))⁻¹)
    (hMajorant : ∀ K A : ℝ,
      Summable (fun m : ℕ => (if m = 0 then K else 0) + A * ((m : ℝ) ^ (3 / 2 : ℝ))⁻¹))
    (hContTsum : ∀ (b : ℕ → ℝ) (u : ℕ → ℝ), Summable u →
      (∀ m : ℕ, ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
        |b m * Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ u m) →
      ContinuousOn (fun θ : ℝ => ∑' m : ℕ, b m * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
        (Set.Ioo 0 (Real.pi / 2)))
    (hResidual : ∀ ψ : ℝ → ℝ,
      MeasureTheory.AEStronglyMeasurable ψ (MeasureTheory.volume.restrict Work.Spaces.Iθ) →
      MeasureTheory.IntegrableOn (fun θ => ψ θ ^ 2 * Real.cos θ) Work.Spaces.Iθ →
      Filter.Tendsto (fun N : ℕ => ∫ θ in Work.Spaces.Iθ,
          (ψ θ - ∑ m ∈ Finset.range (N + 1),
            Work.FTS.PhiStar.Series.cmode m (fun _ θ' => ψ θ') 0
              * Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2 * Real.cos θ)
        Filter.atTop (nhds 0)) :
    ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      (∑' m : ℕ, Work.FTS.PhiStar.Series.cmode m (fun _ θ' => ψ θ') 0
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ) = ψ θ := by
  obtain ⟨C, hCpos, hCdec⟩ := hdecay
  have hpi4 : (Real.pi / 4) ∈ Set.Ioo 0 (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  -- summability of the majorant
  have hu : Summable (modeMajor ψ C) :=
    hMajorant (|mcoeff ψ 0| * Real.sqrt 6) (5 * C / 4)
  -- the pointwise majorant
  have hbu : ∀ m : ℕ, ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |modeSum ψ m θ| ≤ modeMajor ψ C m := by
    intro m θ hθ
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      have hb0 : |Work.FTS.PhiStar.Gegenbauer.eFam 0 θ| ≤ Real.sqrt 6 := by
        have h := hbound 0 θ hθ
        norm_num at h
        exact h
      calc |modeSum ψ 0 θ|
          = |mcoeff ψ 0| * |Work.FTS.PhiStar.Gegenbauer.eFam 0 θ| := by
            simp only [modeSum, abs_mul]
        _ ≤ |mcoeff ψ 0| * Real.sqrt 6 :=
            mul_le_mul_of_nonneg_left hb0 (abs_nonneg _)
        _ = modeMajor ψ C 0 := by
            simp only [modeMajor]
            simp [Real.zero_rpow (show (3 / 2 : ℝ) ≠ 0 by norm_num)]
    · have hm1 : 1 ≤ m := hmpos
      have hm0' : ¬ (m = 0) := Nat.pos_iff_ne_zero.mp hmpos
      have hm1R : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
      have hlamp : 0 < Work.FTS.PhiStar.Gegenbauer.lam m := by
        rw [Work.FTS.PhiStar.Gegenbauer.lam]
        nlinarith
      have hsqrtp : 0 < Real.sqrt (2 * (m : ℝ) + 1) := Real.sqrt_pos.mpr (by linarith)
      have hden : 0 ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)) :=
        div_nonneg hCpos.le (mul_pos hlamp hsqrtp).le
      calc |modeSum ψ m θ|
          = |mcoeff ψ m| * |Work.FTS.PhiStar.Gegenbauer.eFam m θ| := by
            simp only [modeSum, abs_mul]
        _ ≤ (C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
              * Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) :=
            mul_le_mul (hCdec m hm1) (hbound m θ hθ) (abs_nonneg _) hden
        _ = C * (Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3))
              / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))) := by
            ring
        _ ≤ C * ((5 / 4) * ((m : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
            mul_le_mul_of_nonneg_left (hModeRatio m hm1) hCpos.le
        _ = (5 * C / 4) * ((m : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by ring
        _ = modeMajor ψ C m := by
            simp only [modeMajor, if_neg hm0']
            ring
  have hu_nonneg : ∀ m, 0 ≤ modeMajor ψ C m :=
    fun m => le_trans (abs_nonneg _) (hbu m (Real.pi / 4) hpi4)
  -- the partial sums are bounded by the total mass of the majorant
  have hpartial : ∀ N : ℕ, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |∑ m ∈ Finset.range (N + 1), modeSum ψ m θ| ≤ ∑' m, modeMajor ψ C m := by
    intro N θ hθ
    calc |∑ m ∈ Finset.range (N + 1), modeSum ψ m θ|
        ≤ ∑ m ∈ Finset.range (N + 1), |modeSum ψ m θ| :=
          Finset.abs_sum_le_sum_abs (fun m => modeSum ψ m θ) (Finset.range (N + 1))
      _ ≤ ∑ m ∈ Finset.range (N + 1), modeMajor ψ C m :=
          Finset.sum_le_sum (fun m _ => hbu m θ hθ)
      _ ≤ ∑' m, modeMajor ψ C m :=
          hu.sum_le_tsum _ (fun m _ => hu_nonneg m)
  -- absolute convergence of the mode series at every interior point
  have hsummable : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Summable (modeSum ψ · θ) := by
    intro θ hθ
    have h1 : Summable (fun m => |modeSum ψ m θ|) :=
      Summable.of_nonneg_of_le (fun m => abs_nonneg _) (fun m => hbu m θ hθ) hu
    exact Summable.of_norm (by simpa only [Real.norm_eq_abs] using h1)
  have hconvN : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Filter.Tendsto (fun N : ℕ => ∑ m ∈ Finset.range N, modeSum ψ m θ)
        Filter.atTop (nhds (∑' m, modeSum ψ m θ)) :=
    fun θ hθ => (hsummable θ hθ).hasSum.tendsto_sum_nat
  have hconv : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Filter.Tendsto (fun N : ℕ => ∑ m ∈ Finset.range (N + 1), modeSum ψ m θ)
        Filter.atTop (nhds (∑' m, modeSum ψ m θ)) :=
    fun θ hθ => (hconvN θ hθ).comp (tendsto_add_atTop_nat 1)
  have hSbound : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |∑' m, modeSum ψ m θ| ≤ ∑' m, modeMajor ψ C m := by
    intro θ hθ
    refine abs_le.mpr ⟨?_, ?_⟩
    · exact ge_of_tendsto (hconv θ hθ)
        (Eventually.of_forall (fun N => (abs_le.mp (hpartial N θ hθ)).1))
    · exact le_of_tendsto (hconv θ hθ)
        (Eventually.of_forall (fun N => (abs_le.mp (hpartial N θ hθ)).2))
  -- a bound for ψ on the closed interval, and the common bound M
  obtain ⟨Mψ, hMψ⟩ := isCompact_Icc.exists_bound_of_continuousOn hψ.cont
  have hMψ' : ∀ θ ∈ Set.Icc 0 (Real.pi / 2), |ψ θ| ≤ Mψ := by
    intro θ hθ
    simpa only [Real.norm_eq_abs] using hMψ θ hθ
  set M : ℝ := max (∑' m, modeMajor ψ C m) Mψ with hMdef
  have hMnonneg : 0 ≤ M := by
    rw [hMdef]
    exact le_trans (tsum_nonneg hu_nonneg) (le_max_left _ _)
  have hψbound : ∀ θ ∈ Set.Icc 0 (Real.pi / 2), |ψ θ| ≤ M := by
    intro θ hθ
    rw [hMdef]
    exact le_trans (hMψ' θ hθ) (le_max_right _ _)
  have hSboundM : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |seriesSum ψ θ| ≤ M := by
    intro θ hθ
    rw [hMdef]
    simp only [seriesSum]
    exact le_trans (hSbound θ hθ) (le_max_left _ _)
  -- the two inputs of the a.e. step
  have hmeasψ : MeasureTheory.AEStronglyMeasurable ψ
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    hψ.cont.aestronglyMeasurable measurableSet_Icc
  have hzψ : MeasureTheory.IntegrableOn (fun θ => ψ θ ^ 2 * Real.cos θ) Work.Spaces.Iθ :=
    ContinuousOn.integrableOn_compact isCompact_Icc
      ((hψ.cont.pow 2).mul Real.continuous_cos.continuousOn)
  have hres := hResidual ψ hmeasψ hzψ
  have hconvS : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Filter.Tendsto (fun N : ℕ => ∑ m ∈ Finset.range (N + 1),
          mcoeff ψ m * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
        Filter.atTop (nhds (seriesSum ψ θ)) := by
    intro θ hθ
    simpa only [modeSum, seriesSum] using hconv θ hθ
  -- the partial sums are uniformly bounded by `M`
  have hpartialM : ∀ (N : ℕ) (θ : ℝ), θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |∑ m ∈ Finset.range (N + 1), modeSum ψ m θ| ≤ M := by
    intro N θ hθ
    rw [hMdef]
    exact le_trans (hpartial N θ hθ) (le_max_left _ _)
  -- continuity of `S` on the open interval
  have hcontS : ContinuousOn (seriesSum ψ) (Set.Ioo 0 (Real.pi / 2)) :=
    hContTsum (mcoeff ψ) (modeMajor ψ C) hu (fun m θ hθ => hbu m θ hθ)
  -- the `L²`-limit and the pointwise limit agree a.e.
  have hae : seriesSum ψ =ᵐ[MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))] ψ :=
    ae_eq_of_residual (mcoeff ψ) ψ (seriesSum ψ) M hMnonneg hψbound hpartialM hcontS
      hmeasψ hconvS hres
  have hcontψ : ContinuousOn ψ (Set.Ioo 0 (Real.pi / 2)) :=
    hψ.cont.mono Ioo_subset_Icc_self
  have heq : Set.EqOn (seriesSum ψ) ψ (Set.Ioo 0 (Real.pi / 2)) :=
    MeasureTheory.Measure.eqOn_Ioo_of_ae_eq volume hae hcontS hcontψ
  intro θ h0 h1
  exact heq ⟨h0, h1⟩

/-- **The `eFam`-expansion of the angular model `ψ`.** -/
theorem psiExpansion (α : ℝ) (ψ : ℝ → ℝ) (hα : 0 < α) (hα5 : α ≤ 1 / 5)
    (hψ : Work.FTS.PhiStar.AngModel α ψ)
    (hdecay : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.cmode m (fun _ θ => ψ θ) 0|
        ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hbound : ∀ m : ℕ, ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ|
        ≤ Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3))) :
    ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      (∑' m : ℕ, Work.FTS.PhiStar.Series.cmode m (fun _ θ' => ψ θ') 0
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ) = ψ θ :=
  psiExpansion_aux α ψ hα hα5 hψ hdecay hbound
    (fun m hm => modeRatioLe m hm)
    (fun K A => summableModeMajorant K A)
    (fun b u hu h => continuousOnTsumEFam b u hu h)
    (fun ψ' h1 h2 => residualTendstoZero ψ' h1 h2)

end Work.FTS.PhiStar.Series.Deleg
end
end
