import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongEps.EpsE4Thr.regQo_const_mul
import Submission.Work.FTS.StrongEps.EpsRLX.MuBlockXnBound
import Submission.Work.FTS.StrongEps.JfamP_norm
import Submission.Work.FTS.StrongEps.PZeroAux.bumpHkNormBound
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.AuxProof
import Submission.Work.FTS.StrongPersist.SupOpenH2
import Submission.Work.FTS_LocDatum3a.Defs
import Submission.Work.FTS_RegExport.RXR1.mixed_abs_le_weighted
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.starVop
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.HkNorm_JfamP_le_pos =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv

set_option maxHeartbeats 1000000

/-- **E1, with the restriction `ε ≤ 1` removed.**  This is `Work.FTS.StrongEps.HkSq_Jeps_le`
(`Submission/Work/FTS/StrongEps/HkSq_Jeps_le.lean`) with the hypothesis `ε ≤ 1` dropped: its
proof is a verbatim copy of that lemma's, since the underlying engine
`HkSqAux.ofReal_HkSq_Jeps_le` only ever uses `0 < ε` (its support bound
`Jker_support_abs` allows any shift) and the three weight-shift lemmas
(`HkSqAux.wdiv_shift_le`, `HkSqAux.Wt_shift_le`, `HkSqAux.logJac_shift_le`) are stated for
arbitrary shifts. -/
theorem HkSq_Jeps_le_pos (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsMollKernel ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ k : ℕ, ∀ ε : ℝ, 0 < ε →
      ∀ f : ℝ → ℝ → ℝ,
        (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad) →
        Work.Spaces.HkMem α k f → Work.Spaces.HkMem α k (Work.FTS.StrongEps.Jeps ρ ε f) →
          Work.Spaces.HkSq α k (Work.FTS.StrongEps.Jeps ρ ε f)
            ≤ Real.exp (C * ε) * Work.Spaces.HkSq α k f := by
  obtain ⟨cη, hcηpos, hWη0⟩ := Work.FTS.StrongEps.HkSqAux.wdiv_shift_le
  obtain ⟨cγ, hcγpos, hWγ0⟩ := Work.FTS.StrongEps.HkSqAux.Wt_shift_le
  obtain ⟨δ, hδpos, hJac0⟩ := Work.FTS.StrongEps.HkSqAux.logJac_shift_le
  refine ⟨4 * max cη cγ + 2 * δ, by positivity, ?_⟩
  intro α hα k ε hε f hf hF hFJ
  have hc0 : 0 ≤ max cη cγ := le_of_lt (lt_of_lt_of_le hcηpos (le_max_left _ _))
  have hWη : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) → ∀ p : ℝ × ℝ,
      Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
        ≤ Real.exp (max cη cγ * (|p.1| + |p.2|))
          * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p.1)
              / (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2)) ^ (Work.Spaces.eta / 2)) := by
    intro z θ hz hθ p
    refine (hWη0 z θ p.1 p.2 hz hθ).trans (mul_le_mul_of_nonneg_right ?_ ?_)
    · exact Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    · exact div_nonneg (Work.FTS.StrongEps.w_nonneg _)
        (Real.rpow_nonneg
          (le_of_lt (Work.FTS.StrongEps.sin_two_pos (Work.FTS.StrongEps.thShift_mem hθ))) _)
  have hWγ : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) → ∀ p : ℝ × ℝ,
      Work.Spaces.Wt α z θ
        ≤ Real.exp (max cη cγ * (|p.1| + |p.2|))
          * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2) := by
    intro z θ hz hθ p
    exact (hWγ0 α hα z θ p.1 p.2 hz hθ).trans (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))
      (mul_nonneg (Work.FTS.StrongEps.w_nonneg _)
        (Real.rpow_nonneg
          (le_of_lt (Work.FTS.StrongEps.sin_two_pos (Work.FTS.StrongEps.thShift_mem hθ))) _)))
  have hmain := Work.FTS.StrongEps.HkSqAux.ofReal_HkSq_Jeps_le ρ hρ hα hε hf hF hFJ
    (c := max cη cγ) (δ := δ) hc0 (le_of_lt hδpos) hWη hWγ (fun s ζ p₁ p₂ => hJac0 s ζ p₁ p₂)
  have hconv : ENNReal.ofReal (Real.exp ((4 * max cη cγ + 2 * δ) * ε)
        * Work.Spaces.HkSq α k f)
      = ENNReal.ofReal (Real.exp ((4 * max cη cγ + 2 * δ) * ε))
        * ENNReal.ofReal (Work.Spaces.HkSq α k f) :=
    ENNReal.ofReal_mul (Real.exp_pos _).le
  rw [← hconv] at hmain
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (Real.exp_pos _).le (Work.Spaces.HkSq_nonneg α k f))).mp hmain

-- Adapt `Work.FTS.StrongEps.HkNorm_JfamP_le` (`Submission/Work/FTS/StrongEps/JfamP_norm.lean`)
-- by dropping its `ε ∈ Ioc 0 1` hypothesis: the E1 step passes `ε ≤ 1` as an unused argument
-- (`HkSqAux.ofReal_HkSq_Jeps_le` needs only `0 < ε`, and `HkSq_Jeps_le`'s proof never uses
-- `ε ≤ 1`); only the final constant changes, from `A * Xn6 (slice g s)` to
-- `A * Real.exp (A * ε) * Xn6 (slice g s)`.
--
-- Route: re-run `HkSq_Jeps_le`'s ~15 lines against `HkSqAux.ofReal_HkSq_Jeps_le` with
-- `HkSqAux.wdiv_shift_le` / `HkSqAux.Wt_shift_le` / `HkSqAux.logJac_shift_le` (giving
-- `HkSq α k (Jeps ρ ε f) ≤ Real.exp (C * ε) * HkSq α k f` with `C = 4 * max cη cγ + 2 * δ`),
-- then repeat `HkNorm_JfamP_le`'s chain with `PZeroAux.PzJepsHkMem`, `HkMem_Jeps`,
-- `smoothOpen_Jeps`, `PZeroAux.hkNorm_Pz_le`.  Choose the final constant fresh, e.g.
-- `A := max (max A' (C / 2)) 1`, so that `A' * Real.exp (C * ε / 2) ≤ A * Real.exp (A * ε)`
-- for every `ε > 0`.
theorem HkNorm_JfamP_le_pos {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {α ε : ℝ}, α ∈ Set.Ioc 0 1 → 0 < ε →
      ∀ {g : Work.FTS.Galerkin.Fam} {s : ℝ},
        (∀ n : ℕ, ContDiffOn ℝ n
            (Function.uncurry (Work.FTS.Galerkin.slice g s)) Work.FTS.StrongEps.Quad) →
        Work.Spaces.HkMem α 6 (Work.FTS.Galerkin.slice g s) →
        Work.Spaces.HkMem α 6 (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s) ∧
          Work.FTS.StrongGlobal.Xn6 α (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s)
            ≤ A * Real.exp (A * ε) * Work.FTS.StrongGlobal.Xn6 α (Work.FTS.Galerkin.slice g s) := by
  obtain ⟨C, hCpos, hC⟩ := HkSq_Jeps_le_pos ρ hρ.moll
  obtain ⟨A', hA'pos, hA'⟩ := Work.FTS.StrongEps.PZeroAux.hkNorm_Pz_le
  refine ⟨max (max A' (C / 2)) 1, le_trans zero_le_one (le_max_right _ _), ?_⟩
  intro α ε hα hε g s hsm hmem
  -- membership and smoothness of the mollified slice
  have hsmJ : Work.FTS.EllipticEst.SmoothOpen
      (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.Galerkin.slice g s)) :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε hsm
  have hmemJ : Work.Spaces.HkMem α 6
      (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.Galerkin.slice g s)) :=
    Work.FTS.StrongEps.HkMem_Jeps hρ.moll hα hε hsm hmem
  -- the two conclusions of `slice (JfamP ρ ε g) s = Pz (Jeps ρ ε (slice g s))`
  have hmemP : Work.Spaces.HkMem α 6
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s) :=
    Work.FTS.StrongEps.PZeroAux.PzJepsHkMem 6 hρ hα hε hsm hmem
  refine ⟨hmemP, ?_⟩
  -- the `ℋ⁶`-norm bound for `J_ε`, keeping the full factor `e^{Cε/2}`
  have hJ : Work.Spaces.HkNorm α 6
        (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.Galerkin.slice g s))
      ≤ Real.exp (C * ε / 2) * Work.Spaces.HkNorm α 6 (Work.FTS.Galerkin.slice g s) := by
    have hsq := hC α hα 6 ε hε (Work.FTS.Galerkin.slice g s) hsm hmem hmemJ
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    calc Real.sqrt (Work.Spaces.HkSq α 6
            (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.Galerkin.slice g s)))
        ≤ Real.sqrt (Real.exp (C * ε)
            * Work.Spaces.HkSq α 6 (Work.FTS.Galerkin.slice g s)) :=
          Real.sqrt_le_sqrt hsq
      _ = Real.sqrt (Real.exp (C * ε))
            * Real.sqrt (Work.Spaces.HkSq α 6 (Work.FTS.Galerkin.slice g s)) :=
          Real.sqrt_mul (Real.exp_pos _).le _
      _ = Real.exp (C * ε / 2)
            * Work.Spaces.HkNorm α 6 (Work.FTS.Galerkin.slice g s) := by
          rw [Real.exp_half, Work.Spaces.HkNorm]
  have hP : Work.Spaces.HkNorm α 6
        (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.Galerkin.slice g s)))
      ≤ A' * Work.Spaces.HkNorm α 6
          (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.Galerkin.slice g s)) :=
    hA' α hα 6 le_rfl _ hsmJ hmemJ
  -- the new constant absorbs both `A'` and the exponent `C/2`
  set A : ℝ := max (max A' (C / 2)) 1 with hAdef
  have hAle : A' ≤ A := le_trans (le_max_left _ _) (le_max_left _ _)
  have hCle : C / 2 ≤ A := le_trans (le_max_right _ _) (le_max_left _ _)
  have hAnn : 0 ≤ A := le_trans zero_le_one (le_max_right _ _)
  have hexp_le : Real.exp (C * ε / 2) ≤ Real.exp (A * ε) := by
    refine Real.exp_le_exp.mpr ?_
    rw [show C * ε / 2 = (C / 2) * ε by ring]
    exact mul_le_mul_of_nonneg_right hCle hε.le
  have hmain : Work.Spaces.HkNorm α 6
        (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.Galerkin.slice g s)))
      ≤ A * Real.exp (A * ε) * Work.Spaces.HkNorm α 6 (Work.FTS.Galerkin.slice g s) := by
    calc Work.Spaces.HkNorm α 6
          (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.Galerkin.slice g s)))
        ≤ A' * Work.Spaces.HkNorm α 6
            (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.Galerkin.slice g s)) := hP
      _ ≤ A' * (Real.exp (C * ε / 2)
            * Work.Spaces.HkNorm α 6 (Work.FTS.Galerkin.slice g s)) :=
          mul_le_mul_of_nonneg_left hJ hA'pos.le
      _ = A' * Real.exp (C * ε / 2)
            * Work.Spaces.HkNorm α 6 (Work.FTS.Galerkin.slice g s) := by ring
      _ ≤ A * Real.exp (A * ε) * Work.Spaces.HkNorm α 6 (Work.FTS.Galerkin.slice g s) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hAle hexp_le (Real.exp_pos _).le hAnn)
            (Work.Spaces.HkNorm_nonneg α 6 (Work.FTS.Galerkin.slice g s))
  simpa only [Work.FTS.StrongGlobal.Xn6, Work.FTS.StrongEps.slice_JfamP] using hmain

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv
end
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.E_slots_diff_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.StrongEps.EComparison

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The `ℋ^k`-norm only sees the open quadrant -/

/-- **`HkNorm` is insensitive to changes on the boundary of the quadrant.**  Immediate from
`Work.FTS.EllipticEst.HkSq_congr_open` and the definition `HkNorm = √HkSq`. -/
theorem HkNorm_congr_open (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ) :
    Work.Spaces.HkNorm α k f = Work.Spaces.HkNorm α k g := by
  simp only [Work.Spaces.HkNorm]
  rw [Work.FTS.EllipticEst.HkSq_congr_open α k h]

/-! ## The quadrant form of the slot identity -/

/-- **The slots of two class elements with the same source agree on the open quadrant** — the
packaged form of `EComparison.Slot_eq_of_source` (which is the assembled
`EllPkgCls_sub` + `HomClsSlotsZero`). -/
theorem slots_eq_of_source_quadrant {α Ce : ℝ} {F Ψ₁ Ψ₂ : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (h₁ : EllPkgCls α Ce F Ψ₁) (h₂ : EllPkgCls α Ce F Ψ₂) :
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        SlotR α F Ψ₁ z θ = SlotR α F Ψ₂ z θ) ∧
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        SlotU α F Ψ₁ z θ = SlotU α F Ψ₂ z θ) ∧
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        SlotV α F Ψ₁ z θ = SlotV α F Ψ₂ z θ) := by
  obtain ⟨hR, hU, hV⟩ := Slot_eq_of_source hα hα1 h₁ h₂
  exact ⟨fun z θ hz hθ hθ' => hR z hz θ ⟨hθ, hθ'⟩,
    fun z θ hz hθ hθ' => hU z hz θ ⟨hθ, hθ'⟩,
    fun z θ hz hθ hθ' => hV z hz θ ⟨hθ, hθ'⟩⟩

/-! ## The three Lipschitz slot inputs, from the quadrant slot identity

The shape below is the one the `epsW`-estimates consume: `u`, `v` are two `ClassC` profiles (so
that the difference `u - v` is in the class and `hEll` applies to it), `E u - E v` is in the
packages' class (`EComparison.EllPkgCls_E_sub_of_theta`), and the *quadrant* identity of the slots
of `E u - E v` and `E (u - v)` is what the reduction produces. -/




/-! ## Discharging the slot identity -/

/-- **The `Θ`-additivity needed by `EllPkgCls_E_sub_of_theta`**, from `EComparison.L12_sub_HkMem`
and the definition `Theta α F = (1/(4α)) sin(2θ) L₁₂(F)`. -/
theorem theta_sub_of_classC {α : ℝ} {u v : Fn} (hu : Work.FTS.ClassC.ClassC α u)
    (hv : Work.FTS.ClassC.ClassC α v) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      Work.Construction.Theta α (fun z θ => u z θ - v z θ) z θ
        = Work.Construction.Theta α u z θ - Work.Construction.Theta α v z θ := by
  intro z hz θ
  have hmu : Work.Spaces.HkMem α 4 u :=
    Work.FTS.OpenPkg.HkMem_mono_open hu.reg 4 (by norm_num) hu.mem
  have hmv : Work.Spaces.HkMem α 4 v :=
    Work.FTS.OpenPkg.HkMem_mono_open hv.reg 4 (by norm_num) hv.mem
  have hL := L12_sub_HkMem hu.reg hv.reg hmu hmv z hz
  simp only [Work.Construction.Theta]
  rw [hL]
  ring





end Work.FTS.StrongEps.EComparison
end
end
