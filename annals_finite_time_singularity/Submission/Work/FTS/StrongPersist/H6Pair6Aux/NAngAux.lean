import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12FieldsAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.SepMem6Local
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.RadialSlots
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.FstarJet7
import Submission.Work.FTS.StrongPersist.RMul6.Defs
import Submission.Work.FTS.LocData.DthIter_Gam_abs_le
import Submission.Work.FTS.PhiStar.StarPkgo2Aux.CoeffF0
import Submission.Work.Spaces.DzIter_le_of_pzIter
import Submission.Work.FTS.StrongPersist.W6.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- The first iterate of `dthU` is `dthU` itself. -/
theorem dthU_one (g : ℝ → ℝ) : (Work.Spaces.dthU^[1]) g = Work.Spaces.dthU g := rfl

/-! ## The angular identity `sin(2θ)·∂_θΓ = α·q·Γ` on `Iθ` -/

theorem s2_deriv_Gam_Iθ (α : ℝ) (hα : 0 < α) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ
      = α * Work.Spaces.qfun θ * Work.Spaces.Gam α θ := by
  have hGam0 : Work.Spaces.Gam α 0 = 0 := by
    have h : Real.sin 0 * Real.cos 0 ^ 2 = (0 : ℝ) := by norm_num
    rw [Work.Spaces.Gam, h]
    exact Real.zero_rpow (by positivity : α / 3 ≠ 0)
  have hGam1 : Work.Spaces.Gam α (Real.pi / 2) = 0 := by
    have h : Real.sin (Real.pi / 2) * Real.cos (Real.pi / 2) ^ 2 = (0 : ℝ) := by
      rw [Real.cos_pi_div_two]; ring
    rw [Work.Spaces.Gam, h]
    exact Real.zero_rpow (by positivity : α / 3 ≠ 0)
  rcases lt_or_eq_of_le hθ.1 with h0 | h0
  · rcases lt_or_eq_of_le hθ.2 with h1 | h1
    · have h := Work.Spaces.dthU_Gam α θ hα ⟨h0, h1⟩
      rw [Work.Spaces.dthU_apply] at h
      exact h
    · subst h1
      rw [show Real.sin (2 * (Real.pi / 2)) = 0 by
        rw [show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring, Real.sin_pi], hGam1]
      ring
  · subst h0
    rw [show Real.sin (2 * 0) = 0 by rw [mul_zero, Real.sin_zero], hGam0]
    ring

/-! ## The jet bound for the angular profile `q·Γ` -/

/-- The threshold constant of the jet bound. -/
noncomputable def gamqK : ℝ := 4 / 3 + (Work.Spaces.tBound 6 0 + 1)
  + (Work.Spaces.tBound 0 0 + Work.Spaces.tBound 1 0 + Work.Spaces.tBound 2 0
    + Work.Spaces.tBound 3 0 + Work.Spaces.tBound 4 0 + Work.Spaces.tBound 5 0)

theorem gamqK_nonneg : 0 ≤ gamqK := by
  have h := Work.Spaces.tBound_nonneg
  rw [gamqK]
  linarith [h 0 0, h 1 0, h 2 0, h 3 0, h 4 0, h 5 0, h 6 0]

theorem GamQfun_dthU_Iθ (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ i : ℕ, i ≤ 6 → ∀ θ ∈ Work.Spaces.Iθ,
      |(Work.Spaces.dthU^[i]) (fun t => Work.Spaces.Gam α t * Work.Spaces.qfun t) θ|
        ≤ gamqK * Work.Spaces.Gam α θ := by
  intro i hi θ hθ
  have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  have hle : ∀ j : ℕ, j ≤ 6 → Work.Spaces.tBound j 0 ≤ gamqK := by
    intro j hj
    have h := Work.Spaces.tBound_nonneg
    interval_cases j <;> rw [gamqK] <;>
      linarith [h 0 0, h 1 0, h 2 0, h 3 0, h 4 0, h 5 0, h 6 0]
  by_cases h0i : i = 0
  · subst h0i
    simp only [Function.iterate_zero_apply]
    rw [abs_mul]
    have hq : |Work.Spaces.qfun θ| ≤ 4 / 3 := by
      rw [Work.Spaces.qfun, abs_le]
      constructor <;> linarith [Real.neg_one_le_cos (2 * θ), Real.cos_le_one (2 * θ)]
    have hK : (4 / 3 : ℝ) ≤ gamqK := by
      have h := Work.Spaces.tBound_nonneg
      rw [gamqK]; linarith [h 0 0, h 1 0, h 2 0, h 3 0, h 4 0, h 5 0, h 6 0]
    calc |Work.Spaces.Gam α θ| * |Work.Spaces.qfun θ|
        ≤ Work.Spaces.Gam α θ * (4 / 3) := by
          rw [abs_of_nonneg hG0]
          exact mul_le_mul_of_nonneg_left hq hG0
      _ = (4 / 3) * Work.Spaces.Gam α θ := by ring
      _ ≤ gamqK * Work.Spaces.Gam α θ := mul_le_mul_of_nonneg_right hK hG0
  · have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr h0i
    by_cases hθi : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
    · -- interior: `dthU^i (q·Γ) = Γ·Tfun i`
      have hcongr : (fun t => Work.Spaces.Gam α t * Work.Spaces.qfun t)
          = fun t => Work.Spaces.Gam α t * Work.Spaces.qfun t := by
        funext t; ring
      have hEq : ∀ j : ℕ, (Work.Spaces.dthU^[j])
            (fun t => Work.Spaces.Gam α t * Work.Spaces.qfun t) θ
          = Work.Spaces.Gam α θ * Work.Spaces.Tfun j α θ := by
        intro j
        rw [hcongr]
        exact Work.FTS.Nonlinear.Pieces.dthU_iter_Gam_mul_qfun j α hα hθi
      rcases eq_or_lt_of_le hi with h6 | h6
      · -- `i = 6`
        subst h6
        have hEq5 : (Work.Spaces.dthU^[5]) (fun t => Work.Spaces.Gam α t * Work.Spaces.qfun t)
            =ᶠ[𝓝 θ] fun t => Work.Spaces.Gam α t * Work.Spaces.Tfun 5 α t :=
          (Work.FTS.Nonlinear.Pieces.dthU_iter_Gam_mul_qfun 5 α hα).eventuallyEq_of_mem
            (IsOpen.mem_nhds isOpen_Ioo hθi)
        have hGd : DifferentiableAt ℝ (fun t => Work.Spaces.Gam α t) θ :=
          Work.Spaces.Gam_differentiableAt α θ hθi.1 hθi.2
        have hTd : DifferentiableAt ℝ (Work.Spaces.Tfun 5 α) θ :=
          ((Work.Spaces.Tfun_smooth 5 α).differentiable (by simp)).differentiableAt
        have h6eq : (Work.Spaces.dthU^[6]) (fun t => Work.Spaces.Gam α t * Work.Spaces.qfun t) θ
            = Work.Spaces.Gam α θ * Work.Spaces.Tfun 6 α θ := by
          rw [show (6 : ℕ) = 5 + 1 from rfl, Function.iterate_succ_apply']
          have hd : Work.Spaces.dthU ((Work.Spaces.dthU^[5])
                (fun t => Work.Spaces.Gam α t * Work.Spaces.qfun t)) θ
              = Work.Spaces.dthU (fun t => Work.Spaces.Gam α t * Work.Spaces.Tfun 5 α t) θ := by
            rw [Work.Spaces.dthU_apply, Work.Spaces.dthU_apply, hEq5.deriv_eq]
          have hkey : Real.sin (2 * θ) * deriv (fun t => Work.Spaces.Gam α t) θ
              = α * Work.Spaces.qfun θ * Work.Spaces.Gam α θ :=
            s2_deriv_Gam_Iθ α hα ⟨le_of_lt hθi.1, le_of_lt hθi.2⟩
          rw [hd, Work.Spaces.dthU_apply,
            show (fun t => Work.Spaces.Gam α t * Work.Spaces.Tfun 5 α t)
              = (fun t => Work.Spaces.Gam α t) * (Work.Spaces.Tfun 5 α) from rfl,
            deriv_mul hGd hTd]
          have hT6 : (Work.Spaces.Tfun 6 α θ : ℝ) = Real.sin (2 * θ)
                * deriv (fun t => Work.Spaces.Tfun 5 α t) θ + α * Work.Spaces.qfun θ
                * Work.Spaces.Tfun 5 α θ := Work.Spaces.Tfun_succ 5 α θ
          rw [show Real.sin (2 * θ) * (deriv (fun t => Work.Spaces.Gam α t) θ
                * Work.Spaces.Tfun 5 α θ
                + Work.Spaces.Gam α θ * deriv (Work.Spaces.Tfun 5 α) θ)
              = (Real.sin (2 * θ) * deriv (fun t => Work.Spaces.Gam α t) θ)
                  * Work.Spaces.Tfun 5 α θ
                + (Real.sin (2 * θ) * deriv (Work.Spaces.Tfun 5 α) θ)
                  * Work.Spaces.Gam α θ from by ring,
            hkey, hT6]
          ring
        rw [h6eq, abs_mul, abs_of_nonneg hG0]
        have hT6 : |Work.Spaces.Tfun 6 α θ| ≤ Work.Spaces.tBound 6 0 :=
          Work.Spaces.dthU_iter_Tfun_le 6 α hα hα1 θ ⟨le_of_lt hθi.1, le_of_lt hθi.2⟩ 0
        calc Work.Spaces.Gam α θ * |Work.Spaces.Tfun 6 α θ|
            ≤ Work.Spaces.Gam α θ * Work.Spaces.tBound 6 0 :=
              mul_le_mul_of_nonneg_left hT6 hG0
          _ ≤ gamqK * Work.Spaces.Gam α θ := by
              rw [mul_comm (Work.Spaces.Gam α θ) (Work.Spaces.tBound 6 0)]
              exact mul_le_mul_of_nonneg_right (hle 6 le_rfl) hG0
      · -- `i ≤ 5`
        rw [hEq i, abs_mul, abs_of_nonneg hG0]
        have hT : |Work.Spaces.Tfun i α θ| ≤ Work.Spaces.tBound i 0 :=
          Work.Spaces.dthU_iter_Tfun_le i α hα hα1 θ ⟨le_of_lt hθi.1, le_of_lt hθi.2⟩ 0
        calc Work.Spaces.Gam α θ * |Work.Spaces.Tfun i α θ|
            ≤ Work.Spaces.Gam α θ * Work.Spaces.tBound i 0 :=
              mul_le_mul_of_nonneg_left hT hG0
          _ ≤ gamqK * Work.Spaces.Gam α θ := by
              rw [mul_comm (Work.Spaces.Gam α θ) (Work.Spaces.tBound i 0)]
              exact mul_le_mul_of_nonneg_right (hle i (by omega)) hG0
    · -- endpoints: `dthU^i` vanishes
      have hsin : Real.sin (2 * θ) = 0 := by
        rcases eq_or_lt_of_le hθ.1 with hh | hh
        · rw [← hh, mul_zero, Real.sin_zero]
        · have hh2 : θ = Real.pi / 2 := by
            by_contra hc
            exact hθi ⟨hh, lt_of_le_of_ne hθ.2 hc⟩
          rw [hh2, show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
      rw [show i = i - 1 + 1 from by omega, Function.iterate_succ_apply']
      have hz : Work.Spaces.dthU ((Work.Spaces.dthU^[i - 1])
          (fun t => Work.Spaces.Gam α t * Work.Spaces.qfun t)) θ = 0 := by
        rw [Work.Spaces.dthU_apply, hsin]
        ring
      rw [hz, abs_zero]
      exact mul_nonneg gamqK_nonneg hG0

/-- The angular identity `pth(F_*) = α·(Γ'/c)·φ` on the open quadrant. -/
theorem pth_Fstar_eq (α z θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.pth (Work.Construction.Fstar α) z θ
      = α * (deriv (Work.Spaces.Gam α) θ / Work.Spaces.c α) * Work.FM.Fstar z := by
  have hd : DifferentiableAt ℝ (Work.Spaces.Gam α) θ :=
    Work.Spaces.Gam_differentiableAt α θ hθ.1 hθ.2
  have hfun : (fun θ' => Work.Construction.Fstar α z θ')
      = fun θ' => (α * (Work.Spaces.c α)⁻¹ * Work.FM.Fstar z) * Work.Spaces.Gam α θ' := by
    funext θ'
    rw [Work.Construction.Fstar, div_eq_mul_inv]
    ring
  rw [Work.Spaces.pth, hfun, deriv_const_mul _ hd]
  ring

/-- `D_z(F_*) = α·(Γ/c)·D_zφ` on `z > 0`. -/
theorem Dz_Fstar_eq (α z θ : ℝ) (hz : 0 < z) :
    Work.Spaces.Dz (Work.Construction.Fstar α) z θ
      = α * (Work.Spaces.Gam α θ / Work.Spaces.c α)
        * Work.Elliptic.DzdIter 1 Work.FM.Fstar z := by
  have hd : DifferentiableAt ℝ Work.FM.Fstar z := by
    show DifferentiableAt ℝ (fun z : ℝ => 2 * z / (1 + z) ^ 2) z
    exact ((differentiableAt_const (2 : ℝ)).mul differentiableAt_id).div
      (((differentiableAt_const (1 : ℝ)).add differentiableAt_id).pow 2) (by positivity)
  have hfun : (fun z' => Work.Construction.Fstar α z' θ)
      = fun z' => (α * (Work.Spaces.Gam α θ * (Work.Spaces.c α)⁻¹)) * Work.FM.Fstar z' := by
    funext z'
    rw [Work.Construction.Fstar, div_eq_mul_inv]
  have hL : Work.Spaces.Dz (Work.Construction.Fstar α) z θ
      = α * (Work.Spaces.c α)⁻¹ * (z * (Work.Spaces.Gam α θ * deriv Work.FM.Fstar z)) := by
    rw [Work.Spaces.Dz, Work.Spaces.pz, hfun, deriv_const_mul _ hd]
    ring
  rw [hL]
  rw [show Work.Elliptic.DzdIter 1 Work.FM.Fstar z = z * deriv Work.FM.Fstar z from rfl]
  rw [div_eq_mul_inv]
  ring

/-- At the endpoints of `Iθ` (i.e. outside the open interval) `sin(2θ)` vanishes. -/
theorem sin_two_zero_of_not_Ioo {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (h : θ ∉ Set.Ioo (0 : ℝ) (Real.pi / 2)) : Real.sin (2 * θ) = 0 := by
  rcases eq_or_lt_of_le hθ.1 with hh | hh
  · rw [← hh, mul_zero, Real.sin_zero]
  · have hh2 : θ = Real.pi / 2 := by
      by_contra hc
      exact h ⟨hh, lt_of_le_of_ne hθ.2 hc⟩
    rw [hh2, show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]

/-- At the endpoints of `Iθ` the weight `Γ` vanishes. -/
theorem Gam_zero_of_not_Ioo {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ)
    (h : θ ∉ Set.Ioo (0 : ℝ) (Real.pi / 2)) : Work.Spaces.Gam α θ = 0 := by
  have hbase : Real.sin θ * Real.cos θ ^ 2 = (0 : ℝ) := by
    rcases eq_or_lt_of_le hθ.1 with hh | hh
    · rw [← hh, Real.sin_zero]; ring
    · have hh2 : θ = Real.pi / 2 := by
        by_contra hc
        exact h ⟨hh, lt_of_le_of_ne hθ.2 hc⟩
      rw [hh2, Real.cos_pi_div_two]; ring
  rw [Work.Spaces.Gam, hbase]
  exact Real.zero_rpow (by positivity : α / 3 ≠ 0)

/-- Linearity of the iterate `DzdIter` under multiplication by a constant. -/
theorem dzdIter_const_mul (c : ℝ) (f : ℝ → ℝ) (n : ℕ) :
    Work.Elliptic.DzdIter n (fun z => c * f z) = fun z => c * Work.Elliptic.DzdIter n f z := by
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [Work.Elliptic.DzdIter_succ, ih, Work.Elliptic.DzdIter_succ]
      funext z
      show z * deriv (fun z' => c * Work.Elliptic.DzdIter k f z') z
        = c * (z * deriv (Work.Elliptic.DzdIter k f) z)
      rw [deriv_const_mul_field]
      ring

/-- The one-variable `DzdIter` is the slice of the two-variable `DzIter`. -/
theorem dzdIter_eq_DzIter (f : ℝ → ℝ) (n : ℕ) (z : ℝ) :
    Work.Elliptic.DzdIter n f z = Work.Spaces.DzIter n (fun z _ => f z) z 0 := by
  induction n generalizing z with
  | zero => rfl
  | succ k ih =>
      rw [Work.Elliptic.DzdIter_succ, Work.Spaces.DzIter_succ]
      show z * deriv (Work.Elliptic.DzdIter k f) z
        = z * deriv (fun z' => Work.Spaces.DzIter k (fun z _ => f z) z' 0) z
      have h : Work.Elliptic.DzdIter k f
          = fun z' => Work.Spaces.DzIter k (fun z _ => f z) z' 0 := funext fun z' => ih z'
      rw [h]

/-- The `z`-jets of the bounded radial function `z ↦ 2α/(1+z)`. -/
theorem inv_one_add_jets (α : ℝ) (hα : 0 < α) :
    ∀ b : ℕ, b ≤ 6 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter b (fun z => 2 * α / (1 + z)) z| ≤ 2 * α * (250 * 720) := by
  intro b hb z hz
  have hz1 : (-1 : ℝ) < z := by linarith
  have hs : ∀ θ ∈ Work.Spaces.Iθ,
      ContDiffOn ℝ ⊤ (fun z : ℝ => (1 + z)⁻¹) (Set.Ioi (-1)) := by
    intro θ hθ
    refine ContDiffOn.inv (contDiffOn_const.add contDiffOn_id) ?_
    intro z hz'
    have : (-1 : ℝ) < z := hz'
    linarith
  -- the slot bounds
  have hslot : ∀ k : ℕ, k ≤ b → |z ^ k * Work.Spaces.pzIter k
      (fun z (_ : ℝ) => (1 + z)⁻¹) z 0| ≤ 720 := by
    intro k hk
    rw [Work.Spaces.pzIter_eq_iteratedDeriv]
    rw [Work.FTS.PhiStar.StarPkgo2Aux.iteratedDeriv_inv_one_add k z hz1]
    have hprod : |z ^ k * ((1 + z)⁻¹) ^ (k + 1)| ≤ 1 := by
      rw [abs_of_nonneg (by positivity)]
      have hratio : z / (1 + z) ≤ 1 := by
        rw [div_le_one (by linarith)]; linarith
      have hratio0 : 0 ≤ z / (1 + z) := by positivity
      have hinv : (1 + z)⁻¹ ≤ 1 := by
        rw [inv_le_one₀ (by linarith)]; linarith
      have hk1 : (z / (1 + z)) ^ k ≤ 1 := pow_le_one₀ hratio0 hratio
      have heq : z ^ k * ((1 + z)⁻¹) ^ (k + 1) = (z / (1 + z)) ^ k * (1 + z)⁻¹ := by
        rw [pow_succ, inv_pow, div_pow, div_eq_mul_inv]
        ring
      rw [heq]
      calc (z / (1 + z)) ^ k * (1 + z)⁻¹ ≤ 1 * 1 :=
            mul_le_mul hk1 hinv (by positivity) (by norm_num)
        _ = 1 := by ring
    have hfac : |(k.factorial : ℝ)| ≤ 720 := by
      rw [abs_of_nonneg (Nat.cast_nonneg k.factorial)]
      exact_mod_cast Nat.factorial_le (by omega : k ≤ 6)
    have hneg : |((-1 : ℝ) ^ k)| = 1 := by rw [abs_pow]; simp
    have hrearr : z ^ k * ((-1 : ℝ) ^ k * (k.factorial : ℝ) * ((1 + z)⁻¹) ^ (k + 1))
        = ((-1 : ℝ) ^ k * (k.factorial : ℝ)) * (z ^ k * ((1 + z)⁻¹) ^ (k + 1)) := by ring
    rw [hrearr, abs_mul, abs_mul, hneg, one_mul]
    calc |(k.factorial : ℝ)| * |z ^ k * ((1 + z)⁻¹) ^ (k + 1)| ≤ 720 * 1 :=
          mul_le_mul hfac hprod (abs_nonneg _) (by norm_num)
      _ = 720 := by ring
  have hexp := Work.Spaces.DzIter_eq_sum_scoef (h := fun z (_ : ℝ) => (1 + z)⁻¹) hs
    b z (Set.mem_Ioi.mpr hz1) 0 ⟨le_refl 0, by positivity⟩
  have hbound := Work.Spaces.abs_sum_scoef_mul_le b 720
    (fun k => z ^ k * Work.Spaces.pzIter k (fun z (_ : ℝ) => (1 + z)⁻¹) z 0)
    (fun k hk => hslot k (by omega))
  have hbell : (Work.Spaces.bell b : ℝ) ≤ 250 := by
    exact_mod_cast Work.FTS.StrongPersist.W6.bell_le_six hb
  have h1 : |Work.Elliptic.DzdIter b (fun z => (1 + z)⁻¹) z| ≤ 250 * 720 := by
    rw [dzdIter_eq_DzIter]
    rw [hexp]
    calc |∑ k ∈ Finset.range (b + 1), (Work.Spaces.scoef b k : ℝ)
          * (z ^ k * Work.Spaces.pzIter k (fun z (_ : ℝ) => (1 + z)⁻¹) z 0)|
        ≤ (Work.Spaces.bell b : ℝ) * 720 := hbound
      _ ≤ 250 * 720 := mul_le_mul_of_nonneg_right hbell (by norm_num)
  have hfun : (fun z : ℝ => 2 * α / (1 + z)) = fun z => 2 * α * (1 + z)⁻¹ := by
    funext z; rw [div_eq_mul_inv]
  rw [hfun, dzdIter_const_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * α)]
  calc (2 * α) * |Work.Elliptic.DzdIter b (fun z => (1 + z)⁻¹) z|
      ≤ (2 * α) * (250 * 720) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 2 * α * (250 * 720) := by ring

end Work.FTS.StrongPersist.H6Pair6Aux
