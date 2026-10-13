import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Have
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.PhiStar.Psi0Classes
import Submission.Work.FTS.PhiStar.Psi0Ode
import Submission.Work.FTS.PhiStar.Psi0Ident
import Submission.Work.FTS.PhiStar.Psi0Est.AClassDefs
import Submission.Work.FTS.PhiStar.Psi0Est.cVecBound
import Submission.Work.FTS.PhiStar.Psi0Est.fourCosSqBounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Psi0Est

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Differentiation bookkeeping for `dthU` -/

theorem dthU_add_apply' (f g : ℝ → ℝ) (θ : ℝ) (hf : DifferentiableAt ℝ f θ)
    (hg : DifferentiableAt ℝ g θ) :
    Work.Spaces.dthU (f + g) θ = Work.Spaces.dthU f θ + Work.Spaces.dthU g θ := by
  simp only [Work.Spaces.dthU_apply]
  rw [deriv_add hf hg]
  ring

theorem dthU_sum_apply {ι : Type*} (s : Finset ι) (φ : ι → ℝ → ℝ) (θ : ℝ)
    (h : ∀ i ∈ s, DifferentiableAt ℝ (φ i) θ) :
    Work.Spaces.dthU (∑ i ∈ s, φ i) θ = ∑ i ∈ s, Work.Spaces.dthU (φ i) θ := by
  simp only [Work.Spaces.dthU_apply]
  rw [deriv_sum h, Finset.mul_sum]

theorem dthU_four_cos_sq (θ : ℝ) :
    Work.Spaces.dthU (fun θ' : ℝ => 4 * Real.cos θ' ^ 2) θ
      = -16 * Real.sin θ ^ 2 * Real.cos θ ^ 2 := by
  have h : HasDerivAt (fun θ' : ℝ => 4 * Real.cos θ' ^ 2)
      (4 * (2 * Real.cos θ ^ (2 - 1) * (-Real.sin θ))) θ :=
    ((Real.hasDerivAt_cos θ).pow 2).const_mul 4
  rw [Work.Spaces.dthU_apply, h.deriv, Real.sin_two_mul]
  norm_num
  ring

theorem dthU_iter_succ_apply (m : ℕ) (f : ℝ → ℝ) :
    Work.Spaces.dthU^[m + 1] f = Work.Spaces.dthU (Work.Spaces.dthU^[m] f) :=
  Function.iterate_succ_apply' _ _ _

theorem dthU_iter_succ_apply' (m : ℕ) (f : ℝ → ℝ) :
    Work.Spaces.dthU (Work.Spaces.dthU^[m] f) = Work.Spaces.dthU^[m + 1] f :=
  (dthU_iter_succ_apply m f).symm

/-- `dthU`-iterates of a function that is `C^∞` on the open angular interval. -/
theorem contDiffOn_dthU_iter_aux {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ (∞ : ℕ∞ω) f (Set.Ioo 0 (Real.pi / 2))) (m : ℕ) :
    ContDiffOn ℝ (∞ : ℕ∞ω) (Work.Spaces.dthU^[m] f) (Set.Ioo 0 (Real.pi / 2)) := by
  induction m with
  | zero => simpa using hf
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      have hone : (∞ : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω) := by simp
      have hd : ContDiffOn ℝ (∞ : ℕ∞ω) (deriv (Work.Spaces.dthU^[m] f))
          (Set.Ioo 0 (Real.pi / 2)) :=
        ih.deriv_of_isOpen isOpen_Ioo (m := (∞ : ℕ∞ω)) hone
      have hsin : ContDiffOn ℝ (∞ : ℕ∞ω) (fun θ : ℝ => Real.sin (2 * θ))
          (Set.Ioo 0 (Real.pi / 2)) := by fun_prop
      have hfun : Work.Spaces.dthU (Work.Spaces.dthU^[m] f)
          = (fun θ : ℝ => Real.sin (2 * θ)) * deriv (Work.Spaces.dthU^[m] f) := by
        funext θ
        rw [Work.Spaces.dthU_apply]
        rfl
      rw [hfun]
      exact hsin.mul hd

/-- Interior differentiability of the `dthU`-iterates. -/
theorem dthUIter_diffAt_aux {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ (∞ : ℕ∞ω) f (Set.Ioo 0 (Real.pi / 2))) (m : ℕ) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    DifferentiableAt ℝ (Work.Spaces.dthU^[m] f) θ :=
  ((contDiffOn_dthU_iter_aux hf m).contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt
    (by simp)

/-! ## Two elementary index rewritings -/

/-- The `range (j+1)`-shift: the index `r` can be replaced by `r - 1` (with the `r = 0` term
killed), at the cost of the single boundary term `f j`. -/
theorem sum_range_shift (f : ℕ → ℝ) (j : ℕ) :
    (∑ r ∈ Finset.range (j + 1), f r)
      = (∑ r ∈ Finset.range (j + 1), (if r = 0 then 0 else f (r - 1))) + f j := by
  induction j with
  | zero => simp
  | succ j ih =>
      have h1 : (∑ r ∈ Finset.range (j + 1 + 1), f r)
          = (∑ r ∈ Finset.range (j + 1), f r) + f (j + 1) :=
        Finset.sum_range_succ f (j + 1)
      have h2 : (∑ r ∈ Finset.range (j + 1 + 1), (if r = 0 then 0 else f (r - 1)))
          = (∑ r ∈ Finset.range (j + 1), (if r = 0 then 0 else f (r - 1)))
            + (if j + 1 = 0 then 0 else f (j + 1 - 1)) :=
        Finset.sum_range_succ (fun r => if r = 0 then 0 else f (r - 1)) (j + 1)
      rw [h1, ih, h2, if_neg (by omega : ¬ (j + 1 = 0)),
        show (j + 1) - 1 = j from by omega]

/-- Inside the shifted sum the index `(r-1)+1` of `D_θ^·ψ` simplifies to `r`, and the `if` can be
pulled out of the product. -/
theorem cVec_shift_term' (α : ℝ) (j : ℕ) (θ : ℝ) (r : ℕ) :
    (if r = 0 then (0 : ℝ)
        else cVec j (r - 1) θ * (Work.Spaces.dthU^[r - 1 + 1] (psiSol α)) θ)
      = (if r = 0 then 0 else cVec j (r - 1) θ) * (Work.Spaces.dthU^[r] (psiSol α)) θ := by
  by_cases h : r = 0
  · simp [h]
  · rw [if_neg h, if_neg h, show r - 1 + 1 = r from by omega]

/-! ## The identity `D_θ^{j+1}ψ = 4cos²θ·D_θ^j P + ∑_r c_{j,r}·D_θ^rψ` -/

/-- The right-hand side of the `j`-th identity. -/
noncomputable def rhsFun (α : ℝ) (j : ℕ) : ℝ → ℝ :=
  (fun θ : ℝ => 4 * Real.cos θ ^ 2) * (Work.Spaces.dthU^[j] (Pfun α))
    + ∑ r ∈ Finset.range (j + 1), cVec j r * Work.Spaces.dthU^[r] (psiSol α)

theorem A_ident (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) (j : ℕ) :
    Set.EqOn (Work.Spaces.dthU^[j + 1] (psiSol α)) (rhsFun α j)
      (Set.Ioo 0 (Real.pi / 2)) := by
  induction j with
  | zero =>
      intro θ hθ
      have h := dthU_psiSol α hα hα1 hθ
      rw [Function.iterate_one]
      simp only [rhsFun, Pi.mul_apply, Pi.add_apply, Finset.sum_apply,
        show (0 : ℕ) + 1 = 1 from rfl, Finset.sum_range_one, cVec_zero_zero,
        Function.iterate_zero]
      simp only [id_eq]
      linarith [h]
  | succ j ih =>
      intro θ hθ
      have hs : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
      have hPS : ContDiffOn ℝ (∞ : ℕ∞ω) (psiSol α) (Set.Ioo 0 (Real.pi / 2)) :=
        contDiffOn_psiSol α hα hα1
      have hPF : ContDiffOn ℝ (∞ : ℕ∞ω) (Pfun α) (Set.Ioo 0 (Real.pi / 2)) :=
        contDiffOn_Pfun α (le_of_lt hα)
      have hdψ : ∀ r : ℕ, DifferentiableAt ℝ (Work.Spaces.dthU^[r] (psiSol α)) θ :=
        fun r => dthUIter_diffAt_aux hPS r hθ
      have hdP : ∀ r : ℕ, DifferentiableAt ℝ (Work.Spaces.dthU^[r] (Pfun α)) θ :=
        fun r => dthUIter_diffAt_aux hPF r hθ
      have hdc : ∀ r : ℕ, DifferentiableAt ℝ (cVec j r) θ :=
        fun r => IsCoef_differentiableAt (cVec_isCoef j r) θ
      have hd4 : DifferentiableAt ℝ (fun θ : ℝ => 4 * Real.cos θ ^ 2) θ := by fun_prop
      have hih : (Work.Spaces.dthU^[j + 1] (psiSol α)) θ
          = 4 * Real.cos θ ^ 2 * (Work.Spaces.dthU^[j] (Pfun α)) θ
            + ∑ r ∈ Finset.range (j + 1),
                cVec j r θ * (Work.Spaces.dthU^[r] (psiSol α)) θ := by
        have h := ih hθ
        simpa only [rhsFun, Pi.add_apply, Pi.mul_apply, Finset.sum_apply] using h
      have hev : Filter.EventuallyEq (𝓝 θ) (Work.Spaces.dthU^[j + 1] (psiSol α))
          (rhsFun α j) := ih.eventuallyEq_of_mem hs
      rw [Function.iterate_succ_apply']
      have hstep1 : Work.Spaces.dthU (Work.Spaces.dthU^[j + 1] (psiSol α)) θ
          = Work.Spaces.dthU (rhsFun α j) θ := by
        rw [Work.Spaces.dthU_apply, Work.Spaces.dthU_apply, hev.deriv_eq]
      rw [hstep1, rhsFun]
      have hd1 : DifferentiableAt ℝ ((fun θ : ℝ => 4 * Real.cos θ ^ 2)
          * (Work.Spaces.dthU^[j] (Pfun α))) θ := hd4.mul (hdP j)
      have hd2 : ∀ r ∈ Finset.range (j + 1),
          DifferentiableAt ℝ (cVec j r * (Work.Spaces.dthU^[r] (psiSol α))) θ :=
        fun r _ => (hdc r).mul (hdψ r)
      have hd3 : DifferentiableAt ℝ (∑ r ∈ Finset.range (j + 1),
          cVec j r * (Work.Spaces.dthU^[r] (psiSol α))) θ := DifferentiableAt.sum hd2
      rw [dthU_add_apply' _ _ θ hd1 hd3, dthU_sum_apply _ _ θ hd2,
        Work.Spaces.dthU_mul_apply _ _ θ hd4 (hdP j), dthU_four_cos_sq,
        dthU_iter_succ_apply' j (Pfun α)]
      have hterm : ∀ r ∈ Finset.range (j + 1),
          Work.Spaces.dthU (cVec j r * (Work.Spaces.dthU^[r] (psiSol α))) θ
            = Work.Spaces.dthU (cVec j r) θ * (Work.Spaces.dthU^[r] (psiSol α)) θ
              + cVec j r θ * (Work.Spaces.dthU^[r + 1] (psiSol α)) θ := by
        intro r _
        rw [Work.Spaces.dthU_mul_apply _ _ θ (hdc r) (hdψ r),
          dthU_iter_succ_apply' r (psiSol α)]
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
      have hZj : 4 * Real.cos θ ^ 2 * (Work.Spaces.dthU^[j] (Pfun α)) θ
          = (Work.Spaces.dthU^[j + 1] (psiSol α)) θ
            - ∑ r ∈ Finset.range (j + 1),
                cVec j r θ * (Work.Spaces.dthU^[r] (psiSol α)) θ := by
        linarith [hih]
      rw [show (rhsFun α (j + 1)) θ
          = 4 * Real.cos θ ^ 2 * (Work.Spaces.dthU^[j + 1] (Pfun α)) θ
            + ((∑ r ∈ Finset.range (j + 1),
                  cVec (j + 1) r θ * (Work.Spaces.dthU^[r] (psiSol α)) θ)
                + cVec (j + 1) (j + 1) θ * (Work.Spaces.dthU^[j + 1] (psiSol α)) θ) from by
        simp only [rhsFun, Pi.mul_apply, Pi.add_apply, Finset.sum_apply,
          Finset.sum_range_succ]]
      rw [cVec_succ_self j]
      -- lower the `Z_j`-term with the induction hypothesis
      have hZj0 : 4 * Real.cos θ ^ 2 * (Work.Spaces.dthU^[j] (Pfun α)) θ
          = (Work.Spaces.dthU^[j + 1] (psiSol α)) θ
            - ∑ r ∈ Finset.range (j + 1),
                cVec j r θ * (Work.Spaces.dthU^[r] (psiSol α)) θ := by
        linarith [hih]
      have hZj : -16 * Real.sin θ ^ 2 * Real.cos θ ^ 2 * (Work.Spaces.dthU^[j] (Pfun α)) θ
          = -4 * Real.sin θ ^ 2
              * ((Work.Spaces.dthU^[j + 1] (psiSol α)) θ
                - ∑ r ∈ Finset.range (j + 1),
                    cVec j r θ * (Work.Spaces.dthU^[r] (psiSol α)) θ) := by
        linear_combination (-4 * Real.sin θ ^ 2) * hZj0
      -- the shift of the `A_{r+1}`-sum
      have hshift : (∑ r ∈ Finset.range (j + 1),
            cVec j r θ * (Work.Spaces.dthU^[r + 1] (psiSol α)) θ)
          = (∑ r ∈ Finset.range (j + 1),
              (if r = 0 then 0 else cVec j (r - 1) θ)
                * (Work.Spaces.dthU^[r] (psiSol α)) θ)
            + cVec j j θ * (Work.Spaces.dthU^[j + 1] (psiSol α)) θ := by
        rw [sum_range_shift (fun r => cVec j r θ
          * (Work.Spaces.dthU^[r + 1] (psiSol α)) θ) j]
        rw [Finset.sum_congr rfl (fun r _ => cVec_shift_term' α j θ r)]
      -- the recursion, summed over `range (j+1)`
      have hrec : (∑ r ∈ Finset.range (j + 1),
            cVec (j + 1) r θ * (Work.Spaces.dthU^[r] (psiSol α)) θ)
          = (∑ r ∈ Finset.range (j + 1),
              Work.Spaces.dthU (cVec j r) θ * (Work.Spaces.dthU^[r] (psiSol α)) θ)
            + (∑ r ∈ Finset.range (j + 1), 4 * Real.sin θ ^ 2 * cVec j r θ
                * (Work.Spaces.dthU^[r] (psiSol α)) θ)
            + (∑ r ∈ Finset.range (j + 1),
              (if r = 0 then 0 else cVec j (r - 1) θ)
                * (Work.Spaces.dthU^[r] (psiSol α)) θ) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro r hr
        have hr' : r ≠ j + 1 := by
          have := Finset.mem_range.mp hr
          omega
        rcases eq_or_ne r 0 with h0 | h0
        · subst h0
          rw [cVec_succ_zero]
          simp only []
          rw [if_pos trivial]
          ring
        · rw [cVec_succ_of_ne j r hr' h0]
          simp only []
          rw [if_neg h0]
          ring
      -- pulling the constant out of the middle sum
      have hW : (∑ r ∈ Finset.range (j + 1), 4 * Real.sin θ ^ 2 * cVec j r θ
            * (Work.Spaces.dthU^[r] (psiSol α)) θ)
          = 4 * Real.sin θ ^ 2
            * (∑ r ∈ Finset.range (j + 1),
                cVec j r θ * (Work.Spaces.dthU^[r] (psiSol α)) θ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        ring
      rw [hZj, hrec, hshift, hW]
      ring

/-! ## The uniform bound for `ψ` -/

theorem psiSol_bound_aux : ∃ ν0 : ℝ, 0 ≤ ν0 ∧ ∀ α : ℝ, 0 < α → α ≤ 1 / 4 →
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |psiSol α θ| ≤ ν0 * Real.sin (2 * θ) := by
  refine ⟨500 * π, by positivity, fun α hα hα1 θ hθ => ?_⟩
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have hK : |Kc α| ≤ 250 * π := abs_Kc_le α hα hα1
  have hw : |wZer α θ| ≤ 500 * (π / 2) := abs_wZer_le α hα hα1 ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hsum : |Kc α + wZer α θ| ≤ 500 * π := by
    calc |Kc α + wZer α θ| ≤ |Kc α| + |wZer α θ| := abs_add_le _ _
      _ ≤ 250 * π + 500 * (π / 2) := add_le_add hK hw
      _ = 500 * π := by ring
  rw [show psiSol α θ = Real.sin (2 * θ) * (Kc α + wZer α θ) from rfl, abs_mul,
    abs_of_pos hsin]
  calc Real.sin (2 * θ) * |Kc α + wZer α θ| ≤ Real.sin (2 * θ) * (500 * π) :=
        mul_le_mul_of_nonneg_left hsum (le_of_lt hsin)
    _ = (500 * π) * Real.sin (2 * θ) := by ring

noncomputable def nu0c : ℝ := Classical.choose psiSol_bound_aux

theorem nu0c_nonneg : 0 ≤ nu0c := (Classical.choose_spec psiSol_bound_aux).1

theorem psiSol_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    |psiSol α θ| ≤ nu0c * Real.sin (2 * θ) :=
  (Classical.choose_spec psiSol_bound_aux).2 α hα hα1 θ hθ

noncomputable def CPc : ℝ := Classical.choose fourCosSqBounds.1

theorem CPc_spec :
    0 ≤ CPc ∧ ∀ α : ℝ, 0 < α → α ≤ 1 / 4 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      4 * Real.cos θ ^ 2 * |Pfun α θ| ≤ CPc * Real.sin (2 * θ) :=
  Classical.choose_spec fourCosSqBounds.1

noncomputable def cBc : ℕ → ℕ → ℝ := Classical.choose cVecBound

theorem cBc_nonneg (j r : ℕ) : 0 ≤ cBc j r := (Classical.choose_spec cVecBound).1 j r

theorem cBc_spec (j r : ℕ) (θ : ℝ) : |cVec j r θ| ≤ cBc j r :=
  (Classical.choose_spec cVecBound).2 j r θ

/-! ## The constants of the final bound -/

/-- The level-`k` constant multiplying `sin 2θ` in the bound for `4cos²θ·D_θ^k P`. -/
noncomputable def Cf (κ ℓ : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k = 0 then CPc else κ k / 4 + 4 * ℓ k

/-- The geometric factor of the final bound. -/
noncomputable def KK (κ ℓ : ℕ → ℝ) : ℝ :=
  1 + ∑ k ∈ Finset.range 6, ∑ r ∈ Finset.range (k + 1), cBc k r

/-- The base of the final bound `ν j = MM · KK^j`. -/
noncomputable def MM (κ ℓ : ℕ → ℝ) : ℝ :=
  1 + nu0c + ∑ k ∈ Finset.range 6, Cf κ ℓ k

/-- The candidate `ν`-sequence: `ν j = MM · KK^j`. -/
noncomputable def nuFun (κ ℓ : ℕ → ℝ) : ℕ → ℝ := fun j => MM κ ℓ * (KK κ ℓ) ^ j

theorem Cf_nonneg (κ ℓ : ℕ → ℝ) (hκ0 : ∀ j, 0 ≤ κ j) (hℓ0 : ∀ j, 0 ≤ ℓ j) (k : ℕ) :
    0 ≤ Cf κ ℓ k := by
  rcases eq_or_ne k 0 with h | h
  · subst h
    simp only [Cf, if_pos rfl]
    exact CPc_spec.1
  · simp only [Cf, if_neg h]
    have h1 := hκ0 k
    have h2 := hℓ0 k
    linarith

theorem KK_ge_one (κ ℓ : ℕ → ℝ) : 1 ≤ KK κ ℓ := by
  have : 0 ≤ ∑ k ∈ Finset.range 6, ∑ r ∈ Finset.range (k + 1), cBc k r :=
    Finset.sum_nonneg (fun k _ => Finset.sum_nonneg (fun r _ => cBc_nonneg k r))
  simp only [KK]
  linarith

theorem MM_ge_one (κ ℓ : ℕ → ℝ) (hκ0 : ∀ j, 0 ≤ κ j) (hℓ0 : ∀ j, 0 ≤ ℓ j) :
    1 ≤ MM κ ℓ := by
  have h1 : 0 ≤ nu0c := nu0c_nonneg
  have h2 : 0 ≤ ∑ k ∈ Finset.range 6, Cf κ ℓ k :=
    Finset.sum_nonneg (fun k _ => Cf_nonneg κ ℓ hκ0 hℓ0 k)
  simp only [MM]
  linarith

theorem MM_nonneg (κ ℓ : ℕ → ℝ) (hκ0 : ∀ j, 0 ≤ κ j) (hℓ0 : ∀ j, 0 ≤ ℓ j) :
    0 ≤ MM κ ℓ := le_trans (by norm_num) (MM_ge_one κ ℓ hκ0 hℓ0)

/-- `Cf k ≤ MM` for `k ≤ 5`. -/
theorem Cf_le_MM (κ ℓ : ℕ → ℝ) (hκ0 : ∀ j, 0 ≤ κ j) (hℓ0 : ∀ j, 0 ≤ ℓ j)
    {k : ℕ} (hk : k ≤ 5) : Cf κ ℓ k ≤ MM κ ℓ := by
  have hmem : k ∈ Finset.range 6 := Finset.mem_range.mpr (by omega)
  have h1 : Cf κ ℓ k ≤ ∑ i ∈ Finset.range 6, Cf κ ℓ i :=
    Finset.single_le_sum (fun i _ => Cf_nonneg κ ℓ hκ0 hℓ0 i) hmem
  have h2 : 0 ≤ nu0c := nu0c_nonneg
  simp only [MM]
  linarith

/-- `∑_{r ≤ j} cBc j r ≤ KK - 1` for `j ≤ 5`. -/
theorem sum_cBc_le (κ ℓ : ℕ → ℝ) {j : ℕ} (hj : j ≤ 5) :
    (∑ r ∈ Finset.range (j + 1), cBc j r) ≤ KK κ ℓ - 1 := by
  have hmem : j ∈ Finset.range 6 := Finset.mem_range.mpr (by omega)
  have hnonneg : ∀ k ∈ Finset.range 6, 0 ≤ ∑ r ∈ Finset.range (k + 1), cBc k r :=
    fun k _ => Finset.sum_nonneg (fun r _ => cBc_nonneg k r)
  have h1 : (∑ r ∈ Finset.range (j + 1), cBc j r)
      ≤ ∑ k ∈ Finset.range 6, ∑ r ∈ Finset.range (k + 1), cBc k r :=
    Finset.single_le_sum hnonneg hmem
  simp only [KK]
  linarith

/-- The `Z`-bound: `|4cos²θ·D_θ^k P| ≤ Cf k · sin 2θ` for `k ≤ 5`. -/
theorem Z_bound (κ ℓ : ℕ → ℝ) (hZ : ZClass κ ℓ) {k : ℕ} (hk : k ≤ 5) (α : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    |4 * Real.cos θ ^ 2 * Work.Spaces.dthU^[k] (Pfun α) θ| ≤ Cf κ ℓ k * Real.sin (2 * θ) := by
  obtain ⟨hκ0, hℓ0, hZb⟩ := hZ
  rcases eq_or_ne k 0 with h0 | h0
  · subst h0
    have hCf0 : Cf κ ℓ 0 = CPc := by simp only [Cf, ↓reduceIte]
    have habs : |4 * Real.cos θ ^ 2 * (Work.Spaces.dthU^[0] (Pfun α)) θ|
        = 4 * Real.cos θ ^ 2 * |Pfun α θ| := by
      simp only [Function.iterate_zero, id_eq]
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
        abs_of_nonneg (sq_nonneg (Real.cos θ))]
    rw [habs, hCf0]
    exact CPc_spec.2 α hα hα1 θ hθ
  · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr h0
    have hCfn : Cf κ ℓ k = κ k / 4 + 4 * ℓ k := by simp only [Cf, h0, ↓reduceIte]
    have habs : |4 * Real.cos θ ^ 2 * (Work.Spaces.dthU^[k] (Pfun α)) θ|
        = 4 * Real.cos θ ^ 2 * |Work.Spaces.dthU^[k] (Pfun α) θ| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
        abs_of_nonneg (sq_nonneg (Real.cos θ))]
    rw [habs, hCfn]
    exact fourCosSqBounds.2 k hk1 hk κ ℓ ⟨hκ0, hℓ0, hZb⟩ α hα hα1 θ hθ

theorem exists_AClass (hZ : ∃ κ ell : ℕ → ℝ, ZClass κ ell) : ∃ ν : ℕ → ℝ, AClass ν := by
  obtain ⟨κ, ℓ, hκ0, hℓ0, hZb⟩ := hZ
  have hZ : ZClass κ ℓ := ⟨hκ0, hℓ0, hZb⟩
  refine ⟨nuFun κ ℓ, ?_, ?_⟩
  · intro j
    exact mul_nonneg (MM_nonneg κ ℓ hκ0 hℓ0) (pow_nonneg (le_trans (by norm_num) (KK_ge_one κ ℓ)) j)
  · intro α hα hα1 j hj6 θ hθ
    have hsin : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
    have hMnn : 0 ≤ MM κ ℓ := MM_nonneg κ ℓ hκ0 hℓ0
    have hK1 : 1 ≤ KK κ ℓ := KK_ge_one κ ℓ
    have hKnn : 0 ≤ KK κ ℓ := le_trans (by norm_num) hK1
    -- strong induction on the level
    have hA : ∀ N ≤ 6, ∀ j ≤ N,
        |Work.Spaces.dthU^[j] (psiSol α) θ| ≤ nuFun κ ℓ j * Real.sin (2 * θ) := by
      intro N hN
      induction N with
      | zero =>
          intro j hj
          have hj0 : j = 0 := by omega
          subst hj0
          have h1 := psiSol_le α hα hα1 hθ
          have h2 : nu0c ≤ MM κ ℓ := by
            have h3 : 0 ≤ ∑ k ∈ Finset.range 6, Cf κ ℓ k :=
              Finset.sum_nonneg (fun k _ => Cf_nonneg κ ℓ hκ0 hℓ0 k)
            simp only [MM]
            linarith
          simpa only [Function.iterate_zero, id_eq, nuFun, pow_zero, mul_one] using
            le_trans h1 (mul_le_mul_of_nonneg_right h2 (le_of_lt hsin))
      | succ N ih =>
          intro j hj
          rcases Nat.lt_or_eq_of_le hj with hlt | heq
          · exact ih (by omega) j (by omega)
          · subst heq
            have hN5 : N ≤ 5 := by omega
            have hid := A_ident α hα hα1 N hθ
            rw [hid]
            simp only [rhsFun, Pi.add_apply, Pi.mul_apply, Finset.sum_apply]
            have hZbN : |4 * Real.cos θ ^ 2 * (Work.Spaces.dthU^[N] (Pfun α)) θ|
                ≤ Cf κ ℓ N * Real.sin (2 * θ) := Z_bound κ ℓ hZ hN5 α hα hα1 hθ
            have hsum : |∑ r ∈ Finset.range (N + 1),
                  cVec N r θ * (Work.Spaces.dthU^[r] (psiSol α)) θ|
                ≤ (∑ r ∈ Finset.range (N + 1), cBc N r * (MM κ ℓ * (KK κ ℓ) ^ N))
                  * Real.sin (2 * θ) := by
              refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
              rw [Finset.sum_mul]
              apply Finset.sum_le_sum
              intro r hr
              have hrN : r ≤ N := by simpa using Finset.mem_range.mp hr
              have h1 : |cVec N r θ| ≤ cBc N r := cBc_spec N r θ
              have h2 : |Work.Spaces.dthU^[r] (psiSol α) θ| ≤ nuFun κ ℓ r * Real.sin (2 * θ) :=
                ih (by omega) r hrN
              have h3 : nuFun κ ℓ r * Real.sin (2 * θ)
                  ≤ (MM κ ℓ * (KK κ ℓ) ^ N) * Real.sin (2 * θ) := by
                apply mul_le_mul_of_nonneg_right _ (le_of_lt hsin)
                have := pow_le_pow_right₀ hK1 hrN
                simpa only [nuFun] using mul_le_mul_of_nonneg_left this hMnn
              calc |cVec N r θ * (Work.Spaces.dthU^[r] (psiSol α)) θ|
                  = |cVec N r θ| * |Work.Spaces.dthU^[r] (psiSol α) θ| := abs_mul _ _
                _ ≤ cBc N r * (nuFun κ ℓ r * Real.sin (2 * θ)) :=
                    mul_le_mul h1 h2 (abs_nonneg _) (cBc_nonneg N r)
                _ ≤ cBc N r * ((MM κ ℓ * (KK κ ℓ) ^ N) * Real.sin (2 * θ)) :=
                    mul_le_mul_of_nonneg_left h3 (cBc_nonneg N r)
                _ = cBc N r * (MM κ ℓ * (KK κ ℓ) ^ N) * Real.sin (2 * θ) := by ring
            have hsum2 : (∑ r ∈ Finset.range (N + 1), cBc N r * (MM κ ℓ * (KK κ ℓ) ^ N))
                ≤ (KK κ ℓ - 1) * (MM κ ℓ * (KK κ ℓ) ^ N) := by
              rw [← Finset.sum_mul]
              exact mul_le_mul_of_nonneg_right (sum_cBc_le κ ℓ hN5)
                (mul_nonneg hMnn (pow_nonneg hKnn N))
            refine le_trans (abs_add_le _ _) ?_
            refine le_trans (add_le_add hZbN hsum) ?_
            refine le_trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hsum2 (le_of_lt hsin))) ?_
            rw [← add_mul, nuFun, pow_succ]
            apply mul_le_mul_of_nonneg_right _ (le_of_lt hsin)
            have hCf : Cf κ ℓ N ≤ MM κ ℓ := Cf_le_MM κ ℓ hκ0 hℓ0 hN5
            have hM1 : MM κ ℓ ≤ MM κ ℓ * (KK κ ℓ) ^ N :=
              le_mul_of_one_le_right hMnn (one_le_pow₀ hK1)
            nlinarith [hCf, hM1, hMnn]
    exact hA j hj6 j le_rfl

end Work.FTS.PhiStar.Psi0Est
