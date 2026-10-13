/-
Copyright: work module for the Elgindi finite-time singularity project.

# Auxiliary definitions and measure theory for the certificate `HkMem (D_z Ψ)`

This module collects (a) the six terms into which the `ℋ^k`-integrand of `D_z Ψ` is split,

* `PR, ZR` — the two *input* terms (the radial summands at index `k` of `HkIntegrand α k Ψ`
  and of `HkIntegrand α k (z²∂_z²Ψ)`),
* `PM, ZM` — the two input terms of mixed type (the mixed summands at index `(1, k-1)` of the
  same two integrands),
* `EXR, EXM` — the two *excess* terms (the radial summand at index `k+1` of `HkIntegrand α k Ψ`
  and the mixed summand `D_z^kD_θΨ` at index `(1,k-1)` of `HkIntegrand α k (D_z Ψ)`),

and (b) the measure theory that extracts, from an honesty hypothesis `HkMem α k F`, the four
facts about a summand `T ≤ HkIntegrand α k F` used below: the `θ`-slice integrability for every
`z`, the `z`-integrability of the slice integrals, the `z`-integrability of the `θ`-slice for
a.e. `θ`, and the finiteness of `∫⁻_θ ofReal(∫_z T)` (`summand_props`), together with the
operator identities (`z²∂_z²` commutes with `D_z` and `D_θ`, `rDzIter 2 - rDzIter 1 = z²∂_z²`
on the slices) that connect the one-variable `rDz`-form of the Agmon lemma
`Work.FTS.EllipticEst.Cert.rDz_AMGM_diff` with these terms.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.DzCalc
import Submission.Work.FTS.H2.T2Aesm
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.HardyZ
import Submission.Work.Spaces.DzIter_le_of_pzIter
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.Spaces.continuousOn_HkIntegrand_Qd
import Submission.Work.Spaces.HProductRule_Zsummand
import Submission.Work.Spaces.aesm_mixed_Wt_sq_prod
import Submission.Work.Spaces.bt_aux
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.FTS.EllipticEst.GbarSetup
import Submission.Work.FTS.EllipticEst.mul_w_sin_rpow_sq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cert.DzAux

/-! ## The six terms -/

/-- The radial summand at index `k` of `HkIntegrand α k Ψ`. -/
def PR (Ψ : ℝ → ℝ → ℝ) (k : ℕ) : ℝ → ℝ → ℝ :=
  fun z θ => (Work.Spaces.DzIter k Ψ z θ
    * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2

/-- The radial summand at index `k` of `HkIntegrand α k (z²∂_z²Ψ)`. -/
def ZR (Ψ : ℝ → ℝ → ℝ) (k : ℕ) : ℝ → ℝ → ℝ :=
  fun z θ => (Work.Spaces.DzIter k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
    * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2

/-- The mixed summand at index `(1, k-1)` of `HkIntegrand α k Ψ`. -/
def PM (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (k : ℕ) : ℝ → ℝ → ℝ :=
  fun z θ => (Work.Spaces.mixed (k - 1) 1 Ψ z θ * Work.Spaces.Wt α z θ) ^ 2

/-- The mixed summand at index `(1, k-1)` of `HkIntegrand α k (z²∂_z²Ψ)`. -/
def ZM (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (k : ℕ) : ℝ → ℝ → ℝ :=
  fun z θ => (Work.Spaces.mixed (k - 1) 1
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * Work.Spaces.Wt α z θ) ^ 2

/-- The excess radial term `(D_z^{k+1}Ψ · w/sin(2θ)^{η/2})²`. -/
def EXR (Ψ : ℝ → ℝ → ℝ) (k : ℕ) : ℝ → ℝ → ℝ :=
  fun z θ => (Work.Spaces.DzIter (k + 1) Ψ z θ
    * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2

/-- The excess mixed term `(D_z^kD_θΨ · Wt)²`. -/
def EXM (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (k : ℕ) : ℝ → ℝ → ℝ :=
  fun z θ => (Work.Spaces.DzIter k (Work.Spaces.Dth Ψ) z θ * Work.Spaces.Wt α z θ) ^ 2

/-! ## Elementary angular facts -/

theorem sin_two_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem sin_two_pos {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 < Real.sin (2 * θ) ∨ θ = 0 ∨ θ = Real.pi / 2 := by
  rcases hθ with ⟨h0, h2⟩
  rcases eq_or_lt_of_le h0 with h | h
  · exact Or.inr (Or.inl h.symm)
  rcases eq_or_lt_of_le h2 with h' | h'
  · exact Or.inr (Or.inr h')
  exact Or.inl (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))

/-- `(a·(w/sin(2θ)^{η/2}))² = a²·w²·sin(2θ)^{-η}` on `Iθ`. -/
theorem mul_w_H_sq (a w : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (a * (w / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = a ^ 2 * w ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
  mul_w_sin_rpow_sq a w hθ

/-- `(a·Wt α z θ)² = a²·w²·sin(2θ)^{-γ}` on `Iθ`. -/
theorem mul_Wt_sq (α a z θ : ℝ) (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    (a * Work.Spaces.Wt α z θ) ^ 2
      = a ^ 2 * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  rw [mul_pow, Work.Spaces.bt_Wt_sq α z θ hα hθ]
  ring

/-! ## Slices of `SmoothNbhd` functions -/

/-- The `z`-slice of a `SmoothNbhd` function is `C^∞` on `(-1,∞)` for every angle `θ` in
`(-1, π/2+1)`. -/
theorem contDiffOn_slice_nbh {f : ℝ → ℝ → ℝ} (hf : Work.Spaces.SmoothNbhd f) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (-1) (Real.pi / 2 + 1)) :
    ContDiffOn ℝ ⊤ (fun z => f z θ) (Set.Ioi (-1)) :=
  hf.comp (contDiffOn_id.prodMk contDiffOn_const) (fun z hz => ⟨hz, hθ⟩)

theorem differentiableAt_slice_nbh {f : ℝ → ℝ → ℝ} (hf : Work.Spaces.SmoothNbhd f) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (-1) (Real.pi / 2 + 1)) {z : ℝ} (hz : z ∈ Set.Ioi (-1)) :
    DifferentiableAt ℝ (fun z => f z θ) z :=
  ((contDiffOn_slice_nbh hf hθ).contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt (by simp)

theorem contDiffOn_slice_nbh_snd {f : ℝ → ℝ → ℝ} (hf : Work.Spaces.SmoothNbhd f) {z : ℝ}
    (hz : z ∈ Set.Ioi (-1)) :
    ContDiffOn ℝ ⊤ (fun θ => f z θ) (Set.Ioo (-1) (Real.pi / 2 + 1)) :=
  hf.comp (contDiffOn_const.prodMk contDiffOn_id) (fun θ hθ => ⟨hz, hθ⟩)

theorem differentiableAt_slice_nbh_snd {f : ℝ → ℝ → ℝ} (hf : Work.Spaces.SmoothNbhd f) {z : ℝ}
    (hz : z ∈ Set.Ioi (-1)) {θ : ℝ} (hθ : θ ∈ Set.Ioo (-1) (Real.pi / 2 + 1)) :
    DifferentiableAt ℝ (fun θ => f z θ) θ :=
  ((contDiffOn_slice_nbh_snd hf hz).contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by simp)

/-- `z²∂_z²φ = D_z²φ - D_zφ` on the open neighbourhood `nbhU`. -/
theorem zsq_pzIter2_eqOn (Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ) {z θ : ℝ}
    (hz : z ∈ Set.Ioi (-1)) (hθ : θ ∈ Set.Ioo (-1) (Real.pi / 2 + 1)) :
    z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
      = Work.Spaces.DzIter 2 Ψ z θ - Work.Spaces.Dz Ψ z θ :=
  Work.FTS.EllipticEst.zsq_pzIter2_eq Ψ
    (Work.Spaces.differentiableAt_pzIter_slice (contDiffOn_slice_nbh hsm hθ) 0 hz)
    (Work.Spaces.differentiableAt_pzIter_slice (contDiffOn_slice_nbh hsm hθ) 1 hz)

/-! ## `SmoothNbhd` of the auxiliary functions -/

theorem SmoothNbhd_zsq {Ψ : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd Ψ) :
    Work.Spaces.SmoothNbhd (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) := by
  have h : Work.Spaces.SmoothNbhd
      (fun z θ => Work.Spaces.DzIter 2 Ψ z θ - Work.Spaces.Dz Ψ z θ) :=
    (Work.Spaces.SmoothNbhd.Dz (Work.Spaces.SmoothNbhd.Dz hsm)).sub
      (Work.Spaces.SmoothNbhd.Dz hsm)
  refine h.congr (fun p hp => ?_)
  obtain ⟨z, θ⟩ := p
  simpa only [Function.uncurry] using zsq_pzIter2_eqOn Ψ hsm hp.1 hp.2

theorem SmoothNbhd_mixed {Ψ : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd Ψ) (j i : ℕ) :
    Work.Spaces.SmoothNbhd (Work.Spaces.mixed j i Ψ) :=
  Work.Spaces.SmoothNbhd.DzIter (Work.Spaces.SmoothNbhd.DthIter hsm i) j

/-! ## Additivity of `D_z` and `D_θ` on `nbhU` -/

theorem Dz_sub_eqOn {f g : ℝ → ℝ → ℝ} (hf : Work.Spaces.SmoothNbhd f)
    (hg : Work.Spaces.SmoothNbhd g) :
    EqOn (Function.uncurry (Work.Spaces.Dz (fun z θ => f z θ - g z θ)))
      (Function.uncurry (fun z θ => Work.Spaces.Dz f z θ - Work.Spaces.Dz g z θ))
      Work.Spaces.nbhU := by
  intro p hp
  obtain ⟨z, θ⟩ := p
  have h1 : DifferentiableAt ℝ (fun z' => f z' θ) z := differentiableAt_slice_nbh hf hp.2 hp.1
  have h2 : DifferentiableAt ℝ (fun z' => g z' θ) z := differentiableAt_slice_nbh hg hp.2 hp.1
  show z * deriv (fun z' => f z' θ - g z' θ) z
      = z * deriv (fun z' => f z' θ) z - z * deriv (fun z' => g z' θ) z
  rw [show (fun z' => f z' θ - g z' θ) = (fun z' => f z' θ) - (fun z' => g z' θ) from rfl,
    deriv_sub h1 h2]
  ring

theorem Dth_sub_eqOn {f g : ℝ → ℝ → ℝ} (hf : Work.Spaces.SmoothNbhd f)
    (hg : Work.Spaces.SmoothNbhd g) :
    EqOn (Function.uncurry (Work.Spaces.Dth (fun z θ => f z θ - g z θ)))
      (Function.uncurry (fun z θ => Work.Spaces.Dth f z θ - Work.Spaces.Dth g z θ))
      Work.Spaces.nbhU := by
  intro p hp
  obtain ⟨z, θ⟩ := p
  have h1 : DifferentiableAt ℝ (fun θ' => f z θ') θ := differentiableAt_slice_nbh_snd hf hp.1 hp.2
  have h2 : DifferentiableAt ℝ (fun θ' => g z θ') θ := differentiableAt_slice_nbh_snd hg hp.1 hp.2
  show Real.sin (2 * θ) * deriv (fun θ' => f z θ' - g z θ') θ
      = Real.sin (2 * θ) * deriv (fun θ' => f z θ') θ
        - Real.sin (2 * θ) * deriv (fun θ' => g z θ') θ
  rw [show (fun θ' => f z θ' - g z θ') = (fun θ' => f z θ') - (fun θ' => g z θ') from rfl,
    deriv_sub h1 h2]
  ring

/-! ## Congruence of the iterated operators -/

theorem DthIter_congr {f g : ℝ → ℝ → ℝ}
    (h : EqOn (Function.uncurry f) (Function.uncurry g) Work.Spaces.nbhU) (i : ℕ) :
    EqOn (Function.uncurry (Work.Spaces.DthIter i f))
      (Function.uncurry (Work.Spaces.DthIter i g)) Work.Spaces.nbhU := by
  induction i with
  | zero => exact h
  | succ n ih => exact Work.Spaces.Dth_congr ih

theorem mixed_congr {f g : ℝ → ℝ → ℝ}
    (h : EqOn (Function.uncurry f) (Function.uncurry g) Work.Spaces.nbhU) (j i : ℕ) :
    EqOn (Function.uncurry (Work.Spaces.mixed j i f))
      (Function.uncurry (Work.Spaces.mixed j i g)) Work.Spaces.nbhU :=
  Work.Spaces.DzIter_congr (DthIter_congr h i) j

/-! ## Additivity of the iterated operators -/

theorem DthIter_sub_eqOn {f g : ℝ → ℝ → ℝ} (hf : Work.Spaces.SmoothNbhd f)
    (hg : Work.Spaces.SmoothNbhd g) (i : ℕ) :
    EqOn (Function.uncurry (Work.Spaces.DthIter i (fun z θ => f z θ - g z θ)))
      (Function.uncurry (fun z θ => Work.Spaces.DthIter i f z θ
        - Work.Spaces.DthIter i g z θ)) Work.Spaces.nbhU := by
  induction i with
  | zero => intro p hp; rfl
  | succ n ih =>
      exact (Work.Spaces.Dth_congr ih).trans
        (Dth_sub_eqOn (Work.Spaces.SmoothNbhd.DthIter hf n)
          (Work.Spaces.SmoothNbhd.DthIter hg n))

theorem DzIter_sub_eqOn {f g : ℝ → ℝ → ℝ} (hf : Work.Spaces.SmoothNbhd f)
    (hg : Work.Spaces.SmoothNbhd g) (j : ℕ) :
    EqOn (Function.uncurry (Work.Spaces.DzIter j (fun z θ => f z θ - g z θ)))
      (Function.uncurry (fun z θ => Work.Spaces.DzIter j f z θ
        - Work.Spaces.DzIter j g z θ)) Work.Spaces.nbhU := by
  induction j with
  | zero => intro p hp; rfl
  | succ n ih =>
      exact (Work.Spaces.Dz_congr ih).trans
        (Dz_sub_eqOn (Work.Spaces.SmoothNbhd.DzIter hf n)
          (Work.Spaces.SmoothNbhd.DzIter hg n))

theorem mixed_sub_eqOn {f g : ℝ → ℝ → ℝ} (hf : Work.Spaces.SmoothNbhd f)
    (hg : Work.Spaces.SmoothNbhd g) (j i : ℕ) :
    EqOn (Function.uncurry (Work.Spaces.mixed j i (fun z θ => f z θ - g z θ)))
      (Function.uncurry (fun z θ => Work.Spaces.mixed j i f z θ
        - Work.Spaces.mixed j i g z θ)) Work.Spaces.nbhU :=
  (Work.Spaces.DzIter_congr (DthIter_sub_eqOn hf hg i) j).trans
    (DzIter_sub_eqOn (Work.Spaces.SmoothNbhd.DthIter hf i)
      (Work.Spaces.SmoothNbhd.DthIter hg i) j)

/-! ## The identity `D_z^k(z²∂_z²Ψ) = D_z^{k+2}Ψ - D_z^{k+1}Ψ` on `nbhU` -/

theorem DzIter_zsq_eqOn (Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ) (k : ℕ) :
    EqOn (Function.uncurry (Work.Spaces.DzIter k
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)))
      (Function.uncurry (fun z θ => Work.Spaces.DzIter (k + 2) Ψ z θ
        - Work.Spaces.DzIter (k + 1) Ψ z θ)) Work.Spaces.nbhU := by
  induction k with
  | zero =>
      intro p hp
      obtain ⟨z, θ⟩ := p
      rw [show Work.Spaces.DzIter (0 + 2) Ψ = Work.Spaces.DzIter 2 Ψ from rfl,
        show Work.Spaces.DzIter (0 + 1) Ψ = Work.Spaces.Dz Ψ from rfl]
      simpa only [Work.Spaces.DzIter_zero, Function.uncurry]
        using zsq_pzIter2_eqOn Ψ hsm hp.1 hp.2
  | succ n ih =>
      intro p hp
      obtain ⟨z, θ⟩ := p
      have h1 : Work.Spaces.Dz (Work.Spaces.DzIter n
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
          = Work.Spaces.Dz (fun z θ => Work.Spaces.DzIter (n + 2) Ψ z θ
              - Work.Spaces.DzIter (n + 1) Ψ z θ) z θ :=
        Work.Spaces.Dz_congr ih hp
      have h2 : Work.Spaces.Dz (fun z θ => Work.Spaces.DzIter (n + 2) Ψ z θ
              - Work.Spaces.DzIter (n + 1) Ψ z θ) z θ
          = Work.Spaces.Dz (Work.Spaces.DzIter (n + 2) Ψ) z θ
            - Work.Spaces.Dz (Work.Spaces.DzIter (n + 1) Ψ) z θ :=
        Dz_sub_eqOn (Work.Spaces.SmoothNbhd.DzIter hsm (n + 2))
          (Work.Spaces.SmoothNbhd.DzIter hsm (n + 1)) hp
      have harith : Work.Spaces.DzIter (n + 1 + 2) Ψ z θ
            - Work.Spaces.DzIter (n + 1 + 1) Ψ z θ
          = Work.Spaces.Dz (Work.Spaces.DzIter (n + 2) Ψ) z θ
            - Work.Spaces.Dz (Work.Spaces.DzIter (n + 1) Ψ) z θ := by
        rw [show n + 1 + 2 = (n + 2) + 1 from by omega,
          show n + 1 + 1 = (n + 1) + 1 from by omega,
          Work.Spaces.DzIter_succ, Work.Spaces.DzIter_succ]
      show Work.Spaces.Dz (Work.Spaces.DzIter n
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
        = Work.Spaces.DzIter (n + 1 + 2) Ψ z θ - Work.Spaces.DzIter (n + 1 + 1) Ψ z θ
      rw [h1, h2, ← harith]

/-! ## The commutation `z²∂_z²(mixed j i Ψ) = mixed j i(z²∂_z²Ψ)` -/

theorem zsq_pzIter2_mixed (Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ) (j i : ℕ)
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.mixed j i Ψ) z θ
      = Work.Spaces.mixed j i (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ := by
  have hnb : (z, θ) ∈ Work.Spaces.nbhU := Work.Spaces.mem_nbhU hz hθ
  have e1 : Work.Spaces.DzIter 2 (Work.Spaces.mixed j i Ψ) z θ
      = Work.Spaces.mixed (j + 2) i Ψ z θ := by
    show Work.Spaces.DzIter 2 (Work.Spaces.DzIter j (Work.Spaces.DthIter i Ψ)) z θ = _
    rw [← Work.Spaces.DzIter_add_right 2 j (Work.Spaces.DthIter i Ψ)]
    rw [show 2 + j = j + 2 from Nat.add_comm 2 j]
    rfl
  have e2 : Work.Spaces.DzIter 1 (Work.Spaces.mixed j i Ψ) z θ
      = Work.Spaces.mixed (j + 1) i Ψ z θ := by
    show Work.Spaces.DzIter 1 (Work.Spaces.DzIter j (Work.Spaces.DthIter i Ψ)) z θ = _
    rw [← Work.Spaces.DzIter_add_right 1 j (Work.Spaces.DthIter i Ψ)]
    rw [show 1 + j = j + 1 from Nat.add_comm 1 j]
    rfl
  have hL : z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.mixed j i Ψ) z θ
      = Work.Spaces.DzIter 2 (Work.Spaces.mixed j i Ψ) z θ
        - Work.Spaces.DzIter 1 (Work.Spaces.mixed j i Ψ) z θ :=
    zsq_pzIter2_eqOn (Work.Spaces.mixed j i Ψ) (SmoothNbhd_mixed hsm j i) hnb.1 hnb.2
  have e3 : Work.Spaces.mixed j i (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
      = Work.Spaces.mixed j i (fun z θ => Work.Spaces.DzIter 2 Ψ z θ
          - Work.Spaces.Dz Ψ z θ) z θ := by
    refine mixed_congr ?_ j i hnb
    intro p hp
    exact zsq_pzIter2_eqOn Ψ hsm hp.1 hp.2
  have e4 : Work.Spaces.mixed j i (fun z θ => Work.Spaces.DzIter 2 Ψ z θ
          - Work.Spaces.Dz Ψ z θ) z θ
      = Work.Spaces.mixed j i (Work.Spaces.DzIter 2 Ψ) z θ
        - Work.Spaces.mixed j i (Work.Spaces.Dz Ψ) z θ :=
    mixed_sub_eqOn (Work.Spaces.SmoothNbhd.DzIter hsm 2) (Work.Spaces.SmoothNbhd.Dz hsm)
      j i hnb
  have e5 : Work.Spaces.mixed j i (Work.Spaces.DzIter 2 Ψ) z θ
      = Work.Spaces.mixed (j + 2) i Ψ z θ := by
    have h := Work.Spaces.mixed_comm Ψ hsm j i 2 0 z θ hz hθ
    simpa only [Work.Spaces.mixed_zero_right, Nat.add_zero] using h
  have e6 : Work.Spaces.mixed j i (Work.Spaces.Dz Ψ) z θ
      = Work.Spaces.mixed (j + 1) i Ψ z θ := by
    have h := Work.Spaces.mixed_comm Ψ hsm j i 1 0 z θ hz hθ
    have h1 : Work.Spaces.DzIter 1 Ψ = Work.Spaces.Dz Ψ := rfl
    rw [Work.Spaces.mixed_zero_right, h1, Nat.add_zero] at h
    exact h
  rw [hL, e1, e2, ← e5, ← e6, ← e4, ← e3]

/-! ## The one-variable `rDz`-iterates of the `D_z`-slices -/

theorem rDzIter_two_slice (Ψ : ℝ → ℝ → ℝ) (k : ℕ) (θ : ℝ) :
    Work.FTS.EllipticEst.rDzIter 2 (fun z => Work.Spaces.DzIter k Ψ z θ)
      = fun z => Work.Spaces.DzIter (k + 2) Ψ z θ := rfl

theorem rDzIter_one_slice (Ψ : ℝ → ℝ → ℝ) (k : ℕ) (θ : ℝ) :
    Work.FTS.EllipticEst.rDzIter 1 (fun z => Work.Spaces.DzIter k Ψ z θ)
      = fun z => Work.Spaces.DzIter (k + 1) Ψ z θ := rfl

theorem rDzIter_one_const_mul (c : ℝ) (g : ℝ → ℝ) :
    Work.FTS.EllipticEst.rDzIter 1 (fun z => c * g z)
      = fun z => c * Work.FTS.EllipticEst.rDzIter 1 g z :=
  Work.FTS.EllipticEst.rDz_const_mul c g

theorem rDzIter_two_const_mul (c : ℝ) (g : ℝ → ℝ) :
    Work.FTS.EllipticEst.rDzIter 2 (fun z => c * g z)
      = fun z => c * Work.FTS.EllipticEst.rDzIter 2 g z := by
  simp only [Work.FTS.EllipticEst.rDzIter_succ, Work.FTS.EllipticEst.rDzIter_zero]
  rw [Work.FTS.EllipticEst.rDz_const_mul c g, Work.FTS.EllipticEst.rDz_const_mul c
    (Work.FTS.EllipticEst.rDz g)]


/-! ## The open quadrant and the continuity of the weights -/

/-- The open quadrant `(0,∞) × (0,π/2)`. -/
def Qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)

theorem sin_two_pos' {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem continuousOn_w_Qd : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Qd := by
  simp only [Work.Spaces.w]
  refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => ?_)
  exact pow_ne_zero 2 (ne_of_gt hp.1)

theorem continuousOn_sinpow_Qd (c : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c) Qd :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun p hp => Or.inl (ne_of_gt (sin_two_pos' hp.2)))

theorem contOn_uncurry_Wt_Qd (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Qd := by
  simp only [Work.Spaces.Wt, Work.Spaces.wTheta]
  exact continuousOn_w_Qd.mul (continuousOn_sinpow_Qd (-(Work.Spaces.gam α / 2)))

theorem contOn_uncurry_H_Qd :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))
      Qd :=
  continuousOn_w_Qd.div (continuousOn_sinpow_Qd (Work.Spaces.eta / 2))
    (fun p hp => ne_of_gt (Real.rpow_pos_of_pos (sin_two_pos' hp.2) _))

theorem contDiffOn_quadU_of_smoothNbhd {g : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd g) :
    ContDiffOn ℝ ⊤ (Function.uncurry g) Work.Spaces.quadU :=
  hsm.mono (Set.prod_mono (le_refl _)
    (Set.Ioo_subset_Ioo (by norm_num) (by linarith [Real.pi_pos])))

/-! ## Measurability of the two kinds of summand -/

theorem aeMeas_ofReal_HkIntegrand (α : ℝ) (k : ℕ) {g : ℝ → ℝ → ℝ}
    (hsm : Work.Spaces.SmoothNbhd g) :
    AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k g p.1 p.2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
  ENNReal.measurable_ofReal.comp_aemeasurable
    ((Work.Spaces.aesm_of_continuousOn_Qd _ (Work.Spaces.continuousOn_HkIntegrand_Qd α k g
      (contDiffOn_quadU_of_smoothNbhd hsm))).aemeasurable)

theorem aesm_zSummand_prod (α : ℝ) {g : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd g) (m : ℕ) :
    AEMeasurable (fun p : ℝ × ℝ =>
        ENNReal.ofReal ((Work.Spaces.DzIter m g p.1 p.2
          * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
  ENNReal.measurable_ofReal.comp_aemeasurable
    ((Work.Spaces.HPRZ.aesm_DzIter_H_weight_prod g hsm m).pow 2).aemeasurable

theorem aesm_zSummand_slice (α : ℝ) {g : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd g) (m : ℕ)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    AEStronglyMeasurable (fun θ : ℝ => (Work.Spaces.DzIter m g z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
  ((Work.Spaces.HPRZ.aesm_DzIter_H_weight_slice g hsm m hz).pow 2)

theorem aesm_mixed_Wt_sq_slice (α : ℝ) {g : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd g)
    (j i : ℕ) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    AEStronglyMeasurable (fun θ : ℝ =>
        (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hpos
  · subst h0
    have hzero : (fun θ : ℝ => (Work.Spaces.mixed j i g 0 θ * Work.Spaces.Wt α 0 θ) ^ 2)
        = fun _ : ℝ => (0 : ℝ) := by
      funext θ
      simp [Work.Spaces.Wt, Work.Spaces.w]
    rw [hzero]
    exact aestronglyMeasurable_const
  · have hcont : ContinuousOn (fun p : ℝ × ℝ =>
        (Work.Spaces.mixed j i g p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2) Qd :=
      ((((Work.Spaces.contDiffOn_uncurry_mixed_of_quadU g
          (contDiffOn_quadU_of_smoothNbhd hsm) j i).continuousOn.mono
          (Set.prod_mono (Set.Ioi_subset_Ioi (by norm_num)) subset_rfl)).mul
        (contOn_uncurry_Wt_Qd α))).pow 2
    exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hpos

theorem aesm_mixed_Wt_sq_prod' (α : ℝ) {g : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd g)
    (j i : ℕ) :
    AEMeasurable (fun p : ℝ × ℝ =>
        ENNReal.ofReal ((Work.Spaces.mixed j i g p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
  ENNReal.measurable_ofReal.comp_aemeasurable
    (Work.Spaces.aesm_mixed_Wt_sq_prod α g hsm j i).aemeasurable

theorem aesm_zSummand_sq_prod' (α : ℝ) {g : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd g)
    (m : ℕ) :
    AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal
        ((Work.Spaces.DzIter m g p.1 p.2
          * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
  aesm_zSummand_prod α hsm m


/-! ## The product `lintegral` of a nonnegative function -/

theorem lintegral_prod_ofReal_eq_ofReal_integral (F : ℝ → ℝ → ℝ)
    (hnn : ∀ z θ, 0 ≤ F z θ)
    (hslice : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => F z θ) Work.Spaces.Iθ)
    (hFz : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, F z θ) Work.Spaces.Iz)
    (hmeas : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (F p.1 p.2))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))) :
    (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (F p.1 p.2)
        ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))
      = ENNReal.ofReal (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, F z θ) := by
  have h1 : ∀ z ∈ Work.Spaces.Iz, ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, F z θ)
      = ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (F z θ) := fun z hz =>
    ofReal_integral_eq_lintegral_ofReal (hslice z hz) (Eventually.of_forall (fun θ => hnn z θ))
  have h2 : ENNReal.ofReal (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, F z θ)
      = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, F z θ) :=
    ofReal_integral_eq_lintegral_ofReal hFz
      (Eventually.of_forall (fun z => integral_nonneg (fun θ => hnn z θ)))
  rw [h2]
  have h3 : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, F z θ))
      = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (F z θ) := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
    exact h1 z hz
  rw [h3]
  exact lintegral_prod (f := fun p : ℝ × ℝ => ENNReal.ofReal (F p.1 p.2)) hmeas

/-! ## z-slice measurability of the summands -/

theorem aesm_zslice_of_continuousOn_Ioi {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Ioi 0)) :
    AEStronglyMeasurable g (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  rw [Work.Spaces.Iz, ← MeasureTheory.restrict_Ioi_eq_restrict_Ici (a := (0 : ℝ))]
  exact hg.aestronglyMeasurable measurableSet_Ioi

theorem continuousOn_w_Ioi : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioi 0) := by
  simp only [Work.Spaces.w]
  exact ((continuousOn_const.add continuousOn_id).pow 2).div (continuousOn_id.pow 2)
    (fun z hz => pow_ne_zero 2 (ne_of_gt hz))

theorem aesm_zslice_zSummand {g : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd g) (m : ℕ)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.DzIter m g z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  refine aesm_zslice_of_continuousOn_Ioi ?_
  have hs : ContinuousOn (fun z : ℝ => Work.Spaces.DzIter m g z θ) (Set.Ioi (-1)) :=
    (Work.Spaces.hardyZ_contDiffOn_slice (Work.Spaces.DzIter m g)
      (Work.Spaces.SmoothNbhd.DzIter hsm m) hθ).continuousOn
  have hprod : ContinuousOn (fun z : ℝ => Work.Spaces.DzIter m g z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) (Set.Ioi 0) :=
    (hs.mono (Set.Ioi_subset_Ioi (by norm_num : (-1 : ℝ) ≤ 0))).mul
      (continuousOn_w_Ioi.div_const _)
  exact hprod.pow 2

theorem aesm_zslice_mixedSummand (α : ℝ) {g : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd g)
    (j i : ℕ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  refine aesm_zslice_of_continuousOn_Ioi ?_
  have hs : ContinuousOn (fun z : ℝ => Work.Spaces.mixed j i g z θ) (Set.Ioi (-1)) :=
    (Work.Spaces.hardyZ_contDiffOn_slice (Work.Spaces.mixed j i g)
      (SmoothNbhd_mixed hsm j i) hθ).continuousOn
  have hw : ContinuousOn (fun z : ℝ => Work.Spaces.Wt α z θ) (Set.Ioi 0) := by
    simp only [Work.Spaces.Wt]
    exact continuousOn_w_Ioi.mul continuousOn_const
  exact ((hs.mono (Set.Ioi_subset_Ioi (by norm_num : (-1 : ℝ) ≤ 0))).mul hw).pow 2

/-! ## The four facts about a summand of an honest integrand -/

theorem summand_props {α : ℝ} {k : ℕ} {F T : ℝ → ℝ → ℝ}
    (hF : Work.Spaces.HkMem α k F)
    (hFmeas : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k F p.1 p.2))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))
    (hTnn : ∀ z θ, 0 ≤ T z θ) (hTle : ∀ z θ, T z θ ≤ Work.Spaces.HkIntegrand α k F z θ)
    (hTaesm : AEStronglyMeasurable (fun p : ℝ × ℝ => T p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))
    (hTslice : ∀ z ∈ Work.Spaces.Iz, AEStronglyMeasurable (fun θ : ℝ => T z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hTzslice : ∀ θ ∈ Work.Spaces.Iθ, AEStronglyMeasurable (fun z : ℝ => T z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz)) :
    (∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ : ℝ => T z θ) Work.Spaces.Iθ) ∧
      IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, T z θ) Work.Spaces.Iz ∧
      (∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        IntegrableOn (fun z : ℝ => T z θ) Work.Spaces.Iz) ∧
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (∫ z in Work.Spaces.Iz, T z θ)) < ⊤ := by
  have hTmeas : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (T p.1 p.2))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hTaesm.aemeasurable
  have hslice : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ : ℝ => T z θ) Work.Spaces.Iθ := by
    intro z hz
    refine Integrable.mono' (hF.1 z hz) (hTslice z hz) ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Real.norm_of_nonneg (hTnn z θ)]
    exact hTle z θ
  have hFprod_eq : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k F p.1 p.2)
        ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))
      = ENNReal.ofReal (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k F z θ) :=
    lintegral_prod_ofReal_eq_ofReal_integral (fun z θ => Work.Spaces.HkIntegrand α k F z θ)
      (fun z θ => Work.Spaces.HkIntegrand_nonneg α k F z θ) (fun z hz => hF.1 z hz) hF.2 hFmeas
  have hTprod_eq : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (T p.1 p.2)
        ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))
      = ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (T z θ) := by
    rw [← lintegral_lintegral_swap hTmeas, lintegral_prod _ hTmeas]
  have hTprod_lt : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (T p.1 p.2)
        ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))) < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono (fun p => ENNReal.ofReal_le_ofReal (hTle p.1 p.2))) ?_
    rw [hFprod_eq]
    exact ENNReal.ofReal_lt_top
  have hfin : (∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (T z θ)) < ⊤ := by
    rw [← hTprod_eq]; exact hTprod_lt
  -- (a) for a.e. angle, the `z`-slice of `T` is integrable
  have hInner : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (T z θ)) < ⊤ :=
    ae_lt_top' hTmeas.lintegral_prod_left (ne_of_lt hfin)
  have haeslice : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      IntegrableOn (fun z : ℝ => T z θ) Work.Spaces.Iz := by
    filter_upwards [hInner, ae_restrict_mem measurableSet_Icc] with θ hθ hθmem
    refine ⟨hTzslice θ hθmem, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have hnorm : (fun z : ℝ => ‖T z θ‖ₑ) = fun z => ENNReal.ofReal (T z θ) := by
      funext z
      exact Real.enorm_eq_ofReal (hTnn z θ)
    rw [hnorm]
    exact hθ
  -- (b) the `lintegral` over `θ` of the `z`-integral is finite
  have hb : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (∫ z in Work.Spaces.Iz, T z θ)) < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono_ae ?_) hfin
    filter_upwards [haeslice] with θ hθ
    exact le_of_eq (ofReal_integral_eq_lintegral_ofReal hθ (Eventually.of_forall (fun z => hTnn z θ)))
  refine ⟨hslice, ?_, haeslice, hb⟩
  -- the `z`-integral of the slices is integrable
  refine Integrable.mono' hF.2 hTaesm.integral_prod_right' ?_
  filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
  rw [Real.norm_of_nonneg (integral_nonneg (fun θ => hTnn z θ))]
  exact integral_mono_of_nonneg (ae_restrict_of_forall_mem measurableSet_Icc (fun θ _ => hTnn z θ))
    (hF.1 z hz) (ae_restrict_of_forall_mem measurableSet_Icc (fun θ _ => hTle z θ))



/-! ## The `rDz`-form of the slices of the mixed derivatives -/

theorem rDzIter_one_mixed_slice (Ψ : ℝ → ℝ → ℝ) (k : ℕ) (hk : 1 ≤ k) (θ : ℝ) :
    Work.FTS.EllipticEst.rDzIter 1 (fun z => Work.Spaces.DzIter (k - 1) (Work.Spaces.Dth Ψ) z θ)
      = fun z => Work.Spaces.DzIter k (Work.Spaces.Dth Ψ) z θ := by
  rw [show k = (k - 1) + 1 from (Nat.succ_pred_eq_of_pos hk).symm]
  rfl

theorem rDzIter_two_mixed_slice (Ψ : ℝ → ℝ → ℝ) (k : ℕ) (hk : 1 ≤ k) (θ : ℝ) :
    Work.FTS.EllipticEst.rDzIter 2 (fun z => Work.Spaces.DzIter (k - 1) (Work.Spaces.Dth Ψ) z θ)
      = fun z => Work.Spaces.DzIter (k + 1) (Work.Spaces.Dth Ψ) z θ := by
  rw [show Work.FTS.EllipticEst.rDzIter 2
        (fun z => Work.Spaces.DzIter (k - 1) (Work.Spaces.Dth Ψ) z θ)
      = Work.FTS.EllipticEst.rDz (Work.FTS.EllipticEst.rDzIter 1
        (fun z => Work.Spaces.DzIter (k - 1) (Work.Spaces.Dth Ψ) z θ)) from rfl,
    rDzIter_one_mixed_slice Ψ k hk θ]
  rfl

theorem mixed_slice_zsq (Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ) (k : ℕ) (hk : 1 ≤ k)
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.DzIter (k + 1) (Work.Spaces.Dth Ψ) z θ
        - Work.Spaces.DzIter k (Work.Spaces.Dth Ψ) z θ
      = Work.Spaces.mixed (k - 1) 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ := by
  have hnb : (z, θ) ∈ Work.Spaces.nbhU := Work.Spaces.mem_nbhU hz hθ
  have h1 := zsq_pzIter2_mixed Ψ hsm (k - 1) 1 hz hθ
  have h2 := zsq_pzIter2_eqOn (Work.Spaces.mixed (k - 1) 1 Ψ)
    (SmoothNbhd_mixed hsm (k - 1) 1) hnb.1 hnb.2
  rw [← h1, h2]
  have e1 : Work.Spaces.DzIter 2 (Work.Spaces.mixed (k - 1) 1 Ψ) z θ
      = Work.Spaces.DzIter (k + 1) (Work.Spaces.Dth Ψ) z θ := by
    show Work.Spaces.DzIter 2 (Work.Spaces.DzIter (k - 1) (Work.Spaces.DthIter 1 Ψ)) z θ = _
    rw [← Work.Spaces.DzIter_add_right 2 (k - 1) (Work.Spaces.DthIter 1 Ψ)]
    rw [show 2 + (k - 1) = k + 1 from by omega]
    rfl
  have e2 : Work.Spaces.Dz (Work.Spaces.mixed (k - 1) 1 Ψ) z θ
      = Work.Spaces.DzIter k (Work.Spaces.Dth Ψ) z θ := by
    show Work.Spaces.DzIter 1 (Work.Spaces.DzIter (k - 1) (Work.Spaces.DthIter 1 Ψ)) z θ = _
    rw [← Work.Spaces.DzIter_add_right 1 (k - 1) (Work.Spaces.DthIter 1 Ψ)]
    rw [show 1 + (k - 1) = k from by omega]
    rfl
  rw [e1, e2]



/-! ## `D_z` ignores an angular factor -/

theorem Dz_ang_mul (u : ℝ → ℝ) (h : ℝ → ℝ → ℝ) :
    Work.Spaces.Dz (fun z θ => u θ * h z θ) = fun z θ => u θ * Work.Spaces.Dz h z θ := by
  funext z θ
  simp only [Work.Spaces.Dz, Work.Spaces.pz]
  rw [deriv_const_mul_field (u θ)]
  ring

theorem DzIter_ang_mul (u : ℝ → ℝ) (h : ℝ → ℝ → ℝ) (j : ℕ) :
    Work.Spaces.DzIter j (fun z θ => u θ * h z θ)
      = fun z θ => u θ * Work.Spaces.DzIter j h z θ := by
  induction j with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DzIter_succ, ih, Work.Spaces.DzIter_succ]
      exact Dz_ang_mul u (Work.Spaces.DzIter n h)

/-! ## Smoothness of the plain angular derivative, and `θ`-slice continuity -/

theorem contDiffOn_thetaSlice_nbh {g : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd g) {z : ℝ}
    (hz : z ∈ Set.Ioi (-1)) :
    ContDiffOn ℝ ⊤ (fun θ => g z θ) (Set.Ioo (-1) (Real.pi / 2 + 1)) :=
  hsm.comp (contDiffOn_const.prodMk contDiffOn_id) (fun θ hθ => ⟨hz, hθ⟩)

theorem SmoothNbhd_pth {f : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd f) :
    Work.Spaces.SmoothNbhd (Work.Spaces.pth f) := by
  have hfd : ContDiffOn ℝ ⊤ (fderiv ℝ (Function.uncurry f)) Work.Spaces.nbhU :=
    ContDiffOn.fderiv_of_isOpen hsm Work.Spaces.isOpen_nbhU (by simp)
  have hev : ContDiffOn ℝ ⊤
      (fun y : ℝ × ℝ => (fderiv ℝ (Function.uncurry f) y) (0, 1)) Work.Spaces.nbhU :=
    hfd.clm_apply contDiffOn_const
  refine hev.congr (fun y hy => ?_)
  have hdiff : DifferentiableAt ℝ (Function.uncurry f) y :=
    (ContDiffOn.contDiffAt hsm (Work.Spaces.isOpen_nbhU.mem_nhds hy)).differentiableAt
      (by norm_num)
  show deriv (fun θ' => f y.1 θ') y.2 = (fderiv ℝ (Function.uncurry f) y) (0, 1)
  exact Work.Spaces.deriv_slice_snd (Function.uncurry f) y.1 y.2 hdiff

theorem Iθ_subset_nbh : (Work.Spaces.Iθ : Set ℝ) ⊆ Set.Ioo (-1) (Real.pi / 2 + 1) :=
  Set.Icc_subset_Ioo (by norm_num) (by linarith)

/-! ## Integrability of the `θ`-slices of the two excess terms -/

theorem EXR_slice_integrable (k : ℕ) (Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    MeasureTheory.IntegrableOn (fun θ => DzAux.EXR Ψ k z θ) Work.Spaces.Iθ := by
  have hz' : z ∈ Set.Ioi (-1) := by
    rw [Work.Spaces.Iz, Set.mem_Ici] at hz
    rw [Set.mem_Ioi]
    linarith
  have hcont : ContinuousOn (fun θ : ℝ => Work.Spaces.DzIter (k + 1) Ψ z θ)
      Work.Spaces.Iθ :=
    ((contDiffOn_thetaSlice_nbh (Work.Spaces.SmoothNbhd.DzIter hsm (k + 1)) hz').continuousOn).mono
      Iθ_subset_nbh
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hsin := Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
    (by rw [Work.Spaces.eta]; norm_num) (by rw [Work.Spaces.eta]; norm_num)
  refine Integrable.mono'
    (hsin.1.const_mul (C ^ 2 * (Work.Spaces.w z) ^ 2)) ?_ ?_
  · have h := DzAux.aesm_zSummand_slice (0 : ℝ) hsm (k + 1) hz
    simpa only [DzAux.EXR] using h
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    have hs0 : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have h1 : DzAux.EXR Ψ k z θ = (Work.Spaces.DzIter (k + 1) Ψ z θ) ^ 2
        * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
      simp only [DzAux.EXR]
      exact Work.Spaces.sq_mul_div_rpow _ _ _ _ hs0 (by rw [Work.Spaces.eta]; norm_num)
    have h2 : |Work.Spaces.DzIter (k + 1) Ψ z θ| ≤ C := by
      have := hC θ hθ
      rwa [Real.norm_eq_abs] at this
    have h3 : (Work.Spaces.DzIter (k + 1) Ψ z θ) ^ 2 ≤ C ^ 2 :=
      sq_le_sq' (abs_le.mp h2).1 (abs_le.mp h2).2
    have h4 : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
      Real.rpow_nonneg hs0 _
    rw [h1, Real.norm_of_nonneg (by positivity)]
    have h5 : (0 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 h5) h4

theorem EXM_slice_integrable (α : ℝ) (k : ℕ) (Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ)
    (hα : 0 < α) (hα1 : α ≤ 1) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    MeasureTheory.IntegrableOn (fun θ => DzAux.EXM α Ψ k z θ) Work.Spaces.Iθ := by
  have hz' : z ∈ Set.Ioi (-1) := by
    rw [Work.Spaces.Iz, Set.mem_Ici] at hz
    rw [Set.mem_Ioi]
    linarith
  have hcont : ContinuousOn (fun θ : ℝ => Work.Spaces.DzIter k (Work.Spaces.pth Ψ) z θ)
      Work.Spaces.Iθ :=
    ((contDiffOn_thetaSlice_nbh
      (Work.Spaces.SmoothNbhd.DzIter (SmoothNbhd_pth hsm) k) hz').continuousOn).mono
      Iθ_subset_nbh
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hvol : volume Work.Spaces.Iθ = ENNReal.ofReal (Real.pi / 2) := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]
    norm_num
  refine Integrable.mono'
    (integrableOn_const (s := Work.Spaces.Iθ) (C := C ^ 2 * (Work.Spaces.w z) ^ 2) ?_) ?_ ?_
  · rw [hvol]
    exact ENNReal.ofReal_ne_top
  · show AEStronglyMeasurable (fun θ : ℝ =>
      (Work.Spaces.mixed k 0 (Work.Spaces.Dth Ψ) z θ * Work.Spaces.Wt α z θ) ^ 2)
      (volume.restrict Work.Spaces.Iθ)
    exact DzAux.aesm_mixed_Wt_sq_slice α (Work.Spaces.SmoothNbhd.Dth hsm) k 0 hz
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    have hs0 : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hfac : Work.Spaces.DzIter k (Work.Spaces.Dth Ψ) z θ
        = Real.sin (2 * θ) * Work.Spaces.DzIter k (Work.Spaces.pth Ψ) z θ := by
      have h := congrFun (congrFun (DzIter_ang_mul (fun θ' => Real.sin (2 * θ'))
        (Work.Spaces.pth Ψ) k) z) θ
      have hgoal : Work.Spaces.DzIter k (Work.Spaces.Dth Ψ) z θ
          = Work.Spaces.DzIter k (fun z θ => Real.sin (2 * θ) * Work.Spaces.pth Ψ z θ) z θ := rfl
      rw [hgoal]
      exact h
    have hgam : Work.Spaces.gam α = 1 + α / 10 := rfl
    have hA : DzAux.EXM α Ψ k z θ = (Real.sin (2 * θ)
        * Work.Spaces.DzIter k (Work.Spaces.pth Ψ) z θ) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2 := by
      simp only [DzAux.EXM, hfac, mul_pow]
    have hCr : (Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        = (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by
      rw [← Real.rpow_two, ← Real.rpow_add' hs0 (by rw [Work.Spaces.gam]; linarith [hα])]
      rw [show (2 : ℝ) + -(Work.Spaces.gam α) = 2 - Work.Spaces.gam α from by ring]
    have h1 : DzAux.EXM α Ψ k z θ = (Work.Spaces.DzIter k (Work.Spaces.pth Ψ) z θ) ^ 2
        * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by
      calc DzAux.EXM α Ψ k z θ
          = (Real.sin (2 * θ) * Work.Spaces.DzIter k (Work.Spaces.pth Ψ) z θ) ^ 2
            * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
            rw [hA, Work.Spaces.bt_Wt_sq α z θ hα hθ]
        _ = (Work.Spaces.DzIter k (Work.Spaces.pth Ψ) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            * ((Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
            ring
        _ = (Work.Spaces.DzIter k (Work.Spaces.pth Ψ) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by rw [hCr]
    have h2 : |Work.Spaces.DzIter k (Work.Spaces.pth Ψ) z θ| ≤ C := by
      have := hC θ hθ
      rwa [Real.norm_eq_abs] at this
    have h3 : (Work.Spaces.DzIter k (Work.Spaces.pth Ψ) z θ) ^ 2 ≤ C ^ 2 :=
      sq_le_sq' (abs_le.mp h2).1 (abs_le.mp h2).2
    have h4 : 0 ≤ (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := Real.rpow_nonneg hs0 _
    have h5 : (0 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    have h6 : (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) ≤ 1 := by
      refine Real.rpow_le_one hs0 (Real.sin_le_one _) ?_
      have : 0 < α := hα
      rw [Work.Spaces.gam]
      linarith
    rw [h1, Real.norm_of_nonneg (by positivity)]
    calc (Work.Spaces.DzIter k (Work.Spaces.pth Ψ) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
        ≤ C ^ 2 * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 h5) h4
      _ ≤ C ^ 2 * (Work.Spaces.w z) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left h6 (mul_nonneg (sq_nonneg C) h5)
      _ = C ^ 2 * (Work.Spaces.w z) ^ 2 := by ring


end Work.FTS.EllipticEst.Cert.DzAux
