import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.aesm_mixed_Wt_sq_prod
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.continuousOn_HkIntegrand_Qd
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.mixed_sq_integrableOn
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1

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



/-- The mixed summand at index `(1, k-1)` of `HkIntegrand α k Ψ`. -/
def PM (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (k : ℕ) : ℝ → ℝ → ℝ :=
  fun z θ => (Work.Spaces.mixed (k - 1) 1 Ψ z θ * Work.Spaces.Wt α z θ) ^ 2




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


/-! ## `SmoothNbhd` of the auxiliary functions -/



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


/-! ## The commutation `z²∂_z²(mixed j i Ψ) = mixed j i(z²∂_z²Ψ)` -/


/-! ## The one-variable `rDz`-iterates of the `D_z`-slices -/






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



/-! ## Measurability of the two kinds of summand -/








/-! ## The product `lintegral` of a nonnegative function -/


/-! ## z-slice measurability of the summands -/


theorem continuousOn_w_Ioi : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioi 0) := by
  simp only [Work.Spaces.w]
  exact ((continuousOn_const.add continuousOn_id).pow 2).div (continuousOn_id.pow 2)
    (fun z hz => pow_ne_zero 2 (ne_of_gt hz))



/-! ## The four facts about a summand of an honest integrand -/




/-! ## The `rDz`-form of the slices of the mixed derivatives -/






/-! ## `D_z` ignores an angular factor -/

theorem Dz_ang_mul (u : ℝ → ℝ) (h : ℝ → ℝ → ℝ) :
    Work.Spaces.Dz (fun z θ => u θ * h z θ) = fun z θ => u θ * Work.Spaces.Dz h z θ := by
  funext z θ
  simp only [Work.Spaces.Dz, Work.Spaces.pz]
  rw [deriv_const_mul_field (u θ)]
  ring


/-! ## Smoothness of the plain angular derivative, and `θ`-slice continuity -/




/-! ## Integrability of the `θ`-slices of the two excess terms -/




end Work.FTS.EllipticEst.Cert.DzAux
