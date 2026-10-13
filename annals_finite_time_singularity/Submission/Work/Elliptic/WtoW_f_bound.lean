import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Elliptic.WtoWAux
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.WlInf_terms
import Submission.Work.Spaces.BoxBounds
import Submission.Work.Spaces.SmoothCompact_Aux
import Submission.Work.Spaces.psi_mw_le
import Submission.Work.Spaces.pz_aux
import Submission.Work.Spaces.HardyZ
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.DthIter_mul
import Submission.Work.Elliptic.WtoW_f_defs
import Submission.Work.Elliptic.WtoW_f_zero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

open Work.Spaces

set_option autoImplicit false

/-! ## Derivative facts for `sin (2·)` -/

theorem WtoW_f_deriv_sin_two (θ : ℝ) :
    deriv (fun θ' : ℝ => Real.sin (2*θ')) θ = 2 * Real.cos (2*θ) := by
  have h1 : HasDerivAt (fun θ' : ℝ => 2*θ') 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2:ℝ)
  have h2 := h1.sin
  have h3 : Real.cos (2*θ) * 2 = 2 * Real.cos (2*θ) := by ring
  rw [h3] at h2
  exact h2.deriv

theorem WtoW_f_deriv_cos_two (θ : ℝ) :
    deriv (fun θ' : ℝ => Real.cos (2*θ')) θ = -2 * Real.sin (2*θ) := by
  have h1 : HasDerivAt (fun θ' : ℝ => 2*θ') 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2:ℝ)
  have h2 := h1.cos
  have h3 : -(Real.sin (2*θ)) * 2 = -2 * Real.sin (2*θ) := by ring
  rw [h3] at h2
  exact h2.deriv

theorem WtoW_f_deriv_gam1 (θ : ℝ) :
    deriv (fun θ' : ℝ => Real.sin (2*θ') * (2*Real.cos (2*θ'))) θ
      = 4*(Real.cos (2*θ))^2 - 4*(Real.sin (2*θ))^2 := by
  have hs : HasDerivAt (fun θ' : ℝ => Real.sin (2*θ')) (2 * Real.cos (2*θ)) θ := by
    have h1 : HasDerivAt (fun θ' : ℝ => 2*θ') 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2:ℝ)
    have h2 := h1.sin
    have h3 : Real.cos (2*θ) * 2 = 2 * Real.cos (2*θ) := by ring
    rwa [h3] at h2
  have hc : HasDerivAt (fun θ' : ℝ => 2*Real.cos (2*θ')) (-4 * Real.sin (2*θ)) θ := by
    have h1 : HasDerivAt (fun θ' : ℝ => 2*θ') 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2:ℝ)
    have h2 := h1.cos
    have h4 : -(Real.sin (2*θ)) * 2 = -2 * Real.sin (2*θ) := by ring
    rw [h4] at h2
    have h5 := h2.const_mul (2:ℝ)
    have h6 : 2 * (-2 * Real.sin (2*θ)) = -4 * Real.sin (2*θ) := by ring
    rwa [h6] at h5
  have hp := hs.mul hc
  have hv : 2 * Real.cos (2*θ) * (2*Real.cos (2*θ)) + Real.sin (2*θ) * (-4 * Real.sin (2*θ))
      = 4*(Real.cos (2*θ))^2 - 4*(Real.sin (2*θ))^2 := by ring
  rw [hv] at hp
  exact hp.deriv

theorem WtoW_f_deriv_gam2 (θ : ℝ) :
    deriv (fun θ' : ℝ => Real.sin (2*θ') * (4*(Real.cos (2*θ'))^2 - 4*(Real.sin (2*θ'))^2)) θ
      = 8*(Real.cos (2*θ))^3 - 40*(Real.sin (2*θ))^2 * Real.cos (2*θ) := by
  have hs : HasDerivAt (fun θ' : ℝ => Real.sin (2*θ')) (2 * Real.cos (2*θ)) θ := by
    have h1 : HasDerivAt (fun θ' : ℝ => 2*θ') 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2:ℝ)
    have h2 := h1.sin
    have h3 : Real.cos (2*θ) * 2 = 2 * Real.cos (2*θ) := by ring
    rwa [h3] at h2
  have hcos1 : HasDerivAt (fun θ' : ℝ => Real.cos (2*θ')) (-2 * Real.sin (2*θ)) θ := by
    have h1 : HasDerivAt (fun θ' : ℝ => 2*θ') 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2:ℝ)
    have h2 := h1.cos
    have h3 : -(Real.sin (2*θ)) * 2 = -2 * Real.sin (2*θ) := by ring
    rwa [h3] at h2
  have hsin1 : HasDerivAt (fun θ' : ℝ => Real.sin (2*θ')) (2 * Real.cos (2*θ)) θ := hs
  have hc2' : HasDerivAt (fun θ' : ℝ => 4*(Real.cos (2*θ'))^2)
      (4*(2*Real.cos (2*θ)*(-(2*Real.sin (2*θ))))) θ := by
    have h := (hcos1.pow 2).const_mul (4:ℝ)
    simpa [mul_assoc, mul_comm, mul_left_comm] using h
  have hs2' : HasDerivAt (fun θ' : ℝ => 4*(Real.sin (2*θ'))^2)
      (4*(2*Real.sin (2*θ)*(2*Real.cos (2*θ)))) θ := by
    have h := (hsin1.pow 2).const_mul (4:ℝ)
    simpa [mul_assoc, mul_comm, mul_left_comm] using h
  have hc : HasDerivAt (fun θ' : ℝ => 4*(Real.cos (2*θ'))^2 - 4*(Real.sin (2*θ'))^2)
      (4*(2*Real.cos (2*θ)*(-(2*Real.sin (2*θ)))) - 4*(2*Real.sin (2*θ)*(2*Real.cos (2*θ)))) θ :=
    hc2'.sub hs2'
  have hp := hs.mul hc
  have hv : 2 * Real.cos (2*θ) * (4*(Real.cos (2*θ))^2 - 4*(Real.sin (2*θ))^2)
      + Real.sin (2*θ) * (4*(2*Real.cos (2*θ)*(-(2*Real.sin (2*θ))))
          - 4*(2*Real.sin (2*θ)*(2*Real.cos (2*θ))))
      = 8*(Real.cos (2*θ))^3 - 40*(Real.sin (2*θ))^2 * Real.cos (2*θ) := by ring
  rw [hv] at hp
  exact hp.deriv

/-! ## The angular factor `D_θ^i (sin (2·)) = sin (2·) · sigCoeff i` -/

theorem WtoW_f_DthIter_sin_two_1 : DthIter 1 (fun z θ => Real.sin (2 * θ))
    = fun z θ => Real.sin (2 * θ) * (2*Real.cos (2*θ)) := by
  funext z θ
  simp only [DthIter_succ, DthIter_zero, Dth, pth]
  rw [WtoW_f_deriv_sin_two]

theorem WtoW_f_DthIter_sin_two_2 : DthIter 2 (fun z θ => Real.sin (2 * θ))
    = fun z θ => Real.sin (2 * θ) * (4*(Real.cos (2*θ))^2 - 4*(Real.sin (2*θ))^2) := by
  have hstep : DthIter 2 (fun z θ => Real.sin (2 * θ))
      = Dth (DthIter 1 (fun z θ => Real.sin (2 * θ))) := by
    rw [show (2:ℕ) = 1+1 from rfl, DthIter_succ]
  rw [hstep, WtoW_f_DthIter_sin_two_1]
  funext z θ
  simp only [Dth, pth]
  rw [WtoW_f_deriv_gam1]

theorem WtoW_f_DthIter_sin_two_3 : DthIter 3 (fun z θ => Real.sin (2 * θ))
    = fun z θ => Real.sin (2 * θ)
        * (8*(Real.cos (2*θ))^3 - 40*(Real.sin (2*θ))^2 * Real.cos (2*θ)) := by
  have hstep : DthIter 3 (fun z θ => Real.sin (2 * θ))
      = Dth (DthIter 2 (fun z θ => Real.sin (2 * θ))) := by
    rw [show (3:ℕ) = 2+1 from rfl, DthIter_succ]
  rw [hstep, WtoW_f_DthIter_sin_two_2]
  funext z θ
  simp only [Dth, pth]
  rw [WtoW_f_deriv_gam2]

theorem WtoW_f_DthIter_sin_two_eq (i : ℕ) (hi : i ≤ 3) (z θ : ℝ) :
    DthIter i (fun z θ => Real.sin (2 * θ)) z θ = Real.sin (2 * θ) * sigCoeff i θ := by
  interval_cases i
  · simp [DthIter, sigCoeff]
  · rw [WtoW_f_DthIter_sin_two_1]; simp [sigCoeff]
  · rw [WtoW_f_DthIter_sin_two_2]; simp [sigCoeff]
  · rw [WtoW_f_DthIter_sin_two_3]; simp [sigCoeff]

theorem WtoW_f_sigCoeff_bound (i : ℕ) (hi : i ≤ 3) (θ : ℝ) : |sigCoeff i θ| ≤ 48 := by
  interval_cases i
  · simp [sigCoeff]
  · rw [show sigCoeff 1 θ = 2 * Real.cos (2*θ) from rfl, abs_mul]
    have h1 : |(2:ℝ)| = 2 := by norm_num
    rw [h1]
    nlinarith [Real.abs_cos_le_one (2*θ)]
  · rw [show sigCoeff 2 θ = 4*(Real.cos (2*θ))^2 - 4*(Real.sin (2*θ))^2 from rfl]
    have h4c : |4*(Real.cos (2*θ))^2| ≤ 4 := by
      rw [abs_mul, abs_pow]; norm_num
      nlinarith [Real.abs_cos_le_one (2*θ), abs_nonneg (Real.cos (2*θ))]
    have h4s : |4*(Real.sin (2*θ))^2| ≤ 4 := by
      rw [abs_mul, abs_pow]; norm_num
      nlinarith [Real.abs_sin_le_one (2*θ), abs_nonneg (Real.sin (2*θ))]
    calc |4*(Real.cos (2*θ))^2 - 4*(Real.sin (2*θ))^2|
        ≤ |4*(Real.cos (2*θ))^2| + |4*(Real.sin (2*θ))^2| := abs_sub _ _
      _ ≤ 4 + 4 := add_le_add h4c h4s
      _ ≤ 48 := by norm_num
  · rw [show sigCoeff 3 θ = 8*(Real.cos (2*θ))^3 - 40*(Real.sin (2*θ))^2 * Real.cos (2*θ) from rfl]
    have hc1 : |Real.cos (2*θ)| ≤ 1 := Real.abs_cos_le_one _
    have hs1 : |Real.sin (2*θ)| ≤ 1 := Real.abs_sin_le_one _
    have hc1nn : 0 ≤ |Real.cos (2*θ)| := abs_nonneg _
    have hs1nn : 0 ≤ |Real.sin (2*θ)| := abs_nonneg _
    have hc3 : |Real.cos (2*θ)|^3 ≤ 1 := pow_le_one₀ hc1nn hc1
    have hs2 : |Real.sin (2*θ)|^2 ≤ 1 := pow_le_one₀ hs1nn hs1
    have h8c : |8*(Real.cos (2*θ))^3| ≤ 8 := by
      rw [abs_mul, abs_pow, show |(8:ℝ)| = 8 by norm_num]
      nlinarith [hc3]
    have h40 : |40*(Real.sin (2*θ))^2 * Real.cos (2*θ)| ≤ 40 := by
      rw [abs_mul, abs_mul, abs_pow, show |(40:ℝ)| = 40 by norm_num]
      nlinarith [hs2, hc1, hs1nn, hc1nn]
    calc |8*(Real.cos (2*θ))^3 - 40*(Real.sin (2*θ))^2 * Real.cos (2*θ)|
        ≤ |8*(Real.cos (2*θ))^3| + |40*(Real.sin (2*θ))^2 * Real.cos (2*θ)| := abs_sub _ _
      _ ≤ 8 + 40 := add_le_add h8c h40
      _ ≤ 48 := by norm_num

/-! ## The term bound from the `𝒲^{4,∞}`-norm -/

theorem WtoW_f_term (α : ℝ) (f : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hmem : Work.Spaces.WlInfMem α 4 (Work.Spaces.pth f))
    (j c : ℕ) (hj : j ≤ 3) (hjc : c + j ≤ 4)
    (z : ℝ) (hz : z ∈ Work.Spaces.Iz) (θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    |(z + 1) ^ c * Work.Spaces.pzIter c (Work.Spaces.DthIter j (Work.Spaces.pth f)) z θ|
      ≤ 2 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f) := by
  have hWnn : 0 ≤ Work.Spaces.WlInf α 4 (Work.Spaces.pth f) := by
    rw [Work.Spaces.WlInf]
    exact add_nonneg (Work.Spaces.wlZSum_nonneg α 4 (Work.Spaces.pth f) hmem)
      (Work.Spaces.wlThSum_nonneg α 4 (Work.Spaces.pth f) hmem)
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · subst hj0
    simp only [Work.Spaces.DthIter_zero]
    have h := Work.Spaces.WlInf_z_bound α 4 (Work.Spaces.pth f) hmem c (by omega) z θ hz hθ
    linarith
  · have hj1 : 1 ≤ j := hjpos
    have hs0 : 0 ≤ Real.sin (2*θ) := WtoW_sin2_nonneg hθ
    have hs1 : Real.sin (2*θ) ≤ 1 := WtoW_sin2_le_one θ
    have hrp : (α + Real.sin (2*θ)) * (Real.sin (2*θ)) ^ (α/5) ≤ 2 :=
      Work.Spaces.add_mul_rpow_le_two hα hα1 hs0 hs1
    have hz0 : (0:ℝ) ≤ z := hz
    have hz1 : (0:ℝ) < (z+1)^c := pow_pos (by linarith : (0:ℝ) < z + 1) c
    have h := Work.Spaces.pz_Dth_sup_bound α hα 4 (Work.Spaces.pth f) hmem j c hj1
      (by omega) z θ hz hθ
    rw [abs_mul, abs_of_pos hz1]
    have h2 : (z+1)^c * |Work.Spaces.pzIter c (Work.Spaces.DthIter j (Work.Spaces.pth f)) z θ|
        ≤ (z+1)^c * (Work.Spaces.WlInf α 4 (Work.Spaces.pth f) / (z+1)^c
            * ((α + Real.sin (2*θ)) * (Real.sin (2*θ)) ^ (α/5))) :=
      mul_le_mul_of_nonneg_left h (le_of_lt hz1)
    have h3 : (z+1)^c * (Work.Spaces.WlInf α 4 (Work.Spaces.pth f) / (z+1)^c
            * ((α + Real.sin (2*θ)) * (Real.sin (2*θ)) ^ (α/5)))
        = Work.Spaces.WlInf α 4 (Work.Spaces.pth f)
            * ((α + Real.sin (2*θ)) * (Real.sin (2*θ)) ^ (α/5)) := by
      field_simp
    rw [h3] at h2
    have h4 : Work.Spaces.WlInf α 4 (Work.Spaces.pth f)
            * ((α + Real.sin (2*θ)) * (Real.sin (2*θ)) ^ (α/5))
        ≤ Work.Spaces.WlInf α 4 (Work.Spaces.pth f) * 2 :=
      mul_le_mul_of_nonneg_left hrp hWnn
    linarith

/-! ## Linearity of `pzIter` over a finite sum of angular-weighted functions -/

theorem WtoW_f_pzIter_sum_const_mul {ι : Type*} (s : Finset ι) (φ : ι → ℝ → ℝ)
    (X : ι → ℝ → ℝ → ℝ) (c : ℕ) (z θ : ℝ)
    (h : ∀ i ∈ s, ContDiffAt ℝ ⊤ (fun z' => X i z' θ) z) :
    Work.Spaces.pzIter c (fun z θ => ∑ i ∈ s, φ i θ * X i z θ) z θ
      = ∑ i ∈ s, φ i θ * Work.Spaces.pzIter c (X i) z θ := by
  rw [Work.Spaces.pzIter_eq_iteratedDeriv,
    Work.Spaces.iteratedDeriv_sum_const_mul s (fun i => φ i θ)
      (fun i z' => X i z' θ) c z (fun i hi => (h i hi).of_le le_top)]
  exact Finset.sum_congr rfl fun i hi => by rw [Work.Spaces.pzIter_eq_iteratedDeriv]

/-! ## The Leibniz expansion of `D_θ^{b+1} f` -/

theorem WtoW_f_expand (f : ℝ → ℝ → ℝ) (hsm : SmoothNbhd f) (b : ℕ) (hb : b ≤ 3) :
    ∀ z' ∈ Set.Ioi (-1), ∀ θ ∈ Set.Ioo (-1) (π/2 + 1),
      DthIter (b+1) f z' θ
        = ∑ i ∈ Finset.range (b+1),
            ((b.choose i : ℝ) * (Real.sin (2*θ) * sigCoeff i θ))
              * DthIter (b - i) (pth f) z' θ := by
  intro z' hz' θ hθU
  have hDth1 : DthIter 1 f = Dth f := by
    rw [show (1:ℕ) = 0 + 1 from rfl, DthIter_succ, DthIter_zero]
  have hstep1 : DthIter (b+1) f = DthIter b (Dth f) := by
    rw [← hDth1]; exact (DthIter_add_right b 1 f).symm
  rw [hstep1]
  have hg : ContDiffOn ℝ ⊤ (fun θ' : ℝ => Real.sin (2*θ')) (Set.Ioo (-1) (π/2 + 1)) := by
    fun_prop
  have hf : ContDiffOn ℝ ⊤ (fun θ' : ℝ => pth f z' θ') (Set.Ioo (-1) (π/2 + 1)) := by
    have h := (SmoothNbhd.pth hsm).comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun θ' hθ' => show (z', θ') ∈ nbhU from ⟨hz', hθ'⟩)
    simpa [Function.comp_def, Function.uncurry] using h
  have hlei := DthIter_mul b (fun z θ => Real.sin (2 * θ)) (pth f) z'
    (Set.Ioo (-1) (π/2 + 1)) isOpen_Ioo hg hf θ hθU
  rw [show Dth f = fun z θ => Real.sin (2*θ) * pth f z θ from rfl]
  rw [hlei]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi3 : i ≤ 3 := by have := Finset.mem_range.mp hi; omega
  rw [WtoW_f_DthIter_sin_two_eq i hi3 z' θ]
  ring

/-! ## The main estimate -/

theorem WtoW_f_bound : ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.Spaces.SmoothNbhd f → Work.Spaces.VanishTheta f →
    Work.Spaces.WlInfMem α 4 (Work.Spaces.pth f) →
    ∀ (c a : ℕ), c + a ≤ 4 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |(z + 1) ^ c * Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ|
        ≤ K * Work.Spaces.WlInf α 4 (Work.Spaces.pth f) * Real.sin (2 * θ) := by
  obtain ⟨K0, hK0pos, hK0⟩ := WtoW_f_zero
  refine ⟨max 1000 K0, by positivity, ?_⟩
  intro α f hα hα1 hsm hv hmem c a hca z hz θ hθ
  have hWnn : 0 ≤ WlInf α 4 (pth f) := by
    rw [WlInf]
    exact add_nonneg (wlZSum_nonneg α 4 (pth f) hmem) (wlThSum_nonneg α 4 (pth f) hmem)
  have hsnn : 0 ≤ Real.sin (2*θ) := WtoW_sin2_nonneg hθ
  have hzpos : (-1:ℝ) < z := by have h0 : (0:ℝ) ≤ z := hz; linarith
  rcases Nat.eq_zero_or_pos a with ha0 | hapos
  · subst ha0
    have h := hK0 α f hα hα1 hsm hv hmem c (by omega) z hz θ hθ
    calc |(z + 1) ^ c * Work.Spaces.pzIter c (Work.Spaces.DthIter 0 f) z θ|
        = |(z+1)^c * pzIter c f z θ| := rfl
      _ ≤ K0 * WlInf α 4 (pth f) * Real.sin (2*θ) := h
      _ ≤ max 1000 K0 * WlInf α 4 (pth f) * Real.sin (2*θ) := by
          apply mul_le_mul_of_nonneg_right _ hsnn
          apply mul_le_mul_of_nonneg_right _ hWnn
          exact le_max_right _ _
  · obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    have hb3 : b ≤ 3 := by omega
    have hcb : c + b ≤ 3 := by omega
    have hloc : (fun z' => DthIter (b+1) f z' θ) =ᶠ[𝓝 z]
        (fun z' => ∑ i ∈ Finset.range (b+1),
            ((b.choose i : ℝ) * (Real.sin (2*θ) * sigCoeff i θ)) * DthIter (b-i) (pth f) z' θ) := by
      filter_upwards [isOpen_Ioi.mem_nhds hzpos] with z' hz'
      exact WtoW_f_expand f hsm b hb3 z' hz' θ
        ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    have hpz : pzIter c (DthIter (b+1) f) z θ
        = pzIter c (fun z θ => ∑ i ∈ Finset.range (b+1),
            ((b.choose i : ℝ) * (Real.sin (2*θ) * sigCoeff i θ)) * DthIter (b-i) (pth f) z θ) z θ := by
      rw [pzIter_eq_iteratedDeriv, pzIter_eq_iteratedDeriv]
      exact hloc.iteratedDeriv_eq c
    rw [hpz]
    have hlin := WtoW_f_pzIter_sum_const_mul (Finset.range (b+1))
      (fun i θ' => (b.choose i : ℝ) * (Real.sin (2*θ') * sigCoeff i θ'))
      (fun i => DthIter (b-i) (pth f)) c z θ (fun i hi => by
        have hslice : ContDiffOn ℝ ⊤ (fun z' => DthIter (b-i) (pth f) z' θ) (Set.Ioi (-1)) :=
          hardyZ_contDiffOn_slice (DthIter (b-i) (pth f))
            (smoothNbhd_DthIter (SmoothNbhd.pth hsm) (b-i)) hθ
        exact (hslice.contDiffAt (isOpen_Ioi.mem_nhds hzpos)).of_le le_top)
    rw [hlin]
    have hfac : (z+1)^c * (∑ i ∈ Finset.range (b+1),
          ((b.choose i : ℝ) * (Real.sin (2*θ) * sigCoeff i θ)) * pzIter c (DthIter (b-i) (pth f)) z θ)
        = ∑ i ∈ Finset.range (b+1),
            ((b.choose i : ℝ) * (Real.sin (2*θ) * sigCoeff i θ))
              * ((z+1)^c * pzIter c (DthIter (b-i) (pth f)) z θ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i hi => by ring
    rw [hfac]
    have habs : |∑ i ∈ Finset.range (b+1),
          ((b.choose i : ℝ) * (Real.sin (2*θ) * sigCoeff i θ))
            * ((z+1)^c * pzIter c (DthIter (b-i) (pth f)) z θ)|
        ≤ ∑ i ∈ Finset.range (b+1),
            |((b.choose i : ℝ) * (Real.sin (2*θ) * sigCoeff i θ))|
              * |(z+1)^c * pzIter c (DthIter (b-i) (pth f)) z θ| := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i hi => ?_)
      rw [abs_mul]
    refine le_trans habs ?_
    have hsum2 : (∑ i ∈ Finset.range (b+1),
            |((b.choose i : ℝ) * (Real.sin (2*θ) * sigCoeff i θ))|
              * |(z+1)^c * pzIter c (DthIter (b-i) (pth f)) z θ|)
        ≤ ∑ i ∈ Finset.range (b+1),
            ((b.choose i : ℝ) * 48 * Real.sin (2*θ)) * (2 * WlInf α 4 (pth f)) := by
      refine Finset.sum_le_sum fun i hi => ?_
      have hi3 : i ≤ 3 := by have := Finset.mem_range.mp hi; omega
      have hbmi : b - i ≤ 3 := by omega
      have hcmi : c + (b - i) ≤ 4 := by omega
      have h1 : |((b.choose i : ℝ) * (Real.sin (2*θ) * sigCoeff i θ))|
          ≤ (b.choose i : ℝ) * 48 * Real.sin (2*θ) := by
        have hb1 : |sigCoeff i θ| ≤ 48 := WtoW_f_sigCoeff_bound i hi3 θ
        have hbc : |(b.choose i : ℝ)| = (b.choose i : ℝ) :=
          abs_of_nonneg (by positivity)
        have hs2 : |Real.sin (2*θ) * sigCoeff i θ| ≤ Real.sin (2*θ) * 48 := by
          rw [abs_mul, abs_of_nonneg hsnn]
          exact mul_le_mul_of_nonneg_left hb1 hsnn
        rw [abs_mul, hbc]
        calc (b.choose i : ℝ) * |Real.sin (2*θ) * sigCoeff i θ|
            ≤ (b.choose i : ℝ) * (Real.sin (2*θ) * 48) :=
              mul_le_mul_of_nonneg_left hs2 (by positivity)
          _ = (b.choose i : ℝ) * 48 * Real.sin (2*θ) := by ring
      have h2 : |(z+1)^c * pzIter c (DthIter (b-i) (pth f)) z θ| ≤ 2 * WlInf α 4 (pth f) :=
        WtoW_f_term α f hα hα1 hmem (b-i) c hbmi hcmi z hz θ hθ
      exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    refine le_trans hsum2 ?_
    have hsum3 : (∑ i ∈ Finset.range (b+1),
            ((b.choose i : ℝ) * 48 * Real.sin (2*θ)) * (2 * WlInf α 4 (pth f)))
        ≤ 1000 * WlInf α 4 (pth f) * Real.sin (2*θ) := by
      have h1 : (∑ i ∈ Finset.range (b+1),
            ((b.choose i : ℝ) * 48 * Real.sin (2*θ)) * (2 * WlInf α 4 (pth f)))
          = (∑ i ∈ Finset.range (b+1), (b.choose i : ℝ))
              * (96 * Real.sin (2*θ) * WlInf α 4 (pth f)) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i hi => by ring
      rw [h1]
      have hcast : (∑ i ∈ Finset.range (b+1), (b.choose i : ℝ)) = (2:ℝ)^b := by
        rw [← Nat.cast_sum, Nat.sum_range_choose]
        push_cast
        ring
      rw [hcast]
      have hb : (2:ℝ)^b ≤ 8 := by
        calc (2:ℝ)^b ≤ 2^3 := pow_le_pow_right₀ (by norm_num) hb3
          _ = 8 := by norm_num
      have hsW : 0 ≤ 96 * Real.sin (2*θ) * WlInf α 4 (pth f) := by
        have h1 : (0:ℝ) ≤ 96 * Real.sin (2*θ) := by positivity
        exact mul_nonneg h1 hWnn
      have h2 : (2:ℝ)^b * (96 * Real.sin (2*θ) * WlInf α 4 (pth f))
          ≤ 8 * (96 * Real.sin (2*θ) * WlInf α 4 (pth f)) :=
        mul_le_mul_of_nonneg_right hb hsW
      refine le_trans h2 ?_
      have h3 : 8 * (96 * Real.sin (2*θ) * WlInf α 4 (pth f))
          ≤ 1000 * WlInf α 4 (pth f) * Real.sin (2*θ) := by
        have hsW2 : 0 ≤ Real.sin (2*θ) * WlInf α 4 (pth f) := mul_nonneg hsnn hWnn
        nlinarith [hsW2]
      exact h3
    refine le_trans hsum3 ?_
    apply mul_le_mul_of_nonneg_right _ hsnn
    apply mul_le_mul_of_nonneg_right _ hWnn
    exact le_max_left _ _

end Work.Elliptic
