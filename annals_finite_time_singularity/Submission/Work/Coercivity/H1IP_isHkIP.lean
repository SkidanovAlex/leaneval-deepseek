/-
# `IsHkIP α 1 (H1IP α)`: the `ℋ¹` inner product is an admissible inner product

Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the incompressible
Euler equations on `ℝ³`*, Annals of Math. **194** (2021), §"Higher order derivatives and
the inner product on `ℋ^k`".  The paper's `ℋ¹` inner product

  `H1IP α f g = 10 (D_zf,D_zg)_{w²/sin^η} + 10¹⁰ (f,g)_{w²/sin^η}
                 + 10¹⁷ (f,g)_{w²} + 10²¹ (D_θf,D_θg)_{w²/sin^γ}`

satisfies the five clauses of the specification `IsHkIP α 1`:

* *additivity* and *homogeneity* in the first argument (`H1IP_add_eq` below and
  `H1IP_homog`);
* *nonnegativity* of the diagonal (`H1IP_nonneg`);
* comparability with the `ℋ¹` norm on the admissible class (`H1IP_le_self`, and
  `H1IP_upper` with the constant `10²²`);
* coercivity of `𝓛_Γ^T`, i.e. the paper's Corollary `FirstDerivativeCoercivity`
  (`H1IP_coercive`), carrying the analytic hypotheses `IBP`, `HardyHyp`,
  `CoerciveData`, `GammaL2Bnd`, `GammaPointwiseBnd` of the chapter.

## The additivity proof

Additivity is the one clause that is *not* formal bookkeeping: `wip ρ A B = ∫∫ A B ρ` is
the total Bochner integral, which for a non-integrable integrand is Lean's junk value `0`,
so additivity needs the pairing integrands to be honest.  For smooth profiles in `H¹` this
holds because each of the four pairing integrands is the *product of two blocks*

  `D_z a·D_z b·ρη = XetaDz a · XetaDz b`,  `a·b·ρη = Xeta a · Xeta b`,
  `a·b·w² = Xw a · Xw b`,  `D_θ a·D_θ b·ργ = XgamDth α a · XgamDth α b`

(`H1IPAddDefs`), each block having an honest `L²` integral by `HkMem α 1`
(`L2Mem_DzIter_Hwt`, `L2Mem_mixed_Wt_gen`, `L2Mem_Xw`); Cauchy–Schwarz in the form
`I2Mem_mul_of_ae` then makes the product integrand honestly iterated-integrable
(`PairHonest`), whence `wip_add_of_PairHonest` splits the integral.  The measurable
integrability inputs for the pairing blocks are `aesm_blocks`, and the identification of
the four products with the pairing integrands on `Iθ` is `Xeta_mul_eq`, `XetaDz_mul_eq`,
`XgamDth_mul_eq` (the last two at the two endpoints `θ = 0, π/2`, where Lean's totalised
`rpow` sets both sides to `0`).

The counterexample of `H1IP_add_fails.lean` — a two-valued non-measurable `φ` — is excluded
precisely by the `SmoothNbhd` hypotheses of the clause: for smooth profiles the weighted
blocks are continuous on the open quadrant, hence a.e. strongly measurable, so no pairing
is a junk value.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.Coercivity.FirstDerivativeCoercivity
import Submission.Work.Coercivity.Eztheta1_eq_HkSq_one
import Submission.Work.Coercivity.H1IPAddDefs
import Submission.Work.Coercivity.H1IP_nonneg
import Submission.Work.Coercivity.H1IP_homog
import Submission.Work.Coercivity.H1IP_le_self
import Submission.Work.Coercivity.H1IP_upper
import Submission.Work.Coercivity.H1IP_coercive
import Submission.Work.Coercivity.I2Mem_mul_of_ae
import Submission.Work.Coercivity.wip_add_of_PairHonest
import Submission.Work.Coercivity.aesm_blocks
import Submission.Work.Coercivity.L2Mem_Xw
import Submission.Work.Coercivity.Xeta_mul_eq
import Submission.Work.Coercivity.XetaDz_mul_eq
import Submission.Work.Coercivity.XgamDth_mul_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## MY WORK -/

/-- Congruence of `wip` in its first argument, on the integration domain. -/
theorem wip_congr_on {ρ A A' B : ℝ → ℝ → ℝ}
    (h : ∀ z ∈ Spaces.Iz, ∀ θ ∈ Spaces.Iθ, A z θ = A' z θ) : wip ρ A B = wip ρ A' B := by
  unfold wip
  refine MeasureTheory.setIntegral_congr_fun (s := Spaces.Iz) measurableSet_Ici (fun z hz => ?_)
  refine MeasureTheory.setIntegral_congr_fun (s := Spaces.Iθ) measurableSet_Icc (fun θ hθ => ?_)
  rw [h z hz θ hθ]

/-- Congruence of `I2Mem` under pointwise equality on the quadrant. -/
theorem I2Mem_congr {F G : ℝ → ℝ → ℝ}
    (h : ∀ z ∈ Spaces.Iz, ∀ θ ∈ Spaces.Iθ, F z θ = G z θ) (hF : I2Mem F) : I2Mem G := by
  refine ⟨fun z hz => (hF.1 z hz).congr ?_, (hF.2).congr ?_⟩
  · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => h z hz θ hθ)
  · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici
      (fun z hz => MeasureTheory.setIntegral_congr_fun (s := Spaces.Iθ) measurableSet_Icc
        (fun θ hθ => h z hz θ hθ))

/-- The trivial pairing identity for the plain `w²` weight. -/
theorem Xw_mul_eq (a b : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Xw a z θ * Xw b z θ = a z θ * b z θ * lamW z θ := by
  simp only [Xw, lamW]; ring

/-! ## The four honest pairings -/

theorem PairHonest_eta (α : ℝ) (a b : ℝ → ℝ → ℝ) (hsa : Spaces.SmoothNbhd a)
    (hsb : Spaces.SmoothNbhd b) (hma : Spaces.HkMem α 1 a) (hmb : Spaces.HkMem α 1 b) :
    PairHonest lamEta a b := by
  have hbl := aesm_blocks α a b hsa hsb
  refine I2Mem_congr (fun z hz θ hθ => Xeta_mul_eq a b z θ hθ) ?_
  exact I2Mem_mul_of_ae (Xeta a) (Xeta b)
    (L2Mem_DzIter_Hwt α 1 a hsa hma 0 (by norm_num))
    (L2Mem_DzIter_Hwt α 1 b hsb hmb 0 (by norm_num)) hbl.1.2 hbl.1.1

theorem PairHonest_etaDz (α : ℝ) (a b : ℝ → ℝ → ℝ) (hsa : Spaces.SmoothNbhd a)
    (hsb : Spaces.SmoothNbhd b) (hma : Spaces.HkMem α 1 a) (hmb : Spaces.HkMem α 1 b) :
    PairHonest lamEta (Spaces.Dz a) (Spaces.Dz b) := by
  have hbl := aesm_blocks α a b hsa hsb
  refine I2Mem_congr (fun z hz θ hθ => XetaDz_mul_eq a b z θ hθ) ?_
  exact I2Mem_mul_of_ae (XetaDz a) (XetaDz b)
    (L2Mem_DzIter_Hwt α 1 a hsa hma 1 (by norm_num))
    (L2Mem_DzIter_Hwt α 1 b hsb hmb 1 (by norm_num)) hbl.2.1.2 hbl.2.1.1

theorem PairHonest_gam (α : ℝ) (a b : ℝ → ℝ → ℝ) (hsa : Spaces.SmoothNbhd a)
    (hsb : Spaces.SmoothNbhd b) (hma : Spaces.HkMem α 1 a) (hmb : Spaces.HkMem α 1 b) :
    PairHonest (lamGam α) (Spaces.Dth a) (Spaces.Dth b) := by
  have hbl := aesm_blocks α a b hsa hsb
  refine I2Mem_congr (fun z hz θ hθ => XgamDth_mul_eq α a b z θ hθ) ?_
  exact I2Mem_mul_of_ae (XgamDth α a) (XgamDth α b)
    (L2Mem_mixed_Wt_gen α 1 a hsa hma 1 0 (by norm_num) (by norm_num))
    (L2Mem_mixed_Wt_gen α 1 b hsb hmb 1 0 (by norm_num) (by norm_num))
    hbl.2.2.1.2 hbl.2.2.1.1

theorem PairHonest_w (α : ℝ) (a b : ℝ → ℝ → ℝ) (hsa : Spaces.SmoothNbhd a)
    (hsb : Spaces.SmoothNbhd b) (hma : Spaces.HkMem α 1 a) (hmb : Spaces.HkMem α 1 b) :
    PairHonest lamW a b := by
  have hbl := aesm_blocks α a b hsa hsb
  refine I2Mem_congr (fun z _ θ _ => Xw_mul_eq a b z θ) ?_
  exact I2Mem_mul_of_ae (Xw a) (Xw b) (L2Mem_Xw α a hsa hma) (L2Mem_Xw α b hsb hmb)
    hbl.2.2.2.2 hbl.2.2.2.1

/-! ## Derivative linearity -/

theorem Dz_add_smooth {a₁ a₂ : ℝ → ℝ → ℝ} (h₁ : Spaces.SmoothNbhd a₁)
    (h₂ : Spaces.SmoothNbhd a₂) (z : ℝ) (hz : z ∈ Spaces.Iz) (θ : ℝ) (hθ : θ ∈ Spaces.Iθ) :
    Spaces.Dz (a₁ + a₂) z θ = Spaces.Dz a₁ z θ + Spaces.Dz a₂ z θ := by
  have hp : (z, θ) ∈ Spaces.U := Spaces.mem_U_of_dom hz hθ
  have hd : ∀ a : ℝ → ℝ → ℝ, Spaces.SmoothNbhd a → DifferentiableAt ℝ (fun z' => a z' θ) z :=
    fun a ha => Spaces.differentiableAt_curry_left
      (((ha : ContDiffOn ℝ ⊤ (Function.uncurry a) Spaces.U).differentiableOn (n := ⊤)
        (by simp)).differentiableAt (Spaces.isOpen_U.mem_nhds hp))
  simp only [Spaces.Dz, Spaces.pz]
  rw [show (fun z' => (a₁ + a₂) z' θ) = (fun z' => a₁ z' θ) + (fun z' => a₂ z' θ) from rfl,
    deriv_add (hd a₁ h₁) (hd a₂ h₂)]
  ring

theorem Dth_add_smooth {a₁ a₂ : ℝ → ℝ → ℝ} (h₁ : Spaces.SmoothNbhd a₁)
    (h₂ : Spaces.SmoothNbhd a₂) (z : ℝ) (hz : z ∈ Spaces.Iz) (θ : ℝ) (hθ : θ ∈ Spaces.Iθ) :
    Spaces.Dth (a₁ + a₂) z θ = Spaces.Dth a₁ z θ + Spaces.Dth a₂ z θ := by
  have hp : (z, θ) ∈ Spaces.U := Spaces.mem_U_of_dom hz hθ
  have hd : ∀ a : ℝ → ℝ → ℝ, Spaces.SmoothNbhd a → DifferentiableAt ℝ (fun θ' => a z θ') θ :=
    fun a ha => Spaces.differentiableAt_curry_right
      (((ha : ContDiffOn ℝ ⊤ (Function.uncurry a) Spaces.U).differentiableOn (n := ⊤)
        (by simp)).differentiableAt (Spaces.isOpen_U.mem_nhds hp))
  simp only [Spaces.Dth, Spaces.pth]
  rw [show (fun θ' => (a₁ + a₂) z θ') = (fun θ' => a₁ z θ') + (fun θ' => a₂ z θ') from rfl,
    deriv_add (hd a₁ h₁) (hd a₂ h₂)]
  ring

/-! ## Additivity of `H1IP` in its first argument -/

theorem H1IP_add_eq (α : ℝ) (a₁ a₂ b : ℝ → ℝ → ℝ)
    (hs₁ : Spaces.SmoothNbhd a₁) (hs₂ : Spaces.SmoothNbhd a₂) (hsb : Spaces.SmoothNbhd b)
    (hm₁ : Spaces.HkMem α 1 a₁) (hm₂ : Spaces.HkMem α 1 a₂) (hmb : Spaces.HkMem α 1 b) :
    H1IP α (a₁ + a₂) b = H1IP α a₁ b + H1IP α a₂ b := by
  have hEtaW : (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)) = lamEta := rfl
  have hGamW : (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))) = lamGam α := rfl
  have hWtW : (fun z _ => Spaces.w z ^ 2) = lamW := rfl
  have h1 : wip lamEta (Spaces.Dz (a₁ + a₂)) (Spaces.Dz b)
      = wip lamEta (Spaces.Dz a₁) (Spaces.Dz b) + wip lamEta (Spaces.Dz a₂) (Spaces.Dz b) := by
    rw [wip_congr_on (A := Spaces.Dz (a₁ + a₂)) (A' := Spaces.Dz a₁ + Spaces.Dz a₂)
      (fun z hz θ hθ => Dz_add_smooth hs₁ hs₂ z hz θ hθ)]
    exact wip_add_of_PairHonest lamEta (Spaces.Dz a₁) (Spaces.Dz a₂) (Spaces.Dz b)
      (PairHonest_etaDz α a₁ b hs₁ hsb hm₁ hmb)
      (PairHonest_etaDz α a₂ b hs₂ hsb hm₂ hmb)
  have h2 : wip lamEta (a₁ + a₂) b = wip lamEta a₁ b + wip lamEta a₂ b :=
    wip_add_of_PairHonest lamEta a₁ a₂ b (PairHonest_eta α a₁ b hs₁ hsb hm₁ hmb)
      (PairHonest_eta α a₂ b hs₂ hsb hm₂ hmb)
  have h3 : wip lamW (a₁ + a₂) b = wip lamW a₁ b + wip lamW a₂ b :=
    wip_add_of_PairHonest lamW a₁ a₂ b (PairHonest_w α a₁ b hs₁ hsb hm₁ hmb)
      (PairHonest_w α a₂ b hs₂ hsb hm₂ hmb)
  have h4 : wip (lamGam α) (Spaces.Dth (a₁ + a₂)) (Spaces.Dth b)
      = wip (lamGam α) (Spaces.Dth a₁) (Spaces.Dth b)
        + wip (lamGam α) (Spaces.Dth a₂) (Spaces.Dth b) := by
    rw [wip_congr_on (A := Spaces.Dth (a₁ + a₂)) (A' := Spaces.Dth a₁ + Spaces.Dth a₂)
      (fun z hz θ hθ => Dth_add_smooth hs₁ hs₂ z hz θ hθ)]
    exact wip_add_of_PairHonest (lamGam α) (Spaces.Dth a₁) (Spaces.Dth a₂) (Spaces.Dth b)
      (PairHonest_gam α a₁ b hs₁ hsb hm₁ hmb)
      (PairHonest_gam α a₂ b hs₂ hsb hm₂ hmb)
  simp only [H1IP]
  rw [hEtaW, hGamW, hWtW, h1, h2, h3, h4]
  ring

/-! ## `IsHkIP α 1 (H1IP α)` -/

theorem H1IP_isHkIP (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 10 ^ 14)
    (hIBP : ∀ f : ℝ → ℝ → ℝ, HkAdm α 1 f → IBP f)
    (hHH : ∀ f : ℝ → ℝ → ℝ, HkAdm α 1 f → HardyHyp f)
    (hCD : ∀ f : ℝ → ℝ → ℝ, HkAdm α 1 f → CoerciveData α f)
    (hG : GammaL2Bnd α) (hG2 : GammaPointwiseBnd α) :
    IsHkIP α 1 (H1IP α) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f₁ f₂ g hs₁ hs₂ hsg hm₁ hm₂ hmg
    exact H1IP_add_eq α f₁ f₂ g hs₁ hs₂ hsg hm₁ hm₂ hmg
  · intro c f g hsf hsg hmf hmg
    exact H1IP_homog α c f g
  · intro h
    exact H1IP_nonneg α h
  · intro f hf
    exact H1IP_le_self α f (hf.2.1 0 0 (by norm_num)) hf.1
  · obtain ⟨C, hC, hCb⟩ := H1IP_upper α
    exact ⟨C, hC, fun f hf => hCb f (hf.2.1 0 0 (by norm_num)) hf.1 (hCD f hf)⟩
  · exact H1IP_coercive α hα hα1 hIBP hHH hCD hG hG2

end Work.Coercivity
