import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.FTS.BSIdent.Defs
import Submission.Work.Cyl.hasDerivAt_rhoP_rpow_div_snd
import Submission.Work.FTS.BSIdent.Cyl.DecayAux.rho_mul_rpow_weight_le
import Submission.Work.FTS.BSIdent.Cyl.DecayAux.pi_div_two_sub_abs_le_cos
import Submission.Work.FTS.BSIdent.Cyl.DecayAux.abs_deriv_zero_le_of_bound_right
import Submission.Work.FTS.BSIdent.Cyl.DecayAux.hasDerivAt_rhoP_rpow_div_fst
import Submission.Work.FTS.BSIdent.Cyl.DecayAux.hasDerivAt_thetaP_fst
import Submission.Work.FTS.BSIdent.Cyl.DecayAux.PhiOdd_neg_theta_of_pos
import Submission.Work.FTS.BSIdent.Cyl.DecayAux.abs_PhiOdd_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The decay of the ansatz field `psiField (merPsi … · t)`

Elgindi's reconstruction has the meridian stream function

  `merPsi α A B Φ C r z t = ρ(r,z)² · A(τ)⁻¹ · Φ̂(ρ(r,z)^{3α}/B(τ), θ(r,z), τ)`,  `τ = clockInv C t`,

and this file proves that the associated no-swirl field `psiField (merPsi … · t)` decays like
`1/‖x‖` at infinity — the `hdec` clause of the geometric bundle of the ansatz field
(`Work.FTS.BSIdent.AnsatzBundle`).

The proof is a direct computation.  Writing `G = Φ̂(·,·,τ)`, `ρ = rhoP r z`, `θ = thetaP r z`,
`w = ρ^{3α}/B(τ)`, the chain rule gives

  `∂_z ψ = 2 z c G(w,θ) + c (p z w ∂_wG(w,θ) + r ∂_θG(w,θ))`,
  `∂_r ψ = 2 r c G(w,θ) + c (p r w ∂_wG(w,θ) - z ∂_θG(w,θ))`

with `c = A(τ)⁻¹`, `p = 3α`; the hypothesis `hrate` bounds `G` by `(π/2-θ)^q (1+w)^{-λ}` and its
`w`- resp. `θ`-derivative by the same expression with one power of `(1+w)` resp. `(π/2-θ)`
removed.  Since `|z|, r ≤ ρ` and `(π/2-θ) ≤ π/2`, every term is bounded by
`C ρ (1+w)^{-λ} ≤ C · 2 max(1, b^λ)/(1+ρ)`, the last step using `p λ = 3αλ ≥ 3` (`hexp`).  The
term `ψ/r` is handled with the sharp form `π/2-θ ≤ (π/2) cos θ = (π/2) r/ρ` (Jordan's
inequality), which is what makes `ρ²/r · (π/2-θ)^q ≤ C ρ`.

The endpoints `z = 0` (where `θ = 0` and the odd extension need not be differentiable) and
`r = 0` are treated by a one-sided mean value argument, and `z < 0` by the oddness of `ψ` in `z`.
-/

noncomputable section

open scoped Topology

namespace Work.FTS.BSIdent.Cyl

set_option autoImplicit false

/-! ## The meridian stream function and its core -/

/-- The meridian stream function at time `t`, as a function of the meridian coordinates
`(r, x₃)`. -/
noncomputable def merPsiT (α : ℝ) (A B : ℝ → ℝ) (Φ : Work.FTS.BSIdent.Fam)
    (C : Physical.PhysClock) (t : ℝ) : ℝ → ℝ → ℝ :=
  fun r z => Work.FTS.BSIdent.merPsi α A B Φ C r z t

/-- The core of the meridian stream function: `ρ(r,z)² · c · G(ρ(r,z)^p/b, θ(r,z))`. -/
noncomputable def psiCore (p c b : ℝ) (G : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun r z => Work.Cyl.rhoP r z ^ 2 * c * G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)

/-- `merPsiT` is the core `psiCore` with `G` the odd extension of `Φ(·,·,τ)`, `p = 3α`,
`c = A(τ)⁻¹` and `b = B(τ)`. -/
theorem merPsiT_eq_psiCore (α : ℝ) (A B : ℝ → ℝ) (Φ : Work.FTS.BSIdent.Fam)
    (C : Physical.PhysClock) (t : ℝ) :
    merPsiT α A B Φ C t =
      psiCore (Work.FTS.Regularity.pExp α) ((A (Physical.clockInv C t))⁻¹)
        (B (Physical.clockInv C t))
        (fun w θ => Work.FTS.BSIdent.PhiOdd Φ w θ (Physical.clockInv C t)) := by
  funext r z
  simp only [merPsiT, psiCore, Work.FTS.BSIdent.merPsi_apply]

/-! ## The rate hypothesis on the profile -/

/-- **The rate hypothesis of the decay theorem**, as a named predicate: the profile `Φ(·,·,τ)`
and its first two partial derivatives are bounded by the powers of `(π/2-θ)` and `(1+w)` that the
chain rule produces.  It is the conjunction `hrate` of
`decay_psiField_merPsi_of_Phi_decay`, with the time argument made explicit. -/
def PhiRate (Φ : Work.FTS.BSIdent.Fam) (τ C₀ q lam : ℝ) : Prop :=
  ∀ w θ, 0 < w → 0 < θ → θ < Real.pi / 2 →
    |Φ w θ τ| ≤ C₀ * (Real.pi / 2 - θ) ^ q * (1 + w) ^ (-lam) ∧
    |deriv (fun w' => Φ w' θ τ) w| ≤ C₀ * (Real.pi / 2 - θ) ^ q * (1 + w) ^ (-lam - 1) ∧
    |deriv (fun θ' => Φ w θ' τ) θ| ≤ C₀ * (Real.pi / 2 - θ) ^ (q - 1) * (1 + w) ^ (-lam) ∧
    |deriv (fun θ' => deriv (fun θ'' => Φ w θ'' τ) θ') θ|
      ≤ C₀ * (Real.pi / 2 - θ) ^ (q - 2) * (1 + w) ^ (-lam) ∧
    |deriv (fun θ' => deriv (fun w' => Φ w' θ' τ) w) θ|
      ≤ C₀ * (Real.pi / 2 - θ) ^ (q - 1) * (1 + w) ^ (-lam - 1) ∧
    |deriv (fun w' => deriv (fun w'' => Φ w'' θ τ) w') w|
      ≤ C₀ * (Real.pi / 2 - θ) ^ q * (1 + w) ^ (-lam - 2)

/-! ## The two constants -/

/-- The constant in the `(1+ρ)^{-1}` bound for the two partial derivatives of `ψ`. -/
noncomputable def decayKzr (p c C₀ q lam b : ℝ) : ℝ :=
  |c| * C₀ * (Real.pi / 2) ^ (q - 1)
    * (2 * (Real.pi / 2) + p * (Real.pi / 2) + 1)
    * (2 * max 1 (b ^ lam))

/-- The constant in the `(1+ρ)^{-1}` bound for `ψ/r`. -/
noncomputable def decayKq (c C₀ q lam b : ℝ) : ℝ :=
  |c| * C₀ * (Real.pi / 2) ^ q * (2 * max 1 (b ^ lam))

theorem decayKzr_nonneg {p c C₀ q lam b : ℝ} (hC₀ : 0 ≤ C₀) (hp : 0 ≤ p) :
    0 ≤ decayKzr p c C₀ q lam b := by
  have h1 : (0 : ℝ) ≤ (Real.pi / 2) ^ (q - 1) := Real.rpow_nonneg (by positivity) _
  have h2 : (0 : ℝ) ≤ 2 * (Real.pi / 2) + p * (Real.pi / 2) + 1 := by
    have := mul_nonneg hp (by positivity : (0 : ℝ) ≤ Real.pi / 2)
    linarith [Real.pi_pos]
  have h3 : (0 : ℝ) ≤ 2 * max 1 (b ^ lam) :=
    mul_nonneg (by norm_num) (le_trans zero_le_one (le_max_left 1 (b ^ lam)))
  have h4 : (0 : ℝ) ≤ |c| := abs_nonneg c
  rw [decayKzr]
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h4 hC₀) h1) h2) h3

theorem decayKq_nonneg {c C₀ q lam b : ℝ} (hC₀ : 0 ≤ C₀) :
    0 ≤ decayKq c C₀ q lam b := by
  have h1 : (0 : ℝ) ≤ (Real.pi / 2) ^ q := Real.rpow_nonneg (by positivity) _
  have h3 : (0 : ℝ) ≤ 2 * max 1 (b ^ lam) :=
    mul_nonneg (by norm_num) (le_trans zero_le_one (le_max_left 1 (b ^ lam)))
  have h4 : (0 : ℝ) ≤ |c| := abs_nonneg c
  rw [decayKq]
  exact mul_nonneg (mul_nonneg (mul_nonneg h4 hC₀) h1) h3

/-! ## Elementary facts -/

/-- `‖r e_r‖ = r`. -/
theorem norm_radialVec_eq (x : Work.Cyl.R3) :
    ‖Work.Cyl.radialVec x‖ = Work.Cyl.radial x := by
  have h : ‖Work.Cyl.radialVec x‖ ^ 2 = Work.Cyl.radial x ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, Work.Cyl.inner_radialVec_self, Work.Cyl.radial_sq]
  nlinarith [norm_nonneg (Work.Cyl.radialVec x), Work.Cyl.radial_nonneg x]

/-- `‖e₃‖ = 1`. -/
theorem norm_eZ_eq : ‖(Work.Cyl.eZ : Work.Cyl.R3)‖ = 1 := by
  simp [Work.Cyl.eZ, FiniteTimeSingularity.e]

/-- **An odd function has an even derivative.** -/
theorem deriv_odd_eq {f : ℝ → ℝ} (h : ∀ y, f (-y) = - f y) (z : ℝ) :
    deriv f z = deriv f (-z) := by
  have hf : ∀ y, f y = - f (-y) := fun y => by
    have := h (-y); rwa [neg_neg] at this
  by_cases hd : DifferentiableAt ℝ f (-z)
  · have hcomp : HasDerivAt (fun y : ℝ => f (-y)) (deriv f (-z) * (-1)) z :=
      (hd.hasDerivAt).comp z (hasDerivAt_neg z)
    have hneg : HasDerivAt (fun y : ℝ => - f (-y)) (-(deriv f (-z) * (-1))) z := hcomp.neg
    have hfe : f =ᶠ[𝓝 z] fun y : ℝ => - f (-y) := Filter.Eventually.of_forall hf
    have hf' : HasDerivAt f (-(deriv f (-z) * (-1))) z := hneg.congr_of_eventuallyEq hfe
    rw [hf'.deriv]; ring
  · have hz : ¬ DifferentiableAt ℝ f z := by
      intro hz'
      have hz'' : DifferentiableAt ℝ f (- -z) := by simpa using hz'
      have h1 : DifferentiableAt ℝ (fun y : ℝ => f (-y)) (-z) :=
        hz''.comp (-z) ((differentiableAt_id (x := -z)).neg)
      have h2 : DifferentiableAt ℝ (fun y : ℝ => - f (-y)) (-z) := h1.neg
      exact hd (h2.congr_of_eventuallyEq (Filter.Eventually.of_forall hf))
    rw [deriv_zero_of_not_differentiableAt hz, deriv_zero_of_not_differentiableAt hd]

/-- The odd extension inherits the rate of `Φ`, with `(π/2-|θ|)^q` sharpened to
`((π/2) cos θ)^q`. -/
theorem abs_PhiOdd_le_cos {Φ : Work.FTS.BSIdent.Fam} {τ C₀ q lam : ℝ} (hC₀ : 0 ≤ C₀)
    (hq : 0 ≤ q)
    (h0 : ∀ w, 0 < w → Φ w 0 τ = 0)
    (hrate : ∀ w θ, 0 < w → 0 < θ → θ < Real.pi / 2 →
      |Φ w θ τ| ≤ C₀ * (Real.pi / 2 - θ) ^ q * (1 + w) ^ (-lam))
    {w θ : ℝ} (hw : 0 < w) (hθ : |θ| < Real.pi / 2) :
    |Work.FTS.BSIdent.PhiOdd Φ w θ τ|
      ≤ C₀ * (Real.pi / 2) ^ q * (Real.cos θ) ^ q * (1 + w) ^ (-lam) := by
  have habs := abs_lt.1 hθ
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨habs.1, habs.2⟩
  have h1 := DecayAux.abs_PhiOdd_le hC₀ h0 hrate hw hθ
  have h2 : (0 : ℝ) ≤ Real.pi / 2 - |θ| := by linarith [abs_nonneg θ, Real.pi_pos]
  have h3 : Real.pi / 2 - |θ| ≤ Real.pi / 2 * Real.cos θ :=
    DecayAux.pi_div_two_sub_abs_le_cos (le_of_lt hθ)
  have h5 : (Real.pi / 2 - |θ|) ^ q ≤ (Real.pi / 2 * Real.cos θ) ^ q :=
    Real.rpow_le_rpow h2 h3 hq
  have h6 : (Real.pi / 2 * Real.cos θ) ^ q = (Real.pi / 2) ^ q * (Real.cos θ) ^ q :=
    Real.mul_rpow (by positivity) hcos.le
  calc |Work.FTS.BSIdent.PhiOdd Φ w θ τ|
      ≤ C₀ * (Real.pi / 2 - |θ|) ^ q * (1 + w) ^ (-lam) := h1
    _ ≤ C₀ * ((Real.pi / 2) ^ q * (Real.cos θ) ^ q) * (1 + w) ^ (-lam) := by
        rw [h6] at h5
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h5 hC₀)
          (Real.rpow_nonneg (by linarith) _)
    _ = C₀ * (Real.pi / 2) ^ q * (Real.cos θ) ^ q * (1 + w) ^ (-lam) := by ring

/-! ## Oddness of the meridian stream function in the axial variable -/

/-- `z ↦ ψ r z` is odd (for `r > 0`). -/
theorem merPsiT_odd_z {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Physical.PhysClock} {t : ℝ} (hB : 0 < B (Physical.clockInv C t))
    (h0 : ∀ w, 0 < w → Φ w 0 (Physical.clockInv C t) = 0)
    {r z : ℝ} (hr : 0 < r) :
    merPsiT α A B Φ C t r (-z) = -merPsiT α A B Φ C t r z := by
  rw [merPsiT_eq_psiCore]
  simp only [psiCore, Work.Cyl.rhoP_neg, Work.Cyl.thetaP_neg]
  have hw : 0 < Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t) :=
    div_pos (Real.rpow_pos_of_pos (Work.Cyl.rhoP_pos hr z) _) hB
  rw [DecayAux.PhiOdd_neg_theta_of_pos h0 hw]
  ring

/-! ## Elementary comparison lemmas -/

/-- `|z| ≤ ρ(r,z)`. -/
theorem abs_snd_le_rhoP (r z : ℝ) : |z| ≤ Work.Cyl.rhoP r z := by
  have h : (|z| : ℝ) ^ 2 ≤ Work.Cyl.rhoP r z ^ 2 := by
    rw [Work.Cyl.rhoP_sq, sq_abs]; nlinarith [sq_nonneg r]
  nlinarith [abs_nonneg z, Work.Cyl.rhoP_nonneg r z]

/-- `r ≤ ρ(r,z)` for `r ≥ 0`. -/
theorem le_rhoP (r z : ℝ) (hr : 0 ≤ r) : r ≤ Work.Cyl.rhoP r z := by
  have h : r ^ 2 ≤ Work.Cyl.rhoP r z ^ 2 := by
    rw [Work.Cyl.rhoP_sq]; nlinarith [sq_nonneg z]
  nlinarith [Work.Cyl.rhoP_nonneg r z]

/-- `θ(r,z) > 0` for `r, z > 0`. -/
theorem thetaP_pos_of_pos {r z : ℝ} (hr : 0 < r) (hz : 0 < z) : 0 < Work.Cyl.thetaP r z := by
  rw [Work.Cyl.thetaP]
  exact Real.arctan_pos.mpr (div_pos hz hr)

/-- `θ(r,z) < π/2`. -/
theorem thetaP_lt_pi_div_two (r z : ℝ) : Work.Cyl.thetaP r z < Real.pi / 2 :=
  Real.arctan_lt_pi_div_two _

/-- `-π/2 < θ(r,z)`. -/
theorem neg_pi_div_two_lt_thetaP (r z : ℝ) : -(Real.pi / 2) < Work.Cyl.thetaP r z :=
  Real.neg_pi_div_two_lt_arctan _

/-- `|θ(r,z)| < π/2`. -/
theorem abs_thetaP_lt (r z : ℝ) : |Work.Cyl.thetaP r z| < Real.pi / 2 :=
  abs_lt.mpr ⟨neg_pi_div_two_lt_thetaP r z, thetaP_lt_pi_div_two r z⟩

/-- `Φ̂(·,·,τ)` is differentiable on the open quadrant, being `Φ(·,·,τ)` there. -/
theorem diffAt2_PhiOdd {Φ : Work.FTS.BSIdent.Fam} {τ : ℝ}
    (hsm : ∀ w θ, 0 < w → 0 < θ → θ < Real.pi / 2 →
      ContDiffAt ℝ 3 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    {w θ : ℝ} (hw : 0 < w) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    Work.Cyl.DiffAt2 (fun w θ => Work.FTS.BSIdent.PhiOdd Φ w θ τ) w θ := by
  have hmem : {p : ℝ × ℝ | 0 < p.2} ∈ 𝓝 (w, θ) :=
    (isOpen_lt continuous_const continuous_snd).mem_nhds hθ0
  have hev : (fun p : ℝ × ℝ => Φ p.1 p.2 τ) =ᶠ[𝓝 (w, θ)]
      fun p : ℝ × ℝ => Work.FTS.BSIdent.PhiOdd Φ p.1 p.2 τ := by
    filter_upwards [hmem] with p hp
    exact (Work.FTS.BSIdent.PhiOdd_of_nonneg hp.le).symm
  exact (((hsm w θ hw hθ0 hθ1).of_le (by decide)).differentiableAt_one).congr_of_eventuallyEq hev.symm

/-! ## The two chain rules for `psiCore` -/

theorem pdZ_psiCore_eq {G : ℝ → ℝ → ℝ} {p c b r z : ℝ}
    (hG : Work.Cyl.DiffAt2 G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z))
    (hr : 0 < r) :
    Work.Cyl.pdZ (psiCore p c b G) r z =
      2 * z * c * G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)
        + c * (p * z * (Work.Cyl.rhoP r z ^ p / b)
              * Work.Cyl.pdR G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)
            + r * Work.Cyl.pdZ G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)) := by
  have hρpos : 0 < Work.Cyl.rhoP r z := Work.Cyl.rhoP_pos hr z
  have hρne : Work.Cyl.rhoP r z ≠ 0 := ne_of_gt hρpos
  have hρ2ne : Work.Cyl.rhoP r z ^ 2 ≠ 0 := pow_ne_zero 2 hρne
  have hρ2 : HasDerivAt (fun z' : ℝ => Work.Cyl.rhoP r z' ^ 2) (2 * z) z := by
    have hfun : (fun z' : ℝ => Work.Cyl.rhoP r z' ^ 2) = fun z' : ℝ => z' ^ 2 + r ^ 2 := by
      funext z'; rw [Work.Cyl.rhoP_sq]; ring
    rw [hfun]
    have h : HasDerivAt (fun z' : ℝ => z' ^ 2) (2 * z) z := by
      simpa using (hasDerivAt_pow 2 z)
    simpa using h.add_const (r ^ 2)
  have hw : HasDerivAt (fun z' : ℝ => Work.Cyl.rhoP r z' ^ p / b)
      (p * (Work.Cyl.rhoP r z ^ p / b) * (z / Work.Cyl.rhoP r z ^ 2)) z :=
    Work.Cyl.hasDerivAt_rhoP_rpow_div_snd r p z b hr
  have hθ : HasDerivAt (fun z' : ℝ => Work.Cyl.thetaP r z') (r / Work.Cyl.rhoP r z ^ 2) z :=
    Work.Cyl.hasDerivAt_thetaP_snd r z hr
  have h2 : HasDerivAt (fun z' : ℝ => G (Work.Cyl.rhoP r z' ^ p / b) (Work.Cyl.thetaP r z'))
      (Work.Cyl.pdR G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)
          * (p * (Work.Cyl.rhoP r z ^ p / b) * (z / Work.Cyl.rhoP r z ^ 2))
        + Work.Cyl.pdZ G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)
          * (r / Work.Cyl.rhoP r z ^ 2)) z :=
    Work.Cyl.hasDerivAt_comp_two G (fun z' : ℝ => Work.Cyl.rhoP r z' ^ p / b)
      (fun z' : ℝ => Work.Cyl.thetaP r z') _ _ z hG hw hθ
  have h3 : HasDerivAt (fun z' : ℝ =>
      (Work.Cyl.rhoP r z' ^ 2 * c) * G (Work.Cyl.rhoP r z' ^ p / b) (Work.Cyl.thetaP r z'))
      ((2 * z * c) * G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)
        + (Work.Cyl.rhoP r z ^ 2 * c)
          * (Work.Cyl.pdR G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)
              * (p * (Work.Cyl.rhoP r z ^ p / b) * (z / Work.Cyl.rhoP r z ^ 2))
            + Work.Cyl.pdZ G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)
              * (r / Work.Cyl.rhoP r z ^ 2))) z := (hρ2.mul_const c).mul h2
  show deriv (fun z' : ℝ =>
      (Work.Cyl.rhoP r z' ^ 2 * c) * G (Work.Cyl.rhoP r z' ^ p / b)
        (Work.Cyl.thetaP r z')) z = _
  rw [h3.deriv]
  field_simp

theorem pdR_psiCore_eq {G : ℝ → ℝ → ℝ} {p c b r z : ℝ}
    (hG : Work.Cyl.DiffAt2 G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z))
    (hr : 0 < r) :
    Work.Cyl.pdR (psiCore p c b G) r z =
      2 * r * c * G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)
        + c * (p * r * (Work.Cyl.rhoP r z ^ p / b)
              * Work.Cyl.pdR G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)
            + (-z) * Work.Cyl.pdZ G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)) := by
  have hρpos : 0 < Work.Cyl.rhoP r z := Work.Cyl.rhoP_pos hr z
  have hρne : Work.Cyl.rhoP r z ≠ 0 := ne_of_gt hρpos
  have hρ2ne : Work.Cyl.rhoP r z ^ 2 ≠ 0 := pow_ne_zero 2 hρne
  have hρ2 : HasDerivAt (fun r' : ℝ => Work.Cyl.rhoP r' z ^ 2) (2 * r) r := by
    have hfun : (fun r' : ℝ => Work.Cyl.rhoP r' z ^ 2) = fun r' : ℝ => r' ^ 2 + z ^ 2 := by
      funext r'; rw [Work.Cyl.rhoP_sq]
    rw [hfun]
    have h : HasDerivAt (fun r' : ℝ => r' ^ 2) (2 * r) r := by
      simpa using (hasDerivAt_pow 2 r)
    simpa using h.add_const (z ^ 2)
  have hw : HasDerivAt (fun r' : ℝ => Work.Cyl.rhoP r' z ^ p / b)
      (p * (Work.Cyl.rhoP r z ^ p / b) * (r / Work.Cyl.rhoP r z ^ 2)) r :=
    DecayAux.hasDerivAt_rhoP_rpow_div_fst r p z b hr
  have hθ : HasDerivAt (fun r' : ℝ => Work.Cyl.thetaP r' z) (-z / Work.Cyl.rhoP r z ^ 2) r :=
    DecayAux.hasDerivAt_thetaP_fst r z hr
  have h2 : HasDerivAt (fun r' : ℝ => G (Work.Cyl.rhoP r' z ^ p / b) (Work.Cyl.thetaP r' z))
      (Work.Cyl.pdR G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)
          * (p * (Work.Cyl.rhoP r z ^ p / b) * (r / Work.Cyl.rhoP r z ^ 2))
        + Work.Cyl.pdZ G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)
          * (-z / Work.Cyl.rhoP r z ^ 2)) r :=
    Work.Cyl.hasDerivAt_comp_two G (fun r' : ℝ => Work.Cyl.rhoP r' z ^ p / b)
      (fun r' : ℝ => Work.Cyl.thetaP r' z) _ _ r hG hw hθ
  have h3 : HasDerivAt (fun r' : ℝ =>
      (Work.Cyl.rhoP r' z ^ 2 * c) * G (Work.Cyl.rhoP r' z ^ p / b) (Work.Cyl.thetaP r' z))
      ((2 * r * c) * G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)
        + (Work.Cyl.rhoP r z ^ 2 * c)
          * (Work.Cyl.pdR G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)
              * (p * (Work.Cyl.rhoP r z ^ p / b) * (r / Work.Cyl.rhoP r z ^ 2))
            + Work.Cyl.pdZ G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)
              * (-z / Work.Cyl.rhoP r z ^ 2))) r := (hρ2.mul_const c).mul h2
  show deriv (fun r' : ℝ =>
      (Work.Cyl.rhoP r' z ^ 2 * c) * G (Work.Cyl.rhoP r' z ^ p / b)
        (Work.Cyl.thetaP r' z)) r = _
  rw [h3.deriv]
  field_simp


end Work.FTS.BSIdent.Cyl
