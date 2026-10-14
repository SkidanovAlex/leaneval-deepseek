import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.FireFix.Clauses.psiField_contDiffAt_two
import Submission.Work.FTS.FireFix.Prime.PhysVortBundle
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.PressureOn.integral_div_eq_zero_of_offPlanes
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.conv_shift_sq_integral_le
import Submission.Work.FTS_BSIdentP.Slim.AbsPdZPdRPsiCoreLeOne
import Submission.Work.FTS_BSIdentP.Slim.TendstoPhiOddNegPi
import Submission.Work.FTS_FinalLeaves.Min.SliceTheta
import Submission.Work.FTS_RegExport.RXT.SysAux.explicit_piece_bounds
import Submission.Work.R1G.vecResid_eq_scalar_smul
-- ===== merged: Submission.Work.FTS.BSIdent.Cyl.DecayAux.Extension =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The decay of the ansatz field: the bounds on the closed half plane `r ≥ 0`

The bounds of `DecayAux.PosQuadrant` are stated on the open quadrant `r > 0, z > 0`, where the
chain rule applies.  Here they are extended to all `r ≥ 0` and all `z`:

* `z < 0` by the oddness of `ψ` in `z` (`deriv_odd_eq`),
* `z = 0` — where `θ = 0` and the odd extension `Φ̂` need not be differentiable — by the one-sided
  mean value estimate `abs_deriv_zero_le_of_bound_right`, using that `ψ(r, ·)` is differentiable on
  `(0,∞)`,
* `r = 0` by the same mean value estimate in the radial variable, using that `ψ(·, z)` is
  differentiable on `(0,∞)` (through the oddness in `z` for `z < 0`),
*

together with the vanishing of `ψ` on `z = 0` (`merPsiT_zero_snd`) and on `r = 0`
(`merPsiT_zero_fst`), which makes the cases `z = 0` of `∂_r ψ` and `r = 0` of `∂_z ψ` trivial.
-/

noncomputable section

open scoped Topology

namespace Work.FTS.BSIdent.Cyl

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- `deriv` of a negated function (the `Pi`-negation form of `deriv.neg`). -/
theorem deriv_neg_fun {g : ℝ → ℝ} (x : ℝ) : deriv (fun y => - g y) x = - deriv g x := by
  show deriv (-g) x = - deriv g x
  rw [deriv.neg]

/-- `ρ(r,0) = |r|`. -/
theorem rhoP_snd_zero (r : ℝ) : Work.Cyl.rhoP r 0 = |r| := by
  have h : r ^ 2 + (0 : ℝ) ^ 2 = r ^ 2 := by norm_num
  rw [Work.Cyl.rhoP, h, Real.sqrt_sq_eq_abs]

/-- `ρ(0,z) = |z|`. -/
theorem rhoP_fst_zero (z : ℝ) : Work.Cyl.rhoP 0 z = |z| := by
  have h : (0 : ℝ) ^ 2 + z ^ 2 = z ^ 2 := by norm_num
  rw [Work.Cyl.rhoP, h, Real.sqrt_sq_eq_abs]

/-- A nonnegative constant over `1+ρ` (`ρ ≥ 0`) is nonnegative. -/
theorem div_one_add_nonneg {K ρ : ℝ} (h : 0 ≤ K) (hρ : 0 ≤ ρ) : 0 ≤ K / (1 + ρ) :=
  div_nonneg h (by linarith)

/-- **The bound on `∂_z ψ` on `r ≥ 0`, all `z`.** -/
theorem abs_pdZ_merPsiT_le {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Physical.PhysClock} {t : ℝ}
    (hα : 0 < α) (hA : A (Physical.clockInv C t) ≠ 0) (hB : 0 < B (Physical.clockInv C t))
    (hsm : ∀ w θ, 0 < w → 0 < θ → θ < Real.pi / 2 → ContDiffAt ℝ 3
      (fun p : ℝ × ℝ => Φ p.1 p.2 (Physical.clockInv C t)) (w, θ))
    (h0 : ∀ w, 0 < w → Φ w 0 (Physical.clockInv C t) = 0)
    {q lam C₀ : ℝ} (hq : 2 < q) (hlam : 0 < lam) (hC₀ : 0 < C₀)
    (hexp : 3 ≤ Work.FTS.Regularity.pExp α * lam)
    (hrate : PhiRate Φ (Physical.clockInv C t) C₀ q lam) :
    ∀ r z, 0 ≤ r →
      |Work.Cyl.pdZ (merPsiT α A B Φ C t) r z|
        ≤ decayKzr (Work.FTS.Regularity.pExp α) ((A (Physical.clockInv C t))⁻¹) C₀ q lam
            (B (Physical.clockInv C t)) / (1 + Work.Cyl.rhoP r z) := by
  have hp : (0 : ℝ) < Work.FTS.Regularity.pExp α := by
    rw [Work.FTS.Regularity.pExp]; linarith
  have hK : (0 : ℝ) ≤ decayKzr (Work.FTS.Regularity.pExp α)
      ((A (Physical.clockInv C t))⁻¹) C₀ q lam (B (Physical.clockInv C t)) :=
    decayKzr_nonneg hC₀.le hp.le
  intro r z hr0
  rcases eq_or_lt_of_le hr0 with hr_eq | hr
  · subst hr_eq
    rw [show Work.Cyl.pdZ (merPsiT α A B Φ C t) 0 z
        = deriv (fun z' => merPsiT α A B Φ C t 0 z') z from rfl]
    rw [show (fun z' => merPsiT α A B Φ C t 0 z') = fun _ => 0 from
      funext (merPsiT_zero_fst hB h0)]
    rw [deriv_const]
    simpa using div_one_add_nonneg (decayKzr_nonneg hC₀.le hp.le)
      (Work.Cyl.rhoP_nonneg 0 z)
  · rcases lt_trichotomy z 0 with hz | hz0 | hz
    · -- `z < 0`: oddness in `z`
      have hodd : ∀ z' : ℝ, merPsiT α A B Φ C t r (-z') = -merPsiT α A B Φ C t r z' :=
        fun z' => merPsiT_odd_z hB h0 hr
      rw [show Work.Cyl.pdZ (merPsiT α A B Φ C t) r z
            = deriv (fun z' => merPsiT α A B Φ C t r z') z from rfl,
          deriv_odd_eq hodd z]
      have h := abs_pdZ_merPsiT_le_pos hα hA hB hsm h0 hq hlam hC₀ hexp hrate r (-z) hr
        (by linarith)
      rwa [Work.Cyl.rhoP_neg] at h
    · -- `z = 0`: the one-sided mean value estimate in `z`
      subst hz0
      rw [show Work.Cyl.pdZ (merPsiT α A B Φ C t) r 0
          = deriv (fun z' => merPsiT α A B Φ C t r z') 0 from rfl,
        rhoP_snd_zero r, abs_of_nonneg hr.le]
      refine DecayAux.abs_deriv_zero_le_of_bound_right
        (M := decayKzr (Work.FTS.Regularity.pExp α) ((A (Physical.clockInv C t))⁻¹) C₀ q lam
          (B (Physical.clockInv C t)) / (1 + r))
        (div_one_add_nonneg (decayKzr_nonneg hC₀.le hp.le) hr.le) one_pos ?_ ?_
      · intro u hu
        exact differentiableAt_merPsiT_snd hsm hB hr hu.1
      · intro u hu
        have h := abs_pdZ_merPsiT_le_pos hα hA hB hsm h0 hq hlam hC₀ hexp hrate r u hr hu.1
        refine h.trans (div_le_div_of_nonneg_left (decayKzr_nonneg hC₀.le hp.le) ?_ ?_)
        · linarith
        · simpa using le_rhoP r u hr.le
    · -- `z > 0`
      exact abs_pdZ_merPsiT_le_pos hα hA hB hsm h0 hq hlam hC₀ hexp hrate r z hr hz

/-- **The bound on `∂_r ψ` on `r ≥ 0`, all `z`.** -/
theorem abs_pdR_merPsiT_le {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Physical.PhysClock} {t : ℝ}
    (hα : 0 < α) (hA : A (Physical.clockInv C t) ≠ 0) (hB : 0 < B (Physical.clockInv C t))
    (hsm : ∀ w θ, 0 < w → 0 < θ → θ < Real.pi / 2 → ContDiffAt ℝ 3
      (fun p : ℝ × ℝ => Φ p.1 p.2 (Physical.clockInv C t)) (w, θ))
    (h0 : ∀ w, 0 < w → Φ w 0 (Physical.clockInv C t) = 0)
    {q lam C₀ : ℝ} (hq : 2 < q) (hlam : 0 < lam) (hC₀ : 0 < C₀)
    (hexp : 3 ≤ Work.FTS.Regularity.pExp α * lam)
    (hrate : PhiRate Φ (Physical.clockInv C t) C₀ q lam) :
    ∀ r z, 0 ≤ r →
      |Work.Cyl.pdR (merPsiT α A B Φ C t) r z|
        ≤ decayKzr (Work.FTS.Regularity.pExp α) ((A (Physical.clockInv C t))⁻¹) C₀ q lam
            (B (Physical.clockInv C t)) / (1 + Work.Cyl.rhoP r z) := by
  have hp : (0 : ℝ) < Work.FTS.Regularity.pExp α := by
    rw [Work.FTS.Regularity.pExp]; linarith
  have hK : (0 : ℝ) ≤ decayKzr (Work.FTS.Regularity.pExp α)
      ((A (Physical.clockInv C t))⁻¹) C₀ q lam (B (Physical.clockInv C t)) :=
    decayKzr_nonneg hC₀.le hp.le
  -- the odd-in-`z` identity, as an eventual equality near a positive point
  have hoddE : ∀ {r z : ℝ}, 0 < r → (fun r' => merPsiT α A B Φ C t r' z)
      =ᶠ[𝓝 r] fun r' => - merPsiT α A B Φ C t r' (-z) := by
    intro r z hr
    filter_upwards [isOpen_Ioi.mem_nhds hr] with r' hr'
    have h : merPsiT α A B Φ C t r' (-z) = -merPsiT α A B Φ C t r' z := merPsiT_odd_z hB h0 hr'
    rw [h, neg_neg]
  -- the bound for `r > 0`, both signs of `z`
  have hpos : ∀ r z, 0 < r →
      |Work.Cyl.pdR (merPsiT α A B Φ C t) r z|
        ≤ decayKzr (Work.FTS.Regularity.pExp α) ((A (Physical.clockInv C t))⁻¹) C₀ q lam
            (B (Physical.clockInv C t)) / (1 + Work.Cyl.rhoP r z) := by
    intro r z hr
    rcases lt_trichotomy z 0 with hz | hz0 | hz
    · rw [show Work.Cyl.pdR (merPsiT α A B Φ C t) r z
            = deriv (fun r' => merPsiT α A B Φ C t r' z) r from rfl,
          Filter.EventuallyEq.deriv_eq (hoddE hr), deriv_neg_fun, abs_neg]
      have h := abs_pdR_merPsiT_le_pos hα hA hB hsm h0 hq hlam hC₀ hexp hrate r (-z) hr
        (by linarith)
      rwa [Work.Cyl.rhoP_neg] at h
    · subst hz0
      rw [show Work.Cyl.pdR (merPsiT α A B Φ C t) r 0
          = deriv (fun r' => merPsiT α A B Φ C t r' 0) r from rfl,
        show (fun r' => merPsiT α A B Φ C t r' 0) = fun _ => 0 from
          funext (merPsiT_zero_snd hB h0)]
      rw [deriv_const]
      simpa using div_one_add_nonneg (decayKzr_nonneg hC₀.le hp.le)
        (Work.Cyl.rhoP_nonneg r 0)
    · exact abs_pdR_merPsiT_le_pos hα hA hB hsm h0 hq hlam hC₀ hexp hrate r z hr hz
  intro r z hr0
  rcases eq_or_lt_of_le hr0 with hr_eq | hr
  · subst hr_eq
    by_cases hz0 : z = 0
    · subst hz0
      rw [show Work.Cyl.pdR (merPsiT α A B Φ C t) 0 0
            = deriv (fun r' => merPsiT α A B Φ C t r' 0) 0 from rfl,
          show (fun r' => merPsiT α A B Φ C t r' 0) = fun _ => 0 from
            funext (merPsiT_zero_snd hB h0)]
      rw [deriv_const]
      simpa using div_one_add_nonneg (decayKzr_nonneg hC₀.le hp.le)
        (Work.Cyl.rhoP_nonneg 0 0)
    · rw [show Work.Cyl.pdR (merPsiT α A B Φ C t) 0 z
            = deriv (fun r' => merPsiT α A B Φ C t r' z) 0 from rfl, rhoP_fst_zero z]
      refine DecayAux.abs_deriv_zero_le_of_bound_right
        (M := decayKzr (Work.FTS.Regularity.pExp α) ((A (Physical.clockInv C t))⁻¹) C₀ q lam
          (B (Physical.clockInv C t)) / (1 + |z|))
        (div_one_add_nonneg (decayKzr_nonneg hC₀.le hp.le) (abs_nonneg z)) one_pos ?_ ?_
      · intro u hu
        rcases lt_trichotomy z 0 with hz | hzz | hz
        · exact ((differentiableAt_merPsiT_fst hsm hB hu.1 (by linarith)).neg).congr_of_eventuallyEq
            (hoddE hu.1)
        · exact absurd hzz hz0
        · exact differentiableAt_merPsiT_fst hsm hB hu.1 hz
      · intro u hu
        rcases lt_trichotomy z 0 with hz | hzz | hz
        · rw [Filter.EventuallyEq.deriv_eq (hoddE hu.1), deriv_neg_fun, abs_neg]
          have h := abs_pdR_merPsiT_le_pos hα hA hB hsm h0 hq hlam hC₀ hexp hrate u (-z) hu.1
            (by linarith)
          rw [Work.Cyl.rhoP_neg] at h
          refine h.trans (div_le_div_of_nonneg_left (decayKzr_nonneg hC₀.le hp.le) ?_ ?_)
          · positivity
          · simpa using abs_snd_le_rhoP u z
        · exact absurd hzz hz0
        · have h := abs_pdR_merPsiT_le_pos hα hA hB hsm h0 hq hlam hC₀ hexp hrate u z hu.1 hz
          refine h.trans (div_le_div_of_nonneg_left (decayKzr_nonneg hC₀.le hp.le) ?_ ?_)
          · positivity
          · simpa using abs_snd_le_rhoP u z
  · exact hpos r z hr


end Work.FTS.BSIdent.Cyl
end
end
-- ===== merged: Submission.Work.FTS.FireFix.Clauses.PhysVortAe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory Filter Topology
open scoped Topology NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.FireFix.Clauses

/-! ## The pointwise bound for one vorticity slice

The proof is the chain rule for `x ↦ Ψ(ρ(x)^{3α}/B, θ(x)) • e_θ(x)` (`Ψ` the two-variable
profile slice): the product rule bounds the `e_θ`-factor by `2/r`, and the frame decomposition
`‖L‖ ≤ ‖L e_r‖ + ‖L e_θ‖ + ‖L e₃‖` together with the polar chain rules
(`Work.Cyl.fderiv_rho_theta_eR`/`eZ`/`eTheta`) bounds the profile factor by
`2|∂_zΨ|·3αρ^{3α-1}/B + 2|∂_θΨ|/ρ`.  Every ingredient is available at an *arbitrary* point of
`{r > 0}`: whenever the composite is differentiable there, the local right inverse `sect` of
`x ↦ (ρ(x)^{3α}/B, θ(x))` (`diffAt2_of_comp_sect`) upgrades that to the two-variable
differentiability of the profile. -/

lemma physVort_slice_bound {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    {τ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hAτ : 0 < A τ) (hBτ : 0 < B τ)
    {N Npz L : ℝ} (hN0 : 0 ≤ N) (hNpz0 : 0 ≤ Npz)
    (hN : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |g z θ τ| ≤ N)
    (hNpz : ∀ z θ τ' : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → τ' ∈ Set.Icc 0 S →
      |Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ') z θ| ≤ Npz)
    (hcont : ∀ θ ∈ Work.Spaces.Iθ, ContDiffOn ℝ 1 (fun q : ℝ × ℝ => g q.1 θ q.2)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)))
    (hτ : τ ∈ Set.Icc 0 S)
    (hsupp : ∀ z θ : ℝ, L ≤ z → Work.FTS.Regularity.profFull α g z θ τ = 0)
    {x : R3} (hr : 0 < Work.Cyl.radial x) (hθ0 : Work.Cyl.theta x ≠ 0) :
    ‖fderiv ℝ (fun y : R3 => Work.FTS.Regularity.physVort α A B g y τ) x‖
      ≤ psiBound α A B g τ N Npz L (Work.Cyl.rho x ^ (3 * α) / B τ) (Work.Cyl.theta x) := by
  have hρpos : 0 < Work.Cyl.rho x := lt_of_lt_of_le hr (Work.Cyl.radial_le_rho x)
  set Ψ : ℝ → ℝ → ℝ := fun z θ => Work.ConstructionInstance.profile (3 * α)
      (Work.FTS.Regularity.gSlice g τ) z θ with hΨ
  set z0 : ℝ := Work.Cyl.rho x ^ (3 * α) / B τ with hz0
  have hz0pos : 0 < z0 := by
    rw [hz0]
    exact div_pos (Real.rpow_pos_of_pos hρpos _) hBτ
  have hθmem : |Work.Cyl.theta x| < Real.pi / 2 := by
    rw [Work.Cyl.theta]
    exact abs_lt.mpr ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩
  have hBz : B τ * z0 = Work.Cyl.rho x ^ (3 * α) := by
    rw [hz0]; field_simp
  have hpow1 : (B τ * z0) ^ (1 / (3 * α)) = Work.Cyl.rho x := by
    rw [hBz, ← Real.rpow_mul (Work.Cyl.rho_nonneg x)]
    have hexp : 3 * α * (1 / (3 * α)) = 1 := by
      rw [mul_one_div, div_self (by positivity : (3 : ℝ) * α ≠ 0)]
    rw [hexp, Real.rpow_one]
  have hpow2 : (B τ * z0) ^ ((3 * α - 1) / (3 * α)) = Work.Cyl.rho x ^ (3 * α - 1) := by
    rw [hBz, ← Real.rpow_mul (Work.Cyl.rho_nonneg x)]
    congr 1
    field_simp
  have hcosr : Work.Cyl.rho x * Real.cos (Work.Cyl.theta x) = Work.Cyl.radial x := by
    rw [cos_theta_eq x hr]
    field_simp
  have hfun : (fun y : R3 => Work.FTS.Regularity.physVort α A B g y τ)
      = fun y : R3 => (A τ)⁻¹ • (Ψ (Work.Cyl.rho y ^ (3 * α) / B τ) (Work.Cyl.theta y)
          • Work.Cyl.eTheta y) := by
    funext y
    rw [Work.FTS.Regularity.physVort_apply, Work.ConstructionInstance.omegaSz_apply,
      Work.FTS.Regularity.pExp_eq, hΨ]
  by_cases hzL : z0 ≤ L
  · by_cases hd : DifferentiableAt ℝ (fun y : R3 => Ψ (Work.Cyl.rho y ^ (3 * α) / B τ)
        (Work.Cyl.theta y) • Work.Cyl.eTheta y) x
    · have hD : Work.Cyl.DiffAt2 Ψ z0 (Work.Cyl.theta x) := by
        rw [hz0]
        exact diffAt2_of_differentiableAt_smul_eTheta hα hBτ hr hd
      have hDc : Work.Cyl.DiffAt2 (fun r θ => Ψ (r ^ (3 * α) / B τ) θ)
          (Work.Cyl.rho x) (Work.Cyl.theta x) := diffAt2_comp_rpow hBτ hr hD
      have hHd : DifferentiableAt ℝ (fun y : R3 => Ψ (Work.Cyl.rho y ^ (3 * α) / B τ)
          (Work.Cyl.theta y)) x :=
        Work.Cyl.differentiableAt_rho_theta_comp (fun r θ => Ψ (r ^ (3 * α) / B τ) θ) x hDc hr
      have hstep1 : ‖fderiv ℝ (fun y : R3 => Ψ (Work.Cyl.rho y ^ (3 * α) / B τ)
            (Work.Cyl.theta y) • Work.Cyl.eTheta y) x‖
          ≤ |Ψ z0 (Work.Cyl.theta x)| * (2 / Work.Cyl.radial x)
            + ‖fderiv ℝ (fun y : R3 => Ψ (Work.Cyl.rho y ^ (3 * α) / B τ)
                (Work.Cyl.theta y)) x‖ := by
        have h := norm_fderiv_smul_eTheta_le
          (H := fun y : R3 => Ψ (Work.Cyl.rho y ^ (3 * α) / B τ) (Work.Cyl.theta y)) hr hHd
        simpa using h
      have hstep2 : ‖fderiv ℝ (fun y : R3 => Ψ (Work.Cyl.rho y ^ (3 * α) / B τ)
            (Work.Cyl.theta y)) x‖
          ≤ 2 * (|Work.Spaces.pz Ψ z0 (Work.Cyl.theta x)|
                * ((3 * α) * Work.Cyl.rho x ^ (3 * α - 1) / B τ))
            + 2 * |Work.Spaces.pth Ψ z0 (Work.Cyl.theta x)| / Work.Cyl.rho x := by
        have h := norm_fderiv_profile_comp_le hα hBτ hr hD
        rw [← hz0] at h
        exact h
      have habs : |Ψ z0 (Work.Cyl.theta x)| ≤ 20 * (3 * α) + N := by
        have h := profile_abs_le_N hα hα13 (fun z θ hz hθ => hN z θ hz hθ) hz0pos.le
          (le_of_lt hθmem)
        simpa [hΨ] using h
      have hpz : |Work.Spaces.pz Ψ z0 (Work.Cyl.theta x)| ≤ 60 * α + Npz := by
        have h := profile_pz_le hα hα13 hNpz hcont hτ hz0pos.le (le_of_lt hθmem)
        simpa [hΨ] using h
      have hpth : |Work.Spaces.pth Ψ z0 (Work.Cyl.theta x)|
          ≤ 200 * α ^ 2 * (Real.sin (|Work.Cyl.theta x|)) ^ (α - 1)
              * (Real.cos (Work.Cyl.theta x)) ^ (2 * α - 1)
            + |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z0 (|Work.Cyl.theta x|)| := by
        have h := profile_pth_le hα hα13 hz0pos.le (abs_pos.mpr hθ0) hθmem
          (Work.Cyl.differentiableAt_slice_snd Ψ z0 (Work.Cyl.theta x) hD)
        simpa [Work.Spaces.pth, hΨ] using h
      have hρnn : 0 ≤ (3 * α) * Work.Cyl.rho x ^ (3 * α - 1) / B τ :=
        div_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hρpos.le _)) hBτ.le
      have hb1 : |Ψ z0 (Work.Cyl.theta x)| * (2 / Work.Cyl.radial x)
          ≤ (20 * (3 * α) + N) * (2 / Work.Cyl.radial x) :=
        mul_le_mul_of_nonneg_right habs (by positivity)
      have hb2 : 2 * (|Work.Spaces.pz Ψ z0 (Work.Cyl.theta x)|
            * ((3 * α) * Work.Cyl.rho x ^ (3 * α - 1) / B τ))
          ≤ 2 * ((60 * α + Npz) * ((3 * α) * Work.Cyl.rho x ^ (3 * α - 1) / B τ)) := by
        have h := mul_le_mul_of_nonneg_right hpz hρnn
        linarith
      have hb3 : 2 * |Work.Spaces.pth Ψ z0 (Work.Cyl.theta x)| / Work.Cyl.rho x
          ≤ 2 * (200 * α ^ 2 * (Real.sin (|Work.Cyl.theta x|)) ^ (α - 1)
                * (Real.cos (Work.Cyl.theta x)) ^ (2 * α - 1)
              + |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z0 (|Work.Cyl.theta x|)|)
              / Work.Cyl.rho x := by
        have h1 := div_le_div_of_nonneg_right hpth hρpos.le
        have h2 := mul_le_mul_of_nonneg_left h1 (by norm_num : (0:ℝ) ≤ 2)
        rw [← mul_div_assoc, ← mul_div_assoc] at h2
        exact h2
      have hmid0 : ‖fderiv ℝ (fun y : R3 => Ψ (Work.Cyl.rho y ^ (3 * α) / B τ)
            (Work.Cyl.theta y) • Work.Cyl.eTheta y) x‖
          ≤ (20 * (3 * α) + N) * (2 / Work.Cyl.radial x)
            + 2 * ((60 * α + Npz) * ((3 * α) * Work.Cyl.rho x ^ (3 * α - 1) / B τ))
            + 2 * (200 * α ^ 2 * (Real.sin (|Work.Cyl.theta x|)) ^ (α - 1)
                * (Real.cos (Work.Cyl.theta x)) ^ (2 * α - 1)
              + |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z0 (|Work.Cyl.theta x|)|)
              / Work.Cyl.rho x := by
        linarith [hstep1, hstep2, hb1, hb2, hb3]
      have hmid : ‖fderiv ℝ (fun y : R3 => Ψ (Work.Cyl.rho y ^ (3 * α) / B τ)
            (Work.Cyl.theta y) • Work.Cyl.eTheta y) x‖
          ≤ (20 * (3 * α) + N) * (2 / Work.Cyl.radial x)
            + 2 * ((60 * α + Npz) * ((3 * α) * Work.Cyl.rho x ^ (3 * α - 1) / B τ)
                + (200 * α ^ 2 * (Real.sin (|Work.Cyl.theta x|)) ^ (α - 1)
                    * (Real.cos (Work.Cyl.theta x)) ^ (2 * α - 1)
                  + |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z0 (|Work.Cyl.theta x|)|)
                  / Work.Cyl.rho x) := by
        have hd : 2 * ((60 * α + Npz) * ((3 * α) * Work.Cyl.rho x ^ (3 * α - 1) / B τ))
              + 2 * (200 * α ^ 2 * (Real.sin (|Work.Cyl.theta x|)) ^ (α - 1)
                  * (Real.cos (Work.Cyl.theta x)) ^ (2 * α - 1)
                + |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z0 (|Work.Cyl.theta x|)|)
                / Work.Cyl.rho x
            = 2 * ((60 * α + Npz) * ((3 * α) * Work.Cyl.rho x ^ (3 * α - 1) / B τ)
                + (200 * α ^ 2 * (Real.sin (|Work.Cyl.theta x|)) ^ (α - 1)
                    * (Real.cos (Work.Cyl.theta x)) ^ (2 * α - 1)
                  + |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z0 (|Work.Cyl.theta x|)|)
                  / Work.Cyl.rho x) := by ring
        linarith [hmid0, hd.le, hd.ge]
      have hpsi : psiBound α A B g τ N Npz L z0 (Work.Cyl.theta x)
          = |(A τ)⁻¹| * ((20 * (3 * α) + N) * (2 / Work.Cyl.radial x)
              + 2 * ((60 * α + Npz) * ((3 * α) * Work.Cyl.rho x ^ (3 * α - 1) / B τ)
                  + (200 * α ^ 2 * (Real.sin (|Work.Cyl.theta x|)) ^ (α - 1)
                      * (Real.cos (Work.Cyl.theta x)) ^ (2 * α - 1)
                    + |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z0 (|Work.Cyl.theta x|)|)
                    / Work.Cyl.rho x)) := by
        rw [psiBound, if_pos hzL, hpow1, hpow2, hcosr]
        ring
      have hsmul : fderiv ℝ (fun y : R3 => Work.FTS.Regularity.physVort α A B g y τ) x
          = (A τ)⁻¹ • fderiv ℝ (fun y : R3 => Ψ (Work.Cyl.rho y ^ (3 * α) / B τ)
              (Work.Cyl.theta y) • Work.Cyl.eTheta y) x := by
        rw [hfun]
        rw [show (fun y : R3 => (A τ)⁻¹ • (Ψ (Work.Cyl.rho y ^ (3 * α) / B τ)
              (Work.Cyl.theta y) • Work.Cyl.eTheta y))
            = (A τ)⁻¹ • (fun y : R3 => Ψ (Work.Cyl.rho y ^ (3 * α) / B τ)
                (Work.Cyl.theta y) • Work.Cyl.eTheta y) from rfl]
        exact fderiv_const_smul hd (A τ)⁻¹
      rw [hpsi, hsmul, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left hmid (abs_nonneg _)
    · have hd' : ¬ DifferentiableAt ℝ
          (fun y : R3 => Work.FTS.Regularity.physVort α A B g y τ) x := by
        intro hh
        rw [hfun] at hh
        have h2 : DifferentiableAt ℝ (fun y : R3 => (A τ) • ((A τ)⁻¹ •
            (Ψ (Work.Cyl.rho y ^ (3 * α) / B τ) (Work.Cyl.theta y)
              • Work.Cyl.eTheta y))) x := hh.const_smul (A τ)
        refine hd (h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_))
        show Ψ (Work.Cyl.rho y ^ (3 * α) / B τ) (Work.Cyl.theta y) • Work.Cyl.eTheta y
          = (A τ) • ((A τ)⁻¹ • (Ψ (Work.Cyl.rho y ^ (3 * α) / B τ) (Work.Cyl.theta y)
              • Work.Cyl.eTheta y))
        rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hAτ), one_smul]
      rw [fderiv_zero_of_not_differentiableAt hd', norm_zero]
      exact psiBound_nonneg α A B g τ N Npz L z0 (Work.Cyl.theta x) (Bpos := hBτ) hN0 hNpz0 hα
        hz0pos.le (le_of_lt hθmem)
  · have hzLt : L < z0 := not_le.mp hzL
    have hfuneq : (fun y : R3 => Work.FTS.Regularity.physVort α A B g y τ)
        =ᶠ[𝓝 x] (fun _ => 0) := by
      have hcontz : ContinuousAt (fun y : R3 => Work.Cyl.rho y ^ (3 * α) / B τ) x := by
        have h1 : ContinuousAt (fun y : R3 => Work.Cyl.rho y) x := by
          have hρ : (fun y : R3 => Work.Cyl.rho y) = fun y => ‖y‖ := by
            funext y; exact Work.Cyl.rho_eq_norm y
          rw [hρ]; exact continuous_norm.continuousAt
        have h2 : ContinuousAt (fun y : R3 => Work.Cyl.rho y ^ (3 * α)) x :=
          h1.rpow_const (Or.inl (ne_of_gt hρpos))
        have h3 : ContinuousAt (fun y : R3 => Work.Cyl.rho y ^ (3 * α) * (B τ)⁻¹) x :=
          h2.mul_const _
        simpa [div_eq_mul_inv] using h3
      filter_upwards [hcontz.eventually (IsOpen.mem_nhds isOpen_Ioi hzLt)] with y hy
      show (A τ)⁻¹ • (Ψ (Work.Cyl.rho y ^ (3 * α) / B τ) (Work.Cyl.theta y)
          • Work.Cyl.eTheta y) = 0
      have hzero : Ψ (Work.Cyl.rho y ^ (3 * α) / B τ) (Work.Cyl.theta y) = 0 := by
        have h := profile_eq_zero_of_supp (z := Work.Cyl.rho y ^ (3 * α) / B τ)
          (θ := Work.Cyl.theta y) hsupp (le_of_lt hy)
        simpa [hΨ] using h
      rw [hzero, zero_smul, smul_zero]
    have hzero : fderiv ℝ (fun y : R3 => Work.FTS.Regularity.physVort α A B g y τ) x = 0 := by
      rw [Filter.EventuallyEq.fderiv_eq hfuneq]
      simp [fderiv_const]
    rw [hzero, norm_zero, psiBound, if_neg hzL]

theorem ae_bound_physVort {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : Work.FTS.RegPkgGal.RegPkg' α S A B g) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S)
    {N Npz L : ℝ}
    (hN : ∀ z θ τ', 0 ≤ z → θ ∈ Work.Spaces.Iθ → τ' ∈ Set.Icc 0 S → |g z θ τ'| ≤ N)
    (hNpz : ∀ z θ τ', 0 ≤ z → θ ∈ Work.Spaces.Iθ → τ' ∈ Set.Icc 0 S →
      |Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ') z θ| ≤ Npz)
    (hL : 0 < L) (hsupp : ∀ z θ : ℝ, L ≤ z → Work.FTS.Regularity.profFull α g z θ τ = 0) :
    ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))),
      ‖fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) =>
          Work.FTS.Regularity.physVort α A B g y τ) x‖
        ≤ Work.FTS.FireFix.Clauses.psiBound α A B g τ N Npz L
            (Work.Cyl.rho x ^ (3 * α) / B τ) (Work.Cyl.theta x) := by
  have hα := h.hα
  have hα13 := h.hα13
  have hAτ : 0 < A τ := h.hA τ hτ
  have hBτ : 0 < B τ := h.hB τ hτ
  have hIθ0 : (0 : ℝ) ∈ Work.Spaces.Iθ := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hτ0 : (0 : ℝ) ∈ Set.Icc 0 S := ⟨le_rfl, h.hS.le⟩
  have hN0 : 0 ≤ N := le_trans (abs_nonneg _) (hN 0 0 0 le_rfl hIθ0 hτ0)
  have hNpz0 : 0 ≤ Npz := le_trans (abs_nonneg _) (hNpz 0 0 0 le_rfl hIθ0 hτ0)
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.measure_union_null
    volume_radial_eq_zero volume_axial_eq_zero)
  intro x hx
  by_cases hr : Work.Cyl.radial x = 0
  · exact Or.inl hr
  · by_cases ha : Work.Cyl.axial x = 0
    · exact Or.inr ha
    · exfalso
      have hθ0 : Work.Cyl.theta x ≠ 0 := by
        intro h0
        have h1 : Work.Cyl.axial x / Work.Cyl.radial x = 0 := Real.arctan_eq_zero_iff.mp h0
        rcases div_eq_zero_iff.mp h1 with h2 | h2
        · exact ha h2
        · exact hr h2
      exact hx (physVort_slice_bound (A := A) (B := B) (L := L) hα hα13 hAτ hBτ hN0 hNpz0
        (fun z θ hz hθ => hN z θ τ hz hθ hτ) hNpz (fun θ hθ => h.hcont θ hθ) hτ hsupp
        (lt_of_le_of_ne (Work.Cyl.radial_nonneg x) (Ne.symm hr)) hθ0)

end Work.FTS.FireFix.Clauses
end
-- ===== merged: Submission.Work.FTS.FireFix.Clauses.negPhysOmega_contDiffAt_one =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `C¹` clause for the (negated) physical vorticity

`Work.FTS.FireFix.Clauses.negPhysOmega_contDiffAt_one`: the (negated) physical vorticity
`ω := −physOmega α A B g C` is, at every `t ∈ (0, C.T)` and every `x ∈ Uax`, of class `C¹`.

## The mathematical content

Off the axis and off the plane, the (negated) physical vorticity *is* the curl of the velocity
(`hcurl`), and the velocity is the stream-function field `psiField (Φ · t)` of the profile (`hid`,
valid on the open set `Uax`).  So `ω(·,t) = ∇× (psiField (Φ · t))` near `x`, and the vorticity of
a `C²` field is `C¹` (`contDiffAt_vorticity_one`).  The `C²`-ness of `psiField (Φ · t)` off the axis
is `Clauses.psiField_contDiffAt_two`, which needs `Φ(·,·,t)` to be `C³` at `(radial x, axial x)`
(the hypothesis `hΨ`); both `radial x > 0` and `axial x ≠ 0` hold on `Uax`, since
`Uax = {x₂ ≠ 0} ∩ {x₀² + x₁² ≠ 0}`.

## The two helper lemmas

* `curlOf` — the curl `∇× L = ∑ᵢ eᵢ ×₃ (L eᵢ)` of a *continuous linear map* `L : ℝ³ →L[ℝ] ℝ³`,
  i.e. the `FiniteTimeSingularity.vorticity` expression with the derivative already taken (this is
  `Work.SolutionDelivery.Measurable.curlOf`, re-declared in the namespace of this file so that the
  module only needs the `FireFix` imports);
* `contDiff_curlOf` — `curlOf` is `C¹` (indeed linear and continuous): a finite sum of
  compositions of the continuous linear maps `L ↦ L (e i)`, the cross product with the fixed
  vector `e i`, and `WithLp.toLp 2`.  This is the only ingredient the `C¹`-clause needs about the
  vorticity besides the local unfolding `vorticity u y = curlOf (fderiv ℝ u y)`;
* `contDiffAt_vorticity_one` — consequently the vorticity of a `C²` field is `C¹`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open FiniteTimeSingularity Set
open scoped Matrix Topology

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace Work.FTS.FireFix.Clauses

/-- The curl (vorticity) of a continuous linear map `ℝ³ →L[ℝ] ℝ³`, in exactly the form in which
the curl of a differentiable field appears in `FiniteTimeSingularity.vorticity`:
`∇×L = ∑ᵢ eᵢ ×₃ (L eᵢ)`. -/
noncomputable def curlOf (L : ℝ³ →L[ℝ] ℝ³) : ℝ³ :=
  WithLp.toLp 2 (∑ i, FiniteTimeSingularity.e i ⨯₃ (L (FiniteTimeSingularity.e i)))

/-- The vorticity expression is smooth as a function of the derivative: it is a finite sum of
compositions of continuous linear maps, hence smooth (we only need `C¹`). -/
theorem contDiff_curlOf : ContDiff ℝ 1 curlOf := by
  unfold curlOf
  have hsum : ContDiff ℝ 1 (fun L : ℝ³ →L[ℝ] ℝ³ =>
      ∑ i, crossProduct (WithLp.ofLp (FiniteTimeSingularity.e i))
        (WithLp.ofLp (L (FiniteTimeSingularity.e i)))) := by
    refine ContDiff.sum (fun i _ => ?_)
    have h1 : ContDiff ℝ 1 (fun L : ℝ³ →L[ℝ] ℝ³ =>
        L (FiniteTimeSingularity.e i)) :=
      ContDiff.clm_apply contDiff_id contDiff_const
    have h2 : ContDiff ℝ 1 (fun L : ℝ³ →L[ℝ] ℝ³ =>
        WithLp.ofLp (L (FiniteTimeSingularity.e i))) :=
      (EuclideanSpace.equiv (Fin 3) ℝ).contDiff.comp h1
    have h3 : ContDiff ℝ 1 (fun w : Fin 3 → ℝ =>
        crossProduct (WithLp.ofLp (FiniteTimeSingularity.e i)) w) :=
      (LinearMap.toContinuousLinearMap
        (crossProduct (WithLp.ofLp (FiniteTimeSingularity.e i)))).contDiff
    exact h3.comp h2
  have htoLp : ContDiff ℝ 1 (WithLp.toLp 2 : (Fin 3 → ℝ) → ℝ³) :=
    (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff
  exact htoLp.comp hsum

/-- **The vorticity of a `C²` field is `C¹`.**  Unfolding the definition of the vorticity, it is
the fixed smooth function `curlOf` evaluated at the derivative `fderiv ℝ u`, which is `C¹` when
`u` is `C²`. -/
theorem contDiffAt_vorticity_one {u : ℝ³ → ℝ³} {x : ℝ³} (hu : ContDiffAt ℝ 2 u x) :
    ContDiffAt ℝ 1 (fun y => FiniteTimeSingularity.vorticity u y) x := by
  have hfd : ContDiffAt ℝ 1 (fderiv ℝ u) x := hu.fderiv_right (m := 1) (by norm_num)
  have hcurl : ContDiffAt ℝ 1 curlOf (fderiv ℝ u x) := contDiff_curlOf.contDiffAt
  have hmain : ContDiffAt ℝ 1 (fun y => curlOf (fderiv ℝ u y)) x := hcurl.comp x hfd
  refine hmain.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
  funext y
  rfl

/-- **The `C¹` clause of the (negated) physical vorticity.**

For `t ∈ (0, C.T)` and `x ∈ Uax` the (negated) physical vorticity `y ↦ −physOmega α A B g C y t`
is `C¹` at `x`.

Indeed, by `hcurl` it is the curl of the velocity, and by `hid` the velocity agrees, on the open
set `Uax` (which contains a neighbourhood of `x`), with the stream-function field
`psiField (Φ · t)`; that field is `C²` off the axis by `psiField_contDiffAt_two`, and the curl of a
`C²` field is `C¹`. -/
theorem negPhysOmega_contDiffAt_one {α : ℝ} {A B : ℝ → ℝ} {g Φ : ℝ → ℝ → ℝ → ℝ}
    {C : Work.FTS.Physical.PhysClock}
    (hid : ∀ t ∈ Set.Ioo (0 : ℝ) C.T, ∀ x ∈ Work.FTS.PressureOn.Uax,
      Work.FTS.Physical.physVel (fun x s => - Work.FTS.Physical.physOmega α A B g C x s) x t
        = Work.Cyl.psiField (fun r z => Φ r z t) x)
    (hΨ : ∀ t ∈ Set.Ioo (0 : ℝ) C.T, ∀ r z : ℝ, 0 < r → z ≠ 0 →
      ContDiffAt ℝ 3 (fun p : ℝ × ℝ => Φ p.1 p.2 t) (r, z))
    (hcurl : ∀ t ∈ Set.Ico (0 : ℝ) C.T, ∀ x : EuclideanSpace ℝ (Fin 3),
      FiniteTimeSingularity.vorticity
        (fun y => Work.FTS.Physical.physVel
          (fun x s => - Work.FTS.Physical.physOmega α A B g C x s) y t) x
        = - Work.FTS.Physical.physOmega α A B g C x t) :
    ∀ t ∈ Set.Ioo (0 : ℝ) C.T, ∀ x ∈ Work.FTS.PressureOn.Uax,
      ContDiffAt ℝ 1 (fun y : EuclideanSpace ℝ (Fin 3) =>
        - Work.FTS.Physical.physOmega α A B g C y t) x := by
  intro t ht x hx
  -- on `Uax` the radius is positive and the height is non-zero
  have hrad : 0 < Work.Cyl.radial x := by
    rcases eq_or_lt_of_le (Work.Cyl.radial_nonneg x) with h | h
    · exfalso
      have h01 := (Work.Cyl.radial_eq_zero_iff x).mp h.symm
      exact hx.2 (by rw [h01.1, h01.2]; norm_num)
    · exact h
  have hax : Work.Cyl.axial x ≠ 0 := hx.1
  -- the stream-function field `psiField (Φ · t)` is `C²` at `x`, hence its curl is `C¹`
  have h3 : ContDiffAt ℝ 3 (fun p : ℝ × ℝ => Φ p.1 p.2 t)
      (Work.Cyl.radial x, Work.Cyl.axial x) :=
    hΨ t ht (Work.Cyl.radial x) (Work.Cyl.axial x) hrad hax
  have h2 : ContDiffAt ℝ 2 (fun y : ℝ³ => Work.Cyl.psiField (fun r z => Φ r z t) y) x :=
    psiField_contDiffAt_two (ψ := fun r z => Φ r z t) hrad h3
  have h1 : ContDiffAt ℝ 1 (fun y : ℝ³ => FiniteTimeSingularity.vorticity
      (fun z : ℝ³ => Work.Cyl.psiField (fun r z => Φ r z t) z) y) x :=
    contDiffAt_vorticity_one h2
  -- `ω = ∇× u` and `u = psiField (Φ · t)` near `x`, so `ω = ∇×(psiField (Φ · t))` near `x`
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [Work.FTS.PressureOn.isOpen_Uax.mem_nhds hx] with y hy
  have hev : (fun z : ℝ³ => Work.Cyl.psiField (fun r z => Φ r z t) z)
      =ᶠ[𝓝 y] (fun z : ℝ³ => Work.FTS.Physical.physVel
          (fun x s => - Work.FTS.Physical.physOmega α A B g C x s) z t) := by
    filter_upwards [Work.FTS.PressureOn.isOpen_Uax.mem_nhds hy] with z hz
    exact (hid t ht z hz).symm
  have hfd : fderiv ℝ (fun z : ℝ³ => Work.Cyl.psiField (fun r z => Φ r z t) z) y
      = fderiv ℝ (fun z : ℝ³ => Work.FTS.Physical.physVel
          (fun x s => - Work.FTS.Physical.physOmega α A B g C x s) z t) y :=
    hev.fderiv_eq
  have hcurly := hcurl t (Set.Ioo_subset_Ico_self ht) y
  rw [← hcurly]
  simp only [FiniteTimeSingularity.vorticity, hfd]

end Work.FTS.FireFix.Clauses
end
-- ===== merged: Submission.Work.FTS.FireFix.FiringData =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.FireFix

open Work.FTS.Physical (PhysClock)

/-- **The `c/(C.T − t)` lower bound for the sup-norm of the negated physical vorticity.**  From the
smallness of the perturbation (`hsmall`) the full profile is `≥ 3α/100` at some point of the domain
at every fake time, whence the vorticity is `≥ c/A(τ(t)) ≥ c/(2(C.T − t))` by the clock comparison
`A(τ(t)) ≤ C.T − t`. -/
theorem negPhysOmega_lower {α : ℝ≥0} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ} {C : PhysClock}
    (hα : 0 < (α : ℝ)) (hα13 : (α : ℝ) ≤ 1 / 3)
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.RegPkgGal.RegPkg' (α : ℝ) S A B g)
    (hAeq : ∀ τ : ℝ, 0 ≤ τ → C.A τ = 2 * A τ)
    (hsmall : ∀ τ : ℝ, 0 ≤ τ → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |g z θ τ| ≤ 3 * (α : ℝ) / 200) :
    ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Set.Ico 0 C.T,
      c / (C.T - t) ≤ ⨆ x : R3, ‖- Work.FTS.Physical.physOmega (α : ℝ) A B g C x t‖ := by
  have hApos : ∀ τ : ℝ, 0 ≤ τ → 0 < A τ := fun τ hτ =>
    (hreg (τ + 1) (by linarith)).hA τ ⟨hτ, by linarith⟩
  have hBpos : ∀ τ : ℝ, 0 ≤ τ → 0 < B τ := fun τ hτ =>
    (hreg (τ + 1) (by linarith)).hB τ ⟨hτ, by linarith⟩
  have hF := Work.FTS.Physical.RegPkg.profFull_ge_of_small hα (by linarith [hα13]) hsmall
  obtain ⟨c₀, hc₀pos, hc₀⟩ :=
    Work.FTS.Physical.RegPkg.fakeLower_of_Fstar hα hApos hBpos hF
  refine ⟨c₀ / 2, by linarith, fun t ht => ?_⟩
  have hτnn : 0 ≤ Work.FTS.Physical.clockInv C t := Work.FTS.Physical.clockInv_nonneg C ht
  have hTt : (0 : ℝ) < C.T - t := sub_pos.mpr ht.2
  have htail : C.A (Work.FTS.Physical.clockInv C t) ≤ 2 * (C.T - t) := by
    have h := Work.FTS.Physical.Clock.A_le_two_mul_tail C hτnn
    rwa [Work.FTS.Physical.clockInv_clock C ht] at h
  have hAτ : A (Work.FTS.Physical.clockInv C t) ≤ 2 * (C.T - t) := by
    have h2 : A (Work.FTS.Physical.clockInv C t)
        = C.A (Work.FTS.Physical.clockInv C t) / 2 := by
      have h := hAeq (Work.FTS.Physical.clockInv C t) hτnn
      linarith
    rw [h2]; linarith [htail]
  have hAposτ : 0 < A (Work.FTS.Physical.clockInv C t) := hApos _ hτnn
  obtain ⟨x, hx⟩ := hc₀ (Work.FTS.Physical.clockInv C t) hτnn
  have hstep : c₀ / (2 * (C.T - t)) ≤ c₀ / A (Work.FTS.Physical.clockInv C t) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hAposτ hAτ) hc₀pos.le
  have hrew : (c₀ / 2) / (C.T - t) = c₀ / (2 * (C.T - t)) := by rw [div_div]
  have hbd : BddAbove (Set.range (fun x : R3 =>
      ‖- Work.FTS.Physical.physOmega (α : ℝ) A B g C x t‖)) := by
    obtain ⟨M, _hM0, hM⟩ := Prime.physVort_bound
      (hreg (Work.FTS.Physical.clockInv C t + 1) (by linarith))
    refine ⟨M, ?_⟩
    rintro _ ⟨y, rfl⟩
    have h := hM (Work.FTS.Physical.clockInv C t) ⟨hτnn, by linarith⟩ y
    simpa only [Work.FTS.Physical.physOmega_apply, norm_neg] using h
  rw [hrew]
  calc c₀ / (2 * (C.T - t)) ≤ c₀ / A (Work.FTS.Physical.clockInv C t) := hstep
    _ ≤ ‖Work.FTS.Regularity.physVort (α : ℝ) A B g x (Work.FTS.Physical.clockInv C t)‖ := hx
    _ = ‖- Work.FTS.Physical.physOmega (α : ℝ) A B g C x t‖ := by
        rw [Work.FTS.Physical.physOmega_apply, norm_neg]
    _ ≤ ⨆ x : R3, ‖- Work.FTS.Physical.physOmega (α : ℝ) A B g C x t‖ := le_ciSup hbd x

end Work.FTS.FireFix
end
-- ===== merged: Submission.Work.FTS.MeridianDyn.Vort =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set
open scoped Topology

namespace Work.FTS.MeridianDyn

set_option autoImplicit false


end Work.FTS.MeridianDyn
end
end
