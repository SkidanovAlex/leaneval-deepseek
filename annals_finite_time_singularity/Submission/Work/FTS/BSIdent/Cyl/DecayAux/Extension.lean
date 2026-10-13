import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.BSIdent.Defs
import Submission.Work.FTS.BSIdent.Cyl.DecayAux.Basic
import Submission.Work.FTS.BSIdent.Cyl.DecayAux.Wrapper
import Submission.Work.FTS.BSIdent.Cyl.DecayAux.PosQuadrant
import Submission.Work.FTS.BSIdent.Cyl.DecayAux.abs_deriv_zero_le_of_bound_right

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

/-- **The bound on `ψ/r` on `r ≥ 0`, all `z`.** -/
theorem abs_div_merPsiT_le' {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Physical.PhysClock} {t : ℝ}
    (hα : 0 < α) (hB : 0 < B (Physical.clockInv C t))
    (h0 : ∀ w, 0 < w → Φ w 0 (Physical.clockInv C t) = 0)
    {q lam C₀ : ℝ} (hq : 2 < q) (hlam : 0 < lam) (hC₀ : 0 < C₀)
    (hexp : 3 ≤ Work.FTS.Regularity.pExp α * lam)
    (hrate : PhiRate Φ (Physical.clockInv C t) C₀ q lam) :
    ∀ r z, 0 ≤ r →
      |merPsiT α A B Φ C t r z / r|
        ≤ decayKq ((A (Physical.clockInv C t))⁻¹) C₀ q lam (B (Physical.clockInv C t))
            / (1 + Work.Cyl.rhoP r z) := by
  intro r z hr0
  rcases eq_or_lt_of_le hr0 with hr_eq | hr
  · subst hr_eq
    rw [div_zero, abs_zero]
    exact div_one_add_nonneg (decayKq_nonneg hC₀.le) (Work.Cyl.rhoP_nonneg 0 z)
  · exact abs_div_merPsiT_le hα hB h0 hq hlam hC₀ hexp hrate r z hr

end Work.FTS.BSIdent.Cyl
