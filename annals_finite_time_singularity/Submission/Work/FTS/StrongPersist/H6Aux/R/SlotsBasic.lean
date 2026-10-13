/-
# The four level-one slot estimates for the base case `base_R`

This file assembles the lower bound

  `-r · H1IP α h h ≤ H1IP α (Lhat h) h`

out of the four `wip`-pairings that make up `H1IP`, for `h` smooth on the open quadrant
with honest `ℋ²`-integral.

The route is *not* the full expansion of `Lhat h` against all four slots.  Instead:

* the two *zeroth order* slots (`wip ρ_η (Lhat h) h` and `wip (w²) (Lhat h) h`) are bounded
  below by the pointwise AM–GM
  `Lhat h·h·ρ ≥ -(1/2)(D_z h)²ρ - (9/2)(D_θh)²ρ - 2h²ρ`,
  which involves only *first* derivatives of `h` — no integration by parts at all;
* the two *first order* slots (`wip ρ_η (D_z (Lhat h)) (D_z h)` and
  `wip ρ_γ (D_θ (Lhat h)) (D_θ h)`) are first rewritten with the commutator identities of
  `Lhat` (`D_θ Lhat = Lhat D_θ`, `D_z Lhat = Lhat D_z + Ê₂`), then expanded, and the
  *adjacent* pairings `∫ (D_z g)·g·ρ` and `∫ (D_θ g)·g·ρ` (with `g = D_z h` resp. `g = D_θ h`)
  are converted into the `g²`-slot by the two integration by parts `wip_Dz_ibp` and
  `wip_Dth_ibp`.  This is where the second derivatives of `h` are consumed (in the
  integrability hypotheses only), and where `HkMem α 2 h` is used.

Every integral produced on the way is dominated by `HkSq α 1 h ≤ H1IP α h h`, so the
constant `r` is universal.

## Integrability strategy

`HkMem α 2 h` makes `HkIntegrand α 2 h` jointly integrable.  Everything else is obtained
from `integrableOfHkDom`: an integrand that is continuous on the open quadrant and a.e.
dominated by `C·HkIntegrand α 2 h` is integrable.  The a.e. domination is provided by the
block bounds `sq_le_Hk_dz` / `sq_le_Hk_mixed` (the `D_z`- and mixed summands of the
`ℋ²`-integrand) together with `2|uv| ≤ u² + v²`.

Conventions: `ρ_β = Rho β = w²·sin(2θ)^{-β}` (so `ρ_0 = w²`), `η = 99/100`,
`γ = gam α = 1 + α/10`, `Iθ = [0,π/2]`, `Iz = [0,∞)`, `dz dθ` measure.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.Coercivity.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.CoercivityFix.Basic
import Submission.Work.FTS.CoercivityFix.Coer1.Defs
import Submission.Work.FTS.CoercivityFix.Coer1.IntFacts
import Submission.Work.FTS.CoercivityFix.DzSelf.H1IP_Dz_self
import Submission.Work.FTS.IPGen.OpenBasic
import Submission.Work.FTS.StrongPersist.H6Aux.wip_Dz_ibp
import Submission.Work.FTS.StrongPersist.H6Aux.LhatCommOpen
import Submission.Work.FTS.StrongPersist.H6Aux.R.DthIbp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Aux.R

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 3200000
/-- The angular weight `ρ_β = w²·sin(2θ)^{-β}` (the paper's `w²sin^{-β}`). -/
abbrev Rhoq (β : ℝ) : Fn := Work.FTS.CoercivityFix.Coer1.Rho β

/-- The open quadrant of `SmoothOpen`. -/
abbrev Q0 : Set (ℝ × ℝ) := Work.FTS.EllipticEst.Q0

/-- The product measure on the quadrant is the restriction of the planar measure. -/
theorem pm_eq_restrict :
    (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      = MeasureTheory.volume.restrict ((Work.Spaces.Iz : Set ℝ) ×ˢ (Work.Spaces.Iθ : Set ℝ)) := by
  rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.volume_eq_prod]

/-- Almost every angle of the quadrant is interior. -/
theorem ae_angle_Ioo :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)), p.2 ∈ Set.Ioo 0 (Real.pi / 2) :=
  Work.FTS.CoercivityFix.Coer1.ae_prod_snd_mem_Ioo

/-- Almost every point of the quadrant has positive radius. -/
theorem ae_radius_pos : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)), 0 < p.1 :=
  Work.FTS.CoercivityFix.Coer1.ae_prod_fst_pos

/-! ## Elementary `wip` manipulations -/

/-- Pointwise congruence of `wip` in the first argument. -/
theorem wip_congr_fst {ρ A B g : Fn} (h : ∀ z θ, A z θ = B z θ) :
    Work.Coercivity.wip ρ A g = Work.Coercivity.wip ρ B g := by
  simp only [Work.Coercivity.wip]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with z
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc ?_
  intro θ _
  show A z θ * g z θ * ρ z θ = B z θ * g z θ * ρ z θ
  rw [h z θ]

/-- Pointwise congruence of `wip` in the second argument. -/
theorem wip_congr_snd {ρ g₁ g₂ A : Fn} (h : ∀ z θ, g₁ z θ = g₂ z θ) :
    Work.Coercivity.wip ρ A g₁ = Work.Coercivity.wip ρ A g₂ := by
  simp only [Work.Coercivity.wip]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with z
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc ?_
  intro θ _
  show A z θ * g₁ z θ * ρ z θ = A z θ * g₂ z θ * ρ z θ
  rw [h z θ]

/-- `wip ρ u u` is the iterated integral of `u²ρ`. -/
theorem wip_self_eq (ρ u : Fn) :
    Work.Coercivity.wip ρ u u
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, u z θ ^ 2 * ρ z θ := by
  simp only [Work.Coercivity.wip]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with z
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc ?_
  intro θ _; ring

/-- **Monotonicity of `wip`** in the a.e. order of the integrands. -/
theorem wip_mono {ρ₁ ρ₂ A₁ A₂ B : Fn}
    (hint₁ : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => A₁ z θ * B z θ * ρ₁ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hint₂ : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => A₂ z θ * B z θ * ρ₂ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (h : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
        A₁ p.1 p.2 * B p.1 p.2 * ρ₁ p.1 p.2 ≤ A₂ p.1 p.2 * B p.1 p.2 * ρ₂ p.1 p.2) :
    Work.Coercivity.wip ρ₁ A₁ B ≤ Work.Coercivity.wip ρ₂ A₂ B := by
  have hi₁ : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => A₁ p.1 p.2 * B p.1 p.2 * ρ₁ p.1 p.2) ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [MeasureTheory.IntegrableOn] at hint₁
    rwa [← pm_eq_restrict] at hint₁
  have hi₂ : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => A₂ p.1 p.2 * B p.1 p.2 * ρ₂ p.1 p.2) ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [MeasureTheory.IntegrableOn] at hint₂
    rwa [← pm_eq_restrict] at hint₂
  rw [Work.Coercivity.wip_eq_integral_prod ρ₁ A₁ B hint₁,
    Work.Coercivity.wip_eq_integral_prod ρ₂ A₂ B hint₂]
  exact MeasureTheory.integral_mono_ae hi₁ hi₂ h

/-- `wip ρ (χ·A) A ≥ 0` for a nonnegative multiplier `χ` and a nonnegative weight `ρ`. -/
theorem wip_chi_self_nonneg {ρ A : Fn} {χ : ℝ → ℝ}
    (hχ : ∀ z, 0 ≤ χ z) (hρ : ∀ z θ, θ ∈ Work.Spaces.Iθ → 0 ≤ ρ z θ) :
    0 ≤ Work.Coercivity.wip ρ (fun z θ => χ z * A z θ) A := by
  rw [Work.Coercivity.wip]
  refine MeasureTheory.setIntegral_nonneg measurableSet_Ici fun z _ => ?_
  refine MeasureTheory.setIntegral_nonneg measurableSet_Icc fun θ hθ => ?_
  have : (χ z * A z θ) * A z θ * ρ z θ = χ z * (A z θ * A z θ) * ρ z θ := by ring
  rw [this]
  exact mul_nonneg (mul_nonneg (hχ z) (mul_self_nonneg _)) (hρ z θ hθ)

/-! ## The `ℋ²`-integrand is integrable -/

/-- `HkIntegrand α k h` is jointly integrable on the quadrant when `h ∈ ℋᵏ` and is smooth
on the open quadrant. -/
theorem int_HkIntegrand (α : ℝ) (k : ℕ) {h : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen h)
    (hm : Work.Spaces.HkMem α k h) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.HkIntegrand α k h z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  have hsm : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (fun z θ => Work.Spaces.HkIntegrand α k h z θ)) ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _
      (hs.continuousOn_HkIntegrand α k)
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => Work.Spaces.HkIntegrand α k h z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hm.1
  have hmain := (Work.Spaces.integrable_prod_of_iterated
    (fun z θ => Work.Spaces.HkIntegrand_nonneg α k h z θ) hsm hslice hm.2).1
  rw [MeasureTheory.IntegrableOn, ← pm_eq_restrict]
  exact hmain

/-- `HkSq α k h` as a product-measure integral of `HkIntegrand α k h`. -/
theorem HkSq_eq_prod (α : ℝ) (k : ℕ) {h : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen h)
    (hm : Work.Spaces.HkMem α k h) :
    Work.Spaces.HkSq α k h
      = ∫ p : ℝ × ℝ, Work.Spaces.HkIntegrand α k h p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have hsm : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (fun z θ => Work.Spaces.HkIntegrand α k h z θ))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _
      (hs.continuousOn_HkIntegrand α k)
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => Work.Spaces.HkIntegrand α k h z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hm.1
  exact (Work.Spaces.integrable_prod_of_iterated
    (fun z θ => Work.Spaces.HkIntegrand_nonneg α k h z θ) hsm hslice hm.2).2.symm

/-- **A self-pairing dominated by a multiple of the `ℋ^k`-integrand** is bounded by `C·HkSq`. -/
theorem wip_self_le_mul_HkSq (α : ℝ) (k : ℕ) {h u : Fn} {ρ : Fn}
    (hs : Work.FTS.EllipticEst.SmoothOpen h) (hm : Work.Spaces.HkMem α k h) {C : ℝ}
    (hC : 0 ≤ C)
    (hint : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ * u z θ * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hb : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
        u p.1 p.2 * u p.1 p.2 * ρ p.1 p.2
          ≤ C * Work.Spaces.HkIntegrand α k h p.1 p.2) :
    Work.Coercivity.wip ρ u u ≤ C * Work.Spaces.HkSq α k h := by
  rw [Work.Coercivity.wip_eq_integral_prod ρ u u hint, HkSq_eq_prod α k hs hm]
  have hint' : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => u p.1 p.2 * u p.1 p.2 * ρ p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [MeasureTheory.IntegrableOn] at hint
    rw [← pm_eq_restrict] at hint
    exact hint
  have hbase := int_HkIntegrand α k hs hm
  have hbase' : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => C * Work.Spaces.HkIntegrand α k h p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [MeasureTheory.IntegrableOn] at hbase
    rw [← pm_eq_restrict] at hbase
    exact hbase.const_mul C
  rw [← MeasureTheory.integral_const_mul]
  exact MeasureTheory.integral_mono_ae hint' hbase' hb

/-- **A self-pairing dominated pointwise by the `ℋ^k`-integrand is bounded by `HkSq α k h`.** -/
theorem wip_self_le_HkSq (α : ℝ) (k : ℕ) {h u : Fn} {ρ : Fn}
    (hs : Work.FTS.EllipticEst.SmoothOpen h) (hm : Work.Spaces.HkMem α k h)
    (hint : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (u z θ) ^ 2 * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hb : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
        (u p.1 p.2) ^ 2 * ρ p.1 p.2 ≤ Work.Spaces.HkIntegrand α k h p.1 p.2) :
    Work.Coercivity.wip ρ u u ≤ Work.Spaces.HkSq α k h := by
  have hint' : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ * u z θ * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine hint.congr ?_
    filter_upwards with p
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair, sq]
  have := wip_self_le_mul_HkSq α k hs hm (C := 1) (by norm_num) hint'
    (hb.mono (fun p hp => by simpa only [sq, one_mul] using hp))
  simpa using this
/-- **A.e. congruence of `wip` in its first argument** (no integrability needed). -/
theorem wip_congr_fst_ae {ρ A B g : Fn}
    (h : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)), A p.1 p.2 = B p.1 p.2) :
    Work.Coercivity.wip ρ A g = Work.Coercivity.wip ρ B g := by
  simp only [Work.Coercivity.wip]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [MeasureTheory.Measure.ae_ae_of_ae_prod h] with z hz
  exact MeasureTheory.integral_congr_ae (hz.mono (fun θ hθ => by
    show A z θ * g z θ * ρ z θ = B z θ * g z θ * ρ z θ
    rw [hθ]))

/-! ## Weight facts -/

theorem ae_snd_mem_Iθ :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)), p.2 ∈ Work.Spaces.Iθ :=
  Work.FTS.CoercivityFix.Coer1.ae_prod_snd_mem measurableSet_Icc
    (MeasureTheory.ae_restrict_mem measurableSet_Icc)

theorem Rhoq_eta_le_gam (α : ℝ) (hα : 0 < α) :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      Rhoq Work.Spaces.eta p.1 p.2 ≤ Rhoq (Work.Spaces.gam α) p.1 p.2 := by
  filter_upwards [ae_snd_mem_Iθ] with p hp
  exact Work.FTS.CoercivityFix.Coer1.Rho_eta_le_Rho_gam α hα p.1 p.2 hp

theorem w2_le_Rhoq_eta :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (Work.Spaces.w p.1) ^ 2 ≤ Rhoq Work.Spaces.eta p.1 p.2 := by
  filter_upwards [ae_angle_Ioo] with p hp
  exact Work.FTS.CoercivityFix.Coer1.w2_le_Rho_eta p.1 p.2 hp

theorem w2_le_Rhoq_gam (α : ℝ) (hα : 0 < α) :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (Work.Spaces.w p.1) ^ 2 ≤ Rhoq (Work.Spaces.gam α) p.1 p.2 := by
  filter_upwards [ae_angle_Ioo] with p hp
  exact Work.FTS.CoercivityFix.Coer1.w2_le_Rho_gam α hα p.1 p.2 hp

/-- `(w / s^{b/2})² = w²·s^{-b}` for `s > 0`. -/
theorem div_half_sq (s w b : ℝ) (hs : 0 < s) :
    (w / s ^ (b / 2)) ^ 2 = w ^ 2 * s ^ (-b) := by
  have h2 : (s ^ (b / 2)) ^ (2 : ℝ) = (s ^ (b / 2)) ^ (2 : ℕ) := Real.rpow_natCast _ 2
  have hsp : s ^ b = (s ^ (b / 2)) ^ (2 : ℝ) := by
    rw [← Real.rpow_mul hs.le (b / 2) 2]
    norm_num
  rw [div_pow, ← h2, ← hsp, div_eq_mul_inv, Real.rpow_neg hs.le b]

/-- `(w·s^{-b/2})² = w²·s^{-b}` for `s > 0`. -/
theorem mul_half_sq (s w b : ℝ) (hs : 0 < s) :
    (w * s ^ (-(b / 2))) ^ 2 = w ^ 2 * s ^ (-b) := by
  have h2 : (s ^ (-(b / 2))) ^ (2 : ℝ) = (s ^ (-(b / 2))) ^ (2 : ℕ) := Real.rpow_natCast _ 2
  have hsp : s ^ (-b) = (s ^ (-(b / 2))) ^ (2 : ℝ) := by
    rw [← Real.rpow_mul hs.le (-(b / 2)) 2]
    norm_num
  rw [mul_pow, ← h2, ← hsp]

/-- **Integrability by domination.**  An integrand continuous on the open quadrant and a.e.
dominated by `C·HkIntegrand α k h` with `h ∈ ℋᵏ` is integrable. -/
theorem integrableOfHkDom (α : ℝ) (k : ℕ) {h : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen h)
    (hm : Work.Spaces.HkMem α k h) {X : Fn} {C : ℝ}
    (hcont : ContinuousOn (Function.uncurry X) Q0)
    (hd : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
        |X p.1 p.2| ≤ C * Work.Spaces.HkIntegrand α k h p.1 p.2) :
    MeasureTheory.IntegrableOn (Function.uncurry X) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  rw [MeasureTheory.IntegrableOn, ← pm_eq_restrict]
  have hbase := int_HkIntegrand α k hs hm
  have hmaj : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => C * Work.Spaces.HkIntegrand α k h p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [MeasureTheory.IntegrableOn] at hbase
    rw [← pm_eq_restrict] at hbase
    exact hbase.const_mul C
  have haesm : MeasureTheory.AEStronglyMeasurable (Function.uncurry X)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  refine hmaj.mono' haesm ?_
  filter_upwards [hd] with p hp
  rcases p with ⟨z, θ⟩
  simpa only [Function.uncurry_apply_pair, Real.norm_eq_abs] using hp

/-- The `u²ρ` integrability form implies the `u·u·ρ` form. -/
theorem integrableOn_sq_to_mul {u ρ : Fn}
    (h : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (u z θ) ^ 2 * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ * u z θ * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  refine h.congr ?_
  filter_upwards with p
  rcases p with ⟨z, θ⟩
  simp only [Function.uncurry_apply_pair, sq]

end Work.FTS.StrongPersist.H6Aux.R
