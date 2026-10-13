/-
# Row 15: the pointwise `ℋ⁴`-bounds for `N₂^{ss}`

This module proves the two pointwise hypotheses of `wtoHQ_of_pointwise_open` for the
open-quadrant representative `N2ssO α Φs = ψ(z)·(2·C15 α θ)·G15 α Φs z θ` of
`N₂^{ss}(α, Φ_*)`:

* `|(1+z)·w(z)·z^m·∂_z^m N₂^{ss}(z,θ)| ≤ 200000·W`,
* `|(1+z)·w(z)·z^l·∂_z^l D_θ^i N₂^{ss}(z,θ)| ≤ 200000·W·(α+sin2θ)·sin(2θ)^{α/5}`  (`i ≥ 1`),

with `W = KW15·α·|G15|_{𝒲^{4,∞}}`.

The route is the factorization of row 15 on the open quadrant,

  `N₂^{ss}(z,θ) = ψ(z)·A(θ)·G(z,θ)`,   `ψ(z) = z²/(1+z)³`,  `A(θ) = 2·C15 α θ`,
  `G(z,θ) = ((z+1)/z)·(𝒰(Φ̃_*)(z,θ)/sin 2θ) = G15 α Φs z θ`

(`N2ss_open_eq`), the Leibniz inequality `sqm_pz_DthIter_mul_le_4_open`, the jet bound
`pzIter_psi15_le` of the radial factor `ψ`, the angular jet bounds of `A = 2·C15` and the two
`𝒲^{4,∞}`-bounds of `G` (`pz_sup_bound`, `pz_Dth_sup_bound`).

The two facts about the `θ`-only factor that make the bookkeeping work are: its `z`-jets
vanish (so that the `D_z^c`-sum of Leibniz collapses to `c = 0`), and its angular jets carry
either a *flat* bound `|D_θ^a A| ≤ K α²` — used when at least one angular derivative falls on
`G`, whose `𝒲^{4,∞}`-bound then supplies the weight `(α+sin2θ)sin(2θ)^{α/5}` — or the
*weighted* bound `|D_θ^a A| ≤ K α (α+sin2θ)sin(2θ)^{α/5}` — used when all angular
derivatives fall on `A` (there `G` is bounded only by its `𝒲^{4,∞}`-norm).  The weighted bound
is `dthU_Gam_le` (`|D_θ^mΓ| ≤ α·tBound·Γ`) combined with `Gam_mul_weight_le`
(`α Γ sin(2θ)^{-α/5}/(α+sin2θ) ≤ 1`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.NonlinRows.NRow15T2Aux.Defs
import Submission.Work.FTS.NonlinRows.NRow15T2Aux.Jets
import Submission.Work.FTS.NonlinRows.sqm_pz_DthIter_mul_le_4_open
import Submission.Work.FTS.NonlinRows.wtoHQ_of_pointwise_open
import Submission.Work.FTS.NonlinRows.NRow10aux.hkmem_of_majorant
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.Spaces.WlInf_terms
import Submission.Work.FTS.H2.STBounds
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.row15_defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.NonlinRows

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

/-! ## The factorization of `N₂^{ss}` on the open quadrant -/

theorem N2ss_open_eq {α : ℝ} {Φs : Fn} (hα : 0 < α) {z θ : ℝ}
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < π / 2) :
    Work.FTS.Nonlin.N2ss α Φs z θ = psi15 z * (2 * C15 α θ * G15 α Φs z θ) := by
  have hs2 : Work.Construction.s2 θ ≠ 0 := by
    rw [Work.Construction.s2_eq]
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hz1 : (1 : ℝ) + z ≠ 0 := by linarith
  rw [Work.FTS.Nonlin.N2ss, Work.Construction.pth_Fstar_eq hα]
  rw [C15_apply, Work.Spaces.dthU, Work.FM.Fstar, psi15_eq, G15_apply]
  field_simp
  rw [Work.Construction.s2_eq]
  ring

/-! ## Functorial evaluations of the iterated operators on one-variable functions -/

theorem pzIter_thetaFn (A : ℝ → ℝ) (d : ℕ) :
    Work.Spaces.pzIter d (fun _ (θ : ℝ) => A θ) = fun _ θ => if d = 0 then A θ else 0 := by
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [Work.Spaces.pzIter_succ, ih]
      funext z θ
      show deriv (fun z' : ℝ => (if d = 0 then A θ else (0 : ℝ))) z
        = (if d + 1 = 0 then A θ else 0)
      rw [deriv_const]
      simp

theorem pzIter_DthIter_thetaFn (A : ℝ → ℝ) (e d : ℕ) :
    Work.Spaces.pzIter d (Work.Spaces.DthIter e (fun _ (θ : ℝ) => A θ))
      = fun _ θ => if d = 0 then Work.Spaces.dthU^[e] A θ else 0 := by
  rw [DthIter_theta_only, pzIter_thetaFn]

theorem pzIter_thetaFn_apply (A : ℝ → ℝ) (d : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter d (fun _ (θ : ℝ) => A θ) z θ = if d = 0 then A θ else 0 := by
  rw [pzIter_thetaFn]

theorem pzIter_DthIter_thetaFn_apply (A : ℝ → ℝ) (e d : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter d (Work.Spaces.DthIter e (fun _ (θ : ℝ) => A θ)) z θ
      = if d = 0 then Work.Spaces.dthU^[e] A θ else 0 := by
  rw [pzIter_DthIter_thetaFn]

theorem DthIter_zFn (r : ℝ → ℝ) (a : ℕ) (ha : 1 ≤ a) :
    Work.Spaces.DthIter a (fun z _ => r z) = fun _ _ => (0 : ℝ) := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  induction b with
  | zero =>
      funext z θ
      rw [Nat.zero_add, Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero]
      show Real.sin (2 * θ) * Work.Spaces.pth (fun z _ => r z) z θ = 0
      simp [Work.Spaces.pth]
  | succ b ih =>
      have hb : 1 ≤ b + 1 := by omega
      rw [show b + 1 + 1 = (b + 1) + 1 from by ring, Work.Spaces.DthIter_succ, ih hb]
      funext z θ
      show Real.sin (2 * θ) * Work.Spaces.pth (fun _ _ => (0 : ℝ)) z θ = 0
      simp [Work.Spaces.pth]

theorem pzIter_DthIter_zFn (r : ℝ → ℝ) (a c : ℕ) (ha : 1 ≤ a) :
    Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z _ => r z)) = fun _ _ => (0 : ℝ) := by
  rw [DthIter_zFn r a ha]
  induction c with
  | zero => rfl
  | succ c ih =>
      rw [Work.Spaces.pzIter_succ, ih]
      funext z θ
      simp [Work.Spaces.pz]

/-! ## The angular factor `A = 2·C15` and the product `A·G` -/

/-- The angular factor `A = 2·C15 α` of row 15.  Since `C15 α = -2(α/c)·D_θΓ`, `A` carries
two factors of `α` and, like `D_θΓ`, vanishes at the two angular endpoints. -/
def A15 (α : ℝ) : ℝ → ℝ := fun θ => 2 * C15 α θ

/-- The product `A·G` of the angular factor with the weighted star coefficient. -/
def AG15 (α : ℝ) (Φs : Fn) : Fn := fun z θ => 2 * C15 α θ * G15 α Φs z θ

/-- The open-quadrant representative `ψ·A·G` of `N₂^{ss}`. -/
def N2ssO (α : ℝ) (Φs : Fn) : Fn := fun z θ => psi15 z * AG15 α Φs z θ

/-! ## A constant double range sum -/

theorem sum_range_range_const (n m : ℕ) (C : ℝ) :
    (∑ _c ∈ Finset.range (n + 1), ∑ _a ∈ Finset.range (m + 1), C)
      ≤ (((n + 1 : ℕ)) : ℝ) * (((m + 1 : ℕ)) : ℝ) * C := by
  have hinner : ∀ c ∈ Finset.range (n + 1),
      (∑ _a ∈ Finset.range (m + 1), C) ≤ (((m + 1 : ℕ)) : ℝ) * C := by
    intro c hc
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc (∑ _c ∈ Finset.range (n + 1), ∑ _a ∈ Finset.range (m + 1), C)
      ≤ ∑ _c ∈ Finset.range (n + 1), (((m + 1 : ℕ)) : ℝ) * C :=
        Finset.sum_le_sum hinner
    _ ≤ (((n + 1 : ℕ)) : ℝ) * ((((m + 1 : ℕ)) : ℝ) * C) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = (((n + 1 : ℕ)) : ℝ) * (((m + 1 : ℕ)) : ℝ) * C := by ring

/-- Pulling a constant out of a double range sum. -/
theorem mul_sum_sum_const {ι κ : Type*} (s : Finset ι) (t : Finset κ) (c : ℝ)
    (f : ι → κ → ℝ) :
    c * (∑ i ∈ s, ∑ j ∈ t, f i j) = ∑ i ∈ s, ∑ j ∈ t, c * f i j := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]

/-! ## The weighted angular bound `α Γ ≤ (α + sin 2θ) sin(2θ)^{α/5}` -/

theorem alpha_Gam_le_weight (α θ : ℝ) (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    α * Work.Spaces.Gam α θ
      ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) := by
  have hs0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hc0 : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hsin2 : 0 ≤ Real.sin (2 * θ) := by rw [Real.sin_two_mul]; positivity
  have hgam := Work.Spaces.Gam_mul_weight_le α θ hα hθ
  have hden : 0 < α + Real.sin (2 * θ) := by linarith
  have h1 : α * Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ (-(α / 5))
      ≤ α + Real.sin (2 * θ) := (div_le_one hden).mp hgam
  have h2 : α * Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ (-(α / 5))
        * (Real.sin (2 * θ)) ^ (α / 5)
      ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
    mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hsin2 _)
  have hsq : α * Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ (-(α / 5))
        * (Real.sin (2 * θ)) ^ (α / 5) = α * Work.Spaces.Gam α θ := by
    rcases eq_or_lt_of_le hsin2 with h | h
    · have hΓ : Work.Spaces.Gam α θ = 0 := by
        have hle := Work.FTS.Nonlinear.Pieces.RNP.row15aux.Gam_le_sin_two_rpow α θ hα hθ
        rw [← h, Real.zero_rpow (by linarith : α / 5 ≠ 0)] at hle
        linarith [(Work.Spaces.Gam_bounds α θ hα hθ).1]
      rw [hΓ]; ring
    · have h3 : (Real.sin (2 * θ)) ^ (-(α / 5)) * (Real.sin (2 * θ)) ^ (α / 5) = 1 := by
        rw [← Real.rpow_add h, show -(α / 5) + α / 5 = 0 by ring, Real.rpow_zero]
      calc α * Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ (-(α / 5))
            * (Real.sin (2 * θ)) ^ (α / 5)
          = (α * Work.Spaces.Gam α θ)
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) * (Real.sin (2 * θ)) ^ (α / 5)) := by ring
        _ = (α * Work.Spaces.Gam α θ) * 1 := by rw [h3]
        _ = α * Work.Spaces.Gam α θ := by ring
  rw [hsq] at h2
  exact h2

/-! ## The two angular jet bounds of `A = 2·C15` -/

/-- Flat angular jet bound of `A = 2·C15`: `|D_θ^a A| ≤ K α² Γ` for `a ≤ 4`. -/
theorem dthU_iter_A_le :
    ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (a : ℕ), a ≤ 4 →
      ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.dthU^[a] (fun θ => 2 * C15 α θ) θ| ≤ K * α ^ 2 * Work.Spaces.Gam α θ := by
  obtain ⟨K, hK, hKb⟩ := dthU_iter_C15_le
  refine ⟨2 * K, by positivity, ?_⟩
  intro α hα hα1 a ha θ hθ
  rw [show (fun θ => 2 * C15 α θ) = fun θ => (2 : ℝ) * C15 α θ from rfl,
    Work.Spaces.dthU_iter_const_mul]
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc (2 : ℝ) * |Work.Spaces.dthU^[a] (C15 α) θ|
      ≤ 2 * (K * α ^ 2 * Work.Spaces.Gam α θ) :=
        mul_le_mul_of_nonneg_left (hKb α hα hα1 a ha θ hθ) (by norm_num)
    _ = 2 * K * α ^ 2 * Work.Spaces.Gam α θ := by ring

theorem dthU_iter_A_flat_le :
    ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (a : ℕ), a ≤ 4 →
      ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.dthU^[a] (fun θ => 2 * C15 α θ) θ| ≤ K * α ^ 2 := by
  obtain ⟨K, hK, hKb⟩ := dthU_iter_A_le
  refine ⟨max K 1, lt_of_lt_of_le hK (le_max_left _ _), ?_⟩
  intro α hα hα1 a ha θ hθ
  have hG1 : Work.Spaces.Gam α θ ≤ 1 := (Work.Spaces.Gam_bounds α θ hα hθ).2
  have h1 := hKb α hα hα1 a ha θ hθ
  have hKα : (0 : ℝ) ≤ K * α ^ 2 := mul_nonneg hK.le (sq_nonneg α)
  have h2 : K * α ^ 2 * Work.Spaces.Gam α θ ≤ K * α ^ 2 := by
    calc K * α ^ 2 * Work.Spaces.Gam α θ ≤ K * α ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hG1 hKα
      _ = K * α ^ 2 := by ring
  exact le_trans h1 (le_trans h2 (mul_le_mul_of_nonneg_right (le_max_left K 1) (sq_nonneg α)))

theorem dthU_iter_A_weight_le :
    ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (a : ℕ), a ≤ 4 →
      ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.dthU^[a] (fun θ => 2 * C15 α θ) θ|
        ≤ K * α * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
  refine ⟨40 * ((∑ a ∈ Finset.range 5, Work.Spaces.tBound a 0) + 1), ?_, ?_⟩
  · have h0 : (0 : ℝ) ≤ ∑ a ∈ Finset.range 5, Work.Spaces.tBound a 0 :=
      Finset.sum_nonneg fun a _ => Work.Spaces.tBound_nonneg a 0
    linarith
  · intro α hα hα1 a ha θ hθ
    have hTB : (0 : ℝ) ≤ ∑ a ∈ Finset.range 5, Work.Spaces.tBound a 0 :=
      Finset.sum_nonneg fun a _ => Work.Spaces.tBound_nonneg a 0
    have hGam0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
    have hsin2 : 0 ≤ Real.sin (2 * θ) := by
      have hs0 : 0 ≤ Real.sin θ :=
        Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
      have hc0 : 0 ≤ Real.cos θ :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
      rw [Real.sin_two_mul]; positivity
    have hw0 : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
      mul_nonneg (by linarith) (Real.rpow_nonneg hsin2 _)
    have hc : (0 : ℝ) < Work.Spaces.c α := by
      have h := (Work.Spaces.c_bounds α hα hα1).1
      linarith
    have hcinv : (Work.Spaces.c α)⁻¹ ≤ 10 := by
      rw [inv_eq_one_div, div_le_iff₀ hc]
      linarith [(Work.Spaces.c_bounds α hα hα1).1]
    have hk : |α / Work.Spaces.c α| ≤ 10 * α := by
      rw [abs_of_nonneg (div_nonneg hα.le hc.le), div_eq_mul_inv]
      calc α * (Work.Spaces.c α)⁻¹ ≤ α * 10 := mul_le_mul_of_nonneg_left hcinv hα.le
        _ = 10 * α := by ring
    have htb : Work.Spaces.tBound a 0 ≤ ∑ a ∈ Finset.range 5, Work.Spaces.tBound a 0 :=
      Finset.single_le_sum (f := fun a => Work.Spaces.tBound a 0)
        (fun a _ => Work.Spaces.tBound_nonneg a 0) (Finset.mem_range.mpr (by omega))
    have hdth := Work.Spaces.dthU_Gam_le (a + 1) (by omega) α hα hα1 θ hθ
    rw [show a + 1 - 1 = a from by omega] at hdth
    have hGamw := alpha_Gam_le_weight α θ hα hθ
    rw [show (fun θ => 2 * C15 α θ) = fun θ => (2 : ℝ) * C15 α θ from rfl,
      Work.Spaces.dthU_iter_const_mul, dthU_iter_C15]
    rw [abs_mul, abs_mul, show |(2 : ℝ)| = 2 from by norm_num,
      show |(-2 * (α / Work.Spaces.c α))| = 2 * |α / Work.Spaces.c α| from by
        rw [abs_mul]; norm_num]
    rw [show (2 : ℝ) * (2 * |α / Work.Spaces.c α|
          * |Work.Spaces.dthU^[a + 1] (fun t => Work.Spaces.Gam α t) θ|)
        = (2 : ℝ) * (2 * |α / Work.Spaces.c α|)
          * |Work.Spaces.dthU^[a + 1] (fun t => Work.Spaces.Gam α t) θ| from by ring]
    have h1 : |Work.Spaces.dthU^[a + 1] (fun t => Work.Spaces.Gam α t) θ|
        ≤ α * (∑ a ∈ Finset.range 5, Work.Spaces.tBound a 0) * Work.Spaces.Gam α θ :=
      hdth.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htb hα.le) hGam0)
    have h2 : (2 : ℝ) * (2 * |α / Work.Spaces.c α|)
        * |Work.Spaces.dthU^[a + 1] (fun t => Work.Spaces.Gam α t) θ|
        ≤ (2 : ℝ) * (2 * (10 * α))
          * (α * (∑ a ∈ Finset.range 5, Work.Spaces.tBound a 0) * Work.Spaces.Gam α θ) := by
      refine mul_le_mul ?_ h1 (abs_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hk (by norm_num))
        (by norm_num)
    refine le_trans h2 ?_
    have h5 : (2 : ℝ) * (2 * (10 * α))
          * (α * (∑ a ∈ Finset.range 5, Work.Spaces.tBound a 0) * Work.Spaces.Gam α θ)
        = 40 * (∑ a ∈ Finset.range 5, Work.Spaces.tBound a 0)
            * (α * (α * Work.Spaces.Gam α θ)) := by ring
    rw [h5]
    have h6 : α * (α * Work.Spaces.Gam α θ)
        ≤ α * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
      mul_le_mul_of_nonneg_left hGamw hα.le
    have h7 : (40 : ℝ) * (∑ a ∈ Finset.range 5, Work.Spaces.tBound a 0)
          * (α * (α * Work.Spaces.Gam α θ))
        ≤ 40 * (∑ a ∈ Finset.range 5, Work.Spaces.tBound a 0)
          * (α * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
      mul_le_mul_of_nonneg_left h6 (by linarith)
    refine le_trans h7 ?_
    have h8 : (40 : ℝ) * (∑ a ∈ Finset.range 5, Work.Spaces.tBound a 0)
        ≤ 40 * ((∑ a ∈ Finset.range 5, Work.Spaces.tBound a 0) + 1) := by linarith
    have h9 : (40 : ℝ) * (∑ a ∈ Finset.range 5, Work.Spaces.tBound a 0)
          * (α * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
        ≤ 40 * ((∑ a ∈ Finset.range 5, Work.Spaces.tBound a 0) + 1)
          * (α * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
      mul_le_mul_of_nonneg_right h8 (mul_nonneg hα.le hw0)
    refine le_trans h9 (le_of_eq ?_)
    ring

/-! ## Named constants

The final constant `KW15` of the row must be *nameable* (it is the `K` of the row statement),
so the four numerical constants of the lemmas above are extracted with `Classical.choose`. -/

noncomputable def KA15 : ℝ := Classical.choose dthU_iter_A_flat_le

theorem KA15_pos : 0 < KA15 := (Classical.choose_spec dthU_iter_A_flat_le).1

theorem KA15_bd : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (a : ℕ), a ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
    |Work.Spaces.dthU^[a] (fun θ => 2 * C15 α θ) θ| ≤ KA15 * α ^ 2 :=
  (Classical.choose_spec dthU_iter_A_flat_le).2

noncomputable def KB15 : ℝ := Classical.choose dthU_iter_A_weight_le

theorem KB15_pos : 0 < KB15 := (Classical.choose_spec dthU_iter_A_weight_le).1

theorem KB15_bd : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (a : ℕ), a ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
    |Work.Spaces.dthU^[a] (fun θ => 2 * C15 α θ) θ|
      ≤ KB15 * α * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
  (Classical.choose_spec dthU_iter_A_weight_le).2

noncomputable def Cp15 : ℝ := Classical.choose pzIter_psi15_le

theorem Cp15_pos : 0 < Cp15 := (Classical.choose_spec pzIter_psi15_le).1

theorem Cp15_bd : ∀ (c m : ℕ), c ≤ m → m ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ : ℝ,
    (1 + z) * Work.Spaces.w z * z ^ m * |Work.Spaces.pzIter c (fun z _ => psi15 z) z θ|
      ≤ Cp15 * (1 + z) ^ (m - c) :=
  (Classical.choose_spec pzIter_psi15_le).2

/-- The constant of the flat `z`-jet bound of `A·G`. -/
noncomputable def KAG15 : ℝ := 257 * 5 * KA15

/-- The constant of the weighted mixed jet bound of `A·G`. -/
noncomputable def KAGd15 : ℝ := 257 * 25 * (KA15 + KB15 + 1)

theorem KAG15_pos : 0 < KAG15 := by
  rw [KAG15]; exact mul_pos (by norm_num) KA15_pos

theorem KAGd15_pos : 0 < KAGd15 := by
  rw [KAGd15]
  have := KA15_pos
  have := KB15_pos
  positivity

/-- **The final constant of row 15**: `W = KW15·α·|G15|_{𝒲^{4,∞}}`. -/
noncomputable def KW15 : ℝ := 10 ^ 6 * (Cp15 * (KAG15 + KAGd15 + 1) + 1) + 1

theorem KW15_pos : 0 < KW15 := by
  rw [KW15]
  have := Cp15_pos
  have := KAG15_pos
  have := KAGd15_pos
  positivity

/-! ## Smoothness of the two factors on the open quadrant -/

theorem smoothOpen_A15' (α : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => 2 * C15 α θ) :=
  Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl 2 (smoothOpen_C15_bsl α)

theorem smoothOpen_AG15 {α Cs : ℝ} {Φs : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) :
    Work.FTS.EllipticEst.SmoothOpen (AG15 α Φs) := by
  have h := Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
    (smoothOpen_A15' α) (smoothOpen_G15 hα hα1 hs)
  refine Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl h ?_
  intro z θ _ _ _
  simp [AG15]

theorem smoothOpen_N2ssO {α Cs : ℝ} {Φs : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) :
    Work.FTS.EllipticEst.SmoothOpen (N2ssO α Φs) := by
  have h := Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
    (show Work.FTS.EllipticEst.SmoothOpen (fun z (_ : ℝ) => psi15 z) from smoothOpen_psi15)
    (smoothOpen_AG15 hα hα1 hs)
  refine Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl h ?_
  intro z θ _ _ _
  simp [N2ssO]

/-! ## The `z`-jets of the two factors

The Leibniz inequality `sqm_pz_DthIter_mul_le_4_open` is applied to the pair `(A, G)`; because
`A` is `θ`-only, the `D_z^c`-sum over `A` collapses to `c = 0`. -/

