/-
# `Work.FTS.Regularity.physVort_holder_slice` — the spatial Hölder regularity of the physical
vorticity, uniformly on the fake-time strip

**Theorem.**  From the regularity package `RegPkg α S A B g` of node N7 the *physical* vorticity

  `physVort α A B g x τ = A(τ)⁻¹ · F(ρ(x)^{3α}/B(τ), θ(x), τ) · e_θ(x)`

is `α`-Hölder in `x`, with a constant that is uniform in `τ ∈ [0,S]`:

  `∃ C ≥ 0, ∀ τ ∈ [0,S], ∀ x y : ℝ³, ‖ω(x,τ) - ω(y,τ)‖ ≤ C · ‖x - y‖^α`.

## The argument

Everything is a *per-slice* statement, and the whole point of the explicit constants
`gCompConstNN`/`smulEThetaConst` is that the constant of the slice `x ↦ ω(x,τ)` does not depend on
`τ` — so that one constant serves the whole strip.

1. **The self-similar slice is `α`-Hölder, with an explicit constant.**  For a fixed `τ`, put
   `g̃ = gSlice g τ` (the slice of the perturbation) and `ĝ x = g̃ (ρ(x)^{3α}) (|θ(x)|)`.
   The chain of the construction area,

   `ω(x) = (3α/c(3α)) • omegaStar α x + ĝ x • e_θ(x)`  on `x₃ ≥ 0`,

   with the odd extension off that half space, gives

   `ω = omegaS (3α) g̃`  is `HolderWith (omegaSHolderConst α Cv Ng Ng K Cω) ⟨α,_⟩`,

   where the three quantitative inputs are
   * `gCompHolderQuant`: `ĝ` is `α`-Hölder with constant `gCompConstNN α Cv Ng Ng K`
     (the angular vanishing `|g| ≤ Cv Γ`, the radial/angular `α`-moduli and the Taylor data at
     `z = 0` of `RegPkg.htay` — no differentiability is used);
   * `gComp_abs_le_quant`: `|ĝ x| ≤ max K Cv · r(x)^α` (the vanishing that kills the
     discontinuity of `e_θ` on the symmetry axis);
   * `smulEThetaHolder`: `x ↦ A x • e_θ(x)` is `α`-Hölder with constant `smulEThetaConst CA Ca`
     when `A` is `α`-Hölder with constant `CA` and `|A x| ≤ Ca · r(x)^α`;
   * `holder_of_half_odd_const`: the odd extension in `x₃`, which costs a factor `3`.
   The `F_*`-part contributes `Cω` (from `holder_omegaStar`, a constant depending on `α` only).

   One technical point: `RegPkg` gives the vanishing at `z = 0` only for `θ ∈ Iθ`, while the
   composite estimate wants it for all `θ`; the slice is therefore extended off `Iθ` by `0`
   (`G` below).  Since the composite is only ever evaluated at `|θ x| ∈ Iθ`, this changes nothing.

2. **The physical slice is a positive dilation.**  With `b = B(τ)^{-1/(3α)} > 0` one has
   `ρ(b•x) = b ρ(x)`, `θ(b•x) = θ(x)`, `e_θ(b•x) = e_θ(x)`, hence

   `omegaSz (3α) g̃ (ρ(x)^{3α}/B(τ)) x = omegaS (3α) g̃ (b • x)`,

   and composing an `α`-Hölder map with the `b`-Lipschitz dilation multiplies its constant by
   `b^α ≤ bmax^α`, where `bmax = b₀^{-1/(3α)}` and `b₀ ≤ B` is the uniform lower bound of the clock.

3. **The amplitude factor `A(τ)⁻¹`** is bounded by `a₀⁻¹` on the strip, by `a₀ ≤ A`.

Hence the constant

  `C = a₀⁻¹ · (omegaSHolderConst α Cv Ng Ng K Cω : ℝ) · bmax^α`

works for every `τ ∈ [0,S]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.FTS.Regularity.Defs
import Submission.Work.FTS.Regularity.gCompHolderQuant
import Submission.Work.FTS.Regularity.gComp_abs_le_quant
import Submission.Work.FTS.Regularity.smulEThetaHolder
import Submission.Work.ConstructionInstance.Basic
import Submission.Work.ConstructionInstance.AuxOmegaStar
import Submission.Work.ConstructionInstance.omegaStar_eq_Aom
import Submission.Work.ConstructionInstance.holder_omegaStar
import Submission.Work.Cyl

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.Regularity

/-! ## 1. The explicit Hölder constant of `x ↦ omegaS (3α) g x` -/

/-- The Hölder constant of `x ↦ omegaS (3α) g x` produced by the chain
"composite + frame vector" (`gCompConstNN` and `smulEThetaConst`), with the `F_*`-part constant
`Cω` supplied from outside (it depends on `α` only). -/
def omegaSHolderConst (α Cv Lg Lθ K : ℝ) (Cω : NNReal) : NNReal :=
  3 * (Cω * ‖(3 * α / Work.Spaces.c (3 * α))‖₊
      + smulEThetaConst ((gCompConstNN α Cv Lg Lθ K : ℝ)) (max K Cv))

/-! ## 2. The half-space/odd extension at an *explicit* constant

This is `Work.ConstructionInstance.holder_of_half_odd` with the existential constant of the
half-space part replaced by the explicit one, which is what makes the estimate uniform. -/

theorem holder_of_half_odd_const {ω Φ : R3 → R3} {α : ℝ} (hα : 0 < α) {C : NNReal}
    (hΦ : HolderWith C (⟨α, hα.le⟩ : NNReal) Φ)
    (hhalf : ∀ x : R3, 0 ≤ x 2 → ω x = Φ x)
    (hodd : ∀ x : R3, ω (Work.Cyl.reflZ x) = - ω x)
    (hplane : ∀ x : R3, x 2 = 0 → Φ x = 0) :
    HolderWith (3 * C) (⟨α, hα.le⟩ : NNReal) ω := by
  have hΦb : ∀ a b : R3, ‖Φ a - Φ b‖ ≤ (C : ℝ) * ‖a - b‖ ^ α := by
    intro a b
    have h := hΦ.dist_le a b
    rw [dist_eq_norm, dist_eq_norm] at h
    exact h
  have hCnn : (0 : ℝ) ≤ (C : ℝ) := C.coe_nonneg
  have key : ∀ x y : R3, ‖ω x - ω y‖ ≤ 3 * (C : ℝ) * ‖x - y‖ ^ α := by
    intro x y
    have hxy : (0 : ℝ) ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
    have refl2 : ∀ z : R3, (Work.Cyl.reflZ z) 2 = - z 2 := by
      intro z; simp [Work.Cyl.reflZ]
    rcases le_or_gt (0 : ℝ) (x 2) with hx | hx
    · rcases le_or_gt (0 : ℝ) (y 2) with hy | hy
      · rw [hhalf x hx, hhalf y hy]
        calc ‖Φ x - Φ y‖ ≤ (C : ℝ) * ‖x - y‖ ^ α := hΦb x y
          _ ≤ 3 * (C : ℝ) * ‖x - y‖ ^ α := by nlinarith
      · have hy2 : 0 ≤ (Work.Cyl.reflZ y) 2 := by rw [refl2]; linarith
        have hry : ω (Work.Cyl.reflZ y) = Φ (Work.Cyl.reflZ y) := hhalf _ hy2
        have hwx : ω x = Φ x := hhalf x hx
        have hwy : ω y = - Φ (Work.Cyl.reflZ y) := by
          have h := hodd y
          rw [hry] at h
          rw [h]; simp
        have hmid : Φ (!₂[y 0, y 1, (0:ℝ)]) = 0 := hplane _ (by simp)
        have h1 := (Work.Cyl.dist_mid_neg_le hx hy).1
        have h2 := (Work.Cyl.dist_mid_neg_le hx hy).2
        have hpb : ‖Φ x + Φ (Work.Cyl.reflZ y)‖ ≤ 2 * (C : ℝ) * ‖x - y‖ ^ α := by
          have hdec : Φ x + Φ (Work.Cyl.reflZ y)
              = (Φ x - Φ (!₂[y 0, y 1, (0:ℝ)]))
                + (Φ (Work.Cyl.reflZ y) - Φ (!₂[y 0, y 1, (0:ℝ)])) := by
            rw [hmid]; abel
          rw [hdec]
          have htri := norm_add_le (Φ x - Φ (!₂[y 0, y 1, (0:ℝ)]))
            (Φ (Work.Cyl.reflZ y) - Φ (!₂[y 0, y 1, (0:ℝ)]))
          have ha : ‖Φ x - Φ (!₂[y 0, y 1, (0:ℝ)])‖ ≤ (C : ℝ) * ‖x - y‖ ^ α := by
            calc ‖Φ x - Φ (!₂[y 0, y 1, (0:ℝ)])‖
                ≤ (C : ℝ) * ‖x - !₂[y 0, y 1, (0:ℝ)]‖ ^ α := hΦb x _
              _ ≤ (C : ℝ) * ‖x - y‖ ^ α := by
                  apply mul_le_mul_of_nonneg_left _ hCnn
                  apply Real.rpow_le_rpow (norm_nonneg _) _ hα.le
                  rw [← dist_eq_norm, ← dist_eq_norm]
                  exact h1
          have hb : ‖Φ (Work.Cyl.reflZ y) - Φ (!₂[y 0, y 1, (0:ℝ)])‖
              ≤ (C : ℝ) * ‖x - y‖ ^ α := by
            calc ‖Φ (Work.Cyl.reflZ y) - Φ (!₂[y 0, y 1, (0:ℝ)])‖
                ≤ (C : ℝ) * ‖Work.Cyl.reflZ y - !₂[y 0, y 1, (0:ℝ)]‖ ^ α := hΦb _ _
              _ ≤ (C : ℝ) * ‖x - y‖ ^ α := by
                  apply mul_le_mul_of_nonneg_left _ hCnn
                  apply Real.rpow_le_rpow (norm_nonneg _) _ hα.le
                  rw [← dist_eq_norm, ← dist_eq_norm]
                  exact h2
          calc ‖(Φ x - Φ (!₂[y 0, y 1, (0:ℝ)]))
                  + (Φ (Work.Cyl.reflZ y) - Φ (!₂[y 0, y 1, (0:ℝ)]))‖
              ≤ _ := htri
            _ ≤ (C : ℝ) * ‖x - y‖ ^ α + (C : ℝ) * ‖x - y‖ ^ α := add_le_add ha hb
            _ = 2 * (C : ℝ) * ‖x - y‖ ^ α := by ring
        have hsplit : ω x - ω y = Φ x + Φ (Work.Cyl.reflZ y) := by rw [hwx, hwy]; abel
        rw [hsplit]
        calc ‖Φ x + Φ (Work.Cyl.reflZ y)‖ ≤ 2 * (C : ℝ) * ‖x - y‖ ^ α := hpb
          _ ≤ 3 * (C : ℝ) * ‖x - y‖ ^ α := by nlinarith
    · rcases le_or_gt (0 : ℝ) (y 2) with hy | hy
      · have hx2 : 0 ≤ (Work.Cyl.reflZ x) 2 := by rw [refl2]; linarith
        have hrx : ω (Work.Cyl.reflZ x) = Φ (Work.Cyl.reflZ x) := hhalf _ hx2
        have hwx : ω x = - Φ (Work.Cyl.reflZ x) := by
          have h := hodd x
          rw [hrx] at h
          rw [h]; simp
        have hwy : ω y = Φ y := hhalf y hy
        have hmid : Φ (!₂[y 0, y 1, (0:ℝ)]) = 0 := hplane _ (by simp)
        have h1 := (Work.Cyl.dist_mid_pos_le hx hy).1
        have h2 := (Work.Cyl.dist_mid_pos_le hx hy).2
        have hpb : ‖Φ (Work.Cyl.reflZ x) + Φ y‖ ≤ 2 * (C : ℝ) * ‖x - y‖ ^ α := by
          have hdec : Φ (Work.Cyl.reflZ x) + Φ y
              = (Φ (Work.Cyl.reflZ x) - Φ (!₂[y 0, y 1, (0:ℝ)]))
                + (Φ y - Φ (!₂[y 0, y 1, (0:ℝ)])) := by
            rw [hmid]; abel
          rw [hdec]
          have htri := norm_add_le (Φ (Work.Cyl.reflZ x) - Φ (!₂[y 0, y 1, (0:ℝ)]))
            (Φ y - Φ (!₂[y 0, y 1, (0:ℝ)]))
          have ha : ‖Φ (Work.Cyl.reflZ x) - Φ (!₂[y 0, y 1, (0:ℝ)])‖
              ≤ (C : ℝ) * ‖x - y‖ ^ α := by
            calc ‖Φ (Work.Cyl.reflZ x) - Φ (!₂[y 0, y 1, (0:ℝ)])‖
                ≤ (C : ℝ) * ‖Work.Cyl.reflZ x - !₂[y 0, y 1, (0:ℝ)]‖ ^ α := hΦb _ _
              _ ≤ (C : ℝ) * ‖x - y‖ ^ α := by
                  apply mul_le_mul_of_nonneg_left _ hCnn
                  apply Real.rpow_le_rpow (norm_nonneg _) _ hα.le
                  rw [← dist_eq_norm, ← dist_eq_norm]
                  exact h1
          have hb : ‖Φ y - Φ (!₂[y 0, y 1, (0:ℝ)])‖ ≤ (C : ℝ) * ‖x - y‖ ^ α := by
            calc ‖Φ y - Φ (!₂[y 0, y 1, (0:ℝ)])‖
                ≤ (C : ℝ) * ‖y - !₂[y 0, y 1, (0:ℝ)]‖ ^ α := hΦb y _
              _ ≤ (C : ℝ) * ‖x - y‖ ^ α := by
                  apply mul_le_mul_of_nonneg_left _ hCnn
                  apply Real.rpow_le_rpow (norm_nonneg _) _ hα.le
                  rw [← dist_eq_norm, ← dist_eq_norm]
                  exact h2
          calc ‖(Φ (Work.Cyl.reflZ x) - Φ (!₂[y 0, y 1, (0:ℝ)]))
                  + (Φ y - Φ (!₂[y 0, y 1, (0:ℝ)]))‖
              ≤ _ := htri
            _ ≤ (C : ℝ) * ‖x - y‖ ^ α + (C : ℝ) * ‖x - y‖ ^ α := add_le_add ha hb
            _ = 2 * (C : ℝ) * ‖x - y‖ ^ α := by ring
        have hsplit : ω x - ω y = - (Φ (Work.Cyl.reflZ x) + Φ y) := by rw [hwx, hwy]; abel
        rw [hsplit, norm_neg]
        calc ‖Φ (Work.Cyl.reflZ x) + Φ y‖ ≤ 2 * (C : ℝ) * ‖x - y‖ ^ α := hpb
          _ ≤ 3 * (C : ℝ) * ‖x - y‖ ^ α := by nlinarith
      · have hx2 : 0 ≤ (Work.Cyl.reflZ x) 2 := by rw [refl2]; linarith
        have hy2 : 0 ≤ (Work.Cyl.reflZ y) 2 := by rw [refl2]; linarith
        have hrx : ω (Work.Cyl.reflZ x) = Φ (Work.Cyl.reflZ x) := hhalf _ hx2
        have hry : ω (Work.Cyl.reflZ y) = Φ (Work.Cyl.reflZ y) := hhalf _ hy2
        have hwx : ω x = - Φ (Work.Cyl.reflZ x) := by
          have h := hodd x
          rw [hrx] at h
          rw [h]; simp
        have hwy : ω y = - Φ (Work.Cyl.reflZ y) := by
          have h := hodd y
          rw [hry] at h
          rw [h]; simp
        have hsplit : ω x - ω y
            = - (Φ (Work.Cyl.reflZ x) - Φ (Work.Cyl.reflZ y)) := by rw [hwx, hwy]; abel
        rw [hsplit, norm_neg]
        calc ‖Φ (Work.Cyl.reflZ x) - Φ (Work.Cyl.reflZ y)‖
            ≤ (C : ℝ) * ‖Work.Cyl.reflZ x - Work.Cyl.reflZ y‖ ^ α := hΦb _ _
          _ ≤ (C : ℝ) * ‖x - y‖ ^ α := by
              apply mul_le_mul_of_nonneg_left _ hCnn
              apply Real.rpow_le_rpow (norm_nonneg _) _ hα.le
              rw [← dist_eq_norm, ← dist_eq_norm]
              exact Work.Cyl.dist_reflZ_le x y
          _ ≤ 3 * (C : ℝ) * ‖x - y‖ ^ α := by nlinarith
  refine Work.Stability.holderWith_of_dist_le (C := 3 * C) (r := ⟨α, hα.le⟩) ?_
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  have hco : ((3 * C : NNReal) : ℝ) = 3 * (C : ℝ) := by push_cast; ring
  rw [hco]
  exact key x y

/-! ## 3. The cylindrical coordinates under a positive dilation -/

lemma radial_smul_dev {c : ℝ} (hc : 0 ≤ c) (x : R3) :
    Work.Cyl.radial (c • x) = c * Work.Cyl.radial x := by
  rw [Work.Cyl.radial, Work.Cyl.radial,
    show Work.Cyl.radSq (c • x) = c ^ 2 * Work.Cyl.radSq x by
      simp only [Work.Cyl.radSq, PiLp.smul_apply, smul_eq_mul]; ring,
    Real.sqrt_mul (by positivity) (Work.Cyl.radSq x), Real.sqrt_sq_eq_abs, abs_of_nonneg hc]

lemma rho_smul_dev {c : ℝ} (hc : 0 ≤ c) (x : R3) :
    Work.Cyl.rho (c • x) = c * Work.Cyl.rho x := by
  rw [Work.Cyl.rho_eq_norm, Work.Cyl.rho_eq_norm, norm_smul, Real.norm_of_nonneg hc]

lemma angularVec_smul_dev (c : ℝ) (x : R3) :
    Work.Cyl.angularVec (c • x) = c • Work.Cyl.angularVec x := by
  ext i; fin_cases i <;> simp [Work.Cyl.angularVec]

lemma theta_smul_dev {c : ℝ} (hc : 0 < c) (x : R3) :
    Work.Cyl.theta (c • x) = Work.Cyl.theta x := by
  rw [Work.Cyl.theta, Work.Cyl.theta]
  congr 1
  rw [show Work.Cyl.axial (c • x) = c * Work.Cyl.axial x by
        simp only [Work.Cyl.axial, PiLp.smul_apply, smul_eq_mul], radial_smul_dev hc.le]
  field_simp

lemma eTheta_smul_dev {c : ℝ} (hc : 0 < c) (x : R3) :
    Work.Cyl.eTheta (c • x) = Work.Cyl.eTheta x := by
  rw [Work.Cyl.eTheta, Work.Cyl.eTheta, radial_smul_dev hc.le, angularVec_smul_dev, smul_smul]
  congr 1
  field_simp

/-! ## 4. The self-similar vorticity of a slice is `α`-Hölder, with an explicit constant -/

theorem omegaS_holder_dev {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) {g : ℝ → ℝ → ℝ}
    {Cv Lg Lθ K : ℝ} (hCv : 0 ≤ Cv) (hLg : 0 ≤ Lg) (hLθ : 0 ≤ Lθ) (hK : 0 ≤ K)
    (hvt : Work.Spaces.VanishTheta g)
    (hquad0 : ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ → g 0 θ = 0)
    (hvan : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |g z θ| ≤ Cv * Gamma α θ)
    (hzk : ∀ z z' θ : ℝ, 0 ≤ z → 0 ≤ z' → θ ∈ Work.Spaces.Iθ →
      |g z θ - g z' θ| ≤ Lg * |z - z'| ^ α)
    (hzth : ∀ z θ θ' : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
      |g z θ - g z θ'| ≤ Lθ * |θ - θ'| ^ α)
    (hKquad : ∀ z θ : ℝ, 0 ≤ z → z ≤ 2 → θ ∈ Work.Spaces.Iθ → |g z θ| ≤ K * z ^ 2)
    (hKz : ∀ z z' θ : ℝ, 0 ≤ z → z ≤ 2 → 0 ≤ z' → z' ≤ 2 → θ ∈ Work.Spaces.Iθ →
      |g z θ - g z' θ| ≤ K * max z z' * |z - z'|)
    (hKth : ∀ z θ θ' : ℝ, 0 ≤ z → z ≤ 2 → θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
      |g z θ - g z θ'| ≤ K * z * |θ - θ'|)
    (hlin : ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ → ∀ z : ℝ, 0 ≤ z → z ≤ 1 → |g z θ| ≤ K * z)
    {Cω : NNReal}
    (hCω : HolderWith Cω (⟨α, hα.le⟩ : NNReal) (Work.ConstructionInstance.omegaStar α)) :
    HolderWith (omegaSHolderConst α Cv Lg Lθ K Cω) (⟨α, hα.le⟩ : NNReal)
      (Work.ConstructionInstance.omegaS (3 * α) g) := by
  classical
  have hα1 : α ≤ 1 := by linarith
  have hθI : ∀ x : R3, |Work.Cyl.theta x| ∈ Work.Spaces.Iθ := by
    intro x
    refine ⟨abs_nonneg _, ?_⟩
    rw [abs_le]
    exact ⟨le_of_lt (Real.neg_pi_div_two_lt_arctan _), le_of_lt (Real.arctan_lt_pi_div_two _)⟩
  -- Extend the slice off the angular interval `Iθ`, so that the vanishing at `z = 0` holds for
  -- *all* angles: this is the form of the Taylor datum consumed by the composite estimate.
  -- On `Iθ` (where the composite is evaluated, since `|θ x| ∈ Iθ`) nothing changes.
  set G : ℝ → ℝ → ℝ := fun z θ => if θ ∈ Work.Spaces.Iθ then g z θ else 0 with hG
  have hG_eq : ∀ z θ : ℝ, θ ∈ Work.Spaces.Iθ → G z θ = g z θ := by
    intro z θ hθ
    rw [hG]
    exact ite_eq_left hθ
  have hquad0G : ∀ θ : ℝ, G 0 θ = 0 := by
    intro θ
    by_cases hθ : θ ∈ Work.Spaces.Iθ
    · rw [hG_eq 0 θ hθ]; exact hquad0 θ hθ
    · rw [hG]; exact ite_eq_right hθ
  have hvanG : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |G z θ| ≤ Cv * Gamma α θ :=
    fun z θ hz hθ => by rw [hG_eq z θ hθ]; exact hvan z θ hz hθ
  have hzkG : ∀ z z' θ : ℝ, 0 ≤ z → 0 ≤ z' → θ ∈ Work.Spaces.Iθ →
      |G z θ - G z' θ| ≤ Lg * |z - z'| ^ α :=
    fun z z' θ hz hz' hθ => by
      rw [hG_eq z θ hθ, hG_eq z' θ hθ]; exact hzk z z' θ hz hz' hθ
  have hzthG : ∀ z θ θ' : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
      |G z θ - G z θ'| ≤ Lθ * |θ - θ'| ^ α :=
    fun z θ θ' hz hθ hθ' => by
      rw [hG_eq z θ hθ, hG_eq z θ' hθ']; exact hzth z θ θ' hz hθ hθ'
  have hKquadG : ∀ z θ : ℝ, 0 ≤ z → z ≤ 2 → θ ∈ Work.Spaces.Iθ → |G z θ| ≤ K * z ^ 2 :=
    fun z θ hz hz2 hθ => by rw [hG_eq z θ hθ]; exact hKquad z θ hz hz2 hθ
  have hKzG : ∀ z z' θ : ℝ, 0 ≤ z → z ≤ 2 → 0 ≤ z' → z' ≤ 2 → θ ∈ Work.Spaces.Iθ →
      |G z θ - G z' θ| ≤ K * max z z' * |z - z'| :=
    fun z z' θ hz hz2 hz' hz'2 hθ => by
      rw [hG_eq z θ hθ, hG_eq z' θ hθ]; exact hKz z z' θ hz hz2 hz' hz'2 hθ
  have hKthG : ∀ z θ θ' : ℝ, 0 ≤ z → z ≤ 2 → θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
      |G z θ - G z θ'| ≤ K * z * |θ - θ'| :=
    fun z θ θ' hz hz2 hθ hθ' => by
      rw [hG_eq z θ hθ, hG_eq z θ' hθ']; exact hKth z θ θ' hz hz2 hθ hθ'
  have hvtG : Work.Spaces.VanishTheta G :=
    ⟨fun z => by rw [hG_eq z 0 Work.Spaces.zero_mem_Iθ]; exact hvt.1 z,
     fun z => by rw [hG_eq z (Real.pi / 2) Work.Spaces.pi_half_mem_Iθ]; exact hvt.2 z⟩
  set ĝ : R3 → ℝ := fun x => G (Work.Cyl.rho x ^ (3 * α)) (|Work.Cyl.theta x|) with hĝ
  have hĝ_holder : HolderWith (gCompConstNN α Cv Lg Lθ K) (⟨α, hα.le⟩ : NNReal) ĝ :=
    gCompHolderQuant hα hα13 hCv hLg hLθ hK hvtG hquad0G hvanG hzkG hzthG hKquadG hKzG hKthG
  have hĝ_abs : ∀ x : R3, |ĝ x| ≤ max K Cv * (Work.Cyl.radial x) ^ α := by
    intro x
    have hx : ĝ x = g (Work.Cyl.rho x ^ (3 * α)) (|Work.Cyl.theta x|) := by
      simp only [hĝ]
      exact hG_eq _ _ (hθI x)
    rw [hx]
    exact gComp_abs_le_quant hα hα13 hCv hK hvt hvan hlin x
  have hE : HolderWith (smulEThetaConst ((gCompConstNN α Cv Lg Lθ K : ℝ)) (max K Cv))
      (⟨α, hα.le⟩ : NNReal) (fun x : R3 => ĝ x • Work.Cyl.eTheta x) :=
    smulEThetaHolder hα hα1 (gCompConstNN α Cv Lg Lθ K).coe_nonneg
      (le_trans hCv (le_max_right K Cv)) hĝ_holder hĝ_abs
  have hS : HolderWith (Cω * ‖(3 * α / Work.Spaces.c (3 * α))‖₊) (⟨α, hα.le⟩ : NNReal)
      (fun x : R3 =>
        (3 * α / Work.Spaces.c (3 * α)) • Work.ConstructionInstance.omegaStar α x) :=
    HolderWith.smul (3 * α / Work.Spaces.c (3 * α)) hCω
  have hΦ : HolderWith (Cω * ‖(3 * α / Work.Spaces.c (3 * α))‖₊
        + smulEThetaConst ((gCompConstNN α Cv Lg Lθ K : ℝ)) (max K Cv))
      (⟨α, hα.le⟩ : NNReal)
      (fun x : R3 =>
        (3 * α / Work.Spaces.c (3 * α)) • Work.ConstructionInstance.omegaStar α x
          + ĝ x • Work.Cyl.eTheta x) :=
    HolderWith.add hS hE
  have hhalf : ∀ x : R3, 0 ≤ x 2 → Work.ConstructionInstance.omegaS (3 * α) g x
      = (3 * α / Work.Spaces.c (3 * α)) • Work.ConstructionInstance.omegaStar α x
        + ĝ x • Work.Cyl.eTheta x := by
    intro x hx
    have hθ : 0 ≤ Work.Cyl.theta x := Work.ConstructionInstance.theta_nonneg_of_axial_nonneg hx
    have hAom : Work.ConstructionInstance.Aom α x = Work.ConstructionInstance.A0 α x := by
      rw [Work.ConstructionInstance.Aom, Work.ConstructionInstance.cSign,
        ite_eq_left hx, one_mul]
    have hGF : Gamma α (Work.Cyl.theta x) * Work.FM.Fstar (Work.Cyl.rho x ^ (3 * α))
        = Work.ConstructionInstance.A0 α x := by
      rw [← hAom, Work.ConstructionInstance.Gamma_mul_Fstar_eq_Aom α hα x]
    have hF : Work.Construction.Fstar (3 * α) (Work.Cyl.rho x ^ (3 * α)) (Work.Cyl.theta x)
        = (3 * α / Work.Spaces.c (3 * α)) * Work.ConstructionInstance.A0 α x := by
      have hGam : Work.Spaces.Gam (3 * α) (Work.Cyl.theta x)
          = Work.ConstructionInstance.Gamma α (Work.Cyl.theta x) := by
        rw [Work.Spaces.Gam, Work.ConstructionInstance.Gamma,
          show (3 * α) / 3 = α by ring]
      rw [Work.Construction.Fstar, hGam]
      conv_rhs => rw [← hGF]
      ring
    have hĝx : ĝ x = g (Work.Cyl.rho x ^ (3 * α)) (Work.Cyl.theta x) := by
      simp only [hĝ]
      rw [hG_eq _ _ (hθI x), abs_of_nonneg hθ]
    rw [Work.ConstructionInstance.omegaS_apply', Work.ConstructionInstance.profile_of_nonneg hθ,
      hF, hĝx, Work.ConstructionInstance.omegaStar_apply,
      Work.ConstructionInstance.Gamma_mul_Fstar_eq_Aom α hα x, hAom, smul_smul, ← add_smul]
  have hplane : ∀ x : R3, x 2 = 0 →
      (3 * α / Work.Spaces.c (3 * α)) • Work.ConstructionInstance.omegaStar α x
        + ĝ x • Work.Cyl.eTheta x = 0 := by
    intro x hx
    have hθ0 : Work.Cyl.theta x = 0 := by
      rw [Work.Cyl.theta, Work.Cyl.axial, hx]; simp
    have hA0 : Work.ConstructionInstance.A0 α x = 0 := by
      simp [Work.ConstructionInstance.A0, hx, Real.zero_rpow (ne_of_gt hα)]
    have hAom : Work.ConstructionInstance.Aom α x = 0 := by
      rw [Work.ConstructionInstance.Aom, Work.ConstructionInstance.cSign,
        ite_eq_left (le_of_eq hx.symm), one_mul, hA0]
    have hĝ0 : ĝ x = 0 := by
      simp only [hĝ]
      rw [hG_eq _ _ (hθI x), hθ0, abs_zero]
      exact hvt.1 _
    rw [Work.ConstructionInstance.omegaStar_apply,
      Work.ConstructionInstance.Gamma_mul_Fstar_eq_Aom α hα x, hAom, hĝ0]
    simp
  have hodd : ∀ x : R3,
      Work.ConstructionInstance.omegaS (3 * α) g (Work.Cyl.reflZ x)
        = - Work.ConstructionInstance.omegaS (3 * α) g x := by
    intro x
    have hrho : Work.Cyl.rho (Work.Cyl.reflZ x) = Work.Cyl.rho x := by
      simp [Work.Cyl.rho, Work.Cyl.radSq, Work.Cyl.axial, Work.Cyl.reflZ]
    have hth : Work.Cyl.theta (Work.Cyl.reflZ x) = - Work.Cyl.theta x := by
      simp [Work.Cyl.theta, Work.Cyl.radial, Work.Cyl.radSq, Work.Cyl.axial, Work.Cyl.reflZ,
        neg_div, Real.arctan_neg]
    have he : Work.Cyl.eTheta (Work.Cyl.reflZ x) = Work.Cyl.eTheta x := by
      simp [Work.Cyl.eTheta, Work.Cyl.radial, Work.Cyl.radSq, Work.Cyl.angularVec,
        Work.Cyl.reflZ]
    rw [Work.ConstructionInstance.omegaS_apply', Work.ConstructionInstance.omegaS_apply',
      hrho, hth, he,
      Work.ConstructionInstance.profile_odd (by positivity : (3:ℝ) * α ≠ 0)
        (fun z => hvt.1 z), neg_smul]
  exact holder_of_half_odd_const hα hΦ hhalf hodd hplane

/-! ## 5. The target: the physical vorticity slices are `α`-Hölder, uniformly on `[0,S]` -/

theorem physVort_holder_slice {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : Work.FTS.Regularity.RegPkg α S A B g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ Set.Icc 0 S, ∀ x y : Work.FTS.Regularity.R3,
      ‖Work.FTS.Regularity.physVort α A B g x τ - Work.FTS.Regularity.physVort α A B g y τ‖
        ≤ C * ‖x - y‖ ^ α := by
  have hα : 0 < α := h.hα
  have hα13 : α ≤ 1 / 3 := h.hα13
  have hα1 : α ≤ 1 := by linarith
  obtain ⟨Cv, hCv0, hvan⟩ := h.hvan
  obtain ⟨Ng, hJet⟩ := h.hg
  have hLg : 0 ≤ Ng := hJet.1
  obtain ⟨K, hK0, htay⟩ := h.htay
  obtain ⟨a₀, a₁, ha₀, hab⟩ := h.hAb
  obtain ⟨b₀, b₁, hb₀, hbb⟩ := h.hBb
  obtain ⟨Cω, hCω⟩ := Work.ConstructionInstance.holder_omegaStar (β := α) hα hα1
  set CωS := omegaSHolderConst α Cv Ng Ng K Cω with hCωS
  have hslice : ∀ τ ∈ Set.Icc 0 S, HolderWith CωS (⟨α, hα.le⟩ : NNReal)
      (Work.ConstructionInstance.omegaS (3 * α) (gSlice g τ)) := by
    intro τ hτ
    exact omegaS_holder_dev hα hα13 hCv0 hLg hLg hK0 (h.hvt τ hτ)
      (fun θ hθ => h.hquad0 τ hτ θ hθ)
      (fun z θ hz hθ => hvan τ hτ z θ hz hθ)
      (fun z z' θ hz hz' hθ => hJet.zmod hz hz' hθ hτ)
      (fun z θ θ' hz hθ hθ' => hJet.thmod hz hθ hθ' hτ)
      (fun z θ hz hz2 hθ => (htay τ hτ θ hθ).1 z hz hz2)
      (fun z z' θ hz hz2 hz' hz'2 hθ => (htay τ hτ θ hθ).2.1 z z' hz hz2 hz' hz'2)
      (fun z θ θ' hz hz2 hθ hθ' => (htay τ hτ θ hθ).2.2 z hz hz2 θ' hθ')
      (fun θ hθ z hz hz1 => by
        have h1 := (htay τ hτ θ hθ).1 z hz (le_trans hz1 (by norm_num))
        have h2 : z ^ 2 ≤ z := by nlinarith
        exact le_trans h1 (mul_le_mul_of_nonneg_left h2 hK0))
      hCω
  set bmax : ℝ := (b₀⁻¹) ^ (1 / (3 * α)) with hbmax
  have hbmaxnn : 0 ≤ bmax := Real.rpow_nonneg (inv_nonneg.mpr hb₀.le) _
  refine ⟨a₀⁻¹ * (CωS : ℝ) * bmax ^ α, ?_, ?_⟩
  · have h1 : 0 ≤ a₀⁻¹ := inv_nonneg.mpr ha₀.le
    have h2 : 0 ≤ (CωS : ℝ) := CωS.coe_nonneg
    exact mul_nonneg (mul_nonneg h1 h2) (Real.rpow_nonneg hbmaxnn _)
  · intro τ hτ x y
    have hAτ : a₀ ≤ A τ := (hab τ hτ).1
    have hApos : 0 < A τ := lt_of_lt_of_le ha₀ hAτ
    have hBτ : b₀ ≤ B τ := (hbb τ hτ).1
    have hBpos : 0 < B τ := lt_of_lt_of_le hb₀ hBτ
    set b : ℝ := (B τ)⁻¹ ^ (1 / (3 * α)) with hb
    have hbpos : 0 < b := Real.rpow_pos_of_pos (inv_pos.mpr hBpos) _
    have hbp : b ^ (3 * α) = (B τ)⁻¹ := by
      rw [hb, ← Real.rpow_mul (inv_nonneg.mpr hBpos.le) (1 / (3 * α)) (3 * α),
        div_mul_cancel₀ 1 (by positivity : (3:ℝ) * α ≠ 0), Real.rpow_one]
    have hble : b ≤ bmax :=
      Real.rpow_le_rpow (inv_nonneg.mpr hBpos.le)
        ((inv_le_inv₀ hBpos hb₀).mpr hBτ) (by positivity)
    have hid : ∀ z : R3, Work.ConstructionInstance.omegaSz (3 * α) (gSlice g τ)
        (Work.Cyl.rho z ^ (3 * α) / B τ) z
        = Work.ConstructionInstance.omegaS (3 * α) (gSlice g τ) (b • z) := by
      intro z
      have hzb : Work.Cyl.rho (b • z) ^ (3 * α) = Work.Cyl.rho z ^ (3 * α) / B τ := by
        rw [rho_smul_dev hbpos.le z, Real.mul_rpow hbpos.le (Work.Cyl.rho_nonneg z), hbp,
          div_eq_mul_inv, mul_comm]
      rw [Work.ConstructionInstance.omegaS_apply', Work.ConstructionInstance.omegaSz_apply,
        theta_smul_dev hbpos z, eTheta_smul_dev hbpos z, hzb]
    have hH := (hslice τ hτ).dist_le (b • x) (b • y)
    rw [dist_eq_norm, dist_eq_norm] at hH
    have hH' : ‖Work.ConstructionInstance.omegaS (3 * α) (gSlice g τ) (b • x)
        - Work.ConstructionInstance.omegaS (3 * α) (gSlice g τ) (b • y)‖
        ≤ (CωS : ℝ) * ‖b • x - b • y‖ ^ α := hH
    have hbxy : ‖b • x - b • y‖ = b * ‖x - y‖ := by
      rw [← smul_sub, norm_smul, Real.norm_of_nonneg hbpos.le]
    rw [hbxy, Real.mul_rpow hbpos.le (norm_nonneg (x - y))] at hH'
    have hbα : b ^ α ≤ bmax ^ α := Real.rpow_le_rpow hbpos.le hble hα.le
    have hCt : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
    have hcore : (CωS : ℝ) * b ^ α * ‖x - y‖ ^ α ≤ (CωS : ℝ) * bmax ^ α * ‖x - y‖ ^ α := by
      have h1 : (CωS : ℝ) * b ^ α ≤ (CωS : ℝ) * bmax ^ α :=
        mul_le_mul_of_nonneg_left hbα CωS.coe_nonneg
      exact mul_le_mul_of_nonneg_right h1 hCt
    have hinv : (A τ)⁻¹ ≤ a₀⁻¹ := (inv_le_inv₀ hApos ha₀).mpr hAτ
    have hAi : 0 ≤ (A τ)⁻¹ := inv_nonneg.mpr hApos.le
    calc ‖Work.FTS.Regularity.physVort α A B g x τ
            - Work.FTS.Regularity.physVort α A B g y τ‖
        = ‖(A τ)⁻¹ • (Work.ConstructionInstance.omegaSz (3 * α) (gSlice g τ)
              (Work.Cyl.rho x ^ (3 * α) / B τ) x)
            - (A τ)⁻¹ • (Work.ConstructionInstance.omegaSz (3 * α) (gSlice g τ)
              (Work.Cyl.rho y ^ (3 * α) / B τ) y)‖ := by
            rw [Work.FTS.Regularity.physVort_apply, Work.FTS.Regularity.physVort_apply,
              Work.FTS.Regularity.pExp_eq]
      _ = ‖(A τ)⁻¹ • (Work.ConstructionInstance.omegaSz (3 * α) (gSlice g τ)
              (Work.Cyl.rho x ^ (3 * α) / B τ) x
            - Work.ConstructionInstance.omegaSz (3 * α) (gSlice g τ)
              (Work.Cyl.rho y ^ (3 * α) / B τ) y)‖ := by
            rw [smul_sub]
      _ = |(A τ)⁻¹| * ‖Work.ConstructionInstance.omegaSz (3 * α) (gSlice g τ)
              (Work.Cyl.rho x ^ (3 * α) / B τ) x
            - Work.ConstructionInstance.omegaSz (3 * α) (gSlice g τ)
              (Work.Cyl.rho y ^ (3 * α) / B τ) y‖ := by
            rw [norm_smul, Real.norm_eq_abs]
      _ = (A τ)⁻¹ * ‖Work.ConstructionInstance.omegaSz (3 * α) (gSlice g τ)
              (Work.Cyl.rho x ^ (3 * α) / B τ) x
            - Work.ConstructionInstance.omegaSz (3 * α) (gSlice g τ)
              (Work.Cyl.rho y ^ (3 * α) / B τ) y‖ := by
            rw [abs_of_nonneg hAi]
      _ = (A τ)⁻¹ * ‖Work.ConstructionInstance.omegaS (3 * α) (gSlice g τ) (b • x)
            - Work.ConstructionInstance.omegaS (3 * α) (gSlice g τ) (b • y)‖ := by
            rw [hid x, hid y]
      _ ≤ (A τ)⁻¹ * ((CωS : ℝ) * b ^ α * ‖x - y‖ ^ α) := by
            apply mul_le_mul_of_nonneg_left _ hAi
            calc ‖Work.ConstructionInstance.omegaS (3 * α) (gSlice g τ) (b • x)
                  - Work.ConstructionInstance.omegaS (3 * α) (gSlice g τ) (b • y)‖
                ≤ (CωS : ℝ) * (b ^ α * ‖x - y‖ ^ α) := hH'
              _ = (CωS : ℝ) * b ^ α * ‖x - y‖ ^ α := by ring
      _ ≤ a₀⁻¹ * ((CωS : ℝ) * bmax ^ α * ‖x - y‖ ^ α) := by
            have hc0 : 0 ≤ (CωS : ℝ) * b ^ α * ‖x - y‖ ^ α :=
              mul_nonneg (mul_nonneg CωS.coe_nonneg (Real.rpow_nonneg hbpos.le _)) hCt
            exact mul_le_mul hinv hcore hc0 (inv_nonneg.mpr ha₀.le)
      _ = a₀⁻¹ * (CωS : ℝ) * bmax ^ α * ‖x - y‖ ^ α := by ring

end Work.FTS.Regularity
