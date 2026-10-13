/-
# `Work.FTS.RegPkgGal.Consumer` — the composite Hölder transfer for the corrected clause

This is design item 10's "re-prove the consumer `ConstructionInstance.holder_gComp` / `gCompConst`"
for the corrected package `RegPkg'`: the composite `x ↦ g (ρ(x)^{3α}) (|θ(x)|)` is `α`-Hölder on
`ℝ³`, with the *corrected* constant `gCompConst'` of `Defs.lean`.

The delivered proof is `Work.FTS.Regularity.gCompHolderQuant` (and its non-quantitative sibling
`gCompHolder`, and the original `Work.ConstructionInstance.holder_gComp`); it is the same argument
with **one** change: the Taylor angular datum at `z = 0` enters through

  `|g z θ - g z θ'| ≤ K·z²·|θ - θ'|^α`   (corrected clause, design correction 5)

instead of the *false* Lipschitz bound `≤ K·z·|θ - θ'|`.  Only the near-origin, close-together
branch of the proof changes: the two gradient steps

  `K·z·|Δψ|  ≤ K·(3 minρ/2)^{3α}·(4π d/minρ)`   (delivered)
  `K·z²·|Δψ|^α ≤ K·(3 minρ/2)^{6α}·(4π d/minρ)^α ≤ K·(3/2)^{6α}(4π)^α·d^α`   (corrected)

(the last step uses `minρ < 1`, so `minρ^{5α} ≤ 1`), which is exactly why the last summand of
`gCompConst` becomes `K·(3/2)^{6α}·(4π)^α`.  Everything else — the far-field split, the
`Γ`-vanishing bound, the radial Lipschitz datum, the `minρ ≥ 1` branch — is unchanged, and the
proof text is otherwise that of `gCompHolderQuant`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.FTS.RegPkgGal.Defs
import Submission.Work.FTS.RegPkgGal.Basic
import Submission.Work.ConstructionInstance.holder_gComp
import Submission.Work.ConstructionInstance.g_psi_eq
import Submission.Work.ConstructionInstance.psi_sub_le
import Submission.Work.ConstructionInstance.A0_rho_pow_diff
import Submission.Work.Stability.holderWith_of_dist_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open Set Metric
open scoped Topology

namespace Work.FTS.RegPkgGal

open Work.FTS.Regularity

set_option autoImplicit false
theorem gCompHolderQuant' {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) {g : ℝ → ℝ → ℝ}
    {Cv Lg Lθ K : ℝ} (hCv : 0 ≤ Cv) (hLg : 0 ≤ Lg) (hLθ : 0 ≤ Lθ) (hK : 0 ≤ K)
    (hvt : Work.Spaces.VanishTheta g)
    (hquad0 : ∀ θ : ℝ, g 0 θ = 0)
    (hvan : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |g z θ| ≤ Cv * Work.ConstructionInstance.Gamma α θ)
    (hzk : ∀ z z' θ : ℝ, 0 ≤ z → 0 ≤ z' → θ ∈ Work.Spaces.Iθ →
      |g z θ - g z' θ| ≤ Lg * |z - z'| ^ α)
    (hzth : ∀ z θ θ' : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
      |g z θ - g z θ'| ≤ Lθ * |θ - θ'| ^ α)
    (hKquad : ∀ z θ : ℝ, 0 ≤ z → z ≤ 2 → θ ∈ Work.Spaces.Iθ → |g z θ| ≤ K * z ^ 2)
    (hKz : ∀ z z' θ : ℝ, 0 ≤ z → z ≤ 2 → 0 ≤ z' → z' ≤ 2 → θ ∈ Work.Spaces.Iθ →
      |g z θ - g z' θ| ≤ K * max z z' * |z - z'|)
    (hKth : ∀ z θ θ' : ℝ, 0 ≤ z → z ≤ 2 → θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
      |g z θ - g z θ'| ≤ K * z ^ 2 * |θ - θ'| ^ α) :
    HolderWith (gCompConstNN' α Cv Lg Lθ K) (⟨α, hα.le⟩ : NNReal)
      (fun x : Work.FTS.Regularity.R3 =>
        g (Work.Cyl.rho x ^ (3 * α)) (|Work.Cyl.theta x|)) := by
  have h3α : 0 < 3 * α := by linarith
  have h3α1 : 3 * α ≤ 1 := by linarith
  have hvan' : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |g z θ| ≤ Cv * Work.ConstructionInstance.Gamma α θ := hvan
  have hK0 : 0 ≤ K := hK
  have hslicez : ∀ z z' θ : ℝ, 0 ≤ z → z ≤ 2 → 0 ≤ z' → z' ≤ 2 → θ ∈ Work.Spaces.Iθ →
        |g z θ - g z' θ| ≤ K * max z z' * |z - z'| := hKz
  -- the two global bounds of the composite
  have hsup : ∀ z : R3, |g (Work.Cyl.rho z ^ (3 * α)) (Work.ConstructionInstance.psi z)| ≤ Cv := by
    intro z
    have hθ := Work.ConstructionInstance.psi_mem_Iθ z
    have h1 := hvan' (Work.Cyl.rho z ^ (3 * α)) (Work.ConstructionInstance.psi z)
      (Real.rpow_nonneg (Work.Cyl.rho_nonneg z) _) hθ
    have h2 : Work.ConstructionInstance.Gamma α (Work.ConstructionInstance.psi z) ≤ 1 := Work.ConstructionInstance.Gamma_le_one hα.le hθ
    have h3 : 0 ≤ Work.ConstructionInstance.Gamma α (Work.ConstructionInstance.psi z) := Work.ConstructionInstance.Gamma_nonneg hθ
    nlinarith [hCv]
  have hquadbound : ∀ z : R3, Work.Cyl.rho z ≤ 2 →
      |g (Work.Cyl.rho z ^ (3 * α)) (Work.ConstructionInstance.psi z)| ≤ K * (Work.Cyl.rho z) ^ (6 * α) := by
    intro z hz
    have hρ0 := Work.Cyl.rho_nonneg z
    have hZ0 : 0 ≤ Work.Cyl.rho z ^ (3 * α) := Real.rpow_nonneg hρ0 _
    have hZ2 : Work.Cyl.rho z ^ (3 * α) ≤ 2 := by
      calc Work.Cyl.rho z ^ (3 * α) ≤ 2 ^ (3 * α) := Real.rpow_le_rpow hρ0 hz h3α.le
        _ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h3α1
        _ = 2 := Real.rpow_one 2
    have h1 := hKquad _ _ hZ0 hZ2 (Work.ConstructionInstance.psi_mem_Iθ z)
    have h2 : (Work.Cyl.rho z ^ (3 * α)) ^ 2 = (Work.Cyl.rho z) ^ (6 * α) := by
      rw [← Real.rpow_natCast (Work.Cyl.rho z ^ (3 * α)) 2, ← Real.rpow_mul hρ0]
      congr 1
      ring
    calc |g (Work.Cyl.rho z ^ (3 * α)) (Work.ConstructionInstance.psi z)|
        ≤ K * (Work.Cyl.rho z ^ (3 * α)) ^ 2 := h1
      _ = K * (Work.Cyl.rho z) ^ (6 * α) := by rw [h2]
  -- the Hölder constant
  set C : ℝ := 2 * Cv + (2 * Cv * (3/2) ^ α
      + (2 * K * 3 ^ (6 * α) + ((Lg * (3 * α) ^ α + Lθ * (4 * Real.pi) ^ α)
      + (K * (3/2) * 3 ^ α * (3/2) ^ (2 * α)
      + K * (3/2) ^ (6 * α) * (4 * Real.pi) ^ α)))) with hCdef
  have hCnn : 0 ≤ C := by rw [hCdef]; positivity
  have hC1 : 2 * Cv ≤ C := by
    rw [hCdef]
    linarith [show (0:ℝ) ≤ 2 * Cv * (3/2) ^ α
      + (2 * K * 3 ^ (6 * α) + ((Lg * (3 * α) ^ α + Lθ * (4 * Real.pi) ^ α)
      + (K * (3/2) * 3 ^ α * (3/2) ^ (2 * α)
      + K * (3/2) ^ (6 * α) * (4 * Real.pi) ^ α))) by positivity]
  have hC2 : 2 * Cv * (3/2) ^ α ≤ C := by
    rw [hCdef]
    linarith [show (0:ℝ) ≤ 2 * Cv
      + (2 * K * 3 ^ (6 * α) + ((Lg * (3 * α) ^ α + Lθ * (4 * Real.pi) ^ α)
      + (K * (3/2) * 3 ^ α * (3/2) ^ (2 * α)
      + K * (3/2) ^ (6 * α) * (4 * Real.pi) ^ α))) by positivity]
  have hC3 : 2 * K * 3 ^ (6 * α) ≤ C := by
    rw [hCdef]
    linarith [show (0:ℝ) ≤ 2 * Cv
      + (2 * Cv * (3/2) ^ α + ((Lg * (3 * α) ^ α + Lθ * (4 * Real.pi) ^ α)
      + (K * (3/2) * 3 ^ α * (3/2) ^ (2 * α)
      + K * (3/2) ^ (6 * α) * (4 * Real.pi) ^ α))) by positivity]
  have hC4 : Lg * (3 * α) ^ α + Lθ * (4 * Real.pi) ^ α ≤ C := by
    rw [hCdef]
    linarith [show (0:ℝ) ≤ 2 * Cv + (2 * Cv * (3/2) ^ α + (2 * K * 3 ^ (6 * α)
      + (K * (3/2) * 3 ^ α * (3/2) ^ (2 * α)
      + K * (3/2) ^ (6 * α) * (4 * Real.pi) ^ α))) by positivity]
  have hC5 : K * (3/2) * 3 ^ α * (3/2) ^ (2 * α) ≤ C := by
    rw [hCdef]
    linarith [show (0:ℝ) ≤ 2 * Cv + (2 * Cv * (3/2) ^ α + (2 * K * 3 ^ (6 * α)
      + ((Lg * (3 * α) ^ α + Lθ * (4 * Real.pi) ^ α)
      + K * (3/2) ^ (6 * α) * (4 * Real.pi) ^ α))) by positivity]
  have hC6 : K * (3/2) ^ (6 * α) * (4 * Real.pi) ^ α ≤ C := by
    rw [hCdef]
    linarith [show (0:ℝ) ≤ 2 * Cv + (2 * Cv * (3/2) ^ α + (2 * K * 3 ^ (6 * α)
      + ((Lg * (3 * α) ^ α + Lθ * (4 * Real.pi) ^ α)
      + K * (3/2) * 3 ^ α * (3/2) ^ (2 * α)))) by positivity]
  have hC56 : K * (3/2) ^ (6 * α) * (4 * Real.pi) ^ α
      + K * (3/2) * 3 ^ α * (3/2) ^ (2 * α) ≤ C := by
    rw [hCdef]
    linarith [show (0:ℝ) ≤ 2 * Cv + (2 * Cv * (3/2) ^ α + (2 * K * 3 ^ (6 * α)
      + (Lg * (3 * α) ^ α + Lθ * (4 * Real.pi) ^ α))) by positivity]
  have hCco : C = gCompConst' α Cv Lg Lθ K := by
    simp only [gCompConst']
    rw [hCdef]
  have hCg : 0 ≤ gCompConst' α Cv Lg Lθ K := hCco ▸ hCnn
  have hCnne : gCompConstNN' α Cv Lg Lθ K = (⟨C, hCnn⟩ : NNReal) := by
    apply Subtype.ext
    simp only [gCompConstNN']
    rw [abs_of_nonneg hCg]
    exact hCco.symm
  rw [hCnne]
  refine Work.Stability.holderWith_of_dist_le (fun x y => ?_)
  rw [Real.dist_eq, Work.ConstructionInstance.g_psi_eq hquad0 hvt x, Work.ConstructionInstance.g_psi_eq hquad0 hvt y]
  show |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x) - g (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y)|
      ≤ C * dist x y ^ α
  by_cases hxy : x = y
  · subst hxy
    simp only [dist_self, sub_self, abs_zero]
    positivity
  have hdpos : 0 < dist x y := dist_pos.mpr hxy
  have hdnn : 0 ≤ dist x y := dist_nonneg
  have htri : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := Work.ConstructionInstance.abs_sub_le_abs_add
  rcases le_or_gt 1 (dist x y) with hd1 | hd1
  · -- far away (or exactly at distance one): the sup bound suffices
    have h1 : (1 : ℝ) ≤ dist x y ^ α := Real.one_le_rpow hd1 hα.le
    calc |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x) - g (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y)|
        ≤ |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x)|
          + |g (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y)| := htri _ _
      _ ≤ 2 * Cv := by linarith [hsup x, hsup y]
      _ ≤ C * dist x y ^ α := by
          calc 2 * Cv ≤ C := hC1
            _ = C * 1 := by ring
            _ ≤ C * dist x y ^ α := by
                simpa using mul_le_mul_of_nonneg_left h1 hCnn
  · rcases le_or_gt (min (Work.Cyl.rho x) (Work.Cyl.rho y)) (2 * dist x y) with hfar | hnear
    · -- the radii are not large compared with `d`: use the two pointwise bounds
      have hmax3 : max (Work.Cyl.rho x) (Work.Cyl.rho y) ≤ 3 * dist x y := by
        have := Work.ConstructionInstance.max_rho_le_min_rho_add_dist x y
        linarith
      by_cases hsmall : max (Work.Cyl.rho x) (Work.Cyl.rho y) ≤ 2
      · -- both radii at most two: the quadratic vanishing of `g` at `z = 0`
        have hρx2 : Work.Cyl.rho x ≤ 2 := le_trans (le_max_left _ _) hsmall
        have hρy2 : Work.Cyl.rho y ≤ 2 := le_trans (le_max_right _ _) hsmall
        have hρx3 : Work.Cyl.rho x ≤ 3 * dist x y := le_trans (le_max_left _ _) hmax3
        have hρy3 : Work.Cyl.rho y ≤ 3 * dist x y := le_trans (le_max_right _ _) hmax3
        have hpow : dist x y ^ (6 * α) ≤ dist x y ^ α :=
          Real.rpow_le_rpow_of_exponent_ge hdpos (le_of_lt hd1) (by linarith)
        calc |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x) - g (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y)|
            ≤ |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x)|
              + |g (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y)| := htri _ _
          _ ≤ K * (Work.Cyl.rho x) ^ (6 * α) + K * (Work.Cyl.rho y) ^ (6 * α) :=
              add_le_add (hquadbound x hρx2) (hquadbound y hρy2)
          _ ≤ K * (3 * dist x y) ^ (6 * α) + K * (3 * dist x y) ^ (6 * α) := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left
                  (Real.rpow_le_rpow (Work.Cyl.rho_nonneg x) hρx3 (by linarith)) hK0
              · exact mul_le_mul_of_nonneg_left
                  (Real.rpow_le_rpow (Work.Cyl.rho_nonneg y) hρy3 (by linarith)) hK0
          _ = 2 * K * 3 ^ (6 * α) * dist x y ^ (6 * α) := by
              rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) hdnn]; ring
          _ ≤ 2 * K * 3 ^ (6 * α) * dist x y ^ α :=
              mul_le_mul_of_nonneg_left hpow (by positivity)
          _ ≤ C * dist x y ^ α := by
              exact mul_le_mul_of_nonneg_right hC3 (Real.rpow_nonneg hdnn α)
      · -- both radii large: then `d > 2/3` and the sup bound suffices
        have hd23 : 2 / 3 ≤ dist x y := by
          have := Work.ConstructionInstance.max_rho_le_min_rho_add_dist x y
          linarith [not_le.mp hsmall, hfar]
        have h1 : (1 : ℝ) ≤ (3 / 2) ^ α * dist x y ^ α := by
          have h2 : (3 / 2 : ℝ) ^ α * (2 / 3) ^ α = 1 := by
            rw [← Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3 / 2) (by norm_num : (0:ℝ) ≤ 2 / 3),
              show (3:ℝ)/2 * (2/3) = 1 by ring, Real.one_rpow]
          have h3 : (2 / 3 : ℝ) ^ α ≤ dist x y ^ α :=
            Real.rpow_le_rpow (by norm_num) hd23 hα.le
          have h4 : 0 ≤ (3 / 2 : ℝ) ^ α := Real.rpow_nonneg (by norm_num) _
          calc (1 : ℝ) = (3 / 2 : ℝ) ^ α * (2 / 3) ^ α := h2.symm
            _ ≤ (3 / 2 : ℝ) ^ α * dist x y ^ α := mul_le_mul_of_nonneg_left h3 h4
        calc |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x) - g (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y)|
            ≤ |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x)|
              + |g (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y)| := htri _ _
          _ ≤ 2 * Cv := by linarith [hsup x, hsup y]
          _ = 2 * Cv * 1 := by ring
          _ ≤ 2 * Cv * ((3 / 2) ^ α * dist x y ^ α) :=
              mul_le_mul_of_nonneg_left h1 (by linarith)
          _ = 2 * Cv * (3 / 2) ^ α * dist x y ^ α := by ring
          _ ≤ C * dist x y ^ α := by
              exact mul_le_mul_of_nonneg_right hC2 (Real.rpow_nonneg hdnn α)
    · -- close together and away from the origin
      have hρmin2d : 2 * dist x y < min (Work.Cyl.rho x) (Work.Cyl.rho y) := hnear
      have hρminpos : 0 < min (Work.Cyl.rho x) (Work.Cyl.rho y) :=
        lt_of_lt_of_le (by linarith [dist_nonneg (x := x) (y := y)]) (le_of_lt hρmin2d)
      have hminx : min (Work.Cyl.rho x) (Work.Cyl.rho y) ≤ Work.Cyl.rho x := min_le_left _ _
      have hminy : min (Work.Cyl.rho x) (Work.Cyl.rho y) ≤ Work.Cyl.rho y := min_le_right _ _
      have hρxmax : Work.Cyl.rho x ≤ max (Work.Cyl.rho x) (Work.Cyl.rho y) := le_max_left _ _
      have hρymax : Work.Cyl.rho y ≤ max (Work.Cyl.rho x) (Work.Cyl.rho y) := le_max_right _ _
      have hmax32 : max (Work.Cyl.rho x) (Work.Cyl.rho y)
          ≤ 3 * min (Work.Cyl.rho x) (Work.Cyl.rho y) / 2 := by
        have := Work.ConstructionInstance.max_rho_le_min_rho_add_dist x y
        linarith
      have hpsi : |Work.ConstructionInstance.psi x - Work.ConstructionInstance.psi y|
          ≤ 4 * Real.pi * dist x y / min (Work.Cyl.rho x) (Work.Cyl.rho y) :=
        Work.ConstructionInstance.psi_sub_le x y hρminpos hminx hminy
      have hpsi_nn : 0 ≤ |Work.ConstructionInstance.psi x - Work.ConstructionInstance.psi y| := abs_nonneg _
      have hZx0 : 0 ≤ Work.Cyl.rho x ^ (3 * α) := Real.rpow_nonneg (Work.Cyl.rho_nonneg x) _
      have hZy0 : 0 ≤ Work.Cyl.rho y ^ (3 * α) := Real.rpow_nonneg (Work.Cyl.rho_nonneg y) _
      have hsplit : |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x)
            - g (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y)|
          ≤ |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x) - g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi y)|
            + |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi y)
                - g (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y)| := by
        have := abs_add_le
          (g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x) - g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi y))
          (g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi y) - g (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y))
        rwa [show g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x)
              - g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi y)
            + (g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi y) - g (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y))
            = g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x)
              - g (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y) from by ring] at this
      by_cases hB1 : 1 ≤ min (Work.Cyl.rho x) (Work.Cyl.rho y)
      · -- both points at radius at least one: `hzk`/`hzth` and the Lipschitz bound for `Work.ConstructionInstance.psi`
        have hρx1 : 1 ≤ Work.Cyl.rho x := le_trans hB1 hminx
        have hρy1 : 1 ≤ Work.Cyl.rho y := le_trans hB1 hminy
        have hZd : |Work.Cyl.rho x ^ (3 * α) - Work.Cyl.rho y ^ (3 * α)| ≤ 3 * α * dist x y := by
          calc |Work.Cyl.rho x ^ (3 * α) - Work.Cyl.rho y ^ (3 * α)|
              ≤ 3 * α * |Work.Cyl.rho x - Work.Cyl.rho y| :=
                Work.ConstructionInstance.abs_rpow_sub_le_mul_of_one_le h3α h3α1 hρx1 hρy1
            _ ≤ 3 * α * dist x y :=
                mul_le_mul_of_nonneg_left (Work.ConstructionInstance.abs_rho_sub_rho_le_dist x y) h3α.le
        have hdψ : |Work.ConstructionInstance.psi x - Work.ConstructionInstance.psi y| ≤ 4 * Real.pi * dist x y := by
          rw [le_div_iff₀ hρminpos] at hpsi
          have h1 : |Work.ConstructionInstance.psi x - Work.ConstructionInstance.psi y|
              ≤ |Work.ConstructionInstance.psi x - Work.ConstructionInstance.psi y| * min (Work.Cyl.rho x) (Work.Cyl.rho y) :=
            le_mul_of_one_le_right (abs_nonneg _) hB1
          linarith
        calc |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x) - g (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y)|
            ≤ |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x) - g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi y)|
              + |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi y)
                  - g (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y)| := hsplit
          _ ≤ Lθ * |Work.ConstructionInstance.psi x - Work.ConstructionInstance.psi y| ^ α + Lg * |Work.Cyl.rho x ^ (3 * α)
                - Work.Cyl.rho y ^ (3 * α)| ^ α :=
              add_le_add (hzth _ _ _ hZx0 (Work.ConstructionInstance.psi_mem_Iθ x) (Work.ConstructionInstance.psi_mem_Iθ y))
                (hzk _ _ _ hZx0 hZy0 (Work.ConstructionInstance.psi_mem_Iθ y))
          _ ≤ Lθ * (4 * Real.pi * dist x y) ^ α + Lg * (3 * α * dist x y) ^ α := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left
                  (Real.rpow_le_rpow hpsi_nn hdψ hα.le) hLθ
              · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) hZd hα.le) hLg
          _ = (Lg * (3 * α) ^ α + Lθ * (4 * Real.pi) ^ α) * dist x y ^ α := by
              rw [Real.mul_rpow (by positivity : (0:ℝ) ≤ 4 * Real.pi) hdnn,
                Real.mul_rpow (by linarith : (0:ℝ) ≤ 3 * α) hdnn]
              ring
          _ ≤ C * dist x y ^ α := by
              exact mul_le_mul_of_nonneg_right hC4 (Real.rpow_nonneg hdnn α)
      · -- both points at radius below one: the slice bounds of the Taylor expansion
        have hρmin1 : min (Work.Cyl.rho x) (Work.Cyl.rho y) < 1 := lt_of_not_ge hB1
        have hmax2 : max (Work.Cyl.rho x) (Work.Cyl.rho y) ≤ 2 := by linarith
        have hρx32 : Work.Cyl.rho x ≤ 3 / 2 := by
          have := le_trans hρxmax hmax32
          linarith
        have hρy32 : Work.Cyl.rho y ≤ 3 / 2 := by
          have := le_trans hρymax hmax32
          linarith
        have hZx2 : Work.Cyl.rho x ^ (3 * α) ≤ 2 := by
          calc Work.Cyl.rho x ^ (3 * α) ≤ (2 : ℝ) ^ (3 * α) :=
                Real.rpow_le_rpow (Work.Cyl.rho_nonneg x) (le_trans hρxmax hmax2) h3α.le
            _ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h3α1
            _ = 2 := Real.rpow_one 2
        have hZy2 : Work.Cyl.rho y ^ (3 * α) ≤ 2 := by
          calc Work.Cyl.rho y ^ (3 * α) ≤ (2 : ℝ) ^ (3 * α) :=
                Real.rpow_le_rpow (Work.Cyl.rho_nonneg y) (le_trans hρymax hmax2) h3α.le
            _ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h3α1
            _ = 2 := Real.rpow_one 2
        have hZx32 : Work.Cyl.rho x ^ (3 * α) ≤ 3 / 2 := by
          calc Work.Cyl.rho x ^ (3 * α) ≤ (3 / 2 : ℝ) ^ (3 * α) :=
                Real.rpow_le_rpow (Work.Cyl.rho_nonneg x) hρx32 h3α.le
            _ ≤ (3 / 2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h3α1
            _ = 3 / 2 := Real.rpow_one (3 / 2)
        have hZy32 : Work.Cyl.rho y ^ (3 * α) ≤ 3 / 2 := by
          calc Work.Cyl.rho y ^ (3 * α) ≤ (3 / 2 : ℝ) ^ (3 * α) :=
                Real.rpow_le_rpow (Work.Cyl.rho_nonneg y) hρy32 h3α.le
            _ ≤ (3 / 2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h3α1
            _ = 3 / 2 := Real.rpow_one (3 / 2)
        have hmaxZ : max (Work.Cyl.rho x ^ (3 * α)) (Work.Cyl.rho y ^ (3 * α)) ≤ 3 / 2 :=
          max_le hZx32 hZy32
        have hZxle : Work.Cyl.rho x ^ (3 * α)
            ≤ (3 * min (Work.Cyl.rho x) (Work.Cyl.rho y) / 2) ^ (3 * α) :=
          Real.rpow_le_rpow (Work.Cyl.rho_nonneg x) (le_trans hρxmax hmax32) h3α.le
        have hZd : |Work.Cyl.rho x ^ (3 * α) - Work.Cyl.rho y ^ (3 * α)|
            ≤ 3 ^ α * (3 / 2) ^ (2 * α) * dist x y ^ α :=
          Work.ConstructionInstance.A0_rho_pow_diff (β := α) hα (le_trans hα13 (by norm_num)) (Work.Cyl.rho_nonneg x)
            (Work.Cyl.rho_nonneg y) hρx32 hρy32 (Work.ConstructionInstance.abs_rho_sub_rho_le_dist x y)
        have hzslice := hslicez (Work.Cyl.rho x ^ (3 * α)) (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y)
          hZx0 hZx2 hZy0 hZy2 (Work.ConstructionInstance.psi_mem_Iθ y)
        have hθslice : |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x)
              - g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi y)|
            ≤ K * (Work.Cyl.rho x ^ (3 * α)) ^ 2
              * |Work.ConstructionInstance.psi x - Work.ConstructionInstance.psi y| ^ α :=
          hKth _ _ _ hZx0 hZx2 (Work.ConstructionInstance.psi_mem_Iθ x)
            (Work.ConstructionInstance.psi_mem_Iθ y)
        -- the corrected first gradient step: `z²` instead of `z`, and the α-power on `|Δψ|`
        have hsqu : (Work.Cyl.rho x ^ (3 * α)) ^ 2 = (Work.Cyl.rho x) ^ (6 * α) := by
          rw [← Real.rpow_natCast (Work.Cyl.rho x ^ (3 * α)) 2,
            ← Real.rpow_mul (Work.Cyl.rho_nonneg x)]
          congr 1
          ring
        have hstep1 : K * (Work.Cyl.rho x ^ (3 * α)) ^ 2
              * |Work.ConstructionInstance.psi x - Work.ConstructionInstance.psi y| ^ α
            ≤ K * ((3 * min (Work.Cyl.rho x) (Work.Cyl.rho y) / 2) ^ (6 * α)
              * (4 * Real.pi * dist x y / min (Work.Cyl.rho x) (Work.Cyl.rho y)) ^ α) := by
          have h1 : (Work.Cyl.rho x ^ (3 * α)) ^ 2
              ≤ (3 * min (Work.Cyl.rho x) (Work.Cyl.rho y) / 2) ^ (6 * α) := by
            rw [hsqu]
            exact Real.rpow_le_rpow (Work.Cyl.rho_nonneg x) (le_trans hρxmax hmax32)
              (by linarith : (0 : ℝ) ≤ 6 * α)
          have h2 : |Work.ConstructionInstance.psi x - Work.ConstructionInstance.psi y| ^ α
              ≤ (4 * Real.pi * dist x y / min (Work.Cyl.rho x) (Work.Cyl.rho y)) ^ α :=
            Real.rpow_le_rpow hpsi_nn hpsi hα.le
          calc K * (Work.Cyl.rho x ^ (3 * α)) ^ 2
                * |Work.ConstructionInstance.psi x - Work.ConstructionInstance.psi y| ^ α
              = K * ((Work.Cyl.rho x ^ (3 * α)) ^ 2
                * |Work.ConstructionInstance.psi x - Work.ConstructionInstance.psi y| ^ α) := by
                ring
            _ ≤ K * ((3 * min (Work.Cyl.rho x) (Work.Cyl.rho y) / 2) ^ (6 * α)
                * (4 * Real.pi * dist x y / min (Work.Cyl.rho x) (Work.Cyl.rho y)) ^ α) := by
                apply mul_le_mul_of_nonneg_left _ hK0
                exact mul_le_mul h1 h2 (Real.rpow_nonneg hpsi_nn _)
                  (Real.rpow_nonneg (by positivity) _)
        have hstep2 : K * max (Work.Cyl.rho x ^ (3 * α)) (Work.Cyl.rho y ^ (3 * α))
              * |Work.Cyl.rho x ^ (3 * α) - Work.Cyl.rho y ^ (3 * α)|
            ≤ K * ((3 / 2) * (3 ^ α * (3 / 2) ^ (2 * α) * dist x y ^ α)) := by
          have h1 : K * max (Work.Cyl.rho x ^ (3 * α)) (Work.Cyl.rho y ^ (3 * α))
              ≤ K * (3 / 2) := mul_le_mul_of_nonneg_left hmaxZ hK0
          calc K * max (Work.Cyl.rho x ^ (3 * α)) (Work.Cyl.rho y ^ (3 * α))
                * |Work.Cyl.rho x ^ (3 * α) - Work.Cyl.rho y ^ (3 * α)|
              ≤ K * (3 / 2) * |Work.Cyl.rho x ^ (3 * α) - Work.Cyl.rho y ^ (3 * α)| :=
                mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
            _ = K * ((3 / 2) * |Work.Cyl.rho x ^ (3 * α) - Work.Cyl.rho y ^ (3 * α)|) := by ring
            _ ≤ K * ((3 / 2) * (3 ^ α * (3 / 2) ^ (2 * α) * dist x y ^ α)) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ K)
                exact mul_le_mul_of_nonneg_left hZd (by positivity)
        have hstep1' : (3 * min (Work.Cyl.rho x) (Work.Cyl.rho y) / 2) ^ (6 * α)
              * (4 * Real.pi * dist x y / min (Work.Cyl.rho x) (Work.Cyl.rho y)) ^ α
            ≤ (3 / 2) ^ (6 * α) * (4 * Real.pi) ^ α * dist x y ^ α := by
          set m : ℝ := min (Work.Cyl.rho x) (Work.Cyl.rho y) with hm
          have hm0 : 0 < m := hρminpos
          have hm1 : m ≤ 1 := le_of_lt hρmin1
          have e1 : (3 * m / 2) ^ (6 * α) = (3 / 2) ^ (6 * α) * m ^ (6 * α) := by
            rw [show 3 * m / 2 = 3 / 2 * m by ring_nf,
              Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3 / 2) hm0.le]
          have e2 : (4 * Real.pi * dist x y / m) ^ α
              = (4 * Real.pi) ^ α * dist x y ^ α * m ^ (-α) := by
            rw [show 4 * Real.pi * dist x y / m = 4 * Real.pi * dist x y * m⁻¹ by rw [div_eq_mul_inv],
              Real.mul_rpow (by positivity : (0:ℝ) ≤ 4 * Real.pi * dist x y)
                (inv_nonneg.mpr hm0.le),
              Real.mul_rpow (by positivity : (0:ℝ) ≤ 4 * Real.pi) hdnn,
              Real.inv_rpow hm0.le]
            rw [Real.rpow_neg hm0.le]
          have e3 : m ^ (6 * α) * m ^ (-α) = m ^ (5 * α) := by
            rw [← Real.rpow_add hm0]
            congr 1
            ring
          have e4 : m ^ (5 * α) ≤ 1 := Real.rpow_le_one hm0.le hm1 (by linarith)
          rw [e1, e2]
          calc (3 / 2) ^ (6 * α) * m ^ (6 * α)
                * ((4 * Real.pi) ^ α * dist x y ^ α * m ^ (-α))
              = (3 / 2) ^ (6 * α) * ((4 * Real.pi) ^ α * dist x y ^ α
                  * (m ^ (6 * α) * m ^ (-α))) := by ring
            _ = (3 / 2) ^ (6 * α) * ((4 * Real.pi) ^ α * dist x y ^ α * m ^ (5 * α)) := by
                rw [e3]
            _ ≤ (3 / 2) ^ (6 * α) * ((4 * Real.pi) ^ α * dist x y ^ α * 1) := by
                apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 3 / 2) _)
                exact mul_le_mul_of_nonneg_left e4 (by positivity)
            _ = (3 / 2) ^ (6 * α) * (4 * Real.pi) ^ α * dist x y ^ α := by ring
        calc |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x) - g (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y)|
            ≤ |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi x) - g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi y)|
              + |g (Work.Cyl.rho x ^ (3 * α)) (Work.ConstructionInstance.psi y)
                  - g (Work.Cyl.rho y ^ (3 * α)) (Work.ConstructionInstance.psi y)| := hsplit
          _ ≤ K * (Work.Cyl.rho x ^ (3 * α)) ^ 2
                * |Work.ConstructionInstance.psi x - Work.ConstructionInstance.psi y| ^ α
              + K * max (Work.Cyl.rho x ^ (3 * α)) (Work.Cyl.rho y ^ (3 * α))
                * |Work.Cyl.rho x ^ (3 * α) - Work.Cyl.rho y ^ (3 * α)| :=
              add_le_add hθslice hzslice
          _ ≤ K * ((3 * min (Work.Cyl.rho x) (Work.Cyl.rho y) / 2) ^ (6 * α)
                * (4 * Real.pi * dist x y / min (Work.Cyl.rho x) (Work.Cyl.rho y)) ^ α)
              + K * ((3 / 2) * (3 ^ α * (3 / 2) ^ (2 * α) * dist x y ^ α)) :=
              add_le_add hstep1 hstep2
          _ ≤ K * ((3 / 2) ^ (6 * α) * (4 * Real.pi) ^ α * dist x y ^ α)
              + K * ((3 / 2) * (3 ^ α * (3 / 2) ^ (2 * α) * dist x y ^ α)) := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left hstep1' hK0
              · exact le_refl _
          _ = (K * (3 / 2) ^ (6 * α) * (4 * Real.pi) ^ α
                + K * (3 / 2) * 3 ^ α * (3 / 2) ^ (2 * α)) * dist x y ^ α := by ring_nf
          _ ≤ C * dist x y ^ α :=
              mul_le_mul_of_nonneg_right hC56 (Real.rpow_nonneg hdnn α)
end Work.FTS.RegPkgGal
