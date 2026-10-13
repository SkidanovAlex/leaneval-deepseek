import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.ConstructionInstance.Defs
import Submission.Work.ConstructionInstance.profile_add_z_pz_abs_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-! ## The `z∂_z F_*` box: `|z·∂_zF_*(z,θ)| ≤ 5p`

`F_*(z,θ) = p·(Γ(θ)/c(p))·2z/(1+z)²`, so

  `z·∂_zF_*(z,θ) = p·(Γ(θ)/c(p))·(2z(1-z)/(1+z)³)`.

Here `Γ(θ)/c(p) ≤ 10` on `[0,π/2]` (`Work.Spaces.c_bounds` and `Γ ≤ 1`) and
`|2z(1-z)/(1+z)³| ≤ 1/2`: indeed `|1-z| ≤ 1+z` and `2z(1+z) ≤ (1+z)³/2`, the latter being
`4z ≤ (1+z)²`, i.e. `0 ≤ (1-z)²`. -/

/-- **The `F_*` part of the weighted `z`-derivative box.**  For `0 < p ≤ 1`, `z > 0` and
`θ ∈ [0,π/2]`, `|z·∂_zF_*(z,θ)| ≤ 5p`. -/
theorem z_pz_Fstar_abs_le {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |z * Work.Spaces.pz (Work.Construction.Fstar p) z θ| ≤ 5 * p := by
  have hc := (Work.Spaces.c_bounds p hp hp1).1
  have hcpos : 0 < Work.Spaces.c p := by linarith
  have hG := Work.Spaces.Gam_bounds p θ hp hθ
  have hq0 : 0 ≤ Work.Spaces.Gam p θ / Work.Spaces.c p := div_nonneg hG.1 hcpos.le
  have hq1 : Work.Spaces.Gam p θ / Work.Spaces.c p ≤ 10 := by
    rw [div_le_iff₀ hcpos]; nlinarith [hG.2]
  have hzden : (0 : ℝ) < (1 + z) ^ 3 := by positivity
  -- `|2z(1-z)| ≤ 2z(1+z)`
  have h1 : |2 * z * (1 - z)| ≤ 2 * z * (1 + z) := by
    have h2z : |2 * z| = 2 * z := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hz.le]
    have h3 : |1 - z| ≤ 1 + z := by rw [abs_le]; constructor <;> linarith
    rw [abs_mul, h2z]
    exact mul_le_mul_of_nonneg_left h3 (by linarith)
  -- `2z(1+z) ≤ (1+z)³/2`
  have h4 : 2 * z * (1 + z) ≤ (1 + z) ^ 3 / 2 := by
    have hpos : 0 < 1 + z := by linarith
    have hsq : 0 ≤ (1 + z) * (1 - z) ^ 2 := mul_nonneg hpos.le (sq_nonneg _)
    have e : (1 + z) ^ 3 / 2 - 2 * z * (1 + z) = (1 + z) * (1 - z) ^ 2 / 2 := by ring
    linarith
  have hfrac : |2 * z * (1 - z) / (1 + z) ^ 3| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos hzden, div_le_iff₀ hzden]
    linarith
  have hDz := Work.Construction.Dz_Fstar_eq (α := p) (z := z) (θ := θ) hp (by linarith : (-1 : ℝ) < z)
  rw [Work.Spaces.Dz] at hDz
  rw [hDz, abs_mul, abs_of_nonneg (mul_nonneg hp.le hq0)]
  calc p * (Work.Spaces.Gam p θ / Work.Spaces.c p) * |2 * z * (1 - z) / (1 + z) ^ 3|
      ≤ p * 10 * (1 / 2) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hq1 hp.le
        · exact hfrac
        · exact abs_nonneg _
        · positivity
    _ = 5 * p := by ring

/-- **The weighted `z`-derivative box of the profile.**

Writing `F = F_* + g`, the derivative splits as `∂_zF = ∂_zF_* + ∂_zg` on the branch `θ ≥ 0`
(`pz_profile_eq_of_nonneg`) and as `∂_zF = -(∂_zg + ∂_zF_*)(·,-θ)` on `θ < 0`
(`pz_profile_eq_of_neg`).  The `F_*` part is bounded by `5p` uniformly (`z_pz_Fstar_abs_le`)
and the perturbation by `Cg'` (hypothesis `hg2`), giving `|z∂_zF| ≤ 5p + Cg'` for `z > 0`,
`|θ| ≤ π/2`. -/
theorem z_pz_profile_abs_le {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {g : ℝ → ℝ → ℝ} {Cg' : ℝ}
    (hg2 : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |z * Work.Spaces.pz g z θ| ≤ Cg')
    (hgdiff : ∀ z θ : ℝ, 0 < z → HasDerivAt (fun z' => Work.ConstructionInstance.profile p g z' θ)
      (Work.Spaces.pz (Work.ConstructionInstance.profile p g) z θ) z) :
    ∀ z θ : ℝ, 0 < z → |θ| ≤ Real.pi / 2 →
      |z * Work.Spaces.pz (Work.ConstructionInstance.profile p g) z θ| ≤ 5 * p + Cg' := by
  intro z θ hz hθ
  have hz1 : (-1 : ℝ) < z := by linarith
  rcases le_or_gt 0 θ with hθ0 | hθ0
  · -- positive branch
    have hθmem : θ ∈ Work.Spaces.Iθ :=
      ⟨hθ0, by rw [abs_of_nonneg hθ0] at hθ; exact hθ⟩
    have hsplit := pz_profile_eq_of_nonneg (p := p) (g := g) (z := z) (θ := θ) hz1 hθ0
      (hgdiff z θ hz)
    have hkey : z * Work.Spaces.pz (profile p g) z θ
        = z * Work.Spaces.pz g z θ + z * Work.Spaces.pz (Work.Construction.Fstar p) z θ := by
      rw [hsplit]; ring
    rw [hkey]
    calc |z * Work.Spaces.pz g z θ + z * Work.Spaces.pz (Work.Construction.Fstar p) z θ|
        ≤ |z * Work.Spaces.pz g z θ| + |z * Work.Spaces.pz (Work.Construction.Fstar p) z θ| :=
          abs_add_le _ _
      _ ≤ Cg' + 5 * p :=
          add_le_add (hg2 z θ hz.le hθmem) (z_pz_Fstar_abs_le hp hp1 hz hθmem)
      _ = 5 * p + Cg' := by ring
  · -- negative branch: reduce to `-θ > 0`
    have hθmem : -θ ∈ Work.Spaces.Iθ :=
      ⟨by linarith, by rw [abs_of_neg hθ0] at hθ; exact hθ⟩
    have hsplit := pz_profile_eq_of_neg (p := p) (g := g) (z := z) (θ := θ) hz1 hθ0
      (hgdiff z θ hz)
    have hkey : z * Work.Spaces.pz (profile p g) z θ
        = -(z * Work.Spaces.pz g z (-θ)
            + z * Work.Spaces.pz (Work.Construction.Fstar p) z (-θ)) := by
      rw [hsplit]; ring
    rw [hkey, abs_neg]
    calc |z * Work.Spaces.pz g z (-θ) + z * Work.Spaces.pz (Work.Construction.Fstar p) z (-θ)|
        ≤ |z * Work.Spaces.pz g z (-θ)| + |z * Work.Spaces.pz (Work.Construction.Fstar p) z (-θ)| :=
          abs_add_le _ _
      _ ≤ Cg' + 5 * p :=
          add_le_add (hg2 z (-θ) hz.le hθmem) (z_pz_Fstar_abs_le hp hp1 hz hθmem)
      _ = 5 * p + Cg' := by ring

end Work.ConstructionInstance
