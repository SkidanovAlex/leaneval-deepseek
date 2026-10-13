import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.RegExportIface.Defs
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT

/-! ## Elementary facts about the angular factor `Γ(θ) = (sinθ·cos²θ)^α` -/

/-- `Γ` is positive on the open angular interval. -/
lemma Gamma_pos (α θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    0 < Work.FTS.Regularity.Gamma α θ := by
  refine Real.rpow_pos_of_pos ?_ α
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [hθ1, Real.pi_pos])
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith, hθ1⟩
  positivity

/-- `∂_θΓ = Γ·(2α·c2m θ)/sin 2θ` on the open angular interval. -/
lemma hasDerivAt_Gamma (α θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    HasDerivAt (fun θ' : ℝ => Work.FTS.Regularity.Gamma α θ')
      (Work.FTS.Regularity.Gamma α θ
        * (2 * α * Work.Construction.c2m θ / Real.sin (2 * θ))) θ := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [hθ1, Real.pi_pos])
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith, hθ1⟩
  have hφpos : 0 < Real.sin θ * Real.cos θ ^ 2 := by positivity
  have hφ : HasDerivAt (fun θ' : ℝ => Real.sin θ' * Real.cos θ' ^ 2)
      (Real.cos θ * Real.cos θ ^ 2
        + Real.sin θ * (2 * Real.cos θ ^ (2 - 1) * (-Real.sin θ))) θ :=
    (Real.hasDerivAt_sin θ).mul ((Real.hasDerivAt_cos θ).fun_pow 2)
  have hΓ := hφ.rpow_const (p := α) (Or.inl (ne_of_gt hφpos))
  refine hΓ.congr_deriv ?_
  have hA : Real.cos θ * Real.cos θ ^ 2
        + Real.sin θ * (2 * Real.cos θ ^ (2 - 1) * (-Real.sin θ))
      = Real.cos θ * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) := by
    norm_num
    ring
  have hpow : Work.FTS.Regularity.Gamma α θ
      = (Real.sin θ * Real.cos θ ^ 2) ^ (α - 1) * (Real.sin θ * Real.cos θ ^ 2) := by
    show (Real.sin θ * Real.cos θ ^ 2) ^ α = _
    conv_lhs => rw [show α = (α - 1) + 1 by ring]
    rw [Real.rpow_add hφpos, Real.rpow_one]
  have hsin2 : Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ := Real.sin_two_mul θ
  have hc2m : Work.Construction.c2m θ = Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2 := by
    rw [Work.Construction.c2m, Real.cos_two_mul']
    ring
  rw [hA, hpow, hsin2, hc2m]
  have hs0 : Real.sin θ ≠ 0 := ne_of_gt hs
  have hc0 : Real.cos θ ≠ 0 := ne_of_gt hc
  field_simp

/-! ## The two partial derivatives of `ω` -/

/-- `∂_z ω α z θ = ω α z θ · 2/(z(1+z))` for `z > 0`. -/
lemma hasDerivAt_omega_z (α z θ : ℝ) (hz : 0 < z) :
    HasDerivAt (fun z' => Work.FTS.RegExportIface.ω α z' θ)
      (Work.FTS.RegExportIface.ω α z θ * (2 / (z * (1 + z)))) z := by
  have hbase : HasDerivAt (fun z' : ℝ => z' ^ 2 / (1 + z') ^ 2) (2 * z / (1 + z) ^ 3) z := by
    have hnum : HasDerivAt (fun z' : ℝ => z' ^ 2) (2 * z ^ (2 - 1) * 1) z := by
      simpa using hasDerivAt_pow 2 z
    have hden : HasDerivAt (fun z' : ℝ => (1 + z') ^ 2)
        (2 * (1 + z) ^ (2 - 1) * (0 + 1)) z := by
      have hlin : HasDerivAt (fun z' : ℝ => 1 + z') (0 + 1) z :=
        (hasDerivAt_const z (1:ℝ)).add (hasDerivAt_id z)
      exact hlin.fun_pow 2
    have hpos : (1 + z : ℝ) ^ 2 ≠ 0 := by positivity
    have hdiv := hnum.div hden hpos
    exact hdiv.congr_deriv (by norm_num; field_simp; ring)
  have h1 : HasDerivAt (fun z' : ℝ => Work.FTS.Regularity.Gamma α θ * (z' ^ 2 / (1 + z') ^ 2))
      (Work.FTS.Regularity.Gamma α θ * (2 * z / (1 + z) ^ 3)) z := hbase.const_mul _
  have h2 : HasDerivAt (fun z' : ℝ => z' ^ 2 * Work.FTS.Regularity.Gamma α θ / (1 + z') ^ 2)
      (Work.FTS.Regularity.Gamma α θ * (2 * z / (1 + z) ^ 3)) z :=
    h1.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun z' => by ring))
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hz1 : (1 + z : ℝ) ≠ 0 := by positivity
  exact h2.congr_deriv (by simp only [Work.FTS.RegExportIface.ω]; field_simp)

/-- `∂_θ ω α z θ = ω α z θ · 2α·c2m θ / sin 2θ` for `0 < θ < π/2`. -/
lemma hasDerivAt_omega_theta (α z θ : ℝ) (_hα : 0 < α) (hθ0 : 0 < θ)
    (hθ1 : θ < Real.pi / 2) :
    HasDerivAt (fun θ' => Work.FTS.RegExportIface.ω α z θ')
      (Work.FTS.RegExportIface.ω α z θ
        * (2 * α * Work.Construction.c2m θ / Real.sin (2 * θ))) θ := by
  have hbase := hasDerivAt_Gamma α θ hθ0 hθ1
  have h1 : HasDerivAt
      (fun θ' : ℝ => z ^ 2 / (1 + z) ^ 2 * Work.FTS.Regularity.Gamma α θ')
      (z ^ 2 / (1 + z) ^ 2
        * (Work.FTS.Regularity.Gamma α θ
          * (2 * α * Work.Construction.c2m θ / Real.sin (2 * θ)))) θ :=
    hbase.const_mul _
  have h2 : HasDerivAt
      (fun θ' : ℝ => z ^ 2 * Work.FTS.Regularity.Gamma α θ' / (1 + z) ^ 2)
      (z ^ 2 / (1 + z) ^ 2
        * (Work.FTS.Regularity.Gamma α θ
          * (2 * α * Work.Construction.c2m θ / Real.sin (2 * θ)))) θ :=
    h1.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun θ' => by ring))
  exact h2.congr_deriv (by simp only [Work.FTS.RegExportIface.ω]; ring)

/-- Elementary facts about the weight `ω α z θ = z²·(sinθ·cos²θ)^α/(1+z)²` of the
self-similar variables (`Work.FTS.RegExportIface.ω`, whose angular factor is
`Work.FTS.Regularity.Gamma α θ = (sinθ·cos²θ)^α`; note `Work.Spaces.pExp α = 3α`, so this is
`Work.Spaces.Gam (pExp α) θ`), for `α > 0`, `z > 0`, `0 < θ < π/2`:

* `ω α z θ > 0`;
* `∂_z ω = ω·2/(z(1+z))`;
* `∂_θ ω = ω·2α·c2m(θ)/sin 2θ`, where `c2m θ = cos 2θ − sin²θ = cos²θ − 2 sin²θ`
  (`Work.Construction.c2m`).

The last identity: `∂_θΓ = α·Γ·(cos²θ − 2sin²θ)/(sinθ cosθ) = Γ·α·c2m θ/(sinθ cosθ)`,
and `1/(sinθcosθ) = 2/sin 2θ`. -/
theorem omega_facts (α : ℝ) (hα : 0 < α) :
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      0 < Work.FTS.RegExportIface.ω α z θ) ∧
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      HasDerivAt (fun z' => Work.FTS.RegExportIface.ω α z' θ)
        (Work.FTS.RegExportIface.ω α z θ * (2 / (z * (1 + z)))) z) ∧
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      HasDerivAt (fun θ' => Work.FTS.RegExportIface.ω α z θ')
        (Work.FTS.RegExportIface.ω α z θ * (2 * α * Work.Construction.c2m θ
          / Real.sin (2 * θ))) θ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z θ hz hθ0 hθ1
    have hG : 0 < Work.FTS.Regularity.Gamma α θ := Gamma_pos α θ hθ0 hθ1
    rw [show Work.FTS.RegExportIface.ω α z θ
        = z ^ 2 * Work.FTS.Regularity.Gamma α θ / (1 + z) ^ 2 from rfl]
    positivity
  · intro z θ hz _ _
    exact hasDerivAt_omega_z α z θ hz
  · intro z θ _ hθ0 hθ1
    exact hasDerivAt_omega_theta α z θ hα hθ0 hθ1

end Work.FTS_RegExport.RXT
