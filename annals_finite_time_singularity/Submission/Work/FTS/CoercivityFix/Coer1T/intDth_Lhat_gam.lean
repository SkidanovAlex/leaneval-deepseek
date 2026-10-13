/-
# Joint integrability of the `γ`-weighted pairing `D_θ(𝓛̂f)·D_θf·w²sin(2θ)^{-γ}`

This file proves `intDth_Lhat_gam`, one of the integrability certificates needed by the
`γ`-slot (`P₄`) of the level-1 coercivity of `𝓛_Γ^T` in the interior class `RegQ α 2`
(see `NOTES_coer1_LGammaT.md` in this directory): the pairing

  `⟨D_θ(𝓛̂ f), D_θ f⟩_{w² sin(2θ)^{-γ}}`

is an honest real number, i.e. its integrand is `IntegrableOn` the quadrant
`[0,∞) × [0,π/2]`.

## The mathematics

The two structural facts that make the integrand integrable for `f ∈ RegQ α 2` are

* **`D_θ` commutes exactly with `𝓛̂`** on the open quadrant
  (`Work.FTS.CoercivityFix.LhatCalc.Dth_Lhat`), so
  `D_θ(𝓛̂f) = 𝓛̂(D_θf) = D_θf + D_z(D_θf) − 2D_θf/(1+z) − 3D_θ(D_θf)/(1+z)`
  (`intDth_Lhat_gam_expand` below): `D_θ(𝓛̂ f)` is a *combination* of the three blocks
  `D_θf`, `D_zD_θf` and `D_θ²f` with bounded coefficients.  Hence the integrand is a sum
  of terms of the shape `(block₁)·(D_θf)·ρ_γ` with `ρ_γ = w²sin(2θ)^{-γ}`, and each of
  those is a product of two `L²(ρ_γ)`-blocks;
* **`HkMem α 2 f` makes every such block `L²(ρ_γ)`**: `f ∈ ℋ²` gives
  `(mixed j i f)² ρ_γ` integrable for `i + j ≤ 2`, `i ≥ 1`, i.e. for the blocks
  `mixed 1 0 = D_θf`, `mixed 1 1 = D_zD_θf` and `mixed 2 0 = D_θ²f`
  (`Coer1.sq_MixedGam`).  The cross terms are then handled by the elementary
  `2|ab| ≤ a² + b²` (`Coer1.integrableOn_mul_of_sq_Q`), and the coefficient
  `1/(1+z)` by `Coer1.integrableOn_div_one_add_Q` (bounded on `z ≥ 0`); the
  `D_θ²f`-term is exactly the field `hint_Dth_gam` of the bundle `Coer1.IntPkg`
  (`Coer1.IntPkg_Q`).

The identity `D_θ(𝓛̂f) = 𝓛̂(D_θf)` is used only on the *open* quadrant
(`z > 0`, `θ ∈ (0,π/2)`), which is a full-measure subset of `[0,∞) × [0,π/2]`, so all the
bookkeeping is done a.e. (`Coer1.ae_prod_fst_pos`, `Coer1.ae_prod_snd_mem_Ioo`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Vocab
import Submission.Work.Coercivity.thetaAux
import Submission.Work.FTS.CoercivityFix.Basic
import Submission.Work.FTS.CoercivityFix.LhatCalc.Dth_Lhat
import Submission.Work.FTS.CoercivityFix.Coer1.Defs
import Submission.Work.FTS.CoercivityFix.Coer1.IntFacts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Coer1T

set_option autoImplicit false

/-- **The pointwise expansion of `D_θ(𝓛̂ f)` on the open quadrant**: since `D_θ` commutes
with `𝓛̂` (`LhatCalc.Dth_Lhat`) and `𝓛̂g = g + D_zg − 2g/(1+z) − 3D_θg/(1+z)`,
`D_θ(𝓛̂f) = D_θf + D_zD_θf − 2D_θf/(1+z) − 3D_θ²f/(1+z)`. -/
theorem intDth_Lhat_gam_expand {f : ℝ → ℝ → ℝ} (hsq : Work.FTS.LocData.SmoothQuad f)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f) z θ
      = Work.Spaces.Dth f z θ + Work.Spaces.Dz (Work.Spaces.Dth f) z θ
        - 2 * Work.Spaces.Dth f z θ / (1 + z)
        - 3 * Work.Spaces.Dth (Work.Spaces.Dth f) z θ / (1 + z) := by
  rw [Work.FTS.CoercivityFix.LhatCalc.Dth_Lhat hsq hz hθ.1 hθ.2]
  simp only [Work.FTS.CoercivityFix.Lhat, Pi.sub_apply, Work.Coercivity.L,
    Work.Coercivity.Transport]

theorem intDth_Lhat_gam (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.Nonlin.RegQ α 2 f) :
    MeasureTheory.IntegrableOn
        (Function.uncurry (fun z θ => Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f) z θ
          * Work.Spaces.Dth f z θ * Work.Coercivity.thetaW α z θ))
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  -- the integrability bundle for `RegQ α 2` (in particular the `D_θ²f`-cross term)
  have hpk := Work.FTS.CoercivityFix.Coer1.IntPkg_Q α hα hf
  obtain ⟨hsq, hm, _hb⟩ := hf
  have hρnn : ∀ z θ, θ ∈ Work.Spaces.Iθ →
      0 ≤ Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α) z θ :=
    Work.FTS.CoercivityFix.Coer1.Rho_nonneg _
  have hρc : ContinuousOn (fun p : ℝ × ℝ =>
      Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α) p.1 p.2)
      Work.FTS.CoercivityFix.Coer1.Qd :=
    Work.FTS.CoercivityFix.Coer1.continuousOn_Rho _
  -- the two `L²(ρ_γ)`-blocks: `(D_θf)²ρ_γ = (mixed 0 1 f)²ρ_γ` and
  -- `(D_zD_θf)²ρ_γ = (mixed 1 1 f)²ρ_γ`
  have s11 := Work.FTS.CoercivityFix.Coer1.sq_MixedGam α hα hsq hm 1 1 le_rfl (by norm_num)
  have s10 := Work.FTS.CoercivityFix.Coer1.sq_MixedGam α hα hsq hm 1 0 le_rfl (by norm_num)
  -- ### `(D_θf)²ρ_γ`
  have hA : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth f z θ * Work.Spaces.Dth f z θ
        * Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α) z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine s10.congr ?_
    refine MeasureTheory.ae_restrict_of_forall_mem
      (measurableSet_Ici.prod measurableSet_Icc) (fun p hp => ?_)
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair, Work.Spaces.mixed_zero_left,
      Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero, pow_two]
  -- ### `D_zD_θf · D_θf · ρ_γ`
  have hB : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dz (Work.Spaces.Dth f) z θ
        * Work.Spaces.Dth f z θ
        * Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α) z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_mul_of_sq_Q
      (((Work.FTS.CoercivityFix.Coer1.continuousOn_mixed_Q hsq 1 1).mul
        (Work.FTS.CoercivityFix.Coer1.continuousOn_mixed_Q hsq 0 1)).mul hρc) hρnn s11 s10
  -- ### `(D_θf)²ρ_γ/(1+z)`
  have hC : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth f z θ * Work.Spaces.Dth f z θ
        * Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α) z θ / (1 + z)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_div_one_add_Q hA
  -- ### `D_θ²f · D_θf · ρ_γ/(1+z)`
  have hD : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth (Work.Spaces.Dth f) z θ
        * Work.Spaces.Dth f z θ
        * Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α) z θ / (1 + z)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := hpk.hint_Dth_gam
  -- ### the combination, and its a.e. identification with the target integrand
  refine (((hA.add hB).sub (hC.const_mul 2)).sub (hD.const_mul 3)).congr ?_
  have hquad : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      0 < p.1 ∧ p.2 ∈ Set.Ioo 0 (π / 2) :=
    Work.FTS.CoercivityFix.Coer1.ae_prod_fst_pos.and
      Work.FTS.CoercivityFix.Coer1.ae_prod_snd_mem_Ioo
  rw [Work.FTS.CoercivityFix.Coer1.iz_prod_restrict] at hquad
  filter_upwards [hquad] with p hp
  obtain ⟨hpz, hpθ⟩ := hp
  obtain ⟨z, θ⟩ := p
  simp only [Function.uncurry_apply_pair, Pi.add_apply, Pi.sub_apply]
  rw [intDth_Lhat_gam_expand hsq hpz hpθ]
  simp only [Work.FTS.CoercivityFix.Coer1.Rho, Work.FTS.CoercivityFix.Coer1.sig,
    Work.Coercivity.thetaW]
  ring

end Work.FTS.CoercivityFix.Coer1T
