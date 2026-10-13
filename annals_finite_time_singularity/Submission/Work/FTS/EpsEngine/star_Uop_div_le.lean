import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Construction.Defs
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.Spaces.WlInf_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

/-- **The star piece of the `Uop/sin 2θ` slot.**  This is the extraction of the field
`StarPkgo2.UsW` (`WlInfMem α 4 (Uop α (PhiTil α F_* Φs)/sin 2θ) ∧ WlInf α 4 (…) ≤ Cs α`): the
`k = 0` summand of `WlInf` is `supAbs` of the function itself, and `WlInfMem` makes that supremum
honest, so the pointwise bound follows (there is a precedent extraction for the star `U`-field in
`Submission/Work/FTS/NonlinRows/...`, `WlInf_z_bound`).  Only the numerical constant matters
downstream. -/
theorem star_Uop_div_le {α Cs : ℝ} {Φs : ℝ → ℝ → ℝ} (hα : 0 < α) (hCs : 0 ≤ Cs)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
          / Work.Construction.s2 θ| ≤ Cs * α := by
  intro z θ hz hθ hθ2
  -- the domain memberships `z ∈ [0,∞)`, `θ ∈ [0,π/2]`
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ, le_of_lt hθ2⟩
  -- the `𝒲^{4,∞}`-field is the `Uop/sin 2θ` slot of the star package
  set f : ℝ → ℝ → ℝ :=
    fun z θ => Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
      / Work.Construction.s2 θ with hf
  have hmem : Work.Spaces.WlInfMem α 4 f := hstar.UsW.1
  have hb : Work.Spaces.WlInf α 4 f ≤ Cs * α := hstar.UsW.2
  -- the `k = 0` summand of `WlInf` is bounded by the whole norm
  have h0 := Work.Spaces.WlInf_z_bound α 4 f hmem 0 (Nat.zero_le 4) z θ hzI hθI
  have h1 : |f z θ| ≤ Work.Spaces.WlInf α 4 f := by
    simpa only [Work.Spaces.pzIter_zero, pow_zero, one_mul] using h0
  exact le_trans h1 hb

end Work.FTS.EpsEngine
