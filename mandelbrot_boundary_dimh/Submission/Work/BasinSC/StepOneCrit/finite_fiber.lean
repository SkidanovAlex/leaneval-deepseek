import Mathlib

open Set Filter Topology

namespace Work.BasinSC.StepOneCrit

/-- A level set (fibre) of a holomorphic function on a connected open set that is compact is
finite: if it were infinite, compactness would produce an accumulation point inside `U`, and the
identity theorem would force `f` to be constant `w` there, contradicting `hne`. -/
theorem finite_fiber {U : Set ℂ} (hUo : IsOpen U) (hUc : IsConnected U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) {w : ℂ} (hne : ∃ z ∈ U, f z ≠ w)
    (hcomp : IsCompact (U ∩ f ⁻¹' {w})) : (U ∩ f ⁻¹' {w}).Finite := by
  by_contra hfin
  rw [Set.not_finite] at hfin
  obtain ⟨x, hx, hxacc⟩ := hfin.exists_accPt_of_subset_isCompact hcomp subset_rfl
  have hxU : x ∈ U := hx.1
  have hxacc' : AccPt x (𝓟 {z | f z = w}) :=
    hxacc.mono (principal_mono.mpr (fun y hy => by simpa using hy.2))
  have hcl : x ∈ closure ({z | f z = w} \ {x}) :=
    mem_closure_iff_nhdsWithin_neBot.mpr (accPt_principal_iff_nhdsWithin.mp hxacc')
  have heq : EqOn f (fun _ => w) U :=
    (hf.analyticOnNhd hUo).eqOn_of_preconnected_of_mem_closure analyticOnNhd_const
      hUc.isPreconnected hxU hcl
  obtain ⟨z, hzU, hzw⟩ := hne
  exact hzw (heq hzU)

end Work.BasinSC.StepOneCrit
