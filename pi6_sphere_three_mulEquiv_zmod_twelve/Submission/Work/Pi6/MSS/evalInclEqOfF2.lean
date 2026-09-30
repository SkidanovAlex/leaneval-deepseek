import Mathlib
import Submission.Work.Pi6.MSS.CruxDefs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.MSS

/-- **Evaluation is constant on the difference of two fibre inclusions lying in the image of the
second Serre subcomplex.**  If `z` (a chain of the fibre over `b`) and `w` (a chain of the fibre
over `p e₀`) differ, after pushing forward to `E`, by the boundary of a chain `c` that already lies
in the second step of the Serre filtration, then any cochain `α` whose coboundary vanishes on that
second step takes the same value on the two pushforwards. -/
theorem evalInclEqOfF2 {𝕜 : Type} [Field 𝕜] {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (q : ℕ) (b : B)
    (α : Work.Cohomology.Cochain 𝕜 (Work.SSSR.sSing E) q)
    (hα : (Work.Pi6.MSS.serreCF 𝕜 E B p).d q α ∈ (Work.Pi6.MSS.serreCF 𝕜 E B p).F 2 (q + 1))
    (z : (Work.Pi6.MSS.E2cfk.fibCC 𝕜 p b).X q)
    (w : (Work.Pi6.MSS.E2cfk.fibCC 𝕜 p (p e₀)).X q)
    (c : (Work.Pi6.MSS.E2cfk.ECC 𝕜 E).X (q + 1))
    (hc : ∃ c' : (((Work.Pi6.MSS.E2cfk.sser p 2).toSSet).chainComplex (ModuleCat.of 𝕜 𝕜)).X (q + 1),
      (ModuleCat.Hom.hom ((Work.Pi6.MSS.E2cfk.sserInc 𝕜 p 2).f (q + 1))) c' = c)
    (hrel : (ModuleCat.Hom.hom ((Work.Pi6.MSS.E2cfk.fIncl 𝕜 p b).f q)) z
        - (ModuleCat.Hom.hom ((Work.Pi6.MSS.E2cfk.fIncl 𝕜 p (p e₀)).f q)) w
        = (ModuleCat.Hom.hom ((Work.Pi6.MSS.E2cfk.ECC 𝕜 E).d (q + 1) q)) c) :
    α ((ModuleCat.Hom.hom ((Work.Pi6.MSS.E2cfk.fIncl 𝕜 p b).f q)) z)
      = α ((ModuleCat.Hom.hom ((Work.Pi6.MSS.E2cfk.fIncl 𝕜 p (p e₀)).f q)) w) := by
  -- `F^2` is the annihilator of the second Serre subcomplex
  have hmem : (serreCF 𝕜 E B p).d q α ∈ compAnn 𝕜 (Work.Pi6.MSS.E2cfk.sser p 2) (q + 1) := by
    rw [← F_eq_compAnn 𝕜 E B p 2 (q + 1)]
    exact hα
  obtain ⟨c', hc'⟩ := hc
  -- the coboundary of `α` vanishes on the boundary chain `c`
  have h0 : α (((Work.Pi6.MSS.E2cfk.fIncl 𝕜 p b).f q).hom z
      - ((Work.Pi6.MSS.E2cfk.fIncl 𝕜 p (p e₀)).f q).hom w) = 0 := by
    rw [hrel]
    rw [← dPrevL_apply_succ 𝕜 E B p q α c]
    rw [← hc']
    exact hmem c'
  rw [map_sub α (((Work.Pi6.MSS.E2cfk.fIncl 𝕜 p b).f q).hom z)
      (((Work.Pi6.MSS.E2cfk.fIncl 𝕜 p (p e₀)).f q).hom w)] at h0
  exact sub_eq_zero.mp h0

end Work.Pi6.MSS
