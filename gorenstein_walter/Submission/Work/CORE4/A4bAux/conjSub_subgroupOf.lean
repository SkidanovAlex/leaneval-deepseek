import Mathlib
import Submission.Work.CORE4.Defs

namespace Work.CORE4.A4bAux

theorem conjSub_subgroupOf {G : Type*} [Group G] {E K : Subgroup G} (hKE : K ≤ E) {e : G}
    (he : e ∈ E) :
    Work.GW2.conjSub ⟨e, he⟩ (K.subgroupOf E) = (Work.GW2.conjSub e K).subgroupOf E := by
  ext x
  simp only [Work.GW2.conjSub, Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hyK, hxy⟩
    refine ⟨(y : G), hyK, ?_⟩
    have h := congrArg (Subtype.val) hxy
    simpa [MulAut.conj_apply] using h
  · rintro ⟨z, hzK, hzx⟩
    have hzx' : e * z * e⁻¹ = (x : G) := by
      simpa [MulAut.conj_apply] using hzx
    have hzE : z ∈ E := by
      have hz_eq : z = e⁻¹ * (x : G) * e := by
        rw [← hzx']; group
      rw [hz_eq]
      exact E.mul_mem (E.mul_mem (E.inv_mem he) x.2) he
    refine ⟨⟨z, hzE⟩, hzK, ?_⟩
    apply Subtype.ext
    simpa [MulAut.conj_apply] using hzx'

end Work.CORE4.A4bAux
