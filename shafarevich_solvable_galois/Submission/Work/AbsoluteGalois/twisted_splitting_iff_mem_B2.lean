import Mathlib
import Submission.Work.GroupCohomology.Basic
import Submission.Work.GroupCohomology.Extension
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.AbsoluteGalois

set_option linter.style.haveILetI false

open Work.GroupCohomology

theorem twisted_splitting_iff_mem_B2 {Q : Type*} {A : Type*} [Group Q] [AddCommGroup A]
    [DistribMulAction Q A] (c : Q × Q → A) (hc : c ∈ Work.GroupCohomology.Z2 Q A)
    (h1 : c (1, 1) = 0) :
    letI := Work.GroupCohomology.twGroup Q A c hc h1
    (∃ t : Q →* (A × Q), ∀ q : Q, (t q).2 = q) ↔ c ∈ Work.GroupCohomology.B2 Q A := by
  letI := Work.GroupCohomology.twGroup Q A c hc h1
  constructor
  · -- A splitting yields an explicit `1`-cochain `f` with `d¹ f = c`.
    rintro ⟨t, ht⟩
    rw [mem_B2_iff]
    refine ⟨fun q => -(t q).1, ?_⟩
    funext p
    obtain ⟨q, r⟩ := p
    -- The twisted product computed from multiplicativity of `t`.
    have htw : t q * t r = twMul Q A c (t q) (t r) := rfl
    have hcomp : (t (q * r)).1 = (t q).1 + q • (t r).1 + c (q, r) := by
      have h := congrArg Prod.fst (t.map_mul q r)
      rw [htw] at h
      simp only [twMul] at h
      rwa [ht q, ht r] at h
    simp only [d1_apply]
    rw [hcomp, smul_neg]
    abel
  · -- A coboundary yields the splitting `q ↦ (-f q, q)`.
    rintro hB2
    rw [mem_B2_iff] at hB2
    obtain ⟨f, hf⟩ := hB2
    refine ⟨MonoidHom.mk' (fun q => (-f q, q)) ?_, fun q => rfl⟩
    intro q r
    show (-f (q * r), q * r) = twMul Q A c (-f q, q) (-f r, r)
    refine Prod.ext ?_ ?_
    · simp only [twMul]
      have hcr : c (q, r) = q • f r - f (q * r) + f q := by
        have h := congrFun hf (q, r)
        simp only [d1_apply] at h
        rw [← h]
      rw [hcr, smul_neg]
      abel
    · rfl

end Work.AbsoluteGalois
