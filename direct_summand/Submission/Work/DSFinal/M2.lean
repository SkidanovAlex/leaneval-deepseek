import Submission.Work.DSMap.Gaps
import Submission.Work.DSM2p.Main

/-! # DSFinal.M2 — LEAD-OWNED (curric-46, 10-14): `Gaps.m2pos1_any` citing the PROVED
single-polynomial André lemma `DSMap.Gaps.area_M2pos1_proved` (DSM2p). -/

namespace Work.DSFinal

open DSMap

universe a

theorem m2pos1_any_final (p : ℕ) [Fact p.Prime] (A : Type a) [CommRing A] (P : PerfectoidData p A)
    (F : Polynomial A) (hF : F.Monic) (hd : Nontrivial A → 0 < F.natDegree) :
    ∃ (B : Type a) (_ : CommRing B) (_ : Algebra A B) (Q : PerfectoidData p B),
      (∀ k, Q.ϖ k = algebraMap A B (P.ϖ k)) ∧
      Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A)})
        (B ⧸ (Ideal.span {(p : A)}).map (algebraMap A B)) ∧
      ∃ r : ℕ → B, Polynomial.aeval (r 0) F = 0 ∧ ∀ k, r (k + 1) ^ p = r k := by
  by_cases h : Nontrivial A
  · exact DSMap.Gaps.area_M2pos1_proved p A P F hF (hd h)
  · rw [not_nontrivial_iff_subsingleton] at h
    have : Subsingleton (A ⧸ Ideal.span {(p : A)}) := Ideal.Quotient.mk_surjective.subsingleton
    have : Subsingleton (A ⧸ (Ideal.span {(p : A)}).map (algebraMap A A)) :=
      Ideal.Quotient.mk_surjective.subsingleton
    refine ⟨A, inferInstance, Algebra.id A, P, fun _ => rfl, ?_, fun _ => 0,
      Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩
    exact { toFlat := inferInstance,
            submodule_ne_top := fun m hm => (hm.ne_top (Subsingleton.elim _ _)).elim }


end Work.DSFinal
