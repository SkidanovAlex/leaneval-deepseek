import Mathlib
import Submission.Work.DSM4p.Basic
import Submission.Work.DSM4p.Completion
import Submission.Work.DSM4p.chartComp_modPow
import Submission.Work.DSM4p.chartComp_isQRETp
import Submission.Work.DSM4p.chartComp_exists_tr
import Submission.Work.DSM4p.adicTr_exists_compat
import Submission.Work.DSM4p.adicCompletion_kernel_clause
import Submission.Work.DSM4p.adicCompletion_cokernel_clause

namespace Work.DSM4p

universe a

/- The hypothesis `htf` is part of the fixed statement but is not needed for this reduction: the
transfer of the QRET clauses uses only that `E n → AdicCompletion (p) (E n)` induces an
isomorphism modulo `p ^ m`.  We keep the statement verbatim and silence the unused-variable
linter. -/
set_option linter.unusedVariables false

theorem isQRETp_adicCompletion {p : ℕ} [Fact p.Prime] {B : Type a} [CommRing B]
    (ϖ gr : ℕ → B) {E : ℕ → Type a} [∀ n, CommRing (E n)] [∀ n, Algebra B (E n)]
    (htf : ∀ n, IsSMulRegular (E n) (p : E n)) (tr : ∀ n, E (n + 1) →ₐ[B] E n)
    (h : DSMap.Mix2.IsQRETp p B ϖ gr E tr) :
    ∃ tr' : ∀ n, AdicCompletion (Ideal.span {((p : E (n + 1)))}) (E (n + 1)) →ₐ[B]
        AdicCompletion (Ideal.span {((p : E n))}) (E n),
      DSMap.Mix2.IsQRETp p B ϖ gr
        (fun n => AdicCompletion (Ideal.span {((p : E n))}) (E n)) tr' := by
  obtain ⟨tr', htr'⟩ := adicTr_exists_compat (p := p) tr
  refine ⟨tr', ?_⟩
  intro m k
  obtain ⟨c, hk, hc⟩ := h m k
  exact ⟨c,
    adicCompletion_kernel_clause (m := m) (k := k) (c := c) (ϖ := ϖ) (gr := gr) hk,
    adicCompletion_cokernel_clause (m := m) (k := k) (c := c) (ϖ := ϖ) (gr := gr)
      tr tr' htr' hc⟩

end Work.DSM4p
