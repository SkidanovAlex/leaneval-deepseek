import Submission.ZagierHoffmanProof.StepL58
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L59: MAIN(2) assembly — the member 1-admissibility reduction (SESSION 202)

The MAIN(2) assembly (l2_induction over weight-w tuples with
`P(r s hw) := kAdm q s 1 → ¬kAdm q s 2 → AdmExpT F w 2 s`) dispatches each
in-domain CASE-1 j = 1 Step-1 member by `by_cases 2-adm` (A2_self) / `¬2-adm`
(recursion).  Applying the recursion hypothesis to a ¬2-adm member needs the
member to be 1-adm.  This module reduces every level-2 member's 1-admissibility to
its front value and depth:
  ★ kAdm_one_iff_front (q m hm0 hdepth) : kAdmissible q m 1  — 1-adm ⟺ first entry
    ≤ q and not the depth-1 (q) form (cond1 at x < 1, cond2's witness needs dep = 1
    then m⟨0⟩ = q = pad0 m 0);
  kAdm_one_front_le — the converse.
So per member family it suffices to show `pad0 (member) 0 ≤ q` (type-1/type-2:
front = s₁ ≤ q from 1-adm; type-3: s₁+1 ≤ q from hs1q via type3_front_le) and
exclude depth-1-with-head-q (type-1/2/3 members have depth ≥ 2 or head < q —
the type-3 head equals q only when s₁ = q−1, where the member has depth ≥ 2).

NEXT (SESSION 203): finish the MAIN(2) assembly — per-step `inDomain2_cases`
(StepL56): CASE-2 s₁ < q → A2_case2 (closed, non-recursive); CASE-1 j = 1 (s₁ < q):
rcases prop212_step1; per member by_cases 2-adm (A2_self) / ¬2-adm (recursion at
l2μ member < l2μ s via the StepL57/58 dispatch lemmas; member 1-adm via
kAdm_one_iff_front + the front facts); splice by admExpT_combine.  The j = 0 G5
subcases (CASE-2 (q,q), CASE-1 (q, s₂>q)) remain the only in-domain CASE-1/CASE-2
subcases without an expansion; then A(2)@w via A2_with_main2 and theorem_A(w) via
the StepL54 tail.  m ≥ 3 β-design separate; theorem_B/D ABP-gated.
-/

namespace ZagierHoffmanPositiveChar

/-- ★ 1-admissibility from front facts: a tuple is 1-admissible iff its first entry
is ≤ q and it is not the depth-1 form (q).  This reduces every level-2 member's
1-admissibility (needed to apply the MAIN(2) recursion hypothesis) to its front
value and depth. -/
lemma kAdm_one_iff_front (q : ℕ) {dep : ℕ} (m : Fin dep → ℕ+)
    (hm0 : pad0 m 0 ≤ q) (hdepth : dep = 1 → pad0 m 0 ≠ q) : kAdmissible q m 1 := by
  classical
  constructor
  · intro x hx
    have hx0 : x = 0 := by omega
    subst x
    exact hm0
  · intro hw
    rcases hw with ⟨hr1, hdep1, hall, hlast⟩
    have hd : dep = 1 := by omega
    subst dep
    have hp : pad0 m 0 = (m ⟨0, by omega⟩ : ℕ) := pad0_of_lt m (by omega : 0 < 1)
    have hm0q : pad0 m 0 = q := by
      rw [hp]
      have hidx : (⟨1 - 1, by omega⟩ : Fin 1) = ⟨0, by omega⟩ := by
        apply Fin.ext
        simp
      rw [hidx] at hlast
      exact hlast
    exact hdepth (by rfl) hm0q

/-- Converse: 1-admissibility forces the front facts. -/
lemma kAdm_one_front_le {q : ℕ} {dep : ℕ} (m : Fin dep → ℕ+)
    (h1 : kAdmissible q m 1) : pad0 m 0 ≤ q ∧ (dep = 1 → pad0 m 0 ≠ q) := by
  constructor
  · exact h1.1 0 (by omega)
  · intro hd hq
    apply h1.2
    subst dep
    refine ⟨by omega, by omega, ?_, ?_⟩
    · intro x hx
      omega
    · have hp : pad0 m 0 = (m ⟨0, by omega⟩ : ℕ) := pad0_of_lt m (by omega : 0 < 1)
      have hq0 : (m ⟨0, by omega⟩ : ℕ) = q := by
        rw [← hp]
        exact hq
      simpa using hq0
end ZagierHoffmanPositiveChar
