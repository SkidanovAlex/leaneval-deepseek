import Submission.ZagierHoffmanProof.StepL59
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L60: MAIN2-weak assembly — first branch closures (SESSION 204)

MAIN2-weak (PLAN SESSION 203): ∀ in-domain (1-adm ∧ ¬2-adm) weight-w tuples:
AdmExp F w 2 m, by l2_induction with P(r s hw) := kAdm q s 1 → ¬kAdm q s 2 →
AdmExp F w 2 s.  Since a partially-filled theorem cannot compile, StepL60 collects
the per-branch closures as standalone sorry-free lemmas:
  ★ main2_case2 (w s hw hr2 hp1 hs1q) : AdmExp F w 2 s — the NON-RECURSIVE CASE-2
    s₁ < q branch (A2_case2, StepL56, at the weak AdmExp level theorem-A consumes);
  s1_eq_of_not_lt (h1 hnot) : pad0 s 0 = q — the j = 0 (G5) form detector: from
    1-adm's pad0 s 0 ≤ q and ¬(pad0 s 0 < q).
REMAINING (next sessions, per PLAN SESSION 203): the CASE-1 j = 1 splice
(main2_case1_j1: rcases prop212_step1, ζ(s) = Σ_{i₀≠u,2,3} (−a)·ζ(member) over the
reindexed three families, per member by_cases 2-adm (admExp_self) / ¬2-adm
(recursion via ih: member 1-adm by kAdm_one_iff_front + front facts, l2μ < l2μ s by
the StepL57/58 dispatch lemmas), splice with admExp_combine), then the g5-closure of
the two s₁ = q cases, then MAIN2_weak / A2_weak / theorem-A.  j = 0 G5 chains and
the m ≥ 3 hierarchy separate; theorem_B/D ABP-gated.
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★ MAIN2-weak CASE-2 branch (s₁ < q): a depth-2 tuple (s₁, q) with s₁ < q
expands at level 2 WITHOUT recursion (case2_level2's members are 2-adm), at the weak
AdmExp level that theorem-A consumes. -/
theorem main2_case2 (w : ℕ) {r : ℕ} (s : Fin r → ℕ+) (hw : weight r s = w)
    (hr2 : r = 2) (hp1 : pad0 s 1 = Nat.card F) (hs1q : pad0 s 0 < Nat.card F) :
    AdmExp F w 2 s := by
  classical
  have hT : AdmExpT F w 2 s := A2_case2 F w s hw hr2 hp1 hs1q
  exact admExpT_to_AdmExp F w 2 s hT

/-- From `¬ pad0 s 0 < q` and 1-admissibility (pad0 s 0 ≤ q): the first entry is q —
the j = 0 (G5) form. -/
lemma s1_eq_of_not_lt (q : ℕ) {r : ℕ} (s : Fin r → ℕ+)
    (h1 : kAdmissible q s 1) (hnot : ¬ pad0 s 0 < q) : pad0 s 0 = q := by
  have hle : pad0 s 0 ≤ q := h1.1 0 (by omega)
  omega
end ZagierHoffmanPositiveChar
