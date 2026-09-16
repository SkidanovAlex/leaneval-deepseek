import Submission.ZagierHoffmanProof.StepL99
import Submission.ZagierHoffmanProof.StepL56
import Submission.ZagierHoffmanProof.StepL60
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L100: ★ main2T_of_g5T — the strengthened in-domain level-2 handler,
modulo the strengthened j=0 G5 chains (SESSION 251)

theorem main2T_of_g5T (w) (g5T : ∀ r m hm, kAdm1 m → ¬ kAdm2 m → pad0 m 0 = q
  → AdmExpT F w 2 m) : ∀ r s hw, kAdm q s 1 → ¬ kAdm q s 2 → AdmExpT F w 2 s
— MAIN(2)-strengthened (outputs carry the prefix orders ℓ ≥ 2), via l2_induction
with per-step inDomain2_cases dispatch:
  CASE-1 (2 ≤ r ∧ q < pad0 s 1): pad0 s 0 < q → main2T_case1_j1 (StepL99, the
    strengthened (2,1) splice) with the recursion IH; pad0 s 0 = q → g5T;
  CASE-2 (r = 2 ∧ pad0 s 1 = q): a < q → A2_case2 (already AdmExpT, leaf);
    a = q → g5T;
pad0→value conversions via pad0_of_lt + s1_eq_of_not_lt.
So the ONLY remaining level-2 ingredient for main2T (fully unconditional) is the
strengthened G5T total — the two ordered j=0 chains: G5T_case1 ((q, s₂>q,
…), the StepL80 g5_case1_step port to AdmExpT with orders) and G5T_case2 ((q,q),
the StepL75–79 g5qq chain port).  With g5T := g5T_total closed, A2T_from_main2T
and A3_from_main2T (StepL97) make A(1,2,3)@w fully unconditional.
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★ MAIN(2)-strengthened from the j = 0 G5 hypothesis: the in-domain
(1-adm ∧ ¬2-adm) handler at the AdmExpT level (with prefix orders).  The
l2_induction step dispatches inDomain2_cases: CASE-1 (2 ≤ r ∧ q < pad0 s 1):
j=1 (pad0 s 0 < q → main2T_case1_j1 with the recursion IH) or j=0 (pad0 s 0 = q
→ the strengthened G5T hypothesis); CASE-2 (r = 2 ∧ pad0 s 1 = q): a<q →
A2_case2 (already AdmExpT, no recursion) or a=q → G5T. -/
theorem main2T_of_g5T (w : ℕ)
    (g5T : ∀ (r : ℕ) (m : Fin r → ℕ+) (hm : weight r m = w),
      kAdmissible (Nat.card F) m 1 → ¬ kAdmissible (Nat.card F) m 2 →
      pad0 m 0 = Nat.card F → AdmExpT F w 2 m) :
    ∀ (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w),
      kAdmissible (Nat.card F) s 1 → ¬ kAdmissible (Nat.card F) s 2 → AdmExpT F w 2 s := by
  classical
  let P : (r : ℕ) → (s : Fin r → ℕ+) → weight r s = w → Prop :=
    fun r s hw => kAdmissible (Nat.card F) s 1 → ¬ kAdmissible (Nat.card F) s 2 → AdmExpT F w 2 s
  change ∀ (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w), P r s hw
  refine l2_induction (Nat.card F) w P ?_
  intro r s hw rec h1 hn2
  have hcases := inDomain2_cases (Nat.card F) (card_ge_two F) s h1 hn2
  rcases hcases with hc1 | hc2
  · rcases hc1 with ⟨hcase, hbigp⟩
    by_cases hs1 : pad0 s 0 < Nat.card F
    · -- CASE-1 j = 1 (s₀ < q < s₁): the strengthened (2,1) splice
      have hbigv : (Nat.card F : ℕ) < (s ⟨1, by omega⟩ : ℕ) := by
        have hp : pad0 s 1 = (s ⟨1, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 1 < r)
        rw [← hp]
        exact hbigp
      have hs0lt : (s ⟨0, by omega⟩ : ℕ) < Nat.card F := by
        have hp : pad0 s 0 = (s ⟨0, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 0 < r)
        rw [← hp]
        exact hs1
      exact main2T_case1_j1 F w r s hw hcase hbigv hs0lt h1 hn2
        (fun r' m hm hdrop h1m h2m => rec r' m hm hdrop h1m h2m)
    · -- CASE-1 j = 0 (s₀ = q): the strengthened G5 chain
      have hs0 : pad0 s 0 = Nat.card F := s1_eq_of_not_lt (Nat.card F) s h1 hs1
      exact g5T r s hw h1 hn2 hs0
  · rcases hc2 with ⟨hr2, hp1⟩
    by_cases hs1 : pad0 s 0 < Nat.card F
    · -- CASE-2 (a,q) with a < q: the strengthened leaf (no recursion)
      exact A2_case2 F w s hw hr2 hp1 hs1
    · -- CASE-2 (q,q): the strengthened G5 chain
      have hs0 : pad0 s 0 = Nat.card F := s1_eq_of_not_lt (Nat.card F) s h1 hs1
      exact g5T r s hw h1 hn2 hs0

end ZagierHoffmanPositiveChar
