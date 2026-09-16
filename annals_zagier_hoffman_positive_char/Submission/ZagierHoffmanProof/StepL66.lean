import Submission.ZagierHoffmanProof.StepL65
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L66: type-3 member depth and tuple of B*_v (SESSION 217 — verified against the def)

SESSION 217's discovery item, RESOLVED by reading the actual StepL19 definition:
the earlier `D.depB p' + 1` guess was WRONG.  ofBstarOver's fields give
  dep (Sum.inr (Sum.inr p')) = D.depB p'   (headAdd does NOT change the depth),
  c  (Sum.inr (Sum.inr p')) = headAdd v (D.hdepB p') (D.cB p'),
and headAdd v hr0 t adds v to the FIRST entry in place (index 0 ↦ v + t⟨0⟩, else
t j).  Both facts are definitional (rfl); committed here:
  bstar_c_inr_inr_dep : (ofBstarOver D v …).dep (Sum.inr (Sum.inr i)) = D.depB i;
  bstar_c_inr_inr : (ofBstarOver D v …).c (Sum.inr (Sum.inr i)) =
      headAdd v (D.hdepB i) (D.cB i).
CONSEQUENCE (for the per-member dispatch): a type-3 member has DEPTH = D.depB i
(≥ 1, possibly = 1) and head value v + (D.cB i)⟨0⟩ = s₁ + 1 (b-heads are 1 by
hbhd).  So kAdm_one_iff_front's depth-1 exclusion for a head = q type-3 member
requires D.depB i ≠ 1 — i.e., the type-3 member is ¬1-adm exactly when it is the
depth-1 tuple (s₁+1) with s₁ = q−1 — a genuine case to handle in the dispatch
(route through the recursion only if in-domain; otherwise H1-type/2-adm analysis).
NEXT: fold these into q_type3_member_dep at the Q-level (empty prefix), then
continue the per-member e dispatch of main2_case1_j1.  Named gates unchanged.
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Type-3 member dep of B*_v: `(ofBstarOver D v).dep (Sum.inr (Sum.inr i)) =
D.depB i` — headAdd does NOT change the depth (it adds v to the head in place). -/
lemma bstar_c_inr_inr_dep (D : RelData F) (v : ℕ+)
    (hvalid : ∀ e : ℕ, RelData.level F D e = 0)
    (hv : ∀ p : D.ιB, (v : ℕ) + ((D.cB p) ⟨0, D.hdepB p⟩ : ℕ) ≤ Nat.card F)
    (i : D.ιB) :
    (ofBstarOver F D v hvalid hv).dep (Sum.inr (Sum.inr i)) = D.depB i := by
  rfl

/-- Type-3 member tuple of B*_v: headAdd v over `D.cB i` (depth unchanged, head
value v + (D.cB i)⟨0⟩). -/
lemma bstar_c_inr_inr (D : RelData F) (v : ℕ+)
    (hvalid : ∀ e : ℕ, RelData.level F D e = 0)
    (hv : ∀ p : D.ιB, (v : ℕ) + ((D.cB p) ⟨0, D.hdepB p⟩ : ℕ) ≤ Nat.card F)
    (i : D.ιB) :
    (ofBstarOver F D v hvalid hv).c (Sum.inr (Sum.inr i)) =
      headAdd v (D.hdepB i) (D.cB i) := by
  rfl
end ZagierHoffmanPositiveChar
