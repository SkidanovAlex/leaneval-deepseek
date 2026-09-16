import Submission.ZagierHoffmanProof.StepL183

set_option autoImplicit false
set_option maxHeartbeats 40000000
open Polynomial RatFunc
open scoped BigOperators
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

/-!
# Step L184: THE SATURATED SUB-CASE — what `psum x k = w` forces

The last open sub-case of the recursion (PLAN SESSION 272) is the SATURATED one: an in-domain
input `x` at level `k` with `psum x k = w` (both prefix sums at the recursion's level and at the
chain's level saturate at the common weight).  This module writes down exactly what that
hypothesis forces, and shows that the committed depth facts then supply everything the `ambNu`
dispatch needs — no separate treatment of the tie is required:

  • ★★★ `depth_eq_of_inDomain_of_saturated` — an in-domain `x` at level `k` with saturated prefix
    sum at `k` has `depth x = k` ("in-domain forces depth `≥ k`": a depth `< k` tuple would have
    all entries real and `≤ q` by `(k−1)`-admissibility, so `¬k`-admissibility could only come from
    the `(·,q)`-form — which `(k−1)`-admissibility already excludes);
  • ★★ `saturated_profile` — the profile at `k`: the entries `x_1..x_k` are `≤ q` and
    `w = psum x k ≤ k·q`;
  • ★★ `ambNu_lt_of_mainkStep3_or` — the UNIFIED member descent: `MainkStep3 k q w x m` plus
    EITHER the strict prefix drop `psum m k < psum x k` OR the depth bound `depth x ≤ depth m`
    gives `ambNu k q w m < ambNu k q w x`.  The drop case is StepL164's `ambNu_lt_of_psum_lt`
    (no depth needed), the depth case StepL181's `ambNu_lt_of_mainkStep3_of_dep_le`;
  • ★★ `saturated_tie_member_desc` — in the saturated case a tie member (`C2′/C3`) whose depth is
    at least `depth x = k` — which is exactly what the committed `*_dep_ge` facts
    (`type1_dep_ge`, `type3_dep_ge`, `type2_dep_gt`, `maink_g5_aSide_dep_ge`,
    `maink_g5_bSide_dep_gt`, `maink_case2_j_type3_dep`) provide for the TIE families — descends
    under `ambNu`.
⇒ the saturated sub-case is CLOSED for the recursion: the recursion's case-(b) (the `¬(k−1)`-adm
members) then goes through the ambient chain port at the member's own `domLevel`, and the
port's `rec` is fed by the IH through the transitivity
`ambNu k m' < ambNu k m < ambNu k x` of `ambNu_lt_of_mainkStep3_or` and the port's own descents
(Steps L165/L172/L173/L175).  The ONLY remaining input is the three ambient chain ports
(G5 `j0`, CASE-2 `j`, CASE-2 `qqq`) — mechanical ports of StepL166's recipe, recorded in PLAN.
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★★★ IN-DOMAIN FORCES DEPTH `≥ k`: if `x` is `(k−1)`-admissible but not `k`-admissible, then
`depth x ≥ k`.  (A depth `< k` tuple cannot be trapped by the `(·,q)`-form at level `k`, since
that same form witnesses non-`(k−1)`-admissibility.) -/
theorem depth_ge_of_inDomain {q k : ℕ} {r : ℕ} (x : Fin r → ℕ+)
    (h1 : kAdmissible q x (k - 1)) (hnot : ¬ kAdmissible q x k) : k ≤ r := by
  by_contra hcon
  push Not at hcon
  -- `¬k`-admissibility: either an entry `> q` below `k`, or the `(·,q)`-form with `r ≤ k`
  have hcases : (∃ i : ℕ, i < k ∧ q < pad0 x i) ∨
      (∃ hr1 : 1 ≤ r, r ≤ k ∧ (∀ y : ℕ, y < r - 1 → pad0 x y ≤ q) ∧
        (x ⟨r - 1, by omega⟩ : ℕ) = q) := by
    by_contra hc
    push Not at hc
    exact hnot ⟨fun y hy => hc.1 y hy, fun hw => hc.2 hw.1 hw.2.1 hw.2.2.1 hw.2.2.2⟩
  rcases hcases with ⟨i, hik, hiq⟩ | ⟨hr1, hrk, hall, hlast⟩
  · -- the offending entry sits at position `k-1`, which does not exist (depth `< k`)
    have hik' : i < k - 1 := by
      by_contra hge
      have hk1 : k - 1 ≤ i := by omega
      have hzero : pad0 x i = 0 := by
        apply pad0_of_ge
        omega
      omega
    exact absurd (h1.1 i hik') (by omega)
  · -- the same `(·,q)`-form witnesses non-`(k−1)`-admissibility
    have hrk' : r ≤ k - 1 := by omega
    refine hnot ⟨?_, ?_⟩
    · intro y hy
      rcases lt_or_ge y (r - 1) with h | h
      · exact hall y h
      · rcases lt_or_ge y r with h2 | h2
        · have hyr : y = r - 1 := by omega
          subst hyr
          rw [pad0_of_lt x (by omega : r - 1 < r), hlast]
        · have hzero : pad0 x y = 0 := pad0_of_ge x h2
          rw [hzero]
          exact Nat.zero_le _
    · rintro ⟨hr1', hrk'', hall'', hlast''⟩
      exact h1.2 ⟨hr1', by omega, hall'', hlast''⟩

/-- ★★★ THE SATURATED CASE FORCES `depth x = k`. -/
theorem depth_eq_of_inDomain_of_saturated {q k w : ℕ} {r : ℕ} (x : Fin r → ℕ+)
    (h1 : kAdmissible q x (k - 1)) (hnot : ¬ kAdmissible q x k)
    (hsat : psum x k = w) (hw : weight r x = w) : r = k := by
  have hge : k ≤ r := depth_ge_of_inDomain x h1 hnot
  have hle : r ≤ k := by
    by_contra hconC
    push Not at hconC
    have hlt : psum x k < weight r x := by
      have h := psum_lt_psum_of_lt x hconC (le_refl r)
      rwa [psum_self] at h
    omega
  omega

/-- ★★ THE SATURATED PROFILE: in the saturated in-domain case the depth is exactly `k`, the
entries `x_1..x_{k−1}` are `≤ q`, and `psum x k = w`.  (Note the entry at position `k−1` may
exceed `q`: that is precisely the CASE-1 shape at the saturated level.) -/
theorem saturated_profile {q k w : ℕ} {r : ℕ} (x : Fin r → ℕ+)
    (h1 : kAdmissible q x (k - 1)) (hnot : ¬ kAdmissible q x k)
    (hsat : psum x k = w) (hw : weight r x = w) :
    r = k ∧ (∀ i : ℕ, i < k - 1 → pad0 x i ≤ q) ∧ psum x k = w :=
  ⟨depth_eq_of_inDomain_of_saturated x h1 hnot hsat hw, fun _ hi => h1.1 _ hi, hsat⟩

/-- ★★ THE UNIFIED MEMBER DESCENT: `MainkStep3` plus EITHER the strict prefix drop at `k` OR the
depth bound `depth x ≤ depth m` decreases `ambNu`. -/
theorem ambNu_lt_of_mainkStep3_or (k q w : ℕ) {r r' : ℕ} (x : Fin r → ℕ+) (m : Fin r' → ℕ+)
    (hxw : weight r x = w) (hmw : weight r' m = w)
    (hstep : MainkStep3 k q w x m)
    (h : psum m k < psum x k ∨ r ≤ r') :
    ambNu k q w m < ambNu k q w x := by
  rcases h with hdrop | hdep
  · exact ambNu_lt_of_psum_lt k q w x m hdrop
  · exact ambNu_lt_of_mainkStep3_of_dep_le k q w x m hxw hmw hdep hstep

/-- ★★ THE SATURATED TIE MEMBER: in the saturated case (`psum x k = w`), a tie member `m`
(`psum m k = psum x k`) whose depth is at least `depth x` — exactly what the committed
`*_dep_ge` facts give for the TIE families — descends under `ambNu`. -/
theorem saturated_tie_member_desc (k q w : ℕ) {r r' : ℕ} (x : Fin r → ℕ+) (m : Fin r' → ℕ+)
    (hxw : weight r x = w) (hmw : weight r' m = w)
    (htie : psum m k = psum x k) (hdep : r ≤ r')
    (hstep : MainkStep3 k q w x m) :
    ambNu k q w m < ambNu k q w x :=
  ambNu_lt_of_mainkStep3_of_dep_le k q w x m hxw hmw hdep hstep

/-- ★★ THE CASE-(b) CLOSURE: given (i) the member's `ambNu` descent and (ii) the ambient chain
port at the member's own `domLevel` (whose `rec` is fed by the induction hypothesis through the
transitivity `ambNu k m' < ambNu k m < ambNu k x`), the member expands at level `k`. -/
theorem maink_case_b_close (k q w : ℕ) {r r' : ℕ} (x : Fin r → ℕ+) (m : Fin r' → ℕ+)
    (hdesc : ambNu k q w m < ambNu k q w x)
    (port : (∀ (rd : ℕ) (d : Fin rd → ℕ+), weight rd d = w →
      ambNu k q w d < ambNu k q w m → ¬ kAdmissible (Nat.card F) d k → AdmExpT F w k d) →
        AdmExpT F w k m)
    (ih : ∀ (rd : ℕ) (d : Fin rd → ℕ+), weight rd d = w →
      ambNu k q w d < ambNu k q w x → ¬ kAdmissible (Nat.card F) d k → AdmExpT F w k d) :
    AdmExpT F w k m :=
  port (fun rd d hd hlt hnot => ih rd d hd (lt_trans hlt hdesc) hnot)

end ZagierHoffmanPositiveChar
