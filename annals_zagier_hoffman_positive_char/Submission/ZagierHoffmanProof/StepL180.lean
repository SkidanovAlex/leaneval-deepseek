import Submission.ZagierHoffmanProof.StepL179

set_option autoImplicit false
set_option maxHeartbeats 40000000
open Polynomial RatFunc
open scoped BigOperators
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

/-!
# Step L180: the NO-SATURATION machinery — pruning the tie residual down to ONE sub-case

`StepL179` reduced the theorem_A span endgame to the `Init`-transference data of the tie case
(`lkμ3_lt_of_tie_member`), i.e. to the CHAIN TIE FACTS at the recursion's tie level `k`:
for every member `m` of a chain with `psum m k = psum s k`, `initVal s ≤ initVal m`.
StepL178 proves them for the TYPE-1 / TYPE-3 families at ANY level (`InitLe`/`InitLt`), and
shows the strict-drop families (`type2_psum_ge_k_lt` etc.) strictly drop on `[k, r]`
(`r` = the input's depth) — so at levels `k ≤ r` their tie facts are VACUOUS.

This module supplies the missing bookkeeping that makes the vacuity argument usable at the
AMBIENT tie level of the recursion:
  • ★ `lt_depth_of_psum_lt_weight` — `psum t k < w` forces `k < depth t` (otherwise the prefix
    sum saturates at the weight);
  • ★★ `depth_gt_of_tie_of_no_saturation` — if the TOP input `x` is not saturated at `k`
    (`k < depth x`, i.e. `psum x k < w`), then EVERY tuple of weight `w` tying with `x` at level
    `k` also has depth `> k`;
  • ★ `tie_fact_of_strict` — the vacuous discharge pattern of the chain tie facts;
  • ★★ `tie_fact_of_strict_on_range` — the GENERAL chain tie fact: any tuple whose prefix sums
    strictly drop on `[k, r]` satisfies the tie fact at every level in `[k, r]`.
CONSEQUENCE (the pruning): inside the recursion at level `k`, once the top input `x` is
NON-SATURATED at `k` (`k < depth x`, the generic case), every intermediate tuple appearing in
the `H(k−1)` refinement of a tie member has depth `> k` as well, so all the strict-drop
families of all the relevant chains strictly drop at `k` and their tie facts are vacuous;
the ONLY families whose tie facts are then needed are TYPE-1/TYPE-3, which StepL178 supplies at
any level.  The remaining (hard) sub-case is therefore exactly the SATURATED one
(`psum x k = w`, i.e. the `(·,q)`-form CASE-2 shape), where an intermediate input of depth
`< k` can occur — recorded in PLAN SESSION 272.
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★ If the prefix-`k` sum is below the weight, then the depth exceeds `k` (otherwise the
prefix sum saturates at the weight). -/
lemma lt_depth_of_psum_lt_weight {r : ℕ} (t : Fin r → ℕ+) {k w : ℕ}
    (hw : weight r t = w) (h : psum t k < w) : k < r := by
  by_contra hcon
  push Not at hcon
  have hsat : psum t k = weight r t := psum_ge_depth t hcon
  omega

/-- ★ `psum t k < weight` is equivalent to non-saturation at `k`. -/
lemma psum_lt_weight_iff_lt_depth {r : ℕ} (t : Fin r → ℕ+) {k : ℕ} :
    psum t k < weight r t ↔ k < r := by
  constructor
  · intro h
    exact lt_depth_of_psum_lt_weight t rfl h
  · intro h
    have h1 := psum_lt_psum_of_lt t h (le_refl r)
    rwa [psum_self] at h1

/-- ★★ NO-SATURATION ⇒ DEEPER: if the input `x` is not saturated at `k` (`k < depth x`), then
every weight-`w` tuple tying with `x` at level `k` has depth `> k`. -/
lemma depth_gt_of_tie_of_no_saturation {rx : ℕ} (x : Fin rx → ℕ+) {k w : ℕ}
    (hxw : weight rx x = w) (hx : k < rx)
    {rd : ℕ} (d : Fin rd → ℕ+) (hdw : weight rd d = w)
    (htie : psum d k = psum x k) : k < rd := by
  refine lt_depth_of_psum_lt_weight d hdw ?_
  rw [htie, ← hxw]
  exact (psum_lt_weight_iff_lt_depth x).mpr hx

/-- ★ The vacuous discharge of a chain tie fact from a STRICT drop at the tie level. -/
lemma tie_fact_of_strict {rs : ℕ} (s : Fin rs → ℕ+) {rm : ℕ} (m : Fin rm → ℕ+) {k w : ℕ}
    (h : psum m k < psum s k) : psum m k = psum s k → initVal (Nat.card F) w s ≤ initVal (Nat.card F) w m := by
  intro hcon
  exact absurd hcon (ne_of_lt h)

/-- ★★ THE GENERAL CHAIN TIE FACT: a tuple whose prefix sums strictly drop below the input's on
the whole range `[k, r]` satisfies the tie fact at EVERY level of that range. -/
lemma tie_fact_of_strict_on_range {rs : ℕ} (s : Fin rs → ℕ+) {rm : ℕ} (m : Fin rm → ℕ+)
    {k r w : ℕ} (hstrict : ∀ ℓ : ℕ, k ≤ ℓ → ℓ ≤ r → psum m ℓ < psum s ℓ) :
    ∀ (Λ : ℕ), k ≤ Λ → Λ ≤ r →
      (psum m Λ = psum s Λ → initVal (Nat.card F) w s ≤ initVal (Nat.card F) w m) := by
  intro Λ hkΛ hΛr
  exact tie_fact_of_strict F s m (hstrict Λ hkΛ hΛr)

/-- ★★ The pruning of the tie residual: in the non-saturated case (`k < depth x`) every
intermediate tuple `t` of weight `w` lying under a tie with `x` at level `k` also satisfies
`k < depth t` — hence every chain whose input is such a `t` has its strict-drop families
STRICTLY dropping at the tie level `k` (their strictness ranges are `[level, depth]`), so their
chain tie facts are vacuous and only the TYPE-1/TYPE-3 families (StepL178) contribute. -/
theorem tie_intermediate_depth_gt {rx : ℕ} (x : Fin rx → ℕ+) {k w : ℕ}
    (hxw : weight rx x = w) (hx : k < rx)
    {rt : ℕ} (t : Fin rt → ℕ+) (htw : weight rt t = w)
    (htie : psum t k = psum x k) : k < rt :=
  depth_gt_of_tie_of_no_saturation x hxw hx t htw htie

end ZagierHoffmanPositiveChar
