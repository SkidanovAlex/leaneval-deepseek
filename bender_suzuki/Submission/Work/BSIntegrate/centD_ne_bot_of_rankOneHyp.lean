import Mathlib
import Submission.Work.ThmG.Defs
import Submission.Work.BSIntegrate.geometry.exists_conj_elt_of_not_zassenhaus
import Submission.Work.BSIntegrate.Order.exists_involution_of_centralizes_oddPart
import Submission.Work.BSIntegrate.Count.Kset_eq_twoPoint_of_centD_eq_bot
import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.Bender.DTransitiveInv

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `V = C_D(t) ≠ 1` from the rank-one hypotheses

Peterfalvi II, Ch. II §4 Prop. 2 (b) with p. 236 (the "easy" direction of
"`G` is a Zassenhaus group iff `V = C_D(t) = 1`"), in the *unconditional* form used by
Theorem G: in the split rank-one situation `H = Q ⋊ D`, `D = H ∩ Hᵗ = twoPoint H t`,
`t ∉ H` an involution, `G` simple in situation (B0)–(B2) and **not** Zassenhaus, the
centraliser

`V = C_D(t) = centD H t = twoPoint H t ⊓ C_G(t)`

is non-trivial.

The area theorem `Work.PSU3.StageA.centD_ne_bot` proves this under the extra hypothesis that
`Q` is a `2`-group (the `PSU₃` case).  Here `Q` is arbitrary; the missing input is supplied by
Peterfalvi Ch. V §2 Lemma 2 c, i.e. by `FpfOddPartProp`: `D` acts fixed-point-freely on
`Q₁ = O_{2'}(Q)`.  That is exactly why the hypothesis `hFpf` occurs below.

## The proof

Let `Ω = G ⧸ H`, `∞ = H`, `D = H ∩ Hᵗ` the stabiliser of the two points `∞` and `t • ∞`.

1. **Geometry** (`Work.BSIntegrate.geometry.exists_conj_elt_of_not_zassenhaus`).
   `¬ IsZassenhaus H` produces three distinct points of `Ω` and `g ≠ 1` fixing all three; by
   2-transitivity we may take the first two to be `∞` and `t • ∞`, so that `d = x g x⁻¹ ≠ 1`
   lies in `D` and fixes a third point `c' ∉ {∞, t • ∞}`.  Since `H = Q ⋊ D` acts transitively
   on `Ω ∖ {∞}` and `D` fixes `t • ∞`, `c' = q • (t • ∞)` for some `q ∈ Q ∖ {1}`; and `Q` acts
   regularly on `Ω ∖ {∞}`, so `d q d⁻¹ = q`.
2. **Order splitting** (`Work.BSIntegrate.Order.exists_involution_of_centralizes_oddPart`).
   `d` centralises `q := q₀ ∈ Q ∖ {1}`.  If `orderOf q` were odd then `q ∈ O_{2'}(Q)` and
   fixed-point-freeness of `d` would force `q = 1`; hence `orderOf q = 2m` and
   `u := q ^ m ∈ Q` is an involution with `d u d⁻¹ = u`.
3. **Counting** (`Work.BSIntegrate.Count.Kset_eq_twoPoint_of_centD_eq_bot`).
   If `V = centD H t = ⊥`, then — `t` normalising `D` of odd order and acting fixed-point-freely
   modulo `D ⊓ C_G(t)` — every `x ∈ D` is inverted by `t`, i.e. `K = J(D,t) ⊆ D` is all of `D`.
4. **Endgame** (below).  But then `d ∈ K` and `1 ∈ K`, and Ch. I §2 Lemma 1
   (`Kset_conj_injective`) says that `x ↦ x u x⁻¹` is injective on `K`, while both `d` and `1`
   map to `u`.  Hence `d = 1`, contradicting step 1.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

open Classical
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.BSIntegrate

/-! ## The counting endgame -/

/-- **Endgame.**  A non-identity `d ∈ D` centralising an involution `u ∈ H` contradicts
`V = C_D(t) = ⊥`: by `Work.BSIntegrate.Count.Kset_eq_twoPoint_of_centD_eq_bot` we have
`K = J(D,t) = D`, so `d ∈ K` and `1 ∈ K`, while `x ↦ x u x⁻¹` is injective on `K` and both `d`
and `1` are mapped to `u`. -/
private theorem false_of_centD_eq_bot_aux {G : Type*} [Group G] [Finite G]
    {H Q : Subgroup G} {t : G} (h : Submission.Blueprint.IsSplitRankOne H Q t)
    {d u : G} (hd : d ∈ Submission.Blueprint.twoPoint H t) (hd1 : d ≠ 1)
    (huH : u ∈ H) (hu2 : orderOf u = 2) (hdu : d * u * d⁻¹ = u)
    (hV : Submission.Blueprint.centD H t = ⊥) : False := by
  classical
  have hH : IsStronglyEmbedded H := h.stronglyEmbedded
  have htH : t ∉ H := h.not_mem
  -- `V = 1` forces `K = J(D,t)` to be all of `D`
  have hKeq : Work.ThmF.Kset H t = (Submission.Blueprint.twoPoint H t : Set G) :=
    Work.BSIntegrate.Count.Kset_eq_twoPoint_of_centD_eq_bot h hV
  have hdK : d ∈ Work.ThmF.Kset H t := by rw [hKeq]; exact hd
  have h1K : (1 : G) ∈ Work.ThmF.Kset H t := Work.ThmF.one_mem_Kset H t
  -- `x ↦ x u x⁻¹` is injective on `K`, and `d`, `1` have the same image
  have hinj := Work.ThmF.Bender.Kset_conj_injective hH h.invol htH huH hu2
  have himg : d * u * d⁻¹ = 1 * u * 1⁻¹ := by
    rw [one_mul, inv_one, mul_one]
    exact hdu
  exact hd1 (hinj hdK h1K himg)

/-! ## The statement -/

theorem centD_ne_bot_of_rankOneHyp (hFpf : Work.ThmG.FpfOddPartProp) {G : Type} [Group G] [Fintype G] {H Q : Subgroup G} {t : G} (hh : Work.ThmG.RankOneHyp G H Q t) : Submission.Blueprint.centD H t ≠ ⊥ := by
  intro hV
  have hsplit : Submission.Blueprint.IsSplitRankOne H Q t := hh.2.2.1
  have hz : ¬ Submission.Blueprint.IsZassenhaus H := hh.2.2.2.1
  -- a non-identity `d ∈ D` commuting with some `1 ≠ q ∈ Q`
  obtain ⟨d, hdD, hd1, q, hqQ, hq1, hdq⟩ :=
    Work.BSIntegrate.geometry.exists_conj_elt_of_not_zassenhaus hsplit hz
  -- a `d`-centralised involution `u ∈ Q ⊆ H`
  have hfpf := hFpf G H Q t hh d hdD hd1
  obtain ⟨u, huQ, hu2, hdu⟩ :=
    Work.BSIntegrate.Order.exists_involution_of_centralizes_oddPart hfpf hqQ hq1 hdq
  exact false_of_centD_eq_bot_aux hsplit hdD hd1 (hsplit.le huQ) hu2 hdu hV

end Work.BSIntegrate
