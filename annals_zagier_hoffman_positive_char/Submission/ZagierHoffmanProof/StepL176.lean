import Submission.ZagierHoffmanProof.StepL175
import Submission.ZagierHoffmanProof.StepL128
import Submission.ZagierHoffmanProof.StepL82

set_option autoImplicit false
set_option maxHeartbeats 20000000
open Polynomial RatFunc
open scoped BigOperators
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

/-!
# Step L176: the RESIDUAL-FREE measure bridges for the endgame

Three general-purpose bridges that every surviving assembly of theorem_A's span path
needs, extracted as named lemmas:
  • ★ `lkμ3_lt_of_mainkStep3` — the `MainkStep3` relation strictly decreases the μ3
    measure `(psum·k, M0 − initVal, entry)` (this is the content of StepL128's
    `maink_step3_wf`, previously only available inlined);
  • ★★ `ambNu_lt_of_mainkStep3_of_dep_gt` — the SAME relation strictly decreases the
    AMBIENT measure `ambNu Λ` **whenever the member is strictly deeper**: C1 drops the
    prefix component, and C2′/C3 keep it equal but then the depth component wins.
    (Without the depth hypothesis C2′/C3 need `M0 − initVal`, i.e. μ3, not `ambNu`
    — this is exactly why both measures have to be carried.)
  • ★ `initVal_le_of_initLe` — the NON-STRICT companion of `initVal_lex_lt`:
    `InitLe q s t` (lex-≤ on initial tuples) ⟹ `initVal q w s ≤ initVal q w t`.
    This is the lemma the paper's `Init(s) ≺ (s_1,…,s_{j−1},s_j+1) ⪯ Init(u)` argument
    needs to transfer an `Init`-comparison between DIFFERENT tuples (the tie-case
    residual of PLAN SESSION 271: a tie member `m` with `Init(m) ⪯ Init(c)` for its
    level-`(k−1)` outputs `c` would give `initVal m ≤ initVal c`, hence
    `initVal x < initVal c` from `MainkStep3`'s C2′, and close the recursion).
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★ `MainkStep3` strictly decreases the μ3 measure (named form of the content of
`maink_step3_wf`). -/
lemma lkμ3_lt_of_mainkStep3 (k q w : ℕ) {t u : LkCarrier w}
    (h : MainkStep3 k q w t.1.2 u.1.2) : lkμ3 k q w u < lkμ3 k q w t := by
  rcases h with hlt | ⟨heq, hiv⟩ | ⟨heq, hiv, hdrop⟩
  · exact lkμ3_lt_of_psum_lt k q w hlt
  · exact lkμ3_lt_of_initVal k q w heq hiv
  · exact lkμ3_lt_of_entry k q w heq hiv hdrop

/-- ★★ `MainkStep3` strictly decreases the AMBIENT measure `ambNu Λ`, provided the member
is strictly deeper than the input (which is what the chain's TYPE-2/TYPE-3 `depth` facts
give: `type2_dep_gt`, StepL161, and the CASE-2 `ambNu` steps, StepL175). -/
lemma ambNu_lt_of_mainkStep3_of_dep_gt (k q w : ℕ) {r r' : ℕ} (s : Fin r → ℕ+) (m : Fin r' → ℕ+)
    (hs : r ≤ w) (hm : r' ≤ w) (hdep : r < r') (h : MainkStep3 k q w s m) :
    ambNu k q w m < ambNu k q w s := by
  rcases h with hlt | ⟨heq, hiv⟩ | ⟨heq, hiv, hdrop⟩
  · exact ambNu_lt_of_psum_lt k q w s m hlt
  · rw [ambNu, ambNu, Prod.Lex.lt_iff]
    left
    rw [Prod.Lex.lt_iff]
    right
    constructor
    · exact heq
    · show w - r' < w - r
      omega
  · rw [ambNu, ambNu, Prod.Lex.lt_iff]
    left
    rw [Prod.Lex.lt_iff]
    right
    constructor
    · exact heq
    · show w - r' < w - r
      omega

/-- ★ The non-strict companion of `initVal_lex_lt`. -/
lemma initVal_le_of_initLe (q w : ℕ) {r : ℕ} (s : Fin r → ℕ+) (hs : weight r s = w)
    {m : ℕ} (u : Fin m → ℕ+) (hu : weight m u = w)
    (h : InitLe q s u) : initVal q w s ≤ initVal q w u := by
  rcases h with hlt | heq
  · exact le_of_lt (initVal_lex_lt q w s hs u hu hlt)
  · have : initVal q w s = initVal q w u := by
      dsimp [initVal]
      rw [heq]
    omega

/-- ★★ The RESIDUAL-FREE tie bridge: `c` is strictly below `x` in the μ3-at-`k` measure as
soon as its prefix-`k` sum does not exceed `x`'s and its `Init` datum is strictly larger
(or equal with a drop of the entry at the `Init` length).  In the tie case of the endgame
residual (PLAN SESSION 271) `c` is a level-`(k−1)` output of a tie member `m` of `x`'s
level-`k` chain, so `psum c k ≤ psum m k = psum x k` holds, and the `Init` datum comes from
`MainkStep3`'s C2′/C3 together with the chain's `Init`-extension fact `Init m ⪯ Init c`
(`initVal_le_of_initLe` transfers it). -/
lemma lkμ3_lt_of_psum_le_and_init (k q w : ℕ) {r r'' : ℕ} (x : Fin r → ℕ+) (c : Fin r'' → ℕ+)
    (hxw : weight r x = w) (hcw : weight r'' c = w)
    (hpsum : psum c k ≤ psum x k)
    (hinit : initVal q w x < initVal q w c ∨
      (initVal q w x = initVal q w c ∧
        pad0 c (initLen q c) < pad0 x (initLen q x))) :
    lkμ3 k q w ⟨⟨r'', c⟩, hcw⟩ < lkμ3 k q w ⟨⟨r, x⟩, hxw⟩ := by
  rcases lt_or_eq_of_le hpsum with hlt | heq
  · exact lkμ3_lt_of_psum_lt k q w hlt
  · rcases hinit with hiv | ⟨hiv, hdrop⟩
    · exact lkμ3_lt_of_initVal k q w heq hiv
    · exact lkμ3_lt_of_entry k q w heq hiv.symm hdrop

end ZagierHoffmanPositiveChar
