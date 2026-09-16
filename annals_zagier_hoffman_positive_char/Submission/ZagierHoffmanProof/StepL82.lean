import Submission.ZagierHoffmanProof.StepM3
import Mathlib.Data.List.Lex
set_option autoImplicit false
set_option maxHeartbeats 100000000
open scoped BigOperators
/-!
# Step L82: MAIN(3)@general-w — the level-3 termination core (SESSIONS 235-236)

The level-3 recursion for A(3)@w (every weight-w tuple expands at level 3) is a
well-founded recursion over the weight-w carrier; this module provides its measure,
well-foundedness and recursion principle, plus the in-domain trichotomy, all
sorry-free and F-free.

DESIGN (SESSIONS 235-236; the level-3 mirror of StepL55's l2_induction):
  • the recursion runs on in-domain tuples s (2-adm ∧ ¬3-adm, weight w).  By the
    level-3 Step-1 facts (sessions 231-234: every level-3 Step-1 member of the
    CASE-1 chains at j=1/j=2 and of the CASE-2 chains is 2-admissible — the
    (β)-branch is VACUOUS at level 3), the per-step dispatch needs only:
      3-adm members  → admExpT_self;
      2-adm ∧ ¬3-adm members → the recursion call (Main3Step s m).
  • the dispatch step Main3Step q s m := psum m 3 < psum s 3  ∨
    (psum m 3 = psum s 3 ∧ InitLt q s m)  — type-1/type-2 members give the first
    disjunct (prop212/prop213 prefix-3 STRICT drop), type-3 members give ≤ S with
    Init-growth (split < S / = S).
  • WELL-FOUNDEDNESS (SESSION 236, concrete measure, no Init-rank abstraction):
    μ(s) := (psum s 3, M − 1 − initVal q s) : ℕ ×ₗ ℕ with M := (q+2)^(w+1), where
    initVal q w s := padCode (q+2) (w+1) (initList q s) is the base-(q+2) value of
    the ≤q initial tuple, zero-padded to length w+1 (digits 1..q < q+2; the initial
    tuple has length ≤ depth ≤ w).  Lex descent: prefix-3 drop lowers the first
    coordinate; at equal prefix, InitLt s u gives initVal s < initVal u (padCode is
    order-preserving under List.Lex over the fixed-length zero-padded windows), so
    M − 1 − initVal lowers.  main3_step_wf is Subrelation.wf + InvImage.wf of
    wellFounded_lt on the lex pair.
  • l3_induction: the recursion principle over the weight-w carrier (mirror of
    l2_induction).
  • level3_inDomain_cases: the in-domain trichotomy — a 2-adm ∧ ¬3-adm tuple is
    either a CASE-1 tuple (depth ≥ 3, third entry > q) or the depth-3 form
    (a,b,q) with a,b ≤ q (depth-form witness).

NEXT (the A(3) assembly, mirroring StepL57-80's level-2 path): main3 := the
in-domain handler, by l3_induction with the per-step dispatch:
  CASE-1 (3 ≤ r, q < pad0 s 2): j=1 (s₀<q, s₁=q) / j=2 (s₁<q) prop212_step1 at
    (3, j) → members 2-adm (level3_j{1,2}_type3_twoAdm + the type-1/2 mirrors);
    per member: 3-adm → admExpT_self; ¬3-adm → rec (Main3Step via the prefix-3
    strict drop / ≤ S + Init-growth member facts);
  CASE-2 (r=3, (a,b,q)): b<q → case3_leaf_j2 leaf; b=q∧a<q → (a,q,q) prop213_step1
    at (3,1) members 2-adm + rec; a=b=q → (q,q,q) G5-analogue (open).
  then A(3)@w via the A3_with_main3 scaffold; theorem_A(w) via the StepL54 tail.
  The j=0 all-q-front level-3 G5-analogues ((q,q,s₂>q) in CASE-1, (q,q,q) in
  CASE-2) remain open items (mirror StepL75-80's level-2 G5 chains).
-/

namespace ZagierHoffmanPositiveChar

attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## SESSION 235 — MAIN(3): the level-3 in-domain recursion SKELETON.

GOAL (theorem A's level-3 piece): every in-domain weight-w tuple s
(2-adm ∧ ¬3-adm) expands at level 3:
    main3 (w) (hw0) : ∀ r s (hw : weight r s = w), 2-adm s → ¬3-adm s →
        AdmExpT F w 3 s
INVARIANT: AdmExpT F w 3 s (3-adm weight-w outputs + prefix-ℓ ≤ psum s ℓ orders,
ℓ ≥ 3) — the strengthened (H′₃) the higher levels consume.
DECREASING MEASURE (well-founded dispatch, no (β)-branch — sessions 231-234 closed
it: every level-3 Step-1 member is 2-adm):
    Main3Step q s m := psum m 3 < psum s 3 ∨ (psum m 3 = psum s 3 ∧ InitLt q s m)
  (recursion call s ↦ m must satisfy Main3Step; type-1/2 members give the first
  disjunct (prop212/prop213 psum-3 STRICT drop), type-3 members give psum-3 ≤ S and
  InitLt s u — split < S / = S).
  Well-foundedness: prefix-3 ∈ [0,w] drops finitely often; at each fixed prefix the
  in-domain class is FINITE and the =S calls Init-RISE strictly (type3_Init_gt) —
  terminates.  To be formalized via a longest-chain Init-rank over the finite
  weight-w carrier (the single sorry below).
CASE SKELETON (level-3 in-domain trichotomy, level3_inDomain_cases):
  CASE-1 (q < pad0 s 2): prop212_step1 at (3, j), j = 1 (s₁ = q) / j = 2 (s₁ < q);
     members all 2-adm; 3-adm → admExpT_self; 2-adm∧¬3-adm → recursion IH
     (Main3Step via the prop212 conjuncts).
  CASE-2 (r = 3 ∧ pad0 s 2 = q): s = (a,b,q):
     b < q → the case3_leaf_j2 leaf (both members 3-adm; no recursion);
     b = q ∧ a < q → (a,q,q): prop213_step1 at (3,1); members 2-adm (session 234),
        ¬3-adm members → recursion IH;
     a = b = q → (q,q,q): the level-3 G5-analogue — DEFERRED (sorry).
-/

/-- The carrier of weight-`w` tuples (any depth). -/
abbrev L3Carrier (w : ℕ) := { p : (Σ r : ℕ, Fin r → ℕ+) // weight p.1 p.2 = w }

/-- The level-3 dispatch step: `m` is a recursion call from `s` iff prefix-3 drops
or stays with Init-growth. -/
def Main3Step (q : ℕ) {r : ℕ} (s : Fin r → ℕ+) {r' : ℕ} (m : Fin r' → ℕ+) : Prop :=
  psum m 3 < psum s 3 ∨ (psum m 3 = psum s 3 ∧ InitLt q s m)

/-- From the committed Step-1 member facts (prefix-3 < S or ≤ S with Init-growth)
to the dispatch step. -/
lemma l3_member_step (q : ℕ) {r : ℕ} (s : Fin r → ℕ+) {r' : ℕ} (m : Fin r' → ℕ+)
    (h : psum m 3 < psum s 3 ∨ (psum m 3 ≤ psum s 3 ∧ InitLt q s m)) :
    Main3Step q s m := by
  rcases h with hlt | hrest
  · exact Or.inl hlt
  · rcases hrest with ⟨hle, hinit⟩
    by_cases hlt : psum m 3 < psum s 3
    · exact Or.inl hlt
    · right
      constructor
      · omega
      · exact hinit

/-- The value of the first `W` digits of `xs` (zero-padded beyond), most significant
first: `xs[0]·B^(W−1) + …`. -/
noncomputable def padCode (B : ℕ) : ℕ → List ℕ → ℕ
  | 0, _ => 0
  | W + 1, [] => 0
  | W + 1, a :: t => a * B ^ W + padCode B W t

lemma padCode_nil (B : ℕ) (W : ℕ) : padCode B W [] = 0 := by
  induction W with
  | zero => rfl
  | succ W ih => rfl

/-- Digits ≤ q and B ≥ q+2: the code of any `W`-digit window is < B^W. -/
lemma padCode_lt_pow (B q : ℕ) (hB : q + 2 ≤ B) :
    ∀ (W : ℕ) (xs : List ℕ), (∀ v ∈ xs, v ≤ q) → padCode B W xs < B ^ W := by
  intro W
  induction W with
  | zero =>
      intro xs hd
      simp [padCode]
  | succ W ih =>
      intro xs hd
      have hBpos : 0 < B := by omega
      cases xs with
      | nil =>
          rw [padCode_nil]
          exact Nat.pow_pos hBpos
      | cons a t =>
          have ha : a ≤ q := hd a (by simp)
          have htail := ih t (fun v hv => hd v (by simp [hv]))
          have hBpow : 0 < B ^ W := Nat.pow_pos hBpos
          have htail' : padCode B W t ≤ B ^ W - 1 := Nat.le_sub_one_of_lt htail
          calc
            padCode B (W + 1) (a :: t) = a * B ^ W + padCode B W t := rfl
            _ ≤ q * B ^ W + padCode B W t := by
                  exact Nat.add_le_add_right (Nat.mul_le_mul_right (B ^ W) ha) (padCode B W t)
            _ ≤ q * B ^ W + (B ^ W - 1) := by
                  exact Nat.add_le_add_left htail' (q * B ^ W)
            _ ≤ (q + 1) * B ^ W := by
                  have hsub : B ^ W - 1 ≤ B ^ W := Nat.sub_le (B ^ W) 1
                  have h1 : q * B ^ W + (B ^ W - 1) ≤ q * B ^ W + B ^ W := by
                    exact Nat.add_le_add_left hsub (q * B ^ W)
                  have h2 : q * B ^ W + B ^ W = (q + 1) * B ^ W := by ring
                  rw [← h2]
                  exact h1
            _ < (q + 2) * B ^ W := by
                  exact Nat.mul_lt_mul_of_pos_right (by omega : q + 1 < q + 2) hBpow
            _ ≤ B * B ^ W := by
                  exact Nat.mul_le_mul_right (B ^ W) hB
            _ = B ^ (W + 1) := by
                  have hps := (Nat.pow_succ B W).symm
                  rw [Nat.mul_comm]
                  exact hps

/-- Order preservation (∀-W form): full lists (length ≤ W), digits in [1,q] ⟹
`Lex (<) xs ys` gives the padded code smaller. -/
lemma padCode_lex_lt_core (B q : ℕ) (hB : q + 2 ≤ B) :
    ∀ {xs ys : List ℕ}, List.Lex (fun a b : ℕ => a < b) xs ys →
      ∀ (W : ℕ), xs.length ≤ W → ys.length ≤ W →
        (∀ v ∈ xs, 1 ≤ v) → (∀ v ∈ ys, 1 ≤ v) →
        (∀ v ∈ xs, v ≤ q) → (∀ v ∈ ys, v ≤ q) →
        padCode B W xs < padCode B W ys := by
  intro xs ys hlex
  refine List.Lex.recOn hlex
    (motive := fun as bs _ => ∀ (W : ℕ), as.length ≤ W → bs.length ≤ W →
      (∀ v ∈ as, 1 ≤ v) → (∀ v ∈ bs, 1 ≤ v) →
      (∀ v ∈ as, v ≤ q) → (∀ v ∈ bs, v ≤ q) →
      padCode B W as < padCode B W bs) ?nil ?rel ?cons
  · -- nil: [] < (a :: l)
    intro a l W hlenx hleny hposx hposy hqx hqy
    have hleny' : 1 ≤ W := by
      have hl : (a :: l).length = l.length + 1 := rfl
      rw [hl] at hleny
      omega
    have ha : 1 ≤ a := hposy a (by simp)
    have hpow : 0 < B ^ (W - 1) := Nat.pow_pos (by omega : 0 < B)
    have haB : 1 * B ^ (W - 1) ≤ a * B ^ (W - 1) := Nat.mul_le_mul_right (B ^ (W - 1)) ha
    have hcode : 1 ≤ a * B ^ (W - 1) + padCode B (W - 1) l := by
      have h1 : 1 ≤ a * B ^ (W - 1) := by
        have hpow1 : 1 ≤ B ^ (W - 1) := hpow
        have hm : (1 : ℕ) * 1 ≤ a * B ^ (W - 1) := Nat.mul_le_mul ha hpow1
        simpa using hm
      omega
    rw [padCode_nil]
    have hW : W = (W - 1) + 1 := by omega
    rw [hW]
    change 0 < a * B ^ (W - 1) + padCode B (W - 1) l
    exact lt_of_lt_of_le Nat.zero_lt_one hcode
  · -- rel: a₁ < a₂
    intro a₁ l₁ a₂ l₂ ha W hlenx hleny hposx hposy hqx hqy
    have hltail₁ : padCode B (W - 1) l₁ < B ^ (W - 1) := by
      apply padCode_lt_pow B q hB (W - 1) l₁
      intro v hv
      exact hqx v (by simp [hv])
    have hBpow : 0 < B ^ (W - 1) := Nat.pow_pos (by omega : 0 < B)
    have hltail₁' : padCode B (W - 1) l₁ ≤ B ^ (W - 1) - 1 := Nat.le_sub_one_of_lt hltail₁
    have hW1 : 1 ≤ W := by
      have hl : (a₁ :: l₁).length = l₁.length + 1 := rfl
      rw [hl] at hlenx
      omega
    have hW : W = (W - 1) + 1 := by omega
    have hcodex : padCode B W (a₁ :: l₁) = a₁ * B ^ (W - 1) + padCode B (W - 1) l₁ := by
      rw [hW]
      rfl
    have hcodey : padCode B W (a₂ :: l₂) = a₂ * B ^ (W - 1) + padCode B (W - 1) l₂ := by
      rw [hW]
      rfl
    rw [hcodex, hcodey]
    have hcore : a₁ * B ^ (W - 1) + padCode B (W - 1) l₁ < a₂ * B ^ (W - 1) := by
      have h1 : a₁ * B ^ (W - 1) + padCode B (W - 1) l₁ ≤ a₁ * B ^ (W - 1) + (B ^ (W - 1) - 1) := by
        exact Nat.add_le_add_left hltail₁' (a₁ * B ^ (W - 1))
      have h12 : a₁ * B ^ (W - 1) + (B ^ (W - 1) - 1) < (a₁ + 1) * B ^ (W - 1) := by
        have hsub : B ^ (W - 1) - 1 < B ^ (W - 1) := Nat.sub_lt hBpow (by norm_num)
        have hlt : a₁ * B ^ (W - 1) + (B ^ (W - 1) - 1) < a₁ * B ^ (W - 1) + B ^ (W - 1) :=
          Nat.add_lt_add_left hsub (a₁ * B ^ (W - 1))
        have hm : a₁ * B ^ (W - 1) + B ^ (W - 1) = (a₁ + 1) * B ^ (W - 1) := by ring
        rw [← hm]
        exact hlt
      have h23 : (a₁ + 1) * B ^ (W - 1) ≤ a₂ * B ^ (W - 1) := by
        have ha12 : a₁ + 1 ≤ a₂ := by omega
        exact Nat.mul_le_mul_right (B ^ (W - 1)) ha12
      exact Nat.lt_of_le_of_lt h1 (Nat.lt_of_lt_of_le h12 h23)
    exact Nat.lt_of_lt_of_le hcore (Nat.le_add_right (a₂ * B ^ (W - 1)) (padCode B (W - 1) l₂))
  · -- cons: equal head, recurse into tails
    intro a l₁ l₂ hlex' hrec W hlenx hleny hposx hposy hqx hqy
    have hW1 : 1 ≤ W := by
      have hl : (a :: l₁).length = l₁.length + 1 := rfl
      rw [hl] at hlenx
      omega
    have hlen₁ : l₁.length ≤ W - 1 := by
      have hl : (a :: l₁).length = l₁.length + 1 := rfl
      rw [hl] at hlenx
      omega
    have hlen₂ : l₂.length ≤ W - 1 := by
      have hl : (a :: l₂).length = l₂.length + 1 := rfl
      rw [hl] at hleny
      omega
    have hrec' := hrec (W - 1) hlen₁ hlen₂
      (fun v hv => hposx v (by simp [hv])) (fun v hv => hposy v (by simp [hv]))
      (fun v hv => hqx v (by simp [hv])) (fun v hv => hqy v (by simp [hv]))
    have hW : W = (W - 1) + 1 := by omega
    have hcodex : padCode B W (a :: l₁) = a * B ^ (W - 1) + padCode B (W - 1) l₁ := by
      rw [hW]
      rfl
    have hcodey : padCode B W (a :: l₂) = a * B ^ (W - 1) + padCode B (W - 1) l₂ := by
      rw [hW]
      rfl
    rw [hcodex, hcodey]
    exact Nat.add_lt_add_left hrec' (a * B ^ (W - 1))

/-- The ≤q-prefix is a sublist: its members belong to the original list. -/
lemma initListAux_mem_of_mem {q : ℕ} : ∀ (l : List ℕ),
    ∀ v ∈ initListAux q l, v ∈ l := by
  intro l
  induction l with
  | nil => intro v hv; simp [initListAux] at hv
  | cons a t ih =>
      intro v hv
      by_cases ha : a ≤ q
      · rw [initListAux_cons_le q a t ha] at hv
        simp at hv
        rcases hv with rfl | hv
        · simp
        · have hvt : v ∈ t := ih v hv
          simp [hvt]
      · have hgt : q < a := lt_of_not_ge ha
        rw [initListAux_cons_gt q a t hgt] at hv
        simp at hv

/-- Members of the initial tuple are ≥ 1 (they are tuple values). -/
lemma initList_mem_pos {r : ℕ} (q : ℕ) (s : Fin r → ℕ+) :
    ∀ v ∈ initList q s, 1 ≤ v := by
  intro v hv
  have hvl : v ∈ valueList s := by
    simpa [initList] using (initListAux_mem_of_mem (valueList s) v hv)
  -- valueList membership ⟹ v = (s ⟨i,·⟩ : ℕ) ≥ 1
  simp [valueList] at hvl
  rcases hvl with ⟨i, rfl⟩
  exact (s i).pos

/-- The length of the initial tuple is ≤ w for a weight-`w` tuple. -/
lemma initLen_le_weight {r : ℕ} (q : ℕ) (s : Fin r → ℕ+) (w : ℕ) (hw : weight r s = w) :
    initLen q s ≤ w := by
  have h1 := initLen_le q s
  have h2 : r ≤ weight r s := weight_ge_depth r s
  omega

/-- The base-(q+2) code of the initial tuple of a weight-`w` tuple, padded to w+1. -/
noncomputable def initVal (q : ℕ) (w : ℕ) {r : ℕ} (s : Fin r → ℕ+) : ℕ :=
  padCode (q + 2) (w + 1) (initList q s)

/-- initVal < (q+2)^(w+1). -/
lemma initVal_lt_pow (q w : ℕ) {r : ℕ} (s : Fin r → ℕ+) (hw : weight r s = w) :
    initVal q w s < (q + 2) ^ (w + 1) := by
  dsimp [initVal]
  exact padCode_lt_pow (q + 2) q (by omega) (w + 1) (initList q s) (initList_mem_le q s)

/-- Order preservation: InitLt (init-list lex) ⟹ initVal is smaller. -/
lemma initVal_lex_lt (q w : ℕ) {r : ℕ} (s : Fin r → ℕ+) (hs : weight r s = w)
    {m : ℕ} (u : Fin m → ℕ+) (hu : weight m u = w)
    (hlex : InitLt q s u) : initVal q w s < initVal q w u := by
  dsimp [initVal, InitLt] at hlex ⊢
  have hlen1 : (initList q s).length ≤ w + 1 := by
    have hl := initLen_le_weight q s w hs
    change (initList q s).length ≤ w at hl
    omega
  have hlen2 : (initList q u).length ≤ w + 1 := by
    have hl := initLen_le_weight q u w hu
    change (initList q u).length ≤ w at hl
    omega
  exact padCode_lex_lt_core (q + 2) q (by omega)
    (xs := initList q s) (ys := initList q u) hlex (w + 1) hlen1 hlen2
    (initList_mem_pos q s) (initList_mem_pos q u)
    (initList_mem_le q s) (initList_mem_le q u)

/-- The measure: (psum-3, M − 1 − initVal), M = (q+2)^(w+1), in the lex product. -/
noncomputable def l3μ (q w : ℕ) (t : L3Carrier w) : ℕ ×ₗ ℕ :=
  (psum t.1.2 3, (q + 2) ^ (w + 1) - 1 - initVal q w t.1.2)

/-- Prefix-3 drop ⟹ measure drop (first coordinate). -/
lemma l3μ_lt_of_psum_lt (q w : ℕ) {t u : L3Carrier w}
    (h : psum u.1.2 3 < psum t.1.2 3) : l3μ q w u < l3μ q w t := by
  rw [Prod.Lex.lt_iff]
  left
  exact h

/-- Equal prefix + Init-growth ⟹ measure drop (second coordinate). -/
lemma l3μ_lt_of_psum_eq_initLt (q w : ℕ) {t u : L3Carrier w}
    (heq : psum u.1.2 3 = psum t.1.2 3) (hlex : InitLt q t.1.2 u.1.2) :
    l3μ q w u < l3μ q w t := by
  rw [Prod.Lex.lt_iff]
  right
  constructor
  · exact heq
  · have hiv : initVal q w t.1.2 < initVal q w u.1.2 := initVal_lex_lt q w t.1.2 t.2 u.1.2 u.2 hlex
    have hMt : initVal q w t.1.2 < (q + 2) ^ (w + 1) := initVal_lt_pow q w t.1.2 t.2
    have hMu : initVal q w u.1.2 < (q + 2) ^ (w + 1) := initVal_lt_pow q w u.1.2 u.2
    have hivM1 : initVal q w t.1.2 < (q + 2) ^ (w + 1) - 1 := by
      have hle : initVal q w u.1.2 ≤ (q + 2) ^ (w + 1) - 1 := Nat.le_sub_one_of_lt hMu
      omega
    dsimp [l3μ]
    exact Nat.sub_lt_sub_left hivM1 hiv

/-- ★ Well-foundedness of the level-3 dispatch. -/
theorem main3_step_wf (q w : ℕ) :
    WellFounded (fun m s : L3Carrier w => Main3Step q s.1.2 m.1.2) := by
  refine Subrelation.wf ?_ (InvImage.wf (l3μ q w) wellFounded_lt)
  intro m s h
  rcases h with hlt | heq
  · exact l3μ_lt_of_psum_lt q w hlt
  · exact l3μ_lt_of_psum_eq_initLt q w heq.1 heq.2

/-- ★ The level-3 recursion principle: `P` holds for every weight-`w` tuple if each
step `P(s)` follows from `P` on dispatch-calls `m` (Main3Step s m). -/
theorem l3_induction (q w : ℕ) (hwf : WellFounded (fun m s : L3Carrier w => Main3Step q s.1.2 m.1.2))
    (P : (r : ℕ) → (s : Fin r → ℕ+) → weight r s = w → Prop)
    (hstep : ∀ (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w),
      (∀ (r' : ℕ) (m : Fin r' → ℕ+) (hm : weight r' m = w),
          Main3Step q s m → P r' m hm) → P r s hw) :
    ∀ (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w), P r s hw := by
  classical
  let Q : L3Carrier w → Prop := fun t => P t.1.1 t.1.2 t.2
  have hfix : ∀ t : L3Carrier w, Q t := by
    exact WellFounded.fix hwf (fun t ih => by
      dsimp [Q]
      refine hstep t.1.1 t.1.2 t.2 ?_
      intro r' m hm hstepm
      exact ih ⟨⟨r', m⟩, hm⟩ hstepm)
  intro r s hw
  exact hfix ⟨⟨r, s⟩, hw⟩

/-- The level-3 in-domain trichotomy: a 2-adm ∧ ¬3-adm tuple (q ≥ 2) is either a
CASE-1 tuple (depth ≥ 3, third entry > q) or the depth-3 form (a,b,q) with a,b ≤ q. -/
lemma level3_inDomain_cases (q : ℕ) (hq : 2 ≤ q) {r : ℕ} (s : Fin r → ℕ+)
    (h2 : kAdmissible q s 2) (hn3 : ¬ kAdmissible q s 3) :
    (3 ≤ r ∧ q < pad0 s 2) ∨ (r = 3 ∧ (∀ x : ℕ, x < 2 → pad0 s x ≤ q) ∧ pad0 s 2 = q) := by
  classical
  have hdg : 3 ≤ r := depth_ge_of_not_adm q s (by omega : 1 ≤ 3) h2 hn3
  by_cases hA3 : ∀ x : ℕ, x < 3 → pad0 s x ≤ q
  · -- cond1 at level 3 holds: ¬3-adm forces the depth-form witness
    have hw : ∃ hr1 : 1 ≤ r,
        r ≤ 3 ∧ (∀ x : ℕ, x < r - 1 → pad0 s x ≤ q) ∧ (s ⟨r - 1, by omega⟩ : ℕ) = q := by
      by_contra hw'
      apply hn3
      exact ⟨hA3, hw'⟩
    rcases hw with ⟨hr1, hr3w, hall, hlast⟩
    right
    have hr3 : r = 3 := by omega
    refine ⟨hr3, ?_, ?_⟩
    · intro x hx
      exact h2.1 x (by omega)
    · subst r
      have hp2v : pad0 s 2 = (s ⟨2, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 2 < 3)
      rw [hp2v]
      exact hlast
  · push_neg at hA3
    rcases hA3 with ⟨x, hx3, hgt⟩
    have hx2 : x = 2 := by
      have hx02 : x = 0 ∨ x = 1 ∨ x = 2 := by omega
      rcases hx02 with hx0 | hx1 | hx2
      · subst x
        have h0 : pad0 s 0 ≤ q := h2.1 0 (by omega)
        omega
      · subst x
        have h1 : pad0 s 1 ≤ q := h2.1 1 (by omega)
        omega
      · exact hx2
    subst x
    left
    exact ⟨hdg, hgt⟩

