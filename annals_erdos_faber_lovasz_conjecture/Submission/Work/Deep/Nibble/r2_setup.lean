import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.nibble_defs
import Submission.Work.Deep.Reed.Prob.Product
import Submission.Work.Deep.Reed.Prob.pi_prob_inter_eq_mul_of_disjoint
import Submission.Work.Deep.Reed.Prob.pi_uniform_prob_box
import Submission.Work.Deep.Reed.Prob.Expectation

/-!
# One round of the Rödl nibble: setup

The probability space (each edge of `𝓖` is kept independently with probability `p`) and the
combinatorial bookkeeping for the round-2 statement `Work.Deep.Nibble.nibble_round2`.

The coordinates of the space `𝓖 → Bool` are the edges of `𝓖`; `ω e = true` means that `e` is
kept.  Everything in this file is `sorry`-free and is meant to be imported by the lemmas
proved for the round-2 statement.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped BigOperators

namespace Work.Deep.Nibble

open Work.Deep.Reed

/-- The Bernoulli distribution on `Bool`: `true` has probability `p`. -/
noncomputable def boolProb (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : FinProb Bool where
  wt b := if b then p else 1 - p
  wt_nonneg b := by
    cases b with
    | true => simpa using h0
    | false => simp only [Bool.false_eq_true, if_false]; linarith
  wt_sum := by
    rw [Fintype.sum_bool]
    simp

@[simp] lemma boolProb_wt_true (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    (boolProb p h0 h1).wt true = p := by simp [boolProb]

@[simp] lemma boolProb_wt_false (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    (boolProb p h0 h1).wt false = 1 - p := by simp [boolProb]

lemma boolProb_wt_le_one (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (b : Bool) :
    (boolProb p h0 h1).wt b ≤ 1 := by
  cases b <;> simp [h0, h1]

lemma boolProb_prob_singleton (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (b : Bool) :
    (boolProb p h0 h1).prob {b} = (boolProb p h0 h1).wt b := by
  classical
  rw [FinProb.prob, Fintype.sum_bool]
  cases b <;> simp

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (𝓖 : Set (Set V))

noncomputable instance instFintypeSubtypeEdges : Fintype 𝓖 := Fintype.ofFinite 𝓖

noncomputable instance instDecidableEqSubtypeEdges : DecidableEq 𝓖 := Classical.decEq 𝓖

/-- **The measure of one round**: the edges of `𝓖` are kept independently with probability `p`. -/
noncomputable def edgeMeasure (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : FinProb (𝓖 → Bool) :=
  FinProb.pi (fun _ : 𝓖 => boolProb p h0 h1)

lemma edgeMeasure_wt (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (ω : 𝓖 → Bool) :
    (edgeMeasure 𝓖 p h0 h1).wt ω = ∏ e : 𝓖, (if ω e then p else 1 - p) := rfl

/-- **The probability of a box**: prescribing which values a finite set of coordinates takes. -/
lemma edgeMeasure_prob_box (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (S : Finset 𝓖)
    (A : 𝓖 → Finset Bool) :
    (edgeMeasure 𝓖 p h0 h1).prob {ω : 𝓖 → Bool | ∀ e ∈ S, ω e ∈ A e}
      = ∏ e ∈ S, (boolProb p h0 h1).prob {c : Bool | c ∈ A e} := by
  rw [edgeMeasure, Prob.pi_prob_box_finset]

/-- Prescribing the kept status of a finite set of edges. -/
lemma edgeMeasure_prob_box' (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (S : Finset 𝓖)
    (b : 𝓖 → Bool) :
    (edgeMeasure 𝓖 p h0 h1).prob {ω : 𝓖 → Bool | ∀ e ∈ S, ω e = b e}
      = ∏ e ∈ S, (if b e then p else 1 - p) := by
  classical
  have hset : {ω : 𝓖 → Bool | ∀ e ∈ S, ω e = b e}
      = {ω : 𝓖 → Bool | ∀ e ∈ S, ω e ∈ (fun e : 𝓖 =>
          (if b e then ({true} : Finset Bool) else {false})) e} := by
    ext ω
    constructor
    · intro h e he
      rw [h e he]
      cases hb : b e <;> simp [hb]
    · intro h e he
      have := h e he
      cases hb : b e
      · simp [hb] at this; exact this
      · simp [hb] at this; exact this
  rw [hset, edgeMeasure_prob_box]
  refine Finset.prod_congr rfl fun e _ => ?_
  have hset2 : {c : Bool | c ∈ (if b e then ({true} : Finset Bool) else {false})}
      = {b e} := by
    ext c; cases hb : b e <;> simp [hb]
  rw [hset2, boolProb_prob_singleton]
  cases hb : b e <;> simp [hb]

lemma edgeMeasure_prob_unkept (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (S : Finset 𝓖) :
    (edgeMeasure 𝓖 p h0 h1).prob {ω : 𝓖 → Bool | ∀ e ∈ S, ω e = false} = (1 - p) ^ S.card := by
  rw [edgeMeasure_prob_box', Finset.prod_const]
  simp

lemma edgeMeasure_prob_kept (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (S : Finset 𝓖) :
    (edgeMeasure 𝓖 p h0 h1).prob {ω : 𝓖 → Bool | ∀ e ∈ S, ω e = true} = p ^ S.card := by
  rw [edgeMeasure_prob_box']
  rw [Finset.prod_const]
  simp

lemma edgeMeasure_prob_coord (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (e : 𝓖) :
    (edgeMeasure 𝓖 p h0 h1).prob {ω : 𝓖 → Bool | ω e = true} = p := by
  classical
  have hset : {ω : 𝓖 → Bool | ω e = true} = {ω : 𝓖 → Bool | ω e ∈ ({true} : Set Bool)} := by
    ext ω; simp
  rw [hset, edgeMeasure, Prob.pi_prob_mem_apply, boolProb_prob_singleton]
  simp

lemma edgeMeasure_prob_coord_false (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (e : 𝓖) :
    (edgeMeasure 𝓖 p h0 h1).prob {ω : 𝓖 → Bool | ω e = false} = 1 - p := by
  classical
  have hc : {ω : 𝓖 → Bool | ω e = false} = {ω : 𝓖 → Bool | ω e = true}ᶜ := by
    ext ω; simp
  rw [hc, FinProb.prob_compl, edgeMeasure_prob_coord]

/-- The edges of `𝓖` through `v`, as a finite set of coordinates. -/
noncomputable def thruF (v : V) : Finset 𝓖 := by
  classical exact Finset.univ.filter (fun e => v ∈ (e : Set V))

/-- The kept edges, as a finite set of coordinates. -/
noncomputable def keptF (ω : 𝓖 → Bool) : Finset 𝓖 := by
  classical exact Finset.univ.filter (fun e => ω e = true)

/-- The number of kept edges through `v`. -/
noncomputable def kAtF (ω : 𝓖 → Bool) (v : V) : ℕ := by
  classical exact ((thruF 𝓖 v).filter (fun e => ω e = true)).card

/-- The blockers of `e` when the residual degree of `v` is inspected: the edges meeting `e`
which do not contain `v`. -/
noncomputable def Bset (v : V) (e : 𝓖) : Finset 𝓖 := by
  classical exact Finset.univ.filter (fun f => ((f : Set V) ∩ (e : Set V)).Nonempty ∧ v ∉ (f : Set V))

/-- The residual degree at `v` as an explicit function of the coordinates away from `v`:
the number of edges `e ∋ v` all of whose blockers are unkept. -/
noncomputable def Wv (ω : 𝓖 → Bool) (v : V) : ℕ := by
  classical exact ((thruF 𝓖 v).filter (fun e => ∀ f ∈ Bset 𝓖 v e, ω f = false)).card

/-- A chosen kept blocker of `e` for `v` (a junk value if there is none). -/
noncomputable def witF (ω : 𝓖 → Bool) (v : V) (e : 𝓖) : 𝓖 :=
  if h : ∃ f ∈ Bset 𝓖 v e, ω f = true then Classical.choose h else e

/-- The certificate set of an outcome at the vertex `v`. -/
noncomputable def certSet (ω : 𝓖 → Bool) (v : V) : Finset 𝓖 := by
  classical exact (thruF 𝓖 v).image (witF 𝓖 ω v)

/-- The set of coordinates on which the event at `v` depends. -/
noncomputable def Nset (v : V) : Finset 𝓖 := by
  classical exact ((thruF 𝓖 v).biUnion (fun e => Bset 𝓖 v e)) ∪ (thruF 𝓖 v)


/-! ## Bridges between the set-level definitions of the round and the Finset-level objects -/

lemma natCard_subtype_eq_filter_card {α : Type*} [Fintype α] [DecidableEq α] (P : α → Prop)
    [DecidablePred P] : Nat.card {a : α // P a} = (Finset.univ.filter P).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

lemma natCard_setOf_eq_filter_card {α : Type*} [Fintype α] [DecidableEq α] (P : α → Prop)
    [DecidablePred P] : Nat.card {a : α | P a} = (Finset.univ.filter P).card :=
  natCard_subtype_eq_filter_card P

@[simp] lemma mem_thruF {v : V} {e : 𝓖} : e ∈ thruF 𝓖 v ↔ v ∈ (e : Set V) := by
  classical simp [thruF]

@[simp] lemma mem_keptF {ω : 𝓖 → Bool} {e : 𝓖} : e ∈ keptF 𝓖 ω ↔ ω e = true := by
  classical simp [keptF]

lemma hd_eq_card_thruF (v : V) : hd 𝓖 v = (thruF 𝓖 v).card := by
  classical
  rw [hd, thruF, natCard_subtype_eq_filter_card]

lemma kept_card (ω : 𝓖 → Bool) : (kept 𝓖 ω).ncard = (keptF 𝓖 ω).card := by
  classical
  have himg : kept 𝓖 ω = Subtype.val '' {e : 𝓖 | ω e = true} := by
    ext y
    constructor
    · rintro ⟨hy, hyt⟩
      exact ⟨⟨y, hy⟩, hyt, rfl⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨e.2, he⟩
  rw [himg]
  have hinj : Set.InjOn (Subtype.val : 𝓖 → Set V) {e : 𝓖 | ω e = true} :=
    fun a _ b _ h => Subtype.ext h
  rw [Set.InjOn.ncard_image hinj, keptF]
  exact natCard_setOf_eq_filter_card (fun e : 𝓖 => ω e = true)

lemma kAt_eq_kAtF (ω : 𝓖 → Bool) (v : V) : kAt 𝓖 ω v = kAtF 𝓖 ω v := by
  classical
  rw [kAt, kAtF, thruF, Nat.card_eq_fintype_card, Fintype.card_subtype,
    ← Finset.filter_filter]

@[simp] lemma mem_Bset {v : V} {e f : 𝓖} :
    f ∈ Bset 𝓖 v e ↔ ((f : Set V) ∩ (e : Set V)).Nonempty ∧ v ∉ (f : Set V) := by
  classical simp [Bset]

lemma mem_covX_iff (ω : 𝓖 → Bool) (v : V) :
    v ∈ covX 𝓖 ω ↔ ∃ e : 𝓖, ω e = true ∧ v ∈ (e : Set V) := by
  classical
  have h : ∀ y : V, y ∈ covX 𝓖 ω ↔ ∃ e : 𝓖, ω e = true ∧ y ∈ (e : Set V) := by
    intro y
    rw [covX]
    constructor
    · intro hy
      obtain ⟨e, hy'⟩ := Set.mem_iUnion.mp hy
      obtain ⟨hk, hye⟩ := Set.mem_iUnion.mp hy'
      obtain ⟨he𝓖, hω⟩ := hk
      exact ⟨⟨e, he𝓖⟩, hω, hye⟩
    · rintro ⟨e, hk, hye⟩
      refine Set.mem_iUnion.mpr ⟨(e : Set V), Set.mem_iUnion.mpr ⟨?_, hye⟩⟩
      exact ⟨e.2, hk⟩
  exact h v

lemma uncovered_iff (ω : 𝓖 → Bool) (v : V) :
    v ∉ covX 𝓖 ω ↔ ∀ e ∈ thruF 𝓖 v, ω e = false := by
  classical
  constructor
  · intro hv e he
    by_contra hc
    exact hv ((mem_covX_iff 𝓖 ω v).mpr ⟨e, by simpa using hc, (mem_thruF (𝓖 := 𝓖)).mp he⟩)
  · intro h hv
    obtain ⟨e, hk, hve⟩ := (mem_covX_iff 𝓖 ω v).mp hv
    have he : e ∈ thruF 𝓖 v := (mem_thruF (𝓖 := 𝓖)).mpr hve
    have hf := h e he
    rw [hf] at hk
    exact Bool.noConfusion hk

lemma kAtF_pos_iff (ω : 𝓖 → Bool) (v : V) :
    0 < kAtF 𝓖 ω v ↔ v ∈ covX 𝓖 ω := by
  classical
  constructor
  · intro h
    by_contra hcov
    have h0 : kAtF 𝓖 ω v = 0 := by
      rw [kAtF, Finset.card_eq_zero]
      refine Finset.filter_eq_empty_iff.mpr ?_
      intro e he
      have := (uncovered_iff 𝓖 ω v).mp hcov e he
      simp [this]
    omega
  · intro hcov
    obtain ⟨e, hk, hve⟩ := (mem_covX_iff 𝓖 ω v).mp hcov
    rw [kAtF]
    exact Finset.card_pos.mpr ⟨e, by
      rw [Finset.mem_filter]
      exact ⟨(mem_thruF (𝓖 := 𝓖)).mpr hve, by simpa using hk⟩⟩


/-! ## The residual degree at an uncovered vertex -/

/-- On the event that `v` is not covered, the residual degree of `v` is the explicit random
variable `Wv`. -/
lemma Wv_eq_hd_residH (ω : 𝓖 → Bool) (v : V) (hv : v ∉ covX 𝓖 ω) :
    hd (residH 𝓖 ω) v = Wv 𝓖 ω v := by
  classical
  have hcard : Nat.card {e : residH 𝓖 ω // v ∈ ((e : residH 𝓖 ω) : Set V)}
      = Nat.card {e : 𝓖 // v ∈ (e : Set V) ∧ (e : Set V) ⊆ (covX 𝓖 ω)ᶜ} := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    refine Fintype.card_congr ?_
    refine
      { toFun := fun x => ⟨⟨(x.1 : residH 𝓖 ω).1, (x.1 : residH 𝓖 ω).2.1⟩, x.2, (x.1 : residH 𝓖 ω).2.2⟩
        invFun := fun y => ⟨⟨(y.1 : 𝓖).1, ⟨(y.1 : 𝓖).2, y.2.2⟩⟩, y.2.1⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro x; rfl
    · intro y; rfl
  have hstep1 : hd (residH 𝓖 ω) v
      = ((thruF 𝓖 v).filter (fun e : 𝓖 => (e : Set V) ⊆ (covX 𝓖 ω)ᶜ)).card := by
    have h1 : hd (residH 𝓖 ω) v
        = (Finset.univ.filter (fun e : residH 𝓖 ω => v ∈ ((e : residH 𝓖 ω) : Set V))).card := by
      rw [hd]
      exact natCard_subtype_eq_filter_card _
    have h2 : (Finset.univ.filter (fun e : residH 𝓖 ω => v ∈ ((e : residH 𝓖 ω) : Set V))).card
        = (Finset.univ.filter (fun e : 𝓖 => v ∈ (e : Set V) ∧ (e : Set V) ⊆ (covX 𝓖 ω)ᶜ)).card := by
      have hA : (Finset.univ.filter (fun e : residH 𝓖 ω => v ∈ ((e : residH 𝓖 ω) : Set V))).card
          = Nat.card {e : residH 𝓖 ω // v ∈ ((e : residH 𝓖 ω) : Set V)} :=
        (natCard_subtype_eq_filter_card _).symm
      have hB : Nat.card {e : 𝓖 // v ∈ (e : Set V) ∧ (e : Set V) ⊆ (covX 𝓖 ω)ᶜ}
          = (Finset.univ.filter (fun e : 𝓖 => v ∈ (e : Set V) ∧ (e : Set V) ⊆ (covX 𝓖 ω)ᶜ)).card :=
        natCard_subtype_eq_filter_card _
      rw [hA, hcard, hB]
    rw [h1, h2, thruF, ← Finset.filter_filter]
  have hstep2 : (thruF 𝓖 v).filter (fun e : 𝓖 => (e : Set V) ⊆ (covX 𝓖 ω)ᶜ)
      = (thruF 𝓖 v).filter (fun e : 𝓖 => ∀ f ∈ Bset 𝓖 v e, ω f = false) := by
    refine Finset.filter_congr ?_
    intro e he
    constructor
    · intro hsub f hf
      by_contra hc
      obtain ⟨hne, hvf⟩ := (mem_Bset (𝓖 := 𝓖)).mp hf
      obtain ⟨x, hx⟩ := hne
      have hxcov : x ∈ covX 𝓖 ω := (mem_covX_iff 𝓖 ω x).mpr ⟨f, by simpa using hc, hx.1⟩
      exact (hsub hx.2) hxcov
    · intro h x hx hxcov
      obtain ⟨f, hk, hxf⟩ := (mem_covX_iff 𝓖 ω x).mp hxcov
      by_cases hvf : v ∈ (f : Set V)
      · exact hv ((mem_covX_iff 𝓖 ω v).mpr ⟨f, hk, hvf⟩)
      · have hfB : f ∈ Bset 𝓖 v e := by
          rw [mem_Bset]
          exact ⟨⟨x, hxf, hx⟩, hvf⟩
        have := h f hfB
        rw [this] at hk
        exact Bool.noConfusion hk
  rw [hstep1, hstep2]
  rfl

lemma mem_Nset_of_mem_Bset {v : V} {e f : 𝓖} (he : e ∈ thruF 𝓖 v) (hf : f ∈ Bset 𝓖 v e) :
    f ∈ Nset 𝓖 v := by
  classical
  rw [Nset]
  exact Finset.mem_union.mpr (Or.inl (Finset.mem_biUnion.mpr ⟨e, he, hf⟩))

lemma mem_Nset_of_mem_thruF {v : V} {e : 𝓖} (he : e ∈ thruF 𝓖 v) : e ∈ Nset 𝓖 v := by
  classical
  rw [Nset]
  exact Finset.mem_union.mpr (Or.inr he)

/-- `Wv` is determined by the coordinates of `Nset`. -/
lemma Wv_congr {ω ω' : 𝓖 → Bool} {v : V} (h : ∀ e ∈ Nset 𝓖 v, ω e = ω' e) :
    Wv 𝓖 ω v = Wv 𝓖 ω' v := by
  classical
  rw [Wv, Wv]
  congr 1
  refine Finset.filter_congr ?_
  intro e he
  constructor
  · intro hh f hf
    rw [← h f (mem_Nset_of_mem_Bset 𝓖 he hf)]
    exact hh f hf
  · intro hh f hf
    rw [h f (mem_Nset_of_mem_Bset 𝓖 he hf)]
    exact hh f hf

/-- The per-vertex bad event, in a form whose dependence on the coordinates is visible. -/
lemma event_eq (v : V) (ε' D' : ℝ) :
    {ω : 𝓖 → Bool | v ∉ covX 𝓖 ω ∧ ε' * D' < |((hd (residH 𝓖 ω) v : ℝ)) - D'|}
      = {ω : 𝓖 → Bool |
          (∀ e ∈ thruF 𝓖 v, ω e = false) ∧ ε' * D' < |((Wv 𝓖 ω v : ℝ)) - D'|} := by
  classical
  ext ω
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hu, hbad⟩
    refine ⟨(uncovered_iff 𝓖 ω v).mp hu, ?_⟩
    have h := hbad
    rw [Wv_eq_hd_residH 𝓖 ω v hu] at h
    exact h
  · rintro ⟨hu, hbad⟩
    refine ⟨(uncovered_iff 𝓖 ω v).mpr hu, ?_⟩
    rwa [Wv_eq_hd_residH 𝓖 ω v ((uncovered_iff 𝓖 ω v).mpr hu)]

lemma dependsOn_event (v : V) (ε' D' : ℝ) :
    Work.Deep.Reed.DependsOn (Nset 𝓖 v)
      {ω : 𝓖 → Bool | v ∉ covX 𝓖 ω ∧ ε' * D' < |((hd (residH 𝓖 ω) v : ℝ)) - D'|} := by
  classical
  rw [event_eq 𝓖 v ε' D']
  intro ω ω' h
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq]
  have hW : Wv 𝓖 ω v = Wv 𝓖 ω' v := Wv_congr 𝓖 (fun e he => h e he)
  have hthru : (∀ e ∈ thruF 𝓖 v, ω e = false) ↔ (∀ e ∈ thruF 𝓖 v, ω' e = false) := by
    constructor
    · intro hh e he
      rw [← h e (mem_Nset_of_mem_thruF 𝓖 he)]
      exact hh e he
    · intro hh e he
      rw [h e (mem_Nset_of_mem_thruF 𝓖 he)]
      exact hh e he
  rw [hthru, hW]

/-! ## The certificate set -/

lemma certSet_card_le (ω : 𝓖 → Bool) (v : V) :
    (certSet 𝓖 ω v).card ≤ (thruF 𝓖 v).card := by
  classical
  rw [certSet]
  exact Finset.card_image_le

lemma witF_mem {ω : 𝓖 → Bool} {v : V} {e : 𝓖}
    (h : ∃ f ∈ Bset 𝓖 v e, ω f = true) : witF 𝓖 ω v e ∈ Bset 𝓖 v e := by
  classical
  rw [witF]
  rw [dif_pos h]
  exact (Classical.choose_spec h).1

lemma witF_kept {ω : 𝓖 → Bool} {v : V} {e : 𝓖}
    (h : ∃ f ∈ Bset 𝓖 v e, ω f = true) : ω (witF 𝓖 ω v e) = true := by
  classical
  rw [witF]
  rw [dif_pos h]
  exact (Classical.choose_spec h).2

lemma witF_mem_certSet {ω : 𝓖 → Bool} {v : V} {e : 𝓖} (he : e ∈ thruF 𝓖 v) :
    witF 𝓖 ω v e ∈ certSet 𝓖 ω v := by
  classical
  rw [certSet]
  exact Finset.mem_image.mpr ⟨e, he, rfl⟩


/-- An edge, as a `Finset` of vertices. -/
noncomputable def eFin (e : 𝓖) : Finset V := by
  classical exact Finset.univ.filter (fun w => w ∈ (e : Set V))

/-- The uncovered vertices, as a `Finset`. -/
noncomputable def uncovF (ω : 𝓖 → Bool) : Finset V := by
  classical exact Finset.univ.filter (fun v => v ∉ covX 𝓖 ω)

/-- The covered vertices, as a `Finset`. -/
noncomputable def covF (ω : 𝓖 → Bool) : Finset V := by
  classical exact Finset.univ.filter (fun v => v ∈ covX 𝓖 ω)

/-- A real-valued function on a product space **depends only on the coordinates in `S`**. -/
def DependsOnFun {ι : Type*} {Ω : ι → Type*} (S : Finset ι) (f : (∀ i, Ω i) → ℝ) : Prop :=
  ∀ g h : ∀ i, Ω i, (∀ i ∈ S, g i = h i) → f g = f h

@[simp] lemma eFin_mem_iff {e : 𝓖} {w : V} : w ∈ eFin 𝓖 e ↔ w ∈ (e : Set V) := by
  classical
  simp only [eFin, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp] lemma uncovF_mem_iff {ω : 𝓖 → Bool} {v : V} : v ∈ uncovF 𝓖 ω ↔ v ∉ covX 𝓖 ω := by
  classical
  simp only [uncovF, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp] lemma covF_mem_iff {ω : 𝓖 → Bool} {v : V} : v ∈ covF 𝓖 ω ↔ v ∈ covX 𝓖 ω := by
  classical
  simp only [covF, Finset.mem_filter, Finset.mem_univ, true_and]

/-! ## The numeric auxiliary quantities of the round -/

open scoped BigOperators

/-- The residual level `D' = D (1 - θ/D)^{(r-1)(D-1)}` of the round. -/
noncomputable def Dlev (r : ℕ) (θ : ℝ) (D : ℕ) : ℝ :=
  (D : ℝ) * (1 - θ / (D : ℝ)) ^ ((r - 1) * (D - 1))

/-- The per-vertex bad-event bound of the round: `4 exp (- (ε' D')² / (128 r² D))`. -/
noncomputable def qV (r : ℕ) (ε' θ : ℝ) (D : ℕ) : ℝ :=
  4 * Real.exp (-(ε' * Dlev r θ D) ^ 2 / (128 * (r : ℝ) ^ 2 * (D : ℝ)))

/-- The threshold separating the "sparse" from the "dense" regime. -/
noncomputable def nThresh (r : ℕ) (θ δ : ℝ) (D : ℕ) : ℝ :=
  10 ^ 6 * (r : ℝ) * (D : ℝ) / (δ ^ 2 * θ ^ 4)

/-- The variance of a real-valued random variable on a finite probability space. -/
noncomputable def variance {Ω : Type*} [Fintype Ω] (μ : FinProb Ω) (X : Ω → ℝ) : ℝ :=
  μ.exp (fun ω => X ω ^ 2) - (μ.exp X) ^ 2

end Work.Deep.Nibble

namespace Work.Deep.Reed

namespace FinProb

/-- Positive probability yields an outcome in the event. -/
lemma exists_of_prob_pos {Ω : Type*} [Fintype Ω] (μ : FinProb Ω) {A : Set Ω}
    (h : 0 < μ.prob A) : ∃ ω, ω ∈ A := by
  classical
  by_contra hcon
  push_neg at hcon
  have hA : A = ∅ := by ext ω; simp [hcon ω]
  rw [hA, FinProb.prob_empty] at h
  exact lt_irrefl 0 h

end FinProb

end Work.Deep.Reed
