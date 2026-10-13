/-
  WilE5 / Strat — the state invariants of the *profile-indexed* stratification recursion
  `Work.WilE5.levelP` (the version of `Work.WilE5.level` in which the test-order bound is the
  level-indexed profile `Ml`).

  `Work.WilE5.Strat.Inv` (see `Strat/InvariantDef.lean`) bundles the bookkeeping invariants of a
  state of the recursion.  This file proves that every state of every level of the *profiled*
  recursion `levelP X Ml NΦ` satisfies those invariants, together with one further piece of
  bookkeeping that the flat-leaf correctness needs: every flatness source of a state vanishes at
  every point of the state's set (this is `Inv`'s `Φ ⊆ Ξ` together with the definition of the
  state's set).

  The proof is an induction on the level:

  * level `0` is `initStates X`: the disjunct bookkeeping, `Φ = Ξ` and the cube bookkeeping are
    immediate from `initSt`, and the full pivot minor of an initial state is the identity matrix
    (its equations are the face equations `y_l ∓ 1`, one per pivot direction, and the pivots are
    pairwise distinct) — `StratAux.initSt_inv`;
  * a child inherits the disjunct bookkeeping, `Φ = Ξ` and the cube bookkeeping
    (`Strat.inv_child_nondet`), inherits the vanishing of the flatness sources
    (`child_subset_parent` for the old sources and `stSemiPf_child_set_eq` for the new ones), and
    its pivot minor is nonzero on its own set: at an invalid test, or at a test whose peeled
    direction is not the first direction of its support, the child is empty
    (`Strat.childSt_empty_of_not_min`), while at a valid test with minimal peeled direction the
    child's pivot minor is `opVal X.c σ t` (`StratAux.childB_det_eq` glues the pivot minor of
    `childB` to `detOp`, and peeling the outermost operator of `yOpSt` (`Strat.yOpSt_step`) turns
    that `detOp` into `opVal`), which the child's own sign condition makes nonvanishing.

  The induction is stated for *all* levels (`invP_all`); the statement `stateInvP` only asks for
  the levels `≤ q`.
-/
import Mathlib
import Submission.Work.WilE5.SysL
import Submission.Work.WilE5.Strat.InvariantDef
import Submission.Work.WilE5.Strat.InitCover
import Submission.Work.WilE5.Strat.child_subset_parent
import Submission.Work.WilE5.Strat.opVal_eq_zero_of_not_valid
import Submission.Work.WilE5.Strat.stSemiPf_subset_flatSemiPf_union_children
import Submission.Work.WilE5.Strat.childSt_empty_of_not_min
import Submission.Work.WilE5.Strat.inv_child_nondet
import Submission.Work.WilE5.Strat.cover
import Submission.Work.Strat.yOpSt_step
import Submission.Work.WilE5.Strat.childB_det_eq
import Submission.Work.WilE5.initSt_inv

set_option autoImplicit false
noncomputable section
open Classical Filter
open scoped Topology
namespace Work.WilE5.Strat
open WilkiesDesign WilkiesDesign.E

/-! ## §1. The invariant of a state of the profiled recursion -/

/-- The invariant of `stateInvP`: the invariants `Inv` of the state together with the vanishing
of every flatness source on the state's set, in exactly the bracketing of the goal of
`Work.WilE5.Strat.stateInvP`. -/
def InvP {p q : ℕ} (X : WilkiesDesign.E.SemiPf (p + q)) (σ : Work.WilE5.St p q X.r) : Prop :=
  (∃ A ∈ X.basics,
      (∀ f ∈ A.eqs, f ∈ (Work.WilE5.stCond σ).eqs) ∧
      (∀ g ∈ A.pos, g ∈ (Work.WilE5.stCond σ).pos) ∧
      (∀ f ∈ A.eqs, f ∈ σ.Φ)) ∧
    (∀ ψ ∈ σ.Φ, ψ ∈ σ.Ξ) ∧
    (∀ ψ ∈ σ.Ξ, ψ ∈ σ.Φ) ∧
    (∀ ψ ∈ σ.Φ, ∀ w ∈ (Work.WilE5.stSemiPf X σ).set, WilkiesDesign.E.eaEval X.c ψ w = 0) ∧
    (∀ l : Fin q,
        Work.WilE5.intPoly (p := p) (r := X.r) l ∈ σ.ν ∨
          ∃ c : ℝ, (c = 1 ∨ c = -1) ∧
            Work.WilE5.facePoly (p := p) (r := X.r) l c ∈ σ.B.map Prod.fst) ∧
    (∀ z ∈ (Work.WilE5.stSemiPf X σ).set,
      (Matrix.of fun (a : Fin σ.B.length) (b : Fin σ.B.length) =>
        WilkiesDesign.E.eaEval X.c (WilkiesDesign.E.eaD X.c (Work.WilE5.pivFun σ.B b)
          (Work.WilE5.hFun σ.B a)) z).det ≠ 0)

/-- `Inv` together with the `Φ ⊆ Ξ`-vanishing is exactly `InvP`: the vanishing conjunct is a
formal consequence of `Φ ⊆ Ξ` (a state's flatness sources are among its accumulated vanishing
conditions, hence among the equations of its condition, hence vanish on its set). -/
theorem invP_of_inv {p q : ℕ} (X : SemiPf (p + q)) {σ : St p q X.r} (h : Inv X σ) :
    InvP X σ := by
  obtain ⟨hA, hΦΞ, hΞΦ, hcube, hdet⟩ := h
  exact ⟨hA, hΦΞ, hΞΦ, PhiInXi_holds X hΦΞ, hcube, hdet⟩

/-! ## §2. The pivot minor of a child -/

/-- If the peeled direction `t.l` of the test is the smallest direction carrying a nonzero
multiplicity, then `opVal X.c σ t` and the `detOp` expression that is the child's pivot minor
have the same evaluation: peeling the outermost operator of the iterate `yOpSt` rewrites `opVal`
as `detOpSt` applied to the peeled operator. -/
theorem eaEval_opVal_detOp {p q : ℕ} (X : SemiPf (p + q)) (σ : St p q X.r) (t : Test q)
    (hm : t.m t.l ≠ 0) (hmin : ∀ l' : Fin q, t.m l' ≠ 0 → t.l ≤ l') (z : Fin (p + q) → ℝ) :
    eaEval X.c (opVal X.c σ t) z =
      eaEval X.c (detOp X.c (hFun σ.B) (pivFun σ.B) (yDir p t.l) (peelVal X.c σ t)) z := by
  have h2 : opVal X.c σ t
      = detOp X.c (hFun σ.B) (pivFun σ.B) (yDir p t.l) (peelVal X.c σ t) := by
    unfold opVal peelVal
    rw [Work.Strat.yOpSt_step X.c σ.B t.m t.l hm hmin (testPoly σ t.i)]
    rfl
  exact congrArg (fun Q => eaEval X.c Q z) h2

/-- The pivot minor of a child (at test `t` and sign `s`) evaluates to `opVal X.c σ t` at every
point: the child's system is `childB X.c σ t`, whose pivot minor is the `detOp` expression of
`Strat.childB_det_eq`. -/
theorem det_childSt_eq {p q : ℕ} (X : SemiPf (p + q)) (M NΦ : ℕ) (σ : St p q X.r)
    (t : Test q) (s : Bool) (hm : t.m t.l ≠ 0) (hmin : ∀ l' : Fin q, t.m l' ≠ 0 → t.l ≤ l')
    (z : Fin (p + q) → ℝ) :
    (Matrix.of fun (a b : Fin (childSt X.c M NΦ σ t s).B.length) =>
      eaEval X.c (eaD X.c (pivFun (childSt X.c M NΦ σ t s).B b)
        (hFun (childSt X.c M NΦ σ t s).B a)) z).det = eaEval X.c (opVal X.c σ t) z := by
  rw [show (childSt X.c M NΦ σ t s).B = childB X.c σ t from rfl]
  exact (Work.WilE5.Strat.childB_det_eq X σ t z).trans
    (eaEval_opVal_detOp X σ t hm hmin z).symm

/-! ## §3. The invariant at the initial states -/

/-- The invariant holds at the initial states. -/
theorem invP_init {p q : ℕ} (X : SemiPf (p + q)) {σ : St p q X.r} (hσ : σ ∈ initStates X) :
    InvP X σ := by
  obtain ⟨hInv, hvanish⟩ := Work.WilE5.initSt_inv X σ hσ
  exact ⟨hInv.1, hInv.2.1, hInv.2.2.1, hvanish, hInv.2.2.2.1, hInv.2.2.2.2⟩

/-! ## §4. The invariant passes to children -/

/-- The invariant passes to a child of a state, at any test of the test list. -/
theorem invP_childSt {p q : ℕ} (X : SemiPf (p + q)) (M NΦ : ℕ) (σ : St p q X.r)
    (t : Test q) (s : Bool) (ht : t ∈ testL q M NΦ) (hσ : InvP X σ) :
    InvP X (childSt X.c M NΦ σ t s) := by
  obtain ⟨hA, hΦΞ, hΞΦ, hvanish, hcube, hdet⟩ := hσ
  have hInv : Inv X σ := ⟨hA, hΦΞ, hΞΦ, hcube, hdet⟩
  obtain ⟨gA, gΦΞ, gΞΦ, gcube⟩ := inv_child_nondet X M NΦ σ t s ht hInv
  -- the flatness sources of the child vanish on the child's set
  have gvanish : ∀ ψ ∈ (childSt X.c M NΦ σ t s).Φ,
      ∀ w ∈ (stSemiPf X (childSt X.c M NΦ σ t s)).set, eaEval X.c ψ w = 0 := by
    intro ψ hψ w hw
    rw [childSt] at hψ
    rcases List.mem_append.mp hψ with hψ | hψ
    · exact hvanish ψ hψ w (child_subset_parent X M NΦ σ t s hw)
    · have hcx : (stCond (childSt X.c M NΦ σ t s)).eqs
          = (childB X.c σ t).map Prod.fst ++ childΞ X.c M NΦ σ t := rfl
      have hmem : ψ ∈ (stCond (childSt X.c M NΦ σ t s)).eqs := by
        rw [hcx]
        exact List.mem_append_right _ hψ
      rw [stSemiPf, semiPfAnd_set] at hw
      exact hw.2.1 ψ hmem
  refine ⟨gA, gΦΞ, gΞΦ, gvanish, gcube, ?_⟩
  intro z hz
  -- the child's sign condition makes `opVal` nonvanishing at `z`
  have hz' := hz
  rw [stSemiPf_child_set_eq X M NΦ σ t s] at hz'
  obtain ⟨-, -, -, -, hsign⟩ := hz'
  have hopv : eaEval X.c (opVal X.c σ t) z ≠ 0 := by
    cases s
    · exact ne_of_lt hsign
    · exact ne_of_gt hsign
  by_cases hmin : valid σ t ∧ ∀ l' : Fin q, t.m l' ≠ 0 → t.l ≤ l'
  · -- a valid test with minimal peeled direction: the pivot minor is `opVal`
    have hm : t.m t.l ≠ 0 := ((mem_testL_iff t).mp ht).2.2
    rw [det_childSt_eq X M NΦ σ t s hm hmin.2 z]
    exact hopv
  · -- otherwise the child is empty
    have hnot : ¬ valid σ t ∨ ∃ l' : Fin q, l' < t.l ∧ t.m l' ≠ 0 := by
      by_cases hv : valid σ t
      · right
        by_contra hcon
        exact (fun h => hmin ⟨hv, h⟩) (fun l' hl' => by
          by_contra hle
          exact hcon ⟨l', lt_of_not_ge hle, hl'⟩)
      · exact Or.inl hv
    exact absurd hz (childSt_empty_of_not_min X M NΦ σ t s ht hnot z)

/-- The invariant passes from a state to every member of its (profiled) children list. -/
theorem invP_of_mem_childrenP {p q : ℕ} (X : SemiPf (p + q)) (Ml : ℕ → ℕ) (NΦ : ℕ)
    (σ : St p q X.r) (hσ : InvP X σ) {τ : St p q X.r}
    (hτ : τ ∈ childrenP X.c Ml NΦ σ) : InvP X τ := by
  rw [childrenP, List.mem_flatMap] at hτ
  obtain ⟨t, ht, hτ⟩ := hτ
  rw [List.mem_cons] at hτ
  rcases hτ with hτ | hτ
  · subst hτ
    exact invP_childSt X (Ml σ.B.length) NΦ σ t false ht hσ
  · rw [List.mem_singleton] at hτ
    subst hτ
    exact invP_childSt X (Ml σ.B.length) NΦ σ t true ht hσ

/-! ## §5. The induction on the level of the profiled recursion -/

/-- Every state at every level of the profiled recursion satisfies the invariant. -/
theorem invP_all {p q : ℕ} (X : SemiPf (p + q)) (Ml : ℕ → ℕ) (NΦ : ℕ) :
    ∀ n : ℕ, ∀ σ ∈ levelP X Ml NΦ n, InvP X σ := by
  intro n
  induction n with
  | zero =>
    intro σ hσ
    rw [levelP_zero] at hσ
    exact invP_init X hσ
  | succ n ih =>
    intro τ hτ
    rw [mem_levelP_succ] at hτ
    obtain ⟨σ, hσ, hchild⟩ := hτ
    exact invP_of_mem_childrenP X Ml NΦ σ (ih σ hσ) hchild

/-! ## §6. The statement -/

theorem stateInvP {p q : ℕ} (X : WilkiesDesign.E.SemiPf (p + q)) (Ml : ℕ → ℕ) (NΦ : ℕ) :
    ∀ k ∈ Finset.range (q + 1), ∀ σ ∈ Work.WilE5.levelP X Ml NΦ k,
      (∃ A ∈ X.basics,
          (∀ f ∈ A.eqs, f ∈ (Work.WilE5.stCond σ).eqs) ∧
          (∀ g ∈ A.pos, g ∈ (Work.WilE5.stCond σ).pos) ∧
          (∀ f ∈ A.eqs, f ∈ σ.Φ)) ∧
      (∀ ψ ∈ σ.Φ, ψ ∈ σ.Ξ) ∧
      (∀ ψ ∈ σ.Ξ, ψ ∈ σ.Φ) ∧
      (∀ ψ ∈ σ.Φ, ∀ w ∈ (Work.WilE5.stSemiPf X σ).set, WilkiesDesign.E.eaEval X.c ψ w = 0) ∧
      (∀ l : Fin q,
          Work.WilE5.intPoly (p := p) (r := X.r) l ∈ σ.ν ∨
            ∃ c : ℝ, (c = 1 ∨ c = -1) ∧
              Work.WilE5.facePoly (p := p) (r := X.r) l c ∈ σ.B.map Prod.fst) ∧
      (∀ z ∈ (Work.WilE5.stSemiPf X σ).set,
        (Matrix.of fun (a : Fin σ.B.length) (b : Fin σ.B.length) =>
          WilkiesDesign.E.eaEval X.c (WilkiesDesign.E.eaD X.c (Work.WilE5.pivFun σ.B b)
            (Work.WilE5.hFun σ.B a)) z).det ≠ 0) := by
  intro k _hk σ hσ
  exact invP_all X Ml NΦ k σ hσ

end Work.WilE5.Strat
