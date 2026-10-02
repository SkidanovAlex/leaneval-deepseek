import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.Defs
import Submission.Work.Deep.GKO.spanningDefs

/-!
# Reachability, components and path lists inside a vertex subset

Helper layer for the spanning-path theorem of `exists_spanningPath_subset`: `PathListIn`
(lists of vertices forming a path inside `U` from `a` to `b`), reachability inside a vertex
set `Z`, connected components of `G[Z]`, and the hypothesis bundle `SpanHyp`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.Deep.GKO

open Classical
open scoped BigOperators

noncomputable section

variable {n : ℕ}

theorem Walk_support_getLast? : ∀ {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n} (w : G.Walk u v),
  w.support.getLast? = some v :=
fun {n} {G} {u v} w =>
  SimpleGraph.Walk.rec (fun {u} => of_eq_true (eq_self (some u)))
    (fun {u v w} h p ih =>
      Eq.mpr (id (congrArg (fun _a => _a.getLast? = some w) (SimpleGraph.Walk.support_cons h p)))
        (Eq.mpr (id (congrArg (fun _a => _a = some w) List.getLast?_cons))
          (Eq.mpr (id (congrArg (fun _a => some (_a.getD u) = some w) ih)) (Eq.refl (some ((some w).getD u))))))
    w

theorem Walk_support_head? : ∀ {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n} (w : G.Walk u v),
  w.support.head? = some u :=
fun {n} {G} {u v} w =>
  SimpleGraph.Walk.rec (fun {u} => of_eq_true (eq_self (some u)))
    (fun {u v w} h p ih =>
      Eq.mpr (id (congrArg (fun _a => _a.head? = some u) (SimpleGraph.Walk.support_cons h p)))
        (Eq.refl (u :: p.support).head?))
    w

namespace Walk_support_isChain
theorem _simp_1_1 {α : Type*} {a b : α} : (a ∈ some b) = (b = a) := by simp
end Walk_support_isChain

theorem Walk_support_isChain : ∀ {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n} (w : G.Walk u v),
  List.IsChain G.Adj w.support :=
fun {n} {G} {u v} w =>
  SimpleGraph.Walk.rec (fun {u} => of_eq_true (List.IsChain.singleton._simp_1 u))
    (fun {u v w} h p ih =>
      Eq.mpr (id (congrArg (fun _a => List.IsChain G.Adj _a) (SimpleGraph.Walk.support_cons h p)))
        (List.IsChain.cons ih fun y hy =>
          Eq.mp Walk_support_isChain._simp_1_1
              (Eq.mp (congrArg (fun _a => y ∈ _a) (Walk_support_head? p)) hy) ▸
            h))
    w

theorem Walk_mem_support_getLast : ∀ {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n} (w : G.Walk u v),
  v ∈ w.support :=
fun {n} {G} {u v} w =>
  Exists.casesOn (List.getLast?_eq_some_iff.mp (Walk_support_getLast? w)) fun ys hy =>
    Eq.mpr (id (congrArg (fun _a => v ∈ _a) hy)) List.mem_concat_self

def PathListIn : {n : ℕ} → SimpleGraph (Fin n) → Finset (Fin n) → Fin n → Fin n → List (Fin n) → Prop :=
fun {n} G U a b l => l.Nodup ∧ List.IsChain G.Adj l ∧ l.head? = some a ∧ l.getLast? = some b ∧ ∀ v ∈ l, v ∈ U

theorem PathListIn.getLast?_eq : ∀ {n : ℕ} {G : SimpleGraph (Fin n)} {U : Finset (Fin n)} {a b : Fin n}
  {l : List (Fin n)}, PathListIn G U a b l → l.getLast? = some b :=
fun {n} {G} {U} {a b} {l} h => h.right.right.right.left

theorem PathListIn.getLast_mem : ∀ {n : ℕ} {G : SimpleGraph (Fin n)} {U : Finset (Fin n)} {a b : Fin n}
  {l : List (Fin n)}, PathListIn G U a b l → b ∈ l :=
fun {n} {G} {U} {a b} {l} h =>
  Exists.casesOn (List.getLast?_eq_some_iff.mp (PathListIn.getLast?_eq h)) fun ys hy =>
    Eq.mpr (id (congrArg (fun _a => b ∈ _a) hy)) List.mem_concat_self

theorem PathListIn.head?_eq : ∀ {n : ℕ} {G : SimpleGraph (Fin n)} {U : Finset (Fin n)} {a b : Fin n}
  {l : List (Fin n)}, PathListIn G U a b l → l.head? = some a :=
fun {n} {G} {U} {a b} {l} h => h.right.right.left

theorem PathListIn.head_mem : ∀ {n : ℕ} {G : SimpleGraph (Fin n)} {U : Finset (Fin n)} {a b : Fin n}
  {l : List (Fin n)}, PathListIn G U a b l → a ∈ l :=
fun {n} {G} {U} {a b} {l} h =>
  Exists.casesOn (List.head?_eq_some_iff.mp (PathListIn.head?_eq h)) fun ys hy =>
    Eq.mpr (id (congrArg (fun _a => a ∈ _a) hy)) List.mem_cons_self

theorem PathListIn.isChain : ∀ {n : ℕ} {G : SimpleGraph (Fin n)} {U : Finset (Fin n)} {a b : Fin n}
  {l : List (Fin n)}, PathListIn G U a b l → List.IsChain G.Adj l :=
fun {n} {G} {U} {a b} {l} h => h.right.left

theorem PathListIn.nodup : ∀ {n : ℕ} {G : SimpleGraph (Fin n)} {U : Finset (Fin n)} {a b : Fin n}
  {l : List (Fin n)}, PathListIn G U a b l → l.Nodup :=
fun {n} {G} {U} {a b} {l} h => h.left

theorem PathListIn.mem_U : ∀ {n : ℕ} {G : SimpleGraph (Fin n)} {U : Finset (Fin n)} {a b : Fin n}
  {l : List (Fin n)}, PathListIn G U a b l → ∀ {v : Fin n}, v ∈ l → v ∈ U :=
fun {n} {G} {U} {a b} {l} h {v} hv => h.right.right.right.right v hv

theorem PathListIn.toFinset_subset : ∀ {n : ℕ} {G : SimpleGraph (Fin n)} {U : Finset (Fin n)}
  {a b : Fin n} {l : List (Fin n)}, PathListIn G U a b l → l.toFinset ⊆ U :=
fun {n} {G} {U} {a b} {l} h ⦃v⦄ hv => PathListIn.mem_U h (List.mem_toFinset.mp hv)

theorem PathListIn.length_le_card : ∀ {n : ℕ} {G : SimpleGraph (Fin n)} {U : Finset (Fin n)} {a b : Fin n}
  {l : List (Fin n)}, PathListIn G U a b l → l.length ≤ U.card :=
fun {n} {G} {U} {a b} {l} h =>
  Eq.mpr
    (id (congrArg (fun _a => _a ≤ U.card) (Eq.symm (List.toFinset_card_of_nodup (PathListIn.nodup h)))))
    (Finset.card_le_card (PathListIn.toFinset_subset h))


theorem PathListIn.ne_nil : ∀ {n : ℕ} {G : SimpleGraph (Fin n)} {U : Finset (Fin n)} {a b : Fin n}
  {l : List (Fin n)}, PathListIn G U a b l → l ≠ [] :=
fun {n} {G} {U} {a b} {l} h a_1 =>
  Eq.ndrec (motive := fun {l} => PathListIn G U a b l → False)
    (fun h =>
      have hh := PathListIn.head?_eq h;
      False.elim (Eq.mp (eq_false' fun h => False.elim (noConfusion_of_Nat Option.ctorIdx h)) hh))
    (Eq.symm a_1) h

def ReachIn : {n : ℕ} → SimpleGraph (Fin n) → Finset (Fin n) → Fin n → Fin n → Prop :=
fun {n} G Z x y => ∃ w : G.Walk x y, ∀ v ∈ w.support, v ∈ Z

theorem ReachIn.exists_pathList {G : SimpleGraph (Fin n)} {Z : Finset (Fin n)} {x y : Fin n}
    (h : ReachIn G Z x y) : ∃ l, PathListIn G Z x y l := by
  obtain ⟨w, hw⟩ := h
  refine ⟨((w.toPath : G.Path x y) : G.Walk x y).support, ?_, ?_, ?_, ?_, ?_⟩
  · exact (SimpleGraph.Walk.isPath_def _).mp (SimpleGraph.Path.isPath w.toPath)
  · exact Walk_support_isChain _
  · exact Walk_support_head? _
  · exact Walk_support_getLast? _
  · intro v hv
    exact hw v (SimpleGraph.Walk.support_toPath_subset_support w hv)
theorem ReachIn.mono : ∀ {n : ℕ} {G : SimpleGraph (Fin n)} {Z Z' : Finset (Fin n)} {x y : Fin n},
  Z ⊆ Z' → ReachIn G Z x y → ReachIn G Z' x y :=
fun {n} {G} {Z Z'} {x y} h hr => Exists.casesOn hr fun w hw => Exists.intro w fun v hv => h (hw v hv)

theorem ReachIn.refl : ∀ {n : ℕ} {G : SimpleGraph (Fin n)} {Z : Finset (Fin n)} {x : Fin n},
  x ∈ Z → ReachIn G Z x x :=
fun {n} {G} {Z} {x} hx =>
  Exists.intro SimpleGraph.Walk.nil fun v hv =>
    Eq.ndrec (motive := fun {x} => x ∈ Z → v ∈ Z) (fun hx => hx)
      (Eq.mp (congrArg (fun _a => _a) (propext List.mem_singleton))
        (Eq.mp (congrArg (fun _a => v ∈ _a) SimpleGraph.Walk.support_nil) hv))
      hx

theorem ReachIn.symm : ∀ {n : ℕ} {G : SimpleGraph (Fin n)} {Z : Finset (Fin n)} {x y : Fin n},
  ReachIn G Z x y → ReachIn G Z y x :=
fun {n} {G} {Z} {x y} h =>
  Exists.casesOn h fun w hw =>
    Exists.intro w.reverse fun v hv =>
      hw v
        (Eq.mp (congrArg (fun _a => _a) (propext List.mem_reverse))
          (Eq.mp (congrArg (fun _a => v ∈ _a) (SimpleGraph.Walk.support_reverse w)) hv))

theorem ReachIn.trans : ∀ {n : ℕ} {G : SimpleGraph (Fin n)} {Z : Finset (Fin n)} {x y z : Fin n},
  ReachIn G Z x y → ReachIn G Z y z → ReachIn G Z x z :=
fun {n} {G} {Z} {x y z} h₁ h₂ =>
  Exists.casesOn h₁ fun w₁ hw₁ =>
    Exists.casesOn h₂ fun w₂ hw₂ =>
      Exists.intro (w₁.append w₂) fun v hv =>
        Or.casesOn
          (Eq.mp (congrArg (fun _a => _a) (propext List.mem_append))
            (Eq.mp (congrArg (fun _a => v ∈ _a) (SimpleGraph.Walk.support_append w₁ w₂)) hv))
          (fun hv => hw₁ v hv) fun hv => hw₂ v (List.mem_of_mem_tail hv)

def compFinset : {n : ℕ} → SimpleGraph (Fin n) → Finset (Fin n) → Fin n → Finset (Fin n) :=
fun {n} G Z z => {y | ReachIn G Z z y}

namespace compFinsetLemmas

theorem mem_compFinset : ∀ {n : ℕ} {G : SimpleGraph (Fin n)} {Z : Finset (Fin n)}
  {z y : Fin n}, y ∈ compFinset G Z z ↔ ReachIn G Z z y :=
fun {n} {G} {Z} {z y} =>
  Eq.mpr (id (congrArg (fun _a => y ∈ _a ↔ ReachIn G Z z y) (compFinset.eq_1 G Z z)))
    (Eq.mpr (id (congrArg (fun _a => _a ↔ ReachIn G Z z y) (propext Finset.mem_filter)))
      (of_eq_true
        (Eq.trans
          (congrFun'
            (congrArg Iff
              (Eq.trans (congrFun' (congrArg And (Finset.mem_univ._simp_1 y)) (ReachIn G Z z y))
                (true_and (ReachIn G Z z y))))
            (ReachIn G Z z y))
          (iff_self (ReachIn G Z z y)))))

theorem compFinset_subset : ∀ {n : ℕ} {G : SimpleGraph (Fin n)} {Z : Finset (Fin n)}
  {z : Fin n}, compFinset G Z z ⊆ Z :=
fun {n} {G} {Z} {z} ⦃y⦄ hy =>
  Exists.casesOn (mem_compFinset.mp hy) fun w hw =>
    hw y (Walk_mem_support_getLast w)

theorem compFinset_closed : ∀ {n : ℕ} {G : SimpleGraph (Fin n)} {Z : Finset (Fin n)}
  {z x y : Fin n}, x ∈ compFinset G Z z → y ∈ Z → G.Adj x y → y ∈ compFinset G Z z :=
fun {n} {G} {Z} {z x y} hx hy hxy =>
  have hxZ := compFinset_subset hx;
  mem_compFinset.mpr
    (ReachIn.trans (mem_compFinset.mp hx)
      (Exists.intro (SimpleGraph.Walk.cons hxy SimpleGraph.Walk.nil) fun v hv =>
        Or.casesOn
          (Eq.mp (congrArg (fun _a => v = x ∨ _a) (propext List.mem_singleton))
            (Eq.mp (congrArg (fun _a => _a) (propext List.mem_cons))
              (Eq.mp (congrArg (fun _a => v ∈ x :: _a) SimpleGraph.Walk.support_nil)
                (Eq.mp (congrArg (fun _a => v ∈ _a) (SimpleGraph.Walk.support_cons hxy SimpleGraph.Walk.nil)) hv))))
          (fun h =>
            Eq.ndrec (motive := fun {x} => x ∈ compFinset G Z z → G.Adj x y → x ∈ Z → v ∈ Z)
              (fun hx hxy hxZ => hxZ) h hx hxy hxZ)
          fun h => Eq.ndrec (motive := fun {y} => y ∈ Z → G.Adj x y → v ∈ Z) (fun hy hxy => hy) h hy hxy))

theorem compFinset_eq_of_reach : ∀ {n : ℕ} {G : SimpleGraph (Fin n)} {Z : Finset (Fin n)}
  {z z' : Fin n}, ReachIn G Z z z' → compFinset G Z z = compFinset G Z z' :=
fun {n} {G} {Z} {z z'} h =>
  Finset.Subset.antisymm
    (fun ⦃y⦄ hy =>
      mem_compFinset.mpr
        (ReachIn.trans (ReachIn.symm h)
          (mem_compFinset.mp hy)))
    fun ⦃y⦄ hy =>
    mem_compFinset.mpr
      (ReachIn.trans h (mem_compFinset.mp hy))

theorem compFinset_nonempty : ∀ {n : ℕ} {G : SimpleGraph (Fin n)} {Z : Finset (Fin n)}
  {z : Fin n}, z ∈ Z → (compFinset G Z z).Nonempty :=
fun {n} {G} {Z} {z} hz =>
  Exists.intro z (mem_compFinset.mpr (ReachIn.refl hz))

theorem compFinset_disjoint : ∀ {n : ℕ} {G : SimpleGraph (Fin n)} {Z : Finset (Fin n)}
  {z z' : Fin n},
  z' ∉ compFinset G Z z → Disjoint (compFinset G Z z) (compFinset G Z z') :=
fun {n} {G} {Z} {z z'} hzz' =>
  Eq.mpr (id (congrArg (fun _a => _a) (propext Finset.disjoint_left))) fun ⦃y⦄ hy hy' =>
    hzz'
      (mem_compFinset.mpr
        (ReachIn.trans (mem_compFinset.mp hy)
          (ReachIn.symm (mem_compFinset.mp hy'))))

theorem compFinset_not_adj : ∀ {n : ℕ} {G : SimpleGraph (Fin n)} {Z : Finset (Fin n)}
  {z z' x y : Fin n},
  z' ∉ compFinset G Z z →
    x ∈ compFinset G Z z → y ∈ compFinset G Z z' → ¬G.Adj x y :=
fun {n} {G} {Z} {z z' x y} hzz' hx hy hxy =>
  have hyz :=
    compFinset_closed hx (compFinset_subset hy) hxy;
  hzz'
    (mem_compFinset.mpr
      (ReachIn.trans (mem_compFinset.mp hyz)
        (ReachIn.symm (mem_compFinset.mp hy))))

end compFinsetLemmas

theorem list_forall_mem_of_closed : ∀ {n : ℕ} {G : SimpleGraph (Fin n)} {Z D : Finset (Fin n)},
  (∀ v ∈ D, ∀ w ∈ Z, G.Adj v w → w ∈ D) →
    ∀ {l : List (Fin n)},
      List.IsChain G.Adj l →
        (∀ x ∈ l, x ∈ Z) → ∀ {x : Fin n}, x ∈ D → l.head? = some x → ∀ {y : Fin n}, y ∈ l → y ∈ D :=
fun {n} {G} {Z D} hclosed {l} hchain hlZ {x} hx hhead {y} hy =>
  List.rec (motive := fun {l} =>
    List.IsChain G.Adj l → (∀ x ∈ l, x ∈ Z) → ∀ {x : Fin n}, x ∈ D → l.head? = some x → y ∈ l → y ∈ D)
    (fun hchain hlZ {x} hx hhead hy => False.elim (Eq.mp List.not_mem_nil._simp_1 hy))
    (fun a t ih hchain hlZ {x} hx hhead hy =>
      have ha_eq :=
        have hh := hhead;
        Option.some.inj (Eq.mp (congrArg (fun _a => _a = some x) List.head?_cons) hh);
      have haD := Eq.mpr (id (congrArg (fun _a => _a ∈ D) ha_eq)) hx;
      Or.casesOn (Eq.mp (congrArg (fun _a => _a) (propext List.mem_cons)) hy)
        (fun h =>
          Eq.ndrec (motive := fun a =>
            List.IsChain G.Adj (a :: t) → (∀ x ∈ a :: t, x ∈ Z) → (a :: t).head? = some x → a = x → a ∈ D → y ∈ D)
            (fun hchain hlZ hhead ha_eq haD => haD) h hchain hlZ hhead ha_eq haD)
        fun hy =>
        Or.casesOn (Eq.mp (congrArg (fun _a => _a) (propext (List.isChain_cons_iff G.Adj a t))) hchain)
          (fun htnil => False.elim (Eq.mp List.not_mem_nil._simp_1 (Eq.mp (congrArg (fun _a => y ∈ _a) htnil) hy)))
          fun h =>
          Exists.casesOn h fun b h =>
            Exists.casesOn h fun l' h =>
              And.casesOn h fun hab right =>
                And.casesOn right fun hchain' right =>
                  Eq.ndrec (motive := fun t =>
                    (List.IsChain G.Adj t →
                        (∀ x ∈ t, x ∈ Z) → ∀ {x : Fin n}, x ∈ D → t.head? = some x → y ∈ t → y ∈ D) →
                      (∀ x ∈ a :: t, x ∈ Z) → (a :: t).head? = some x → y ∈ t → y ∈ D)
                    (fun ih hlZ hhead hy =>
                      have hbZ := hlZ b (List.mem_cons_of_mem a List.mem_cons_self);
                      have hbD := hclosed a haD b hbZ hab;
                      ih hchain' (fun z hz => hlZ z (List.mem_cons_of_mem a hz)) hbD rfl hy)
                    (Eq.symm right) ih hlZ hhead hy)
    l hchain hlZ hx hhead hy

/-- If `D` is closed under taking edges into `Z`, then no vertex of `D` reaches a vertex
outside `D` by a walk inside `Z`. -/
theorem not_reachIn_of_closed {G : SimpleGraph (Fin n)} {Z D : Finset (Fin n)}
    (hclosed : ∀ v ∈ D, ∀ w ∈ Z, G.Adj v w → w ∈ D) {x : Fin n} (hx : x ∈ D) {y : Fin n}
    (hyD : y ∉ D) : ¬ReachIn G Z x y := by
  rintro ⟨w, hw⟩
  exact hyD (list_forall_mem_of_closed hclosed (Walk_support_isChain w) (fun v hv => hw v hv)
    hx (Walk_support_head? w) (Walk_mem_support_getLast w))
lemma PathListIn.two_le_length {G : SimpleGraph (Fin n)} {U : Finset (Fin n)} {a b : Fin n}
    {l : List (Fin n)} (h : PathListIn G U a b l) (hab : a ≠ b) : 2 ≤ l.length := by
  have hhead : l.head? = some a := h.head?_eq
  have hlast : l.getLast? = some b := h.getLast?_eq
  match l, hhead, hlast with
  | [], h1, _ => simp at h1
  | [_], h1, h2 => simp at h1 h2; exact absurd (h1 ▸ h2 : a = b) hab
  | _ :: _ :: _, _, _ => simp


/-- The hypotheses of the spanning-path theorem `exists_spanningPath_subset`: lower regularity
of `G` inside `U`, the inequalities `ε < p` and `8ε ≤ α`, `1 ≤ ε|U|`, and minimum degree at
least `α|U|` inside `U`. -/
structure SpanHyp (G : SimpleGraph (Fin n)) (U : Finset (Fin n)) (p ε α : ℝ) : Prop where
  lr : LowerRegOn G U p ε
  eps_lt_p : ε < p
  eps_pos : 0 < ε
  epsN_ge_one : 1 ≤ ε * (U.card : ℝ)
  eps_le_alpha : 8 * ε ≤ α
  minDeg : MinDegOn G U α

/-- `U` is nonempty. -/
theorem SpanHyp.N_pos {G : SimpleGraph (Fin n)} {U : Finset (Fin n)} {p ε α : ℝ}
    (h : SpanHyp G U p ε α) : 0 < U.card := by
  have h1 := h.epsN_ge_one
  have h2 := h.eps_pos
  have : (0 : ℝ) < (U.card : ℝ) := by nlinarith
  exact_mod_cast this

/-- `ε * |U| > 0`. -/
theorem SpanHyp.epsN_pos {G : SimpleGraph (Fin n)} {U : Finset (Fin n)} {p ε α : ℝ}
    (h : SpanHyp G U p ε α) : 0 < ε * (U.card : ℝ) :=
  lt_of_lt_of_le zero_lt_one h.epsN_ge_one

/-- `α > 0`. -/
theorem SpanHyp.alpha_pos {G : SimpleGraph (Fin n)} {U : Finset (Fin n)} {p ε α : ℝ}
    (h : SpanHyp G U p ε α) : 0 < α := by
  linarith [h.eps_pos, h.eps_le_alpha]

/-- The bound on the edge connectivity of `G[U]`. -/
theorem SpanHyp.kappa_pos {G : SimpleGraph (Fin n)} {U : Finset (Fin n)} {p ε α : ℝ}
    (h : SpanHyp G U p ε α) : 0 < α * (U.card : ℝ) - ε * (U.card : ℝ) := by
  have hN := h.N_pos
  have hN' : (0 : ℝ) < (U.card : ℝ) := by exact_mod_cast hN
  nlinarith [h.eps_pos, h.eps_le_alpha]

/-- `2 * ε|U| + 1 ≤ α|U| - ε|U|`. -/
theorem SpanHyp.two_mul_epsN_add_one_le_kappa {G : SimpleGraph (Fin n)} {U : Finset (Fin n)} {p ε α : ℝ}
    (h : SpanHyp G U p ε α) :
    2 * (ε * (U.card : ℝ)) + 1 ≤ α * (U.card : ℝ) - ε * (U.card : ℝ) := by
  have hN := h.epsN_ge_one
  have hα := h.eps_le_alpha
  nlinarith [hN, hα]

end

end Work.Deep.GKO
