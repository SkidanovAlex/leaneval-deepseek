import Mathlib
import Submission.Work.Diff.EXT.ConnCov.RicFlip.TermCalc
import Submission.Work.Diff.EXT.ConnCov.RicFlip.Bnd1CompOSub
import Submission.Work.Diff.EXT.ConnCov.RicFlip.SlotAddP_comp
import Submission.Work.Diff.EXT.ConnCov.RicFlip.OSubChain
import Submission.Work.Diff.EXT.ConnCov.RicFlip.atomEval_smE

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Work.Diff.EXT.ConnCov.RicFlip

/-!
# The uniform honest-tower bound of the connection flip (`honestTowerBoundUniform`)

`honestTowerBoundUniform` bounds the **fixed**-connection honest tower
`pDiter2 (lcOf (G 0)) (ric2 (G t)) k` uniformly in `t ∈ [TT/2, TT)`, from

* bounds on the **moving**-connection honest towers `pDiter2 (lcOf (G t)) (ric2 (G t)) j`, `j ≤ k`
  (`hleaf`),
* bounds on the moving `δ`-towers `deltaTowerM G t ord`, `ord < k` (`hB`),
* the two structural invariants of the term calculus (`hsmT`, `hslot`).

The proof is the *term expansion* of the flip `pD (lcOf (G 0)) = pD (lcOf (G t)) + Ins δ`
(`pD_flip_full`).  The `k`-fold iteration of `pD (lcOf (G 0))` on `ric2 (G t)` is expanded into the
finite list of **terms** `Expand k`, each of which is

* either a *leaf* `pDiter2 (lcOf (G t)) (ric2 (G t)) i` (`i = k` only),
* or a composition of a leaf with one-atom substitutions, whose atoms are the `δ`-towers
  `deltaTowerM G t ord` with `ord < k`;

the `cost` of a term in `Expand m` is exactly `m`, which is what makes the leaf/atom orders fit the
hypotheses.  Every term is bounded by `boundT R Bm`, and summing over the (finitely many) terms of
`Expand k` gives the constant `C = Σ_{T ∈ Expand k} boundT R Bm T`, which does not depend on `t`.

The term calculus (`Term`, `evalT`, `nextT`, `insStep`, `evalList`) is `TermCalc`; the chain rule is
`OSubChain` and the `Bnd1`-bookkeeping of a substitution is `Bnd1CompOSub`.  This file only adds the
*uniform* assembly and the small list bookkeeping missing from `TermCalc`.
-/

namespace HonestUnif

open Work.Diff.EXT.ConnCov.AMB Work.Diff.EXT.ATower

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-! ## List bookkeeping -/

/-- A finite sum of a list sum is the list sum of the finite sums. -/
theorem list_sum_comm {ι α : Type*} [Fintype α] (l : List ι) (f : ι → α → ℝ) :
    (∑ a : α, (l.map (fun T => f T a)).sum) = (l.map (fun T => ∑ a : α, f T a)).sum := by
  induction l with
  | nil => simp
  | cons T l ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [Finset.sum_add_distrib, ih]

/-- A list sum of a difference is the difference of the list sums. -/
theorem list_sum_sub {ι : Type*} (l : List ι) (f g : ι → ℝ) :
    (l.map (fun T => f T - g T)).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons T l ih => rw [List.map_cons, List.map_cons, List.map_cons, List.sum_cons, List.sum_cons,
      List.sum_cons, ih]; ring

/-- The list sum of a `flatMap` is the list sum of the list sums. -/
theorem list_sum_flatMap {ι α : Type*} (l : List ι) (f : ι → List α) (g : α → ℝ) :
    ((l.flatMap f).map g).sum = (l.map (fun i => ((f i).map g).sum)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons]

/-- A finite sum of smooth functions is smooth. -/
theorem smF_list_sum {ι : Type*} (l : List ι) (f : ι → M → ℝ) (hf : ∀ i ∈ l, SmF I M (f i)) :
    SmF I M (fun y : M => (l.map (fun i => f i y)).sum) := by
  induction l with
  | nil =>
      have h : (fun y : M => (List.map (fun i => f i y) ([] : List ι)).sum)
          = fun _ : M => (0 : ℝ) := by
        funext y; simp
      rw [h]
      exact contMDiff_const
  | cons a l ih =>
      have ha : SmF I M (f a) := hf a (by simp)
      have hl : ∀ i ∈ l, SmF I M (f i) := fun i hi => hf i (by simp [hi])
      have h : (fun y : M => (List.map (fun i => f i y) (a :: l)).sum)
          = f a + (fun y : M => (l.map (fun i => f i y)).sum) := by
        funext y; simp
      rw [h]
      exact ha.add (ih hl)

/-- `mvfderiv` of a finite sum of smooth scalar functions. -/
theorem mvfderiv_list_sum {ι : Type*} (l : List ι) (f : ι → M → ℝ) (x : M) (v : TangentSpace I x)
    (hf : ∀ i ∈ l, SmF I M (f i)) :
    mvfderiv I (fun y : M => (l.map (fun i => f i y)).sum) x v
      = (l.map (fun i => mvfderiv I (f i) x v)).sum := by
  induction l with
  | nil =>
      have h : (fun y : M => (List.map (fun i => f i y) ([] : List ι)).sum)
          = fun _ : M => (0 : ℝ) := by
        funext y; simp
      rw [h, List.map_nil, List.sum_nil]
      exact congrArg (fun (L : TangentSpace I x →L[ℝ] ℝ) => L v)
        (mvfderiv_const (0 : ℝ) (x := x))
  | cons a l ih =>
      have ha : SmF I M (f a) := hf a (by simp)
      have hl : ∀ i ∈ l, SmF I M (f i) := fun i hi => hf i (by simp [hi])
      have hsum : (fun y : M => (List.map (fun i => f i y) (a :: l)).sum)
          = f a + (fun y : M => (l.map (fun i => f i y)).sum) := by
        funext y; simp
      rw [hsum, List.map_cons, List.sum_cons]
      rw [mvfderiv_add (g := f a) (g' := fun y : M => (l.map (fun i => f i y)).sum)
        ((ha x).mdifferentiableAt (by simp))
        ((smF_list_sum l f hl x).mdifferentiableAt (by simp))]
      simp only [ContinuousLinearMap.add_apply]
      rw [ih hl]

/-! ## `evalList` bookkeeping -/

theorem evalList_nil (G : ℝ → Submission.Diff.SMet I M) (t : ℝ)
    (base : AMB.Fam (I := I) (M := M) 2) {n : ℕ} (F : Fin n → AMB.TF (I := I) (M := M)) (x : M) :
    evalList G t base ([] : List (Term n)) F x = 0 := rfl

theorem evalList_append (G : ℝ → Submission.Diff.SMet I M) (t : ℝ)
    (base : AMB.Fam (I := I) (M := M) 2) {n : ℕ} (l₁ l₂ : List (Term n))
    (F : Fin n → AMB.TF (I := I) (M := M)) (x : M) :
    evalList G t base (l₁ ++ l₂) F x = evalList G t base l₁ F x + evalList G t base l₂ F x := by
  simp only [evalList, List.map_append, List.sum_append]

theorem evalList_cons (G : ℝ → Submission.Diff.SMet I M) (t : ℝ)
    (base : AMB.Fam (I := I) (M := M) 2) {n : ℕ} (T : Term n) (l : List (Term n))
    (F : Fin n → AMB.TF (I := I) (M := M)) (x : M) :
    evalList G t base (T :: l) F x = evalT G t base T F x + evalList G t base l F x := rfl

/-- Pushing a `comp` into a list. -/
theorem evalList_map_comp (G : ℝ → Submission.Diff.SMet I M) (t : ℝ)
    (base : AMB.Fam (I := I) (M := M) 2) {a b ord : ℕ} (Φ : O.OSub a b ord)
    (l : List (Term b)) (F : Fin a → AMB.TF (I := I) (M := M)) (x : M) :
    evalList G t base (l.map (fun T' => Term.comp Φ T')) F x
      = evalList G t base l (Φ.eval G t F) x := by
  induction l with
  | nil => rfl
  | cons T l ih =>
      rw [List.map_cons, evalList_cons, ih, evalList_cons]
      rfl

/-- `evalList` of a `flatMap` is the sum of the `evalList`s. -/
theorem evalList_flatMap (G : ℝ → Submission.Diff.SMet I M) (t : ℝ)
    (base : AMB.Fam (I := I) (M := M) 2) {m n : ℕ} (l : List (Term m))
    (f : Term m → List (Term n)) (F : Fin n → AMB.TF (I := I) (M := M)) (x : M) :
    evalList G t base (l.flatMap f) F x
      = (l.map (fun T => evalList G t base (f T) F x)).sum := by
  induction l with
  | nil => simp [evalList]
  | cons T l ih =>
      rw [List.flatMap_cons, evalList_append, ih, List.map_cons, List.sum_cons]

/-! ## The structural inputs of the calculus -/

/-- Smoothness of the components of a substituted tuple. -/
theorem eval_smE (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M) (t : ℝ)
    {a b ord : ℕ} (Φ : O.OSub a b ord) (F : Fin a → AMB.TF (I := I) (M := M))
    (hF : ∀ i, SmE I M (F i)) : ∀ i : Fin b, SmE I M (Φ.eval G t F i) := by
  intro i
  by_cases hi : i = Φ.idx
  · subst hi
    rw [O.OSub.eval_atom]
    exact atomEval_smE hLC G t Φ.τ F hF
  · rw [O.OSub.eval_slot Φ F hi]
    exact hF _

/-- **The chain rule for terms**: `pD (lcOf (G t))` of the evaluation of a term is the sum of the
evaluations of `nextT T`. -/
theorem nextT_correct (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M)
    (t : ℝ) (base : AMB.Fam (I := I) (M := M) 2)
    (hslot : ∀ {n : ℕ} (S : Term n),
      AMB.SlotAddP (I := I) (M := M) (evalT G t base S)) :
    ∀ {n : ℕ} (T : Term n) (F : Fin (n + 1) → AMB.TF (I := I) (M := M)),
      (∀ i, SmE I M (F i)) → ∀ x : M,
      AMB.pD (Submission.Diff.lcOf (G t)) (evalT G t base T) F x
        = evalList G t base (nextT T) F x := by
  intro n T
  induction T with
  | leaf i =>
      intro F _ x
      simp only [evalT, nextT, evalList, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero, pDiter2]
  | @comp a b ord Φ T ih =>
      intro F hF x
      have hsmE : ∀ i : Fin b, SmE I M
          (O.OSub.eval G t Φ (fun j : Fin a => F j.succ) i) :=
        fun i => eval_smE hLC G t Φ _ (fun j => hF _) i
      have hchain := OSubChain (I := I) (M := M) hLC G t Φ (evalT G t base T)
        (hslot T) F hF hsmE x
      have hshiftsm : ∀ i : Fin (b + 1), SmE I M ((O.OSub.shift Φ).eval G t F i) :=
        fun i => eval_smE hLC G t (O.OSub.shift Φ) F hF i
      have hih := ih ((O.OSub.shift Φ).eval G t F) hshiftsm x
      have hL : AMB.pD (Submission.Diff.lcOf (G t)) (evalT G t base (Term.comp Φ T)) F x
          = AMB.pD (Submission.Diff.lcOf (G t)) (evalT G t base T)
              ((O.OSub.shift Φ).eval G t F) x
            + evalT G t base T ((O.OSub.deriv Φ).eval G t F) x := hchain
      rw [hL, hih, nextT, evalList_append, evalList_map_comp, evalList_cons]
      simp only [evalList, List.map_nil, List.sum_nil, add_zero]
      rfl

/-- **The insertion expansion**: `Ins (deltaTens G t)` of the evaluation of a term is the sum of the
evaluations of `insStep T`. -/
theorem insStep_correct (G : ℝ → Submission.Diff.SMet I M) (t : ℝ)
    (base : AMB.Fam (I := I) (M := M) 2) {n : ℕ} (T : Term n)
    (F : Fin (n + 1) → AMB.TF (I := I) (M := M)) (x : M) :
    AMB.Ins (deltaTens G t) (evalT G t base T) F x = evalList G t base (insStep T) F x := by
  rw [Ins_deltaTens_eq_sum G t (evalT G t base T) F x]
  have h1 : evalList G t base (insStep T) F x
      = ((List.finRange n).map (fun j => evalT G t base T ((insSub n j).eval G t F) x)).sum := by
    simp only [insStep, evalList, List.map_map]
    rfl
  rw [h1]
  exact Fin.sum_univ_def (fun j : Fin n => evalT G t base T ((insSub n j).eval G t F) x)

/-! ## Linearity of `pD` and `Ins` over finite sums of terms -/

/-- **Linearity of `pD` over a finite sum of terms.** -/
theorem pD_evalList (G : ℝ → Submission.Diff.SMet I M) (t : ℝ)
    (base : AMB.Fam (I := I) (M := M) 2) {n : ℕ} (l : List (Term n))
    (hgood : ∀ T ∈ l, AMB.SmP (evalT G t base T))
    (F : Fin (n + 1) → AMB.TF (I := I) (M := M)) (hF : ∀ i, SmE I M (F i)) (x : M)
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) :
    AMB.pD cov (evalList G t base l) F x
      = (l.map (fun T => AMB.pD cov (evalT G t base T) F x)).sum := by
  have hsm : ∀ T ∈ l, SmF I M (evalT G t base T (fun j : Fin n => F j.succ)) :=
    fun T hT => hgood T hT _ (fun j => hF _)
  have he : (evalList G t base l (fun j : Fin n => F j.succ))
      = fun y : M => (l.map (fun T => evalT G t base T (fun j : Fin n => F j.succ) y)).sum := by
    funext y; rfl
  have h1 : mvfderiv I (evalList G t base l (fun j : Fin n => F j.succ)) x (F 0 x)
      = (l.map (fun T => mvfderiv I (evalT G t base T (fun j : Fin n => F j.succ)) x
          (F 0 x))).sum := by
    rw [he]
    exact mvfderiv_list_sum l (fun T => fun y => evalT G t base T (fun j : Fin n => F j.succ) y) x
      (F 0 x) hsm
  have h2 : (∑ j : Fin n, (l.map (fun T => evalT G t base T
        (Function.update (fun i : Fin n => F i.succ) j
          (fun y => cov (F j.succ) y (F 0 y))) x)).sum)
      = (l.map (fun T => ∑ j : Fin n, evalT G t base T
        (Function.update (fun i : Fin n => F i.succ) j
          (fun y => cov (F j.succ) y (F 0 y))) x)).sum :=
    list_sum_comm l (fun T j => evalT G t base T
      (Function.update (fun i : Fin n => F i.succ) j
        (fun y => cov (F j.succ) y (F 0 y))) x)
  simp only [AMB.pD, evalList]
  rw [h1, h2, list_sum_sub]

/-- **Linearity of `Ins` over a finite sum of terms.** -/
theorem Ins_evalList (G : ℝ → Submission.Diff.SMet I M) (t : ℝ)
    (base : AMB.Fam (I := I) (M := M) 2) {n : ℕ} (l : List (Term n))
    (F : Fin (n + 1) → AMB.TF (I := I) (M := M)) (x : M) :
    AMB.Ins (deltaTens G t) (evalList G t base l) F x
      = (l.map (fun T => AMB.Ins (deltaTens G t) (evalT G t base T) F x)).sum := by
  have h1 : AMB.Ins (deltaTens G t) (evalList G t base l) F x
      = ∑ j : Fin n, (l.map (fun T => evalT G t base T
          (Function.update (fun i : Fin n => F i.succ) j
            (deltaTens G t (F j.succ) (F 0))) x)).sum := by
    simp only [AMB.Ins, evalList]
  rw [h1, list_sum_comm]
  simp only [AMB.Ins]

/-! ## The cost and the bound constants -/

/-- The **cost** of a term: the order of its leaf plus the orders of the inserted atoms. -/
noncomputable def costT : {n : ℕ} → Term n → ℕ
  | _, Term.leaf i => i
  | _, @Term.comp _ _ ord _ T => costT T + (ord + 1)

/-- The **bound constant** of a term: `R i` at a leaf, multiplied by `(1 + Bm ord)` at a `comp`. -/
noncomputable def boundT (R Bm : ℕ → ℝ) : {n : ℕ} → Term n → ℝ
  | _, Term.leaf i => R i
  | _, @Term.comp _ _ ord _ T => boundT R Bm T * (1 + Bm ord)

/-- The leaf order of a term. -/
noncomputable def leafOrd : {n : ℕ} → Term n → ℕ
  | _, Term.leaf i => i
  | _, Term.comp _ T => leafOrd T

@[simp] theorem costT_leaf (i : ℕ) : costT (Term.leaf i) = i := rfl
@[simp] theorem costT_comp {a b ord : ℕ} (Ψ : O.OSub a b ord) (T : Term b) :
    costT (Term.comp Ψ T) = costT T + (ord + 1) := rfl
@[simp] theorem boundT_leaf (R Bm : ℕ → ℝ) (i : ℕ) : boundT R Bm (Term.leaf i) = R i := rfl
@[simp] theorem boundT_comp (R Bm : ℕ → ℝ) {a b ord : ℕ} (Ψ : O.OSub a b ord) (T : Term b) :
    boundT R Bm (Term.comp Ψ T) = boundT R Bm T * (1 + Bm ord) := rfl
@[simp] theorem leafOrd_leaf (i : ℕ) : leafOrd (Term.leaf i) = i := rfl
@[simp] theorem leafOrd_comp {a b ord : ℕ} (Ψ : O.OSub a b ord) (T : Term b) :
    leafOrd (Term.comp Ψ T) = leafOrd T := rfl

/-- The cost of the terms produced by the chain rule is the cost of the term plus one. -/
theorem costT_mem_nextT : ∀ {n : ℕ} (T : Term n) (S : Term (n+1)),
    S ∈ nextT T → costT S = costT T + 1 := by
  intro n T
  induction T with
  | leaf i =>
      intro S hS
      rw [nextT, List.mem_singleton] at hS
      subst hS
      simp
  | @comp a b ord Ψ T ih =>
      intro S hS
      rw [nextT, List.mem_append, List.mem_map] at hS
      rcases hS with ⟨T', hT', rfl⟩ | hS
      · rw [costT_comp Ψ.shift T', ih T' hT', costT_comp Ψ T]
        omega
      · rw [List.mem_singleton] at hS
        subst hS
        rw [costT_comp Ψ.deriv T, costT_comp Ψ T]
        omega

/-- The cost of the terms produced by the insertion expansion is the cost of the term plus one. -/
theorem costT_mem_insStep : ∀ {n : ℕ} (T : Term n) (S : Term (n+1)),
    S ∈ insStep T → costT S = costT T + 1 := by
  intro n T S hS
  rw [insStep, List.mem_map] at hS
  obtain ⟨j, _, rfl⟩ := hS
  rw [costT_comp (insSub n j) T]

/-! ## The expansion of `(pD (lcOf (G 0)))^k (ric2 (G t))` -/

/-- **The expansion of the fixed-connection iteration.**  `Expand m` is the list of terms obtained by
expanding `(pD (lcOf (G t)) + Ins (deltaTens G t))^m` applied to a base. -/
noncomputable def Expand : (m : ℕ) → List (Term (m + 2))
  | 0 => [Term.leaf 0]
  | (m+1) => (Expand m).flatMap (fun T => nextT T ++ insStep T)

theorem Expand_zero : Expand 0 = [Term.leaf 0] := rfl

theorem Expand_succ (m : ℕ) :
    Expand (m + 1) = (Expand m).flatMap (fun T => nextT T ++ insStep T) := rfl

/-- Every term of the expansion of level `m` has cost exactly `m`. -/
theorem costT_mem_Expand (m : ℕ) (T : Term (m + 2)) (h : T ∈ Expand m) : costT T = m := by
  induction m with
  | zero =>
      rw [Expand_zero, List.mem_singleton] at h
      subst h
      simp
  | succ m ih =>
      rw [Expand_succ, List.mem_flatMap] at h
      obtain ⟨S, hS, hT⟩ := h
      have hcS := ih S hS
      rw [List.mem_append] at hT
      rcases hT with hT | hT
      · rw [costT_mem_nextT S T hT, hcS]
      · rw [costT_mem_insStep S T hT, hcS]

/-! ## The bound of a single term, and of a list of terms -/

/-- Nonnegativity of the bound constant. -/
theorem boundT_nonneg (R Bm : ℕ → ℝ) (hR : ∀ i, 0 ≤ R i) (hBm : ∀ ord, 0 ≤ Bm ord) :
    ∀ {n : ℕ} (T : Term n), 0 ≤ boundT R Bm T := by
  intro n T
  induction T with
  | leaf i => exact hR i
  | @comp a b ord Ψ T ih =>
      rw [boundT_comp]
      exact mul_nonneg ih (by linarith [hBm ord])

/-- **The bound of every term of cost `≤ k`**, by induction on the term using `Bnd1CompOSub`. -/
theorem term_bound (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M)
    (t : ℝ) (base : AMB.Fam (I := I) (M := M) 2) (R Bm : ℕ → ℝ) (k : ℕ)
    (hR : ∀ i, 0 ≤ R i) (hBm : ∀ ord, 0 ≤ Bm ord)
    (hleaf : ∀ j, j ≤ k → AMB.Bnd1 G t (pDiter2 (Submission.Diff.lcOf (G t)) base j) (R j))
    (hB : ∀ ord, ord < k → AMB.BndV G t (deltaTowerM G t ord) (Bm ord)) :
    ∀ {n : ℕ} (T : Term n) (m : ℕ), m ≤ k → costT T = m →
      AMB.Bnd1 G t (evalT G t base T) (boundT R Bm T) := by
  intro n T
  induction T with
  | leaf i =>
      intro m hm hc
      rw [costT_leaf] at hc
      subst hc
      exact hleaf i hm
  | @comp a b ord Ψ T ih =>
      intro m hm hc
      rw [costT_comp] at hc
      have hle : costT T ≤ k := by omega
      have hord : ord < k := by omega
      have h1 := ih (costT T) hle rfl
      have h2 := Bnd1CompOSub (I := I) (M := M) hLC G t Ψ
        (boundT_nonneg R Bm hR hBm T) h1 (hBm ord) (hB ord hord)
      rw [boundT_comp]
      exact h2

/-- **The bound of a list of terms**: the triangle inequality plus the distributivity of the finite
sum over the common product. -/
theorem bnd1_evalList (G : ℝ → Submission.Diff.SMet I M) (t : ℝ)
    (base : AMB.Fam (I := I) (M := M) 2) {n : ℕ} (l : List (Term n)) (c : Term n → ℝ)
    (h : ∀ T ∈ l, AMB.Bnd1 G t (evalT G t base T) (c T)) :
    AMB.Bnd1 G t (evalList G t base l) ((l.map c).sum) := by
  induction l with
  | nil =>
      intro F x _
      simp [evalList]
  | cons T l ih =>
      intro F x hF
      rw [evalList_cons, List.map_cons, List.sum_cons]
      have hhead := h T (by simp) F x hF
      have htail := ih (fun S hS => h S (by simp [hS])) F x hF
      calc |evalT G t base T F x + evalList G t base l F x|
          ≤ |evalT G t base T F x| + |evalList G t base l F x| := abs_add_le _ _
        _ ≤ c T * ∏ j : Fin n, (1 + Real.sqrt ((G t).inner x (F j x) (F j x)))
            + (l.map c).sum * ∏ j : Fin n, (1 + Real.sqrt ((G t).inner x (F j x) (F j x))) :=
              add_le_add hhead htail
        _ = (c T + (l.map c).sum) * ∏ j : Fin n, (1 + Real.sqrt ((G t).inner x (F j x) (F j x))) := by
              ring

/-! ## The correctness of the expansion -/

/-- Smoothness of a one-slot update by a connection correction. -/
theorem smE_update_succ {m : ℕ} (hLC : Submission.Diff.LCSmooth I M)
    (g : Submission.Diff.SMet I M) (F : Fin (m + 3) → AMB.TF (I := I) (M := M))
    (hF : ∀ j, SmE I M (F j)) (j : Fin (m + 2)) :
    ∀ i, SmE I M ((Function.update (fun i : Fin (m + 2) => F i.succ) j
        (fun y => Submission.Diff.lcOf g (F j.succ) y (F 0 y))) i) := by
  intro i
  by_cases hi : i = j
  · rw [hi, Function.update_self]
    exact lcOf_apply_smE hLC g (F j.succ) (F 0) (hF _) (hF 0)
  · rw [Function.update_of_ne hi]
    exact hF _

/-- **The expansion is correct**: the sum of the evaluations of the terms of `Expand m` is the
`m`-fold iteration of the fixed-connection derivative. -/
theorem expand_correct (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M)
    (t : ℝ) (base : AMB.Fam (I := I) (M := M) 2)
    (hsmT : ∀ {n : ℕ} (T : Term n), AMB.SmP (evalT G t base T))
    (hslot : ∀ {n : ℕ} (T : Term n), AMB.SlotAddP (evalT G t base T)) :
    ∀ (m : ℕ) (F : Fin (m + 2) → AMB.TF (I := I) (M := M)), (∀ j, SmE I M (F j)) →
      (fun y : M => evalList G t base (Expand m) F y)
        = fun y : M => pDiter2 (Submission.Diff.lcOf (G 0)) base m F y := by
  intro m
  induction m with
  | zero =>
      intro F hF
      funext y
      rw [Expand_zero]
      simp only [evalList, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        evalT, pDiter2, add_zero]
  | succ m ih =>
      intro F hF
      funext y
      have hF' : ∀ j : Fin (m + 2), SmE I M ((fun i : Fin (m + 2) => F i.succ) j) :=
        fun j => hF _
      have hletter : ∀ T ∈ (Expand m), evalList G t base (nextT T ++ insStep T) F y
          = AMB.pD (Submission.Diff.lcOf (G 0)) (evalT G t base T) F y := by
        intro T hT
        rw [evalList_append, pD_flip_full hLC G t (hslot T) F hF]
        simp only [Pi.add_apply]
        rw [nextT_correct hLC G t base hslot T F hF y, insStep_correct G t base T F y]
      have hpD : AMB.pD (Submission.Diff.lcOf (G 0)) (evalList G t base (Expand m)) F y
          = ((Expand m).map (fun T => AMB.pD (Submission.Diff.lcOf (G 0))
              (evalT G t base T) F y)).sum :=
        pD_evalList G t base (Expand m) (fun T _ => hsmT T) F hF y (Submission.Diff.lcOf (G 0))
      have hfun : evalList G t base (Expand m) (fun j : Fin (m + 2) => F j.succ)
          = pDiter2 (Submission.Diff.lcOf (G 0)) base m (fun j : Fin (m + 2) => F j.succ) :=
        funext (fun z => congrFun (ih (fun j : Fin (m + 2) => F j.succ) hF') z)
      have hstep : AMB.pD (Submission.Diff.lcOf (G 0)) (evalList G t base (Expand m)) F y
          = AMB.pD (Submission.Diff.lcOf (G 0))
              (pDiter2 (Submission.Diff.lcOf (G 0)) base m) F y := by
        have hpt : ∀ (S : Fin (m + 2) → AMB.TF (I := I) (M := M)), (∀ j, SmE I M (S j)) →
            evalList G t base (Expand m) S y
              = pDiter2 (Submission.Diff.lcOf (G 0)) base m S y :=
          fun S hS => congrFun (ih S hS) y
        simp only [AMB.pD]
        rw [hfun]
        congr 1
        refine Finset.sum_congr rfl (fun j _ => ?_)
        exact hpt _ (smE_update_succ hLC (G 0) F hF j)
      rw [Expand_succ, evalList_flatMap, List.map_congr_left hletter, ← hpD, hstep]
      simp only [pDiter2]

end HonestUnif

theorem honestTowerBoundUniform
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) {TT : ℝ} (hT : 0 < TT) (k : ℕ) (Bm R : ℕ → ℝ)
    (hBm : ∀ j, 0 ≤ Bm j) (hR : ∀ j, 0 ≤ R j)
    (hleaf : ∀ j, j ≤ k → ∀ t ∈ Set.Ico (TT / 2) TT,
      Work.Diff.EXT.ConnCov.AMB.Bnd1 G t
        (Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf (G t))
          (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t)) j) (R j))
    (hB : ∀ ord, ord < k → ∀ t ∈ Set.Ico (TT / 2) TT,
      Work.Diff.EXT.ConnCov.AMB.BndV G t
        (Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM G t ord) (Bm ord))
    (hsmT : ∀ t ∈ Set.Ico (TT / 2) TT, ∀ {n : ℕ}
      (Tm : Work.Diff.EXT.ConnCov.RicFlip.Term n),
      Work.Diff.EXT.ConnCov.AMB.SmP (I := I) (M := M)
        (Work.Diff.EXT.ConnCov.RicFlip.evalT G t
          (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t)) Tm))
    (hslot : ∀ t ∈ Set.Ico (TT / 2) TT, ∀ {n : ℕ}
      (Tm : Work.Diff.EXT.ConnCov.RicFlip.Term n),
      Work.Diff.EXT.ConnCov.AMB.SlotAddP (I := I) (M := M)
        (Work.Diff.EXT.ConnCov.RicFlip.evalT G t
          (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t)) Tm)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico (TT / 2) TT,
      Work.Diff.EXT.ConnCov.AMB.Bnd1 G t
        (Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf (G 0))
          (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t)) k) C := by
  refine ⟨(List.map (HonestUnif.boundT R Bm) (HonestUnif.Expand k)).sum, ?_, ?_⟩
  · refine List.sum_nonneg (fun x hx => ?_)
    obtain ⟨T, hT, hbT⟩ := List.mem_map.mp hx
    rw [← hbT]
    exact HonestUnif.boundT_nonneg R Bm hR hBm T
  · intro t ht
    have hsm : ∀ {n : ℕ} (T : Work.Diff.EXT.ConnCov.RicFlip.Term n),
        Work.Diff.EXT.ConnCov.AMB.SmP (I := I) (M := M)
          (Work.Diff.EXT.ConnCov.RicFlip.evalT G t
            (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t)) T) :=
      fun T => hsmT t ht T
    have hsl : ∀ {n : ℕ} (T : Work.Diff.EXT.ConnCov.RicFlip.Term n),
        Work.Diff.EXT.ConnCov.AMB.SlotAddP (I := I) (M := M)
          (Work.Diff.EXT.ConnCov.RicFlip.evalT G t
            (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t)) T) :=
      fun T => hslot t ht T
    have hcorr := HonestUnif.expand_correct (I := I) (M := M) hLC G t
      (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t)) hsm hsl k
    have hbnd := HonestUnif.bnd1_evalList (I := I) (M := M) G t
      (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t)) (HonestUnif.Expand k)
      (HonestUnif.boundT R Bm)
      (fun T hT => HonestUnif.term_bound (I := I) (M := M) hLC G t
        (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t)) R Bm k hR hBm
        (fun j hj => hleaf j hj t ht) (fun ord ho => hB ord ho t ht) T k (le_refl k)
        (HonestUnif.costT_mem_Expand k T hT))
    intro F x hF
    rw [← congrFun (hcorr F hF) x]
    exact hbnd F x hF

end Work.Diff.EXT.ConnCov.RicFlip
