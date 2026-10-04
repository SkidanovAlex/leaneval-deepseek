import Mathlib
import Submission.Work.Diff.STE.FlatPDE

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Vocabulary for the joint-smoothness bootstrap (`contDiffOn_of_solves_jet`)

This file fixes the vocabulary used by `Work.Diff.STE.Lead.contDiffOn_of_solves_jet`.
Everything is *componentwise*: the unknown `u` is `MatC n`-valued, and the tower of jets is
indexed by a pair `(a,b)` of coordinate directions (the entry of the matrix) and a *word* `w` of
coordinate directions (the spatial derivative); the corresponding function is the `(a,b)`-entry of
the word derivative.

* `Modl n = Fin n → ℝ` — the model space;
* `Mtrx n = MatC n = Fin n → Fin n → ℂ` — the values of the unknown;
* `Wds n m` — the words of length `≤ m` (multi-indices of spatial derivatives of order `≤ m`);
* `pdW u j w` — the spatial derivative of `u` along the word `w`: the first coordinate is the
  outermost derivative, so that `pdList l = pdW · l.length (listOfWord l)` (the `List.foldr`
  convention of `Work.Diff.STE.pdList`);
* `Idx n m = (Fin n × Fin n) × Wds n m` — the index set of the jet tower of order `m`;
* `compTower u m y` — the jet tower of order `m` of `u` at `y`.

The bridges `pdList ↔ pdW` are proved at the end of the file, together with the continuity of the
tower deduced from the jet hypothesis of the main lemma.
-/

open scoped ContDiff BigOperators
open Set Filter

namespace Work.Diff.STE.Lead

variable {n : ℕ}

/-- The model space of the flat problem. -/
abbrev Modl (n : ℕ) := Fin n → ℝ

/-- The value space of the flat problem: `n × n` matrices over `ℂ`. -/
abbrev Mtrx (n : ℕ) := Work.Diff.STE.Flat.MatC n

/-- **Words of length at most `m`**: the multi-indices of the spatial derivatives of order `≤ m`.

A word is a pair `(j, w)` with `j ≤ m` and `w : Fin j → Fin n`; the corresponding derivative is
`∂_{w 0} ∂_{w 1} ⋯ ∂_{w (j-1)}`, i.e. the *first* coordinate is the outermost derivative (the
`List.foldr` convention of `Work.Diff.STE.pdList`). -/
abbrev Wds (n m : ℕ) := (j : Fin (m+1)) × (Fin j.val → Fin n)

/-- The index set of the jet tower of order `m`: a pair of coordinate directions `(a,b)` (an entry
of the matrix) together with a word (a spatial derivative). -/
abbrev Idx (n m : ℕ) := (Fin n × Fin n) × Wds n m

/-- The list of coordinate directions read off a word, by recursion on the length (so that its
length is the length of the word by construction). -/
def listOfWord : (j : ℕ) → (Fin j → Fin n) → List (Fin n)
  | 0, _ => []
  | (j + 1), w => w 0 :: listOfWord j (Fin.tail w)

@[simp] lemma listOfWord_zero (w : Fin 0 → Fin n) : listOfWord 0 w = [] := rfl

lemma listOfWord_succ (j : ℕ) (w : Fin (j + 1) → Fin n) :
    listOfWord (j + 1) w = w 0 :: listOfWord j (Fin.tail w) := rfl

lemma listOfWord_length : ∀ (j : ℕ) (w : Fin j → Fin n), (listOfWord j w).length = j
  | 0, _ => rfl
  | (j + 1), w => by rw [listOfWord_succ, List.length_cons, listOfWord_length j (Fin.tail w)]

/-- Spatial derivatives along a word: `pdW u (j+1) w = ∂_{w 0} (pdW u j (tail w))`. -/
noncomputable def pdW {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    (Modl n → F) → (j : ℕ) → (Fin j → Fin n) → (Modl n → F)
  | u, 0, _ => u
  | u, (j + 1), w => fun y => fderiv ℝ (pdW u j (Fin.tail w)) y (Pi.single (w 0) 1)

@[simp] lemma pdW_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : Modl n → F) (w : Fin 0 → Fin n) : pdW u 0 w = u := rfl

lemma pdW_succ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : Modl n → F) (j : ℕ) (w : Fin (j + 1) → Fin n) :
    pdW u (j + 1) w = fun y => fderiv ℝ (pdW u j (Fin.tail w)) y (Pi.single (w 0) 1) := rfl

lemma pdW_succ_cons {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : Modl n → F) (j : ℕ) (c : Fin n) (w : Fin j → Fin n) :
    pdW u (j + 1) (Fin.cons c w) = fun y => fderiv ℝ (pdW u j w) y (Pi.single c 1) := by
  rw [pdW_succ]
  simp

/-- A one-letter word is the `fderiv` in the corresponding coordinate direction. -/
lemma pdW_one {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : Modl n → F) (c : Fin n) (y : Modl n) :
    pdW u 1 (fun _ : Fin 1 => c) y = fderiv ℝ u y (Pi.single c 1) := rfl

/-- **The bridge between `Work.Diff.STE.pdList` and `pdW`.** -/
theorem pdW_eq_pdList (j : ℕ) (w : Fin j → Fin n) (f : Modl n → ℂ) :
    pdW f j w = Work.Diff.STE.pdList (listOfWord j w) f := by
  induction j with
  | zero => funext y; simp [pdW, Work.Diff.STE.pdList]
  | succ j ih =>
    funext y
    rw [pdW_succ, listOfWord_succ,
      show Work.Diff.STE.pdList (w 0 :: listOfWord j (Fin.tail w)) f =
        fun y => fderiv ℝ (Work.Diff.STE.pdList (listOfWord j (Fin.tail w)) f) y
          (Pi.single (w 0) 1) from rfl]
    rw [← ih (Fin.tail w)]

/-! ## The jet tower of a matrix valued function -/

/-- The jet tower of order `m` of a matrix valued function: the entries of all its spatial
derivatives of order `≤ m`. -/
noncomputable def compTower (u : Modl n → Mtrx n) (m : ℕ) : Modl n → (Idx n m → ℂ) :=
  fun y i => pdW (fun y' => u y' i.1.1 i.1.2) i.2.1.val i.2.2 y

@[simp] lemma compTower_apply (u : Modl n → Mtrx n) (m : ℕ) (y : Modl n) (i : Idx n m) :
    compTower u m y i = pdW (fun y' => u y' i.1.1 i.1.2) i.2.1.val i.2.2 y := rfl

/-- The shift of a word: `β ↦ c :: β`. -/
noncomputable def wshift (c : Fin n) {m : ℕ} (β : Wds n m) : Wds n (m + 1) :=
  ⟨⟨β.1.val + 1, Nat.succ_lt_succ β.1.2⟩, Fin.cons c β.2⟩

/-- The shift of a tower index: only the word is shifted. -/
noncomputable def ishift (c : Fin n) {m : ℕ} (i : Idx n m) : Idx n (m + 1) :=
  (i.1, wshift c i.2)

/-- The linear map sending the `(m+1)`-tower to the derivative of the `m`-tower in the direction
`c`: the component on the index `i` is the `(m+1)`-component on the shifted index. -/
noncomputable def towerShift (c : Fin n) {m : ℕ} :
    (Idx n (m + 1) → ℂ) →L[ℝ] (Idx n m → ℂ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (ishift c i)

@[simp] lemma towerShift_apply (c : Fin n) {m : ℕ} (J : Idx n (m + 1) → ℂ) (i : Idx n m) :
    towerShift c J i = J (ishift c i) := rfl

/-- The **shift derivation**: the derivative in the direction `v` of the tower map is the linear
combination `∑ c, v c • towerShift c ((m+1)-tower)`. -/
noncomputable def towerDeriv {m : ℕ} (v : Modl n) : (Idx n (m + 1) → ℂ) →L[ℝ] (Idx n m → ℂ) :=
  ∑ c : Fin n, (v c) • towerShift (n := n) c

@[simp] lemma towerDeriv_apply {m : ℕ} (v : Modl n) (J : Idx n (m + 1) → ℂ) (i : Idx n m) :
    towerDeriv v J i = ∑ c : Fin n, v c • J (ishift c i) := by
  simp [towerDeriv]

/-! ## Continuity of the tower from the jet hypothesis -/

/-- The word derivative (for a fixed entry `(a,b)`) is jointly continuous on `Ico 0 τ ×ˢ Ω`, given
the hypothesis on `pdList` of the main lemma. -/
theorem continuousOn_pdW {τ : ℝ} {Ω : Set (Modl n)}
    {V : ℝ → Modl n → Mtrx n}
    (hjet : ∀ (l : List (Fin n)) (a b : Fin n), ContinuousOn (fun p : ℝ × Modl n =>
        Work.Diff.STE.pdList l (fun y => V p.1 y a b) p.2) (Set.Ico (0 : ℝ) τ ×ˢ Ω))
    (j : ℕ) (w : Fin j → Fin n) (a b : Fin n) :
    ContinuousOn (fun p : ℝ × Modl n => pdW (fun y' => V p.1 y' a b) j w p.2)
      (Set.Ico (0 : ℝ) τ ×ˢ Ω) := by
  have h : (fun p : ℝ × Modl n => pdW (fun y' => V p.1 y' a b) j w p.2) =
      (fun p : ℝ × Modl n => Work.Diff.STE.pdList (listOfWord j w) (fun y => V p.1 y a b) p.2) := by
    funext p
    exact congrFun (pdW_eq_pdList j w (fun y => V p.1 y a b)) p.2
  rw [h]
  exact hjet (listOfWord j w) a b

/-- The tower of order `m` of the family `t ↦ V t` is jointly continuous on `Ico 0 τ ×ˢ Ω`, given
the componentwise hypothesis of the main lemma. -/
theorem continuousOn_compTower {τ : ℝ} {Ω : Set (Modl n)}
    {V : ℝ → Modl n → Mtrx n}
    (hjet : ∀ (l : List (Fin n)) (a b : Fin n), ContinuousOn (fun p : ℝ × Modl n =>
        Work.Diff.STE.pdList l (fun y => V p.1 y a b) p.2) (Set.Ico (0 : ℝ) τ ×ˢ Ω))
    (m : ℕ) :
    ContinuousOn (fun p : ℝ × Modl n => compTower (V p.1) m p.2) (Set.Ico (0 : ℝ) τ ×ˢ Ω) := by
  rw [continuousOn_pi]
  rintro i
  exact continuousOn_pdW hjet i.2.1.val i.2.2 i.1.1 i.1.2

end Work.Diff.STE.Lead
