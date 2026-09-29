import Mathlib
import Submission.HvdH.Interfaces

/-!
# Tensoring the one-dimensional resampling words: shared definitions

`progTensorB` (paper Theorem 4.1, the `B̃` half) applies the uniform one-dimensional word `q` of
`SliceSpecB` along all `D` axes of a flat lexicographic array.

This file contains the definitions shared between the program and its correctness proof:

* `WordM` — `WordR` extended with explicit descriptions of the *non-zero* stacks as lists of
  self-delimiting values (each on top of an arbitrary, fixed raw suffix).  The program parks the
  array on stack 1, keeps the per-axis data on stacks 2–6 and the temporaries on stacks 7–10, so it
  needs this extra bookkeeping; the FRAME below everything is inherited from `WordR`.
* `axisPairs`, `midAxis`, `progAxis` — the axis-by-axis application of a one-dimensional map on
  flat lexicographic arrays, in the exact `slices`/`unslices` layout of `LayoutLib.applyAlong`
  (list level), and its `D`-fold composition.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-! ## The extended Hoare triple -/

/-- `WordM main p Pre Post C`: for every value stack `vs` and every description `a` of the non-zero
stacks as value lists satisfying `Pre`, every state whose stack 0 is `encs vs ++ R` and whose stack
`k ≠ 0` is `encs (a k) ++ Bg k`: `p` terminates with cost `≤ C vs a`, producing `out`, `b` with
`Post vs a out b`, stack 0 `encs out ++ R`, stack `k ≠ 0` equal to `encs (b k) ++ Bg k`. -/
def WordM (main p : Cmd) (Pre : List Val → (Stk → List Val) → Prop)
    (Post : List Val → (Stk → List Val) → List Val → (Stk → List Val) → Prop)
    (C : List Val → (Stk → List Val) → ℕ) : Prop :=
  ∀ (vs : List Val) (a : Stk → List Val), Pre vs a →
  ∀ (s : State) (R : List Glyph) (Bg : Stk → List Glyph),
    s.stk 0 = encs vs ++ R → (∀ k : Stk, k ≠ 0 → s.stk k = encs (a k) ++ Bg k) →
    ∃ (out : List Val) (b : Stk → List Val) (s' : State) (n : ℕ),
      Post vs a out b ∧ Eval main p s s' n ∧ n ≤ C vs a ∧
      s'.stk 0 = encs out ++ R ∧ (∀ k : Stk, k ≠ 0 → s'.stk k = encs (b k) ++ Bg k)

/-- `WordR` gives a `WordM` with the non-zero stacks unchanged. -/
theorem WordM.ofWordR {main p : Cmd} {Pre : List Val → Prop}
    {Post : List Val → List Val → Prop} {C : List Val → ℕ}
    (h : WordR main p Pre Post C) :
    WordM main p (fun vs _ => Pre vs) (fun vs a out b => Post vs out ∧ b = a)
      (fun vs _ => C vs) := by
  intro vs a hPre s R Bg h0 hk
  obtain ⟨out, s', n, hPost, hev, hc, h0', hk'⟩ := h vs hPre s R h0
  refine ⟨out, a, s', n, ⟨hPost, rfl⟩, hev, hc, h0', ?_⟩
  intro k hk0
  rw [hk' k hk0]
  exact hk k hk0

/-- Composition of two `WordM` programs. -/
theorem WordM.seq {main : Cmd} {p q : Cmd}
    {Pre₁ : List Val → (Stk → List Val) → Prop}
    {Post₁ : List Val → (Stk → List Val) → List Val → (Stk → List Val) → Prop}
    {Pre₂ : List Val → (Stk → List Val) → Prop}
    {Post₂ : List Val → (Stk → List Val) → List Val → (Stk → List Val) → Prop}
    {C₁ : List Val → (Stk → List Val) → ℕ} {C₂ : List Val → (Stk → List Val) → ℕ}
    {B : List Val → (Stk → List Val) → ℕ}
    (h₁ : WordM main p Pre₁ Post₁ C₁) (h₂ : WordM main q Pre₂ Post₂ C₂)
    (hpre : ∀ vs a mid a', Post₁ vs a mid a' → Pre₂ mid a')
    (hcost : ∀ vs a mid a', Post₁ vs a mid a' → C₂ mid a' ≤ B vs a) :
    WordM main (.seq p q) Pre₁
      (fun vs a out b => ∃ mid a', Post₁ vs a mid a' ∧ Post₂ mid a' out b)
      (fun vs a => C₁ vs a + B vs a) := by
  intro vs a hPre s R Bg h0 hk
  obtain ⟨mid, a', s', n₁, hP₁, hev₁, hc₁, h0', hk'⟩ := h₁ vs a hPre s R Bg h0 hk
  obtain ⟨out, b, s'', n₂, hP₂, hev₂, hc₂, h0'', hk''⟩ :=
    h₂ mid a' (hpre vs a mid a' hP₁) s' R Bg h0' hk'
  refine ⟨out, b, s'', n₁ + n₂, ⟨mid, a', hP₁, hP₂⟩, Eval.seq hev₁ hev₂, ?_, h0'', hk''⟩
  exact Nat.add_le_add hc₁ (le_trans hc₂ (hcost vs a mid a' hP₁))

/-- Consequence rule for `WordM`. -/
theorem WordM.conseq {main p : Cmd}
    {Pre : List Val → (Stk → List Val) → Prop}
    {Post : List Val → (Stk → List Val) → List Val → (Stk → List Val) → Prop}
    {C : List Val → (Stk → List Val) → ℕ}
    {Pre' : List Val → (Stk → List Val) → Prop}
    {Post' : List Val → (Stk → List Val) → List Val → (Stk → List Val) → Prop}
    {C' : List Val → (Stk → List Val) → ℕ}
    (h : WordM main p Pre Post C) (h1 : ∀ vs a, Pre' vs a → Pre vs a)
    (h2 : ∀ vs a out b, Pre' vs a → Post vs a out b → Post' vs a out b)
    (h3 : ∀ vs a, Pre' vs a → C vs a ≤ C' vs a) : WordM main p Pre' Post' C' := by
  intro vs a hPre s R Bg h0 hk
  obtain ⟨out, b, s', n, hPost, hev, hc, h0', hk'⟩ := h vs a (h1 vs a hPre) s R Bg h0 hk
  exact ⟨out, b, s', n, h2 vs a out b hPre hPost, hev, le_trans hc (h3 vs a hPre), h0', hk'⟩

/-- Monotone cost bound for `WordM`. -/
theorem WordM.mono {main p : Cmd} {Pre : List Val → (Stk → List Val) → Prop}
    {Post : List Val → (Stk → List Val) → List Val → (Stk → List Val) → Prop}
    {C C' : List Val → (Stk → List Val) → ℕ}
    (h : WordM main p Pre Post C) (hC : ∀ vs a, C vs a ≤ C' vs a) : WordM main p Pre Post C' :=
  fun vs a hP s R Bg h0 hk => by
    obtain ⟨out, b, s', n, hPost, hev, hc, h0', hk'⟩ := h vs a hP s R Bg h0 hk
    exact ⟨out, b, s', n, hPost, hev, le_trans hc (hC vs a), h0', hk'⟩

/-- Building a `WordM` program from `Ev`-level facts. -/
theorem WordM.ofEv (main p : Cmd) (Pre : List Val → (Stk → List Val) → Prop)
    (Post : List Val → (Stk → List Val) → List Val → (Stk → List Val) → Prop)
    (C : List Val → (Stk → List Val) → ℕ)
    (h : ∀ (vs : List Val) (a : Stk → List Val), Pre vs a →
      ∀ (s : State) (R : List Glyph) (Bg : Stk → List Glyph),
      s.stk 0 = encs vs ++ R → (∀ k : Stk, k ≠ 0 → s.stk k = encs (a k) ++ Bg k) →
      ∃ (out : List Val) (b : Stk → List Val) (s' : State) (n : ℕ),
        Post vs a out b ∧ Eval main p s s' n ∧ n ≤ C vs a ∧
        s'.stk 0 = encs out ++ R ∧ (∀ k : Stk, k ≠ 0 → s'.stk k = encs (b k) ++ Bg k)) :
    WordM main p Pre Post C :=
  fun vs a hP s R Bg h0 hk => h vs a hP s R Bg h0 hk

/-! ## The axis-by-axis application on flat arrays (list level) -/

/-- The input slice `s` of a flat `A × m × B` pair-array (`slices` layout, `getD` outside). -/
def sliceIn (m B : ℕ) (zs : List (ℤ × ℤ)) (s j : ℕ) : ℤ × ℤ :=
  zs.getD ((s / B * m + j) * B + s % B) (0, 0)

/-- Applying a one-dimensional map along the middle axis of a flat `A × m × B` pair-array, in the
exact `slices`/`unslices` layout used by `LayoutLib.applyAlong`. -/
noncomputable def axisPairs (A m n B : ℕ) (Φ : (Fin m → ℤ × ℤ) → (Fin n → ℤ × ℤ))
    (zs : List (ℤ × ℤ)) : List (ℤ × ℤ) :=
  (List.range (A * n * B)).map fun idx =>
    (List.ofFn (Φ (fun j => sliceIn m B zs (idx / (n * B) * B + idx % B) (j : ℕ)))).getD (idx / B % n) (0, 0)

/-- The same axis application, on `Fin`-indexed arrays. -/
noncomputable def midAxis (A m n B : ℕ) (Φ : (Fin m → ℤ × ℤ) → (Fin n → ℤ × ℤ))
    (u : Fin (A * m * B) → ℤ × ℤ) : Fin (A * n * B) → ℤ × ℤ :=
  fun idx => (List.ofFn (Φ (fun j =>
      (List.ofFn u).getD (((idx : ℕ) / (n * B) * m + (j : ℕ)) * B + (idx : ℕ) % B) (0, 0)))).getD
        ((idx : ℕ) / B % n) (0, 0)

/-- The `D`-fold composition of the axis applications, in the order and with the outer/inner
products used by the program: axis `i` (0-based) has outer product `∏_{k<i} s k`, slice length
`t i`, output slice length `s i` and inner product `∏_{k>i} t k`. -/
noncomputable def progAxis (ss ts : List ℕ)
    (Φ : (i : ℕ) → (Fin (ts.getD i 0) → ℤ × ℤ) → (Fin (ss.getD i 0) → ℤ × ℤ)) :
    ℕ → List (ℤ × ℤ) → List (ℤ × ℤ)
  | 0, zs => zs
  | (i + 1), zs => axisPairs (ss.take i).prod (ts.getD i 0) (ss.getD i 0) (ts.drop (i + 1)).prod
      (Φ i) (progAxis ss ts Φ i zs)

end Work.Resample

namespace Work.Resample

open HvdH


/-- Upper bound on the encoded size of a table produced by `prep` for one axis, used both as the
safety margin for the marker `M` and to bound the cleanup cost. -/
def PBTab (Kb p : ℕ) (ts : List ℕ) : ℕ := Kb * (ts.sum + 1) * (p + 1) ^ Kb + 4 * (p + 3)

/-- The per-round invariant of `progTensorB`: stack 0 holds the current array, the marker `M` and the
honest suffix `rest`; the auxiliary stacks hold the remaining dimension lists, `p`, `α`, the running
outer product `A`, the running inner product `B`, and the empty per-round stash registers.  The array
is the `j`-fold axis application of `Φ` to `zs0`, all its entries are in the disc, and `M` is larger
than any table `prep` can produce (and not much larger). -/
def PBInv (p α : ℕ) (ss ts : List ℕ) (Kb : ℕ)
    (Φ : (i : ℕ) → (Fin (ts.getD i 0) → ℤ × ℤ) → (Fin (ss.getD i 0) → ℤ × ℤ))
    (zs0 : List (ℤ × ℤ)) (M : Val) (rest : List Val) (j : ℕ)
    (vs : List Val) (a : Stk → List Val) : Prop :=
  vs = cvecVal (progAxis ss ts Φ j zs0) :: M :: rest ∧
  (progAxis ss ts Φ j zs0).length = (ss.take j).prod * (ts.drop j).prod ∧
  (∀ z ∈ progAxis ss ts Φ j zs0, inDisc p z) ∧
  PBTab Kb p ts < vsz M ∧ vsz M ≤ PBTab Kb p ts + 3 ∧
  a 1 = [] ∧ a 2 = [intList (ts.drop j)] ∧ a 3 = [intList (ss.drop j)] ∧
  a 4 = [.int α] ∧ a 5 = [.int p] ∧
  a 6 = [.int ((ss.take j).prod)] ∧ a 7 = [.int ((ts.drop j).prod)] ∧
  a 8 = [] ∧ a 9 = [] ∧ a 10 = [] ∧ a 11 = [] ∧ a 12 = [M] ∧ a 13 = [] ∧
  (∀ k : Stk, k ≠ 0 → (k : ℕ) ∉ ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13} : Finset ℕ) →
    a k = [])


/-- The one-dimensional resampling specification of `hB` (the body of `SliceSpecB`'s quantification)
extracted for a specific map `Φ` and table `P` at the parameters `(p, α, s, t)`, with the uniform
cost constant `Kb` and the words `prep`, `q`. -/
def SliceSpecAt (prep q : Cmd) (Kb p α s t : ℕ)
    (Φ : (Fin t → ℤ × ℤ) → (Fin s → ℤ × ℤ)) (P : List Val) : Prop :=
  (∀ (main : Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → MulBelow main N Cm → Kb * p < N →
    WordR main prep (fun vs => ∃ rest, vs = .int p :: .int α :: .int s :: .int t :: rest)
      (fun vs out => ∃ rest,
        vs = .int p :: .int α :: .int s :: .int t :: rest ∧ out = P ++ rest)
      (fun _ => Kb * (t + 1) * (p + 1) ^ Kb)) ∧
  (∀ (main : Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → MulBelow main N Cm → Kb * p < N →
    WordR main q
      (fun vs => ∃ (u : List (ℤ × ℤ)) (rest : List Val),
        vs = ofList (u.map cfxVal) :: P ++ rest ∧ u.length = t ∧ (∀ z ∈ u, inDisc p z))
      (fun vs out => ∃ (u : List (ℤ × ℤ)) (rest : List Val) (w : List (ℤ × ℤ)),
        vs = ofList (u.map cfxVal) :: P ++ rest ∧ out = cvecVal w :: P ++ rest ∧ w.length = s ∧
          (∀ z ∈ w, inDisc p z) ∧ (∀ k : Fin s, w.getD k (0, 0) = Φ (fun j => u.getD j (0, 0)) k))
      (fun _ => Kb * (t + 1) * (Nat.sqrt p + 1) * (α + 1) * (Cm (Kb * p) + p + 1) +
        Kb * (t + 1) * (p + 1) ^ 2)) ∧
  (∀ w : Fin t → ℤ × ℤ, (∀ j, inDisc p (w j)) → ∀ k : Fin s, inDisc p (Φ w k)) ∧
  (∀ w : Fin t → ℤ × ℤ, (∀ j, inDisc p (w j)) → ∀ k : Fin s,
    ‖fxC p (Φ w k) - (resB s t α).mulVec (fun j => fxC p (w j)) k‖ * (2 : ℝ) ^ p < (p : ℝ) ^ 2)

end Work.Resample
