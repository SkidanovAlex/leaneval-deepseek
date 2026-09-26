import Mathlib
import Submission.Work.PTCert.GlueDefs

namespace Work.PTCert.ldlChainSound

/-!
# Specification of one kernel LDL row step

`Submission.PTCert.ldlRowStep` performs one row of the scaled LDL reduction: given the
upper-triangle block entries `b d = B (i) (i+d)`, weights `w`, the factor row `ci = C i` and the
factor rows `cs d = C (i+d)`, it recomputes the remaining entries
`r d = rii * (w i) * (w (i+d)) * B (i) (i+d) - ⟨C i, C (i+d)⟩` (as `wi * ws d * b d - dotZ ci cs d`),
checks that the accumulated column sums plus `Σ_{d≥1} |r d|` are at most `r 0`, and on success
returns the accumulator advanced by the absolute values of `r d`, `d ≥ 1`.

The lemma below extracts the exact effect of this one step, under the concrete instantiation used by
the certificate chain (`b = f`, `w = g`, `C (i+d) = h d`): the new accumulator has length `m - 1`,
its entries are the old ones shifted by one plus the absolute value of `r d`, and diagonal dominance
at the current row holds. Everything is a computation on `List.range`-indexed lists.
-/

/-- The `foldr (+) 0` of a `range`-indexed list is the corresponding `Finset.sum`. -/
private lemma foldr_range_map (n : ℕ) : ∀ (φ : ℕ → ℤ),
    ((List.range n).map φ).foldr (· + ·) 0 = Finset.sum (Finset.range n) φ := by
  induction n with
  | zero => intro φ; simp
  | succ n ih =>
    intro φ
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.foldr_cons, ih (φ ∘ Nat.succ),
        Finset.sum_range_succ']
    simp only [Function.comp]
    rw [add_comm]

/-- Indexing a `range`-indexed list below its length. -/
private lemma getD_map_range {φ : ℕ → ℤ} {n c : ℕ} (hc : c < n) :
    ((List.range n).map φ).getD c 0 = φ c := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hc]
  rfl

/-- Dropping the first element shifts the index. -/
private lemma getD_drop_one (l : List ℤ) (c : ℕ) : (l.drop 1).getD c 0 = l.getD (c + 1) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_comm]

/-- `getD` commutes with pointwise addition when the index is in range. -/
private lemma getD_zipWith_add (a b : List ℤ) (c : ℕ) (ha : c < a.length) (hb : c < b.length) :
    (List.zipWith (· + ·) a b).getD c 0 = a.getD c 0 + b.getD c 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_zipWith, List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hb]
  simp

/-- `List.range m` with its first element dropped is `List.range (m-1)` shifted by one. -/
private lemma drop_one_range (m : ℕ) : (List.range m).drop 1 = (List.range (m - 1)).map (· + 1) := by
  cases m with
  | zero => rfl
  | succ k => rw [List.range_succ_eq_map]; simp

/-- The head of a nonempty `range`-indexed list is the value at `0`. -/
private lemma headD_range_map {φ : ℕ → ℤ} {n : ℕ} (hn : 1 ≤ n) :
    ((List.range n).map φ).headD 0 = φ 0 := by
  cases n with
  | zero => omega
  | succ k => rw [List.range_succ_eq_map, List.map_cons, List.headD_cons]

/-- Zipping two `map`s of the same list pairs the values pointwise. -/
private lemma zip_map_map_self {α : Type*} (u v : α → ℤ) (l : List α) :
    List.zip (l.map u) (l.map v) = l.map (fun a => (u a, v a)) := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

/-- `zipWith` of two `map`s of the same list acts pointwise. -/
private lemma zipWith_map_self {α : Type*} (F : ℤ × ℤ → List ℤ → ℤ) (K : α → ℤ × ℤ)
    (hh : α → List ℤ) (l : List α) :
    List.zipWith F (l.map K) (l.map hh) = l.map (fun a => F (K a) (hh a)) := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

/-- The three-fold `zip`/`zipWith` fold collapses to a pointwise `map`. -/
private lemma zipWith_zip_map_self {α : Type*} (F : ℤ × ℤ → List ℤ → ℤ) (u v : α → ℤ)
    (hh : α → List ℤ) (l : List α) :
    List.zipWith F (List.zip (l.map u) (l.map v)) (l.map hh) = l.map (fun a => F (u a, v a) (hh a)) := by
  rw [zip_map_map_self u v l, zipWith_map_self F (fun a => (u a, v a)) hh l]

/-- **Effect of one `ldlRowStep`.**  If the step accepts, then the residual list has one entry fewer
than the row length, its entries are the old accumulator (shifted by one) plus the absolute values of
the residuals of the shifted columns, and diagonal dominance holds at the current row. -/
theorem ldlRowStep_abstract
    {m : ℕ} (hm : 1 ≤ m) (Z off : List ℤ) (ψ : ℕ → ℤ) (acc acc' : List ℤ)
    (hlen : m ≤ acc.length)
    (hZ : Z = (List.range m).map ψ)
    (hoff : off = (Z.drop 1).map (fun x => |x|))
    (hstep : acc.headD 0 + off.foldr (· + ·) 0 ≤ Z.headD 0 ∧
      acc' = List.zipWith (· + ·) (acc.drop 1) off) :
    acc'.length = m - 1 ∧
    (∀ c < m - 1, acc'.getD c 0 = acc.getD (c + 1) 0 + |ψ (c + 1)|) ∧
    (acc.headD 0 + Finset.sum (Finset.range (m - 1)) (fun d => |ψ (d + 1)|) ≤ ψ 0) := by
  obtain ⟨hcond, hacc'⟩ := hstep
  have hoff_eq : off = (List.range (m - 1)).map (fun d => |ψ (d + 1)|) := by
    rw [hoff, hZ, ← List.map_drop, List.map_map, drop_one_range, List.map_map]
    rfl
  have hoff_len : off.length = m - 1 := by rw [hoff_eq, List.length_map, List.length_range]
  have hhead : Z.headD 0 = ψ 0 := by rw [hZ]; exact headD_range_map hm
  have hfold : off.foldr (· + ·) 0 = Finset.sum (Finset.range (m - 1)) (fun d => |ψ (d + 1)|) := by
    rw [hoff_eq]; exact foldr_range_map (m - 1) (fun d => |ψ (d + 1)|)
  refine ⟨?_, ?_, ?_⟩
  · rw [hacc', List.length_zipWith, List.length_drop, hoff_len]
    exact Nat.min_eq_right (Nat.sub_le_sub_right hlen 1)
  · intro c hc
    rw [hacc', getD_zipWith_add _ _ _ (by rw [List.length_drop]; omega) (by rw [hoff_len]; exact hc),
        getD_drop_one, hoff_eq, getD_map_range hc]
  · rw [hfold, hhead] at hcond
    exact hcond

theorem ldlRowStep_spec {m : ℕ} (hm : 1 ≤ m) (f g : ℕ → ℤ) (h : ℕ → List ℤ) (wi : ℤ) (ci acc acc' : List ℤ)
    (hlen : m ≤ acc.length)
    (hstep : Submission.PTCert.ldlRowStep ((List.range m).map f) wi ((List.range m).map g) ci
      ((List.range m).map h) acc = some acc') :
    acc'.length = m - 1 ∧
    (∀ c < m - 1, acc'.getD c 0 = acc.getD (c + 1) 0 + |wi * g (c + 1) * f (c + 1) - Submission.PTCert.dotZ ci (h (c + 1))|) ∧
    (acc.headD 0 + Finset.sum (Finset.range (m - 1)) (fun d => |wi * g (d + 1) * f (d + 1) - Submission.PTCert.dotZ ci (h (d + 1))|)
      ≤ wi * g 0 * f 0 - Submission.PTCert.dotZ ci (h 0)) := by
  let ψ : ℕ → ℤ := fun d => wi * g d * f d - Submission.PTCert.dotZ ci (h d)
  let ZIP : List ℤ :=
    List.zipWith (fun (bw : ℤ × ℤ) (cj : List ℤ) => wi * bw.2 * bw.1 - Submission.PTCert.dotZ ci cj)
      (List.zip ((List.range m).map f) ((List.range m).map g)) ((List.range m).map h)
  let OFF : List ℤ := (ZIP.drop 1).map (fun x => |x|)
  have hstep' := hstep
  unfold Submission.PTCert.ldlRowStep at hstep'
  rw [Bool.cond_decide, ite_eq_iff] at hstep'
  rcases hstep' with ⟨hcond, heq⟩ | ⟨hbad, hcontra⟩
  · have hZ : ZIP = (List.range m).map ψ := by
      simp only [ZIP, ψ]
      exact zipWith_zip_map_self _ f g h (List.range m)
    exact ldlRowStep_abstract hm ZIP OFF ψ acc acc' hlen hZ rfl
      ⟨hcond, Option.some.inj heq.symm⟩
  · exact absurd hcontra (by simp)

end Work.PTCert.ldlChainSound
