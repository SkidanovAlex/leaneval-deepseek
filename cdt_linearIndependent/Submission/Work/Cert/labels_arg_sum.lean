import Mathlib
import Submission.Work.Cert.WindDefs

/-!
# The total argument turn of a cyclic quarter-turn label sequence

`labelsOK labs` holds exactly when the cyclic list `labs` of quadrant labels `∈ {0,1,2,3}`
makes one full positive turn: the sum of the signed quarter-turns `turn` along the cyclic
sequence `labs` (including the wrap-around edge) is `4`.

Here we prove that this is reflected in the principal arguments of the ratios
`I ^ labs[i+1] / I ^ labs[i]`: the cyclic sum of those arguments is exactly `2π`.

The main output is `Work.Cert.labels_arg_sum`.
-/

namespace Work.Cert

/-- The principal argument of `I ^ b / I ^ a`, the contribution of the step `a → b` of the
label sequence to the total winding argument. -/
noncomputable def argStep (a b : ℕ) : ℝ := Complex.arg (Complex.I ^ b / Complex.I ^ a)

/-- For labels `a b < 4` the principal argument `argStep a b` is the signed quarter-turn
`turn a b` (when this is defined, i.e. the labels are not opposite) times `π / 2`. -/
lemma argStep_eq_turn (a b : ℕ) (ha : a < 4) (hb : b < 4) (s : ℤ) (h : turn a b = some s) :
    argStep a b = (s : ℝ) * (Real.pi / 2) := by
  interval_cases a <;> interval_cases b <;>
    simp_all [turn, argStep, Complex.arg_I, Complex.arg_neg_I, Complex.arg_one, div_neg,
      div_one] <;>
    (rw [← h]; push_cast; ring_nf)

/-- The cyclic sum of `argStep` along the list `l`, closed up by returning to the label `w`:
`argStep l₀ l₁ + argStep l₁ l₂ + ⋯ + argStep l_{n-1} w`. -/
noncomputable def cycArg (w : ℕ) : List ℕ → ℝ
  | [] => 0
  | [a] => argStep a w
  | a :: b :: rest => argStep a b + cycArg w (b :: rest)

/-- If the cyclic sequence `l`, closed up at `w`, consists of labels `< 4` that avoid opposite
pairs and whose signed quarter-turns sum to `s`, then the cyclic `argStep` sum equals
`s * (π / 2)`. -/
lemma cycArg_eq_turns (w : ℕ) (hw : w < 4) :
    ∀ (l : List ℕ), (∀ x ∈ l, x < 4) → ∀ s, turnsFrom w l = some s →
      cycArg w l = (s : ℝ) * (Real.pi / 2) := by
  intro l
  induction l with
  | nil => intro hl s h; simp [turnsFrom, cycArg] at h ⊢; omega
  | cons a t ih =>
    cases t with
    | nil =>
      intro hl s h
      have ha : a < 4 := hl a (by simp)
      have := argStep_eq_turn a w ha hw s (by simpa [turnsFrom] using h)
      simp only [cycArg]
      rw [this]
    | cons b rest =>
      intro hl s h
      have ha : a < 4 := hl a (by simp)
      have hb : b < 4 := hl b (by simp)
      have htail : ∀ x ∈ b :: rest, x < 4 := fun x hx => hl x (by simp [hx])
      cases hta : turn a b with
      | none => simp [turnsFrom, hta] at h
      | some x =>
        cases htb : turnsFrom w (b :: rest) with
        | none => simp [turnsFrom, hta, htb] at h
        | some y =>
          have hxy : x + y = s := by simpa [turnsFrom, hta, htb] using h
          have h1 := argStep_eq_turn a b ha hb x hta
          have h2 := ih htail y htb
          simp only [cycArg]
          rw [h1, h2, ← hxy]; push_cast; ring

/-- The cyclic `argStep` sum written with `List.zipWith` against the rotated list:
`(l.zipWith argStep (l.tail ++ [w])).sum = cycArg w l`. -/
lemma zipWith_tail_sum_eq_cycArg (w : ℕ) : ∀ (l : List ℕ),
    (l.zipWith argStep (l.tail ++ [w])).sum = cycArg w l
  | [] => by simp [cycArg]
  | [a] => by simp [cycArg]
  | a :: b :: rest => by
      have ih := zipWith_tail_sum_eq_cycArg w (b :: rest)
      rw [List.tail_cons, List.cons_append, List.zipWith_cons_cons, List.sum_cons, cycArg]
      rw [show rest ++ [w] = (b :: rest).tail ++ [w] by rfl, ih]

/-- `List.get` does not depend on the proof argument of the index. -/
lemma List.get_proof_irrel {α : Type*} (l : List α) {k : ℕ} (h1 h2 : k < l.length) :
    l.get ⟨k, h1⟩ = l.get ⟨k, h2⟩ := by
  congr 1

/-- The sum over `Fin l.length` of `G` applied to cyclic consecutive pairs equals the list sum
of `G` over `l` zipped with its rotation by one. -/
lemma sum_fin_cyclic (l : List ℕ) (G : ℕ → ℕ → ℝ) (hpos : 0 < l.length) :
    (∑ i : Fin l.length, G (l.get ⟨(i : ℕ), i.isLt⟩)
        (l.get ⟨((i : ℕ) + 1) % l.length, Nat.mod_lt _ hpos⟩))
      = (l.zipWith G (l.rotate 1)).sum := by
  rw [← List.sum_ofFn]
  congr 1
  apply List.ext_getElem
  · simp [List.length_ofFn, List.length_zipWith, List.length_rotate]
  · intro i h1 h2
    simp only [List.getElem_ofFn, List.getElem_zipWith, List.getElem_rotate, List.get_eq_getElem]

theorem labels_arg_sum {n : ℕ} (hn : 0 < n) (labs : List ℕ) (hlen : labs.length = n)
    (hlt : ∀ l ∈ labs, l < 4) (hOK : labelsOK labs = true) :
    (∑ i : Fin n, (Complex.arg (Complex.I ^ labs.get ⟨((i : ℕ) + 1) % n, by rw [hlen]; exact Nat.mod_lt _ hn⟩
        / Complex.I ^ labs.get ⟨i, by rw [hlen]; exact i.isLt⟩) : ℂ)) = 2 * (Real.pi : ℂ) := by
  cases labs with
  | nil => simp [labelsOK] at hOK
  | cons a t =>
    subst n
    rw [← Complex.ofReal_sum]
    rw [show (2 : ℂ) * ↑Real.pi = ↑(2 * Real.pi) by push_cast; ring]
    rw [Complex.ofReal_inj]
    have hturn : turnsFrom a (a :: t) = some 4 := by simpa [labelsOK] using hOK
    have ha : a < 4 := hlt a (by simp)
    have hpos : 0 < (a :: t).length := hn
    trans (∑ i : Fin (a :: t).length, argStep ((a :: t).get ⟨(i : ℕ), i.isLt⟩)
        ((a :: t).get ⟨((i : ℕ) + 1) % (a :: t).length, Nat.mod_lt _ hpos⟩))
    · apply Finset.sum_congr rfl
      intro i _
      apply congrArg₂ argStep
      · exact List.get_proof_irrel _ _ _
      · exact List.get_proof_irrel _ _ _
    · rw [sum_fin_cyclic (a :: t) argStep hpos]
      rw [show (a :: t).rotate 1 = t ++ [a] by
        rw [show (1 : ℕ) = 0 + 1 from rfl, List.rotate_cons_succ, List.rotate_zero]]
      rw [show t ++ [a] = (a :: t).tail ++ [a] from rfl,
          zipWith_tail_sum_eq_cycArg a (a :: t)]
      rw [cycArg_eq_turns a ha (a :: t) hlt 4 hturn]
      ring

end Work.Cert
