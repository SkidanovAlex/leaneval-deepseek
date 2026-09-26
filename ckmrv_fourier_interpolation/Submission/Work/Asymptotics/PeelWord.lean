/-
# The peeling word of an element of `SL(2,ℤ)`

`Work.Asymptotics.frobSq_peel` provides, for every `γ` with `frobSq γ > 2`, one of the four
elementary moves `T`, `T⁻¹`, `S*T`, `S*T⁻¹` that decreases the squared Frobenius norm by at least
one.  Iterating this at most `frobSq γ` times gives a word `L` in the four letters and a "reduced"
element `δ ∈ {±1,±S}` with `γ * L.prod = δ`.  The number of letters is at most `frobSq γ`.

We record the elementary properties: the product identity, the membership of the letters, the
length bound, and the fact that all the intermediate elements (the partial products) have
polynomially bounded Frobenius norm.
-/
import Mathlib
import Submission.Work.Asymptotics.CarryDefs
import Submission.Work.Asymptotics.FrobPeel

set_option maxHeartbeats 800000

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

/-- The reduction letter chosen by `frobSq_peel` (arbitrary when `frobSq γ ≤ 2`). -/
noncomputable def peelLetter (γ : SL(2,ℤ)) : SL(2,ℤ) :=
  if h : 2 < frobSq γ then Classical.choose ((frobSq_peel γ).1 h) else 1

lemma peelLetter_spec (γ : SL(2,ℤ)) (h : 2 < frobSq γ) :
    (peelLetter γ = ModularGroup.T ∨ peelLetter γ = ModularGroup.T⁻¹
      ∨ peelLetter γ = ModularGroup.S * ModularGroup.T
      ∨ peelLetter γ = ModularGroup.S * ModularGroup.T⁻¹)
    ∧ frobSq (γ * peelLetter γ) + 1 ≤ frobSq γ := by
  have h' := Classical.choose_spec ((frobSq_peel γ).1 h)
  rw [peelLetter, dif_pos h]
  exact h'

lemma peelLetter_decrease (γ : SL(2,ℤ)) (h : 2 < frobSq γ) :
    frobSq (γ * peelLetter γ) < frobSq γ := by
  have := (peelLetter_spec γ h).2
  omega

/-- `n` steps of the peeling of `γ`: the current element together with the list of letters
applied so far. -/
noncomputable def peelIter : ℕ → SL(2,ℤ) → SL(2,ℤ) × List SL(2,ℤ)
  | 0, γ => (γ, [])
  | n + 1, γ =>
      if 2 < frobSq γ then
        let r := peelIter n (γ * peelLetter γ)
        (r.1, peelLetter γ :: r.2)
      else (γ, [])

lemma peelIter_zero (γ : SL(2,ℤ)) : peelIter 0 γ = (γ, []) := rfl

lemma peelIter_succ_pos (n : ℕ) (γ : SL(2,ℤ)) (h : 2 < frobSq γ) :
    peelIter (n + 1) γ = ((peelIter n (γ * peelLetter γ)).1,
      peelLetter γ :: (peelIter n (γ * peelLetter γ)).2) := by
  rw [peelIter]; simp only [if_pos h]

lemma peelIter_succ_neg (n : ℕ) (γ : SL(2,ℤ)) (h : ¬ 2 < frobSq γ) :
    peelIter (n + 1) γ = (γ, []) := by
  rw [peelIter]; simp only [if_neg h]

/-- The peeling of `γ` with the maximum number of steps `frobSq γ`. -/
noncomputable def peelAux (γ : SL(2,ℤ)) : SL(2,ℤ) × List SL(2,ℤ) := peelIter (frobSq γ) γ

/-- The reduced element of the peeling. -/
noncomputable def peelBase (γ : SL(2,ℤ)) : SL(2,ℤ) := (peelAux γ).1

/-- The list of letters applied in the peeling. -/
noncomputable def peelList (γ : SL(2,ℤ)) : List SL(2,ℤ) := (peelAux γ).2

theorem peelIter_prod : ∀ (n : ℕ) (γ : SL(2,ℤ)),
    γ * (peelIter n γ).2.prod = (peelIter n γ).1 := by
  intro n
  induction n with
  | zero => intro γ; simp [peelIter_zero]
  | succ n ih =>
    intro γ
    by_cases h : 2 < frobSq γ
    · rw [peelIter_succ_pos n γ h, List.prod_cons, ← mul_assoc, ih]
    · rw [peelIter_succ_neg n γ h, List.prod_nil, mul_one]

theorem peelIter_invariant : ∀ (n : ℕ) (γ : SL(2,ℤ)),
    (peelIter n γ).2.length + frobSq ((peelIter n γ).1) ≤ frobSq γ := by
  intro n
  induction n with
  | zero => intro γ; simp [peelIter_zero]
  | succ n ih =>
    intro γ
    by_cases h : 2 < frobSq γ
    · rw [peelIter_succ_pos n γ h, List.length_cons]
      have hdec := peelLetter_decrease γ h
      have hid := ih (γ * peelLetter γ)
      show (peelIter n (γ * peelLetter γ)).2.length + 1
        + frobSq ((peelIter n (γ * peelLetter γ)).1) ≤ frobSq γ
      omega
    · rw [peelIter_succ_neg n γ h, List.length_nil, Nat.zero_add]

theorem peelIter_terminated : ∀ (n : ℕ) {γ : SL(2,ℤ)}, ¬ (2 < frobSq γ) → peelIter n γ = (γ, []) := by
  intro n
  induction n with
  | zero => intro γ _; exact peelIter_zero γ
  | succ n ih =>
    intro γ h
    cases n with
    | zero => exact peelIter_succ_neg 0 γ h
    | succ m => exact peelIter_succ_neg (m + 1) γ h

theorem peelIter_len_of_not_term : ∀ (n : ℕ) (γ : SL(2,ℤ)),
    2 < frobSq ((peelIter (n + 1) γ).1) → (peelIter (n + 1) γ).2.length = n + 1 := by
  intro n
  induction n with
  | zero =>
    intro γ h
    by_cases hγ : 2 < frobSq γ
    · rw [peelIter_succ_pos 0 γ hγ]; simp [peelIter_zero]
    · rw [peelIter_succ_neg 0 γ hγ] at h
      exact absurd h hγ
  | succ n ih =>
    intro γ h
    by_cases hγ : 2 < frobSq γ
    · rw [peelIter_succ_pos (n + 1) γ hγ] at h ⊢
      simp only [List.length_cons]
      have hid := ih (γ * peelLetter γ) h
      omega
    · rw [peelIter_succ_neg (n + 1) γ hγ] at h
      exact absurd h hγ

lemma peelAux_prod (γ : SL(2,ℤ)) : γ * (peelList γ).prod = peelBase γ :=
  peelIter_prod (frobSq γ) γ

lemma peelAux_terminal (γ : SL(2,ℤ)) : ¬ (2 < frobSq (peelBase γ)) := by
  intro h
  have hinv := peelIter_invariant (frobSq γ) γ
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp (frobSq_pos γ))
  have hh : 2 < frobSq ((peelIter (n + 1) γ).1) := by
    rw [peelBase, peelAux, hn] at h
    exact h
  have hlen : (peelIter (frobSq γ) γ).2.length = frobSq γ := by
    rw [hn]
    exact peelIter_len_of_not_term n γ hh
  rw [hn] at hlen hinv
  rw [peelBase, peelAux, hn] at h
  omega

lemma peelAux_len (γ : SL(2,ℤ)) : (peelList γ).length ≤ frobSq γ := by
  have hinv := peelIter_invariant (frobSq γ) γ
  show (peelIter (frobSq γ) γ).2.length ≤ frobSq γ
  exact le_trans (Nat.le_add_right _ _) hinv

lemma peelAux_base (γ : SL(2,ℤ)) :
    peelBase γ = 1 ∨ peelBase γ = -1 ∨ peelBase γ = ModularGroup.S
      ∨ peelBase γ = -ModularGroup.S :=
  (frobSq_peel (peelBase γ)).2 (not_lt.mp (peelAux_terminal γ))

lemma peelIter_mem : ∀ (n : ℕ) (γ : SL(2,ℤ)), ∀ ℓ ∈ (peelIter n γ).2,
    ℓ = ModularGroup.T ∨ ℓ = ModularGroup.T⁻¹ ∨ ℓ = ModularGroup.S * ModularGroup.T
      ∨ ℓ = ModularGroup.S * ModularGroup.T⁻¹ := by
  intro n
  induction n with
  | zero => intro γ ℓ hℓ; exact absurd hℓ (by simp [peelIter_zero])
  | succ n ih =>
    intro γ ℓ hℓ
    by_cases h : 2 < frobSq γ
    · rw [peelIter_succ_pos n γ h] at hℓ
      simp only [List.mem_cons] at hℓ
      rcases hℓ with rfl | hℓ
      · exact (peelLetter_spec γ h).1
      · exact ih (γ * peelLetter γ) ℓ hℓ
    · rw [peelIter_succ_neg n γ h] at hℓ
      exact absurd hℓ (by simp)

lemma peelAux_mem (γ : SL(2,ℤ)) : ∀ ℓ ∈ peelList γ,
    ℓ = ModularGroup.T ∨ ℓ = ModularGroup.T⁻¹ ∨ ℓ = ModularGroup.S * ModularGroup.T
      ∨ ℓ = ModularGroup.S * ModularGroup.T⁻¹ :=
  peelIter_mem (frobSq γ) γ

end Work.Asymptotics
