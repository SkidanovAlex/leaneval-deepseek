import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Resample.fx

/-!
# The one-dimensional slice specifications of paper Lemmas 4.8–4.12

`SliceSpecA`/`SliceSpecB` package the *uniform* one-dimensional resampling words: one preparation
word `prep` (turning `p, α, s, t` into the data bundle `P` of the dimension) and one slice word `q`
(transforming a slice of length `s` resp. `t`), together with the disc invariance and the
one-dimensional error bound `< p²`.  Uniformity in `(p, α, s, t)` is exactly what the `D`-fold
`applyAlong` chain of the tensoring needs (a single `Cmd` must serve every dimension).
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-- The uniform one-dimensional slice specification for `Ã₁ = S̃'` (paper Lemma 4.9). -/
def SliceSpecA (KL : KernelLib) (IL : IntLib) (LL : LayoutLib) (FL : FxLib) (RM : ResMath1DProp) :
    Prop :=
  ∃ (prep q : Cmd) (K : ℕ),
    ∀ (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hcop : Nat.Coprime s t) (htp : t < 2 ^ p)
      (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p)
      (hθ : (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1),
    ∃ (Φ : (Fin s → ℤ × ℤ) → (Fin t → ℤ × ℤ)) (P : List Val),
      (∀ (main : Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → MulBelow main N Cm → K * p < N →
        WordR main prep
          (fun vs => ∃ rest, vs = .int p :: .int α :: .int s :: .int t :: rest)
          (fun vs out => ∃ rest, vs = .int p :: .int α :: .int s :: .int t :: rest ∧
            out = P ++ rest)
          (fun _ => K * (t + 1) * (p + 1) ^ K)) ∧
      (∀ (main : Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → MulBelow main N Cm → K * p < N →
        WordR main q
          (fun vs => ∃ (u : List (ℤ × ℤ)) (rest : List Val),
            vs = ofList (u.map cfxVal) :: P ++ rest ∧
            u.length = s ∧ (∀ z ∈ u, inDisc p z))
          (fun vs out => ∃ (u : List (ℤ × ℤ)) (rest : List Val) (w : List (ℤ × ℤ)),
            vs = ofList (u.map cfxVal) :: P ++ rest ∧
            out = cvecVal w :: P ++ rest ∧ w.length = t ∧ (∀ z ∈ w, inDisc p z) ∧
            (∀ k : Fin t, w.getD k (0,0) = Φ (fun j => u.getD j (0,0)) k))
          (fun _ => K * (t + 1) * (Nat.sqrt p + 1) * (α + 1) * (Cm (K * p) + p + 1))) ∧
      (∀ w : Fin s → ℤ × ℤ, (∀ j, inDisc p (w j)) → ∀ k : Fin t, inDisc p (Φ w k)) ∧
      (∀ w : Fin s → ℤ × ℤ, (∀ j, inDisc p (w j)) → ∀ k : Fin t,
        ‖fxC p (Φ w k) - (resA s t α).mulVec (fun j => fxC p (w j)) k‖ * (2 : ℝ) ^ p
          < (p : ℝ) ^ 2)

/-- The uniform one-dimensional slice specification for `B̃ = P̃_s⁻¹ D̃' J̃' C̃ P̃_t` (Lemmas 4.8,
4.11, 4.12 and the data moves of the proof of Prop 4.7(ii)). -/
def SliceSpecB (KL : KernelLib) (IL : IntLib) (LL : LayoutLib) (FL : FxLib) (RM : ResMath1DProp) :
    Prop :=
  ∃ (prep q : Cmd) (K : ℕ),
    ∀ (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hcop : Nat.Coprime s t) (htp : t < 2 ^ p)
      (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p)
      (hθ : (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1),
    ∃ (Φ : (Fin t → ℤ × ℤ) → (Fin s → ℤ × ℤ)) (P : List Val),
      (∀ (main : Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → MulBelow main N Cm → K * p < N →
        WordR main prep
          (fun vs => ∃ rest, vs = .int p :: .int α :: .int s :: .int t :: rest)
          (fun vs out => ∃ rest, vs = .int p :: .int α :: .int s :: .int t :: rest ∧
            out = P ++ rest)
          (fun _ => K * (t + 1) * (p + 1) ^ K)) ∧
      (∀ (main : Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → MulBelow main N Cm → K * p < N →
        WordR main q
          (fun vs => ∃ (u : List (ℤ × ℤ)) (rest : List Val),
            vs = ofList (u.map cfxVal) :: P ++ rest ∧
            u.length = t ∧ (∀ z ∈ u, inDisc p z))
          (fun vs out => ∃ (u : List (ℤ × ℤ)) (rest : List Val) (w : List (ℤ × ℤ)),
            vs = ofList (u.map cfxVal) :: P ++ rest ∧
            out = cvecVal w :: P ++ rest ∧ w.length = s ∧ (∀ z ∈ w, inDisc p z) ∧
            (∀ k : Fin s, w.getD k (0,0) = Φ (fun j => u.getD j (0,0)) k))
          (fun _ => K * (t + 1) * (Nat.sqrt p + 1) * (α + 1) * (Cm (K * p) + p + 1) +
            K * (t + 1) * (p + 1) ^ 2)) ∧
      (∀ w : Fin t → ℤ × ℤ, (∀ j, inDisc p (w j)) → ∀ k : Fin s, inDisc p (Φ w k)) ∧
      (∀ w : Fin t → ℤ × ℤ, (∀ j, inDisc p (w j)) → ∀ k : Fin s,
        ‖fxC p (Φ w k) - (resB s t α).mulVec (fun j => fxC p (w j)) k‖ * (2 : ℝ) ^ p
          < (p : ℝ) ^ 2)

end Work.Resample
