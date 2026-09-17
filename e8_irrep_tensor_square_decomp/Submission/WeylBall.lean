import Submission.E8Character
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_posRoots_finset

/-!
# The Weyl group of `E₈`: words, length, sign, and the ball of radius `K`

This file sets up the *combinatorial* side of any sum over the Weyl group `W(E₈)` that arises from
the Weyl character formula.  Everything is phrased in terms of *words* in the simple reflections, so
that it is kernel-checkable.

* `rhoZ` — the Weyl vector `ρ = ω₁ + ⋯ + ω₈` in the fundamental-weight basis; `htOf rhoZ = 620`
  (`620` is the sum of all entries of the inverse Cartan matrix).
* `wact L v` — the action of the word `L` on the weight lattice (`L.foldl sref v`).
* `htDefect x = 620 - htOf x` for `x = wρ` — this is **NOT** the length `ℓ(w)`, it is the
  **sum of the heights of the positive roots sent negative** by `w`:
  `620 - htOf(wρ) = htOf(ρ - wρ) = Σ_{α ∈ N(w)} htOf(α)`, with `N(w) = {α > 0 : wα < 0}`.
  Consequently `htDefect (wρ) ≥ ℓ(w) = #N(w)`, with equality iff all flipped roots are simple.
  **Caution (machine-checked counterexample, found by a fleet agent):** the claimed identity
  `ℓ(w) = 620 - htOf(wρ)` is *FALSE*; e.g. `L₀ = [3,4,4,7,6,0,7,3,6]` has
  `wact L₀ rhoZ = ![-1,1,2,1,1,2,1,-2]`, `htDefect = 4`, while `wact L₀ = wact [0,6,7]` has `ℓ = 3`.
* `wsign (L : List (Fin 8)) = (-1) ^ L.length` — the sign of the *word* `L`.  This **is** the sign
  `ε(w)` of the element `w = wact L`: each `sref i` is a reflection, hence has determinant `-1` on
  `ℤ⁸`, so `det (wact L) = (-1)^{L.length}`, so the parity of a word is well defined on the element
  and equals `ℓ(w) mod 2` (`det (w) = (-1)^{ℓ(w)}`).
* `wordsUpTo K` — all words of length `≤ K`; `ballSet K` — the *distinct* elements `wρ` realized by
  them (i.e. the elements of length `≤ K`, since `w ↦ wρ` is injective); `ballSum K f` — the
  alternating sum `Σ_{ℓ(w) ≤ K} ε(w) f(wρ)` over the ball.

The use for this project: the multiplicities of the tensor square are

  `c_ν = Σ_{w ∈ W} ε(w) · mfun (ν + ρ - w(λ+ρ))`

(a corollary of the Weyl character formula for `V = L(ω₁+ω₈)` and for the constituents of `T`),
and the summand vanishes unless `ν + ρ - w(λ+ρ)` is a weight of `V`, i.e. one of the `56881`
lattice points of norm `≤ 10` (`mfun_eq_mnorm`).  Numerically (SESSION 22) all contributing `w`
have `ℓ(w) ≤ 4`, so the sum over the elements of length `≤ 4` (≈ 467 elements, 1162 contributing
terms) is the object to evaluate — **once** the vanishing of the remaining terms is known.
The sign of an element is the parity of *any* word representing it (`wsign`).
-/

namespace Submission.WeylBall

open Submission.E8Character
open Submission.WeylWeights

/-- The Weyl vector `ρ = ω₁ + ⋯ + ω₈` in the fundamental-weight basis. -/
def rhoZ : Fin 8 → ℤ := fun _ => 1

/-- The height of `ρ` is `620`, the sum of all entries of the inverse Cartan matrix. -/
lemma htOf_rhoZ : htOf rhoZ = 620 := by decide

/-- The action of a *word* `L` in the simple reflections on the weight lattice. -/
def wact (L : List (Fin 8)) (v : Fin 8 → ℤ) : Fin 8 → ℤ := L.foldl (fun w i => sref i w) v

@[simp] lemma wact_nil (v : Fin 8 → ℤ) : wact [] v = v := rfl

lemma wact_cons (i : Fin 8) (L : List (Fin 8)) (v : Fin 8 → ℤ) :
    wact (i :: L) v = wact L (sref i v) := rfl

lemma wact_append (L₁ L₂ : List (Fin 8)) (v : Fin 8 → ℤ) :
    wact (L₁ ++ L₂) v = wact L₂ (wact L₁ v) := by
  induction L₁ generalizing v with
  | nil => rfl
  | cons i L ih => exact ih (sref i v)

open Classical in
/-- The finite set of the **120 positive roots** of `E₈`, extracted from the commons lemma
`E8_posRoots_finset` (the nonzero vectors of norm `2` in the positive cone). -/
noncomputable def posRoots : Finset (Fin 8 → ℤ) :=
  Classical.choose Commons.LinearAlgebra.Matrix.Cartan.E8_posRoots_finset

lemma mem_posRoots {v : Fin 8 → ℤ} :
    v ∈ posRoots ↔ v ≠ 0 ∧ Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.qZ v = 2 ∧
      ∀ i, 0 ≤ Commons.LinearAlgebra.Matrix.Cartan.coords v i :=
  (Classical.choose_spec Commons.LinearAlgebra.Matrix.Cartan.E8_posRoots_finset).1 v

lemma posRoots_card : posRoots.card = 120 :=
  (Classical.choose_spec Commons.LinearAlgebra.Matrix.Cartan.E8_posRoots_finset).2

open Classical in
/-- The **length** of the Weyl group element given by a word `L`: the number of positive roots that
`w = wact L` sends to negative roots.  This is `ℓ(w) = #N(w)`. -/
noncomputable def wlenOf (L : List (Fin 8)) : ℕ :=
  (posRoots.filter (fun α => posCon (-(wact L α)))).card

/-- The sign `ε(w) = (-1)^{ℓ(w)}` of the element given by the word `L`.
(Key fact to be proved: `wsignOf L = (-1 : ℤ) ^ L.length`, i.e. the parity of `ℓ(w)` is the parity
of any word representing `w`; equivalently `det (wact L) = (-1)^{L.length}`.) -/
noncomputable def wsignOf (L : List (Fin 8)) : ℤ := (-1) ^ wlenOf L

/-- `620 - ht(wρ)` for the element `w` with `wρ = x`.  This is the **sum of the heights of the
positive roots sent negative** by `w`, hence `≥ ℓ(w)`, but it is *not* `ℓ(w)` (see the file
docstring). -/
def htDefect (x : Fin 8 → ℤ) : ℤ := 620 - htOf x

/-- The sign of a *word* `L` in the simple reflections; this is the sign `ε(w)` of the element
`w = wact L`. -/
def wsign (L : List (Fin 8)) : ℤ := (-1) ^ L.length

lemma htDefect_rhoZ : htDefect rhoZ = 0 := by rw [htDefect, htOf_rhoZ]; norm_num

lemma wsign_nil : wsign ([] : List (Fin 8)) = 1 := rfl

/-- All words in the simple reflections of length `≤ K`. -/
def wordsUpTo : ℕ → List (List (Fin 8))
  | 0 => [[]]
  | n + 1 =>
      let W := wordsUpTo n
      W ++ W.flatMap (fun L => (List.finRange 8).map (fun i => L ++ [i]))

@[simp] lemma mem_wordsUpTo_zero : ([] : List (Fin 8)) ∈ wordsUpTo 0 := by simp [wordsUpTo]

lemma mem_wordsUpTo_succ {n : ℕ} {L : List (Fin 8)} (h : L ∈ wordsUpTo n) :
    L ∈ wordsUpTo (n + 1) := by
  simp only [wordsUpTo, List.mem_append]
  exact Or.inl h

/-- The elements of `W(E₈)` of length `≤ K`, represented by the vector `wρ`
(`w ↦ wρ` is injective because `ρ` is regular). -/
def ballList (K : ℕ) : List (Fin 8 → ℤ) := (wordsUpTo K).map (fun L => wact L rhoZ)

lemma mem_ballList {K : ℕ} {L : List (Fin 8)} (h : L ∈ wordsUpTo K) :
    wact L rhoZ ∈ ballList K :=
  List.mem_map.2 ⟨L, h, rfl⟩

/-- The *distinct* elements of the ball of radius `K` (as vectors `wρ`). -/
def ballSet (K : ℕ) : List (Fin 8 → ℤ) := (ballList K).dedup

/-- The elements of the ball of radius `K`, as pairs `(wρ, ε(w))`: one pair per *distinct* vector
`wρ` realized by a word of length `≤ K`, the sign being the parity of the first such word.  (That
this sign is independent of the chosen word is the statement that `det (wact L) = (-1)^{L.length}`;
see the file docstring.) -/
def ballPairs (K : ℕ) : List ((Fin 8 → ℤ) × ℤ) :=
  (wordsUpTo K).foldl (fun acc L =>
    let x := wact L rhoZ
    if acc.any (fun p => decide (p.1 = x)) then acc else acc ++ [(x, wsign L)]) []

/-- The alternating sum over the elements of the ball of radius `K`,
`Σ_{w : ℓ(w) ≤ K} ε(w) f(wρ)` (as represented by `ballPairs`, i.e. by words of length `≤ K`). -/
def ballSum (K : ℕ) (f : (Fin 8 → ℤ) → ℤ) : ℤ :=
  ((ballPairs K).map (fun p => p.2 * f p.1)).sum

end Submission.WeylBall
