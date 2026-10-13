/-
  `Work.WilLibTS` — additions to the `SemialgebraicOn` API of
  `Submission.Work.WilLibTS.TS.Pair` (a mechanical port of `OAI.Analysis.SymmetricDomains.Pair`).

  The ported file `Pair.lean` already provides, for a *finite* index type `κ`,

  * `SemialgebraicOn.domain`, `.restrict`, `.mono`, `.congr`,
  * `.polynomial`, `.identity`, `.constant`,
  * `.preimage`, `.image`, `.comp`, `.pair`.

  What is *not* there — and is needed the moment one does algebra with semialgebraic functions
  (as in the CAD/elimination machinery) — is closure under the arithmetic operations on the
  target space `κ → ℝ`: pointwise addition, negation, subtraction, multiplication, scalar
  multiplication and powers.  This file supplies them.

  All of them are instances of one pattern: the graph of `x ↦ x (f x) (g x)` is the image of the
  graph of the pair `x ↦ (f x, g x)` under a *polynomial* map `(κ ⊕ κ) → ℝ → (κ → ℝ)`, which is
  semialgebraic by `SemialgebraicOn.polynomial`; then `SemialgebraicOn.comp` applies, and the
  result is identified with the pointwise operation by `SemialgebraicOn.congr`.

  Note the `[Finite κ]` hypotheses: they are the same hypotheses as on the ported
  `SemialgebraicOn.polynomial`, and they are unavoidable — the definition is phrased in terms of
  finitely many polynomials in the coordinates of the value.
-/
import Mathlib
import Submission.Work.WilLibTS.TS.Pair

namespace Work.WilLibTS.TS

noncomputable section

namespace SemialgebraicOn

variable {ι κ δ : Type*} {B : Set (ι → ℝ)}
variable {f : (ι → ℝ) → (κ → ℝ)} {g : (ι → ℝ) → (κ → ℝ)}

/-- Pointwise addition of two semialgebraic functions (finite target index type). -/
lemma add [Finite κ] (hf : SemialgebraicOn B f) (hg : SemialgebraicOn B g) :
    SemialgebraicOn B (fun x => f x + g x) := by
  have hadd : SemialgebraicOn (Set.univ : Set (κ ⊕ κ → ℝ))
      (fun v : κ ⊕ κ → ℝ => fun i => v (Sum.inl i) + v (Sum.inr i)) := by
    refine (polynomial (PolynomialSignSet.univ (c := id))
      (fun i : κ => MvPolynomial.X (Sum.inl i) + MvPolynomial.X (Sum.inr i))).congr ?_
    intro v _
    funext i
    simp
  refine (hadd.comp (hf.pair hg) (fun x _ => trivial)).congr ?_
  intro x _
  funext i
  rfl

/-- Pointwise negation of a semialgebraic function. -/
lemma neg [Finite κ] (hf : SemialgebraicOn B f) :
    SemialgebraicOn B (fun x => -f x) := by
  have hneg : SemialgebraicOn (Set.univ : Set (κ → ℝ))
      (fun v : κ → ℝ => fun i => -v i) := by
    refine (polynomial (PolynomialSignSet.univ (c := id))
      (fun i : κ => -MvPolynomial.X i)).congr ?_
    intro v _
    funext i
    simp
  refine (hneg.comp hf (fun x _ => trivial)).congr ?_
  intro x _
  funext i
  rfl

/-- Pointwise subtraction of two semialgebraic functions. -/
lemma sub [Finite κ] (hf : SemialgebraicOn B f) (hg : SemialgebraicOn B g) :
    SemialgebraicOn B (fun x => f x - g x) := by
  simpa only [Pi.sub_apply, sub_eq_add_neg] using hf.add hg.neg

/-- Pointwise multiplication of two semialgebraic functions (finite target index type). -/
lemma mul [Finite κ] (hf : SemialgebraicOn B f) (hg : SemialgebraicOn B g) :
    SemialgebraicOn B (fun x => f x * g x) := by
  have hmul : SemialgebraicOn (Set.univ : Set (κ ⊕ κ → ℝ))
      (fun v : κ ⊕ κ → ℝ => fun i => v (Sum.inl i) * v (Sum.inr i)) := by
    refine (polynomial (PolynomialSignSet.univ (c := id))
      (fun i : κ => MvPolynomial.X (Sum.inl i) * MvPolynomial.X (Sum.inr i))).congr ?_
    intro v _
    funext i
    simp
  refine (hmul.comp (hf.pair hg) (fun x _ => trivial)).congr ?_
  intro x _
  funext i
  rfl

/-- Pointwise scalar multiplication of a semialgebraic function by a constant. -/
lemma smul [Finite κ] (c : ℝ) (hf : SemialgebraicOn B f) :
    SemialgebraicOn B (fun x => c • f x) := by
  have hsmul : SemialgebraicOn (Set.univ : Set (κ → ℝ))
      (fun v : κ → ℝ => fun i => c * v i) := by
    refine (polynomial (PolynomialSignSet.univ (c := id))
      (fun i : κ => MvPolynomial.C c * MvPolynomial.X i)).congr ?_
    intro v _
    funext i
    simp
  refine (hsmul.comp hf (fun x _ => trivial)).congr ?_
  intro x _
  funext i
  rfl

/-- Pointwise power of a semialgebraic function. -/
lemma pow [Finite κ] (hf : SemialgebraicOn B f) (n : ℕ) :
    SemialgebraicOn B (fun x => f x ^ n) := by
  have hpow : SemialgebraicOn (Set.univ : Set (κ → ℝ))
      (fun v : κ → ℝ => fun i => v i ^ n) := by
    refine (polynomial (PolynomialSignSet.univ (c := id))
      (fun i : κ => MvPolynomial.X i ^ n)).congr ?_
    intro v _
    funext i
    simp
  refine (hpow.comp hf (fun x _ => trivial)).congr ?_
  intro x _
  funext i
  rfl

/-- Composition with a map that is semialgebraic on the whole space. -/
lemma comp_univ [Finite κ] {h : (κ → ℝ) → (δ → ℝ)}
    (hh : SemialgebraicOn (Set.univ : Set (κ → ℝ)) h) (hf : SemialgebraicOn B f) :
    SemialgebraicOn B (h ∘ f) :=
  hh.comp hf (fun _ _ => trivial)

/-- Composition with a polynomial map: if `p i` is a polynomial for each target coordinate `i`,
then `x ↦ fun i => p i (f x)` is semialgebraic whenever `f` is. -/
lemma comp_polynomial [Finite κ] [Finite δ] {h : (κ → ℝ) → (δ → ℝ)}
    (hp : ∃ p : δ → MvPolynomial κ ℝ, ∀ v i, h v i = MvPolynomial.eval v (p i))
    (hf : SemialgebraicOn B f) : SemialgebraicOn B (h ∘ f) := by
  obtain ⟨p, hp⟩ := hp
  have hh : SemialgebraicOn (Set.univ : Set (κ → ℝ)) h := by
    refine (polynomial (PolynomialSignSet.univ (c := id)) p).congr ?_
    intro v _
    funext i
    exact (hp v i).symm
  exact hh.comp hf (fun _ _ => trivial)

end SemialgebraicOn

end

end Work.WilLibTS.TS
