import Mathlib
import Submission.Work.SignatureBordism.Intersection
import Submission.Work.SignatureBordism.Rationalisation
import Submission.Work.SignatureBordism.Hirzebruch

/-!
# The Pontryagin numbers of a closed oriented manifold, against a fundamental class

The dimension-`8` Hirzebruch identity `45 σ(M) = 7 p₂(M) - p₁(M)²` is an identity between three
integers attached to a closed oriented smooth `8`-manifold `M` together with its Pontryagin classes
`p₁ ∈ H⁴(M;ℤ)` and `p₂ ∈ H⁸(M;ℤ)`:

* the signature `σ(M)` (`Work.SignatureBordism.sigma`), the signature of the middle intersection
  form;
* the `p₁²`-number `⟨p₁ ⌣ p₁, [M]⟩` (`Work.SignatureBordism.p₁SqNumber`);
* the `p₂`-number `⟨p₂, [M]⟩` (`Work.SignatureBordism.p₂Number`).

None of the three is *defined* here as a Pontryagin class of the tangent bundle — that is the
characteristic-class chapter's business.  What this file provides is the pairing of *given*
cohomology classes against the fundamental class, so that the identity can be stated (as
`HirzebruchEightManifold`) as soon as those classes are produced, and so that the arithmetic of the
endgame can be fed with the right inputs.

## Main definitions

* `Work.SignatureBordism.p₁SqNumber X c p₁ = ⟨p₁ ⌣ p₁, c⟩`;
* `Work.SignatureBordism.p₂Number X c p₂ = ⟨p₂, c⟩`;
* `Work.SignatureBordism.p₁Number X c p₁ = ⟨p₁, c⟩` (dimension `4`);
* `Work.SignatureBordism.HirzebruchEightManifold X c p₁ p₂` — the dimension-`8` identity,
  `45 σ(X) = 7 p₂(X) - p₁(X)²`.

## Main results

* `Work.SignatureBordism.p₁SqNumber_eq_sq` — if `p₁ = q · x` and `⟨x ⌣ x, c⟩ = m` then
  `p₁²-number = q² m` (this is how the endgame's `p₁(X) = ±6 x` turns into `p₁(X)² = 36 m`);
* `Work.SignatureBordism.p₁SqNumber_neg_fundamental`,
  `Work.SignatureBordism.p₂Number_neg_fundamental`,
  `Work.SignatureBordism.p₁Number_neg_fundamental` — all three numbers *change sign* when the
  orientation (the fundamental class) is reversed, the first step towards bordism invariance;
* `Work.SignatureBordism.hirzebruchEightManifold_congruence` — the congruence form
  `p₁² ≡ 4 σ (mod 7)` of the identity, for a manifold with chosen classes.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.SignatureBordism

open Work.Cohomology

noncomputable section

variable (X : SSet)

/-- **The `p₁²`-number** of a closed oriented `8`-manifold with a chosen class `p₁ ∈ H⁴(X;ℤ)`:
`⟨p₁ ⌣ p₁, c⟩`, where `c ∈ H₈(X;ℤ)` is the fundamental class. -/
def p₁SqNumber (c : (chainC ℤ X).homology 8) (p₁ : (cochainC ℤ X).homology 4) : ℤ :=
  interForm ℤ X 4 4 c p₁ p₁

/-- **The `p₂`-number** of a closed oriented `8`-manifold with a chosen class `p₂ ∈ H⁸(X;ℤ)`:
`⟨p₂, c⟩` against the fundamental class `c ∈ H₈(X;ℤ)`. -/
def p₂Number (c : (chainC ℤ X).homology 8) (p₂ : (cochainC ℤ X).homology 8) : ℤ :=
  kronH ℤ X 8 p₂ c

/-- **The `p₁`-number** of a closed oriented `4`-manifold with a chosen class `p₁ ∈ H⁴(X;ℤ)`:
`⟨p₁, c⟩` against the fundamental class `c ∈ H₄(X;ℤ)`. -/
def p₁Number (c : (chainC ℤ X).homology 4) (p₁ : (cochainC ℤ X).homology 4) : ℤ :=
  kronH ℤ X 4 p₁ c

@[simp] theorem p₁SqNumber_apply (c : (chainC ℤ X).homology 8) (p₁ : (cochainC ℤ X).homology 4) :
    p₁SqNumber X c p₁ = interForm ℤ X 4 4 c p₁ p₁ := rfl

@[simp] theorem p₂Number_apply (c : (chainC ℤ X).homology 8) (p₂ : (cochainC ℤ X).homology 8) :
    p₂Number X c p₂ = kronH ℤ X 8 p₂ c := rfl

@[simp] theorem p₁Number_apply (c : (chainC ℤ X).homology 4) (p₁ : (cochainC ℤ X).homology 4) :
    p₁Number X c p₁ = kronH ℤ X 4 p₁ c := rfl

/-! ## The `p₁²`-number of a multiple of the middle generator -/

/-- **`p₁²` for `p₁ = q · x`**: if the Pontryagin class is a multiple of a middle class `x` whose
self-intersection is `m = ⟨x ⌣ x, c⟩`, then the `p₁²`-number is `q² m`.

This is the step which turns the characteristic-class input `p₁(X) = ±6 · x` of the endgame into
the numerical input `p₁(X)² = 36 m`. -/
theorem p₁SqNumber_eq_sq (c : (chainC ℤ X).homology 8) (x p₁ : (cochainC ℤ X).homology 4)
    {q m : ℤ} (hp : p₁ = q • x) (hm : interForm ℤ X 4 4 c x x = m) :
    p₁SqNumber X c p₁ = q ^ 2 * m := by
  subst hp
  have key : interForm ℤ X 4 4 c (q • x) (q • x) = q ^ 2 * interForm ℤ X 4 4 c x x := by
    have h1 : interForm ℤ X 4 4 c (q • x) = q • interForm ℤ X 4 4 c x :=
      map_zsmul (interForm ℤ X 4 4 c) q x
    have h2 : (interForm ℤ X 4 4 c x) (q • x) = q • (interForm ℤ X 4 4 c x x) :=
      map_zsmul (interForm ℤ X 4 4 c x) q x
    calc interForm ℤ X 4 4 c (q • x) (q • x)
        = (q • interForm ℤ X 4 4 c x) (q • x) := by rw [h1]
      _ = q • ((interForm ℤ X 4 4 c x) (q • x)) := rfl
      _ = q • (q • (interForm ℤ X 4 4 c x x)) := by rw [h2]
      _ = q ^ 2 * (interForm ℤ X 4 4 c x x) := by simp [sq]; ring
  rw [p₁SqNumber, key, hm]

/-- The `p₁²`-number of `q · x` when `⟨x ⌣ x, c⟩ = ±1` is `± q²`. -/
theorem p₁SqNumber_eq_sq_of_pm_one (c : (chainC ℤ X).homology 8) (x p₁ : (cochainC ℤ X).homology 4)
    {q : ℤ} (hp : p₁ = q • x) (hm : interForm ℤ X 4 4 c x x = 1 ∨ interForm ℤ X 4 4 c x x = -1) :
    p₁SqNumber X c p₁ = q ^ 2 ∨ p₁SqNumber X c p₁ = -(q ^ 2) := by
  rcases hm with hm | hm
  · left; simpa using p₁SqNumber_eq_sq X c x p₁ hp hm
  · right; simpa using p₁SqNumber_eq_sq X c x p₁ hp hm

/-! ## Orientation reversal -/

/-- **Reversing the orientation negates the `p₁²`-number.** -/
@[simp] theorem p₁SqNumber_neg_fundamental (c : (chainC ℤ X).homology 8)
    (p₁ : (cochainC ℤ X).homology 4) :
    p₁SqNumber X (-c) p₁ = -p₁SqNumber X c p₁ := by
  rw [p₁SqNumber, p₁SqNumber, interForm_neg_fundamental]

/-- **Reversing the orientation negates the `p₂`-number.** -/
@[simp] theorem p₂Number_neg_fundamental (c : (chainC ℤ X).homology 8)
    (p₂ : (cochainC ℤ X).homology 8) :
    p₂Number X (-c) p₂ = -p₂Number X c p₂ := by
  simp only [p₂Number]
  exact map_neg (kronH ℤ X 8 p₂) c

/-- **Reversing the orientation negates the `p₁`-number** (dimension `4`). -/
@[simp] theorem p₁Number_neg_fundamental (c : (chainC ℤ X).homology 4)
    (p₁ : (cochainC ℤ X).homology 4) :
    p₁Number X (-c) p₁ = -p₁Number X c p₁ := by
  simp only [p₁Number]
  exact map_neg (kronH ℤ X 4 p₁) c

/-! ## The Hirzebruch identity for a manifold with chosen Pontryagin classes -/

/-- **The dimension-`8` Hirzebruch identity for a closed oriented `8`-manifold** with chosen
classes `p₁ ∈ H⁴(X;ℤ)` (the first Pontryagin class of the tangent bundle) and `p₂ ∈ H⁸(X;ℤ)`:

  `45 σ(X) = 7 · ⟨p₂, [X]⟩ - ⟨p₁ ⌣ p₁, [X]⟩`.

This is the interface of `Submission/NOTES.md` §8.4's hard core; the content — that the classes
which *are* the Pontryagin classes of `TX` satisfy it — is the dimension-`8` signature theorem and
is not proved in this workspace (see `Submission/Work/SignatureBordism/Hirzebruch.lean` for what the
proof would need). -/
def HirzebruchEightManifold (c : (chainC ℤ X).homology 8) (p₁ : (cochainC ℤ X).homology 4)
    (p₂ : (cochainC ℤ X).homology 8) : Prop :=
  HirzebruchEight (sigma 4 X c) (p₁SqNumber X c p₁) (p₂Number X c p₂)

/-- **The dimension-`4` Hirzebruch identity for a closed oriented `4`-manifold** with a chosen
class `p₁ ∈ H⁴(X;ℤ)`: `⟨p₁, [X]⟩ = 3 σ(X)`.  This is the base case of the Hirzebruch theory; as
with `HirzebruchEightManifold`, the content (that `p₁` is the first Pontryagin class of `TX`) is
not formalised here. -/
def HirzebruchFourManifold (c : (chainC ℤ X).homology 4) (p₁ : (cochainC ℤ X).homology 4) : Prop :=
  HirzebruchFour (sigma 2 X c) (p₁Number X c p₁)

/-- **The congruence form of the dimension-`8` identity, for a manifold**: the identity implies
`⟨p₁ ⌣ p₁, [X]⟩ ≡ 4 σ(X) (mod 7)`. -/
theorem hirzebruchEightManifold_congruence (c : (chainC ℤ X).homology 8)
    (p₁ : (cochainC ℤ X).homology 4) (p₂ : (cochainC ℤ X).homology 8)
    (h : HirzebruchEightManifold X c p₁ p₂) :
    p₁SqNumber X c p₁ ≡ 4 * sigma 4 X c [ZMOD 7] :=
  hirzebruchEight_congruence _ _ _ h

end

end Work.SignatureBordism
