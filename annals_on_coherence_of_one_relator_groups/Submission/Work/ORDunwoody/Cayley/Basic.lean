/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# The Cayley complex of a finite presentation: the 1-skeleton

`dunwoodyResolution` is proved by Dunwoody's pattern/tracks construction inside the universal
cover `Λ` of a finite presentation 2-complex (`DESIGN_N13.md`).  This file builds `Λ`.

* `genF`, `genE`: a generator-with-sign, as an element of the free group and of `G`;
* `swapLetter`: the reversal of a generator-with-sign;
* `CayV P`: the vertex type of the Cayley complex (a copy of `G`, made a *structure* so that a
  `Quiver` instance can be registered on it without a global instance on `G`);
* the Cayley quiver: `a ⟶ b` is the set of letters `x` with `a * genE x = b`, with the
  involutive reversal `x ↦ swapLetter x`;
* `cayEnd`, `cayPath`: the canonical path spelling a word from a vertex;
* `pathLabel`: the word of a path;
* `cayPath_snoc` and `pathLabel_cayPath`: the comparison between `cayPath` and an arbitrary
  path, which is what turns the word-theoretic computation of `π₁` into statements about
  paths.

## Implementation notes

Since `FreeGroup α` in this Mathlib is a quotient of `List (α × Bool)` and has no recursor, the
face boundaries are built from `FreeGroup.toWord` together with `cayPath`.

`CayV P` is a genuine structure (not a type synonym `G`) because the `Quiver` instance must be
found by typeclass search for the type `CayV P` without a `FinPresentation` parameter being
invented by unification.
-/
import Mathlib
import Submission.Work.ORDunwoody.Foundations.Presentation

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORDunwoody.Cayley

open Quiver

variable {G : Type u}

/-- The free-group letter determined by a generator-with-sign: `(i, false) ↦ of i`,
`(i, true) ↦ (of i)⁻¹`. -/
def genF (n : ℕ) : Fin n × Bool → FreeGroup (Fin n)
  | (i, false) => (FreeGroup.of i)⁻¹
  | (i, true) => FreeGroup.of i

/-- The reversal of a generator-with-sign. -/
def swapLetter {n : ℕ} (x : Fin n × Bool) : Fin n × Bool := (x.1, !x.2)

@[simp] theorem swapLetter_swapLetter {n : ℕ} (x : Fin n × Bool) :
    swapLetter (swapLetter x) = x := by
  unfold swapLetter; cases x with | mk i b => cases b <;> rfl

theorem genF_swap (n : ℕ) (x : Fin n × Bool) : genF n (swapLetter x) = (genF n x)⁻¹ := by
  unfold swapLetter
  cases x with
  | mk i b => cases b <;> simp [genF]

/-- The vertex type of the Cayley complex of a finite presentation. -/
structure CayV (G : Type u) [Group G] (P : FinPresentation G) where
  /-- The underlying group element. -/
  pt : G

namespace CayV

variable [Group G] {P : FinPresentation G}

instance instCoe : CoeOut (CayV G P) G := ⟨pt⟩

@[ext] theorem ext (v w : CayV G P) (h : v.pt = w.pt) : v = w := by
  cases v; cases w; simp_all

@[simp] theorem pt_mk (x : G) : (⟨x⟩ : CayV G P).pt = x := rfl

theorem pt_injective : Function.Injective (fun v : CayV G P => v.pt) := fun _ _ h => ext _ _ h

/-- The image in `G` of a generator-with-sign. -/
def genE (P : FinPresentation G) (x : Fin P.n × Bool) : G := P.π (genF P.n x)

theorem genE_false (P : FinPresentation G) (i : Fin P.n) :
    genE P (i, false) = (P.π (FreeGroup.of i))⁻¹ :=
  map_inv P.π (FreeGroup.of i)

theorem genE_true (P : FinPresentation G) (i : Fin P.n) :
    genE P (i, true) = P.π (FreeGroup.of i) := rfl

/-- `genF` is the one-letter word. -/
theorem genF_eq_mk (n : ℕ) (x : Fin n × Bool) : genF n x = FreeGroup.mk [x] := by
  unfold genF
  cases x with
  | mk i b => cases b <;> rfl

theorem genE_swap (P : FinPresentation G) (x : Fin P.n × Bool) :
    genE P (swapLetter x) = (genE P x)⁻¹ := by
  unfold genE
  rw [genF_swap]
  exact map_inv P.π _

instance instMulAction : MulAction G (CayV G P) where
  smul g v := ⟨g * v.pt⟩
  one_smul v := CayV.ext _ _ (one_mul v.pt)
  mul_smul g h v := CayV.ext _ _ (mul_assoc g h v.pt)

@[simp] theorem smul_pt (g : G) (v : CayV G P) : (g • v).pt = g * v.pt := rfl

instance instQuiver : Quiver (CayV G P) :=
  ⟨fun a b => { x : Fin P.n × Bool // a.pt * genE P x = b.pt }⟩

theorem hom_eq (P : FinPresentation G) (a b : CayV G P) :
    (a ⟶ b) = { x : Fin P.n × Bool // a.pt * genE P x = b.pt } := rfl

/-- The letter of an arrow of the Cayley quiver. -/
abbrev Hom.letter {a b : CayV G P} (e : a ⟶ b) : Fin P.n × Bool := e.1

theorem Hom.letter_spec {a b : CayV G P} (e : a ⟶ b) : a.pt * genE P e.1 = b.pt := e.2

instance instHasInvolutiveReverse : HasInvolutiveReverse (CayV G P) where
  reverse' := fun {a b} e => ⟨swapLetter e.1, by
    have h : a.pt * genE P e.1 = b.pt := e.2
    show b.pt * genE P (swapLetter e.1) = a.pt
    rw [genE_swap]
    calc b.pt * (genE P e.1)⁻¹ = (a.pt * genE P e.1) * (genE P e.1)⁻¹ := by rw [h]
      _ = a.pt := by group⟩
  inv' := fun {a b} e => by
    apply Subtype.ext
    exact swapLetter_swapLetter e.1

@[simp] theorem reverse_letter {a b : CayV G P} (e : a ⟶ b) :
    (Quiver.reverse e).1 = swapLetter e.1 := rfl

end CayV

open CayV

variable [Group G]

/-- The vertex reached from `a` by the word `w`. -/
def cayEnd (P : FinPresentation G) (a : CayV G P) (w : List (Fin P.n × Bool)) : CayV G P :=
  w.foldl (fun b x => ⟨b.pt * genE P x⟩) a

@[simp] theorem cayEnd_nil (P : FinPresentation G) (a : CayV G P) : cayEnd P a [] = a := rfl

@[simp] theorem cayEnd_cons (P : FinPresentation G) (a : CayV G P) (x : Fin P.n × Bool)
    (w : List (Fin P.n × Bool)) :
    cayEnd P a (x :: w) = cayEnd P ⟨a.pt * genE P x⟩ w := rfl

/-- **The canonical path spelling a word from a vertex of the Cayley complex.** -/
noncomputable def cayPath (P : FinPresentation G) (a : CayV G P) :
    (w : List (Fin P.n × Bool)) → Quiver.Path a (cayEnd P a w)
  | [] => Quiver.Path.nil
  | x :: w =>
      (Quiver.Path.nil.cons (⟨x, rfl⟩ : a ⟶ ⟨a.pt * genE P x⟩)).comp
        (cayPath P ⟨a.pt * genE P x⟩ w)

@[simp] theorem cayPath_nil (P : FinPresentation G) (a : CayV G P) :
    cayPath P a [] = Quiver.Path.nil := rfl

theorem cayPath_cons (P : FinPresentation G) (a : CayV G P) (x : Fin P.n × Bool)
    (w : List (Fin P.n × Bool)) :
    cayPath P a (x :: w) =
      (Quiver.Path.nil.cons (⟨x, rfl⟩ : a ⟶ ⟨a.pt * genE P x⟩)).comp
        (cayPath P ⟨a.pt * genE P x⟩ w) := rfl

/-- The word of a path in the Cayley quiver. -/
def pathLabel (P : FinPresentation G) (a : CayV G P) :
    ∀ {b : CayV G P}, Quiver.Path a b → List (Fin P.n × Bool)
  | _, .nil => []
  | _, .cons p e => pathLabel P a p ++ [e.1]

@[simp] theorem pathLabel_nil (P : FinPresentation G) (a : CayV G P) :
    pathLabel P a (Quiver.Path.nil : Quiver.Path a a) = [] := rfl

@[simp] theorem pathLabel_cons (P : FinPresentation G) {a b c : CayV G P}
    (p : Quiver.Path a b) (e : b ⟶ c) :
    pathLabel P a (p.cons e) = pathLabel P a p ++ [e.1] := rfl

end Work.ORDunwoody.Cayley
