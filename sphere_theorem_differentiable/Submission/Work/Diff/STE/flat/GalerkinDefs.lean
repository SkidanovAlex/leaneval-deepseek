/-
# The Galerkin truncation: definitions

This module fixes the vocabulary for `Work.Diff.STE.flat.galerkin_ode_existence`: the
finite-dimensional space of coefficient families supported in the box `box n N`, the extension by
zero `toCoeff`, the *explicit* jet of a trigonometric polynomial with such coefficients, and the two
forms of the Galerkin right-hand side.

## Why an explicit jet

The statement of the Galerkin ODE

`c' = projBox N (fourierCoeff (Φ ∘ jet))`

involves `jetM (seriesFunM (toCoeff a))`, i.e. the value, the first and the second *coordinate
derivatives* of a Fourier series.  For a coefficient family supported in the box the series is a
finite sum of characters, so all three jets can be written down explicitly (`valExp`, `linExp`,
`secExp`, assembled as `jetExp`), and each is a *finite sum of products* of a linear function of the
coefficients with a smooth function of `x`.  That is the form in which smoothness and Lipschitz
estimates are proved.

The identity `jetM (seriesFunM (toCoeff a)) x = jetExp a x` is
`Work.Diff.STE.Flat.Galerkin.jetM_seriesFunM_toCoeff` (sibling file).
-/
import Mathlib
import Submission.Work.Diff.STE.FlatPDE

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE

namespace Flat

namespace Galerkin

noncomputable section

open scoped BigOperators

/-- The finite-dimensional real vector space of coefficient families of `MatC n`-valued
coefficients supported on the box `box n N`. -/
abbrev Coeff (n N : ℕ) := (box n N) → MatC n

/-- The closed unit cube `[0,1]^n`, a compact convex fundamental domain. -/
def closedCube (n : ℕ) : Set (Fin n → ℝ) := Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1

/-- Extension by zero of a box-supported coefficient family. -/
def toCoeff {n N : ℕ} (a : Coeff n N) : (Fin n → ℤ) → MatC n :=
  fun k => if h : k ∈ box n N then a ⟨k, h⟩ else 0

@[simp] lemma toCoeff_apply_mem {n N : ℕ} (a : Coeff n N) {k : Fin n → ℤ}
    (hk : k ∈ box n N) : toCoeff a k = a ⟨k, hk⟩ := dif_pos hk

@[simp] lemma toCoeff_apply_not_mem {n N : ℕ} (a : Coeff n N) {k : Fin n → ℤ}
    (hk : k ∉ box n N) : toCoeff a k = 0 := dif_neg hk

lemma toCoeff_injective {n N : ℕ} : Function.Injective (toCoeff (n := n) (N := N)) := by
  intro a b hab
  funext k
  have := congrFun hab k.1
  rwa [toCoeff_apply_mem a k.2, toCoeff_apply_mem b k.2] at this

/-- Directional derivative of the character `fourierExp m` in the direction `e_c`,
`∂_c e^{2π i m·x} = 2π i m_c e^{2π i m·x}`. -/
def dExp {n : ℕ} (m : Fin n → ℤ) (c : Fin n) (x : Fin n → ℝ) : ℂ :=
  (2 * Real.pi * Complex.I * (m c : ℂ)) * Work.Diff.STE.fourierExp m x

/-- Second directional derivative of the character, first in the direction `e_d` and then `e_c`. -/
def d2Exp {n : ℕ} (m : Fin n → ℤ) (d c : Fin n) (x : Fin n → ℝ) : ℂ :=
  (2 * Real.pi * Complex.I * (m d : ℂ)) * dExp m c x

/-- The value component of the explicit jet: the trigonometric polynomial of the coefficients
`a` supported on the box. -/
def valExp {n N : ℕ} (a : Coeff n N) (x : Fin n → ℝ) : MatC n :=
  fun i j => ∑ m : box n N, a m i j * Work.Diff.STE.fourierExp m.1 x

/-- The first-derivative component of the explicit jet. -/
def linExp {n N : ℕ} (a : Coeff n N) (x : Fin n → ℝ) : Fin n → MatC n :=
  fun c i j => ∑ m : box n N, a m i j * dExp m.1 c x

/-- The second-derivative component of the explicit jet. -/
def secExp {n N : ℕ} (a : Coeff n N) (x : Fin n → ℝ) : Fin n → Fin n → MatC n :=
  fun c d i j => ∑ m : box n N, a m i j * d2Exp m.1 d c x

/-- The explicit spatial `2`-jet of the trigonometric polynomial with coefficients `a`. -/
def jetExp {n N : ℕ} (a : Coeff n N) (x : Fin n → ℝ) : Jet n :=
  (valExp a x, linExp a x, secExp a x)

@[simp] lemma jetExp_fst {n N : ℕ} (a : Coeff n N) (x : Fin n → ℝ) :
    (jetExp a x).1 = valExp a x := rfl

@[simp] lemma jetExp_snd {n N : ℕ} (a : Coeff n N) (x : Fin n → ℝ) :
    (jetExp a x).2.1 = linExp a x := rfl

@[simp] lemma jetExp_trd {n N : ℕ} (a : Coeff n N) (x : Fin n → ℝ) :
    (jetExp a x).2.2 = secExp a x := rfl

/-- The Galerkin right-hand side, in the form of the statement (`jetM` of the Fourier series). -/
def rhs {n N : ℕ} (Φ : (Fin n → ℝ) × Jet n → MatC n) (a : Coeff n N) : Coeff n N :=
  fun k i j => Work.Diff.STE.fourierCoeff
    (fun x => Φ (x, jetM (seriesFunM (toCoeff a)) x) i j) k.1

/-- The Galerkin right-hand side, in the explicit-jet form used for the estimates. -/
def rhsExp {n N : ℕ} (Φ : (Fin n → ℝ) × Jet n → MatC n) (a : Coeff n N) : Coeff n N :=
  fun k i j => Work.Diff.STE.fourierCoeff (fun x => Φ (x, jetExp a x) i j) k.1

/-- The coefficient family supported on the box associated with a globally supported family `c`
with `c = 0` outside the box. -/
def ofCoeff {n N : ℕ} (c : (Fin n → ℤ) → MatC n) (hc : ∀ k, k ∉ box n N → c k = 0) :
    Coeff n N := fun k => c k.1

lemma toCoeff_ofCoeff {n N : ℕ} (c : (Fin n → ℤ) → MatC n)
    (hc : ∀ k, k ∉ box n N → c k = 0) : toCoeff (ofCoeff c hc) = c := by
  funext k
  by_cases hk : k ∈ box n N
  · rw [toCoeff_apply_mem _ hk]; rfl
  · rw [toCoeff_apply_not_mem _ hk, hc k hk]

end

end Galerkin

end Flat

end Work.Diff.STE
