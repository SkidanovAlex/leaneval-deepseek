/-
# EKLC8Core: the standalone real-analysis / linear-algebra core of the low-entropy method

This file fixes the vocabulary of component C8 of the EKL formalisation (`ROUTE_LEAD.md` §5,
EKL §4.2–4.5).  Everything here is independent of the leafwise-measure layer
(`IsLeafwise`, `P_Leafwise`): it is about the group `SL₃(ℝ)`, the diagonal flow
`φ_τ = α^{-τ(-1,1,0)}`, the root groups `U_ij`, and explicit matrix entries.

Conventions (all fixed once here):
* `Fin 3` indices `0,1,2` are the paper's indices `1,2,3`; the distinguished pair is
  `(a,b) = (0,1)` and `c = 2`.
* `uij h s = 1 + s E_ij` is `u_ij(s)`, the shear `u(r)` of the paper is `uij h01 r`.
* `phi τ = diag(e^{-τ}, e^{τ}, 1) = α^{-τ t}` with `t = (-1,1,0)`; it contracts `U_01`
  (entry `(0,1)`) by `e^{-2τ}`.
* `kappa`, `kappaA`, `kappaU` are the three quantities of EKL (4.4)/(4.6);
  `drift` and `u12max` are the two sides of Ratner's H-property bounds
  (EKL (e:boundC) and (e:boundC2)).
-/
import Mathlib

noncomputable section

namespace Work.EKLC8Core

open scoped Matrix
open MeasureTheory

/-! ## The group and the flow -/

/-- `SL₃(ℝ)`, as Mathlib's special linear group. -/
abbrev SL3 : Type := Matrix.SpecialLinearGroup (Fin 3) ℝ

/-- `α^t = diag(e^{t_i - (∑ t_j)/3})`: EKL's diagonal element, normalised. -/
def aDiag (t : Fin 3 → ℝ) : SL3 :=
  ⟨Matrix.diagonal (fun i => Real.exp (t i - (∑ j, t j) / 3)), by
    rw [Matrix.det_diagonal, ← Real.exp_sum, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h3 : ((3 : ℕ) : ℝ) * ((∑ j, t j) / 3) = ∑ j, t j := by push_cast; ring
    rw [h3, sub_self, Real.exp_zero]⟩

/-- The exponent vector `t = (-1,1,0)` of the flow direction used in C8.
`φ_τ = α^{-τt} = aDiag(τ • flowExp) = diag(e^{-τ}, e^{τ}, 1)`. -/
def flowExp : Fin 3 → ℝ := ![-1, 1, 0]

/-- `α' = diag(e^s, e^s, e^{-2s})` with the slot `c` carrying `-2s`: the group `A'_{ab}`
(EKL §4.1; here always used with `c = 2`, the third index of the pair `(0,1)`). -/
def aPrime (c : Fin 3) (s : ℝ) : SL3 := aDiag (fun i => if i = c then -2 * s else s)

/-- The contracting flow `φ_τ = diag(e^{-τ}, e^{τ}, 1)`, `τ : ℝ`. -/
def phi (τ : ℝ) : SL3 := aDiag (τ • flowExp)

/-- `u_ij(s) = 1 + s E_ij`, written with `Matrix.SpecialLinearGroup.transvection`. -/
def uij {i j : Fin 3} (h : i ≠ j) (s : ℝ) : SL3 := Matrix.SpecialLinearGroup.transvection h s

/-- The root subgroup `U_ij`. -/
def Uij {i j : Fin 3} (h : i ≠ j) : Subgroup SL3 :=
  Subgroup.closure (Set.range fun s : ℝ => uij h s)

/-- EKL's `U_(ab) = ⟨U_ab, U_ac, U_cb⟩` (`c` the third index). -/
def Upar {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b) : Subgroup SL3 :=
  Uij hab ⊔ Uij hac ⊔ Uij hcb

/-- `u_ij([-R,R])`, the ball in the root group used to phrase leafwise measures on `ℝ`. -/
def ballU {i j : Fin 3} (h : i ≠ j) (R : ℝ) : Set SL3 :=
  (fun s : ℝ => uij h s) '' Set.Icc (-R) R

/-- Displacement neighbourhood of the identity: max-entry distance `< δ` from `1`. -/
def V (δ : ℝ) : Set SL3 :=
  {g | ∀ i j, |(g : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < δ}

/-- The shape `[[1,p,q],[0,1,0],[0,r,1]]` of the limit displacement `h` of EKL §4.5
(Step 11 of `ROUTE_LEAD.md` §5): an element of the Heisenberg group `U_(01)`. -/
def uparShape (p q r : ℝ) : SL3 :=
  ⟨!![1, p, q; 0, 1, 0; 0, r, 1], by simp [Matrix.det_fin_three]⟩

/-- The distinguished index pair `(0,1)` of C8. -/
abbrev h01 : (0 : Fin 3) ≠ 1 := by decide

/-- The two "third index" pairs. -/
abbrev h02 : (0 : Fin 3) ≠ 2 := by decide
abbrev h12 : (1 : Fin 3) ≠ 2 := by decide
abbrev h10 : (1 : Fin 3) ≠ 0 := by decide
abbrev h20 : (2 : Fin 3) ≠ 0 := by decide
abbrev h21 : (2 : Fin 3) ≠ 1 := by decide

/-! ## The shearing map `g ↦ u(r) g u(-r)` (EKL (e:As)) -/

/-- `r ↦ u(r)`, i.e. `u_01(r)`, the one-parameter unipotent used in C8. -/
def u (r : ℝ) : SL3 := uij h01 r

/-- The shear `g ↦ u(r) g u(-r)` of EKL (e:As) (there called `g(r)`). -/
def shear (g : SL3) (r : ℝ) : SL3 := u r * g * u (-r)

/-- The same shearing, on plain matrices ("`u(r) g u(-r)`"). -/
def shearMat (g : Matrix (Fin 3) (Fin 3) ℝ) (r : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (1 + Matrix.single 0 1 r) * g * (1 - Matrix.single 0 1 r)

/-! ## The quantities `κ, κ_a, κ_u` of EKL (4.4) and the H-property bounds

For a matrix `g` (thought of as the displacement matrix `g̃ = φ_τ g φ_τ⁻¹` obtained after
time `τ` of the flow), in the paper's notation
`κ_a = |a₂-a₁| = |g₁₁-g₀₀|`, `κ_u = max(|g₂₁|^{1/2}, |g₃₁|, |g₂₃|)` and
`κ = max(κ_a, κ_u)`.

`drift g r` is the left hand side of Ratner's H-property estimate EKL (e:boundC), i.e. the
max of the three "drift" entries `(a₂-a₁)r - g₂₁r²`, `g₂₃r`, `g₃₁r`; after the shear
`u(r) g u(-r)` these are (up to the `g₁₂` term) the `U_(12)`-entries `(0,1),(0,2),(2,1)`.
`u12max M` is the max of those three `U_(12)`-entries of a matrix `M`. -/

/-- `κ_a(g) = |a₂ - a₁| = |g₁₁ - g₀₀|`. -/
def kappaA (g : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := |g 1 1 - g 0 0|

/-- `κ_u(g) = max(|g₂₁|^{1/2}, |g₃₁|, |g₂₃|) = max(√|g₁₀|, |g₂₀|, |g₁₂|)`. -/
def kappaU (g : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  max (Real.sqrt |g 1 0|) (max |g 2 0| |g 1 2|)

/-- `κ(g) = max(κ_a(g), κ_u(g))`. -/
def kappa (g : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := max (kappaA g) (kappaU g)

/-- The max of the three `U_(12)`-entries of `M`: `max(|M₀₁|, |M₀₂|, |M₂₁|)`. -/
def u12max (M : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := max (max |M 0 1| |M 0 2|) |M 2 1|

/-- The drift `max(|(a₂-a₁)r - g₂₁r²|, |g₂₃r|, |g₃₁r|)` of EKL (e:boundC). -/
def drift (g : Matrix (Fin 3) (Fin 3) ℝ) (r : ℝ) : ℝ :=
  max (max |(g 1 1 - g 0 0) * r - g 1 0 * r ^ 2| |g 1 2 * r|) |g 2 0 * r|

/-- The `U_(12)`-entries of the sheared matrix `shearMat g r`, in the paper's notation. -/
def shearEntry01 (g : Matrix (Fin 3) (Fin 3) ℝ) (r : ℝ) : ℝ :=
  g 0 1 + (g 1 1 - g 0 0) * r - g 1 0 * r ^ 2

def shearEntry02 (g : Matrix (Fin 3) (Fin 3) ℝ) (r : ℝ) : ℝ := g 0 2 + g 1 2 * r

def shearEntry21 (g : Matrix (Fin 3) (Fin 3) ℝ) (r : ℝ) : ℝ := g 2 1 - g 2 0 * r

/-! ## Normalisation of the flow at the scale `T = ¼|ln κ|` -/

/-- The time `T = ¼|ln κ|` of EKL Lemma 4.5/4.6. -/
def Tscale (κ : ℝ) : ℝ := (1 / 4) * |Real.log κ|

/-- `BadAt ν ρ S`: the conclusion of EKL Lemma 4.5 and of EKL Lemma 4.6, phrased for a
measure `ν` on `ℝ` (in applications the push-forward of a leafwise measure along
`u(r) ↦ r`, normalised by `ν [−1,1] = 1`):

  `ν([−ρS,ρS]) < ½ ν([−S,S])`.

The values are taken with `Measure.real` (`= (μ s).toReal`), which agrees with the
`ℝ≥0∞`-valued inequality whenever `ν` is finite on the relevant compact interval (as
leafwise measures and Lebesgue measure are). -/
def BadAt (ν : Measure ℝ) (ρ S : ℝ) : Prop :=
  ν.real (Set.Icc (-(ρ * S)) (ρ * S)) < (1 / 2) * ν.real (Set.Icc (-S) S)

/-- EKL's condition `x ∈ 𝒳(ρ)`: `ν_x([−ρ,ρ]) < ½ ν_x([−1,1])`. -/
def InXrho (ν : Measure ℝ) (ρ : ℝ) : Prop := BadAt ν ρ 1

/-! ## Lebesgue measure, as a real number -/

/-- Lebesgue measure of a subset of `ℝ`, as a real number: `(volume s).toReal`.
This is the form in which all the density bookkeeping of C8 (Steps 7–9 of
`ROUTE_LEAD.md` §5) is phrased; `Vol.lean` provides its API. -/
def vol (s : Set ℝ) : ℝ := (volume s).toReal

end Work.EKLC8Core
