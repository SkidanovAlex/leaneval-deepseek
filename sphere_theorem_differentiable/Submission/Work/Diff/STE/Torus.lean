import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer A of the STE development: the Fourier/Sobolev toolkit on the unit torus

We work with functions `f : (ι → ℝ) → ℂ` that are `1`-periodic in every coordinate (the
"functions on the flat torus" of the lead's design, REFS/NOTES_LEAD_P1_STE.md, Layer A).

Main definitions:

* `unitCube`      : the half open unit cube `(0,1]^ι`, a fundamental domain;
* `fourierExp k`  : the character `x ↦ exp (2πi k·x)`;
* `fourierCoeff f k` : the `k`-th Fourier coefficient `∫_{cube} exp(-2πi k·x) f x`;
* `wt k`          : the weight `⟨k⟩² = 1 + Σ kᵢ²`;
* `Hsq s f`       : `Σ_k ⟨k⟩^{2s} ‖û(k)‖²`, the square of the `Hˢ` (Sobolev) seminorm;
* `pd i f`        : the `i`-th partial derivative (directional derivative along `eᵢ`).

Everything in Layer A is a statement about these objects; the estimates of the design
(A1–A9) are stated in terms of them in the sibling files.
-/

noncomputable section

namespace Work.Diff.STE

open MeasureTheory BigOperators
open scoped ComplexConjugate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The half open unit cube `(0,1]^ι` in `ι → ℝ`. -/
def unitCube : Set (ι → ℝ) := Set.pi Set.univ fun _ => Set.Ioc (0 : ℝ) 1

/-- The complex Fourier monomial `x ↦ exp (2πi k·x)`. -/
def fourierExp (k : ι → ℤ) (x : ι → ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ∑ i, (k i : ℂ) * (x i : ℂ))

/-- The `k`-th Fourier coefficient of `f`, `∫_{cube} exp (-2πi k·x) f x`. -/
def fourierCoeff (f : (ι → ℝ) → ℂ) (k : ι → ℤ) : ℂ :=
  ∫ x in unitCube, fourierExp (-k) x * f x

/-- `1`-periodicity of `f` in every coordinate: `f (x + eᵢ) = f x`. -/
def Periodic1 {β : Type*} (f : (ι → ℝ) → β) : Prop :=
  ∀ (i : ι) (x : ι → ℝ), f (x + Pi.single i 1) = f x

/-- `1`-periodicity of `f` in the coordinate `i`. -/
def PeriodicIn {β : Type*} (i : ι) (f : (ι → ℝ) → β) : Prop :=
  ∀ x : ι → ℝ, f (x + Pi.single i 1) = f x

/-- The `i`-th partial derivative of `f` (directional derivative along `eᵢ`). -/
def pd (i : ι) (f : (ι → ℝ) → ℂ) : (ι → ℝ) → ℂ :=
  fun x => fderiv ℝ f x (Pi.single i 1)

/-- The weight `⟨k⟩² = 1 + Σ kᵢ²`. -/
def wt (k : ι → ℤ) : ℝ := 1 + ∑ i, ((k i : ℤ) : ℝ) ^ 2

/-- The square of the `Hˢ` seminorm, `Σ_k ⟨k⟩^{2s} ‖û(k)‖²`. -/
def Hsq (s : ℕ) (f : (ι → ℝ) → ℂ) : ℝ :=
  ∑' k : ι → ℤ, (wt k) ^ s * ‖fourierCoeff f k‖ ^ 2

/-- The `Hˢ` seminorm of `f`. -/
def Hnorm (s : ℕ) (f : (ι → ℝ) → ℂ) : ℝ := Real.sqrt (Hsq s f)

/-- The `L²` inner product on the cube, `∫_{cube} conj f · g`. -/
def L2IP (f g : (ι → ℝ) → ℂ) : ℂ := ∫ x in unitCube, conj (f x) * g x

/-- The `L²` norm squared on the cube, `∫_{cube} ‖f‖²`. -/
def L2sq (f : (ι → ℝ) → ℂ) : ℝ := ∫ x in unitCube, ‖f x‖ ^ 2

lemma wt_pos (k : ι → ℤ) : 0 < wt k := by
  simp only [wt]
  have : 0 ≤ ∑ i, ((k i : ℤ) : ℝ) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  linarith

omit [DecidableEq ι] in
lemma wt_one_le (k : ι → ℤ) : 1 ≤ wt k := by
  have : 0 ≤ ∑ i, ((k i : ℤ) : ℝ) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  simp only [wt]; linarith


/-! ## Coefficient families on `ℤᵈ`

All the estimates of Layer A are, after Fourier transformation, inequalities about families
`c : (ι → ℤ) → ℂ`.  We record the basic operations here: convolution (the Fourier side of
pointwise multiplication), the multiplier of a partial derivative, and the weighted `ℓ²`
norms. -/

/-- Convolution of coefficient families; this is the Fourier side of pointwise multiplication. -/
def conv (c d : (ι → ℤ) → ℂ) : (ι → ℤ) → ℂ := fun k => ∑' l : ι → ℤ, c l * d (k - l)

/-- The weighted `ℓ²` norm squared of a coefficient family, `Σ_k ⟨k⟩^{2s} ‖c k‖²`. -/
def CSq (s : ℕ) (c : (ι → ℤ) → ℂ) : ℝ := ∑' k : ι → ℤ, (wt k) ^ s * ‖c k‖ ^ 2

/-- The `ℓ¹` norm of a coefficient family. -/
def l1 (c : (ι → ℤ) → ℂ) : ℝ := ∑' k : ι → ℤ, ‖c k‖

/-- The Fourier multiplier of `∂ᵢ - ı`, i.e. `∂ᵢ` is `2πi kᵢ` on the Fourier side. -/
def dmul (i : ι) (c : (ι → ℤ) → ℂ) : (ι → ℤ) → ℂ :=
  fun k => (2 * Real.pi * Complex.I * (k i : ℂ)) * c k

/-- The function on the torus with coefficient family `c`, `x ↦ Σ_k c k * exp (2πi k·x)`. -/
def seriesFun (c : (ι → ℤ) → ℂ) : (ι → ℝ) → ℂ := fun x => ∑' k : ι → ℤ, c k * fourierExp k x

lemma Hsq_eq_CSq (s : ℕ) (f : (ι → ℝ) → ℂ) :
    Hsq s f = CSq s (fourierCoeff f) := rfl


/-- Sum of the derivative monomials `∏ᵢ (2π mᵢ)^{2 αᵢ}` over multi-indices `α` of total degree
`≤ k`.  This is the Fourier-side weight of `Σ_{|α| ≤ k} ‖∂^α f‖²_{L²}`. -/
def monomialSum (k : ℕ) (m : ι → ℤ) : ℝ :=
  ∑ α : ι → Fin (k + 1),
    if (∑ i, (α i : ℕ)) ≤ k then
      ∏ i, (2 * Real.pi * (m i : ℝ)) ^ (2 * (α i : ℕ))
    else 0


/-- Fourier truncation of a coefficient family: multiply the `k`-th coefficient by `ρ (ε k)`.
This is the Fourier side of the Friedrichs mollifier used in the energy method (design A8). -/
def trunc (ρ : (ι → ℝ) → ℝ) (ε : ℝ) (c : (ι → ℤ) → ℂ) : (ι → ℤ) → ℂ :=
  fun k => (ρ (ε • (fun i => (k i : ℝ))) : ℂ) * c k

/-- The Fourier multiplier of the multi-index derivative `∂^α`, i.e. `∏ᵢ (2π kᵢ)^{αᵢ}`. -/
def dmulMulti (α : ι → ℕ) (c : (ι → ℤ) → ℂ) : (ι → ℤ) → ℂ :=
  fun k => (∏ i, (2 * Real.pi * Complex.I * (k i : ℂ)) ^ (α i)) * c k


/-- The real part of the `L²` pairing of two functions on the cube. -/
def L2re (f g : (ι → ℝ) → ℂ) : ℝ := Complex.re (∫ x in unitCube, f x * star (g x))

/-- The `L²` norm squared of a function on the cube. -/
def L2normSq (f : (ι → ℝ) → ℂ) : ℝ := ∫ x in unitCube, ‖f x‖ ^ 2


/-- The `i`-th partial derivative of a real-valued function. -/
def pdR (i : ι) (f : (ι → ℝ) → ℝ) : (ι → ℝ) → ℝ := fun x => fderiv ℝ f x (Pi.single i 1)


/-- Iterated partial derivative along a list of directions. -/
def pdList (l : List ι) (f : (ι → ℝ) → ℂ) : (ι → ℝ) → ℂ := l.foldr (fun i g => pd i g) f

/-- Iterated partial derivative of order `≤ k`, indexed by `Fin k → ι`; repeated and dummy
directions are allowed, which only changes constants.  This is the index set used for the
`Hᵏ` energy estimates (`ENormSq`). -/
def pdVec (k : ℕ) (l : Fin k → ι) (f : (ι → ℝ) → ℂ) : (ι → ℝ) → ℂ := pdList (List.ofFn l) f

/-- The sum of the `L²` norms squared of all derivatives of order `≤ k`; the physical-space
counterpart of `CSq k (fourierCoeff f)`. -/
def ENormSq (k : ℕ) (f : (ι → ℝ) → ℂ) : ℝ :=
  ∑ l : Fin k → ι, ∫ x in unitCube, ‖pdVec k l f x‖ ^ 2


/-- Iterated partial derivative of a real-valued function along a list. -/
def pdRList (l : List ι) (f : (ι → ℝ) → ℝ) : (ι → ℝ) → ℝ := l.foldr (fun i g => pdR i g) f

/-- Iterated partial derivative of a real-valued function, indexed by `Fin k → ι`. -/
def pdRVec (k : ℕ) (l : Fin k → ι) (f : (ι → ℝ) → ℝ) : (ι → ℝ) → ℝ := pdRList (List.ofFn l) f


/-- A trigonometric polynomial with coefficient family `p : (ι → ℤ) →₀ ℂ`, as a function on the
torus.  These are the functions in the range of the Friedrichs mollifier. -/
def trigFun (p : (ι → ℤ) →₀ ℂ) : (ι → ℝ) → ℂ :=
  fun x => ∑ k ∈ p.support, p k * fourierExp k x

end Work.Diff.STE
