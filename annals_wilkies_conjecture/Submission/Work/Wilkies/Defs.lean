import ChallengeDeps
import Mathlib.ModelTheory.Algebra.Ring.Basic
import Mathlib.ModelTheory.Definability
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Connected.Basic

/-! Frozen vocabulary of the wilkies plan (curric-46 design 2026-10-08; cbc/wilkies_design.md). Do not edit. -/

set_option autoImplicit false
noncomputable section
open Classical
namespace WilkiesDesign
open WilkiesConjecture

/-! ## 0. Shared definitions (owned by the lead; frozen) -/

/-- `P(z, e^z)`: an exp-polynomial in `N` variables. Variable `Sum.inl i` is `z i` and
variable `Sum.inr i` is `exp (z i)`. -/
def expPolyEval {N : ℕ} (P : MvPolynomial (Fin N ⊕ Fin N) ℝ) (z : Fin N → ℝ) : ℝ :=
  MvPolynomial.eval (Sum.elim z (fun i => Real.exp (z i))) P

/-- Existentially definable in `ℝ_exp`: a projection of the zero set of one exp-polynomial.
(Inequalities, conjunctions and disjunctions all reduce to a single equation once extra
variables are added. That reduction is area B's job.) -/
def ExpExist {n : ℕ} (X : Set (Fin n → ℝ)) : Prop :=
  ∃ (m : ℕ) (P : MvPolynomial (Fin (n + m) ⊕ Fin (n + m)) ℝ),
    X = {x | ∃ y : Fin m → ℝ, expPolyEval P (Fin.append x y) = 0}

/-- Restricted exponential: `exp` on `[-1,1]`, and `0` outside. -/
def rexp (x : ℝ) : ℝ := if |x| ≤ 1 then Real.exp x else 0

def rexpPolyEval {N : ℕ} (P : MvPolynomial (Fin N ⊕ Fin N) ℝ) (z : Fin N → ℝ) : ℝ :=
  MvPolynomial.eval (Sum.elim z (fun i => rexp (z i))) P

/-- Existentially definable in `ℝ_rexp = (ℝ, +, ·, exp|[-1,1])`. -/
def RExpExist {n : ℕ} (X : Set (Fin n → ℝ)) : Prop :=
  ∃ (m : ℕ) (P : MvPolynomial (Fin (n + m) ⊕ Fin (n + m)) ℝ),
    X = {x | ∃ y : Fin m → ℝ, rexpPolyEval P (Fin.append x y) = 0}

/-- The zero set of `P(z, e^z)` inside the cube `[-M,M]^N`. -/
def boxZero {N : ℕ} (M : ℝ) (P : MvPolynomial (Fin N ⊕ Fin N) ℝ) : Set (Fin N → ℝ) :=
  {z | (∀ i, |z i| ≤ M) ∧ expPolyEval P z = 0}

/-- Graph of `f : ℝⁿ → ℝ`, as a subset of `ℝⁿ⁺¹` (last coordinate = value). -/
def graphOf {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Set (Fin (n + 1) → ℝ) :=
  {z | z (Fin.last n) = f (Fin.init z)}

/-- Drop the last coordinate. -/
def projLast {n : ℕ} (A : Set (Fin (n + 1) → ℝ)) : Set (Fin n → ℝ) :=
  {x | ∃ t : ℝ, Fin.snoc x t ∈ A}

/-- `dim X ≤ μ`, in the o-minimal sense: every projection to `μ+1` coordinates has empty interior. -/
def DimLE {n : ℕ} (X : Set (Fin n → ℝ)) (μ : ℕ) : Prop :=
  ∀ e : Fin (μ + 1) ↪ Fin n, interior ((fun x => x ∘ e) '' X) = ∅

def cube01 (n : ℕ) : Set (Fin n → ℝ) := {x | ∀ i, x i ∈ Set.Icc (0 : ℝ) 1}
def openCube (μ : ℕ) : Set (Fin μ → ℝ) := {t | ∀ i, t i ∈ Set.Ioo (0 : ℝ) 1}

/-- Cylindrical cells in `ℝⁿ`. Boundary functions are continuous on the base cell.
`band` allows `±∞` through `EReal`. -/
inductive IsCell : (n : ℕ) → Set (Fin n → ℝ) → Prop
  | zero : IsCell 0 Set.univ
  | graph {n : ℕ} {C : Set (Fin n → ℝ)} (hC : IsCell n C) (f : (Fin n → ℝ) → ℝ)
      (hf : ContinuousOn f C) :
      IsCell (n + 1) {z | Fin.init z ∈ C ∧ z (Fin.last n) = f (Fin.init z)}
  | band {n : ℕ} {C : Set (Fin n → ℝ)} (hC : IsCell n C) (a b : (Fin n → ℝ) → EReal)
      (ha : ContinuousOn a C) (hb : ContinuousOn b C) (hab : ∀ x ∈ C, a x < b x) :
      IsCell (n + 1) {z | Fin.init z ∈ C ∧ a (Fin.init z) < ((z (Fin.last n) : ℝ) : EReal) ∧
        ((z (Fin.last n) : ℝ) : EReal) < b (Fin.init z)}

/-- A cylindrical decomposition of `ℝⁿ`: a finite partition into nonempty cells whose
projections form a cylindrical decomposition of `ℝⁿ⁻¹`. -/
def IsCylDecomp : (n : ℕ) → Finset (Set (Fin n → ℝ)) → Prop
  | 0, C => C = {Set.univ}
  | n + 1, C => (∀ c ∈ C, IsCell (n + 1) c ∧ c.Nonempty) ∧
      (C : Set (Set (Fin (n + 1) → ℝ))).PairwiseDisjoint id ∧ (∀ z, ∃ c ∈ C, z ∈ c) ∧
      IsCylDecomp n (C.image (fun c => Fin.init '' c))

/-- A sharply o-minimal structure (BNZ §2.1), indexed by ambient dimension.
We drop BNZ's convention that `n ≤ F`; constants are allowed to depend on `n` as well. -/
structure SOMin where
  Ω : ℕ → ℕ → (n : ℕ) → Set (Set (Fin n → ℝ))
  mono_F : ∀ {F D n : ℕ} {X : Set (Fin n → ℝ)}, X ∈ Ω F D n → X ∈ Ω (F + 1) D n
  mono_D : ∀ {F D n : ℕ} {X : Set (Fin n → ℝ)}, X ∈ Ω F D n → X ∈ Ω F (D + 1) n
  compl : ∀ {F D n : ℕ} {X : Set (Fin n → ℝ)}, X ∈ Ω F D n → Xᶜ ∈ Ω (F + 1) D n
  proj : ∀ {F D n : ℕ} {X : Set (Fin (n + 1) → ℝ)}, X ∈ Ω F D (n + 1) →
    projLast X ∈ Ω (F + 1) D n
  prod_right : ∀ {F D n : ℕ} {X : Set (Fin n → ℝ)}, X ∈ Ω F D n →
    {z : Fin (n + 1) → ℝ | Fin.init z ∈ X} ∈ Ω (F + 1) D (n + 1)
  prod_left : ∀ {F D n : ℕ} {X : Set (Fin n → ℝ)}, X ∈ Ω F D n →
    {z : Fin (n + 1) → ℝ | Fin.tail z ∈ X} ∈ Ω (F + 1) D (n + 1)
  union : ∀ {F n k : ℕ} (D : Fin k → ℕ) (A : Fin k → Set (Fin n → ℝ)),
    (∀ i, A i ∈ Ω F (D i) n) → (⋃ i, A i) ∈ Ω F (∑ i, D i) n
  inter : ∀ {F n k : ℕ} (D : Fin k → ℕ) (A : Fin k → Set (Fin n → ℝ)),
    (∀ i, A i ∈ Ω F (D i) n) → (⋂ i, A i) ∈ Ω (F + 1) (∑ i, D i) n
  hyp : ∀ (n : ℕ) (P : MvPolynomial (Fin n) ℝ),
    {x : Fin n → ℝ | MvPolynomial.eval x P = 0} ∈ Ω n P.totalDegree n
  comps : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (D : ℕ) (A : Set (Fin 1 → ℝ)), A ∈ Ω F D 1 →
    ∃ s : Finset (Set (Fin 1 → ℝ)), s.card ≤ p.eval D ∧ (∀ c ∈ s, IsPreconnected c) ∧
      A = ⋃₀ (s : Set (Set (Fin 1 → ℝ)))

/-- Sharp cell decomposition (BNZ §2.2). -/
def SOMin.SharpCD (S : SOMin) : Prop :=
  ∀ F n : ℕ, ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : Polynomial ℕ),
    ∀ (D k : ℕ) (X : Fin k → Set (Fin n → ℝ)), (∀ i, X i ∈ S.Ω F D n) →
      ∃ C : Finset (Set (Fin n → ℝ)), IsCylDecomp n C ∧
        (∀ i, ∀ κ ∈ C, κ ⊆ X i ∨ Disjoint κ (X i)) ∧
        C.card ≤ MvPolynomial.eval ![D, k] b ∧ ∀ κ ∈ C, κ ∈ S.Ω a (c.eval D) n

/-- Sharp derivatives (BNZ §2.4). `v : Fin k → Fin n` lists the directions of a k-th order
partial derivative. The domain is the interior of the `C^k` locus. -/
def SOMin.SharpDeriv (S : SOMin) : Prop :=
  ∀ F n : ℕ, ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
    ∀ (D : ℕ) (f : (Fin n → ℝ) → ℝ), graphOf f ∈ S.Ω F D (n + 1) →
      ∀ (k : ℕ) (v : Fin k → Fin n),
        {z : Fin (n + 1) → ℝ | Fin.init z ∈ interior {x | ContDiffAt ℝ k f x} ∧
          z (Fin.last n) = iteratedFDeriv ℝ k f (Fin.init z) (fun j => Pi.single (v j) 1)}
          ∈ S.Ω a (MvPolynomial.eval ![D, k] b) (n + 1)

/-- The effective algebraic lemma (BNZ Lemma 3), in the form area H consumes. -/
def AlgLemma (S : SOMin) (F n : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin 3) ℝ, ∀ (D r : ℕ) (ε : ℝ), 0 < ε → ε < 1 →
    ∀ (μ : ℕ) (X : Set (Fin n → ℝ)), μ ≤ n → X ⊆ cube01 n → X ∈ S.Ω F D n → DimLE X μ →
      ∃ Φ : Finset ((Fin μ → ℝ) → (Fin n → ℝ)),
        (Φ.card : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), -Real.log ε] p ∧
        (∀ φ ∈ Φ, (∀ t ∈ openCube μ, φ t ∈ X) ∧ ContDiffOn ℝ r φ (openCube μ) ∧
          ∀ k ≤ r, ∀ t ∈ openCube μ, ‖iteratedFDeriv ℝ k φ t‖ ≤ 1) ∧
        ∀ x ∈ X, ∃ φ ∈ Φ, ∃ t ∈ openCube μ, dist (φ t) x < ε

/-- The counting conclusion for one format `F` and dimension `n`. It is stated over finite
subsets, so Northcott is never needed. -/
def CountBound (S : SOMin) (F n : ℕ) : Prop :=
  ∃ f : MvPolynomial (Fin 3) ℝ, ∀ (D : ℕ) (X : Set (Fin n → ℝ)), X ∈ S.Ω F D n →
    ∀ (g H : ℕ) (T : Finset (Fin n → ℝ)), (↑T : Set (Fin n → ℝ)) ⊆ degreeHeightLE X.trans g H →
      (T.card : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] f

end WilkiesDesign
