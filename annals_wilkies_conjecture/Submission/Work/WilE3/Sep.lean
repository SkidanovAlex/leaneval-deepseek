/-
  annals_wilkies_conjecture, AREA E3 (`Submission.Work.WilE3`): separable chains, local form.

  Area E2 owns `Work.WilE2.SepChain` (`Submission/Work/WilE2/SepChain.lean`) and its internal bound
  `Work.WilE2.SepKhovanskiiBound`.  E3 needs the same notion with one difference: the half-angle
  chain function `t ↦ tan t` used by the realification of a *complexified* exp-affine system
  satisfies `φ' = 1 + φ²` only away from its poles, so E2's field
  `hderiv : ∀ y, HasDerivAt (phi j) … y` is unsatisfiable for `φ = Real.tan` and cannot host the
  realification.  Here the relation is therefore required only *locally* (`∀ y, ∃ ε > 0, ∀ z,
  |z - y| < ε → …`), which `Real.tan` satisfies (its poles are isolated) and which still gives
  `∂ᵢ (φ_j ∘ ℓ_j) = a_{j i} · R_j (φ_j ∘ ℓ_j)` on the region where the chain is used.

  The intended instance is the realification of a complexified exp-affine system described in
  `NOTES.md` §3: variables `(Re z, Im z)`, chain functions `y_j = e^{(Re ℓ_j) (z)}` (`φ = Real.exp`,
  `R = X`) and `t_j = tan ((Im ℓ_j) (z) / 2)` (`φ = Real.tan`, `R = 1 + X²`), after clearing the
  denominators `(1 + t_j²)^{deg}`.
-/
import Submission.Work.Wilkies.E.Spec

set_option autoImplicit false
noncomputable section
open Classical Topology
namespace Work.WilE3

/-- A *local* separable chain: `r` chain functions `ψ_j = φ_j ∘ ℓ_j` with `ℓ_j` affine, such that
`φ_j' = R_j ∘ φ_j` holds locally at every point (so that `φ = Real.tan` is allowed, `R = 1 + X²`). -/
structure SepChainLocal (n r : ℕ) where
  a : Fin r → Fin n → ℝ
  b : Fin r → ℝ
  phi : Fin r → ℝ → ℝ
  R : Fin r → MvPolynomial (Fin 1) ℝ
  /-- the set on which the chain function satisfies its differential equation -/
  dom : Fin r → Set ℝ
  hderiv : ∀ (j : Fin r) (y : ℝ), y ∈ dom j →
    HasDerivAt (phi j) ((R j).eval (fun _ => phi j y)) y

namespace SepChainLocal

variable {n r : ℕ}

/-- `R_j` with its variable read as the `j`-th chain value. -/
def Rpoly (S : SepChainLocal n r) (j : Fin r) : WilkiesDesign.E.EAPoly n r :=
  MvPolynomial.rename (fun _ => Sum.inr j) (S.R j)

/-- The chain function `ψ_j = φ_j (ℓ_j x)`. -/
def psi (S : SepChainLocal n r) (j : Fin r) (x : Fin n → ℝ) : ℝ :=
  S.phi j (∑ i, S.a j i * x i + S.b j)

/-- Evaluation of an EA polynomial along a separable chain. -/
def ev (S : SepChainLocal n r) (P : WilkiesDesign.E.EAPoly n r) : (Fin n → ℝ) → ℝ :=
  fun x => MvPolynomial.eval (Sum.elim x (fun j => S.psi j x)) P

/-- The symbolic derivative `∂ᵢ = ∂/∂xᵢ + ∑ⱼ a_{j i} R_j (ψ_j) ∂/∂ψ_j`. -/
def d (S : SepChainLocal n r) (i : Fin n) (Q : WilkiesDesign.E.EAPoly n r) :
    WilkiesDesign.E.EAPoly n r :=
  MvPolynomial.pderiv (Sum.inl i) Q +
    ∑ j : Fin r, MvPolynomial.C (S.a j i) * S.Rpoly j * MvPolynomial.pderiv (Sum.inr j) Q

/-- A nondegenerate zero of an `S`-system: all equations vanish and the Jacobian `(∂_j f_i)` is
invertible. -/
def Nondegen (S : SepChainLocal n r) (f : Fin n → WilkiesDesign.E.EAPoly n r)
    (x : Fin n → ℝ) : Prop :=
  (∀ i, S.ev (f i) x = 0) ∧
    (Matrix.of fun i j => S.ev (S.d j (f i)) x).det ≠ 0

end SepChainLocal

/-- **FALSE as stated — kept only for the record; use `SepKhovanskiiET` below.**  Bounding the
domain is *not* the right repair: with `n = r = 1`, `φ = Real.tan`, `R = 1 + X²`, `ℓ x = a * x` and
`f = X 0 - X (Sum.inr 0)` (i.e. `x - tan (a x)`), the bounded set `D = [-1,1]` minus the poles of
`tan (a ·)` has `≈ 2 a / π` nondegenerate zeros, unbounded in the *coefficient* `a` at fixed
degree.  The counterexample is machine-checked in the lead's design file
(`sources/wilkiesE3E9/wilkies_E3E9_gaps.lean`, `not_sepKhovanskiiLocal`). -/
def SepKhovanskiiLocal (F : ℕ) : Prop :=
  ∃ p : Polynomial ℕ, ∀ (n r : ℕ) (S : SepChainLocal n r)
      (f : Fin n → WilkiesDesign.E.EAPoly n r) (D : Set (Fin n → ℝ))
      (s : Finset (Fin n → ℝ)), n + r ≤ F →
    Bornology.IsBounded D →
    (∀ x ∈ D, ∀ j, (∑ i, S.a j i * x i + S.b j) ∈ S.dom j) →
    (↑s : Set (Fin n → ℝ)) ⊆ D →
    (∀ x ∈ s, S.Nondegen f x) →
    s.card ≤ p.eval (∑ i, WilkiesDesign.E.atomDeg (f i) + ∑ j, (S.R j).totalDegree)

/-- **The corrected separable Khovanskii bound** (the lead's design `WilE3K`, GAP 1; the eventual
home of this name is `Work.WilE3K.SepKhovanskiiET`, which will be proved from the frozen
`E2_khovanskii` in the new subproject — this copy is byte-compatible so that E3's proof can be
developed against it in the meantime).

`D` is *convex*, so every `ℓ_j '' D` is an interval inside `dom j`; since `hderiv` forces `dom j`
to miss the poles of `tan`, each `tan` chain function lives on **one branch**, which is what kills
the coefficient-uniformity counterexample above.  Only the chain types E3 uses are allowed:
`exp` (`R = X`) and `tan` (`R = 1 + X²`).  The right-hand side is the same as in
`SepKhovanskiiLocal`. -/
def SepKhovanskiiET (F : ℕ) : Prop :=
  ∃ p : Polynomial ℕ, ∀ (n r : ℕ) (S : SepChainLocal n r)
      (f : Fin n → WilkiesDesign.E.EAPoly n r) (D : Set (Fin n → ℝ))
      (s : Finset (Fin n → ℝ)), n + r ≤ F →
    (∀ j : Fin r, (S.phi j = Real.exp ∧ S.R j = MvPolynomial.X 0) ∨
      (S.phi j = Real.tan ∧ S.R j = 1 + MvPolynomial.X 0 ^ 2)) →
    Convex ℝ D →
    (∀ x ∈ D, ∀ j, (∑ i, S.a j i * x i + S.b j) ∈ S.dom j) →
    (↑s : Set (Fin n → ℝ)) ⊆ D →
    (∀ x ∈ s, S.Nondegen f x) →
    s.card ≤ p.eval (∑ i, WilkiesDesign.E.atomDeg (f i) + ∑ j, (S.R j).totalDegree)

end Work.WilE3
