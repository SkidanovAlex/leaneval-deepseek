import Submission.Work.PTCert.Math
import Submission.Work.PTCert.OrderUnit

/-!
# PTCert — the generic lemmas of the certificate chain (design P, "row blocks + transport")

See `NOTES_LEAD_checker.md` (workspace root) for how these compose.  Everything here is generic
(finite group `Sg` acting on a finite index family by conjugation); no data.
-/

open OnPropertyT Submission.RouteB
open scoped BigOperators

set_option autoImplicit false

namespace Submission.PTCert

/-- The `Sg`-average of a matrix along an action on the indices. -/
noncomputable def avgMat {G : Type} (Sg : Finset G) {ι : Type} (act : G → ι → ι)
    (U : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => ∑ g ∈ Sg, U (act g i) (act g j)

/-- A conjugation-compatible action of `Sg` on an injective family. -/
def ConjAction {G : Type} [Group G] (Sg : Finset G) {ι : Type} (f : ι → G) (act : G → ι → ι) : Prop :=
  Function.Injective f ∧ ∀ g ∈ Sg, ∀ i, f (act g i) = g * f i * g⁻¹

/-- **(C1) Invariance of an average.** -/
def AvgMatInvariant : Prop :=
  ∀ (G : Type) [Group G] (Sg : Finset G), IsFinSubgroup Sg →
    ∀ {ι : Type} (f : ι → G) (act : G → ι → ι), ConjAction Sg f act →
      ∀ (U : Matrix ι ι ℝ) (h : G), h ∈ Sg → ∀ i j,
        avgMat Sg act U (act h i) (act h j) = avgMat Sg act U i j

/-- **(C2) Row formula.**  If `U` is supported on rows lying in distinct orbits, and each row
`x` of `U` is invariant under the stabiliser of `x`, then on a row the average is
`|Stab x| • U x z`. -/
def RowFormula : Prop :=
  ∀ (G : Type) [Group G] [DecidableEq G] (Sg : Finset G), IsFinSubgroup Sg →
    ∀ {ι : Type} [DecidableEq ι] (f : ι → G) (act : G → ι → ι), ConjAction Sg f act →
      ∀ (rows : Finset ι) (U : Matrix ι ι ℝ),
        (∀ i j, i ∉ rows → U i j = 0) →
        (∀ x ∈ rows, ∀ g ∈ Sg, act g x ∈ rows → act g x = x) →
        (∀ x ∈ rows, ∀ g ∈ Sg, act g x = x → ∀ z, U x (act g z) = U x z) →
        ∀ x ∈ rows, ∀ z,
          avgMat Sg act U x z = ((Sg.filter (fun g => act g x = x)).card : ℝ) * U x z

/-- **(C3) PSD is invariant under signed permutation similarity.** -/
def PSDSignedPerm : Prop :=
  ∀ {ι κ : Type} [Fintype ι] [Fintype κ] (M : Matrix ι ι ℝ) (τ : κ ≃ ι) (s : κ → ℝ),
    (∀ x, s x = 1 ∨ s x = -1) → M.PosSemidef →
      (Matrix.of fun x y => s x * s y * M (τ x) (τ y)).PosSemidef

/-- **(C4) PSD from a PSD principal block and zero elsewhere.** -/
def PSDOfBlock : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (S : Finset ι),
    (∀ x y, x ∉ S → M x y = 0) → (∀ x y, y ∉ S → M x y = 0) →
    (Matrix.of fun (x y : S) => M x.1 y.1).PosSemidef → M.PosSemidef

/-- **(C5) Scaled LDL principle** (handles an exact null vector): with a positive diagonal
scaling `w`, if `diag(w) · M · diag(w) = L Lᵀ + R` and `R` is symmetric and diagonally dominant
(nonnegative diagonal), then `M ⪰ 0`. -/
def LdlScaledPrinciple : Prop :=
  ∀ {n : ℕ} (M L R : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ),
    (∀ i, 0 < w i) → R.transpose = R →
    (∀ i, ∑ j ∈ Finset.univ.erase i, |R i j| ≤ R i i) →
    (Matrix.of fun i j => w i * M i j * w j) = L * L.transpose + R → M.PosSemidef

/-- **(C6) Residual absorption.**  For a finite family of group elements `g t` given as
products of at most `4` letters, with rational weights `r t` summing to zero, the element
`c • Δ + Σ_t (r t / 2) • (of (g t) + of (g t)⁻¹)` is a sum of hermitian squares as soon as
`16 · Σ_t |r t| ≤ c`. -/
def ResidualAbsorption (r : ℕ) : Prop :=
  ∀ {τ : Type} (I : Finset τ) (ks : τ → List ℕ) (w : τ → ℝ) (c : ℝ),
    (∀ t ∈ I, (ks t).length ≤ 4 ∧ ∀ k ∈ ks t, k < NB1 r) →
    ∑ t ∈ I, w t = 0 → 16 * ∑ t ∈ I, |w t| ≤ c →
    IsSOS (c • Edge.deltaSub r r + ∑ t ∈ I, (w t / 2) •
      (MonoidAlgebra.of ℝ _ (lprod r (ks t)) + MonoidAlgebra.of ℝ _ (lprod r (ks t))⁻¹))

end Submission.PTCert
