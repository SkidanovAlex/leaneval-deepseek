import Submission.Work.PTCert.Interfaces

/-!
# PTCert — linear-algebra / averaging principles for the fully symmetric certificate

Definitions and `Prop`s only.  See `NOTES_LEAD_certificate.md` (workspace root) for the design:
the certificate is a `Σ`-average `P` of a row-supported matrix `U` on the ball `B₂`; `P ⪰ 0` is
certified by a two-level sign-character Fourier decomposition (`TwistedFourierCriterion`, used for
the sign flips `N = (ℤ/2)^5` and then for a Klein four-group inside each character stabiliser).
-/

open OnPropertyT Submission.RouteB
open scoped BigOperators

set_option autoImplicit false

namespace Submission.PTCert

/-- Gram form of a real matrix over a family of group elements:
`Λ_f(U) = Σ_{i,j} U i j • of ((f i)⁻¹ * f j)`. -/
noncomputable def gramForm {G : Type} [Group G] {ι : Type} [Fintype ι] (f : ι → G)
    (U : Matrix ι ι ℝ) : MonoidAlgebra ℝ G :=
  ∑ i, ∑ j, U i j • MonoidAlgebra.of ℝ G ((f i)⁻¹ * f j)

/-- Sign character of `(ℤ/2)^m` attached to `S`. -/
def chiS {m : ℕ} (S : Finset (Fin m)) (a : Fin m → ZMod 2) : ℝ :=
  ∏ i ∈ S, (if a i = 0 then (1 : ℝ) else -1)

/-- **(Q1) Gram forms of PSD matrices are sums of hermitian squares.** -/
def GramSOS : Prop :=
  ∀ (G : Type) [Group G] [DecidableEq G] {ι : Type} [Fintype ι] (f : ι → G) (U : Matrix ι ι ℝ),
    U.PosSemidef → IsSOS (gramForm f U)

/-- **(Q2) Averaging a Gram matrix over a group acting compatibly on the index family.**
If `Sg` acts on the indices by `act`, compatibly with conjugation on the family, then the
`Sg`-averaged matrix has (up to `|Sg|`) the same conjugation average of its Gram form. -/
def AvgGram : Prop :=
  ∀ (G : Type) [Group G] [DecidableEq G] (Sg : Finset G), IsFinSubgroup Sg →
    ∀ {ι : Type} [Fintype ι] (f : ι → G) (act : G → ι → ι),
      (∀ σ ∈ Sg, Function.Bijective (act σ)) →
      (∀ σ ∈ Sg, ∀ i, f (act σ i) = σ * f i * σ⁻¹) →
      ∀ U : Matrix ι ι ℝ,
        conjAvg Sg (gramForm f (Matrix.of fun i j => ∑ σ ∈ Sg, U (act σ i) (act σ j)))
          = (Sg.card : ℝ) • conjAvg Sg (gramForm f U)

/-- **(Q3) Twisted Fourier criterion for an elementary abelian 2-group.**
`(ℤ/2)^m` acts on a finite index type by *signed* permutations
`ρ(a) e_x = sgn a x • e_{act a x}` (a genuine representation: the cocycle identity), `M` is a
symmetric matrix commuting with this action, and `rep`/`nu` pick an orbit representative and a
group element carrying it to `x`.  If for every sign character `χ_S` the matrix
`W_S(x̄, ȳ) = Σ_a χ_S(a) · sgn a ȳ · M x̄ (act a ȳ)` on the representatives is PSD, then `M ⪰ 0`.
(Proof: the projectors `Π_S = 2^{-m} Σ_a χ_S(a) ρ(a)` are orthogonal, commute with `M` and sum
to `1`; `vᵀ M v = Σ_S (Π_S v)ᵀ M (Π_S v)` and `Π_S v` is a combination of `Π_S e_ȳ`, whose Gram
matrix against `M` is `2^{-m} W_S`.) -/
def TwistedFourierCriterion : Prop :=
  ∀ (m : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (act : (Fin m → ZMod 2) → ι → ι) (sgn : (Fin m → ZMod 2) → ι → ℝ),
    (∀ a b x, act (a + b) x = act a (act b x)) → (∀ x, act 0 x = x) →
    (∀ a b x, sgn (a + b) x = sgn a (act b x) * sgn b x) → (∀ a x, sgn a x = 1 ∨ sgn a x = -1) →
    ∀ (M : Matrix ι ι ℝ), M.transpose = M →
      (∀ a x y, sgn a x * sgn a y * M (act a x) (act a y) = M x y) →
      ∀ (rep : ι → ι) (nu : ι → (Fin m → ZMod 2)),
        (∀ x, act (nu x) (rep x) = x) → (∀ x, rep (rep x) = rep x) → (∀ a x, rep (act a x) = rep x) →
        (∀ S : Finset (Fin m), (Matrix.of fun (x y : {x // rep x = x}) =>
            ∑ a, chiS S a * sgn a y.1 * M x.1 (act a y.1)).PosSemidef) →
        M.PosSemidef

end Submission.PTCert
