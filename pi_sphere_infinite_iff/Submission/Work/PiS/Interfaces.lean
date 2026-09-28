import Mathlib
import Submission.Work.Serre.Defs
import Submission.Work.Serre.Models
import Submission.Work.StemsB.Fibrations

set_option synthInstance.maxHeartbeats 400000

/-!
# pi_sphere_infinite_iff — the lead's interface (DO NOT EDIT: every `Prop` below is a contract)

Target (Serre): for `n ≥ 1`, `π_k(Sⁿ)` is infinite iff `k = n` or (`n` even and `k = 2n - 1`).

The proof is the composition (`Work.PiS.pi_sphere_of_areas`, file `Wiring.lean`) of the area `Prop`s
below. Every area is dispatched as ONE lemma; an area may take other areas' `Prop`s as hypotheses
(the statement you were given says which), so all areas run in parallel.

Sphere-level areas (all at the fixed base point `pt n`; `BasepointHomog` moves the base point):
* `BasepointHomog`, `LowDegree`, `CircleFacts`, `DegreeInfinite` — elementary / from milnor's
  Hurewicz chapter.
* `SphereFG` — `π_{j+2}(Sⁿ)` finitely generated (`n ≥ 2`); from `SerreFGTheorem`.
* `SphereTorsion` — `π_{j+2}(Sⁿ)` torsion off `k = n` and (`n` even, `k = 2n-1`) (rational side).
* `HopfInfinite` — `π_{2n-1}(Sⁿ)` infinite for `n` even (rational side).

Engine areas (general theorems):
* `SerreFGThreeForTwo` — THE CRUX: the Serre spectral sequence of a Serre fibration over a simply
  connected base, used mod the Serre class of finitely generated groups (range form, three
  directions). Route: `REFS/NOTES_LEAD_SSS.md`.
* `EMHomologyFG` — `H_i(K(A,m);ℤ)` finitely generated for `A` f.g., `m ≥ 2` (every range model).
* `SerreFGTheorem` — simply connected + f.g. integral homology ⇒ f.g. homotopy groups.

Conventions: integral singular homology `HZ X i` is the homology of Mathlib's singular chain complex
with `ℤ` coefficients (`Work.Cohomology.singularChains ℤ`, the milnor workspace's convention);
homotopy groups are Mathlib's `HomotopyGroup.Pi` (cube model; `π₀` = path components).
-/

set_option autoImplicit false

open CategoryTheory

namespace Work.PiS

noncomputable section

/-- The unit sphere `Sⁿ ⊆ ℝⁿ⁺¹` — literally the challenge's space (and `Work.Serre.Sph n`). -/
abbrev Sph (n : ℕ) : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

/-- The base point `e₀ = (1, 0, …, 0)` of `Sⁿ`. -/
def pt (n : ℕ) : Sph n :=
  ⟨EuclideanSpace.single 0 1, by simp⟩

/-- Integral singular homology `H_i(X;ℤ)`. -/
abbrev HZ (X : Type) [TopologicalSpace X] (i : ℕ) : ModuleCat ℤ :=
  (Work.Cohomology.singularChains ℤ (TopCat.of X)).homology i

/-- `H_i(X;ℤ)` is finitely generated for every `i ≤ N`. -/
def FGUpTo (X : Type) [TopologicalSpace X] (N : ℕ) : Prop :=
  ∀ i : ℕ, i ≤ N → Module.Finite ℤ (HZ X i)

/-- `X` is path connected and simply connected (cube model: `π₀` and `π₁` at `x` are trivial). -/
def SimplyConn (X : Type) [TopologicalSpace X] (x : X) : Prop :=
  Subsingleton (HomotopyGroup.Pi 0 X x) ∧ Subsingleton (HomotopyGroup.Pi 1 X x)

/-! ## Sphere-level areas -/

/-- **Area BASEPT.** The homotopy sets of `Sⁿ` do not depend on the base point (up to a bijection). -/
def BasepointHomog : Prop :=
  ∀ (n k : ℕ) (x y : Sph n),
    Nonempty (HomotopyGroup.Pi k (Sph n) x ≃ HomotopyGroup.Pi k (Sph n) y)

/-- **Area LOW.** `π₀(Sⁿ) = *` for `n ≥ 1` and `π₁(Sⁿ) = 1` for `n ≥ 2`. -/
def LowDegree : Prop :=
  (∀ n : ℕ, 1 ≤ n → Subsingleton (HomotopyGroup.Pi 0 (Sph n) (pt n))) ∧
    (∀ n : ℕ, 2 ≤ n → Subsingleton (HomotopyGroup.Pi 1 (Sph n) (pt n)))

/-- **Area CIRCLE.** `π₁(S¹)` is infinite and `π_k(S¹) = 1` for `k ≥ 2`. -/
def CircleFacts : Prop :=
  Infinite (HomotopyGroup.Pi 1 (Sph 1) (pt 1)) ∧
    ∀ k : ℕ, 2 ≤ k → Subsingleton (HomotopyGroup.Pi k (Sph 1) (pt 1))

/-- **Area DEGREE.** `πₙ(Sⁿ)` is infinite for `n ≥ 2`. -/
def DegreeInfinite : Prop :=
  ∀ n : ℕ, 2 ≤ n → Infinite (HomotopyGroup.Pi n (Sph n) (pt n))

/-- **Area HOPF (rational side).** `π_{2n-1}(Sⁿ)` is infinite for `n ≥ 2` even. -/
def HopfInfinite : Prop :=
  ∀ n : ℕ, 2 ≤ n → Even n → ∀ k : ℕ, k + 1 = 2 * n →
    Infinite (HomotopyGroup.Pi k (Sph n) (pt n))

/-- **Area SPHEREFG.** `π_{j+2}(Sⁿ)` is finitely generated for `n ≥ 2`. -/
def SphereFG : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ j : ℕ, Group.FG (HomotopyGroup.Pi (j + 2) (Sph n) (pt n))

/-- **Area TORSION (rational side).** Off the two infinite cases, every element of
`π_{j+2}(Sⁿ)` (`n ≥ 2`) has finite order. -/
def SphereTorsion : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ j : ℕ, j + 2 ≠ n → ¬ (Even n ∧ j + 3 = 2 * n) →
    ∀ a : HomotopyGroup.Pi (j + 2) (Sph n) (pt n), ∃ m : ℕ, 0 < m ∧ a ^ m = 1

/-! ## Engine areas -/

/-- **Area SSS (the crux).** The Serre spectral sequence of a Serre fibration `p : E → B` over a
simply connected base, read modulo the Serre class of finitely generated abelian groups, in range
form. `F = p⁻¹(p e₀)` is the strict fibre (nonempty: it contains `e₀`).
1. total from base and fibre;  2. base from total and fibre;  3. fibre from base and total.
(Degree bookkeeping: `E²_{s,t} = H_s(B; H_t F)` and `E^∞` is the graded of `H_*(E)`.) -/
def SerreFGThreeForTwo : Prop :=
  ∀ (E B : Type) [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (e₀ : E),
    Work.StemsB.IsSerreFibration p → SimplyConn B (p e₀) →
      (∀ N : ℕ, FGUpTo B N → FGUpTo (Work.StemsB.fibre p (p e₀)) N → FGUpTo E N) ∧
      (∀ N : ℕ, FGUpTo E (N + 1) → FGUpTo (Work.StemsB.fibre p (p e₀)) N → FGUpTo B (N + 1)) ∧
      (∀ N : ℕ, FGUpTo B (N + 1) → FGUpTo E N → FGUpTo (Work.StemsB.fibre p (p e₀)) N)

/-- **Area EMFG.** Every range model of `K(A,m)` (`A` finitely generated, `m ≥ 2`) through degree
`N + 1` has finitely generated integral homology through degree `N`. -/
def EMHomologyFG : Prop :=
  ∀ (A : Type) [AddCommGroup A] [Module.Finite ℤ A] (m : ℕ) (hm : 2 ≤ m) (N : ℕ)
    (X : Type) [TopologicalSpace X] (x : X),
    Work.Serre.IsEMSpaceUpTo A m (by omega) (N + 1) X x → FGUpTo X N

/-- **Area FGTHM.** Serre: a simply connected space with finitely generated integral homology in
every degree has finitely generated homotopy groups. -/
def SerreFGTheorem : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (x : X), SimplyConn X x → (∀ N : ℕ, FGUpTo X N) →
    ∀ j : ℕ, Group.FG (HomotopyGroup.Pi (j + 2) X x)

end

end Work.PiS
