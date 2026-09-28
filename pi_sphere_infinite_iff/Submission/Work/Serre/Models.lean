import Submission.Work.Serre.Basic
import Submission.Work.RatHurewicz.Basic
import Submission.Work.StemsB.PiMap
import Submission.Work.RatHurewicz.RelHomotopy

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# SUBPROJECT SERRE — Postnikov models and the computations C0 … C3

`Submission/Work/Drive/SERRE_BLUEPRINT.md` §2, with C0 imported from subproject RATHUREWICZ as the
lead's brief prescribes.

| label | name | status |
|---|---|---|
| C0 | `Work.Serre.SerreC0` | **contract**: existence of models of `K(A,m)` (cell attachment — RATHUREWICZ) |
| C1 | `Work.Serre.SerreC1` | **contract**: a `K(ℤ,1)` is rationally `S¹` |
| C2 (even) | `Work.Serre.SerreC2even` | **contract**: `K(ℤ,2j)` has the rational homology of `ℂP^∞` with `\|x\| = 2j` |
| C2 (odd) | `Work.Serre.SerreC2odd` | **contract**: for `n` odd the `(n-1)`-connected cover of `Sⁿ` is rationally acyclic |
| C3 | `Work.Serre.SerreC3` | **contract**: `K(A,n)` is rationally acyclic for torsion `A` |
| — | `Work.Serre.piMapN` | **contract** (a small gap in Mathlib: `π_n` functoriality) |

**Index conventions.**  Mathlib's `HomotopyGroup (Fin m) X pt` *is* `π_m(X,pt)`, and the group
structure on it is available exactly when `0 < m`; therefore
`IsEMSpace A m hm X pt` (`hm : 0 < m`) is the statement "`X` is a model of `K(A,m)`", with `A`
matched **as a group** (`π_m(X,pt) ≃* A`) and all other homotopy groups trivial.  `SerreC2even` and
`SerreC2odd` are indexed by `j` and `n` and refer to `IsEMSpace ℤ (2j)` and `IsEMSpace ℤ n`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Topology Topology.Homotopy unitInterval

namespace Work.Serre

noncomputable section

/-! ## `K(A,m)`: the models of C0 -/

/-- **`X` is a model of `K(A,m)`**: the group `π_m(X,pt)` (Mathlib's `HomotopyGroup (Fin m)`) is
isomorphic to `A` **as a group**, and every other homotopy group is trivial.  The proof `hm : 0 < m`
is what supplies Mathlib's group structure on `HomotopyGroup (Fin m)`.  The condition at `i = 0`
says that `X` is (path) connected.

A *group* isomorphism is essential: with a bare type equivalence the torus would be a "model of
`K(ℤ,1)`" (`π₁(T²) = ℤ² ≃ ℤ` as types), which is not rationally `S¹`. -/
def IsEMSpace (A : Type) [AddCommGroup A] (m : ℕ) (hm : 0 < m) (X : Type) [TopologicalSpace X]
    (pt : X) : Prop :=
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  Nonempty (HomotopyGroup (Fin m) X pt ≃* Multiplicative A) ∧
    ∀ i : ℕ, i ≠ m → Subsingleton (HomotopyGroup (Fin i) X pt)

/-- The defining vanishing of a `K(A,m)`. -/
theorem IsEMSpace.subsingleton {A : Type} [AddCommGroup A] {m : ℕ} {hm : 0 < m} {X : Type}
    [TopologicalSpace X] {pt : X} (h : IsEMSpace A m hm X pt) {i : ℕ} (hi : i ≠ m) :
    Subsingleton (HomotopyGroup (Fin i) X pt) :=
  h.2 i hi

/-- **C0 (blueprint §2 and its ADDENDUM 1 (E): finite truncations).**  For every abelian group `A`
and every `m ≥ 1` there is a space with the homotopy groups of `K(A,m)`: build
`Y = Y_0 ⊆ … ⊆ Y_N` by attaching one `(i+2)`-disc per element of `π_{i+1}(Y_i)`, so that
`π_{≤m}` is unchanged and `π_j(Y_N) = 0` for `m < j ≤ N`.  Only finitely many cells are needed
because every use is in a bounded range of degrees. -/
def SerreC0 : Prop :=
  ∀ (A : Type) [AddCommGroup A] (m : ℕ) (hm : 1 ≤ m),
    ∃ (X : Type) (_ : TopologicalSpace X) (pt : X), IsEMSpace A m (by omega : 0 < m) X pt

/-- **A model of `K(A,m)` in a range of degrees** (the range form of `IsEMSpace`, ADDENDUM 1 (E)):
`π_m(X,pt) ≃* A`, `π_i(X,pt)` trivial for `i < m`, and `π_i(X,pt)` trivial for `m < i ≤ N`.  Every
use of a `K(A,m)` in this project is in a bounded range of degrees, and the finite truncations of
the Postnikov tower (`Work.Serre.serrePostnikovTower`) deliver exactly this. -/
def IsEMSpaceUpTo (A : Type) [AddCommGroup A] (m : ℕ) (hm : 0 < m) (N : ℕ) (X : Type)
    [TopologicalSpace X] (pt : X) : Prop :=
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  Nonempty (HomotopyGroup (Fin m) X pt ≃* Multiplicative A) ∧
    ∀ i : ℕ, i ≠ m → (i < m ∨ i ≤ N) → Subsingleton (HomotopyGroup (Fin i) X pt)

/-- **C0 in range form.**  For `1 ≤ m ≤ N` every abelian group `A` has a `K(A,m)` model up to
degree `N`.  (For `A = ℤ` this is the Postnikov truncation of `Sᵐ`; in general one first builds a
Moore space `M(A,m)` by attaching cells — RATHUREWICZ's `AttachCells` — and then truncates.) -/
def SerreC0Range : Prop :=
  ∀ (A : Type) [AddCommGroup A] (m N : ℕ) (hm : 1 ≤ m) (hmN : m ≤ N),
    ∃ (X : Type) (_ : TopologicalSpace X) (pt : X), IsEMSpaceUpTo A m (by omega : 0 < m) N X pt

/-! ## C1 — a `K(ℤ,1)` is rationally `S¹` -/

/-- **C1 (blueprint §2).**  Every model of `K(ℤ,1)` is rationally the circle: there is a continuous
map `S¹ → X` inducing an isomorphism on rational homology.

(Proof, from the blueprint: `S¹` is aspherical via the covering `ℝ → S¹`, so `S¹ → X` is a
`π`-isomorphism; E0 plus E3(a) applied to its homotopy fibre promote this to a rational homology
isomorphism.) -/
def SerreC1 : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (pt : X), IsEMSpace ℤ 1 (by norm_num : 0 < 1) X pt →
    ∃ f : C(Sph 1, X), IsRatHomologyIso f

/-! ## The induced map on `π_n` -/

/-- **The map `π_n(X,x) → π_n(Y,f x)` induced by a continuous map**, in the exact degree `n` (the
workspace's `Work.StemsB.πmap` is stated for the shifted index `Fin (n+1)`).  Absent from Mathlib;
needed to *state* C2 (a map `Sⁿ → K(ℤ,n)` inducing a bijection on `π_n`). -/
def piMapN {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ) (x : X) :
    HomotopyGroup (Fin n) X x → HomotopyGroup (Fin n) Y (f x) :=
  Quotient.map (Work.StemsB.genLoopMap f n)
    (fun a b h => by
      change (Work.StemsB.genLoopMap f n a).1.HomotopicRel (Work.StemsB.genLoopMap f n b).1
        (Cube.boundary (Fin n))
      change a.1.HomotopicRel b.1 (Cube.boundary (Fin n)) at h
      exact h.comp_continuousMap f)

@[simp]
theorem piMapN_apply_mk {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    (n : ℕ) (x : X) (γ : Ω^ (Fin n) X x) :
    piMapN f n x (Quotient.mk _ γ) = Quotient.mk _ (Work.StemsB.genLoopMap f n γ) := rfl

/-- `piMapN` of the identity is the identity. -/
theorem piMapN_id {X : Type*} [TopologicalSpace X] (n : ℕ) (x : X)
    (a : HomotopyGroup (Fin n) X x) : piMapN (ContinuousMap.id X) n x a = a := by
  induction a using Quotient.inductionOn with
  | h p => rfl

/-- `piMapN` is functorial. -/
theorem piMapN_comp {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : C(X, Y)) (g : C(Y, Z)) (n : ℕ) (x : X)
    (a : HomotopyGroup (Fin n) X x) :
    piMapN (g.comp f) n x a = piMapN g n (f x) (piMapN f n x a) := by
  induction a using Quotient.inductionOn with
  | h p => rfl

/-- **C3 for FINITE groups** (ADDENDUM 3 (A): this is the only case needed — an arbitrary torsion
`π_k` is reduced to the finitely generated (hence, after the compactness argument on RATHUREWICZ's
side, to the finite) case).  If `A` is a *finite* abelian group then every model of `K(A,n)`,
`n ≥ 1`, is rationally acyclic.

(Proof: the base case is the transfer for the finite free quotient `S^{2N+1} → L = S^{2N+1}/μ_n`,
`τ(σ) =` the sum of the `n` lifts of `σ`, with `p_* ∘ τ = n · id`; since `n` is invertible in `ℚ`,
`H_i(L;ℚ)` embeds into `H_i(S^{2N+1};ℚ) = 0` for `0 < i ≤ 2N`.  Then the path–loop fibration and
the cell-step engine propagate it upwards.) -/
def SerreC3Finite : Prop :=
  ∀ (A : Type) [AddCommGroup A] [Fintype A] (n : ℕ) (hn : 1 ≤ n)
    (X : Type) [TopologicalSpace X] (pt : X),
      IsEMSpace A n (by omega : 0 < n) X pt → RatAcyclic X

/-! ## The Postnikov tower (ADDENDUM 2, K6 / C0) -/

/-- **The Postnikov tower in a range** (blueprint ADDENDUM 2, K6 / C0): for `m ≤ N` and a space
`Y` there is `P` and a map `g : Y → P` which is an isomorphism on `π_i` for `i ≤ m` and has
`π_i(P) = 0` for `m < i ≤ N`.  Built by attaching cells to kill `π_{m+1}, …, π_N` (K1/C0,
RATHUREWICZ's `AttachCells`); the tower is **proved** in `serrePostnikovTower.lean`
(`Work.Serre.serrePostnikovTower`). -/
def SerrePostnikov : Prop :=
  ∀ (m N : ℕ) (Y : Type) [TopologicalSpace Y] (y₀ : Y), m ≤ N →
    ∃ (P : Type) (_ : TopologicalSpace P) (g : C(Y, P)),
      (∀ i : ℕ, i ≤ m → Function.Bijective (piMapN g i y₀)) ∧
        (∀ i : ℕ, m < i → i ≤ N → ∀ p : P, Subsingleton (HomotopyGroup (Fin i) P p))

/-! ## C2 — the even/odd induction -/

/-- **C2, even step (blueprint §2).**  A model of `K(ℤ,2j)` (`j ≥ 1`) has the rational homology of
`ℂP^∞` rescaled by `2j`: `H_{2jk}(X;ℚ) ≅ ℚ` for every `k`, and `H_d(X;ℚ) = 0` when `2j ∤ d`.

(The blueprint's proof: `ΩL_{2j} ≃_ℚ L_{2j-1}` is a rational homology sphere of dimension `2j-1`,
so E3(b) for the path–loop fibration gives the periodicity `⌣e : H^n ≅ H^{n+2j}`, i.e.
`H^*(L_{2j};ℚ) = ℚ[x]` with `|x| = 2j`.) -/
def SerreC2even : Prop :=
  ∀ (j : ℕ) (hj : 1 ≤ j) (X : Type) [TopologicalSpace X] (pt : X),
    IsEMSpace ℤ (2 * j) (by omega : 0 < 2 * j) X pt →
    (∀ k : ℕ, Nonempty (ratH (TopCat.of X) (2 * j * k) ≅ ModuleCat.of ℚ ℚ)) ∧
      (∀ d : ℕ, (∀ k : ℕ, d ≠ 2 * j * k) → IsZero (ratH (TopCat.of X) d))

/-- **C2, odd step (blueprint §2).**  For `n` odd, let `X` be a model of `K(ℤ,n)` and `f : Sⁿ → X`
a map inducing a bijection on `π_n`.  Then the homotopy fibre of `f` — the `(n-1)`-connected cover
`Eₙ` of `Sⁿ` — is rationally acyclic.

(Proof, from the blueprint: `Eₙ` is `n`-connected with `π_i(Eₙ) ≅ π_i(Sⁿ)` for `i > n`; the Wang
sequence of the fibration `Eₙ → Sⁿ → Lₙ` (E4) with the derivation property shows
`H̃^*(Eₙ;ℚ) = 0`.) -/
def SerreC2odd : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), Odd n →
    ∀ (X : Type) [TopologicalSpace X] (pt : X), IsEMSpace ℤ n (by omega : 0 < n) X pt →
      ∀ (s₀ : Sph n) (f : C(Sph n, X)),
        Function.Bijective (piMapN f n s₀) → RatAcyclic (Work.RatHurewicz.homotopyFibre f s₀)

/-! ## C3 — `K(A,m)` for torsion `A` -/

/-- **C3 (blueprint §2).**  If `A` is a torsion abelian group then every model of `K(A,n)`, `n ≥ 1`,
is rationally acyclic.

(Proof, from the blueprint: for `A` finite cyclic, `K(A,1) = S^∞/(ℤ/r)` and the transfer of the
finite covering shows `H̃_*(K(A,1);ℚ) = 0`; products and the `m ≥ 2` induction with the path–loop
fibration and C0/E3(a) finish.  The `A` met by the applications is finitely generated.) -/
def SerreC3 : Prop :=
  ∀ (A : Type) [AddCommGroup A], Work.RatHurewicz.IsTorsionGroupAdd A →
    ∀ (n : ℕ) (hn : 1 ≤ n) (X : Type) [TopologicalSpace X] (pt : X),
      IsEMSpace A n (by omega : 0 < n) X pt → RatAcyclic X

end

end Work.Serre
