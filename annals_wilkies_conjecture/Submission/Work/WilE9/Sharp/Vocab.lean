/-
  WilE9 / Sharp — vocabulary for the extended-system construction.

  `exTset E L` is the projection to the first `n+1` coordinates of the extended semi-Pfaffian
  set of a stratum `E` and an order `L`: the `ψ`-image of (a piece of) the graph of `∂_L f`.
  `psiInvV` is the coordinatewise inverse of `ψ` (legitimate on the open cube, where it is the
  actual inverse), and `ocube` is the open cube.
-/
import Mathlib
import Submission.Work.WilE9.Sharp.ExtSystem

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Work.WilE9.Sharp
open WilkiesDesign WilkiesDesign.E

/-- The coordinatewise inverse of `psi` (the honest inverse on the open cube). -/
def psiInvV {n : ℕ} (y : Fin n → ℝ) : Fin n → ℝ := fun i => psiInv (y i)

/-- The open cube `(-1,1)^n`, i.e. the range of `psiV` and the set on which `psiInvV` inverts it. -/
def ocube (n : ℕ) : Set (Fin n → ℝ) := {x | ∀ i, |x i| < 1}

-- `stratInj` and `stratProj` are declared in `Submission/Work/WilE9/Sharp/EffInput.lean` (they
-- occur in the statement of the geometric input `EffStrat`, which everything here imports).

/-- The projection of the extended ambient to the `(y, σ)` coordinates. -/
def exOut {n m : ℕ} (z : Fin (Next n m) → ℝ) : Fin (n + 1) → ℝ := projFirst (n + 1) (n + m + 3) z

/-- **The `ψ`-image of the `L`-th derivative graph over a stratum**: the projection of the
extended semi-Pfaffian set of `E` and `L` to the first `n+1` coordinates. -/
def exTset {n m : ℕ} (E : EffStratum n m) (L : List (Fin n)) : Set (Fin (n + 1) → ℝ) :=
  projFirst (n + 1) (n + m + 3) '' (exSemiPf n m E L).set

/-- The extended set of a list `L` is a subset of the cube, and hence of the `ψ`-image of the
graph over the open cube. -/
theorem exTset_subset_cube {n m : ℕ} (E : EffStratum n m) (L : List (Fin n)) :
    exTset E L ⊆ cubeC (n + 1) := by
  rintro z' ⟨z, hz, rfl⟩ i
  exact hz.1 (Fin.castAdd (n + m + 3) i)

/-! ## Transporting a `SemiPf` set along an equality of ambient dimensions -/

/-- Reindex a `SemiPf` set along an equality `a = b` of ambient dimensions: the chain is
reindexed by `Fin.cast h` and every atom by `MvPolynomial.rename (Sum.map (Fin.cast h) id)`.
A `*`-piece has ambient `(n+1) + m` while `EffStratum n m` has ambient `n + (1+m)`; the two are
equal (`addSplit`) but not definitionally, so this is the transport between them. -/
def SemiPf.castFin {a b : ℕ} (h : a = b) (X : WilkiesDesign.E.SemiPf a) :
    WilkiesDesign.E.SemiPf b :=
  ⟨X.r, ⟨fun j i => X.c.a j (Fin.cast h.symm i), X.c.b⟩,
    X.basics.map fun B =>
      ⟨B.eqs.map (MvPolynomial.rename (Sum.map (Fin.cast h) id)),
        B.pos.map (MvPolynomial.rename (Sum.map (Fin.cast h) id))⟩⟩

end Work.WilE9.Sharp
