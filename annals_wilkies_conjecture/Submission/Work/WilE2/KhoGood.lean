/-
  Work.WilE2 — area E2.  The hypothesis bundle for the proper case of the elimination.

  The elimination step replaces a system `F` with a chain of `s+1` functions by the *lifted*
  system `G = liftSystem S F : ℝⁿ⁺¹ → ℝⁿ` (the last chain function becoming a free coordinate)
  together with the graph function `g = rolleg S`, whose zero set `N` carries the roots.  The
  counting then runs on the level set `{G = y}` for a value `y` which must satisfy four
  genericity properties:

  * `KhoSubmersion` — `y` is a regular value of `G`, so that `{G = y}` is a smooth compact
    `1`-manifold (this is the *only* property for which the development currently has no proof:
    it is Sard's theorem for the rectangular map `G`, isolated as `regular_values_dense`);
  * `KhoRegValue` — `y` is a regular value of the old system map, which by
    `nondegen_iff_lift` makes every crossing of `N` by the level curve non-degenerate;
  * `KhoSliceNull` — above `y`, the critical values of the Rolle determinant `ψ` form a null set,
    which supplies a level `δ` of `ψ|_C` that is regular (`delta_generic`);
  * the last conjunct — the inverse function theorem at the lifted roots, which moves the
    crossings onto `{G = y}` (`ift_perturbation`).

  `KhoGood S F T y` is the conjunction; `kho_good_exists` produces such a `y` (with the Sard
  input as an explicit hypothesis), and `kho_proper` consumes it.
-/
import Mathlib
import Submission.Work.WilE2.KhoCount
import Submission.Work.WilE2.RolleDetAnalytic
import Submission.Work.WilE2.KhovB

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.WilE2

open Classical
open WilkiesDesign WilkiesDesign.E WilkiesConjecture

variable {n s : ℕ}

/-- `y` is a regular value of the lifted system: the level set `{G = y}` is a smooth manifold. -/
def KhoSubmersion (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1)) (y : Fin n → ℝ) : Prop :=
  ∀ z, liftSystem S F z = y →
    LinearIndependent ℝ (fun a => fderiv ℝ (fun w => liftSystem S F w a) z)

/-- `y` is a regular value of the old system: every root over `y` is non-degenerate. -/
def KhoRegValue (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1)) (y : Fin n → ℝ) : Prop :=
  ∀ x, (fun i => S.ev (F i) x) = y →
    (Matrix.of fun i j => S.ev (S.d j (F i)) x).det ≠ 0

/-- The Rolle determinant as a function of the lifted variable. -/
def rolleDetFun (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1)) :
    (Fin (n + 1) → ℝ) → ℝ :=
  fun z => (S.liftChain).ev (S.rolleDet F) z

/-- The lifted system together with the Rolle determinant, as a map `ℝⁿ⁺¹ → ℝⁿ⁺¹`. -/
def rolleMap (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1)) :
    (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) :=
  fun z => Fin.snoc (liftSystem S F z) (rolleDetFun S F z)

/-- The lifted system together with the graph function, as a map `ℝⁿ⁺¹ → ℝⁿ⁺¹`. -/
def graphMap (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1)) :
    (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) :=
  fun z => Fin.snoc (liftSystem S F z) (rolleg S z)

/-- Above `y`, the critical values of the Rolle determinant form a null set, so that a regular
level `δ` of `ψ|_C` can be chosen below any prescribed bound. -/
def KhoSliceNull (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1)) (y : Fin n → ℝ) : Prop :=
  MeasureTheory.volume {t : ℝ | Fin.snoc y t ∈
      rolleMap S F '' {z | (fderiv ℝ (rolleMap S F) z).det = 0}} = 0

/-- The inverse-function-theorem data at the lifted roots: for every target `y'` close to `0`
there are as many solutions of `(G, g) = (y', 0)` as there are elements of `T`. -/
def KhoIft (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1)) (T : Finset (Fin n → ℝ)) :
    Prop :=
  ∃ ρ : ℝ, 0 < ρ ∧ ∀ y' : Fin n → ℝ, dist y' 0 < ρ →
    ∃ t : Finset (Fin (n + 1) → ℝ), t.card = T.card ∧
      ∀ z ∈ t, graphMap S F z = Fin.snoc y' 0

/-- The genericity bundle of the proper case: all four properties above, for one common value
`y` sitting inside the radius supplied by `KhoIft`. -/
def KhoGood (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1)) (T : Finset (Fin n → ℝ))
    (y : Fin n → ℝ) : Prop :=
  KhoSubmersion S F y ∧ KhoRegValue S F y ∧ KhoSliceNull S F y ∧
    (∃ ρ : ℝ, 0 < ρ ∧ dist y 0 < ρ ∧ ∀ y' : Fin n → ℝ, dist y' 0 < ρ →
      ∃ t : Finset (Fin (n + 1) → ℝ), t.card = T.card ∧
        ∀ z ∈ t, graphMap S F z = Fin.snoc y' 0)

@[simp] theorem rolleMap_apply_castSucc (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1))
    (z : Fin (n + 1) → ℝ) (i : Fin n) :
    rolleMap S F z (Fin.castSucc i) = liftSystem S F z i :=
  Fin.snoc_castSucc _ _ i

@[simp] theorem rolleMap_apply_last (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1))
    (z : Fin (n + 1) → ℝ) :
    rolleMap S F z (Fin.last n) = rolleDetFun S F z :=
  Fin.snoc_last _ _

@[simp] theorem graphMap_apply_castSucc (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1))
    (z : Fin (n + 1) → ℝ) (i : Fin n) :
    graphMap S F z (Fin.castSucc i) = liftSystem S F z i :=
  Fin.snoc_castSucc _ _ i

@[simp] theorem graphMap_apply_last (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1))
    (z : Fin (n + 1) → ℝ) :
    graphMap S F z (Fin.last n) = rolleg S z :=
  Fin.snoc_last _ _

end Work.WilE2
