/-
  Subproject WilE9G — vocabulary for G4, the construction of the Lagrange stratum.

  The construction takes an ambient `Good` stratum `S` (of `AmbStratum (n + (1+m))`), an
  effectively smooth weight `Φ` which is strictly positive on `S.X.set` (in the application,
  the product of the `pos` polynomials of one basic of `X`) and a direction
  `c : Fin (1+m) → ℝ`, and produces an `EffStratum n (m + S.j + 1)` whose unknowns are the
  `(1+m)` fibre coordinates of `S`, the `S.j` multipliers `μ` and the homogeneous multiplier
  `μ₀`, subject to

  * the `S.j` equations `h_a` of `S`,
  * the homogeneous Lagrange equations `μ₀ (∂_l Φ + Φ c_l) = ∑_a μ_a ∂_l h_a`, `l = 1..1+m`,
  * the normalisation `∑_a μ_a² + μ₀² = 1`,
  * the open condition `det ≠ 0` of the `(1+m')` square block of the Jacobian
    (`1+m' = (1+m) + S.j + 1`).

  The definitions here fix the *conventions* (coordinate order, the multiplicative form of the
  Lagrange equations, the sign-free determinant condition), so that the construction lemma
  `Work.WilE9G.Lagrange.exists_lagrange_stratum` can be stated without ambiguity.
-/
import Submission.Work.WilE9G.Amb
import Submission.Work.WilE9G.Jac

set_option autoImplicit false
noncomputable section
open Classical Topology Filter MeasureTheory
namespace Work.WilE9G
open WilkiesDesign WilkiesDesign.E Work.WilE9.Sharp

/-! ## The point of the Lagrange stratum -/

/-- The point of the Lagrange stratum with base-and-fibre part `z : Fin (n + (1+m)) → ℝ` and
multiplier part `(μ, μ₀)`: the coordinate order is
`(x_0,…,x_{n-1}, (y,t)_0,…,(y,t)_m, μ_0,…,μ_{j-1}, μ₀)`. -/
def lagPoint {n m j : ℕ} (z : Fin (n + (1 + m)) → ℝ) (μ : Fin j → ℝ) (μ₀ : ℝ) :
    Fin (n + (1 + (m + j + 1))) → ℝ :=
  fun i => Fin.append z (Fin.append μ (fun _ : Fin 1 => μ₀))
    (finCongr (show n + (1 + (m + j + 1)) = n + (1 + m) + (j + 1) by omega) i)

/-! ## The determinant block of an `EffStratum` -/

/-- The square block of the symbolic Jacobian of an `EffStratum` that `EffStratum.Good` requires
to be invertible: the derivatives of the `1+m'` equations in the `1+m'` fibre coordinates. -/
def effBlock {n m' : ℕ} (E : EffStratum n m') (w : Fin (n + (1 + m')) → ℝ) :
    Matrix (Fin (1 + m')) (Fin (1 + m')) ℝ :=
  Matrix.of fun a l => eaEval E.X.c (eaD E.X.c (Fin.natAdd n l) (E.h a)) w

theorem effBlock_det_eq {n m' : ℕ} (E : EffStratum n m') (w : Fin (n + (1 + m')) → ℝ) :
    (effBlock E w).det
      = (Matrix.of fun (a : Fin (1 + m')) (l : Fin (1 + m')) =>
          eaEval E.X.c (eaD E.X.c (Fin.natAdd n l) (E.h a)) w).det := rfl

/-! ## The Lagrange system of the construction -/

/-- The (homogeneous) Lagrange equations of the construction at `z` with multipliers
`(μ, μ₀)`: for every fibre direction `l`, the `l`-th partial of `log Φ + c·(y,t)` (multiplied by
`μ₀`) is the corresponding combination of the partials of the equations of `S`. -/
def LagEq {n m : ℕ} (S : AmbStratum (n + (1 + m))) (Φ : EAPoly (n + (1 + m)) S.X.r)
    (c : Fin (1 + m) → ℝ) (z : Fin (n + (1 + m)) → ℝ) (μ : Fin S.j → ℝ) (μ₀ : ℝ) : Prop :=
  ∀ l : Fin (1 + m),
    μ₀ * (eaEval S.X.c (eaD S.X.c (Fin.natAdd n l) Φ) z + eaEval S.X.c Φ z * c l)
      = ∑ a, μ a * eaEval S.X.c (eaD S.X.c (Fin.natAdd n l) (S.h a)) z

/-- The Jacobian of the Lagrange system of the construction, as a square matrix.

**Index conventions** (both index types are `Fin ((1+m) + (S.j + 1))`):
the rows are, in order, the `1+m` Lagrange equations `L_l`, then the `S.j` equations `h_a`, then
the normalisation `N`; the columns are, in order, the `1+m` fibre directions `(y,t)_{l'}` (in the
coordinates `Fin.natAdd n l'`), then the `S.j` multipliers `μ_a`, then `μ₀`.  Concretely

* row `Fin.castAdd (S.j+1) l` (an `L_l` row): column `Fin.castAdd (S.j+1) l'` is
  `μ₀ (∂_{l'}∂_l Φ + (∂_{l'}Φ) c_l) - ∑_a μ_a ∂_{l'}∂_l h_a`, column
  `Fin.natAdd (1+m) (Fin.castAdd 1 a)` is `- ∂_l h_a`, column `Fin.natAdd (1+m) (Fin.last S.j)` is
  `∂_l Φ + Φ c_l`;
* row `Fin.natAdd (1+m) (Fin.castAdd 1 a)` (an `h_a` row): column `Fin.castAdd (S.j+1) l'` is
  `∂_{l'} h_a`, and both the `μ_a` and the `μ₀` columns are `0`;
* row `Fin.natAdd (1+m) (Fin.last S.j)` (the `N` row): column `Fin.castAdd (S.j+1) l'` is `0`,
  column `Fin.natAdd (1+m) (Fin.castAdd 1 a)` is `2 μ_a`, column `Fin.natAdd (1+m) (Fin.last S.j)`
  is `2 μ₀`.

So `det (lagJac …) ≠ 0` is exactly the nondegeneracy (Morse) condition on the Lagrange system,
which is the condition the maximiser of the construction satisfies for almost every `x`.  This is the intrinsic nondegeneracy matrix of the construction: its nonvanishing at a Lagrange point is the Morse condition that FIX-5 has to arrange for almost every `x`. -/
def lagJac {n m : ℕ} (S : AmbStratum (n + (1 + m))) (Phi : EAPoly (n + (1 + m)) S.X.r)
    (c : Fin (1 + m) → ℝ) (z : Fin (n + (1 + m)) → ℝ) (mu : Fin S.j → ℝ) (mu0 : ℝ) :
    Matrix (Fin ((1 + m) + (S.j + 1))) (Fin ((1 + m) + (S.j + 1))) ℝ :=
  Matrix.of fun a l =>
    Fin.addCases
      (fun l' : Fin (1 + m) =>
        Fin.addCases
          (fun l0 : Fin (1 + m) =>
            mu0 * (eaEval S.X.c (eaD S.X.c (Fin.natAdd n l') (eaD S.X.c (Fin.natAdd n l0) Phi)) z
                  + eaEval S.X.c (eaD S.X.c (Fin.natAdd n l0) Phi) z * c l')
              - ∑ a' : Fin S.j, mu a' * eaEval S.X.c
                  (eaD S.X.c (Fin.natAdd n l') (eaD S.X.c (Fin.natAdd n l0) (S.h a'))) z)
          (fun r : Fin (S.j + 1) =>
            Fin.addCases
              (fun a' : Fin S.j => eaEval S.X.c (eaD S.X.c (Fin.natAdd n l') (S.h a')) z)
              (fun _ : Fin 1 => 0) r)
          a)
      (fun s : Fin (S.j + 1) =>
        Fin.addCases
          (fun b : Fin S.j =>
            Fin.addCases
              (fun l0 : Fin (1 + m) => - eaEval S.X.c (eaD S.X.c (Fin.natAdd n l0) (S.h b)) z)
              (fun r : Fin (S.j + 1) =>
                Fin.addCases
                  (fun _ : Fin S.j => (0 : ℝ))
                  (fun _ : Fin 1 => 2 * mu b) r)
              a)
          (fun _ : Fin 1 =>
            Fin.addCases
              (fun l0 : Fin (1 + m) => eaEval S.X.c (eaD S.X.c (Fin.natAdd n l0) Phi) z
                + eaEval S.X.c Phi z * c l0)
              (fun r : Fin (S.j + 1) =>
                Fin.addCases
                  (fun _ : Fin S.j => (0 : ℝ))
                  (fun _ : Fin 1 => 2 * mu0) r)
              a)
          s)
      l

/-- The normalisation of the multipliers: they lie on the unit sphere. -/
def LagNorm {j : ℕ} (μ : Fin j → ℝ) (μ₀ : ℝ) : Prop := (∑ a, (μ a) ^ 2) + μ₀ ^ 2 = 1

end Work.WilE9G
