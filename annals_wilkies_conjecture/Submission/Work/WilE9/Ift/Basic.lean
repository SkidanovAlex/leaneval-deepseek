/-
  WilE9 — the implicit-function-theorem polynomials of BNZ §3 ("sharp derivatives").

  Setting: `n` base coordinates `x : Fin n → ℝ` and `q` fibre coordinates `y : Fin q → ℝ`, so the
  ambient coordinates are `Fin (n+q)` with `Fin.castAdd q i` the `i`-th base coordinate and
  `Fin.natAdd n l` the `l`-th fibre coordinate.  `F : Fin q → EAPoly (n+q) r` is a system of `q`
  EA polynomials and `y` is a smooth solution of `F (x, y x) = 0` whose fibre Jacobian
  `A = ∂F/∂y` is invertible.

  All derivatives of the *ambient* EA function `eaEval c P` in an ambient coordinate direction
  are computed by the symbolic operator `eaD c ·`; in particular the fibre Jacobian is
  `eaD c (Fin.natAdd n l)` and not `MvPolynomial.pderiv`, because the chain functions
  `exp (c.ell j ·)` may depend on the fibre coordinates as well.

  * `jm c F` is the matrix `A`,
  * `jQ c F = det A` is the denominator `Q` of BNZ's formula,
  * `jc c F l i = -Σ_j adj(A)_{lj} (∂F_j/∂x_i)` is the *cleared* first derivative `Q · ∂y_l/∂x_i`,
  * `iftP c F l₀ L` is the polynomial `P_L` with the property (proved in `WilE9/Ift/Identity.lean`)
      `(∂_L y_{l₀})(x) = P_L(x, y x) / Q(x, y x) ^ (2 * |L|)`.

  The recursion is the one obtained by differentiating `P_L/Q^{2|L|}` along `x_i` and clearing
  denominators with the first-derivative formula `Q ∂_{x_i} y_l = -Σ_j adj(A)_{lj} ∂F_j/∂x_i`:

    `P_{i::L} = Q² · ∂_{x_i}P_L + Q · Σ_l (∂_{y_l}P_L)·(C_{l i})
                - 2|L| · P_L · ( Q·∂_{x_i}Q + Σ_l (∂_{y_l}Q)·(C_{l i}) )`

  where `C_{l i} = jc c F l i`.  This is what makes the degree grow *additively* in `|L|`, i.e.
  polynomially in the order of the derivative — the content of "sharp derivatives".
-/
import Submission.Work.WilE9.Defs

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Classical Filter Topology
namespace Work.WilE9
open WilkiesDesign WilkiesDesign.E

/-- `∂F_j/∂y_l`, as a `q × q` matrix of EA polynomials (total derivative in the ambient
coordinate `Fin.natAdd n l`). -/
def jm {n q r : ℕ} (c : EAChain (n + q) r) (F : Fin q → EAPoly (n + q) r) :
    Matrix (Fin q) (Fin q) (EAPoly (n + q) r) :=
  Matrix.of fun j l => eaD c (Fin.natAdd n l) (F j)

/-- `Q = det (∂F/∂y)`: the denominator in BNZ's implicit-derivative formula. -/
def jQ {n q r : ℕ} (c : EAChain (n + q) r) (F : Fin q → EAPoly (n + q) r) : EAPoly (n + q) r :=
  (jm c F).det

/-- `∂F_j/∂x_i` (total derivative in the ambient coordinate `Fin.castAdd q i`). -/
def jb {n q r : ℕ} (c : EAChain (n + q) r) (F : Fin q → EAPoly (n + q) r) (j : Fin q)
    (i : Fin n) : EAPoly (n + q) r := eaD c (Fin.castAdd q i) (F j)

/-- The cleared first derivative `Q · ∂y_l/∂x_i = -Σ_j adj(A)_{lj} ∂F_j/∂x_i`. -/
def jc {n q r : ℕ} (c : EAChain (n + q) r) (F : Fin q → EAPoly (n + q) r) (l : Fin q)
    (i : Fin n) : EAPoly (n + q) r :=
  -∑ j, (jm c F).adjugate l j * jb c F j i

/-- The implicit-derivative polynomial `P_L`: `(∂_L y_{l₀})(x) = P_L(x,yx)/Q(x,yx)^{2|L|}`. -/
def iftP {n q r : ℕ} (c : EAChain (n + q) r) (F : Fin q → EAPoly (n + q) r) (l₀ : Fin q) :
    List (Fin n) → EAPoly (n + q) r
  | [] => MvPolynomial.X (Sum.inl (Fin.natAdd n l₀))
  | i :: L =>
      jQ c F ^ 2 * eaD c (Fin.castAdd q i) (iftP c F l₀ L)
      + jQ c F * ∑ l : Fin q,
          eaD c (Fin.natAdd n l) (iftP c F l₀ L) * jc c F l i
      - (2 * L.length) • (iftP c F l₀ L *
          (jQ c F * eaD c (Fin.castAdd q i) (jQ c F)
            + ∑ l : Fin q,
                eaD c (Fin.natAdd n l) (jQ c F) * jc c F l i))

/-- Hypotheses of the implicit function theorem in the form used here: `F(x, y x) = 0` near
`x₀` and the fibre Jacobian `∂F/∂y` invertible near `x₀`. -/
def IsSoln {n q r : ℕ} (c : EAChain (n + q) r) (F : Fin q → EAPoly (n + q) r)
    (y : (Fin n → ℝ) → (Fin q → ℝ)) (x₀ : Fin n → ℝ) : Prop :=
  (∀ᶠ x in 𝓝 x₀, ∀ j, eaEval c (F j) (Fin.append x (y x)) = 0) ∧
  (∀ᶠ x in 𝓝 x₀, ((jm c F).map (fun P => eaEval c P (Fin.append x (y x)))).det ≠ 0)

end Work.WilE9
