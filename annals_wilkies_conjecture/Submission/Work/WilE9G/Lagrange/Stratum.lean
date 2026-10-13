/-
  WilE9G / Lagrange — **the construction (G4) of the Lagrange stratum**.

  Given an ambient `Good` stratum `S : AmbStratum (n + (1+m))`, an effectively smooth weight
  `Phi : EAPoly (n + (1+m)) S.X.r` which is strictly positive on `S.X.set` and a direction
  `c : Fin (1+m) → ℝ`, the construction produces an `EffStratum n (m + S.j + 1)` whose unknown
  fibre coordinates are `((y,t), μ, μ₀)` and whose equations are

  * `h_a` (`a : Fin S.j`), lifted from `S`,
  * the `1+m` homogeneous Lagrange equations `μ₀ (∂_l Φ + Φ c_l) - ∑_a μ_a ∂_l h_a`,
  * the normalisation `∑_a μ_a² + μ₀² - 1`,

  with the single disjunct whose strict inequalities are the nonvanishing of the fibre Jacobian's
  determinant (squared) together with the interior conditions `1 - x_i² > 0` on the base-and-fibre
  coordinates.  The set of the stratum is then *exactly* the nondegenerate part of the Lagrange
  locus intersected with the open cube, which is what makes `Good` provable (§5.1 and §8 of
  `WilE9G/STATUS.md`) and what makes the Lagrange points land in `E.X.set`.

  The statements below fix the exact polynomials; the proofs of the facts about them live in the
  delegated modules next to this one (see `exists_lagrange_stratum.lean`).
-/
import Mathlib
import Submission.Work.WilE9G.Lagrange.Defs
import Submission.Work.WilE7.Defs
import Submission.Work.WilE7.pad_eval

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE9G.Lagrange
open WilkiesDesign WilkiesDesign.E Work.WilE9G

/-! ## Index bookkeeping -/

/-- The equivalence between the equation-index type of the constructed stratum and the block
structure `Fin ((1+m) + (j+1))` used by `lagJac`.  It preserves values: `i < 1+m` is an
`L`-index, `1+m ≤ i < 1+m+j` an `h`-index, and `i = 1+m+j` the normalisation. -/
def lagEquiv (m j : ℕ) : Fin (1 + (m + j + 1)) ≃ Fin ((1 + m) + (j + 1)) :=
  Work.WilE7.finEquiv (by omega : 1 + (m + j + 1) = (1 + m) + (j + 1))

@[simp] theorem lagEquiv_apply_val (m j : ℕ) (i : Fin (1 + (m + j + 1))) :
    ((lagEquiv m j) i).val = i.val := rfl

/-- The ambient index of the multiplier `μ_a` of the constructed stratum: the coordinate order of
`lagPoint` is `(x, (y,t), μ, μ₀)`. -/
def muIdx (n m : ℕ) {j : ℕ} (a : Fin j) : Fin (n + (1 + (m + j + 1))) :=
  ⟨n + (1 + m) + a.val, by omega⟩

/-- The ambient index of the multiplier `μ₀` of the constructed stratum. -/
def mu0Idx (n m j : ℕ) : Fin (n + (1 + (m + j + 1))) := ⟨n + (1 + m) + j, by omega⟩

@[simp] theorem muIdx_val (n m : ℕ) {j : ℕ} (a : Fin j) :
    (muIdx n m a).val = n + (1 + m) + a.val := rfl

@[simp] theorem mu0Idx_val (n m j : ℕ) : (mu0Idx n m j).val = n + (1 + m) + j := rfl

/-! ## The polynomials of the construction -/

/-- The chain of the constructed stratum: the chain of `S`, padded to the extra coordinates. -/
def lagChain {n m : ℕ} (S : AmbStratum (n + (1 + m))) :
    EAChain (n + (1 + (m + S.j + 1))) S.X.r :=
  Work.WilE7.EAChain.pad (by omega) S.X.c

/-- The multiplier variable `μ_a`. -/
def muVar {n m : ℕ} (S : AmbStratum (n + (1 + m))) (a : Fin S.j) :
    EAPoly (n + (1 + (m + S.j + 1))) S.X.r :=
  MvPolynomial.X (Sum.inl (muIdx n m a))

/-- The multiplier variable `μ₀`. -/
def mu0Var {n m : ℕ} (S : AmbStratum (n + (1 + m))) :
    EAPoly (n + (1 + (m + S.j + 1))) S.X.r :=
  MvPolynomial.X (Sum.inl (mu0Idx n m S.j))

/-- The lift of the equation `h_a` of `S`. -/
def lagH {n m : ℕ} (S : AmbStratum (n + (1 + m))) (a : Fin S.j) :
    EAPoly (n + (1 + (m + S.j + 1))) S.X.r :=
  Work.WilE7.EAPoly.pad (by omega) (S.h a)

/-- The homogeneous Lagrange equation indexed by `l`:
`μ₀ (∂_l Φ + Φ c_l) - ∑_a μ_a ∂_l h_a`. -/
def lagL {n m : ℕ} (S : AmbStratum (n + (1 + m))) (Phi : EAPoly (n + (1 + m)) S.X.r)
    (c : Fin (1 + m) → ℝ) (l : Fin (1 + m)) :
    EAPoly (n + (1 + (m + S.j + 1))) S.X.r :=
  mu0Var S * (Work.WilE7.EAPoly.pad (by omega) (eaD S.X.c (Fin.natAdd n l) Phi)
      + MvPolynomial.C (c l) * Work.WilE7.EAPoly.pad (by omega) Phi)
    - ∑ a : Fin S.j,
        muVar S a * Work.WilE7.EAPoly.pad (by omega) (eaD S.X.c (Fin.natAdd n l) (S.h a))

/-- The normalisation equation `∑_a μ_a² + μ₀² - 1`. -/
def lagN {n m : ℕ} (S : AmbStratum (n + (1 + m))) :
    EAPoly (n + (1 + (m + S.j + 1))) S.X.r :=
  (∑ a : Fin S.j, (muVar S a) ^ 2) + (mu0Var S) ^ 2 - 1

/-- The equations of the constructed stratum, in the block order `(L, h, N)` of `lagJac`. -/
def lagEqs {n m : ℕ} (S : AmbStratum (n + (1 + m))) (Phi : EAPoly (n + (1 + m)) S.X.r)
    (c : Fin (1 + m) → ℝ) :
    Fin (1 + (m + S.j + 1)) → EAPoly (n + (1 + (m + S.j + 1))) S.X.r :=
  fun a => Fin.addCases (fun l : Fin (1 + m) => lagL S Phi c l)
    (fun s : Fin (S.j + 1) =>
      Fin.addCases (fun b : Fin S.j => lagH S b) (fun _ : Fin 1 => lagN S) s)
    (lagEquiv m S.j a)

/-- The symbolic determinant of the fibre block of the constructed system. -/
def lagDet {n m : ℕ} (S : AmbStratum (n + (1 + m))) (Phi : EAPoly (n + (1 + m)) S.X.r)
    (c : Fin (1 + m) → ℝ) : EAPoly (n + (1 + (m + S.j + 1))) S.X.r :=
  Matrix.det (Matrix.of fun (a l : Fin (1 + (m + S.j + 1))) =>
    eaD (lagChain S) (Fin.natAdd n l) (lagEqs S Phi c a))

/-- The strict inequalities of the constructed stratum: the nonvanishing of the fibre determinant
(squared, so that one disjunct covers both signs) and the interior conditions `1 - x_i² > 0` on the
base-and-fibre coordinates of `S`. -/
def lagPos {n m : ℕ} (S : AmbStratum (n + (1 + m))) (Phi : EAPoly (n + (1 + m)) S.X.r)
    (c : Fin (1 + m) → ℝ) : List (EAPoly (n + (1 + (m + S.j + 1))) S.X.r) :=
  (lagDet S Phi c * lagDet S Phi c)
    :: (List.ofFn fun i : Fin (n + (1 + m)) =>
          1 - (MvPolynomial.X (Sum.inl (Fin.castLE (by omega) i))) ^ 2)

/-- **The Lagrange stratum of the construction.** -/
def lagStratum {n m : ℕ} (S : AmbStratum (n + (1 + m))) (Phi : EAPoly (n + (1 + m)) S.X.r)
    (c : Fin (1 + m) → ℝ) : Work.WilE9.Sharp.EffStratum n (m + S.j + 1) :=
  ⟨⟨S.X.r, lagChain S, [⟨List.ofFn (lagEqs S Phi c), lagPos S Phi c⟩]⟩, lagEqs S Phi c⟩

theorem lagStratum_X_r {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ) :
    (lagStratum S Phi c).X.r = S.X.r := rfl

theorem lagStratum_X_c {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ) :
    (lagStratum S Phi c).X.c = lagChain S := rfl

theorem lagStratum_h {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ) :
    (lagStratum S Phi c).h = lagEqs S Phi c := rfl

theorem lagStratum_basics {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ) :
    (lagStratum S Phi c).X.basics
      = [⟨List.ofFn (lagEqs S Phi c), lagPos S Phi c⟩] := rfl

/-! ## The two matrices -/

/-- The *true* Jacobian of the natural Lagrange system, written in the index conventions of
`lagJac` (rows `(L, h, N)`, columns `((y,t), μ, μ₀)`): the `(L_{l₀}, yt_{l'})` entry is the honest
partial derivative `∂_{l'}` of the equation `μ₀(∂_{l₀}Φ + Φ c_{l₀}) - ∑_a μ_a ∂_{l₀}h_a`, i.e.
`μ₀(∂_{l'}∂_{l₀}Φ + c_{l₀}∂_{l'}Φ) - ∑_a μ_a ∂_{l'}∂_{l₀}h_a`.  It differs from `lagJac` only in
the `(L,yt)` block, which is the transpose of that of `lagJac`: `lagJac` carries the `Φ`-derivative
`∂_{l₀}Φ` and the coefficient `c_{l'}` there instead of `∂_{l'}Φ` and `c_{l₀}`. -/
def lagJacTrue {n m : ℕ} (S : AmbStratum (n + (1 + m))) (Phi : EAPoly (n + (1 + m)) S.X.r)
    (c : Fin (1 + m) → ℝ) (z : Fin (n + (1 + m)) → ℝ) (mu : Fin S.j → ℝ) (mu0 : ℝ) :
    Matrix (Fin ((1 + m) + (S.j + 1))) (Fin ((1 + m) + (S.j + 1))) ℝ :=
  Matrix.of fun a l =>
    Fin.addCases
      (fun l' : Fin (1 + m) =>
        Fin.addCases
          (fun l0 : Fin (1 + m) =>
            mu0 * (eaEval S.X.c (eaD S.X.c (Fin.natAdd n l') (eaD S.X.c (Fin.natAdd n l0) Phi)) z
                  + eaEval S.X.c (eaD S.X.c (Fin.natAdd n l') Phi) z * c l0)
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

/-- The fibre block of the constructed stratum at a point: the derivatives of its equations in the
`1 + m + S.j + 1` fibre coordinates.  This is what `EffStratum.Good` requires to be invertible. -/
def lagBlock {n m : ℕ} (S : AmbStratum (n + (1 + m))) (Phi : EAPoly (n + (1 + m)) S.X.r)
    (c : Fin (1 + m) → ℝ) (w : Fin (n + (1 + (m + S.j + 1))) → ℝ) :
    Matrix (Fin (1 + (m + S.j + 1))) (Fin (1 + (m + S.j + 1))) ℝ :=
  Matrix.of fun (a l : Fin (1 + (m + S.j + 1))) =>
    eaEval (lagChain S) (eaD (lagChain S) (Fin.natAdd n l) (lagEqs S Phi c a)) w

theorem lagBlock_apply {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ)
    (w : Fin (n + (1 + (m + S.j + 1))) → ℝ) (a l : Fin (1 + (m + S.j + 1))) :
    lagBlock S Phi c w a l
      = eaEval (lagChain S) (eaD (lagChain S) (Fin.natAdd n l) (lagEqs S Phi c a)) w := rfl

end Work.WilE9G.Lagrange
