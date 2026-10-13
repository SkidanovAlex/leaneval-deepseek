/-
  WilG0 — area G0 of the BNZ algebraic lemma (Binyamini–Novikov–Zak, arXiv 2202.05305 §2):
  the Ω-formula calculus.  The frozen target is

    `WilkiesDesign.CG.G0_calculus`   (in `Submission/Work/Wilkies/CG/Spec.lean`)

  saying: for every shape `s : OShape n` and every format `F` there is a single format `a`
  such that every good datum `d` realizes `s` as a set in `S.Ω a (s.deg d) n`, where `s.deg`
  adds degrees over the shape (`+2` for every substitution atom).

  This file holds the vocabulary of the area: the vector-glueing map `snocIt` which puts the
  surviving `n` coordinates in front and the eliminated `m` coordinates at the end, the
  iterated projection `projLastIter`, and the "lift"/"diagonal" sets used to code a
  substitution atom.  The lemmas live in sibling modules of this directory, all of which
  import this one.
-/
import Submission.Work.Wilkies.CG.Spec

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilG0

open WilkiesDesign

/-! ## Vector glueing

`snocIt n m x w : Fin (n + m) → ℝ` has the coordinates of `x` in positions `0, …, n-1` and
those of `w` in positions `n, …, n+m-1`.  This is the vector produced by iterating
`Fin.snoc`, i.e. by iterating the projection axiom `SOMin.proj` (`projLast`). -/
def snocIt (n : ℕ) : (m : ℕ) → (Fin n → ℝ) → (Fin m → ℝ) → Fin (n + m) → ℝ
  | 0, x, _ => x
  | m + 1, x, w => Fin.snoc (snocIt n m x (Fin.init w)) (w (Fin.last m))

/-- Iterated `projLast`: eliminate the last `m` coordinates of a set in `ℝ^{n+m}`. -/
def projLastIter (n : ℕ) : (m : ℕ) → Set (Fin (n + m) → ℝ) → Set (Fin n → ℝ)
  | 0, X => X
  | m + 1, X => projLastIter n m (projLast X)

/-! ## The sets coding a substitution atom

To code `x ∘ ι ∈ D` (`D ⊆ ℝ^m`, `ι : Fin m → Fin n`) we work in `ℝ^{n+m}`: the first `n`
coordinates carry `x`, the last `m` carry a fresh `w`, and we impose `w ∈ D` together with
`w = x ∘ ι`.  Compositional order is forced by the axioms: `SOMin.prod_left` prepends free
coordinates (so the `D`-block sits at the *end* of `Fin (m+n)`), whereas `SOMin.proj` removes
the *last* coordinates (so the surviving block sits in front, i.e. in `Fin (n+m)`).
The two orders are bridged by `Omega_cast` (`Nat.add_comm`), which is free. -/

/-- `D` placed in the *last* `m` coordinates of `ℝ^{m+n}` (index `j ↦ j+n`); the first `n`
coordinates are free.  This is the shape produced by iterating `SOMin.prod_left`. -/
def liftMN (n m : ℕ) (D : Set (Fin m → ℝ)) : Set (Fin (m + n) → ℝ) :=
  {z | (fun j : Fin m => z (Fin.addNat j n)) ∈ D}

/-- The same set as `liftMN`, but written in `ℝ^{n+m}`: the surviving coordinates come first,
the `D`-block is the last `m` coordinates (index `j ↦ n+j`).  This is the shape consumed by
`projLastIter`.  It is the transport of `liftMN` along `Nat.add_comm`. -/
def liftNM (n m : ℕ) (D : Set (Fin m → ℝ)) : Set (Fin (n + m) → ℝ) :=
  {z | (fun j : Fin m => z (Fin.natAdd n j)) ∈ D}

/-- The graph of the substitution `x ↦ x ∘ ι` inside `ℝ^{n+m}`: the last `m` coordinates
equal the first `n` coordinates composed with `ι`. -/
def diagSet (n m : ℕ) (ι : Fin m → Fin n) : Set (Fin (n + m) → ℝ) :=
  {z | ∀ j : Fin m, z (Fin.natAdd n j) = z (Fin.castAdd m (ι j))}

/-- The polynomial `Σ_j (W_j - X_{ι j})²` whose zero set is `diagSet`: it has total degree at
most two, which is exactly the `+2` charged for a substitution atom. -/
def diagPoly (n m : ℕ) (ι : Fin m → Fin n) : MvPolynomial (Fin (n + m)) ℝ :=
  ∑ j : Fin m, (MvPolynomial.X (Fin.natAdd n j) - MvPolynomial.X (Fin.castAdd m (ι j))) *
    (MvPolynomial.X (Fin.natAdd n j) - MvPolynomial.X (Fin.castAdd m (ι j)))

end Work.WilG0
