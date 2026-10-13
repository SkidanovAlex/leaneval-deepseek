/-
  Subproject WilE9G / Assembly — the definitions of the final assembly of `EffStratAE_of_frozen`.

  Three things are fixed here.

  * `atomChain n m c` : the exp-affine chain with the single atom `c · (y,t)`
    (`∑_l c l * w (Fin.natAdd n l)`), used to make the weight
    `Φ_β · e^{c·(y,t)}` an `EAPoly` of the stratum's chain.

  * `AmbStratum.cat S c₂` : an ambient stratum whose chain is `S.X.c` concatenated with `c₂` (so
    that polynomials of *other* chains become available while the set and `Good` are unchanged).

  * `lagStratumAE` : the **boundary-compatible** Lagrange stratum.  It is the Lagrange stratum of
    `Work.WilE9G.Lagrange.Stratum` with two changes:

    - the single disjunct `⟨lagEqs, [lagDet², 1 - xᵢ², …]⟩` is replaced by the DNF
      `⟨lagEqs ++ B.eqs, [lagDet²] ++ B.pos⟩` over the basics `B` of the *input* stratum `S`
      (so that `E.X.set ⊆ {v | v ∈ S.X.set} × multipliers`), and
    - the interior (open cube) conditions are dropped.

    These two changes are what make `Good` compatible with Lagrange points whose base-and-fibre
    part lies on the *boundary* of the cube `[-1,1]^{n+(1+m)}`: `Good`'s locality clause is
    recovered from the locality of `S` (a point of `E.X.set` has its `(x,(y,t))`-part in `S.X.set`,
    and the equation part `lagH` reproduces the equations of `S`), while the cube bound on a
    neighbourhood follows from `S.X.set ⊆ cubeC` and the normalisation equation.
-/
import Mathlib
import Submission.Work.WilE9G.Lagrange.Stratum
import Submission.Work.WilE9G.Amb
import Submission.Work.WilE7.SubPfAux.unionSet_set

set_option autoImplicit false
noncomputable section
open Classical Topology Filter MeasureTheory
namespace Work.WilE9G.Assembly
open WilkiesDesign WilkiesDesign.E Work.WilE9G Work.WilE9G.Lagrange

/-! ## The single-atom chain `c · (y,t)` -/

/-- The exp-affine chain with one function, `ℓ(w) = ∑_l c l * w (Fin.natAdd n l)`, i.e. the
linear form `c` read on the *fibre* coordinates of `ℝ^{n + (1+m)}`. -/
def atomChain (n m : ℕ) (c : Fin (1 + m) → ℝ) : EAChain (n + (1 + m)) 1 :=
  ⟨fun _ i => if h : n ≤ i.val then c ⟨i.val - n, by omega⟩ else 0, fun _ => 0⟩

/-- The coefficient of the atom `c · (y,t)` on a fibre coordinate is the corresponding `c l`. -/
theorem atomChain_a_natAdd (n m : ℕ) (c : Fin (1 + m) → ℝ) (l : Fin (1 + m)) :
    (atomChain n m c).a 0 (Fin.natAdd n l) = c l := by
  simp only [atomChain, Fin.val_natAdd, Nat.add_sub_cancel_left]
  rw [dif_pos (Nat.le_add_right n l)]

/-- The coefficient of the atom `c · (y,t)` on a base coordinate vanishes. -/
theorem atomChain_a_castAdd (n m : ℕ) (c : Fin (1 + m) → ℝ) (i : Fin n) :
    (atomChain n m c).a 0 (Fin.castAdd (1 + m) i) = 0 := by
  simp only [atomChain, Fin.val_castAdd]
  rw [dif_neg (by omega : ¬ n ≤ i.val)]

/-- The chain function of `atomChain` is `c` on the fibre coordinates. -/
theorem atomChain_ell (n m : ℕ) (c : Fin (1 + m) → ℝ) (w : Fin (n + (1 + m)) → ℝ) :
    (atomChain n m c).ell 0 w = ∑ l : Fin (1 + m), c l * w (Fin.natAdd n l) := by
  rw [EAChain.ell]
  have hb : (atomChain n m c).b 0 = 0 := rfl
  rw [hb, add_zero]
  rw [Fin.sum_univ_add]
  rw [show (∑ i : Fin n, (atomChain n m c).a 0 (Fin.castAdd (1 + m) i)
      * w (Fin.castAdd (1 + m) i)) = 0 from
    Finset.sum_eq_zero (fun i _ => by rw [atomChain_a_castAdd, zero_mul])]
  rw [zero_add]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [atomChain_a_natAdd]

/-- The evaluation of the atom polynomial of the chain `atomChain n m c`. -/
theorem eaEval_atomChain (n m : ℕ) (c : Fin (1 + m) → ℝ) (w : Fin (n + (1 + m)) → ℝ) :
    eaEval (atomChain n m c) (MvPolynomial.X (Sum.inr 0)) w
      = Real.exp (∑ l : Fin (1 + m), c l * w (Fin.natAdd n l)) := by
  rw [eaEval, MvPolynomial.eval_X]
  simp only [Sum.elim_inr]
  rw [atomChain_ell]

/-- The derivative of the atom polynomial in a fibre direction is `c l` times the atom. -/
theorem eaD_atomChain (n m : ℕ) (c : Fin (1 + m) → ℝ) (l : Fin (1 + m)) :
    eaD (atomChain n m c) (Fin.natAdd n l) (MvPolynomial.X (Sum.inr 0))
      = MvPolynomial.C (c l) * MvPolynomial.X (Sum.inr 0) := by
  rw [eaD]
  have hp1 : MvPolynomial.pderiv (Sum.inl (Fin.natAdd n l)) (MvPolynomial.X (Sum.inr 0))
      = (0 : EAPoly (n + (1 + m)) 1) :=
    MvPolynomial.pderiv_X_of_ne (i := Sum.inl (Fin.natAdd n l)) (j := Sum.inr 0)
      (by simp)
  rw [hp1, zero_add, Fin.sum_univ_one]
  rw [MvPolynomial.pderiv_X_self, mul_one, atomChain_a_natAdd]

/-! ## Extending the chain of an ambient stratum -/

/-- The ambient stratum `S` with the chain `c₂` concatenated to its own: the set, the equations
and the `Good` predicate are unchanged. -/
def ambCat {N r₂ : ℕ} (S : Work.WilE9G.AmbStratum N) (c₂ : EAChain N r₂) :
    Work.WilE9G.AmbStratum N :=
  ⟨Work.WilE7.SemiPf.unionSet S.X ⟨r₂, c₂, []⟩, S.j,
    fun a => Work.WilE7.EAPoly.inl (S.h a)⟩

@[simp] theorem ambCat_j {N r₂ : ℕ} (S : Work.WilE9G.AmbStratum N)
    (c₂ : EAChain N r₂) : (ambCat S c₂).j = S.j := rfl

@[simp] theorem ambCat_h {N r₂ : ℕ} (S : Work.WilE9G.AmbStratum N)
    (c₂ : EAChain N r₂) (a : Fin S.j) :
    (ambCat S c₂).h a = Work.WilE7.EAPoly.inl (S.h a) := rfl

@[simp] theorem ambCat_X_c {N r₂ : ℕ} (S : Work.WilE9G.AmbStratum N)
    (c₂ : EAChain N r₂) : (ambCat S c₂).X.c = Work.WilE7.EAChain.cat S.X.c c₂ := rfl

@[simp] theorem ambCat_X_r {N r₂ : ℕ} (S : Work.WilE9G.AmbStratum N)
    (c₂ : EAChain N r₂) : (ambCat S c₂).X.r = S.X.r + r₂ := rfl

@[simp] theorem ambCat_X_basics {N r₂ : ℕ} (S : Work.WilE9G.AmbStratum N)
    (c₂ : EAChain N r₂) :
    (ambCat S c₂).X.basics = S.X.basics.map Work.WilE7.Basic.inl := by
  simp only [ambCat, Work.WilE7.SemiPf.unionSet, List.map_nil, List.append_nil]

/-! ## The boundary-compatible Lagrange stratum -/

/-- **The boundary-compatible Lagrange stratum.**  Given an ambient `Good` stratum `S` (of
`ℝ^{n+(1+m)}`), a weight `Φ` and a direction `c`, this is the `EffStratum n (m + S.j + 1)` with

* equations `lagEqs S Φ c` (the `1+m` Lagrange equations, the `S.j` lifted equations of `S`, and
  the normalisation), and
* one disjunct per basic `B` of `S.X`, whose equations are `lagEqs S Φ c` together with `B.eqs`
  and whose strict inequalities are `lagDet² > 0` together with `B.pos`.

`lagStratumAE` differs from `Lagrange.lagStratum` only in that it has *no* interior (open cube)
conditions and in that it carries the conditions of `S.X` as part of its DNF.  Consequently it
contains Lagrange points whose base-and-fibre part is only in the *closed* cube. -/
def lagStratumAE {n m : ℕ} (S : Work.WilE9G.AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ) :
    Work.WilE9.Sharp.EffStratum n (m + S.j + 1) :=
  ⟨⟨S.X.r, lagChain S,
      S.X.basics.map (fun B =>
        ⟨List.ofFn (lagEqs S Phi c) ++ B.eqs.map (Work.WilE7.EAPoly.pad (by omega)),
         [lagDet S Phi c * lagDet S Phi c] ++ B.pos.map (Work.WilE7.EAPoly.pad (by omega))⟩)⟩,
    lagEqs S Phi c⟩

@[simp] theorem lagStratumAE_h {n m : ℕ} (S : Work.WilE9G.AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ) :
    (lagStratumAE S Phi c).h = lagEqs S Phi c := rfl

@[simp] theorem lagStratumAE_X_r {n m : ℕ} (S : Work.WilE9G.AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ) :
    (lagStratumAE S Phi c).X.r = S.X.r := rfl

@[simp] theorem lagStratumAE_X_c {n m : ℕ} (S : Work.WilE9G.AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ) :
    (lagStratumAE S Phi c).X.c = lagChain S := rfl


/-! ## Extending the chain of an ambient stratum by the chain of a semi-Pfaffian set -/

/-- `S` with the chain of `X` concatenated to the right of its own.  (An `abbrev` on a literal, so
that its fields reduce at reducible transparency.) -/
abbrev ambCatX {N : ℕ} (S : Work.WilE9G.AmbStratum N)
    (X : WilkiesDesign.E.SemiPf N) : Work.WilE9G.AmbStratum N :=
  ⟨⟨S.X.r + X.r, Work.WilE7.EAChain.cat S.X.c X.c, S.X.basics.map Work.WilE7.Basic.inl⟩,
   S.j, fun a => Work.WilE7.EAPoly.inl (S.h a)⟩

end Work.WilE9G.Assembly
