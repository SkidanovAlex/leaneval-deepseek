/-
  Subproject WilE9G — packaging of the covering step (§5.2 of `STATUS.md`).

  `stratProj_eq_of_isPreconnected` (delegated, `Cover/stratProj_eq_of_isPreconnected.lean`) says
  that a preconnected subset of `comp(X, z₀)` lying over a base point `x` is *projected to a
  single point* as soon as the `P`-fibre over `x` is finite.  Here it is specialised to the object
  the construction maximises over: a connected component of
  `comp(X, z₀) ∩ {π_base = x}`.
-/
import Submission.Work.WilE9G.Basic
import Submission.Work.WilE9G.Cover.stratProj_eq_of_isPreconnected

set_option autoImplicit false
noncomputable section
open Classical Topology Filter MeasureTheory
namespace Work.WilE9G
open WilkiesDesign WilkiesDesign.E Work.WilE9.Sharp

/-- The fibre of the `*`-piece `P = stratProj '' connectedComponentIn X.set z₀` over `x`. -/
def fibrePiece {n m : ℕ} (X : SemiPf (n + (1 + m))) (z₀ : Fin (n + (1 + m)) → ℝ)
    (x : Fin n → ℝ) : Set (Fin (n + 1) → ℝ) :=
  {y' | y' ∈ stratProj '' connectedComponentIn X.set z₀ ∧ Fin.init y' = x}

/-- The part of `comp(X, z₀)` that lies over the base point `x`. -/
def compFibre {n m : ℕ} (X : SemiPf (n + (1 + m))) (z₀ : Fin (n + (1 + m)) → ℝ)
    (x : Fin n → ℝ) : Set (Fin (n + (1 + m)) → ℝ) :=
  connectedComponentIn X.set z₀ ∩ {w | Fin.init (stratProj w) = x}

/-- **The covering step.**  A component of the part of `comp(X, z₀)` over `x` is projected to a
single point of `ℝ^{n+1}`, as soon as the `P`-fibre over `x` is finite.  This is what makes a
maximiser `w` of `Φ · e^{c·(y,t)}` over such a component satisfy `stratProj w = y` for the
`y ∈ P` above `x`. -/
theorem stratProj_eq_of_mem_compFibre {n m : ℕ} {X : SemiPf (n + (1 + m))}
    {z₀ z : Fin (n + (1 + m)) → ℝ} {x : Fin n → ℝ}
    (hfin : (fibrePiece X z₀ x).Finite)
    {u v : Fin (n + (1 + m)) → ℝ}
    (hu : u ∈ connectedComponentIn (compFibre X z₀ x) z)
    (hv : v ∈ connectedComponentIn (compFibre X z₀ x) z) :
    stratProj u = stratProj v :=
  Work.WilE9G.Cover.stratProj_eq_of_isPreconnected
    (K := connectedComponentIn (compFibre X z₀ x) z)
    isPreconnected_connectedComponentIn
    (fun _ hw => (connectedComponentIn_subset _ _ hw).1)
    (fun _ hw => (connectedComponentIn_subset _ _ hw).2)
    hfin u hu v hv

/-- The value of `stratProj` on such a component is the value at any of its points: if the
maximiser `w` lies in the component of `z` and `stratProj z = y`, then `stratProj w = y`. -/
theorem stratProj_eq_of_mem_compFibre' {n m : ℕ} {X : SemiPf (n + (1 + m))}
    {z₀ : Fin (n + (1 + m)) → ℝ} {x : Fin n → ℝ}
    (hfin : (fibrePiece X z₀ x).Finite) {z v : Fin (n + (1 + m)) → ℝ}
    (hz : z ∈ compFibre X z₀ x) (hv : v ∈ connectedComponentIn (compFibre X z₀ x) z) :
    stratProj v = stratProj z :=
  stratProj_eq_of_mem_compFibre (u := v) (v := z) hfin hv (mem_connectedComponentIn hz)

end Work.WilE9G
