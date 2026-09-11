import Submission.GraphSpec
import Submission.PfExtra
import Submission.Perron
import Submission.Upper0
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Card

open Matrix
open scoped BigOperators

namespace Submission

set_option autoImplicit false

attribute [local instance] Classical.propDecidable

noncomputable section

/-! Machinery for the connected components of a graph `G : SimpleGraph (Fin n)`.
For a component `c : G.ConnectedComponent` (whose vertex type is the `SetLike` carrier `c`)
the induced component graph is `cGraph G c = c.toSimpleGraph`, and `compPreconnected` says it is
connected.  The decoupling lemmas `adj_restrict_mem` / `lamI_sub_adj_restrict` express that the
adjacency operator is block-diagonal over the components. -/

/-- `(B - C) *ᵥ v = B *ᵥ v - C *ᵥ v` for any index type. -/
lemma mulVec_sub_any {ι : Type*} [Fintype ι] (B C : Matrix ι ι ℝ) (v : ι → ℝ) :
    (B - C) *ᵥ v = B *ᵥ v - C *ᵥ v := by
  classical
  ext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_sub_distrib, sub_mul]

/-- `(s • 1) *ᵥ v = s • v` for any index type. -/
lemma mulVec_smul_one_any {ι : Type*} [Fintype ι] (s : ℝ) (v : ι → ℝ) :
    (s • (1 : Matrix ι ι ℝ)) *ᵥ v = s • v := by
  classical
  ext i
  simp [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Matrix.one_apply, Finset.sum_ite_eq]

variable {n : ℕ}

/-- the induced graph of a connected component (vertex type is the component itself). -/
def cGraph (G : SimpleGraph (Fin n)) (c : G.ConnectedComponent) : SimpleGraph c :=
  c.toSimpleGraph

noncomputable instance compVertFintype (G : SimpleGraph (Fin n)) (c : G.ConnectedComponent) :
    Fintype c := by
  classical
  exact Fintype.ofFinite c

noncomputable instance compFintype (G : SimpleGraph (Fin n)) : Fintype G.ConnectedComponent :=
  Fintype.ofFinite G.ConnectedComponent

/-- the size of a component. -/
noncomputable def compCard (G : SimpleGraph (Fin n)) (c : G.ConnectedComponent) : ℕ :=
  Fintype.card c

/-- the induced graph of a component is connected. -/
lemma compPreconnected (G : SimpleGraph (Fin n)) (c : G.ConnectedComponent) :
    (cGraph G c).Preconnected := by
  simpa [cGraph] using (SimpleGraph.ConnectedComponent.connected_toSimpleGraph c).preconnected

/-- vertices of the same component are reachable in the induced graph. -/
lemma compReachable (G : SimpleGraph (Fin n)) (c : G.ConnectedComponent) (u v : c) :
    (cGraph G c).Reachable u v := by
  simpa [cGraph] using (SimpleGraph.ConnectedComponent.reachable_toSimpleGraph c u.2 v.2)

/-- the adjacency matrix of a component, on the component type. -/
noncomputable def compAdj (G : SimpleGraph (Fin n)) (c : G.ConnectedComponent) :
    Matrix c c ℝ := (cGraph G c).adjMatrix ℝ

/-- extension of a function on a component to all vertices, zero outside. -/
def compExt (G : SimpleGraph (Fin n)) (c : G.ConnectedComponent) (y : c → ℝ) : Fin n → ℝ :=
  fun v => if h : v ∈ c.supp then y ⟨v, h⟩ else 0

lemma compExt_apply_mem (G : SimpleGraph (Fin n)) (c : G.ConnectedComponent) (y : c → ℝ)
    {v : Fin n} (hv : v ∈ c.supp) : compExt G c y v = y ⟨v, hv⟩ := by
  simp [compExt, hv]

lemma compExt_apply_not_mem (G : SimpleGraph (Fin n)) (c : G.ConnectedComponent) (y : c → ℝ)
    {v : Fin n} (hv : v ∉ c.supp) : compExt G c y v = 0 := by
  simp [compExt, hv]

lemma adj_in_supp {G : SimpleGraph (Fin n)} {c : G.ConnectedComponent} {u v : Fin n}
    (hv : v ∈ c.supp) (hadj : G.Adj v u) : u ∈ c.supp := by
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hv ⊢
  exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).symm.trans hv

lemma adj_self_in_supp {G : SimpleGraph (Fin n)} {c : G.ConnectedComponent} {v u : Fin n}
    (hu : u ∈ c.supp) (hadj : G.Adj v u) : v ∈ c.supp := by
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hu ⊢
  exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans hu

/-- adjacency applied to a function supported in one component stays supported there. -/
lemma adj_compExt_outside (G : SimpleGraph (Fin n)) (c : G.ConnectedComponent) (y : c → ℝ)
    {v : Fin n} (hv : v ∉ c.supp) : ((G.adjMatrix ℝ) *ᵥ compExt G c y) v = 0 := by
  classical
  have hno : ∀ u : Fin n, G.Adj v u → u ∉ c.supp := by
    intro u hadj
    by_contra hc
    exact hv (adj_self_in_supp hc hadj)
  simp only [Matrix.mulVec, dotProduct, SimpleGraph.adjMatrix_apply]
  apply Finset.sum_eq_zero
  intro u hu
  by_cases ha : G.Adj v u
  · have hu' : u ∉ c.supp := hno u ha
    simp [ha, compExt_apply_not_mem G c y hu']
  · simp [ha]

lemma cGraph_adj_iff (G : SimpleGraph (Fin n)) (c : G.ConnectedComponent) {u v : c} :
    (cGraph G c).Adj u v ↔ G.Adj u.1 v.1 := by
  simp [cGraph, SimpleGraph.ConnectedComponent.toSimpleGraph]

/-- restriction of a function on `Fin n` to the vertices of a component. -/
def compRest (G : SimpleGraph (Fin n)) (c : G.ConnectedComponent) (x : Fin n → ℝ) : c → ℝ :=
  fun v => x v.1

/-- `A_G x` at a vertex of component `c` only depends on `x` restricted to `c`. -/
lemma adj_restrict_mem (G : SimpleGraph (Fin n)) (c : G.ConnectedComponent) (x : Fin n → ℝ)
    (v : c) : ((G.adjMatrix ℝ) *ᵥ x) v.1 = ((cGraph G c).adjMatrix ℝ *ᵥ compRest G c x) v := by
  classical
  let g : Fin n → ℝ := fun u => if G.Adj v.1 u then x u else 0
  let T : Finset (Fin n) := (Finset.univ : Finset c).image (fun w : c => w.1)
  have himg_supp : ∀ u : Fin n, u ∈ T ↔ u ∈ c.supp := by
    intro u
    constructor
    · intro hu
      rcases Finset.mem_image.mp hu with ⟨w, hw, rfl⟩
      exact w.2
    · intro hu
      exact Finset.mem_image.mpr ⟨⟨u, hu⟩, Finset.mem_univ _, rfl⟩
  have hzero_out (u : Fin n) (huT : u ∉ T) : g u = 0 := by
    have hus : u ∉ c.supp := by intro h; exact huT ((himg_supp u).2 h)
    have hno : ¬ G.Adj v.1 u := by
      intro hadj
      exact hus (adj_in_supp v.2 hadj)
    simp [g, hno]
  have hL : (∑ u : Fin n, g u) = (∑ u ∈ T, g u) := by
    symm
    exact Finset.sum_subset (s₁ := T) (s₂ := Finset.univ) (f := g)
      (by intro u hu; exact Finset.mem_univ u)
      (by intro u hu huT; exact hzero_out u huT)
  have hT : (∑ u ∈ T, g u) = (∑ w : c, g w.1) := by
    rw [Finset.sum_image]
    intro u hu v' hv' huv
    exact Subtype.ext huv
  have hprod (u : Fin n) : (if G.Adj v.1 u then (1 : ℝ) else 0) * x u = g u := by
    by_cases ha : G.Adj v.1 u
    · simp [g, ha]
    · simp [g, ha]
  have hg (w : c) : g w.1 = (if G.Adj v.1 w.1 then (1 : ℝ) else 0) * compRest G c x w := by
    by_cases ha : G.Adj v.1 w.1
    · simp [g, ha, compRest]
    · simp [g, ha, compRest]
  calc
    ((G.adjMatrix ℝ) *ᵥ x) v.1
        = (∑ u : Fin n, (if G.Adj v.1 u then (1 : ℝ) else 0) * x u) := by
          simp [Matrix.mulVec, dotProduct, SimpleGraph.adjMatrix_apply]
    _ = (∑ u : Fin n, g u) := by
          apply Finset.sum_congr rfl
          intro u hu
          exact hprod u
    _ = (∑ u ∈ T, g u) := hL
    _ = (∑ w : c, g w.1) := hT
    _ = (∑ w : c, (if G.Adj v.1 w.1 then (1 : ℝ) else 0) * compRest G c x w) := by
          apply Finset.sum_congr rfl
          intro w hw
          exact hg w
    _ = ((cGraph G c).adjMatrix ℝ *ᵥ compRest G c x) v := by
          simp [Matrix.mulVec, dotProduct, SimpleGraph.adjMatrix_apply, cGraph_adj_iff]

/-- decoupling for `lam0I - A`: restriction to a component of `(lam0I-A_G)x` equals
`(lam0I-A_c)(x|_c)`. -/
lemma lamI_sub_adj_restrict (G : SimpleGraph (Fin n)) (c : G.ConnectedComponent) {lam0 : ℝ}
    (x : Fin n → ℝ) :
    compRest G c ((lam0 • (1 : Matrix (Fin n) (Fin n) ℝ) - (G.adjMatrix ℝ)) *ᵥ x)
      = (lam0 • (1 : Matrix c c ℝ) - (cGraph G c).adjMatrix ℝ) *ᵥ compRest G c x := by
  classical
  funext v
  have h1 := adj_restrict_mem G c x v
  simp only [compRest]
  have hlam1 : ((lam0 • (1 : Matrix (Fin n) (Fin n) ℝ) - (G.adjMatrix ℝ)) *ᵥ x) v.1
      = lam0 * x v.1 - ((G.adjMatrix ℝ) *ᵥ x) v.1 := by
    rw [mulVec_sub_any]
    simp [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Matrix.one_apply]
  have hlam2 : ((lam0 • (1 : Matrix c c ℝ) - (cGraph G c).adjMatrix ℝ) *ᵥ compRest G c x) v
      = lam0 * (compRest G c x) v - ((cGraph G c).adjMatrix ℝ *ᵥ compRest G c x) v := by
    rw [mulVec_sub_any]
    simp [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Matrix.one_apply]
  rw [hlam1, hlam2, h1]
  simp [compRest]

/-- if `x` is in the kernel of `lam0I - A_G` then its restriction to any component is in the
kernel of `lam0I - A_c`. -/
lemma compRest_ker (G : SimpleGraph (Fin n)) (c : G.ConnectedComponent) {lam0 : ℝ}
    (x : Fin n → ℝ) (hx : ((lam0 • (1 : Matrix (Fin n) (Fin n) ℝ) - (G.adjMatrix ℝ)) *ᵥ x) = 0) :
    ((lam0 • (1 : Matrix c c ℝ) - (cGraph G c).adjMatrix ℝ) *ᵥ compRest G c x) = 0 := by
  classical
  have h := lamI_sub_adj_restrict G c (lam0 := lam0) (x := x)
  rw [hx] at h
  have h0 : compRest G c (0 : Fin n → ℝ) = 0 := by
    funext v
    rfl
  rw [h0] at h
  exact h.symm

end
end Submission
