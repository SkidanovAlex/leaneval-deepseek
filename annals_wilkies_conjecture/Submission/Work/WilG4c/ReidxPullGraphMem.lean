/-
  WilG4c / ReidxPullGraphMem — the `Ω`-bookkeeping of the `(p+1)`-parameter reindexing of the
  `y`-pullback.

  The family whose graph is bounded here is

    `g w y = F i (w ∘ castSucc) (cons (w (last p)) (ψ · w y))`,

  i.e. the `y`-pullback of `F i` along the chart tuple `ψ`, with the distinguished `x`
  coordinate *moved out of the values and into the parameter space* — so that the resulting
  family has parameter block `Fin (p+1)` and variable block `Fin n`, while the ambient space
  `ℝ^{(p+1)+n+1} = ℝ^{p+n+2}` is the same one as `famGraph (F i) ⊆ ℝ^{p+(n+1)+1}`.

  The proof is a two-step assembly of existing `Ω`-bookkeeping lemmas:

  * **Reindexing** (`vieGraphMem`).  Moving the last variable `x` of a `(n+1)`-variable family
    into the parameter space is the coordinate permutation `Fin.cast` of the two index types
    `Fin (p + (n+1) + 1) ≃ Fin ((p+1) + n + 1)`, so the graph is the very same set on the same
    coordinates.  Coordinate pullback is one of the closure axioms of `Ω` (packaged as
    `Work.WilG4c.Subst`), and the two descriptions agree by `Work.WilG4c.reindex_famGraph`
    (indeed definitionally, since `famGraph (vie f) = graphOf (vieRead f)`).  Cost: `D + 2`
    and an additive format.

  * **Composition with the chart** (`Work.WilkG4c.famGraph_comp_single`).  `g` is
    `l ↦ (vie f) l (ψ · l ·)`, so the composition lemma applies verbatim with the chart tuple
    `ψ`, at a cost which is linear in the chart degree.

  Nothing here is specific to `S`; the file is `sorry`-free.  (`Work.WilG4c.vieClampGraph`
  contains the same reindexing, packaged together with a value clamp; the clamp is *not* used
  here.)
-/
import Mathlib
import Submission.Work.WilG4c.YPullback
import Submission.Work.WilG4c.StepLipHighAux
import Submission.Work.WilG4c.YbddAux
import Submission.Work.WilG4c.Subst
import Submission.Work.WilG4c.vieClampGraph

set_option autoImplicit false

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-- `Fin.snoc` of the restriction of `w` to the first `p` coordinates and its last value is `w`
again.  (This is the identity that lets the target family be read as the composition of the
regrouped family with the chart tuple.) -/
theorem fin_snoc_castSucc_last {p : ℕ} (w : Fin (p + 1) → ℝ) :
    Fin.snoc (fun j : Fin p => w (Fin.castSucc j)) (w (Fin.last p)) = w := by
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [Fin.snoc_castSucc]
  · rw [Fin.snoc_last]

/-- **Reindexing a family along the `x`-into-the-parameters move.**  If the graph of a family
member `f` of `(n+1)`-variable functions is `Ω F0 D`-bounded, then so is the graph of
`(w, y) ↦ f (w ∘ castSucc) (cons (w (last p)) y)`: the two graphs are the same set, read in the
two coordinate orders `Fin (p + (n+1) + 1)` and `Fin ((p+1) + n + 1)`. -/
theorem vieGraphMem (S : WilkiesDesign.SOMin) (p n : ℕ) :
    ∃ (a c : ℕ), ∀ (F0 D : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ),
      WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
      WilkiesDesign.CG.famGraph
        (fun (w : Fin (p + 1) → ℝ) (y : Fin n → ℝ) =>
          f (fun a : Fin p => w (Fin.castSucc a)) (Fin.cons (w (Fin.last p)) y))
        ∈ S.Ω (F0 + a) (D + c) ((p + 1) + n + 1) := by
  refine ⟨(p + (n + 1) + 1) + (((p + 1) + n + 1) + (p + (n + 1) + 1)) + 1 + 2, 2, ?_⟩
  intro F0 D f hf
  have hh : p + (n + 1) + 1 = (p + 1) + n + 1 := by omega
  -- the coordinate pullback of `famGraph f` along the identification of the two index types
  have hsub : {w : Fin ((p + 1) + n + 1) → ℝ |
      w ∘ (fun i : Fin (p + (n + 1) + 1) => Fin.cast hh i) ∈ WilkiesDesign.CG.famGraph f} ∈
      S.Ω (max (F0 + ((p + 1) + n + 1)) (((p + 1) + n + 1) + (p + (n + 1) + 1)) + 1
        + (p + (n + 1) + 1)) (D + 2) ((p + 1) + n + 1) :=
    Work.WilG4c.Subst S (fun i : Fin (p + (n + 1) + 1) => Fin.cast hh i) hf
  rw [Work.WilG4c.reindex_famGraph p n f hh] at hsub
  -- the reindexed graph is `graphOf (vieRead f)` definitionally
  have heq : WilkiesDesign.CG.famGraph
      (fun (w : Fin (p + 1) → ℝ) (y : Fin n → ℝ) =>
        f (fun a : Fin p => w (Fin.castSucc a)) (Fin.cons (w (Fin.last p)) y))
      = WilkiesDesign.graphOf (Work.WilG4c.vieRead f) := rfl
  rw [heq]
  exact Omega_mono_le S (by omega) (by omega) hsub

/-- The graph of the `(p+1)`-parameter reindexing of the `y`-pullback is `Ω`-bounded. -/
theorem ReidxPullGraphMem (S : WilkiesDesign.SOMin) (p n k : ℕ) (F0 Dg aψ Dgψ : ℕ)
    (F : Work.WilkG4c.Family k p (n + 1)) (ψ : Work.WilkG4c.ChartTuple (p + 1) n) (i : Fin k)
    (hG : WilkiesDesign.CG.famGraph (F i) ∈ S.Ω F0 Dg (p + (n + 1) + 1))
    (hψg : ∀ j, WilkiesDesign.CG.famGraph (ψ j) ∈ S.Ω aψ Dgψ ((p + 1) + n + 1)) :
    ∃ (F1 D1 : ℕ), WilkiesDesign.CG.famGraph
      (fun (w : Fin (p + 1) → ℝ) (y : Fin n → ℝ) =>
        F i (fun j : Fin p => w (Fin.castSucc j))
          (Fin.cons (w (Fin.last p))
            (fun j : Fin n =>
              ψ j (Fin.snoc (fun j' : Fin p => w (Fin.castSucc j')) (w (Fin.last p))) y)))
      ∈ S.Ω F1 D1 ((p + 1) + n + 1) := by
  -- 1. reindex `F i` as a family over `Fin (p+1)` parameters and `Fin n` variables
  obtain ⟨aV, cV, hV⟩ := vieGraphMem S p n
  have hvie : WilkiesDesign.CG.famGraph
      (fun (w : Fin (p + 1) → ℝ) (y : Fin n → ℝ) =>
        F i (fun a : Fin p => w (Fin.castSucc a)) (Fin.cons (w (Fin.last p)) y)) ∈
      S.Ω (F0 + aV) (Dg + cV) ((p + 1) + n + 1) := hV F0 Dg (F i) hG
  -- 2. compose with the chart tuple `ψ`
  obtain ⟨aC, cC, hC⟩ := famGraph_comp_single S (p + 1) n
  have hcomp := hC (F0 + aV) aψ (Dg + cV) Dgψ
    (fun (w : Fin (p + 1) → ℝ) (y : Fin n → ℝ) =>
      F i (fun a : Fin p => w (Fin.castSucc a)) (Fin.cons (w (Fin.last p)) y)) ψ hvie hψg
  refine ⟨(F0 + aV) + aψ + aC, (Dg + cV) + ((p + 1) + n) * Dgψ + cC, ?_⟩
  -- 3. the stated family is the composite, since `snoc (w ∘ castSucc) (w last) = w`
  have hfun : (fun (w : Fin (p + 1) → ℝ) (y : Fin n → ℝ) =>
        F i (fun j : Fin p => w (Fin.castSucc j))
          (Fin.cons (w (Fin.last p))
            (fun j : Fin n =>
              ψ j (Fin.snoc (fun j' : Fin p => w (Fin.castSucc j')) (w (Fin.last p))) y)))
      = (fun (l : Fin (p + 1) → ℝ) (z : Fin n → ℝ) =>
          (fun (w : Fin (p + 1) → ℝ) (y : Fin n → ℝ) =>
            F i (fun a : Fin p => w (Fin.castSucc a)) (Fin.cons (w (Fin.last p)) y))
          l (fun j => ψ j l z)) := by
    funext w y
    rw [fin_snoc_castSucc_last w]
  rw [hfun]
  exact hcomp

end Work.WilkG4c

namespace Work.WilG4c

/-- The graph of the `(p+1)`-parameter reindexing of the `y`-pullback is `Ω`-bounded.

This is the module-path spelling (`Submission.Work.WilG4c.ReidxPullGraphMem`) of the theorem
proved just above: the two names have the same statement and the same proof, so downstream
users may refer to either. -/
theorem ReidxPullGraphMem (S : WilkiesDesign.SOMin) (p n k : ℕ) (F0 Dg aψ Dgψ : ℕ)
    (F : Work.WilkG4c.Family k p (n + 1)) (ψ : Work.WilkG4c.ChartTuple (p + 1) n) (i : Fin k)
    (hG : WilkiesDesign.CG.famGraph (F i) ∈ S.Ω F0 Dg (p + (n + 1) + 1))
    (hψg : ∀ j, WilkiesDesign.CG.famGraph (ψ j) ∈ S.Ω aψ Dgψ ((p + 1) + n + 1)) :
    ∃ (F1 D1 : ℕ), WilkiesDesign.CG.famGraph
      (fun (w : Fin (p + 1) → ℝ) (y : Fin n → ℝ) =>
        F i (fun j : Fin p => w (Fin.castSucc j))
          (Fin.cons (w (Fin.last p))
            (fun j : Fin n =>
              ψ j (Fin.snoc (fun j' : Fin p => w (Fin.castSucc j')) (w (Fin.last p))) y)))
      ∈ S.Ω F1 D1 ((p + 1) + n + 1) :=
  Work.WilkG4c.ReidxPullGraphMem S p n k F0 Dg aψ Dgψ F ψ i hG hψg

end Work.WilG4c
