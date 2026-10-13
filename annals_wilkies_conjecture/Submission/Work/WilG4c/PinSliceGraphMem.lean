import Mathlib
import Submission.Work.WilG4c.Defs
import Submission.Work.WilG4c.YbddAux
import Submission.Work.WilG4c.graphOfCompGen
import Submission.Work.WilkG4c.FamGraphConstPtMem
import Submission.Work.WilkG4c.FamGraphTailMem

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG
open Work.WilG0 Work.WilG1

/-!
# `Work.WilG4c.PinSliceGraphMem` — `Ω`-membership of a pinned slice of a family

Let `f : ℝ^p × ℝ^{n+1} → ℝ` be a family (whose graph is `Ω`-bounded at format `F0` and degree
`D`) and let `pt : ℝ^p → ℝ` be an `Ω`-bounded function (format `A0`, degree `A`).  Then the
*pinned slice*

    `(l, u) ↦ f l (Fin.cons (pt l) u)`

of `f` — the first cube coordinate of `f` is pinned to the definable value `pt l`, the remaining
`n` coordinates are free — has an `Ω`-bounded graph in `ℝ^{p+n+1}`, with format bounded by a
constant and degree by a polynomial in `D` and `A`.

This is the `Ω`-bookkeeping of the substitution `x₀ ↦ pt l` into the first cube coordinate of a
family, which the `§5.3` assembly performs for every pin cell.

## The construction

Write `F := flatFun f : ℝ^{p+(n+1)} → ℝ`, so that `famGraph f = graphOf F` by definition.  The
substitution map

    `pinPhi pt : ℝ^{p+n} → ℝ^{p+(n+1)}`,   `w ↦ (l w, Fin.cons (pt (l w)) (u w))`

(with `l w` the first `p` and `u w` the last `n` coordinates of `w`) satisfies

    `famGraph (fun l u => f l (Fin.cons (pt l) u)) = graphOf (F ∘ pinPhi pt)`

(`flatFun_comp_pinPhi`), so the rectangular composition lemma `graphOfCompGen` applies, provided
every coordinate of `pinPhi pt` has an `Ω`-bounded graph.  There are `p + (n+1)` of them:
the `p` coordinates `w ↦ w i` and the last `n` coordinates `w ↦ w (natAdd p j)` are coordinate
hyperplanes (`Work.WilkG4c.graphOf_coord_mem`, format `p+n+1`, degree `1`), and the remaining
coordinate `w ↦ pt (l w)` is the pullback of `graphOf pt` along the projection to the first `p`
coordinates (`graphOf_projPar_mem`, format `A0 + K`, degree `A + 2`).  Feeding the common bounds
`max (A0 + K) (p+n+1)` and `max (A + 2) 1` into `graphOfCompGen` multiplies the `pt`-cost by the
number `p + (n+1)` of coordinates, which is exactly the polynomial in `(D, A)` of the statement.
-/

/-! ## 1. Pulling a graph back along a projection to the leading coordinates

`iotaPad p m` keeps the first `p` coordinates and sends the value coordinate to the last one, so
that the coordinate preimage of `graphOf α` along it is the graph of `α` read through the first
`p` coordinates.  This is `Work.WilkG4c.padGraph_mem` without the artificial `n + 1` shape of the
padding block, i.e. for an arbitrary number `m` of padded coordinates. -/

/-- The index map `Fin (p+1) → Fin (p+m+1)`: the first `p` coordinates stay put, the value
coordinate goes to the end. -/
def iotaPad (p m : ℕ) : Fin (p + 1) → Fin (p + m + 1) :=
  Fin.snoc (fun i : Fin p => (Fin.castAdd m i).castSucc) (Fin.last (p + m))

@[simp] theorem iotaPad_castSucc (p m : ℕ) (i : Fin p) :
    iotaPad p m (Fin.castSucc i) = (Fin.castAdd m i).castSucc := by
  simp [iotaPad]

@[simp] theorem iotaPad_last (p m : ℕ) : iotaPad p m (Fin.last p) = Fin.last (p + m) := by
  simp [iotaPad]

/-- **Padded graph.**  A graph of a function of `p` variables is `Ω`-bounded in `p + m + 1`
variables, the extra `m` coordinates being ignored. -/
theorem graphOf_projPar_mem (S : SOMin) {p m Fa Da : ℕ} {α : (Fin p → ℝ) → ℝ}
    (hα : graphOf α ∈ S.Ω Fa Da (p + 1)) :
    graphOf (fun y : Fin (p + m) → ℝ => α (fun i : Fin p => y (Fin.castAdd m i)))
      ∈ S.Ω (Fa + 2 * ((p + m + 1) + (p + 1)) + 1) (Da + 2) (p + m + 1) := by
  have h := GraphComp.subst_mem S (iotaPad p m) hα
  have hset : {x : Fin (p + m + 1) → ℝ | x ∘ iotaPad p m ∈ graphOf α}
      = graphOf (fun y : Fin (p + m) → ℝ => α (fun i : Fin p => y (Fin.castAdd m i))) := by
    ext z
    simp only [Set.mem_ofPred_eq, graphOf, Function.comp_apply, Fin.init_def,
      iotaPad_last, iotaPad_castSucc]
  rw [hset] at h
  exact h

/-! ## 2. The substitution map of the pinned slice

`pinPhi pt w` replaces the block of `n + 1` "cube" coordinates of `w` by the block whose first
entry is the definable value `pt (l w)` and whose remaining entries are the last `n` coordinates
of `w`. -/

/-- The substitution `(l, u) ↦ (l, Fin.cons (pt l) u)`. -/
def pinPhi {p n : ℕ} (pt : (Fin p → ℝ) → ℝ) :
    (Fin (p + n) → ℝ) → (Fin (p + (n + 1)) → ℝ) :=
  fun w => Fin.append (fun i : Fin p => w (Fin.castAdd n i))
    (Fin.cons (pt (fun i : Fin p => w (Fin.castAdd n i))) (fun j : Fin n => w (Fin.natAdd p j)))

@[simp] theorem pinPhi_castAdd {p n : ℕ} (pt : (Fin p → ℝ) → ℝ) (w : Fin (p + n) → ℝ)
    (i : Fin p) : pinPhi pt w (Fin.castAdd (n + 1) i) = w (Fin.castAdd n i) := by
  simp [pinPhi, Fin.append_left]

@[simp] theorem pinPhi_natAdd_zero {p n : ℕ} (pt : (Fin p → ℝ) → ℝ) (w : Fin (p + n) → ℝ) :
    pinPhi pt w (Fin.natAdd p 0) = pt (fun i : Fin p => w (Fin.castAdd n i)) := by
  simp [pinPhi, Fin.append_right]

@[simp] theorem pinPhi_natAdd_succ {p n : ℕ} (pt : (Fin p → ℝ) → ℝ) (w : Fin (p + n) → ℝ)
    (j : Fin n) : pinPhi pt w (Fin.natAdd p (Fin.succ j)) = w (Fin.natAdd p j) := by
  simp [pinPhi, Fin.append_right]

/-- The flattened pinned slice is the flattened family composed with `pinPhi`. -/
theorem flatFun_comp_pinPhi {p n : ℕ} (pt : (Fin p → ℝ) → ℝ)
    (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) :
    Work.WilkG4c.flatFun (fun (l : Fin p → ℝ) (u : Fin n → ℝ) => f l (Fin.cons (pt l) u))
      = Work.WilkG4c.flatFun f ∘ pinPhi pt := by
  funext w
  simp only [Function.comp_apply, Work.WilkG4c.flatFun, pinPhi, Fin.append_left,
    Fin.append_right]

/-! ## 3. The polynomial bound on the degree -/

/-- The degree polynomial of the conclusion: `(p + (n+1)) * A + D + const`. -/
def pinPoly (p n C₂ : ℕ) : MvPolynomial (Fin 2) ℕ :=
  MvPolynomial.C (p + (n + 1)) * MvPolynomial.X 1 + MvPolynomial.X 0
    + MvPolynomial.C ((p + (n + 1)) * 2 + C₂)

theorem pinPoly_eval (p n C₂ D A : ℕ) :
    MvPolynomial.eval ![D, A] (pinPoly p n C₂)
      = (p + (n + 1)) * A + D + ((p + (n + 1)) * 2 + C₂) := by
  simp [pinPoly, MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_X]

/-! ## 4. The main theorem -/

theorem PinSliceGraphMem (S : WilkiesDesign.SOMin) (p n F0 A0 : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ (D A : ℕ) (pt : (Fin p → ℝ) → ℝ)
        (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ),
        WilkiesDesign.graphOf pt ∈ S.Ω A0 A (p + 1) →
        WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
        WilkiesDesign.CG.famGraph
            (fun (l : Fin p → ℝ) (u : Fin n → ℝ) => f l (Fin.cons (pt l) u)) ∈
          S.Ω a (MvPolynomial.eval ![D, A] b) (p + n + 1) := by
  obtain ⟨C₁, C₂, hcomp⟩ := graphOfCompGen S (p + (n + 1)) (p + n)
  refine ⟨F0 + max (A0 + 2 * ((p + n + 1) + (p + 1)) + 1) (p + n + 1) + C₁,
    pinPoly p n C₂, ?_⟩
  intro D A pt f hpt hf
  -- every coordinate of `pinPhi pt` has an `Ω`-bounded graph at the common bounds
  have hcoord : ∀ j : Fin (p + (n + 1)),
      graphOf (fun w : Fin (p + n) → ℝ => pinPhi pt w j) ∈
        S.Ω (max (A0 + 2 * ((p + n + 1) + (p + 1)) + 1) (p + n + 1))
            (max (A + 2) 1) (p + n + 1) := by
    intro j
    refine Fin.addCases (fun i => ?_) (fun k => ?_) j
    · -- the `p` parameter coordinates: projections
      have heq : (fun w : Fin (p + n) → ℝ => pinPhi pt w (Fin.castAdd (n + 1) i))
          = (fun w : Fin (p + n) → ℝ => w (Fin.castAdd n i)) := by
        funext w; simp
      rw [heq]
      exact Omega.mono (Work.WilkG4c.graphOf_coord_mem S (Fin.castAdd n i))
        (le_max_right _ _) (le_max_right _ _)
    · refine Fin.cases ?_ (fun j' => ?_) k
      · -- the pinned coordinate: the graph of `pt` read along the projection to the parameters
        have heq : (fun w : Fin (p + n) → ℝ => pinPhi pt w (Fin.natAdd p 0))
            = (fun w : Fin (p + n) → ℝ => pt (fun i : Fin p => w (Fin.castAdd n i))) := by
          funext w; simp
        rw [heq]
        exact Omega.mono (graphOf_projPar_mem (S := S) (m := n) hpt)
          (le_max_left _ _) (le_max_left _ _)
      · -- the remaining cube coordinates: projections
        have heq : (fun w : Fin (p + n) → ℝ => pinPhi pt w (Fin.natAdd p (Fin.succ j')))
            = (fun w : Fin (p + n) → ℝ => w (Fin.natAdd p j')) := by
          funext w; simp
        rw [heq]
        exact Omega.mono (Work.WilkG4c.graphOf_coord_mem S (Fin.natAdd p j'))
          (le_max_right _ _) (le_max_right _ _)
  have hres := hcomp F0 (max (A0 + 2 * ((p + n + 1) + (p + 1)) + 1) (p + n + 1)) D
    (max (A + 2) 1) (Work.WilkG4c.flatFun f) (pinPhi pt) hf hcoord
  -- identify the composite with the pinned slice
  have hset : famGraph (fun (l : Fin p → ℝ) (u : Fin n → ℝ) => f l (Fin.cons (pt l) u))
      = graphOf (Work.WilkG4c.flatFun f ∘ pinPhi pt) := by
    rw [Work.WilkG4c.famGraph_eq_graphOf_flatFun, flatFun_comp_pinPhi pt f]
  rw [← hset] at hres
  refine Omega.mono hres (le_of_eq rfl) ?_
  rw [pinPoly_eval]
  have hmax : max (A + 2) 1 = A + 2 := by omega
  rw [hmax]
  have hmul : (p + (n + 1)) * (A + 2) = (p + (n + 1)) * A + (p + (n + 1)) * 2 :=
    Nat.mul_add _ _ _
  omega

end Work.WilG4c
