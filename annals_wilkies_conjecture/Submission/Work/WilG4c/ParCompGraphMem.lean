import Mathlib
import Submission.Work.WilG4c.Defs
import Submission.Work.WilG4c.YbddAux
import Submission.Work.WilG4c.graphOfCompGen

/-!
## `Work.WilG4c.ParCompGraphMem`

`Ω`-closure of the *parametric* composition of a family: if the graph of the family

    `f : ℝ^{p'} × ℝ^n → ℝ`    (`famGraph f ⊆ ℝ^{p'+n+1}`, format `F0`, degree `D`)

is `Ω`-definable and each of the `p'` coordinate functions of the parameter map

    `g : ℝ^p → ℝ^{p'}`

has an `Ω`-definable graph (format `A0`, degree `A`, ambient dimension `p+1`), then the graph
of the composed family

    `(l, u) ↦ f (g l) u`

is `Ω`-definable, with format `F0 + max(A0 + 2*((p+n+1)+(p+1)) + 1, (p+n)+1) + C₁` and degree
`D + (p'+n)*(A+2) + C₂`.

The construction is the *rectangular* composition lemma `Work.WilG4c.graphOfCompGen` applied to

* the uncurried family `pcgm_compGFam f : ℝ^{p'+n} → ℝ` (`graphOf (pcgm_compGFam f)` is by
  definition `famGraph f`), and
* the index map `pcgm_parIdx g : ℝ^{p+n} → ℝ^{p'+n}`, `z ↦ (g (first p coordinates of z),
  remaining n coordinates of z)`, whose `p'` "parameter" coordinates are coordinate preimages
  of the graphs `graphOf (fun l => g l j)` (`GraphComp.subst_mem`, implemented by the index map
  `pcgm_liftParIdx`) and whose `n` remaining coordinates are plain coordinate projections
  (`pcgm_graphOf_projCoord_mem`, an affine hyperplane).

The only combinatorial work is the identity `pcgm_famGraph_parComp` saying that the graph of
`(l,u) ↦ f (g l) u` is the graph of `pcgm_compGFam f ∘ pcgm_parIdx g`.
-/

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-! ## 1. The uncurried family and the parameter substitution -/

/-- The *uncurried* family of `famGraph f`: `famGraph f = graphOf (pcgm_compGFam f)`. -/
def pcgm_compGFam {p' n : ℕ} (f : (Fin p' → ℝ) → (Fin n → ℝ) → ℝ) :
    (Fin (p' + n) → ℝ) → ℝ :=
  fun z => f (fun i : Fin p' => z (Fin.castAdd n i)) (fun j : Fin n => z (Fin.natAdd p' j))

/-- The parameter substitution `z ↦ (g (first p coordinates of z), remaining n coordinates
of z)`, going from `ℝ^{p+n}` (the ambient space of the composed family) to `ℝ^{p'+n}` (the
ambient space of the family `f`). -/
def pcgm_parIdx {p n p' : ℕ} (g : (Fin p → ℝ) → (Fin p' → ℝ)) :
    (Fin (p + n) → ℝ) → (Fin (p' + n) → ℝ) :=
  fun z => Fin.append (g (fun a : Fin p => z (Fin.castAdd n a)))
    (fun j : Fin n => z (Fin.natAdd p j))

/-- Index map presenting the "parameter" coordinates of `pcgm_parIdx g` as the coordinate
preimage, along `pcgm_liftParIdx`, of the graph of `fun l => g l j`: it is the identity on the
first `p` coordinates and sends the last coordinate to the last coordinate (the value of `g`). -/
def pcgm_liftParIdx (p n : ℕ) : Fin (p + 1) → Fin (p + n + 1) :=
  Fin.snoc (fun a : Fin p => (Fin.castAdd n a).castSucc) (Fin.last (p + n))

theorem pcgm_graphOf_compGFam {p' n : ℕ} (f : (Fin p' → ℝ) → (Fin n → ℝ) → ℝ) :
    graphOf (pcgm_compGFam f) = CG.famGraph f := by
  rw [CG.famGraph]; rfl

/-- The graph of the parametrically composed family is the graph of the composite
`pcgm_compGFam f ∘ pcgm_parIdx g`.  This is the only combinatorial identity of the proof: it
uses `Fin.append_left`/`Fin.append_right` to see that `pcgm_parIdx g z` reads the first `p`
coordinates of `z` through `g` and keeps the last `n` of them. -/
theorem pcgm_famGraph_parComp {p p' n : ℕ} (f : (Fin p' → ℝ) → (Fin n → ℝ) → ℝ)
    (g : (Fin p → ℝ) → (Fin p' → ℝ)) :
    CG.famGraph (fun (l : Fin p → ℝ) (u : Fin n → ℝ) => f (g l) u)
      = graphOf (pcgm_compGFam f ∘ pcgm_parIdx g) := by
  ext z
  simp only [CG.famGraph, graphOf, Set.mem_ofPred_eq, Fin.init_def, Function.comp_def,
    pcgm_compGFam, pcgm_parIdx, Fin.append_left, Fin.append_right]

/-- The coordinate graph of a "parameter" coordinate of `pcgm_parIdx g` is the coordinate
preimage, along `pcgm_liftParIdx`, of the graph `graphOf (fun l => g l j)`. -/
theorem pcgm_graphOf_parIdx_fst {p p' n : ℕ} (g : (Fin p → ℝ) → (Fin p' → ℝ)) (i' : Fin p') :
    graphOf (fun z : Fin (p + n) → ℝ => pcgm_parIdx g z (Fin.castAdd n i'))
      = {x : Fin (p + n + 1) → ℝ |
          x ∘ pcgm_liftParIdx p n ∈ graphOf (fun l : Fin p → ℝ => g l i')} := by
  ext x
  simp only [graphOf, Set.mem_ofPred_eq, Function.comp_def, pcgm_parIdx, pcgm_liftParIdx,
    Fin.snoc_castSucc, Fin.snoc_last, Fin.append_left, Fin.init_def]

/-- The graph of a coordinate projection `z ↦ z k` is the hyperplane `x (last N) = x k`, cut
out by a *linear* polynomial; hence it is `Ω`-definable at format `N+1` and degree `1`. -/
theorem pcgm_graphOf_projCoord_mem (S : SOMin) (N : ℕ) (k : Fin N) :
    graphOf (fun z : Fin N → ℝ => z k) ∈ S.Ω (N + 1) 1 (N + 1) := by
  have h : {x : Fin (N + 1) → ℝ | x (Fin.last N) = x (Fin.castSucc k)} ∈
      S.Ω (N + 1) 1 (N + 1) := by
    simpa using Work.WilG1.Omega.coordEq_mem (S := S) (n := N + 1) 0 (Fin.last N)
      (Fin.castSucc k)
  have hset : graphOf (fun z : Fin N → ℝ => z k) =
      {x : Fin (N + 1) → ℝ | x (Fin.last N) = x (Fin.castSucc k)} := by
    ext z; simp [graphOf, Fin.init_def]
  rw [hset]; exact h

/-! ## 2. The main statement -/

theorem ParCompGraphMem (S : WilkiesDesign.SOMin) (p p' n F0 A0 : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ (D A : ℕ) (f : (Fin p' → ℝ) → (Fin n → ℝ) → ℝ)
        (g : (Fin p → ℝ) → (Fin p' → ℝ)),
        WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p' + n + 1) →
        (∀ j : Fin p', WilkiesDesign.graphOf (fun l : Fin p → ℝ => g l j) ∈ S.Ω A0 A (p + 1)) →
        WilkiesDesign.CG.famGraph (fun (l : Fin p → ℝ) (u : Fin n → ℝ) => f (g l) u) ∈
          S.Ω a (MvPolynomial.eval ![D, A] b) (p + n + 1) := by
  obtain ⟨C₁, C₂, hcomp⟩ := graphOfCompGen S (p' + n) (p + n)
  refine ⟨F0 + max (A0 + 2 * ((p + n + 1) + (p + 1)) + 1) ((p + n) + 1) + C₁,
      MvPolynomial.X 0 + MvPolynomial.C (p' + n) * MvPolynomial.X 1 +
        MvPolynomial.C ((p' + n) * 2 + C₂), ?_⟩
  intro D A f g hf hg
  -- the coordinate graphs of `pcgm_parIdx g` at the common format and degree
  have hcoord : ∀ i : Fin (p' + n),
      graphOf (fun z : Fin (p + n) → ℝ => pcgm_parIdx g z i) ∈
        S.Ω (max (A0 + 2 * ((p + n + 1) + (p + 1)) + 1) ((p + n) + 1)) (A + 2)
          (p + n + 1) := by
    intro i
    refine Fin.addCases (fun i' => ?_) (fun j => ?_) i
    · -- the `p'` parameter coordinates: coordinate preimages of the graphs of `g`
      have h : graphOf (fun z : Fin (p + n) → ℝ => pcgm_parIdx g z (Fin.castAdd n i')) ∈
          S.Ω (A0 + 2 * ((p + n + 1) + (p + 1)) + 1) (A + 2) (p + n + 1) := by
        rw [pcgm_graphOf_parIdx_fst g i']
        exact Work.WilG4c.GraphComp.subst_mem S (pcgm_liftParIdx p n) (hg i')
      exact Work.WilG1.Omega.mono h (le_max_left _ _) le_rfl
    · -- the `n` remaining coordinates: plain projections
      have hset : (fun z : Fin (p + n) → ℝ => pcgm_parIdx g z (Fin.natAdd p' j)) =
          (fun z : Fin (p + n) → ℝ => z (Fin.natAdd p j)) := by
        funext z; simp [pcgm_parIdx, Fin.append_right]
      rw [hset]
      exact Work.WilG1.Omega.mono (pcgm_graphOf_projCoord_mem S (p + n) (Fin.natAdd p j))
        (le_max_right _ _) (by omega)
  -- the rectangular composition lemma
  have hcomp' := hcomp F0 (max (A0 + 2 * ((p + n + 1) + (p + 1)) + 1) ((p + n) + 1)) D (A + 2)
    (pcgm_compGFam f) (pcgm_parIdx g) ?_ hcoord
  · -- identify the composite with the graph of the parametrically composed family
    rw [pcgm_famGraph_parComp]
    refine Work.WilG1.Omega.mono hcomp' le_rfl ?_
    have hb : MvPolynomial.eval ![D, A]
        (MvPolynomial.X 0 + MvPolynomial.C (p' + n) * MvPolynomial.X 1 +
          MvPolynomial.C ((p' + n) * 2 + C₂)) =
        D + (p' + n) * A + ((p' + n) * 2 + C₂) := by
      simp [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_X]
    rw [hb]
    have hmul : (p' + n) * (A + 2) = (p' + n) * A + (p' + n) * 2 := Nat.mul_add _ _ _
    rw [hmul]
    omega
  · -- `graphOf (pcgm_compGFam f) = famGraph f`
    rwa [pcgm_graphOf_compGFam]

end Work.WilG4c
