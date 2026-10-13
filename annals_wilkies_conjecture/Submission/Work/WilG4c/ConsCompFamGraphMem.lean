import Mathlib
import Submission.Work.WilG4c.graphOfCompGen
import Submission.Work.WilG1.Basic
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilG4c.LipDefs

/-!
## `Work.WilG4c.ConsCompFamGraphMem`

`Ω`-closure of the BNZ §5 "restricted composition" of a family with a curve: if the graph of
the family `f` (in `p` parameters and `n+1` variables) is `Ω`-definable, and each coordinate of
the curve `γ` has an `Ω`-definable graph (in `p+1` variables), then the graph of

    `(l, u) ↦ f l (Fin.cons (u 0) (γ l (u 0)))`

is `Ω`-definable, with format `F0 + Ag + A` and degree `D + (p + (n+1)) * (Dg+1) + C`, for
constants `A, C` depending only on `S`, `p`, `n`.

The construction is the rectangular composition lemma `Work.WilG4c.graphOfCompGen` applied to
the *uncurried* family

    `g z = f (z ∘ castAdd (n+1)) (z ∘ natAdd p)`      (so `famGraph f = graphOf g`)

and the index map

    `φ w = Fin.append (Fin.init w) (Fin.cons (w (last p)) (γ (init w) (last p)))`,

whose coordinates are: the `p` projections `w ↦ w i` (`i : Fin p`), the projection
`w ↦ w (last p)` (the coordinate `0` of the second block, i.e. the variable `u 0`), and the `n`
curve coordinates `w ↦ γ (init w) (last p) j`.  The first `p+1` are coordinate hyperplanes
(degree `≤ 1`), the last `n` have format `Ag`/degree `Dg` by hypothesis; feeding the common
bound `max Ag (p+1+1)`, `max Dg 1` into `graphOfCompGen` multiplies the curve cost by the number
`p + (n+1)` of coordinates.  The remaining ingredient is the purely combinatorial identity that
`g ∘ φ` is the uncurried restricted composition.
-/

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-- The *uncurried* family of `famGraph f`: `famGraph f = graphOf (compG f)` by definition. -/
def compG {p n : ℕ} (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) :
    (Fin (p + (n + 1)) → ℝ) → ℝ :=
  fun z => f (fun i => z (Fin.castAdd (n + 1) i)) (fun j => z (Fin.natAdd p j))

/-- In the coordinates `(l, u)` of the source (`l : ℝ^p`, `u : ℝ^1`), the map taking the whole
parameter point `w` to the point `(l, Fin.cons (u 0) (γ l (u 0)))` of `ℝ^{p+(n+1)}` on which
the uncurried family `compG f` is evaluated. -/
def compPhi {p n : ℕ} (γ : (Fin p → ℝ) → ℝ → (Fin n → ℝ)) :
    (Fin (p + 1) → ℝ) → (Fin (p + (n + 1)) → ℝ) :=
  fun w => Fin.append (Fin.init w)
    (Fin.cons (w (Fin.last p))
      (fun j : Fin n => γ (fun a : Fin p => w (Fin.castSucc a)) (w (Fin.last p)) j))

/-- `Fin`-bookkeeping: the `famGraph` of the restricted composition is the graph of
`compG f ∘ compPhi γ`.  Both sides are the same set of points `z : ℝ^{p+1+1}`; the two
spellings of the first coordinates (`z ∘ castSucc` versus `Fin.init z`) coincide. -/
theorem famGraph_comp_phi_eq (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (γ : (Fin p → ℝ) → ℝ → (Fin n → ℝ)) :
    WilkiesDesign.CG.famGraph
        (fun (l : Fin p → ℝ) (u : Fin 1 → ℝ) => f l (Fin.cons (u 0) (γ l (u 0))))
      = WilkiesDesign.graphOf (compG f ∘ compPhi γ) := by
  ext z
  simp only [Set.mem_ofPred_eq, famGraph, graphOf, compG, compPhi, Function.comp_apply,
    Fin.append_left, Fin.append_right, Fin.init]
  exact Iff.rfl

/-- The graph of a coordinate projection `w ↦ w k` is the hyperplane `z (last M) = z k`, cut
out by a *linear* polynomial; hence it is `Ω`-definable at format `M+1` and degree `1`. -/
theorem graphOf_projCoord_mem (S : SOMin) (M : ℕ) (k : Fin M) :
    WilkiesDesign.graphOf (fun w : Fin M → ℝ => w k) ∈ S.Ω (M + 1) 1 (M + 1) := by
  have h : {x : Fin (M + 1) → ℝ | x (Fin.last M) = x (Fin.castSucc k)} ∈
      S.Ω (M + 1) 1 (M + 1) := by
    simpa using Work.WilG1.Omega.coordEq_mem (S := S) (n := M + 1) 0 (Fin.last M)
      (Fin.castSucc k)
  have hset : WilkiesDesign.graphOf (fun w : Fin M → ℝ => w k)
      = {x : Fin (M + 1) → ℝ | x (Fin.last M) = x (Fin.castSucc k)} := by
    ext z; simp [graphOf, Fin.init]
  rw [hset]; exact h

theorem ConsCompFamGraphMem (S : WilkiesDesign.SOMin) (p n : ℕ) :
    ∃ (A C : ℕ), ∀ (F0 D Ag Dg : ℕ)
      (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
      (γ : (Fin p → ℝ) → ℝ → (Fin n → ℝ)),
      WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
      (∀ j : Fin n, WilkiesDesign.graphOf (fun w : Fin (p + 1) → ℝ =>
          γ (fun a => w (Fin.castSucc a)) (w (Fin.last p)) j) ∈ S.Ω Ag Dg ((p + 1) + 1)) →
      WilkiesDesign.CG.famGraph (fun (l : Fin p → ℝ) (u : Fin 1 → ℝ) =>
          f l (Fin.cons (u 0) (γ l (u 0)))) ∈
        S.Ω (F0 + Ag + A) (D + (p + (n + 1)) * (Dg + 1) + C) (p + 1 + 1) := by
  obtain ⟨C₁, C₂, hcomp⟩ := Work.WilG4c.graphOfCompGen S (p + (n + 1)) (p + 1)
  refine ⟨(p + 1 + 1) + C₁, C₂, ?_⟩
  intro F0 D Ag Dg f γ hf hγ
  -- `famGraph f` is `graphOf` of the uncurried family
  have hgph : WilkiesDesign.graphOf (compG f) ∈ S.Ω F0 D (p + (n + 1) + 1) := hf
  -- every coordinate of `compPhi γ` has an `Ω`-definable graph at the common bounds
  have hcoord : ∀ i : Fin (p + (n + 1)),
      WilkiesDesign.graphOf (fun w : Fin (p + 1) → ℝ => compPhi γ w i) ∈
        S.Ω (max Ag (p + 1 + 1)) (max Dg 1) (p + 1 + 1) := by
    intro i
    refine Fin.addCases (fun i' => ?_) (fun k => ?_) i
    · -- first block: the projection `w ↦ w i'`
      have heq : (fun w : Fin (p + 1) → ℝ => compPhi γ w (Fin.castAdd (n + 1) i'))
          = (fun w : Fin (p + 1) → ℝ => w (Fin.castSucc i')) := by
        funext w; simp [compPhi, Fin.init]
      rw [heq]
      exact Work.WilG1.Omega.mono (graphOf_projCoord_mem S (p + 1) (Fin.castSucc i'))
        (le_max_right _ _) (le_max_right _ _)
    · refine Fin.cases ?_ (fun j => ?_) k
      · -- the coordinate `0` of the second block: the projection `w ↦ w (last p)`
        have heq : (fun w : Fin (p + 1) → ℝ => compPhi γ w (Fin.natAdd p 0))
            = (fun w : Fin (p + 1) → ℝ => w (Fin.last p)) := by
          funext w; simp [compPhi]
        rw [heq]
        exact Work.WilG1.Omega.mono (graphOf_projCoord_mem S (p + 1) (Fin.last p))
          (le_max_right _ _) (le_max_right _ _)
      · -- the curve coordinates: the hypothesis on `γ`
        have heq : (fun w : Fin (p + 1) → ℝ => compPhi γ w (Fin.natAdd p (Fin.succ j)))
            = (fun w : Fin (p + 1) → ℝ =>
                γ (fun a : Fin p => w (Fin.castSucc a)) (w (Fin.last p)) j) := by
          funext w; simp [compPhi]
        rw [heq]
        exact Work.WilG1.Omega.mono (hγ j) (le_max_left _ _) (le_max_left _ _)
  have hres := hcomp F0 (max Ag (p + 1 + 1)) D (max Dg 1) (compG f) (compPhi γ) hgph hcoord
  rw [← famGraph_comp_phi_eq p n f γ] at hres
  refine Work.WilG1.Omega.mono hres ?_ ?_
  · omega
  · have h : max Dg 1 ≤ Dg + 1 := by omega
    have := Nat.mul_le_mul_left (p + (n + 1)) h
    omega

end Work.WilG4c
