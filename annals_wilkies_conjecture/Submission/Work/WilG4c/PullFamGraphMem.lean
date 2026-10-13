import Mathlib
import Submission.Work.WilG4c.AlSliceBase
import Submission.Work.WilG4a.CD.thinCellParam

/-!
## `Work.WilG4c.PullFamGraphMem`

Pulling a family graph back along an `Ω`-definable parametrisation.

Let `f : ℝ^p × ℝ^{n+1} → ℝ` be a family whose graph `famGraph f ⊆ ℝ^{p+(n+1)+1}` is
`Ω F0 D`-definable, and let `Ψ : ℝ^{p'} → ℝ^p` be a parametrisation whose graph
`paramGraph Ψ ⊆ ℝ^{p'+p}` is `Ω F0 D`-definable.  Then the graph of the pulled-back family

    `(u, y) ↦ f (Ψ u) y`

is `Ω`-definable with format and degree depending polynomially on `D` only (format `O(1)`,
degree `≤ D + D + 4`).

### Construction

Work in `ℝ^{(p'+(n+1)+1)+p}` with layout `(u, y, t, l)`: the first `p'` coordinates are `u`, the
next `n+1` are `y`, coordinate `p'+(n+1)` is the *value* `t` of the family, and the last `p`
coordinates are the "intermediate" parameter vector `l`.

* `sigF` selects `(l, y, t)` out of `(u, y, t, l)`; the pullback `setF` of `famGraph f` along it
  expresses `t = f l y`.
* `sigPsi` selects `(u, l)` out of `(u, y, t, l)`; the pullback `setPsi` of `paramGraph Ψ` along
  it expresses `l = Ψ u`.

Both pullbacks are substitution atoms (`Work.WilG4a.subst_mem`, degree `D + 2`, format
`F0 + 2*(ambient + source) + 1`).  Their intersection is projected away from the `p`
coordinates `l` (`Work.WilG0.projLastIter`), and the result is exactly the graph of the
pulled-back family — the set-theoretic identity `projLastIter_setF_inter_setPsi`.
-/

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

open Work.WilG0

namespace PullFamGraphMemAux

/-! ### The two coordinate substitutions -/

/-- In `ℝ^{(p'+(n+1)+1)+p}` with layout `(u, y, t, l)`, the substitution selecting
`(l, y, t)`: the `p` coordinates `l` (the last block), the `n+1` coordinates `y` (middle of the
`u`-block) and the value coordinate `t` (coordinate `p'+(n+1)`). -/
def sigF (p p' n : ℕ) : Fin (p + (n + 1) + 1) → Fin ((p' + (n + 1) + 1) + p) :=
  Fin.snoc
    (Fin.addCases
      (fun i : Fin p => Fin.natAdd (p' + (n + 1) + 1) i)
      (fun j : Fin (n + 1) => Fin.castAdd p (Fin.castSucc (Fin.natAdd p' j))))
    (Fin.castAdd p (Fin.last (p' + (n + 1))))

/-- In `ℝ^{(p'+(n+1)+1)+p}` with layout `(u, y, t, l)`, the substitution selecting `(u, l)`:
the `p'` coordinates `u` (the initial segment of the `u`-block) and the `p` coordinates `l`
(the last block). -/
def sigPsi (p p' n : ℕ) : Fin (p' + p) → Fin ((p' + (n + 1) + 1) + p) :=
  Fin.append
    (fun i : Fin p' => Fin.castAdd p (Fin.castSucc (Fin.castAdd (n + 1) i)))
    (fun j : Fin p => Fin.natAdd (p' + (n + 1) + 1) j)

/-- The `y`-block of a point of `ℝ^{(p'+(n+1)+1)}`, read in layout `(u, y, t)`. -/
def glueY (p' n : ℕ) (x : Fin (p' + (n + 1) + 1) → ℝ) : Fin (n + 1) → ℝ :=
  fun j => x (Fin.castSucc (Fin.natAdd p' j))

/-- The `u`-block of a point of `ℝ^{(p'+(n+1)+1)}`, read in layout `(u, y, t)`. -/
def glueU (p' n : ℕ) (x : Fin (p' + (n + 1) + 1) → ℝ) : Fin p' → ℝ :=
  fun i => x (Fin.castSucc (Fin.castAdd (n + 1) i))

@[simp] theorem sigF_castSucc (p p' n : ℕ) (k : Fin (p + (n + 1))) :
    sigF p p' n (Fin.castSucc k) =
      Fin.addCases
        (fun i : Fin p => Fin.natAdd (p' + (n + 1) + 1) i)
        (fun j : Fin (n + 1) => Fin.castAdd p (Fin.castSucc (Fin.natAdd p' j))) k :=
  Fin.snoc_castSucc _ _ k

@[simp] theorem sigF_last (p p' n : ℕ) :
    sigF p p' n (Fin.last (p + (n + 1))) = Fin.castAdd p (Fin.last (p' + (n + 1))) :=
  Fin.snoc_last _ _

/-! ### The two identities describing the glued vector -/

/-- On the glued vector `snocIt _ p x w`, the substitution `sigF` reads `(w, y, x_last)`. -/
theorem snocIt_sigF (p p' n : ℕ) (x : Fin (p' + (n + 1) + 1) → ℝ) (w : Fin p → ℝ) :
    snocIt (p' + (n + 1) + 1) p x w ∘ sigF p p' n =
      Fin.snoc (Fin.append w (glueY p' n x)) (x (Fin.last (p' + (n + 1)))) := by
  funext k
  refine Fin.lastCases ?_ ?_ k
  · rw [Function.comp_apply, sigF_last, snocIt_castAdd, Fin.snoc_last]
  · intro k'
    rw [Function.comp_apply, sigF_castSucc]
    refine Fin.addCases ?_ ?_ k'
    · intro i
      rw [Fin.addCases_left, snocIt_natAdd, Fin.snoc_castSucc, Fin.append_left]
    · intro j
      rw [Fin.addCases_right, snocIt_castAdd, Fin.snoc_castSucc, Fin.append_right]
      rfl

/-- On the glued vector `snocIt _ p x w`, the substitution `sigPsi` reads `(u, w)`. -/
theorem snocIt_sigPsi (p p' n : ℕ) (x : Fin (p' + (n + 1) + 1) → ℝ) (w : Fin p → ℝ) :
    snocIt (p' + (n + 1) + 1) p x w ∘ sigPsi p p' n =
      Fin.append (glueU p' n x) w := by
  funext k
  refine Fin.addCases ?_ ?_ k
  · intro i
    simp only [Function.comp_apply, sigPsi, Fin.append_left, snocIt_castAdd, glueU]
  · intro j
    simp only [Function.comp_apply, sigPsi, Fin.append_right, snocIt_natAdd]

/-! ### The two pulled-back sets -/

/-- The pullback of `famGraph f` along `sigF`. -/
def setF (p p' n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) :
    Set (Fin ((p' + (n + 1) + 1) + p) → ℝ) :=
  {z | z ∘ sigF p p' n ∈ famGraph f}

/-- The pullback of `paramGraph Ψ` along `sigPsi`. -/
def setPsi (p p' n : ℕ) (Ψ : (Fin p' → ℝ) → (Fin p → ℝ)) :
    Set (Fin ((p' + (n + 1) + 1) + p) → ℝ) :=
  {z | z ∘ sigPsi p p' n ∈ Work.WilG4a.CD.paramGraph Ψ}

/-- Membership in the pulling-back set of `famGraph f`: on `snocIt _ p x w` it says
`x_last = f w y`. -/
theorem mem_setF (p p' n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (x : Fin (p' + (n + 1) + 1) → ℝ) (w : Fin p → ℝ) :
    snocIt (p' + (n + 1) + 1) p x w ∈ setF p p' n f ↔
      x (Fin.last (p' + (n + 1))) = f w (glueY p' n x) := by
  show (snocIt (p' + (n + 1) + 1) p x w ∘ sigF p p' n ∈ famGraph f) ↔ _
  rw [snocIt_sigF]
  simp only [famGraph, graphOf, Set.mem_ofPred_eq, Fin.init_def, Fin.snoc_castSucc,
    Fin.snoc_last, Fin.append_left, Fin.append_right, glueY]
  exact Iff.rfl

/-- Membership in the pulling-back set of `paramGraph Ψ`: on `snocIt _ p x w` it says
`w = Ψ u`. -/
theorem mem_setPsi (p p' n : ℕ) (Ψ : (Fin p' → ℝ) → (Fin p → ℝ))
    (x : Fin (p' + (n + 1) + 1) → ℝ) (w : Fin p → ℝ) :
    snocIt (p' + (n + 1) + 1) p x w ∈ setPsi p p' n Ψ ↔ w = Ψ (glueU p' n x) := by
  show (snocIt (p' + (n + 1) + 1) p x w ∘ sigPsi p p' n ∈ Work.WilG4a.CD.paramGraph Ψ) ↔ _
  rw [snocIt_sigPsi]
  simp only [Work.WilG4a.CD.paramGraph, Set.mem_ofPred_eq]
  have hcomp : (Fin.append (glueU p' n x) w) ∘ Fin.castAdd p = glueU p' n x := by
    funext i; rw [Function.comp_apply, Fin.append_left]
  rw [hcomp]
  simp only [Fin.append_right]
  constructor
  · intro h; funext j; exact h j
  · intro h j; rw [h]

/-- Projecting the `l`-block away from `setF ∩ setPsi` leaves exactly the graph of the
pulled-back family. -/
theorem projLastIter_setF_inter_setPsi (p p' n : ℕ)
    (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (Ψ : (Fin p' → ℝ) → (Fin p → ℝ)) :
    projLastIter (p' + (n + 1) + 1) p (setF p p' n f ∩ setPsi p p' n Ψ) =
      famGraph (fun (u : Fin p' → ℝ) (y : Fin (n + 1) → ℝ) => f (Ψ u) y) := by
  rw [projLastIter_eq]
  ext x
  constructor
  · rintro ⟨w, hw⟩
    rw [Set.mem_inter_iff] at hw
    obtain ⟨hF, hP⟩ := hw
    rw [mem_setF] at hF
    rw [mem_setPsi] at hP
    simp only [famGraph, graphOf, Set.mem_ofPred_eq, Fin.init_def]
    show x (Fin.last (p' + (n + 1))) = f (Ψ (glueU p' n x)) (glueY p' n x)
    rw [← hP, hF]
  · intro hx
    simp only [famGraph, graphOf, Set.mem_ofPred_eq, Fin.init_def] at hx
    have hx' : x (Fin.last (p' + (n + 1))) = f (Ψ (glueU p' n x)) (glueY p' n x) := hx
    refine ⟨Ψ (glueU p' n x), ?_⟩
    rw [Set.mem_inter_iff]
    exact ⟨(mem_setF p p' n f x (Ψ (glueU p' n x))).mpr hx',
      (mem_setPsi p p' n Ψ x (Ψ (glueU p' n x))).mpr rfl⟩

end PullFamGraphMemAux

open PullFamGraphMemAux

/-- **Pulling a family graph back along an `Ω`-definable parametrisation.**
If `famGraph f ⊆ ℝ^{p+(n+1)+1}` and `paramGraph Ψ ⊆ ℝ^{p'+p}` are both `Ω F0 D`-definable, then
the graph of `(u, y) ↦ f (Ψ u) y` is `Ω`-definable with a format independent of `D` and degree
at most `D + D + 4`.

The two pullbacks (`setF`, `setPsi`) are substitution atoms (`Work.WilG4a.subst_mem`) of degree
`D + 2`; they are intersected and the `p` intermediate coordinates are projected away. -/
theorem PullFamGraphMem (S : WilkiesDesign.SOMin) (p p' n F0 : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ (D : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
        (Ψ : (Fin p' → ℝ) → (Fin p → ℝ)),
      WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
      Work.WilG4a.CD.paramGraph Ψ ∈ S.Ω F0 D (p' + p) →
      WilkiesDesign.CG.famGraph (fun (u : Fin p' → ℝ) (y : Fin (n + 1) → ℝ) => f (Ψ u) y) ∈
        S.Ω a (MvPolynomial.eval ![D, D] b) (p' + (n + 1) + 1) := by
  refine ⟨max (F0 + 2 * (((p' + (n + 1) + 1) + p) + (p + (n + 1) + 1)) + 1)
      (F0 + 2 * (((p' + (n + 1) + 1) + p) + (p' + p)) + 1) + 1 + p,
    MvPolynomial.X 0 + MvPolynomial.X 1 + MvPolynomial.C 4, ?_⟩
  intro D f Ψ hf hΨ
  have hF : setF p p' n f ∈
      S.Ω (F0 + 2 * (((p' + (n + 1) + 1) + p) + (p + (n + 1) + 1)) + 1)
        (D + 2) ((p' + (n + 1) + 1) + p) :=
    Work.WilG4a.subst_mem S (sigF p p' n) hf
  have hP : setPsi p p' n Ψ ∈
      S.Ω (F0 + 2 * (((p' + (n + 1) + 1) + p) + (p' + p)) + 1)
        (D + 2) ((p' + (n + 1) + 1) + p) :=
    Work.WilG4a.subst_mem S (sigPsi p p' n) hΨ
  have hF' : setF p p' n f ∈
      S.Ω (max (F0 + 2 * (((p' + (n + 1) + 1) + p) + (p + (n + 1) + 1)) + 1)
        (F0 + 2 * (((p' + (n + 1) + 1) + p) + (p' + p)) + 1))
        (D + 2) ((p' + (n + 1) + 1) + p) :=
    Work.WilG1.Omega.mono hF (le_max_left _ _) le_rfl
  have hP' : setPsi p p' n Ψ ∈
      S.Ω (max (F0 + 2 * (((p' + (n + 1) + 1) + p) + (p + (n + 1) + 1)) + 1)
        (F0 + 2 * (((p' + (n + 1) + 1) + p) + (p' + p)) + 1))
        (D + 2) ((p' + (n + 1) + 1) + p) :=
    Work.WilG1.Omega.mono hP (le_max_right _ _) le_rfl
  have hInt := Work.WilG0.Omega_inter2 hF' hP'
  have hProj := Work.WilG4a.projLastIter_mem (S := S) hInt
  rw [projLastIter_setF_inter_setPsi] at hProj
  refine Work.WilG1.Omega.mono hProj le_rfl ?_
  have hb : MvPolynomial.eval ![D, D]
      (MvPolynomial.X 0 + MvPolynomial.X 1 + MvPolynomial.C 4 : MvPolynomial (Fin 2) ℕ)
      = D + D + 4 := by
    simp [MvPolynomial.eval_add, MvPolynomial.eval_X]
  rw [hb]
  omega

end Work.WilG4c
