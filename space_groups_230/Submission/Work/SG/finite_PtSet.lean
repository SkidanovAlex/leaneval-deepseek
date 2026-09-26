import Mathlib
import Submission.Work.SG.Defs
import Submission.Work.SG.AffCoord
import Submission.Work.SG.NormalForm
import Submission.Work.SG.lattice_ball_finite

/-!
# The point set in coordinates is finite

Let `G` be a crystallographic subgroup of `E 3 = ℝ³` and `T : (Fin 3 → ℝ) ≃ₗ[ℝ] E 3` a linear
isomorphism identifying the standard lattice `ℤ³ ⊂ ℝ³` with the translation lattice
`transLattice G` of `G` (`hT1`, `hT2` say that `T ∘ intVec : ℤ³ → E 3` is a bijection onto
`transLattice G`).

We show that the set of integer matrices which occur as the coordinate matrix of the linear part
of an element of `G` is finite:
`{A : IMat | ∃ g ∈ G, ∀ n, lmap T g (intVec n) = intVec (A.mulVec n)}`.

The argument is the classical finiteness of the point group.  `G` being crystallographic, it
is discrete (`G.2.discrete`) and contains three linearly independent translation vectors
`v i` (`G.2.cocompact`), so `v` is a real basis of `E 3` and the linear parts of `G` are
determined by their values on `v`.  For `g ∈ G` the linear part `linPart g` is orthogonal, so
`linPart g (v i)` has the same norm as `v i`, and it lies in the (discrete) translation lattice
because linear parts of elements of `G` preserve `transLattice G`.  Hence the map sending
`g ∈ G` to `(linPart g (v i))ᵢ` lands in a *finite* product of lattice balls, and it is
injective up to the value of the coordinate matrix.  Injecting the target set into this finite
product gives finiteness.
-/

namespace Work.SG

open LeanEval.Geometry.SpaceGroupsProblem

noncomputable section

/-- An integer matrix is determined by the map `n ↦ A.mulVec n` on `ℤ³` (the columns of `A`
are the images of the standard basis vectors). -/
theorem imat_ext_of_mulVec {A A' : IMat}
    (h : ∀ n : Fin 3 → ℤ, A.mulVec n = A'.mulVec n) : A = A' := by
  ext i j
  have h1 := congrFun (h (Pi.single j (1 : ℤ))) i
  rwa [Matrix.mulVec_single_one, Matrix.mulVec_single_one, Matrix.col_apply,
    Matrix.col_apply] at h1

theorem finite_PtSet (G : LeanEval.Geometry.SpaceGroupsProblem.CrystallographicGroup 3)
    (T : (Fin 3 → ℝ) ≃ₗ[ℝ] LeanEval.Geometry.SpaceGroupsProblem.E 3)
    (hT1 : ∀ n : Fin 3 → ℤ, T (Work.SG.intVec n) ∈ Work.SG.transLattice G.1)
    (hT2 : ∀ v ∈ Work.SG.transLattice G.1, ∃ n : Fin 3 → ℤ, T.symm v = Work.SG.intVec n) :
    {A : Work.SG.IMat | ∃ g ∈ G.1, ∀ n : Fin 3 → ℤ,
      Work.SG.lmap T g (Work.SG.intVec n) = Work.SG.intVec (A.mulVec n)}.Finite := by
  -- Cocompactness: three linearly independent translation vectors `v i`.
  obtain ⟨v, hvli, hv⟩ := G.2.cocompact
  have hvL : ∀ i, v i ∈ transLattice G.1 := fun i => by
    obtain ⟨g, hg, hgt⟩ := hv i
    exact mem_transLattice.mpr ⟨g, hg, hgt⟩
  -- They form a real basis of `E 3`.
  have hspan : Submodule.span ℝ (Set.range v) = ⊤ :=
    hvli.span_eq_top_of_card_eq_finrank (by rw [finrank_euclideanSpace])
  -- The target set, named for the argument below.
  let S : Set IMat := {A : IMat | ∃ g ∈ G.1, ∀ n : Fin 3 → ℤ,
      lmap T g (intVec n) = intVec (A.mulVec n)}
  change S.Finite
  -- The finite codomain: for each `i`, the lattice points of the ball of radius `‖v i‖`.
  let F : Fin 3 → Set (E 3) := fun i => {w : E 3 | w ∈ transLattice G.1 ∧ ‖w‖ ≤ ‖v i‖}
  have hFfin : ∀ i, (F i).Finite := fun i => lattice_ball_finite G (‖v i‖)
  haveI : Finite {p : Fin 3 → E 3 // ∀ i, p i ∈ F i} :=
    Set.Finite.to_subtype (Set.Finite.pi' hFfin)
  -- Every `A ∈ S` determines a tuple `(linPart g (v i))ᵢ` for any witness `g`.
  let ψ : S → {p : Fin 3 → E 3 // ∀ i, p i ∈ F i} := fun x =>
    ⟨fun i => linPart (Classical.choose x.2) (v i), fun i =>
      ⟨linPart_transLattice (Classical.choose_spec x.2).1 (hvL i),
        by rw [linPart_norm]⟩⟩
  -- `ψ` is injective: the tuple determines `linPart g`, hence `lmap T g`, hence `A`.
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    have hφeq : (fun i => linPart (Classical.choose x.2) (v i)) =
        (fun i => linPart (Classical.choose y.2) (v i)) := congrArg Subtype.val hxy
    have hlin : linPart (Classical.choose x.2) = linPart (Classical.choose y.2) := by
      apply LinearEquiv.toLinearMap_injective
      apply LinearMap.ext_on hspan
      intro w hw
      obtain ⟨i, rfl⟩ := hw
      exact congrFun hφeq i
    have hlmap : lmap T (Classical.choose x.2) = lmap T (Classical.choose y.2) :=
      congrArg (fun e : E 3 ≃ₗ[ℝ] E 3 => (T.trans e).trans T.symm) hlin
    have hA : x.1 = y.1 := by
      apply imat_ext_of_mulVec
      intro n
      have hx' := (Classical.choose_spec x.2).2 n
      have hy' := (Classical.choose_spec y.2).2 n
      have : intVec (x.1.mulVec n) = intVec (y.1.mulVec n) := by
        rw [← hx', ← hy', hlmap]
      exact intVec_injective this
    exact Subtype.ext hA
  exact Set.finite_coe_iff.mp (Finite.of_injective ψ hψinj)

end

end Work.SG
