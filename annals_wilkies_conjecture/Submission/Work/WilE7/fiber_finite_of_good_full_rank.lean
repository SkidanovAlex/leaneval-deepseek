/-
  WilE7, the base case `k = 0` of BV's fibre-cutting induction.

  `Work.WilE7.fiber_finite_of_good_full_rank`: a `Good` stratum `S` with `S.j = q` has finite
  fibres over the base `ℝ^p`.  The argument is

  * a `Good` stratum of fibre codimension `q` is *discrete in each fibre*: at a point `z` of
    `S.X.set` the fibrewise Jacobian `∂S.h/∂y` is a square matrix of full rank `S.j = q`, so it is
    invertible, and the implicit function theorem (in the local-isolation form
    `Work.WilE7.eaEval_eventually_eq`) shows that `z` is the only point of `S.X.set` in that fibre
    near `z`;
  * the fibre is the set of a semi-Pfaffian set in `ℝ^q`, namely the *specialization* of `S.X` at
    the base point `x` (`Work.WilE7.speAt_set`);
  * `E2_components` (the hypothesis `hE2`) bounds the number of connected components of that
    semi-Pfaffian set by a polynomial in its degree; a discrete set has one point per connected
    component, so this bounds its cardinality
    (`Work.WilE7.finite_of_isolated_of_finite_components`).

  The hypothesis `hE2` is used in an essential way: without it the fibre of a `Good` stratum can be
  an infinite discrete set (in the semi-Pfaffian world such a set is *not* definable, which is
  exactly what `E2_components` supplies).
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.SpeAt
import Submission.Work.WilE7.speAt_set
import Submission.Work.WilE7.eaEval_eventually_eq
import Submission.Work.WilE7.finite_of_isolated_of_finite_components

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
namespace Work.WilE7
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-- A square real matrix whose rank equals the size of its index type is invertible, so has
nonzero determinant. -/
theorem det_ne_zero_of_rank_eq {q : ℕ} {M : Matrix (Fin q) (Fin q) ℝ} (h : M.rank = q) :
    M.det ≠ 0 := by
  rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  show Function.Injective (fun v => M.mulVec v)
  have hfun : (fun v => M.mulVec v) = M.mulVecLin :=
    funext (fun v => (Matrix.mulVecLin_apply M v).symm)
  rw [hfun]
  have hrank : M.mulVecLin.range = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Matrix.rank] at h
    rw [h]
    simp
  have hker : M.mulVecLin.ker = ⊥ := by
    rw [← Submodule.finrank_eq_zero]
    have h1 := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    rw [hrank] at h1
    have h2 : Module.finrank ℝ (↥(⊤ : Submodule ℝ (Fin q → ℝ))) = q := by simp
    have h3 : Module.finrank ℝ (Fin q → ℝ) = q := by simp
    rw [h2, h3] at h1
    omega
  exact LinearMap.ker_eq_bot.mp hker

theorem fiber_finite_of_good_full_rank
    (hE2 : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : WilkiesDesign.E.SemiPf k), X.fmt ≤ F →
      ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ (↑s : Set (Fin k → ℝ)) ⊆ X.set ∧
        ∀ x ∈ X.set, ∃ y ∈ s, connectedComponentIn X.set x = connectedComponentIn X.set y)
    {p q : ℕ} (S : WilkiesDesign.E.Stratum p q) (hGood : S.Good) (hj : S.j = q) :
    ∀ x : Fin p → ℝ, (WilkiesDesign.E.fiber S.X.set x).Finite := by
  intro x
  by_cases hx : x ∈ cubeC p
  · -- The fibre is the set of the specialization of `S.X` at `x`.
    have hset := speAt_set x S.X hx
    rw [← hset]
    -- `E2_components` bounds the number of connected components of that semi-Pfaffian set.
    obtain ⟨P, hP⟩ := hE2 (speSemiPfAt x S.X).fmt
    obtain ⟨s, -, hssub, hcomp⟩ := hP q (speSemiPfAt x S.X) le_rfl
    -- Each point of the fibre is isolated; hence components are singletons and the fibre is `s`.
    refine finite_of_isolated_of_finite_components (F := (speSemiPfAt x S.X).set) ?_ hssub hcomp
    intro y hy
    have hzy : Fin.append x y ∈ S.X.set := by
      have : y ∈ fiber S.X.set x := hset ▸ hy
      exact this
    obtain ⟨hh0, hrank, hloc⟩ := hGood (Fin.append x y) hzy
    -- Reindex the `S.j × q` Jacobian of `Good` along `S.j = q`.
    let e : Fin q ≃ Fin S.j := finCongr hj.symm
    let h' : Fin q → EAPoly (p + q) S.X.r := fun a => S.h (e a)
    have hMrank : (Matrix.of fun (a : Fin q) (l : Fin q) =>
        eaEval S.X.c (eaD S.X.c (Fin.natAdd p l) (h' a)) (Fin.append x y)).rank = q := by
      have hsub : (Matrix.of fun (a : Fin q) (l : Fin q) =>
            eaEval S.X.c (eaD S.X.c (Fin.natAdd p l) (h' a)) (Fin.append x y))
          = (Matrix.of fun (a : Fin S.j) (l : Fin q) =>
              eaEval S.X.c (eaD S.X.c (Fin.natAdd p l) (S.h a)) (Fin.append x y)).submatrix
            (⇑e) (⇑(Equiv.refl (Fin q))) := rfl
      rw [hsub, Matrix.rank_submatrix]
      rw [hrank, hj]
    have hdet : (Matrix.of fun (a : Fin q) (l : Fin q) =>
        eaEval S.X.c (eaD S.X.c (Fin.natAdd p l) (h' a)) (Fin.append x y)).det ≠ 0 :=
      det_ne_zero_of_rank_eq hMrank
    -- Local isolation of `y` among the zeros of the fibre system.
    have hev := eaEval_eventually_eq S.X.c h' x y (fun a => hh0 (e a)) hdet
    have hev2 : ∀ᶠ y' in nhds y, y' ∈ (speSemiPfAt x S.X).set → y' = y := by
      filter_upwards [hev] with y' hmem hy'
      refine hmem (fun a => ?_)
      have hz' : Fin.append x y' ∈ S.X.set := by
        have : y' ∈ fiber S.X.set x := hset ▸ hy'
        exact this
      exact (hGood (Fin.append x y') hz').1 (e a)
    -- Turn the eventual statement into the open neighbourhood required by the counting lemma.
    obtain ⟨U, hUsub, hUopen, hyU⟩ := mem_nhds_iff.mp hev2
    refine ⟨U, hUopen, hyU, ?_⟩
    ext z
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
    constructor
    · intro hz
      exact hUsub hz.1 hz.2
    · intro hz
      subst hz
      exact ⟨hyU, hy⟩
  · -- `x` is outside the cube, so no point lies in the fibre.
    have hempty : fiber S.X.set x = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro y hy
      exact hx fun i => by
        have h1 : |Fin.append x y (Fin.castAdd q i)| ≤ 1 := hy.1 (Fin.castAdd q i)
        rwa [Fin.append_left] at h1
    rw [hempty]
    exact Set.finite_empty

end Work.WilE7
