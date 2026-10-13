/-
  WilE7 (`Work.WilE7.stratGraph`): a `Good` stratum `S` with `S.j = q` — i.e. the equations `S.h`
  cut out the fibres of `S.X` in the maximal possible fibre codimension — is *locally a graph*
  over the base `ℝ^p`.

  Concretely: at every `z ∈ S.X.set` there is an open neighbourhood `U` of `x = projFirst p q z`,
  a *continuous* map `y : ℝ^p → ℝ^q` on `U` with `y x = projSnd p q z` solving the equations
  `S.h a (x, y x) = 0`, and an open neighbourhood `W` of `z` such that every point of `S.X.set`
  in `W` whose base projection lies in `U` is on the graph of `y`.

  Mathematics.  At `z` the `S.j = q` equations `S.h a` vanish and their *fibrewise* Jacobian
  `∂S.h/∂y` is a square matrix of rank `S.j = q`, hence invertible
  (`goodJacDet`, from `Stratum.Good` + `Matrix.rank_submatrix` + `det_ne_zero_of_rank_eq`).
  The implicit function theorem — in the form of the already proved
  `Work.WilE2.local_graph_of_submersion`, packaged as `Work.WilE7.localSection` — therefore
  produces open `U ∋ x`, `B ∋ projSnd p q z` and `φ : U → ℝ^q` with `φ x = projSnd p q z`,
  `S.h a (x, φ x) = 0` on `U`, and *uniqueness*: any `v ∈ B` with `S.h a (x, v) = 0` equals
  `φ x`.  The `Good` stratum only supplies the equations at its own points (no localisation of
  `S.X.set` is needed here); combined with `Fin.append (projFirst p q z') (projSnd p q z') = z'`
  this gives the graph property on
  `W = {z' | projFirst p q z' ∈ U} ∩ {z' | projSnd p q z' ∈ B}`.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE9.Ift.ift_exists
import Submission.Work.WilE9.Ift.ift_identity
import Submission.Work.WilE7.fiber_finite_of_good_full_rank
import Submission.Work.WilE7.localSection

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
namespace Work.WilE7
open WilkiesDesign WilkiesDesign.E

/-! ## Elementary splits of `Fin (p+q)` along `projFirst`/`projSnd` -/

/-- `z` is the gluing of its first `p` and its last `q` coordinates. -/
theorem append_proj {p q : ℕ} (z : Fin (p + q) → ℝ) :
    Fin.append (projFirst p q z) (projSnd p q z) = z := by
  funext i
  refine Fin.addCases (motive := fun i => Fin.append (projFirst p q z) (projSnd p q z) i = z i)
    (fun i => ?_) (fun j => ?_) i
  · simp [projFirst]
  · simp [projSnd]

/-- `projFirst` is continuous. -/
theorem continuous_projFirst (p q : ℕ) : Continuous (projFirst p q) :=
  continuous_pi (fun i => continuous_apply _)

/-- `projSnd` is continuous. -/
theorem continuous_projSnd (p q : ℕ) : Continuous (projSnd p q) :=
  continuous_pi (fun i => continuous_apply _)

/-! ## The fibrewise Jacobian of a `Good` stratum of fibre codimension `q` is invertible -/

/-- A `Good` stratum with `S.j = q` has an invertible fibrewise Jacobian at every point of its
set: the `S.j × q` matrix of `Stratum.Good` has rank `S.j = q`, so the `q × q` matrix obtained by
relabelling its rows along an equivalence `e : Fin q ≃ Fin S.j` is of full rank, hence has nonzero
determinant. -/
theorem goodJacDet {p q : ℕ} (S : WilkiesDesign.E.Stratum p q) (hj : S.j = q)
    (e : Fin q ≃ Fin S.j) (w : Fin (p + q) → ℝ)
    (hrank : (Matrix.of fun (a : Fin S.j) (l : Fin q) =>
      eaEval S.X.c (eaD S.X.c (Fin.natAdd p l) (S.h a)) w).rank = S.j) :
    (Matrix.of fun (a : Fin q) (l : Fin q) =>
      eaEval S.X.c (eaD S.X.c (Fin.natAdd p l) (S.h (e a))) w).det ≠ 0 := by
  have hsub : (Matrix.of fun (a : Fin q) (l : Fin q) =>
        eaEval S.X.c (eaD S.X.c (Fin.natAdd p l) (S.h (e a))) w)
      = (Matrix.of fun (a : Fin S.j) (l : Fin q) =>
          eaEval S.X.c (eaD S.X.c (Fin.natAdd p l) (S.h a)) w).submatrix
        (⇑e) (⇑(Equiv.refl (Fin q))) := rfl
  refine det_ne_zero_of_rank_eq ?_
  rw [hsub, Matrix.rank_submatrix, hrank, hj]

/-! ## The main statement -/

theorem stratGraph {p q : ℕ} (S : WilkiesDesign.E.Stratum p q) (hGood : S.Good) (hj : S.j = q)
    (z : Fin (p + q) → ℝ) (hz : z ∈ S.X.set) :
    ∃ (U : Set (Fin p → ℝ)) (y : (Fin p → ℝ) → (Fin q → ℝ)) (W : Set (Fin (p + q) → ℝ)),
      IsOpen U ∧ WilkiesDesign.E.projFirst p q z ∈ U ∧ IsOpen W ∧ z ∈ W ∧
      y (WilkiesDesign.E.projFirst p q z) = WilkiesDesign.E.projSnd p q z ∧
      ContinuousOn y U ∧
      (∀ x ∈ U, ∀ a : Fin S.j,
        WilkiesDesign.E.eaEval S.X.c (S.h a) (Fin.append x (y x)) = 0) ∧
      (∀ z' ∈ W, z' ∈ S.X.set → WilkiesDesign.E.projFirst p q z' ∈ U →
        WilkiesDesign.E.projSnd p q z' = y (WilkiesDesign.E.projFirst p q z')) := by
  classical
  obtain ⟨hzero, hrank, _hloc⟩ := hGood z hz
  -- relabel the `S.j = q` equations along the equivalence `Fin q ≃ Fin S.j`
  set e : Fin q ≃ Fin S.j := (finCongr hj).symm with he
  set F : Fin q → EAPoly (p + q) S.X.r := fun a => S.h (e a) with hF
  have hsplit : Fin.append (projFirst p q z) (projSnd p q z) = z := append_proj z
  have h0 : ∀ a, eaEval S.X.c (F a) (Fin.append (projFirst p q z) (projSnd p q z)) = 0 := by
    intro a
    rw [hsplit]
    exact hzero (e a)
  have hdet : (Matrix.of fun (a : Fin q) (l : Fin q) =>
      eaEval S.X.c (eaD S.X.c (Fin.natAdd p l) (F a))
        (Fin.append (projFirst p q z) (projSnd p q z))).det ≠ 0 := by
    have hmat : (Matrix.of fun (a : Fin q) (l : Fin q) =>
        eaEval S.X.c (eaD S.X.c (Fin.natAdd p l) (F a))
          (Fin.append (projFirst p q z) (projSnd p q z)))
        = (Matrix.of fun (a : Fin q) (l : Fin q) =>
          eaEval S.X.c (eaD S.X.c (Fin.natAdd p l) (S.h (e a))) z) := by
      ext a l
      simp only [Matrix.of_apply, hF]
      rw [hsplit]
    rw [hmat]
    exact goodJacDet S hj e z hrank
  -- the implicit function, with uniqueness on the product `U × B`
  obtain ⟨U, φ, B, hUo, hxU, hBo, hyB, hφ0, hφcont, hφsol, hφuniq⟩ :=
    localSection S.X.c F (projFirst p q z) (projSnd p q z) h0 hdet
  refine ⟨U, φ, {z' | projFirst p q z' ∈ U} ∩ {z' | projSnd p q z' ∈ B}, hUo, hxU, ?_, ?_,
    hφ0, hφcont, ?_, ?_⟩
  · exact ((continuous_projFirst p q).isOpen_preimage U hUo).inter
      ((continuous_projSnd p q).isOpen_preimage B hBo)
  · exact ⟨hxU, hyB⟩
  · intro x hx a
    have h := hφsol x hx (e.symm a)
    have hea : e (e.symm a) = a := Equiv.apply_symm_apply e a
    simpa [hF, hea] using h
  · rintro z' ⟨hz'U, hz'B⟩ hz' _
    have hsplit' : Fin.append (projFirst p q z') (projSnd p q z') = z' := append_proj z'
    have hg : ∀ a, eaEval S.X.c (F a)
        (Fin.append (projFirst p q z') (projSnd p q z')) = 0 := by
      intro a
      rw [hsplit']
      exact (hGood z' hz').1 (e a)
    exact hφuniq (projFirst p q z') hz'U (projSnd p q z') hz'B hg

end Work.WilE7
