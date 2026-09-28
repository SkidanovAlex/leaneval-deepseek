import Mathlib
import Submission.Work.SSS.serreE1Defs
import Submission.Work.SSS.serreSkelNodeg
import Submission.Work.SSS.serreSubcomplexToN
import Submission.Work.SSS.ezFaceEpi
import Submission.Work.SSS.ezFaceNonEpi
import Submission.Work.StemsB.SerreFiltration
import Submission.Work.SSS.Filtration

/-!
# Auxiliary material for the Eilenberg–Zilber splitting of the graded pieces

Vocabulary for `Work.SSS.serreE1Graded`: the element `nBase y` underlying a nondegenerate
`d`-simplex, the simplices of the pullback `T_y = Δ[d] ×_Y X` with prescribed components
(`pullPt`), and the two chain maps `Θ`/`Ψ` (the Eilenberg–Zilber section) and `Φ` (the sum of the
second projections) whose composite is the desired isomorphism.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

noncomputable section

variable {X Y : SSet.{0}}

/-! ## The pullback of a morphism along the simplex attached to a nondegenerate simplex -/

/-- The simplex of `Y` underlying an element `y` of `nIndex Y d`. -/
def nBase {d : ℕ} (y : nIndex Y d) : Y _⦋d⦌ := (y.1.toS.cast y.2).simplex

lemma nBase_mem {d : ℕ} (y : nIndex Y d) : nBase y ∈ Y.nonDegenerate d :=
  (y.1.cast y.2).nonDegenerate

lemma nIndexSigma_eq {d : ℕ} (y : nIndex Y d) :
    nIndexSigma Y d y = SSet.yonedaEquiv.symm (nBase y) := rfl

/-- Evaluation of `nIndexSigma Y d y : Δ[d] ⟶ Y` at the simplex of `Δ[d]` corresponding to a
monotone map `v : ⦋n⦌ ⟶ ⦋d⦌`. -/
lemma nIndexSigma_app {d n : ℕ} (y : nIndex Y d) (v : ⦋n⦌ ⟶ ⦋d⦌) :
    (nIndexSigma Y d y).app (op ⦋n⦌) (SSet.stdSimplex.objEquiv.symm v) = Y.map v.op (nBase y) := by
  rw [show nIndexSigma Y d y = SSet.yonedaEquiv.symm (nBase y) from rfl]
  exact (SSet.stdSimplex.map_objEquiv_op_apply (nBase y) (SSet.stdSimplex.objEquiv.symm v)).symm

lemma map_δ_map {d n : ℕ} (y : nIndex Y d) (v : ⦋n+1⦌ ⟶ ⦋d⦌) (i : Fin (n+2)) :
    Y.map (SimplexCategory.δ i ≫ v).op (nBase y) = Y.δ i (Y.map v.op (nBase y)) := by
  rw [op_comp]
  simp only [Functor.map_comp, ConcreteCategory.comp_apply]
  rfl

/-- The nondegenerate part of `Y.map v.op (nBase y)` has dimension at most `d`. -/
lemma toN_dim_le_map {d n : ℕ} (y : nIndex Y d) (v : ⦋n⦌ ⟶ ⦋d⦌) :
    (SSet.S.mk (Y.map v.op (nBase y))).toN.dim ≤ d := by
  have hle : (SSet.S.mk (Y.map v.op (nBase y))).subcomplex ≤ (SSet.S.mk (nBase y)).subcomplex :=
    SSet.S.subcomplex_map_le _ _ v rfl
  have h1 : (SSet.S.mk (Y.map v.op (nBase y))).toN ≤ (SSet.S.mk (nBase y)).toN := by
    rw [SSet.N.le_iff, SSet.S.subcomplex_toN, SSet.S.subcomplex_toN]
    exact hle
  have h2 : (SSet.S.mk (nBase y)).toN.dim = d := by
    have : (SSet.S.mk (nBase y)).toN = SSet.N.mk (nBase y) (nBase_mem y) := by
      rw [SSet.S.toN_eq_iff]
      rfl
    rw [this]
    rfl
  exact (SSet.N.dim_le_of_le h1).trans_eq h2

variable (f : X ⟶ Y)

lemma isPullback_T {d : ℕ} (y : nIndex Y d) (n : ℕ) :
    IsPullback ((pullback.fst (nIndexSigma Y d y) f).app (op ⦋n⦌))
      ((pullback.snd (nIndexSigma Y d y) f).app (op ⦋n⦌))
      ((nIndexSigma Y d y).app (op ⦋n⦌)) (f.app (op ⦋n⦌)) :=
  (IsPullback.of_hasPullback (nIndexSigma Y d y) f).map (SSet.evaluation.obj (op ⦋n⦌))

lemma pullPt_exists {d n : ℕ} (y : nIndex Y d) (v : ⦋n⦌ ⟶ ⦋d⦌) (x : X _⦋n⦌)
    (h : Y.map v.op (nBase y) = f.app (op ⦋n⦌) x) :
    ∃ w : (pullAlong f (nIndexSigma Y d y)).obj (op ⦋n⦌),
      (pullback.fst (nIndexSigma Y d y) f).app (op ⦋n⦌) w = SSet.stdSimplex.objEquiv.symm v ∧
      (pullback.snd (nIndexSigma Y d y) f).app (op ⦋n⦌) w = x := by
  have hpb := isPullback_T f y n
  have := (Types.isPullback_iff _ _ _ _).mp hpb
  obtain ⟨w, hw1, hw2⟩ := this.2.2 (SSet.stdSimplex.objEquiv.symm v) x (by rw [nIndexSigma_app, h])
  exact ⟨w, hw1, hw2⟩

/-- The `n`-simplex of `T_y = Δ[d] ×_Y X` whose `Δ[d]`-component is (the simplex corresponding
to) the monotone map `v` and whose `X`-component is `x`. -/
def pullPt {d n : ℕ} (y : nIndex Y d) (v : ⦋n⦌ ⟶ ⦋d⦌) (x : X _⦋n⦌)
    (h : Y.map v.op (nBase y) = f.app (op ⦋n⦌) x) :
    (pullAlong f (nIndexSigma Y d y)).obj (op ⦋n⦌) :=
  Classical.choose (pullPt_exists f y v x h)

lemma pullPt_fst {d n : ℕ} (y : nIndex Y d) (v : ⦋n⦌ ⟶ ⦋d⦌) (x : X _⦋n⦌)
    (h : Y.map v.op (nBase y) = f.app (op ⦋n⦌) x) :
    (pullback.fst (nIndexSigma Y d y) f).app (op ⦋n⦌) (pullPt f y v x h) =
      SSet.stdSimplex.objEquiv.symm v :=
  (Classical.choose_spec (pullPt_exists f y v x h)).1

lemma pullPt_snd {d n : ℕ} (y : nIndex Y d) (v : ⦋n⦌ ⟶ ⦋d⦌) (x : X _⦋n⦌)
    (h : Y.map v.op (nBase y) = f.app (op ⦋n⦌) x) :
    (pullback.snd (nIndexSigma Y d y) f).app (op ⦋n⦌) (pullPt f y v x h) = x :=
  (Classical.choose_spec (pullPt_exists f y v x h)).2

lemma pullPt_ext {d n : ℕ} (y : nIndex Y d)
    {w w' : (pullAlong f (nIndexSigma Y d y)).obj (op ⦋n⦌)}
    (h1 : (pullback.fst (nIndexSigma Y d y) f).app (op ⦋n⦌) w =
      (pullback.fst (nIndexSigma Y d y) f).app (op ⦋n⦌) w')
    (h2 : (pullback.snd (nIndexSigma Y d y) f).app (op ⦋n⦌) w =
      (pullback.snd (nIndexSigma Y d y) f).app (op ⦋n⦌) w') : w = w' :=
  ((Types.isPullback_iff _ _ _ _).mp (isPullback_T f y n)).2.1 w w' ⟨h1, h2⟩

lemma pullPt_δ_fst {d n : ℕ} (y : nIndex Y d)
    (w : (pullAlong f (nIndexSigma Y d y)).obj (op ⦋n+1⦌)) (i : Fin (n+2)) :
    (pullback.fst (nIndexSigma Y d y) f).app (op ⦋n⦌)
        ((pullAlong f (nIndexSigma Y d y)).δ i w) =
      (Δ[d] : SSet).δ i ((pullback.fst (nIndexSigma Y d y) f).app (op ⦋n+1⦌) w) :=
  SSet.δ_naturality_apply (pullback.fst (nIndexSigma Y d y) f) i w

lemma pullPt_δ_snd {d n : ℕ} (y : nIndex Y d)
    (w : (pullAlong f (nIndexSigma Y d y)).obj (op ⦋n+1⦌)) (i : Fin (n+2)) :
    (pullback.snd (nIndexSigma Y d y) f).app (op ⦋n⦌)
        ((pullAlong f (nIndexSigma Y d y)).δ i w) =
      X.δ i ((pullback.snd (nIndexSigma Y d y) f).app (op ⦋n+1⦌) w) :=
  SSet.δ_naturality_apply (pullback.snd (nIndexSigma Y d y) f) i w

/-- The faces of `pullPt` are given by the pullback of the faces. -/
lemma pullPt_δ {d n : ℕ} (y : nIndex Y d) (v : ⦋n+1⦌ ⟶ ⦋d⦌) (x : X _⦋n+1⦌)
    (h : Y.map v.op (nBase y) = f.app (op ⦋n+1⦌) x) (i : Fin (n+2))
    (h' : Y.map (SimplexCategory.δ i ≫ v).op (nBase y) = f.app (op ⦋n⦌) (X.δ i x)) :
    (pullAlong f (nIndexSigma Y d y)).δ i (pullPt f y v x h) =
      pullPt f y (SimplexCategory.δ i ≫ v) (X.δ i x) h' := by
  apply pullPt_ext f y
  · rw [pullPt_δ_fst, pullPt_fst, pullPt_fst, SSet.stdSimplex.δ_objEquiv_symm_apply]
  · rw [pullPt_δ_snd, pullPt_snd, pullPt_snd]

section Bdry

variable {f}

/-- A simplex `w` of `∂T_y` lies in the boundary if and only if its `Δ[d]`-component is not an
epimorphism. -/
lemma mem_bdry_iff {d n : ℕ} (y : nIndex Y d)
    (w : (pullAlong f (nIndexSigma Y d y)).obj (op ⦋n⦌)) :
    w ∈ (bdryAlong f (nIndexSigma Y d y)).obj (op ⦋n⦌) ↔
      ¬ Epi (SSet.stdSimplex.objEquiv ((pullback.fst (nIndexSigma Y d y) f).app (op ⦋n⦌) w)) := by
  change (pullback.fst (nIndexSigma Y d y) f).app (op ⦋n⦌) w ∈ (SSet.boundary d).obj (op ⦋n⦌) ↔
      ¬ Epi (SSet.stdSimplex.objEquiv ((pullback.fst (nIndexSigma Y d y) f).app (op ⦋n⦌) w))
  rw [SSet.mem_boundary_iff_notMem_range, SimplexCategory.epi_iff_surjective]
  constructor
  · rintro ⟨j, hj⟩ hsurj
    obtain ⟨i, hi⟩ := hsurj j
    exact hj ⟨i, by simpa using hi⟩
  · intro h
    by_contra hc
    push_neg at hc
    exact h fun j => by
      obtain ⟨i, hi⟩ := hc j
      exact ⟨i, by simpa using hi⟩

end Bdry


section Ez

variable {f}

/-- The nondegenerate `d`-simplex underlying a simplex `x` whose image in `Y` has nondegenerate
part of dimension exactly `d`. -/
def ezY {d n : ℕ} (f : X ⟶ Y) (x : X _⦋n⦌)
    (h : (SSet.S.mk (f.app (op ⦋n⦌) x)).toN.dim = d) : nIndex Y d :=
  ⟨(SSet.S.mk (f.app (op ⦋n⦌) x)).toN, h⟩

/-- The Eilenberg–Zilber epimorphism of `x` (relative to the nondegenerate part of its image). -/
def ezU {d n : ℕ} (f : X ⟶ Y) (x : X _⦋n⦌)
    (h : (SSet.S.mk (f.app (op ⦋n⦌) x)).toN.dim = d) : ⦋n⦌ ⟶ ⦋d⦌ :=
  h ▸ (SSet.S.mk (f.app (op ⦋n⦌) x)).toNπ

lemma ez_compat {d n : ℕ} (f : X ⟶ Y) (x : X _⦋n⦌)
    (h : (SSet.S.mk (f.app (op ⦋n⦌) x)).toN.dim = d) :
    Y.map (ezU f x h).op (nBase (ezY f x h)) = f.app (op ⦋n⦌) x := by
  subst h
  simp only [ezU, ezY, nBase, SSet.S.cast_simplex_rfl]
  exact SSet.S.map_toNπ_op_apply _

lemma ezU_epi {d n : ℕ} (f : X ⟶ Y) (x : X _⦋n⦌)
    (h : (SSet.S.mk (f.app (op ⦋n⦌) x)).toN.dim = d) : Epi (ezU f x h) := by
  subst h
  simp only [ezU]
  infer_instance

/-- The `n`-simplex of `T_{ezY}` given by `x` and the Eilenberg–Zilber epimorphism of `f x`. -/
def ezPoint {d n : ℕ} (f : X ⟶ Y) (x : X _⦋n⦌)
    (h : (SSet.S.mk (f.app (op ⦋n⦌) x)).toN.dim = d) :
    (pullAlong f (nIndexSigma Y d (ezY f x h))).obj (op ⦋n⦌) :=
  pullPt f (ezY f x h) (ezU f x h) x (ez_compat f x h)

lemma ezPoint_snd {d n : ℕ} (f : X ⟶ Y) (x : X _⦋n⦌)
    (h : (SSet.S.mk (f.app (op ⦋n⦌) x)).toN.dim = d) :
    (pullback.snd (nIndexSigma Y d (ezY f x h)) f).app (op ⦋n⦌) (ezPoint f x h) = x :=
  pullPt_snd f (ezY f x h) (ezU f x h) x (ez_compat f x h)

/-- The value of `f` on the `i`-th face of `x`, expressed through the Eilenberg–Zilber
epimorphism of `x`. -/
lemma ez_face_val {d n : ℕ} (f : X ⟶ Y) (x : X _⦋n+1⦌)
    (h : (SSet.S.mk (f.app (op ⦋n+1⦌) x)).toN.dim = d) (i : Fin (n+2)) :
    f.app (op ⦋n⦌) (X.δ i x) =
      Y.map (SimplexCategory.δ i ≫ ezU f x h).op (nBase (ezY f x h)) := by
  rw [map_δ_map, ez_compat f x h, ← SSet.δ_naturality_apply]

/-- If the `i`-th face of `x` is again "good" (its image has nondegenerate part of dimension
`d`), then it has the same underlying nondegenerate simplex as `x`. -/
lemma ezY_δ {d n : ℕ} (f : X ⟶ Y) (x : X _⦋n+1⦌)
    (h : (SSet.S.mk (f.app (op ⦋n+1⦌) x)).toN.dim = d) (i : Fin (n+2))
    (h' : (SSet.S.mk (f.app (op ⦋n⦌) (X.δ i x))).toN.dim = d)
    (hv : Epi (SimplexCategory.δ i ≫ ezU f x h)) :
    ezY f (X.δ i x) h' = ezY f x h := by
  apply Subtype.ext
  show (SSet.S.mk (f.app (op ⦋n⦌) (X.δ i x))).toN = (SSet.S.mk (f.app (op ⦋n+1⦌) x)).toN
  have h1 : (SSet.S.mk (f.app (op ⦋n⦌) (X.δ i x))).toN =
      SSet.N.mk (nBase (ezY f x h)) (nBase_mem (ezY f x h)) := by
    rw [ez_face_val f x h i]
    exact ezFaceEpi (nBase (ezY f x h)) (nBase_mem (ezY f x h)) _ hv
  have h2 : (SSet.S.mk (f.app (op ⦋n+1⦌) x)).toN =
      SSet.N.mk (nBase (ezY f x h)) (nBase_mem (ezY f x h)) := by
    rw [← ez_compat f x h]
    exact ezFaceEpi (nBase (ezY f x h)) (nBase_mem (ezY f x h)) _ (ezU_epi f x h)
  rw [h1, h2]

/-- If the `i`-th face of `x` is again "good", then its Eilenberg–Zilber epimorphism is the
composite of that of `x` with the face inclusion. -/
lemma ezU_δ {d n : ℕ} (f : X ⟶ Y) (x : X _⦋n+1⦌)
    (h : (SSet.S.mk (f.app (op ⦋n+1⦌) x)).toN.dim = d) (i : Fin (n+2))
    (h' : (SSet.S.mk (f.app (op ⦋n⦌) (X.δ i x))).toN.dim = d)
    (hv : Epi (SimplexCategory.δ i ≫ ezU f x h)) :
    ezU f (X.δ i x) h' = SimplexCategory.δ i ≫ ezU f x h := by
  have hy : ezY f (X.δ i x) h' = ezY f x h := ezY_δ f x h i h' hv
  have hcomp : Y.map (ezU f (X.δ i x) h').op (nBase (ezY f x h)) = f.app (op ⦋n⦌) (X.δ i x) := by
    rw [← hy]
    exact ez_compat f (X.δ i x) h'
  have hcomp' : Y.map (SimplexCategory.δ i ≫ ezU f x h).op (nBase (ezY f x h)) =
      f.app (op ⦋n⦌) (X.δ i x) := (ez_face_val f x h i).symm
  haveI : Epi (ezU f (X.δ i x) h') := ezU_epi f (X.δ i x) h'
  exact SSet.unique_nonDegenerate_map Y (f.app (op ⦋n⦌) (X.δ i x)) (ezU f (X.δ i x) h')
    ⟨nBase (ezY f x h), nBase_mem (ezY f x h)⟩ hcomp.symm
    (SimplexCategory.δ i ≫ ezU f x h) ⟨nBase (ezY f x h), nBase_mem (ezY f x h)⟩ hcomp'.symm

end Ez


section MapsAux

/-- Evaluation of `nIndexSigma Y d y` at an arbitrary simplex of `Δ[d]`. -/
lemma nIndexSigma_app' {d n : ℕ} (y : nIndex Y d) (a : (Δ[d]).obj (op ⦋n⦌)) :
    (nIndexSigma Y d y).app (op ⦋n⦌) a =
      Y.map (SSet.stdSimplex.objEquiv a).op (nBase y) := by
  conv_lhs => rw [← Equiv.symm_apply_apply (SSet.stdSimplex.objEquiv (n := ⦋d⦌) (m := op ⦋n⦌)) a]
  exact nIndexSigma_app y (SSet.stdSimplex.objEquiv a)

/-- The two projections of a simplex of `T_y` have the same image in `Y`. -/
lemma pullback_condition_apply {d : ℕ} (f : X ⟶ Y) (y : nIndex Y d) (n : ℕ)
    (w : (pullAlong f (nIndexSigma Y d y)).obj (op ⦋n⦌)) :
    (nIndexSigma Y d y).app (op ⦋n⦌) ((pullback.fst (nIndexSigma Y d y) f).app (op ⦋n⦌) w) =
      f.app (op ⦋n⦌) ((pullback.snd (nIndexSigma Y d y) f).app (op ⦋n⦌) w) :=
  congr($(pullback.condition (f := nIndexSigma Y d y) (g := f)).app (op ⦋n⦌) w)

/-- The `X`-component of a simplex of `T_y` lies in `f ⁻¹' (sk (d+1))`. -/
lemma T_snd_mem (f : X ⟶ Y) {d : ℕ} (y : nIndex Y d) (n : ℕ)
    (w : (pullAlong f (nIndexSigma Y d y)).obj (op ⦋n⦌)) :
    (pullback.snd (nIndexSigma Y d y) f).app (op ⦋n⦌) w ∈
      (Work.StemsB.serreSubcomplex f (d+1)).obj (op ⦋n⦌) := by
  rw [Work.SSS.serreSubcomplexToN]
  rw [← pullback_condition_apply f y n w, nIndexSigma_app']
  exact Nat.lt_succ_of_le (toN_dim_le_map y _)

/-- The `X`-component of a simplex of `∂T_y` lies in `f ⁻¹' (sk d)`. -/
lemma bdry_snd_mem (f : X ⟶ Y) {d : ℕ} (y : nIndex Y d) (n : ℕ)
    (w : (bdryAlong f (nIndexSigma Y d y)).obj (op ⦋n⦌)) :
    (pullback.snd (nIndexSigma Y d y) f).app (op ⦋n⦌) (w : pullAlong f (nIndexSigma Y d y) _⦋n⦌) ∈
      (Work.StemsB.serreSubcomplex f d).obj (op ⦋n⦌) := by
  set w' : (pullAlong f (nIndexSigma Y d y)).obj (op ⦋n⦌) :=
    (w : (pullAlong f (nIndexSigma Y d y)).obj (op ⦋n⦌)) with hw'
  have hmem : w' ∈ (bdryAlong f (nIndexSigma Y d y)).obj (op ⦋n⦌) := by
    rw [hw']; exact w.2
  rw [Work.SSS.serreSubcomplexToN, ← pullback_condition_apply f y n w', nIndexSigma_app']
  exact ezFaceNonEpi (nBase y) (nBase_mem y) _ ((mem_bdry_iff y w').mp hmem)

/-- A point `pullPt f y v x` of `T_y` lies in `∂T_y` if and only if `v` is not an epimorphism. -/
lemma pullPt_mem_bdry_iff (f : X ⟶ Y) {d n : ℕ} (y : nIndex Y d) (v : ⦋n⦌ ⟶ ⦋d⦌)
    (x : X _⦋n⦌) (h : Y.map v.op (nBase y) = f.app (op ⦋n⦌) x) :
    pullPt f y v x h ∈ (bdryAlong f (nIndexSigma Y d y)).obj (op ⦋n⦌) ↔ ¬ Epi v := by
  rw [mem_bdry_iff y, pullPt_fst]
  simp

/-- A point `pullPt f y v x` of `T_y` does not lie in `∂T_y` if and only if `v` is an
epimorphism. -/
lemma pullPt_notMem_bdry_iff (f : X ⟶ Y) {d n : ℕ} (y : nIndex Y d) (v : ⦋n⦌ ⟶ ⦋d⦌)
    (x : X _⦋n⦌) (hh : Y.map v.op (nBase y) = f.app (op ⦋n⦌) x) :
    pullPt f y v x hh ∉ (bdryAlong f (nIndexSigma Y d y)).obj (op ⦋n⦌) ↔ Epi v := by
  rw [← not_iff_not]
  simp only [not_not]
  exact pullPt_mem_bdry_iff f y v x hh

end MapsAux


/-- Faces do not increase the dimension of the nondegenerate part. -/
lemma toN_dim_δ_le {Y : SSet.{0}} {n : ℕ} (z : Y _⦋n+1⦌) (i : Fin (n+2)) :
    (SSet.S.mk (Y.δ i z)).toN.dim ≤ (SSet.S.mk z).toN.dim := by
  have hle : (SSet.S.mk (Y.δ i z)).subcomplex ≤ (SSet.S.mk z).subcomplex :=
    SSet.S.subcomplex_map_le _ _ _ rfl
  have h1 : (SSet.S.mk (Y.δ i z)).toN ≤ (SSet.S.mk z).toN := by
    rw [SSet.N.le_iff, SSet.S.subcomplex_toN, SSet.S.subcomplex_toN]
    exact hle
  exact SSet.N.dim_le_of_le h1

/-- `pullPt` does not depend on the proof of the compatibility condition. -/
lemma pullPt_proof_irrel (f : X ⟶ Y) {d n : ℕ} (y : nIndex Y d) (v : ⦋n⦌ ⟶ ⦋d⦌)
    (x : X _⦋n⦌) (h₁ h₂ : Y.map v.op (nBase y) = f.app (op ⦋n⦌) x) :
    pullPt f y v x h₁ = pullPt f y v x h₂ :=
  congrArg Classical.choose (Subsingleton.elim _ _)

end

end Work.SSS
