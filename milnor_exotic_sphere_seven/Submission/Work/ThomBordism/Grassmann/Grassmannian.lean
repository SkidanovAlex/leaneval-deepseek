import Submission.Work.ThomBordism.Grassmann.Frame
import Submission.Work.TangentClasses.Bundle
import Submission.Work.ThomBordism.Grassmann.Linear
import Submission.Work.ThomBordism.Grassmann.Coord

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-!
# The oriented Grassmannian and its tautological bundle

`G̃r_k(ℝ^{k+m})` is the quotient of the Stiefel manifold `V_k(ℝ^{k+m})` of orthonormal `k`-frames
by the action of `SO(k)`; two frames are equivalent iff they span the same `k`-plane with the same
orientation.  This module builds

* the group `SO(k)` acting on frames (`SOk`, `SOk.act`) and the quotient `OG k m`;
* the **charts** `U_S`, one for each `k`-element set `S` of coordinates, and the proof that they
  cover (`isOpen_baseSet`, `exists_mem_baseSet`) — the cover is
  `Work.ThomBordism.Grassmann.exists_chartIdx_det_ne_zero`;
* the **transition functions** `coordChange S T` (the matrix `frameMatrix T f * (frameMatrix S f)⁻¹`
  read as a continuous linear map), with the cocycle `coordChange_comp`, the unit law
  `coordChange_self` and continuity `continuousOn_coordChange`;
* therefore the **tautological oriented rank-`k` bundle** `tautologicalBundle k m` as a
  `VectorBundleCore ℝ (OG k m) (Amb k) (ChartIdx k m)` over the *finite* cover `ChartIdx k m`.
-/

namespace Work.ThomBordism.Grassmann

open scoped Topology

noncomputable section

variable {k m : ℕ}

instance instCompactSpaceStiefel (k m : ℕ) : CompactSpace (Stiefel k m) := compactSpace_stiefel k m

/-! ## The group `SO(k)` acting on frames -/

/-- The group `SO(k)` of orthogonal `k × k` matrices of determinant `1`. -/
def SOk (k : ℕ) : Type := {A : Matrix (Fin k) (Fin k) ℝ // IsSO A}

namespace SOk

instance instOne (k : ℕ) : One (SOk k) := ⟨⟨1, IsSO.one⟩⟩
instance instMul (k : ℕ) : Mul (SOk k) := ⟨fun A B => ⟨A.1 * B.1, A.2.mul B.2⟩⟩

/-- The transpose of an element of `SO(k)` is its inverse. -/
def transpose (A : SOk k) : SOk k := ⟨A.1.transpose, A.2.transpose⟩

/-- The action of `SO(k)` on the Stiefel manifold: `(A · f)_i = ∑ j, A_{ji} f_j`. -/
def act (A : SOk k) (f : Stiefel k m) : Stiefel k m :=
  ⟨soActFun A.1 f.1, orthonormal_soActFun A.2.1 f.2⟩

@[simp] theorem act_one (f : Stiefel k m) : (1 : SOk k).act f = f := by
  apply Subtype.ext
  exact soActFun_one f.1

theorem act_mul (A B : SOk k) (f : Stiefel k m) : (A * B).act f = B.act (A.act f) := by
  apply Subtype.ext
  exact (soActFun_comp B.1 A.1 f.1).symm

theorem transpose_mul_self (A : SOk k) : A * A.transpose = 1 :=
  Subtype.ext A.2.mul_transpose_self

theorem act_transpose_act (A : SOk k) (f : Stiefel k m) : A.transpose.act (A.act f) = f := by
  rw [← act_mul, transpose_mul_self, act_one]

end SOk

/-- The orbit relation of the `SO(k)`-action on frames: the **oriented Grassmannian** is its
quotient. -/
def grassmannSetoid (k m : ℕ) : Setoid (Stiefel k m) where
  r f g := ∃ A : SOk k, g = A.act f
  iseqv :=
    { refl := fun f => ⟨1, (SOk.act_one f).symm⟩
      symm := by
        rintro f g ⟨A, rfl⟩
        exact ⟨A.transpose, (SOk.act_transpose_act A f).symm⟩
      trans := by
        rintro f g h ⟨A, rfl⟩ ⟨B, rfl⟩
        exact ⟨A * B, (SOk.act_mul A B f).symm⟩ }

/-- **The oriented Grassmannian** `G̃r_k(ℝ^{k+m})`: the quotient of the Stiefel manifold by the
action of `SO(k)`, i.e. the space of oriented `k`-dimensional subspaces of `ℝ^{k+m}`. -/
def OG (k m : ℕ) : Type := Quotient (grassmannSetoid k m)

instance instTopologicalSpaceOG (k m : ℕ) : TopologicalSpace (OG k m) :=
  inferInstanceAs (TopologicalSpace (Quotient (grassmannSetoid k m)))

instance instCompactSpaceOG (k m : ℕ) : CompactSpace (OG k m) :=
  inferInstanceAs (CompactSpace (Quotient (grassmannSetoid k m)))

instance instNonemptyOG (k m : ℕ) : Nonempty (OG k m) :=
  ⟨Quotient.mk'' (Classical.choice (nonempty_stiefel k m))⟩

/-- The quotient map `V_k(ℝ^{k+m}) → G̃r_k(ℝ^{k+m})`. -/
def ogMk (k m : ℕ) : C(Stiefel k m, OG k m) := ⟨Quotient.mk'', continuous_quotient_mk'⟩

/-! ## The charts -/

/-- The image in the Grassmannian of the frames whose `S`-th coordinate projection is invertible. -/
def baseSet (S : ChartIdx k m) : Set (OG k m) := Quotient.mk'' '' chartSet S

theorem continuous_frameMatrix (S : ChartIdx k m) :
    Continuous fun f : Stiefel k m => frameMatrix S f.1 := by
  refine continuous_matrix fun i j => ?_
  exact (EuclideanSpace.proj (𝕜 := ℝ)
      (((S.1.equivFinOfCardEq S.2).symm i : ↥S.1) : Fin (k+m))).continuous.comp
    ((continuous_apply j).comp continuous_subtype_val)

theorem chartSet_isOpen (S : ChartIdx k m) : IsOpen (chartSet S) := by
  have hcont : Continuous fun f : Stiefel k m => (frameMatrix S f.1).det :=
    (continuous_frameMatrix S).matrix_det
  have h : chartSet S
      = (fun f : Stiefel k m => (frameMatrix S f.1).det) ⁻¹' ({0}ᶜ : Set ℝ) := rfl
  rw [h]
  exact isOpen_compl_singleton.preimage hcont

theorem chartSet_saturated (S : ChartIdx k m) {f : Stiefel k m} (hf : f ∈ chartSet S) :
    ∀ {g : Stiefel k m}, (grassmannSetoid k m).r f g → g ∈ chartSet S := by
  intro g h
  obtain ⟨A, rfl⟩ := h
  simp only [mem_chartSet] at hf ⊢
  change (frameMatrix S (soActFun A.1 f.1)).det ≠ 0
  rw [det_frameMatrix_soActFun, A.2.2, mul_one]
  exact hf

theorem mem_baseSet_iff (S : ChartIdx k m) (f : Stiefel k m) :
    Quotient.mk'' f ∈ baseSet S ↔ f ∈ chartSet S := by
  constructor
  · rintro ⟨g, hg, hgf⟩
    exact chartSet_saturated S hg (Quotient.exact hgf)
  · intro hf; exact ⟨f, hf, rfl⟩

theorem isOpen_baseSet (S : ChartIdx k m) : IsOpen (baseSet S) := by
  have hpre : Quotient.mk'' ⁻¹' (baseSet S) = chartSet S := by
    ext f
    rw [Set.mem_preimage, mem_baseSet_iff]
  rw [isOpen_coinduced]
  show IsOpen ((Quotient.mk'' : Stiefel k m → OG k m) ⁻¹' baseSet S)
  rw [hpre]
  exact chartSet_isOpen S

theorem exists_mem_baseSet (x : OG k m) : ∃ S : ChartIdx k m, x ∈ baseSet S := by
  refine Quotient.inductionOn x fun f => ?_
  obtain ⟨S, hS⟩ := exists_chartIdx_det_ne_zero f.1 f.2.linearIndependent
  exact ⟨S, f, hS, rfl⟩

/-- The chart containing a point of the Grassmannian. -/
noncomputable def chartCover (x : OG k m) : ChartIdx k m := Classical.choose (exists_mem_baseSet x)

theorem mem_baseSet_chartCover (x : OG k m) : x ∈ baseSet (chartCover x) :=
  Classical.choose_spec (exists_mem_baseSet x)

/-! ## The transition functions -/

/-- The transition function from the chart `T` to the chart `S`, on frames: the matrix
`frameMatrix S f * (frameMatrix T f)⁻¹` as a continuous linear endomorphism of `ℝ^k` (and `0` where
the chart `T` does not contain the frame). -/
def coordChangeAux (S T : ChartIdx k m) (f : Stiefel k m) : Amb k →L[ℝ] Amb k :=
  if h : (frameMatrix S f.1).det ≠ 0 then matLin (frameMatrix T f.1 * (frameMatrix S f.1)⁻¹)
  else 0

theorem coordChangeAux_invariant (S T : ChartIdx k m) (A : SOk k) (f : Stiefel k m) :
    coordChangeAux S T (A.act f) = coordChangeAux S T f := by
  have hdet : (frameMatrix S (soActFun A.1 f.1)).det = (frameMatrix S f.1).det := by
    rw [det_frameMatrix_soActFun, A.2.2, mul_one]
  show (if h : (frameMatrix S (soActFun A.1 f.1)).det ≠ 0 then
        matLin (frameMatrix T (soActFun A.1 f.1) * (frameMatrix S (soActFun A.1 f.1))⁻¹) else 0)
      = (if h : (frameMatrix S f.1).det ≠ 0 then
        matLin (frameMatrix T f.1 * (frameMatrix S f.1)⁻¹) else 0)
  by_cases h : (frameMatrix S f.1).det ≠ 0
  · rw [dif_pos (by rw [hdet]; exact h), dif_pos h]
    rw [frameMatrix_mul_inv_invariant T S A.1 A.2 f.1 h]
  · rw [dif_neg (by rw [hdet]; exact h), dif_neg h]

/-- The transition function from the chart `T` to the chart `S` of the tautological bundle. -/
def coordChange (S T : ChartIdx k m) : OG k m → (Amb k →L[ℝ] Amb k) :=
  Quotient.lift (coordChangeAux S T) fun f g hfg => by
    obtain ⟨A, rfl⟩ := hfg
    exact (coordChangeAux_invariant S T A f).symm

theorem coordChange_mk (S T : ChartIdx k m) (f : Stiefel k m) :
    coordChange S T (Quotient.mk'' f) = coordChangeAux S T f := rfl

theorem continuousOn_coordChangeAux (S T : ChartIdx k m) :
    ContinuousOn (coordChangeAux S T) (chartSet S ∩ chartSet T) := by
  have h2 : ContinuousOn (fun f : Stiefel k m => frameMatrix T f.1) (chartSet S ∩ chartSet T) :=
    (continuous_frameMatrix T).continuousOn
  have h1 : ContinuousOn (fun f : Stiefel k m => (frameMatrix S f.1)⁻¹)
      (chartSet S ∩ chartSet T) := by
    refine (continuousOn_matrix_inv k).comp (continuous_frameMatrix S).continuousOn ?_
    intro f hf
    exact hf.1
  have hmain : ContinuousOn
      (fun f : Stiefel k m => matLin (frameMatrix T f.1 * (frameMatrix S f.1)⁻¹))
      (chartSet S ∩ chartSet T) :=
    continuous_matLin.comp_continuousOn (h2.mul h1)
  refine hmain.congr ?_
  intro f hf
  simp only [coordChangeAux]
  rw [dif_pos (show (frameMatrix S f.1).det ≠ 0 from hf.1)]

theorem continuousOn_coordChange (S T : ChartIdx k m) :
    ContinuousOn (coordChange S T) (baseSet S ∩ baseSet T) := by
  have hoopen : IsOpen (baseSet S ∩ baseSet T) := (isOpen_baseSet S).inter (isOpen_baseSet T)
  have hpre : (Quotient.mk'' ⁻¹' (baseSet S ∩ baseSet T)) = chartSet S ∩ chartSet T := by
    ext f
    rw [Set.mem_preimage, Set.mem_inter_iff, Set.mem_inter_iff, mem_baseSet_iff, mem_baseSet_iff]
  have hq : Topology.IsQuotientMap
      ((baseSet S ∩ baseSet T).restrictPreimage (Quotient.mk'' : Stiefel k m → OG k m)) :=
    Topology.IsQuotientMap.restrictPreimage_isOpen isQuotientMap_quotient_mk' hoopen
  have hcomp : ((baseSet S ∩ baseSet T).domRestrict (coordChange S T)) ∘
        ((baseSet S ∩ baseSet T).restrictPreimage (Quotient.mk'' : Stiefel k m → OG k m))
      = fun y : ↥(Quotient.mk'' ⁻¹' (baseSet S ∩ baseSet T)) => coordChangeAux S T y.1 := by
    funext y
    exact coordChange_mk S T y.1
  rw [continuousOn_iff_continuous_domRestrict, hq.isCoinducing.eq_coinduced,
    continuous_coinduced_dom]
  rw [hcomp, hpre]
  exact (continuousOn_iff_continuous_domRestrict.mp (continuousOn_coordChangeAux S T))

/-! ## The cocycle of the transition functions -/

theorem coordChangeAux_self (S : ChartIdx k m) (f : Stiefel k m) (hf : f ∈ chartSet S)
    (v : Amb k) : coordChangeAux S S f v = v := by
  have hunit : IsUnit (frameMatrix S f.1).det := isUnit_iff_ne_zero.mpr hf
  show (if h : (frameMatrix S f.1).det ≠ 0 then
      matLin (frameMatrix S f.1 * (frameMatrix S f.1)⁻¹) else 0) v = v
  rw [dif_pos (show (frameMatrix S f.1).det ≠ 0 from hf), Matrix.mul_nonsing_inv _ hunit,
    matLin_one]
  rfl

theorem coordChange_self (S : ChartIdx k m) (x : OG k m) (hx : x ∈ baseSet S) (v : Amb k) :
    coordChange S S x v = v := by
  obtain ⟨f, rfl⟩ : ∃ f : Stiefel k m, Quotient.mk'' f = x := Quotient.exists_rep x
  rw [coordChange_mk, coordChangeAux_self S f ((mem_baseSet_iff S f).mp hx) v]

theorem coordChangeAux_comp (S T U : ChartIdx k m) (f : Stiefel k m)
    (hS : f ∈ chartSet S) (hT : f ∈ chartSet T) (hU : f ∈ chartSet U) (v : Amb k) :
    coordChangeAux T U f (coordChangeAux S T f v) = coordChangeAux S U f v := by
  have hunitT : IsUnit (frameMatrix T f.1).det := isUnit_iff_ne_zero.mpr hT
  show (if h : (frameMatrix T f.1).det ≠ 0 then
        matLin (frameMatrix U f.1 * (frameMatrix T f.1)⁻¹) else 0)
      ((if h : (frameMatrix S f.1).det ≠ 0 then
        matLin (frameMatrix T f.1 * (frameMatrix S f.1)⁻¹) else 0) v)
    = (if h : (frameMatrix S f.1).det ≠ 0 then
        matLin (frameMatrix U f.1 * (frameMatrix S f.1)⁻¹) else 0) v
  rw [dif_pos (show (frameMatrix T f.1).det ≠ 0 from hT),
    dif_pos (show (frameMatrix S f.1).det ≠ 0 from hS),
    dif_pos (show (frameMatrix S f.1).det ≠ 0 from hS)]
  rw [← ContinuousLinearMap.comp_apply, ← matLin_mul]
  congr 1
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (frameMatrix T f.1)⁻¹ (frameMatrix T f.1)
      (frameMatrix S f.1)⁻¹, Matrix.nonsing_inv_mul _ hunitT, Matrix.one_mul]

theorem coordChange_comp (i j l : ChartIdx k m) (x : OG k m)
    (hx : x ∈ baseSet i ∩ baseSet j ∩ baseSet l) (v : Amb k) :
    coordChange j l x (coordChange i j x v) = coordChange i l x v := by
  obtain ⟨f, rfl⟩ : ∃ f : Stiefel k m, Quotient.mk'' f = x := Quotient.exists_rep x
  obtain ⟨hij, hl⟩ := hx
  obtain ⟨hi, hj⟩ := hij
  rw [coordChange_mk, coordChange_mk, coordChange_mk]
  exact coordChangeAux_comp i j l f ((mem_baseSet_iff i f).mp hi) ((mem_baseSet_iff j f).mp hj)
    ((mem_baseSet_iff l f).mp hl) v

/-! ## The tautological bundle -/

/-- **The tautological oriented rank-`k` real bundle over the oriented Grassmannian**: the bundle
whose fibre over an oriented `k`-plane `P` is `P` itself, presented by gluing data over the finite
cover `ChartIdx k m` (the `k`-element subsets of the coordinates).

The trivialisation over the chart `S` is the coordinate projection `p_S`; the transition functions
therefore have determinant of either sign.  This naive presentation is kept for the record (its
transition functions and their cocycle are used by the corrected, orientation-consistent bundle
`Oriented.tautologicalBundle`, which is *the* model's tautological bundle);
see `Submission/Work/ThomBordism/Grassmann/Oriented.lean`. -/
noncomputable def tautologicalBundleNaive (k m : ℕ) :
    Work.TangentClasses.RealBundle (OG k m) (Amb k) (ChartIdx k m) where
  baseSet := baseSet
  isOpen_baseSet := isOpen_baseSet
  indexAt := chartCover
  mem_baseSet_at := mem_baseSet_chartCover
  coordChange := coordChange
  coordChange_self := fun S x hx v => coordChange_self S x hx v
  continuousOn_coordChange := fun S T => continuousOn_coordChange S T
  coordChange_comp := fun i j l x hx v => coordChange_comp i j l x hx v

end

end Work.ThomBordism.Grassmann
