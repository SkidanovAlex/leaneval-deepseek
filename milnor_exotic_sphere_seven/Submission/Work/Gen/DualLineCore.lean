import Mathlib
import Submission.Work.Gen.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# The dual of a complex line bundle (gluing-data model)

For a rank-one complex bundle `Z` over `B` (gluing data over a cover `ι`), the **dual** bundle
`Work.Gen.dualLineCore Z` is the complex line bundle whose transition functions are the inverse
transitions: `coordChange i j x = Z.coordChange j i x` (which is `(Z.coordChange i j x)⁻¹` by the
cocycle condition, since for rank one the transitions are scalar multiplications).  This agrees with
the classical complex dual `Z*`, whose first Chern class is the negative of that of `Z`.

The main raison d'être of this module is the *definition*, so that a lemma about the Chern class of
the dual can be stated.  The identification `dualLineCore (tautLine n) = tautDual n` records that the
`Work.Gen.tautDual` of `Submission/Work/Gen/Basic.lean` is exactly the dual of `Work.Gen.tautLine`.
-/

open Work.Projective

namespace Work.Gen

noncomputable section

/-- **Any two `ℂ`-linear endomorphisms of `ℂ` commute** (they are both scalar multiplications). -/
theorem clm_fin_one_comm (f g : EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1))
    (v : EuclideanSpace ℂ (Fin 1)) : f (g v) = g (f v) := by
  set one : EuclideanSpace ℂ (Fin 1) := EuclideanSpace.single (0 : Fin 1) (1 : ℂ) with hone
  have hsmul : ∀ w : EuclideanSpace ℂ (Fin 1),
      w = (w.ofLp 0) • one := by
    intro w
    ext i; fin_cases i
    simp [hone, EuclideanSpace.single]
  have hf : ∀ (h : EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1))
      (w : EuclideanSpace ℂ (Fin 1)), h w = (w.ofLp 0) • h one := by
    intro h w
    conv_lhs => rw [hsmul w]
    rw [map_smul]
  rw [hf f (g v), hf g (f v), hf g v, hf f v]
  -- both sides are scalar multiples of `one`; commute the scalars
  have hfo : f one = (f one).ofLp 0 • one := hsmul (f one)
  have hgo : g one = (g one).ofLp 0 • one := hsmul (g one)
  have hsm : ∀ (c : ℂ) (w : EuclideanSpace ℂ (Fin 1)), (c • w).ofLp 0 = c * w.ofLp 0 := by
    intro c w; simp
  rw [hsm (v.ofLp 0) (g one), hsm (v.ofLp 0) (f one), hfo, hgo, smul_smul, smul_smul]
  rw [hsm ((g one).ofLp 0) one, hsm ((f one).ofLp 0) one]
  have hone1 : one.ofLp 0 = 1 := by simp [hone, EuclideanSpace.single]
  rw [hone1, mul_one, mul_one]
  ring

/-- **The dual of a complex line bundle**: the complex line bundle with the inverse transition
functions, written as `coordChange i j x = Z.coordChange j i x`. -/
def dualLineCore {B : Type} [TopologicalSpace B] {ι : Type}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) :
    VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι where
  baseSet i := Z.baseSet i
  isOpen_baseSet i := Z.isOpen_baseSet i
  indexAt x := Z.indexAt x
  mem_baseSet_at x := Z.mem_baseSet_at x
  coordChange i j x := Z.coordChange j i x
  coordChange_self i x _ v := Z.coordChange_self i x ‹x ∈ Z.baseSet i› v
  continuousOn_coordChange i j := by
    have h := Z.continuousOn_coordChange j i
    rwa [Set.inter_comm] at h
  coordChange_comp i j k x hx v := by
    have hxij : x ∈ Z.baseSet i ∩ Z.baseSet j := hx.1
    have hxjk : x ∈ Z.baseSet j ∩ Z.baseSet k := ⟨hxij.2, hx.2⟩
    have hxik : x ∈ Z.baseSet i ∩ Z.baseSet k := ⟨hxij.1, hx.2⟩
    have hxkj : x ∈ Z.baseSet k ∩ Z.baseSet j := ⟨hx.2, hxij.2⟩
    show Z.coordChange k j x (Z.coordChange j i x v) = Z.coordChange k i x v
    rw [clm_fin_one_comm (Z.coordChange k j x) (Z.coordChange j i x) v]
    exact Z.coordChange_comp k j i x ⟨hxkj, hxij.1⟩ v

@[simp] theorem dualLineCore_baseSet {B : Type} [TopologicalSpace B] {ι : Type}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) (i : ι) :
    (dualLineCore Z).baseSet i = Z.baseSet i := rfl

@[simp] theorem dualLineCore_indexAt {B : Type} [TopologicalSpace B] {ι : Type}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) (x : B) :
    (dualLineCore Z).indexAt x = Z.indexAt x := rfl

@[simp] theorem dualLineCore_coordChange {B : Type} [TopologicalSpace B] {ι : Type}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) (i j : ι) (x : B) :
    (dualLineCore Z).coordChange i j x = Z.coordChange j i x := rfl

/-- **`tautDual` is the dual of `tautLine`**: the two gluing data are literally the same (up to the
order of the transition indices). -/
theorem dualLineCore_tautLine (n : ℕ) :
    dualLineCore (tautLine n) = tautDual n := by
  rfl

end

end Work.Gen

namespace Work.Gen

open scoped BigOperators

noncomputable section

/-- **The positive gauge factor on the chart `i` of `ℂPⁿ`**: `1 + Σ_k ‖z_k/z_i‖²` in the chart `i`,
a smooth positive function on `chartSet i`.  It is the scale of the standard Hermitian metric on the
tautological line bundle (with the homogeneous representative normalised to have `i`-th coordinate
`1`); it satisfies `gaugeFun n i x = ‖homCoord n i j x‖² · gaugeFun n j x` on the overlap of the two
charts, which is exactly the cocycle relation that makes
`μ_i · conj` a fibrewise conjugate-linear isomorphism `tautLine n → tautDual n`. -/
def gaugeFun (n : ℕ) (i : Fin (n + 1)) (x : CP n) : ℝ :=
  1 + ∑ k : Fin n, ‖chartFun i x k‖ ^ 2

theorem gaugeFun_pos (n : ℕ) (i : Fin (n + 1)) (x : CP n) : 0 < gaugeFun n i x := by
  unfold gaugeFun
  positivity

end

end Work.Gen
