import Mathlib.RingTheory.PicardGroup
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Submission.Work.BoseBoxFock.bridge_defs
import Submission.Work.BoseBoxFock.exists_isometry_of_gram_general
import Submission.Work.BoseBoxFock.exists_orthonormal_offBox
import Submission.Work.BoseBoxFock.gramFamV
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.modeONBCplx` — the complex mode ONB of the honest box model

The physical one-particle vectors of the box model (`Work.BoseBoxFock.FamV`: the
χ-modes `Q(e^{ikx}χ_Λ)` and the θ-modes `e^{isx}θ_Λ`) live in the infinite
dimensional complex Hilbert space `L²(ℝ³; ℂ)`, while `HonestModes` gives their
**coordinates** in the finite dimensional model space `Fin m → ℂ` in the sense of
`Work.BoseBoxFock.CoordV` (only the *real* parts are pinned by `HonestModes`, via
`realIP`; the complex Gram matrix is `Work.BoseBoxFock.gramFamV`).

The proof constructs the modes `e l` explicitly:

* `W` is the span in `ℂ^m` of the coordinate rows `CoordV · i`; `inner_XLp` says
  that the coefficient map `α ↦ ∑ i, α i • XLp i` is an isometry onto the physical
  span with the coordinate map `α ↦ ∑ i, α i • CLp i`;
* `e l` is the physical vector with coordinates `W.starProjection δ_l` (a finite
  linear combination of the `XLp i`, with coefficients `α l` extracted from the
  spanning property of `W`), plus the off-box correction
  `∑ t, (Wᗮ.starProjection δ_l).ofLp t • b_t`, where the `b_t` are the explicitly
  constructed orthonormal functions supported off the box
  (`Work.BoseBoxFock.exists_orthonormal_offBox`).

The correction implements the complement of the projection: the Gram matrix of
`W.starProjection δ_l` is `W.starProjection`, that of the correction is
`1 - W.starProjection`, and their sum is `1`, so the `e l` are orthonormal.

Everything is carried out in `L²` (`MeasureTheory.Lp`), which carries Mathlib's
inner product structure; `MeasureTheory.L2.inner_def` converts the inner products
back to the integrals of the statement.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

open Work.BoseB4

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The label `0` of the cube carries momentum `0` (local copy, so that this module depends
only on the *statements* of the delegated nodes). -/
lemma kmomLab_zero' (ℓ : ℝ) (N : ℕ) : kmomLab ℓ N (0 : Lab N) = 0 := by
  have h0 : labVec N (0 : Lab N) = 0 := by
    funext i
    simp [labVec]
  rw [kmomLab, h0]
  ext i
  simp [Work.BoseB4.vec]

/-- The θ-mode at momentum `0` is the condensate. -/
lemma thetaExp_zero' (ℓ : ℝ) :
    Work.BoseK15.corpusBox.thetaExp ℓ (0 : EuclideanSpace ℝ (Fin 3)) =
      Work.BoseK15.corpusBox.thetaFun ℓ := by
  funext x
  simp [Work.BoseB4.BoxData.thetaExp_apply]

/-- The physical θ-vector at the label `0` is the condensate. -/
lemma FamV_inr_zero' (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (HM : HonestModes v μ) :
    FamV v μ HM (Sum.inr (0 : Lab HM.N)) = Work.BoseK15.corpusBox.thetaFun (ellH v μ) := by
  rw [FamV, kmomLab_zero' (ellH v μ) HM.N, thetaExp_zero']

/-- Every member of the physical family is `L²`. -/
lemma memLp_FamV' (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (HM : HonestModes v μ)
    (i : Lab HM.N ⊕ Lab HM.N) :
    MemLp (FamV v μ HM i) 2 (volume : Measure (EuclideanSpace ℝ (Fin 3))) := by
  obtain ⟨hq, ht, _⟩ := memLp_modes (ellH v μ) (ellH_pos v μ)
  rcases i with k | s
  · exact hq (kmomLab (ellH v μ) HM.N k)
  · exact ht (kmomLab (ellH v μ) HM.N s)

/-- The one-particle Hilbert space `L²(ℝ³; ℂ)` of the box model. -/
abbrev L2sp : Type :=
  MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))

/-! ## The two families in `L²` and in `ℂ^m` -/

/-- The physical family, as classes in `L²(ℝ³; ℂ)`. -/
def XLp (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (HM : HonestModes v μ)
    (i : Lab HM.N ⊕ Lab HM.N) : L2sp :=
  MemLp.toLp (FamV v μ HM i) (memLp_FamV' v μ HM i)

/-- The coordinate family, as vectors of `ℂ^m = EuclideanSpace ℂ (Fin m)`. -/
def CLp (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (HM : HonestModes v μ)
    (i : Lab HM.N ⊕ Lab HM.N) : EuclideanSpace ℂ (Fin HM.m) :=
  WithLp.toLp 2 (CoordV v μ HM i)

/-! ## The inner products of the two families -/

/-- The complex inner product of an arbitrary `L²` class with `XLp i` is the integral
of `conj · ·` against the physical vector `FamV i`. -/
lemma inner_F_XLp (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (HM : HonestModes v μ)
    (F : L2sp) (i : Lab HM.N ⊕ Lab HM.N) :
    inner ℂ F (XLp v μ HM i)
      = ∫ x, (starRingEnd ℂ) ((F : EuclideanSpace ℝ (Fin 3) → ℂ) x) * FamV v μ HM i x := by
  rw [XLp, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (memLp_FamV' v μ HM i)] with x hx
  rw [hx, RCLike.inner_apply]
  ring

/-- The pairing of two coordinate vectors is the explicit sum `∑ l, conj (a l) * b l`. -/
lemma inner_CLp (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (HM : HonestModes v μ)
    (i j : Lab HM.N ⊕ Lab HM.N) :
    inner ℂ (CLp v μ HM i) (CLp v μ HM j)
      = ∑ l : Fin HM.m, (starRingEnd ℂ) (CoordV v μ HM i l) * CoordV v μ HM j l := by
  rw [CLp, CLp, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [WithLp.ofLp_toLp, WithLp.ofLp_toLp, RCLike.inner_apply]
  ring

/-- **The Gram identity, at the level of `L²` and `ℂ^m`**: the complex Gram matrix of
the physical family is that of the coordinate family. -/
lemma inner_XLp (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (HM : HonestModes v μ)
    (i j : Lab HM.N ⊕ Lab HM.N) :
    inner ℂ (XLp v μ HM i) (XLp v μ HM j) = inner ℂ (CLp v μ HM i) (CLp v μ HM j) := by
  rw [inner_CLp,
    show inner ℂ (XLp v μ HM i) (XLp v μ HM j)
      = ∫ x, (starRingEnd ℂ) (FamV v μ HM i x) * FamV v μ HM j x from ?_]
  · exact gramFamV v μ HM i j
  · rw [XLp, XLp, MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp (memLp_FamV' v μ HM i),
      MemLp.coeFn_toLp (memLp_FamV' v μ HM j)] with x hi hj
    rw [hi, hj, RCLike.inner_apply]
    ring

/-! ## The off-box orthonormal family -/

/-- The explicitly constructed orthonormal family supported off the box
(`Work.BoseBoxFock.exists_orthonormal_offBox`), chosen once. -/
def offBoxFun (ℓ : ℝ) (hℓ : 0 < ℓ) (m : ℕ) : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ :=
  Classical.choose (exists_orthonormal_offBox ℓ hℓ m)

lemma offBoxFun_memLp (ℓ : ℝ) (hℓ : 0 < ℓ) (m : ℕ) (t : Fin m) :
    MemLp (offBoxFun ℓ hℓ m t) 2 (volume : Measure (EuclideanSpace ℝ (Fin 3))) :=
  (Classical.choose_spec (exists_orthonormal_offBox ℓ hℓ m)).1 t

lemma offBoxFun_eq_zero (ℓ : ℝ) (hℓ : 0 < ℓ) (m : ℕ) (t : Fin m)
    (x : EuclideanSpace ℝ (Fin 3))
    (hx : x ∈ Work.BoseB4.BoxData.boxL Work.BoseK15.corpusBox ℓ) :
    offBoxFun ℓ hℓ m t x = 0 :=
  (Classical.choose_spec (exists_orthonormal_offBox ℓ hℓ m)).2.1 t x hx

lemma offBoxFun_orth (ℓ : ℝ) (hℓ : 0 < ℓ) (m : ℕ) (t t' : Fin m) :
    (∫ x, (starRingEnd ℂ) (offBoxFun ℓ hℓ m t x) * offBoxFun ℓ hℓ m t' x)
      = if t = t' then 1 else 0 :=
  (Classical.choose_spec (exists_orthonormal_offBox ℓ hℓ m)).2.2 t t'

/-- The off-box family, as classes in `L²(ℝ³; ℂ)`. -/
def BLp (ℓ : ℝ) (hℓ : 0 < ℓ) (m : ℕ) (t : Fin m) : L2sp :=
  MemLp.toLp (offBoxFun ℓ hℓ m t) (offBoxFun_memLp ℓ hℓ m t)

lemma inner_BLp_BLp (ℓ : ℝ) (hℓ : 0 < ℓ) (m : ℕ) (t t' : Fin m) :
    inner ℂ (BLp ℓ hℓ m t) (BLp ℓ hℓ m t') = if t = t' then 1 else 0 := by
  rw [BLp, BLp, MeasureTheory.L2.inner_def]
  rw [← offBoxFun_orth ℓ hℓ m t t']
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (offBoxFun_memLp ℓ hℓ m t),
    MemLp.coeFn_toLp (offBoxFun_memLp ℓ hℓ m t')] with x ht ht'
  rw [ht, ht', RCLike.inner_apply]
  ring

/-- The off-box family is orthogonal to the physical family (the physical vectors are
supported in the box, where the `b_t` vanish). -/
lemma inner_BLp_XLp (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (HM : HonestModes v μ)
    (t : Fin HM.m) (i : Lab HM.N ⊕ Lab HM.N) :
    inner ℂ (BLp (ellH v μ) (ellH_pos v μ) HM.m t) (XLp v μ HM i) = 0 := by
  have hℓ : 0 < ellH v μ := ellH_pos v μ
  rw [inner_F_XLp]
  have hae : (fun x => (starRingEnd ℂ) ((BLp (ellH v μ) hℓ HM.m t : L2sp) x)
      * FamV v μ HM i x) =ᵐ[volume] fun _ => (0 : ℂ) := by
    filter_upwards [show ↑↑(BLp (ellH v μ) hℓ HM.m t) =ᵐ[volume]
        offBoxFun (ellH v μ) hℓ HM.m t from
      MemLp.coeFn_toLp (offBoxFun_memLp (ellH v μ) hℓ HM.m t)] with x hx
    rw [hx]
    by_cases hxb : x ∈ Work.BoseB4.BoxData.boxL Work.BoseK15.corpusBox (ellH v μ)
    · rw [offBoxFun_eq_zero (ellH v μ) hℓ HM.m t x hxb, map_zero, zero_mul]
    · have h2 : FamV v μ HM i x = 0 := by
        by_contra hc
        exact hxb (support_FamV v μ HM i hc)
      rw [h2, mul_zero]
  rw [integral_congr_ae hae]
  simp

/-- The coordinates of the standard basis vectors of `ℂ^m`. -/
lemma single_ofLp {m : ℕ} (l l' : Fin m) :
    (EuclideanSpace.single l (1 : ℂ)).ofLp l' = if l' = l then 1 else 0 := by
  simp [EuclideanSpace.single]

/-- The complex inner product of a coordinate vector pair, as the explicit sum of its
entries (the ℂ-conjugation convention of `RCLike.inner_apply`). -/
lemma inner_euclid_eq_sum {m : ℕ} (x y : EuclideanSpace ℂ (Fin m)) :
    inner ℂ x y = ∑ t : Fin m, y.ofLp t * (starRingEnd ℂ) (x.ofLp t) := by
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl fun t _ => by rw [RCLike.inner_apply]

theorem modeONBCplx (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ)
    (HM : Work.BoseBoxFock.HonestModes v μ) :
    ∃ e : Fin HM.m → EuclideanSpace ℝ (Fin 3) → ℂ,
      (∀ l l' : Fin HM.m,
        (∫ x, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0) ∧
      (∀ (k : Work.BoseBoxFock.Lab HM.N) (l : Fin HM.m),
        (∫ x, (starRingEnd ℂ) (e l x)
            * Work.BoseK15.corpusBox.qVec (Work.BoseBoxFock.ellH v μ)
                (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) HM.N k) x)
          = (((Work.BoseBoxFock.ellH v μ) ^ (3 / 2 : ℝ) * HM.f k l : ℝ) : ℂ)) ∧
      (∀ (s : Work.BoseBoxFock.Lab HM.N) (l : Fin HM.m), s ≠ 0 →
        (∫ x, (starRingEnd ℂ) (e l x)
            * Work.BoseK15.corpusBox.thetaExp (Work.BoseBoxFock.ellH v μ)
                (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) HM.N s) x)
          = (((Work.BoseBoxFock.ellH v μ) ^ (3 / 2 : ℝ) * HM.g s l : ℝ) : ℂ)) ∧
      (∀ l : Fin HM.m, l ≠ 0 →
        (∫ x, (starRingEnd ℂ) (e l x)
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) x) = 0) ∧
      (∫ x, (starRingEnd ℂ) (e 0 x)
        * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) x)
        = (((Work.BoseBoxFock.ellH v μ) ^ (3 / 2 : ℝ) : ℝ) : ℂ) := by
  classical
  have hℓ : 0 < ellH v μ := ellH_pos v μ
  -- the span of the coordinate rows and the coefficient extraction
  set W : Submodule ℂ (EuclideanSpace ℂ (Fin HM.m)) :=
    Submodule.span ℂ (Set.range (CLp v μ HM)) with hWdef
  have hCW : ∀ i : Lab HM.N ⊕ Lab HM.N, CLp v μ HM i ∈ W := by
    intro i
    rw [hWdef]
    exact Submodule.subset_span (Set.mem_range_self i)
  have hex : ∀ l : Fin HM.m, ∃ c : (Lab HM.N ⊕ Lab HM.N) → ℂ,
      ∑ i, c i • CLp v μ HM i = W.starProjection (EuclideanSpace.single l 1) := by
    intro l
    have h : W.starProjection (EuclideanSpace.single l 1) ∈ W :=
      Submodule.starProjection_apply_mem W _
    rw [hWdef] at h
    exact (Submodule.mem_span_range_iff_exists_fun ℂ).mp h
  let a : Fin HM.m → (Lab HM.N ⊕ Lab HM.N) → ℂ := fun l => Classical.choose (hex l)
  have ha : ∀ l, ∑ i, a l i • CLp v μ HM i = W.starProjection (EuclideanSpace.single l 1) :=
    fun l => Classical.choose_spec (hex l)
  -- the modes
  let E : Fin HM.m → L2sp := fun l => (∑ i, a l i • XLp v μ HM i)
      + ∑ t : Fin HM.m, (Wᗮ.starProjection (EuclideanSpace.single l 1)).ofLp t
          • BLp (ellH v μ) hℓ HM.m t
  -- the two projections of the standard basis vectors
  have hcomp : ∀ l : Fin HM.m, Wᗮ.starProjection (EuclideanSpace.single l 1)
      = EuclideanSpace.single l 1 - W.starProjection (EuclideanSpace.single l 1) := by
    intro l
    rw [Submodule.starProjection_orthogonal]
    simp
  -- the inner-product algebra of the two blocks
  have hA : ∀ (c : (Lab HM.N ⊕ Lab HM.N) → ℂ) (i : Lab HM.N ⊕ Lab HM.N),
      inner ℂ (∑ j, c j • XLp v μ HM j) (XLp v μ HM i)
        = inner ℂ (∑ j, c j • CLp v μ HM j) (CLp v μ HM i) := by
    intro c i
    rw [sum_inner, sum_inner]
    exact Finset.sum_congr rfl fun j _ => by rw [inner_smul_left, inner_smul_left, inner_XLp]
  have hB : ∀ (u : Fin HM.m → ℂ) (i : Lab HM.N ⊕ Lab HM.N),
      inner ℂ (∑ t, u t • BLp (ellH v μ) hℓ HM.m t) (XLp v μ HM i) = 0 := by
    intro u i
    rw [sum_inner]
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [inner_smul_left, inner_BLp_XLp, mul_zero]
  have hAB : ∀ (c : (Lab HM.N ⊕ Lab HM.N) → ℂ) (u : Fin HM.m → ℂ),
      inner ℂ (∑ j, c j • XLp v μ HM j)
        (∑ t, u t • BLp (ellH v μ) hℓ HM.m t) = 0 := by
    intro c u
    rw [sum_inner]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [inner_smul_left, inner_sum]
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun t _ => ?_)
    rw [inner_smul_right, ← inner_conj_symm, inner_BLp_XLp, map_zero, mul_zero]
  have hAA : ∀ (c c' : (Lab HM.N ⊕ Lab HM.N) → ℂ),
      inner ℂ (∑ j, c j • XLp v μ HM j) (∑ j, c' j • XLp v μ HM j)
        = inner ℂ (∑ j, c j • CLp v μ HM j) (∑ j, c' j • CLp v μ HM j) := by
    intro c c'
    rw [inner_sum_smul (x := XLp v μ HM) c c', inner_sum_smul (x := CLp v μ HM) c c']
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by rw [inner_XLp]
  have hBB : ∀ (u u' : Fin HM.m → ℂ),
      inner ℂ (∑ t, u t • BLp (ellH v μ) hℓ HM.m t)
        (∑ t, u' t • BLp (ellH v μ) hℓ HM.m t)
        = ∑ t, (starRingEnd ℂ) (u t) * u' t := by
    intro u u'
    rw [inner_sum_smul (x := BLp (ellH v μ) hℓ HM.m) u u']
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_eq_single t]
    · rw [inner_BLp_BLp, if_pos rfl, mul_one, starRingEnd_apply]
    · intro t' _ ht'
      rw [inner_BLp_BLp, if_neg (Ne.symm ht'), mul_zero]
    · intro ht
      exact absurd (Finset.mem_univ t) ht
  -- the modes pair with the physical family as the coordinates prescribe
  have hInnerE : ∀ (l : Fin HM.m) (i : Lab HM.N ⊕ Lab HM.N),
      inner ℂ (E l) (XLp v μ HM i) = CoordV v μ HM i l := by
    intro l i
    dsimp only [E]
    rw [inner_add_left, hB (fun t => (Wᗮ.starProjection (EuclideanSpace.single l 1)).ofLp t) i,
      add_zero, hA (a l) i, ha l, Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr (hCW i), EuclideanSpace.inner_single_left]
    simp [CLp]
  -- the modes are orthonormal
  have hEE : ∀ l l' : Fin HM.m, inner ℂ (E l) (E l') = if l = l' then 1 else 0 := by
    intro l l'
    have hcross1 : inner ℂ (∑ j, a l j • XLp v μ HM j)
        (∑ t : Fin HM.m, (Wᗮ.starProjection (EuclideanSpace.single l' 1)).ofLp t
          • BLp (ellH v μ) hℓ HM.m t) = 0 :=
      hAB (a l) (fun t => (Wᗮ.starProjection (EuclideanSpace.single l' 1)).ofLp t)
    have hcross2 : inner ℂ (∑ t : Fin HM.m,
          (Wᗮ.starProjection (EuclideanSpace.single l 1)).ofLp t • BLp (ellH v μ) hℓ HM.m t)
        (∑ j, a l' j • XLp v μ HM j) = 0 := by
      rw [← inner_conj_symm,
        hAB (a l') (fun t => (Wᗮ.starProjection (EuclideanSpace.single l 1)).ofLp t),
        map_zero]
    have hphys : inner ℂ (∑ j, a l j • XLp v μ HM j) (∑ j, a l' j • XLp v μ HM j)
        = inner ℂ (W.starProjection (EuclideanSpace.single l 1))
            (W.starProjection (EuclideanSpace.single l' 1)) := by
      rw [hAA (a l) (a l'), ha l, ha l']
    have hcorr : inner ℂ (∑ t : Fin HM.m,
          (Wᗮ.starProjection (EuclideanSpace.single l 1)).ofLp t • BLp (ellH v μ) hℓ HM.m t)
        (∑ t : Fin HM.m, (Wᗮ.starProjection (EuclideanSpace.single l' 1)).ofLp t
          • BLp (ellH v μ) hℓ HM.m t)
        = inner ℂ (Wᗮ.starProjection (EuclideanSpace.single l 1))
            (Wᗮ.starProjection (EuclideanSpace.single l' 1)) := by
      rw [hBB (fun t => (Wᗮ.starProjection (EuclideanSpace.single l 1)).ofLp t)
        (fun t => (Wᗮ.starProjection (EuclideanSpace.single l' 1)).ofLp t), inner_euclid_eq_sum]
      exact Finset.sum_congr rfl fun t _ => by ring
    dsimp only [E]
    rw [inner_add_left, inner_add_right, inner_add_right, hcross1, hcross2,
      add_zero, zero_add, hphys, hcorr,
      Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem W _),
      Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem Wᗮ _),
      ← inner_add_right,
      show W.starProjection (EuclideanSpace.single l' 1)
          + Wᗮ.starProjection (EuclideanSpace.single l' 1) = EuclideanSpace.single l' 1 from by
        rw [hcomp l']; abel]
    rw [EuclideanSpace.inner_single_left, single_ofLp l' l]
    simp
  refine ⟨fun l => (E l : EuclideanSpace ℝ (Fin 3) → ℂ), ?_, ?_, ?_, ?_, ?_⟩
  · intro l l'
    rw [← hEE l l', MeasureTheory.L2.inner_def]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [RCLike.inner_apply]
    ring
  · intro k l
    rw [show Work.BoseK15.corpusBox.qVec (ellH v μ)
            (kmomLab (ellH v μ) HM.N k) = FamV v μ HM (Sum.inl k) from rfl]
    rw [← inner_F_XLp v μ HM (E l) (Sum.inl k), hInnerE l (Sum.inl k)]
    rfl
  · intro s l hs
    rw [show Work.BoseK15.corpusBox.thetaExp (ellH v μ)
            (kmomLab (ellH v μ) HM.N s) = FamV v μ HM (Sum.inr s) from rfl]
    rw [← inner_F_XLp v μ HM (E l) (Sum.inr s), hInnerE l (Sum.inr s)]
    simp only [CoordV, if_neg hs]
  · intro l hl
    rw [← FamV_inr_zero' v μ HM]
    rw [← inner_F_XLp v μ HM (E l) (Sum.inr 0), hInnerE l (Sum.inr 0)]
    show (if (0 : Lab HM.N) = 0 then
        (if l = 0 then (((ellH v μ) ^ (3 / 2 : ℝ) : ℝ) : ℂ) else 0)
      else ((ellH v μ) ^ (3 / 2 : ℝ) * HM.g (0 : Lab HM.N) l : ℝ)) = 0
    rw [if_pos rfl, if_neg hl]
  · rw [← FamV_inr_zero' v μ HM]
    rw [← inner_F_XLp v μ HM (E 0) (Sum.inr 0), hInnerE 0 (Sum.inr 0)]
    show (if (0 : Lab HM.N) = 0 then
        (if (0 : Fin HM.m) = 0 then (((ellH v μ) ^ (3 / 2 : ℝ) : ℝ) : ℂ) else 0)
      else ((ellH v μ) ^ (3 / 2 : ℝ) * HM.g (0 : Lab HM.N) (0 : Fin HM.m) : ℝ))
        = (((ellH v μ) ^ (3 / 2 : ℝ) : ℝ) : ℂ)
    rw [if_pos rfl, if_pos rfl]

end Work.BoseBoxFock
