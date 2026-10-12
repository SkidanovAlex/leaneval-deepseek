import Mathlib.RingTheory.PicardGroup
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Submission.Work.BoseBoxFock.exists_boxOrthFam
import Submission.Work.BoseBoxFock.memLp_top_modes
import Submission.Work.BoseBoxFock.modeFam_independent
import Submission.Work.BoseBoxFock.modeONBCplx
import Submission.Work.BoseBoxFock.modeProd_realIP
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.modeONBCplx_phys` — the box-supported complex mode ONB

`Work.BoseBoxFock.modeONBCplx` produces the complex ONB of the honest box model whose
coordinate span is the model space `ℂ^m`, but its modes carry an *off-box* correction
(`Work.BoseBoxFock.exists_orthonormal_offBox`), so they are not supported in the box.

This module re-runs the same construction with the off-box family replaced by a family
`b : Fin m → ℝ³ → ℂ` of **bounded functions supported in the box** which is orthonormal
and orthogonal to the whole physical mode family (`Work.BoseBoxFock.exists_boxOrthFam`,
built from the disjoint slab decomposition of the box and a dimension count in the
kernel of the slab-integral map).  The resulting modes `e l` are explicit functions
`∑_i a l i · FamV i + ∑_t c_{l t} · b t`, hence box-supported and a.e. equal to the
`L²` classes `E l` of the `modeONBCplx` construction; the pairings and the orthonormality
are transferred from the `L²` inner products along that a.e. equality
(`integral_congr_ae` + `MeasureTheory.L2.inner_def`).

The two extra conjuncts (`Function.support (e l) ⊆ boxL ℓ`, `MemLp (e l) ⊤`) are what
the box ↔ model dictionary needs to form the mode products `modeProd e` inside the box
(`BF3B_PLAN_S6.md` §2).
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## a.e. bookkeeping helper -/

/-- The pointwise sum of a finite family of `Lp` classes, evaluated. -/
lemma Lp_coeFn_finset_sum {α E : Type*} [MeasurableSpace α] {μ : Measure α} {p : ENNReal}
    [NormedAddCommGroup E] {ι : Type*} (s : Finset ι) (f : ι → Lp E p μ) :
    ((∑ i ∈ s, f i : Lp E p μ) : α → E) =ᵐ[μ] fun x => ∑ i ∈ s, ((f i : α → E) x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty]
      filter_upwards [Lp.coeFn_zero E p μ] with x hx
      simpa using hx
  | insert a s ha ih =>
      have h1 : ((∑ i ∈ insert a s, f i : Lp E p μ) : α → E)
          =ᵐ[μ] (((f a + ∑ i ∈ s, f i : Lp E p μ)) : α → E) := by
        rw [Finset.sum_insert ha]
      have h2 : (((f a + ∑ i ∈ s, f i : Lp E p μ)) : α → E)
          =ᵐ[μ] (fun x => ∑ i ∈ insert a s, ((f i : α → E) x)) := by
        filter_upwards [Lp.coeFn_add (f a) (∑ i ∈ s, f i), ih] with x hxa hxb
        rw [hxa, Pi.add_apply, hxb, Finset.sum_insert ha]
      exact h1.trans h2

/-! ## the theorem -/

theorem modeONBCplx_phys (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ)
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
      (∫ x, (starRingEnd ℂ) (e 0 x)
        * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) x)
        = (((Work.BoseBoxFock.ellH v μ) ^ (3 / 2 : ℝ) : ℝ) : ℂ) ∧
      (∀ l : Fin HM.m,
        Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ)) ∧
      (∀ l : Fin HM.m, MeasureTheory.MemLp (e l) ⊤ MeasureTheory.volume) := by
  classical
  have hℓ : 0 < ellH v μ := ellH_pos v μ
  obtain ⟨hqtop, httop, hθtop⟩ := memLp_top_modes (ellH v μ) hℓ
  have hFamVtop : ∀ i : Lab HM.N ⊕ Lab HM.N, MemLp (FamV v μ HM i) ⊤ volume := by
    intro i
    rcases i with k | s
    · exact hqtop (kmomLab (ellH v μ) HM.N k)
    · exact httop (kmomLab (ellH v μ) HM.N s)
  obtain ⟨b, hbtop, hbmem2, hbsupp, hborth, hboff⟩ :=
    exists_boxOrthFam (ellH v μ) hℓ (FamV v μ HM) (fun i => memLp_FamV' v μ HM i) HM.m
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
  -- the box family as `L²` classes
  let Bb : Fin HM.m → L2sp := fun t => MemLp.toLp (b t) (hbmem2 t)
  have hBbcoe : ∀ t, ((Bb t : L2sp) : EuclideanSpace ℝ (Fin 3) → ℂ) =ᵐ[volume] b t :=
    fun t => MemLp.coeFn_toLp (hbmem2 t)
  let cf : Fin HM.m → Fin HM.m → ℂ :=
    fun l t => (Wᗮ.starProjection (EuclideanSpace.single l 1)).ofLp t
  let E : Fin HM.m → L2sp := fun l => (∑ i, a l i • XLp v μ HM i) + ∑ t, cf l t • Bb t
  -- the inner products of the two blocks
  have hBb_off : ∀ (t : Fin HM.m) (i : Lab HM.N ⊕ Lab HM.N),
      inner ℂ (Bb t) (XLp v μ HM i) = 0 := by
    intro t i
    rw [inner_F_XLp v μ HM (Bb t) i]
    rw [show (∫ x, (starRingEnd ℂ) (((Bb t : L2sp) :
            EuclideanSpace ℝ (Fin 3) → ℂ) x) * FamV v μ HM i x)
        = ∫ x, (starRingEnd ℂ) (b t x) * FamV v μ HM i x from ?_]
    · exact hboff t i
    · refine integral_congr_ae ?_
      filter_upwards [hBbcoe t] with x hx
      rw [hx]
  have hBb_orth : ∀ t t' : Fin HM.m, inner ℂ (Bb t) (Bb t') = if t = t' then 1 else 0 := by
    intro t t'
    rw [MeasureTheory.L2.inner_def]
    rw [show (∫ a, inner ℂ (((Bb t : L2sp) : EuclideanSpace ℝ (Fin 3) → ℂ) a)
            (((Bb t' : L2sp) : EuclideanSpace ℝ (Fin 3) → ℂ) a))
        = ∫ a, (starRingEnd ℂ) (b t a) * b t' a from ?_]
    · exact hborth t t'
    · refine integral_congr_ae ?_
      filter_upwards [hBbcoe t, hBbcoe t'] with x h1 h2
      rw [h1, h2, RCLike.inner_apply]
      ring
  have hcomp : ∀ l : Fin HM.m, Wᗮ.starProjection (EuclideanSpace.single l 1)
      = EuclideanSpace.single l 1 - W.starProjection (EuclideanSpace.single l 1) := by
    intro l
    rw [Submodule.starProjection_orthogonal]
    simp
  have hA : ∀ (c : (Lab HM.N ⊕ Lab HM.N) → ℂ) (i : Lab HM.N ⊕ Lab HM.N),
      inner ℂ (∑ j, c j • XLp v μ HM j) (XLp v μ HM i)
        = inner ℂ (∑ j, c j • CLp v μ HM j) (CLp v μ HM i) := by
    intro c i
    rw [sum_inner, sum_inner]
    exact Finset.sum_congr rfl fun j _ => by rw [inner_smul_left, inner_smul_left, inner_XLp]
  have hB : ∀ (u : Fin HM.m → ℂ) (i : Lab HM.N ⊕ Lab HM.N),
      inner ℂ (∑ t, u t • Bb t) (XLp v μ HM i) = 0 := by
    intro u i
    rw [sum_inner]
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [inner_smul_left, hBb_off t i, mul_zero]
  have hAB : ∀ (c : (Lab HM.N ⊕ Lab HM.N) → ℂ) (u : Fin HM.m → ℂ),
      inner ℂ (∑ j, c j • XLp v μ HM j) (∑ t, u t • Bb t) = 0 := by
    intro c u
    rw [sum_inner]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [inner_smul_left, inner_sum]
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun t _ => ?_)
    rw [inner_smul_right, ← inner_conj_symm, hBb_off t j, map_zero, mul_zero]
  have hAA : ∀ (c c' : (Lab HM.N ⊕ Lab HM.N) → ℂ),
      inner ℂ (∑ j, c j • XLp v μ HM j) (∑ j, c' j • XLp v μ HM j)
        = inner ℂ (∑ j, c j • CLp v μ HM j) (∑ j, c' j • CLp v μ HM j) := by
    intro c c'
    rw [inner_sum_smul (x := XLp v μ HM) c c', inner_sum_smul (x := CLp v μ HM) c c']
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by rw [inner_XLp]
  have hBB : ∀ (u u' : Fin HM.m → ℂ),
      inner ℂ (∑ t, u t • Bb t) (∑ t, u' t • Bb t)
        = ∑ t, (starRingEnd ℂ) (u t) * u' t := by
    intro u u'
    rw [inner_sum_smul (x := Bb) u u']
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_eq_single t]
    · rw [hBb_orth, if_pos rfl, mul_one, starRingEnd_apply]
    · intro t' _ ht'
      rw [hBb_orth, if_neg (Ne.symm ht'), mul_zero]
    · intro ht
      exact absurd (Finset.mem_univ t) ht
  -- the pairings of the modes with the physical family
  have hInnerE : ∀ (l : Fin HM.m) (i : Lab HM.N ⊕ Lab HM.N),
      inner ℂ (E l) (XLp v μ HM i) = CoordV v μ HM i l := by
    intro l i
    dsimp only [E]
    rw [inner_add_left, hB (cf l) i, add_zero, hA (a l) i, ha l,
      Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr (hCW i), EuclideanSpace.inner_single_left]
    simp [CLp]
  have hEE : ∀ l l' : Fin HM.m, inner ℂ (E l) (E l') = if l = l' then 1 else 0 := by
    intro l l'
    have hcross1 : inner ℂ (∑ j, a l j • XLp v μ HM j)
        (∑ t : Fin HM.m, cf l' t • Bb t) = 0 := hAB (a l) (cf l')
    have hcross2 : inner ℂ (∑ t : Fin HM.m, cf l t • Bb t)
        (∑ j, a l' j • XLp v μ HM j) = 0 := by
      rw [← inner_conj_symm, hAB (a l') (cf l), map_zero]
    have hphys : inner ℂ (∑ j, a l j • XLp v μ HM j) (∑ j, a l' j • XLp v μ HM j)
        = inner ℂ (W.starProjection (EuclideanSpace.single l 1))
            (W.starProjection (EuclideanSpace.single l' 1)) := by
      rw [hAA (a l) (a l'), ha l, ha l']
    have hcorr : inner ℂ (∑ t : Fin HM.m, cf l t • Bb t)
        (∑ t : Fin HM.m, cf l' t • Bb t)
        = inner ℂ (Wᗮ.starProjection (EuclideanSpace.single l 1))
            (Wᗮ.starProjection (EuclideanSpace.single l' 1)) := by
      rw [hBB (cf l) (cf l'), inner_euclid_eq_sum]
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
  -- the explicit function realisation
  let e : Fin HM.m → EuclideanSpace ℝ (Fin 3) → ℂ := fun l x =>
    (∑ i, a l i * FamV v μ HM i x) + ∑ t : Fin HM.m, cf l t * b t x
  have hsmulXLp : ∀ (l : Fin HM.m) (i : Lab HM.N ⊕ Lab HM.N),
      ((a l i • XLp v μ HM i : L2sp) : EuclideanSpace ℝ (Fin 3) → ℂ)
        =ᵐ[volume] fun x => a l i * FamV v μ HM i x := by
    intro l i
    refine (Lp.coeFn_smul (a l i) (XLp v μ HM i)).trans ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_FamV' v μ HM i)] with x hx
    simp only [XLp, Pi.smul_apply, smul_eq_mul]
    rw [hx]
  have hsmulB : ∀ (l t : Fin HM.m),
      ((cf l t • Bb t : L2sp) : EuclideanSpace ℝ (Fin 3) → ℂ)
        =ᵐ[volume] fun x => cf l t * b t x := by
    intro l t
    refine (Lp.coeFn_smul (cf l t) (Bb t)).trans ?_
    filter_upwards [hBbcoe t] with x hx
    rw [Pi.smul_apply, hx, smul_eq_mul]
  have hpartXLp : ∀ l : Fin HM.m,
      ((∑ i, a l i • XLp v μ HM i : L2sp) : EuclideanSpace ℝ (Fin 3) → ℂ)
        =ᵐ[volume] (fun x => ∑ i, a l i * FamV v μ HM i x) := by
    intro l
    refine (Lp_coeFn_finset_sum Finset.univ (fun i => a l i • XLp v μ HM i)).trans ?_
    have hall : ∀ᶠ x in MeasureTheory.ae volume, ∀ i : Lab HM.N ⊕ Lab HM.N,
        (((a l i • XLp v μ HM i : L2sp)) : EuclideanSpace ℝ (Fin 3) → ℂ) x
          = a l i * FamV v μ HM i x := Filter.eventually_all.2 (fun i => hsmulXLp l i)
    filter_upwards [hall] with x hx
    exact Finset.sum_congr rfl fun i _ => hx i
  have hpartB : ∀ l : Fin HM.m,
      ((∑ t, cf l t • Bb t : L2sp) : EuclideanSpace ℝ (Fin 3) → ℂ)
        =ᵐ[volume] (fun x => ∑ t, cf l t * b t x) := by
    intro l
    refine (Lp_coeFn_finset_sum Finset.univ (fun t => cf l t • Bb t)).trans ?_
    have hall : ∀ᶠ x in MeasureTheory.ae volume, ∀ t : Fin HM.m,
        (((cf l t • Bb t : L2sp)) : EuclideanSpace ℝ (Fin 3) → ℂ) x = cf l t * b t x :=
      Filter.eventually_all.2 (fun t => hsmulB l t)
    filter_upwards [hall] with x hx
    exact Finset.sum_congr rfl fun t _ => hx t
  have he : ∀ l : Fin HM.m,
      e l =ᵐ[volume] ((E l : L2sp) : EuclideanSpace ℝ (Fin 3) → ℂ) := by
    intro l
    have hEeq : E l = (∑ i, a l i • XLp v μ HM i) + (∑ t, cf l t • Bb t) := rfl
    have h1 : ((E l : L2sp) : EuclideanSpace ℝ (Fin 3) → ℂ) =ᵐ[volume]
        (((∑ i, a l i • XLp v μ HM i : L2sp) : EuclideanSpace ℝ (Fin 3) → ℂ)
          + ((∑ t, cf l t • Bb t : L2sp) : EuclideanSpace ℝ (Fin 3) → ℂ)) := by
      rw [hEeq]
      exact Lp.coeFn_add _ _
    have h2 : e l =ᵐ[volume]
        (((∑ i, a l i • XLp v μ HM i : L2sp) : EuclideanSpace ℝ (Fin 3) → ℂ)
          + ((∑ t, cf l t • Bb t : L2sp) : EuclideanSpace ℝ (Fin 3) → ℂ)) := by
      filter_upwards [hpartXLp l, hpartB l] with x hx hy
      rw [Pi.add_apply, hx, hy]
    exact h2.trans h1.symm
  have hpair : ∀ (l : Fin HM.m) (i : Lab HM.N ⊕ Lab HM.N),
      (∫ x, (starRingEnd ℂ) (e l x) * FamV v μ HM i x) = CoordV v μ HM i l := by
    intro l i
    have h : (∫ x, (starRingEnd ℂ) (e l x) * FamV v μ HM i x)
        = ∫ x, (starRingEnd ℂ) (((E l : L2sp) :
            EuclideanSpace ℝ (Fin 3) → ℂ) x) * FamV v μ HM i x := by
      refine integral_congr_ae ?_
      filter_upwards [he l] with x hx
      rw [hx]
    rw [h, ← inner_F_XLp v μ HM (E l) i, hInnerE l i]
  refine ⟨e, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l l'
    rw [← hEE l l', MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [he l, he l'] with x hx hx'
    rw [hx, hx', RCLike.inner_apply]
    ring
  · intro k l
    rw [show Work.BoseK15.corpusBox.qVec (ellH v μ)
        (kmomLab (ellH v μ) HM.N k) = FamV v μ HM (Sum.inl k) from rfl]
    rw [hpair l (Sum.inl k)]
    rfl
  · intro s l hs
    rw [show Work.BoseK15.corpusBox.thetaExp (ellH v μ)
        (kmomLab (ellH v μ) HM.N s) = FamV v μ HM (Sum.inr s) from rfl]
    rw [hpair l (Sum.inr s)]
    simp only [CoordV, if_neg hs]
  · rw [← FamV_inr_zero' v μ HM]
    rw [hpair 0 (Sum.inr 0)]
    show (if (0 : Lab HM.N) = 0 then
        (if (0 : Fin HM.m) = 0 then (((ellH v μ) ^ (3 / 2 : ℝ) : ℝ) : ℂ) else 0)
      else ((ellH v μ) ^ (3 / 2 : ℝ) * HM.g (0 : Lab HM.N) (0 : Fin HM.m) : ℝ))
        = (((ellH v μ) ^ (3 / 2 : ℝ) : ℝ) : ℂ)
    rw [if_pos rfl, if_pos rfl]
  · intro l x hx
    by_cases hxb : x ∈ Work.BoseK15.corpusBox.boxL (ellH v μ)
    · exact hxb
    · exfalso
      refine hx ?_
      have hA0 : (∑ i, a l i * FamV v μ HM i x) = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [show FamV v μ HM i x = 0 from by
          by_contra hc
          exact hxb (support_FamV v μ HM i (Function.mem_support.mpr hc))]
        ring
      have hB0 : (∑ t : Fin HM.m, cf l t * b t x) = 0 := by
        refine Finset.sum_eq_zero fun t _ => ?_
        rw [show b t x = 0 from by
          by_contra hc
          exact hxb (hbsupp t (Function.mem_support.mpr hc))]
        ring
      show e l x = 0
      rw [show e l x = (∑ i, a l i * FamV v μ HM i x)
          + ∑ t : Fin HM.m, cf l t * b t x from rfl, hA0, hB0, add_zero]
  · intro l
    have hmeas : AEStronglyMeasurable (e l) volume :=
      AEStronglyMeasurable.congr (MeasureTheory.Lp.aestronglyMeasurable (E l)) (he l).symm
    choose C hC using fun i : Lab HM.N ⊕ Lab HM.N => exists_bound_of_memLp_top (hFamVtop i)
    choose D hD using fun t : Fin HM.m => exists_bound_of_memLp_top (hbtop t)
    have hCall : ∀ᶠ x in MeasureTheory.ae volume, ∀ i : Lab HM.N ⊕ Lab HM.N, ‖FamV v μ HM i x‖ ≤ C i :=
      Filter.eventually_all.2 hC
    have hDall : ∀ᶠ x in MeasureTheory.ae volume, ∀ t : Fin HM.m, ‖b t x‖ ≤ D t :=
      Filter.eventually_all.2 hD
    refine MeasureTheory.memLp_top_of_bound hmeas
      ((∑ i, ‖a l i‖ * C i) + ∑ t : Fin HM.m, ‖cf l t‖ * D t) ?_
    filter_upwards [hCall, hDall] with x hx hY
    have h1 : ‖∑ i, a l i * FamV v μ HM i x‖ ≤ ∑ i, ‖a l i‖ * C i :=
      le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hx i) (norm_nonneg _))
    have h2 : ‖∑ t : Fin HM.m, cf l t * b t x‖ ≤ ∑ t : Fin HM.m, ‖cf l t‖ * D t :=
      le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun t _ => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hY t) (norm_nonneg _))
    calc ‖e l x‖ = ‖(∑ i, a l i * FamV v μ HM i x)
            + ∑ t : Fin HM.m, cf l t * b t x‖ := rfl
      _ ≤ _ + _ := norm_add_le _ _
      _ ≤ _ := add_le_add h1 h2

end Work.BoseBoxFock

