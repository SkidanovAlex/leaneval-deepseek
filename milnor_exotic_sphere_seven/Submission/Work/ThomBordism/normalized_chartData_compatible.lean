import Mathlib
import Submission.Work.ThomBordism.h0SignUnit
import Submission.Work.ThomBordism.localThom_unit_relation
import Submission.Work.ThomBordism.coeff_pm_one_of_normalized

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 3200000

namespace Work.ThomBordism

open CategoryTheory

/-!
# Compatibility of the normalised chart data of a Thom class

Let `Z → B` be a real bundle (as gluing data), `T` a Thom class of `Z` of degree `n`, `e` a
trivialisation of the fibre, and `d i ∈ H⁰(Z.baseSet i; ℤ)` the *coefficient* of `T.τ` over the
chart piece `Z.baseSet i` (so that `T.τ|_i = d i ⌣ τ_i` with `τ_i` the explicit chart class,
`Work.Thom.chartCoeff`).  Let `s i` be the *sign* class of `d i`, characterised pointwise by
`ptEv p (s i ⌣ d i) = |ptEv p (d i)|` (`Work.ThomBordism.h0SignUnit`).

The lemma below is the compatibility of the *normalised* local data `σ_i := s_i ⌣ τ_i` over the
overlap of two charts: it is the input of the descent `Work.ThomBordism.chartDataDescent` (the
pieces `c i := localThomMap τ_i 0 (s i)` must agree on `Z.baseSet i ∩ Z.baseSet j`).

The proof does not use any geometry of the charts: everything is read off from the hypotheses.

* `localThom_unit_relation` produces, over the intersection, a unit `u` with
  `τ_j = u ⌣ τ_i` (the two chart classes are Thom classes of the same bundle).
* Restricting the coefficient equation `hd i` to the intersection and cancelling the (injective)
  degree-zero local Thom map gives `d_i = d_j ⌣ u` there.
* Pointwise, `u` and the `d`'s are then determined: `u = d_i/d_j` has square `1`, so that
  `s_j ⌣ u = s_j (d_i/d_j) = s_i` (all values are integers, and `d_i = ±d_j`), i.e. the two
  normalised classes agree on the overlap.

The lemmas `chartClass_pdCohMap_reduce`, `chartClass_unit_relation_of_subset`, `ltMap_cup`,
`ltMap_inj` and `int_relation` above are the (reusable) pieces of the argument.
-/

/-! ## Reusable pieces -/

/-- **Restriction of the degree-zero local Thom map to a smaller piece**: restricting
`x ↦ π^*(x) ⌣ τ_i` from the chart piece `Z.baseSet i` to `W ⊆ Z.baseSet i` gives the degree-zero
local Thom map of the *restricted* chart class applied to the restriction of `x`.  This is
`Work.Thom.localThomMap_pdCohMap` in degree zero, with `Work.Thom.localThomOfChart_restrict`
replacing the restricted chart class, and the degree cast `0 + n = n` moved outside. -/
theorem chartClass_pdCohMap_reduce {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type} {n : ℕ}
    (Z : Work.TangentClasses.RealBundle B F ι) (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (i : ι) (W : Set B) (hW : W ⊆ Z.baseSet i) (x : Work.Thom.Coh ℤ 0 ↥(Z.baseSet i)) :
    (ModuleCat.Hom.hom (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' (Z.baseSet i)) (Z.proj ⁻¹' W) (Set.preimage_mono hW) n))
        ((Nat.zero_add n) ▸ (Work.Thom.localThomMap Z n (Z.baseSet i)
          ((Work.Thom.localThomOfChart Z n e i (Z.baseSet i) (fun _ hx => hx)).τ) 0 x))
      = (Nat.zero_add n) ▸ (Work.Thom.localThomMap Z n W
          ((Work.Thom.localThomOfChart Z n e i W hW).τ) 0
          ((Work.Thom.CohMap (TopCat.Hom.hom (Work.Cohomology.pdIncl (M := TopCat.of B)
            (Z.baseSet i) W hW)) ℤ 0).hom x)) := by
  have hmap : Work.Thom.localThomMap Z n W
      ((Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' (Z.baseSet i)) (Z.proj ⁻¹' W) (Set.preimage_mono hW) n).hom
        ((Work.Thom.localThomOfChart Z n e i (Z.baseSet i) (fun _ hx => hx)).τ)) 0
      ((Work.Thom.CohMap (TopCat.Hom.hom (Work.Cohomology.pdIncl (M := TopCat.of B)
        (Z.baseSet i) W hW)) ℤ 0).hom x)
    = (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' (Z.baseSet i)) (Z.proj ⁻¹' W) (Set.preimage_mono hW) (0 + n)).hom
        (Work.Thom.localThomMap Z n (Z.baseSet i)
          ((Work.Thom.localThomOfChart Z n e i (Z.baseSet i) (fun _ hx => hx)).τ) 0 x) := by
    have h := congrArg (fun (g : Work.Thom.Coh ℤ 0 ↥(Z.baseSet i) →ₗ[ℤ]
        Work.Thom.PieceCoh Z W (0 + n)) => g x)
      (congrArg ModuleCat.Hom.hom (Work.Thom.localThomMap_pdCohMap (Z := Z) (n := n)
        (U := Z.baseSet i) (W := W) hW
        ((Work.Thom.localThomOfChart Z n e i (Z.baseSet i) (fun _ hx => hx)).τ) 0))
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply] at h
    exact h
  have hτ := Work.Thom.localThomOfChart_restrict Z n e i W (Z.baseSet i) hW (fun _ hx => hx) hW
  rw [← hτ]
  rw [Work.Thom.cast_pdCohMap Z hW (Nat.zero_add n)
    (Work.Thom.localThomMap Z n (Z.baseSet i)
      ((Work.Thom.localThomOfChart Z n e i (Z.baseSet i) (fun _ hx => hx)).τ) 0 x)]
  rw [← hmap]

/-- **Two chart classes over the same piece differ by a unit.**  For two charts `i`, `j` of a real
bundle over a common piece `W`, the explicit chart Thom classes of `i` and `j` differ by the local
Thom map of a degree-zero class `u` with `u ⌣ u = 1`; this is
`Work.ThomBordism.localThom_unit_relation` applied to the two `Work.Thom.LocalThom` structures
constructed by `Work.Thom.localThomOfChart`. -/
theorem chartClass_unit_relation_of_subset {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type} {n : ℕ}
    (Z : Work.TangentClasses.RealBundle B F ι) (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (i j : ι) (W : Set B) (hWi : W ⊆ Z.baseSet i) (hWj : W ⊆ Z.baseSet j) :
    ∃ u : Work.Thom.Coh ℤ 0 ↥W,
      (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥W)) 0 0) u u
          = Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of ↥W)) ∧
      (Work.Thom.localThomOfChart Z n e j W hWj).τ
        = (Nat.zero_add n) ▸ (Work.Thom.localThomMap Z n W
            ((Work.Thom.localThomOfChart Z n e i W hWi).τ) 0 u) := by
  exact Work.ThomBordism.localThom_unit_relation Z (P := W)
    (Work.Thom.localThomOfChart Z n e i W hWi).τ
    (Work.Thom.localThomOfChart Z n e j W hWj).τ
    (fun k => (Work.Thom.localThomOfChart Z n e i W hWi).isThom k)
    (fun k => (Work.Thom.localThomOfChart Z n e j W hWj).isThom k)

/-- **The degree-zero local Thom map of a class which is itself a local Thom map of `u` is the
local Thom map of `x ↦ x ⌣ u`** (in degree zero, with the degree cast `0 + n = n` pushed outside).
This is `Work.ThomBordism.localThomMap_cup_general` in degree zero. -/
theorem ltMap_cup {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type} {n : ℕ}
    (Z : Work.TangentClasses.RealBundle B F ι) (W : Set B)
    (τ : Work.Thom.PieceCoh Z W n) (u : Work.Thom.Coh ℤ 0 ↥W) (x : Work.Thom.Coh ℤ 0 ↥W) :
    (Nat.zero_add n) ▸ (Work.Thom.localThomMap Z n W
        ((Nat.zero_add n) ▸ (Work.Thom.localThomMap Z n W τ 0 u)) 0 x)
      = (Nat.zero_add n) ▸ (Work.Thom.localThomMap Z n W τ 0
          ((Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥W)) 0 0) x u)) :=
  congrArg (fun y => (Nat.zero_add n) ▸ y)
    (Work.ThomBordism.localThomMap_cup_general Z n W τ u 0 x)

/-- **Injectivity of the degree-zero local Thom map**, transported along the degree cast
`0 + n = n`. -/
theorem ltMap_inj {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type} {n : ℕ}
    (Z : Work.TangentClasses.RealBundle B F ι) (W : Set B) (τ : Work.Thom.PieceCoh Z W n)
    (hτ : Function.Bijective (Work.Thom.localThomMap Z n W τ 0)) :
    Function.Injective (fun x : Work.Thom.Coh ℤ 0 ↥W =>
      (Nat.zero_add n) ▸ (Work.Thom.localThomMap Z n W τ 0 x)) := by
  intro x y hxy
  have h' := congrArg (fun z => (Nat.zero_add n).symm ▸ z) hxy
  rw [Work.Thom.zeroAdd_cancel Z n (Work.Thom.localThomMap Z n W τ 0 x),
      Work.Thom.zeroAdd_cancel Z n (Work.Thom.localThomMap Z n W τ 0 y)] at h'
  exact hτ.1 h'

/-- **The integer algebra of the normalisation.**  If `u² = 1`, `a = b u`, `s a = |a|`, `t b = |b|`
and `a ≠ 0` (all in `ℤ`), then `s = t u`.  (Indeed `u = ±1`, whence `a = ±b`; multiplying both
sides of the conclusion by `a` reduces the claim to `|b| = |a|`.) -/
theorem int_relation {a b s t u : ℤ} (hu : u * u = 1) (ha : a = b * u)
    (hI : s * a = a.natAbs) (hJ : t * b = b.natAbs) (ha0 : a ≠ 0) : s = t * u := by
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hu with hu1 | hu1
  · rw [hu1, mul_one] at ha ⊢
    have hb0 : b ≠ 0 := fun h => ha0 (by rw [ha, h])
    rw [ha] at hI
    exact mul_right_cancel₀ hb0 (hI.trans hJ.symm)
  · rw [hu1, mul_neg, mul_one] at ha ⊢
    have hb : b = -a := by linarith
    rw [hb, Int.natAbs_neg] at hJ
    have hcancel : (-t) * a = s * a := by
      rw [hI, neg_mul, ← hJ]
      ring
    have hts : -t = s := mul_right_cancel₀ ha0 hcancel
    exact hts.symm

/-- The inclusion of the piece `W` into the piece `A`. -/
noncomputable abbrev subIncl {B : Type} [TopologicalSpace B] (A W : Set B) (h : W ⊆ A) : C(↥W, ↥A) :=
  TopCat.Hom.hom (Work.Cohomology.pdIncl (M := TopCat.of B) A W h)

/-- The restriction of a degree-zero class along `subIncl`. -/
noncomputable abbrev cohRes {B : Type} [TopologicalSpace B] (A W : Set B) (h : W ⊆ A)
    (x : Work.Thom.Coh ℤ 0 ↥A) : Work.Thom.Coh ℤ 0 ↥W :=
  (Work.Thom.CohMap (subIncl A W h) ℤ 0).hom x

/-! ## The compatibility -/

theorem normalized_chartData_compatible {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type} {n : ℕ}
    (Z : Work.TangentClasses.RealBundle B F ι) (T : Work.Thom.ThomClass Z n)
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (d : (i : ι) → Work.Thom.Coh ℤ 0 ↥(Z.baseSet i))
    (hd : ∀ i : ι, (ModuleCat.Hom.hom (Work.Thom.PieceRes Z (Z.baseSet i) n)) T.τ
        = (Nat.zero_add n) ▸ (Work.Thom.localThomMap Z n (Z.baseSet i)
            ((Work.Thom.localThomOfChart Z n e i (Z.baseSet i) (fun _ hx => hx)).τ) 0 (d i)))
    (hdv : ∀ (i : ι) (p : ↥(Z.baseSet i)), Work.Thom.ptEv p (d i) ≠ 0)
    (s : (i : ι) → Work.Thom.Coh ℤ 0 ↥(Z.baseSet i))
    (hs : ∀ (i : ι) (p : ↥(Z.baseSet i)),
        Work.Thom.ptEv p ((Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.baseSet i))) 0 0)
          (s i) (d i)) = (Work.Thom.ptEv p (d i)).natAbs)
    (i j : ι) :
    (ModuleCat.Hom.hom (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' (Z.baseSet i)) (Z.proj ⁻¹' (Z.baseSet i ∩ Z.baseSet j))
        (Set.preimage_mono Set.inter_subset_left) n))
        ((Nat.zero_add n) ▸ (Work.Thom.localThomMap Z n (Z.baseSet i)
          ((Work.Thom.localThomOfChart Z n e i (Z.baseSet i) (fun _ hx => hx)).τ) 0 (s i)))
      = (ModuleCat.Hom.hom (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' (Z.baseSet j)) (Z.proj ⁻¹' (Z.baseSet i ∩ Z.baseSet j))
        (Set.preimage_mono Set.inter_subset_right) n))
        ((Nat.zero_add n) ▸ (Work.Thom.localThomMap Z n (Z.baseSet j)
          ((Work.Thom.localThomOfChart Z n e j (Z.baseSet j) (fun _ hx => hx)).τ) 0 (s j))) := by
  classical
  -- the unit relating the two chart classes over the intersection
  obtain ⟨u, huu, hchart⟩ :=
    chartClass_unit_relation_of_subset Z e i j (Z.baseSet i ∩ Z.baseSet j)
      Set.inter_subset_left Set.inter_subset_right
  -- both sides are computed by the restricted chart classes
  rw [chartClass_pdCohMap_reduce Z e i (Z.baseSet i ∩ Z.baseSet j) Set.inter_subset_left (s i),
      chartClass_pdCohMap_reduce Z e j (Z.baseSet i ∩ Z.baseSet j) Set.inter_subset_right (s j)]
  -- the coefficient equation, restricted to the intersection
  have hPiece : ∀ (l : ι) (hWl : Z.baseSet i ∩ Z.baseSet j ⊆ Z.baseSet l),
      (ModuleCat.Hom.hom (Work.Thom.PieceRes Z (Z.baseSet i ∩ Z.baseSet j) n)) T.τ
        = (Nat.zero_add n) ▸ (Work.Thom.localThomMap Z n (Z.baseSet i ∩ Z.baseSet j)
          ((Work.Thom.localThomOfChart Z n e l (Z.baseSet i ∩ Z.baseSet j) hWl).τ) 0
          ((Work.Thom.CohMap (TopCat.Hom.hom (Work.Cohomology.pdIncl (M := TopCat.of B)
            (Z.baseSet l) (Z.baseSet i ∩ Z.baseSet j) hWl)) ℤ 0).hom (d l))) := by
    intro l hWl
    rw [Work.Thom.PieceRes_eq_pdCohMap Z n hWl T.τ, hd l,
      chartClass_pdCohMap_reduce Z e l (Z.baseSet i ∩ Z.baseSet j) hWl (d l)]
  have hdEq := (hPiece i Set.inter_subset_left).symm.trans (hPiece j Set.inter_subset_right)
  -- injectivity of the (degree-zero) local Thom map over the intersection
  have hinj := ltMap_inj Z (Z.baseSet i ∩ Z.baseSet j)
    ((Work.Thom.localThomOfChart Z n e i (Z.baseSet i ∩ Z.baseSet j) Set.inter_subset_left).τ)
    ((Work.Thom.localThomOfChart Z n e i (Z.baseSet i ∩ Z.baseSet j) Set.inter_subset_left).isThom 0)
  -- the coefficient of the second chart is the first one times `u`
  have hdIJ : cohRes (Z.baseSet i) (Z.baseSet i ∩ Z.baseSet j) Set.inter_subset_left (d i)
      = (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.baseSet i ∩ Z.baseSet j))) 0 0)
          (cohRes (Z.baseSet j) (Z.baseSet i ∩ Z.baseSet j) Set.inter_subset_right (d j)) u := by
    refine hinj ?_
    rw [hchart] at hdEq
    exact hdEq.trans (ltMap_cup Z (Z.baseSet i ∩ Z.baseSet j)
      ((Work.Thom.localThomOfChart Z n e i (Z.baseSet i ∩ Z.baseSet j) Set.inter_subset_left).τ) u
      (cohRes (Z.baseSet j) (Z.baseSet i ∩ Z.baseSet j) Set.inter_subset_right (d j)))
  -- the two normalised classes agree on the intersection
  have hsEq : cohRes (Z.baseSet i) (Z.baseSet i ∩ Z.baseSet j) Set.inter_subset_left (s i)
      = (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.baseSet i ∩ Z.baseSet j))) 0 0)
          (cohRes (Z.baseSet j) (Z.baseSet i ∩ Z.baseSet j) Set.inter_subset_right (s j)) u := by
    apply Work.Thom.ptEv_ext
    intro p
    rw [Work.Thom.ptEv_cup]
    refine int_relation (a := Work.Thom.ptEv p (cohRes (Z.baseSet i) (Z.baseSet i ∩ Z.baseSet j) Set.inter_subset_left (d i)))
      (b := Work.Thom.ptEv p (cohRes (Z.baseSet j) (Z.baseSet i ∩ Z.baseSet j) Set.inter_subset_right (d j))) ?_ ?_ ?_ ?_ ?_
    · have h1 : Work.Thom.ptEv p ((Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.baseSet i ∩ Z.baseSet j))) 0 0) u u)
          = Work.Thom.ptEv p (Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.baseSet i ∩ Z.baseSet j)))) := by rw [huu]
      rw [Work.Thom.ptEv_cup, Work.Thom.ptEv_one] at h1
      exact h1
    · have h := congrArg (Work.Thom.ptEv p) hdIJ
      rw [Work.Thom.ptEv_cup] at h
      exact h
    · rw [Work.Thom.ptEv_pullback, Work.Thom.ptEv_pullback, ← Work.Thom.ptEv_cup]
      exact hs i (subIncl (Z.baseSet i) (Z.baseSet i ∩ Z.baseSet j) Set.inter_subset_left p)
    · rw [Work.Thom.ptEv_pullback, Work.Thom.ptEv_pullback, ← Work.Thom.ptEv_cup]
      exact hs j (subIncl (Z.baseSet j) (Z.baseSet i ∩ Z.baseSet j) Set.inter_subset_right p)
    · rw [Work.Thom.ptEv_pullback]
      exact hdv i (subIncl (Z.baseSet i) (Z.baseSet i ∩ Z.baseSet j) Set.inter_subset_left p)
  -- conclude
  rw [hchart]
  rw [ltMap_cup Z (Z.baseSet i ∩ Z.baseSet j)
    ((Work.Thom.localThomOfChart Z n e i (Z.baseSet i ∩ Z.baseSet j) Set.inter_subset_left).τ) u
    (cohRes (Z.baseSet j) (Z.baseSet i ∩ Z.baseSet j) Set.inter_subset_right (s j))]
  rw [← hsEq]

end Work.ThomBordism
