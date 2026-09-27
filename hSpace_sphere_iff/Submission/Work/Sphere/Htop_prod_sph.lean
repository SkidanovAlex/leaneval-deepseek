/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# `H^{p+1}(S^p × S^{p+1}; ℚ) ≅ ℚ`

The cohomology of `S^p × S^{p+1}` in degree `p+1` (the top degree of the second factor) is one
dimensional.  This is the base case `baseC` of the induction
`Work.Sphere.prod_sph_main_of_bases` computing the cohomology of a product of two spheres.

The proof covers `S^p` by its two contractible caps `capPlus (p-1)`, `capMinus (p-1)` and pulls
this cover back to `X = S^p × S^{p+1}`.  The pieces are homotopy equivalent to `S^{p+1}`, the
intersection `C` to `S^{p-1} × S^{p+1}`.  The Mayer–Vietoris sequence in degree `p+1` reads

`H^{p+1}(X) → H^{p+1}(A) ⊕ H^{p+1}(B) ≅ ℚ² --mvBetaH--> H^{p+1}(C) → H^{p+2}(X)`

and the connecting map of degree `p` has a vanishing domain (`H^p(S^{p-1} × S^{p+1}) = 0`, the
"gap" vanishing `subsingleton_prod_sph_gap`), so that `mvAlphaH` in degree `p+1` is *injective*
and `H^{p+1}(X) ≅ ker (mvBetaH)`.

Two facts pin down `ker (mvBetaH)`: it is nonzero (the class `κ = pr₂^*z` has nonzero restrictions
to the two pieces because `mvAlphaH` is injective) and `mvBetaH` itself is nonzero.  The latter is
the delicate point: it is proved by exhibiting an explicit *left inverse* of the restriction map
`H^{p+1}(A) → H^{p+1}(C)`, namely the pullback along the slice `y ↦ (c, y)` for a point `c` lying
in the intersection of the caps (`exists_htopSlice_fstAsub`, `exists_slice_fstCsub`).  Rank–nullity on
`mvBetaH : ℚ² → H^{p+1}(C)` then gives `dim ker (mvBetaH) = 1`, whence `H^{p+1}(X) ≅ ℚ`.
-/
import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Sphere.ProdSetup
import Submission.Work.Sphere.ProdRec
import Submission.Work.Sphere.Values
import Submission.Work.Sphere.H_prod_sph_zero
import Submission.Work.Cohomology.SingIn
import Submission.Work.Cohomology.MVH
import Submission.Work.Cohomology.mvAlphaH_ker_eq_range
import Submission.Work.Cohomology.mvBetaH_ker_eq_range
import Submission.Work.Cohomology.mvConnecting_ker_eq_range
import Submission.Work.Cohomology.H_map_comp

open CategoryTheory Simplicial Opposite
open Submission.Cohomology Submission.Sphere

namespace Work.Sphere

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

/-! ## The slice maps -/

/-- The second projection `X × Y ⟶ Y` as a morphism of `TopCat`. -/
def htopSndMor (X Y : TopCat.{0}) : TopProd X Y ⟶ Y :=
  TopCat.ofHom ⟨Prod.snd, continuous_snd⟩

/-- The slice `Y ⟶ X × Y`, `y ↦ (c, y)`. -/
def htopSliceMor (X Y : TopCat.{0}) (c : ↥X) : Y ⟶ TopProd X Y :=
  TopCat.ofHom ⟨fun y => (c, y), continuous_const.prodMk continuous_id⟩

lemma htopSliceMor_snd (X Y : TopCat.{0}) (c : ↥X) : htopSliceMor X Y c ≫ htopSndMor X Y = 𝟙 Y := by
  apply TopCat.hom_ext
  ext y
  rfl

lemma htopSlice_val {X Y : TopCat.{0}} (c : ↥X) (n : SimplexCategoryᵒᵖ)
    (τ : (TopCat.toSSet.obj Y).obj n) (t : stdSimplex ℝ (Fin (n.unop.len + 1))) :
    TopCat.toSSetObjEquivT (TopProd X Y) n ((TopCat.toSSet.map (htopSliceMor X Y c)).app n τ) t
      = (c, (TopCat.toSSetObjEquivT Y n τ) t) := rfl

lemma htopSubcomplex_iota_mem {S : SSet.{0}} (A : S.Subcomplex) {n : SimplexCategoryᵒᵖ}
    (y : A.toSSet.obj n) : A.ι.app n y ∈ A.obj n := y.2

variable {X Y : TopCat.{0}}

/-- **The slice into the subcomplex of simplices lying over `W`.**  For a point `c ∈ W` there is a
simplicial map `Sing Y ⟶ {q | q.1 ∈ W}` whose composite with the projection to `Y` is the
identity; consequently the projection pullback is injective in every degree. -/
theorem exists_htopSlice_fstSub (W : Set ↥X) (c : ↥X) (hc : c ∈ W) :
    ∃ ψ : TopCat.toSSet.obj Y ⟶ (fstSub X Y W).toSSet,
      ψ ≫ ((fstSub X Y W).ι ≫ TopCat.toSSet.map (htopSndMor X Y)) = 𝟙 (TopCat.toSSet.obj Y) := by
  have h₁ : SSet.Subcomplex.range (TopCat.toSSet.map (htopSliceMor X Y c)) ≤ fstSub X Y W := by
    intro n σ hσ
    rw [CategoryTheory.Subfunctor.range_obj, Set.mem_range] at hσ
    obtain ⟨τ, rfl⟩ := hσ
    rw [mem_singIn_iff]
    intro t
    show (TopCat.toSSetObjEquivT (TopProd X Y) n
      ((TopCat.toSSet.map (htopSliceMor X Y c)).app n τ) t).1 ∈ W
    rw [htopSlice_val]
    exact hc
  refine ⟨SSet.Subcomplex.lift (TopCat.toSSet.map (htopSliceMor X Y c)) h₁, ?_⟩
  rw [← Category.assoc, SSet.Subcomplex.lift_ι]
  have h2 : TopCat.toSSet.map (htopSliceMor X Y c ≫ htopSndMor X Y) = 𝟙 (TopCat.toSSet.obj Y) := by
    rw [htopSliceMor_snd]
    exact CategoryTheory.Functor.map_id _ _
  rw [← h2, CategoryTheory.Functor.map_comp]

/-- The same slice, into the first piece of the two-piece cover. -/
theorem exists_htopSlice_fstAsub (W₁ W₂ : Set ↥X) (c : ↥X) (hc : c ∈ W₁) :
    ∃ ψ : TopCat.toSSet.obj Y ⟶ (fstAsub X Y W₁ W₂).toSSet,
      ψ ≫ ((fstAsub X Y W₁ W₂).ι ≫ (fstSmall X Y W₁ W₂).ι ≫ TopCat.toSSet.map (htopSndMor X Y))
        = 𝟙 (TopCat.toSSet.obj Y) := by
  obtain ⟨ψ₀, hψ₀⟩ := exists_htopSlice_fstSub (X := X) (Y := Y) W₁ c hc
  set g : TopCat.toSSet.obj Y ⟶ (fstSmall X Y W₁ W₂).toSSet :=
    ψ₀ ≫ SSet.Subcomplex.homOfLE (le_sup_left : fstSub X Y W₁ ≤ fstSmall X Y W₁ W₂) with hg
  have h₂ : SSet.Subcomplex.range g ≤ fstAsub X Y W₁ W₂ := by
    intro n σ hσ
    rw [CategoryTheory.Subfunctor.range_obj, Set.mem_range] at hσ
    obtain ⟨τ, rfl⟩ := hσ
    rw [SSet.Subcomplex.preimage_obj]
    show ((fstSmall X Y W₁ W₂).ι).app n (g.app n τ) ∈ (fstSub X Y W₁).obj n
    have hgg : g.app n τ = (SSet.Subcomplex.homOfLE
        (le_sup_left : fstSub X Y W₁ ≤ fstSmall X Y W₁ W₂)).app n (ψ₀.app n τ) := rfl
    rw [hgg]
    have hcomp : (SSet.Subcomplex.homOfLE
        (le_sup_left : fstSub X Y W₁ ≤ fstSmall X Y W₁ W₂)) ≫
        (fstSmall X Y W₁ W₂).ι = (fstSub X Y W₁).ι :=
      SSet.Subcomplex.homOfLE_ι _
    have happ := congrArg (fun (φ : (fstSub X Y W₁).toSSet ⟶
        TopCat.toSSet.obj (TopProd X Y)) => φ.app n (ψ₀.app n τ)) hcomp
    exact happ ▸ htopSubcomplex_iota_mem (fstSub X Y W₁) (ψ₀.app n τ)
  refine ⟨SSet.Subcomplex.lift g h₂, ?_⟩
  rw [← Category.assoc, SSet.Subcomplex.lift_ι]
  rw [hg]
  have hcomp2 : (ψ₀ ≫ SSet.Subcomplex.homOfLE (le_sup_left : fstSub X Y W₁ ≤ fstSmall X Y W₁ W₂)) ≫
      (fstSmall X Y W₁ W₂).ι = ψ₀ ≫ (fstSub X Y W₁).ι := by
    rw [Category.assoc, SSet.Subcomplex.homOfLE_ι]
  rw [← Category.assoc, hcomp2, Category.assoc, hψ₀]

/-- The same slice, into the intersection of the two pieces of the cover. -/
theorem exists_htopSlice_inter (W₁ W₂ : Set ↥X) (c : ↥X) (hc : c ∈ W₁ ∩ W₂) :
    ∃ ψ : TopCat.toSSet.obj Y ⟶
        ((fstSub X Y W₁ ⊓ fstSub X Y W₂).preimage (fstSmall X Y W₁ W₂).ι).toSSet,
      ψ ≫ (((fstSub X Y W₁ ⊓ fstSub X Y W₂).preimage (fstSmall X Y W₁ W₂).ι).ι ≫
        (fstSmall X Y W₁ W₂).ι ≫ TopCat.toSSet.map (htopSndMor X Y)) = 𝟙 (TopCat.toSSet.obj Y) := by
  have h₁ : SSet.Subcomplex.range (TopCat.toSSet.map (htopSliceMor X Y c)) ≤
      fstSub X Y W₁ ⊓ fstSub X Y W₂ := by
    intro n σ hσ
    rw [CategoryTheory.Subfunctor.range_obj, Set.mem_range] at hσ
    obtain ⟨τ, rfl⟩ := hσ
    refine ⟨?_, ?_⟩ <;> rw [mem_singIn_iff]
    · intro t
      show (TopCat.toSSetObjEquivT (TopProd X Y) n
        ((TopCat.toSSet.map (htopSliceMor X Y c)).app n τ) t).1 ∈ W₁
      rw [htopSlice_val]
      exact hc.1
    · intro t
      show (TopCat.toSSetObjEquivT (TopProd X Y) n
        ((TopCat.toSSet.map (htopSliceMor X Y c)).app n τ) t).1 ∈ W₂
      rw [htopSlice_val]
      exact hc.2
  let ψ₀ : TopCat.toSSet.obj Y ⟶ (fstSub X Y W₁ ⊓ fstSub X Y W₂).toSSet :=
    SSet.Subcomplex.lift (TopCat.toSSet.map (htopSliceMor X Y c)) h₁
  have hψ₀ : ψ₀ ≫ (fstSub X Y W₁ ⊓ fstSub X Y W₂).ι
      = TopCat.toSSet.map (htopSliceMor X Y c) := SSet.Subcomplex.lift_ι _ _
  have hle : fstSub X Y W₁ ⊓ fstSub X Y W₂ ≤ fstSmall X Y W₁ W₂ :=
    le_trans inf_le_left le_sup_left
  set g : TopCat.toSSet.obj Y ⟶ (fstSmall X Y W₁ W₂).toSSet :=
    ψ₀ ≫ SSet.Subcomplex.homOfLE hle with hg
  refine ⟨SSet.Subcomplex.lift g ?_, ?_⟩
  · intro n σ hσ
    rw [CategoryTheory.Subfunctor.range_obj, Set.mem_range] at hσ
    obtain ⟨τ, rfl⟩ := hσ
    rw [SSet.Subcomplex.preimage_obj]
    show ((fstSmall X Y W₁ W₂).ι).app n (g.app n τ) ∈ (fstSub X Y W₁ ⊓ fstSub X Y W₂).obj n
    have hgg : g.app n τ = (SSet.Subcomplex.homOfLE hle).app n (ψ₀.app n τ) := rfl
    rw [hgg]
    have hcomp : (SSet.Subcomplex.homOfLE hle) ≫ (fstSmall X Y W₁ W₂).ι
        = (fstSub X Y W₁ ⊓ fstSub X Y W₂).ι := SSet.Subcomplex.homOfLE_ι hle
    have hmem := htopSubcomplex_iota_mem (fstSub X Y W₁ ⊓ fstSub X Y W₂) (ψ₀.app n τ)
    convert hmem using 1
    rfl
  · rw [← Category.assoc, SSet.Subcomplex.lift_ι]
    rw [hg]
    have hcomp2 : (ψ₀ ≫ SSet.Subcomplex.homOfLE hle) ≫ (fstSmall X Y W₁ W₂).ι
        = ψ₀ ≫ (fstSub X Y W₁ ⊓ fstSub X Y W₂).ι := by
      rw [Category.assoc, SSet.Subcomplex.homOfLE_ι]
    rw [← Category.assoc, hcomp2, Category.assoc, ← Category.assoc, hψ₀,
      ← CategoryTheory.Functor.map_comp, htopSliceMor_snd, CategoryTheory.Functor.map_id]

/-! ## A point of the doubly punctured sphere -/

/-- The first standard basis vector of `ℝ^{n+2}`, as a point of `S^{n+1}` lying in neither pole. -/
def goodPt (n : ℕ) : ↥(Sph (n+1)) :=
  ⟨EuclideanSpace.single (0 : Fin (n+2)) 1, by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, PiLp.norm_single]; norm_num⟩

lemma goodPt_mem_capPlus (n : ℕ) : goodPt n ∈ capPlus n := by
  intro h
  have h2 : (EuclideanSpace.single (0 : Fin (n+2)) (1:ℝ)).ofLp
      = (pole (n+1)).ofLp := congrArg WithLp.ofLp h
  have h3 := congrFun h2 (0 : Fin (n+2))
  rw [PiLp.single_apply] at h3
  simp [pole] at h3

lemma goodPt_mem_capMinus (n : ℕ) : goodPt n ∈ capMinus n := by
  intro h
  have h2 : (EuclideanSpace.single (0 : Fin (n+2)) (1:ℝ)).ofLp
      = (-pole (n+1)).ofLp := congrArg WithLp.ofLp h
  have h3 := congrFun h2 (0 : Fin (n+2))
  rw [PiLp.single_apply] at h3
  simp [pole] at h3

lemma goodPt_mem (n : ℕ) : goodPt n ∈ capPlus n ∩ capMinus n :=
  ⟨goodPt_mem_capPlus n, goodPt_mem_capMinus n⟩

/-! ## The gap vanishing `H^{a+1}(S^a × S^{a+2}) = 0` -/

/-- The degree shift `H^{a+1}(S^a × S^{a+2}) = 0` for `a ≥ 1`, by iterating the degree shift
`H^{k+1}(S^{n+1} × S^q) ≅ H^k(S^n × S^q)` down to `a = 0`. -/
theorem subsingleton_prod_sph_gap_succ (a b : ℕ) (ha : 1 ≤ a) (hab : a + 2 ≤ b) :
    Subsingleton (H (TopCat.toSSet.obj (TopProd (Sph a) (Sph b))) ℚ (a+1)) := by
  induction a with
  | zero => omega
  | succ a ih =>
      rcases Nat.eq_zero_or_pos a with ha0 | hapos
      · subst ha0
        refine subsingleton_of_linearEquiv
          (Classical.choice (prod_fst_shift (n := 0) (q := b) (k := 1) (by omega)
            (sphere_subsingleton b 1 (by omega) (by omega))
            (sphere_subsingleton b 2 (by omega) (by omega))))
          (H_prod_sph_zero b 1 le_rfl (by omega))
      · refine subsingleton_of_linearEquiv
          (Classical.choice (prod_fst_shift (n := a) (q := b) (k := a+1) (by omega)
            (sphere_subsingleton b (a+1) (by omega) (by omega))
            (sphere_subsingleton b (a+2) (by omega) (by omega))))
          (ih (by omega) (by omega))

/-- **The gap vanishing** `H^{p}(S^{p-1} × S^{p+1}) = 0` for `p ≥ 1`. -/
theorem subsingleton_prod_sph_gap (p : ℕ) (hp : 1 ≤ p) :
    Subsingleton (H (TopCat.toSSet.obj (TopProd (Sph (p-1)) (Sph (p+1)))) ℚ p) := by
  rcases Nat.eq_zero_or_pos (p-1) with h0 | hpos
  · -- `p = 1`: this is `H¹(S⁰ × S²) = 0`
    have hp1 : p = 1 := by omega
    subst hp1
    exact H_prod_sph_zero 2 1 le_rfl (by norm_num)
  · have h := subsingleton_prod_sph_gap_succ (p-1) (p+1) hpos (by omega)
    simpa [Nat.sub_add_cancel hp] using h

/-! ## The main computation -/

/-- The small complex of the two-cap cover of `S^{n+1} × S^{n+1+1}` pulled back from the first
factor, as a subcomplex of the singular complex. -/
abbrev htopCovSsub (n : ℕ) : (TopCat.toSSet.obj (TopProd (Sph (n+1)) (Sph (n+1+1)))).Subcomplex :=
  fstSmall (Sph (n+1)) (Sph (n+1+1)) (capPlus n) (capMinus n)

/-- The same small complex, as a simplicial set. -/
abbrev htopCovS (n : ℕ) : SSet.{0} := (htopCovSsub n : SSet.{0})

/-- The first piece of the cover. -/
abbrev htopCovA (n : ℕ) : (htopCovS n).Subcomplex :=
  fstAsub (Sph (n+1)) (Sph (n+1+1)) (capPlus n) (capMinus n)

/-- The second piece of the cover. -/
abbrev htopCovB (n : ℕ) : (htopCovS n).Subcomplex :=
  fstBsub (Sph (n+1)) (Sph (n+1+1)) (capPlus n) (capMinus n)

/-- The intersection of the two pieces of the cover. -/
abbrev htopCovI (n : ℕ) : (htopCovS n).Subcomplex := htopCovA n ⊓ htopCovB n

lemma htopCovA_sup_htopCovB (n : ℕ) : htopCovA n ⊔ htopCovB n = ⊤ :=
  fstAsub_sup_fstBsub _ _ _ _

lemma htopCovA_inf_htopCovB (n : ℕ) : htopCovA n ⊓ htopCovB n = fstCsub (Sph (n+1)) (Sph (n+1+1))
    (capPlus n) (capMinus n) :=
  fstAsub_inf_fstBsub _ _ _ _

/-- The main computation `H^{n+2}(S^{n+1} × S^{n+1+1}; ℚ) ≅ ℚ`. -/
theorem Htop_prod_sph_aux (n : ℕ) :
    Nonempty (H (TopCat.toSSet.obj (TopProd (Sph (n+1)) (Sph (n+1+1)))) ℚ (n+1+1) ≃ₗ[ℚ] ℚ) := by
  haveI hcp : ContractibleSpace ↥(capPlus n) := capPlus_contractible n
  haveI hcm : ContractibleSpace ↥(capMinus n) := capMinus_contractible n
  have hAB : htopCovA n ⊔ htopCovB n = ⊤ := htopCovA_sup_htopCovB n
  -- ### the pieces in the top degree are `ℚ`
  have hA_ne : Nonempty (H (htopCovA n) ℚ (n+1+1) ≃ₗ[ℚ] ℚ) := by
    obtain ⟨e1⟩ := H_fstAsub_iso (Sph (n+1)) (Sph (n+1+1)) (capPlus n) (capMinus n) (n+1+1)
    obtain ⟨e2⟩ := H_fstSub_contractible_iso (X := Sph (n+1)) (Y := Sph (n+1+1))
      (capPlus n) (n+1+1)
    obtain ⟨e3⟩ := sphere_top (n+1+1) (by omega)
    exact ⟨(e1.trans e2).trans e3⟩
  have hB_ne : Nonempty (H (htopCovB n) ℚ (n+1+1) ≃ₗ[ℚ] ℚ) := by
    obtain ⟨e1⟩ := H_fstBsub_iso (Sph (n+1)) (Sph (n+1+1)) (capPlus n) (capMinus n) (n+1+1)
    obtain ⟨e2⟩ := H_fstSub_contractible_iso (X := Sph (n+1)) (Y := Sph (n+1+1))
      (capMinus n) (n+1+1)
    obtain ⟨e3⟩ := sphere_top (n+1+1) (by omega)
    exact ⟨(e1.trans e2).trans e3⟩
  -- ### the pieces in degree `n+1` vanish
  have hA_mid : Subsingleton (H (htopCovA n) ℚ (n+1)) := by
    obtain ⟨e1⟩ := H_fstAsub_iso (Sph (n+1)) (Sph (n+1+1)) (capPlus n) (capMinus n) (n+1)
    obtain ⟨e2⟩ := H_fstSub_contractible_iso (X := Sph (n+1)) (Y := Sph (n+1+1))
      (capPlus n) (n+1)
    exact subsingleton_of_linearEquiv (e1.trans e2)
      (sphere_subsingleton (n+1+1) (n+1) (by omega) (by omega))
  have hB_mid : Subsingleton (H (htopCovB n) ℚ (n+1)) := by
    obtain ⟨e1⟩ := H_fstBsub_iso (Sph (n+1)) (Sph (n+1+1)) (capPlus n) (capMinus n) (n+1)
    obtain ⟨e2⟩ := H_fstSub_contractible_iso (X := Sph (n+1)) (Y := Sph (n+1+1))
      (capMinus n) (n+1)
    exact subsingleton_of_linearEquiv (e1.trans e2)
      (sphere_subsingleton (n+1+1) (n+1) (by omega) (by omega))
  -- ### the intersection vanishes in degree `n+1` (the gap vanishing)
  have hI_mid : Subsingleton (H (htopCovI n) ℚ (n+1)) := by
    obtain ⟨e0⟩ := Submission.Sphere.H_iso_of_iso
      (SSet.Subcomplex.eqToIso (htopCovA_inf_htopCovB n)) (n+1)
    refine subsingleton_of_linearEquiv e0 ?_
    obtain ⟨e1⟩ := H_fstCsub_homeo (Sph (n+1)) (Sph (n+1+1)) (capPlus n) (capMinus n) (n+1)
    rw [capPlus_inter_capMinus_eq_DPset n] at e1
    obtain ⟨e2⟩ := H_DPset_prod_iso n (Sph (n+1+1)) (n+1)
    exact subsingleton_of_linearEquiv (e1.trans e2) (subsingleton_prod_sph_gap (n+1) (by omega))
  -- ### `mvAlphaH` is injective in degree `n+2`
  have hα : Function.Injective (mvAlphaH (htopCovS n) (htopCovA n) (htopCovB n) (n+1+1)) := by
    rw [← LinearMap.ker_eq_bot]
    rw [Work.Cohomology.mvAlphaH_ker_eq_range (htopCovS n) (htopCovA n) (htopCovB n) hAB (n+1)]
    rw [LinearMap.range_eq_bot]
    apply LinearMap.ext
    intro x
    rw [hI_mid.allEq x 0]
    exact map_zero _
  -- ### hence `H^{n+2}(S) ≅ ker mvBetaH`
  have hker : Nonempty (H (htopCovS n) ℚ (n+1+1) ≃ₗ[ℚ]
      (mvBetaH (htopCovS n) (htopCovA n) (htopCovB n) (n+1+1)).ker) := by
    refine ⟨(LinearEquiv.ofInjective (mvAlphaH (htopCovS n) (htopCovA n) (htopCovB n) (n+1+1)) hα).trans
      (LinearEquiv.ofEq _ _ ?_)⟩
    rw [Work.Cohomology.mvBetaH_ker_eq_range (htopCovS n) (htopCovA n) (htopCovB n) hAB (n+1+1)]
  -- ### the class `z` and the restriction maps
  obtain ⟨eY⟩ := sphere_top (n+1+1) (by omega)
  let z : H (TopCat.toSSet.obj (Sph (n+1+1))) ℚ (n+1+1) := eY.symm 1
  have hz : z ≠ 0 := by
    intro h
    have h1 : eY z = eY (0 : H (TopCat.toSSet.obj (Sph (n+1+1))) ℚ (n+1+1)) := by rw [h]
    rw [map_zero, eY.apply_symm_apply] at h1
    exact one_ne_zero h1
  let πA : H (TopCat.toSSet.obj (Sph (n+1+1))) ℚ (n+1+1) →ₗ[ℚ] H (htopCovA n) ℚ (n+1+1) :=
    H.map ℚ ((htopCovA n).ι ≫ (htopCovSsub n).ι ≫ TopCat.toSSet.map
      (htopSndMor (Sph (n+1)) (Sph (n+1+1)))) (n+1+1)
  let πB : H (TopCat.toSSet.obj (Sph (n+1+1))) ℚ (n+1+1) →ₗ[ℚ] H (htopCovB n) ℚ (n+1+1) :=
    H.map ℚ ((htopCovB n).ι ≫ (htopCovSsub n).ι ≫ TopCat.toSSet.map
      (htopSndMor (Sph (n+1)) (Sph (n+1+1)))) (n+1+1)
  let πI : H (TopCat.toSSet.obj (Sph (n+1+1))) ℚ (n+1+1) →ₗ[ℚ] H (htopCovI n) ℚ (n+1+1) :=
    H.map ℚ (((SSet.Subcomplex.homOfLE (inf_le_left : htopCovA n ⊓ htopCovB n ≤ htopCovA n) ≫
      (htopCovA n).ι)) ≫ (htopCovSsub n).ι ≫ TopCat.toSSet.map
      (htopSndMor (Sph (n+1)) (Sph (n+1+1)))) (n+1+1)
  -- ### the slices give left inverses
  obtain ⟨ψA, hψA⟩ := exists_htopSlice_fstAsub (X := Sph (n+1)) (Y := Sph (n+1+1))
    (capPlus n) (capMinus n) (goodPt n) (goodPt_mem_capPlus n)
  have hsliceA : ∀ w, H.map ℚ ψA (n+1+1) (πA w) = w := by
    intro w
    show H.map ℚ ψA (n+1+1) (H.map ℚ ((htopCovA n).ι ≫ ((htopCovSsub n).ι ≫ TopCat.toSSet.map
      (htopSndMor (Sph (n+1)) (Sph (n+1+1))))) (n+1+1) w) = w
    rw [← Work.Cohomology.H_map_comp, hψA, H.map_id]
    simp
  have hπA : πA z ≠ 0 := fun h0 => hz (by rw [← hsliceA z, h0, map_zero])
  obtain ⟨ψI, hψI⟩ := exists_htopSlice_inter (X := Sph (n+1)) (Y := Sph (n+1+1))
    (capPlus n) (capMinus n) (goodPt n) (goodPt_mem n)
  have hsliceI : ∀ w, H.map ℚ ψI (n+1+1) (πI w) = w := by
    intro w
    have h1 : H.map ℚ (ψI ≫ ((htopCovI n).ι ≫ ((htopCovSsub n).ι ≫ TopCat.toSSet.map
        (htopSndMor (Sph (n+1)) (Sph (n+1+1)))))) (n+1+1) w = w := by
      rw [show (ψI ≫ ((htopCovI n).ι ≫ ((htopCovSsub n).ι ≫ TopCat.toSSet.map
          (htopSndMor (Sph (n+1)) (Sph (n+1+1)))))) = ψI ≫
            (((fstSub (Sph (n+1)) (Sph (n+1+1)) (capPlus n) ⊓ fstSub (Sph (n+1))
              (Sph (n+1+1)) (capMinus n)).preimage
              (fstSmall (Sph (n+1)) (Sph (n+1+1)) (capPlus n) (capMinus n)).ι).ι ≫
              (fstSmall (Sph (n+1)) (Sph (n+1+1)) (capPlus n) (capMinus n)).ι ≫
              TopCat.toSSet.map (htopSndMor (Sph (n+1)) (Sph (n+1+1)))) from rfl]
      rw [hψI, H.map_id]
      simp
    rwa [Work.Cohomology.H_map_comp] at h1
  have hπI : πI z ≠ 0 := fun h0 => hz (by rw [← hsliceI z, h0]; exact map_zero _)
  -- ### the formal relation between the restrictions to `A` and to `A ⊓ B`
  have hπI_eq : ∀ w, πI w = H.map ℚ
      (SSet.Subcomplex.homOfLE (inf_le_left : htopCovA n ⊓ htopCovB n ≤ htopCovA n)) (n+1+1) (πA w) := by
    intro w
    have hL : H.map ℚ (SSet.Subcomplex.homOfLE (inf_le_left : htopCovA n ⊓ htopCovB n ≤ htopCovA n))
        (n+1+1) (πA w)
        = H.map ℚ ((htopCovI n).ι ≫ ((htopCovSsub n).ι ≫ TopCat.toSSet.map
            (htopSndMor (Sph (n+1)) (Sph (n+1+1))))) (n+1+1) w := by
      rw [show H.map ℚ (SSet.Subcomplex.homOfLE (inf_le_left : htopCovA n ⊓ htopCovB n ≤ htopCovA n))
            (n+1+1) (H.map ℚ ((htopCovA n).ι ≫ ((htopCovSsub n).ι ≫ TopCat.toSSet.map
              (htopSndMor (Sph (n+1)) (Sph (n+1+1))))) (n+1+1) w)
          = H.map ℚ (SSet.Subcomplex.homOfLE (inf_le_left : htopCovA n ⊓ htopCovB n ≤ htopCovA n) ≫
              ((htopCovA n).ι ≫ ((htopCovSsub n).ι ≫ TopCat.toSSet.map
                (htopSndMor (Sph (n+1)) (Sph (n+1+1)))))) (n+1+1) w
          from (Work.Cohomology.H_map_comp _ _ _ _).symm]
      congr 1
    rw [hL]
    rfl
  -- ### `mvBetaH` is nonzero
  have hβ_ne : mvBetaH (htopCovS n) (htopCovA n) (htopCovB n) (n+1+1) ≠ 0 := by
    intro h0
    have hval : mvBetaH (htopCovS n) (htopCovA n) (htopCovB n) (n+1+1) (πA z, 0)
        = H.map ℚ (SSet.Subcomplex.homOfLE (inf_le_left : htopCovA n ⊓ htopCovB n ≤ htopCovA n))
            (n+1+1) (πA z) := by
      rw [mvBetaH_apply]
      simp
    have hzero : H.map ℚ (SSet.Subcomplex.homOfLE (inf_le_left : htopCovA n ⊓ htopCovB n ≤ htopCovA n))
        (n+1+1) (πA z) = 0 := by
      rw [← hval, h0]
      rfl
    exact hπI (by rw [hπI_eq z]; exact hzero)
  -- ### the kernel is nonzero
  have hker_ne : (mvBetaH (htopCovS n) (htopCovA n) (htopCovB n) (n+1+1)).ker ≠ ⊥ := by
    let κ : H (htopCovS n) ℚ (n+1+1) := H.map ℚ ((htopCovSsub n).ι ≫ TopCat.toSSet.map
      (htopSndMor (Sph (n+1)) (Sph (n+1+1)))) (n+1+1) z
    have hκA : H.map ℚ (htopCovA n).ι (n+1+1) κ = πA z := by
      show H.map ℚ (htopCovA n).ι (n+1+1) (H.map ℚ ((htopCovSsub n).ι ≫ TopCat.toSSet.map
        (htopSndMor (Sph (n+1)) (Sph (n+1+1)))) (n+1+1) z)
        = H.map ℚ ((htopCovA n).ι ≫ ((htopCovSsub n).ι ≫ TopCat.toSSet.map
          (htopSndMor (Sph (n+1)) (Sph (n+1+1))))) (n+1+1) z
      rw [← Work.Cohomology.H_map_comp]
    have hκ : κ ≠ 0 := by
      intro h0
      have h1 : H.map ℚ ψA (n+1+1) (πA z) = 0 := by
        rw [← hκA, h0]
        exact map_zero _
      rw [hsliceA z] at h1
      exact hz h1
    have h1 : H.map ℚ (SSet.Subcomplex.homOfLE (inf_le_left : htopCovA n ⊓ htopCovB n ≤ htopCovA n))
        (n+1+1) ((H.map ℚ (htopCovA n).ι (n+1+1)) κ)
        = H.map ℚ (SSet.Subcomplex.homOfLE (inf_le_left : htopCovA n ⊓ htopCovB n ≤ htopCovA n) ≫
          (htopCovA n).ι) (n+1+1) κ := by
      rw [← Work.Cohomology.H_map_comp]
    have h2 : H.map ℚ (SSet.Subcomplex.homOfLE (inf_le_right : htopCovA n ⊓ htopCovB n ≤ htopCovB n))
        (n+1+1) ((H.map ℚ (htopCovB n).ι (n+1+1)) κ)
        = H.map ℚ (SSet.Subcomplex.homOfLE (inf_le_right : htopCovA n ⊓ htopCovB n ≤ htopCovB n) ≫
          (htopCovB n).ι) (n+1+1) κ := by
      rw [← Work.Cohomology.H_map_comp]
    have hmem : ((H.map ℚ (htopCovA n).ι (n+1+1)) κ, (H.map ℚ (htopCovB n).ι (n+1+1)) κ) ∈
        (mvBetaH (htopCovS n) (htopCovA n) (htopCovB n) (n+1+1)).ker := by
      rw [LinearMap.mem_ker, mvBetaH_apply, h1, h2]
      rw [show (SSet.Subcomplex.homOfLE (inf_le_left : htopCovA n ⊓ htopCovB n ≤ htopCovA n) ≫ (htopCovA n).ι)
          = (SSet.Subcomplex.homOfLE (inf_le_right : htopCovA n ⊓ htopCovB n ≤ htopCovB n) ≫ (htopCovB n).ι)
          from by rw [SSet.Subcomplex.homOfLE_ι, SSet.Subcomplex.homOfLE_ι]]
      rw [sub_self]
    rw [Submodule.ne_bot_iff]
    exact ⟨_, hmem, fun hpair => hπA (by
      rw [Prod.ext_iff] at hpair
      rw [← hκA]
      exact hpair.1)⟩
  -- ### the dimension count
  obtain ⟨eAB⟩ := hA_ne
  obtain ⟨eBB⟩ := hB_ne
  let e2 : (H (htopCovA n) ℚ (n+1+1) × H (htopCovB n) ℚ (n+1+1)) ≃ₗ[ℚ] (ℚ × ℚ) := eAB.prodCongr eBB
  haveI hfin : FiniteDimensional ℚ (H (htopCovA n) ℚ (n+1+1) × H (htopCovB n) ℚ (n+1+1)) :=
    e2.symm.finiteDimensional
  have hsrc : Module.finrank ℚ (H (htopCovA n) ℚ (n+1+1) × H (htopCovB n) ℚ (n+1+1)) = 2 := by
    rw [LinearEquiv.finrank_eq e2, Module.finrank_prod, Module.finrank_self]
  have h1 : 0 < Module.finrank ℚ ↥(mvBetaH (htopCovS n) (htopCovA n) (htopCovB n) (n+1+1)).ker := by
    by_contra hcon
    rw [not_lt, Nat.le_zero] at hcon
    exact hker_ne (Submodule.finrank_eq_zero.mp hcon)
  have h2 : 0 < Module.finrank ℚ ↥(mvBetaH (htopCovS n) (htopCovA n) (htopCovB n) (n+1+1)).range := by
    by_contra hcon
    rw [not_lt, Nat.le_zero] at hcon
    exact hβ_ne (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hcon))
  have hsum := LinearMap.finrank_range_add_finrank_ker
    (mvBetaH (htopCovS n) (htopCovA n) (htopCovB n) (n+1+1))
  have hker_fin : Module.finrank ℚ ↥(mvBetaH (htopCovS n) (htopCovA n) (htopCovB n) (n+1+1)).ker = 1 := by
    omega
  -- ### assemble
  obtain ⟨eSmall⟩ := H_fstSmall_iso (Sph (n+1)) (Sph (n+1+1)) (capPlus n) (capMinus n)
    (isOpen_capPlus n) (isOpen_capMinus n)
    (fun x => Set.eq_univ_iff_forall.mp (capPlus_union_capMinus n) x) (n+1+1)
  obtain ⟨eker⟩ := hker
  have hker_iso : (↥(mvBetaH (htopCovS n) (htopCovA n) (htopCovB n) (n+1+1)).ker) ≃ₗ[ℚ] ℚ :=
    LinearEquiv.ofFinrankEq (R := ℚ) _ ℚ (by rw [hker_fin, Module.finrank_self])
  exact ⟨eSmall.trans (eker.trans hker_iso)⟩

/-- **`H^{p+1}(S^p × S^{p+1}; ℚ) ≅ ℚ`.**  The cohomology of `S^p × S^{p+1}` in degree `p+1` (the
top degree of the second factor) is one dimensional; this is the base case `baseC` of
`Work.Sphere.prod_sph_main_of_bases`. -/
theorem Htop_prod_sph (p : ℕ) (hp : 1 ≤ p) :
    Nonempty (Submission.Cohomology.H
      (TopCat.toSSet.obj (Work.Sphere.TopProd (Submission.Sphere.Sph p) (Submission.Sphere.Sph (p+1)))) ℚ (p+1)
      ≃ₗ[ℚ] ℚ) := by
  have h := Htop_prod_sph_aux (p-1)
  rw [Nat.sub_add_cancel hp] at h
  exact h

end

end Work.Sphere
