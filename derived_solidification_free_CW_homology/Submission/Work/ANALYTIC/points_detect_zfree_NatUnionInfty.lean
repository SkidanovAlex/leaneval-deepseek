import Mathlib
import Submission.Work.ANALYTIC.unprimedSetup
import Submission.Work.ATOM.Defs
import Submission.Work.ATOM.exists_level_enumeration
import Submission.Work.ANALYTIC.pointsDetectSetup
import Submission.Work.ANALYTIC.zfree_level_separating
import Submission.Work.ANALYTIC.zfree_locally_zmap
import Submission.Work.ANALYTIC.zfree_zmap_combo_locally_zero
import Submission.Work.ANALYTIC.zfree_finite_point_independent_mor

namespace Work.ANALYTIC

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid
open Opposite

noncomputable section

/-- `homFreeEquiv` sends `0` to `0`. -/
theorem homFreeEquiv_zeroA (S : LightProfinite.{0}) (A : LightCondAb) :
    Work.ATOM.homFreeEquiv S A 0 = 0 := by
  rw [homFreeEquiv_eq_evalA]
  show (0 : ↥(A.obj.obj (op S))) = 0
  rfl

/-- Point classes of distinct points of a light profinite set are `ℤ`-linearly independent. -/
theorem pointClass_independent (T : LightProfinite.{0}) (m : ℕ) (t : Fin m → ↥T)
    (ht : Function.Injective t) (c : Fin m → ℤ)
    (h : (∑ j, c j • (pointClassM T (t j))) = 0) : ∀ j, c j = 0 := by
  obtain ⟨n, hn⟩ := zfree_level_separating T m t ht
  haveI : Finite ↥(T.component n) := Work.ATOM.finite_component T n
  have h2 := congrArg (fun g => g ≫ Work.ATOM.zmap (T.proj n)) h
  rw [zero_comp] at h2
  have h4 : (∑ j, c j • pointClassM T (t j)) ≫ Work.ATOM.zmap (T.proj n)
      = ∑ j, c j • pointClassM (T.component n) (T.proj n (t j)) := by
    rw [Preadditive.sum_comp]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Preadditive.zsmul_comp, pointClassM_comp]
  rw [h4] at h2
  exact zfree_finite_point_independent_mor (T.component n) m (fun j => T.proj n (t j)) hn c h2

/-- **Scholze, *Lectures on Analytic Geometry*, Proposition 2.1 (the injectivity part).**
A section of `ℤ[T]` over a light profinite set `S` killed by every point of `S` is zero.  The
hypothesis `hind` is the independence of the point classes of distinct points of `T`. -/
theorem points_detect_zfree_of_hind (T S : LightProfinite.{0})
    (hind : ∀ (m : ℕ) (t : Fin m → ↥T), Function.Injective t → ∀ c : Fin m → ℤ,
      (∑ j, c j • (pointClassM T (t j))) = 0 → ∀ j, c j = 0)
    (x : ↥((Work.ATOM.zfree T).obj.obj (op S)))
    (h : ∀ s : ↥S, (Work.ATOM.zfree T).obj.map (Work.ATOM.ptAt s).op x = 0) : x = 0 := by
  -- (★) local representation of `x` as a finite ℤ-linear combination of `zmap`s
  obtain ⟨m, C, ι, hcov, k, φ, c, hrep⟩ := zfree_locally_zmap T S x
  have hpiece : ∀ i : Fin m, (Work.ATOM.zfree T).obj.map (ι i).op x = 0 := by
    intro i
    have hnull : ∀ v : ↥(C i), prePt v (zmapCombo (φ i) (c i)) = 0 := by
      intro v
      apply (Work.ATOM.homFreeEquiv Work.ATOM.pt (Work.ATOM.zfree T)).injective
      show (Work.ATOM.homFreeEquiv Work.ATOM.pt (Work.ATOM.zfree T))
        (Work.ATOM.zmap (Work.ATOM.ptAt v) ≫ (∑ j, c i j • Work.ATOM.zmap (φ i j))) = 0
      rw [Work.ATOM.homFreeEquiv_zmap, ← hrep i]
      have hcomp : ((Work.ATOM.ptAt v) ≫ (ι i)) = Work.ATOM.ptAt (ι i v) := by
        apply ConcreteCategory.hom_ext
        intro w
        rfl
      rw [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp,
        ← CategoryTheory.op_comp, hcomp]
      exact h (ι i v)
    obtain ⟨m', D, ν, hcov', hzero⟩ :=
      zfree_zmap_combo_locally_zero T (C i) hind (k i) (φ i) (c i) hnull
    refine Work.ATOM.eq_of_forall_map_eq_of_jointlySurjective D ν (fun u => ?_) (Work.ATOM.zfree T)
      (x := (Work.ATOM.zfree T).obj.map (ι i).op x) (y := 0) (fun l => ?_)
    · obtain ⟨l, c', hc'⟩ := hcov' u
      exact ⟨l, c', hc'⟩
    · show (Work.ATOM.zfree T).obj.map (ν l).op ((Work.ATOM.zfree T).obj.map (ι i).op x)
        = (Work.ATOM.zfree T).obj.map (ν l).op 0
      rw [map_zero]
      have h1 : Work.ATOM.homFreeEquiv (D l) (Work.ATOM.zfree T)
            (Work.ATOM.zmap (ν l) ≫ zmapCombo (φ i) (c i))
          = (Work.ATOM.zfree T).obj.map (ν l).op
              ((Work.ATOM.zfree T).obj.map (ι i).op x) := by
        rw [hrep i, ← Work.ATOM.homFreeEquiv_zmap (ν l) (Work.ATOM.zfree T)
          (zmapCombo (φ i) (c i))]
      rw [← h1]
      have h2 : (Work.ATOM.zmap (ν l) : Work.ATOM.zfree (D l) ⟶ Work.ATOM.zfree (C i)) ≫
            zmapCombo (φ i) (c i)
          = zmapCombo (fun j => ν l ≫ φ i j) (c i) := by
        rw [zmapCombo, zmapCombo, Preadditive.comp_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Preadditive.comp_zsmul, Work.ATOM.zmap_comp_zfree]
      rw [h2, hzero l, homFreeEquiv_zeroA]
  refine Work.ATOM.eq_of_forall_map_eq_of_jointlySurjective C ι (fun u => ?_) (Work.ATOM.zfree T)
    (x := x) (y := 0) (fun i => ?_)
  · obtain ⟨i, c', hc'⟩ := hcov u
    exact ⟨i, c', hc'⟩
  · rw [hpiece i, map_zero]

/-- Sections of `ℤ[ℕ∪{∞}]` over a light profinite set are detected by their restrictions to the
points of that set: a section `x : ℤ[ℕ∪{∞}](S)` whose pullback along every point `pt ⟶ S` is zero
is zero.  (For `S` finite this is `Work.ATOM.zmap_ext_of_closed_cover`; the content is the infinite
case.) -/
theorem points_detect_zfree_NatUnionInfty (S : LightProfinite.{0})
    (x : ↥((Work.ATOM.zfree (LightProfinite.NatUnionInfty)).obj.obj (Opposite.op S)))
    (h : ∀ s : ↥S,
      (Work.ATOM.zfree (LightProfinite.NatUnionInfty)).obj.map (Work.ATOM.ptAt s).op x = 0) :
    x = 0 :=
  points_detect_zfree_of_hind (LightProfinite.NatUnionInfty) S
    (pointClass_independent (LightProfinite.NatUnionInfty)) x h

end

end Work.ANALYTIC
