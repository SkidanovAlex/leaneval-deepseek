/-
# The lift to the cyclic cover is compatible with the groupoid multiplication

This file proves `Work.ORLocInd.Howie.liftPath_pmul`: the lift `liftPath L` to the cyclic cover
`Γ̃` of a `ℤ`-labelled graph `Γ` (see `Submission.Work.ORLocInd.Howie.CoverGraph`) commutes with
the groupoid multiplication `pmul` of the free groupoid `F(Γ)`
(`Submission.Work.ORLocInd.Howie.Basic`).

Since `pmul p q = red (p.comp q)` is the normal form of the concatenation, the statement is a
statement about the interaction of `liftPath` with reduction.  The proof is organised as follows,
all the auxiliary statements living in the local namespace `LiftPathPmulAux`:

* `circle` : the lift of a *backtrack circle* `e · e⁻¹` reduces to the empty path.  Here the
  backtrack in the base graph lifts to a genuine backtrack in the cover, and the crux is the
  geometric identity `(e, m)⁻¹ = (e⁻¹, m + θ e)` (`coverLiftArrow_reverse`);
* `reduceTo_tail` : the same statement with an arbitrary tail `p` glued on, proved by induction
  on `p`.  The level of the tail changes by `θ`-sums, which is handled by `heq_coverLiftArrow`
  (the lifted arrows at equal levels are `HEq`);
* `liftPath_deleteBacktrack` : the lift of a single backtrack deletion in the base graph is a
  reduction in the cover;
* `liftPath_reducesTo` : the lift of a reduction is a reduction;
* `liftPath_red` : the lift of the normal form is the normal form of the lift.

The final statement `liftPath_pmul` is then a short computation: `pmul` is `red` of a
concatenation on both sides, and `liftPath_comp` identifies the lift of a concatenation with the
concatenation of the lifts.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.Basic
import Submission.Work.ORLocInd.Howie.CoverGraph
import Submission.Work.ORLocInd.Howie.liftPath_isReduced
import Submission.Work.ORLocInd.Howie.LiftPathComp
import Submission.Work.ORLocInd.Howie.liftPath_toPath
import Submission.Work.ORLocInd.Howie.coverLiftArrow_reverse

open Quiver

namespace Work.ORLocInd.Howie

variable {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
variable (L : Labelling V)

namespace LiftPathPmulAux

/-- The lift of a backtrack circle reduces to the empty path. -/
theorem circle {x y : V} (e : x ⟶ y) (m : ℤ)
    (heq : (⟨x, m⟩ : CoverVertex L)
      = ⟨x, m + pathSum L.toFun (e.toPath.comp (Quiver.reverse e).toPath)⟩) :
    (liftPath L (e.toPath.comp (Quiver.reverse e).toPath) m).ReducesTo
      ((Quiver.Path.nil : Quiver.Path (⟨x, m⟩ : CoverVertex L) ⟨x, m⟩).cast rfl heq) := by
  have h1 : (⟨y, m + L.toFun (Quiver.Total.mk x y e)⟩ : CoverVertex L)
      = ⟨y, m + pathSum L.toFun e.toPath⟩ :=
    coverVertex_level_eq L (by rw [pathSum_toPath])
  have h2 : (⟨x, (m + pathSum L.toFun e.toPath)
        + L.toFun (Quiver.Total.mk y x (Quiver.reverse e))⟩ : CoverVertex L)
      = ⟨x, (m + pathSum L.toFun e.toPath) + pathSum L.toFun (Quiver.reverse e).toPath⟩ :=
    coverVertex_level_eq L (by rw [pathSum_toPath L.toFun (Quiver.reverse e)])
  have e0 : (⟨x, m⟩ : CoverVertex L)
      = ⟨x, (m + pathSum L.toFun e.toPath) + pathSum L.toFun (Quiver.reverse e).toPath⟩ := by
    refine coverVertex_level_eq L ?_
    rw [← Quiver.Path.reverse_toPath, pathSum_reverse L.toFun L.isBalanced]
    ring
  have e00 : (⟨x, m⟩ : CoverVertex L)
      = ⟨x, (m + pathSum L.toFun e.toPath) + L.toFun (Quiver.Total.mk y x (Quiver.reverse e))⟩ := by
    refine coverVertex_level_eq L ?_
    rw [← Quiver.totalReverse_mk, L.balanced, pathSum_toPath]
    ring
  have h3 : (⟨x, (m + L.toFun (Quiver.Total.mk x y e))
        + L.toFun (Quiver.Total.mk y x (Quiver.reverse e))⟩ : CoverVertex L) = ⟨x, m⟩ := by
    have hb := L.balanced (Quiver.Total.mk x y e)
    rw [Quiver.totalReverse_mk] at hb
    rw [hb]; ring
  have hcomp : liftPath L (e.toPath.comp (Quiver.reverse e).toPath) m
      = ((liftPath L e.toPath m).comp
          (liftPath L (Quiver.reverse e).toPath (m + pathSum L.toFun e.toPath))).cast rfl
          (coverVertex_comp_eq L e.toPath (Quiver.reverse e).toPath m) :=
    liftPath_comp L e.toPath (Quiver.reverse e).toPath m
  rw [hcomp]
  have hR : (Quiver.Path.nil : Quiver.Path (⟨x, m⟩ : CoverVertex L) ⟨x, m⟩).cast rfl heq
      = ((Quiver.Path.nil : Quiver.Path (⟨x, m⟩ : CoverVertex L) ⟨x, m⟩).cast rfl e0).cast rfl
          (coverVertex_comp_eq L e.toPath (Quiver.reverse e).toPath m) := by
    rw [Quiver.Path.cast_cast]
  rw [hR]
  have hF : liftPath L e.toPath m
      = Quiver.Path.cast rfl h1 ((coverLiftArrow L e m).toPath) := by
    rw [liftPath_toPath]
  have hG : liftPath L (Quiver.reverse e).toPath (m + pathSum L.toFun e.toPath)
      = Quiver.Path.cast rfl h2
          ((coverLiftArrow L (Quiver.reverse e) (m + pathSum L.toFun e.toPath)).toPath) := by
    rw [liftPath_toPath]
  have hGF : (coverLiftArrow L (Quiver.reverse e) (m + pathSum L.toFun e.toPath)).cast h1.symm rfl
      = (Quiver.reverse (coverLiftArrow L e m)).cast rfl e00 := by
    refine (Quiver.Hom.cast_eq_cast_iff_heq _ _ _ _ _ _).mpr ?_
    have hrf : Quiver.reverse (coverLiftArrow L e m)
        = (coverLiftArrow L (Quiver.reverse e)
            (m + L.toFun (Quiver.Total.mk x y e))).cast rfl h3 := by
      rw [coverLiftArrow_reverse L e m]
    rw [hrf]
    exact HEq.symm ((Quiver.Hom.cast_heq rfl h3 _).trans
      (heq_coverLiftArrow L (Quiver.reverse e) h1))
  have hY : (Quiver.Path.cast rfl h1 ((coverLiftArrow L e m).toPath)).comp
        (Quiver.Path.cast rfl h2
          ((coverLiftArrow L (Quiver.reverse e) (m + pathSum L.toFun e.toPath)).toPath))
      = (((coverLiftArrow L e m).toPath).comp
          ((Quiver.reverse (coverLiftArrow L e m)).toPath)).cast rfl e0 := by
    rw [Quiver.Path.comp_cast_right']
    rw [Quiver.Path.cast_comp_left']
    rw [Quiver.Path.cast_rfl_rfl]
    rw [Quiver.Path.cast_toPath', hGF, ← Quiver.Path.cast_toPath']
    rw [Quiver.Path.comp_cast_right']
    rw [Quiver.Path.cast_cast]
  have hdel : Quiver.Path.DeleteBacktrack
      (((coverLiftArrow L e m).toPath).comp ((Quiver.reverse (coverLiftArrow L e m)).toPath))
      (Quiver.Path.nil : Quiver.Path (⟨x, m⟩ : CoverVertex L) ⟨x, m⟩) := by
    have h := Quiver.Path.DeleteBacktrack.intro
      (Quiver.Path.nil : Quiver.Path (⟨x, m⟩ : CoverVertex L) ⟨x, m⟩)
      (coverLiftArrow L e m)
      (Quiver.Path.nil : Quiver.Path (⟨x, m⟩ : CoverVertex L) ⟨x, m⟩)
    simpa only [Quiver.Hom.toPath, Quiver.Path.nil_comp, Quiver.Path.comp_nil] using h
  have hDB : (((coverLiftArrow L e m).toPath).comp
        ((Quiver.reverse (coverLiftArrow L e m)).toPath)).ReducesTo
      (Quiver.Path.nil : Quiver.Path (⟨x, m⟩ : CoverVertex L) ⟨x, m⟩) :=
    Quiver.Path.ReducesTo.tail (Quiver.Path.ReducesTo.refl _) hdel
  rw [hF, hG, hY]
  refine Quiver.Path.ReducesTo.cast' rfl
    (coverVertex_comp_eq L e.toPath (Quiver.reverse e).toPath m) ?_
  exact Quiver.Path.ReducesTo.cast' rfl e0 hDB

/-- **The circle lemma with a tail**: reducing the backtrack in the lift of `e · e⁻¹ · p`. -/
theorem reduceTo_tail {x y : V} (e : x ⟶ y) {β : V} (p₂ : Quiver.Path x β) (m : ℤ) :
    ∀ (hm : (⟨β, m + pathSum L.toFun p₂⟩ : CoverVertex L)
        = ⟨β, m + pathSum L.toFun (e.toPath.comp ((Quiver.reverse e).toPath.comp p₂))⟩),
      (liftPath L (e.toPath.comp ((Quiver.reverse e).toPath.comp p₂)) m).ReducesTo
        ((liftPath L p₂ m).cast rfl hm) := by
  induction p₂ with
  | nil =>
    intro hm
    rw [liftPath_nil_cast', Quiver.Path.cast_cast]
    exact circle L e m ((coverVertex_nil_eq L x m).trans hm)
  | cons q f ih =>
    rename_i vb vc
    intro hm
    have hSe : pathSum L.toFun e.toPath = L.toFun (Quiver.Total.mk x y e) :=
      pathSum_toPath L.toFun e
    have hSre : pathSum L.toFun (Quiver.reverse e).toPath = -L.toFun (Quiver.Total.mk x y e) := by
      rw [pathSum_toPath, ← Quiver.totalReverse_mk, L.balanced]
    have hmq : (⟨vb, m + pathSum L.toFun q⟩ : CoverVertex L)
        = ⟨vb, m + pathSum L.toFun (e.toPath.comp ((Quiver.reverse e).toPath.comp q))⟩ := by
      refine coverVertex_level_eq L ?_
      simp only [pathSum_comp, hSre, hSe]
      ring
    have he' : (⟨vc, m + pathSum L.toFun q + L.toFun (Quiver.Total.mk vb vc f)⟩ : CoverVertex L)
        = ⟨vc, m + pathSum L.toFun (e.toPath.comp ((Quiver.reverse e).toPath.comp q))
            + L.toFun (Quiver.Total.mk vb vc f)⟩ := by
      refine coverVertex_level_eq L ?_
      simp only [pathSum_comp, hSre, hSe]
      ring
    let g : (⟨vb, m + pathSum L.toFun (e.toPath.comp ((Quiver.reverse e).toPath.comp q))⟩ : CoverVertex L)
        ⟶ ⟨vc, (m + pathSum L.toFun (e.toPath.comp ((Quiver.reverse e).toPath.comp q)))
            + L.toFun (Quiver.Total.mk vb vc f)⟩ :=
      coverLiftArrow L f (m + pathSum L.toFun (e.toPath.comp ((Quiver.reverse e).toPath.comp q)))
    let g' : (⟨vb, m + pathSum L.toFun q⟩ : CoverVertex L)
        ⟶ ⟨vc, (m + pathSum L.toFun q) + L.toFun (Quiver.Total.mk vb vc f)⟩ :=
      coverLiftArrow L f (m + pathSum L.toFun q)
    have hg : g.cast hmq.symm rfl = g'.cast rfl he' :=
      (Quiver.Hom.cast_eq_cast_iff_heq _ _ _ _ _ _).mpr (heq_coverLiftArrow L f hmq).symm
    have hcons : liftPath L (e.toPath.comp ((Quiver.reverse e).toPath.comp (q.cons f))) m
        = Quiver.Path.cast rfl
            (coverVertex_cons_eq L (e.toPath.comp ((Quiver.reverse e).toPath.comp q)) f m)
            ((liftPath L (e.toPath.comp ((Quiver.reverse e).toPath.comp q)) m).cons g) :=
      liftPath_cons_cast' L (e.toPath.comp ((Quiver.reverse e).toPath.comp q)) f m
    have hcons' : liftPath L (q.cons f) m
        = Quiver.Path.cast rfl (coverVertex_cons_eq L q f m) ((liftPath L q m).cons g') :=
      liftPath_cons_cast' L q f m
    rw [hcons, hcons', Quiver.Path.cast_cast]
    have hiff : (liftPath L (e.toPath.comp ((Quiver.reverse e).toPath.comp q)) m).ReducesTo
        ((liftPath L q m).cast rfl hmq) := ih hmq
    have hiff2 : ((liftPath L (e.toPath.comp ((Quiver.reverse e).toPath.comp q)) m).cons g).ReducesTo
        (((liftPath L q m).cast rfl hmq).cons g) :=
      Quiver.Path.ReducesTo.comp_right hiff g.toPath
    have hcast : ((liftPath L q m)).cons (g'.cast rfl he')
        = (((liftPath L q m)).cons g').cast rfl he' := by
      rw [Quiver.Path.cast_cons, Quiver.Path.cast_rfl_rfl]
    rw [Quiver.Path.cons_cast', hg, hcast] at hiff2
    have hiff3 := Quiver.Path.ReducesTo.cast' rfl
      (coverVertex_cons_eq L (e.toPath.comp ((Quiver.reverse e).toPath.comp q)) f m) hiff2
    rw [Quiver.Path.cast_cast] at hiff3
    exact hiff3

/-- **Lifting a single backtrack deletion.** -/
theorem liftPath_deleteBacktrack {a b : V} {p q : Quiver.Path a b}
    (h : p.DeleteBacktrack q) (n : ℤ)
    (hq : (⟨b, n + pathSum L.toFun q⟩ : CoverVertex L) = ⟨b, n + pathSum L.toFun p⟩) :
    (liftPath L p n).ReducesTo ((liftPath L q n).cast rfl hq) := by
  obtain ⟨x, y, p₁, e, p₂, rfl, rfl⟩ :=
    Work.ORBassSerre.Path.Reduction.deleteBacktrack_cases h
  rw [liftPath_comp L p₁ (e.toPath.comp ((Quiver.reverse e).toPath.comp p₂)) n,
      liftPath_comp L p₁ p₂ n, Quiver.Path.cast_cast]
  have hSe : pathSum L.toFun e.toPath = L.toFun (Quiver.Total.mk x y e) :=
    pathSum_toPath L.toFun e
  have hSre : pathSum L.toFun (Quiver.reverse e).toPath = -L.toFun (Quiver.Total.mk x y e) := by
    rw [pathSum_toPath, ← Quiver.totalReverse_mk, L.balanced]
  have hmid : (⟨b, (n + pathSum L.toFun p₁) + pathSum L.toFun p₂⟩ : CoverVertex L)
      = ⟨b, (n + pathSum L.toFun p₁)
          + pathSum L.toFun (e.toPath.comp ((Quiver.reverse e).toPath.comp p₂))⟩ := by
    refine coverVertex_level_eq L ?_
    simp only [pathSum_comp, hSre, hSe]
    ring
  have hred : ((liftPath L p₁ n).comp
        (liftPath L (e.toPath.comp ((Quiver.reverse e).toPath.comp p₂))
          (n + pathSum L.toFun p₁))).ReducesTo
      ((liftPath L p₁ n).comp ((liftPath L p₂ (n + pathSum L.toFun p₁)).cast rfl hmid)) :=
    reducesTo_comp_left (reduceTo_tail L e p₂ (n + pathSum L.toFun p₁) hmid) (liftPath L p₁ n)
  rw [Quiver.Path.comp_cast_right'] at hred
  have hred2 := Quiver.Path.ReducesTo.cast' rfl
    (coverVertex_comp_eq L p₁ (e.toPath.comp ((Quiver.reverse e).toPath.comp p₂)) n) hred
  rw [Quiver.Path.cast_cast] at hred2
  exact hred2

/-- **Lifting a reduction.** -/
theorem liftPath_reducesTo {a b : V} {p : Quiver.Path a b} :
    ∀ {q : Quiver.Path a b}, p.ReducesTo q → ∀ (n : ℤ)
      (hq : (⟨b, n + pathSum L.toFun q⟩ : CoverVertex L) = ⟨b, n + pathSum L.toFun p⟩),
      (liftPath L p n).ReducesTo ((liftPath L q n).cast rfl hq) := by
  intro q h
  induction h with
  | refl => intro n hq; exact Quiver.Path.ReducesTo.refl _
  | tail hbase hstep ih =>
    rename_i mid fin
    intro n hq
    have hqsum : pathSum L.toFun mid = pathSum L.toFun fin :=
      pathSum_of_reducesTo L.toFun L.isBalanced
        (Quiver.Path.ReducesTo.tail (Quiver.Path.ReducesTo.refl _) hstep)
    have hstep_q : (⟨b, n + pathSum L.toFun fin⟩ : CoverVertex L)
        = ⟨b, n + pathSum L.toFun mid⟩ := by
      rw [hqsum]
    have hq1 : (⟨b, n + pathSum L.toFun mid⟩ : CoverVertex L)
        = ⟨b, n + pathSum L.toFun p⟩ := hstep_q.symm.trans hq
    have hA := ih n hq1
    have hB : ((liftPath L mid n).cast rfl hq1).ReducesTo ((liftPath L fin n).cast rfl hq) := by
      have h2 := Quiver.Path.ReducesTo.cast' rfl hq1 (liftPath_deleteBacktrack L hstep n hstep_q)
      rw [Quiver.Path.cast_cast] at h2
      exact h2
    exact hA.trans hB

/-- **The lift of the normal form is the normal form of the lift.** -/
theorem liftPath_red {a b : V} (p : Quiver.Path a b) (n : ℤ) :
    red (liftPath L p n) = (liftPath L (red p) n).cast rfl
      (coverVertex_level_eq L (by
        rw [← pathSum_of_reducesTo L.toFun L.isBalanced (reducesTo_red p)])) := by
  refine red_eq_of_reducesTo_isReduced (liftPath_reducesTo L (reducesTo_red p) n _) ?_
  exact (isReduced_cast rfl _ (liftPath L (red p) n)).mpr
    (liftPath_isReduced L (red p) (isReduced_red p) n)

end LiftPathPmulAux

theorem liftPath_pmul {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (L : Work.ORLocInd.Howie.Labelling V) {a b c : V} (p : Quiver.Path a b) (q : Quiver.Path b c)
    (n : ℤ)
    (h : (⟨c, (n + Work.ORLocInd.Howie.pathSum L.toFun p) + Work.ORLocInd.Howie.pathSum L.toFun q⟩ :
        Work.ORLocInd.Howie.CoverVertex L) =
      ⟨c, n + Work.ORLocInd.Howie.pathSum L.toFun (Work.ORLocInd.Howie.pmul p q)⟩) :
    Work.ORLocInd.Howie.liftPath L (Work.ORLocInd.Howie.pmul p q) n =
      (Work.ORLocInd.Howie.pmul (Work.ORLocInd.Howie.liftPath L p n)
        (Work.ORLocInd.Howie.liftPath L q (n + Work.ORLocInd.Howie.pathSum L.toFun p))).cast rfl h := by
  change liftPath L (red (p.comp q)) n
    = (red ((liftPath L p n).comp (liftPath L q (n + pathSum L.toFun p)))).cast rfl h
  have h1 : (liftPath L p n).comp (liftPath L q (n + pathSum L.toFun p))
      = (liftPath L (p.comp q) n).cast rfl (coverVertex_comp_eq L p q n).symm := by
    rw [liftPath_comp L p q n, Quiver.Path.cast_cast]
    rw [Subsingleton.elim ((coverVertex_comp_eq L p q n).trans (coverVertex_comp_eq L p q n).symm)
      rfl, Quiver.Path.cast_rfl_rfl]
  rw [h1]
  rw [red_cast']
  rw [Quiver.Path.cast_cast]
  rw [LiftPathPmulAux.liftPath_red L (p.comp q) n]
  rw [Quiver.Path.cast_cast]
  exact (Quiver.Path.eq_cast_iff_heq rfl _ (liftPath L (red (p.comp q)) n)
    (liftPath L (red (p.comp q)) n)).2 (HEq.refl _)

end Work.ORLocInd.Howie
