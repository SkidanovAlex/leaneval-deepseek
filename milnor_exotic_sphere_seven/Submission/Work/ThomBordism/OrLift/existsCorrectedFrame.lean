import Mathlib
import Submission.Work.ThomBordism.OrLift.ogFlipNeSelf
import Submission.Work.ThomBordism.Grassmann.chartFrameAt
import Submission.Work.PTGeometric.exists_projOfPlane
import Submission.Work.ThomBordism.Grassmann.projOfPlaneEqIff

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Correcting a chart-wise family of oriented planes to a continuous frame field

The base set `baseSet S` of a chart `S` of the oriented Grassmannian `G̃r_k(ℝ^{k+m})` consists of the
oriented `k`-planes whose projection to the `S`-coordinates is an isomorphism.  Over such a chart the
frame bundle is trivial, but the *canonical* frame attached to the chart (the Gram–Schmidt
orthonormalisation of the coordinate frame, `Work.ThomBordism.Grassmann.chartFrame`) need not be a
section of `ogMk`: it represents the plane *or its orientation reversal*, the ambiguity depending on
the sign of the `S`-minor of the frame (`Work.ThomBordism.Grassmann.frameSign`) which is itself a
locally constant but non-constant function on the chart.

The main theorem `existsCorrectedFrame` corrects this: every continuous family of points of a chart
of the oriented Grassmannian can be lifted to a continuous family of orthonormal frames.  The
correction is by the orientation-reversing change of frame `orLiftFlip` (`f ↦ diag(-1,1,…)·f`),
applied on the (clopen) set where the chart frame has the wrong orientation; continuity on that
clopen set and its complement is `Work.ThomBordism.ol_continuous_ite_of_clopen`, and the fact that
the correction set *is* clopen uses `Work.ThomBordism.ol_ogFlip_ne_self` (the orientation reversal
has no fixed point for `k ≥ 1`).
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

namespace Work.ThomBordism.OrLift

open scoped Topology
open Work.ThomBordism.Grassmann

noncomputable section

variable {k m : ℕ}

/-- **The orthogonal projection onto an orthonormal frame depends only on its span.**  Two
orthonormal frames with the same span define the same self-adjoint idempotent, and two self-adjoint
idempotents with the same range agree: for `u := P w - Q w` in the common range one has
`⟪u, u⟫ = ⟪P u, w⟫ - ⟪Q u, w⟫ = ⟪u, w⟫ - ⟪u, w⟫ = 0`. -/
theorem frameProj_eq_of_span_eq {f g : Fin k → Amb (k + m)}
    (hf : Orthonormal ℝ f) (hg : Orthonormal ℝ g)
    (h : Submodule.span ℝ (Set.range f) = Submodule.span ℝ (Set.range g)) :
    Work.PTGeometric.frameProj f = Work.PTGeometric.frameProj g := by
  have hfixf : ∀ v ∈ LinearMap.range
      ((Work.PTGeometric.frameProj f : Amb (k + m) →L[ℝ] Amb (k + m)) :
        Amb (k + m) →ₗ[ℝ] Amb (k + m)), Work.PTGeometric.frameProj f v = v := by
    rintro v ⟨y, rfl⟩
    simpa using congrArg (fun T : Amb (k + m) →L[ℝ] Amb (k + m) => T y)
      (Work.PTGeometric.frameProj_mul_self hf)
  have hfixg : ∀ v ∈ LinearMap.range
      ((Work.PTGeometric.frameProj g : Amb (k + m) →L[ℝ] Amb (k + m)) :
        Amb (k + m) →ₗ[ℝ] Amb (k + m)), Work.PTGeometric.frameProj g v = v := by
    rintro v ⟨y, rfl⟩
    simpa using congrArg (fun T : Amb (k + m) →L[ℝ] Amb (k + m) => T y)
      (Work.PTGeometric.frameProj_mul_self hg)
  have hrange : LinearMap.range ((Work.PTGeometric.frameProj f :
          Amb (k + m) →L[ℝ] Amb (k + m)) : Amb (k + m) →ₗ[ℝ] Amb (k + m))
      = LinearMap.range ((Work.PTGeometric.frameProj g :
          Amb (k + m) →L[ℝ] Amb (k + m)) : Amb (k + m) →ₗ[ℝ] Amb (k + m)) := by
    rw [Work.PTGeometric.frameProj_range hf, Work.PTGeometric.frameProj_range hg, h]
  refine ContinuousLinearMap.ext fun w => ?_
  have hmem : Work.PTGeometric.frameProj f w - Work.PTGeometric.frameProj g w ∈ LinearMap.range
      ((Work.PTGeometric.frameProj f : Amb (k + m) →L[ℝ] Amb (k + m)) :
        Amb (k + m) →ₗ[ℝ] Amb (k + m)) := by
    refine Submodule.sub_mem _ ⟨w, rfl⟩ ?_
    rw [hrange]
    exact ⟨w, rfl⟩
  have h0 : inner ℝ (Work.PTGeometric.frameProj f w - Work.PTGeometric.frameProj g w)
      (Work.PTGeometric.frameProj f w - Work.PTGeometric.frameProj g w) = 0 := by
    have h1 : inner ℝ (Work.PTGeometric.frameProj f w - Work.PTGeometric.frameProj g w)
          (Work.PTGeometric.frameProj f w)
        = inner ℝ (Work.PTGeometric.frameProj f w - Work.PTGeometric.frameProj g w) w := by
      rw [← Work.PTGeometric.frameProj_inner_eq f _ w, hfixf _ hmem]
    have h2 : inner ℝ (Work.PTGeometric.frameProj f w - Work.PTGeometric.frameProj g w)
          (Work.PTGeometric.frameProj g w)
        = inner ℝ (Work.PTGeometric.frameProj f w - Work.PTGeometric.frameProj g w) w := by
      rw [← Work.PTGeometric.frameProj_inner_eq g _ w, hfixg _ (by rw [← hrange]; exact hmem)]
    rw [inner_sub_right, h1, h2, sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp h0)

/-- **The orientation-reversing change of frame**: right multiplication by `diag(-1,1,…,1)`. -/
def orLiftFlip (g : Stiefel k m) : Stiefel k m :=
  ⟨soActFun (flipMat k) g.1, orthonormal_soActFun (flipMat_transpose_mul k) g.2⟩

theorem continuous_orLiftFlip : Continuous (orLiftFlip : Stiefel k m → Stiefel k m) := by
  refine Continuous.subtype_mk ?_ _
  exact continuous_soActFun.comp (Continuous.prodMk continuous_const continuous_subtype_val)

/-- The frame `orLiftFlip g` represents the orientation reversal of the plane of `g`. -/
theorem ogMk_orLiftFlip (g : Stiefel k m) :
    ogMk k m (orLiftFlip g) = ogFlip k m (ogMk k m g) :=
  (ogFlip_mk g).symm

/-- **The chart frame of a chart of the oriented Grassmannian can be corrected to a continuous
frame field.**  For every continuous family `γ` of points of the chart `baseSet S` there is a
continuous family `f` of orthonormal frames representing it. -/
theorem existsCorrectedFrame (k m : ℕ) {X : Type*} [TopologicalSpace X]
    (S : Work.ThomBordism.Grassmann.ChartIdx k m)
    (γ : X → ↥(Work.ThomBordism.Grassmann.baseSet S)) (hγ : Continuous γ) :
    ∃ f : X → Work.ThomBordism.Grassmann.Stiefel k m, Continuous f ∧
      ∀ x, Work.ThomBordism.Grassmann.ogMk k m (f x) = (γ x : Work.ThomBordism.Grassmann.OG k m) := by
  classical
  by_cases hk : k = 0
  · subst hk
    haveI : Subsingleton (OG 0 m) := Quotient.instSubsingletonQuotient _
    exact ⟨fun _ => Classical.choice (nonempty_stiefel 0 m), continuous_const,
      fun x => Subsingleton.elim _ _⟩
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hsec : ∃ s : ↥(baseSet S) → Stiefel k m, Continuous s ∧
        ∀ y, ogMk k m (s y) = (y : OG k m) := by
      obtain ⟨F, hForth, hFspan, hFcont⟩ := exists_chartFrameAt k m S
      let G : ↥(baseSet S) → Stiefel k m := fun x => ⟨F x, hForth x⟩
      have hGcont : Continuous G := hFcont.subtype_mk _
      let ρ : ↥(baseSet S) → OG k m := fun x => ogMk k m (G x)
      have hρcont : Continuous ρ := (ogMk k m).continuous.comp hGcont
      -- the representative of a point of the chart used to compare with the chart frame
      have hout : ∀ x : ↥(baseSet S),
          (Quotient.out (x : OG k m) : Stiefel k m) ∈ chartSet S := by
        intro x
        have hx : (x : OG k m) ∈ baseSet S := x.2
        have h1 : (Quotient.mk'' (Quotient.out (x : OG k m)) : OG k m) = (x : OG k m) :=
          Quotient.out_eq _
        rw [← h1] at hx
        exact (mem_baseSet_iff S (Quotient.out (x : OG k m))).mp hx
      -- the chart frame represents the point or its orientation reversal
      have halt : ∀ x : ↥(baseSet S),
          ρ x = (x : OG k m) ∨ ρ x = ogFlip k m (x : OG k m) := by
        intro x
        have hspanG : Submodule.span ℝ (Set.range (G x).1)
            = Submodule.span ℝ (Set.range (fun v : Amb k => evalChart S (x, v))) := hFspan x
        have hspano : Submodule.span ℝ
              (Set.range (Quotient.out (x : OG k m) : Stiefel k m).1)
            = Submodule.span ℝ (Set.range (fun v : Amb k => evalChart S (x, v))) :=
          (span_evalChart_eq S x (Quotient.out (x : OG k m)) (hout x)
            (Quotient.out_eq (x : OG k m)).symm).symm
        have hfp : Work.PTGeometric.frameProj (G x).1
            = Work.PTGeometric.frameProj (Quotient.out (x : OG k m) : Stiefel k m).1 :=
          frameProj_eq_of_span_eq (hForth x) (Quotient.out (x : OG k m)).2
            (by rw [hspanG, hspano])
        rcases eq_or_flip_of_frameProj_eq (G x) (Quotient.out (x : OG k m)) hfp with h | h
        · left
          exact h.trans (Quotient.out_eq (x : OG k m))
        · right
          exact h.trans (congrArg (ogFlip k m) (Quotient.out_eq (x : OG k m)))
      -- the set on which the chart frame has the correct orientation is clopen
      let Z : Set ↥(baseSet S) := {x | ρ x = (x : OG k m)}
      have hZcl : IsClopen Z := by
        have hZclosed : IsClosed Z := isClosed_eq hρcont continuous_subtype_val
        have hWclosed : IsClosed {x : ↥(baseSet S) | ogFlip k m (ρ x) = (x : OG k m)} :=
          isClosed_eq ((continuous_ogFlip k m).comp hρcont) continuous_subtype_val
        have hcompl : Zᶜ = {x : ↥(baseSet S) | ogFlip k m (ρ x) = (x : OG k m)} := by
          ext x
          constructor
          · intro hx
            rcases halt x with h | h
            · exact absurd h hx
            · show ogFlip k m (ρ x) = (x : OG k m)
              rw [h, ogFlip_idem]
          · intro hx hxZ
            have hxZ' : ρ x = (x : OG k m) := hxZ
            have h2 : ogFlip k m (x : OG k m) = (x : OG k m) := by
              rw [← hxZ', hx, hxZ']
            exact ol_ogFlip_ne_self hkpos (x : OG k m) h2
        have hZeq : Z = ({x : ↥(baseSet S) | ogFlip k m (ρ x) = (x : OG k m)})ᶜ := by
          rw [← hcompl]
          ext x
          simp
        exact ⟨hZclosed, hZeq ▸ hWclosed.isOpen_compl⟩
      have hscont : Continuous fun y : ↥(baseSet S) =>
          if y ∈ Z then G y else orLiftFlip (G y) :=
        ol_continuous_ite_of_clopen hZcl hGcont (continuous_orLiftFlip.comp hGcont)
      have hssec : ∀ y : ↥(baseSet S),
          ogMk k m (if y ∈ Z then G y else orLiftFlip (G y)) = (y : OG k m) := by
        intro y
        by_cases hy : y ∈ Z
        · rw [if_pos hy]
          exact hy
        · rw [if_neg hy, ogMk_orLiftFlip]
          have h1 : ρ y = ogFlip k m (y : OG k m) := by
            rcases halt y with h | h
            · exact absurd h hy
            · exact h
          show ogFlip k m (ρ y) = (y : OG k m)
          rw [h1, ogFlip_idem]
      exact ⟨_, hscont, hssec⟩
    obtain ⟨s, hscont, hssec⟩ := hsec
    exact ⟨fun x => s (γ x), hscont.comp hγ, fun x => hssec (γ x)⟩

end

end Work.ThomBordism.OrLift
