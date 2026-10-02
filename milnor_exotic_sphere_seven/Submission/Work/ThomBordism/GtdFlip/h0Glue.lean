import Mathlib
import Submission.Work.ThomBordism.GtdFlip.H0Paths
import Submission.Work.Thom.chartCoeffAux
import Submission.Work.Cohomology.h0Evaluation
import Submission.Work.Cohomology.singularCohomology_zero
import Submission.Work.Cohomology.linSimplex_boundary
import Submission.Work.ThomBordism.GtdFlip.exists_class_ptEv

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000

/-!
# Gluing degree-zero cohomology classes on an open cover

In the singular model, `H⁰(X;ℤ)` is the module of functions `X → ℤ` constant on path components
(`Work.Thom.ptEv` reads such a function at a point); consequently two degree-zero classes which
agree at every point of their common domain agree altogether.  This module proves the *gluing*
statement: a family of degree-zero classes on the members of an open cover of `X` whose values
agree at every point of every overlap is the restriction of a global degree-zero class.

The two ingredients are

* `Work.ThomBordism.GtdFlip.ptEv_eq_of_path` (in `H0Paths`): a class of `H⁰` is constant along
  paths, so that the pointwise glued value `glueFun` of the local classes is a function on `π₀`;
* the construction, for every function `g` on `π₀(X)`, of a class of `H⁰(X;ℤ)` whose point
  evaluations are `g` (the formal statement `exists_class_ptEv`, proved by a colleague).

The main statement is `Work.ThomBordism.GtdFlip.h0Glue`.
-/

namespace Work.ThomBordism.GtdFlip

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

noncomputable section

variable {X : Type} [TopologicalSpace X] {ι : Type}

/-! ## The pointwise glued value of a compatible family -/

/-- A chosen member of the cover containing a point. -/
def glueIdx (V : ι → Set X) (hcov : ∀ x : X, ∃ j : ι, x ∈ V j) (x : X) : ι :=
  Classical.choose (hcov x)

/-- The chosen member of the cover does contain the point. -/
theorem glueIdx_mem (V : ι → Set X) (hcov : ∀ x : X, ∃ j : ι, x ∈ V j) (x : X) :
    x ∈ V (glueIdx V hcov x) :=
  Classical.choose_spec (hcov x)

/-- **The pointwise glued value** of a compatible family of degree-zero classes: at a point `x` it
is the value of the chosen local class containing `x`. -/
def glueFun (V : ι → Set X) (hcov : ∀ x : X, ∃ j : ι, x ∈ V j)
    (c : (j : ι) → Work.Thom.Coh ℤ 0 ↥(V j)) (x : X) : ℤ :=
  Work.Thom.ptEv ⟨x, glueIdx_mem V hcov x⟩ (c (glueIdx V hcov x))

/-- **The glued value is the value of any local class whose piece contains the point.**  This is
exactly the compatibility of the family on the overlap of the two pieces. -/
theorem glueFun_eq (V : ι → Set X) (hcov : ∀ x : X, ∃ j : ι, x ∈ V j)
    (c : (j : ι) → Work.Thom.Coh ℤ 0 ↥(V j))
    (hcompat : ∀ (j k : ι) (x : ↥(V j ∩ V k)),
      Work.Thom.ptEv ⟨x.1, x.2.1⟩ (c j) = Work.Thom.ptEv ⟨x.1, x.2.2⟩ (c k))
    (x : X) (j : ι) (hx : x ∈ V j) :
    glueFun V hcov c x = Work.Thom.ptEv ⟨x, hx⟩ (c j) :=
  hcompat (glueIdx V hcov x) j ⟨x, glueIdx_mem V hcov x, hx⟩

/-- **The glued value is constant along paths.**  This is the point at which the compatibility of
the local classes enters beyond the definition of `glueFun`: along a small piece of the path which
stays inside a single member `V j` of the cover, the value is that of the class `c j`, which is
constant along paths (`Work.ThomBordism.GtdFlip.ptEv_eq_of_path`).  Hence `t ↦ glueFun (p t)` is
locally constant on the (preconnected) unit interval. -/
theorem glueFun_eq_of_path (V : ι → Set X) (hopen : ∀ j : ι, IsOpen (V j))
    (hcov : ∀ x : X, ∃ j : ι, x ∈ V j)
    (c : (j : ι) → Work.Thom.Coh ℤ 0 ↥(V j))
    (hcompat : ∀ (j k : ι) (x : ↥(V j ∩ V k)),
      Work.Thom.ptEv ⟨x.1, x.2.1⟩ (c j) = Work.Thom.ptEv ⟨x.1, x.2.2⟩ (c k))
    {x y : X} (p : Path x y) : glueFun V hcov c x = glueFun V hcov c y := by
  have hlc : IsLocallyConstant (fun t : unitInterval => glueFun V hcov c (p t)) := by
    rw [IsLocallyConstant.iff_exists_open]
    intro t
    have hmemt : p t ∈ V (glueIdx V hcov (p t)) := glueIdx_mem V hcov (p t)
    obtain ⟨ε, hεpos, hball⟩ := Metric.isOpen_iff.mp
      ((hopen (glueIdx V hcov (p t))).preimage p.continuous) t hmemt
    refine ⟨Metric.ball t ε, Metric.isOpen_ball, Metric.mem_ball_self hεpos, fun t' ht' => ?_⟩
    have ht'V : p t' ∈ V (glueIdx V hcov (p t)) := hball ht'
    have hdt : abs ((t' : ℝ) - (t : ℝ)) < ε := by
      have h := Metric.mem_ball.mp ht'
      rwa [Subtype.dist_eq, Real.dist_eq] at h
    have hIcc : ∀ r : unitInterval,
        (1 - (r : ℝ)) * (t : ℝ) + (r : ℝ) * (t' : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
      intro r
      constructor <;> nlinarith [r.2.1, r.2.2, t.2.1, t.2.2, t'.2.1, t'.2.2]
    have hdist : ∀ r : unitInterval,
        dist (⟨(1 - (r : ℝ)) * (t : ℝ) + (r : ℝ) * (t' : ℝ), hIcc r⟩ : unitInterval) t < ε := by
      intro r
      rw [Subtype.dist_eq]
      have hr0 : 0 ≤ (r : ℝ) := r.2.1
      have hr1 : (r : ℝ) ≤ 1 := r.2.2
      have heq : (1 - (r : ℝ)) * (t : ℝ) + (r : ℝ) * (t' : ℝ) - (t : ℝ)
          = (r : ℝ) * ((t' : ℝ) - (t : ℝ)) := by ring
      calc abs ((1 - (r : ℝ)) * (t : ℝ) + (r : ℝ) * (t' : ℝ) - (t : ℝ))
          = abs ((r : ℝ) * ((t' : ℝ) - (t : ℝ))) := by rw [heq]
        _ = abs (r : ℝ) * abs ((t' : ℝ) - (t : ℝ)) := abs_mul _ _
        _ = (r : ℝ) * abs ((t' : ℝ) - (t : ℝ)) := by rw [abs_of_nonneg hr0]
        _ ≤ 1 * abs ((t' : ℝ) - (t : ℝ)) :=
              mul_le_mul_of_nonneg_right hr1 (abs_nonneg _)
        _ = abs ((t' : ℝ) - (t : ℝ)) := one_mul _
        _ < ε := hdt
    let q : C(unitInterval, ↥(V (glueIdx V hcov (p t)))) :=
      ⟨fun r => ⟨p ⟨(1 - (r : ℝ)) * (t : ℝ) + (r : ℝ) * (t' : ℝ), hIcc r⟩,
          hball (hdist r)⟩, by
        apply Continuous.subtype_mk
        exact p.continuous.comp (Continuous.subtype_mk (by fun_prop) hIcc)⟩
    have hγ : Work.Thom.ptEv (q 0) (c (glueIdx V hcov (p t)))
        = Work.Thom.ptEv (q 1) (c (glueIdx V hcov (p t))) :=
      ptEv_eq_of_path (c (glueIdx V hcov (p t))) ⟨q, rfl, rfl⟩
    have h0 : q 0 = (⟨p t, hmemt⟩ : ↥(V (glueIdx V hcov (p t)))) := by
      apply Subtype.ext
      show p ⟨(1 - (0 : ℝ)) * (t : ℝ) + (0 : ℝ) * (t' : ℝ), hIcc 0⟩ = p t
      congr 1
      apply Subtype.ext
      norm_num
    have h1 : q 1 = (⟨p t', ht'V⟩ : ↥(V (glueIdx V hcov (p t)))) := by
      apply Subtype.ext
      show p ⟨(1 - (1 : ℝ)) * (t : ℝ) + (1 : ℝ) * (t' : ℝ), hIcc 1⟩ = p t'
      congr 1
      apply Subtype.ext
      norm_num
    rw [h0, h1] at hγ
    rw [glueFun_eq V hcov c hcompat (p t') (glueIdx V hcov (p t)) ht'V,
      glueFun_eq V hcov c hcompat (p t) (glueIdx V hcov (p t)) hmemt]
    exact hγ.symm
  have h := hlc.apply_eq_of_isPreconnected (s := Set.univ) isPreconnected_univ
    (Set.mem_univ (0 : unitInterval)) (Set.mem_univ (1 : unitInterval))
  rw [Path.source, Path.target] at h
  exact h

/-- **The glued value is constant along the edges of the singular complex.**  An edge of the
singular simplicial set between the vertices of the points `x` and `y` is a path from `x` to `y`,
so this follows from `glueFun_eq_of_path`. -/
theorem glueFun_eq_of_edge (V : ι → Set X) (hopen : ∀ j : ι, IsOpen (V j))
    (hcov : ∀ x : X, ∃ j : ι, x ∈ V j)
    (c : (j : ι) → Work.Thom.Coh ℤ 0 ↥(V j))
    (hcompat : ∀ (j k : ι) (x : ↥(V j ∩ V k)),
      Work.Thom.ptEv ⟨x.1, x.2.1⟩ (c j) = Work.Thom.ptEv ⟨x.1, x.2.2⟩ (c k))
    {s t : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk 0))}
    (e : SSet.Edge s t) :
    glueFun V hcov c (TopCat.toSSetObj₀Equiv (X := TopCat.of X) s)
      = glueFun V hcov c (TopCat.toSSetObj₀Equiv (X := TopCat.of X) t) := by
  have e' : SSet.Edge
      ((TopCat.toSSetObj₀Equiv (X := TopCat.of X)).symm
        ((TopCat.toSSetObj₀Equiv (X := TopCat.of X)) s))
      ((TopCat.toSSetObj₀Equiv (X := TopCat.of X)).symm
        ((TopCat.toSSetObj₀Equiv (X := TopCat.of X)) t)) := by
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    exact e
  have h := glueFun_eq_of_path V hopen hcov c hcompat
    (TopCat.pathEquiv (X := TopCat.of X) (TopCat.toSSetObjEdgeEquiv e'))
  exact h

/-! ## The gluing step -/

/-- **Gluing of compatible degree-zero classes on an open cover**, given that every function on
`π₀` is realised by a degree-zero class.  The class realising the glued point function restricts to
each local class, because two degree-zero classes with the same point evaluations agree
(`Work.Thom.ptEv_ext`). -/
theorem glue_of_existsClass
    (hP2 : ∀ (g : (TopCat.toSSet.obj (TopCat.of X)).π₀ → ℤ),
      ∃ c₀ : Work.Thom.Coh ℤ 0 X, ∀ x : X,
        Work.Thom.ptEv x c₀
          = g (SSet.π₀.mk ((TopCat.toSSetObj₀Equiv (X := TopCat.of X)).symm x)))
    (V : ι → Set X) (hopen : ∀ j : ι, IsOpen (V j)) (hcov : ∀ x : X, ∃ j : ι, x ∈ V j)
    (c : (j : ι) → Work.Thom.Coh ℤ 0 ↥(V j))
    (hcompat : ∀ (j k : ι) (x : ↥(V j ∩ V k)),
      Work.Thom.ptEv ⟨x.1, x.2.1⟩ (c j) = Work.Thom.ptEv ⟨x.1, x.2.2⟩ (c k)) :
    ∃ c₀ : Work.Thom.Coh ℤ 0 X, ∀ (j : ι) (x : ↥(V j)),
      Work.Thom.ptEv x ((Work.Thom.CohMap (Work.Thom.subtypeMap (V j)) ℤ 0).hom c₀)
        = Work.Thom.ptEv x (c j) := by
  classical
  let g : (TopCat.toSSet.obj (TopCat.of X)).π₀ → ℤ :=
    SSet.π₀.lift (fun s => glueFun V hcov c (TopCat.toSSetObj₀Equiv (X := TopCat.of X) s))
      (fun s t e => glueFun_eq_of_edge V hopen hcov c hcompat e)
  obtain ⟨c₀, hc₀⟩ := hP2 g
  refine ⟨c₀, fun j x => ?_⟩
  rw [Work.Thom.ptEv_pullback]
  rw [hc₀ ((Work.Thom.subtypeMap (V j)) x)]
  have hg : g (SSet.π₀.mk ((TopCat.toSSetObj₀Equiv (X := TopCat.of X)).symm x.1))
      = glueFun V hcov c x.1 := by
    rw [show g (SSet.π₀.mk ((TopCat.toSSetObj₀Equiv (X := TopCat.of X)).symm x.1))
        = glueFun V hcov c (TopCat.toSSetObj₀Equiv (X := TopCat.of X)
            ((TopCat.toSSetObj₀Equiv (X := TopCat.of X)).symm x.1)) from rfl]
    rw [Equiv.apply_symm_apply]
  rw [show ((Work.Thom.subtypeMap (V j)) x : X) = x.1 from rfl, hg]
  exact glueFun_eq V hcov c hcompat x.1 j x.2

theorem h0Glue {X : Type} [TopologicalSpace X] {ι : Type} (V : ι → Set X)
    (hopen : ∀ j : ι, IsOpen (V j)) (hcov : ∀ x : X, ∃ j : ι, x ∈ V j)
    (c : (j : ι) → Work.Thom.Coh ℤ 0 ↥(V j))
    (hcompat : ∀ (j k : ι) (x : ↥(V j ∩ V k)),
      Work.Thom.ptEv ⟨x.1, x.2.1⟩ (c j) = Work.Thom.ptEv ⟨x.1, x.2.2⟩ (c k)) :
    ∃ c₀ : Work.Thom.Coh ℤ 0 X, ∀ (j : ι) (x : ↥(V j)),
      Work.Thom.ptEv x ((Work.Thom.CohMap (Work.Thom.subtypeMap (V j)) ℤ 0).hom c₀)
        = Work.Thom.ptEv x (c j) :=
  glue_of_existsClass (fun g => exists_class_ptEv X g) V hopen hcov c hcompat

end

end Work.ThomBordism.GtdFlip
