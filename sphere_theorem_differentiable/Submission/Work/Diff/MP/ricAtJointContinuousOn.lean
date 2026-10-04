import Mathlib
import Submission.Work.Diff.MP.Defs
import Submission.Work.Diff.GE.frame_deps
import Submission.Work.Diff.GE.norms_defs
import Submission.Work.Diff.GE.rmP_jointSmooth
import Submission.Work.Diff.EXT.ricAt_invGram_chart
import Submission.Work.Diff.EXT.ric_bound_of_curvBound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Joint continuity of the pointwise Ricci tensor along a smooth metric family

Target: `Work.Diff.MP.ricAtJointContinuousOn` — if `G` is a family of smooth metrics jointly smooth
on an open time set `J`, then the pointwise Ricci tensor `ricAt (lcOf (G t)) x` of the
Levi-Civita connection of `G t`, evaluated on two globally smooth vector fields `A`, `B`, is
*jointly* continuous in `(t, x)` on `Icc a b × U` for `[a,b] ⊆ J` and `U` compact.

## Route

Everything is computed on the chart at the point `x₀` at which continuity is claimed, in the
*coordinate frame* `σᵢ = cFrame x₀ i` of that chart.  Three ingredients:

1. `Work.Diff.MP.ricAt_coordFrame_expansion`: `ricAt` is bilinear, and a section expands in the
   coordinate frame as `A y = ∑ i, (bB.coord i (coordFun x₀ A y)) • σᵢ y`; hence
   `ricAt (lcOf g) y (A y) (B y) = ∑ i j αⁱ(y) βʲ(y) · ricAt (lcOf g) y (σᵢ y) (σⱼ y)`.
2. `Work.Diff.EXT.ricAt_invGram_chart` (already proved): the trace of `w ↦ R(w,u)v` read in the
   coordinate frame is the contraction with the inverse Gram matrix of the frame,
   `Ric(σᵢ,σⱼ) = ∑ k l γᵏˡ · ⟪R(σ_k,σᵢ)σⱼ, σ_l⟫`, i.e. `∑ k l GramInv k l · rmC4 k i l j`.
   Combining 1 and 2 gives the purely chart-expressible identity
   `Work.Diff.MP.ricAt_gramInv_chart_expansion` below.
3. Each factor of that sum is jointly `C^∞` near `(t₀, x₀)`: the coefficients `αⁱ` because `A`,`B`
   are smooth (`Submission.ChartCurv.contMDiffAt_coordFun`), the inverse Gram matrix by
   `Work.Diff.GE.gramInv_jointSmooth` and the curvature components by
   `Work.Diff.GE.rmC4_jointSmooth` (both from `Submission.Diff.JointSmooth G J` and `t₀ ∈ J`).

The target then follows: the sum is jointly `C^∞` at `(t₀, x₀)`, hence continuous there, and it
agrees with the pointwise Ricci tensor on a neighbourhood of `(t₀, x₀)` (the chart source of `x₀`).
Note that the compactness of `U` is not used: `ContinuousOn` is pointwise, and the argument at each
point of `Icc a b × U` is local.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.MP

section Helpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- `ricAt` is linear in its middle argument, in `Finset` form. -/
theorem ricAt_finSum_middle [T2Space M] (hLC : Submission.Diff.LCSmooth I M)
    (g : Submission.Diff.SMet I M) (x : M) (v : TangentSpace I x)
    {ι : Type*} (s : Finset ι) (c : ι → ℝ) (u : ι → TangentSpace I x) :
    Submission.Diff.ricAt (Submission.Diff.lcOf g) x (∑ i ∈ s, c i • u i) v
      = ∑ i ∈ s, c i * Submission.Diff.ricAt (Submission.Diff.lcOf g) x (u i) v := by
  classical
  have hcov : (Submission.Diff.lcOf g).ContMDiffCovariantDerivative ∞ := (hLC g).1.some
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      simpa using Work.Diff.EXT.ricAt_smul_middle_L g hcov x (0 : ℝ) (0 : TangentSpace I x) v
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        Work.Diff.EXT.ricAt_add_middle_L g hcov x _ _ v,
        Work.Diff.EXT.ricAt_smul_middle_L g hcov x (c a) (u a) v, ih]

/-- `ricAt` is linear in its last argument, in `Finset` form. -/
theorem ricAt_finSum_last [T2Space M] (hLC : Submission.Diff.LCSmooth I M)
    (g : Submission.Diff.SMet I M) (x : M) (w : TangentSpace I x)
    {ι : Type*} (s : Finset ι) (c : ι → ℝ) (u : ι → TangentSpace I x) :
    Submission.Diff.ricAt (Submission.Diff.lcOf g) x w (∑ i ∈ s, c i • u i)
      = ∑ i ∈ s, c i * Submission.Diff.ricAt (Submission.Diff.lcOf g) x w (u i) := by
  classical
  have hcov : (Submission.Diff.lcOf g).ContMDiffCovariantDerivative ∞ := (hLC g).1.some
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      simpa using Work.Diff.EXT.ricAt_smul_last_L g hcov x (0 : ℝ) w (0 : TangentSpace I x)
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        Work.Diff.EXT.ricAt_add_last_L g hcov x w _ _,
        Work.Diff.EXT.ricAt_smul_last_L g hcov x (c a) w (u a), ih]

/-- **Expansion of `ricAt` in the coordinate frame of the chart at `x₀`.**  For a point `p` of the
chart source, the sections `A`, `B` expand as `A p = ∑ i, αⁱ • σᵢ p` with the chart coordinates
`αⁱ = (bB.coord i) ∘ coordFun x₀ A`, so by bilinearity of `ricAt` (in its two vector slots) its
value is the corresponding bilinear combination of the frame values. -/
theorem ricAt_coordFrame_expansion [T2Space M] (hLC : Submission.Diff.LCSmooth I M)
    (g : Submission.Diff.SMet I M) (x₀ : M) {p : M} (hp : p ∈ (chartAt H x₀).source)
    (A B : Π y : M, TangentSpace I y) :
    Submission.Diff.ricAt (Submission.Diff.lcOf g) p (A p) (B p)
      = ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          ((Module.finBasis ℝ E).coord i (Submission.ChartCurv.coordFun x₀ A p))
          * ((Module.finBasis ℝ E).coord j (Submission.ChartCurv.coordFun x₀ B p))
          * Submission.Diff.ricAt (Submission.Diff.lcOf g) p
              (Work.Diff.GE.cFrame (I := I) x₀ i p) (Work.Diff.GE.cFrame (I := I) x₀ j p) := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ((⊤ : ℕ∞) : WithTop ℕ∞) E
      (fun x : M ↦ TangentSpace I x) := inferInstance
  have hA := Work.Diff.GE.section_eq_sum_coordFun (I := I) (M := M) (x₀ := x₀) (W := A) hp
  have hB := Work.Diff.GE.section_eq_sum_coordFun (I := I) (M := M) (x₀ := x₀) (W := B) hp
  have hsum :=
    ricAt_finSum_middle (I := I) (M := M) hLC g p
      (∑ j : Fin (Module.finrank ℝ E),
        (Module.finBasis ℝ E).coord j (Submission.ChartCurv.coordFun x₀ B p)
          • Work.Diff.GE.cFrame (I := I) x₀ j p)
      (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun i => (Module.finBasis ℝ E).coord i (Submission.ChartCurv.coordFun x₀ A p))
      (fun i => Work.Diff.GE.cFrame (I := I) x₀ i p)
  rw [hA, hB, hsum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [ricAt_finSum_last (I := I) (M := M) hLC g p (Work.Diff.GE.cFrame (I := I) x₀ i p)
      (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun j => (Module.finBasis ℝ E).coord j (Submission.ChartCurv.coordFun x₀ B p))
      (fun j => Work.Diff.GE.cFrame (I := I) x₀ j p)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-- **The `GramInv`/`rmC4` form of the pointwise Ricci tensor.**  On the chart at `x₀`, the Ricci
tensor of the metric `G t`, evaluated on two arbitrary sections, is the contraction of the inverse
Gram matrix of the coordinate frame with the frame curvature components `rmC4`:

`Ric(A p, B p) = ∑ i j αⁱ(p) βʲ(p) · ∑ k l γᵏˡ(p) · rmC4 k i l j`,

where `αⁱ`, `βʲ` are the chart coordinates of `A p`, `B p`.  Every factor on the right is a
jointly smooth function of `(t,p)` near `(t₀, x₀)`. -/
theorem ricAt_gramInv_chart_expansion [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ)
    {p : M} (hp : p ∈ (chartAt H x₀).source) (A B : Π y : M, TangentSpace I y) :
    Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) p (A p) (B p)
      = ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          ((Module.finBasis ℝ E).coord i (Submission.ChartCurv.coordFun x₀ A p))
          * ((Module.finBasis ℝ E).coord j (Submission.ChartCurv.coordFun x₀ B p))
          * ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
              Work.Diff.GE.GramInv (I := I) G x₀ t p k l
                * Work.Diff.GE.rmC4 (I := I) G x₀ t p k i l j := by
  rw [ricAt_coordFrame_expansion (I := I) (M := M) hLC (G t) x₀ hp A B]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  have key : Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) p
        (Work.Diff.GE.cFrame (I := I) x₀ i p) (Work.Diff.GE.cFrame (I := I) x₀ j p)
      = ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          Work.Diff.GE.GramInv (I := I) G x₀ t p k l
            * Work.Diff.GE.rmC4 (I := I) G x₀ t p k i l j := by
    rw [show Work.Diff.GE.cFrame (I := I) x₀ i p
          = Work.Diff.EXT.cvec (I := I) x₀ p (Work.Diff.EXT.bB (E := E) i) from rfl,
        show Work.Diff.GE.cFrame (I := I) x₀ j p
          = Work.Diff.EXT.cvec (I := I) x₀ p (Work.Diff.EXT.bB (E := E) j) from rfl,
        Work.Diff.EXT.ricAt_invGram_chart (I := I) (M := M) (G t) x₀ hp i j]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
    rfl
  rw [key]

end Helpers

theorem ricAtJointContinuousOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → Submission.Diff.SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : Submission.Diff.JointSmooth G J)
    {a b : ℝ} (hJab : ∀ s ∈ Set.Icc a b, s ∈ J)
    (A B : Π y : M, TangentSpace I y)
    (hA : Work.Diff.GE.SmoothField (I := I) (M := M) A)
    (hB : Work.Diff.GE.SmoothField (I := I) (M := M) B)
    {U : Set M} (hU : IsCompact U) :
    ContinuousOn (fun p : ℝ × M =>
      Submission.Diff.ricAt (Submission.Diff.lcOf (G p.1)) p.2 (A p.2) (B p.2))
      (Set.prod (Set.Icc a b) U) := by
  rintro ⟨t₀, x₀⟩ hp
  obtain ⟨ht₀, hx₀⟩ := hp
  have ht₀J : t₀ ∈ J := hJab t₀ ht₀
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G t₀).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ((⊤ : ℕ∞) : WithTop ℕ∞) E
      (fun x : M ↦ TangentSpace I x) := inferInstance
  -- a neighbourhood of `(t₀, x₀)` on which the chart at `x₀` is available
  have hsrc : ∀ᶠ q : ℝ × M in 𝓝 (t₀, x₀), q.2 ∈ (chartAt H x₀).source :=
    (continuous_snd.tendsto (t₀, x₀)).eventually
      ((chartAt H x₀).open_source.mem_nhds (mem_chart_source H x₀))
  -- the chart coordinates of a smooth field are jointly smooth
  have hcoef : ∀ (V : Π y : M, TangentSpace I y), Work.Diff.GE.SmoothField (I := I) (M := M) V →
      ∀ i : Fin (Module.finrank ℝ E),
        ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
          (fun q : ℝ × M ↦ (Module.finBasis ℝ E).coord i
            (Submission.ChartCurv.coordFun x₀ V q.2)) (t₀, x₀) := by
    intro V hV i
    have h1 : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, E) ∞
        (fun q : ℝ × M ↦ Submission.ChartCurv.coordFun x₀ V q.2) (t₀, x₀) :=
      (Submission.ChartCurv.contMDiffAt_coordFun (I := I) (M := M) x₀ hV
        (mem_chart_source H x₀)).comp (t₀, x₀) contMDiffAt_snd
    exact (ContinuousLinearMap.contMDiffAt
      (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i))).comp (t₀, x₀) h1
  -- the model sum is jointly smooth at `(t₀, x₀)`
  have hmodel : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M ↦ ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          ((Module.finBasis ℝ E).coord i (Submission.ChartCurv.coordFun x₀ A q.2))
          * ((Module.finBasis ℝ E).coord j (Submission.ChartCurv.coordFun x₀ B q.2))
          * ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
              Work.Diff.GE.GramInv (I := I) G x₀ q.1 q.2 k l
                * Work.Diff.GE.rmC4 (I := I) G x₀ q.1 q.2 k i l j) (t₀, x₀) := by
    refine ContMDiffAt.sum (fun i _ => ContMDiffAt.sum (fun j _ => ?_))
    refine ((hcoef A hA i).mul (hcoef B hB j)).mul ?_
    refine ContMDiffAt.sum (fun k _ => ContMDiffAt.sum (fun l _ => ?_))
    exact (Work.Diff.GE.gramInv_jointSmooth (I := I) (M := M) hJ hG ht₀J x₀ k l).mul
      (Work.Diff.GE.rmC4_jointSmooth (I := I) (M := M) hLC hJ hG ht₀J x₀ k i l j)
  -- the pointwise Ricci tensor agrees with the model sum near `(t₀, x₀)`
  have hev : (fun q : ℝ × M ↦
        Submission.Diff.ricAt (Submission.Diff.lcOf (G q.1)) q.2 (A q.2) (B q.2))
      =ᶠ[𝓝 (t₀, x₀)]
      (fun q : ℝ × M ↦ ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          ((Module.finBasis ℝ E).coord i (Submission.ChartCurv.coordFun x₀ A q.2))
          * ((Module.finBasis ℝ E).coord j (Submission.ChartCurv.coordFun x₀ B q.2))
          * ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
              Work.Diff.GE.GramInv (I := I) G x₀ q.1 q.2 k l
                * Work.Diff.GE.rmC4 (I := I) G x₀ q.1 q.2 k i l j) := by
    filter_upwards [hsrc] with q hq
    exact ricAt_gramInv_chart_expansion (I := I) (M := M) hLC G x₀ q.1 hq A B
  exact (hmodel.continuousAt.congr hev.symm).continuousWithinAt

end Work.Diff.MP
