import Mathlib
import Submission.Work.Whitney.TripleLocusDefs
import Submission.Work.Projection.dimH_badImmCharts

/-!
# Smoothness of the triple parametrisation

The triple parametrisation `Work.Projection.tripleParam e p q r` of
`Submission.Work.Whitney.TripleLocusDefs` is built from the chart representations of the embedding
`e` (smooth on the chart targets) and the map `(u, w) ↦ projVec u w` (a polynomial, hence `C¹`), so
it is `C¹` on the open set of triples of chart parameters lying in the chart targets.
-/

open scoped Manifold ContDiff
open Topology

namespace Work.Projection

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- **The map `(u, w) ↦ projVec u w` is `C¹`.**  It decomposes as
`projVec u w = projVec 0 w - (w last) • u`, a sum of a continuous linear map and of a product of
two continuous linear maps. -/
lemma contDiff_projVec_pair (k : ℕ) :
    ContDiff ℝ 1 (fun y : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (k + 1)) =>
      projVec y.1 y.2) := by
  have hdecomp : (fun y : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (k + 1)) =>
        projVec y.1 y.2)
      = fun y : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (k + 1)) =>
        projVec (0 : EuclideanSpace ℝ (Fin k)) y.2 - (y.2 (Fin.last k)) • y.1 := by
    funext x
    apply WithLp.ofLp_injective
    funext i
    simp only [projVec_apply]
    simp
    ring
  rw [hdecomp]
  refine ContDiff.sub ?_ ?_
  · exact ((projVec (0 : EuclideanSpace ℝ (Fin k))).comp
      (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin k))
        (EuclideanSpace ℝ (Fin (k + 1))))).contDiff (n := (1 : ℕ∞ω))
  · have hf : ContDiff ℝ 1 (fun y : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (k + 1)) =>
        y.2 (Fin.last k)) :=
      ((EuclideanSpace.proj (Fin.last k)).comp
        (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin k))
          (EuclideanSpace ℝ (Fin (k + 1))))).contDiff (n := (1 : ℕ∞ω))
    have hg : ContDiff ℝ 1 (fun y : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (k + 1)) =>
        y.1) :=
      (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin k))
        (EuclideanSpace ℝ (Fin (k + 1)))).contDiff (n := (1 : ℕ∞ω))
    exact hf.smul hg

/-- The open set of triples of chart parameters lying in the three chart targets. -/
def tripleTgt (p q r : M) :
    Set ((Fin 3 → EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin (2 * n))) :=
  {x | x.1 0 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).target ∧
       x.1 1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q).target ∧
       x.1 2 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) r).target}

lemma isOpen_tripleTgt {p q r : M} : IsOpen (tripleTgt (n := n) p q r) := by
  have h0 : IsOpen {x : (Fin 3 → EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin (2 * n)) |
      x.1 0 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).target} :=
    IsOpen.preimage (f := fun x : (Fin 3 → EuclideanSpace ℝ (Fin n)) ×
        EuclideanSpace ℝ (Fin (2 * n)) => x.1 0) (by fun_prop)
      (chartAt (EuclideanSpace ℝ (Fin n)) p).open_target
  have h1 : IsOpen {x : (Fin 3 → EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin (2 * n)) |
      x.1 1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q).target} :=
    IsOpen.preimage (f := fun x : (Fin 3 → EuclideanSpace ℝ (Fin n)) ×
        EuclideanSpace ℝ (Fin (2 * n)) => x.1 1) (by fun_prop)
      (chartAt (EuclideanSpace ℝ (Fin n)) q).open_target
  have h2 : IsOpen {x : (Fin 3 → EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin (2 * n)) |
      x.1 2 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) r).target} :=
    IsOpen.preimage (f := fun x : (Fin 3 → EuclideanSpace ℝ (Fin n)) ×
        EuclideanSpace ℝ (Fin (2 * n)) => x.1 2) (by fun_prop)
      (chartAt (EuclideanSpace ℝ (Fin n)) r).open_target
  exact h0.inter (h1.inter h2)

/-- **The triple parametrisation is `C¹` on the chart targets.** -/
lemma contDiffOn_tripleParam (e : M → EuclideanSpace ℝ (Fin (2 * n + 1)))
    (he : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n + 1)))) ((⊤ : ℕ∞) : WithTop ℕ∞) e)
    (p q r : M) :
    ContDiffOn ℝ 1 (tripleParam e p q r) (tripleTgt (n := n) p q r) := by
  have hcp : ContDiffOn ℝ 1 (chartRep e p) (chartAt (EuclideanSpace ℝ (Fin n)) p).target :=
    (contDiffOn_chartRep (k := 2 * n) e he p).of_le (by norm_num)
  have hcq : ContDiffOn ℝ 1 (chartRep e q) (chartAt (EuclideanSpace ℝ (Fin n)) q).target :=
    (contDiffOn_chartRep (k := 2 * n) e he q).of_le (by norm_num)
  have hcr : ContDiffOn ℝ 1 (chartRep e r) (chartAt (EuclideanSpace ℝ (Fin n)) r).target :=
    (contDiffOn_chartRep (k := 2 * n) e he r).of_le (by norm_num)
  have hZ1 : ContDiffOn ℝ 1 (fun x : (Fin 3 → EuclideanSpace ℝ (Fin n)) ×
      EuclideanSpace ℝ (Fin (2 * n)) => pairZ e p q (x.1 0, x.1 1))
      (tripleTgt (n := n) p q r) := by
    have hp : ContDiffOn ℝ 1 (fun x : (Fin 3 → EuclideanSpace ℝ (Fin n)) ×
        EuclideanSpace ℝ (Fin (2 * n)) => chartRep e p (x.1 0)) (tripleTgt (n := n) p q r) :=
      hcp.comp ((((ContinuousLinearMap.proj (0 : Fin 3)).comp
          (ContinuousLinearMap.fst ℝ ((Fin 3 → EuclideanSpace ℝ (Fin n)))
          (EuclideanSpace ℝ (Fin (2 * n))))).contDiff (n := (1 : ℕ∞ω))).contDiffOn.mono
            (Set.subset_univ _)) (fun x hx => hx.1)
    have hq : ContDiffOn ℝ 1 (fun x : (Fin 3 → EuclideanSpace ℝ (Fin n)) ×
        EuclideanSpace ℝ (Fin (2 * n)) => chartRep e q (x.1 1)) (tripleTgt (n := n) p q r) :=
      hcq.comp ((((ContinuousLinearMap.proj (1 : Fin 3)).comp
          (ContinuousLinearMap.fst ℝ ((Fin 3 → EuclideanSpace ℝ (Fin n)))
          (EuclideanSpace ℝ (Fin (2 * n))))).contDiff (n := (1 : ℕ∞ω))).contDiffOn.mono
            (Set.subset_univ _)) (fun x hx => hx.2.1)
    simpa only [pairZ] using hq.sub hp
  have hZ2 : ContDiffOn ℝ 1 (fun x : (Fin 3 → EuclideanSpace ℝ (Fin n)) ×
      EuclideanSpace ℝ (Fin (2 * n)) => pairZ e p r (x.1 0, x.1 2))
      (tripleTgt (n := n) p q r) := by
    have hp : ContDiffOn ℝ 1 (fun x : (Fin 3 → EuclideanSpace ℝ (Fin n)) ×
        EuclideanSpace ℝ (Fin (2 * n)) => chartRep e p (x.1 0)) (tripleTgt (n := n) p q r) :=
      hcp.comp ((((ContinuousLinearMap.proj (0 : Fin 3)).comp
          (ContinuousLinearMap.fst ℝ ((Fin 3 → EuclideanSpace ℝ (Fin n)))
          (EuclideanSpace ℝ (Fin (2 * n))))).contDiff (n := (1 : ℕ∞ω))).contDiffOn.mono
            (Set.subset_univ _)) (fun x hx => hx.1)
    have hr : ContDiffOn ℝ 1 (fun x : (Fin 3 → EuclideanSpace ℝ (Fin n)) ×
        EuclideanSpace ℝ (Fin (2 * n)) => chartRep e r (x.1 2)) (tripleTgt (n := n) p q r) :=
      hcr.comp ((((ContinuousLinearMap.proj (2 : Fin 3)).comp
          (ContinuousLinearMap.fst ℝ ((Fin 3 → EuclideanSpace ℝ (Fin n)))
          (EuclideanSpace ℝ (Fin (2 * n))))).contDiff (n := (1 : ℕ∞ω))).contDiffOn.mono
            (Set.subset_univ _)) (fun x hx => hx.2.2)
    simpa only [pairZ] using hr.sub hp
  have hsnd : ContDiffOn ℝ 1 (fun x : (Fin 3 → EuclideanSpace ℝ (Fin n)) ×
      EuclideanSpace ℝ (Fin (2 * n)) => x.2) (tripleTgt (n := n) p q r) :=
    ((ContinuousLinearMap.snd ℝ ((Fin 3 → EuclideanSpace ℝ (Fin n)))
      (EuclideanSpace ℝ (Fin (2 * n)))).contDiff (n := (1 : ℕ∞ω))).contDiffOn
  have h1 : ContDiffOn ℝ 1 (fun x : (Fin 3 → EuclideanSpace ℝ (Fin n)) ×
      EuclideanSpace ℝ (Fin (2 * n)) => projVec x.2 (pairZ e p q (x.1 0, x.1 1)))
      (tripleTgt (n := n) p q r) := by
    have hbase : ContDiffOn ℝ 1 (fun x : (Fin 3 → EuclideanSpace ℝ (Fin n)) ×
        EuclideanSpace ℝ (Fin (2 * n)) =>
          projVec (0 : EuclideanSpace ℝ (Fin (2 * n))) (pairZ e p q (x.1 0, x.1 1)))
        (tripleTgt (n := n) p q r) :=
      ((projVec (0 : EuclideanSpace ℝ (Fin (2 * n)))).contDiff (n := (1 : ℕ∞ω))).contDiffOn.comp
        hZ1 (fun x _ => Set.mem_univ _)
    have hlast : ContDiffOn ℝ 1 (fun x : (Fin 3 → EuclideanSpace ℝ (Fin n)) ×
        EuclideanSpace ℝ (Fin (2 * n)) =>
          (pairZ e p q (x.1 0, x.1 1)) (Fin.last (2 * n))) (tripleTgt (n := n) p q r) :=
      ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin (2 * n + 1)) (Fin.last (2 * n))).contDiff
        (n := (1 : ℕ∞ω))).contDiffOn.comp hZ1 (fun x _ => Set.mem_univ _)
    refine (hbase.sub (hlast.smul hsnd)).congr fun x hx => ?_
    apply WithLp.ofLp_injective
    funext i
    simp only [projVec_apply]
    simp
    ring
  have h2 : ContDiffOn ℝ 1 (fun x : (Fin 3 → EuclideanSpace ℝ (Fin n)) ×
      EuclideanSpace ℝ (Fin (2 * n)) => projVec x.2 (pairZ e p r (x.1 0, x.1 2)))
      (tripleTgt (n := n) p q r) := by
    have hbase : ContDiffOn ℝ 1 (fun x : (Fin 3 → EuclideanSpace ℝ (Fin n)) ×
        EuclideanSpace ℝ (Fin (2 * n)) =>
          projVec (0 : EuclideanSpace ℝ (Fin (2 * n))) (pairZ e p r (x.1 0, x.1 2)))
        (tripleTgt (n := n) p q r) :=
      ((projVec (0 : EuclideanSpace ℝ (Fin (2 * n)))).contDiff (n := (1 : ℕ∞ω))).contDiffOn.comp
        hZ2 (fun x _ => Set.mem_univ _)
    have hlast : ContDiffOn ℝ 1 (fun x : (Fin 3 → EuclideanSpace ℝ (Fin n)) ×
        EuclideanSpace ℝ (Fin (2 * n)) =>
          (pairZ e p r (x.1 0, x.1 2)) (Fin.last (2 * n))) (tripleTgt (n := n) p q r) :=
      ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin (2 * n + 1)) (Fin.last (2 * n))).contDiff
        (n := (1 : ℕ∞ω))).contDiffOn.comp hZ2 (fun x _ => Set.mem_univ _)
    refine (hbase.sub (hlast.smul hsnd)).congr fun x hx => ?_
    apply WithLp.ofLp_injective
    funext i
    simp only [projVec_apply]
    simp
    ring
  show ContDiffOn ℝ 1 (fun x : (Fin 3 → EuclideanSpace ℝ (Fin n)) ×
      EuclideanSpace ℝ (Fin (2 * n)) =>
      (projVec x.2 (pairZ e p q (x.1 0, x.1 1)), projVec x.2 (pairZ e p r (x.1 0, x.1 2))))
    (tripleTgt (n := n) p q r)
  exact h1.prodMk h2

/-- The manifold points corresponding to a triple of chart parameters are in the chart sources. -/
lemma symm_mem_source_of_mem_target {p : M} {a : EuclideanSpace ℝ (Fin n)}
    (ha : a ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).target) :
    (chartAt (EuclideanSpace ℝ (Fin n)) p).symm a ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source :=
  (chartAt (EuclideanSpace ℝ (Fin n)) p).map_target ha

/-- **The triple parametrisation is `C¹` at every point of `tripleDomTrans`.** -/
lemma contDiffAt_tripleParam (e : M → EuclideanSpace ℝ (Fin (2 * n + 1)))
    (he : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n + 1)))) ((⊤ : ℕ∞) : WithTop ℕ∞) e)
    (p q r : M) (x : (Fin 3 → EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin (2 * n)))
    (hx : x ∈ tripleDomTrans e p q r) :
    ContDiffAt ℝ 1 (tripleParam e p q r) x :=
  (contDiffOn_tripleParam e he p q r).contDiffAt
    (isOpen_tripleTgt.mem_nhds ⟨hx.1.1, hx.1.2.1, hx.1.2.2.1⟩)

end Work.Projection
