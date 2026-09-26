import Mathlib
import Submission.Work.Drive.Mono.CylRegionDefs
import Submission.Work.CoreTopology.Disk
import Submission.Work.InnermostDisk.Defs
import Submission.Work.Drive.Mono.cylRegion_e_mem_interior
import Submission.Work.Drive.Mono.isEmbeddedSphere_of_doubleDisc
import Submission.Work.Drive.Mono.WindowCase.exists_cupParam
import Submission.Work.Drive.Mono.WindowCase.frontier_hypograph_eq

/-!
# The frontier of the solid over a plane disc is an embedded sphere

`Work.Drive.Mono.WindowCase.tls_hypograph_sphere`: if `K ⊆ ℝ²` is a plane disc (the image of the
closed unit disc under an injective continuous map whose boundary circle maps onto `frontier K`)
and `g : K → ℝ` is continuous, nonnegative, and strictly positive in `interior K`, then the
frontier of the solid

`H = {P : ℝ³ | cproj P ∈ K ∧ 0 ≤ clast P ≤ g (cproj P)}`

is an embedded `2`-sphere.

## Route

`frontier H` is the union of the two discs

* the **cup** `E = {(x,0) | x ∈ K} ∪ {(x,y) | x ∈ frontier K, 0 ≤ y ≤ g x}`
  (`exists_cupParam`), and
* the **top graph** `T = {(x,g x) | x ∈ K}`,

glued along their common boundary circle `{(x,g x) | x ∈ frontier K}`, with disjoint open-disc
images.  `isEmbeddedSphere_of_doubleDisc` then yields the sphere.

The cup is *not* parametrised by the naive collar-aligned map: at a point `x ∈ frontier K` with
`g x = 0` the whole collar fibre collapses, so that map is not injective.  `exists_cupParam`
constructs the collapse-aware variant instead.
-/

namespace Work.Drive.Mono.WindowCase

open LeanEval.KnotTheory.PardonDistortion Set

noncomputable section

/-! ## Elementary facts about a plane disc parametrised by the closed unit disc -/

section DiscFacts

variable {K : Set (EuclideanSpace ℝ (Fin 2))}

theorem tls_isCompact_of_discParam {e : C(Metric.closedBall (0 : ℂ) 1, EuclideanSpace ℝ (Fin 2))}
    (he_range : Set.range e = K) : IsCompact K := by
  rw [← he_range]
  exact isCompact_range e.continuous

theorem tls_mem_K_of_discParam {e : C(Metric.closedBall (0 : ℂ) 1, EuclideanSpace ℝ (Fin 2))}
    (he_range : Set.range e = K) (z : Metric.closedBall (0 : ℂ) 1) : e z ∈ K := by
  rw [← he_range]
  exact Set.mem_range_self z

theorem tls_norm_le_one (z : Metric.closedBall (0 : ℂ) 1) : ‖(z : ℂ)‖ ≤ 1 := by
  have h := z.2
  rwa [Metric.mem_closedBall, dist_zero_right] at h

/-- A point of the disc parametrising `K` lies on the frontier of `K` exactly at the unit circle. -/
theorem tls_mem_frontier_iff_norm_eq_one {e : C(Metric.closedBall (0 : ℂ) 1, EuclideanSpace ℝ (Fin 2))}
    (he_inj : Function.Injective e) (he_range : Set.range e = K)
    (he_bdry : Set.range (fun θ : ℝ => e (Work.CoreTopology.circlePoint θ)) = frontier K)
    (z : Metric.closedBall (0 : ℂ) 1) : e z ∈ frontier K ↔ ‖(z : ℂ)‖ = 1 := by
  have hKc : IsCompact K := tls_isCompact_of_discParam he_range
  have hzK : e z ∈ K := tls_mem_K_of_discParam he_range z
  have hint := Work.Drive.Mono.cylRegion_e_mem_interior he_inj he_range he_bdry z
  have hzle := tls_norm_le_one z
  rw [show frontier K = K \ interior K by rw [frontier, hKc.isClosed.closure_eq]]
  constructor
  · rintro ⟨-, hni⟩
    exact le_antisymm hzle (not_lt.mp fun hlt => hni (hint.mpr hlt))
  · intro hz
    refine ⟨hzK, fun hmem => ?_⟩
    have hlt : ‖(z : ℂ)‖ < 1 := hint.mp hmem
    rw [hz] at hlt
    exact lt_irrefl _ hlt

/-- The open disc of `ℂ` is dense in the closed disc. -/
theorem tls_dense_setOf_norm_lt_one :
    closure {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ < 1} = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro z
  rcases lt_or_eq_of_le (tls_norm_le_one z) with hlt | heq
  · exact subset_closure hlt
  · rw [Metric.mem_closure_iff]
    intro ε hε
    set δ : ℝ := min (ε / 2) (1 / 2) with hδ
    have hδpos : 0 < δ := by rw [hδ]; exact lt_min (by linarith) (by norm_num)
    have hδle : δ ≤ 1 / 2 := by rw [hδ]; exact min_le_right _ _
    have hδle' : δ ≤ ε / 2 := by rw [hδ]; exact min_le_left _ _
    have hnn : 0 ≤ 1 - δ := by linarith
    have hball : (1 - δ) • (z : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg hnn, heq,
        mul_one]
      linarith
    have hnorm : ‖(1 - δ) • (z : ℂ)‖ < 1 := by
      rw [norm_smul, Real.norm_of_nonneg hnn, heq, mul_one]
      linarith
    refine ⟨⟨(1 - δ) • (z : ℂ), hball⟩, hnorm, ?_⟩
    have hd : dist z (⟨(1 - δ) • (z : ℂ), hball⟩ : Metric.closedBall (0 : ℂ) 1) < ε := by
      rw [Subtype.dist_eq, dist_eq_norm]
      change ‖(z : ℂ) - (1 - δ) • (z : ℂ)‖ < ε
      rw [show (z : ℂ) - (1 - δ) • (z : ℂ) = δ • (z : ℂ) by module, norm_smul,
        Real.norm_of_nonneg hδpos.le, heq, mul_one]
      linarith
    exact hd

/-- The closure of the interior of a plane disc is the disc. -/
theorem tls_closure_interior_eq_of_discParam
    {e : C(Metric.closedBall (0 : ℂ) 1, EuclideanSpace ℝ (Fin 2))}
    (he_inj : Function.Injective e) (he_range : Set.range e = K)
    (he_bdry : Set.range (fun θ : ℝ => e (Work.CoreTopology.circlePoint θ)) = frontier K) :
    closure (interior K) = K := by
  have hKc : IsCompact K := tls_isCompact_of_discParam he_range
  have hInt : interior K = e '' {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ < 1} := by
    ext x
    constructor
    · intro hx
      obtain ⟨z, rfl⟩ := Set.mem_range.mp (show x ∈ Set.range e by
        rw [he_range]; exact interior_subset hx)
      exact ⟨z, (Work.Drive.Mono.cylRegion_e_mem_interior he_inj he_range he_bdry z).mp hx, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact (Work.Drive.Mono.cylRegion_e_mem_interior he_inj he_range he_bdry z).mpr hz
  rw [hInt]
  refine Subset.antisymm ?_ ?_
  · refine (hKc.isClosed.closure_subset_iff).mpr ?_
    rintro x ⟨z, -, rfl⟩
    exact tls_mem_K_of_discParam he_range z
  · have h := image_closure_subset_closure_image e.continuous
      (s := {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ < 1})
    rw [tls_dense_setOf_norm_lt_one, Set.image_univ, he_range] at h
    exact h

end DiscFacts

/-- The frontier of the solid over a plane disc is an embedded sphere. -/
theorem tls_hypograph_sphere
    {W : Set (EuclideanSpace ℝ (Fin 2))} (hWc : Convex ℝ W) (hWk : IsCompact W)
    (hWi : (interior W).Nonempty)
    {a' h' lam : ℝ} (hh' : 0 < h')
    {K : Set (EuclideanSpace ℝ (Fin 2))}
    (hKdisc : ∃ e : C(Metric.closedBall (0 : ℂ) 1, EuclideanSpace ℝ (Fin 2)),
      Function.Injective e ∧ Set.range e = K ∧
      Set.range (fun θ : ℝ => e (Work.CoreTopology.circlePoint θ)) = frontier K)
    (hKcl : K = closure (interior W ∩
      {X : EuclideanSpace ℝ (Fin 2) | h' < |X 0 - a'| ∨ lam ≤ X 1}))
    {g : EuclideanSpace ℝ (Fin 2) → ℝ} (hgc : ContinuousOn g K) (hg : ConcaveOn ℝ K g)
    (hg0 : ∀ x ∈ K, 0 ≤ g x) (hgpos : ∀ x ∈ interior K, 0 < g x) :
    Work.InnermostDisk.IsEmbeddedSphere
      (frontier {P : EuclideanSpace ℝ (Fin 3) | Work.Drive.Mono.cproj P ∈ K ∧
        0 ≤ Work.Drive.Mono.clast P ∧
        Work.Drive.Mono.clast P ≤ g (Work.Drive.Mono.cproj P)}) := by
  -- the plane disc and its elementary properties
  obtain ⟨e, he_inj, he_range, he_bdry⟩ := hKdisc
  have hKc : IsCompact K := tls_isCompact_of_discParam he_range
  have hKcl' : closure (interior K) = K :=
    tls_closure_interior_eq_of_discParam he_inj he_range he_bdry
  -- the cup `{cproj ∈ K, clast = 0} ∪ {cproj ∈ frontier K, 0 ≤ clast ≤ g}`
  obtain ⟨eC, heC_inj, heC_range, heC_bdry⟩ :=
    exists_cupParam e he_inj he_range he_bdry hgc hg0
  -- the graph of `g` over `K`
  have hgK : ∀ z : Metric.closedBall (0 : ℂ) 1, e z ∈ K := fun z => tls_mem_K_of_discParam he_range z
  have hgcont : Continuous fun z : Metric.closedBall (0 : ℂ) 1 => g (e z) :=
    hgc.comp_continuous e.continuous hgK
  let eT : C(Metric.closedBall (0 : ℂ) 1, EuclideanSpace ℝ (Fin 3)) :=
    ⟨fun z => Work.Drive.Mono.cmk (e z) (g (e z)),
     Work.Drive.Mono.continuous_cmk.comp (e.continuous.prodMk hgcont)⟩
  have heT_apply : ∀ z, eT z = Work.Drive.Mono.cmk (e z) (g (e z)) := fun z => rfl
  have heT_inj : Function.Injective eT := by
    intro z w h
    have h1 : e z = e w := ((Work.Drive.Mono.cmk_eq_cmk_iff _ _ _ _).mp h).1
    exact he_inj h1
  have heT_range : Set.range eT = {P : EuclideanSpace ℝ (Fin 3) |
      Work.Drive.Mono.cproj P ∈ K ∧
      Work.Drive.Mono.clast P = g (Work.Drive.Mono.cproj P)} := by
    ext P
    constructor
    · rintro ⟨z, rfl⟩
      constructor
      · rw [heT_apply, Work.Drive.Mono.cproj_cmk]; exact tls_mem_K_of_discParam he_range z
      · rw [heT_apply, Work.Drive.Mono.clast_cmk, Work.Drive.Mono.cproj_cmk]
    · rintro ⟨hPK, hPg⟩
      obtain ⟨z, hz⟩ := Set.mem_range.mp (by rw [he_range]; exact hPK)
      refine ⟨z, ?_⟩
      rw [heT_apply, hz, ← hPg, Work.Drive.Mono.cmk_cproj_clast]
  -- the two discs agree on the boundary circle
  have hbd : ∀ θ : ℝ, eC (Work.CoreTopology.circlePoint θ) =
      eT (Work.CoreTopology.circlePoint θ) := by
    intro θ
    rw [heT_apply]
    exact heC_bdry θ
  -- and their open discs are disjoint
  have hint : ∀ z w : Metric.closedBall (0 : ℂ) 1, ‖(z : ℂ)‖ < 1 → ‖(w : ℂ)‖ < 1 →
      eC z = eT w → False := by
    intro z w hz hw heq
    have hmem : eT w ∈ Set.range eC := ⟨z, heq⟩
    rw [heC_range] at hmem
    have hwT : eT w = Work.Drive.Mono.cmk (e w) (g (e w)) := heT_apply w
    have hcproj : Work.Drive.Mono.cproj (eT w) ∈ interior K := by
      rw [hwT, Work.Drive.Mono.cproj_cmk]
      exact (Work.Drive.Mono.cylRegion_e_mem_interior he_inj he_range he_bdry w).mpr hw
    have hclast : Work.Drive.Mono.clast (eT w) = g (Work.Drive.Mono.cproj (eT w)) := by
      rw [hwT, Work.Drive.Mono.cproj_cmk, Work.Drive.Mono.clast_cmk]
    have hpos : 0 < Work.Drive.Mono.clast (eT w) := by
      rw [hclast]; exact hgpos _ hcproj
    rcases hmem with ⟨-, hcl⟩ | ⟨hfr, -, -⟩
    · rw [hcl] at hpos; exact lt_irrefl _ hpos
    · exact hfr.2 hcproj
  have hsphere := Work.Drive.Mono.isEmbeddedSphere_of_doubleDisc eC eT heC_inj heT_inj hbd hint
  have hset : Set.range eC ∪ Set.range eT = frontier {P : EuclideanSpace ℝ (Fin 3) |
      Work.Drive.Mono.cproj P ∈ K ∧ 0 ≤ Work.Drive.Mono.clast P ∧
      Work.Drive.Mono.clast P ≤ g (Work.Drive.Mono.cproj P)} := by
    rw [heC_range, heT_range, frontier_hypograph_eq hKc hKcl' hgc hg0 hgpos]
    ext P
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    tauto
  rw [hset] at hsphere
  exact hsphere

end

end Work.Drive.Mono.WindowCase
