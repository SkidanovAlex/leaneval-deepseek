import Mathlib
import Submission.Work.Drive.Mono.CylRegionDefs
import Submission.Work.Drive.Mono.WindowCase.exists_cupParam
import Submission.Work.Drive.Mono.WindowCase.tls_hypograph_sphere
import Submission.Work.Drive.Mono.FiberModel.hypograph_sphere
import Submission.Work.InnermostDisk.isEmbeddedSphere_image_homeomorph
import Submission.Work.CoreTopology.Disk
import Submission.Work.Drive.Mono.WindowCase.frontierStrictOverEq
import Submission.Work.Drive.Mono.FiberModel.interior_cCyl_of_continuousOn

/-!
# The frontier of the solid between two graphs over a plane disc

`solidOverDiscSphere`: if `K ⊆ ℝ²` is a plane disc and `α ≤ β` are continuous on `K` with
`α < β` on `interior K`, then the frontier of the solid

`cCyl K α β = {p : ℝ³ | cproj p ∈ K ∧ α (cproj p) ≤ clast p ∧ clast p ≤ β (cproj p)}`

is an embedded `2`-sphere.

## Route

The frontier splits into three pieces (`frontier_cCyl_between`): the bottom graph
`{clast = α}`, the top graph `{clast = β}` and the side wall over `frontier K`.

* the **cup** `{clast = α} ∪ wall` is obtained from the cup of the *nonnegative* height
  `β - α` (whose parametrisation by the disc is `exists_cupParam`, valid for an arbitrary
  continuous nonnegative height -- no concavity) by the "vertical shear"
  `(x,y) ↦ (x, y + α x)` over `K`; the shear preserves injectivity because it is injective
  over `K`;
* the **top graph** is the graph of `β` over `K`;

the two discs are glued along the common top rim `{clast = β, cproj ∈ frontier K}` and meet only
there (this is where `α < β` on `interior K` is used), so `isEmbeddedSphere_of_doubleDisc`
applies.
-/

namespace Work.Drive.Mono.WindowCase

open LeanEval.KnotTheory.PardonDistortion Set

noncomputable section

local notation "𝔻" => Metric.closedBall (0 : ℂ) 1

/-! ## 1. The frontier of the solid between two graphs -/

/-- **The frontier of the solid between two graphs.**  For `K` compact and `α ≤ β` continuous on
`K`, the frontier of `cCyl K α β` is the union of the bottom graph, the top graph and the side wall
over `frontier K`.  (No strictness `α < β` is needed: the description of `interior (cCyl K α β)`
as `cInt K α β` holds for arbitrary continuous `α`, `β` on `K`.) -/
theorem frontier_cCyl_between {K : Set (EuclideanSpace ℝ (Fin 2))}
    {α β : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hKc : IsCompact K) (hα : ContinuousOn α K) (hβ : ContinuousOn β K)
    (hαβ : ∀ x ∈ K, α x ≤ β x) :
    frontier (Work.Drive.Mono.cCyl K α β) =
      {p : R3 | Work.Drive.Mono.cproj p ∈ K ∧
          Work.Drive.Mono.clast p = α (Work.Drive.Mono.cproj p)} ∪
      {p : R3 | Work.Drive.Mono.cproj p ∈ K ∧
          Work.Drive.Mono.clast p = β (Work.Drive.Mono.cproj p)} ∪
      {p : R3 | Work.Drive.Mono.cproj p ∈ frontier K ∧
          α (Work.Drive.Mono.cproj p) ≤ Work.Drive.Mono.clast p ∧
          Work.Drive.Mono.clast p ≤ β (Work.Drive.Mono.cproj p)} := by
  have hclosed : IsClosed (Work.Drive.Mono.cCyl K α β) := cCyl_isClosed hKc.isClosed hα hβ
  have hfront : frontier (Work.Drive.Mono.cCyl K α β)
      = Work.Drive.Mono.cCyl K α β \ Work.Drive.Mono.cInt K α β := by
    rw [frontier, hclosed.closure_eq,
      Work.Drive.Mono.FiberModel.interior_cCyl_of_continuousOn hα hβ]
  rw [hfront]
  ext p
  rw [Set.mem_sdiff, Work.Drive.Mono.cCyl, Work.Drive.Mono.cInt, Set.mem_ofPred_eq,
    Set.mem_union]
  constructor
  · rintro ⟨⟨hxK, hlo, hhi⟩, hni⟩
    by_cases hxi : Work.Drive.Mono.cproj p ∈ interior K
    · have hcon : ¬ (α (Work.Drive.Mono.cproj p) < Work.Drive.Mono.clast p ∧
          Work.Drive.Mono.clast p < β (Work.Drive.Mono.cproj p)) := by
        intro h; exact hni ⟨hxi, h⟩
      rcases not_and_or.mp hcon with h | h
      · exact Or.inl (Or.inl ⟨hxK, le_antisymm (not_lt.mp h) hlo⟩)
      · exact Or.inl (Or.inr ⟨hxK, le_antisymm hhi (not_lt.mp h)⟩)
    · refine Or.inr ⟨?_, hlo, hhi⟩
      rw [frontier, hKc.isClosed.closure_eq, Set.mem_sdiff]
      exact ⟨hxK, hxi⟩
  · rintro ((⟨hxK, heq⟩ | ⟨hxK, heq⟩) | ⟨hxf, hlo, hhi⟩)
    · refine ⟨⟨hxK, ?_, ?_⟩, ?_⟩
      · rw [heq]
      · rw [heq]; exact hαβ _ hxK
      · rintro ⟨-, hlt, -⟩
        rw [heq] at hlt
        exact absurd hlt (lt_irrefl _)
    · refine ⟨⟨hxK, ?_, ?_⟩, ?_⟩
      · rw [heq]; exact hαβ _ hxK
      · rw [heq]
      · rintro ⟨-, -, hlt⟩
        rw [heq] at hlt
        exact absurd hlt (lt_irrefl _)
    · refine ⟨⟨?_, hlo, hhi⟩, ?_⟩
      · rw [frontier, hKc.isClosed.closure_eq, Set.mem_sdiff] at hxf
        exact hxf.1
      · rintro ⟨hint, -, -⟩
        rw [frontier, hKc.isClosed.closure_eq, Set.mem_sdiff] at hxf
        exact hxf.2 hint

/-! ## 2. The two discs: the cup (sheared) and the top graph -/

/-- **The frontier of the solid over a plane disc is a sphere.**  If `K ⊆ ℝ²` is a topological disc
(the image of the closed unit disc under an injective continuous map whose boundary circle maps onto
`frontier K`) and `α ≤ β` are continuous on `K` with `α < β` on `interior K`, then the frontier of
the solid between the two graphs over `K` is an embedded `2`-sphere. -/
theorem solidOverDiscSphere
    {K : Set (EuclideanSpace ℝ (Fin 2))} {α β : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hKdisc : ∃ e : C(Metric.closedBall (0 : ℂ) 1, EuclideanSpace ℝ (Fin 2)),
      Function.Injective e ∧ Set.range e = K ∧
      Set.range (fun θ : ℝ => e (Work.CoreTopology.circlePoint θ)) = frontier K)
    (hα : ContinuousOn α K) (hβ : ContinuousOn β K)
    (hαβ : ∀ x ∈ K, α x ≤ β x) (hpos : ∀ x ∈ interior K, α x < β x) :
    Work.InnermostDisk.IsEmbeddedSphere
      (frontier {p : EuclideanSpace ℝ (Fin 3) |
        Work.Drive.Mono.cproj p ∈ K ∧ α (Work.Drive.Mono.cproj p) ≤ Work.Drive.Mono.clast p ∧
        Work.Drive.Mono.clast p ≤ β (Work.Drive.Mono.cproj p)}) := by
  classical
  obtain ⟨e, he_inj, he_range, he_bdry⟩ := hKdisc
  have hKc : IsCompact K := tls_isCompact_of_discParam he_range
  -- the height of the cup
  set hgt : EuclideanSpace ℝ (Fin 2) → ℝ := fun x => β x - α x with hgtdef
  have hgc : ContinuousOn hgt K := hβ.sub hα
  have hg0 : ∀ x ∈ K, 0 ≤ hgt x := fun x hx => by
    rw [hgtdef]; exact sub_nonneg.mpr (hαβ x hx)
  -- the collapse-aware parametrisation of the cup over `K` of height `hgt`
  obtain ⟨E, hEinj, hErange, hEbd⟩ := exists_cupParam e he_inj he_range he_bdry hgc hg0
  have hprojE : ∀ z : 𝔻, Work.Drive.Mono.cproj (E z) ∈ K := by
    intro z
    have hz : E z ∈ Set.range ⇑E := Set.mem_range_self z
    rw [hErange] at hz
    rcases hz with hz | hz
    · exact hz.1
    · have h : Work.Drive.Mono.cproj (E z) ∈ frontier K := hz.1
      rw [frontier, hKc.isClosed.closure_eq, Set.mem_sdiff] at h
      exact h.1
  have hαE : Continuous fun z : 𝔻 => α (Work.Drive.Mono.cproj (E z)) :=
    hα.comp_continuous (Work.Drive.Mono.continuous_cproj.comp E.continuous) hprojE
  -- the sheared cup
  set A : C(𝔻, R3) :=
    ⟨fun z => Work.Drive.Mono.cmk (Work.Drive.Mono.cproj (E z))
        (Work.Drive.Mono.clast (E z) + α (Work.Drive.Mono.cproj (E z))),
      Work.Drive.Mono.continuous_cmk.comp
        ((Work.Drive.Mono.continuous_cproj.comp E.continuous).prodMk
          ((Work.Drive.Mono.continuous_clast.comp E.continuous).add hαE))⟩ with hAdef
  have hAapply : ∀ z : 𝔻, A z = Work.Drive.Mono.cmk (Work.Drive.Mono.cproj (E z))
      (Work.Drive.Mono.clast (E z) + α (Work.Drive.Mono.cproj (E z))) := fun z => rfl
  -- the top graph of `β` over `K`
  set B : C(𝔻, R3) :=
    ⟨fun z => Work.Drive.Mono.cmk (e z) (β (e z)),
      Work.Drive.Mono.continuous_cmk.comp (e.continuous.prodMk
        (hβ.comp_continuous e.continuous (fun z => by
          rw [← he_range]; exact Set.mem_range_self z)))⟩ with hBdef
  have hBapply : ∀ z : 𝔻, B z = Work.Drive.Mono.cmk (e z) (β (e z)) := fun z => rfl
  -- injectivity
  have hAinj : Function.Injective ⇑A := by
    intro z z' h
    have h1 : Work.Drive.Mono.cproj (E z) = Work.Drive.Mono.cproj (E z') := by
      have hh := congrArg Work.Drive.Mono.cproj h
      simpa only [hAapply, Work.Drive.Mono.cproj_cmk] using hh
    have h2 : Work.Drive.Mono.clast (E z) = Work.Drive.Mono.clast (E z') := by
      have hh := congrArg Work.Drive.Mono.clast h
      simp only [hAapply, Work.Drive.Mono.clast_cmk] at hh
      rw [h1] at hh
      exact add_right_cancel hh
    exact hEinj (by rw [← Work.Drive.Mono.cmk_cproj_clast (E z),
      ← Work.Drive.Mono.cmk_cproj_clast (E z'), h1, h2])
  have hBinj : Function.Injective ⇑B := fun z z' h => he_inj (by
    have hh := congrArg Work.Drive.Mono.cproj h
    simpa only [hBapply, Work.Drive.Mono.cproj_cmk] using hh)
  -- the range of the sheared cup
  have hArange : Set.range ⇑A =
      {p : R3 | Work.Drive.Mono.cproj p ∈ K ∧
          Work.Drive.Mono.clast p = α (Work.Drive.Mono.cproj p)} ∪
      {p : R3 | Work.Drive.Mono.cproj p ∈ frontier K ∧
          α (Work.Drive.Mono.cproj p) ≤ Work.Drive.Mono.clast p ∧
          Work.Drive.Mono.clast p ≤ β (Work.Drive.Mono.cproj p)} := by
    ext p
    constructor
    · rintro ⟨z, rfl⟩
      have hz : E z ∈ Set.range ⇑E := Set.mem_range_self z
      rw [hErange] at hz
      rcases hz with hz | hz
      · obtain ⟨hxK, hcl⟩ := hz
        refine Or.inl ⟨?_, ?_⟩
        · simpa only [hAapply, Work.Drive.Mono.cproj_cmk] using hxK
        · rw [hAapply]
          simp only [Work.Drive.Mono.cproj_cmk, Work.Drive.Mono.clast_cmk, hcl, zero_add]
      · obtain ⟨hxf, h0, hle⟩ := hz
        refine Or.inr ⟨?_, ?_, ?_⟩
        · simpa only [hAapply, Work.Drive.Mono.cproj_cmk] using hxf
        · rw [hAapply]
          simp only [Work.Drive.Mono.cproj_cmk, Work.Drive.Mono.clast_cmk]
          linarith
        · rw [hAapply]
          simp only [Work.Drive.Mono.cproj_cmk, Work.Drive.Mono.clast_cmk]
          have hh : hgt (Work.Drive.Mono.cproj (E z)) = β (Work.Drive.Mono.cproj (E z))
              - α (Work.Drive.Mono.cproj (E z)) := by rw [hgtdef]
          rw [hh] at hle
          linarith
    · rintro (⟨hxK, hcl⟩ | ⟨hxf, hlo, hhi⟩)
      · have hbot : Work.Drive.Mono.cmk (Work.Drive.Mono.cproj p) 0 ∈ Set.range ⇑E := by
          rw [hErange]; refine Or.inl ⟨?_, rfl⟩
          simpa using hxK
        obtain ⟨z, hz⟩ := hbot
        refine ⟨z, ?_⟩
        rw [hAapply, hz]
        simp only [Work.Drive.Mono.cproj_cmk, Work.Drive.Mono.clast_cmk, zero_add]
        rw [← hcl]
        exact Work.Drive.Mono.cmk_cproj_clast p
      · have hq : Work.Drive.Mono.cmk (Work.Drive.Mono.cproj p)
            (Work.Drive.Mono.clast p - α (Work.Drive.Mono.cproj p)) ∈ Set.range ⇑E := by
          rw [hErange]; refine Or.inr ⟨?_, ?_, ?_⟩
          · simpa using hxf
          · rw [Work.Drive.Mono.clast_cmk]; linarith
          · rw [Work.Drive.Mono.clast_cmk, Work.Drive.Mono.cproj_cmk]
            have hh : hgt (Work.Drive.Mono.cproj p) = β (Work.Drive.Mono.cproj p)
                - α (Work.Drive.Mono.cproj p) := by rw [hgtdef]
            rw [hh]; linarith
        obtain ⟨z, hz⟩ := hq
        refine ⟨z, ?_⟩
        rw [hAapply, hz]
        simp only [Work.Drive.Mono.cproj_cmk, Work.Drive.Mono.clast_cmk]
        rw [sub_add_cancel]
        exact Work.Drive.Mono.cmk_cproj_clast p
  -- the range of the top graph
  have hBrange : Set.range ⇑B = {p : R3 | Work.Drive.Mono.cproj p ∈ K ∧
      Work.Drive.Mono.clast p = β (Work.Drive.Mono.cproj p)} := by
    ext p
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [hBapply]; simp only [Work.Drive.Mono.cproj_cmk]
        rw [← he_range]; exact Set.mem_range_self z
      · rw [hBapply]; simp only [Work.Drive.Mono.clast_cmk, Work.Drive.Mono.cproj_cmk]
    · rintro ⟨hxK, hcl⟩
      have hxr : Work.Drive.Mono.cproj p ∈ Set.range ⇑e := by rw [he_range]; exact hxK
      obtain ⟨z, hz⟩ := hxr
      refine ⟨z, ?_⟩
      rw [hBapply, hz]
      rw [← hcl]
      exact Work.Drive.Mono.cmk_cproj_clast p
  -- the two discs agree on the boundary circle
  have hbd : ∀ θ : ℝ, A (Work.CoreTopology.circlePoint θ) = B (Work.CoreTopology.circlePoint θ) := by
    intro θ
    rw [hAapply, hBapply, hEbd θ]
    simp only [Work.Drive.Mono.cproj_cmk, Work.Drive.Mono.clast_cmk]
    have hh : hgt (e (Work.CoreTopology.circlePoint θ)) = β (e (Work.CoreTopology.circlePoint θ))
        - α (e (Work.CoreTopology.circlePoint θ)) := by rw [hgtdef]
    rw [hh]
    congr 1
    ring
  -- the open discs meet only in the boundary
  have hint : ∀ z w : 𝔻, ‖(z : ℂ)‖ < 1 → ‖(w : ℂ)‖ < 1 → A z = B w → False := by
    intro z w hz hw heq
    have hwe : e w ∈ interior K :=
      (Work.Drive.Mono.cylRegion_e_mem_interior he_inj he_range he_bdry w).mpr hw
    have hcproj : Work.Drive.Mono.cproj (A z) = e w := by
      have hh := congrArg Work.Drive.Mono.cproj heq
      simpa only [hAapply, hBapply, Work.Drive.Mono.cproj_cmk] using hh
    have hclast : Work.Drive.Mono.clast (A z) = β (e w) := by
      have hh := congrArg Work.Drive.Mono.clast heq
      simpa only [hAapply, hBapply, Work.Drive.Mono.clast_cmk] using hh
    have hAz : A z ∈ Set.range ⇑A := Set.mem_range_self z
    rw [hArange] at hAz
    rcases hAz with ⟨-, heqα⟩ | ⟨hxf, -, -⟩
    · have h1 : β (e w) = α (e w) := by
        rw [← hclast, heqα, hcproj]
      exact (ne_of_gt (hpos (e w) hwe)) h1
    · have h1 : e w ∈ frontier K := by rw [← hcproj]; exact hxf
      rw [frontier, hKc.isClosed.closure_eq, Set.mem_sdiff] at h1
      exact h1.2 hwe
  -- assembly
  have hsphere : Work.InnermostDisk.IsEmbeddedSphere (Set.range ⇑A ∪ Set.range ⇑B) :=
    Work.Drive.Mono.isEmbeddedSphere_of_doubleDisc A B hAinj hBinj hbd hint
  have hfr : frontier (Work.Drive.Mono.cCyl K α β) = Set.range ⇑A ∪ Set.range ⇑B := by
    rw [frontier_cCyl_between hKc hα hβ hαβ, hArange, hBrange]
    ext p
    simp only [Set.mem_union]
    tauto
  show Work.InnermostDisk.IsEmbeddedSphere (frontier (Work.Drive.Mono.cCyl K α β))
  rw [hfr]
  exact hsphere

end

end Work.Drive.Mono.WindowCase
