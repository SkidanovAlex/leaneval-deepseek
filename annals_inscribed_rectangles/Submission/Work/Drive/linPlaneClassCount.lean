import Mathlib
import Submission.Work.Drive.classTripleCount
import Submission.Work.Drive.linPlaneTripleCount

/-!
# The base case of the ends parity: three linear plane charts have class count one

The ends clause of Hugelmeyer's Lemmas 3–4 needs the mod-`2` degree input `n_{-λ}` odd, i.e. that the
number of triples of class coordinates at which the three rotated class maps agree is **odd**.  The
bordism route (`Work.Drive.even_ncard_classCount_add_of_homotopy`) reduces this to the case in which the
three class maps are the *disk models of linear projective planes*; this file settles that case.

`Work.Drive.ncard_linPlaneTriples_eq_one` (`Submission/Work/Drive/linPlaneTripleCount.lean`) computes the
number of triples at which the three *capping-space* values `diskPlane (linPlaneChart (φ k) c hc)` agree
as `1`.  Since the three charts all sit at the level `c`, equality of capping-space values is equivalent
to equality of the projective classes over the whole square
(`Work.Drive.capping_eq_iff_of_level_eq`), so the *class*-triple count is `1` as well, hence odd.

Also here: the invariance of the class-triple count under a relabelling of the three slots, which is what
lets the bordism step replace the class map of any one of the three planes (the raw statement replaces the
`0`-th slot).
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

set_option linter.style.haveILetI false

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

/-- **Two capping points of equal level are equal iff their projective classes are equal.** -/
lemma capping_eq_iff_of_level_eq {p q : CappingSpace} (h : levelOf p = levelOf q) :
    p = q ↔ (cappingSpaceHomeoProj p).2 = (cappingSpaceHomeoProj q).2 := by
  constructor
  · intro hpq; rw [hpq]
  · intro hpq
    apply cappingSpaceHomeoProj.injective
    refine Prod.ext ?_ ?_
    · show (⟨levelOf p, levelOf_pos p⟩ : Pos) = ⟨levelOf q, levelOf_pos q⟩
      exact Subtype.ext h
    · exact hpq

/-- The level of a folded linear plane chart is its level. -/
lemma level_diskPlane_linPlaneChart (φ : Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c)
    (y : EuclideanSpace ℝ (Fin 2)) :
    levelOf (diskPlane (linPlaneChart φ c hc) y) = c := by
  rw [diskPlane_apply]
  exact level_linPlaneChart φ c hc _

/-- **The base case of the ends parity: three linear plane charts of one level in general position
have class count exactly one** (hence odd). -/
theorem odd_ncard_classCount_linPlaneCharts (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c)
    (h : Module.finrank ℝ ↥(⨅ k : Fin 3, linSub (φ k)) = 1)
    (hgen : ∀ (k : Fin 3) (z : ℂ), ‖z‖ = 1 →
      linPlaneChart (φ k) c hc z ≠ linCommonPt φ c hc h) :
    Odd (classCount (fun k => planeClassMap (diskPlane (linPlaneChart (φ k) c hc)))).ncard := by
  have hcount := ncard_linPlaneTriples_eq_one φ c hc h hgen
  have hset : classCount (fun k => planeClassMap (diskPlane (linPlaneChart (φ k) c hc)))
      = {x : Fin 3 → EuclideanSpace ℝ (Fin 2) |
          (∀ k, x k ∈ Submission.Drive.unitBox 1) ∧
          diskPlane (linPlaneChart (φ 0) c hc) (x 0)
            = diskPlane (linPlaneChart (φ 1) c hc) (x 1) ∧
          diskPlane (linPlaneChart (φ 0) c hc) (x 0)
            = diskPlane (linPlaneChart (φ 2) c hc) (x 2)} := by
    ext x
    simp only [mem_classCount, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hbox, hcls⟩
      refine ⟨hbox, ?_, ?_⟩
      · refine (capping_eq_iff_of_level_eq ?_).mpr ?_
        · rw [level_diskPlane_linPlaneChart, level_diskPlane_linPlaneChart]
        · exact (hcls 1).symm
      · refine (capping_eq_iff_of_level_eq ?_).mpr ?_
        · rw [level_diskPlane_linPlaneChart, level_diskPlane_linPlaneChart]
        · exact (hcls 2).symm
    · rintro ⟨hbox, h01, h02⟩
      refine ⟨hbox, ?_⟩
      intro k
      fin_cases k
      · rfl
      · exact ((capping_eq_iff_of_level_eq (by rw [level_diskPlane_linPlaneChart,
          level_diskPlane_linPlaneChart])).mp h01).symm
      · exact ((capping_eq_iff_of_level_eq (by rw [level_diskPlane_linPlaneChart,
          level_diskPlane_linPlaneChart])).mp h02).symm
  rw [hset, hcount]
  exact ⟨0, rfl⟩

/-- **The class-triple count only depends on the three maps, not on the order in which the slots are
listed.**  The relabelling `y ↦ y ∘ σ⁻¹` is a bijection of the triples of parameters. -/
theorem ncard_classCount_perm (σ : Equiv.Perm (Fin 3))
    (f : Fin 3 → EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)) :
    (classCount (fun k => f (σ k))).ncard = (classCount f).ncard := by
  refine Set.ncard_congr (fun y _ => fun k => y (σ.symm k)) ?_ ?_ ?_
  · rintro y ⟨hbox, hcls⟩
    refine ⟨fun k => hbox _, fun k => ?_⟩
    have h1 := hcls (σ.symm k)
    simp only [Function.comp_apply, Equiv.apply_symm_apply] at h1
    have h2 := hcls (σ.symm 0)
    simp only [Function.comp_apply, Equiv.apply_symm_apply] at h2
    exact h1.trans h2.symm
  · intro y z hy hz h
    funext k
    have hk := congrFun h (σ k)
    simpa only [Equiv.symm_apply_apply] using hk
  · intro z hz
    refine ⟨fun k => z (σ k), ?_, ?_⟩
    · refine ⟨fun k => hz.1 _, fun k => ?_⟩
      show f (σ k) (z (σ k)) = f (σ 0) (z (σ 0))
      exact (hz.2 (σ k)).trans (hz.2 (σ 0)).symm
    · funext k
      simp

end

end Work.Drive
