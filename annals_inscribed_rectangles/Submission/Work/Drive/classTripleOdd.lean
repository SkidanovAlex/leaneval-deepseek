import Mathlib
import Submission.Work.Drive.even_ncard_classCount_add_of_homotopy
import Submission.Work.Drive.linPlaneClassCount
import Submission.Work.Drive.odd_sum_bottomBdryMeet_of_classTriple

/-!
# The ends parity of the class-triple count

The ends clause of Hugelmeyer's Lemmas 3–4 needs the mod-`2` degree input `n_{-λ}`, i.e. the number of
triples of class coordinates at which the three rotated class maps of the design agree, to be **odd**
(`Submission/Work/Drive/CLASS_TRIPLE_REGULAR_DESIGN.md` §7).  This file assembles it from

* the **bordism invariance** of the class-triple count
  (`Work.Drive.even_ncard_classCount_add_of_homotopy`): a homotopy of one of the three class maps does
  not change the parity of the count;
* the **base case** (`Work.Drive.odd_ncard_classCount_linPlaneCharts`): three disk models of linear
  projective planes of one level, in general position, have class count exactly one.

The input is therefore a *linearisation*: for each of the three planes a homotopy, through class maps of
the square, from the class map of the plane to the disk model of a linear projective plane, together
with the transversality data (`Meet3Hyp`, the `hV`/face conditions of the counting engine's encoding)
that pin the count to the two ends of the homotopy.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

/-- `Odd` of a sum of two odds is even; here in the form used by the assembly: from `Even (a + b)` and
`Odd a` conclude `Odd b`. -/
lemma odd_of_odd_add_even {a b : ℕ} (hab : Even (a + b)) (ha : Odd a) : Odd b := by
  rcases ha with ⟨k, hk⟩
  rcases hab with ⟨m, hm⟩
  exact ⟨m - k - 1, by omega⟩

/-- **A set whose `ncard` is odd is finite.**  (`Set.ncard` is `0` on infinite sets, and `0` is not odd;
this makes the consumer's finiteness hypothesis `(classTripleSet P).Finite` free from the parity.) -/
lemma finite_of_odd_ncard {α : Type*} {s : Set α} (h : Odd s.ncard) : s.Finite := by
  by_contra hcon
  have h0 : s.ncard = 0 := (Set.not_finite.mp hcon).ncard
  rw [h0] at h
  obtain ⟨k, hk⟩ := h
  omega

/-- **The linearisation data of the ends parity.**  For the design's triple `P` of plane presentations
this is the paper's standing hypothesis "`[P k]` generates `H₂(ℝP³; ℤ/2)`" in the form in which the
bordism engine consumes it:

* a triple of *linear* plane charts `φ k` of one common level `c`, in general position (`hrank`) with
  the common point of the three projective planes off the boundary circle of every chart (`hgen`) —
  the data supplied by `Work.Drive.exists_linPlaneCharts_hgen`;
* a homotopy `H k` from the class map of `P k` (time `0`) to the disk model of the `k`-th linear plane
  (time `1`), through class maps of the square;
* the transversality data of the `3 + 2 + 2` encoding at a common encoding time `c₀ ∈ (0,1)`.

The last clause is the only non-homotopy input; it is the analogue, for the encoded chains, of the
engine's `Meet3Hyp` for the clamped sweeps (`Work.Drive.meet3Hyp_of_classTripleRegular`). -/
def HasClassLinearization
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) (Projectivization ℝ (Eucl 3) × ℝ)]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (Projectivization ℝ (Eucl 3) × ℝ)]
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace) : Prop :=
  ∃ (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c)
    (hrank : Module.finrank ℝ ↥(⨅ k : Fin 3, linSub (φ k)) = 1)
    (hgen : ∀ (k : Fin 3) (z : ℂ), ‖z‖ = 1 →
      linPlaneChart (φ k) c hc z ≠ linCommonPt φ c hc hrank)
    (H : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (c₀ : ℝ) (hc₀0 : 0 < c₀) (hc₀1 : c₀ < 1),
    (∀ k, (fun y => H k (0, y)) = planeClassMap (P k)) ∧
    (∀ k, (fun y => H k (1, y)) = planeClassMap (diskPlane (linPlaneChart (φ k) c hc))) ∧
    Meet3Hyp (Projectivization ℝ (Eucl 3) × ℝ)
      (encodedChains (fun x => H 0 (x 2, pt2 (x 0) (x 1)))
        (planeClassMap (P 1)) (planeClassMap (P 2)) c₀) ∧
    Meet3Hyp (Projectivization ℝ (Eucl 3) × ℝ)
      (encodedChains (fun x => H 1 (x 2, pt2 (x 0) (x 1)))
        (planeClassMap (diskPlane (linPlaneChart (φ 0) c hc))) (planeClassMap (P 2)) c₀) ∧
    Meet3Hyp (Projectivization ℝ (Eucl 3) × ℝ)
      (encodedChains (fun x => H 2 (x 2, pt2 (x 0) (x 1)))
        (planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)))
        (planeClassMap (diskPlane (linPlaneChart (φ 1) c hc))) c₀)

/-- **The ends parity of the class-triple count, from a linearisation of the three class maps** (the
unpacked form of `Work.Drive.HasClassLinearization`): the three bordism steps
(`Work.Drive.even_ncard_classCount_add_of_homotopy`) replace the class maps one at a time by the disk
models of the three linear planes, where the count is one
(`Work.Drive.odd_ncard_classCount_linPlaneCharts`). -/
theorem odd_ncard_classTripleSet_of_linearization
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) (Projectivization ℝ (Eucl 3) × ℝ)]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (Projectivization ℝ (Eucl 3) × ℝ)]
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c)
    (hrank : Module.finrank ℝ ↥(⨅ k : Fin 3, linSub (φ k)) = 1)
    (hgen : ∀ (k : Fin 3) (z : ℂ), ‖z‖ = 1 →
      linPlaneChart (φ k) c hc z ≠ linCommonPt φ c hc hrank)
    (H : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (hH0 : ∀ k, (fun y => H k (0, y)) = planeClassMap (P k))
    (hH1 : ∀ k,
      (fun y => H k (1, y)) = planeClassMap (diskPlane (linPlaneChart (φ k) c hc)))
    {c₀ : ℝ} (hc₀0 : 0 < c₀) (hc₀1 : c₀ < 1)
    (hM0 : Meet3Hyp (Projectivization ℝ (Eucl 3) × ℝ)
      (encodedChains (fun x => H 0 (x 2, pt2 (x 0) (x 1)))
        (planeClassMap (P 1)) (planeClassMap (P 2)) c₀))
    (hM1 : Meet3Hyp (Projectivization ℝ (Eucl 3) × ℝ)
      (encodedChains (fun x => H 1 (x 2, pt2 (x 0) (x 1)))
        (planeClassMap (diskPlane (linPlaneChart (φ 0) c hc))) (planeClassMap (P 2)) c₀))
    (hM2 : Meet3Hyp (Projectivization ℝ (Eucl 3) × ℝ)
      (encodedChains (fun x => H 2 (x 2, pt2 (x 0) (x 1)))
        (planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)))
        (planeClassMap (diskPlane (linPlaneChart (φ 1) c hc))) c₀)) :
    Odd (classTripleSet P).ncard := by
  classical
  -- the three bordism steps, with the two ends identified
  have step0 := even_ncard_classCount_add_of_homotopy (H 0) (planeClassMap (P 1))
    (planeClassMap (P 2)) hc₀0 hc₀1 hM0
  have step1 := even_ncard_classCount_add_of_homotopy (H 1)
    (planeClassMap (diskPlane (linPlaneChart (φ 0) c hc))) (planeClassMap (P 2)) hc₀0 hc₀1 hM1
  have step2 := even_ncard_classCount_add_of_homotopy (H 2)
    (planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)))
    (planeClassMap (diskPlane (linPlaneChart (φ 1) c hc))) hc₀0 hc₀1 hM2
  -- the three steps in the notation of the conclusion
  have hs0 : Even ((classCount (fun k => ![planeClassMap (P 0), planeClassMap (P 1),
        planeClassMap (P 2)] k)).ncard
      + (classCount (fun k => ![planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)),
        planeClassMap (P 1), planeClassMap (P 2)] k)).ncard) := by
    have h := step0
    rw [show (fun y => H 0 (0, y)) = planeClassMap (P 0) from hH0 0,
      show (fun y => H 0 (1, y))
        = planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)) from hH1 0] at h
    simpa using h
  have hs1 : Even ((classCount (fun k => ![planeClassMap (P 1),
        planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)), planeClassMap (P 2)] k)).ncard
      + (classCount (fun k => ![planeClassMap (diskPlane (linPlaneChart (φ 1) c hc)),
        planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)), planeClassMap (P 2)] k)).ncard) := by
    have h := step1
    rw [show (fun y => H 1 (0, y)) = planeClassMap (P 1) from hH0 1,
      show (fun y => H 1 (1, y))
        = planeClassMap (diskPlane (linPlaneChart (φ 1) c hc)) from hH1 1] at h
    simpa using h
  have hs2 : Even ((classCount (fun k => ![planeClassMap (P 2),
        planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)),
        planeClassMap (diskPlane (linPlaneChart (φ 1) c hc))] k)).ncard
      + (classCount (fun k => ![planeClassMap (diskPlane (linPlaneChart (φ 2) c hc)),
        planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)),
        planeClassMap (diskPlane (linPlaneChart (φ 1) c hc))] k)).ncard) := by
    have h := step2
    rw [show (fun y => H 2 (0, y)) = planeClassMap (P 2) from hH0 2,
      show (fun y => H 2 (1, y))
        = planeClassMap (diskPlane (linPlaneChart (φ 2) c hc)) from hH1 2] at h
    simpa using h
  -- the permutations that move the homotopied slot to the first place
  have hfunA : (fun k : Fin 3 => ![planeClassMap (P 0), planeClassMap (P 1),
      planeClassMap (P 2)] k)
      = (fun k => ![planeClassMap (P 0), planeClassMap (P 1), planeClassMap (P 2)] k) := rfl
  have hpermA : (classCount (fun k => ![planeClassMap (P 1),
        planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)), planeClassMap (P 2)] k)).ncard
      = (classCount (fun k => ![planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)),
        planeClassMap (P 1), planeClassMap (P 2)] k)).ncard := by
    have hfun : (fun k : Fin 3 => ![planeClassMap (P 1),
        planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)), planeClassMap (P 2)] k)
        = (fun k => ![planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)),
            planeClassMap (P 1), planeClassMap (P 2)] (Equiv.swap 0 1 k)) := by
      funext k; fin_cases k <;> simp [Equiv.swap_apply_def]
    rw [hfun, ncard_classCount_perm]
  have hpermB : (classCount (fun k => ![planeClassMap (diskPlane (linPlaneChart (φ 1) c hc)),
        planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)), planeClassMap (P 2)] k)).ncard
      = (classCount (fun k => ![planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)),
        planeClassMap (diskPlane (linPlaneChart (φ 1) c hc)),
        planeClassMap (P 2)] k)).ncard := by
    have hfun : (fun k : Fin 3 => ![planeClassMap (diskPlane (linPlaneChart (φ 1) c hc)),
        planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)), planeClassMap (P 2)] k)
        = (fun k => ![planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)),
            planeClassMap (diskPlane (linPlaneChart (φ 1) c hc)),
            planeClassMap (P 2)] (Equiv.swap 0 1 k)) := by
      funext k; fin_cases k <;> simp [Equiv.swap_apply_def]
    rw [hfun, ncard_classCount_perm]
  have hpermC : (classCount (fun k => ![planeClassMap (P 2),
        planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)),
        planeClassMap (diskPlane (linPlaneChart (φ 1) c hc))] k)).ncard
      = (classCount (fun k => ![planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)),
        planeClassMap (diskPlane (linPlaneChart (φ 1) c hc)),
        planeClassMap (P 2)] k)).ncard := by
    have hfun : (fun k : Fin 3 => ![planeClassMap (P 2),
        planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)),
        planeClassMap (diskPlane (linPlaneChart (φ 1) c hc))] k)
        = (fun k => ![planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)),
            planeClassMap (diskPlane (linPlaneChart (φ 1) c hc)),
            planeClassMap (P 2)] ((Equiv.swap 0 2).trans (Equiv.swap 0 1) k)) := by
      funext k; fin_cases k <;> simp [Equiv.swap_apply_def]
    rw [hfun, ncard_classCount_perm]
  have hpermD : (classCount (fun k => ![planeClassMap (diskPlane (linPlaneChart (φ 2) c hc)),
        planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)),
        planeClassMap (diskPlane (linPlaneChart (φ 1) c hc))] k)).ncard
      = (classCount (fun k => ![planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)),
        planeClassMap (diskPlane (linPlaneChart (φ 1) c hc)),
        planeClassMap (diskPlane (linPlaneChart (φ 2) c hc))] k)).ncard := by
    have hfun : (fun k : Fin 3 => ![planeClassMap (diskPlane (linPlaneChart (φ 2) c hc)),
        planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)),
        planeClassMap (diskPlane (linPlaneChart (φ 1) c hc))] k)
        = (fun k => ![planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)),
            planeClassMap (diskPlane (linPlaneChart (φ 1) c hc)),
            planeClassMap (diskPlane (linPlaneChart (φ 2) c hc))]
              ((Equiv.swap 0 2).trans (Equiv.swap 0 1) k)) := by
      funext k; fin_cases k <;> simp [Equiv.swap_apply_def]
    rw [hfun, ncard_classCount_perm]
  -- the base case
  have hbase : Odd (classCount (fun k => ![planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)),
      planeClassMap (diskPlane (linPlaneChart (φ 1) c hc)),
      planeClassMap (diskPlane (linPlaneChart (φ 2) c hc))] k)).ncard := by
    have h := odd_ncard_classCount_linPlaneCharts φ c hc hrank hgen
    have hfun : (fun k : Fin 3 => ![planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)),
        planeClassMap (diskPlane (linPlaneChart (φ 1) c hc)),
        planeClassMap (diskPlane (linPlaneChart (φ 2) c hc))] k)
        = (fun k => planeClassMap (diskPlane (linPlaneChart (φ k) c hc))) := by
      funext k; fin_cases k <;> rfl
    rw [hfun]; exact h
  -- the parity chain
  have eA1 : Even ((classCount (fun k => ![planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)),
        planeClassMap (P 1), planeClassMap (P 2)] k)).ncard
      + (classCount (fun k => ![planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)),
        planeClassMap (diskPlane (linPlaneChart (φ 1) c hc)),
        planeClassMap (P 2)] k)).ncard) := by
    have h := hs1
    rwa [hpermA, hpermB] at h
  have eA2 : Even ((classCount (fun k => ![planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)),
        planeClassMap (diskPlane (linPlaneChart (φ 1) c hc)),
        planeClassMap (P 2)] k)).ncard
      + (classCount (fun k => ![planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)),
        planeClassMap (diskPlane (linPlaneChart (φ 1) c hc)),
        planeClassMap (diskPlane (linPlaneChart (φ 2) c hc))] k)).ncard) := by
    have h := hs2
    rwa [hpermC, hpermD] at h
  have hodd2 : Odd (classCount (fun k => ![planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)),
      planeClassMap (diskPlane (linPlaneChart (φ 1) c hc)),
      planeClassMap (P 2)] k)).ncard :=
    odd_of_odd_add_even (by rwa [Nat.add_comm] at eA2) hbase
  have hodd1 : Odd (classCount (fun k => ![planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)),
      planeClassMap (P 1), planeClassMap (P 2)] k)).ncard :=
    odd_of_odd_add_even (by rwa [Nat.add_comm] at eA1) hodd2
  have hodd0 : Odd (classCount (fun k => ![planeClassMap (P 0), planeClassMap (P 1),
      planeClassMap (P 2)] k)).ncard :=
    odd_of_odd_add_even (by rwa [Nat.add_comm] at hs0) hodd1
  -- back to `classTripleSet`
  rw [classTripleSet_eq_classCount]
  have hfun : (fun k : Fin 3 => planeClassMap (P k))
      = (fun k => ![planeClassMap (P 0), planeClassMap (P 1), planeClassMap (P 2)] k) := by
    funext k; fin_cases k <;> rfl
  rw [hfun]
  exact hodd0

/-- **The ends parity from the packaged linearisation data**: `HasClassLinearization P` gives
`Odd (classTripleSet P).ncard` — the mod-`2` degree input `n_{-λ}` of Hugelmeyer's Lemmas 3–4. -/
theorem odd_ncard_classTripleSet_of_hasClassLinearization
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) (Projectivization ℝ (Eucl 3) × ℝ)]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (Projectivization ℝ (Eucl 3) × ℝ)]
    {P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace}
    (h : HasClassLinearization P) :
    Odd (classTripleSet P).ncard := by
  obtain ⟨φ, c, hc, hrank, hgen, H, c₀, hc₀0, hc₀1, hH0, hH1, hM0, hM1, hM2⟩ := h
  exact odd_ncard_classTripleSet_of_linearization P φ c hc hrank hgen H hH0 hH1 hc₀0 hc₀1 hM0 hM1 hM2


/-- **The ends clause of Hugelmeyer's Lemmas 3–4 in its final form**: for a `ClassTripleRegular` triple
of plane presentations and the truncation data of the design, the linearisation data
`HasClassLinearization P` gives

> `Odd (Σ_k #(bottom_k))`,

i.e. the paper's `n_{-λ}` odd — the end contribution of the parity identity
`n_P + n_Q + n_R + n_λ + n_{-λ} ≡ 0`.  This is `Work.Drive.odd_sum_bottomBdryMeet_of_classTriple` with
both of its inputs discharged from `HasClassLinearization P` (the parity
`odd_ncard_classTripleSet_of_hasClassLinearization`, and the finiteness `finite_of_odd_ncard`, which is
automatic). -/
theorem odd_sum_bottomBdryMeet_of_hasClassLinearization
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) (Projectivization ℝ (Eucl 3) × ℝ)]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (Projectivization ℝ (Eucl 3) × ℝ)]
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (c : Fin 3 → ℝ) (ψ : ℝ → ℝ)
    (hreg : ClassTripleRegular P)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0)
    (hψ01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hcont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1)) (hanti : StrictAntiOn ψ (Set.Icc (0 : ℝ) 1))
    (hcpos : ∀ k : Fin 3, 0 < c k) (hck : ∀ k : Fin 3, c k ≤ c 0)
    (hc1 : c 1 < c 0) (hc2 : c 2 < c 0)
    (hlev : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), c 0 < levelOf (P k y))
    (hlin : HasClassLinearization P) :
    Odd ((bottomBdryMeet CappingSpace
            (fun k => clampedSweep (c k) ψ (P k)) 0).ncard
      + (bottomBdryMeet CappingSpace
            (fun k => clampedSweep (c k) ψ (P k)) 1).ncard
      + (bottomBdryMeet CappingSpace
            (fun k => clampedSweep (c k) ψ (P k)) 2).ncard) := by
  have hodd := odd_ncard_classTripleSet_of_hasClassLinearization (P := P) hlin
  exact odd_sum_bottomBdryMeet_of_classTriple P c ψ hreg hψ hψ0 hψ1 hψ01 hcont hanti hcpos hck hc1 hc2
    hlev (finite_of_odd_ncard hodd) hodd


end

end Work.Drive
