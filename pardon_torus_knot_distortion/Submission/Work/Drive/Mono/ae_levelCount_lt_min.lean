import Mathlib
import Submission.Work.Drive.Mono.LevelCountDefs
import Submission.Work.Drive.Mono.encard_le_two_mul_of_periodic_visits
import Submission.Work.Drive.Mono.visit_facts
import Submission.Work.Drive.Mono.visit_cover

/-!
# The level count at every level of the sweep

`Work.Drive.Mono.ae_levelCount_lt_min`: at every level `lam` of the window outside the finite
exceptional set `exc`, the knot meets the frontier of the level's removed set in fewer than
`min p q` parameters.  The counting is spent on the **crossings of the knot with the cutting
plane**: the non-grazing hypotheses of the statement force every visit of the knot to the box and
the slab to cross the plane exactly once, and each visit contributes at most two trace parameters.

The definitions and the elementary lemmas are in `Submission.Work.Drive.Mono.LevelCountDefs`; the
visit geometry is delegated to `Work.Drive.Mono.visit_facts` and `Work.Drive.Mono.visit_cover`,
and the periodic counting to `Work.Drive.Mono.encard_le_two_mul_of_periodic_visits`.
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set
open scoped ENNReal Topology

noncomputable section


open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set in
open scoped ENNReal Topology in
theorem ae_levelCount_lt_min
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (ψ : Submission.Diffeo) (K : Knot) {r s u : ℝ} (hr : 0 < r) (hrs : r < s)
    (hu : |u| < Submission.eps * r) (c : R3) (σ : Equiv.Perm (Fin 3))
    {A B : ℕ}
    (hA : Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s} ≤ A)
    (harith : A + 2 * B < Nat.min p q)
    (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) (exc : Finset ℝ) (lam0 lam1 : ℝ)
    (hT : Work.Drive.Mono.TiltData ψ s c σ u v h R ℓ exc lam0 lam1)
    (hB : Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧
          inner ℝ v (K.curve t) = inner ℝ v c + u} ≤ B)
    (hboxsph : ∀ t : ℝ, Submission.boxNorm c σ (K.curve t) = s →
        h ≤ |inner ℝ v (K.curve t) - (inner ℝ v c + u)|)
    (hgraze : ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
        deriv (fun r : ℝ => inner ℝ v (K.curve r)) t = 0 →
        h ≤ |inner ℝ v (K.curve t) - (inner ℝ v c + u)|)
    (hwall : ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
        |inner ℝ v (K.curve t) - (inner ℝ v c + u)| ≤ h →
        deriv (fun r : ℝ => ℓ (K.curve r)) t ≠ 0)
    (hface : ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
        |inner ℝ v (K.curve t) - (inner ℝ v c + u)| = h →
        deriv (fun r : ℝ => inner ℝ v (K.curve r)) t ≠ 0)
    (hcorner : ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
        |inner ℝ v (K.curve t) - (inner ℝ v c + u)| = h →
        ℓ (K.curve t) ∈ (exc : Set ℝ)) :
    ∀ lam ∈ Set.Icc lam0 lam1, lam ∉ (exc : Set ℝ) →
      Set.encard (Set.range K.curve ∩
        frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam)) <
          (Nat.min p q : ℕ∞) := by
  have hh : 0 < h := hT.2.2.2.2.2.1
  have hs : 0 < s := lt_trans hr hrs
  intro lam hlam hne
  -- ### the visit geometry (delegated: `Work.Drive.Mono.visit_facts`)
  have hfacts : ∀ z ∈ slabVisit K s c σ u v h,
      (∃! w : ℝ, w ∈ visit (slabVisit K s c σ u v h) z ∧ cutG K c u v w = 0) ∧
      (∀ x ∈ closure (visit (slabVisit K s c σ u v h) z),
        ∀ y ∈ closure (visit (slabVisit K s c σ u v h) z),
        ∀ k : ℤ, k ≠ 0 → y - x ≠ 2 * Real.pi * (k : ℝ)) ∧
      (((facePts K s c σ u v h ℓ lam ∪ wallPts K s c σ u v h ℓ lam) ∩
        closure (visit (slabVisit K s c σ u v h) z)).encard ≤ 2) :=
    Work.Drive.Mono.visit_facts (K := K) (s := s) (u := u) (c := c) (σ := σ) (v := v) (h := h)
      (ℓ := ℓ) (lam := lam) (exc := exc) hh hboxsph hgraze hwall hcorner hne
  -- ### the cover of the face and wall parameters by the visits (delegated: `visit_cover`)
  have hcover0 : ∀ p ∈ facePts K s c σ u v h ℓ lam ∪ wallPts K s c σ u v h ℓ lam,
      ∃ z ∈ cutCross K s c σ u v,
        p ∈ closure (visit (slabVisit K s c σ u v h) z) :=
    Work.Drive.Mono.visit_cover (K := K) (s := s) (u := u) (c := c) (σ := σ) (v := v) (h := h)
      (ℓ := ℓ) (lam := lam) (exc := exc) hh
      (fun t ht => (hfacts t ht).1.imp (fun w hw => hw.1))
      (fun t ht hg => hface t ht hg)
  -- ### the in-box parameters are face or wall parameters
  have hsub : inboxPts K s c σ u v h ℓ lam ⊆
      facePts K s c σ u v h ℓ lam ∪ wallPts K s c σ u v h ℓ lam :=
    inboxPts_subset_corner (K := K) (s := s) (u := u) (c := c) (σ := σ) (v := v) (h := h)
      (ℓ := ℓ) (lam := lam) (exc := exc) hh hwall hface hcorner hne
  -- ### the crossings of the cutting plane
  have hset_eq : cutCross K s c σ u v ∩ Set.Ico 0 (2 * Real.pi) =
      {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧ K.curve t ∈ Submission.PBox s c σ ∧
        inner ℝ v (K.curve t) = inner ℝ v c + u} := by
    ext t
    simp only [cutCross, Set.mem_inter_iff, Set.mem_ofPred_eq, cutG]
    rw [boxA_lt_zero_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h3, h1, by linarith⟩
    · rintro ⟨h3, h1, h2⟩
      exact ⟨⟨h1, by linarith⟩, h3⟩
  have hCfin : (cutCross K s c σ u v ∩ Set.Ico 0 (2 * Real.pi)).Finite := by
    rw [hset_eq]
    exact (Set.encard_le_coe_iff.mp hB).1
  have hBbound : (cutCross K s c σ u v ∩ Set.Ico 0 (2 * Real.pi)).encard ≤ (B : ℕ∞) := by
    rw [hset_eq]
    exact hB
  -- ### the periodic counting of the visits
  have hcount := Work.Drive.Mono.encard_le_two_mul_of_periodic_visits
    (P := inboxPts K s c σ u v h ℓ lam)
    (P' := facePts K s c σ u v h ℓ lam ∪ wallPts K s c σ u v h ℓ lam)
    (C := cutCross K s c σ u v)
    (V := fun z => visit (slabVisit K s c σ u v h) z)
    hsub (fun t => cornerPts_periodic t) (fun t => cutCross_periodic t) hCfin
    (fun z hz => connectedComponentIn_add_period (Y := slabVisit K s c σ u v h)
      (fun t => slabVisit_periodic t) (cutCross_subset_slabVisit hh hz))
    (fun p hp => hcover0 p (hsub hp))
    (fun z hz => (hfacts z (cutCross_subset_slabVisit hh hz)).2.2)
    (fun z hz => (hfacts z (cutCross_subset_slabVisit hh hz)).2.1)
  have hPin : inboxPts K s c σ u v h ℓ lam ∩ Set.Ico 0 (2 * Real.pi) =
      inboxPts K s c σ u v h ℓ lam := by
    ext t
    simp only [inboxPts, Set.mem_inter_iff, Set.mem_ofPred_eq]
    tauto
  rw [hPin] at hcount
  have hcount' : (inboxPts K s c σ u v h ℓ lam).encard ≤ ((2 * B : ℕ) : ℕ∞) := by
    calc (inboxPts K s c σ u v h ℓ lam).encard
        ≤ 2 * (cutCross K s c σ u v ∩ Set.Ico 0 (2 * Real.pi)).encard := hcount
      _ ≤ 2 * (B : ℕ∞) := by gcongr
      _ = ((2 * B : ℕ) : ℕ∞) := by push_cast; ring
  -- ### the arithmetic and the level count
  have hin : (Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
      K.curve t ∈ Submission.PBox s c σ ∧
      K.curve t ∈ frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam)} : ℕ∞)
      ≤ ((2 * B : ℕ) : ℕ∞) := by
    simpa only [inboxPts, Set.mem_ofPred_eq] using hcount'
  have harith' : (A : ℕ∞) + ((2 * B : ℕ) : ℕ∞) < (Nat.min p q : ℕ∞) := by
    have h := harith
    exact_mod_cast h
  exact levelCount_lt_min_of_parts p q K (A := (A : ℕ∞))
    (B := ((2 * B : ℕ) : ℕ∞)) hs hA hin harith'


end

end Work.Drive.Mono
