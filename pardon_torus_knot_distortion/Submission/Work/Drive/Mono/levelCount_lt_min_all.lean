import Mathlib
import Submission.Work.Drive.Mono.ae_levelCount_lt_min
import Submission.Work.Drive.Mono.LevelCountDefs
import Submission.Work.Drive.Mono.LevelCountLeDefs
import Submission.Work.Drive.Mono.visit_facts_le
import Submission.Work.Drive.Mono.visit_cover_le

/-!
# The level count at *every* level of the sweep

`Work.Drive.Mono.ae_levelCount_lt_min` bounds the number of parameters at which the knot meets the
frontier of the removed set of a level `lam` by `A + 2B` (whence `< min p q`), but only under the two
restrictions `lam ∉ exc` (the level is not exceptional) and `hcorner` (which forces the knot's
slab-face points at the level's height into the finite set `exc`).

Both restrictions are spurious.  The corner points `{|⟪v,·⟫ - a| = h ∧ ℓ = lam}` are counted as
*face* parameters of the level if one relaxes the strict inequality `ℓ < lam` of
`Work.Drive.Mono.facePts` to `ℓ ≤ lam` (`Work.Drive.Mono.facePtsLe`), and the visit lemmas
`Work.Drive.Mono.visit_facts_le`/`Work.Drive.Mono.visit_cover_le` still show that at most two
parameters of `facePtsLe ∪ wallPts` lie on the closure of any one visit of the knot to the
box-and-slab: the wall point lies strictly between the two endpoints of the visit, so at most one
endpoint is at height `≤ lam` when a wall point is present, and the endpoints are the only face
parameters of the visit.  Everything else (`hcorner`, `lam ∉ exc`) was already unused.
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

section

variable {K : Knot} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : R3} {h : ℝ}
variable {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ}

/-- **The in-box trace parameters of the level are face or wall parameters**, the face parameters
being taken at height `≤ lam` (so that the corner points of the level, `{|⟪v,·⟫ - a| = h ∧ ℓ = lam}`,
are included).  This is `Work.Drive.Mono.inboxPts_subset_corner` with the exceptional-set hypothesis
`hcorner` — used there only to discard the corners — replaced by the relaxed face condition. -/
theorem inboxPts_subset_facePtsLe
    (hh : 0 < h)
    (hwall : ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
      |cutG K c u v t| ≤ h → deriv (wallW K ℓ) t ≠ 0)
    (hface : ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
      |cutG K c u v t| = h → deriv (fun r : ℝ => inner ℝ v (K.curve r)) t ≠ 0) :
    inboxPts K s c σ u v h ℓ lam ⊆
      facePtsLe K s c σ u v h ℓ lam ∪ wallPts K s c σ u v h ℓ lam := by
  intro t ht
  obtain ⟨htIco, htbox, htfr⟩ := ht
  have htboxA : boxA K s c σ t < 0 := (boxA_lt_zero_iff t).mpr htbox
  have h1 := Work.Drive.Mono.inbox_frontier_subset (K := K) (s := s) (u := u) (c := c) (σ := σ)
    (v := v) (h := h) (ℓ := ℓ) (lam := lam) hh ⟨htIco, htbox, htfr⟩
  have hle : |cutG K c u v t| ≤ h :=
    levelCount_abs_le_of_mem_inbox htbox htfr
  rcases h1 with h12 | hD
  · rcases h12 with hAB | hC
    · rcases hAB with hfr | hB
      · -- `t` is on the frontier of the trench: either `|g| = h` (at height `≤ lam`) or `ℓ = lam`
        have hfr' : t ∈ frontier (trenchSet K s c σ u v h ℓ lam) := by
          rwa [trenchSet_eq_raw]
        have hcl := closure_trenchSet_le (K := K) (s := s) (c := c) (σ := σ) (u := u) (v := v)
          (h := h) (ℓ := ℓ) (lam := lam) (frontier_subset_closure hfr')
        have hnotX : t ∉ trenchSet K s c σ u v h ℓ lam := by
          intro hX
          have : t ∈ interior (trenchSet K s c σ u v h ℓ lam) := by
            rwa [isOpen_trenchSet.interior_eq]
          have hfr'' := hfr'
          rw [frontier, Set.mem_sdiff] at hfr''
          exact hfr''.2 this
        by_cases hlt : |cutG K c u v t| < h
        · -- `t` is in the open slab and on the wall: a wall parameter
          right
          refine ⟨htboxA, hlt, le_antisymm hcl.2.2 (le_of_not_gt ?_)⟩
          intro hw
          exact hnotX ⟨htboxA, hlt, hw⟩
        · -- `t` is on a slab face, at height `≤ lam`: a (relaxed) face parameter
          left
          exact ⟨htboxA, le_antisymm hcl.2.1 (not_lt.mp hlt), hcl.2.2⟩
      · -- the wall functional has a critical point at `t` inside the box and the slab: excluded
        have hB' : deriv (wallW K ℓ) t = 0 := by
          rw [deriv_wallW_eq]
          exact hB
        exact absurd hB' (hwall t htbox hle)
    · -- `|g| = h` with critical height: excluded by `hface`
      have hg : |cutG K c u v t| = h := by simpa [cutG] using hC.1
      have hne0 : deriv (cutG K c u v) t ≠ 0 := by
        rw [deriv_cutG_eq]
        exact hface t htbox hg
      exact absurd (by rw [deriv_cutG_eq]; exact hC.2) hne0
  · -- the corner `|g| = h ∧ ℓ = lam`: a relaxed face parameter of the level
    exact Or.inl ⟨htboxA, by simpa [cutG] using hD.1,
      by rw [wallW_apply]; exact le_of_eq hD.2⟩

end

/-- **The level count `< min p q` at EVERY level of the window.**  This is
`Work.Drive.Mono.ae_levelCount_lt_min` with the two spurious restrictions removed: the conclusion is
demanded at every level `lam ∈ Icc lam0 lam1` (no `lam ∉ exc`) and the hypothesis `hcorner` (which
merely forced the knot's slab-face points into the finite set `exc`) is dropped.  The point is that in
the definition of the level's "face points" one may take `ℓ ≤ λ` rather than `ℓ = λ`, and then the
visit count is still at most two per visit of the knot to the box-and-slab, so the arithmetic
`A + 2 B < min p q` proves the bound at the exceptional levels as well.  Needed because the (L) route
consumes the count at *event* levels, which are exactly the elements of `exc`
(`Submission/Work/Drive/Final/NOTES_LEAD_L4_L1.md` §0.2(ii) and §4). -/
theorem levelCount_lt_min_all
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (ψ : Submission.Diffeo) (K : LeanEval.KnotTheory.PardonDistortion.Knot) {r s u : ℝ}
    (hr : 0 < r) (hrs : r < s)
    (hu : |u| < Submission.eps * r) (c : LeanEval.KnotTheory.PardonDistortion.R3)
    (σ : Equiv.Perm (Fin 3)) {A B : ℕ}
    (hA : Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s} ≤ A)
    (harith : A + 2 * B < Nat.min p q)
    (v : LeanEval.KnotTheory.PardonDistortion.R3) (h R : ℝ)
    (ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ)
    (exc : Finset ℝ) (lam0 lam1 : ℝ)
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
        deriv (fun r : ℝ => inner ℝ v (K.curve r)) t ≠ 0) :
    ∀ lam ∈ Set.Icc lam0 lam1,
      Set.encard (Set.range K.curve ∩
        frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam)) <
          (Nat.min p q : ℕ∞) := by
  have hh : 0 < h := hT.2.2.2.2.2.1
  have hs : 0 < s := lt_trans hr hrs
  intro lam hlam
  -- ### the visit geometry (delegated: `Work.Drive.Mono.visit_facts_le`)
  have hfacts : ∀ z ∈ slabVisit K s c σ u v h,
      (∃! w : ℝ, w ∈ visit (slabVisit K s c σ u v h) z ∧ cutG K c u v w = 0) ∧
      (∀ x ∈ closure (visit (slabVisit K s c σ u v h) z),
        ∀ y ∈ closure (visit (slabVisit K s c σ u v h) z),
        ∀ k : ℤ, k ≠ 0 → y - x ≠ 2 * Real.pi * (k : ℝ)) ∧
      (((facePtsLe K s c σ u v h ℓ lam ∪ wallPts K s c σ u v h ℓ lam) ∩
        closure (visit (slabVisit K s c σ u v h) z)).encard ≤ 2) :=
    visit_facts_le (K := K) (s := s) (u := u) (c := c) (σ := σ) (v := v) (h := h)
      (ℓ := ℓ) (lam := lam) hh hboxsph hgraze hwall
  -- ### the cover of the face and wall parameters by the visits (delegated: `visit_cover_le`)
  have hcover0 : ∀ p ∈ facePtsLe K s c σ u v h ℓ lam ∪ wallPts K s c σ u v h ℓ lam,
      ∃ z ∈ cutCross K s c σ u v,
        p ∈ closure (visit (slabVisit K s c σ u v h) z) :=
    visit_cover_le (K := K) (s := s) (u := u) (c := c) (σ := σ) (v := v) (h := h)
      (ℓ := ℓ) (lam := lam) hh
      (fun t ht => by
        obtain ⟨w, hw, -⟩ := (hfacts t ht).1
        exact ⟨w, hw.1, hw.2⟩)
      (fun t ht hg => hface t ht hg)
  -- ### the in-box parameters are (relaxed) face or wall parameters
  have hsub : inboxPts K s c σ u v h ℓ lam ⊆
      facePtsLe K s c σ u v h ℓ lam ∪ wallPts K s c σ u v h ℓ lam :=
    inboxPts_subset_facePtsLe (K := K) (s := s) (u := u) (c := c) (σ := σ) (v := v) (h := h)
      (ℓ := ℓ) (lam := lam) hh hwall hface
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
  have hcount := encard_le_two_mul_of_periodic_visits
    (P := inboxPts K s c σ u v h ℓ lam)
    (P' := facePtsLe K s c σ u v h ℓ lam ∪ wallPts K s c σ u v h ℓ lam)
    (C := cutCross K s c σ u v)
    (V := fun z => visit (slabVisit K s c σ u v h) z)
    hsub (fun t => facePtsLe_union_wallPts_periodic t) (fun t => cutCross_periodic t) hCfin
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
