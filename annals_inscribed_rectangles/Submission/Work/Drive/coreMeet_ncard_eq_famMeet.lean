import Mathlib
import Submission.Work.Drive.coreCountFam
import Submission.Work.Drive.famMeetDefs

namespace Work.Drive

/-!
# The link between the design's count `coreSideCount` and the L6 engine `odd_ncard_famMeet_iff`

`Work.Drive.coreSideCount Q c P` counts the meets of the core loop `t ↦ Q (exp (i π t))` of the chart
`Q` with the clamped sweep of the plane presentation `P`; the L6 engine
`Work.Drive.odd_ncard_famMeet_iff` controls the parity of the *family* count
`famMeet (coreLoopFam Q) (sweepFam c ψ P) t`.  This file supplies the missing identification of the
two sets: for `t ∈ [0,1]` there is a bijection

`(s, x) ↦ (t, s, x 0, x 1, x 2)`

between `coreMeet Q c (P t) ⊆ ℝ × 𝔸²` and `famMeet (coreLoopFam Q) (sweepFam c (1 - ·) P) t ⊆ 𝔼⁵`, so
that the two cardinalities agree.

The hypothesis `t ∈ [0,1]` is genuinely used (in the `unitBox` clause of the *fourth* coordinate
`p 0 = t`): `famMeet L N t` is empty for `t ∉ [0,1]` while `coreMeet` does not depend on `t` except
through `P t`.
-/

noncomputable section

/-! ## Coordinate lemmas

The two maps `famT3 a b c = (a, b, c)` and `famPt t x = (t, x)` are `Fin.cons`-based, so `simp` reads
off the coordinates only at the numerals `0` and `1`.  The lemmas below record the `.succ` form (which
`simp` does see) together with the numeral forms the main proof needs. -/

@[simp] lemma famT3_apply_zero (a b c : ℝ) : famT3 a b c 0 = a := by simp [famT3]
@[simp] lemma famT3_apply_one (a b c : ℝ) : famT3 a b c 1 = b := by simp [famT3]
@[simp] lemma famT3_apply_two (a b c : ℝ) : famT3 a b c 2 = c := by simp [famT3]

/-- `famT3` rebuilds a `3`-vector from its coordinates. -/
lemma famT3_eta (x : EuclideanSpace ℝ (Fin 3)) : famT3 (x 0) (x 1) (x 2) = x := by
  ext i
  fin_cases i <;> simp [famT3]

/-- The `.succ` coordinates of `famPt t x = (t, x)`. -/
@[simp] lemma famPt_apply_succ (t : ℝ) (x : EuclideanSpace ℝ (Fin 3)) (i : Fin 3) :
    famPt t x i.succ = x i := by simp [famPt]

/-- The tail `(x 0, x 1, x 2)` of `famPt t x` is `x`. -/
lemma famT3_famPt_tail (t : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    famT3 ((famPt t x) 1) ((famPt t x) 2) ((famPt t x) 3) = x := by
  rw [show (1 : Fin 4) = (0 : Fin 3).succ from rfl,
    show (2 : Fin 4) = (1 : Fin 3).succ from rfl,
    show (3 : Fin 4) = (2 : Fin 3).succ from rfl]
  simp only [famPt, WithLp.ofLp_toLp, Fin.cons_succ]
  exact famT3_eta x

/-! ## The two sides of the family, in coordinates -/

/-- The loop side of the family depends only on the second coordinate. -/
lemma famLoop_coreLoopFam (Q : ℂ → CappingSpace) (p : EuclideanSpace ℝ (Fin 5)) :
    famLoop (coreLoopFam Q) p = coreLoop Q (p 1) := by
  simp [famLoop, coreLoopFam, mk2]

/-- The chain side of the family `sweepFam c ψ P` is the sweep of the `p 0`-th presentation at the
chain parameter `(p 2, p 3, p 4)`. -/
lemma famChain_sweepFam (c : ℝ) (ψ : ℝ → ℝ)
    (P : ℝ → EuclideanSpace ℝ (Fin 2) → CappingSpace) (p : EuclideanSpace ℝ (Fin 5)) :
    famChain (sweepFam c ψ P) p
      = clampedSweep c ψ (P (p 0)) (famT3 (p 2) (p 3) (p 4)) := by
  simp only [famChain, sweepFam]
  rw [famPt_apply_zero, famT3_famPt_tail]

/-! ## The bijection -/

/-- **The bijection `q ↦ (t, q.1, q.2 0, q.2 1, q.2 2)`** of the design's count: insert the family
parameter `t` as the first coordinate and read the `3`-chain parameter `q.2` out as the last three
coordinates.  It is written through `ezOfProd` (the coordinate-wise identification `ℝ × 𝔼ⁿ ≅ 𝔼ⁿ⁺¹` of
`Submission/Work/Drive/EZCSetup.lean`), which makes the inverse computations one-liners. -/
def famOfPair (t : ℝ) (q : ℝ × Amb 2) : EuclideanSpace ℝ (Fin 5) :=
  ezOfProd 4 (t, ezOfProd 3 (q.1, q.2))

@[simp] lemma famOfPair_apply_zero (t : ℝ) (q : ℝ × Amb 2) : famOfPair t q 0 = t := by
  simp [famOfPair, ezOfProd]

lemma famOfPair_apply_one (t : ℝ) (q : ℝ × Amb 2) : famOfPair t q 1 = q.1 := by
  rw [show (1 : Fin 5) = (0 : Fin 4).succ from rfl]
  simp only [famOfPair, ezOfProd, WithLp.ofLp_toLp]
  rw [Fin.cons_succ, Fin.cons_zero]

lemma famOfPair_apply_two (t : ℝ) (q : ℝ × Amb 2) : famOfPair t q 2 = q.2 0 := by
  rw [show (2 : Fin 5) = ((0 : Fin 3).succ : Fin 4).succ from rfl]
  simp only [famOfPair, ezOfProd, WithLp.ofLp_toLp]
  rw [Fin.cons_succ, Fin.cons_succ]

lemma famOfPair_apply_three (t : ℝ) (q : ℝ × Amb 2) : famOfPair t q 3 = q.2 1 := by
  rw [show (3 : Fin 5) = ((1 : Fin 3).succ : Fin 4).succ from rfl]
  simp only [famOfPair, ezOfProd, WithLp.ofLp_toLp]
  rw [Fin.cons_succ, Fin.cons_succ]

lemma famOfPair_apply_four (t : ℝ) (q : ℝ × Amb 2) : famOfPair t q 4 = q.2 2 := by
  rw [show (4 : Fin 5) = ((2 : Fin 3).succ : Fin 4).succ from rfl]
  simp only [famOfPair, ezOfProd, WithLp.ofLp_toLp]
  rw [Fin.cons_succ, Fin.cons_succ]

/-- The tail of `famOfPair t q` is `q.2` — the chain parameter is `(p 2, p 3, p 4)`. -/
lemma famT3_famOfPair_tail (t : ℝ) (q : ℝ × Amb 2) :
    famT3 ((famOfPair t q) 2) ((famOfPair t q) 3) ((famOfPair t q) 4) = q.2 := by
  rw [famOfPair_apply_two, famOfPair_apply_three, famOfPair_apply_four, famT3_eta]

/-- The map sends the design's box into the five-box (here `ht` is used, for the coordinate `p 0`). -/
lemma famOfPair_mem_unitBox (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (q : ℝ × Amb 2)
    (h1 : q.1 ∈ Set.Icc (0 : ℝ) 1) (h2 : q.2 ∈ Submission.Drive.unitBox 2) :
    famOfPair t q ∈ Submission.Drive.unitBox 4 := by
  rw [mem_unitBox_iff 4 (famOfPair t q)]
  refine ⟨?_, ?_⟩
  · rw [famOfPair_apply_zero]; exact ht
  · have htail : (ezToProd 4 (famOfPair t q)).2 = ezOfProd 3 (q.1, q.2) := by
      simp only [famOfPair, ezToProd_ofProd]
    rw [htail]
    change ezOfProd 3 (q.1, q.2) ∈ Submission.Drive.unitBox 3
    rw [mem_unitBox_iff 3 (ezOfProd 3 (q.1, q.2))]
    refine ⟨?_, ?_⟩
    · rw [ezOfProd_fst]; exact h1
    · have htail2 : (ezToProd 3 (ezOfProd 3 (q.1, q.2))).2 = q.2 := by
        simp only [ezToProd_ofProd]
      rw [htail2]
      exact h2

/-- The inverse assignment: keep the loop parameter `p 1` and the last three coordinates. -/
def pairOfFam (p : EuclideanSpace ℝ (Fin 5)) : ℝ × Amb 2 :=
  (p 1, WithLp.toLp 2 (fun i : Fin 3 => p i.succ.succ))

@[simp] lemma pairOfFam_fst (p : EuclideanSpace ℝ (Fin 5)) : (pairOfFam p).1 = p 1 := rfl

lemma pairOfFam_snd_apply (p : EuclideanSpace ℝ (Fin 5)) (i : Fin 3) :
    (pairOfFam p).2 i = p i.succ.succ := by simp [pairOfFam]

/-- The tail of `p` as `famT3`. -/
lemma pairOfFam_snd (p : EuclideanSpace ℝ (Fin 5)) :
    (pairOfFam p).2 = famT3 (p 2) (p 3) (p 4) := by
  rw [show (2 : Fin 5) = ((0 : Fin 3).succ : Fin 4).succ from rfl,
    show (3 : Fin 5) = ((1 : Fin 3).succ : Fin 4).succ from rfl,
    show (4 : Fin 5) = ((2 : Fin 3).succ : Fin 4).succ from rfl]
  ext i
  fin_cases i <;> simp [pairOfFam, famT3]

/-- The inverse identification in `𝔼⁴`: the coordinates `(p 1, p 2, p 3, p 4)` of `p`, read as a
`4`-vector. -/
lemma ezOfProd_pairOfFam (p : EuclideanSpace ℝ (Fin 5)) :
    ezOfProd 3 (pairOfFam p) = WithLp.toLp 2 (fun i : Fin 4 => p i.succ) := by
  simp only [pairOfFam, ezOfProd]
  congr 1
  ext i
  rcases Fin.eq_zero_or_eq_succ i with h | ⟨j, h⟩
  · subst h
    simp only [Fin.cons_zero]
    rfl
  · subst h
    simp only [Fin.cons_succ]

/-- `pairOfFam` is a left inverse of `famOfPair` at the parameter `t = p 0`. -/
lemma famOfPair_pairOfFam (t : ℝ) (p : EuclideanSpace ℝ (Fin 5)) (hp : p 0 = t) :
    famOfPair t (pairOfFam p) = p := by
  rw [famOfPair, ezOfProd_pairOfFam, ← hp]
  exact ezOfProd_toProd 4 p

/-- `famOfPair t` is injective (its coordinates `0,1,2,3,4` are `t, q.1, q.2 0, q.2 1, q.2 2`). -/
lemma famOfPair_injective (t : ℝ) : Function.Injective (famOfPair t) := by
  intro q q' h
  have h1 : q.1 = q'.1 := by
    have := congrArg (fun r : EuclideanSpace ℝ (Fin 5) => r 1) h
    rw [famOfPair_apply_one, famOfPair_apply_one] at this
    exact this
  have h2 : q.2 = q'.2 := by
    have hA : famT3 ((famOfPair t q) 2) ((famOfPair t q) 3) ((famOfPair t q) 4)
        = famT3 ((famOfPair t q') 2) ((famOfPair t q') 3) ((famOfPair t q') 4) := by rw [h]
    rw [famT3_famOfPair_tail, famT3_famOfPair_tail] at hA
    exact hA
  exact Prod.ext h1 h2

/-! ## The identification of the two meet sets -/

/-- **The design's count is a `famMeet`**: for `t ∈ [0,1]`, the meet set `Work.Drive.coreMeet Q c (P t)`
of the core loop of the chart `Q` with the clamped sweep of the presentation `P t` (truncated with the
cutoff `s ↦ 1 - s`) has the same cardinality as the family meet set
`Work.Drive.famMeet (coreLoopFam Q) (sweepFam c (fun s => 1 - s) P) t`, under the bijection
`q ↦ (t, q.1, q.2 0, q.2 1, q.2 2)`.  The hypothesis `ht` is necessary: `famMeet L N t` is empty for
`t ∉ [0,1]` because `unitBox 4` constrains the coordinate `p 0 = t`, while `coreMeet` does not depend on
`t` except through `P t`.  This is the link between the design's `coreSideCount` (the `n` of
`Submission/Work/Drive/CHAINPARITY_REDUCTION.md`) and the L6 engine
`Work.Drive.odd_ncard_famMeet_iff`. -/
theorem coreMeet_ncard_eq_famMeet (Q : ℂ → Work.Drive.CappingSpace) (c : ℝ)
    (P : ℝ → EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (Work.Drive.coreMeet Q c (P t)).ncard
      = (Work.Drive.famMeet (Work.Drive.coreLoopFam Q)
          (Work.Drive.sweepFam c (fun s => 1 - s) P) t).ncard := by
  refine Set.ncard_congr (fun q _ => famOfPair t q) ?_ ?_ ?_
  · -- the map sends a `coreMeet` point into the family box
    intro q hq
    rw [coreMeet, Set.mem_ofPred_eq] at hq
    obtain ⟨hq1, hq2, hqeq⟩ := hq
    rw [famMeet, Set.mem_ofPred_eq]
    refine ⟨?_, ?_, ?_⟩
    · exact famOfPair_mem_unitBox t ht q hq1 hq2
    · rw [famOfPair_apply_zero]
    · rw [famLoop_coreLoopFam, famChain_sweepFam]
      rw [famOfPair_apply_zero, famOfPair_apply_one, famT3_famOfPair_tail]
      exact hqeq
  · -- injectivity
    intro q q' _ _ heq
    exact famOfPair_injective t heq
  · -- surjectivity
    intro p hp
    rw [famMeet, Set.mem_ofPred_eq] at hp
    obtain ⟨hpbox, hp0, hpe⟩ := hp
    refine ⟨pairOfFam p, ?_, ?_⟩
    · rw [coreMeet, Set.mem_ofPred_eq]
      refine ⟨?_, ?_, ?_⟩
      · rw [pairOfFam_fst]; exact hpbox 1
      · rw [Submission.Drive.unitBox, Set.mem_ofPred_eq]
        intro i
        rw [pairOfFam_snd_apply]
        exact hpbox i.succ.succ
      · have he : coreLoop Q (p 1)
            = clampedSweep c (fun s => 1 - s) (P t) (famT3 (p 2) (p 3) (p 4)) := by
          have h := hpe
          rw [famLoop_coreLoopFam, famChain_sweepFam, hp0] at h
          exact h
        rw [pairOfFam_fst, pairOfFam_snd, he]
    · exact famOfPair_pairOfFam t p hp0

end

end Work.Drive
