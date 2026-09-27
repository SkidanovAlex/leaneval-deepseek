import Mathlib
import Submission.Work.Drive.Surf.Model

namespace Work.Surf

noncomputable section

/-- Two vectors of the plane whose `det2` vanishes are proportional, when the second is nonzero. -/
private lemma exists_smul_of_det2_eq_zero {u z : EuclideanSpace ℝ (Fin 2)} (hz : z ≠ 0)
    (h : Work.Drive.det2 u z = 0) : ∃ lam : ℝ, u = lam • z := by
  have key : u 0 * z 1 = u 1 * z 0 := by
    have h' := h
    simp only [Work.Drive.det2] at h'
    linarith
  by_cases h0 : z 0 = 0
  · have h1 : z 1 ≠ 0 := by
      intro h1
      apply hz
      apply PiLp.ext
      rw [Fin.forall_fin_two]
      exact ⟨h0, h1⟩
    refine ⟨u 1 / z 1, ?_⟩
    apply PiLp.ext
    rw [Fin.forall_fin_two]
    constructor
    · simp only [Work.Drive.smul_apply']
      rw [h0, mul_zero]
      have hk : u 0 * z 1 = 0 := by rw [key, h0, mul_zero]
      exact (mul_eq_zero.mp hk).resolve_right h1
    · simp only [Work.Drive.smul_apply']
      rw [div_mul_cancel₀ (u 1) h1]
  · refine ⟨u 0 / z 0, ?_⟩
    apply PiLp.ext
    rw [Fin.forall_fin_two]
    constructor
    · simp only [Work.Drive.smul_apply']
      rw [div_mul_cancel₀ (u 0) h0]
    · simp only [Work.Drive.smul_apply']
      have h : u 0 / z 0 * z 1 = u 1 := by
        field_simp
        linarith [key]
      rw [h]

/-- `t ↦ cos (π t)` is injective on the open unit interval. -/
private lemma cos_pi_mul_injOn :
    Set.InjOn (fun t : ℝ => Real.cos (Real.pi * t)) (Set.Ioo (0 : ℝ) 1) := by
  intro t1 ht1 t2 ht2 h
  have e1 : Real.pi * t1 ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨le_of_lt (mul_pos Real.pi_pos ht1.1), le_of_lt (by nlinarith [ht1.2, Real.pi_pos])⟩
  have e2 : Real.pi * t2 ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨le_of_lt (mul_pos Real.pi_pos ht2.1), le_of_lt (by nlinarith [ht2.2, Real.pi_pos])⟩
  exact mul_left_cancel₀ (ne_of_gt Real.pi_pos) (Real.strictAntiOn_cos.injOn e1 e2 h)

/-- Every number in `(-1, 1)` is `cos (π t)` for a unique `t ∈ (0,1)`; here the existence half. -/
private lemma exists_cos_pi_mul_eq {lam : ℝ} (h1 : -1 < lam) (h2 : lam < 1) :
    ∃ t ∈ Set.Ioo (0 : ℝ) 1, Real.cos (Real.pi * t) = lam := by
  refine ⟨Real.arccos lam / Real.pi, ⟨?_, ?_⟩, ?_⟩
  · exact div_pos (Real.arccos_pos.mpr h2) Real.pi_pos
  · rw [div_lt_one Real.pi_pos]
    exact Real.arccos_lt_pi.mpr h1
  · have h : Real.pi * (Real.arccos lam / Real.pi) = Real.arccos lam := by
      field_simp
    rw [h]
    exact Real.cos_arccos (le_of_lt h1) (le_of_lt h2)

/-- **The crossings of a chord with a diameter are the zeros of the projected determinant.**

`chordMeet a (straightChord z)` is the set of pairs `(s,t) ∈ (0,1)²` with `a s = cos (π t) • z`; since
`IsChord.mem_disk` gives `‖a s‖ ≤ 1` and `‖z‖ = 1` forces `a s = lam z` with `|lam| ≤ 1` whenever
`det2 (a s) z = 0`, and since `hz1`/`hz2` exclude `|lam| = 1`, the first-coordinate projection is a
bijection onto `{s ∈ [0,1] : det2 (a s) z = 0}`, using that `t ↦ cos (π t)` is a bijection
`(0,1) → (-1,1)` (both directions by `Real.cos` on `(0,π)`; e.g. via `Real.arccos`,
`Real.cos_arccos`, `Real.arccos_mem_Ioo`, or `Real.strictAntiOn_cos`).

Useful ingredients: `Work.Drive.IsChord.mem_disk`, `Work.Drive.det2` (the 2×2 determinant),
`Set.ncard_congr` / `Set.ncard_image_of_injective` (or prove the equality of the two `ncard`s by
exhibiting the bijection in both directions). -/
theorem ncard_chordMeet_straightChord {a : ℝ → EuclideanSpace ℝ (Fin 2)}
    (ha : Work.Drive.IsChord a) {z : EuclideanSpace ℝ (Fin 2)} (hz : z ∈ Work.Drive.unitCircle)
    (hz1 : ∀ s ∈ Set.Icc (0 : ℝ) 1, a s ≠ z)
    (hz2 : ∀ s ∈ Set.Icc (0 : ℝ) 1, a s ≠ -z) :
    (Work.Drive.chordMeet a (Work.Drive.straightChord z)).ncard =
      ({s ∈ Set.Icc (0 : ℝ) 1 | Work.Drive.det2 (a s) z = 0} : Set ℝ).ncard := by
  have hznorm : ‖z‖ = 1 := by simpa [Work.Drive.unitCircle] using hz
  have hz_ne : z ≠ 0 := by
    intro h
    rw [h] at hznorm
    simp at hznorm
  have key : ∀ s ∈ Set.Icc (0 : ℝ) 1, Work.Drive.det2 (a s) z = 0 →
      ∃ lam : ℝ, a s = lam • z ∧ |lam| < 1 ∧ s ∈ Set.Ioo (0 : ℝ) 1 := by
    intro s hs hdet
    obtain ⟨lam, hlam⟩ := exists_smul_of_det2_eq_zero hz_ne hdet
    have hnorm : ‖a s‖ = |lam| := by
      rw [hlam, norm_smul, hznorm, mul_one, Real.norm_eq_abs]
    have hle : |lam| ≤ 1 := by
      rw [← hnorm]
      exact ha.mem_disk s hs
    have hne1 : lam ≠ 1 := fun h => hz1 s hs (by rw [hlam, h, one_smul])
    have hnem1 : lam ≠ -1 := fun h => hz2 s hs (by rw [hlam, h, neg_one_smul])
    have hlt : |lam| < 1 := by
      rcases lt_or_eq_of_le hle with h | h
      · exact h
      · exfalso
        rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp h with h' | h'
        · exact hne1 h'
        · exact hnem1 h'
    have hIoo : s ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor
      · rcases eq_or_lt_of_le hs.1 with h | h
        · exfalso
          have h1 : ‖a s‖ = 1 := by
            rw [← h]
            simpa [Work.Drive.unitCircle] using ha.start
          rw [hnorm] at h1
          linarith
        · exact h
      · rcases eq_or_lt_of_le hs.2 with h | h
        · exfalso
          have h1 : ‖a s‖ = 1 := by
            rw [h]
            simpa [Work.Drive.unitCircle] using ha.end
          rw [hnorm] at h1
          linarith
        · exact h
    exact ⟨lam, hlam, hlt, hIoo⟩
  refine Set.ncard_congr (fun p _ => p.1) ?_ ?_ ?_
  · rintro ⟨s, t⟩ hp
    simp only [Work.Drive.chordMeet, Set.mem_ofPred_eq] at hp
    obtain ⟨hs, ht, heq⟩ := hp
    refine ⟨⟨le_of_lt hs.1, le_of_lt hs.2⟩, ?_⟩
    rw [heq, Work.Drive.straightChord, Work.Drive.det2_smul_left, Work.Drive.det2_self, mul_zero]
  · rintro ⟨s1, t1⟩ ⟨s2, t2⟩ hp hq hst
    simp only [Work.Drive.chordMeet, Set.mem_ofPred_eq] at hp hq
    obtain ⟨hs1, ht1, heq1⟩ := hp
    obtain ⟨hs2, ht2, heq2⟩ := hq
    simp only [Work.Drive.straightChord] at heq1 heq2
    have hst' : s1 = s2 := hst
    refine Prod.ext hst' ?_
    have hcos : Real.cos (Real.pi * t1) = Real.cos (Real.pi * t2) := by
      apply smul_left_injective ℝ hz_ne
      show Real.cos (Real.pi * t1) • z = Real.cos (Real.pi * t2) • z
      rw [← heq1, ← heq2, hst']
    exact cos_pi_mul_injOn ht1 ht2 hcos
  · rintro s ⟨hs, hdet⟩
    obtain ⟨lam, hlam, hlt, hsIoo⟩ := key s hs hdet
    obtain ⟨hlam1, hlam2⟩ := abs_lt.mp hlt
    obtain ⟨t, ht, hcost⟩ := exists_cos_pi_mul_eq hlam1 hlam2
    refine ⟨(s, t), ?_, rfl⟩
    simp only [Work.Drive.chordMeet, Set.mem_ofPred_eq]
    refine ⟨hsIoo, ht, ?_⟩
    rw [hlam, Work.Drive.straightChord, hcost]

end

end Work.Surf
