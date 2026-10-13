import Mathlib
import Submission.Work.WilC4.ULPMDev
import Submission.Work.WilC4.mb_exists_mid_between
import Submission.Work.WilC4.mb_mid_gap_unique

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilC4

/-! ## Elementary facts about `Mid`

`Mid E` (see `ULPMDev.lean`) is the set of positive geometric means `√(ρ₁ρ₂)` of pairs
`ρ₁ < ρ₂` of *consecutive* positive elements of `E`.  In this file we show that, for `E` finite,
every `x > 0` lies in the band of a *unique* positive element `ρ ∈ E` — i.e. no element of `Mid E`
lies strictly between `x` and `ρ`, unless `x` is itself such a geometric mean (in which case there
are two).  This is the "slot" bookkeeping that makes the telescoping in `realULPM` well defined. -/

/-- An element of `Mid E` is positive. -/
lemma mid_pos {E : Set ℝ} {m : ℝ} (hm : m ∈ Mid E) : 0 < m := by
  obtain ⟨ρ₁, -, ρ₂, -, -, -, -, -, hm0⟩ := hm
  exact hm0

/-- Every element of `Mid E` lies strictly below some positive element of `E`. -/
lemma mid_lt_some {E : Set ℝ} {m : ℝ} (hm : m ∈ Mid E) :
    ∃ b : ℝ, b ∈ E ∧ 0 < b ∧ m < b := by
  obtain ⟨ρ₁, -, ρ₂, h2, h0, hlt, -, hsq, -⟩ := hm
  refine ⟨ρ₂, h2, lt_trans h0 hlt, ?_⟩
  nlinarith [sq_nonneg (m - ρ₂), sq_nonneg (m + ρ₂), sq_nonneg m, sq_nonneg ρ₂]

/-- Every element of `Mid E` lies strictly above some positive element of `E`. -/
lemma mid_gt_some {E : Set ℝ} {m : ℝ} (hm : m ∈ Mid E) :
    ∃ a : ℝ, a ∈ E ∧ 0 < a ∧ a < m := by
  obtain ⟨ρ₁, h1, ρ₂, -, h0, hlt, -, hsq, hm0⟩ := hm
  refine ⟨ρ₁, h1, h0, ?_⟩
  nlinarith [sq_nonneg (m - ρ₁), sq_nonneg (m + ρ₁), mul_pos h0 (sub_pos.mpr hlt), sq_nonneg ρ₁]

/-- **Uniqueness of the band.**  If `x ∉ Mid E` and `ρ, ρ'` are two positive elements of `E` whose
bands around `x` avoid `Mid E`, then `ρ = ρ'`.  The proof uses that between two distinct positive
elements of `E` there is always a geometric mean in `Mid E`. -/
lemma band_good_unique {E : Set ℝ} (hE : E.Finite) {x ρ ρ' : ℝ} (hxm : x ∉ Mid E)
    (hρE : ρ ∈ E) (hρ0 : 0 < ρ)
    (hρgood : ∀ m ∈ Mid E, ¬ (min x ρ < m ∧ m < max x ρ))
    (hρ'E : ρ' ∈ E) (hρ'0 : 0 < ρ')
    (hρ'good : ∀ m ∈ Mid E, ¬ (min x ρ' < m ∧ m < max x ρ')) :
    ρ = ρ' := by
  rcases lt_trichotomy ρ ρ' with h | h | h
  · obtain ⟨m, hmMid, hm1, hm2⟩ := mb_exists_mid_between hE hρE hρ0 hρ'E h
    rcases lt_or_ge x ρ with hxρ | hρx
    · exfalso
      refine hρ'good m hmMid ?_
      rw [min_eq_left (le_of_lt (lt_trans hxρ h)), max_eq_right (le_of_lt (lt_trans hxρ h))]
      exact ⟨lt_trans hxρ hm1, hm2⟩
    · rcases lt_or_ge ρ' x with hρ'x | hxρ'
      · exfalso
        refine hρgood m hmMid ?_
        rw [min_eq_right hρx, max_eq_left hρx]
        exact ⟨hm1, lt_trans hm2 hρ'x⟩
      · rcases lt_trichotomy m x with hmx | hmx | hmx
        · exfalso
          refine hρgood m hmMid ?_
          rw [min_eq_right hρx, max_eq_left hρx]
          exact ⟨hm1, hmx⟩
        · exact absurd (hmx ▸ hmMid) hxm
        · exfalso
          refine hρ'good m hmMid ?_
          rw [min_eq_left hxρ', max_eq_right hxρ']
          exact ⟨hmx, hm2⟩
  · exact h
  · obtain ⟨m, hmMid, hm1, hm2⟩ := mb_exists_mid_between hE hρ'E hρ'0 hρE h
    rcases lt_or_ge x ρ' with hxρ | hρx
    · exfalso
      refine hρgood m hmMid ?_
      rw [min_eq_left (le_of_lt (lt_trans hxρ h)), max_eq_right (le_of_lt (lt_trans hxρ h))]
      exact ⟨lt_trans hxρ hm1, hm2⟩
    · rcases lt_or_ge ρ x with hρx' | hxρ'
      · exfalso
        refine hρ'good m hmMid ?_
        rw [min_eq_right hρx, max_eq_left hρx]
        exact ⟨hm1, lt_trans hm2 hρx'⟩
      · rcases lt_trichotomy m x with hmx | hmx | hmx
        · exfalso
          refine hρ'good m hmMid ?_
          rw [min_eq_right hρx, max_eq_left hρx]
          exact ⟨hm1, hmx⟩
        · exact absurd (hmx ▸ hmMid) hxm
        · exfalso
          refine hρgood m hmMid ?_
          rw [min_eq_left hxρ', max_eq_right hxρ']
          exact ⟨hmx, hm2⟩

/-- **The bad scales `Mid E` separate the positive elements of `E` into slots.**  For `E` finite
containing a positive element and `x > 0` with `x ∉ Mid E`, there is a *unique* positive element
`ρ ∈ E` such that no geometric mean of consecutive positive elements of `E` lies strictly between
`x` and `ρ`. -/
theorem mid_band_unique {E : Set ℝ} (hE : E.Finite) (hne : ∃ ρ ∈ E, 0 < ρ) {x : ℝ}
    (hx : 0 < x) (hxm : x ∉ Work.WilC4.Mid E) :
    ∃! ρ : ℝ, ρ ∈ E ∧ 0 < ρ ∧
      ∀ m ∈ Work.WilC4.Mid E, ¬ (min x ρ < m ∧ m < max x ρ) := by
  classical
  have hex : ∃ ρ : ℝ, ρ ∈ E ∧ 0 < ρ ∧ ∀ m ∈ Mid E, ¬ (min x ρ < m ∧ m < max x ρ) := by
    by_cases hxE : x ∈ E
    · refine ⟨x, hxE, hx, ?_⟩
      intro m hm
      rw [min_self, max_self]
      exact fun h => absurd h.1 (not_lt.mpr (le_of_lt h.2))
    · set P : Finset ℝ := hE.toFinset.filter (fun r => 0 < r) with hPdef
      have memP : ∀ r : ℝ, r ∈ P ↔ r ∈ E ∧ 0 < r := by
        intro r
        rw [hPdef, Finset.mem_filter, hE.mem_toFinset]
      have hPne : P.Nonempty := by
        obtain ⟨ρ0, hρ0E, hρ0pos⟩ := hne
        exact ⟨ρ0, (memP ρ0).mpr ⟨hρ0E, hρ0pos⟩⟩
      set S : Finset ℝ := P.filter (fun r => r < x) with hSdef
      set T : Finset ℝ := P.filter (fun r => x < r) with hTdef
      have memS : ∀ r : ℝ, r ∈ S ↔ r ∈ E ∧ 0 < r ∧ r < x := by
        intro r
        rw [hSdef, Finset.mem_filter, memP r]
        tauto
      have memT : ∀ r : ℝ, r ∈ T ↔ r ∈ E ∧ 0 < r ∧ x < r := by
        intro r
        rw [hTdef, Finset.mem_filter, memP r]
        tauto
      have hST : ∀ r ∈ P, r ∈ S ∨ r ∈ T := by
        intro r hrP
        obtain ⟨hrE, hr0⟩ := (memP r).mp hrP
        rcases lt_trichotomy r x with h | h | h
        · exact Or.inl ((memS r).mpr ⟨hrE, hr0, h⟩)
        · exact absurd (h ▸ hrE) hxE
        · exact Or.inr ((memT r).mpr ⟨hrE, hr0, h⟩)
      rcases S.eq_empty_or_nonempty with hSe | hSn
      · rcases T.eq_empty_or_nonempty with hTe | hTn
        · exfalso
          obtain ⟨r, hrP⟩ := hPne
          rcases hST r hrP with h | h
          · rw [hSe] at h; exact (Finset.notMem_empty r) h
          · rw [hTe] at h; exact (Finset.notMem_empty r) h
        · obtain ⟨hbE, hb0, hxb⟩ := (memT (T.min' hTn)).mp (T.min'_mem hTn)
          refine ⟨T.min' hTn, hbE, hb0, ?_⟩
          intro m hmMid
          rw [min_eq_left (le_of_lt hxb), max_eq_right (le_of_lt hxb)]
          rintro ⟨hxm', hmxb⟩
          obtain ⟨a', ha'E, ha'0, ha'm⟩ := mid_gt_some hmMid
          have ha'P : a' ∈ P := (memP a').mpr ⟨ha'E, ha'0⟩
          have hb_le : T.min' hTn ≤ a' := by
            rcases hST a' ha'P with h | h
            · rw [hSe] at h; exact absurd h (Finset.notMem_empty a')
            · exact Finset.min'_le T a' h
          linarith
      · rcases T.eq_empty_or_nonempty with hTe | hTn
        · obtain ⟨haE, ha0, hax⟩ := (memS (S.max' hSn)).mp (S.max'_mem hSn)
          refine ⟨S.max' hSn, haE, ha0, ?_⟩
          intro m hmMid
          rw [min_eq_right (le_of_lt hax), max_eq_left (le_of_lt hax)]
          rintro ⟨hmam, hmx'⟩
          obtain ⟨b', hb'E, hb'0, hmb'⟩ := mid_lt_some hmMid
          have hb'P : b' ∈ P := (memP b').mpr ⟨hb'E, hb'0⟩
          have hle' : b' ≤ S.max' hSn := by
            rcases hST b' hb'P with h | h
            · exact Finset.le_max' S b' h
            · rw [hTe] at h; exact absurd h (Finset.notMem_empty b')
          linarith
        · set a : ℝ := S.max' hSn with hadef
          set b : ℝ := T.min' hTn with hbdef
          have haS : a ∈ S := by rw [hadef]; exact S.max'_mem hSn
          have hbT : b ∈ T := by rw [hbdef]; exact T.min'_mem hTn
          obtain ⟨haE, ha0, hax⟩ := (memS a).mp haS
          obtain ⟨hbE, hb0, hxb⟩ := (memT b).mp hbT
          have hab : a < b := lt_trans hax hxb
          have hno : ∀ c ∈ E, 0 < c → ¬ (a < c ∧ c < b) := by
            intro c hcE hc0
            rintro ⟨hac, hcb⟩
            have hcP : c ∈ P := (memP c).mpr ⟨hcE, hc0⟩
            rcases hST c hcP with h | h
            · have : c ≤ a := by rw [hadef]; exact Finset.le_max' S c h
              linarith
            · have : b ≤ c := by rw [hbdef]; exact Finset.min'_le T c h
              linarith
          have habpos : 0 < a * b := mul_pos ha0 hb0
          set m0 : ℝ := Real.sqrt (a * b) with hm0def
          have hm0sq : m0 * m0 = a * b := by
            rw [hm0def]; exact Real.mul_self_sqrt (le_of_lt habpos)
          have hm0pos : 0 < m0 := by rw [hm0def]; exact Real.sqrt_pos.mpr habpos
          have hm0Mid : m0 ∈ Mid E := by
            refine ⟨a, haE, b, hbE, ha0, hab, ?_, hm0sq, hm0pos⟩
            intro ρ hρE hρ0
            rcases lt_or_ge a ρ with h | h
            · refine Or.inr ?_
              by_contra hbρ
              exact hno ρ hρE hρ0 ⟨h, lt_of_not_ge hbρ⟩
            · exact Or.inl h
          rcases lt_or_ge x m0 with hxlt | hm0x
          · refine ⟨a, haE, ha0, ?_⟩
            intro m hmMid
            rw [min_eq_right (le_of_lt hax), max_eq_left (le_of_lt hax)]
            rintro ⟨hmam, hmx'⟩
            have hsq : m * m = a * b :=
              mb_mid_gap_unique haE ha0 hbE hab hno hmMid hmam (lt_trans hmx' hxb)
            have hmpos : 0 < m := mid_pos hmMid
            have hmEq : m = m0 := by
              have h2 : m * m = m0 * m0 := by rw [hsq, hm0sq]
              rcases mul_self_eq_mul_self_iff.mp h2 with h | h
              · exact h
              · exfalso; rw [h] at hmpos; linarith [hm0pos]
            rw [hmEq] at hmx'
            linarith
          · refine ⟨b, hbE, hb0, ?_⟩
            intro m hmMid
            rw [min_eq_left (le_of_lt hxb), max_eq_right (le_of_lt hxb)]
            rintro ⟨hxm', hmb⟩
            have hsq : m * m = a * b :=
              mb_mid_gap_unique haE ha0 hbE hab hno hmMid (lt_trans hax hxm') hmb
            have hmpos : 0 < m := mid_pos hmMid
            have hmEq : m = m0 := by
              have h2 : m * m = m0 * m0 := by rw [hsq, hm0sq]
              rcases mul_self_eq_mul_self_iff.mp h2 with h | h
              · exact h
              · exfalso; rw [h] at hmpos; linarith [hm0pos]
            rw [hmEq] at hxm'
            linarith
  obtain ⟨ρ, hρE, hρ0, hρgood⟩ := hex
  refine ⟨ρ, ⟨hρE, hρ0, hρgood⟩, ?_⟩
  intro ρ' hρ'
  obtain ⟨hρ'E, hρ'0, hρ'good⟩ := hρ'
  exact (band_good_unique hE hxm hρE hρ0 hρgood hρ'E hρ'0 hρ'good).symm

end Work.WilC4
