import Mathlib
import Submission.Work.EQ.LaTB.la_fan_trichotomy
import Submission.Work.EQ.FanTri.fan_split2
import Submission.Work.EQ.FanTri.fan_decay
import Submission.Work.EQ.charVal_props
import Submission.Work.EQ.germC_facts

namespace Work.EQ.LaTB

open Work.EQ Complex Filter _root_.Topology
open scoped BigOperators

noncomputable section

/-- **Rychlik's fan trichotomy, in the form where case (i) means *literally constant* words.**

This is a variant of `Work.EQ.LaTB.la_fan_trichotomy` (file
`Submission/Work/EQ/LaTB/la_fan_trichotomy.lean`, already proved and `sorry`-free) with two
changes:

* case (i) is strengthened to `∃ ε₀, ∀ k, ε (φ k) = ε₀` — the words are literally constant, not
  merely equal as fan *maps* on a disc;
* to compensate, the case-(ii) alternative is weakened: the third conjunct becomes
  `(charVal a h ε₁).re ≤ 1` instead of `< 1`, i.e. the characteristic value `1` is allowed there.

This is exactly what is needed for the uniform tail bound `Work.EQ.la_tail_bound_value`: a
constant reading word has a bounded tail index (so case (i) can be excluded when the tail
indices are unbounded), while a case-(ii) word with `charVal = 1` is a chain reading with a long
run of stationary letters that `Work.EQ.LaTB.case_i_words_bounded` (via
`fan_prepend_eq_of_germ`) shows cannot be minimal — it is fed, with its own (possibly `1`)
characteristic value, to `Work.EQ.LaTB.case_ii_reflection_le`.

Proof (please *edit the proved proof* of `Work.EQ.LaTB.la_fan_trichotomy`, do not reinvent):
copy that file and make exactly two changes in the bounded-`fVis` branch produced by
`FanTri.fan_split2`:
1. the first disjunct (`∃ ε₀, ∀ k, ε (φ k) = ε₀`) already gives the new case (i) verbatim;
2. in the second disjunct, *delete* the `by_cases hmu1 : charVal a h ε₁ = 1` split and always
   emit the case-(ii) shape; the three real/imaginary conjuncts are then
   `(charVal a h ε₁).im = 0`, `0 < (charVal a h ε₁).re` and `(charVal a h ε₁).re ≤ 1`, all three
   supplied by `charVal_props ha0 ha1 hh` applied to `ε₁` (its output gives exactly
   `im = 0`, `0 < re ≤ 1`).
The `TendstoUniformlyOn` step is absent here as in `la_fan_trichotomy`.  The unbounded-`fVis`
branch (via `FanTri.fan_decay`, the shrinking case (iii)) is copied unchanged. -/
theorem la_fan_trichotomy_v2 {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : Work.EQ.IsStableGerm a h r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℕ → List Bool, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ((∃ ε₀ : List Bool, ∀ k, ε (φ k) = ε₀) ∨
       (∃ (ε₀ ε₁ : List Bool) (s : ℕ → ℕ) (C : ℕ → List Bool),
          Filter.Tendsto s Filter.atTop Filter.atTop ∧
          (∀ k, ε (φ k) = ε₀ ++ List.replicate (s k) true ++ C k) ∧
          (∀ k, Work.EQ.fan a h (C k) 0 = ((-1 / 2 : ℂ), (0 : ℂ)) ∧
            Work.EQ.charVal a h (C k) = Work.EQ.charVal a h ε₁) ∧
          Work.EQ.fan a h ε₁ 0 = ((-1 / 2 : ℂ), (0 : ℂ)) ∧
          (Work.EQ.charVal a h ε₁).im = 0 ∧ 0 < (Work.EQ.charVal a h ε₁).re ∧
          (Work.EQ.charVal a h ε₁).re ≤ 1) ∨
       ((∀ n : ℕ, ∀ᶠ k in Filter.atTop, n ≤ Work.EQ.nonA1Count a h (ε (φ k))) ∧
          ∀ η : ℝ, 0 < η → ∀ᶠ k in Filter.atTop, ∀ u ∈ Metric.ball (0 : ℂ) δ,
            ‖(Work.EQ.fan a h (ε (φ k)) u).1 - (Work.EQ.fan a h (ε (φ k)) 0).1‖ < η ∧
            ‖(Work.EQ.fan a h (ε (φ k)) u).2‖ < η *
              ‖(Work.EQ.fan a h (ε (φ k)) u).1 - ((a / 2 : ℝ) : ℂ)‖)) := by
  obtain ⟨δ₁, Q, hδ₁, hQ, hest⟩ := FanTri.fan_decay ha0 ha1 hh
  obtain ⟨δ₃, hδ₃, hprops, -⟩ := charVal_props ha0 ha1 hh
  obtain ⟨-, -, -, δ₄, hδ₄, hinv₄⟩ := germC_diff_at_zero ha0 ha1 hh
  have hϑ0 : 0 < fanTh a := fanTh_pos ha0 ha1
  have hϑ1 : fanTh a < 1 := fanTh_lt_one ha0 ha1
  have h1a : (0 : ℝ) < 1 - a := by linarith
  set δ : ℝ := min (min δ₁ (min δ₃ δ₄)) ((1 - a) / (4 * Q)) with hδdef
  have hδ0 : 0 < δ := by
    rw [hδdef]
    exact lt_min (lt_min hδ₁ (lt_min hδ₃ hδ₄)) (by positivity)
  have hδ₁' : δ ≤ δ₁ := by rw [hδdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ₃' : δ ≤ δ₃ := by
    rw [hδdef]
    exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδ₄' : δ ≤ δ₄ := by
    rw [hδdef]
    exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hδQ : δ ≤ (1 - a) / (4 * Q) := by rw [hδdef]; exact min_le_right _ _
  have hQδ : Q * δ ≤ (1 - a) / 4 := by
    have h := mul_le_mul_of_nonneg_left hδQ (le_of_lt hQ)
    have h2 : Q * ((1 - a) / (4 * Q)) = (1 - a) / 4 := by field_simp
    rwa [h2] at h
  refine ⟨δ, hδ0, ?_⟩
  intro ε
  by_cases hbdd : ∃ N : ℕ, ∀ k, fVis (ε k) ≤ N
  · obtain ⟨N, hN⟩ := hbdd
    obtain ⟨φ, hφmono, hsplit⟩ := FanTri.fan_split2 ha0 ha1 ε N hN
    refine ⟨φ, hφmono, ?_⟩
    rcases hsplit with ⟨ε₀, hconst⟩ | ⟨ε₀, C, s, ε₁, hst, hword, hCret, he₁ret, hsgn⟩
    · left
      exact ⟨ε₀, hconst⟩
    · have hC0 : ∀ k, fan a h (C k) 0 = ((-1 / 2 : ℂ), (0 : ℂ)) :=
        fun k => fan_centre_of_ret ha0 ha1 hh (hCret k)
      have hchar : ∀ k, charVal a h (C k) = charVal a h ε₁ := by
        intro k
        rw [charVal_eq_sgnAux ha0 ha1 hh (C k), hsgn k, ← charVal_eq_sgnAux ha0 ha1 hh ε₁]
      have he₁0 : fan a h ε₁ 0 = ((-1 / 2 : ℂ), (0 : ℂ)) :=
        fan_centre_of_ret ha0 ha1 hh he₁ret
      right; left
      obtain ⟨him, hpos, hle, -⟩ := hprops ε₁ he₁0
      exact ⟨ε₀, ε₁, s, C, hst, hword, fun k => ⟨hC0 k, hchar k⟩, he₁0, him, hpos, hle⟩
  · obtain ⟨φ, hφmono, hφfvis⟩ := exists_fVis_subseq ε hbdd
    refine ⟨φ, hφmono, Or.inr (Or.inr ?_)⟩
    refine ⟨?_, ?_⟩
    · intro n
      filter_upwards [Filter.eventually_ge_atTop n] with k hk
      rw [Work.EQ.nonA1Count_eq_fVis ha0 ha1 hh]
      exact le_trans (Nat.le_succ_of_le hk) (hφfvis k)
    · intro η hη
      obtain ⟨K, hK⟩ : ∃ K : ℕ, Q * δ * fanTh a ^ K < η := by
        have hpos : 0 < η / (Q * δ) := by positivity
        obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hpos hϑ1
        refine ⟨K, ?_⟩
        rw [lt_div_iff₀ (by positivity : (0 : ℝ) < Q * δ)] at hK
        linarith
      filter_upwards [Filter.eventually_ge_atTop K] with k hk
      intro u hu
      have hu₁ : u ∈ Metric.ball (0 : ℂ) δ₁ := lt_of_lt_of_le hu hδ₁'
      rw [Metric.mem_ball, dist_zero_right] at hu
      obtain ⟨-, hw, hx⟩ := hest (ε (φ k)) u hu₁
      have hϑle : fanTh a ^ (fVis (ε (φ k))) ≤ fanTh a ^ K :=
        pow_le_pow_of_le_one hϑ0.le hϑ1.le (le_trans (Nat.le_succ_of_le hk) (hφfvis k))
      have hbound : Q * ‖u‖ * fanTh a ^ (fVis (ε (φ k))) < η := by
        calc Q * ‖u‖ * fanTh a ^ (fVis (ε (φ k)))
            ≤ Q * δ * fanTh a ^ K := by
              have h2 : Q * ‖u‖ ≤ Q * δ := mul_le_mul_of_nonneg_left hu.le (le_of_lt hQ)
              have h3 : Q * ‖u‖ * fanTh a ^ (fVis (ε (φ k))) ≤ Q * ‖u‖ * fanTh a ^ K :=
                mul_le_mul_of_nonneg_left hϑle (by positivity)
              have h4 : Q * ‖u‖ * fanTh a ^ K ≤ Q * δ * fanTh a ^ K :=
                mul_le_mul_of_nonneg_right h2 (pow_nonneg hϑ0.le _)
              linarith
          _ < η := hK
      have hxne : (fan a h (ε (φ k)) u).1 - ((a / 2 : ℝ) : ℂ) ≠ 0 := by
        intro hcon
        have hx0 : (1 - a) / 2 ≤ ‖(fan a h (ε (φ k)) 0).1 - ((a / 2 : ℝ) : ℂ)‖ := by
          rw [fan_centre_walk ha0 ha1 hh]
          have h := ((FanSep.centre_numbers ha0 ha1).1
            (stIdx (stAux (ε (φ k)).reverse 0))).2
          simpa only [stCtr] using h
        have hxd : ‖(fan a h (ε (φ k)) u).1 - (fan a h (ε (φ k)) 0).1‖ ≤ Q * δ := by
          refine le_trans hx ?_
          have h1 : fanTh a ^ (fVis (ε (φ k))) ≤ 1 := pow_le_one₀ hϑ0.le hϑ1.le
          have h2 : Q * ‖u‖ ≤ Q * δ := mul_le_mul_of_nonneg_left hu.le (le_of_lt hQ)
          calc Q * ‖u‖ * fanTh a ^ (fVis (ε (φ k)))
              ≤ Q * ‖u‖ * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
            _ = Q * ‖u‖ := by ring
            _ ≤ Q * δ := h2
        have htri : ‖(fan a h (ε (φ k)) 0).1 - ((a / 2 : ℝ) : ℂ)‖
            ≤ ‖(fan a h (ε (φ k)) u).1 - ((a / 2 : ℝ) : ℂ)‖
              + ‖(fan a h (ε (φ k)) u).1 - (fan a h (ε (φ k)) 0).1‖ := by
          have h := norm_sub_le ((fan a h (ε (φ k)) u).1 - ((a / 2 : ℝ) : ℂ))
            ((fan a h (ε (φ k)) u).1 - (fan a h (ε (φ k)) 0).1)
          convert h using 1 <;> ring
        rw [hcon, norm_zero, zero_add] at htri
        linarith [hx0, htri, hxd, hQδ, h1a]
      have hy : (fan a h (ε (φ k)) u).2
          = wFan a h (ε (φ k)) u * ((fan a h (ε (φ k)) u).1 - ((a / 2 : ℝ) : ℂ)) := by
        rw [wFan, div_mul_cancel₀ _ hxne]
      constructor
      · exact lt_of_le_of_lt hx hbound
      · rw [hy, norm_mul]
        have hpos : 0 < ‖(fan a h (ε (φ k)) u).1 - ((a / 2 : ℝ) : ℂ)‖ :=
          norm_pos_iff.mpr hxne
        have hη : ‖wFan a h (ε (φ k)) u‖ < η := lt_of_le_of_lt hw hbound
        nlinarith [hη, hpos]

end

end Work.EQ.LaTB
