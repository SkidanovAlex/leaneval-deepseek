/-
# ZeroFreeTables — Table8Printed.lean

**HB Table 8 as printed, certified.**  `Table8CertPrinted` and `Table8CertExtPrinted`
decide the two conjuncts of HB (9.13) (the side condition `cond913` and the failure
of `p913 < 0` of HB Lemma 9.1) at the *printed* entries of HB's Table 8, with
explicit rational witnesses `a` (`t8certRowsP`, `t8certRowsExtP`).  The margins are
between `7.5e-5` and `1.0e-3`, so the printed table needs no `0.001` safety margin
(the frozen `rows15` carry one in any case).

From the certificate and the engine `HBLemma9_1` (and the bridge `HBWideMin`
between the contract's working-region minimality and HB's rectangle (6.1)):

* `lam0_certified_printed` — `λ₀ ≥` the printed value, for all 21 rows, above one
  threshold `q₀`;
* `HBTable8_of_engine` — **HB Table 8 itself** (`HBTable8`, i.e. the whole
  `tableR hbTable8` read in the paper's sense), where the multiplicity conjunct of
  `Lam0Bound` is discharged by the repeated-zero case `HBRepZero` (which forces
  `λ₁ ≥ 1.724 > 1.526`, beyond every Table-8 entry).
-/
import Mathlib
import Submission.Work.ZeroFreeTables.CertData
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.HBProps
import Submission.Work.ZeroFreeTables.API
import Submission.Work.ZeroFreeTables.Tables
import Submission.Work.ZeroFreeTables.Table8Derive
import Submission.Work.ZeroFreeTables.Table8CertPrinted
import Submission.Work.ZeroFreeTables.Table8CertExtPrinted
import Submission.Work.ZeroFreeTables.HBRepZero_red

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

open Work.LinnikContract

/-! ## The arithmetic facts about the printed witnesses -/

theorem t8certRowsP_facts : ∀ r ∈ t8certRowsP,
    0 < r.2.2.2 ∧ 0 < Kaff r.2.1 ∧ r.2.1 ≤ r.2.2.1 ∧ 0 < r.2.1 ∧
      r.2.1 ≤ 696/1000 ∧ r.2.2.1 ≤ 1526/1000 := by
  intro r hr
  simp only [t8certRowsP, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    · subst h
      exact ⟨by norm_num, by norm_num [Kaff], by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem t8certRowsExtP_facts : ∀ r ∈ t8certRowsExtP,
    0 < r.2.2.2 ∧ 0 < Kaff r.2.1 ∧ r.2.1 ≤ r.2.2.1 ∧ 0 < r.2.1 ∧
      r.2.1 ≤ 696/1000 ∧ r.2.2.1 ≤ 1526/1000 := by
  intro r hr
  simp only [t8certRowsExtP, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h | h | h | h <;>
    · subst h
      exact ⟨by norm_num, by norm_num [Kaff], by norm_num, by norm_num, by norm_num, by norm_num⟩

/-! ## The 21 printed entries against the certificate -/

theorem t8printed_route : ∀ p ∈ tableR hbTable8,
    ∃ r ∈ t8certRowsP ++ t8certRowsExtP, r.2.1 = p.1 ∧ p.2 ≤ r.2.2.1 := by
  intro p hp
  fin_cases hp
  · exact ⟨((0.3:ℝ), (0.3:ℝ), (1.526:ℝ), (2181/1000:ℝ)), by norm_num [List.mem_append, t8certRowsP, t8certRowsExtP, List.mem_cons], by norm_num, by norm_num⟩
  · exact ⟨((0.32:ℝ), (0.32:ℝ), (1.446:ℝ), (279/125:ℝ)), by norm_num [List.mem_append, t8certRowsP, t8certRowsExtP, List.mem_cons], by norm_num, by norm_num⟩
  · exact ⟨((0.34:ℝ), (0.34:ℝ), (1.374:ℝ), (2279/1000:ℝ)), by norm_num [List.mem_append, t8certRowsP, t8certRowsExtP, List.mem_cons], by norm_num, by norm_num⟩
  · exact ⟨((0.348:ℝ), (0.36:ℝ), (1.309:ℝ), (1161/500:ℝ)), by norm_num [List.mem_append, t8certRowsP, t8certRowsExtP, List.mem_cons], by norm_num, by norm_num⟩
  · exact ⟨((0.36:ℝ), (0.38:ℝ), (1.25:ℝ), (59/25:ℝ)), by norm_num [List.mem_append, t8certRowsP, t8certRowsExtP, List.mem_cons], by norm_num, by norm_num⟩
  · exact ⟨((0.38:ℝ), (0.4:ℝ), (1.196:ℝ), (599/250:ℝ)), by norm_num [List.mem_append, t8certRowsP, t8certRowsExtP, List.mem_cons], by norm_num, by norm_num⟩
  · exact ⟨((0.4:ℝ), (0.42:ℝ), (1.145:ℝ), (607/250:ℝ)), by norm_num [List.mem_append, t8certRowsP, t8certRowsExtP, List.mem_cons], by norm_num, by norm_num⟩
  · exact ⟨((0.42:ℝ), (0.44:ℝ), (1.099:ℝ), (1229/500:ℝ)), by norm_num [List.mem_append, t8certRowsP, t8certRowsExtP, List.mem_cons], by norm_num, by norm_num⟩
  · exact ⟨((0.44:ℝ), (0.46:ℝ), (1.055:ℝ), (1243/500:ℝ)), by norm_num [List.mem_append, t8certRowsP, t8certRowsExtP, List.mem_cons], by norm_num, by norm_num⟩
  · exact ⟨((0.46:ℝ), (0.48:ℝ), (1.015:ℝ), (2511/1000:ℝ)), by norm_num [List.mem_append, t8certRowsP, t8certRowsExtP, List.mem_cons], by norm_num, by norm_num⟩
  · exact ⟨((0.48:ℝ), (0.5:ℝ), (0.977:ℝ), (507/200:ℝ)), by norm_num [List.mem_append, t8certRowsP, t8certRowsExtP, List.mem_cons], by norm_num, by norm_num⟩
  · exact ⟨((0.5:ℝ), (0.52:ℝ), (0.941:ℝ), (639/250:ℝ)), by norm_num [List.mem_append, t8certRowsP, t8certRowsExtP, List.mem_cons], by norm_num, by norm_num⟩
  · exact ⟨((0.52:ℝ), (0.54:ℝ), (0.907:ℝ), (322/125:ℝ)), by norm_num [List.mem_append, t8certRowsP, t8certRowsExtP, List.mem_cons], by norm_num, by norm_num⟩
  · exact ⟨((0.54:ℝ), (0.56:ℝ), (0.875:ℝ), (519/200:ℝ)), by norm_num [List.mem_append, t8certRowsP, t8certRowsExtP, List.mem_cons], by norm_num, by norm_num⟩
  · exact ⟨((0.56:ℝ), (0.58:ℝ), (0.845:ℝ), (653/250:ℝ)), by norm_num [List.mem_append, t8certRowsP, t8certRowsExtP, List.mem_cons], by norm_num, by norm_num⟩
  · exact ⟨((0.58:ℝ), (0.6:ℝ), (0.816:ℝ), (657/250:ℝ)), by norm_num [List.mem_append, t8certRowsP, t8certRowsExtP, List.mem_cons], by norm_num, by norm_num⟩
  · exact ⟨((0.62:ℝ), (0.62:ℝ), (0.789:ℝ), (2643/1000:ℝ)), by norm_num [List.mem_append, t8certRowsP, t8certRowsExtP, List.mem_cons], by norm_num, by norm_num⟩
  · exact ⟨((0.64:ℝ), (0.64:ℝ), (0.763:ℝ), (2657/1000:ℝ)), by norm_num [List.mem_append, t8certRowsP, t8certRowsExtP, List.mem_cons], by norm_num, by norm_num⟩
  · exact ⟨((0.66:ℝ), (0.66:ℝ), (0.738:ℝ), (267/100:ℝ)), by norm_num [List.mem_append, t8certRowsP, t8certRowsExtP, List.mem_cons], by norm_num, by norm_num⟩
  · exact ⟨((0.68:ℝ), (0.68:ℝ), (0.714:ℝ), (2681/1000:ℝ)), by norm_num [List.mem_append, t8certRowsP, t8certRowsExtP, List.mem_cons], by norm_num, by norm_num⟩
  · exact ⟨((0.696:ℝ), (0.696:ℝ), (0.696:ℝ), (269/100:ℝ)), by norm_num [List.mem_append, t8certRowsP, t8certRowsExtP, List.mem_cons], by norm_num, by norm_num⟩

/-- **The certified `λ₀`-bounds for all 21 printed entries of HB Table 8**: modulo
the engine `HBLemma9_1` and the rational certificate, every row gives
`λ₀ ≥` its printed value, above one common threshold `q₀`. -/
theorem lam0_certified_printed (h9 : HBLemma9_1)
    (hc : ∀ r ∈ t8certRowsP,
      cond913 r.2.1 r.2.2.1 r.2.2.2 (Kaff r.2.1) ∧
      p913 r.2.1 r.2.2.1 r.2.2.2 (Kaff r.2.1) < 0)
    (hcExt : ∀ r ∈ t8certRowsExtP,
      cond913 r.2.1 r.2.2.1 r.2.2.2 (Kaff r.2.1) ∧
      p913 r.2.1 r.2.2.1 r.2.2.2 (Kaff r.2.1) < 0) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → ¬ (χ₁ ^ 2 = 1 ∧ ρ₁.im = 0) →
      ∀ r ∈ t8certRowsP ++ t8certRowsExtP, lamOf q ρ₁ ≤ r.2.1 → Lam0BoundOther χ₁ ρ₁ r.2.2.1 := by
  obtain ⟨N, hN⟩ := exists_threshold_of_forall_mem (t8certRowsP ++ t8certRowsExtP)
    (fun r N => ∀ q : ℕ, N ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → ¬ (χ₁ ^ 2 = 1 ∧ ρ₁.im = 0) → lamOf q ρ₁ ≤ r.2.1 →
      Lam0BoundOther χ₁ ρ₁ r.2.2.1)
    (fun r hr => by
      rcases List.mem_append.mp hr with hr' | hr'
      · obtain ⟨ha, hK, hhiv, hhipos, -, -⟩ := t8certRowsP_facts r hr'
        exact lam0_row_of_lemma9_1_of_facts h9 (hc r hr') ha hK hhiv hhipos
      · obtain ⟨ha, hK, hhiv, hhipos, -, -⟩ := t8certRowsExtP_facts r hr'
        exact lam0_row_of_lemma9_1_of_facts h9 (hcExt r hr') ha hK hhiv hhipos)
    (fun r hr n n' hn hn' q hq => hn' q (le_trans hn hq))
  exact ⟨N, fun q hq _ χ₁ ρ₁ hm hcx r hr hlam => hN r hr q hq χ₁ ρ₁ hm hcx hlam⟩

/-! ## HB Table 8 as a theorem -/

/-- Below `0.696`, a printed row `p` of Table 8 with `0.696 ≤ p.1` is necessarily the
last row `(0.696, 0.696)`, where `p.2 = 0.696`: this is what the multiplicity conjunct
needs (`HBRepZeroC` gives `λ₁ ≥ 0.696` for multiple zeros outside the real-real case). -/
theorem t8printed_lambda0_le : ∀ p ∈ tableR hbTable8, (696:ℝ)/1000 ≤ p.1 → p.2 ≤ 696/1000 := by
  intro p hp h
  fin_cases hp <;> (norm_num at h; try norm_num)

/-- **HB Table 8, as printed in the paper, from the engine and the certificate.**
The hypothesis of `HBTable8` is HB's §6 minimality `IsMin1Wide` (see `API.lean`), so
this needs no bridge: the paper's table is a theorem for *its own* setting. -/
theorem HBTable8_of_engine (h9 : HBLemma9_1)
    (hc : ∀ r ∈ t8certRowsP,
      cond913 r.2.1 r.2.2.1 r.2.2.2 (Kaff r.2.1) ∧
      p913 r.2.1 r.2.2.1 r.2.2.2 (Kaff r.2.1) < 0)
    (hcExt : ∀ r ∈ t8certRowsExtP,
      cond913 r.2.1 r.2.2.1 r.2.2.2 (Kaff r.2.1) ∧
      p913 r.2.1 r.2.2.1 r.2.2.2 (Kaff r.2.1) < 0)
    (hrzc : HBRepZeroC) : HBTable8 := by
  obtain ⟨N, hN⟩ := lam0_certified_printed h9 hc hcExt
  obtain ⟨Nz, hz⟩ := hrzc
  refine ⟨max N Nz, ?_⟩
  intro q hq hqne χ₁ ρ₁ hm hcx p hp hlam
  have hNq : N ≤ q := le_trans (le_max_left N Nz) hq
  have hzq : Nz ≤ q := le_trans (le_max_right N Nz) hq
  obtain ⟨r, hr, hr1, hr2⟩ := t8printed_route p hp
  obtain ⟨-, -, -, -, hrhi, hrv⟩ :=
    (List.mem_append.mp hr).elim (fun h => t8certRowsP_facts r h)
      (fun h => t8certRowsExtP_facts r h)
  have hlam' : lamOf q ρ₁ ≤ r.2.1 := hr1 ▸ hlam
  have hlam696 : lamOf q ρ₁ ≤ 696/1000 := le_trans hlam' hrhi
  have hother := hN q hNq χ₁ ρ₁ hm hcx r hr hlam'
  refine ⟨?_, ?_⟩
  · intro hmult
    have hb := hz q hzq χ₁ ρ₁ hm hcx hmult (by linarith [hlam696] : lamOf q ρ₁ ≤ 7/10)
    have hp1 : (696:ℝ)/1000 ≤ p.1 := le_trans hb hlam
    have hle := t8printed_lambda0_le p hp hp1
    linarith
  · intro ρ hZ hne hconj
    exact le_trans hr2 (hother ρ hZ hne hconj)

end Work.ZeroFreeTables
