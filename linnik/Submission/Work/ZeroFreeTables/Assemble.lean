/-
# ZeroFreeTables — Assemble.lean

The assembly of AREA 3: the frozen `ZeroFreeCert` of `ROUTE_LEAD.md` §3.1 /
`Work.LinnikContract.Areas` is reduced to the paper's results, with the `P₃`
(Table 8) part *certified* by the rational certificate of `Table8Cert.lean`.

The steps are

* `(Z1)` from HB Theorem 1 (`HBTheorem1`);
* `(Z2)` from [X] Lemma 3.8 (`XYLemma3_8`, `0.628 ≥ 0.56`);
* `(Z3)` and `(Z4)`: `λ₀` from the certified Table 8 (complex case) and Table 4
  (real case), `λ₂` from Lemma 9.4 (Table 10 in all cases), `λ₃` from Table 9 or
  Lemma 10.3;
* `(Z5)` from HB Lemmas 8.4 and 8.8 (Deuring–Heilbronn repulsion) and Table 7;
* the multiplicity case of `λ₀` from `HBRepZero`.

The `Prop`s consumed here are listed in `HBProps.lean`; the two *proved* inputs are
the certificate `Table8Cert` and the engine lemmas of `Table8Derive.lean`.
-/
import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.ZeroFreeTables.Defs
import Submission.Work.ZeroFreeTables.API
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.HBProps
import Submission.Work.ZeroFreeTables.Tables
import Submission.Work.ZeroFreeTables.CertData
import Submission.Work.ZeroFreeTables.Table8Derive
import Submission.Work.ZeroFreeTables.HBRepZero_red
import Submission.Work.LinnikContract2.Areas

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

open Work.LinnikContract

/-! ## Routing: `rows15` against the certified rows of Table 8 -/

/-- Every row of `rows15` is dominated by a certified row of Table 8 (same right
end, tabulated value `≥` the row's `λ₀` entry, which is the tabulated value minus
`0.001`). -/
theorem rows15_t8cert_route : ∀ r ∈ rows15,
    ∃ p ∈ t8certRows, p.2.1 = r.2.1 ∧ r.2.2.1 ≤ p.2.2.1 := by
  intro r hr
  fin_cases hr
  · exact ⟨(((87:ℝ)/250), ((9:ℝ)/25), ((327:ℝ)/250), ((9:ℝ)/4)), by norm_num [t8certRows], by norm_num, by norm_num⟩
  · exact ⟨(((9:ℝ)/25), ((19:ℝ)/50), ((1249:ℝ)/1000), ((23:ℝ)/10)), by norm_num [t8certRows], by norm_num, by norm_num⟩
  · exact ⟨(((19:ℝ)/50), ((2:ℝ)/5), ((239:ℝ)/200), ((117:ℝ)/50)), by norm_num [t8certRows], by norm_num, by norm_num⟩
  · exact ⟨(((2:ℝ)/5), ((21:ℝ)/50), ((143:ℝ)/125), ((47:ℝ)/20)), by norm_num [t8certRows], by norm_num, by norm_num⟩
  · exact ⟨(((21:ℝ)/50), ((11:ℝ)/25), ((549:ℝ)/500), ((12:ℝ)/5)), by norm_num [t8certRows], by norm_num, by norm_num⟩
  · exact ⟨(((11:ℝ)/25), ((23:ℝ)/50), ((527:ℝ)/500), ((241:ℝ)/100)), by norm_num [t8certRows], by norm_num, by norm_num⟩
  · exact ⟨(((23:ℝ)/50), ((12:ℝ)/25), ((507:ℝ)/500), ((49:ℝ)/20)), by norm_num [t8certRows], by norm_num, by norm_num⟩
  · exact ⟨(((12:ℝ)/25), ((1:ℝ)/2), ((122:ℝ)/125), ((247:ℝ)/100)), by norm_num [t8certRows], by norm_num, by norm_num⟩
  · exact ⟨(((1:ℝ)/2), ((13:ℝ)/25), ((47:ℝ)/50), ((249:ℝ)/100)), by norm_num [t8certRows], by norm_num, by norm_num⟩
  · exact ⟨(((13:ℝ)/25), ((27:ℝ)/50), ((453:ℝ)/500), ((5:ℝ)/2)), by norm_num [t8certRows], by norm_num, by norm_num⟩
  · exact ⟨(((27:ℝ)/50), ((14:ℝ)/25), ((437:ℝ)/500), ((63:ℝ)/25)), by norm_num [t8certRows], by norm_num, by norm_num⟩
  · exact ⟨(((14:ℝ)/25), ((29:ℝ)/50), ((211:ℝ)/250), ((127:ℝ)/50)), by norm_num [t8certRows], by norm_num, by norm_num⟩
  · exact ⟨(((29:ℝ)/50), ((3:ℝ)/5), ((163:ℝ)/200), ((51:ℝ)/20)), by norm_num [t8certRows], by norm_num, by norm_num⟩

/-- **The `λ₀`-part of `Z4` for `λ₁ ∈ [0.348, 0.60]`**, from the engine and the
certificate: every zero of `χ₁` other than `ρ₁` has `λ ≥ r.λ₀` on the row `r`. -/
theorem lam0Other_rows15_of_certified (h9 : HBLemma9_1)
    (hcert : ∀ r ∈ t8certRows,
      cond913 r.2.1 r.2.2.1 r.2.2.2 (Kaff r.2.1) ∧
      p913 r.2.1 r.2.2.1 r.2.2.2 (Kaff r.2.1) < 0) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → ¬ (χ₁ ^ 2 = 1 ∧ ρ₁.im = 0) →
      ∀ r ∈ rows15, lamOf q ρ₁ ≤ r.2.1 → Lam0BoundOther χ₁ ρ₁ r.2.2.1 := by
  obtain ⟨N, hN⟩ := HBTable8_certified_other h9 hcert
  exact ⟨N, fun q hq _ χ₁ ρ₁ hm hcx r hr hlam => by
    obtain ⟨p, hp, hp1, hp2⟩ := rows15_t8cert_route r hr
    exact (hN q hq χ₁ ρ₁ hm hcx p hp (by rw [hp1]; exact hlam)).mono' hp2⟩


theorem rows15_t10_route : ∀ r ∈ rows15,
    ∃ p ∈ tableR hbTable10, r.2.1 ≤ p.1 ∧ r.2.2.2.1 ≤ p.2 := by
  intro r hr
  fin_cases hr
  · exact ⟨(((9:ℝ)/25), ((903:ℝ)/1000)), by norm_num [tableR, hbTable10], by norm_num, by norm_num⟩
  · exact ⟨(((19:ℝ)/50), ((887:ℝ)/1000)), by norm_num [tableR, hbTable10], by norm_num, by norm_num⟩
  · exact ⟨(((2:ℝ)/5), ((871:ℝ)/1000)), by norm_num [tableR, hbTable10], by norm_num, by norm_num⟩
  · exact ⟨(((21:ℝ)/50), ((107:ℝ)/125)), by norm_num [tableR, hbTable10], by norm_num, by norm_num⟩
  · exact ⟨(((11:ℝ)/25), ((421:ℝ)/500)), by norm_num [tableR, hbTable10], by norm_num, by norm_num⟩
  · exact ⟨(((23:ℝ)/50), ((829:ℝ)/1000)), by norm_num [tableR, hbTable10], by norm_num, by norm_num⟩
  · exact ⟨(((12:ℝ)/25), ((102:ℝ)/125)), by norm_num [tableR, hbTable10], by norm_num, by norm_num⟩
  · exact ⟨(((1:ℝ)/2), ((803:ℝ)/1000)), by norm_num [tableR, hbTable10], by norm_num, by norm_num⟩
  · exact ⟨(((13:ℝ)/25), ((791:ℝ)/1000)), by norm_num [tableR, hbTable10], by norm_num, by norm_num⟩
  · exact ⟨(((27:ℝ)/50), ((39:ℝ)/50)), by norm_num [tableR, hbTable10], by norm_num, by norm_num⟩
  · exact ⟨(((14:ℝ)/25), ((769:ℝ)/1000)), by norm_num [tableR, hbTable10], by norm_num, by norm_num⟩
  · exact ⟨(((29:ℝ)/50), ((759:ℝ)/1000)), by norm_num [tableR, hbTable10], by norm_num, by norm_num⟩
  · exact ⟨(((3:ℝ)/5), ((749:ℝ)/1000)), by norm_num [tableR, hbTable10], by norm_num, by norm_num⟩

theorem rows15_t9_route : ∀ r ∈ rows15,
    r.2.2.2.2 ≤ 6/7 - 1/1000 ∨ ∃ p ∈ tableR hbTable9, r.2.1 ≤ p.1 ∧ r.2.2.2.2 ≤ p.2 := by
  intro r hr
  fin_cases hr
  · exact Or.inr ⟨(((9:ℝ)/25), ((123:ℝ)/100)), by norm_num [tableR, hbTable9], by norm_num, by norm_num⟩
  · exact Or.inr ⟨(((19:ℝ)/50), ((1181:ℝ)/1000)), by norm_num [tableR, hbTable9], by norm_num, by norm_num⟩
  · exact Or.inr ⟨(((2:ℝ)/5), ((227:ℝ)/200)), by norm_num [tableR, hbTable9], by norm_num, by norm_num⟩
  · exact Or.inr ⟨(((21:ℝ)/50), ((547:ℝ)/500)), by norm_num [tableR, hbTable9], by norm_num, by norm_num⟩
  · exact Or.inr ⟨(((11:ℝ)/25), ((211:ℝ)/200)), by norm_num [tableR, hbTable9], by norm_num, by norm_num⟩
  · exact Or.inr ⟨(((23:ℝ)/50), ((509:ℝ)/500)), by norm_num [tableR, hbTable9], by norm_num, by norm_num⟩
  · exact Or.inr ⟨(((12:ℝ)/25), ((123:ℝ)/125)), by norm_num [tableR, hbTable9], by norm_num, by norm_num⟩
  · exact Or.inr ⟨(((1:ℝ)/2), ((119:ℝ)/125)), by norm_num [tableR, hbTable9], by norm_num, by norm_num⟩
  · exact Or.inr ⟨(((13:ℝ)/25), ((461:ℝ)/500)), by norm_num [tableR, hbTable9], by norm_num, by norm_num⟩
  · exact Or.inr ⟨(((27:ℝ)/50), ((893:ℝ)/1000)), by norm_num [tableR, hbTable9], by norm_num, by norm_num⟩
  · exact Or.inr ⟨(((14:ℝ)/25), ((433:ℝ)/500)), by norm_num [tableR, hbTable9], by norm_num, by norm_num⟩
  · exact Or.inl (by norm_num)
  · exact Or.inl (by norm_num)

theorem rows14_t7_route : ∀ r ∈ rows14,
    ∃ p ∈ tableR hbTable7, r.2.1 ≤ p.1 ∧ r.2.2 ≤ p.2 := by
  intro r hr
  fin_cases hr
  · exact ⟨(((7:ℝ)/20), ((71:ℝ)/50)), by norm_num [tableR, hbTable7], by norm_num, by norm_num⟩
  · exact ⟨(((3:ℝ)/10), ((79:ℝ)/50)), by norm_num [tableR, hbTable7], by norm_num, by norm_num⟩
  · exact ⟨(((1:ℝ)/4), ((177:ℝ)/100)), by norm_num [tableR, hbTable7], by norm_num, by norm_num⟩
  · exact ⟨(((1:ℝ)/5), ((201:ℝ)/100)), by norm_num [tableR, hbTable7], by norm_num, by norm_num⟩

/-! ## Membership of the three universal entries used below -/

theorem mem_tableR_hbTable10_702 : ((702:ℝ)/1000, (702:ℝ)/1000) ∈ tableR hbTable10 := by
  norm_num [tableR, hbTable10]

theorem mem_tableR_hbTable4_35 : ((35:ℝ)/100, (2195:ℝ)/1000) ∈ tableR hbTable4 := by
  norm_num [tableR, hbTable4]

theorem mem_tableR_hbTable8_696 : ((696:ℝ)/1000, (696:ℝ)/1000) ∈ tableR hbTable8 := by
  norm_num [tableR, hbTable8]

theorem rows15_t7_route : ∀ r ∈ rows15,
    ∃ p ∈ tableR hbTable7, r.2.1 ≤ p.1 ∧ r.2.2.2.2 ≤ p.2 := by
  intro r hr
  fin_cases hr
  · exact ⟨(((2:ℝ)/5), ((129:ℝ)/100)), by norm_num [tableR, hbTable7], by norm_num, by norm_num⟩ -- l3=1.229 v=1.29 ok=True
  · exact ⟨(((2:ℝ)/5), ((129:ℝ)/100)), by norm_num [tableR, hbTable7], by norm_num, by norm_num⟩ -- l3=1.18 v=1.29 ok=True
  · exact ⟨(((2:ℝ)/5), ((129:ℝ)/100)), by norm_num [tableR, hbTable7], by norm_num, by norm_num⟩ -- l3=1.134 v=1.29 ok=True
  · exact ⟨(((9:ℝ)/20), ((59:ℝ)/50)), by norm_num [tableR, hbTable7], by norm_num, by norm_num⟩ -- l3=1.093 v=1.18 ok=True
  · exact ⟨(((9:ℝ)/20), ((59:ℝ)/50)), by norm_num [tableR, hbTable7], by norm_num, by norm_num⟩ -- l3=1.054 v=1.18 ok=True
  · exact ⟨(((1:ℝ)/2), ((27:ℝ)/25)), by norm_num [tableR, hbTable7], by norm_num, by norm_num⟩ -- l3=1.017 v=1.08 ok=True
  · exact ⟨(((1:ℝ)/2), ((27:ℝ)/25)), by norm_num [tableR, hbTable7], by norm_num, by norm_num⟩ -- l3=0.983 v=1.08 ok=True
  · exact ⟨(((1:ℝ)/2), ((27:ℝ)/25)), by norm_num [tableR, hbTable7], by norm_num, by norm_num⟩ -- l3=0.951 v=1.08 ok=True
  · exact ⟨(((11:ℝ)/20), ((1:ℝ)/1)), by norm_num [tableR, hbTable7], by norm_num, by norm_num⟩ -- l3=0.921 v=1.0 ok=True
  · exact ⟨(((11:ℝ)/20), ((1:ℝ)/1)), by norm_num [tableR, hbTable7], by norm_num, by norm_num⟩ -- l3=0.892 v=1.0 ok=True
  · exact ⟨(((3:ℝ)/5), ((23:ℝ)/25)), by norm_num [tableR, hbTable7], by norm_num, by norm_num⟩ -- l3=0.865 v=0.92 ok=True
  · exact ⟨(((3:ℝ)/5), ((23:ℝ)/25)), by norm_num [tableR, hbTable7], by norm_num, by norm_num⟩ -- l3=0.856 v=0.92 ok=True
  · exact ⟨(((3:ℝ)/5), ((23:ℝ)/25)), by norm_num [tableR, hbTable7], by norm_num, by norm_num⟩ -- l3=0.856 v=0.92 ok=True
/-! ## (Z1) and (Z2) -/

/-- Unpacking a common threshold given as a five-fold `max`. -/
theorem unpack7 {a b c d e f g q : ℕ} (h : max (max (max (max (max (max a b) c) d) e) f) g ≤ q) :
    a ≤ q ∧ b ≤ q ∧ c ≤ q ∧ d ≤ q ∧ e ≤ q ∧ f ≤ q ∧ g ≤ q := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem unpack8 {a b c d e f g hh q : ℕ}
    (h : max (max (max (max (max (max (max a b) c) d) e) f) g) hh ≤ q) :
    a ≤ q ∧ b ≤ q ∧ c ≤ q ∧ d ≤ q ∧ e ≤ q ∧ f ≤ q ∧ g ≤ q ∧ hh ≤ q := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem unpack6 {a b c d e f q : ℕ} (h : max (max (max (max (max a b) c) d) e) f ≤ q) :
    a ≤ q ∧ b ≤ q ∧ c ≤ q ∧ d ≤ q ∧ e ≤ q ∧ f ≤ q := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem unpack5 {a b c d e q : ℕ} (h : max (max (max (max a b) c) d) e ≤ q) :
    a ≤ q ∧ b ≤ q ∧ c ≤ q ∧ d ≤ q ∧ e ≤ q := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem Z1_source (h : HBTheorem1) : ∀ lamS : ℝ, 0 < lamS → ∃ q₀ : ℕ,
    ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → Z1 χ₁ ρ₁ := by
  obtain ⟨N, hN⟩ := h
  intro lamS hS
  refine ⟨N, fun q hq _ χ₁ ρ₁ hm => ?_⟩
  intro hlt
  exact hN q hq χ₁ ρ₁ hm hlt

theorem Z2_source (h : XYLemma3_8) : ∀ lamS : ℝ, 0 < lamS → ∃ q₀ : ℕ,
    ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → Z2 χ₁ ρ₁ := by
  intro lamS hS
  obtain ⟨q₀, hq⟩ := h
  refine ⟨q₀, fun q hq' _ χ₁ ρ₁ hm h2 him => ?_⟩
  show 0.56 ≤ lamOf q ρ₁
  linarith [hq q hq' χ₁ ρ₁ hm h2 him]

/-! ## (Z3) -/

/-- **`λ₀ ≥ 0.695`** (Z3, first part): from HB Table 8 in the complex case, HB Table 4 in
the real case, and the repeated-zero case (`HBRepZero`). -/
theorem lam0_0695_of_props
    (hc8 : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → ¬ (χ₁ ^ 2 = 1 ∧ ρ₁.im = 0) →
      ∀ r ∈ t8certRows ++ t8certRowsExt, lamOf q ρ₁ ≤ r.2.1 → Lam0BoundOther χ₁ ρ₁ r.2.2.1)
    (ht4 : HBTable4) (hrzc : HBRepZeroC) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → Lam0Bound χ₁ ρ₁ 0.695 := by
  obtain ⟨N8, h8⟩ := hc8
  obtain ⟨Nrz, hrz⟩ := hbRepZero_of_table4 ht4
  obtain ⟨N4, h4⟩ := ht4
  obtain ⟨Nrzc, hrzc⟩ := hrzc
  refine ⟨max (max (max N8 N4) Nrz) Nrzc, fun q hq _ χ₁ ρ₁ hm => ?_⟩
  obtain ⟨hq8, hq4, hqrz, hqrzc⟩ : N8 ≤ q ∧ N4 ≤ q ∧ Nrz ≤ q ∧ Nrzc ≤ q := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
  have hmem : IsZ χ₁ ρ₁ := isMin1_isZ hm.1
  refine ⟨?_, ?_⟩
  · intro hmult
    by_cases hl : lamOf q ρ₁ ≤ 7/10
    · by_cases hrr : χ₁ ^ 2 = 1 ∧ ρ₁.im = 0
      · have h := hrz q hqrz χ₁ ρ₁ hm hrr.1 hrr.2 hmult hl
        linarith
      · have h := hrzc q hqrzc χ₁ ρ₁ hm hrr hmult hl
        linarith
    · push_neg at hl
      linarith
  · intro ρ hZ hne hconj
    by_cases hl : lamOf q ρ₁ ≤ 695/1000
    · by_cases hcx : ¬ (χ₁ ^ 2 = 1 ∧ ρ₁.im = 0)
      · have hb := h8 q hq8 χ₁ ρ₁ hm hcx
            ((695:ℝ)/1000, (695:ℝ)/1000, (695:ℝ)/1000, (129:ℝ)/50)
            (by norm_num [List.mem_append, t8certRowsExt, List.mem_cons]) hl
        have hb2 := hb ρ hZ hne hconj
        linarith
      · push_neg at hcx
        have hb := h4 q hq4 χ₁ ρ₁ hm hcx.1 hcx.2
          ((70:ℝ)/100, (1724:ℝ)/1000) mem_tableR_hbTable4_70 (by linarith)
        have hb2 := (lam0Bound_iff.mp hb).2 ρ hZ hne hconj
        linarith
    · push_neg at hl
      linarith [hl, isMin1_lam_le hm.1 hZ]

/-- **`λ₂ ≥ 0.701`** (Z3, second part): from HB Lemma 9.4 (Table 10 in all cases)
when `λ₁ ≤ 0.702`, and from `λ₂ ≥ λ₁` otherwise. -/
theorem lam2_0701_of_lemma94 (h94 : HBLemma9_4) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → Lam2Bound χ₁ 0.701 := by
  obtain ⟨N, hN⟩ := h94
  refine ⟨N, ?_⟩
  intro q hq _ χ₁ ρ₁ hm
  show ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZ χ ρ → χ ≠ χ₁ → χ ≠ χ₁⁻¹ →
    0.701 ≤ lamOf q ρ
  intro χ ρ hZ h1 h2
  by_cases hl : lamOf q ρ₁ ≤ 702/1000
  · have hb : Lam2Bound χ₁ (702/1000) :=
      hN q hq χ₁ ρ₁ hm _ mem_tableR_hbTable10_702 hl
    exact le_trans (by norm_num) (hb χ ρ hZ h1 h2)
  · push_neg at hl
    exact le_trans (by norm_num) (le_trans (le_of_lt hl) (isMin1_lam_le hm.1 hZ))

/-- **`λ₃ ≥ 0.856`** (Z3, third part): from HB Lemma 10.3 with the contract's
margin `1/1000`. -/
theorem lam3_0856_of_lemma10_3 (h103 : HB10_3_conclusion) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → Lam3Bound χ₁ 0.856 := by
  obtain ⟨N, hN⟩ := h103
  exact ⟨N, fun q hq _ χ₁ ρ₁ hm => lam3Bound_mono (hN q hq χ₁ ρ₁ hm) (by norm_num)⟩

theorem Z3_source     (hc8 : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
        (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → ¬ (χ₁ ^ 2 = 1 ∧ ρ₁.im = 0) →
      ∀ r ∈ t8certRows ++ t8certRowsExt, lamOf q ρ₁ ≤ r.2.1 → Lam0BoundOther χ₁ ρ₁ r.2.2.1)
    (ht4 : HBTable4) (h94 : HBLemma9_4)
    (h103 : HB10_3_conclusion) (hrzc : HBRepZeroC) : ∀ lamS : ℝ, 0 < lamS → ∃ q₀ : ℕ,
    ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → Z3 χ₁ ρ₁ := by
  obtain ⟨N1, h1⟩ := lam0_0695_of_props hc8 ht4 hrzc
  obtain ⟨N2, h2⟩ := lam2_0701_of_lemma94 h94
  obtain ⟨N3, h3⟩ := lam3_0856_of_lemma10_3 h103
  intro lamS hS
  refine ⟨max (max N1 N2) N3, fun q hq _ χ₁ ρ₁ hm => ?_⟩
  obtain ⟨hq1, hq2, hq3⟩ : N1 ≤ q ∧ N2 ≤ q ∧ N3 ≤ q := by
    refine ⟨?_, ?_, ?_⟩ <;> omega
  exact ⟨h1 q hq1 χ₁ ρ₁ hm, h2 q hq2 χ₁ ρ₁ hm, h3 q hq3 χ₁ ρ₁ hm⟩


/-! ## (Z4): the §15 rows -/

/-- **`(Z4)`**, the §15 rows: on row `r`, with `λ₁ ∈ [r.1, r.hi]`, all three table
bounds hold.  `λ₀` comes from the *certified* Table 8 in the complex case and from
HB Table 4 in the real case (with `HBRepZero` excluding a multiple `ρ₁`), `λ₂` from
HB Lemma 9.4, `λ₃` from HB Table 9 or Lemma 10.3. -/
theorem Z4_source (h9 : HBLemma9_1)
    (hcert : ∀ r ∈ t8certRows,
      cond913 r.2.1 r.2.2.1 r.2.2.2 (Kaff r.2.1) ∧
      p913 r.2.1 r.2.2.1 r.2.2.2 (Kaff r.2.1) < 0)
    (ht4 : HBTable4) (h94 : HBLemma9_4) (ht9 : HBTable9) (h103 : HB10_3_conclusion)
    (ht7 : HBTable7) (hrzc : HBRepZeroC) (hxy : XYLemma3_8) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ), IsMin1WideAt 10 χ₁ ρ₁ →
      ∀ r ∈ rows15, r.1 ≤ lamOf q ρ₁ → lamOf q ρ₁ ≤ r.2.1 →
        Lam0Bound χ₁ ρ₁ r.2.2.1 ∧ Lam2Bound χ₁ r.2.2.2.1 ∧ Lam3Bound χ₁ r.2.2.2.2 := by
  obtain ⟨N1, h1⟩ := lam0Other_rows15_of_certified h9 hcert
  obtain ⟨Nrz, hrz⟩ := hbRepZero_of_table4 ht4
  obtain ⟨N4, h4⟩ := ht4
  obtain ⟨N94, h94⟩ := h94
  obtain ⟨N9, h9t⟩ := ht9
  obtain ⟨N10, h10⟩ := h103
  obtain ⟨N7, h7⟩ := ht7
  obtain ⟨Nrzc, hrzc⟩ := hrzc
  obtain ⟨Nxy, hxy'⟩ := hxy
  refine ⟨max (max (max (max (max (max (max N1 N4) N94) N9) N10) N7) (max Nrz Nrzc)) Nxy,
    fun q hq _ χ₁ ρ₁ hm r hr hlo hhi => ?_⟩
  obtain ⟨hN1, hN4, hN94, hN9, hN10, hN7, hmax, hNxy⟩ := unpack8 hq
  obtain ⟨hNrz, hNrzc⟩ : Nrz ≤ q ∧ Nrzc ≤ q := max_le_iff.mp hmax
  refine ⟨?_, ?_, ?_⟩
  · -- `λ₀`
    refine ⟨?_, ?_⟩
    · intro hmult
      exfalso
      have hrng6 : lamOf q ρ₁ ≤ 6/10 := by
        have : r.2.1 ≤ 6/10 := by fin_cases hr <;> norm_num
        linarith
      have hrng : lamOf q ρ₁ ≤ 7/10 := by linarith
      by_cases hrr : χ₁ ^ 2 = 1 ∧ ρ₁.im = 0
      · have := hrz q hNrz χ₁ ρ₁ hm hrr.1 hrr.2 hmult hrng
        linarith
      · have := hrzc q hNrzc χ₁ ρ₁ hm hrr hmult hrng
        linarith
    · intro ρ hZ hne hconj
      by_cases hcx : ¬ (χ₁ ^ 2 = 1 ∧ ρ₁.im = 0)
      · have hhi7 : lamOf q ρ₁ ≤ 6/7 - 1/1000 := by
          have : r.2.1 ≤ 6/10 := by fin_cases hr <;> norm_num
          linarith
        have ho := h1 q hN1 χ₁ ρ₁ hm hcx r hr hhi
        exact ho ρ hZ hne hconj
      · push_neg at hcx
        have hhi2 : r.2.1 ≤ 7/10 := by fin_cases hr <;> norm_num
        have hb := h4 q hN4 χ₁ ρ₁ hm hcx.1 hcx.2
          ((70:ℝ)/100, (1724:ℝ)/1000) mem_tableR_hbTable4_70 (by linarith)
        have hb2 := (lam0Bound_iff.mp hb).2 ρ hZ hne hconj
        have hle : r.2.2.1 ≤ 1724/1000 := by fin_cases hr <;> norm_num
        linarith
  · -- `λ₂`
    obtain ⟨p, hp, hp1, hp2⟩ := rows15_t10_route r hr
    have hhi6 : lamOf q ρ₁ ≤ 6/7 - 1/1000 := by
      have : r.2.1 ≤ 6/10 := by fin_cases hr <;> norm_num
      linarith
    have hb := h94 q hN94 χ₁ ρ₁ hm p hp (le_trans hhi hp1)
    exact lam2Bound_mono hb hp2
  · -- `λ₃`: Table 9 in the complex case, Table 7 (via `λ₃ ≥ λ₂`) in the real one
    have hhi6 : lamOf q ρ₁ ≤ 6/7 - 1/1000 := by
      have : r.2.1 ≤ 6/10 := by fin_cases hr <;> norm_num
      linarith
    by_cases hcx : ¬ (χ₁ ^ 2 = 1 ∧ ρ₁.im = 0)
    · -- in the complex case; when `χ₁` is real we use `XYLemma3_8` (the row is vacuous)
      by_cases hchi : χ₁ ^ 2 = 1
      · exfalso
        have him : ρ₁.im ≠ 0 := fun h0 => hcx ⟨hchi, h0⟩
        have h628 := hxy' q hNxy χ₁ ρ₁ hm hchi him
        have : r.2.1 ≤ 6/10 := by fin_cases hr <;> norm_num
        linarith
      · rcases rows15_t9_route r hr with hcap | ⟨p, hp, hp1, hp2⟩
        · exact lam3Bound_mono (h10 q hN10 χ₁ ρ₁ hm) hcap
        · exact lam3Bound_mono
            (h9t q hN9 χ₁ ρ₁ hm hchi p hp (le_trans hhi hp1)) hp2
    · push_neg at hcx
      obtain ⟨p, hp, hp1, hp2⟩ := rows15_t7_route r hr
      have hhi6 : lamOf q ρ₁ ≤ 6/7 - 1/1000 := by
        have : r.2.1 ≤ 6/10 := by fin_cases hr <;> norm_num
        linarith
      have hg7 : lamOf q ρ₁ < 696/1000 := by
        have : r.2.1 ≤ 6/10 := by fin_cases hr <;> norm_num
        linarith
      have hb := h7 q hN7 χ₁ ρ₁ hm hcx.1 hcx.2 hg7 p hp (le_trans hhi hp1)
      exact lam3Bound_mono (lam2Bound_to_lam3Bound hb) hp2

/-! ## (Z5): the Deuring–Heilbronn range and repulsion -/

/-- **`(Z5)`, rows part**: for `λ₁ < 0.348` the zero is real (`(Z1)`), so the
`λ₀`-bounds come from HB Table 4 and the `λ₂`-bounds from HB Table 7. -/
theorem Z5rows_source (hZ1 : ∀ lamS : ℝ, 0 < lamS → ∃ q₀ : ℕ,
      ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
        IsMin1WideAt 10 χ₁ ρ₁ → Z1 χ₁ ρ₁)
    (ht4 : HBTable4) (ht7 : HBTable7) : ∀ lamS : ℝ, 0 < lamS → ∃ q₀ : ℕ,
    ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → Z5rows χ₁ ρ₁ lamS := by
  intro lamS hS
  obtain ⟨N1, h1⟩ := hZ1 lamS hS
  obtain ⟨N4, h4⟩ := ht4
  obtain ⟨N7, h7⟩ := ht7
  refine ⟨max (max N1 N4) N7, fun q hq _ χ₁ ρ₁ hm => ?_⟩
  obtain ⟨hq1, hq4, hq7⟩ : N1 ≤ q ∧ N4 ≤ q ∧ N7 ≤ q := by
    refine ⟨?_, ?_, ?_⟩ <;> omega
  intro r hr hS' hlo hhi
  have hhi' : r.2.1 ≤ 0.348 := by fin_cases hr <;> norm_num
  have hlt : lamOf q ρ₁ < 0.348 := lt_of_lt_of_le hhi hhi'
  obtain ⟨hrl, hzi, -, -⟩ := h1 q hq1 χ₁ ρ₁ hm hlt
  have hrng : lamOf q ρ₁ ≤ 35/100 := by linarith
  have hcle : r.2.2 ≤ 18/10 := by fin_cases hr <;> norm_num
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro hmult
      have := (lam0Bound_iff.mp (h4 q hq4 χ₁ ρ₁ hm hrl hzi
        ((35:ℝ)/100, (2195:ℝ)/1000) mem_tableR_hbTable4_35 hrng)).1 hmult
      linarith
    · intro ρ hZ hne hconj
      have := (lam0Bound_iff.mp (h4 q hq4 χ₁ ρ₁ hm hrl hzi
        ((35:ℝ)/100, (2195:ℝ)/1000) mem_tableR_hbTable4_35 hrng)).2 ρ hZ hne hconj
      linarith
  · obtain ⟨p, hp, hp1, hp2⟩ := rows14_t7_route r hr
    have hb := h7 q hq7 χ₁ ρ₁ hm hrl hzi (by linarith) p hp
      (le_trans (le_of_lt hhi) hp1)
    exact lam2Bound_mono hb hp2

/-- **`(Z5)`, repulsion part**: for `λ₁ < 0.2` the zero is real (`(Z1)`), HB Lemma
8.4 gives `λ₀ ≥ (3/2)log(1/λ₁)` and HB Lemma 8.8 gives `λ₂ ≥ (12/11)log(1/λ₁)`;
both dominate `(99/100)log(1/λ₁)`. -/
theorem Z5rep_source (hZ1 : ∀ lamS : ℝ, 0 < lamS → ∃ q₀ : ℕ,
      ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
        IsMin1WideAt 10 χ₁ ρ₁ → Z1 χ₁ ρ₁)
    (h84 : HBLemma8_4) (h88 : HBLemma8_8) : ∀ lamS : ℝ, 0 < lamS → ∃ q₀ : ℕ,
    ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → Z5rep χ₁ ρ₁ lamS := by
  intro lamS hS
  obtain ⟨N1, h1⟩ := hZ1 lamS hS
  obtain ⟨N84, h84⟩ := h84 1 (by norm_num) lamS hS
  obtain ⟨N88, h88⟩ := h88 (1/100) (by norm_num) lamS hS
  refine ⟨max (max N1 N84) N88, fun q hq _ χ₁ ρ₁ hm => ?_⟩
  obtain ⟨hq1, hq84, hq88⟩ : N1 ≤ q ∧ N84 ≤ q ∧ N88 ≤ q := by
    refine ⟨?_, ?_, ?_⟩ <;> omega
  intro hS' hlt
  have hlt348 : lamOf q ρ₁ < 0.348 := by linarith
  obtain ⟨hrl, hzi, -, -⟩ := h1 q hq1 χ₁ ρ₁ hm hlt348
  have hle20 : lamOf q ρ₁ ≤ 2/10 := by linarith
  have hlognn : 0 ≤ Real.log (1 / lamOf q ρ₁) := by
    by_cases h0 : lamOf q ρ₁ = 0
    · simp [h0]
    · have hq2 : 2 ≤ q := two_le_modulus_of_char_ne_one (isZ_ne_one (isMin1_isZ hm.1))
      have hpos : 0 < lamOf q ρ₁ :=
        lt_of_le_of_ne (Work.LinnikContract.API.isZ_lambda_nonneg hq2 (isMin1_isZ hm.1)) (Ne.symm h0)
      apply Real.log_nonneg
      rw [le_div_iff₀ hpos]
      linarith
  have hwide : IsMin1WideAt 10 χ₁ ρ₁ := hm
  have hb0 := (h84 q hq84 χ₁ ρ₁ hwide hrl hzi hS').2
  have hb2 := (h88 q hq88 χ₁ ρ₁ hwide hrl hzi hS' (by linarith only [hlt348])).1
  refine ⟨lam0Bound_mono hb0 ?_, lam2Bound_mono hb2 ?_⟩
  · exact le_trans (by nlinarith [hlognn]) (le_max_left _ _)
  · nlinarith [hlognn]


/-! ## The assembly -/

/-- **AREA 3.**  The frozen `ZeroFreeCert` of `ROUTE_LEAD.md` §3.1 follows from
Heath-Brown's paper (his Theorems 1–3, Tables 4, 7, 8, 9, 10, Lemma 9.4, Lemmas
8.4 and 8.8, Lemma 10.3, the repeated-zero case of §6), from the `P₃` engine
`HBLemma9_1` together with the *certified* entries of Table 8, and from [X]
Lemma 3.8. -/
theorem zeroFreeCert_of_props
    (h9 : HBLemma9_1)
    (hcert : ∀ r ∈ t8certRows,
      cond913 r.2.1 r.2.2.1 r.2.2.2 (Kaff r.2.1) ∧
      p913 r.2.1 r.2.2.1 r.2.2.2 (Kaff r.2.1) < 0)
    (hcertExt : ∀ r ∈ t8certRowsExt,
      cond913 r.2.1 r.2.2.1 r.2.2.2 (Kaff r.2.1) ∧
      p913 r.2.1 r.2.2.1 r.2.2.2 (Kaff r.2.1) < 0)
    (ht1 : HBTheorem1) (hxy : XYLemma3_8) (ht4 : HBTable4)
    (h94 : HBLemma9_4) (ht9 : HBTable9) (h103 : HB10_3_conclusion)
    (ht7 : HBTable7) (h84 : HBLemma8_4) (h88 : HBLemma8_8) (hrzc : HBRepZeroC) :
    ZeroFreeCert := by
  have hc8 := HBTable8_certified_all h9 hcert hcertExt
  have hZ1 : ∀ lamS : ℝ, 0 < lamS → ∃ q₀ : ℕ,
      ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
        IsMin1WideAt 10 χ₁ ρ₁ → Z1 χ₁ ρ₁ := Z1_source ht1
  refine zeroFreeCert_of hZ1 (Z2_source hxy) (Z3_source hc8 ht4 h94 h103 hrzc) ?_ ?_
  · refine fun lamS hS => ?_
    obtain ⟨N, hN⟩ := Z4_source h9 hcert ht4 h94 ht9 h103 ht7 hrzc hxy
    exact ⟨N, fun q hq _ χ₁ ρ₁ hm => hN q hq χ₁ ρ₁ hm⟩
  · refine fun lamS hS => ?_
    obtain ⟨N1, h1⟩ := Z5rows_source hZ1 ht4 ht7 lamS hS
    obtain ⟨N2, h2⟩ := Z5rep_source hZ1 h84 h88 lamS hS
    refine ⟨max N1 N2, fun q hq _ χ₁ ρ₁ hm => ?_⟩
    exact ⟨h1 q (le_trans (le_max_left _ _) hq) χ₁ ρ₁ hm,
      h2 q (le_trans (le_max_right _ _) hq) χ₁ ρ₁ hm⟩

/-- The statement as frozen by the contract subproject: since
`Submission.Work.ZeroFreeTables.Defs` uses the very same `rows15`, `rows14` and
`IsZ`/`Lam0Bound`/… of `Work.LinnikContract`, this is the same `Prop`. -/
theorem linnikContract_ZeroFreeCert_of_props
    (h9 : HBLemma9_1)
    (hcert : ∀ r ∈ t8certRows,
      cond913 r.2.1 r.2.2.1 r.2.2.2 (Kaff r.2.1) ∧
      p913 r.2.1 r.2.2.1 r.2.2.2 (Kaff r.2.1) < 0)
    (hcertExt : ∀ r ∈ t8certRowsExt,
      cond913 r.2.1 r.2.2.1 r.2.2.2 (Kaff r.2.1) ∧
      p913 r.2.1 r.2.2.1 r.2.2.2 (Kaff r.2.1) < 0)
    (ht1 : HBTheorem1) (hxy : XYLemma3_8) (ht4 : HBTable4)
    (h94 : HBLemma9_4) (ht9 : HBTable9) (h103 : HB10_3_conclusion)
    (ht7 : HBTable7) (h84 : HBLemma8_4) (h88 : HBLemma8_8) (hrzc : HBRepZeroC) :
    ZeroFreeCert :=
  zeroFreeCert_of_props h9 hcert hcertExt ht1 hxy ht4 h94 ht9 h103 ht7 h84 h88 hrzc

/-- **AREA 3** in the shape of the frozen contract: `Area1 → ZeroFreeCert`, with
the paper's results as inputs. -/
theorem area3_of_props
    (h9 : HBLemma9_1)
    (hcert : ∀ r ∈ t8certRows,
      cond913 r.2.1 r.2.2.1 r.2.2.2 (Kaff r.2.1) ∧
      p913 r.2.1 r.2.2.1 r.2.2.2 (Kaff r.2.1) < 0)
    (hcertExt : ∀ r ∈ t8certRowsExt,
      cond913 r.2.1 r.2.2.1 r.2.2.2 (Kaff r.2.1) ∧
      p913 r.2.1 r.2.2.1 r.2.2.2 (Kaff r.2.1) < 0)
    (ht1 : HBTheorem1) (hxy : XYLemma3_8) (ht4 : HBTable4)
    (h94 : HBLemma9_4) (ht9 : HBTable9) (h103 : HB10_3_conclusion)
    (ht7 : HBTable7) (h84 : HBLemma8_4) (h88 : HBLemma8_8) (hrzc : HBRepZeroC) :
    Area3 Work.LinnikContract.Area1 :=
  fun _ => linnikContract_ZeroFreeCert_of_props h9 hcert hcertExt ht1 hxy ht4 h94 ht9 h103
    ht7 h84 h88 hrzc


/-! ## The round-2 target

`ZeroFreeCert` above is the *on-axis* form (height-10 wide minimality).  Round 2 numbers `λ₁` over
the wide region `|Im| ≤ 50`, so its `ZeroFreeCert` is obtained by combining the on-axis assembly
with the off-axis input `HBOffAxis`. -/

/-- **The round-2 target**: `Work.LinnikContract2.ZeroFreeCert` from the on-axis assembly and
the off-axis input. -/
theorem linnikContract2_ZeroFreeCert_of_props (hOff : HBOffAxis)
    (h9 : HBLemma9_1)
    (hcert : ∀ r ∈ t8certRows,
      cond913 r.2.1 r.2.2.1 r.2.2.2 (Kaff r.2.1) ∧
      p913 r.2.1 r.2.2.1 r.2.2.2 (Kaff r.2.1) < 0)
    (hcertExt : ∀ r ∈ t8certRowsExt,
      cond913 r.2.1 r.2.2.1 r.2.2.2 (Kaff r.2.1) ∧
      p913 r.2.1 r.2.2.1 r.2.2.2 (Kaff r.2.1) < 0)
    (ht1 : HBTheorem1) (hxy : XYLemma3_8) (ht4 : HBTable4)
    (h94 : HBLemma9_4) (ht9 : HBTable9) (h103 : HB10_3_conclusion)
    (ht7 : HBTable7) (h84 : HBLemma8_4) (h88 : HBLemma8_8) (hrzc : HBRepZeroC) :
    LinnikContract2.ZeroFreeCert := by
  have hOn := zeroFreeCert_of_props h9 hcert hcertExt ht1 hxy ht4 h94 ht9 h103 ht7 h84 h88 hrzc
  intro lamS hS
  obtain ⟨Qa, ha⟩ := hOn lamS hS
  obtain ⟨Qb, hb⟩ := hOff lamS hS
  refine ⟨max Qa Qb, fun q hq _ χ₁ ρ₁ hm => ?_⟩
  by_cases hz : |ρ₁.im| ≤ 1
  · refine ha q (le_trans (le_max_left _ _) hq) χ₁ ρ₁ ?_
    exact IsMin1WideAt_of_isMin1 hm ⟨hm.ne_one, hm.mult_ne_zero, hz⟩
  · exact hb q (le_trans (le_max_right _ _) hq) χ₁ ρ₁ hm (not_le.mp hz)

/-- **AREA 3 (round 2)** in the shape of the frozen contract: `Area1 → ZeroFreeCert`, with
`Area1` (Burgess) as a hypothesis and the paper's results as inputs. -/
theorem linnikContract2_area3_of_props (hOff : HBOffAxis)
    (h9 : HBLemma9_1)
    (hcert : ∀ r ∈ t8certRows,
      cond913 r.2.1 r.2.2.1 r.2.2.2 (Kaff r.2.1) ∧
      p913 r.2.1 r.2.2.1 r.2.2.2 (Kaff r.2.1) < 0)
    (hcertExt : ∀ r ∈ t8certRowsExt,
      cond913 r.2.1 r.2.2.1 r.2.2.2 (Kaff r.2.1) ∧
      p913 r.2.1 r.2.2.1 r.2.2.2 (Kaff r.2.1) < 0)
    (ht1 : HBTheorem1) (hxy : XYLemma3_8) (ht4 : HBTable4)
    (h94 : HBLemma9_4) (ht9 : HBTable9) (h103 : HB10_3_conclusion)
    (ht7 : HBTable7) (h84 : HBLemma8_4) (h88 : HBLemma8_8) (hrzc : HBRepZeroC) :
    LinnikContract2.Area3 :=
  fun _ => linnikContract2_ZeroFreeCert_of_props hOff h9 hcert hcertExt ht1 hxy ht4 h94 ht9 h103
    ht7 h84 h88 hrzc

end Work.ZeroFreeTables