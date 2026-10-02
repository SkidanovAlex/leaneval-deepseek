/-
# §15 — Case B (`29/50 ≤ λ₁ < 43/40`) via the two-pivot argument

This is the sub-case of the area-7 assembly (round 2) in which the numbered, *wide*
minimiser `(χ₁,ρ₁)` has `λ₁ ≥ 29/50` but `λ(ρ₀) < 43/40`, where `(χ₀,ρ₀)` is a *narrow*
(working-region) minimiser whose parameter is `≥ 695/1000 = 0.695`.

The two pivots are used differently, exactly as in `README.md` §5:

* the **counting** pivot is `λ₁` (via `h58 : 29/50 ≤ λ₁` every column of HB's Table 13 is
  available, so `(D2)` may be applied to *every* row); it is converted to the
  working-region form the round-1 lemmas consume through `table13_col_le` and the wide
  minimality `hwide`;
* the **decay** pivot is `λ* = λ(ρ₀) ≥ 695/1000`, supplied by the narrow minimiser `hnarrow`.

Everything else is round 1's §15 machinery (`Work.A7.sec15_step`/`core15`, the numeric
certificates of `sec15_num`, and the `Z3` clauses transferred where necessary); the only
new ingredient is the derivation of the third clause `Lam3Bound χ₀ (107/125)` for the
*narrow* pair from the *wide* pair's `Lam3Bound χ₁ (107/125)` — valid because a narrow zero
of parameter `< 107/125` would have to belong to one of the wide pair's two exceptional
conjugate pairs.
-/
import Mathlib
import Submission.Work.LinnikContract2.Defs
import Submission.Work.LinnikContract2.API
import Submission.Work.LinnikContract2.Areas
import Submission.Work.LinnikContract2.Bridge
import Submission.Work.LinnikContract2.Numbering
import Submission.Work.LinnikContract2.A7.table13_col_le
import Submission.Work.A7.sec15_uniform
import Submission.Work.A7.sec14_uniform
import Submission.Work.LinnikAreas.A7.WBox
import Submission.Work.LinnikAreas.A7.Basic7

set_option maxHeartbeats 4000000

namespace Work.LinnikContract2.A7

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

/-- **`Lam3Bound` transfers along an equality of the two exceptional pairs.**  This is the
bookkeeping step of the §15 argument in Case B: the wide pair's `Z3`-clause
`Lam3Bound χ₁ (107/125)` transfers to the narrow member `χ₀` whenever the narrow parameter
`< 107/125` forces `χ₀` into the wide pair's exceptional set. -/
private lemma lam3Bound_transfer {q : ℕ} [NeZero q] {χ₀ χ₁ χ₂ : DirichletCharacter ℂ q} {c : ℝ}
    (hmem : χ₀ = χ₁ ∨ χ₀ = χ₁⁻¹ ∨ χ₀ = χ₂ ∨ χ₀ = χ₂⁻¹)
    (H : ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), Work.LinnikContract.IsZ χ ρ →
      χ ≠ χ₁ → χ ≠ χ₁⁻¹ → χ ≠ χ₂ → χ ≠ χ₂⁻¹ → c ≤ Work.LinnikContract.lamOf q ρ) :
    ∃ χ₂' : DirichletCharacter ℂ q, ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ),
      Work.LinnikContract.IsZ χ ρ → χ ≠ χ₀ → χ ≠ χ₀⁻¹ → χ ≠ χ₂' → χ ≠ χ₂'⁻¹ →
        c ≤ Work.LinnikContract.lamOf q ρ := by
  rcases hmem with h | h | h | h
  · -- `χ₀ = χ₁`: the exceptional pairs coincide, so keep `χ₂`
    refine ⟨χ₂, fun χ ρ hZ hn0 hn1 hn2 hn3 => H χ ρ hZ ?_ ?_ hn2 hn3⟩
    · intro hh; exact hn0 (hh.trans h.symm)
    · intro hh; exact hn1 (hh.trans (congrArg Inv.inv h).symm)
  · -- `χ₀ = χ₁⁻¹`: the exceptional pairs coincide, with the roles swapped
    have hinv : χ₀⁻¹ = χ₁ := by rw [h, inv_inv]
    refine ⟨χ₂, fun χ ρ hZ hn0 hn1 hn2 hn3 => H χ ρ hZ ?_ ?_ hn2 hn3⟩
    · intro hh; exact hn1 (hh.trans hinv.symm)
    · intro hh; exact hn0 (hh.trans h.symm)
  · -- `χ₀ = χ₂`: swap the two exceptional pairs, so take `χ₁`
    refine ⟨χ₁, fun χ ρ hZ hn0 hn1 hn2 hn3 => H χ ρ hZ hn2 hn3 ?_ ?_⟩
    · intro hh; exact hn0 (hh.trans h.symm)
    · intro hh; exact hn1 (hh.trans (congrArg Inv.inv h).symm)
  · -- `χ₀ = χ₂⁻¹`: swap the pairs, with the roles of `χ₂,χ₂⁻¹` exchanged
    have hinv : χ₀⁻¹ = χ₂ := by rw [h, inv_inv]
    refine ⟨χ₁, fun χ ρ hZ hn0 hn1 hn2 hn3 => H χ ρ hZ hn2 hn3 ?_ ?_⟩
    · intro hh; exact hn1 (hh.trans hinv.symm)
    · intro hh; exact hn0 (hh.trans h.symm)

theorem sec15_caseB {q : ℕ} [NeZero q] (hq : 2 ≤ q) {R η εw : ℝ}
    {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} {χ₀ : DirichletCharacter ℂ q} {ρ₀ : ℂ}
    (hR : 0 < R) (hRlog : R ≤ Real.log q) (hRmax : R ≤ Work.LinnikContract2.lamMax q)
    (hη : 0 ≤ η) (hεw : 0 ≤ εw) (hεw1 : εw ≤ 1/1000)
    (hwide : Work.LinnikContract2.IsMin1 χ₁ ρ₁) (hZ3 : Work.LinnikContract2.Z3 χ₁ ρ₁)
    (hnarrow : Work.LinnikContract2.IsMin1N χ₀ ρ₀)
    (h695 : (695:ℝ)/1000 ≤ Work.LinnikContract2.lamOf q ρ₀)
    (h58 : (29:ℝ)/50 ≤ Work.LinnikContract2.lamOf q ρ₁)
    (hS : Finset (DirichletCharacter ℂ q))
    (hSiff : ∀ χ : DirichletCharacter ℂ q, χ ∈ hS ↔ ∃ ρ : ℂ, Work.LinnikContract2.IsZ χ ρ ∧ Work.LinnikContract2.lamOf q ρ ≤ Work.LinnikContract2.lamMax q)
    (hD1 : ∑ χ ∈ hS, Work.LinnikContract2.wHB (Work.LinnikContract2.lamChar χ) ≤ (67:ℝ)/6 + εw)
    (hPC : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ lam' : ℝ, 0 ≤ lam' → lam' ≤ R →
        (∀ ρ : ℂ, Work.LinnikContract2.IsZ χ ρ → lam' ≤ Work.LinnikContract2.lamOf q ρ) →
        Work.LinnikContract2.boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (Work.LinnikContract2.Bfun ((3:ℝ)/10) lam' + η))
    (hD2 : ∀ e ∈ Work.LinnikContract2.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), Work.LinnikContract2.IsZW χ ρ → e.2.1 ≤ Work.LinnikContract2.lamOf q ρ) →
        Work.LinnikContract2.Ncount q e.1 ≤ e.2.2) :
    ∑ χ ∈ Work.LinnikAreas.A7.Aset q R, Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ
      ≤ ((9:ℝ)/100) * ((9968:ℝ)/10000) + ((9:ℝ)/100) * η * 1000 := by
  classical
  -- ### Bookkeeping: round-1 forms of the hypotheses
  have hminN : Work.LinnikContract.IsMin1 χ₀ ρ₀ := hnarrow
  have h695' : (695:ℝ)/1000 ≤ Work.LinnikContract.lamOf q ρ₀ := h695
  have h58' : (29:ℝ)/50 ≤ Work.LinnikContract.lamOf q ρ₁ := h58
  have hSiff' : ∀ χ : DirichletCharacter ℂ q, χ ∈ hS ↔
      ∃ ρ : ℂ, Work.LinnikContract.IsZ χ ρ ∧ Work.LinnikContract.lamOf q ρ ≤ Work.LinnikContract.lamMax q :=
    hSiff
  have hD1' : ∑ χ ∈ hS, Work.LinnikContract.wHB (Work.LinnikContract.lamChar χ) ≤ (67:ℝ)/6 + εw := hD1
  have hPC' : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ lam' : ℝ, 0 ≤ lam' → lam' ≤ R →
      (∀ ρ : ℂ, Work.LinnikContract.IsZ χ ρ → lam' ≤ Work.LinnikContract.lamOf q ρ) →
      Work.LinnikContract.boxAbs q ((3:ℝ)/10) R χ ≤
        ((9:ℝ)/100) * (Work.LinnikContract.Bfun ((3:ℝ)/10) lam' + η) :=
    fun χ hχ lam' h0 hle hsec => hPC χ hχ lam' h0 hle hsec
  -- ### the `Z3` clauses of the wide pair, in rational-literal form
  have hZ3' : Work.LinnikContract.Lam0Bound χ₁ ρ₁ ((695:ℝ)/1000) ∧
      Work.LinnikContract.Lam2Bound χ₁ ((701:ℝ)/1000) ∧
      Work.LinnikContract.Lam3Bound χ₁ ((107:ℝ)/125) := by
    unfold Work.LinnikContract2.Z3 at hZ3
    have h1 : (0.695 : ℝ) = (695:ℝ)/1000 := by norm_num
    have h2 : (0.701 : ℝ) = (701:ℝ)/1000 := by norm_num
    have h3 : (0.856 : ℝ) = (107:ℝ)/125 := by norm_num
    rw [h1, h2, h3] at hZ3
    exact hZ3
  -- ### the working-region form of `(D2)`: the counting pivot `λ₁ ≥ 29/50` opens every column
  have hD2' : ∀ e ∈ Work.LinnikContract.table13,
      (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), Work.LinnikContract.IsZ χ ρ →
        e.2.1 ≤ Work.LinnikContract.lamOf q ρ) →
      Work.LinnikContract.Ncount q e.1 ≤ e.2.2 := by
    intro e he _
    refine hD2 e he (fun χ ρ hZW => ?_)
    have hcol0 := Work.LinnikContract2.A7.table13_col_le e he
    have hcol : e.2.1 ≤ (29:ℝ)/50 := by
      have hc : (58:ℝ)/100 = (29:ℝ)/50 := by norm_num
      linarith
    exact le_trans hcol (le_trans h58' (hwide.le_lamOf hZW))
  -- ### the narrow parameter
  have hp0 : 0 < Work.LinnikContract.lamOf q ρ₀ := lt_of_lt_of_le (by norm_num) h695'
  have h348 : (348:ℝ)/1000 ≤ Work.LinnikContract.lamOf q ρ₀ :=
    le_trans (by norm_num) h695'
  -- ### Case `λ(ρ₀) ≥ 43/40`: the crude global bound, with the narrow pair as pivot
  by_cases h43 : (43:ℝ)/40 ≤ Work.LinnikContract.lamOf q ρ₀
  · exact Work.A7.sec15_crude (q := q) (R := R) (η := η) (εw := εw)
      (lam₁ := Work.LinnikContract.lamOf q ρ₀) (χ₁ := χ₀) (ρ₁ := ρ₀)
      hq hR hRlog hRmax hη hεw hεw1 hminN rfl h43 hS hSiff' hD1' hPC'
  · -- ### Case `λ(ρ₀) < 43/40`
    have hlt43 : Work.LinnikContract.lamOf q ρ₀ < (43:ℝ)/40 := lt_of_not_ge h43
    by_cases h78 : (7:ℝ)/8 ≤ Work.LinnikContract.lamOf q ρ₀
    · -- ## `7/8 ≤ λ(ρ₀) < 43/40`: the `u4`-branches, whose clauses come from minimality
      by_cases h910 : (9:ℝ)/10 ≤ Work.LinnikContract.lamOf q ρ₀
      · by_cases h3740 : (37:ℝ)/40 ≤ Work.LinnikContract.lamOf q ρ₀
        · by_cases h1920 : (19:ℝ)/20 ≤ Work.LinnikContract.lamOf q ρ₀
          · by_cases h3940 : (39:ℝ)/40 ≤ Work.LinnikContract.lamOf q ρ₀
            · by_cases h11 : (1:ℝ)/1 ≤ Work.LinnikContract.lamOf q ρ₀
              · by_cases h4140 : (41:ℝ)/40 ≤ Work.LinnikContract.lamOf q ρ₀
                · by_cases h2120 : (21:ℝ)/20 ≤ Work.LinnikContract.lamOf q ρ₀
                  · exact Work.A7.cfg_u4_8 (q := q) (R := R) (η := η) (εw := εw)
                      (lam₁ := Work.LinnikContract.lamOf q ρ₀) (χ₁ := χ₀) (ρ₁ := ρ₀)
                      hq hR hRlog hRmax hη hεw hεw1 hminN rfl h2120 hlt43.le
                      hS hSiff' hD1' hPC' hD2'
                  · exact Work.A7.cfg_u4_9 (q := q) (R := R) (η := η) (εw := εw)
                      (lam₁ := Work.LinnikContract.lamOf q ρ₀) (χ₁ := χ₀) (ρ₁ := ρ₀)
                      hq hR hRlog hRmax hη hεw hεw1 hminN rfl h4140 (le_of_lt (lt_of_not_ge h2120))
                      hS hSiff' hD1' hPC' hD2'
                · exact Work.A7.cfg_u4_10 (q := q) (R := R) (η := η) (εw := εw)
                    (lam₁ := Work.LinnikContract.lamOf q ρ₀) (χ₁ := χ₀) (ρ₁ := ρ₀)
                    hq hR hRlog hRmax hη hεw hεw1 hminN rfl h11 (le_of_lt (lt_of_not_ge h4140))
                    hS hSiff' hD1' hPC' hD2'
              · exact Work.A7.cfg_u4_11 (q := q) (R := R) (η := η) (εw := εw)
                  (lam₁ := Work.LinnikContract.lamOf q ρ₀) (χ₁ := χ₀) (ρ₁ := ρ₀)
                  hq hR hRlog hRmax hη hεw hεw1 hminN rfl h3940 (le_of_lt (lt_of_not_ge h11))
                  hS hSiff' hD1' hPC' hD2'
            · exact Work.A7.cfg_u4_12 (q := q) (R := R) (η := η) (εw := εw)
                (lam₁ := Work.LinnikContract.lamOf q ρ₀) (χ₁ := χ₀) (ρ₁ := ρ₀)
                hq hR hRlog hRmax hη hεw hεw1 hminN rfl h1920 (le_of_lt (lt_of_not_ge h3940))
                hS hSiff' hD1' hPC' hD2'
          · exact Work.A7.cfg_u4_13 (q := q) (R := R) (η := η) (εw := εw)
              (lam₁ := Work.LinnikContract.lamOf q ρ₀) (χ₁ := χ₀) (ρ₁ := ρ₀)
              hq hR hRlog hRmax hη hεw hεw1 hminN rfl h3740 (le_of_lt (lt_of_not_ge h1920))
              hS hSiff' hD1' hPC' hD2'
        · exact Work.A7.cfg_u4_14 (q := q) (R := R) (η := η) (εw := εw)
            (lam₁ := Work.LinnikContract.lamOf q ρ₀) (χ₁ := χ₀) (ρ₁ := ρ₀)
            hq hR hRlog hRmax hη hεw hεw1 hminN rfl h910 (le_of_lt (lt_of_not_ge h3740))
            hS hSiff' hD1' hPC' hD2'
      · exact Work.A7.cfg_u4_15 (q := q) (R := R) (η := η) (εw := εw)
          (lam₁ := Work.LinnikContract.lamOf q ρ₀) (χ₁ := χ₀) (ρ₁ := ρ₀)
          hq hR hRlog hRmax hη hεw hεw1 hminN rfl h78 (le_of_lt (lt_of_not_ge h910))
          hS hSiff' hD1' hPC' hD2'
    · -- ## `139/200 ≤ λ(ρ₀) < 7/8`: the §15 core at the narrow pivot
      have hlt78 : Work.LinnikContract.lamOf q ρ₀ < (7:ℝ)/8 := lt_of_not_ge h78
      -- the third clause for the *narrow* pair, transferred from the wide pair
      have hL3 : Work.LinnikContract.Lam3Bound χ₀ ((107:ℝ)/125) := by
        by_cases hge : ((107:ℝ)/125) ≤ Work.LinnikContract.lamOf q ρ₀
        · refine ⟨χ₀, fun χ ρ hZ _ _ _ _ => le_trans hge (hminN.2 χ ρ hZ)⟩
        · obtain ⟨χ₂, hχ₂⟩ := hZ3'.2.2
          have hlt : Work.LinnikContract.lamOf q ρ₀ < (107:ℝ)/125 := lt_of_not_ge hge
          have hmem : χ₀ = χ₁ ∨ χ₀ = χ₁⁻¹ ∨ χ₀ = χ₂ ∨ χ₀ = χ₂⁻¹ := by
            by_contra hc
            push Not at hc
            have h := hχ₂ χ₀ ρ₀ hminN.1 hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
            linarith
          exact lam3Bound_transfer hmem hχ₂
      -- the second clause for the narrow pair comes from minimality alone
      have hLam2 : Work.LinnikContract.Lam2Bound χ₀ (Work.LinnikContract.lamOf q ρ₀) :=
        fun χ ρ hZ _ _ => hminN.2 χ ρ hZ
      have hLam0 : Work.LinnikContract.Lam0Bound χ₀ ρ₀ (Work.LinnikContract.lamOf q ρ₀) :=
        ⟨fun _ => le_rfl, fun ρ hZ _ _ => hminN.2 χ₀ ρ hZ⟩
      have hΛ : (0:ℝ) < (51:ℝ)/40 := by norm_num
      have hlam1Λ : Work.LinnikContract.lamOf q ρ₀ ≤ (51:ℝ)/40 := by linarith
      have h139 : (139:ℝ)/200 ≤ Work.LinnikContract.lamOf q ρ₀ := by
        have hc : (139:ℝ)/200 = (695:ℝ)/1000 := by norm_num
        rw [hc]; exact h695'
      have hrowB : Work.LinnikAreas.A7.Cf ((51:ℝ)/40) (Work.LinnikContract.lamOf q ρ₀)
          ≤ ((100147:ℝ)/2000000) :=
        le_trans (Work.A7.Cf_antitone (fun {x y} hx hxy => Work.A7.PhiWf_antitone hx hxy)
          hΛ (by norm_num : (0:ℝ) < 139/200) h139) Work.A7.cred_u3.2.2
      have hcard := Work.A7.card_S1_le_two (q := q) (χ₁ := χ₀) (R := R)
      have hpt1 (hA : χ₀ ∈ Work.LinnikAreas.A7.Aset q R) :
          Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ₀
            ≤ ((9:ℝ)/100) * (((100147:ℝ)/2000000)
                + (Work.LinnikAreas.A7.Phi ((51:ℝ)/40) / Work.LinnikAreas.A7.Wf ((51:ℝ)/40))
                  * Work.LinnikContract.wHB (Work.LinnikContract.lamOf q ρ₀) + η) := by
        have hlam1R : Work.LinnikContract.lamOf q ρ₀ ≤ R := by
          rw [← Work.A7.lamChar_eq_of_isMin1 hq hminN rfl]
          exact Work.A7.lamChar_le_R_of_mem_Aset hq hRlog hA
        refine Work.A7.S1_plain (c := 0) hΛ hη hp0 hlam1Λ ?_
          (hPC' χ₀ hminN.1.1 (Work.LinnikContract.lamOf q ρ₀) hp0.le hlam1R
            (fun ρ hZ => hminN.2 χ₀ ρ hZ)) hrowB (by norm_num)
        intro ρ' hb' hz'
        exact hminN.2 χ₀ ρ' (Work.A7.box_api7_p1 hq hRlog hminN.1.1 hz' hb')
      have hpt2 (hA : χ₀⁻¹ ∈ Work.LinnikAreas.A7.Aset q R) :
          Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ₀⁻¹
            ≤ ((9:ℝ)/100) * (((100147:ℝ)/2000000)
                + (Work.LinnikAreas.A7.Phi ((51:ℝ)/40) / Work.LinnikAreas.A7.Wf ((51:ℝ)/40))
                  * Work.LinnikContract.wHB (Work.LinnikContract.lamOf q ρ₀) + η) := by
        have hlam1R : Work.LinnikContract.lamOf q ρ₀ ≤ R := by
          rw [← Work.A7.lamChar_inv_eq hq hminN rfl]
          exact Work.A7.lamChar_le_R_of_mem_Aset hq hRlog hA
        have hne : χ₀⁻¹ ≠ 1 := fun h => hminN.1.1 (inv_eq_one.mp h)
        refine Work.A7.S1_plain (c := 0) hΛ hη hp0 hlam1Λ ?_
          (hPC' χ₀⁻¹ hne (Work.LinnikContract.lamOf q ρ₀) hp0.le hlam1R
            (fun ρ hZ => hminN.2 χ₀⁻¹ ρ hZ)) hrowB (by norm_num)
        intro ρ' hb' hz'
        exact hminN.2 χ₀⁻¹ ρ' (Work.A7.box_api7_p1 hq hRlog hne hz' hb')
      have hS1point : ∀ χ ∈ ({χ₀, χ₀⁻¹} : Finset (DirichletCharacter ℂ q)) ∩ Work.LinnikAreas.A7.Aset q R,
          Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ
            ≤ ((9:ℝ)/100) * (((100147:ℝ)/2000000)
                + (Work.LinnikAreas.A7.Phi ((51:ℝ)/40) / Work.LinnikAreas.A7.Wf ((51:ℝ)/40))
                  * Work.LinnikContract.wHB (Work.LinnikContract.lamOf q ρ₀) + η) := by
        intro χ hχ
        obtain ⟨hχp, hχA⟩ := Finset.mem_inter.mp hχ
        rcases Finset.mem_insert.mp hχp with h | h
        · rw [h]; exact hpt1 (h ▸ hχA)
        · rw [Finset.mem_singleton.mp h]; exact hpt2 (Finset.mem_singleton.mp h ▸ hχA)
      have hle3 : min ((107:ℝ)/125) ((51:ℝ)/40)
          ≤ (51:ℝ)/40 - (25:ℝ)/1000 * ((16:ℕ):ℝ) := by norm_num
      have hlam1small : Work.LinnikContract.lamOf q ρ₀
          ≤ (51:ℝ)/40 - (25:ℝ)/1000 * ((16:ℕ):ℝ) := by
        have : (51:ℝ)/40 - (25:ℝ)/1000 * ((16:ℕ):ℝ) = (7:ℝ)/8 := by norm_num
        rw [this]; exact hlt78.le
      have hcred : Work.LinnikAreas.A7.Cf ((51:ℝ)/40) (min ((107:ℝ)/125) ((51:ℝ)/40))
          ≤ ((100147:ℝ)/2000000) := by
        rw [show min ((107:ℝ)/125) ((51:ℝ)/40) = ((107:ℝ)/125) from by norm_num]
        exact Work.A7.cred_u3.1
      have hTOT : (Work.LinnikAreas.A7.Phi ((51:ℝ)/40) / Work.LinnikAreas.A7.Wf ((51:ℝ)/40))
            * ((67:ℝ)/6 + εw)
          + ((2:ℕ):ℝ) * ((100147:ℝ)/2000000) + 2 * ((100147:ℝ)/2000000)
          + max 0 ((Work.A7.Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] 16 : ℝ) - ((2:ℕ):ℝ) - 2)
              * Work.LinnikAreas.A7.Cf ((51:ℝ)/40) (min ((107:ℝ)/125) ((51:ℝ)/40))
          + ∑ j ∈ Finset.range 16,
              ((Work.A7.Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] j : ℝ)
                - (Work.A7.Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] (j+1) : ℝ))
              * Work.LinnikAreas.A7.Cf ((51:ℝ)/40) (((51:ℝ)/40) - (25:ℝ)/1000 * ((j:ℝ)+1))
          ≤ ((9968:ℝ)/10000) := by
        simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using Work.A7.total_u3 hεw hεw1
      have hETA : (Real.exp (-(Work.LinnikAreas.A7.ac * ((51:ℝ)/40))) / Work.LinnikAreas.A7.Wf ((51:ℝ)/40))
            * ((67:ℝ)/6 + εw)
          + (Work.A7.Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] 0 : ℝ)
          + 4 ≤ 1000 := Work.A7.etab_u3 hεw hεw1
      have hcount := Work.A7.hcount_u3 (q := q) (χ₁ := χ₀) (ρ₁ := ρ₀)
        (lam₁ := Work.LinnikContract.lamOf q ρ₀) hminN rfl
        (le_trans (by norm_num : (29:ℝ)/50 ≤ 695/1000) h695') hD2'
      exact Work.A7.sec15_step (q := q) (R := R) (Λ := (51:ℝ)/40) (η := η) (εw := εw)
        (lam₁ := Work.LinnikContract.lamOf q ρ₀)
        (CST1 := (100147:ℝ)/2000000) (CST2 := (100147:ℝ)/2000000)
        (TOTAL := (9968:ℝ)/10000) (ETAB := 1000)
        (s := 16) (N := fun j => Work.A7.Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] j)
        (n₁ := 2) (c₀ := Work.LinnikContract.lamOf q ρ₀)
        (l₂ := Work.LinnikContract.lamOf q ρ₀) (l₃ := (107:ℝ)/125)
        (χ₁ := χ₀) (ρ₁ := ρ₀)
        hq hR hRlog hRmax hΛ hη hp0 hp0 hminN rfl h348 hlam1Λ le_rfl hLam0 hLam2 hL3
        (by simpa using hcard) hS1point hS hSiff' hD1' hPC' hcount hle3 hlam1small
        hcred (by norm_num) hrowB hTOT hETA

end

end Work.LinnikContract2.A7
