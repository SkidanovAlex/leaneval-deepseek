import Mathlib
import Submission.Work.OROneRel.gaugeExtWalkDefs

namespace Work.OROneRel

theorem walkTriv_gNegL {p q : ℕ} (hp : 1 ≤ p) {hq : 1 ≤ q} {Wt : ℤ → FreeGroup (Fin 2)}
    (htree : ∀ i : ℤ, 0 ≤ i → i ≤ Work.OROneRel.npq p q →
      ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0 (Work.OROneRel.wordOf (Wt i)),
        Work.OROneRel.coverEdge e ∈
          Work.OROneRel.winTree Wt (Work.OROneRel.tlW p q) 0 (Work.OROneRel.npq p q))
    (hl : ∀ t : ℤ, Work.OROneRel.lsig (Work.OROneRel.tlW p q) (Work.OROneRel.wordOf (Wt t)) = t) :
    ∀ i : ℤ, i < 0 →
      Work.OROneRel.lsig (Work.OROneRel.tlW p q) (Work.OROneRel.gNegL p q hq Wt i) = i ∧
      Work.OROneRel.walkTriv (Work.OROneRel.gaugeExt p q hq Wt) (Work.OROneRel.tlW p q) 0
        (Work.OROneRel.gNegL p q hq Wt i) := by
  -- Strong induction on the depth `(-i).toNat` of the level below the band.
  have key : ∀ n : ℕ, ∀ i : ℤ, (-i).toNat ≤ n → i < 0 →
      lsig (tlW p q) (gNegL p q hq Wt i) = i ∧
      walkTriv (gaugeExt p q hq Wt) (tlW p q) 0 (gNegL p q hq Wt i) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i hin hineg
      have hqle : (q : ℤ) ≤ npq p q := q_le_npq (p := p) (q := q) hp
      by_cases hsq : 0 ≤ i + (q : ℤ)
      · -- the chain has come back into the band: `gNegL i = wordOf (Wt (i+q)) ++ [a⁻¹]`
        have hg : gNegL p q hq Wt i =
            wordOf (Wt (i + (q : ℤ))) ++ [((0 : Fin 2), false)] := by
          rw [gNegL_eq, if_pos hsq]
        have hsigi : lsig (tlW p q) (wordOf (Wt (i + (q : ℤ)))) = i + (q : ℤ) :=
          hl (i + (q : ℤ))
        rw [hg]
        constructor
        · rw [decor_lsig_append, hsigi, lsig_singleton_false, tlW_zero]
          ring
        · rw [walkTriv_append]
          refine ⟨walkTriv_band hp htree hsq (by omega), ?_⟩
          rw [hsigi, zero_add]
          exact walkTriv_single_zero_false (p := p) (q := q) hp (by rw [tlW_zero]; omega)
      · -- the chain takes a step: `gNegL i = gNegL (i+q) ++ [a⁻¹]`
        have hsqneg : i + (q : ℤ) < 0 := by omega
        have hg : gNegL p q hq Wt i =
            gNegL p q hq Wt (i + (q : ℤ)) ++ [((0 : Fin 2), false)] := by
          rw [gNegL_eq, if_neg hsq]
        have hlt : (-(i + (q : ℤ))).toNat < n := by
          have h2 : 0 < -i := by omega
          have hstep : (-(i + (q : ℤ))).toNat < (-i).toNat := by
            rw [Int.toNat_lt_toNat h2]
            omega
          omega
        obtain ⟨hsigq, htrivq⟩ :=
          ih ((-(i + (q : ℤ))).toNat) hlt (i + (q : ℤ)) le_rfl hsqneg
        rw [hg]
        constructor
        · rw [decor_lsig_append, hsigq, lsig_singleton_false, tlW_zero]
          ring
        · rw [walkTriv_append]
          refine ⟨htrivq, ?_⟩
          rw [hsigq, zero_add]
          exact walkTriv_single_zero_false (p := p) (q := q) hp (by rw [tlW_zero]; omega)
  exact fun i hi => key (-i).toNat i le_rfl hi

end Work.OROneRel
