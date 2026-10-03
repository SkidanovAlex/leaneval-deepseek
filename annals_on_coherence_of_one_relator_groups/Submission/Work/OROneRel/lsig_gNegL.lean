import Mathlib
import Submission.Work.OROneRel.globalGauge

namespace Work.OROneRel

/-- The lower `a`-chain of the global gauge has weight exactly the level: if `Wt` is a gauge on the
band (`lsig (tlW p q) (wordOf (Wt t)) = t` for all `t`), then for every level `i < 0` the chain word
`gNegL i` — built by descending the `a`-edges down to the band — has weight `i`.

The proof is the recursion: at a level `i` with `i + q ≥ 0` the chain is the band word at `i + q`
followed by one `a⁻¹` (weight `(i + q) - q = i`), and otherwise it is the chain at `i + q` followed
by one `a⁻¹`, so the claim follows by strong induction on the depth `(-i).toNat`. -/
theorem lsig_gNegL {p q : ℕ} {hq : 1 ≤ q} {Wt : ℤ → FreeGroup (Fin 2)}
    (hl : ∀ t : ℤ, Work.OROneRel.lsig (Work.OROneRel.tlW p q) (Work.OROneRel.wordOf (Wt t)) = t) :
    ∀ i : ℤ, i < 0 →
      Work.OROneRel.lsig (Work.OROneRel.tlW p q) (Work.OROneRel.gNegL p q hq Wt i) = i := by
  have key : ∀ n : ℕ, ∀ i : ℤ, (-i).toNat ≤ n → i < 0 →
      lsig (tlW p q) (gNegL p q hq Wt i) = i := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i _ hineg
      by_cases hsq : 0 ≤ i + (q : ℤ)
      · -- the chain has come back into the band: `gNegL i = wordOf (Wt (i+q)) ++ [a⁻¹]`
        rw [gNegL_eq, if_pos hsq, decor_lsig_append, hl (i + (q : ℤ)), lsig_singleton_false,
          tlW_zero]
        ring
      · -- the chain takes a step: `gNegL i = gNegL (i+q) ++ [a⁻¹]`
        have hsqneg : i + (q : ℤ) < 0 := by omega
        have hlt : (-(i + (q : ℤ))).toNat < n := by
          have h2 : 0 < -i := by omega
          have hstep : (-(i + (q : ℤ))).toNat < (-i).toNat := by
            rw [Int.toNat_lt_toNat h2]
            omega
          omega
        rw [gNegL_eq, if_neg hsq, decor_lsig_append,
          ih ((-(i + (q : ℤ))).toNat) hlt (i + (q : ℤ)) le_rfl hsqneg,
          lsig_singleton_false, tlW_zero]
        ring
  exact fun i hi => key (-i).toNat i le_rfl hi

end Work.OROneRel
