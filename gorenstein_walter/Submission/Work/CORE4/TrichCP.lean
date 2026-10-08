import Mathlib
import Submission.Work.CORE4.Defs27
import Submission.Work.CORE4.EightDichotomyOfTrich

namespace Work.CORE4

open Work.GW2 Subgroup

/-- Design-27 leaf `Work.GW2.C27.TrichCPProp I` (see `CORE4/Defs27.lean`,
`Submission/Work/NOTES_LEAD_gw_design27.md` §3).  Unfolded statement at
`Submission/Work/_design_gw/Core27.lean:394`.

In words: with the §4 (1)–(6) data `C : Case2Ctx6 B` plus `Case2PrePlus`/`Case2SevenFacts`,
`p` prime, `P ≤ C.D.F` of order `p` and `A` the `(p,p)`-subgroup:
`Qsub p B ⊓ C_G(P) ≤ A`.

Proof: `C_G(P) ≤ N_G(P) = C.D.M` (`Work.CORE4.Case2NormalizerP`, whose proof uses only `pre`,
`F_ti`, `F_cyclic` — all present in `Case2Ctx6`; `P ≠ ⊥` from `|P| = p`).  So
`Qsub p B ⊓ C_G(P) ≤ O_p(U) ⊓ C.D.M`, and `F(U) ⊓ M = K₀ ⊔ F` (`SixThree` /
`Case2SixThreeRaw`), with `A = Ω₁(F ⊔ K₀)` (`Work.CORE4.EightAeqOmegaCtx6_c4`, whose hypotheses
are exactly this leaf's).  The elements of `Qsub p B = Ω₁(Z₂(O_p(U)))` are `p`-torsion (the
`Z₂` of a `p`-group has class ≤ 2 and `p` is odd — `p` odd is derivable here), so they lie in
`Ω₁(F ⊔ K₀) = A`.

This is the step the earlier "not derivable" verdicts for `EightTrich9` had missed; the design
proves `eightTrich9_of_leaves` from this leaf plus `TrichCore`/`TrichCs`.  Must be sorry-free:
`#print axioms Work.CORE4.TrichCP` = `[propext, Classical.choice, Quot.sound]`. -/
theorem TrichCP (I : Work.GW2.C4Inputs) : Work.GW2.C27.TrichCPProp I := by
  intro G _ _ hbc B _h2 C _hplus _h7 p P A hp hPF hPcard hObj
  -- `P ≠ ⊥` because `|P| = p` and `p` is prime
  have hPne : P ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hPcard
    exact hp.ne_one hPcard.symm
  -- `p` is odd: `p ∣ |F| ∣ |U|` and `|U|` is odd
  have hpodd : Odd p := by
    have h1 : p ∣ Nat.card ↥C.D.F := by
      rw [← hPcard]; exact Subgroup.card_dvd_of_le hPF
    exact Odd.of_dvd_nat B.U_odd
      (h1.trans (Subgroup.card_dvd_of_le (Case2Data.F_le_U B C.D)))
  -- `N_G(P) = M`
  have hNP : Subgroup.normalizer (P : Set G) = C.D.M :=
    normalizerP_of_ctx6 B C P hPF hPne
  -- `F(U) ⊓ M = K₀ ⊔ F`
  have hSix : Work.GW2.fittingIn B.U ⊓ C.D.M = C.D.K0 ⊔ C.D.F := by
    have h := SixThree I G hbc B C.D C.pre
    simpa [Work.GW2.Case2Data.K0] using h
  -- `A = Ω₁(F ⊔ K₀)`
  have hAeq : A = omega1 p (C.D.F ⊔ C.D.K0) :=
    (EightAeqOmegaCtx6_c4 I G hbc B C p P A hp hPF hPcard hObj).2
  have hAeq' : A = omega1 p (C.D.K0 ⊔ C.D.F) := by rw [hAeq, sup_comm]
  intro x hx
  obtain ⟨hxQ, hxC⟩ := Subgroup.mem_inf.mp hx
  -- `x ∈ O_p(U) ≤ F(U)`
  have hxOp : x ∈ Work.GW2.pCoreIn p B.U :=
    omega1_z2_le_self p (Work.GW2.pCoreIn p B.U) hxQ
  have hxFU : x ∈ Work.GW2.fittingIn B.U := pCoreIn_le_fittingIn_c4 hp B.U hxOp
  -- `x ∈ C_G(P) ≤ N_G(P) = M`
  have hxM : x ∈ C.D.M := by
    rw [← hNP]
    exact Subgroup.centralizer_le_normalizer (P : Set G) hxC
  -- so `x ∈ F(U) ⊓ M = K₀ ⊔ F`
  have hxKF : x ∈ C.D.K0 ⊔ C.D.F := by
    rw [← hSix]
    exact Subgroup.mem_inf.mpr ⟨hxFU, hxM⟩
  -- `x` has order dividing `p`, hence lies in `Ω₁(K₀ ⊔ F) = A`
  have hxpow : x ^ p = 1 := Qsub_pow_eq_one_c4 p B hpodd x hxQ
  have hxOm : x ∈ omega1 p (C.D.K0 ⊔ C.D.F) := Subgroup.subset_closure ⟨hxKF, hxpow⟩
  rw [← hAeq'] at hxOm
  exact hxOm

end Work.CORE4
