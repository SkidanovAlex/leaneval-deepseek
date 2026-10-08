import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2EightObjExists
import Submission.Work.CORE4.Case2K1_ne_bot
import Submission.Work.CORE4.S0CentUO2
import Submission.Work.CORE4.Case2EightDisjOfCtx
import Submission.Work.CORE4.EightIdxDefs
import Submission.Work.CORE4.Case2SevenRemainingOfCtx
import Submission.Work.CORE4.SevenX.piFU_le_pi_K0F
import Submission.Work.CORE4.Case2SevenAux
import Submission.Work.CORE4.SevenFactsOfCtx
import Submission.Work.CORE4.Case2Numeric
import Submission.Work.CORE4.Case2EightA_le_FsupK0
import Submission.Work.CORE4.Case2EightQfacts
import Submission.Work.CORE4.E2Z2le
import Submission.Work.CORE4.ConjSubOrbitNcard
import Submission.Work.CORE4.ncard_subgroups_prime_cube
import Submission.Work.CORE4.EightAnormalPcore_of_Qpos
import Submission.Work.CORE4.EightAnormalFitting_of_pcore

namespace Work.CORE4

open Subgroup

set_option linter.style.haveILetI false

/-! ## The centre of `Q` is invariant under `N_G(Q)` -/

/-- `Z(Q)` is invariant under conjugation by any element of `N_G(Q)`: an element `z ∈ Q` commutes
with all of `Q` if and only if `g z g⁻¹` does. -/
theorem conjSub_centerIn_of_mem_normalizer {G : Type} [Group G] {Q : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) :
    Work.GW2.conjSub g (Work.CORE4.centerIn Q) = Work.CORE4.centerIn Q := by
  have hginv : g⁻¹ ∈ Subgroup.normalizer (Q : Set G) := (Subgroup.normalizer (Q : Set G)).inv_mem hg
  have key : ∀ z : G, z ∈ Work.CORE4.centerIn Q ↔ g * z * g⁻¹ ∈ Work.CORE4.centerIn Q := by
    intro z
    rw [Work.CORE4.mem_centerIn_iff, Work.CORE4.mem_centerIn_iff]
    constructor
    · rintro ⟨hzQ, hzc⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp hg z).mp hzQ, fun y hy => ?_⟩
      have hy' : g⁻¹ * y * g ∈ Q := by
        simpa using (Subgroup.mem_normalizer_iff.mp hginv y).mp hy
      have h2 := hzc (g⁻¹ * y * g) hy'
      have h4 := congrArg (fun t => g * t * g⁻¹) h2
      rw [show g * (z * (g⁻¹ * y * g)) * g⁻¹ = (g * z * g⁻¹) * y from by group,
          show g * ((g⁻¹ * y * g) * z) * g⁻¹ = y * (g * z * g⁻¹) from by group] at h4
      exact h4
    · rintro ⟨hzQ, hzc⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp hg z).mpr hzQ, fun y hy => ?_⟩
      have hy' : g * y * g⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hg y).mp hy
      have h2 := hzc (g * y * g⁻¹) hy'
      have h4 := congrArg (fun t => g⁻¹ * t * g) h2
      rw [show g⁻¹ * ((g * z * g⁻¹) * (g * y * g⁻¹)) * g = z * y from by group,
          show g⁻¹ * ((g * y * g⁻¹) * (g * z * g⁻¹)) * g = y * z from by group] at h4
      exact h4
  ext x
  rw [Work.GW2.conjSub, Subgroup.mem_map]
  constructor
  · rintro ⟨w, hw, hwx⟩
    rw [← hwx]
    exact (key w).mp hw
  · intro hx
    refine ⟨g⁻¹ * x * g, (key _).mpr ?_, ?_⟩
    · show g * (g⁻¹ * x * g) * g⁻¹ ∈ Work.CORE4.centerIn Q
      rw [show g * (g⁻¹ * x * g) * g⁻¹ = x from by group]
      exact hx
    · show (MulAut.conj g) (g⁻¹ * x * g) = x
      rw [MulAut.conj_apply]
      group

variable {G : Type} [Group G] [Finite G]

/-! ## The target -/

/-- Bender 1981, §4 (8) (p. 226), cases 1–2 of the `Q = Ω₁(Z₂(O_p(U)))` trichotomy, at the
`Case2Ctx` level: for Bender's `(p,p)`-subgroup `A` (the `Case2EightObj` for the given `P ≤ F` of
order `p`) one has

* `u = |U : N_U(A)| ≤ p`,
* `A ⊴ F(U)`,
* `3 ≤ p₀ = |N_U(A) : N_U(P)|` whenever `U ⊄ M`.

These are exactly the three conjuncts of the second branch of `Case2EightFacts`.

The proof is the §4 (8) case analysis:

* the position of `A` in `Q := Ω₁(Z₂(O_p(U)))` (Bender's trichotomy, cases 1 and 2, the third case
  `s` inverts `Q` being excluded by `¬ Case2InvNormal`) gives `A ≤ Q`: `Work.CORE4.EightQposCtx.QposOfCtx`;
* hence `A ⊴ O_p(U)` (`EightAnormalPcore_of_Qpos`, via `[Q, O_p(U)] ≤ Z(Q) ≤ A`) and then
  `A ⊴ F(U)` (`EightAnormalFitting_of_pcore`);
* `u` is the number of `U`-conjugates of `A` (`ConjSubOrbitNcard`), all of which are subgroups of
  `Q` of order `p ^ 2` containing `Z(Q)`; if `A = Q` then `Q ⊴ U` forces `u = 1`, and otherwise
  `|Q : A| = p` makes the number of such subgroups `p + 1` (`ncard_subgroups_prime_cube`), so
  `u ≤ p + 1`, and `u` is odd, whence `u ≤ p`;
* the third conjunct is `three_le_p0_of_not_invNormal`. -/

theorem Case2EightCasesOfCtx (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B),
        ¬ Work.GW2.Case2InvNormal B h.D →
        ∀ (p : ℕ) (P A : Subgroup G), p.Prime → P ≤ h.D.F → Nat.card P = p →
          Work.GW2.Case2EightObj h.D p P A →
          Work.GW2.Case2EightU B A ≤ p ∧
          (A.subgroupOf (Work.GW2.fittingIn B.U)).Normal ∧
          (¬ B.U ≤ h.D.M → 3 ≤ Work.GW2.Case2EightP0 B P A) := by
  intro G _ _ hbc B h hInv p P A hp hPF hPcard hObj
  classical
  -- §4 (7) and (1)–(2) at this level
  have h7 : Work.GW2.Case2SevenFacts B h.D := Work.CORE4.Case2SevenFacts_of_ctx I G hbc B h
  let h6 : Work.GW2.Case2Ctx6 B := Work.CORE4.Case2Ctx.toCtx6 h
  have h2 : Work.GW2.Case2 B := Work.CORE4.Case2Ctx.toCase2 h
  have hplus : Work.GW2.Case2PrePlus B h.D := Work.CORE4.Case2PrePlusOfCtx G I hbc B h
  have hAcard : Nat.card ↥A = p ^ 2 := hObj.2.2.2.2.1
  -- the `Q`-facts of §4 (8)
  obtain ⟨hQ_le_FU, hUnormQ, hQexp, hQnc⟩ :=
    Work.CORE4.Case2EightQfacts I G hbc B h2 h6 hplus h7 p P A hp hPF hPcard hObj
  -- the position of `A` in `Q` (Bender's trichotomy, cases 1–2)
  have hpos : A ≤ Work.CORE4.Qsub p B ∧
      (A = Work.CORE4.Qsub p B ∨
        (Work.CORE4.centerIn (Work.CORE4.Qsub p B) < A ∧
          A.relIndex (Work.CORE4.Qsub p B) = p)) := by
    sorry
  obtain ⟨hAQ, hpos'⟩ := hpos
  -- `A ⊴ O_p(U)`
  have hAnOp : (A.subgroupOf (Work.GW2.pCoreIn p B.U)).Normal :=
    Work.CORE4.EightAnormalPcore_of_Qpos p hp A hAQ
      (hpos'.elim Or.inl fun hh => Or.inr hh.1)
  have hAleOp : A ≤ Work.GW2.pCoreIn p B.U :=
    hAQ.trans (Work.CORE4.omega1_z2_le_self p _)
  -- `A ≤ F(U)`
  have hAleFU : A ≤ Work.GW2.fittingIn B.U :=
    (Work.CORE4.Case2EightA_le_FsupK0 I G hbc B h2 h6 hplus h7 p P A hp hPF hPcard hObj).trans
      (sup_le (Work.GW2.Case2Data.F_le_fitting B h.D) inf_le_left)
  have hAp : IsPGroup p ↥A := IsPGroup.of_card (n := 2) hAcard
  -- `A ⊴ F(U)`
  have hAnF : (A.subgroupOf (Work.GW2.fittingIn B.U)).Normal :=
    Work.CORE4.EightAnormalFitting_of_pcore (B := B) p hp A hAleFU hAp hAleOp hAnOp
  refine ⟨?_, hAnF, ?_⟩
  · -- `u ≤ p`
    have hu_eq : Work.GW2.Case2EightU B A =
        {X : Subgroup G | ∃ g : G, g ∈ B.U ∧ X = Work.GW2.conjSub g A}.ncard :=
      (Work.CORE4.ConjSubOrbitNcard B.U A).symm
    rw [hu_eq]
    have hodd : Odd {X : Subgroup G | ∃ g : G, g ∈ B.U ∧ X = Work.GW2.conjSub g A}.ncard := by
      rw [← hu_eq]
      exact Odd.of_dvd_nat B.U_odd (Subgroup.relIndex_dvd_card _ _)
    have hpodd : Odd p := by
      have h1 : p ∣ Nat.card ↥h.D.F := by
        rw [← hPcard]; exact Subgroup.card_dvd_of_le hPF
      exact Odd.of_dvd_nat B.U_odd (h1.trans (Subgroup.card_dvd_of_le (h.D.F_le_U B)))
    rcases hpos' with hAeq | ⟨hZlt, hrel⟩
    · -- case 1: `A = Q`, and `Q ⊴ U`, so `u = 1`
      have hcard1 : {X : Subgroup G | ∃ g : G, g ∈ B.U ∧ X = Work.GW2.conjSub g A}.ncard = 1 := by
        rw [← hu_eq, hAeq, Work.GW2.Case2EightU, inf_eq_left.mpr hUnormQ,
          Subgroup.relIndex_self]
      rw [hcard1]
      exact hp.one_le
    · -- case 2: `Z(Q) < A < Q`, `|Q : A| = p`
      -- `|Q| = p ^ 3`
      have hQcard : Nat.card ↥(Work.CORE4.Qsub p B) = p ^ 3 := by
        have h1 : Nat.card ↥(A.subgroupOf (Work.CORE4.Qsub p B)) *
            (A.subgroupOf (Work.CORE4.Qsub p B)).index = Nat.card ↥(Work.CORE4.Qsub p B) :=
          Subgroup.card_mul_index _
        have h2 : Nat.card ↥(A.subgroupOf (Work.CORE4.Qsub p B)) = p ^ 2 := by
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAQ).toEquiv, hAcard]
        have h3 : (A.subgroupOf (Work.CORE4.Qsub p B)).index = p := hrel
        rw [h2, h3] at h1
        rw [← h1]; ring
      -- `|Z(Q)| = p`
      have hZcard : Nat.card ↥(Work.CORE4.centerIn (Work.CORE4.Qsub p B)) = p := by
        have hdvd : Nat.card ↥(Work.CORE4.centerIn (Work.CORE4.Qsub p B)) ∣ p ^ 2 :=
          hAcard ▸ Subgroup.card_dvd_of_le hZlt.le
        have hlt : Nat.card ↥(Work.CORE4.centerIn (Work.CORE4.Qsub p B)) < p ^ 2 :=
          hAcard ▸ Subgroup.card_lt_of_lt hZlt
        have hmap : Nat.card ↥(Work.CORE4.centerIn (Work.CORE4.Qsub p B)) =
            Nat.card ↥(Subgroup.center ↥(Work.CORE4.Qsub p B)) :=
          Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
        haveI : Fact p.Prime := ⟨hp⟩
        haveI : IsPGroup p ↥(Work.CORE4.Qsub p B) := IsPGroup.iff_card.mpr ⟨3, hQcard⟩
        obtain ⟨k, hk0, hk⟩ := IsPGroup.card_center_eq_prime_pow
          (G := ↥(Work.CORE4.Qsub p B)) (p := p) (n := 3) hQcard (by norm_num)
        have hklt : k < 2 := by
          have h : p ^ k < p ^ 2 := by rw [← hk, ← hmap]; exact hlt
          exact (Nat.pow_lt_pow_iff_right hp.one_lt).mp h
        have hk1 : k = 1 := by omega
        rw [hmap, hk, hk1, pow_one]
      -- the counting lemma
      have hcount : {H : Subgroup G | H ≤ Work.CORE4.Qsub p B ∧ Nat.card ↥H = p ^ 2 ∧
          Work.CORE4.centerIn (Work.CORE4.Qsub p B) ≤ H}.ncard = p + 1 :=
        Work.CORE4.ncard_subgroups_prime_cube p hp (Work.CORE4.Qsub p B) hQexp hQcard hZcard
      -- the orbit lies in the counted set
      have hsub : {X : Subgroup G | ∃ g : G, g ∈ B.U ∧ X = Work.GW2.conjSub g A} ⊆
          {H : Subgroup G | H ≤ Work.CORE4.Qsub p B ∧ Nat.card ↥H = p ^ 2 ∧
            Work.CORE4.centerIn (Work.CORE4.Qsub p B) ≤ H} := by
        rintro X ⟨g, hg, rfl⟩
        have hgQ : Work.GW2.conjSub g (Work.CORE4.Qsub p B) = Work.CORE4.Qsub p B :=
          Subgroup.mem_normalizer_iff_map_conj_eq.mp (hUnormQ hg)
        refine ⟨?_, ?_, ?_⟩
        · rw [← hgQ]; exact Subgroup.map_mono hAQ
        · rw [Work.GW2.conjSub,
            Subgroup.card_map_of_injective (MulAut.conj g).injective, hAcard]
        · calc Work.CORE4.centerIn (Work.CORE4.Qsub p B)
              = Work.GW2.conjSub g (Work.CORE4.centerIn (Work.CORE4.Qsub p B)) :=
                (conjSub_centerIn_of_mem_normalizer (Q := Work.CORE4.Qsub p B)
                  (hUnormQ hg)).symm
            _ ≤ Work.GW2.conjSub g A := Subgroup.map_mono hZlt.le
      have hle : {X : Subgroup G | ∃ g : G, g ∈ B.U ∧ X = Work.GW2.conjSub g A}.ncard ≤ p + 1 :=
        (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (le_of_eq hcount)
      obtain ⟨j, hj⟩ := hodd
      obtain ⟨i, hi⟩ := hpodd
      omega
  · -- the third conjunct
    intro _hUM
    exact Work.CORE4.three_le_p0_of_not_invNormal I hbc B h p P A hp hPF hPcard hObj hInv hAnF

end Work.CORE4
