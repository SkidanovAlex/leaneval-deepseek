import Mathlib
import Submission.Work.CORE4.Defs10
import Submission.Work.CORE4.API
import Submission.Work.CORE4.EightIdxDefs
import Submission.Work.CORE4.Case2EightA_le_FsupK0
import Submission.Work.CORE4.SixThree
import Submission.Work.CORE4.Case2EightN9Sup
import Submission.Work.CORE4.CtxN9Inf
import Submission.Work.CORE4.Case2EightQfacts
import Submission.Work.CORE4.EightAnormalPcore_of_Qpos
import Submission.Work.CORE4.N9InfC4Aux.CenterCard
import Submission.Work.CORE4.N9InfC4Aux.ConjPowOrbitSelf
import Submission.Work.CORE4.Case2EightCasesOfCtx

namespace Work.CORE4

open scoped commutatorElement

/-- Bender 1981, §4 (8), case 2 of the trichotomy on `Q := Qsub p B = Ω₁(Z₂(O_p(U)))`, the
inclusion half of `N_U(A) = (U ⊓ M) ⊔ F(U)`: with `Z(Q) < A < Q` and `A.relIndex Q = p`, every
`x ∈ U` normalising `A` lies in `(U ⊓ M) ⊔ F(U)`.

This is a copy of the sorry-backed `Work.CORE4.Case2EightN9Inf`; the companion inclusion
`(U ⊓ M) ⊔ F(U) ≤ N_U(A)` is already PROVED as `Work.CORE4.Case2EightN9Sup`, and the consumer is
`Work.CORE4.Case2EightCase2N9`.

Blueprint: `Submission/Work/CORE4/CtxN9Inf.lean` proves the `Case2Ctx`-level version
(`N_U(A) ≤ (U ⊓ M) ⊔ Qsub`) with the same pointwise argument (for `x ∈ U ⊓ N_G(A)`: `P^x ≤ A`;
either `P^x = P`, or a power of an element of `Q` conjugates `P^x` back to `P`), so only the port
from `Case2Ctx` to `Case2Ctx6` is needed — none of that proof's steps uses §4 (9) `nine`.  Must be
sorry-free: `#print axioms Work.CORE4.EightN9Inf` = `[propext, Classical.choice, Quot.sound]`. -/
theorem EightN9Inf (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G → ∀ B : Work.GW2.BenderSetup G,
      Work.GW2.Case2 B → ∀ C : Work.GW2.Case2Ctx6 B, Work.GW2.Case2PrePlus B C.D →
        Work.GW2.Case2SevenFacts B C.D →
        ∀ (p : ℕ) (P A : Subgroup G), p.Prime → P ≤ C.D.F → Nat.card P = p →
          Work.GW2.Case2EightObj C.D p P A →
          A ≤ Work.CORE4.Qsub p B → Work.CORE4.centerIn (Work.CORE4.Qsub p B) < A →
            A < Work.CORE4.Qsub p B → A.relIndex (Work.CORE4.Qsub p B) = p →
            B.U ⊓ Subgroup.normalizer (A : Set G) ≤
              (B.U ⊓ C.D.M) ⊔ Work.GW2.fittingIn B.U := by
  intro G _ _ hbc B h2 C hplus h7 p P A hp hPF hPcard hObj hAQ hZA hAlt hIdx
  -- ## the data of `A` (`Case2EightObj`), read off at the `Case2Ctx6` level
  have hAcard : Nat.card ↥A = p ^ 2 := hObj.2.2.2.2.1
  have hAexp : ∀ x ∈ A, x ^ p = 1 := hObj.2.2.2.2.2.1
  have hPA : P ≤ A := hObj.2.2.2.2.2.2.1
  have hAle : A ≤ C.D.F ⊔ C.D.K := hObj.2.2.2.1
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x :=
    Case2Eight_A_comm I B C A hAle
  -- ## the facts about `Q = Ω₁(Z₂(O_p(U)))`
  -- `Q ≤ F(U)`, `U ≤ N_G(Q)`, `Q` has exponent `p` and is not cyclic
  -- (`Case2EightQfacts`), and `|Z(Q)| = p` (`CenterCard`), while `[Q, A] ≤ Z(Q)` follows from
  -- `commutator_omega1_z2_mem_centerIn` and `Q ≤ O_p(U)`.
  obtain ⟨hQleFU, hUleNQ, -, -⟩ :=
    Case2EightQfacts I G hbc B h2 C hplus h7 p P A hp hPF hPcard hObj
  have hZcard : Nat.card ↥(centerIn (Qsub p B)) = p :=
    N9InfC4Aux.CenterCard p hp (Qsub p B) A hAQ hAcard hIdx hZA
  have hZle : centerIn (Qsub p B) ≤ A := le_of_lt hZA
  have hcomm : ∀ a ∈ A, ∀ y ∈ Qsub p B,
      y * a * y⁻¹ * a⁻¹ ∈ centerIn (Qsub p B) := by
    intro a haA y hyQ
    have haQ : a ∈ Qsub p B := hAQ haA
    have hyP : y ∈ Work.GW2.pCoreIn p B.U := n9_Qsub_le_pCoreIn B p hyQ
    have h : ⁅a, y⁆ ∈ centerIn (Qsub p B) := by
      have h' := commutator_omega1_z2_mem_centerIn p (Work.GW2.pCoreIn p B.U) haQ hyP
      simpa only [Qsub] using h'
    rw [show y * a * y⁻¹ * a⁻¹ = ⁅y, a⁆ from by rw [commutatorElement_def],
        ← commutatorElement_inv]
    exact (centerIn (Qsub p B)).inv_mem h
  -- ## the pointwise argument: `x ∈ U` normalising `A` lies in `(U ⊓ M) ⊔ Q`
  have hmain : B.U ⊓ Subgroup.normalizer (A : Set G) ≤
      (B.U ⊓ C.D.M) ⊔ Qsub p B := by
    have hFUleU : Work.GW2.fittingIn B.U ≤ B.U := Subgroup.map_subtype_le _
    have hPne : P ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hPcard
      have hp2 : 2 ≤ p := hp.two_le
      omega
    have hNP : Subgroup.normalizer (P : Set G) = C.D.M :=
      normalizerP_of_ctx6 B C P hPF hPne
    intro x hx
    obtain ⟨hxU, hxN⟩ := Subgroup.mem_inf.mp hx
    have hAx : Work.GW2.conjSub x A = A :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hxN
    have hxNQ : x ∈ Subgroup.normalizer (Qsub p B : Set G) := hUleNQ hxU
    have hZfix : Work.GW2.conjSub x (centerIn (Qsub p B)) = centerIn (Qsub p B) :=
      conjSub_centerIn_of_mem_normalizer hxNQ
    have hPxA : Work.GW2.conjSub x P ≤ A := by
      rw [← hAx]; exact Subgroup.map_mono hPA
    have hPxcard : Nat.card ↥(Work.GW2.conjSub x P) = p := by
      rw [Work.GW2.conjSub, Subgroup.card_map_of_injective (MulAut.conj x).injective, hPcard]
    by_cases hPZ : P = centerIn (Qsub p B)
    · -- `P = Z(Q)` is fixed by `x`
      have hPfix : Work.GW2.conjSub x P = P := by rw [hPZ, hZfix]
      have hxNP : x ∈ Subgroup.normalizer (P : Set G) :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mpr hPfix
      rw [hNP] at hxNP
      exact Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hxU, hxNP⟩)
    · by_cases hPfix : Work.GW2.conjSub x P = P
      · -- `P^x = P` again gives `x ∈ N_G(P) = M`
        have hxNP : x ∈ Subgroup.normalizer (P : Set G) :=
          Subgroup.mem_normalizer_iff_map_conj_eq.mpr hPfix
        rw [hNP] at hxNP
        exact Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hxU, hxNP⟩)
      · -- ## the hard case: `P ≠ Z(Q)` and `P^x ≠ P`
        have hdisj : P ⊓ centerIn (Qsub p B) = ⊥ := by
          rw [eq_bot_iff]
          intro y hy
          obtain ⟨hyP, -⟩ := Subgroup.mem_inf.mp hy
          by_contra hyne
          have hcardP : Nat.card ↥(P ⊓ centerIn (Qsub p B)) = p := by
            have hdvd : Nat.card ↥(P ⊓ centerIn (Qsub p B)) ∣ p := by
              rw [← hPcard]; exact Subgroup.card_dvd_of_le inf_le_left
            rcases (Nat.dvd_prime hp).mp hdvd with h1 | h2
            · exact absurd h1 (fun h1' =>
                hyne (Subgroup.mem_bot.mp (Subgroup.card_eq_one.mp h1' ▸ hy)))
            · exact h2
          have hPleZ : P ≤ centerIn (Qsub p B) := by
            have heq : P ⊓ centerIn (Qsub p B) = P :=
              Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcardP, hPcard])
            exact heq ▸ inf_le_right
          exact hPZ (Subgroup.eq_of_le_of_card_ge hPleZ (by rw [hZcard, hPcard]))
        have hPleNZ : P ≤ Subgroup.normalizer (centerIn (Qsub p B) : Set G) := by
          intro q hq
          have hqQ : q ∈ Qsub p B := hAQ (hPA hq)
          have hqU : q ∈ B.U := hFUleU (hQleFU hqQ)
          exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
            (conjSub_centerIn_of_mem_normalizer (hUleNQ hqU))
        have hAeq : A = P ⊔ centerIn (Qsub p B) := by
          have hcard : Nat.card ↥(P ⊔ centerIn (Qsub p B)) = p ^ 2 := by
            rw [card_sup_of_disjoint_normalizer hdisj hPleNZ, hPcard, hZcard]
            ring
          exact (Subgroup.eq_of_le_of_card_ge (sup_le hPA hZle)
            (by rw [hAcard, hcard])).symm
        have hPxneZ : Work.GW2.conjSub x P ≠ centerIn (Qsub p B) := by
          intro hcon
          have hmap : Work.GW2.conjSub x A
              = Work.GW2.conjSub x P ⊔ Work.GW2.conjSub x (centerIn (Qsub p B)) := by
            rw [hAeq, Work.GW2.conjSub, Work.GW2.conjSub, Work.GW2.conjSub, Subgroup.map_sup]
          have hconjA : Work.GW2.conjSub x A = Work.GW2.conjSub x P ⊔ centerIn (Qsub p B) := by
            rw [hmap, hZfix]
          have hAZ : A = centerIn (Qsub p B) :=
            hAx.symm.trans (hconjA.trans (by rw [hcon, sup_idem]))
          have hcard : Nat.card ↥A = p := by rw [hAZ, hZcard]
          rw [hAcard] at hcard
          have hp2 : 2 ≤ p := hp.two_le
          nlinarith
        -- ## pick `q ∈ Q` with `[q, A] ≠ 1`
        obtain ⟨a, haA, haZ⟩ : ∃ a ∈ A, a ∉ centerIn (Qsub p B) := by
          by_contra hc
          push Not at hc
          exact (ne_of_lt hZA) (le_antisymm hZle (fun a ha => hc a ha))
        have haQ : a ∈ Qsub p B := hAQ haA
        have hnotcen : (⟨a, haQ⟩ : ↥(Qsub p B)) ∉ Subgroup.center ↥(Qsub p B) := by
          intro hcen
          exact haZ (Subgroup.mem_map.mpr ⟨⟨a, haQ⟩, hcen, rfl⟩)
        have hex : ∃ y : ↥(Qsub p B),
            (⟨a, haQ⟩ : ↥(Qsub p B)) * y ≠ y * ⟨a, haQ⟩ := by
          by_contra hc
          push Not at hc
          exact hnotcen ((Subgroup.mem_center_iff (G := ↥(Qsub p B))).mpr
            (fun g => (hc g).symm))
        obtain ⟨y, hy⟩ := hex
        have hqQ : (y : G) ∈ Qsub p B := y.2
        have hqane : (y : G) * a * (y : G)⁻¹ * a⁻¹ ≠ 1 := by
          intro h1
          apply hy
          have hconj : (y : G) * a * (y : G)⁻¹ = a := by
            have h2 := congrArg (fun t => t * a) h1
            simpa [mul_assoc] using h2
          refine Subtype.ext ?_
          show a * (y : G) = (y : G) * a
          calc a * (y : G) = ((y : G) * a * (y : G)⁻¹) * (y : G) := by rw [hconj]
            _ = (y : G) * a := by group
        have hcommq : ∀ b ∈ A, (y : G) * b * (y : G)⁻¹ * b⁻¹ ∈ centerIn (Qsub p B) :=
          fun b hb => hcomm b hb (y : G) hqQ
        -- ## some power of `q` conjugates `P^x` back onto `P`
        obtain ⟨i, hi⟩ := N9InfC4Self.ConjPowOrbit p hp (Qsub p B) A (y : G) hqQ
          (le_of_lt hAlt) hAcard hAexp hAcomm hZcard hZle hcommq ⟨a, haA, hqane⟩
          (Work.GW2.conjSub x P) P hPxA hPA hPxcard hPcard hPxneZ hPZ
        have hmem : (y : G) ^ i * x ∈ Subgroup.normalizer (P : Set G) := by
          rw [Subgroup.mem_normalizer_iff_map_conj_eq]
          exact (conjSub_mul' ((y : G) ^ i) x P).symm.trans hi
        rw [hNP] at hmem
        have hqiQ : (y : G) ^ i ∈ Qsub p B := (Qsub p B).pow_mem hqQ i
        have hqiU : (y : G) ^ i ∈ B.U := hFUleU (hQleFU hqiQ)
        have hmid : (y : G) ^ i * x ∈ B.U ⊓ C.D.M :=
          Subgroup.mem_inf.mpr ⟨B.U.mul_mem hqiU hxU, hmem⟩
        have hxsplit : x = ((y : G) ^ i)⁻¹ * ((y : G) ^ i * x) := by group
        rw [hxsplit]
        have h1 : ((y : G) ^ i)⁻¹ ∈ (B.U ⊓ C.D.M) ⊔ Qsub p B :=
          Subgroup.mem_sup_right ((Qsub p B).inv_mem hqiQ)
        have h2 : (y : G) ^ i * x ∈ (B.U ⊓ C.D.M) ⊔ Qsub p B :=
          Subgroup.mem_sup_left hmid
        exact mul_mem h1 h2
  exact hmain.trans (sup_le_sup_left hQleFU _)

end Work.CORE4
