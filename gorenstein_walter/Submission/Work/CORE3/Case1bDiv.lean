import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE3.Case1bEightNineDefs
import Submission.Work.CORE2A.inf_U_S_eq_bot
import Submission.Work.CORE3.NormalizerPcoreEqHhat
import Submission.Work.CORE3.CosetInvCountAPI
import Submission.Work.BSW.Cases.K4.CardSup
import Submission.Work.CORE3.Case1bStabTrivial

set_option linter.unusedVariables false

namespace Work.CORE3
open Subgroup
open Work.GW2

variable {G : Type} [Group G] [Finite G] (B : BenderSetup G)

/-!
# `Work.CORE3.Case1bDiv`: B81 p. 224, `12 ∣ b₄`

Bender's "fixed-point-free action of `KV = O₂(Ĥ)·O(Ĥ)` on the set of cosets `Ĥg` contributing to
`b₄` forces `|KV| = 12` to divide `b₄`", formalised as an orbit count for the conjugation action
of `VU = O₂(Ĥ) ⊔ O(H)` on the `b₄`-cosets of `G ⧸ Ĥ`.

* `conjQuot`, `instSMulVU`, `instMulActionVU` — the conjugation action of `VU ≤ Ĥ` on `G ⧸ Ĥ`;
* `b4Set` — the set of cosets `≠ Ĥ` carrying exactly four involutions; `bCount Ĥ 4 = |b4Set|`;
* `instSMulB4`, `instMulActionB4` — its restriction to `b4Set`;
* `natCard_dvd_of_free` — a free action of a finite group has orbits of full size;
* `exists_j4_rep` — a `b₄`-coset contains an involution `∉ Ĥ`;
* `card_VU` — `|VU| = |O₂(Ĥ)| · |O(H)| = 12` (`O₂(Ĥ) ⊓ O(H) = ⊥`, `O(H)` normalises `O₂(Ĥ)`).

The single external input is `Work.CORE3.Case1bStabTrivial` (the trivial-stabilizer statement of
Bender's fixed-point-free action).
-/

noncomputable def conjQuot (a : G) (ha : a ∈ B.Hhat) : G ⧸ B.Hhat → G ⧸ B.Hhat :=
  Quotient.map' (fun g => a * g * a⁻¹) (by
    intro x y hxy
    rw [QuotientGroup.leftRel_eq] at hxy
    simp only [QuotientGroup.leftRel_eq]
    have h : (a * x * a⁻¹)⁻¹ * (a * y * a⁻¹) = a * (x⁻¹ * y) * a⁻¹ := by group
    rw [h]
    exact B.Hhat.mul_mem (B.Hhat.mul_mem ha hxy) (B.Hhat.inv_mem ha))

@[simp] theorem conjQuot_mk (a : G) (ha : a ∈ B.Hhat) (g : G) :
    conjQuot B a ha (QuotientGroup.mk g) = QuotientGroup.mk (a * g * a⁻¹) :=
  Quotient.map'_mk'' _ _ g

theorem conjQuot_irrel (a : G) (ha ha' : a ∈ B.Hhat) :
    conjQuot B a ha = conjQuot B a ha' := by
  have h : ha = ha' := Subsingleton.elim _ _
  rw [h]

theorem conjQuot_one : conjQuot B 1 B.Hhat.one_mem = id := by
  funext c
  refine Quotient.inductionOn' c (fun g => ?_)
  simp [conjQuot_mk]

theorem conjQuot_mul (a b : G) (ha : a ∈ B.Hhat) (hb : b ∈ B.Hhat) :
    conjQuot B (a * b) (B.Hhat.mul_mem ha hb) = conjQuot B a ha ∘ conjQuot B b hb := by
  funext c
  refine Quotient.inductionOn' c (fun g => ?_)
  simp only [conjQuot_mk, Function.comp_apply]
  rw [show a * b * g * (a * b)⁻¹ = a * (b * g * b⁻¹) * a⁻¹ by group]

theorem conjQuot_inv_cancel (a : G) (ha : a ∈ B.Hhat) (c : G ⧸ B.Hhat) :
    conjQuot B a ha (conjQuot B a⁻¹ (B.Hhat.inv_mem ha) c) = c := by
  refine Quotient.inductionOn' c (fun g => ?_)
  rw [conjQuot_mk, conjQuot_mk]
  rw [show a * (a⁻¹ * g * (a⁻¹)⁻¹) * a⁻¹ = g by group]

theorem conjQuot_cancel' (a : G) (ha : a ∈ B.Hhat) (c : G ⧸ B.Hhat) :
    conjQuot B a⁻¹ (B.Hhat.inv_mem ha) (conjQuot B a ha c) = c := by
  refine Quotient.inductionOn' c (fun g => ?_)
  rw [conjQuot_mk, conjQuot_mk]
  rw [show a⁻¹ * (a * g * a⁻¹) * (a⁻¹)⁻¹ = g by group]

theorem conjQuot_one_coset (a : G) (ha : a ∈ B.Hhat) :
    conjQuot B a ha (QuotientGroup.mk (1 : G)) = QuotientGroup.mk (1 : G) := by
  rw [conjQuot_mk]
  rw [show a * 1 * a⁻¹ = 1 by group]

theorem conjQuot_eq_one_iff (a : G) (ha : a ∈ B.Hhat) (c : G ⧸ B.Hhat) :
    conjQuot B a ha c = QuotientGroup.mk (1 : G) ↔ c = QuotientGroup.mk (1 : G) := by
  constructor
  · intro h
    have h2 := congrArg (conjQuot B a⁻¹ (B.Hhat.inv_mem ha)) h
    rw [conjQuot_cancel' B a ha c, conjQuot_one_coset B a⁻¹ (B.Hhat.inv_mem ha)] at h2
    exact h2
  · intro h; rw [h]; exact conjQuot_one_coset B a ha

theorem VU_le_Hhat : (pCoreIn 2 B.Hhat ⊔ B.U : Subgroup G) ≤ B.Hhat :=
  sup_le (by simpa [pCoreIn] using Subgroup.map_subtype_le (pCore 2 ↥B.Hhat))
    (Work.CORE2A.bSetup_U_le_Hhat B)

noncomputable instance instSMulVU : SMul ↥(pCoreIn 2 B.Hhat ⊔ B.U : Subgroup G) (G ⧸ B.Hhat) :=
  ⟨fun a c => conjQuot B (a : G) (VU_le_Hhat B a.2) c⟩

noncomputable instance instMulActionVU : MulAction ↥(pCoreIn 2 B.Hhat ⊔ B.U : Subgroup G)
    (G ⧸ B.Hhat) where
  one_smul c := by
    change conjQuot B (1 : G) (VU_le_Hhat B (1 : ↥(pCoreIn 2 B.Hhat ⊔ B.U : Subgroup G)).2) c = c
    rw [conjQuot_irrel B 1 _ B.Hhat.one_mem, conjQuot_one]
    rfl
  mul_smul a b c := by
    change conjQuot B ((a : G) * (b : G))
        (VU_le_Hhat B ((a * b : ↥(pCoreIn 2 B.Hhat ⊔ B.U : Subgroup G)).2)) c
      = conjQuot B (a : G) (VU_le_Hhat B a.2) (conjQuot B (b : G) (VU_le_Hhat B b.2) c)
    rw [conjQuot_irrel B ((a:G)*(b:G)) _ (B.Hhat.mul_mem (VU_le_Hhat B a.2) (VU_le_Hhat B b.2)),
      conjQuot_mul B (a:G) (b:G) (VU_le_Hhat B a.2) (VU_le_Hhat B b.2)]
    rfl

/-- The `b₄`-cosets. -/
def b4Set : Set (G ⧸ B.Hhat) :=
  {c | c ≠ QuotientGroup.mk (1 : G) ∧ cosetInvCount B.Hhat (Quotient.out c) = 4}

theorem b4Set_smul_mem (a : ↥(pCoreIn 2 B.Hhat ⊔ B.U : Subgroup G))
    {c : G ⧸ B.Hhat} (hc : c ∈ b4Set B) : (a • c) ∈ b4Set B := by
  obtain ⟨hc1, hc2⟩ := hc
  refine ⟨?_, ?_⟩
  · show conjQuot B (a : G) (VU_le_Hhat B a.2) c ≠ QuotientGroup.mk (1 : G)
    intro h
    exact hc1 ((conjQuot_eq_one_iff B (a:G) (VU_le_Hhat B a.2) c).mp h)
  · have hsm : conjQuot B (a : G) (VU_le_Hhat B a.2) c
        = QuotientGroup.mk ((a:G) * (Quotient.out c) * (a:G)⁻¹) := by
      conv_lhs => rw [← Quotient.out_eq c]
      rw [conjQuot_mk]
    rw [show (a • c) = conjQuot B (a : G) (VU_le_Hhat B a.2) c from rfl, hsm]
    rw [Work.CORE3.cosetInvCount_congr B.Hhat
      (show (Quotient.out (QuotientGroup.mk ((a:G) * (Quotient.out c) * (a:G)⁻¹)))⁻¹
          * ((a:G) * (Quotient.out c) * (a:G)⁻¹) ∈ B.Hhat from
        (QuotientGroup.eq).mp (Quotient.out_eq (QuotientGroup.mk ((a:G) * (Quotient.out c) * (a:G)⁻¹))))]
    rw [Work.CORE3.cosetInvCount_conj B.Hhat (Subgroup.le_normalizer (VU_le_Hhat B a.2))]
    exact hc2

end Work.CORE3

namespace Work.CORE3

theorem natCard_dvd_of_free {A X : Type*} [Group A] [MulAction A X] [Finite A] [Finite X]
    (hfree : ∀ a : A, a ≠ 1 → ∀ x : X, a • x ≠ x) : Nat.card A ∣ Nat.card X := by
  classical
  haveI : Fintype A := Fintype.ofFinite A
  haveI : Fintype X := Fintype.ofFinite X
  have hstab : ∀ x : X, MulAction.stabilizer A x = ⊥ := by
    intro x
    rw [Subgroup.eq_bot_iff_forall]
    intro a ha
    by_contra hne
    exact hfree a hne x ha
  have h1 : ∀ ω : Quotient (MulAction.orbitRel A X),
      Nat.card (A ⧸ MulAction.stabilizer A (Quotient.out ω)) = Nat.card A := by
    intro ω
    rw [← Subgroup.index_eq_card, hstab (Quotient.out ω), Subgroup.index_bot]
  have hcard : Nat.card X = Nat.card A * Nat.card (Quotient (MulAction.orbitRel A X)) := by
    rw [Nat.card_congr (MulAction.selfEquivSigmaOrbitsQuotientStabilizer A X)]
    rw [Nat.card_sigma]
    simp_rw [h1]
    simp [Finset.sum_const, mul_comm]
  exact ⟨_, hcard⟩

end Work.CORE3

namespace Work.CORE3
open Subgroup
open Work.GW2

variable {G : Type} [Group G] [Finite G] (B : BenderSetup G)

noncomputable instance instSMulB4 : SMul ↥(pCoreIn 2 B.Hhat ⊔ B.U : Subgroup G) ↥(b4Set B) :=
  ⟨fun a x => ⟨a • x.1, b4Set_smul_mem B a x.2⟩⟩

noncomputable instance instMulActionB4 : MulAction ↥(pCoreIn 2 B.Hhat ⊔ B.U : Subgroup G)
    ↥(b4Set B) where
  one_smul x := Subtype.ext (one_smul _ x.1)
  mul_smul a b x := Subtype.ext (mul_smul a b x.1)

end Work.CORE3

namespace Work.CORE3
open Subgroup
open Work.GW2

variable {G : Type} [Group G] [Finite G] (B : BenderSetup G)

/-- A `b₄`-coset carries an involution `∉ Ĥ` whose coset-involution count is `4`. -/
theorem exists_j4_rep {c : G ⧸ B.Hhat} (hc : c ∈ b4Set B) :
    ∃ y : G, orderOf y = 2 ∧ y ∉ B.Hhat ∧ cosetInvCount B.Hhat y = 4 ∧
      QuotientGroup.mk y = c := by
  obtain ⟨hc1, hc2⟩ := hc
  have hne : ({x : G | orderOf x = 2 ∧ (Quotient.out c)⁻¹ * x ∈ B.Hhat} : Set G).Nonempty := by
    rw [← Set.ncard_pos]
    rw [show ({x : G | orderOf x = 2 ∧ (Quotient.out c)⁻¹ * x ∈ B.Hhat} : Set G).ncard
        = cosetInvCount B.Hhat (Quotient.out c) from rfl, hc2]
    norm_num
  obtain ⟨y, hy⟩ := hne
  simp only [Set.mem_ofPred_eq] at hy
  obtain ⟨hy2, hymem⟩ := hy
  have hmky : QuotientGroup.mk y = c := by
    rw [← Quotient.out_eq c, QuotientGroup.eq]
    have e : y⁻¹ * Quotient.out c = ((Quotient.out c)⁻¹ * y)⁻¹ := by group
    rw [e]
    exact B.Hhat.inv_mem hymem
  refine ⟨y, hy2, ?_, ?_, hmky⟩
  · intro hyH
    exact hc1 (by rw [← hmky, QuotientGroup.eq]; simpa using hyH)
  · rw [← Work.CORE3.cosetInvCount_congr B.Hhat hymem, hc2]

theorem card_VU (h26 : (B.S : Subgroup G) ⊓ centralizer (B.U : Set G) = pCoreIn 2 B.Hhat) :
    Nat.card ↥(pCoreIn 2 B.Hhat ⊔ B.U : Subgroup G)
      = Nat.card ↥(pCoreIn 2 B.Hhat) * Nat.card ↥B.U := by
  have hVS : (pCoreIn 2 B.Hhat : Subgroup G) ≤ (B.S : Subgroup G) := by
    rw [← h26]; exact inf_le_left
  have hN : B.U ≤ Subgroup.normalizer ((pCoreIn 2 B.Hhat : Subgroup G) : Set G) :=
    le_trans (Work.CORE2A.bSetup_U_le_Hhat B)
      (by simpa [pCoreIn] using Work.CORE3.le_normalizer_map_subtype B.Hhat (pCore 2 ↥B.Hhat))
  have hd : (pCoreIn 2 B.Hhat : Subgroup G) ⊓ B.U = ⊥ := by
    have h1 : (pCoreIn 2 B.Hhat : Subgroup G) ⊓ B.U ≤ (B.S : Subgroup G) ⊓ B.U :=
      inf_le_inf hVS le_rfl
    have hS : (B.S : Subgroup G) ⊓ B.U = ⊥ := by
      rw [inf_comm]; exact Work.CORE2A.inf_U_S_eq_bot B
    rw [hS] at h1
    exact le_bot_iff.mp h1
  exact Work.BSW.Cases.K4.card_sup_of_le_normalizer_of_inf_eq_bot hN hd

end Work.CORE3

namespace Work.CORE3

open Subgroup
open Work.GW2

/-- B81 p. 224: `12 ∣ b₄` in the subcase `V = O₂(Ĥ)`.  The group `VU = O₂(Ĥ) ⊔ O(H)` of order
`12` acts on the set of `b₄`-cosets by conjugation; the action is free
(`Work.CORE3.Case1bStabTrivial`), so `12 = |VU|` divides `bCount B.Hhat 4`. -/
theorem Case1bDiv (I : Case1Inputs) (hSetup : Case1bSetupProp) (hCount : Case1bCountProp)
    (hFive : Case1bFiveProp) (h89 : Case1bEightNineProp) : Case1bDivProp := by
  intro G instG instFin hFT hBc B h1 h4
  classical
  by_cases hb : bCount B.Hhat 4 = 0
  · rw [hb]; exact dvd_zero 12
  obtain ⟨D⟩ := hSetup G hFT hBc B h1 h4
  have hU3 : Nat.card ↥B.U = 3 := (h89 G hFT hBc B h1 D).2.2 hb |>.1
  have hcardA : Nat.card ↥(pCoreIn 2 B.Hhat ⊔ B.U : Subgroup G) = 12 := by
    rw [card_VU B (I.h26 G hFT hBc B).2.1, h4.1, hU3]
  have hfree : ∀ a : ↥(pCoreIn 2 B.Hhat ⊔ B.U : Subgroup G), a ≠ 1 →
      ∀ x : ↥(b4Set B), a • x ≠ x := by
    intro a ha1 x hax
    obtain ⟨y, hy2, hyH, hy4, hyc⟩ := exists_j4_rep B x.2
    have hyy : y * y = 1 := by
      have h := pow_orderOf_eq_one y
      rw [hy2] at h
      simpa [pow_two] using h
    have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
    have h2 : conjQuot B (a : G) (VU_le_Hhat B a.2) x.1 = x.1 := congrArg Subtype.val hax
    rw [← hyc, conjQuot_mk] at h2
    have hmem : ((a : G) * y * (a : G)⁻¹)⁻¹ * y ∈ B.Hhat := (QuotientGroup.eq).mp h2
    have hmem2 : y * (a : G)⁻¹ * y ∈ B.Hhat := by
      have h := B.Hhat.mul_mem (B.Hhat.inv_mem (VU_le_Hhat B a.2)) hmem
      have e : (a : G)⁻¹ * (((a : G) * y * (a : G)⁻¹)⁻¹ * y) = y⁻¹ * (a : G)⁻¹ * y := by group
      rw [e, hyinv] at h
      exact h
    have hmem3 : y * (a : G) * y ∈ B.Hhat := by
      have h := B.Hhat.inv_mem hmem2
      have e : (y * (a : G)⁻¹ * y)⁻¹ = y * (a : G) * y := by
        rw [show (y * (a : G)⁻¹ * y)⁻¹ = y⁻¹ * (a : G) * y⁻¹ by group, hyinv]
      rwa [e] at h
    exact Case1bStabTrivial I hBc B h1 D hy2 hyH hy4 a.2
      (fun h => ha1 (Subtype.ext h)) hmem3
  have hdvd : Nat.card ↥(pCoreIn 2 B.Hhat ⊔ B.U : Subgroup G) ∣ Nat.card ↥(b4Set B) :=
    natCard_dvd_of_free hfree
  rw [hcardA] at hdvd
  rwa [show bCount B.Hhat 4 = Nat.card ↥(b4Set B) from by rw [Nat.card_coe_set_eq]; rfl]

end Work.CORE3
