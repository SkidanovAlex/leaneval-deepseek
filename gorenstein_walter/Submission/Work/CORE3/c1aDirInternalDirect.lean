import Mathlib
import Submission.Work.CORE3.Case1aThmCInputs
import Submission.Work.CORE3.Case1aSetup
import Submission.Work.CORE3.Case1aBothInvert
import Submission.Work.CORE3.Case1aBFitting
import Submission.Work.CORE2A.odd_subgroup_le_oddCoreIn
import Submission.Work.CORE3.c1aDirPcommF3
import Submission.Work.CORE3.p_eq_three
import Submission.Work.CORE3.c1aDirCU_t1_inf_fittingIn_eq

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.CORE3

open Subgroup
open Work.GW2

/-- If `s` normalizes `t`, every element of `s ⊔ t` is a product `y * z` with `y ∈ s`, `z ∈ t`.
(This is `Subgroup.mem_sup_of_normal_right` with `G`-normality of `t` relaxed to normalisation
by `s`; the proof is the same closure induction.) -/
theorem c1aDir_mem_sup_of_le_normalizer {G : Type*} [Group G] {s t : Subgroup G}
    (h : s ≤ Subgroup.normalizer (t : Set G)) {x : G} :
    x ∈ s ⊔ t ↔ ∃ y ∈ s, ∃ z ∈ t, y * z = x := by
  constructor
  · intro hx
    rw [Subgroup.sup_eq_closure] at hx
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
    · rintro y (hy | hy)
      · exact ⟨y, hy, 1, t.one_mem, by simp⟩
      · exact ⟨1, s.one_mem, y, hy, by simp⟩
    · exact ⟨1, s.one_mem, 1, t.one_mem, by simp⟩
    · rintro _ _ _ _ ⟨y₁, hy₁, z₁, hz₁, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, rfl⟩
      refine ⟨y₁ * y₂, s.mul_mem hy₁ hy₂, (y₂⁻¹ * z₁ * y₂) * z₂, ?_, by group⟩
      exact t.mul_mem (by
        simpa using (Subgroup.le_normalizer_iff.mp h) y₂⁻¹ (s.inv_mem hy₂) z₁ hz₁) hz₂
    · rintro _ _ ⟨y, hy, z, hz, rfl⟩
      refine ⟨y⁻¹, s.inv_mem hy, y * z⁻¹ * y⁻¹, ?_, by group⟩
      have h1 : y * z⁻¹ * y⁻¹ = (y * z * y⁻¹)⁻¹ := by group
      rw [h1]
      exact t.inv_mem ((Subgroup.le_normalizer_iff.mp h) y hy z hz)
  · rintro ⟨y, hy, z, hz, rfl⟩
    exact Subgroup.mul_mem_sup hy hz

/-- Bender 1981 §3, subcase `Ĥ = H`: the two subgroups
`A = C_U(t₁) ∩ F(U)` and `C = (C_U(t₁) ∩ C_U(t₂)) ⊔ F_{3'}(U)` are complementary direct
factors of `U = O(H)`.

Both pieces are located by the §3 data.  Write `B = C_U(S)`, `P = O_p(U)`,
`F_{3'} = F_{3'}(U)` and `X = C_U(t₁) ∩ C_U(t₂)`.

* `p = 3` (`Work.CORE3.p_eq_three`) and `t₁` inverts `F_{3'}` (`Case1aBothInvertProp`), so
  `A = C_F(t₁) = O_3(U) = P` (`F(U) = F_{3'} ⊔ O_3(U)` elementwise).
* `X = B`: `x ∈ X ⊆ B₁ = B ⊔ P` has trivial `P`-component because `t₂` fixes `x` but inverts
  `P`.
* `P ∩ C = 1`: if `P ∋ x = b·f` with `b ∈ B`, `f ∈ F_{3'}`, then `b⁻¹x = f` is `t₁`-fixed and
  `t₁`-inverted, so `f = 1` (odd order) and `x = b ∈ B ∩ P = 1`.
* `[P, C] = 1`: `[P, B] = 1` is the second conjunct of `Case1aDirectProp`, and
  `[P, F_{3'}] = 1` is `Work.CORE3.c1aDirPcommF3`.
* `A ⊔ C = U`: `U = F(U) ⊔ B` (`Work.CORE3.c1aU_eq_fitting_sup_B`) and `F(U) = F_{3'} ⊔ P`. -/
theorem c1aDirInternalDirect (I : Work.CORE3.Case1Inputs) (hFr : Work.GW2.Case1aFrattiniProp)
    (hAb : Work.GW2.Case1aAbelianProp) (hA7 : Work.GW2.Case1aA7Prop)
    (hBpf : Work.CORE3.Case1aBFpfProp) (hMD : Work.CORE3.Case1aMDataProp)
    (hDir : Work.CORE3.Case1aDirectProp) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
      ∀ B : Work.GW2.BenderSetup G, Work.GW2.Case1 B → B.Hhat = B.H →
      ∀ D : Work.GW2.Case1aData B,
        Work.GW2.IsInternalDirect B.U
          ((B.U ⊓ Subgroup.centralizer ({D.t1} : Set G)) ⊓ Work.GW2.fittingIn B.U)
          (((B.U ⊓ Subgroup.centralizer ({D.t1} : Set G)) ⊓
              (B.U ⊓ Subgroup.centralizer ({D.t2} : Set G))) ⊔
            (Work.GW2.fittingPiIn ({3}ᶜ) B.U ⊓ Work.GW2.fittingIn B.U)) := by
  intro G _instG _finG hFT hCtx B hCase1 hHhat D
  classical
  haveI hpFact : Fact D.p.Prime := ⟨D.hp⟩
  haveI h3Fact : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  -- abbreviations for the subgroups of the statement
  let Bc : Subgroup G := B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G)
  let B1 : Subgroup G := B.U ⊓ Subgroup.centralizer ({D.t1} : Set G)
  let B2 : Subgroup G := B.U ⊓ Subgroup.centralizer ({D.t2} : Set G)
  let P : Subgroup G := Work.GW2.pCoreIn D.p B.U
  let F3 : Subgroup G := Work.GW2.fittingPiIn ({3}ᶜ : Set ℕ) B.U
  let F : Subgroup G := Work.GW2.fittingIn B.U
  let X : Subgroup G := B1 ⊓ B2
  change Work.GW2.IsInternalDirect B.U (B1 ⊓ F) (X ⊔ (F3 ⊓ F))
  -- ## preparatory facts
  have hInv : Work.CORE3.Case1aBothInvertProp :=
    Case1aBothInvert I (Case1aSetup I) hFr hAb hA7 hBpf
  have hInvD := hInv G hFT hCtx B hCase1 hHhat D
  have hInv1 : Work.GW2.Inverts D.t1 F3 := hInvD.1
  have hInv2 : Work.GW2.Inverts D.t2 F3 := hInvD.2
  have hp3 : D.p = 3 := p_eq_three B D hInv1
  have hP3 : P = Work.GW2.pCoreIn 3 B.U := by
    show Work.GW2.pCoreIn D.p B.U = Work.GW2.pCoreIn 3 B.U
    rw [hp3]
  have hdir := hDir G hFT hCtx B hCase1 hHhat D
  have hB1_eq : B1 = Bc ⊔ P := hdir.1
  have hcommBcP : ∀ a ∈ Bc, ∀ b ∈ P, a * b = b * a := hdir.2
  have hF_eq : F = F3 ⊔ P := by
    show Work.GW2.fittingIn B.U = F3 ⊔ P
    rw [hP3]
    exact c1aFittingIn_eq_sup_three B.U
  have hUeq : B.U = F ⊔ Bc := c1aU_eq_fitting_sup_B I G hFT hCtx B hCase1
  have hA : B1 ⊓ F = P :=
    (c1aDirCU_t1_inf_fittingIn_eq G B D hp3 hInv1).trans hP3.symm
  have hF3_le_F : F3 ≤ F := bfpf_fittingPiIn_le_fittingIn ({3}ᶜ) B.U
  have hF3inf : F3 ⊓ F = F3 := inf_eq_left.mpr hF3_le_F
  have hF3tU : F3 ≤ B.U := hF3_le_F.trans (c1aFittingIn_le B.U)
  have hP_le_A : P ≤ B1 ⊓ F :=
    le_inf (le_inf (c1aPcoreIn_le_self D.p B.U) D.cent) (c1aPcoreIn_le_fittingIn D.p B.U)
  have hBc_le_B1 : Bc ≤ B1 :=
    le_inf inf_le_left (le_trans inf_le_right (Subgroup.centralizer_le (fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact D.t1_mem)))
  have hBc_le_B2 : Bc ≤ B2 :=
    le_inf inf_le_left (le_trans inf_le_right (Subgroup.centralizer_le (fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact D.t2_mem)))
  have hBc_le_NP : Bc ≤ Subgroup.normalizer (P : Set G) :=
    le_trans (le_trans (inf_le_left : Bc ≤ B.U) (Subgroup.le_normalizer (H := B.U)))
      (c1aLe_normalizer_pCoreIn D.p B.U)
  have hBc_le_NF3 : Bc ≤ Subgroup.normalizer (F3 : Set G) :=
    le_trans (inf_le_left : Bc ≤ B.U)
      (Work.DSTR.M110.le_normalizer_fittingPiIn G ({3}ᶜ : Set ℕ) B.U)
  -- ## the two inclusions `Bc ≤ X` and `X ≤ Bc`
  have hBc_le_X : Bc ≤ X := le_inf hBc_le_B1 hBc_le_B2
  have hX_le_Bc : X ≤ Bc := by
    intro y hy
    have hy' : y ∈ B1 ⊓ B2 := hy
    have hyB1 : y ∈ B1 := (inf_le_left : B1 ⊓ B2 ≤ B1) hy'
    have hyB2 : y ∈ B2 := (inf_le_right : B1 ⊓ B2 ≤ B2) hy'
    have hyBP : y ∈ Bc ⊔ P := by rw [← hB1_eq]; exact hyB1
    obtain ⟨b, hbBc, p0, hp0P, hbp0⟩ := (c1aDir_mem_sup_of_le_normalizer hBc_le_NP).mp hyBP
    -- `t₂` fixes `y`, fixes `b` and inverts `p₀`
    have hy_cen2 : y ∈ Subgroup.centralizer ({D.t2} : Set G) :=
      (inf_le_right : B2 ≤ Subgroup.centralizer ({D.t2} : Set G)) hyB2
    have hy_cen : D.t2 * y * D.t2⁻¹ = y := by
      have h := (Subgroup.mem_centralizer_iff.mp hy_cen2) D.t2 (Set.mem_singleton D.t2)
      rw [h]; group
    have hb_cen : D.t2 * b * D.t2⁻¹ = b := by
      have hbS : b ∈ Subgroup.centralizer ((B.S : Subgroup G) : Set G) :=
        (inf_le_right : Bc ≤ Subgroup.centralizer ((B.S : Subgroup G) : Set G)) hbBc
      have hbC2 : b ∈ Subgroup.centralizer ({D.t2} : Set G) :=
        Subgroup.centralizer_le (fun x hx => by
          rw [Set.mem_singleton_iff] at hx
          rw [hx]
          exact D.t2_mem) hbS
      have h := (Subgroup.mem_centralizer_iff.mp hbC2) D.t2 (Set.mem_singleton D.t2)
      rw [h]; group
    have hp0_inv : D.t2 * p0 * D.t2⁻¹ = p0⁻¹ := D.inv p0 hp0P
    have hp0_eq : p0⁻¹ = p0 := by
      have h1 : D.t2 * y * D.t2⁻¹ = b * p0⁻¹ := by
        rw [← hbp0]
        calc D.t2 * (b * p0) * D.t2⁻¹
            = (D.t2 * b * D.t2⁻¹) * (D.t2 * p0 * D.t2⁻¹) := by group
          _ = b * p0⁻¹ := by rw [hb_cen, hp0_inv]
      have h2 : y = b * p0⁻¹ := by rw [hy_cen] at h1; exact h1
      have h3 : b * p0 = b * p0⁻¹ := by rw [hbp0]; exact h2
      exact (mul_left_cancel h3).symm
    have hp0_sq : p0 * p0 = 1 := by
      have h := mul_inv_cancel p0
      rwa [hp0_eq] at h
    have hp0_1 : p0 = 1 :=
      c1aEqOneOfMulSelfOdd (Work.CORE2A.bSetup_U_odd B) (c1aPcoreIn_le_self D.p B.U hp0P)
        hp0_sq
    have hy_eq : y = b := by rw [← hbp0, hp0_1, mul_one]
    rw [hy_eq]
    exact hbBc
  have hXBc : X = Bc := le_antisymm hX_le_Bc hBc_le_X
  have hX_le_NF3 : X ≤ Subgroup.normalizer (F3 : Set G) := le_trans hX_le_Bc hBc_le_NF3
  -- ## the inclusions used in the sup computation
  have hAtU : B1 ⊓ F ≤ B.U := le_trans (inf_le_left : B1 ⊓ F ≤ B1) (inf_le_left : B1 ≤ B.U)
  have hXtU : X ≤ B.U := le_trans (inf_le_left : X ≤ B1) (inf_le_left : B1 ≤ B.U)
  have hF3_le_sup : F3 ≤ (B1 ⊓ F) ⊔ (X ⊔ F3) := le_sup_of_le_right (le_sup_right : F3 ≤ X ⊔ F3)
  have hP_le_sup : P ≤ (B1 ⊓ F) ⊔ (X ⊔ F3) := le_sup_of_le_left hP_le_A
  have hBc_le_sup : Bc ≤ (B1 ⊓ F) ⊔ (X ⊔ F3) :=
    le_sup_of_le_right (le_trans hBc_le_X (le_sup_left : X ≤ X ⊔ F3))
  -- ## the three conjuncts
  refine ⟨?_, ?_, ?_⟩
  · -- `(B₁ ⊓ F) ⊔ (X ⊔ F₃) = U`
    rw [hF3inf]
    refine le_antisymm ?_ ?_
    · exact sup_le hAtU (sup_le hXtU hF3tU)
    · rw [hUeq]
      conv_lhs => rw [hF_eq]
      exact sup_le (sup_le hF3_le_sup hP_le_sup) hBc_le_sup
  · -- `(B₁ ⊓ F) ⊓ (X ⊔ F₃) = ⊥`
    rw [hF3inf, hA, hXBc]
    refine (Subgroup.eq_bot_iff_forall _).mpr ?_
    intro x hx
    obtain ⟨hxP, hxC⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨b, hbBc, f, hfF3, hbf⟩ := (c1aDir_mem_sup_of_le_normalizer hBc_le_NF3).mp hxC
    -- `f = b⁻¹ x` is fixed by `t₁` and inverted by `t₁`, hence `f = 1`
    have hbS : b ∈ Subgroup.centralizer ((B.S : Subgroup G) : Set G) :=
      (inf_le_right : Bc ≤ Subgroup.centralizer ((B.S : Subgroup G) : Set G)) hbBc
    have hb1 : b ∈ Subgroup.centralizer ({D.t1} : Set G) :=
      Subgroup.centralizer_le (fun z hz => by
        rw [Set.mem_singleton_iff] at hz
        rw [hz]
        exact D.t1_mem) hbS
    have hx1 : x ∈ Subgroup.centralizer ({D.t1} : Set G) :=
      (D.cent : P ≤ Subgroup.centralizer ({D.t1} : Set G)) hxP
    have hf_eq : f = b⁻¹ * x := by rw [← hbf]; group
    have hb1' : D.t1 * b⁻¹ * D.t1⁻¹ = b⁻¹ := by
      have h := (Subgroup.mem_centralizer_iff.mp hb1) D.t1 (Set.mem_singleton D.t1)
      have h2 : b⁻¹ * D.t1⁻¹ = D.t1⁻¹ * b⁻¹ := by
        have := congrArg (fun z : G => z⁻¹) h
        simpa using this
      calc D.t1 * b⁻¹ * D.t1⁻¹ = D.t1 * (b⁻¹ * D.t1⁻¹) := by group
        _ = D.t1 * (D.t1⁻¹ * b⁻¹) := by rw [h2]
        _ = b⁻¹ := by group
    have hx1' : D.t1 * x * D.t1⁻¹ = x := by
      have h := (Subgroup.mem_centralizer_iff.mp hx1) D.t1 (Set.mem_singleton D.t1)
      rw [h]; group
    have hf_fix : D.t1 * f * D.t1⁻¹ = f := by
      calc D.t1 * f * D.t1⁻¹ = D.t1 * (b⁻¹ * x) * D.t1⁻¹ := by rw [hf_eq]
        _ = (D.t1 * b⁻¹ * D.t1⁻¹) * (D.t1 * x * D.t1⁻¹) := by group
        _ = b⁻¹ * x := by rw [hb1', hx1']
        _ = f := hf_eq.symm
    have hf_inv : D.t1 * f * D.t1⁻¹ = f⁻¹ := hInv1 f hfF3
    have hf_eq1 : f⁻¹ = f := hf_inv.symm.trans hf_fix
    have hff : f * f = 1 := by
      have h := mul_inv_cancel f
      rwa [hf_eq1] at h
    have hf1 : f = 1 :=
      c1aEqOneOfMulSelfOdd (Work.CORE2A.bSetup_U_odd B)
        (c1aFittingIn_le B.U (hF3_le_F hfF3)) hff
    rw [← hbf, hf1, mul_one] at hxP
    -- now `b ∈ P`; `t₂` fixes `b` and inverts it, so `b = 1`
    have hb2 : b ∈ Subgroup.centralizer ({D.t2} : Set G) :=
      Subgroup.centralizer_le (fun z hz => by
        rw [Set.mem_singleton_iff] at hz
        rw [hz]
        exact D.t2_mem) hbS
    have hb_cen : D.t2 * b * D.t2⁻¹ = b := by
      have h := (Subgroup.mem_centralizer_iff.mp hb2) D.t2 (Set.mem_singleton D.t2)
      rw [h]; group
    have hb_inv : D.t2 * b * D.t2⁻¹ = b⁻¹ := D.inv b hxP
    have hb_eq : b⁻¹ = b := hb_inv.symm.trans hb_cen
    have hbb : b * b = 1 := by
      have h := mul_inv_cancel b
      rwa [hb_eq] at h
    have hb1' : b = 1 :=
      c1aEqOneOfMulSelfOdd (Work.CORE2A.bSetup_U_odd B) (c1aPcoreIn_le_self D.p B.U hxP) hbb
    rw [← hbf, hf1, mul_one]
    exact hb1'
  · -- elementwise commutation
    rw [hF3inf, hA, hXBc]
    intro a ha c hc
    obtain ⟨b, hbBc, f, hfF3, hbf⟩ := (c1aDir_mem_sup_of_le_normalizer hBc_le_NF3).mp hc
    have hcommPF3 : Bracket.bracket P F3 = ⊥ := by
      rw [hP3]
      exact c1aDirPcommF3 B.U
    have hP_cen_F3 : P ≤ Subgroup.centralizer (F3 : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hcommPF3
    have hcomm_aF3 : a * f * a⁻¹ = f := by
      have h := (Subgroup.mem_centralizer_iff.mp (hP_cen_F3 ha)) f hfF3
      rw [← h]; group
    have hcomm_aBc : a * b * a⁻¹ = b := by
      have h := hcommBcP b hbBc a ha
      rw [← h]; group
    have hmain : a * c * a⁻¹ = c := by
      rw [← hbf]
      calc a * (b * f) * a⁻¹ = (a * b * a⁻¹) * (a * f * a⁻¹) := by group
        _ = b * f := by rw [hcomm_aBc, hcomm_aF3]
    calc a * c = (a * c * a⁻¹) * a := by group
      _ = c * a := by rw [hmain]

end Work.CORE3
