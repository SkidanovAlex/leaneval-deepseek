/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# AREA CORE4 — Bender §4 (8): `A ⊴ O_p(U)` at the `Case2Ctx` level

Bender 1981, §4 (8), p. 226.  With `Q := Ω₁(Z₂(O_p(U)))` (`Qsub`) and `A` the `(p,p)`-subgroup
of `F × K₁` (`Case2EightObj h.D p P A`), Bender's case analysis on `Q` reads

* either `A = Q`, or `Z(Q) < A < Q` with `|Q : A| = p` — and then `⁅A, O_p(U)⁆ ≤ Z(Q) ≤ A`,
  i.e. `A ⊴ O_p(U)`;
* or `s` inverts `Q` — the exceptional branch, which in the present configuration is impossible
  (its content is isolated as `CtxCase3InvNormal`).

Everything except the two object-layer branches is elementary and proved here:

* `not_isCyclic_pCoreIn`, `not_isCyclic_Qsub`: `O_p(U)` and `Q = Ω₁(Z₂(O_p(U)))` are non-cyclic,
  because `A ≤ O_p(U)` is non-cyclic (Bender 1.9(ii) / BG Lemma 4.5(c));
* `omega1_centerIn_pCoreIn_le_A`: `Ω₁(Z(O_p(U))) ≤ A`.  For `z ∈ Z(O_p(U))` with `z ^ p = 1`:
  `z ∈ O_p(U) ≤ F(U)`, and `z` centralizes `P ≤ A`; by `§4 (6)` (`normalizerP_of_ctx6`)
  `N_G(P) = M`, so `z ∈ M`; by `§4 (3)` (`Case2SixThreeRaw`) `F(U) ⊓ M = K₀ ⊔ F`, and
  `A = Ω₁(K₀ ⊔ F)` (`EightAeqOmega`), so `z ∈ A`.
-/
import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.EightIdxDefs
import Submission.Work.CORE4.EightAeqOmega
import Submission.Work.CORE4.Case2EightObjExists
import Submission.Work.CORE4.Case2QsubNoncyclic
import Submission.Work.CORE4.Case2NormalizerP
import Submission.Work.CORE4.Case2NotInvNormal
import Submission.Work.CORE4.S0CentUO2
import Submission.Work.CORE4.Case2PrePlusOfCtx
import Submission.Work.CORE4.EightAnormalPcore_of_Qpos
import Submission.Work.CORE4.EightANormalFitting
import Submission.Work.CORE4.EightAnormalFitting_of_pcore
import Submission.Work.CORE4.Case2EightN9Sup
import Submission.Work.CORE4.Case2EightQfacts
import Submission.Work.CORE4.Case2SixThreeRaw
import Submission.Work.CORE4.SixThree
import Submission.Work.CORE4.A7VnotCyclicAux
import Submission.Work.CORE4.EightTrichOfCtx
import Submission.Work.CORE4.CtxCase3InvNormal

namespace Work.CORE4

open Work.GW2 Subgroup

variable {G : Type} [Group G] [Finite G]

/-! ## Elementary consequences of the object `Case2EightObj` -/

/-- `Case2Ctx` gives the `Case2Ctx6` data (§4 (1)–(6)). -/
def ctx6_of_ctx' {B : BenderSetup G} (h : Case2Ctx B) : Case2Ctx6 B :=
  ⟨h.D, h.pre, h.F_ti, h.F_cyclic⟩

/-- `|A| = p ^ 2` for the `(p,p)`-subgroup of §4 (8). -/
theorem card_A_of_obj {B : BenderSetup G} {D : Case2Data B} {p : ℕ} {P A : Subgroup G}
    (hObj : Case2EightObj D p P A) : Nat.card ↥A = p ^ 2 :=
  hObj.2.2.2.2.1

/-- Every element of `A` has `p`-th power `1`. -/
theorem exp_A_of_obj {B : BenderSetup G} {D : Case2Data B} {p : ℕ} {P A : Subgroup G}
    (hObj : Case2EightObj D p P A) : ∀ x ∈ A, x ^ p = 1 :=
  hObj.2.2.2.2.2.1

/-- `P ≤ A`. -/
theorem P_le_A_of_obj {B : BenderSetup G} {D : Case2Data B} {p : ℕ} {P A : Subgroup G}
    (hObj : Case2EightObj D p P A) : P ≤ A :=
  hObj.2.2.2.2.2.2.1

/-- `A` is not cyclic: `|A| = p ^ 2` but all its elements have `p`-th power `1`. -/
theorem not_isCyclic_A_of_obj {B : BenderSetup G} {D : Case2Data B} {p : ℕ} {P A : Subgroup G}
    (hp : p.Prime) (hObj : Case2EightObj D p P A) : ¬ IsCyclic ↥A := by
  intro hcyc
  haveI := hcyc
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥A)
  have hdvd : orderOf g ∣ p :=
    orderOf_dvd_iff_pow_eq_one.mpr
      (Subtype.ext (by simpa using exp_A_of_obj hObj (g : G) g.2))
  rw [hg, card_A_of_obj hObj] at hdvd
  have hle : p ^ 2 ≤ p := Nat.le_of_dvd hp.pos hdvd
  nlinarith [hp.two_le]

/-- `P ≠ ⊥` for `P` of prime order `p`. -/
theorem P_ne_bot_of_obj {p : ℕ} {P : Subgroup G}
    (hp : p.Prime) (hPcard : Nat.card P = p) : P ≠ ⊥ := by
  intro hbot
  rw [hbot, Subgroup.card_bot] at hPcard
  have := hp.two_le
  omega

/-! ## `O_p(U)` and `Q = Ω₁(Z₂(O_p(U)))` are non-cyclic -/

/-- **`O_p(U)` is not cyclic**: it contains the non-cyclic `A`. -/
theorem not_isCyclic_pCoreIn (I : C4Inputs) (hbc : BenderCtx G) (B : BenderSetup G)
    (h : Case2Ctx B) (p : ℕ) (P A : Subgroup G) (hp : p.Prime) (hPF : P ≤ h.D.F)
    (hPcard : Nat.card P = p) (hObj : Case2EightObj h.D p P A) :
    ¬ IsCyclic ↥(pCoreIn p B.U) := by
  have hAleR : A ≤ pCoreIn p B.U := A_le_pCoreIn I hbc B h p P A hp hPF hPcard hObj
  have hAnc : ¬ IsCyclic ↥A := not_isCyclic_A_of_obj hp hObj
  intro hcyc
  haveI := hcyc
  exact hAnc (Subgroup.isCyclic_of_le hAleR)

/-- **`p` is odd**: it divides `|F| ≤ |U|`, and `U = O(H)` has odd order. -/
theorem odd_p_of_obj (B : BenderSetup G) (h : Case2Ctx B) (p : ℕ) (P : Subgroup G)
    (hp : p.Prime) (hPF : P ≤ h.D.F) (hPcard : Nat.card P = p) : Odd p := by
  have h1 : p ∣ Nat.card ↥h.D.F := by
    rw [← hPcard]
    exact Subgroup.card_dvd_of_le hPF
  have h2 : Nat.card ↥h.D.F ∣ Nat.card ↥B.U :=
    Subgroup.card_dvd_of_le (Case2Data.F_le_U B h.D)
  exact Odd.of_dvd_nat B.U_odd (h1.trans h2)

/-- **`Q = Ω₁(Z₂(O_p(U)))` is non-cyclic** (Bender 1.9(ii) / BG Lemma 4.5(c)): `O_p(U)` is
non-cyclic, hence so is `Ω₁(Z₂(O_p(U)))`. -/
theorem not_isCyclic_Qsub (I : C4Inputs) (hbc : BenderCtx G) (B : BenderSetup G)
    (h : Case2Ctx B) (p : ℕ) (P A : Subgroup G) (hp : p.Prime) (hPF : P ≤ h.D.F)
    (hPcard : Nat.card P = p) (hObj : Case2EightObj h.D p P A) :
    ¬ IsCyclic ↥(Qsub p B) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hRnc : ¬ IsCyclic ↥(pCoreIn p B.U) :=
    not_isCyclic_pCoreIn I hbc B h p P A hp hPF hPcard hObj
  have hpodd : Odd p := odd_p_of_obj B h p P hp hPF hPcard
  rw [Qsub_eq_map_omega1UpperCentralTwo]
  intro hcyc
  haveI := hcyc
  have hWc : IsCyclic ↥(OddOrder.GroupTheory.omega1UpperCentralTwo
      ↥(pCoreIn p B.U) p) := by
    have e := (Subgroup.equivMapOfInjective
      (OddOrder.GroupTheory.omega1UpperCentralTwo ↥(pCoreIn p B.U) p)
      (pCoreIn p B.U).subtype (pCoreIn p B.U).subtype_injective).symm
    exact isCyclic_of_surjective e.toMonoidHom e.surjective
  exact not_isCyclic_omega1UpperCentralTwo hpodd (isPGroup_pCoreIn p B.U) hRnc hWc

/-! ## `Ω₁(Z(O_p(U))) ≤ A` -/

/-- **`Ω₁(Z(O_p(U))) ≤ A`** (Bender 1981, §4 (8), p. 226).

For `z ∈ Z(O_p(U))` of order dividing `p`: `z ∈ O_p(U) ≤ F(U)`, and `z` centralizes `P ≤ A`
(all elements of `A` have `p`-th power `1`, and `z` centralizes `O_p(U) ⊇ P`), so
`z ∈ C_G(P) ⊆ N_G(P) = M` (`§4 (6)`); hence `z ∈ F(U) ⊓ M = K₀ ⊔ F` (`§4 (3)`), and since
`A = Ω₁(K₀ ⊔ F)` (`EightAeqOmega`), `z ∈ A`. -/
theorem omega1_centerIn_pCoreIn_le_A (I : C4Inputs) (hbc : BenderCtx G) (B : BenderSetup G)
    (h : Case2Ctx B) (p : ℕ) (P A : Subgroup G) (hp : p.Prime) (hPF : P ≤ h.D.F)
    (hPcard : Nat.card P = p) (hObj : Case2EightObj h.D p P A) :
    omega1 p (centerIn (pCoreIn p B.U)) ≤ A := by
  have hAleR : A ≤ pCoreIn p B.U := A_le_pCoreIn I hbc B h p P A hp hPF hPcard hObj
  -- `F(U) ⊓ M = K₀ ⊔ F` (§4 (3))
  have hSix : fittingIn B.U ⊓ h.D.M =
      (fittingIn B.U ⊓ h.D.K) ⊔ h.D.F :=
    Case2SixThreeRaw I G hbc B h.D.M h.D.s h.D.K h.D.B0 h.D.F
      (B.S_le_H h.D.s_mem_S)
      (Case2Ctx.S_le_M h h.D.s_mem_S) h.D.s_order
      h.pre.U_eq (h.D.K_le B) (h.D.B0_le B) h.D.K_def h.D.B0_def h.D.F_def
  -- `A = Ω₁(K₀ ⊔ F)` (§4 (8), `EightAeqOmega`)
  have hA : A = omega1 p (Case2Data.K0 h.D ⊔ h.D.F) := by
    rw [sup_comm]
    exact (EightAeqOmega I G hbc B h p P A hp hPF hPcard hObj).2
  have hgen : omega1Set p (centerIn (pCoreIn p B.U)) ⊆ A := by
    rintro z ⟨hzZ, hzp⟩
    obtain ⟨hzR, hzcomm⟩ := mem_centerIn_iff.mp hzZ
    -- `z` centralizes `P`, hence lies in `N_G(P) = M`
    have hzcent : z ∈ centralizer (P : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (hzcomm x (hAleR (P_le_A_of_obj hObj hx))).symm
    have hzM : z ∈ h.D.M := by
      rw [← Case2NormalizerP G B h P hPF (P_ne_bot_of_obj hp hPcard)]
      exact (Subgroup.centralizer_le_normalizer (P : Set G)) hzcent
    -- `z ∈ F(U) ∩ M = K₀ ⊔ F`, and `z ^ p = 1`, so `z ∈ Ω₁(K₀ ⊔ F) = A`
    have hzFU : z ∈ fittingIn B.U := pCoreIn_le_fittingIn B.U hp hzR
    have hzK0F : z ∈ Case2Data.K0 h.D ⊔ h.D.F := by
      have hmem : z ∈ fittingIn B.U ⊓ h.D.M := ⟨hzFU, hzM⟩
      rw [hSix] at hmem
      simpa [Case2Data.K0] using hmem
    rw [hA]
    exact Subgroup.subset_closure ⟨hzK0F, hzp⟩
  rw [omega1]
  exact (Subgroup.closure_le A).mpr hgen

/-! ## The target -/

/-- **Bender 1981, §4 (8)** (p. 226): the `(p,p)`-subgroup `A` of `F ⊔ K` is normal in
`O_p(U) = pCoreIn p B.U`.

Case analysis on `Q := Ω₁(Z₂(O_p(U)))` (`EightTrichOfCtx`): if `s` inverts `Q`, the exceptional
branch (`CtxCase3InvNormal`) would force `Case2InvNormal B h.D`, which is impossible
(`not_Case2InvNormal_of_ctx`); hence `A ≤ Q` with `A = Q` or `Z(Q) < A`, and then
`⁅A, O_p(U)⁆ ≤ Z(Q) ≤ A` (`ANormalPCoreIn_of_Qsub`). -/
theorem APcoreCtx (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B),
        ¬ Work.GW2.Case2InvNormal B h.D →
        ∀ (p : ℕ) (P A : Subgroup G), p.Prime → P ≤ h.D.F → Nat.card P = p →
          Work.GW2.Case2EightObj h.D p P A →
          (A.subgroupOf (Work.GW2.pCoreIn p B.U)).Normal := by
  intro G _ _ hbc B h _hInv p P A hp hPF hPcard hObj
  have hAexp : ∀ x ∈ A, x ^ p = 1 := exp_A_of_obj hObj
  rcases EightTrichOfCtx I G hbc B h p P A hp hPF hPcard hObj with h3 | ⟨hAleQ, hpos⟩
  · -- the exceptional branch (`s` inverts `Q`) forces `Case2InvNormal`, which is impossible
    exact absurd
      (CtxCase3InvNormal I G hbc B h p P A hp hPF hPcard hObj
        (not_isCyclic_Qsub I hbc B h p P A hp hPF hPcard hObj) h3)
      (not_Case2InvNormal_of_ctx I hbc h)
  · -- cases 1–2: `A ≤ Q`, with `A = Q` or `Z(Q) < A`
    have hZle : centerIn (Qsub p B) ≤ A := by
      rcases hpos with hEq | hlt
      · exact (centerIn_le_self (Qsub p B)).trans (le_of_eq hEq.symm)
      · exact le_of_lt hlt
    exact ANormalPCoreIn_of_Qsub B p A hAleQ hZle hAexp

end Work.CORE4
