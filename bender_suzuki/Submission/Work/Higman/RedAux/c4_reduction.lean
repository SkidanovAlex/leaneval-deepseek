/-
Copyright (c) 2024. All rights reserved.

# The `C₄` exclusion: reduction of the reducible case to one endgame residual

`Work.Higman.reducible_aux` (Higman 1963, Lemma 8 in the reducible case) is proved here from the
single residual `Work.Higman.RedAux.c4Endgame`, which is the `L₁ × L₂ → L₃` configuration of
Higman's §4 Lemma 6 in the reducible shape.

The reduction is a strong induction on `Nat.card P` for the **full** `C₄` exclusion (`C4Fail`).
Given the `C₄` data:

* if `P ⧸ A` is irreducible the clean `Work.Higman.NSM.irreducible` finishes;
* otherwise take a *minimal* `ξ`-invariant normal cover `C > A` of `A`
  (`Work.Higman.MSA.exists_minimal_covering`); then `C < ⊤`, `C ⧸ A` is `ξ`-irreducible and the
  map `D ↦ D` between `A` and `C` is controlled by `hcover`;
* `⁅C,C⁆` is a `ξ`-invariant subgroup of `A`, hence `⊥`, `A²` or `A` (`RedAux.red_trichotomy`):
  * `⊥`: `C` is abelian, contradicting maximality of `A`;
  * `A`: the pair `(↥C, A.subgroupOf C)` is again a `C₄` instance of smaller order, so the
    induction hypothesis applies;
  * `A²`: then `C²` is a `ξ`-invariant subgroup of `A`, hence `⊥`, `A²` or `A`:
    * `⊥`: `C ≤ Ω₁(P) = A² ≤ A`, contradiction;
    * `A`: Higman's Lemma 7 (`MSA.higman_lemma7_msa`) makes `C` abelian, contradiction;
    * `A²`: `⁅⊤,C⁆` is a `ξ`-invariant subgroup of `A` containing `A²`, hence `A²` or `A`:
      * `A²` with `⁅A,C⁆ = A²`: `A = P² ≤ C_P(C)`, so `⁅A,C⁆ = ⊥`, contradiction;
      * `A²` with `⁅A,C⁆ = ⊥` (and `= A` impossible since `⁅A,C⁆ ≤ A² ≠ A`):
        Gorenstein–Thompson (`NSM.c4gapCentralises`);
      * `A` with `⁅A,C⁆ = ⊥`: Gorenstein–Thompson;
      * `A` with `⁅A,C⁆ = A²`: **the endgame** `RedAux.c4Endgame`.

The auxiliary facts about `ξ`-invariant subgroups of `A` and of `A²` are
`RedAux.red_trichotomy` and `NSM.powSubA2Irreducible`.
-/
import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.OmegaAux
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.MSA.basic
import Submission.Work.Higman.MSA.lemma8_clean
import Submission.Work.Higman.MSA.higman_lemma7_msa
import Submission.Work.Higman.NSM.irreducible
import Submission.Work.Higman.NSM.c4gapCentralises
import Submission.Work.Higman.NSM.c4sqAMaximal
import Submission.Work.Higman.NSM.powSubA2Irreducible
import Submission.Work.Higman.nsd_powSub_top_eq
import Submission.Work.Higman.RedAux.setup
import Submission.Work.Higman.RedAux.subgroup_transfer

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option maxHeartbeats 10000000

open scoped commutatorElement

namespace Work.Higman.RedAux

/-- **The `C₄` endgame residual.**  `P` a Suzuki 2-group, `A ⊴ P` a `ξ`-invariant abelian normal
subgroup with `Ω₁(P) ≤ A`, `⁅P,P⁆ = A`, every square of `P` in `A`, `A⁴ = 1`, `A² = Ω₁(P)` and
`|A| = |Ω₁(P)|²`; `C` a minimal `ξ`-invariant normal cover of `A` with `⁅C,C⁆ = C² = A²`,
`⁅⊤,C⁆ = A` and `⁅A,C⁆ = A²`.  This is the reducible `L₁ × L₂ → L₃` configuration of Higman §4
Lemma 6; it is the single missing input of `Work.Higman.reducible_aux`. -/
def c4Endgame : Prop :=
  ∀ (P : Type) [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P) {A C : Subgroup P},
    Work.Higman.IsXiAbelNormal h A →
    Work.Higman.omega1 P ≤ A →
    ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ = A →
    (∀ x : P, x ^ 2 ∈ A) →
    Work.Higman.powSub A 4 = ⊥ →
    Work.Higman.powSub A 2 = Work.Higman.omega1 P →
    Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2 →
    C.Normal →
    C.map (h.xi : MulAut P).toMonoidHom = C →
    A ≤ C → A ≠ C →
    (∀ E : Subgroup P, E.Normal → E.map (h.xi : MulAut P).toMonoidHom = E →
      A ≤ E → E ≤ C → E = A ∨ E = C) →
    ⁅C, C⁆ = Work.Higman.powSub A 2 →
    Work.Higman.powSub C 2 = Work.Higman.powSub A 2 →
    ⁅(⊤ : Subgroup P), C⁆ = A →
    ⁅A, C⁆ = Work.Higman.powSub A 2 →
    False

/-- **The full `C₄` exclusion at order `m`** (Higman 1963, Theorem 1 / Lemma 8): no Suzuki
2-group `P` of order `m` has a `ξ`-invariant abelian normal subgroup `A` with `Ω₁(P) ≤ A`,
`⁅P,P⁆ = A`, all squares of `P` in `A`, `A⁴ = 1`, `A² = Ω₁(P)` and `|A| = |Ω₁(P)|²`. -/
def C4Fail (m : ℕ) : Prop :=
  ∀ (P : Type) [Group P] [Finite P], Nat.card P = m →
    ∀ (h : Work.Higman.IsSuzuki2Grp P) (A : Subgroup P),
      Work.Higman.IsXiAbelNormal h A →
      Work.Higman.omega1 P ≤ A →
      ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ = A →
      (∀ x : P, x ^ 2 ∈ A) →
      Work.Higman.powSub A 4 = ⊥ →
      Work.Higman.powSub A 2 = Work.Higman.omega1 P →
      Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2 →
      False

/-- `⁅x²,y⁆ = ⁅x,⁅x,y⁆⁆ · ⁅x,y⁆²`. -/
theorem commutatorElement_sq_self' {G : Type} [Group G] (x y : G) :
    ⁅x ^ 2, y⁆ = ⁅x, ⁅x, y⁆⁆ * ⁅x, y⁆ ^ 2 := by
  simp only [commutatorElement_def, pow_two]
  group

/-- **The `C₄` exclusion, reducible case, given the endgame residual.** -/
theorem c4Fail_all_of_endgame (hEnd : c4Endgame) : ∀ m : ℕ, C4Fail m := by
  classical
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro P _ _ hcardP h A hA hNA hGs hsq hA4 htop hcard
    have hAxi : A.map (h.xi : MulAut P).toMonoidHom = A := hA.map_eq
    have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := hA.abelian
    have hmax : ∀ B : Subgroup P, Work.Higman.IsXiAbelNormal h B → A ≤ B → B = A :=
      Work.Higman.NSM.c4sqAMaximal h hAxi hAab hNA hGs hsq hA4 htop hcard
    have hA2ne : Work.Higman.powSub A 2 ≠ ⊥ := by
      intro hb
      have h1 : Nat.card ↥(Work.Higman.omega1 P) = 1 := by rw [← htop, hb, Subgroup.card_bot]
      have h4 := h.omega1_card_ge_four
      omega
    have hAne : A ≠ ⊥ := by
      intro hb
      have h1 : Nat.card ↥A = 1 := by rw [hb, Subgroup.card_bot]
      rw [h1] at hcard
      have h4 := h.omega1_card_ge_four
      nlinarith [hcard, h4]
    by_cases hirr : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
        A ≤ D → D = A ∨ D = ⊤
    · exact Work.Higman.NSM.irreducible h hAxi hAab hNA hGs hsq hA4 htop hcard hirr
    · push_neg at hirr
      obtain ⟨D₀, hD₀n, hD₀inv, hAD₀, hD₀A, hD₀top⟩ := hirr
      obtain ⟨C, hCn, hCinv, hAC, hCD₀, hCA, hcover⟩ :=
        Work.Higman.MSA.exists_minimal_covering h hD₀n hD₀inv hAD₀ hD₀A
      have hCtop : C ≠ ⊤ := fun hc => hD₀top (le_antisymm le_top (hc ▸ hCD₀))
      -- `⁅C,C⁆` is `ξ`-invariant and lies in `A`
      have hCdle : ⁅C, C⁆ ≤ A := by
        rw [← hGs]
        exact Subgroup.commutator_mono le_top le_top
      have hCdinv : (⁅C, C⁆ : Subgroup P).map (h.xi : MulAut P).toMonoidHom = ⁅C, C⁆ := by
        rw [Subgroup.map_commutator, hCinv]
      rcases red_trichotomy h A (⁅C, C⁆) hA hA4 hCdle hCdinv with hCd | hCd | hCd
      · -- `⁅C,C⁆ = ⊥`: `C` abelian, contradicting maximality of `A`
        have hCab : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x := by
          intro x hx y hy
          refine commutatorElement_eq_one_iff_mul_comm.mp ?_
          have hmem : ⁅x, y⁆ ∈ (⁅C, C⁆ : Subgroup P) :=
            Subgroup.commutator_mem_commutator hx hy
          rw [hCd] at hmem
          simpa using hmem
        exact hCA (hmax C ⟨hCn, hCinv, hCab⟩ hAC)
      · -- `⁅C,C⁆ = A²`: analyse `C²`
        have hC2le : Work.Higman.powSub C 2 ≤ A := by
          rw [Work.Higman.powSub, Subgroup.closure_le]
          rintro y ⟨x, -, rfl⟩
          exact hsq x
        have hC2inv : (Work.Higman.powSub C 2).map (h.xi : MulAut P).toMonoidHom
            = Work.Higman.powSub C 2 := Work.Higman.map_powSub (h.xi : MulAut P) hCinv 2
        rcases red_trichotomy h A (Work.Higman.powSub C 2) hA hA4 hC2le hC2inv
          with hC2 | hC2 | hC2
        · -- `C² = ⊥`: `C ≤ Ω₁(P) = A² ≤ A`
          have hCle : C ≤ Work.Higman.omega1 P := by
            intro x hx
            rw [h.mem_omega1]
            have hx2 : x ^ 2 ∈ Work.Higman.powSub C 2 := Work.Higman.pow_mem_powSub hx
            rw [hC2, Subgroup.mem_bot] at hx2
            exact hx2
          exact hCA (le_antisymm (hCle.trans hNA) hAC)
        · -- `C² = A²`: analyse `⁅⊤,C⁆`
          have hCPle : ⁅(⊤ : Subgroup P), C⁆ ≤ A := by
            rw [← hGs]; exact Subgroup.commutator_mono le_rfl le_top
          have hCPinv : (⁅(⊤ : Subgroup P), C⁆ : Subgroup P).map
              (h.xi : MulAut P).toMonoidHom = ⁅(⊤ : Subgroup P), C⁆ := by
            rw [Subgroup.map_commutator,
              Subgroup.map_top_of_surjective _ (h.xi : MulAut P).surjective, hCinv]
          have hACle : ⁅A, C⁆ ≤ Work.Higman.powSub A 2 :=
            (Subgroup.commutator_mono hAC le_rfl).trans (le_of_eq hCd)
          have hACinv : (⁅A, C⁆ : Subgroup P).map (h.xi : MulAut P).toMonoidHom = ⁅A, C⁆ := by
            rw [Subgroup.map_commutator, hAxi, hCinv]
          have hACsplit : ⁅A, C⁆ = ⊥ ∨ ⁅A, C⁆ = Work.Higman.powSub A 2 :=
            Work.Higman.NSM.powSubA2Irreducible h hA htop.symm ⁅A, C⁆ hACle hACinv
          rcases red_trichotomy h A (⁅(⊤ : Subgroup P), C⁆) hA hA4 hCPle hCPinv
            with hCP | hCP | hCP
          · -- `⁅⊤,C⁆ = ⊥` contradicts `⁅C,C⁆ = A²`
            have hle : ⁅C, C⁆ ≤ ⁅(⊤ : Subgroup P), C⁆ :=
              Subgroup.commutator_mono le_top le_rfl
            rw [hCP] at hle
            exact hA2ne (hCd ▸ le_bot_iff.mp hle)
          · -- `⁅⊤,C⁆ = A²`: then `⁅A,C⁆ = ⊥` and `A = P² ≤ C_P(C)`
            rcases hACsplit with hACbot | hACsq
            · exact Work.Higman.NSM.c4gapCentralises h hAxi hAab hNA hGs hsq hA4 htop hcard
                hA hmax hCn hCinv hAC (Ne.symm hCA) hcover hCd (fun c hc a ha =>
                  (commutatorElement_eq_one_iff_mul_comm.mp
                    (Subgroup.mem_bot.mp (by
                      have hmem : ⁅a, c⁆ ∈ (⁅A, C⁆ : Subgroup P) :=
                        Subgroup.commutator_mem_commutator ha hc
                      rw [hACbot] at hmem
                      simpa using hmem))).symm)
            · exfalso
              have hsqcent : ∀ u : P, ∀ c : P, c ∈ C → u ^ 2 * c = c * u ^ 2 := by
                intro u c hc
                have hud : ⁅u, c⁆ ∈ Work.Higman.powSub A 2 := by
                  rw [← hCP]
                  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top u) hc
                have hcent : ⁅u, c⁆ ∈ Subgroup.center P :=
                  h.omega1_le_center (htop ▸ hud)
                have hinv : ⁅u, c⁆ ^ 2 = 1 := h.mem_omega1.mp (htop ▸ hud)
                have h2 : ⁅u, ⁅u, c⁆⁆ = 1 :=
                  commutatorElement_eq_one_iff_mul_comm.mpr
                    (Subgroup.mem_center_iff.mp hcent u)
                have h4 : ⁅u ^ 2, c⁆ = 1 := by
                  rw [commutatorElement_sq_self' u c, h2, hinv, one_mul]
                exact commutatorElement_eq_one_iff_mul_comm.mp h4
              have h1 : A ≤ Subgroup.centralizer (C : Set P) := by
                rw [← Work.Higman.nsd_powSub_top_eq h hAxi hAab hGs hsq htop hcard,
                  Work.Higman.powSub, Subgroup.closure_le]
                rintro y ⟨u, -, rfl⟩
                exact Subgroup.mem_centralizer_iff.mpr (fun c hc => (hsqcent u c hc).symm)
              have h2 : ⁅A, C⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h1
              rw [hACsq] at h2
              exact hA2ne h2
          · -- `⁅⊤,C⁆ = A`: the endgame (or Gorenstein–Thompson)
            rcases hACsplit with hACbot | hACsq
            · exact Work.Higman.NSM.c4gapCentralises h hAxi hAab hNA hGs hsq hA4 htop hcard
                hA hmax hCn hCinv hAC (Ne.symm hCA) hcover hCd (fun c hc a ha =>
                  (commutatorElement_eq_one_iff_mul_comm.mp
                    (Subgroup.mem_bot.mp (by
                      have hmem : ⁅a, c⁆ ∈ (⁅A, C⁆ : Subgroup P) :=
                        Subgroup.commutator_mem_commutator ha hc
                      rw [hACbot] at hmem
                      simpa using hmem))).symm)
            · exact hEnd P h hA hNA hGs hsq hA4 htop hcard hCn hCinv hAC (Ne.symm hCA) hcover hCd hC2
                hCP hACsq
        · -- `C² = A`: Higman's Lemma 7 makes `C` abelian
          have hPhi : Work.Higman.powSub C 2 ⊔ ⁅C, C⁆ = A := by
            rw [hC2, hCd]
            exact sup_eq_left.mpr (Work.Higman.powSub_le (n := 2) (by norm_num))
          have hab : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x :=
            Work.Higman.MSA.higman_lemma7_msa h hA hCn hCinv hAC (Ne.symm hCA) hcover hPhi
              (le_of_eq hCd) 
          exact hA2ne (by
            rw [← hCd, Subgroup.commutator_eq_bot_iff_le_centralizer]
            intro x hx
            rw [Subgroup.mem_centralizer_iff]
            intro y hy
            exact (hab x hx y hy).symm)
      · -- `⁅C,C⁆ = A`: descend to `↥C` and apply the induction hypothesis
        have hni : ∃ x y : ↥C, x * y ≠ y * x := by
          by_contra hcon
          push_neg at hcon
          have hcomm : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x :=
            fun x hx y hy => congrArg Subtype.val (hcon ⟨x, hx⟩ ⟨y, hy⟩)
          have h2 : ⁅C, C⁆ ≤ (⊥ : Subgroup P) := by
            rw [Subgroup.commutator_le]
            intro x hx y hy
            rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
            exact hcomm x hx y hy
          rw [hCd, le_bot_iff] at h2
          exact hAne h2
        obtain ⟨hCSz, hCSzdef⟩ : ∃ sz : Work.Higman.IsSuzuki2Grp ↥C,
            (sz.xi : MulAut ↥C) = xiSubRG h hCinv :=
          ⟨isSuzuki2Grp_subgroupRG h hCinv (hNA.trans hAC) hni, rfl⟩
        have hCcard_lt : Nat.card ↥C < m := by
          rw [← hcardP]
          exact lt_of_le_of_ne
            (Nat.card_le_card_of_injective (Subgroup.subtype C) (Subgroup.subtype_injective C))
            (fun hcon => hCtop (Subgroup.eq_top_of_card_eq C hcon))
        have hom : Work.Higman.omega1 ↥C = (Work.Higman.omega1 P).subgroupOf C :=
          omega1_subgroupOf h hCSz
        have hA4' : Work.Higman.powSub (A.subgroupOf C) 4 = ⊥ := by
          rw [powSub_subgroupOf hAC (by norm_num : 0 < 4), hA4]
          exact Subgroup.bot_subgroupOf C
        have htop' : Work.Higman.powSub (A.subgroupOf C) 2 = Work.Higman.omega1 ↥C := by
          rw [powSub_subgroupOf hAC (by norm_num : 0 < 2), htop, hom]
        have hom2 : Nat.card ↥(Work.Higman.omega1 ↥C) = Nat.card ↥(Work.Higman.omega1 P) := by
          rw [hom, card_subgroupOf (hNA.trans hAC)]
        have hcard' : Nat.card ↥(A.subgroupOf C)
            = (Nat.card ↥(Work.Higman.omega1 ↥C)) ^ 2 := by
          rw [card_subgroupOf hAC, hom2]
          exact hcard
        have hAisC : Work.Higman.IsXiAbelNormal hCSz (A.subgroupOf C) :=
          ⟨hA.normal.subgroupOf C,
            (by rw [hCSzdef]
                exact map_xiSubRG_subgroupOf h hCinv hAxi (hAD := hAC)),
            (fun x hx y hy => Subtype.ext
              (hAab x (Subgroup.mem_subgroupOf.mp hx) y (Subgroup.mem_subgroupOf.mp hy)))⟩
        have hNAC : Work.Higman.omega1 ↥C ≤ A.subgroupOf C := by
          rw [hom]; exact Subgroup.subgroupOf_mono C hNA
        have hGsC : ⁅(⊤ : Subgroup ↥C), (⊤ : Subgroup ↥C)⁆ = A.subgroupOf C :=
          commutator_top_subgroupOf hAC hCd
        have hsqC : ∀ x : ↥C, x ^ 2 ∈ A.subgroupOf C :=
          fun x => Subgroup.mem_subgroupOf.mpr (hsq (x : P))
        exact ih (Nat.card ↥C) hCcard_lt ↥C rfl hCSz (A.subgroupOf C) hAisC hNAC hGsC hsqC
          hA4' htop' hcard'

/-- **The `C₄`-shape is excluded when `P / A` is reducible** (Higman 1963, Lemma 8 / §4
Lemma 6), given the endgame residual `RedAux.c4Endgame`. -/
theorem reducible_aux_of_endgame (hEnd : c4Endgame) {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P}
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hNA : Work.Higman.omega1 P ≤ A)
    (hGs : commutator P = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hnirr : ¬ (∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D = A ∨ D = ⊤)) :
    False := by
  have hAn : A.Normal := by rw [← hGs]; exact Subgroup.commutator_normal ⊤ ⊤
  have hGs' : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ = A := by
    simpa [commutator] using hGs
  have hfail := c4Fail_all_of_endgame hEnd (Nat.card P)
  exact hfail P rfl h A ⟨hAn, hAxi, hAab⟩ hNA hGs' hsq hA4 htop hcard

end Work.Higman.RedAux
