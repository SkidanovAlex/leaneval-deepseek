import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.EightIdxDefs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2EightObjExists
import Submission.Work.CORE4.Case2EightA_le_FsupK0
import Submission.Work.CORE4.Case2Eight
import Submission.Work.CORE4.Case2SixThreeRaw
import Submission.Work.CORE4.SixThree
import Submission.Work.CORE4.EightAnormalFitting_of_pcore

namespace Work.CORE4

open Subgroup
open scoped commutatorElement

set_option linter.unusedVariables false

variable {G : Type} [Group G] [Finite G]

/-! ## Auxiliary: `Ω₁` and `Z₂` inside their group -/

theorem n9_omega1_le_self (p : ℕ) (X : Subgroup G) : omega1 p X ≤ X := by
  rw [omega1]
  exact (Subgroup.closure_le X).mpr fun _ hx => hx.1

theorem n9_z2_le_self (X : Subgroup G) : z2 X ≤ X := by
  rw [z2]
  exact (Subgroup.closure_le X).mpr fun _ hx => hx.1

/-- `Q = Ω₁(Z₂(O_p(U))) ≤ O_p(U)`. -/
theorem n9_Qsub_le_pCoreIn (B : Work.GW2.BenderSetup G) (p : ℕ) :
    Qsub p B ≤ Work.GW2.pCoreIn p B.U :=
  (n9_omega1_le_self p _).trans (n9_z2_le_self _)

/-- `Q = Ω₁(Z₂(O_p(U))) ≤ Z₂(O_p(U))`. -/
theorem n9_Qsub_le_z2 (B : Work.GW2.BenderSetup G) (p : ℕ) :
    Qsub p B ≤ z2 (Work.GW2.pCoreIn p B.U) :=
  n9_omega1_le_self p _

/-! ## The defining set of `z2` is already a subgroup

`z2 P` is the closure of `z2Set P = {x ∈ P | ⁅x, P⁆ ≤ Z(P)}`.  That set is closed under
multiplication (`⁅x y, z⁆ = x ⁅y, z⁆ x⁻¹ · ⁅x, z⁆`, and `Z(P) ⊴ P`) and under inversion
(`⁅x⁻¹, z⁆ = x⁻¹ ⁅x, z⁆⁻¹ x`), so the closure adds nothing. -/

/-- The set `z2Set P` as a subgroup of `G`. -/
def n9_Z2 (P : Subgroup G) : Subgroup G where
  carrier := z2Set P
  one_mem' := ⟨P.one_mem, by
    intro y hy z hz
    rw [commutatorElement_one_left, commutatorElement_one_left]⟩
  mul_mem' := by
    intro x y hx hy
    obtain ⟨hxP, hxprop⟩ := hx
    obtain ⟨hyP, hyprop⟩ := hy
    refine ⟨P.mul_mem hxP hyP, fun w hw z hz => ?_⟩
    have hcx : ∀ t ∈ P, ⁅x, w⁆ * t = t * ⁅x, w⁆ := fun t ht =>
      commutatorElement_eq_one_iff_mul_comm.mp (hxprop w hw t ht)
    have hcy : ∀ t ∈ P, ⁅y, w⁆ * t = t * ⁅y, w⁆ := fun t ht =>
      commutatorElement_eq_one_iff_mul_comm.mp (hyprop w hw t ht)
    have heP : ∀ t ∈ P, (x * ⁅y, w⁆ * x⁻¹) * t = t * (x * ⁅y, w⁆ * x⁻¹) := by
      intro t ht
      have ht' : x⁻¹ * t * x ∈ P := P.mul_mem (P.mul_mem (P.inv_mem hxP) ht) hxP
      calc (x * ⁅y, w⁆ * x⁻¹) * t = x * (⁅y, w⁆ * (x⁻¹ * t * x)) * x⁻¹ := by group
        _ = x * ((x⁻¹ * t * x) * ⁅y, w⁆) * x⁻¹ := by rw [hcy (x⁻¹ * t * x) ht']
        _ = t * (x * ⁅y, w⁆ * x⁻¹) := by group
    rw [commutatorElement_mul_left_eq_conj_mul x y w,
      commutatorElement_mul_left_eq_conj_mul (x * ⁅y, w⁆ * x⁻¹) ⁅x, w⁆ z,
      commutatorElement_eq_one_iff_mul_comm.mpr (heP z hz),
      commutatorElement_eq_one_iff_mul_comm.mpr (hcx z hz)]
    group
  inv_mem' := by
    intro x hx
    obtain ⟨hxP, hxprop⟩ := hx
    refine ⟨P.inv_mem hxP, fun w hw z hz => ?_⟩
    have hcx : ∀ t ∈ P, ⁅x, w⁆ * t = t * ⁅x, w⁆ := fun t ht =>
      commutatorElement_eq_one_iff_mul_comm.mp (hxprop w hw t ht)
    have hcinv : ∀ t ∈ P, ⁅x, w⁆⁻¹ * t = t * ⁅x, w⁆⁻¹ := by
      intro t ht
      calc ⁅x, w⁆⁻¹ * t = ⁅x, w⁆⁻¹ * (t * ⁅x, w⁆) * ⁅x, w⁆⁻¹ := by group
        _ = ⁅x, w⁆⁻¹ * (⁅x, w⁆ * t) * ⁅x, w⁆⁻¹ := by rw [hcx t ht]
        _ = t * ⁅x, w⁆⁻¹ := by group
    have heP : ∀ t ∈ P, (x⁻¹ * ⁅x, w⁆⁻¹ * x) * t = t * (x⁻¹ * ⁅x, w⁆⁻¹ * x) := by
      intro t ht
      have ht' : x * t * x⁻¹ ∈ P := P.mul_mem (P.mul_mem hxP ht) (P.inv_mem hxP)
      calc (x⁻¹ * ⁅x, w⁆⁻¹ * x) * t = x⁻¹ * (⁅x, w⁆⁻¹ * (x * t * x⁻¹)) * x := by group
        _ = x⁻¹ * ((x * t * x⁻¹) * ⁅x, w⁆⁻¹) * x := by rw [hcinv (x * t * x⁻¹) ht']
        _ = t * (x⁻¹ * ⁅x, w⁆⁻¹ * x) := by group
    rw [commutatorElement_inv_left]
    have heq : x⁻¹ * ⁅w, x⁆ * x = x⁻¹ * ⁅x, w⁆⁻¹ * x := by
      rw [commutatorElement_inv]
    rw [heq]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (heP z hz)

/-- **`z2 P` is the strong second centre**: `x ∈ z2 P` really does satisfy `⁅x, P⁆ ≤ Z(P)`. -/
theorem n9_mem_z2_iff (P : Subgroup G) (x : G) :
    x ∈ z2 P ↔ x ∈ P ∧ ∀ y ∈ P, ∀ z ∈ P, ⁅⁅x, y⁆, z⁆ = 1 := by
  have hle1 : z2 P ≤ n9_Z2 P := by
    rw [z2]
    exact (Subgroup.closure_le (n9_Z2 P)).mpr fun _ hx => hx
  have hle2 : n9_Z2 P ≤ z2 P := fun _ hx => Subgroup.subset_closure hx
  rw [le_antisymm hle1 hle2]
  exact Iff.rfl

/-! ## Bender §4 (8), case 2: `A ⊴ O_p(U)`

In Bender's trichotomy middle case one has `Z(Q) ≤ A ≤ Q` for `Q := Ω₁(Z₂(O_p(U)))`.  An element
`a ∈ A` lies in `Q ≤ Z₂(O_p(U))`, so it sends `O_p(U)` into its centre, and `a` has order
dividing `p` (`x^p = 1` on `A`); hence `⁅a, y⁆ ∈ Ω₁(Z(O_p(U))) ⊆ Q` for every `y ∈ O_p(U)`, and
`⁅a, y⁆` is centralised by all of `Q`, i.e. lies in `Z(Q) ≤ A`. -/

theorem ANormalPCoreIn_of_Qsub (B : Work.GW2.BenderSetup G) (p : ℕ) (A : Subgroup G)
    (hAleQ : A ≤ Qsub p B) (hZle : centerIn (Qsub p B) ≤ A)
    (hAexp : ∀ x ∈ A, x ^ p = 1) :
    (A.subgroupOf (Work.GW2.pCoreIn p B.U)).Normal := by
  have hAleP : A ≤ Work.GW2.pCoreIn p B.U := hAleQ.trans (n9_Qsub_le_pCoreIn B p)
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hAleP,
    Subgroup.le_normalizer_iff_commutator_le_right, Subgroup.commutator_comm]
  refine Subgroup.commutator_le.mpr ?_
  intro a ha y hy
  have haz2 : a ∈ z2 (Work.GW2.pCoreIn p B.U) := n9_Qsub_le_z2 B p (hAleQ ha)
  have hcen : ∀ z ∈ Work.GW2.pCoreIn p B.U, ⁅⁅a, y⁆, z⁆ = 1 :=
    (n9_mem_z2_iff _ a).mp haz2 |>.2 y hy
  have hcP : ⁅a, y⁆ ∈ Work.GW2.pCoreIn p B.U :=
    Subgroup.commutator_le_of_le hAleP le_rfl (Subgroup.commutator_mem_commutator ha hy)
  have hcQ : ⁅a, y⁆ ∈ Qsub p B := by
    show ⁅a, y⁆ ∈ Subgroup.closure (omega1Set p (z2 (Work.GW2.pCoreIn p B.U)))
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · refine (n9_mem_z2_iff _ _).mpr ⟨hcP, fun y' hy' z' hz' => ?_⟩
      rw [hcen y' hy']
      exact commutatorElement_one_left z'
    · have hcomm : Commute a ⁅a, y⁆ := by
        refine commutatorElement_eq_one_iff_commute.mp ?_
        have h1 : ⁅a, ⁅a, y⁆⁆⁻¹ = 1 := by rw [commutatorElement_inv, hcen a (hAleP ha)]
        exact inv_eq_one.mp h1
      rw [Commute.commutatorElement_pow_left hcomm p, hAexp a ha, commutatorElement_one_left]
  have hcZ : ⁅a, y⁆ ∈ centerIn (Qsub p B) := by
    refine Subgroup.mem_map.mpr ⟨⟨⁅a, y⁆, hcQ⟩, ?_, rfl⟩
    refine Subgroup.mem_center_iff.mpr fun t => Subtype.ext ?_
    exact (commutatorElement_eq_one_iff_mul_comm.mp
      (hcen t ((n9_Qsub_le_pCoreIn B p) t.2))).symm
  exact hZle hcZ

/-! ## Bender §4 (8), case 2: `(U ⊓ M) ⊔ F(U) ≤ N_U(A)` -/

/-- `(U ⊓ M) ⊔ F(U) ≤ N_U(A)`: `U ⊓ M ≤ N_G(A)` by the uniqueness of `A` (Bender §4 (8)), and
`F(U) ≤ N_G(A)` because `A ≤ O_p(U) ≤ F(U)`, `A ⊴ O_p(U)` (the case-2 hypothesis `Z(Q) ≤ A`)
and the `p'`-part of the nilpotent `F(U)` centralises `O_p(U)`. -/
theorem Case2EightN9Sup (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G → ∀ B : Work.GW2.BenderSetup G,
      Work.GW2.Case2 B → ∀ C : Work.GW2.Case2Ctx6 B, Work.GW2.Case2PrePlus B C.D →
        Work.GW2.Case2SevenFacts B C.D →
        ∀ (p : ℕ) (P A : Subgroup G), p.Prime → P ≤ C.D.F → Nat.card P = p →
          Work.GW2.Case2EightObj C.D p P A →
          A ≤ Work.CORE4.Qsub p B → Work.CORE4.centerIn (Work.CORE4.Qsub p B) < A →
            A < Work.CORE4.Qsub p B → A.relIndex (Work.CORE4.Qsub p B) = p →
            (B.U ⊓ C.D.M) ⊔ Work.GW2.fittingIn B.U ≤
              B.U ⊓ Subgroup.normalizer (A : Set G) := by
  intro G _ _ hbc B h2 C hplus h7 p P A hp hPF hPcard hObj hAleQ hZlt hAlt hidx
  -- `A ≤ F(U)`
  have hAleFU : A ≤ Work.GW2.fittingIn B.U :=
    (Case2EightA_le_FsupK0 I G hbc B h2 C hplus h7 p P A hp hPF hPcard hObj).trans
      (sup_le (Work.GW2.Case2Data.F_le_fitting B C.D) (by
        rw [Work.GW2.Case2Data.K0]
        exact inf_le_left))
  -- `A` is a `p`-group of exponent `p`
  have hAcard : Nat.card ↥A = p ^ 2 := hObj.2.2.2.2.1
  have hAp : IsPGroup p ↥A := IsPGroup.of_card (n := 2) (by rw [hAcard])
  have hAexp : ∀ x ∈ A, x ^ p = 1 := hObj.2.2.2.2.2.1
  -- `A ≤ O_p(U)` and `A ⊴ O_p(U)`
  have hAleP : A ≤ Work.GW2.pCoreIn p B.U := hAleQ.trans (n9_Qsub_le_pCoreIn B p)
  have hAnOp : (A.subgroupOf (Work.GW2.pCoreIn p B.U)).Normal :=
    ANormalPCoreIn_of_Qsub B p A hAleQ hZlt.le hAexp
  -- hence `A ⊴ F(U)`, so `F(U) ≤ N_G(A)`
  have hAn : (A.subgroupOf (Work.GW2.fittingIn B.U)).Normal :=
    EightAnormalFitting_of_pcore p hp A hAleFU hAp hAleP hAnOp
  have hFUleN : Work.GW2.fittingIn B.U ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAleFU).mp hAn
  have hFUleU : Work.GW2.fittingIn B.U ≤ B.U := Subgroup.map_subtype_le _
  refine sup_le (le_inf inf_le_left ?_) (le_inf hFUleU hFUleN)
  exact Case2Eight_le_normalizer_A I B C p P A hObj

end Work.CORE4
