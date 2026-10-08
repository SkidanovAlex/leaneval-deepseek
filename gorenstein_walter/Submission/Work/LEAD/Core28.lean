/- Ported (gw_stage, 2026-10-08) from the lead design file `Submission/Work/_design_gw/Core28.lean`;
   content unchanged except this header. Namespace `Work.GW2.C28`. -/
/-
GW design pass 28 (lead's design file; NOT a fleet file).

# Bender §4 (8), case 3 ("`s` inverts `Q`"): the producer that replaces (α)

Bender p. 226 (page image, authoritative):
  "In the third case, `s` inverts `C_{F(U)}(Q) = F(C_U(Q))` because `Q ⊄ M` implies
   `C_U(Q) ∩ F = 1`, and then `I_U(s) ⊆ C_U(F(C_U(Q))) = F(C_U(Q))`, hence `U = B F(U)`."

Bender does NOT claim (α) `C_U(Q) ∩ C_U(s) = 1`.  He claims the weaker
  (α')  `C_{F(U)}(Q) ∩ C_U(s) = 1`,
which follows from §4 (5) `C_{F(U)}(s) = F` (here: `Case2Pre.B0_eq` + `Case2Data.F_def`, both
ALREADY in `Case2Ctx6`) and the TI property (6) (`Case2Ctx6.F_ti`).  So nothing new is needed
from the producer `Case2Setup9`: (5) is `C.pre`'s last conjunct `D.B0 = B.U ⊓ C_G(s)`.

With `Y := F(U) ⊓ C_G(Q)`:
1. `Q ⊄ M`: else `Q ⊆ I_{U∩M}(s) = K` (`K_def`), cyclic (`Case2Pre.K_cyclic`); `Q` is not.
2. (α'): `y ∈ Y ∩ C(s)` ⇒ `y ∈ U ∩ C(s) ∩ F(U) = B₀ ∩ F(U) = F`; take `q ∈ Q ∖ M`, then
   `y = q y q⁻¹ ∈ F ∩ F^q = 1`.                                   [`case3Fix`, PROVED]
3. `s` acts fixed-point-freely on `Y`, so inverts it.             [`fpfInverts`, PROVED]
4. `x ∈ I_U(s)` ⇒ `x ∈ C_U(Q) =: X` (`invSet_commute_of_inverts`) ⇒ `x` centralizes `Y`
   (same lemma inside `X`) ⇒ `x ∈ C_X(F(X))` as `F(X) ≤ Y` ⇒ `x ∈ F(X) ≤ Y`.
   Hence `I_U(s) = Y` as sets.                                    [`invSet_eq_case3Y`, PROVED]
5. `Y ⊴ Ĥ` (U ⊴ Ĥ by Thm 2.6; `F(U)`, `Q` characteristic).       [`case3Hhat`, PROVED]
   So `Case2InvNormal B C.D`.                                      [`case3InvNormal`, PROVED]
6. `Case2InvNormal` ⇒ `U = (U ⊓ M) ⊔ F(U)` (c15 + Bender 1.5).    [`U_eq_of_invNormal`, PROVED]

Then both §4 (8) leaves of route L are PROVED (`eightIndexLeaf_of_case3`,
`eightExceptLeaf_of_case3`, the latter also closing the `U ≤ N_G(A)` branch directly), so
`case2EightImpl_holds : Case2EightImpl I` is unconditional and `case2False_routeL28'` is route L
with ONLY the design-27 count leaves (hL2 hCopy hFour hY hZ) open.  All `#print axioms` clean.
GAP: `Core28_case3.g` (5712 configurations, 0 fails; (α) strictly stronger in 40 of them).
-/
import Mathlib
import Submission.Work.CORE4.Final3
import Submission.Work.CORE4.EightIndexOfAlpha
import Submission.Work.CORE4.EightDichotomyOfTrich
import Submission.Work.CORE4.EightTrich9Holds
import Submission.Work.CORE4.Case2EightCase3U9plus
import Submission.Work.CORE4.Case2SevenCentralizer
import Submission.Work.CORE4.FittingMonotone.fittingIn_le_fittingIn_of_le_normalizer
import Submission.Work.CORE4.A4aAux.U_eq_F_sup_invSet

namespace Work.GW2.C28

open Work.GW2 Subgroup

section

variable {G : Type} [Group G] [Finite G]

/-- `Y := F(U) ⊓ C_G(Q)`, `Q = Ω₁(Z₂(O_p(U)))` (Bender's `C_{F(U)}(Q) = F(C_U(Q))`). -/
noncomputable def case3Y (B : BenderSetup G) (p : ℕ) : Subgroup G :=
  fittingIn B.U ⊓ centralizer ((Work.CORE4.Qsub p B : Subgroup G) : Set G)

theorem s_mul_s {B : BenderSetup G} (D : Case2Data B) : D.s * D.s = 1 := by
  have h : D.s ^ 2 = 1 := by rw [← D.s_order]; exact pow_orderOf_eq_one D.s
  simpa [pow_two] using h

theorem s_mem_normalizer_U {B : BenderSetup G} (D : Case2Data B) :
    D.s ∈ normalizer ((B.U : Subgroup G) : Set G) := by
  have hsH : D.s ∈ B.H := B.S_le_H D.s_mem_S
  have hUnorm : ∀ y ∈ B.U, ∀ k ∈ B.H, k * y * k⁻¹ ∈ B.U := fun y hy k hk =>
    (Subgroup.normal_subgroupOf_iff B.U_le_H).mp B.U_normal y k hy hk
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => hUnorm y hy D.s hsH, fun hy => ?_⟩
  have h2 := hUnorm (D.s * y * D.s⁻¹) hy D.s⁻¹ (B.H.inv_mem hsH)
  have h3 : D.s⁻¹ * (D.s * y * D.s⁻¹) * (D.s⁻¹)⁻¹ = y := by group
  rwa [h3] at h2

/-- Step 1: in case 3, `Q ⊄ M`. -/
theorem case3_Q_not_le_M {B : BenderSetup G} (C : Case2Ctx6 B) (p : ℕ)
    (hQnc : ¬ IsCyclic ↥(Work.CORE4.Qsub p B))
    (hinv : ∀ x ∈ Work.CORE4.Qsub p B, C.D.s * x * C.D.s⁻¹ = x⁻¹) :
    ¬ Work.CORE4.Qsub p B ≤ C.D.M := by
  intro hQM
  have hQK : Work.CORE4.Qsub p B ≤ C.D.K := by
    intro x hx
    have : x ∈ (C.D.K : Set G) := by
      rw [C.D.K_def]
      exact ⟨⟨Work.CORE4.u9_Qsub_le_U p B hx, hQM hx⟩, hinv x hx⟩
    exact this
  have : IsCyclic ↥C.D.K := Case2Pre.K_cyclic B C.D C.pre
  exact hQnc (Subgroup.isCyclic_of_le hQK)

/-- Step 2 (α'): `C_{F(U)}(Q) ∩ C(s) = 1` — uses §4 (5) (`B0_eq`, `F_def`) and (6) (`F_ti`). -/
theorem case3Fix {B : BenderSetup G} (C : Case2Ctx6 B) (p : ℕ)
    (hQnc : ¬ IsCyclic ↥(Work.CORE4.Qsub p B))
    (hinv : ∀ x ∈ Work.CORE4.Qsub p B, C.D.s * x * C.D.s⁻¹ = x⁻¹) :
    case3Y B p ⊓ centralizer ({C.D.s} : Set G) = ⊥ := by
  obtain ⟨q, hqQ, hqM⟩ := Set.not_subset.mp (case3_Q_not_le_M C p hQnc hinv)
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  obtain ⟨⟨hyFU, hyCQ⟩, hyCs⟩ := hy
  have hyU : y ∈ B.U := Subgroup.map_subtype_le _ hyFU
  have hyB0 : y ∈ C.D.B0 := by
    rw [Case2Pre.B0_eq B C.D C.pre]; exact ⟨hyU, hyCs⟩
  have hyF : y ∈ C.D.F := by rw [C.D.F_def]; exact ⟨hyB0, hyFU⟩
  have hqy : q * y * q⁻¹ = y := by
    have := (Subgroup.mem_centralizer_iff.mp hyCQ) q hqQ
    rw [this]; group
  have hyconj : y ∈ conjSub q C.D.F := by
    refine Subgroup.mem_map.mpr ⟨y, hyF, ?_⟩
    simpa [MulAut.conj_apply] using hqy
  have hti := C.F_ti q hqM
  have : y ∈ C.D.F ⊓ conjSub q C.D.F := ⟨hyF, hyconj⟩
  rw [hti] at this
  exact (Subgroup.mem_bot.mp this)

end

/-- Step 3 (pure): a fixed-point-free involutory conjugation inverts. -/
theorem fpfInverts {G : Type} [Group G] [Finite G] (Y : Subgroup G) (s : G) (hss : s * s = 1)
    (hsN : s ∈ normalizer ((Y : Subgroup G) : Set G))
    (hfix : Y ⊓ centralizer ({s} : Set G) = ⊥) :
    ∀ y ∈ Y, s * y * s⁻¹ = y⁻¹ := by
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hσ : ∀ y ∈ Y, s * y * s⁻¹ ∈ Y := fun y hy => (Subgroup.mem_normalizer_iff.mp hsN y).mp hy
  let f : ↥Y → ↥Y := fun y => ⟨(y : G)⁻¹ * (s * y * s⁻¹), Y.mul_mem (Y.inv_mem y.2) (hσ y y.2)⟩
  have hfinj : Function.Injective f := by
    intro a b hab
    have h : (a : G)⁻¹ * (s * a * s⁻¹) = (b : G)⁻¹ * (s * b * s⁻¹) := congrArg Subtype.val hab
    have hz : (b : G) * (a : G)⁻¹ ∈ Y ⊓ centralizer ({s} : Set G) := by
      refine ⟨Y.mul_mem b.2 (Y.inv_mem a.2), ?_⟩
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      rw [hg]
      have h2 : s * ((b : G) * (a : G)⁻¹) * s⁻¹ = (b : G) * (a : G)⁻¹ := by
        have h3 : (b : G) * ((a : G)⁻¹ * (s * a * s⁻¹)) * (s * (a : G) * s⁻¹)⁻¹ * (a : G)⁻¹ =
            (b : G) * ((b : G)⁻¹ * (s * b * s⁻¹)) * (s * (a : G) * s⁻¹)⁻¹ * (a : G)⁻¹ := by rw [h]
        have e1 : (b : G) * ((a : G)⁻¹ * (s * a * s⁻¹)) * (s * (a : G) * s⁻¹)⁻¹ * (a : G)⁻¹ =
            (b : G) * (a : G)⁻¹ * (a : G)⁻¹ := by group
        have e2 : (b : G) * ((b : G)⁻¹ * (s * b * s⁻¹)) * (s * (a : G) * s⁻¹)⁻¹ * (a : G)⁻¹ =
            s * ((b : G) * (a : G)⁻¹) * s⁻¹ * (a : G)⁻¹ := by group
        rw [e1, e2] at h3
        exact (mul_right_cancel h3).symm
      calc s * ((b : G) * (a : G)⁻¹) = s * ((b : G) * (a : G)⁻¹) * s⁻¹ * s := by group
        _ = (b : G) * (a : G)⁻¹ * s := by rw [h2]
    rw [hfix, Subgroup.mem_bot] at hz
    exact Subtype.ext (mul_inv_eq_one.mp hz).symm
  have hfsurj : Function.Surjective f := Finite.surjective_of_injective hfinj
  intro w hw
  obtain ⟨y, hy⟩ := hfsurj ⟨w, hw⟩
  have hwy : w = (y : G)⁻¹ * (s * y * s⁻¹) := (congrArg Subtype.val hy).symm
  rw [hwy, hsinv]
  calc s * ((y : G)⁻¹ * (s * ↑y * s)) * s = s * (y : G)⁻¹ * s * ↑y * (s * s) := by group
    _ = s * (y : G)⁻¹ * s * ↑y := by rw [hss, mul_one]
    _ = ((↑y)⁻¹ * (s * ↑y * s))⁻¹ := by
        rw [show ((↑y)⁻¹ * (s * ↑y * s))⁻¹ = s⁻¹ * (↑y : G)⁻¹ * s⁻¹ * ↑y by group, hsinv]

/-- Step 4 (pure): `I_U(s) = F(U) ⊓ C_G(Q)` when `s` inverts `Q ⊴ U` and fixes no element of
`F(U) ⊓ C_G(Q)`. -/
theorem invSet_eq_case3Y {G : Type} [Group G] [Finite G] (hft : FeitThompsonProp)
    (U Q : Subgroup G) (s : G) (hodd : Odd (Nat.card U)) (hss : s * s = 1)
    (hsU : s ∈ normalizer ((U : Subgroup G) : Set G)) (hQU : Q ≤ U)
    (hQn : (Q.subgroupOf U).Normal) (hinv : ∀ x ∈ Q, s * x * s⁻¹ = x⁻¹)
    (hfix : (fittingIn U ⊓ centralizer (Q : Set G)) ⊓ centralizer ({s} : Set G) = ⊥) :
    ((fittingIn U ⊓ centralizer (Q : Set G) : Subgroup G) : Set G) = invSet U s := by
  set Y : Subgroup G := fittingIn U ⊓ centralizer (Q : Set G) with hYdef
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  -- `s` normalizes `F(U)`
  have hsF : s ∈ normalizer ((fittingIn U : Subgroup G) : Set G) := by
    have hmapU : U.map (MulAut.conj s).toMonoidHom = U :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hsU
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
    change Subgroup.map (MulAut.conj s).toMonoidHom (fittingIn U) = fittingIn U
    rw [← Work.CORE4.FittingInConj U (MulAut.conj s), hmapU]
  -- `s` normalizes `C_G(Q)`
  have hsC : ∀ y ∈ centralizer (Q : Set G), s * y * s⁻¹ ∈ centralizer (Q : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro q hq
    have hq' : s⁻¹ * q * s ∈ Q := by
      have := hinv q hq
      have e : s⁻¹ * q * s = s * q * s⁻¹ := by rw [hsinv]
      rw [e, this]; exact Q.inv_mem hq
    have hc := hy _ hq'
    calc q * (s * y * s⁻¹) = s * ((s⁻¹ * q * s) * y) * s⁻¹ := by group
      _ = s * (y * (s⁻¹ * q * s)) * s⁻¹ := by rw [hc]
      _ = s * y * s⁻¹ * q := by group
  have hsY : s ∈ normalizer ((Y : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp hsF y).mp h1, hsC y h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp hsF y).mpr h1, ?_⟩
      have := hsC _ h2
      have e : s * (s * y * s⁻¹) * s⁻¹ = y := by
        rw [hsinv]
        calc s * (s * y * s) * s = (s * s) * y * (s * s) := by group
          _ = y := by rw [hss]; group
      rwa [e] at this
  have hinvY : ∀ y ∈ Y, s * y * s⁻¹ = y⁻¹ := fpfInverts Y s hss hsY hfix
  have hFU_le_U : fittingIn U ≤ U := Subgroup.map_subtype_le _
  ext x
  constructor
  · intro hx
    exact ⟨hFU_le_U hx.1, hinvY x hx⟩
  · intro hx
    have hxU : x ∈ U := hx.1
    have hxCQ : x ∈ centralizer (Q : Set G) :=
      Subgroup.mem_centralizer_iff.mpr (fun q hq =>
        (Work.CORE4.invSet_commute_of_inverts hodd hQU hQn hinv hxU hx q hq).symm)
    set X : Subgroup G := U ⊓ centralizer (Q : Set G) with hXdef
    have hxX : x ∈ X := ⟨hxU, hxCQ⟩
    have hYX : Y ≤ X := fun y hy => ⟨hFU_le_U hy.1, hy.2⟩
    have hXodd : Odd (Nat.card X) :=
      Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le inf_le_left)
    have hUNQ : U ≤ normalizer ((Q : Subgroup G) : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQU).mp hQn
    have hXY : X ≤ normalizer ((Y : Subgroup G) : Set G) := by
      intro z hz
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have hzF := Subgroup.mem_normalizer_iff.mp (Work.CORE4.le_normalizer_fittingIn U hz.1) y
      have hzc : z * y * z⁻¹ ∈ centralizer (Q : Set G) ↔ y ∈ centralizer (Q : Set G) := by
        constructor
        · intro h
          have := (centralizer (Q : Set G)).mul_mem
            ((centralizer (Q : Set G)).mul_mem ((centralizer (Q : Set G)).inv_mem hz.2) h) hz.2
          simpa [mul_assoc] using this
        · intro h
          exact (centralizer (Q : Set G)).mul_mem
            ((centralizer (Q : Set G)).mul_mem hz.2 h) ((centralizer (Q : Set G)).inv_mem hz.2)
      exact ⟨fun h => ⟨hzF.mp h.1, hzc.mpr h.2⟩, fun h => ⟨hzF.mpr h.1, hzc.mp h.2⟩⟩
    have hYn : (Y.subgroupOf X).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hYX).mpr hXY
    have hxY : ∀ y ∈ Y, x * y = y * x :=
      Work.CORE4.invSet_commute_of_inverts hXodd hYX hYn hinvY hxX ⟨hxX, hx.2⟩
    -- `F(X) ≤ Y`
    have hUX : U ≤ normalizer ((X : Subgroup G) : Set G) := by
      intro z hz
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have hzQ := Subgroup.mem_normalizer_iff.mp (hUNQ hz)
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨U.mul_mem (U.mul_mem hz h1) (U.inv_mem hz), ?_⟩
        replace h2 := Subgroup.mem_centralizer_iff.mp h2
        refine Subgroup.mem_centralizer_iff.mpr ?_
        intro q hq
        have hq' : z⁻¹ * q * z ∈ Q := by
          simpa using (Subgroup.mem_normalizer_iff.mp (hUNQ (U.inv_mem hz)) q).mp hq
        have hc := h2 _ hq'
        calc q * (z * y * z⁻¹) = z * ((z⁻¹ * q * z) * y) * z⁻¹ := by group
          _ = z * (y * (z⁻¹ * q * z)) * z⁻¹ := by rw [hc]
          _ = z * y * z⁻¹ * q := by group
      · rintro ⟨h1, h2⟩
        have hyU : y ∈ U := by
          have := U.mul_mem (U.mul_mem (U.inv_mem hz) h1) hz
          simpa [mul_assoc] using this
        refine ⟨hyU, ?_⟩
        replace h2 := Subgroup.mem_centralizer_iff.mp h2
        refine Subgroup.mem_centralizer_iff.mpr ?_
        intro q hq
        have hq' : z * q * z⁻¹ ∈ Q := (hzQ q).mp hq
        have hc := h2 _ hq'
        calc q * y = z⁻¹ * ((z * q * z⁻¹) * (z * y * z⁻¹)) * z := by group
          _ = z⁻¹ * ((z * y * z⁻¹) * (z * q * z⁻¹)) * z := by rw [hc]
          _ = y * q := by group
    have hFXU : fittingIn X ≤ fittingIn U :=
      Work.CORE4.FittingMonotone.fittingIn_le_fittingIn_of_le_normalizer inf_le_left hUX
    have hFXY : fittingIn X ≤ Y := fun z hz =>
      ⟨hFXU hz, ((Subgroup.map_subtype_le _ hz : z ∈ X)).2⟩
    have hsolX : Group.IsSolvable ↥X := hft ↥X hXodd
    have hxC : x ∈ centralizer ((fittingIn X : Subgroup G) : Set G) :=
      Subgroup.mem_centralizer_iff.mpr (fun z hz => (hxY z (hFXY hz)).symm)
    exact hFXY (Work.CORE4.sevenX_centralizer_fittingIn_inf_le_fittingIn X hsolX ⟨hxC, hxX⟩)

/-! ## The one new leaf -/

/-- **LEAF** (context, Thm 2.6 + characteristic chain): `Y = F(U) ⊓ C_G(Q)` is a normal subgroup
of `Ĥ` contained in `Ĥ`.

Route: `I.thm26 … |>.1 : oddCoreIn B.Hhat = B.U`, so `U ⊴ Ĥ` (`oddCore_normal`, transported as in
`Work.GW2.BenderSetup.U_normal`).  For `h ∈ Ĥ` let `φ = MulAut.conj h`; `U.map φ = U`.  Then
`(fittingIn U).map φ = fittingIn U` (`Work.CORE4.FittingInConj`), `(pCoreIn p U).map φ =
pCoreIn p U` (same proof with `pCore`, or `Work.CORE4.u9_le_normalizer_map_subtype_of_normal`
applied in `Ĥ` after showing `pCoreIn p U ⊴ Ĥ`), then `Ĥ ≤ N(z2 ·)`, `Ĥ ≤ N(omega1 p ·)` by the
generic `Work.CORE4.u9_le_normalizer_z2`, `u9_le_normalizer_omega1`; finally `N(Q) ≤ N(C_G(Q))`
and `N` of an inf.  `case3Y ≤ U ≤ H ≤ Ĥ` (`B.H_le_Hhat`).  Size 150–250. -/
def Case3HhatProp (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], BenderCtx G → ∀ (B : BenderSetup G) (p : ℕ),
    case3Y B p ≤ B.Hhat ∧ ((case3Y B p).subgroupOf B.Hhat).Normal

/-! ### Proof of the leaf `Case3HhatProp` (characteristic chain; copied from
`BMAX/le_normalizer_pCoreIn_zcenterIn_fittingIn.lean` to avoid importing BMAX vocabulary) -/

theorem characteristic_normalCore' {G : Type} [Group G] {H : Subgroup G}
    (hH : H.Characteristic) : H.normalCore.Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro φ
  haveI : (H.normalCore.map φ.toMonoidHom).Normal :=
    Subgroup.Normal.map H.normalCore_normal φ.toMonoidHom φ.surjective
  refine Subgroup.normal_le_normalCore.mpr ?_
  calc H.normalCore.map φ.toMonoidHom ≤ H.map φ.toMonoidHom := Subgroup.map_mono H.normalCore_le
    _ = H := Subgroup.characteristic_iff_map_eq.mp hH φ

theorem characteristic_sSup_normal_isPGroup' {M : Type} [Group M] (p : ℕ) :
    (sSup {N : Subgroup M | N.Normal ∧ IsPGroup p N}).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro φ
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun N hN x hx => ?_
  rw [Subgroup.mem_comap]
  exact (le_sSup (s := {N : Subgroup M | N.Normal ∧ IsPGroup p N})
    ⟨Subgroup.Normal.map hN.1 φ.toMonoidHom φ.surjective, hN.2.map φ.toMonoidHom⟩)
    (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)

theorem pCore_characteristic' {M : Type} [Group M] (p : ℕ) :
    (Work.GW2.pCore p M).Characteristic := by
  rw [Work.GW2.pCore]
  exact characteristic_normalCore' (characteristic_sSup_normal_isPGroup' (M := M) p)

theorem le_normalizer_map_subtype_of_characteristic' {G : Type} [Group G] {K C : Subgroup G}
    {H : Subgroup ↥K} (hH : H.Characteristic)
    (h : C ≤ Subgroup.normalizer (K : Set G)) :
    C ≤ Subgroup.normalizer ((H.map K.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff] at h ⊢
  intro c hc x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  let φ : ↥K ≃* ↥K := {
    toFun := fun z => ⟨c * (z : G) * c⁻¹, h c hc z z.2⟩
    invFun := fun z => ⟨c⁻¹ * (z : G) * c, by
      have hh := h c⁻¹ (C.inv_mem hc) z z.2
      rwa [inv_inv] at hh⟩
    left_inv := by intro z; ext; simp [mul_assoc]
    right_inv := by intro z; ext; simp [mul_assoc]
    map_mul' := by intro z w; ext; simp [mul_assoc] }
  refine Subgroup.mem_map.mpr ⟨φ y, ?_, rfl⟩
  exact (Subgroup.characteristic_iff_map_le.mp hH φ) (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩)

theorem mem_normalizer_fittingIn_of {G : Type} [Group G] [Finite G] {U : Subgroup G} {h : G}
    (hh : h ∈ normalizer ((U : Subgroup G) : Set G)) :
    h ∈ normalizer ((fittingIn U : Subgroup G) : Set G) := by
  have hmapU : U.map (MulAut.conj h).toMonoidHom = U :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hh
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
  change Subgroup.map (MulAut.conj h).toMonoidHom (fittingIn U) = fittingIn U
  rw [← Work.CORE4.FittingInConj U (MulAut.conj h), hmapU]

theorem mem_normalizer_centralizer_of {G : Type} [Group G] {Q : Subgroup G} {h : G}
    (hh : h ∈ normalizer ((Q : Subgroup G) : Set G)) :
    h ∈ normalizer ((centralizer (Q : Set G) : Subgroup G) : Set G) := by
  have key : ∀ k ∈ normalizer ((Q : Subgroup G) : Set G), ∀ y ∈ centralizer (Q : Set G),
      k * y * k⁻¹ ∈ centralizer (Q : Set G) := by
    intro k hk y hy
    have hy' := Subgroup.mem_centralizer_iff.mp hy
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro q hq
    have hq' : k⁻¹ * q * k ∈ Q := by
      simpa using (Subgroup.mem_normalizer_iff.mp
        ((normalizer ((Q : Subgroup G) : Set G)).inv_mem hk) q).mp hq
    have hc := hy' _ hq'
    calc q * (k * y * k⁻¹) = k * ((k⁻¹ * q * k) * y) * k⁻¹ := by group
      _ = k * (y * (k⁻¹ * q * k)) * k⁻¹ := by rw [hc]
      _ = k * y * k⁻¹ * q := by group
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key h hh y, fun hy => ?_⟩
  have := key h⁻¹ ((normalizer ((Q : Subgroup G) : Set G)).inv_mem hh) _ hy
  simpa [mul_assoc] using this

/-- **PROVED**: the leaf `Case3HhatProp` (Theorem 2.6: `U = O(Ĥ)`). -/
theorem case3Hhat (I : C4Inputs) : Case3HhatProp I := by
  intro G _ _ hbc B p
  have hU : B.Hhat ≤ normalizer ((B.U : Subgroup G) : Set G) := by
    have h := (I.thm26 G I.toolkit.ft hbc B).1
    rw [← h]
    exact Work.CORE4.u9_le_normalizer_map_subtype_of_normal (Work.GW2.oddCore_normal _)
  have hP : B.Hhat ≤ normalizer ((pCoreIn p B.U : Subgroup G) : Set G) :=
    le_normalizer_map_subtype_of_characteristic' (pCore_characteristic' (M := ↥B.U) p) hU
  have hQ : B.Hhat ≤ normalizer ((Work.CORE4.Qsub p B : Subgroup G) : Set G) := by
    unfold Work.CORE4.Qsub
    exact Work.CORE4.u9_le_normalizer_omega1 p (Work.CORE4.u9_le_normalizer_z2 hP)
  have hYle : case3Y B p ≤ B.Hhat :=
    inf_le_left.trans ((Subgroup.map_subtype_le _).trans (B.U_le_H.trans B.H_le_Hhat))
  refine ⟨hYle, (Subgroup.normal_subgroupOf_iff_le_normalizer hYle).mpr ?_⟩
  intro h hh
  have h1 := Subgroup.mem_normalizer_iff.mp (mem_normalizer_fittingIn_of (hU hh))
  have h2 := Subgroup.mem_normalizer_iff.mp (mem_normalizer_centralizer_of (hQ hh))
  rw [Subgroup.mem_normalizer_iff]
  intro y
  exact ⟨fun hy => ⟨(h1 y).mp hy.1, (h2 y).mp hy.2⟩, fun hy => ⟨(h1 y).mpr hy.1, (h2 y).mpr hy.2⟩⟩

/-- The case-3 producer, as consumed by §4 (8). -/
def Case3InvNormalProp (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], BenderCtx G → ∀ B : BenderSetup G,
    Case2 B → ∀ C : Case2Ctx6 B, Case2PrePlus B C.D → Case2SevenFacts B C.D →
    ∀ (p : ℕ) (P A : Subgroup G), p.Prime → P ≤ C.D.F → Nat.card P = p →
      Case2EightObj C.D p P A →
      ¬ IsCyclic ↥(Work.CORE4.Qsub p B) →
      (∀ x ∈ Work.CORE4.Qsub p B, C.D.s * x * C.D.s⁻¹ = x⁻¹) →
      Case2InvNormal B C.D

/-- **PROVED**: Bender's case 3 gives `I_U(s) ⊴ Ĥ`. -/
theorem case3InvNormal (I : C4Inputs) (hH : Case3HhatProp I) : Case3InvNormalProp I := by
  intro G _ _ hbc B _h2 C _hplus _h7 p P A _hp _hPF _hPcard _hobj hQnc hinv
  have hset := invSet_eq_case3Y I.toolkit.ft B.U (Work.CORE4.Qsub p B) C.D.s B.U_odd
    (s_mul_s C.D) (s_mem_normalizer_U C.D) (Work.CORE4.u9_Qsub_le_U p B)
    (Work.CORE4.u9_Qsub_normal_in_U p B) hinv (case3Fix C p hQnc hinv)
  obtain ⟨hle, hn⟩ := hH G hbc B p
  exact ⟨case3Y B p, hset, hle, hn⟩

/-- **PROVED**: `I_U(s) ⊴ Ĥ` ⇒ `U = (U ⊓ M) ⊔ F(U)` (Coprime 1.5: `I ≤ F(U)`; Bender 1.5:
`U = C_U(s) I_U(s)`; §4 (5): `C_U(s) = B₀ ≤ U ⊓ M`). -/
theorem U_eq_of_invNormal (I : C4Inputs) {G : Type} [Group G] [Finite G]
    {B : BenderSetup G} (C : Case2Ctx6 B) (hInv : Case2InvNormal B C.D) :
    B.U = (B.U ⊓ C.D.M) ⊔ fittingIn B.U := by
  obtain ⟨J, hJ, _, _⟩ := hInv
  have hodd := B.U_odd
  have hsNU := s_mem_normalizer_U C.D
  have hc15 := I.toolkit.c15 G I.toolkit.ft B.U C.D.s C.D.s_order hodd hsNU
  have hJfit : J ≤ fittingIn B.U := (hc15.2.2 J hJ).2.2
  refine le_antisymm ?_ (sup_le inf_le_left (Subgroup.map_subtype_le _))
  intro u hu
  obtain ⟨c, hc, i, hi, hci⟩ :=
    Work.CORE4.A4aAux.exists_centralizer_mul_of_odd B.U hsNU (s_mul_s C.D) hodd hu
  have hcM : c ∈ B.U ⊓ C.D.M := by
    have hcB0 : c ∈ C.D.B0 := by rw [Case2Pre.B0_eq B C.D C.pre]; exact hc
    exact Case2Data.B0_le B C.D hcB0
  have hiJ : i ∈ J := by
    have : i ∈ (J : Set G) := by rw [hJ]; exact hi
    exact this
  rw [hci]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hcM) (Subgroup.mem_sup_right (hJfit hiJ))

/-! ## Route L's two §4 (8) leaves -/

/-- **PROVED**: the dichotomy leaf `EightExceptLeafProp` from the case-3 producer. -/
theorem eightExceptLeaf_of_case3 (I : C4Inputs) (h3 : Case3InvNormalProp I) :
    Work.CORE4.EightExceptLeafProp := by
  intro G _ _ hbc B h2 C hplus h7 p P A hp hPF hPcard hobj
  by_cases hInv : Case2InvNormal B C.D
  · exact Or.inl hInv
  right
  by_cases hUNA : B.U ≤ normalizer (A : Set G)
  · have hAle0 : A ≤ C.D.F ⊔ C.D.K0 :=
      Work.CORE4.Case2EightA_le_FsupK0 I G hbc B h2 C hplus h7 p P A hp hPF hPcard hobj
    have hAleFU : A ≤ fittingIn B.U :=
      hAle0.trans (sup_le (Case2Data.F_le_fitting B C.D) inf_le_left)
    have hAnF : (A.subgroupOf (fittingIn B.U)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hAleFU).mpr
        ((Subgroup.map_subtype_le _).trans hUNA)
    refine ⟨?_, hAnF, fun hunotM => ?_⟩
    · have hu : Case2EightU B A = 1 := by
        rw [Case2EightU, inf_eq_left.mpr hUNA, Subgroup.relIndex_self]
      rw [hu]; exact hp.one_le
    · exact Work.CORE4.three_le_p0_of_not_invNormal_ctx6 I hbc B C p P A hp hPF hPcard hobj
        hAleFU hAnF hunotM
  · rcases Work.CORE4.EightTrich9Holds I G hbc B h2 C hplus h7 p P A hp hPF hPcard hobj hUNA
      with hinvQ | ⟨hAQ, hZ, hAQlt, hidx⟩
    · exact absurd (h3 G hbc B h2 C hplus h7 p P A hp hPF hPcard hobj
        (Work.CORE4.Case2EightQfacts I G hbc B h2 C hplus h7 p P A hp hPF hPcard hobj).2.2.2
        hinvQ) hInv
    · exact Work.CORE4.EightDichotomyOfTrich I G hbc B h2 C hplus h7 p P A hp hPF hPcard hobj
        hInv ⟨hAQ, Or.inr ⟨hZ, hAQlt, hidx⟩⟩

section IdxCopy
open Work.CORE4

/-- **PROVED**: the index leaf `EightIndexLeafProp` from the case-3 producer.  Body copied from
`Work.CORE4.EightIndexOfAlpha` with its (α)-branch replaced by `U_eq_of_invNormal ∘ h3`. -/
theorem eightIndexLeaf_of_case3 (I : C4Inputs) (h3 : Case3InvNormalProp I) :
    Work.CORE4.EightIndexLeafProp := by
  intro G _ _ hbc B h2 C hplus h7 p P hp hPF hPcard
  -- `B₀ ⊔ K = U ⊓ M` (§4 (5)), so the target index is `|U : (U ⊓ M) ⊔ F(U)|`.
  have hD : C.D.B0 ⊔ C.D.K ⊔ Work.GW2.fittingIn B.U
      = (B.U ⊓ C.D.M) ⊔ Work.GW2.fittingIn B.U := by
    rw [sup_comm C.D.B0 C.D.K, ← C.pre.U_eq]
  rw [hD]
  -- the `(p,p)`-subgroup `A`
  obtain ⟨A, hobj⟩ := Case2EightObjExists I G hbc B h2 C hplus h7 p P hp hPF hPcard
  have hAle : A ≤ C.D.F ⊔ C.D.K := hobj.2.2.2.1
  have hAcard : Nat.card ↥A = p ^ 2 := hobj.2.2.2.2.1
  have hAexp : ∀ x ∈ A, x ^ p = 1 := hobj.2.2.2.2.2.1
  have hPA : P ≤ A := hobj.2.2.2.2.2.2.1
  -- `P ≠ ⊥`
  have hpne : P ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hPcard
    have := hp.two_le
    omega
  -- `N_U(P) = U ⊓ M` and `N_U(P) ≤ N_G(A)`
  have hNU : B.U ⊓ Subgroup.normalizer (P : Set G) = B.U ⊓ C.D.M :=
    Case2Eight_NU B C P hPF hpne
  have h4 : B.U ⊓ Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (A : Set G) := by
    rw [hNU]; exact Case2Eight_le_normalizer_A I B C p P A hobj
  have hp0odd := Case2Eight_odd_p0 B p P A h4
  have h6a := Case2EightP0LeP1 B p P A hPA h4
  have hAcomm := Case2Eight_A_comm I B C A hAle
  have h6b := Case2EightP1Le p P A hp hPA hAcard hAexp hAcomm hPcard
  have hpodd : Odd p := by
    have h1 : p ∣ Nat.card ↥C.D.F := by rw [← hPcard]; exact Subgroup.card_dvd_of_le hPF
    exact Odd.of_dvd_nat B.U_odd (h1.trans (Subgroup.card_dvd_of_le (Case2Data.F_le_U B C.D)))
  have hp0lep := Case2Eight_p0_le_p B p P A hp0odd h6a h6b hpodd
  by_cases hUNA : B.U ≤ Subgroup.normalizer (A : Set G)
  · -- `U ≤ N_G(A)`: the index is at most `p₀`
    have hmono : ((B.U ⊓ C.D.M) ⊔ Work.GW2.fittingIn B.U).relIndex B.U
        ≤ (B.U ⊓ C.D.M).relIndex B.U := by
      refine Subgroup.relIndex_le_of_le_left le_sup_left ?_
      intro hzero
      have h := Subgroup.relIndex_mul_card (B.U ⊓ C.D.M) B.U
      rw [hzero, zero_mul] at h
      exact (Nat.card_pos (α := ↥B.U)).ne' h.symm
    have hp0eq : Work.GW2.Case2EightP0 B P A = (B.U ⊓ C.D.M).relIndex B.U := by
      show (B.U ⊓ Subgroup.normalizer (P : Set G)).relIndex
        (B.U ⊓ Subgroup.normalizer (A : Set G)) = (B.U ⊓ C.D.M).relIndex B.U
      rw [hNU, inf_eq_left.mpr hUNA]
    calc ((B.U ⊓ C.D.M) ⊔ Work.GW2.fittingIn B.U).relIndex B.U
        ≤ (B.U ⊓ C.D.M).relIndex B.U := hmono
      _ = Work.GW2.Case2EightP0 B P A := hp0eq.symm
      _ ≤ p := hp0lep
  · -- Bender's trichotomy
    rcases EightTrich9Holds I G hbc B h2 C hplus h7 p P A hp hPF hPcard hobj hUNA with
      hinv | ⟨hAleQ, hQltA, hAltQ, hrelQA⟩
    · -- case 3: `s` inverts `Q`, so `U = (U ⊓ M) ⊔ F(U)`
      rw [← U_eq_of_invNormal I C (h3 G hbc B h2 C hplus h7 p P A hp hPF hPcard hobj
            (Case2EightQfacts I G hbc B h2 C hplus h7 p P A hp hPF hPcard hobj).2.2.2 hinv),
        Subgroup.relIndex_self]
      exact le_of_lt (by have := hp.two_le; omega)
    · -- case 2: `N_U(A) = (U ⊓ M) ⊔ F(U)` and the index is `u ≤ p`
      have hu : Work.GW2.Case2EightU B A ≤ p :=
        EightN9U I G hbc B h2 C hplus h7 p P A hp hPF hPcard hobj hAleQ hQltA hAltQ hrelQA
      have hNUA : B.U ⊓ Subgroup.normalizer (A : Set G)
          = (B.U ⊓ C.D.M) ⊔ Work.GW2.fittingIn B.U :=
        le_antisymm
          (EightN9Inf I G hbc B h2 C hplus h7 p P A hp hPF hPcard hobj hAleQ hQltA hAltQ hrelQA)
          (Case2EightN9Sup I G hbc B h2 C hplus h7 p P A hp hPF hPcard hobj
            hAleQ hQltA hAltQ hrelQA)
      rw [← hNUA]
      exact hu


end IdxCopy

/-- **PROVED**: §4 (8) (`Case2EightImpl`) from the single new leaf. -/
theorem case2EightImpl_of_case3Hhat (I : C4Inputs) (hH : Case3HhatProp I) : Case2EightImpl I :=
  Case2EightImpl_of_leaves I (eightIndexLeaf_of_case3 I (case3InvNormal I hH))
    (eightExceptLeaf_of_case3 I (case3InvNormal I hH))

/-- **PROVED**: route L with the §4 (8) leaves discharged; open inputs = `Case3HhatProp` + the
design-27 count leaves. -/
theorem case2False_routeL28 (I : C4Inputs10) (hH : Case3HhatProp I.toC4Inputs)
    (hL2 : Work.GW2.C27.L2pLocalProp)
    (hCopy : Work.GW2.C27.L2pLocalProp → Work.GW2.C27.CopyLocalProp)
    (hFour : Work.GW2.C27.FourCentProp I.toC4Inputs)
    (hY : Work.GW2.C27.CopyLocalProp → Work.GW2.C27.FourCentProp I.toC4Inputs →
      Work.GW2.C27.PerYProp I.toC4Inputs)
    (hZ : Work.GW2.C27.CopyLocalProp → Work.GW2.C27.FourCentProp I.toC4Inputs →
      Work.GW2.C27.PerZProp I.toC4Inputs) : Case2FalseProp :=
  case2False_routeL I
    (eightIndexLeaf_of_case3 I.toC4Inputs (case3InvNormal I.toC4Inputs hH))
    (eightExceptLeaf_of_case3 I.toC4Inputs (case3InvNormal I.toC4Inputs hH))
    hL2 hCopy hFour hY hZ

/-- **PROVED, unconditional**: §4 (8) holds (`Case2EightImpl I`), no open leaf. -/
theorem case2EightImpl_holds (I : C4Inputs) : Case2EightImpl I :=
  case2EightImpl_of_case3Hhat I (case3Hhat I)

/-- **PROVED**: route L whose only open inputs are the design-27 count leaves. -/
theorem case2False_routeL28' (I : C4Inputs10)
    (hL2 : Work.GW2.C27.L2pLocalProp)
    (hCopy : Work.GW2.C27.L2pLocalProp → Work.GW2.C27.CopyLocalProp)
    (hFour : Work.GW2.C27.FourCentProp I.toC4Inputs)
    (hY : Work.GW2.C27.CopyLocalProp → Work.GW2.C27.FourCentProp I.toC4Inputs →
      Work.GW2.C27.PerYProp I.toC4Inputs)
    (hZ : Work.GW2.C27.CopyLocalProp → Work.GW2.C27.FourCentProp I.toC4Inputs →
      Work.GW2.C27.PerZProp I.toC4Inputs) : Case2FalseProp :=
  case2False_routeL28 I (case3Hhat I.toC4Inputs) hL2 hCopy hFour hY hZ

end Work.GW2.C28

#print axioms Work.GW2.C28.case3Fix
#print axioms Work.GW2.C28.invSet_eq_case3Y
#print axioms Work.GW2.C28.case3InvNormal
#print axioms Work.GW2.C28.U_eq_of_invNormal
#print axioms Work.GW2.C28.eightExceptLeaf_of_case3
#print axioms Work.GW2.C28.eightIndexLeaf_of_case3
#print axioms Work.GW2.C28.case2False_routeL28
#print axioms Work.GW2.C28.case3Hhat
#print axioms Work.GW2.C28.case2EightImpl_holds
#print axioms Work.GW2.C28.case2False_routeL28'
