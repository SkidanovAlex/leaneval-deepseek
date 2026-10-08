import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.CharBridge
import Submission.Work.BG.S_le_H
import Submission.Work.GLUE.InBridge
import Submission.OddOrder.GroupTheory.SubgroupInAmbient

/-!
# Area BG: setup for `Work.BG.lemma33Case1b` (BG Lemma 3.3, first case)

The conjugation action `φS` of the Sylow `2`-subgroup `D.S` on `U = O(H) = ↥(Uin C)`, its
fixed-point subgroup `C_U(S)`, and the elementary lemmas about them that both the target file
and the delegated pieces use.

Everything here is in the vocabulary of `Work.BG`/`Work.GW2.C16`; the main target
`Work.BG.lemma33Case1b` (in `Submission.Work.BG.lemma33Case1b`) imports this module.
-/

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Subgroup

variable {G : Type} [Group G] [Finite G]

/-! ## 1. `U = O(H)` is normalized by `H ⊇ S` -/

/-- `H` normalizes `U = O(H)`. -/
theorem l33_H_le_normalizer_U (D : BGData G) : D.H ≤ Subgroup.normalizer D.U := by
  have h : D.U = OddOrder.GroupTheory.opiCoreInG {q : ℕ | q ≠ 2} D.H :=
    Work.GW2.oddCoreIn_eq_opiCoreInG D.H
  rw [h]
  exact OddOrder.GroupTheory.le_normalizer_opiCoreInG {q : ℕ | q ≠ 2} D.H

/-- Conjugation by `s ∈ S` maps `U` into itself. -/
theorem l33_S_conj_mem_U (D : BGData G) {s x : G} (hs : s ∈ (D.S : Subgroup G)) (hx : x ∈ D.U) :
    s * x * s⁻¹ ∈ D.U := by
  have hsH : s ∈ D.H := S_le_H D hs
  have hnorm : s ∈ Subgroup.normalizer D.U := l33_H_le_normalizer_U D hsH
  rw [Subgroup.mem_normalizer_iff] at hnorm
  exact (hnorm x).mp hx

/-- `u ∈ C.P.U` is closed under conjugation by `s ∈ D.S`, in the notation of `C` (`C.P.U = D.U`
by `Compat`). -/
theorem l33_conj_mem_CPU (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C)
    {s x : G} (hs : s ∈ (D.S : Subgroup G)) (hx : x ∈ C.P.U) : s * x * s⁻¹ ∈ C.P.U := by
  rw [hDC.U_eq]
  exact l33_S_conj_mem_U D hs (by rwa [hDC.U_eq] at hx)

/-- The element of `↥(Uin C)` attached to an element of `C.P.U`. -/
theorem l33_mem_Uin (C : Sec2Ctx G) {w : G} (hw : w ∈ C.P.U) :
    (⟨w, C.P.U_le_H0 hw⟩ : ↥C.P.H0) ∈ Uin C := by
  rw [Subgroup.mem_subgroupOf]
  exact hw

/-! ## 2. The conjugation action `φS : S →* MulAut U` and its fixed points -/

section Action

variable (D : BGData G) (C : Sec2Ctx G)

/-- Conjugation by `s ∈ S` as an automorphism of `↥(Uin C)`. -/
noncomputable def l33_conjAutU (hDC : Compat D C) (s : ↥(D.S)) : MulAut ↥(Uin C) where
  toFun u :=
    ⟨⟨(s : G) * ((u : ↥C.P.H0) : G) * (s : G)⁻¹,
        C.P.U_le_H0 (l33_conj_mem_CPU D C hDC s.2 u.2)⟩,
      l33_mem_Uin C (l33_conj_mem_CPU D C hDC s.2 u.2)⟩
  invFun u :=
    ⟨⟨(s : G)⁻¹ * ((u : ↥C.P.H0) : G) * (s : G),
        C.P.U_le_H0 (by simpa using l33_conj_mem_CPU D C hDC (inv_mem s.2) u.2)⟩,
      l33_mem_Uin C (by simpa using l33_conj_mem_CPU D C hDC (inv_mem s.2) u.2)⟩
  left_inv u := by
    apply Subtype.ext; apply Subtype.ext
    simp only [Subtype.coe_mk]
    group
  right_inv u := by
    apply Subtype.ext; apply Subtype.ext
    simp only [Subtype.coe_mk]
    group
  map_mul' u v := by
    apply Subtype.ext; apply Subtype.ext
    simp only [Subtype.coe_mk, Subgroup.coe_mul]
    group

/-- The conjugation action of the Sylow `2`-subgroup `S` on `U = O(H)`. -/
noncomputable def l33_phiS (hDC : Compat D C) : ↥(D.S) →* MulAut ↥(Uin C) where
  toFun s := l33_conjAutU D C hDC s
  map_one' := by
    apply MulEquiv.ext
    intro u
    apply Subtype.ext; apply Subtype.ext
    show (↑(1 : ↥(D.S)) : G) * ((u : ↥C.P.H0) : G) * (↑(1 : ↥(D.S)) : G)⁻¹
      = ((u : ↥C.P.H0) : G)
    simp
  map_mul' a b := by
    apply MulEquiv.ext
    intro u
    apply Subtype.ext; apply Subtype.ext
    show (↑(a * b) : G) * ((u : ↥C.P.H0) : G) * (↑(a * b) : G)⁻¹
      = (↑a : G) * ((↑b : G) * ((u : ↥C.P.H0) : G) * (↑b : G)⁻¹) * (↑a : G)⁻¹
    rw [Subgroup.coe_mul]
    group

end Action

/-- Unfolding of the action: `φS s` is conjugation by `s`. -/
theorem l33_phiS_apply (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C)
    (s : ↥(D.S)) (u : ↥(Uin C)) :
    (((l33_phiS D C hDC s u : ↥(Uin C)) : ↥C.P.H0) : G)
      = (s : G) * ((u : ↥C.P.H0) : G) * (s : G)⁻¹ := rfl

/-- The fixed points of the `S`-action on `U` are `C_U(S)`. -/
theorem l33_mem_fixed (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C)
    (u : ↥(Uin C)) :
    u ∈ fixedSubgroupS (l33_phiS D C hDC) ↔
      ∀ s : ↥(D.S), (s : G) * ((u : ↥C.P.H0) : G) * (s : G)⁻¹ = ((u : ↥C.P.H0) : G) := by
  rw [mem_fixedSubgroupS]
  constructor
  · intro h s
    have h' := congrArg (fun x : ↥(Uin C) => ((x : ↥C.P.H0) : G)) (h s)
    simpa [l33_phiS_apply D C hDC s u] using h'
  · intro h s
    refine Subtype.ext (Subtype.ext ?_)
    rw [l33_phiS_apply D C hDC s u]
    exact h s

/-- The fixed points of the `S`-action, in the `∈ D.S`-form. -/
theorem l33_mem_fixed' (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C)
    (u : ↥(Uin C)) :
    u ∈ fixedSubgroupS (l33_phiS D C hDC) ↔
      ∀ g ∈ (D.S : Subgroup G), g * ((u : ↥C.P.H0) : G) * g⁻¹ = ((u : ↥C.P.H0) : G) := by
  rw [l33_mem_fixed D C hDC u]
  constructor
  · intro h g hg
    exact h ⟨g, hg⟩
  · intro h s
    exact h (s : G) s.2

/-- `S` is contained in the centralizer of every element of `C_U(S)`. -/
theorem l33_fixed_centralizes (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C)
    {u : ↥(Uin C)} (hu : u ∈ fixedSubgroupS (l33_phiS D C hDC)) :
    (D.S : Subgroup G) ≤ Subgroup.centralizer ({((u : ↥C.P.H0) : G)} : Set G) := by
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  have h := (l33_mem_fixed' D C hDC u).mp hu g hg
  have h2 : (g * ((u : ↥C.P.H0) : G)) * g⁻¹ = ((u : ↥C.P.H0) : G) := h
  have h3 : g * ((u : ↥C.P.H0) : G) = ((u : ↥C.P.H0) : G) * g := by
    have := congrArg (fun y => y * g) h2
    simpa [mul_assoc] using this
  exact h3.symm

/-- An element of `C_U(S)` commutes with `D.t1` (which is `C.s`). -/
theorem l33_commute_t1 (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C)
    {u : ↥(Uin C)} (hu : u ∈ fixedSubgroupS (l33_phiS D C hDC)) :
    D.t1 * ((u : ↥C.P.H0) : G) = ((u : ↥C.P.H0) : G) * D.t1 := by
  have h := (l33_mem_fixed' D C hDC u).mp hu D.t1 D.t1_mem
  have h2 : (D.t1 * ((u : ↥C.P.H0) : G)) * D.t1⁻¹ = ((u : ↥C.P.H0) : G) := h
  have h3 : D.t1 * ((u : ↥C.P.H0) : G) = ((u : ↥C.P.H0) : G) * D.t1 := by
    have := congrArg (fun y => y * D.t1) h2
    simpa [mul_assoc] using this
  exact h3

/-- The `s`-conjugate of a class function of `H₀` has the same value at a point of `C_U(S)`:
`C.s = D.t1` acts trivially there. -/
theorem l33_sconj_apply (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C)
    {u : ↥(Uin C)} (hu : u ∈ fixedSubgroupS (l33_phiS D C hDC))
    (ξ : ClassFunction ↥C.P.H0 ℂ) :
    sconj C ξ (u : ↥C.P.H0) = ξ (u : ↥C.P.H0) := by
  have hcomm := l33_commute_t1 D C hDC hu
  have hone : (conjMulEquiv C.P C.s).toMonoidHom (u : ↥C.P.H0) = (u : ↥C.P.H0) := by
    have h : (conjMulEquiv C.P C.s) (u : ↥C.P.H0) = (u : ↥C.P.H0) := by
      refine Subtype.ext ?_
      rw [conjMulEquiv_apply, hDC.s_eq]
      rw [show D.t1 * ((u : ↥C.P.H0) : G) = ((u : ↥C.P.H0) : G) * D.t1 from hcomm]
      group
    simpa using h
  rw [sconj, conjByH]
  simp only [ClassFunction.compHom_apply, hone]

/-! ## 3. `S` is a `2`-group and `U` has odd order -/

open ClassFunction in
/-- `S` is a `2`-group. -/
theorem l33_isPGroup_S (D : BGData G) : IsPGroup 2 ↥(D.S) := (D.S).isPGroup'

open ClassFunction in
/-- `U = O(H)` has odd order. -/
theorem l33_odd_card_U (D : BGData G) : Odd (Nat.card ↥D.U) := by
  haveI : Fintype ↥D.H := Fintype.ofFinite _
  have e : ↥(Work.GW2.oddCore ↥D.H) ≃* ↥D.U :=
    Subgroup.equivMapOfInjective (Work.GW2.oddCore ↥D.H) D.H.subtype D.H.subtype_injective
  rw [← Nat.card_congr e.toEquiv]
  exact Work.GW2.odd_card_oddCore (G := ↥D.H)

open ClassFunction in
/-- `↥(Uin C)` has odd order. -/
theorem l33_odd_card_Uin (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C) :
    Odd (Nat.card ↥(Uin C)) := by
  have e : ↥(Uin C) ≃* ↥C.P.U := Subgroup.subgroupOfEquivOfLe C.P.U_le_H0
  rw [Nat.card_congr e.toEquiv, hDC.U_eq]
  exact l33_odd_card_U D

open ClassFunction in
/-- `↥(fixedSubgroupS (l33_phiS D C hDC))` has odd order. -/
theorem l33_odd_card_fixed (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C) :
    Odd (Nat.card ↥(fixedSubgroupS (l33_phiS D C hDC))) :=
  Odd.of_dvd_nat (l33_odd_card_Uin D C hDC) (Subgroup.card_subgroup_dvd_card _)

end Work.BG
