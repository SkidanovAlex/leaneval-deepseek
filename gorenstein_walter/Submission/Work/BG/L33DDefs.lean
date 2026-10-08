import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.CharBridge
import Submission.Work.BG.S_le_H
import Submission.Work.GLUE.InBridge
import Submission.OddOrder.GroupTheory.SubgroupInAmbient

/-!
# Area BG: plumbing and `S`-invariance for the first case of BG Lemma 3.3

Definition module for `Work.BG.lemma33Case1d`: the conjugation action `phiS` of the Sylow
`2`-subgroup `D.S` on `U = O(H) = ↥(Uin C)`, its fixed-point subgroup `C_U(S)`, the fact
that `D.S = D.S₀ ⊔ ⟨t₁⟩`, and the resulting `S`-invariance criterion
`invariant_phiS` (an `H₀`-invariant and `t₁`-invariant class function of `U` is invariant
under the whole of `S`).

Everything is in the namespace `Work.BG.L33D`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Subgroup

namespace L33D

variable {G : Type} [Group G] [Finite G]

/-! ## 1. `U = O(H)` is normalized by `H ⊇ S` -/

/-- `H` normalizes `U = O(H)`. -/
theorem H_le_normalizer_U (D : BGData G) : D.H ≤ Subgroup.normalizer D.U := by
  have h : D.U = OddOrder.GroupTheory.opiCoreInG {q : ℕ | q ≠ 2} D.H :=
    Work.GW2.oddCoreIn_eq_opiCoreInG D.H
  rw [h]
  exact OddOrder.GroupTheory.le_normalizer_opiCoreInG {q : ℕ | q ≠ 2} D.H

/-- Conjugation by `s ∈ S` maps `U` into itself. -/
theorem S_conj_mem_U (D : BGData G) {s x : G} (hs : s ∈ (D.S : Subgroup G)) (hx : x ∈ D.U) :
    s * x * s⁻¹ ∈ D.U := by
  have hsH : s ∈ D.H := S_le_H D hs
  have hnorm : s ∈ Subgroup.normalizer D.U := H_le_normalizer_U D hsH
  rw [Subgroup.mem_normalizer_iff] at hnorm
  exact (hnorm x).mp hx

/-- `u ∈ C.P.U` is closed under conjugation by `s ∈ D.S`, in the notation of `C`. -/
theorem conj_mem_CPU (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C)
    {s x : G} (hs : s ∈ (D.S : Subgroup G)) (hx : x ∈ C.P.U) : s * x * s⁻¹ ∈ C.P.U := by
  rw [hDC.U_eq]
  exact S_conj_mem_U D hs (by rwa [hDC.U_eq] at hx)

/-- The element of `↥(Uin C)` attached to an element of `C.P.U`. -/
theorem mem_Uin_of_mem_CPU (C : Sec2Ctx G) {w : G} (hw : w ∈ C.P.U) :
    (⟨w, C.P.U_le_H0 hw⟩ : ↥C.P.H0) ∈ Uin C := by
  rw [Subgroup.mem_subgroupOf]
  exact hw

/-! ## 2. The conjugation action `φS : S →* MulAut U` and its fixed points -/

section Action

variable (D : BGData G) (C : Sec2Ctx G)

/-- Conjugation by `s ∈ S` as an automorphism of `↥(Uin C)`. -/
noncomputable def conjAutU (hDC : Compat D C) (s : ↥(D.S)) : MulAut ↥(Uin C) where
  toFun u :=
    ⟨⟨(s : G) * ((u : ↥C.P.H0) : G) * (s : G)⁻¹,
        C.P.U_le_H0 (conj_mem_CPU D C hDC s.2 u.2)⟩,
      mem_Uin_of_mem_CPU C (conj_mem_CPU D C hDC s.2 u.2)⟩
  invFun u :=
    ⟨⟨(s : G)⁻¹ * ((u : ↥C.P.H0) : G) * (s : G),
        C.P.U_le_H0 (by simpa using conj_mem_CPU D C hDC (inv_mem s.2) u.2)⟩,
      mem_Uin_of_mem_CPU C (by simpa using conj_mem_CPU D C hDC (inv_mem s.2) u.2)⟩
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
noncomputable def phiS (hDC : Compat D C) : ↥(D.S) →* MulAut ↥(Uin C) where
  toFun s := conjAutU D C hDC s
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

/-- Unfolding of the action: `φS s` is conjugation by `s` in `G`. -/
theorem phiS_apply (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C)
    (s : ↥(D.S)) (u : ↥(Uin C)) :
    (((phiS D C hDC s u : ↥(Uin C)) : ↥C.P.H0) : G)
      = (s : G) * ((u : ↥C.P.H0) : G) * (s : G)⁻¹ := rfl

/-- The fixed points of the `S`-action are `C_U(S)`. -/
theorem mem_fixedSubgroupS_phiS (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C)
    (u : ↥(Uin C)) :
    u ∈ fixedSubgroupS (phiS D C hDC) ↔
      ∀ s : ↥(D.S), (s : G) * ((u : ↥C.P.H0) : G) * (s : G)⁻¹ = ((u : ↥C.P.H0) : G) := by
  rw [mem_fixedSubgroupS]
  constructor
  · intro h s
    have h' := congrArg (fun x : ↥(Uin C) => ((x : ↥C.P.H0) : G)) (h s)
    simpa [phiS_apply D C hDC s u] using h'
  · intro h s
    refine Subtype.ext (Subtype.ext ?_)
    rw [phiS_apply D C hDC s u]
    exact h s

/-- The fixed points of the `S`-action, in the `∈ D.S`-form. -/
theorem mem_fixedSubgroupS_phiS' (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C)
    (u : ↥(Uin C)) :
    u ∈ fixedSubgroupS (phiS D C hDC) ↔
      ∀ g ∈ (D.S : Subgroup G), g * ((u : ↥C.P.H0) : G) * g⁻¹ = ((u : ↥C.P.H0) : G) := by
  rw [mem_fixedSubgroupS_phiS D C hDC u]
  constructor
  · intro h g hg
    exact h ⟨g, hg⟩
  · intro h s
    exact h (s : G) s.2

/-- `S` is contained in the centralizer of every element of `C_U(S)`. -/
theorem S_le_centralizer_of_mem_fixed (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C)
    {u : ↥(Uin C)} (hu : u ∈ fixedSubgroupS (phiS D C hDC)) :
    (D.S : Subgroup G) ≤ Subgroup.centralizer ({((u : ↥C.P.H0) : G)} : Set G) := by
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  have h := (mem_fixedSubgroupS_phiS' D C hDC u).mp hu g hg
  have h2 : (g * ((u : ↥C.P.H0) : G)) * g⁻¹ = ((u : ↥C.P.H0) : G) := h
  have h3 : g * ((u : ↥C.P.H0) : G) = ((u : ↥C.P.H0) : G) * g := by
    have := congrArg (fun y => y * g) h2
    simpa [mul_assoc] using this
  exact h3.symm

/-- The `s`-conjugate of a class function of `H₀` has the same value at a point of `C_U(S)`. -/
theorem sconj_apply_eq_of_mem_fixed (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C)
    {u : ↥(Uin C)} (hu : u ∈ fixedSubgroupS (phiS D C hDC))
    (ξ : ClassFunction ↥C.P.H0 ℂ) :
    sconj C ξ (u : ↥C.P.H0) = ξ (u : ↥C.P.H0) := by
  have h := (mem_fixedSubgroupS_phiS' D C hDC u).mp hu D.t1 D.t1_mem
  have hone : conjMulEquiv C.P C.s (u : ↥C.P.H0) = (u : ↥C.P.H0) := by
    refine Subtype.ext ?_
    rw [conjMulEquiv_apply, hDC.s_eq]
    exact h
  rw [sconj, conjByH, ClassFunction.compHom_apply]
  exact congrArg (fun x : ↥C.P.H0 => ξ x) hone

/-! ## 3. `S` is a `2`-group and `U` has odd order -/

/-- `S` is a `2`-group. -/
theorem isPGroup_S (D : BGData G) : IsPGroup 2 ↥(D.S) := (D.S).isPGroup'

/-- `↥(Uin C)` has odd order. -/
theorem odd_card_Uin (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C) :
    Odd (Nat.card ↥(Uin C)) := by
  haveI : Fintype ↥D.H := Fintype.ofFinite _
  have e : ↥(Work.GW2.oddCore ↥D.H) ≃* ↥D.U :=
    Subgroup.equivMapOfInjective (Work.GW2.oddCore ↥D.H) D.H.subtype D.H.subtype_injective
  have h1 : Odd (Nat.card ↥D.U) := by
    rw [← Nat.card_congr e.toEquiv]
    exact Work.GW2.odd_card_oddCore (G := ↥D.H)
  have e2 : ↥(Uin C) ≃* ↥C.P.U := Subgroup.subgroupOfEquivOfLe C.P.U_le_H0
  rw [Nat.card_congr e2.toEquiv, hDC.U_eq]
  exact h1

/-- `↥(fixedSubgroupS (phiS D C hDC))` has odd order. -/
theorem odd_card_fixedSubgroupS_phiS (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C) :
    Odd (Nat.card ↥(fixedSubgroupS (phiS D C hDC))) :=
  Odd.of_dvd_nat (odd_card_Uin D C hDC) (Subgroup.card_subgroup_dvd_card _)

/-! ## 4. `D.S = D.S₀ ⊔ ⟨t₁⟩` -/

/-- In the Bender–Glauberman data, the Sylow `2`-subgroup is generated by its maximal
cyclic subgroup `S₀` and the involution `t₁`. -/
theorem S_eq_sup_S0_t1 (D : BGData G) :
    (D.S : Subgroup G) = D.S0 ⊔ Subgroup.zpowers D.t1 := by
  refine le_antisymm ?_ (sup_le D.S0_le (Subgroup.zpowers_le.mpr D.t1_mem))
  intro x hx
  by_contra hcon
  have hHle : D.S0 ≤ D.S0 ⊔ Subgroup.zpowers D.t1 := le_sup_left
  have hHS : D.S0 ⊔ Subgroup.zpowers D.t1 ≤ (D.S : Subgroup G) :=
    sup_le D.S0_le (Subgroup.zpowers_le.mpr D.t1_mem)
  have hprod := Subgroup.relIndex_mul_relIndex D.S0 (D.S0 ⊔ Subgroup.zpowers D.t1)
    (D.S : Subgroup G) hHle hHS
  rw [D.S0_index] at hprod
  have hdvd : (D.S0 ⊔ Subgroup.zpowers D.t1).relIndex (D.S : Subgroup G) ∣ 2 :=
    ⟨D.S0.relIndex (D.S0 ⊔ Subgroup.zpowers D.t1), by rw [mul_comm]; exact hprod.symm⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · rw [Subgroup.relIndex_eq_one] at h1
    exact hcon (h1 hx)
  · have : D.S0.relIndex (D.S0 ⊔ Subgroup.zpowers D.t1) = 1 := by
      rw [h2, mul_comm] at hprod
      simpa using hprod
    rw [Subgroup.relIndex_eq_one] at this
    exact D.t1_nmem (this (Subgroup.mem_sup_right (Subgroup.mem_zpowers D.t1)))

/-- The corresponding statement inside `↥(D.S)`. -/
theorem S0_subgroupOf_sup_zpowers_t1 (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C) :
    D.S0.subgroupOf (D.S : Subgroup G) ⊔
        Subgroup.zpowers (⟨D.t1, D.t1_mem⟩ : ↥(D.S : Subgroup G)) = ⊤ := by
  have hsup : (D.S0 ⊔ Subgroup.zpowers D.t1 : Subgroup G) = (D.S : Subgroup G) :=
    (S_eq_sup_S0_t1 D).symm
  have h1 : (D.S0 ⊔ Subgroup.zpowers D.t1).subgroupOf (D.S : Subgroup G) = ⊤ := by
    rw [hsup, Subgroup.subgroupOf_self]
  rw [Subgroup.subgroupOf_sup D.S0_le (Subgroup.zpowers_le.mpr D.t1_mem)] at h1
  have h2 : (Subgroup.zpowers D.t1).subgroupOf (D.S : Subgroup G) =
      Subgroup.zpowers (⟨D.t1, D.t1_mem⟩ : ↥(D.S : Subgroup G)) := by
    ext y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by rw [← hk, Subgroup.coe_zpow]⟩
  rw [h2] at h1
  exact h1

/-! ## 5. `S`-invariance -/

/-- A class function of `U` invariant under `H₀` and under `t₁` is invariant under the whole
Sylow `2`-subgroup `S = S₀ ⊔ ⟨t₁⟩`. -/
theorem invariant_phiS (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C)
    (a : ClassFunction ↥(Uin C) ℂ)
    (hS0 : ∀ s : ↥(D.S), (s : G) ∈ D.S0 →
        ∀ u : ↥(Uin C), a (phiS D C hDC s u) = a u)
    (ht1 : ∀ u : ↥(Uin C), a (phiS D C hDC ⟨D.t1, D.t1_mem⟩ u) = a u) :
    ∀ s : ↥(D.S), ∀ u : ↥(Uin C), a (phiS D C hDC s u) = a u := by
  classical
  let T : Subgroup ↥(D.S) :=
    { carrier := {s | ∀ u : ↥(Uin C), a (phiS D C hDC s u) = a u}
      one_mem' := by
        intro u
        simp
      mul_mem' := by
        intro x y hx hy u
        rw [map_mul, MulAut.mul_apply, hx (phiS D C hDC y u), hy u]
      inv_mem' := by
        intro x hx u
        have hkey : phiS D C hDC x (phiS D C hDC x⁻¹ u) = u := by
          rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel]
          simp
        have h := hx (phiS D C hDC x⁻¹ u)
        rw [hkey] at h
        exact h.symm }
  have hT0 : D.S0.subgroupOf (D.S : Subgroup G) ≤ T := by
    intro s hs
    rw [Subgroup.mem_subgroupOf] at hs
    exact hS0 s hs
  have ht1T : (⟨D.t1, D.t1_mem⟩ : ↥(D.S : Subgroup G)) ∈ T := ht1
  have hsup := S0_subgroupOf_sup_zpowers_t1 D C hDC
  have hle : (⊤ : Subgroup ↥(D.S)) ≤ T := by
    rw [← hsup]
    exact sup_le hT0 (Subgroup.zpowers_le.mpr ht1T)
  intro s u
  exact hle (Subgroup.mem_top s) u

end L33D

end Work.BG
