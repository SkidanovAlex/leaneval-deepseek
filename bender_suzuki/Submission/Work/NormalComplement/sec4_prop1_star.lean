import Mathlib
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.p3Normal_of_chIIFourP3Subnormal
import Submission.Work.NormalComplement.sec4_one_c
import Submission.Work.NormalComplement.sec4_one_d
import Submission.Work.NormalComplement.sec4_P2d
import Submission.Work.NormalComplement.prop2b_conj_into_centD

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement

open Submission.Blueprint
open scoped Pointwise commutatorElement

/-! ## Small general group-theoretic helpers used below -/

section Helpers

variable {G : Type*} [Group G]

/-- If `K ≤ L` then `C_G(L) ≤ N_G(K)` (an element centralising the bigger subgroup normalises the
smaller one). -/
lemma sec4_star_centralizer_le_normalizer {K L : Subgroup G} (h : K ≤ L) :
    Subgroup.centralizer (L : Set G) ≤ Subgroup.normalizer (K : Set G) :=
  (Subgroup.centralizer_le (fun _ hx => h hx)).trans
    (Subgroup.centralizer_le_normalizer (K : Set G))

/-- If `K ≤ C_G(L)` then `L ≤ N_G(K)`. -/
lemma sec4_star_le_normalizer_of_le_centralizer {K L : Subgroup G}
    (h : K ≤ Subgroup.centralizer (L : Set G)) :
    L ≤ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro l hl k hk
  have hc : l * k = k * l := (Subgroup.mem_centralizer_iff.mp (h hk)) l hl
  rw [hc]
  simpa using hk

/-- `N_G(K) ⊓ N_G(L) ≤ N_G(K ⊔ L)`. -/
lemma sec4_star_normalizer_inf_le_normalizer_sup (K L : Subgroup G) :
    Subgroup.normalizer (K : Set G) ⊓ Subgroup.normalizer (L : Set G) ≤
      Subgroup.normalizer ((K ⊔ L : Subgroup G) : Set G) := by
  intro g hg
  obtain ⟨hgK, hgL⟩ := Subgroup.mem_inf.mp hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hgK hgL ⊢
  rw [Subgroup.map_sup, hgK, hgL]

/-- `C_G(K ⊔ L) ≤ C_G(K) ⊓ C_G(L)`. -/
lemma sec4_star_centralizer_sup_le (K L : Subgroup G) :
    Subgroup.centralizer ((K ⊔ L : Subgroup G) : Set G) ≤
      Subgroup.centralizer (K : Set G) ⊓ Subgroup.centralizer (L : Set G) :=
  le_inf (Subgroup.centralizer_le (fun _ hx => Subgroup.mem_sup_left hx))
         (Subgroup.centralizer_le (fun _ hx => Subgroup.mem_sup_right hx))

end Helpers

/-- **Peterfalvi I Ch. III §4 Proposition 1, formula (∗)** (p.180).  For `1 ≠ U ≤ C_A(P)` there is
a 2-subgroup `S₂ ≤ H` centralising `U` and `P` with
`N_H(U) ⊓ N_H(P) = (S₂ ⊔ P) ⊔ (C_A(P) ⊓ N_H(U))`.

Route in `_design/Sec4.lean`: Ch. II §4 Prop. 3 with a *subnormal* `Y` (`hP3`), applied to
`X = U ⊔ P` and `Y = U` (`N_K(U) ⊇ C_K(A) ≠ 1`): `N_H(X) = S ⋊ N_D(X)`; then
`N_D(U × P) = C_A(P) × P` by §4 Lemma 1 (c), (d) (`sec4_one_c`, `sec4_one_d`).  The step
`N_H(U ⊔ P) ↦ N_H(U) ⊓ N_H(P)` is the one obligation the source asserts. -/
theorem sec4_prop1_star (hFT : Submission.Blueprint.FeitThompsonProp)
    (hP3 : Submission.Blueprint.ChIIFourP3SubnormalProp) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G}
    (h : Work.NormalComplement.Design.Setup45A G H t W p P A) (U : Subgroup G) (hU : U ≠ ⊥)
    (hUA : U ≤ A ⊓ Subgroup.centralizer (P : Set G)) :
    ∃ S₂ : Subgroup G, IsPGroup 2 S₂ ∧ S₂ ≤ H ∧
      S₂ ≤ Subgroup.centralizer (U : Set G) ⊓ Subgroup.centralizer (P : Set G) ∧
      H ⊓ Subgroup.normalizer (U : Set G) ⊓ Subgroup.normalizer (P : Set G) =
        (S₂ ⊔ P) ⊔ (A ⊓ Subgroup.centralizer (P : Set G) ⊓
          Subgroup.normalizer (U : Set G)) := by
  classical
  -- ## Elementary inclusions among `U, P, A, V = C_D(t)`
  have hU_le_A : U ≤ A := hUA.trans inf_le_left
  have hU_le_V : U ≤ centD H t := hU_le_A.trans h.A_le
  have hP_le_V : P ≤ centD H t := h.P_le.trans inf_le_right
  have hX_le_V : U ⊔ P ≤ centD H t := sup_le hU_le_V hP_le_V
  have hPU : P ≤ Subgroup.normalizer (U : Set G) :=
    sec4_star_le_normalizer_of_le_centralizer (hUA.trans inf_le_right)
  have hX_norm : U ⊔ P ≤ Subgroup.normalizer (U : Set G) :=
    sup_le Subgroup.le_normalizer hPU
  -- ## a non-identity element of `K` normalising `U` (from `C_K(A) ≠ 1`)
  have hp2 : 2 ≤ p := h.prime.two_le
  have hpow : 4 ≤ 2 ^ p := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp2
  have h1CK : (1 : G) ∈ Design.CK H t A :=
    ⟨⟨Subgroup.one_mem _, by simp⟩, Subgroup.one_mem _⟩
  have hk : ∃ k ∈ Design.CK H t A, k ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have hsub : Design.CK H t A ⊆ ({1} : Set G) := fun x hx => by
      simpa using hcon x hx
    have hle : (Design.CK H t A).ncard ≤ 1 := by
      have := Set.ncard_le_ncard hsub (Set.finite_singleton (1 : G))
      simpa using this
    rw [h.A_CK] at hle
    omega
  obtain ⟨k, hkCK, hk1⟩ := hk
  have hkN : k ∈ Subgroup.normalizer (U : Set G) :=
    sec4_star_centralizer_le_normalizer hU_le_A hkCK.2
  have hk' : ∃ k ∈ invertedBy (twoPoint H t) t, k ≠ 1 ∧
      k ∈ Subgroup.normalizer (U : Set G) :=
    ⟨k, hkCK.1, hk1, hkN⟩
  -- ## Ch. II §4 Prop. 3 with `X = U ⊔ P`, `Y = U`
  obtain ⟨-, S, hS2, hSF, hSH, hSN, _hSD, hSsup⟩ :=
    (p3Normal_of_chIIFourP3Subnormal hP3) G h.sit H h.se t h.invol h.notMem
      (U ⊔ P) U hX_le_V hU le_sup_left hX_norm hk'
  have hS'_le : S ≤ Subgroup.centralizer ((U ⊔ P : Subgroup G) : Set G) :=
    hSF.trans (Subgroup.map_subtype_le
      (K := Submission.Blueprint.oddResidual ↥(Subgroup.centralizer
        ((U ⊔ P : Subgroup G) : Set G))))
  have hS_le_cent : S ≤ Subgroup.centralizer (U : Set G) ⊓ Subgroup.centralizer (P : Set G) :=
    le_inf (hS'_le.trans ((sec4_star_centralizer_sup_le U P).trans inf_le_left))
           (hS'_le.trans ((sec4_star_centralizer_sup_le U P).trans inf_le_right))
  -- ## §4 Lemma 1 (c): the normaliser of `P` inside `D`
  have hNDP : twoPoint H t ⊓ Subgroup.normalizer (P : Set G) =
      (A ⊓ Subgroup.centralizer (P : Set G)) ⊔ P := (sec4_one_c hFT h).1
  have hcentD_tp : centD H t ≤ twoPoint H t := inf_le_left
  have hcentD_H : centD H t ≤ H := inf_le_left.trans inf_le_left
  have hAH : A ≤ H := h.A_le.trans (inf_le_left.trans inf_le_left)
  have hS_le_C : S ≤ H ⊓ Subgroup.normalizer (U : Set G) ⊓
      Subgroup.normalizer (P : Set G) :=
    le_inf (le_inf hSH (hS_le_cent.trans (inf_le_left.trans
            (Subgroup.centralizer_le_normalizer (U : Set G)))))
           (hS_le_cent.trans (inf_le_right.trans
            (Subgroup.centralizer_le_normalizer (P : Set G))))
  refine ⟨S, hS2, hSH, hS_le_cent, ?_⟩
  -- ## the group identity
  apply le_antisymm
  · -- `N_H(U) ⊓ N_H(P) ≤ (S ⊔ P) ⊔ (C_A(P) ⊓ N_H(U))`
    -- `N_D(U ⊔ P) = D ⊓ N(U ⊔ P)` is normalised by `S` (Ch. II §4 Prop. 3)
    have hM_le_NS : twoPoint H t ⊓ Subgroup.normalizer ((U ⊔ P : Subgroup G) : Set G) ≤
        Subgroup.normalizer (S : Set G) :=
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right).trans hSN
    -- hence `N_H(U ⊔ P) = S · N_D(U ⊔ P)` as a set product
    have hSM : (↑(S ⊔ (twoPoint H t ⊓ Subgroup.normalizer ((U ⊔ P : Subgroup G) : Set G))) :
          Set G) =
        (S : Set G) *
          (twoPoint H t ⊓ Subgroup.normalizer ((U ⊔ P : Subgroup G) : Set G) : Set G) :=
      Subgroup.coe_mul_of_right_le_normalizer_left S _ hM_le_NS
    -- and `N_D(U ⊔ P) ⊓ N_H(U) ⊓ N_H(P) ≤ (C_A(P) ⊓ N_H(U)) ⊔ P`
    have hMC_le : (twoPoint H t ⊓ Subgroup.normalizer ((U ⊔ P : Subgroup G) : Set G)) ⊓
          (H ⊓ Subgroup.normalizer (U : Set G) ⊓ Subgroup.normalizer (P : Set G)) ≤
        (A ⊓ Subgroup.centralizer (P : Set G) ⊓ Subgroup.normalizer (U : Set G)) ⊔ P := by
      have hP_le_NA : P ≤ Subgroup.normalizer ((A ⊓ Subgroup.centralizer (P : Set G)) : Set G) :=
        sec4_star_le_normalizer_of_le_centralizer inf_le_right
      have hprod : (↑((A ⊓ Subgroup.centralizer (P : Set G)) ⊔ P) : Set G) =
          ((A ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) : Set G) * (P : Set G) :=
        Subgroup.coe_mul_of_right_le_normalizer_left
          (A ⊓ Subgroup.centralizer (P : Set G)) P hP_le_NA
      intro x hx
      obtain ⟨hxM, hxC⟩ := Subgroup.mem_inf.mp hx
      have hxTP : x ∈ twoPoint H t := (Subgroup.mem_inf.mp hxM).1
      have hxNP : x ∈ Subgroup.normalizer (P : Set G) := (Subgroup.mem_inf.mp hxC).2
      have hxNU : x ∈ Subgroup.normalizer (U : Set G) :=
        (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hxC).1).2
      have hxJP : x ∈ (A ⊓ Subgroup.centralizer (P : Set G)) ⊔ P := by
        have h1 : x ∈ twoPoint H t ⊓ Subgroup.normalizer (P : Set G) :=
          ⟨hxTP, hxNP⟩
        rwa [hNDP] at h1
      have hx' : x ∈ ((A ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) : Set G) *
          (P : Set G) := by
        rw [← hprod]
        exact hxJP
      obtain ⟨a, ha, q, hq, haq⟩ := Set.mem_mul.mp hx'
      have hqNU : q ∈ Subgroup.normalizer (U : Set G) := hPU hq
      have haNU : a ∈ Subgroup.normalizer (U : Set G) := by
        have h3 : x * q⁻¹ ∈ Subgroup.normalizer (U : Set G) :=
          (Subgroup.normalizer (U : Set G)).mul_mem hxNU
            ((Subgroup.normalizer (U : Set G)).inv_mem hqNU)
        rw [← haq] at h3
        rwa [mul_assoc, mul_inv_cancel, mul_one] at h3
      rw [← haq]
      exact ((A ⊓ Subgroup.centralizer (P : Set G) ⊓ Subgroup.normalizer (U : Set G)) ⊔
        P).mul_mem (Subgroup.mem_sup_left ⟨ha, haNU⟩) (Subgroup.mem_sup_right hq)
    intro g hg
    -- `g` lies in `H ⊓ N(U ⊔ P) = S ⊔ N_D(U ⊔ P)`
    have hgH : g ∈ H := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hg).1).1
    have hgNU : g ∈ Subgroup.normalizer (U : Set G) :=
      (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hg).1).2
    have hgNP : g ∈ Subgroup.normalizer (P : Set G) := (Subgroup.mem_inf.mp hg).2
    have hnin : Subgroup.normalizer (U : Set G) ⊓ Subgroup.normalizer (P : Set G) ≤
        Subgroup.normalizer ((U ⊔ P : Subgroup G) : Set G) :=
      sec4_star_normalizer_inf_le_normalizer_sup U P
    have hgNX : g ∈ Subgroup.normalizer ((U ⊔ P : Subgroup G) : Set G) :=
      hnin (Subgroup.mem_inf.mpr ⟨hgNU, hgNP⟩)
    have hgHNX : g ∈ H ⊓ Subgroup.normalizer ((U ⊔ P : Subgroup G) : Set G) :=
      Subgroup.mem_inf.mpr ⟨hgH, hgNX⟩
    have hgSM : g ∈ (S : Set G) *
        (twoPoint H t ⊓ Subgroup.normalizer ((U ⊔ P : Subgroup G) : Set G) : Set G) := by
      rw [← hSM, hSsup]
      exact hgHNX
    obtain ⟨s, hs, m, hm, hsm⟩ := Set.mem_mul.mp hgSM
    have hsC : s ∈ H ⊓ Subgroup.normalizer (U : Set G) ⊓
        Subgroup.normalizer (P : Set G) := hS_le_C hs
    have hmC : m ∈ H ⊓ Subgroup.normalizer (U : Set G) ⊓
        Subgroup.normalizer (P : Set G) := by
      have h2 : s⁻¹ * g ∈ H ⊓ Subgroup.normalizer (U : Set G) ⊓
          Subgroup.normalizer (P : Set G) :=
        (H ⊓ Subgroup.normalizer (U : Set G) ⊓
            Subgroup.normalizer (P : Set G)).mul_mem
          ((H ⊓ Subgroup.normalizer (U : Set G) ⊓
            Subgroup.normalizer (P : Set G)).inv_mem hsC) hg
      rw [← hsm] at h2
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at h2
    have hmT : m ∈ (A ⊓ Subgroup.centralizer (P : Set G) ⊓
        Subgroup.normalizer (U : Set G)) ⊔ P := hMC_le ⟨hm, hmC⟩
    have hmBig : m ∈ (S ⊔ P) ⊔ (A ⊓ Subgroup.centralizer (P : Set G) ⊓
        Subgroup.normalizer (U : Set G)) :=
      (sup_le_sup (le_sup_right : P ≤ S ⊔ P) le_rfl)
        ((sup_comm (A ⊓ Subgroup.centralizer (P : Set G) ⊓
          Subgroup.normalizer (U : Set G)) P) ▸ hmT)
    rw [← hsm]
    exact ((S ⊔ P) ⊔ (A ⊓ Subgroup.centralizer (P : Set G) ⊓
      Subgroup.normalizer (U : Set G))).mul_mem
        (Subgroup.mem_sup_left (Subgroup.mem_sup_left hs)) hmBig
  · -- `(S ⊔ P) ⊔ (C_A(P) ⊓ N_H(U)) ≤ N_H(U) ⊓ N_H(P)`
    have hPE : P ≤ Design.Egrp H t W := h.P_le.trans inf_le_left
    have hPW : P ≤ W := hPE.trans inf_le_left
    have hPH : P ≤ H := hPW.trans h.le
    have hPC : P ≤ H ⊓ Subgroup.normalizer (U : Set G) ⊓
        Subgroup.normalizer (P : Set G) :=
      le_inf (le_inf hPH hPU) Subgroup.le_normalizer
    have hAC1 : A ⊓ Subgroup.centralizer (P : Set G) ⊓ Subgroup.normalizer (U : Set G) ≤ H :=
      inf_le_left.trans (inf_le_left.trans hAH)
    have hAC2 : A ⊓ Subgroup.centralizer (P : Set G) ⊓ Subgroup.normalizer (U : Set G) ≤
        Subgroup.normalizer (P : Set G) :=
      inf_le_left.trans (inf_le_right.trans (Subgroup.centralizer_le_normalizer (P : Set G)))
    have hAC : A ⊓ Subgroup.centralizer (P : Set G) ⊓ Subgroup.normalizer (U : Set G) ≤
        H ⊓ Subgroup.normalizer (U : Set G) ⊓ Subgroup.normalizer (P : Set G) :=
      le_inf (le_inf hAC1 inf_le_right) hAC2
    exact sup_le (sup_le hS_le_C hPC) hAC

end Work.NormalComplement
