import Mathlib
import Submission.Work.BG.ThmABCDefs
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.kappaExists
import Submission.OddOrder.GroupTheory.RepresentationTheory.InflationCharacter
import Submission.OddOrder.GroupTheory.RepresentationTheory.CliffordSingleOrbit
import Submission.Work.BG.c3FrobLiesOverConstituent
import Submission.Work.BG.c3FrobFrobeniusDvdDegree
import Submission.Work.BG.c3FrobCliffordDvdDegree
import Submission.Work.BG.c3FrobFrobeniusGroupOfWith

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem c3FrobDegree {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) (K1 K2 : Subgroup G)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hC : Work.GW2.C16.Compat D C) (hHyps : Work.GW2.C16.ThmCHyps D K1 K2)
    (a : ClassFunction ↥(Work.GW2.C16.Uin C) ℂ) (ha : IsIrreducibleCharacter a)
    (haK : ∃ u : ↥(Work.GW2.C16.Uin C),
      ((u : ↥C.P.H0) : G) ∈ (K1 ⊓ K2) ∧ a u ≠ a 1) :
    D.U ≠ D.B ⊔ (K1 ⊓ K2) → ∃ da : ℕ, a 1 = (da : ℂ) ∧ Nat.card D.B ≤ da := by
  intro hU
  -- abbreviations
  let K : Subgroup G := K1 ⊓ K2
  let A : Subgroup G := D.B1 ⊓ K2
  let BF : Subgroup G := D.B ⊔ K
  have hDir : IsInternalDirect D.U A BF := hHyps.2.2.1
  have hFrob : IsFrobeniusWith BF K D.B := hHyps.2.2.2.2.2 hU
  -- `BF ≤ D.U`, and `D.U` normalizes `BF`
  have hBF_le : BF ≤ D.U := by rw [← hDir.1]; exact le_sup_right
  have hDU_norm : D.U ≤ Subgroup.normalizer (BF : Set G) := by
    rw [← hDir.1]
    refine sup_le ?_ Subgroup.le_normalizer
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer (BF : Set G))
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hDir.2.2 x hx y hy).symm
  have hHZ_normal : (BF.subgroupOf D.U).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hBF_le]
    intro h k hh hk
    have hk' := hDU_norm hk
    rw [Subgroup.mem_normalizer_iff] at hk'
    exact (hk' h).mp hh
  -- transfer `a` to a class function of `↥D.U`
  haveI : Fintype ↥D.U := Fintype.ofFinite _
  haveI : Finite ↥D.U := Subtype.finite
  let e0 : ↥(Uin C) ≃* ↥D.U :=
    (Subgroup.subgroupOfEquivOfLe C.P.U_le_H0).trans (MulEquiv.subgroupCongr hC.U_eq)
  let a' : ClassFunction ↥D.U ℂ := a.compHom e0.symm.toMonoidHom
  have ha' : IsIrreducibleCharacter a' :=
    IsIrreducibleCharacter.compHom_of_surjective e0.symm.surjective ha
  have ha'1 : a' 1 = a 1 := by simp [a']
  obtain ⟨u, huK, hua⟩ := haK
  have he0coe : ∀ x : ↥(Uin C), ((e0 x : ↥D.U) : G) = ((x : ↥C.P.H0) : G) := by
    intro x
    have key : (((MulEquiv.subgroupCongr hC.U_eq)
        ((Subgroup.subgroupOfEquivOfLe C.P.U_le_H0) x) : ↥D.U) : G) = ((x : ↥C.P.H0) : G) := by
      rw [MulEquiv.subgroupCongr_apply]
      rfl
    exact key
  have hunk : (e0 u : G) ∈ K := by rw [he0coe u]; exact huK
  have hueq : a' (e0 u) ≠ a' 1 := by
    have h1 : a' (e0 u) = a u := by simp [a']
    rw [h1, ha'1]; exact hua
  -- the Frobenius group `BF ⋊ ...` realised inside `↥D.U`
  haveI : Fintype ↥(BF.subgroupOf D.U) := Fintype.ofFinite _
  haveI : Finite ↥(BF.subgroupOf D.U) := Subtype.finite
  haveI : Invertible (Nat.card ↥(BF.subgroupOf D.U) : ℂ) := by
    refine invertibleOfNonzero ?_
    rw [Nat.cast_ne_zero]
    exact (Nat.card_pos (α := ↥(BF.subgroupOf D.U))).ne'
  have hNle : K.subgroupOf D.U ≤ BF.subgroupOf D.U := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact Subgroup.mem_sup_right hx
  -- a constituent `θ` of `a'|_{BF}` which is non-trivial on `K`
  haveI : (BF.subgroupOf D.U).Normal := hHZ_normal
  have hkerArg : ∃ n : ↥D.U, n ∈ K.subgroupOf D.U ∧ a' n ≠ a' 1 :=
    ⟨e0 u, by rw [Subgroup.mem_subgroupOf]; exact hunk, hueq⟩
  obtain ⟨θ, hθlies, m, hmN, hmθ⟩ :=
    c3FrobLiesOverConstituent (H := BF.subgroupOf D.U) (N := K.subgroupOf D.U)
      (hN := hNle) (χ := ⟨a', ha'⟩) (hker := hkerArg)
  -- the Frobenius degree divisibility
  have hFG : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(BF.subgroupOf D.U)
      ((K.subgroupOf D.U).subgroupOf (BF.subgroupOf D.U))
      ((D.B.subgroupOf D.U).subgroupOf (BF.subgroupOf D.U)) :=
    c3FrobFrobeniusGroupOfWith (BF := BF) (F := K) (B := D.B) (T := D.U) hBF_le hFrob
  have hkerθ : ∃ n : ↥(BF.subgroupOf D.U),
      n ∈ (K.subgroupOf D.U).subgroupOf (BF.subgroupOf D.U) ∧
        (θ : ClassFunction ↥(BF.subgroupOf D.U) ℂ) n ≠
          (θ : ClassFunction ↥(BF.subgroupOf D.U) ℂ) 1 :=
    ⟨m, by rw [Subgroup.mem_subgroupOf]; exact hmN, hmθ⟩
  obtain ⟨d, hd1, hdvdA⟩ := c3FrobFrobeniusDvdDegree
    (N := (K.subgroupOf D.U).subgroupOf (BF.subgroupOf D.U))
    (A := (D.B.subgroupOf D.U).subgroupOf (BF.subgroupOf D.U)) (hF := hFG)
    (θ := (θ : ClassFunction ↥(BF.subgroupOf D.U) ℂ)) (hθ := θ.isIrreducible) (hker := hkerθ)
  -- `|B| = |B_inside|`
  have hB_le_U : D.B ≤ D.U := by
    rw [BGData.B]
    exact le_trans inf_le_left inf_le_left
  have hcardA : Nat.card ↥((D.B.subgroupOf D.U).subgroupOf (BF.subgroupOf D.U)) =
      Nat.card D.B := by
    have hle1 : (D.B.subgroupOf D.U) ≤ (BF.subgroupOf D.U) := by
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact Subgroup.mem_sup_left hx
    have h1 : Nat.card ↥((D.B.subgroupOf D.U).subgroupOf (BF.subgroupOf D.U)) =
        Nat.card ↥(D.B.subgroupOf D.U) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle1).toEquiv
    have h2 : Nat.card ↥(D.B.subgroupOf D.U) = Nat.card D.B :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB_le_U).toEquiv
    exact h1.trans h2
  -- Clifford: `|B|` divides the degree of `a'`
  have hcArg : ∃ d : ℕ, (θ : ClassFunction ↥(BF.subgroupOf D.U) ℂ) 1 = (d : ℂ) ∧
      Nat.card D.B ∣ d := ⟨d, hd1, hcardA ▸ hdvdA⟩
  obtain ⟨e, he1, hedvd⟩ :=
    c3FrobCliffordDvdDegree (H := BF.subgroupOf D.U) (χ := ⟨a', ha'⟩) (θ := θ)
      (hover := hθlies) (c := Nat.card D.B) (hc := hcArg)
  refine ⟨e, ?_, ?_⟩
  · rw [← ha'1, he1]
  · obtain ⟨n, hnpos, hn, -⟩ := IsIrreducibleCharacter.exists_natDegree_charValue_one_dvd_card
      (φ := a') ha'
    have hen : e = n := by
      have h2 : (e : ℂ) = (n : ℂ) := by rw [← he1, ← hn]
      exact_mod_cast h2
    have hepos : 0 < e := by omega
    exact Nat.le_of_dvd hepos hedvd

end Work.BG
