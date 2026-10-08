import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.CharBridge
import Submission.Work.BG.invJCard
import Submission.Work.BG.decompH1
import Submission.Work.BG.kappaCharExists

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Subgroup

variable {G : Type} [Group G] [Finite G]

/-! ## The group-theoretic facts about `BGData` used below -/

/-- `S = ⟨t₁, t₂⟩`. -/
theorem S_eq_closure {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G) :
    (D.S : Subgroup G) = Subgroup.closure ({D.t1, D.t2} : Set G) := by
  have hsup : D.S0 ⊔ Subgroup.zpowers D.t1 = (D.S : Subgroup G) :=
    sup_zpowers_eq_of_relIndex_eq_two D.S0_le D.S0_index D.t1_mem D.t1_nmem
  rw [← hsup, D.gen]
  refine le_antisymm ?_ ?_
  · refine sup_le ?_ ?_
    · refine Subgroup.zpowers_le.mpr ?_
      exact Subgroup.mul_mem _
        (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
    · refine Subgroup.zpowers_le.mpr ?_
      exact Subgroup.subset_closure (by simp)
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers D.t1)
    · have h1 : D.t1 ∈ Subgroup.zpowers (D.t1 * D.t2) ⊔ Subgroup.zpowers D.t1 :=
        Subgroup.mem_sup_right (Subgroup.mem_zpowers D.t1)
      have h2 : D.t1 * D.t2 ∈ Subgroup.zpowers (D.t1 * D.t2) ⊔ Subgroup.zpowers D.t1 :=
        Subgroup.mem_sup_left (Subgroup.mem_zpowers (D.t1 * D.t2))
      have h3 := (Subgroup.zpowers (D.t1 * D.t2) ⊔ Subgroup.zpowers D.t1).mul_mem
        ((Subgroup.zpowers (D.t1 * D.t2) ⊔ Subgroup.zpowers D.t1).inv_mem h1) h2
      rwa [show D.t1⁻¹ * (D.t1 * D.t2) = D.t2 from by group] at h3

/-- `D.B = C_U(S)`: `D.B` centralizes the Sylow `2`-subgroup `S`. -/
theorem B_le_centralizer_S {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G) :
    D.B ≤ Subgroup.centralizer ((D.S : Subgroup G) : Set G) := by
  rw [S_eq_closure D, Subgroup.centralizer_closure]
  intro b hb
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
  have hb1 : b ∈ Subgroup.centralizer ({D.t1} : Set G) := hb.1.2
  have hb2 : b ∈ Subgroup.centralizer ({D.t2} : Set G) := hb.2.2
  rcases hh with rfl | rfl
  · exact (Subgroup.mem_centralizer_singleton_iff.mp hb1).symm
  · exact (Subgroup.mem_centralizer_singleton_iff.mp hb2).symm

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem kappaExists {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) :
    Work.GW2.C16.KappaExistsProp D C := by
  intro hC hB
  obtain ⟨χ, hχne, hχinv⟩ :=
    kappaCharExists (G := G) (U := D.U) (S := (D.S : Subgroup G)) (B := D.B)
      (S_le_normalizer_U D) (odd_card_U D) D.S.isPGroup'
      (show D.B ≤ D.U from inf_le_left.trans inf_le_left) (B_le_centralizer_S D) hB
  have hUpH0 : D.U ≤ C.P.H0 := by rw [hC.H0_eq]; exact le_sup_left
  have hdecomp : ∀ x : ↥C.P.H0, ∃! p : ↥D.U × ↥D.S0, (p.1 : G) * (p.2 : G) = (x : G) := by
    intro x
    exact decompH1 D (x := (x : G)) (by rw [← hC.H0_eq]; exact x.2)
  let d : ↥C.P.H0 → ↥D.U × ↥D.S0 := fun x => Classical.choose (hdecomp x)
  have hd : ∀ x : ↥C.P.H0, ((d x).1 : G) * ((d x).2 : G) = (x : G) :=
    fun x => (Classical.choose_spec (hdecomp x)).1
  have hdu : ∀ (x : ↥C.P.H0) (p : ↥D.U × ↥D.S0),
      (p.1 : G) * (p.2 : G) = (x : G) → p = d x :=
    fun x p hp => (Classical.choose_spec (hdecomp x)).2 p hp
  have hsS : (C.s : G) ∈ (D.S : Subgroup G) := by rw [hC.s_eq]; exact D.t1_mem
  -- multiplicativity
  have hκmul : ∀ x y : ↥C.P.H0, χ (d (x * y)).1 = χ (d x).1 * χ (d y).1 := by
    intro x y
    have hmemU2 : (d x).2.1 * (d y).1.1 * (d x).2.1⁻¹ ∈ D.U :=
      (Subgroup.mem_normalizer_iff.mp (S0_le_normalizer_U D (d x).2.2) (d y).1.1).mp (d y).1.2
    have hmemS0 : (d x).2.1 * (d y).2.1 ∈ D.S0 := D.S0.mul_mem (d x).2.2 (d y).2.2
    have hprod : ((⟨(d x).1.1 * ((d x).2.1 * (d y).1.1 * (d x).2.1⁻¹),
          D.U.mul_mem (d x).1.2 hmemU2⟩ : ↥D.U) : G)
        * ((⟨(d x).2.1 * (d y).2.1, hmemS0⟩ : ↥D.S0) : G) = ((x * y : ↥C.P.H0) : G) := by
      show (d x).1.1 * ((d x).2.1 * (d y).1.1 * (d x).2.1⁻¹) * ((d x).2.1 * (d y).2.1)
          = (x : G) * (y : G)
      have hsplit : (d x).1.1 * ((d x).2.1 * (d y).1.1 * (d x).2.1⁻¹) * ((d x).2.1 * (d y).2.1)
          = ((d x).1.1 * (d x).2.1) * ((d y).1.1 * (d y).2.1) := by group
      rw [hsplit, hd x, hd y]
    have huniq : (⟨⟨(d x).1.1 * ((d x).2.1 * (d y).1.1 * (d x).2.1⁻¹),
          D.U.mul_mem (d x).1.2 hmemU2⟩,
        ⟨(d x).2.1 * (d y).2.1, hmemS0⟩⟩ : ↥D.U × ↥D.S0) = d (x * y) :=
      hdu (x * y) _ hprod
    have hfst : (d (x * y)).1 = (d x).1 * ⟨(d x).2.1 * (d y).1.1 * (d x).2.1⁻¹, hmemU2⟩ := by
      rw [← huniq]
      rfl
    rw [hfst, map_mul]
    congr 1
    exact hχinv ⟨(d x).2.1, D.S0_le (d x).2.2⟩ (d y).1
  -- the homomorphism `H₀ →* ℂˣ`
  let κhom : ↥C.P.H0 →* ℂˣ :=
    { toFun := fun x => χ (d x).1
      map_one' := by
        have h1 : d 1 = ((1 : ↥D.U), (1 : ↥D.S0)) :=
          (hdu 1 ((1 : ↥D.U), (1 : ↥D.S0)) (by simp)).symm
        show χ (d 1).1 = 1
        rw [congrArg Prod.fst h1]
        simp
      map_mul' := hκmul }
  -- `s`-invariance of `κ`
  have hconj : ∀ x : ↥C.P.H0, κhom (conjMulEquiv C.P C.s x) = κhom x := by
    intro x
    have hmemU' : (C.s : G) * (d x).1.1 * (C.s : G)⁻¹ ∈ D.U :=
      (Subgroup.mem_normalizer_iff.mp (S_le_normalizer_U D hsS) (d x).1.1).mp (d x).1.2
    have hmemS0' : (C.s : G) * (d x).2.1 * (C.s : G)⁻¹ ∈ D.S0 := by
      have h1 := (BGData_S0_subgroupOf_normal D).conj_mem
        (⟨(d x).2.1, D.S0_le (d x).2.2⟩ : ↥(D.S : Subgroup G))
        (by rw [Subgroup.mem_subgroupOf]; exact (d x).2.2)
        (⟨(C.s : G), hsS⟩ : ↥(D.S : Subgroup G))
      rwa [Subgroup.mem_subgroupOf] at h1
    have hprod : ((⟨(C.s : G) * (d x).1.1 * (C.s : G)⁻¹, hmemU'⟩ : ↥D.U) : G)
        * ((⟨(C.s : G) * (d x).2.1 * (C.s : G)⁻¹, hmemS0'⟩ : ↥D.S0) : G)
        = ((conjMulEquiv C.P C.s x : ↥C.P.H0) : G) := by
      show (C.s : G) * (d x).1.1 * (C.s : G)⁻¹ * ((C.s : G) * (d x).2.1 * (C.s : G)⁻¹)
          = ↑(conjMulEquiv C.P C.s x)
      rw [conjMulEquiv_apply, ← hd x]
      group
    have hkey : (⟨⟨(C.s : G) * (d x).1.1 * (C.s : G)⁻¹, hmemU'⟩,
        ⟨(C.s : G) * (d x).2.1 * (C.s : G)⁻¹, hmemS0'⟩⟩ : ↥D.U × ↥D.S0)
        = d (conjMulEquiv C.P C.s x) := hdu _ _ hprod
    show χ (d (conjMulEquiv C.P C.s x)).1 = χ (d x).1
    rw [← hkey]
    exact hχinv ⟨(C.s : G), hsS⟩ (d x).1
  refine ⟨↑(linearIrreducibleCharacter κhom), (linearIrreducibleCharacter κhom).2, ?_, ?_, ?_, ?_⟩
  · exact linearIrreducibleCharacter_apply_one κhom
  · ext h
    rw [sconj, conjByH_apply, linearIrreducibleCharacter_apply,
      linearIrreducibleCharacter_apply]
    exact congrArg (fun u : ℂˣ => (u : ℂ)) (hconj h)
  · intro h hh
    have h1 : d h = ((1 : ↥D.U), (⟨(h : G), hh⟩ : ↥D.S0)) :=
      (hdu h ((1 : ↥D.U), (⟨(h : G), hh⟩ : ↥D.S0)) (by simp)).symm
    show ((↑(linearIrreducibleCharacter κhom) : ClassFunction ↥C.P.H0 ℂ) h) = 1
    rw [linearIrreducibleCharacter_apply]
    show (χ (d h).1 : ℂ) = 1
    rw [congrArg Prod.fst h1]
    simp
  · intro hcontra
    obtain ⟨u, hu⟩ : ∃ u : ↥D.U, χ u ≠ 1 := by
      by_contra hcon
      exact hχne (MonoidHom.ext fun u => by simpa using not_exists.mp hcon u)
    have hx : (u : G) ∈ C.P.H0 := hUpH0 u.2
    have h1 : d ⟨(u : G), hx⟩ = (u, (1 : ↥D.S0)) :=
      (hdu ⟨(u : G), hx⟩ (u, (1 : ↥D.S0)) (by simp)).symm
    have h2 : ((↑(linearIrreducibleCharacter κhom) : ClassFunction ↥C.P.H0 ℂ) ⟨(u : G), hx⟩)
        = (χ u : ℂ) := by
      rw [linearIrreducibleCharacter_apply]
      show (χ (d ⟨(u : G), hx⟩).1 : ℂ) = (χ u : ℂ)
      rw [congrArg Prod.fst h1]
    have h3 : (lamCF C 1) ⟨(u : G), hx⟩ = 1 := by
      rw [lamCF, ClassFunction.compHom_apply, linearClassFunction_apply]
      simp
    have h4 : ((↑(linearIrreducibleCharacter κhom) : ClassFunction ↥C.P.H0 ℂ) ⟨(u : G), hx⟩)
        = (lamCF C 1) ⟨(u : G), hx⟩ :=
      congrArg (fun f : ClassFunction ↥C.P.H0 ℂ => f ⟨(u : G), hx⟩) hcontra
    rw [h2, h3] at h4
    exact hu (Units.val_injective h4)

end Work.BG
