import Mathlib
import Submission.Work.BMAX.D17Defs
import Submission.Work.BMAX.Defs
import Submission.Work.BMAX.Basic
import Submission.Work.BMAX.Thompson
import Submission.Work.BMAX.LayerCentralizesFitting
import Submission.Work.BMAX.centralizer_pResidualIn_witness_le
import Submission.Work.BMAX.fstarIn_le_pResidualIn_of_notMem_primesOf
import Submission.Work.BMAX.fittingPiIn_le_iSup_pCoreIn
import Submission.Work.BMAX.le_normalizer_pCoreIn_zcenterIn_fittingIn
import Submission.Work.BMAX.pCoreIn_zcenterIn_fittingIn_ne_bot
import Submission.Work.BMAX.commutator_pCoreIn_inf_coatom_pResidualIn
import Submission.Work.CORE2A.thm26_aux

set_option maxHeartbeats 800000

namespace Work.BMAX

open Subgroup

/-! ## 1. Elementary API for `pCoreIn` / `pResidualIn` -/

section Api

variable {G : Type*} [Group G]

/-- `O_p(K) ≤ K`. -/
theorem pCoreIn_le_self (p : ℕ) (K : Subgroup G) : Work.GW2.pCoreIn p K ≤ K :=
  Subgroup.map_subtype_le _

/-- `O_p(K)` is normalised by `K`. -/
theorem le_normalizer_pCoreIn_of_primeFirst (p : ℕ) (K : Subgroup G) :
    K ≤ Subgroup.normalizer ((Work.GW2.pCoreIn p K : Subgroup G) : Set G) := by
  rw [Work.GW2.pCoreIn]
  exact le_normalizer_map_subtype_of_normal (Work.GW2.pCore_normal p ↥K)

/-- `O^p(K)` is normalised by `K`. -/
theorem le_normalizer_pResidualIn (p : ℕ) (K : Subgroup G) :
    K ≤ Subgroup.normalizer ((pResidualIn p K : Subgroup G) : Set G) := by
  rw [pResidualIn.eq_map]
  exact le_normalizer_map_subtype_of_normal (pResidual.normal p ↥K)

/-- `O_p(K)` is a `p`-group. -/
theorem isPGroup_pCoreIn [Finite G] {p : ℕ} [Fact p.Prime] (K : Subgroup G) :
    IsPGroup p ↥(Work.GW2.pCoreIn p K) := by
  have h : IsPGroup p ↥(Work.GW2.pCore p ↥K) := PiPart.pCore_isPGroup
  rw [Work.GW2.pCoreIn]
  exact h.of_equiv (Subgroup.equivMapOfInjective (Work.GW2.pCore p ↥K) K.subtype
    K.subtype_injective)

end Api

/-! ## 2. A `p`-subgroup of a `p'`-group is trivial -/

section Trivial

variable {G : Type*} [Group G]

/-- A `p`-subgroup of a group of order prime to `p` is trivial. -/
theorem eq_bot_of_isPGroup_of_not_dvd_card {p : ℕ} [Fact p.Prime] {X Y : Subgroup G}
    (hXY : X ≤ Y) (hX : IsPGroup p ↥X) (hY : ¬ p ∣ Nat.card ↥Y) : X = ⊥ := by
  have hdvd : Nat.card ↥X ∣ Nat.card ↥Y := Subgroup.card_dvd_of_le hXY
  rcases hX.card_eq_or_dvd with h1 | h2
  · exact Subgroup.card_eq_one.mp h1
  · exact absurd (h2.trans hdvd) hY

/-- Intersecting a `p`-subgroup with a `p'`-subgroup gives `⊥`. -/
theorem inf_eq_bot_of_isPGroup_of_not_dvd_card {p : ℕ} [Fact p.Prime] {X Y : Subgroup G}
    (hX : IsPGroup p ↥X) (hY : ¬ p ∣ Nat.card ↥Y) : X ⊓ Y = ⊥ :=
  eq_bot_of_isPGroup_of_not_dvd_card inf_le_right hX.to_inf_left hY

end Trivial

/-! ## 2'. (removed) -/

section NilpotentCommute

end NilpotentCommute

/-! ## 3. Thompson's `P × K` lemma for subgroups acting by conjugation -/

section Thompson

variable {G : Type*} [Group G] [Finite G]

/-- **Thompson's `P × K` lemma (Bender 1970, 1.1; Isaacs 4.31).**  Let `Q` be a `p`-group
normalised by `B`, and `P, K ≤ B` with `P` a `p`-group, `K` a `p'`-group, `P` and `K`
commuting elementwise, and `K` centralising the `P`-fixed points of `Q`.  Then `K` centralises
`Q`. -/
theorem thompson_PK_commutator {p : ℕ} [Fact p.Prime] {B Q P K : Subgroup G}
    (hQB : Q ≤ B) (hPB : P ≤ B) (hKB : K ≤ B)
    (hQn : B ≤ Subgroup.normalizer (Q : Set G))
    (hQp : IsPGroup p ↥Q) (hPp : IsPGroup p ↥P) (hKc : ¬ p ∣ Nat.card ↥K)
    (hcomm : ∀ x ∈ P, ∀ y ∈ K, x * y = y * x)
    (hfix : ∀ q ∈ Q, (∀ x ∈ P, q * x = x * q) → ∀ y ∈ K, q * y = y * q) :
    ⁅Q, K⁆ = ⊥ := by
  classical
  haveI hQnB : (Q.subgroupOf B).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hQn
  -- the identification `↥(Q.subgroupOf B) ≃* ↥Q`
  let e : ↥(Q.subgroupOf B) ≃* ↥Q :=
    { toFun := fun x => ⟨(((x : ↥B) : G)), x.2⟩
      invFun := fun x => ⟨⟨(x : G), hQB x.2⟩, x.2⟩
      left_inv := fun x => by ext <;> rfl
      right_inv := fun x => by ext <;> rfl
      map_mul' := fun x y => by ext <;> rfl }
  -- the multiplication map `↥P × ↥K →* ↥B`
  let mult : ↥P × ↥K →* ↥B :=
    { toFun := fun x => ⟨(x.1 : G) * (x.2 : G), B.mul_mem (hPB x.1.2) (hKB x.2.2)⟩
      map_one' := by ext; simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        show ((x.1 : G) * (y.1 : G)) * ((x.2 : G) * (y.2 : G)) =
          (x.1 : G) * (x.2 : G) * ((y.1 : G) * (y.2 : G))
        have hxy : (y.1 : G) * (x.2 : G) = (x.2 : G) * (y.1 : G) :=
          hcomm (y.1 : G) y.1.2 (x.2 : G) x.2.2
        calc ((x.1 : G) * (y.1 : G)) * ((x.2 : G) * (y.2 : G))
            = (x.1 : G) * ((y.1 : G) * (x.2 : G)) * (y.2 : G) := by group
          _ = (x.1 : G) * ((x.2 : G) * (y.1 : G)) * (y.2 : G) := by rw [hxy]
          _ = (x.1 : G) * (x.2 : G) * ((y.1 : G) * (y.2 : G)) := by group }
  -- the conjugation action of `P × K` on `Q` (computed inside `B`)
  let φ : ↥P × ↥K →* MulAut ↥(Q.subgroupOf B) := MulAut.conjNormal.comp mult
  have he_symm_apply : ∀ x : ↥Q, e.symm x = (⟨⟨(x : G), hQB x.2⟩, x.2⟩ : ↥(Q.subgroupOf B)) :=
    fun x => rfl
  have hmult_left : ∀ x : ↥P, mult (x, 1) = (⟨(x : G), hPB x.2⟩ : ↥B) := by
    intro x
    apply Subtype.ext
    show (x : G) * 1 = (x : G)
    simp
  have hmult_right : ∀ y : ↥K, mult (1, y) = (⟨(y : G), hKB y.2⟩ : ↥B) := by
    intro y
    apply Subtype.ext
    show (1 : G) * (y : G) = (y : G)
    simp
  -- the two hypotheses of Isaacs 4.31
  have hfixφ : ∀ g : ↥(Q.subgroupOf B),
      (∀ x : ↥P, (φ (x, 1)) g = g) → ∀ y : ↥K, (φ (1, y)) g = g := by
    intro g hg y
    have hgc : ∀ x ∈ P, ((g : ↥B) : G) * x = x * ((g : ↥B) : G) := by
      intro x hx
      have hpt : MulAut.conjNormal (mult (⟨x, hx⟩, 1)) g = g := hg ⟨x, hx⟩
      rw [hmult_left ⟨x, hx⟩] at hpt
      have hpt' := congrArg (fun z : ↥(Q.subgroupOf B) => (z : ↥B)) hpt
      rw [MulAut.conjNormal_apply] at hpt'
      have hval : x * ((g : ↥B) : G) * x⁻¹ = ((g : ↥B) : G) := by
        have h := congrArg (fun z : ↥B => (z : G)) hpt'
        simpa using h
      calc ((g : ↥B) : G) * x = (x * ((g : ↥B) : G) * x⁻¹) * x := by rw [hval]
        _ = x * ((g : ↥B) : G) := by group
    have hfixg := hfix ((g : ↥B) : G) g.2 hgc (y : G) y.2
    show MulAut.conjNormal (mult (1, y)) g = g
    rw [hmult_right y]
    apply Subtype.ext
    show (((MulAut.conjNormal (⟨(y : G), hKB y.2⟩ : ↥B)) g : ↥(Q.subgroupOf B)) : ↥B) = (g : ↥B)
    rw [MulAut.conjNormal_apply]
    apply Subtype.ext
    show (y : G) * ((g : ↥B) : G) * (y : G)⁻¹ = ((g : ↥B) : G)
    rw [← hfixg]
    group
  have hthom := OddOrder.Isaacs.Ch04.isaacs_thm_4_31_external φ
    (hQp.of_equiv e.symm) hPp hKc hfixφ
  have hthom' : ∀ (y : ↥K) (b : ↥(Q.subgroupOf B)), (φ (1, y)) b = b :=
    (OddOrder.Isaacs.Ch04.actionCommutator_eq_bot_iff_acts_trivially _).mp hthom
  -- conclude
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hpt : MulAut.conjNormal (mult (1, ⟨y, hy⟩)) (e.symm ⟨k, hk⟩) = e.symm ⟨k, hk⟩ :=
    hthom' ⟨y, hy⟩ (e.symm ⟨k, hk⟩)
  rw [hmult_right ⟨y, hy⟩] at hpt
  have hpt' := congrArg (fun z : ↥(Q.subgroupOf B) => (z : ↥B)) hpt
  rw [MulAut.conjNormal_apply] at hpt'
  have hval : y * k * y⁻¹ = k := by
    have h := congrArg (fun z : ↥B => (z : G)) hpt'
    rw [he_symm_apply ⟨k, hk⟩] at h
    simpa using h
  calc y * k = (y * k * y⁻¹) * y := by group
    _ = k * y := by rw [hval]

end Thompson

/-! ## 4. `Z(F(A))` centralises every `S ≤ F*(A)` -/

section ZCenter

variable {G : Type} [Group G] [Finite G]

/-- `Z(F(A))` centralises `S` as soon as `S ≤ F*(A) = F(A) ⊔ E(A)`: since `Z(F(A)) ≤ F(A)`
centralises `F(A)` and `E(A) ≤ C_G(F(A))` (`LayerCentralizesFitting`) centralises `Z(F(A))`,
the join `F(A) ⊔ E(A)` lies in the double centraliser of `Z(F(A))`. -/
theorem zcenterIn_fittingIn_le_centralizer {A S : Subgroup G} (hS : S ≤ Work.GW2.fstarIn A) :
    Work.GW2.zcenterIn (Work.GW2.fittingIn A) ≤ Subgroup.centralizer (S : Set G) := by
  have hZ : Work.GW2.zcenterIn (Work.GW2.fittingIn A) ≤
      Subgroup.centralizer ((Work.GW2.fstarIn A : Subgroup G) : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    rw [Work.GW2.fstarIn_eq_sup]
    refine sup_le ?_ ?_
    · rw [Subgroup.le_centralizer_iff]
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      exact ((Work.GW2.mem_zcenterIn.mp hz).2 f hf).symm
    · intro e he
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact Subgroup.mem_centralizer_iff.mp (Work.BMAX.LayerCentralizesFitting G A he) z
        (Work.GW2.mem_zcenterIn.mp hz).1
  exact le_trans hZ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hS))

/-- If `y` commutes with `x`, it commutes with every element of the cyclic subgroup `⟨x⟩`. -/
theorem commute_zpowers_of_commute {x y : G} (h : y * x = x * y) {k : G}
    (hk : k ∈ Subgroup.zpowers x) : y * k = k * y := by
  have hx : x ∈ Subgroup.centralizer ({y} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact h
  have hk' : k ∈ Subgroup.centralizer ({y} : Set G) := (Subgroup.zpowers_le.mpr hx) hk
  exact (Subgroup.mem_centralizer_iff.mp hk') y (Set.mem_singleton y)

end ZCenter

/-! ## 5. `C_G(O_p(Z(F(A)))) ≤ A` -/

section Centralizer

variable {G : Type} [Group G] [Finite G]

/-- `C_G(O_p(Z(F(A)))) ≤ A` for a coatomic `A` of a finite simple group and
`p ∈ π(F(A))`: `O_p(Z(F(A)))` is a non-trivial subgroup of `A` normalised by `A`, so the
coatomic (simplicity) argument applies.  This is Bender's "hence `C_G(O_p(S)) ≤ A`". -/
theorem centralizer_pCoreIn_zcenterIn_fittingIn_le_coatom (hG : IsSimpleGroup G) (A : Subgroup G)
    (hA : IsCoatom A) (p : ℕ) (hp : p.Prime) (hpi : p ∈ Work.GW2.primesOf (Work.GW2.fittingIn A)) :
    Subgroup.centralizer
      ((Work.GW2.pCoreIn p (Work.GW2.zcenterIn (Work.GW2.fittingIn A)) : Subgroup G) : Set G) ≤ A := by
  have hbot : Work.GW2.pCoreIn p (Work.GW2.zcenterIn (Work.GW2.fittingIn A)) ≠ ⊥ :=
    pCoreIn_zcenterIn_fittingIn_ne_bot A p hp hpi
  have hNA : Work.GW2.pCoreIn p (Work.GW2.zcenterIn (Work.GW2.fittingIn A)) ≤ A :=
    (pCoreIn_le_self p _).trans ((Work.GW2.zcenterIn_le _).trans (Work.GW2.fittingIn_le_self A))
  have hnorm : A ≤ Subgroup.normalizer
      ((Work.GW2.pCoreIn p (Work.GW2.zcenterIn (Work.GW2.fittingIn A)) : Subgroup G) : Set G) :=
    le_normalizer_pCoreIn_zcenterIn_fittingIn A p
  exact le_coatom_of_le_normalizer_of_ne_bot hG hA hbot hNA hnorm
    (Subgroup.centralizer_le_normalizer _)

end Centralizer

/-! ## 6. The Thompson step: reduction to `⁅O_p(B) ⊓ A, O^p(S)⁆ = ⊥` -/

section ThompsonStep

variable {G : Type} [Group G] [Finite G]

/-- **Reduction step.**  Let `N₀ = O_p(Z(F(A)))`.  If `C_G(N₀) ≤ A`, `N₀ ≤ B`, `N₀` centralises
`S`, and `⁅O_p(B) ⊓ A, O^p(S)⁆ = ⊥`, then `⁅O_p(B), O^p(S)⁆ = ⊥`.

Indeed, for each `p'`-element `x ∈ S` Thompson's `P × K` lemma applied to the action of
`N₀ × ⟨x⟩` on the `p`-group `O_p(B) ◁ B` gives `⁅O_p(B), ⟨x⟩⁆ = ⊥`: the actors commute
because `N₀ ≤ C_G(S)`, and the `N₀`-fixed points of `O_p(B)` centralise `x` because they lie
in `C_G(N₀) ∩ O_p(B) ≤ A`, hence in `O_p(B) ⊓ A`.  Since `O^p(S)` is generated by its
`p'`-elements, the conclusion follows. -/
theorem commutator_pCoreIn_pResidualIn_of_coatom_facts (A B S : Subgroup G) (p : ℕ)
    (hp : p.Prime)
    (hN₀B : Work.GW2.pCoreIn p (Work.GW2.zcenterIn (Work.GW2.fittingIn A)) ≤ B)
    (hN₀S : Work.GW2.pCoreIn p (Work.GW2.zcenterIn (Work.GW2.fittingIn A)) ≤
      Subgroup.centralizer (S : Set G))
    (hcent : Subgroup.centralizer
      ((Work.GW2.pCoreIn p (Work.GW2.zcenterIn (Work.GW2.fittingIn A)) : Subgroup G) : Set G) ≤ A)
    (hSB : S ≤ B)
    (hD : ⁅Work.GW2.pCoreIn p B ⊓ A, Work.BMAX.pResidualIn p S⁆ = ⊥) :
    ⁅Work.GW2.pCoreIn p B, Work.BMAX.pResidualIn p S⁆ = ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  refine (Subgroup.le_centralizer_iff (H := Work.GW2.pCoreIn p B)
    (K := Work.BMAX.pResidualIn p S)).mpr ?_
  rw [Work.BMAX.pResidualIn]
  refine (Subgroup.closure_le (K := Subgroup.centralizer
    ((Work.GW2.pCoreIn p B : Subgroup G) : Set G))).mpr ?_
  rintro x ⟨hxS, hxp⟩
  have hKc : ¬ p ∣ Nat.card ↥(Subgroup.zpowers x) := by
    rw [Nat.card_zpowers]
    exact hxp
  have hcomm : ∀ y ∈ Work.GW2.pCoreIn p (Work.GW2.zcenterIn (Work.GW2.fittingIn A)),
      ∀ k ∈ Subgroup.zpowers x, y * k = k * y := by
    intro y hy k hk
    have hyx : y * x = x * y :=
      ((Subgroup.mem_centralizer_iff.mp (hN₀S hy)) x hxS).symm
    exact commute_zpowers_of_commute hyx hk
  have hfix : ∀ q ∈ Work.GW2.pCoreIn p B,
      (∀ y ∈ Work.GW2.pCoreIn p (Work.GW2.zcenterIn (Work.GW2.fittingIn A)),
        q * y = y * q) → ∀ k ∈ Subgroup.zpowers x, q * k = k * q := by
    intro q hq hqN k hk
    have hqC : q ∈ Subgroup.centralizer
        ((Work.GW2.pCoreIn p (Work.GW2.zcenterIn (Work.GW2.fittingIn A)) : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hqN y hy).symm
    have hqD : q ∈ Work.GW2.pCoreIn p B ⊓ A := Subgroup.mem_inf.mpr ⟨hq, hcent hqC⟩
    have hxW : x ∈ Work.BMAX.pResidualIn p S := Work.BMAX.pResidualIn.subset_closure hxS hxp
    have hqx : q * x = x * q := by
      have hmem := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hD) hqD
      exact ((Subgroup.mem_centralizer_iff.mp hmem) x hxW).symm
    exact commute_zpowers_of_commute hqx hk
  have hPK := thompson_PK_commutator (p := p) (B := B) (Q := Work.GW2.pCoreIn p B)
    (P := Work.GW2.pCoreIn p (Work.GW2.zcenterIn (Work.GW2.fittingIn A)))
    (K := Subgroup.zpowers x)
    (pCoreIn_le_self p B) hN₀B (Subgroup.zpowers_le.mpr (hSB hxS)) (le_normalizer_pCoreIn_of_primeFirst p B)
    (isPGroup_pCoreIn B)
    (isPGroup_pCoreIn (Work.GW2.zcenterIn (Work.GW2.fittingIn A))) hKc hcomm hfix
  have hC : Work.GW2.pCoreIn p B ≤ Subgroup.centralizer (Subgroup.zpowers x : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hPK
  refine Subgroup.mem_centralizer_iff.mpr ?_
  intro v hv
  exact ((Subgroup.mem_centralizer_iff.mp (hC hv)) x (Subgroup.mem_zpowers x)).symm

end ThompsonStep

theorem commutator_pCoreIn_pResidualIn_witness {G : Type} [Group G] [Finite G]
    (hG : IsSimpleGroup G) (A B S : Subgroup G) (hA : IsCoatom A) (hB : B ≠ ⊤)
    (hA_dih : Work.GW2.DihOrCycSylow A) (hA_D : Work.GW2.IsDGroup A)
    (hB_dih : Work.GW2.DihOrCycSylow B) (hB_D : Work.GW2.IsDGroup B)
    (hSB : S ≤ B) (hSf : S ≤ Work.GW2.fstarIn A)
    (hSl : Work.GW2.layerIn A ≤ S) (hZs : Work.GW2.zcenterIn (Work.GW2.fittingIn A) ≤ S)
    (p : ℕ) (hp : p.Prime) (hpi : p ∈ Work.GW2.primesOf (Work.GW2.fittingIn A)) :
    ⁅Work.GW2.pCoreIn p B, Work.BMAX.pResidualIn p S⁆ = ⊥ := by
  refine commutator_pCoreIn_pResidualIn_of_coatom_facts A B S p hp ?_ ?_ ?_ hSB ?_
  · exact (pCoreIn_le_self p _).trans (hZs.trans hSB)
  · exact (pCoreIn_le_self p _).trans (zcenterIn_fittingIn_le_centralizer hSf)
  · exact centralizer_pCoreIn_zcenterIn_fittingIn_le_coatom hG A hA p hp hpi
  · exact commutator_pCoreIn_inf_coatom_pResidualIn hG A B S hA hB hA_dih hA_D hB_dih hB_D
      hSB hSf hSl hZs p hp hpi

end Work.BMAX
