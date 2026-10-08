import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.bswHyps2_of_config2
import Submission.Work.CORE2A.exists_mul_of_mem_sup_of_normal
import Submission.Work.CORE2A.exists_mul_of_notMem_of_relIndex_eq_two
import Submission.Work.CORE2A.exists_mul_of_mem_involutionSet_H
import Submission.Work.CORE3.SylowDihedral
import Submission.Work.CORE3.OutsideS0OrderTwo
import Submission.Work.CORE3.H_eq_U_sup_S
import Submission.Work.CORE3.Case1aSetup


/-!
# CORE3 / `Case1aFrattini`: the shared vocabulary

The leaf `Work.CORE3.Case1aFrattini` (Bender 1981, §3, p. 222, second step) needs two
sub-results which live in their own modules (so that they can be proved in parallel and
imported by the assembly):

* `Work.CORE3.SActsTriviallyModFitting B` — `S` acts trivially on `U/F(U)`, i.e. `[S,U] ≤ F(U)`
  (this is Bender's "As `S` centralizes `U/F(U)`", which follows from Case (1) of Theorem 2.10:
  for `s ∈ S − S₀` the set `I_U(s)` *is* a subgroup of `F(U)`, and a product of two elements of
  `S − S₀` is an arbitrary element of `S₀`);

* `Work.CORE3.P1SylowIn B D P2` — `P₁ := O_p(U)·P₂` is a Sylow `p`-subgroup of `C_G(V₁)`,
  `V₁ = ⟨t,t₁⟩`.  (`C_G(V₁) = C_U(t₁) ⋊ V₁`, and the two computations
  `|C_G(V₁)|_p = |P|·|C_U(S)|_p = |P₁|` are the content.)

This module only fixes the *notation*; both statements refer to the ambient vocabulary
`Work.GW2` of `Submission.Work.CORE3.Defs`.
-/

open scoped MatrixGroups

namespace Work.CORE3

open Work.GW2
open Subgroup

/-- `S` acts trivially on `U/F(U)`, i.e. `[S,U] ≤ F(U)`: every commutator `u⁻¹ (s u s⁻¹)`
with `s ∈ S`, `u ∈ U` lies in the Fitting subgroup `F(U)`. -/
def SActsTriviallyModFitting {G : Type} [Group G] [Finite G] (B : BenderSetup G) : Prop :=
  ∀ s ∈ (B.S : Subgroup G), ∀ u ∈ B.U, u⁻¹ * (s * u * s⁻¹) ∈ fittingIn B.U

/-- `V₁ = ⟨t, t₁⟩`. -/
def V1 {G : Type} [Group G] [Finite G] (B : BenderSetup G) (D : Case1aData B) : Subgroup G :=
  Subgroup.zpowers B.t ⊔ Subgroup.zpowers D.t1

/-- `P₁ := P·P₂ = O_p(U)·P₂` is a Sylow `p`-subgroup of `C_G(V₁)`. -/
def P1SylowIn {G : Type} [Group G] [Finite G] (B : BenderSetup G) (D : Case1aData B)
    (P2 : Subgroup G) : Prop :=
  (pCoreIn D.p B.U ⊔ P2 : Subgroup G) ≤ centralizer ((V1 B D : Subgroup G) : Set G) ∧
  IsPGroup D.p (↥(pCoreIn D.p B.U ⊔ P2 : Subgroup G)) ∧
  ¬ D.p ∣ (pCoreIn D.p B.U ⊔ P2 : Subgroup G).relIndex
      (centralizer ((V1 B D : Subgroup G) : Set G))

/-- `C_G(V₁) = C_U(t₁) ⋊ V₁`: the centralizer of `V₁ = ⟨t,t₁⟩` is the join of the centralizer
of `t₁` in `U = O(H)` and `V₁` itself.  Since `t` is central in `S` and `S₀` is the cyclic
subgroup of index two of the dihedral group `S`, an element of `S` commuting with `t₁` lies in
`⟨t,t₁⟩ = V₁`. -/
def CentralizerV1Prop {G : Type} [Group G] [Finite G] (B : BenderSetup G)
    (D : Case1aData B) : Prop :=
  centralizer ((V1 B D : Subgroup G) : Set G)
    = (B.U ⊓ centralizer ({D.t1} : Set G)) ⊔ V1 B D

/-- The `p`-part of `C_U(t₁)` is the product of `|O_p(U)|` and the `p`-part of `C_U(S)`:
`|C_U(t₁)|_p = |P| · |C_U(S)|_p`.  This is Bender's computation
`C_U(t₁) = C_U(S) × O_p(U)` read at the prime `p`.
(`Nat.factorization n p` is the exponent of the prime `p` in `n`.) -/
def PpartProp {G : Type} [Group G] [Finite G] (B : BenderSetup G)
    (D : Case1aData B) : Prop :=
  (Nat.card ↥(B.U ⊓ centralizer ({D.t1} : Set G))).factorization D.p
    = (Nat.card ↥(pCoreIn D.p B.U)).factorization D.p
      + (Nat.card ↥(B.U ⊓ centralizer ((B.S : Subgroup G) : Set G))).factorization D.p

end Work.CORE3

namespace Work.CORE3

namespace Work.CORE3

open Work.GW2
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem fourGroup_V1 (hBc : BenderCtx G) (B : BenderSetup G) (D : Case1aData B) :
    IsFourGroup (V1 B D) := by
  classical
  have ht2 : B.t ^ 2 = 1 := by simpa [B.t_order] using pow_orderOf_eq_one B.t
  have ht12 : D.t1 ^ 2 = 1 := by simpa [D.t1_order] using pow_orderOf_eq_one D.t1
  have hcomm : B.t * D.t1 = D.t1 * B.t :=
    (Subgroup.mem_centralizer_iff.mp (Work.CORE2A.bSetup_S_le_H B D.t1_mem)) B.t (by simp)
  have hmul_mem : B.t * D.t1 ∈ (B.S : Subgroup G) :=
    (B.S : Subgroup G).mul_mem (B.S0_le B.t_mem) D.t1_mem
  have hmul_nmem : B.t * D.t1 ∉ B.S0 := by
    intro h
    have h1 : D.t1 ∈ B.S0 := by
      have : B.t⁻¹ * (B.t * D.t1) ∈ B.S0 :=
        B.S0.mul_mem (B.S0.inv_mem B.t_mem) h
      simpa using this
    exact D.t1_nmem h1
  obtain ⟨n, hn, hdih⟩ := Work.CORE3.SylowDihedral G hBc B
  have horder : orderOf (B.t * D.t1) = 2 :=
    Work.CORE3.OutsideS0OrderTwo G hBc B n hn hdih (B.t * D.t1) hmul_mem hmul_nmem
  have hsq_mul : (B.t * D.t1) ^ 2 = 1 := by
    simpa [horder] using pow_orderOf_eq_one (B.t * D.t1)
  have hnormalizer : Subgroup.zpowers D.t1 ≤
      Subgroup.normalizer (Subgroup.zpowers B.t : Set G) := by
    have hcen : Subgroup.zpowers D.t1 ≤
        Subgroup.centralizer (Subgroup.zpowers B.t : Set G) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (Commute.zpow_left (hcomm : Commute B.t D.t1) k).eq
    exact le_trans hcen (Subgroup.centralizer_le_normalizer _)
  have hcoe : ((V1 B D : Subgroup G) : Set G)
      = (Subgroup.zpowers B.t : Set G) * (Subgroup.zpowers D.t1 : Set G) := by
    rw [V1]
    exact Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnormalizer
  have hmem_set : ∀ x : G, x ∈ (V1 B D : Set G) → x ∈ ({1, B.t, D.t1, B.t * D.t1} : Set G) := by
    intro x hx
    rw [hcoe, Set.mem_mul] at hx
    obtain ⟨a, ha, b, hb, hab⟩ := hx
    have ha' : a = 1 ∨ a = B.t :=
      Work.CORE2A.eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two B.t_order ha
    have hb' : b = 1 ∨ b = D.t1 :=
      Work.CORE2A.eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two D.t1_order hb
    rw [← hab]
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
    · simp
    · simp
    · simp
    · simp [hcomm]
  have hset_sub : ({1, B.t, D.t1, B.t * D.t1} : Set G) ⊆ (V1 B D : Set G) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact (V1 B D).one_mem
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers B.t)
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers D.t1)
    · exact (V1 B D).mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers B.t))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers D.t1))
  have hset : (V1 B D : Set G) = ({1, B.t, D.t1, B.t * D.t1} : Set G) :=
    Set.Subset.antisymm hmem_set hset_sub
  have hne_t : B.t ≠ D.t1 := fun h => D.t1_nmem (h ▸ B.t_mem)
  have hn1t : B.t ≠ 1 := by
    intro h
    have hone : orderOf B.t = 1 := by rw [h]; exact orderOf_one
    rw [B.t_order] at hone
    exact absurd hone (by norm_num)
  have hn1t1 : D.t1 ≠ 1 := by
    intro h
    have hone : orderOf D.t1 = 1 := by rw [h]; exact orderOf_one
    rw [D.t1_order] at hone
    exact absurd hone (by norm_num)
  have hdtinv : D.t1⁻¹ = D.t1 := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using ht12)
  have hn1mul : B.t * D.t1 ≠ 1 := by
    intro h
    have h1 : B.t = D.t1 := by
      have h2 : B.t = D.t1⁻¹ := eq_inv_of_mul_eq_one_left h
      rwa [hdtinv] at h2
    exact hne_t h1
  have hmul_ne_t : B.t * D.t1 ≠ B.t := by
    intro h
    exact hn1t1 (mul_left_cancel (by rw [h, mul_one]))
  have hmul_ne_t1 : B.t * D.t1 ≠ D.t1 := by
    intro h
    exact hn1t (mul_right_cancel (by rw [h, one_mul]))
  have h1t : (1 : G) ≠ B.t := fun h => hn1t h.symm
  have h1t1 : (1 : G) ≠ D.t1 := fun h => hn1t1 h.symm
  have h1mul : (1 : G) ≠ B.t * D.t1 := fun h => hn1mul h.symm
  have ht_mul : B.t ≠ B.t * D.t1 := fun h => hmul_ne_t h.symm
  have ht1_mul : D.t1 ≠ B.t * D.t1 := fun h => hmul_ne_t1 h.symm
  have h1n : (1 : G) ∉ ({B.t, D.t1, B.t * D.t1} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨h1t, h1t1, h1mul⟩
  have htn : B.t ∉ ({D.t1, B.t * D.t1} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hne_t, ht_mul⟩
  have ht1n : D.t1 ∉ ({B.t * D.t1} : Set G) := by
    simpa using ht1_mul
  have hcard4 : ({1, B.t, D.t1, B.t * D.t1} : Set G).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem (s := ({B.t, D.t1, B.t * D.t1} : Set G)) (a := 1) h1n,
      Set.ncard_insert_of_notMem (s := ({D.t1, B.t * D.t1} : Set G)) (a := B.t) htn,
      Set.ncard_insert_of_notMem (s := ({B.t * D.t1} : Set G)) (a := D.t1) ht1n,
      Set.ncard_singleton]
  have hcard : Nat.card (V1 B D) = 4 := by
    have hcoe' : Nat.card (V1 B D) = Nat.card ((V1 B D : Subgroup G) : Set G) := rfl
    rw [hcoe', Nat.card_coe_set_eq, hset, hcard4]
  refine ⟨hcard, ?_⟩
  intro v hv
  have hv' := hmem_set v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv'
  rcases hv' with rfl | rfl | rfl | rfl
  · exact one_pow 2
  · exact ht2
  · exact ht12
  · exact hsq_mul

/-- `t₁ * t₁ = 1`. -/
lemma t1_sq (B : BenderSetup G) (D : Case1aData B) : D.t1 * D.t1 = 1 := by
  have h : D.t1 ^ 2 = 1 := by simpa [D.t1_order] using pow_orderOf_eq_one D.t1
  simpa [pow_two] using h

/-- The centralizer of `zpowers g` is the centralizer of `g`. -/
lemma centralizer_zpowers_eq (g : G) :
    Subgroup.centralizer (Subgroup.zpowers g : Set G) = Subgroup.centralizer ({g} : Set G) := by
  refine le_antisymm ?_ ?_
  · exact Subgroup.centralizer_le (fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      exact hx ▸ Subgroup.mem_zpowers g)
  · rw [Subgroup.le_centralizer_iff, Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro y hy
    exact ((Subgroup.mem_centralizer_iff.mp hy) g (by simp)).symm

/-- `t₁ ∈ S − S₀` inverts the cyclic index-two subgroup `S₀`. -/
lemma t1_inverts_S0 (hBc : BenderCtx G) (B : BenderSetup G) (D : Case1aData B) :
    Inverts D.t1 B.S0 := by
  obtain ⟨n, hn, hdih⟩ := Work.CORE3.SylowDihedral G hBc B
  exact Work.CORE2A.inverts_of_dihedral_cyclic_index_two n hn (B.S : Subgroup G) B.S0 hdih
    B.S0_le B.S0_cyclic B.S0_index D.t1 D.t1_mem D.t1_nmem

/-- `C_S(t₁) = ⟨t, t₁⟩ = V₁`. -/
lemma inf_S_centralizer_t1 (hBc : BenderCtx G) (B : BenderSetup G) (D : Case1aData B) :
    (B.S : Subgroup G) ⊓ centralizer ({D.t1} : Set G) = V1 B D := by
  have hinvS0 := t1_inverts_S0 hBc B D
  have hcommS : B.t * D.t1 = D.t1 * B.t :=
    (Subgroup.mem_centralizer_iff.mp (Work.CORE2A.bSetup_S_le_H B D.t1_mem)) B.t (by simp)
  have hsq_of : ∀ x ∈ B.S0, x ^ 2 = 1 → x = 1 ∨ x = B.t := by
    intro x hx0 hx2
    have hdvd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hx2
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hdvd with h | h
    · left; exact orderOf_eq_one_iff.mp h
    · right
      haveI : IsCyclic ↥B.S0 := B.S0_cyclic
      exact congrArg Subtype.val (Work.CORE2A.eq_of_orderOf_eq_two_of_isCyclic
        (a := (⟨x, hx0⟩ : ↥B.S0)) (b := (⟨B.t, B.t_mem⟩ : ↥B.S0))
        (by rw [Subgroup.orderOf_mk]; exact h)
        (by rw [Subgroup.orderOf_mk]; exact B.t_order))
  refine le_antisymm ?_ ?_
  · rintro s ⟨hsS, hsC⟩
    have hsc : D.t1 * s = s * D.t1 := (Subgroup.mem_centralizer_iff.mp hsC) D.t1 (by simp)
    by_cases hs0 : s ∈ B.S0
    · have hinv : D.t1 * s * D.t1⁻¹ = s⁻¹ := hinvS0 s hs0
      have hfix : D.t1 * s * D.t1⁻¹ = s := by rw [hsc]; group
      have hsq : s ^ 2 = 1 := by
        have hsinv : s⁻¹ = s := by rw [← hinv, hfix]
        calc s ^ 2 = s * s := pow_two s
          _ = s⁻¹ * s := by rw [hsinv]
          _ = 1 := inv_mul_cancel s
      rcases hsq_of s hs0 hsq with rfl | rfl
      · exact (V1 B D).one_mem
      · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers B.t)
    · obtain ⟨c, hc, hceq⟩ := Work.CORE2A.exists_mul_of_notMem_of_relIndex_eq_two
        B.S0_index D.t1_mem D.t1_nmem hsS hs0
      have hcc : D.t1 * c * D.t1 = c := by
        have h1 : D.t1 * (D.t1 * c) = (D.t1 * c) * D.t1 := by rw [← hceq]; exact hsc
        rw [← mul_assoc, t1_sq B D, one_mul] at h1
        exact h1.symm
      have hfix : D.t1 * c * D.t1⁻¹ = c := by
        have ht1inv : D.t1⁻¹ = D.t1 := inv_eq_of_mul_eq_one_right (t1_sq B D)
        rw [ht1inv]; exact hcc
      have hinv : D.t1 * c * D.t1⁻¹ = c⁻¹ := hinvS0 c hc
      have hsq : c ^ 2 = 1 := by
        have hcinv : c⁻¹ = c := by rw [← hinv, hfix]
        calc c ^ 2 = c * c := pow_two c
          _ = c⁻¹ * c := by rw [hcinv]
          _ = 1 := inv_mul_cancel c
      rcases hsq_of c hc hsq with rfl | rfl
      · rw [hceq, mul_one]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers D.t1)
      · rw [hceq]
        exact (V1 B D).mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers D.t1))
          (Subgroup.mem_sup_left (Subgroup.mem_zpowers B.t))
  · refine le_inf ?_ ?_
    · rw [V1]
      exact sup_le (Subgroup.zpowers_le.mpr (B.S0_le B.t_mem)) (Subgroup.zpowers_le.mpr D.t1_mem)
    · rw [V1]
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact ((Subgroup.mem_centralizer_iff.mp (Work.CORE2A.bSetup_S_le_H B D.t1_mem)) B.t (by simp)).symm
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        rfl

/-- Conjugation in `H` preserves `U = O(H)`. -/
lemma U_conj_mem (B : BenderSetup G) {h u : G} (hh : h ∈ B.H) (hu : u ∈ B.U) :
    h * u * h⁻¹ ∈ B.U := by
  haveI : (B.U.subgroupOf B.H).Normal := Work.CORE2A.subgroupOf_oddCoreIn_normal B.H
  let h' : ↥B.H := ⟨h, hh⟩
  let u' : ↥B.H := ⟨u, Work.CORE2A.bSetup_U_le_H B hu⟩
  have hu'mem : u' ∈ B.U.subgroupOf B.H := Subgroup.mem_subgroupOf.mpr hu
  have hmem : h' * u' * h'⁻¹ ∈ B.U.subgroupOf B.H :=
    Subgroup.Normal.conj_mem (G := ↥B.H) inferInstance u' hu'mem h'
  have h2 := Subgroup.mem_subgroupOf.mp hmem
  show h * u * h⁻¹ ∈ B.U
  simpa [h', u'] using h2

/-- `C_G(V₁) = C_U(t₁) ⋊ V₁`. -/
theorem centralizer_V1 (hBc : BenderCtx G) (T : LocalToolkit) (B : BenderSetup G)
    (D : Case1aData B) : CentralizerV1Prop B D := by
  have hUsup : B.U ⊔ (B.S : Subgroup G) = B.H := Work.CORE3.H_eq_U_sup_S G T hBc B
  have hUinf : B.U ⊓ (B.S : Subgroup G) = ⊥ := Work.CORE2A.inf_U_S_eq_bot B
  have hSLeH : (B.S : Subgroup G) ≤ B.H := Work.CORE2A.bSetup_S_le_H B
  have hULeH : B.U ≤ B.H := Work.CORE2A.bSetup_U_le_H B
  have hUnorm : (B.U.subgroupOf B.H).Normal := Work.CORE2A.subgroupOf_oddCoreIn_normal B.H
  have hS_inf := inf_S_centralizer_t1 hBc B D
  have hkey : centralizer ((V1 B D : Subgroup G) : Set G) = B.H ⊓ centralizer ({D.t1} : Set G) := by
    rw [V1, Subgroup.centralizer_sup, centralizer_zpowers_eq, centralizer_zpowers_eq]
  show centralizer ((V1 B D : Subgroup G) : Set G)
      = (B.U ⊓ centralizer ({D.t1} : Set G)) ⊔ V1 B D
  rw [hkey]
  refine le_antisymm ?_ ?_
  · rintro x ⟨hxH, hxC⟩
    obtain ⟨u, hu, s, hs, hus⟩ :=
      Work.CORE2A.exists_mul_of_mem_sup_of_normal hULeH hSLeH hUnorm hUsup x hxH
    have hxc : D.t1 * x = x * D.t1 := (Subgroup.mem_centralizer_iff.mp hxC) D.t1 (by simp)
    have hxc' : D.t1 * (u * s) = (u * s) * D.t1 := by rw [hus]; exact hxc
    have hyS : s * D.t1 * s⁻¹ ∈ (B.S : Subgroup G) :=
      (B.S : Subgroup G).mul_mem ((B.S : Subgroup G).mul_mem hs D.t1_mem)
        ((B.S : Subgroup G).inv_mem hs)
    have hyt1 : u * (s * D.t1 * s⁻¹) * u⁻¹ = D.t1 := by
      calc u * (s * D.t1 * s⁻¹) * u⁻¹
          = (u * s) * D.t1 * (u * s)⁻¹ := by group
        _ = D.t1 * (u * s) * (u * s)⁻¹ := by rw [← hxc']
        _ = D.t1 := by group
    have hy_eq : s * D.t1 * s⁻¹ = u⁻¹ * D.t1 * u := by
      have h2 : u * (s * D.t1 * s⁻¹) * u⁻¹ = u * (u⁻¹ * D.t1 * u) * u⁻¹ := by
        rw [hyt1]; group
      exact mul_left_cancel (mul_right_cancel h2)
    have hconj : D.t1⁻¹ * u⁻¹ * D.t1 ∈ B.U := by
      have := U_conj_mem B (B.H.inv_mem (hSLeH D.t1_mem)) (B.U.inv_mem hu)
      simpa using this
    have hyU : D.t1⁻¹ * (s * D.t1 * s⁻¹) ∈ B.U := by
      have heq : D.t1⁻¹ * (s * D.t1 * s⁻¹) = (D.t1⁻¹ * u⁻¹ * D.t1) * u := by
        rw [hy_eq]; group
      rw [heq]
      exact B.U.mul_mem hconj hu
    have hy_bot : D.t1⁻¹ * (s * D.t1 * s⁻¹) ∈ (⊥ : Subgroup G) := by
      rw [← hUinf]
      exact ⟨hyU, (B.S : Subgroup G).mul_mem ((B.S : Subgroup G).inv_mem D.t1_mem) hyS⟩
    have hy_eq_t1 : s * D.t1 * s⁻¹ = D.t1 := by
      have hone : D.t1⁻¹ * (s * D.t1 * s⁻¹) = 1 := Subgroup.mem_bot.mp hy_bot
      calc s * D.t1 * s⁻¹ = D.t1 * (D.t1⁻¹ * (s * D.t1 * s⁻¹)) := by group
        _ = D.t1 * 1 := by rw [hone]
        _ = D.t1 := mul_one D.t1
    have hsC : s ∈ centralizer ({D.t1} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      have h1 : s * D.t1 = D.t1 * s := by
        calc s * D.t1 = (s * D.t1 * s⁻¹) * s := by group
          _ = D.t1 * s := by rw [hy_eq_t1]
      exact h1.symm
    have huC : u ∈ centralizer ({D.t1} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      have h1 : u * D.t1 * u⁻¹ = D.t1 := by
        calc u * D.t1 * u⁻¹ = u * (s * D.t1 * s⁻¹) * u⁻¹ := by rw [hy_eq_t1]
          _ = D.t1 := hyt1
      have h2 : u * D.t1 = D.t1 * u := by
        have h3 := congrArg (fun z => z * u) h1
        simpa [mul_assoc] using h3
      exact h2.symm
    have hsV1 : s ∈ V1 B D := by rw [← hS_inf]; exact ⟨hs, hsC⟩
    have huUC : u ∈ B.U ⊓ centralizer ({D.t1} : Set G) := ⟨hu, huC⟩
    rw [← hus]
    exact Subgroup.mul_mem_sup huUC hsV1
  · refine sup_le ?_ ?_
    · exact le_inf (le_trans inf_le_left hULeH) inf_le_right
    · refine le_inf ?_ ?_
      · rw [V1]
        exact sup_le (Subgroup.zpowers_le.mpr (hSLeH (B.S0_le B.t_mem)))
          (Subgroup.zpowers_le.mpr (hSLeH D.t1_mem))
      · rw [V1]
        refine sup_le ?_ ?_
        · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst hy
          exact ((Subgroup.mem_centralizer_iff.mp (Work.CORE2A.bSetup_S_le_H B D.t1_mem)) B.t (by simp)).symm
        · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst hy
          rfl



/-- `B.H` normalizes `B.U`. -/
lemma H_le_normalizer_U (B : BenderSetup G) : B.H ≤ Subgroup.normalizer (B.U : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro h hh u hu
  exact U_conj_mem B hh hu

/-- `B.H` normalizes `O_p(U)`. -/
lemma H_le_normalizer_P (B : BenderSetup G) (p : ℕ) [Fact p.Prime] :
    B.H ≤ Subgroup.normalizer (Work.GW2.pCoreIn p B.U : Set G) :=
  le_trans (H_le_normalizer_U B) (Work.CORE3.c1aLe_normalizer_pCoreIn p B.U)


end Work.CORE3

end Work.CORE3
