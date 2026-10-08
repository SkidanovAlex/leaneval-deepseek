import Mathlib
import Submission.Work.PGroup.Omega1
import Submission.Work.PGroup.frattini_eq_agemo_sup_commutator

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Thompson's critical subgroup: the construction inside a finite `p`-group

This file proves the existence of a Thompson critical subgroup of a nontrivial finite `p`-group,
in the "intrinsic" form in which the ambient group is the `p`-group itself.

The construction follows Thompson (Feit--Thompson, Lemma 8.2; Gorenstein, *Finite Groups*,
Theorem 5.3.11):

* `K` is a maximal abelian characteristic subgroup of `H`;
* `L` is the inverse image in `H` of `Ω₁(Z(H/K))`, the `p`-socle of the centre of `H/K`;
* `C = C_H(K) ∩ L`.

Then `C` is characteristic, nontrivial, Frattini-in-centre (`Φ(C) ≤ Z(C)`),
commutator-in-centre (`[H, C] ≤ Z(C)`) and self-centralizing (`C_H(C) ≤ C`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open Subgroup
open scoped Pointwise

namespace Work.PGroup

variable {H : Type*} [Group H]

/-- The centre of a subgroup, regarded as a subgroup of the ambient group. -/
def zCenter (C : Subgroup H) : Subgroup H := (Subgroup.center ↥C).map C.subtype

theorem zCenter_eq_inf_centralizer (C : Subgroup H) :
    zCenter C = C ⊓ Subgroup.centralizer (C : Set H) := by
  ext x
  constructor
  · intro hx
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_inf.mpr ⟨c.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨y, hy⟩)
  · intro hx
    obtain ⟨hxC, hxcent⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hxC⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp hxcent) (y : H) y.2

/-- A maximal (by inclusion) abelian characteristic subgroup exists in a finite group. -/
theorem exists_maximal_abelian_characteristic [Finite H] :
    ∃ K : Subgroup H, IsMulCommutative K ∧ K.Characteristic ∧
      ∀ A : Subgroup H, IsMulCommutative A → A.Characteristic → K ≤ A → A = K := by
  have hfin : ({A : Subgroup H | IsMulCommutative A ∧ A.Characteristic} : Set (Subgroup H)).Finite :=
    Set.toFinite _
  obtain ⟨K, hK⟩ := hfin.exists_maximal
    ⟨Subgroup.center H, inferInstance, Subgroup.centerCharacteristic⟩
  exact ⟨K, hK.1.1, hK.1.2,
    fun A hA1 hA2 hKA => le_antisymm (hK.2 ⟨hA1, hA2⟩ hKA) hKA⟩

/-- **Thompson's critical subgroup theorem**, intrinsic form. -/
theorem exists_characteristic_critical_intrinsic [Finite H] {p : ℕ} (hp : p.Prime)
    (hH : IsPGroup p H) [Nontrivial H] :
    ∃ C : Subgroup H, C.Characteristic ∧ C ≠ ⊥ ∧
      (frattini ↥C).map C.subtype ≤ (Subgroup.center ↥C).map C.subtype ∧
      ⁅(⊤ : Subgroup H), C⁆ ≤ (Subgroup.center ↥C).map C.subtype ∧
      Subgroup.centralizer (C : Set H) ≤ C := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, hKcomm, hKchar, hKmax⟩ := exists_maximal_abelian_characteristic (H := H)
  haveI : K.Characteristic := hKchar
  haveI : K.Normal := inferInstance
  have hKne : K ≠ ⊥ := by
    intro hKbot
    have hle : K ≤ Subgroup.center H := hKbot ▸ bot_le
    have hcen : Subgroup.center H = K :=
      hKmax (Subgroup.center H) inferInstance Subgroup.centerCharacteristic hle
    exact (ne_of_gt hH.bot_lt_center) (by rw [hcen, hKbot])
  set Lbar : Subgroup (H ⧸ K) := omega1 (H ⧸ K) p (Subgroup.center (H ⧸ K)) with hLbar
  set L : Subgroup H := Subgroup.comap (QuotientGroup.mk' K) Lbar with hL
  set HK : Subgroup H := Subgroup.centralizer (K : Set H) with hHK
  set C : Subgroup H := HK ⊓ L with hC
  have hK_le_HK : K ≤ HK := by
    rw [hHK]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact setLike_mul_comm (s := K) hy hx
  have hK_le_L : K ≤ L := by
    rw [hL]
    intro x hx
    rw [Subgroup.mem_comap]
    have h1 : QuotientGroup.mk' K x = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']; exact hx
    rw [h1]
    exact Subgroup.one_mem _
  have hK_le_C : K ≤ C := by rw [hC]; exact le_inf hK_le_HK hK_le_L
  have hCne : C ≠ ⊥ :=
    fun hbot => hKne (le_bot_iff.mp (hK_le_C.trans (le_of_eq hbot)))
  have hC_le_HK : C ≤ HK := by rw [hC]; exact inf_le_left
  have hC_le_L : C ≤ L := by rw [hC]; exact inf_le_right
  have hHKchar : HK.Characteristic := by
    rw [hHK]; exact Subgroup.characteristic_centralizer
  have hLbarchar : Lbar.Characteristic := by
    rw [hLbar]; exact omega1_characteristic p Subgroup.centerCharacteristic
  have hLchar : L.Characteristic := by
    rw [hL]; exact Subgroup.Characteristic.comap_quotient_mk hLbarchar
  haveI : HK.Characteristic := hHKchar
  haveI : L.Characteristic := hLchar
  have hCchar : C.Characteristic := by rw [hC]; exact Subgroup.characteristic_inf
  haveI : C.Characteristic := hCchar
  -- `Z(C) = K`
  have hK_le_Zc : K ≤ zCenter C := by
    rw [zCenter_eq_inf_centralizer]
    exact le_inf hK_le_C (Subgroup.le_centralizer_iff.mp hC_le_HK)
  have hZc_comm : IsMulCommutative (zCenter C) := by
    rw [zCenter]; infer_instance
  have hZc_char : (zCenter C).Characteristic := by
    rw [zCenter_eq_inf_centralizer]; exact Subgroup.characteristic_inf
  have hZcC : zCenter C = K := hKmax (zCenter C) hZc_comm hZc_char hK_le_Zc
  have hQinfC : Subgroup.centralizer (C : Set H) ⊓ C = K := by
    rw [inf_comm, ← zCenter_eq_inf_centralizer, hZcC]
  -- `[⊤, C] ≤ Z(C)`
  have hcomm : ⁅(⊤ : Subgroup H), C⁆ ≤ zCenter C := by
    have hmapC : Subgroup.map (QuotientGroup.mk' K) C ≤ Subgroup.center (H ⧸ K) := by
      refine le_trans (Subgroup.map_mono (f := QuotientGroup.mk' K) hC_le_L) ?_
      calc Subgroup.map (QuotientGroup.mk' K) L
          = Subgroup.map (QuotientGroup.mk' K)
              (Subgroup.comap (QuotientGroup.mk' K) Lbar) := by rw [hL]
        _ = (QuotientGroup.mk' K).range ⊓ Lbar := Subgroup.map_comap_eq _ _
        _ ≤ Lbar := inf_le_right
        _ ≤ Subgroup.center (H ⧸ K) := by rw [hLbar]; exact omega1_le p _
    have hzero : Subgroup.map (QuotientGroup.mk' K) ⁅(⊤ : Subgroup H), C⁆ = ⊥ := by
      rw [Subgroup.map_commutator, Subgroup.map_top,
        MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective K)]
      exact le_bot_iff.mp (le_trans (Subgroup.commutator_mono le_top hmapC)
        (le_of_eq (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (by
          intro x _
          rw [Subgroup.mem_centralizer_iff]
          intro z hz
          exact (Subgroup.mem_center_iff.mp hz x).symm))))
    have hker : ⁅(⊤ : Subgroup H), C⁆ ≤ K := by
      have h := (Subgroup.map_eq_bot_iff ⁅(⊤ : Subgroup H), C⁆).mp hzero
      rwa [QuotientGroup.ker_mk'] at h
    exact le_trans hker hK_le_Zc
  -- membership of `p`-th powers of `C` in `K`
  have hpow_mem_K : ∀ c : ↥C, (c : H) ^ p ∈ K := by
    intro c
    have hcL : (c : H) ∈ L := hC_le_L c.2
    rw [hL, Subgroup.mem_comap, hLbar] at hcL
    have h1 : (QuotientGroup.mk' K) ((c : H) ^ p) = 1 := by
      rw [map_pow]
      exact omega1_pow_eq_one inferInstance hcL
    rwa [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at h1
  -- `Φ(C) ≤ Z(C)`
  have hfr : (frattini ↥C).map C.subtype ≤ zCenter C := by
    have hCisP : IsPGroup p ↥C := hH.to_subgroup C
    rw [frattini_eq_powClosure_sup_commutator hp hCisP, Subgroup.map_sup]
    refine le_trans (sup_le ?_ ?_) hK_le_Zc
    · rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro y ⟨x, ⟨c, rfl⟩, rfl⟩
      simpa using hpow_mem_K c
    · rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
      exact le_trans (Subgroup.commutator_mono le_top le_rfl) (hZcC ▸ hcomm)
  -- self-centralizing
  have hsc : Subgroup.centralizer (C : Set H) ≤ C := by
    by_contra hcon
    have hQ_le_HK : Subgroup.centralizer (C : Set H) ≤ HK := by
      rw [hHK]
      intro x hx
      rw [Subgroup.mem_centralizer_iff] at hx ⊢
      intro y hy
      exact hx y (hK_le_C hy)
    have hK_le_Q : K ≤ Subgroup.centralizer (C : Set H) :=
      Subgroup.le_centralizer_iff.mp hC_le_HK
    have hQne : Subgroup.centralizer (C : Set H) ≠ K :=
      fun h => hcon (le_trans (le_of_eq h) hK_le_C)
    haveI : (Subgroup.centralizer (C : Set H)).Normal := by
      haveI : (Subgroup.centralizer (C : Set H)).Characteristic :=
        Subgroup.characteristic_centralizer
      infer_instance
    have hQbar : Subgroup.map (QuotientGroup.mk' K) (Subgroup.centralizer (C : Set H)) ≠ ⊥ := by
      intro hbot
      have h : Subgroup.centralizer (C : Set H) ≤ K := by
        have h' := (Subgroup.map_eq_bot_iff _).mp hbot
        rwa [QuotientGroup.ker_mk'] at h'
      exact hQne (le_antisymm h hK_le_Q)
    have hlarge := inf_omega1_center_ne_bot
      (N := Subgroup.map (QuotientGroup.mk' K) (Subgroup.centralizer (C : Set H)))
      hp (hH.to_quotient K) inferInstance hQbar
    have hHKbar_inf : Subgroup.map (QuotientGroup.mk' K) HK ⊓ Lbar =
        Subgroup.map (QuotientGroup.mk' K) C := by
      refine le_antisymm ?_ ?_
      · intro x hx
        obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
        obtain ⟨h, hhHK, rfl⟩ := Subgroup.mem_map.mp hx1
        have hhL : h ∈ L := by rw [hL, Subgroup.mem_comap]; exact hx2
        exact Subgroup.mem_map.mpr ⟨h, Subgroup.mem_inf.mpr ⟨hhHK, hhL⟩, rfl⟩
      · refine le_inf (Subgroup.map_mono (f := QuotientGroup.mk' K) hC_le_HK) ?_
        calc Subgroup.map (QuotientGroup.mk' K) C
            ≤ Subgroup.map (QuotientGroup.mk' K) L :=
              Subgroup.map_mono (f := QuotientGroup.mk' K) hC_le_L
          _ = Subgroup.map (QuotientGroup.mk' K)
                (Subgroup.comap (QuotientGroup.mk' K) Lbar) := by rw [hL]
          _ = (QuotientGroup.mk' K).range ⊓ Lbar := Subgroup.map_comap_eq _ _
          _ ≤ Lbar := inf_le_right
    have hQbar_inf : Subgroup.map (QuotientGroup.mk' K) (Subgroup.centralizer (C : Set H)) ⊓
        Subgroup.map (QuotientGroup.mk' K) C = ⊥ := by
      refine le_antisymm ?_ bot_le
      intro x hx
      obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨q, hqQ, rfl⟩ := Subgroup.mem_map.mp hx1
      obtain ⟨c, hcC, hc⟩ := Subgroup.mem_map.mp hx2
      have hker : (QuotientGroup.mk' K) (c⁻¹ * q) = 1 := by
        rw [map_mul, map_inv, hc, inv_mul_cancel]
      have hKmem : c⁻¹ * q ∈ K := by
        rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at hker; exact hker
      have hqC : q ∈ C := by
        have : q = c * (c⁻¹ * q) := by group
        rw [this]
        exact C.mul_mem hcC (hK_le_C hKmem)
      have hqK : q ∈ K := by
        rw [← hQinfC]
        exact Subgroup.mem_inf.mpr ⟨hqQ, hqC⟩
      have h1 : (QuotientGroup.mk' K) q = 1 := by
        rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']; exact hqK
      rw [h1]
      simp
    have hcontra : Subgroup.map (QuotientGroup.mk' K) (Subgroup.centralizer (C : Set H)) ⊓
        Lbar = ⊥ := by
      have hA : Subgroup.map (QuotientGroup.mk' K) (Subgroup.centralizer (C : Set H)) ⊓
          Subgroup.map (QuotientGroup.mk' K) HK =
          Subgroup.map (QuotientGroup.mk' K) (Subgroup.centralizer (C : Set H)) :=
        inf_eq_left.mpr (Subgroup.map_mono (f := QuotientGroup.mk' K) hQ_le_HK)
      calc Subgroup.map (QuotientGroup.mk' K) (Subgroup.centralizer (C : Set H)) ⊓ Lbar
          = (Subgroup.map (QuotientGroup.mk' K) (Subgroup.centralizer (C : Set H)) ⊓
              Subgroup.map (QuotientGroup.mk' K) HK) ⊓ Lbar := by rw [hA]
        _ = Subgroup.map (QuotientGroup.mk' K) (Subgroup.centralizer (C : Set H)) ⊓
              (Subgroup.map (QuotientGroup.mk' K) HK ⊓ Lbar) := by rw [inf_assoc]
        _ = Subgroup.map (QuotientGroup.mk' K) (Subgroup.centralizer (C : Set H)) ⊓
              Subgroup.map (QuotientGroup.mk' K) C := by rw [hHKbar_inf]
        _ = ⊥ := hQbar_inf
    exact hlarge hcontra
  exact ⟨C, hCchar, hCne, hfr, hcomm, hsc⟩

end Work.PGroup
