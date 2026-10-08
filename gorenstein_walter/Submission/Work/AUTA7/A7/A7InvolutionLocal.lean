import Mathlib
import Submission.Work.AUTA7.Defs
import Submission.Work.A7.Defs
import Submission.Work.AUTA7.A7.CentralizerInvolution
import Submission.Work.AUTA7.A7.InvolutionsConjugate
import Submission.Work.A7F.Facts
import Submission.Work.A7F.normalizer_V1
import Submission.Work.A7F.normal_K_in_centralizer
import Submission.Work.AUTA7.A7.A7KCentralizerCard
import Submission.Work.AUTA7.A7.A7KNoOrderFour

namespace Work.AUTA7.A7

open Subgroup

/-! ## Transport of centralizers and normalizers along a group isomorphism -/

/-- The image of the centralizer of a point is the centralizer of the image. -/
theorem mapCentralizerSingleton {G H : Type*} [Group G] [Group H] (ψ : G ≃* H) (z : G) :
    (Subgroup.centralizer ({z} : Set G)).map ψ.toMonoidHom =
      Subgroup.centralizer ({ψ z} : Set H) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hy1 : y * z = z * y := Subgroup.mem_centralizer_singleton_iff.mp hy
    rw [← hyx]
    rw [Subgroup.mem_centralizer_singleton_iff]
    change ψ.toMonoidHom y * ψ.toMonoidHom z = ψ.toMonoidHom z * ψ.toMonoidHom y
    rw [← map_mul, ← map_mul, hy1]
  · intro x hx
    refine Subgroup.mem_map.mpr ⟨ψ.symm x, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply ψ.injective
    rw [map_mul, map_mul, ψ.apply_symm_apply]
    exact Subgroup.mem_centralizer_singleton_iff.mp hx

/-- The image of the centralizer of a subgroup is the centralizer of the image. -/
theorem mapCentralizerSubgroup {G H : Type*} [Group G] [Group H] (ψ : G ≃* H)
    (K : Subgroup G) :
    (Subgroup.centralizer (K : Set G)).map ψ.toMonoidHom =
      Subgroup.centralizer ((K.map ψ.toMonoidHom) : Set H) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hy1 : ∀ h ∈ K, h * y = y * h := Subgroup.mem_centralizer_iff.mp hy
    rw [← hyx]
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨a, ha, hax⟩ := hb
    rw [← hax, ← map_mul, ← map_mul, hy1 a ha]
  · intro x hx
    refine Subgroup.mem_map.mpr ⟨ψ.symm x, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    apply ψ.injective
    rw [map_mul, map_mul, ψ.apply_symm_apply]
    exact Subgroup.mem_centralizer_iff.mp hx (ψ a) (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩)

/-- The image of the normalizer of a subgroup is the normalizer of the image. -/
theorem mapNormalizerSubgroup {G H : Type*} [Group G] [Group H] (ψ : G ≃* H)
    (K : Subgroup G) :
    (Subgroup.normalizer (K : Set G)).map ψ.toMonoidHom =
      Subgroup.normalizer ((K.map ψ.toMonoidHom) : Set H) :=
  Subgroup.map_equiv_normalizer_eq K ψ

/-! ## The model subgroup `K = ⟨(4 5 6)⟩` -/

/-- `K = a7K` is contained in the centralizer of the model involution `a7Invol = (0 1)(2 3)`. -/
theorem a7K_le_centralizer_a7Invol :
    Work.A7.a7K ≤
      Subgroup.centralizer ({Work.A7.a7Invol} : Set (alternatingGroup (Fin 7))) := by
  rw [Work.A7.a7K, Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
  decide

/-- `a7K` is normal in the centralizer of `a7Invol`, in the `subgroupOf` sense. -/
theorem a7K_normal_in_centralizer_a7Invol :
    (Work.A7.a7K.subgroupOf
      (Subgroup.centralizer ({Work.A7.a7Invol} : Set (alternatingGroup (Fin 7))))).Normal :=
  Work.A7F.normal_K_in_centralizer

/-- The centralizer of `a7K` has order `36`. -/
theorem a7K_centralizer_card :
    Nat.card
      (Subgroup.centralizer (Work.A7.a7K : Set (alternatingGroup (Fin 7)))) = 36 :=
  A7KCentralizerCard

/-- No element of the centralizer of `a7K` has order `4`. -/
theorem a7K_no_order_four :
    ∀ x ∈ Subgroup.centralizer (Work.A7.a7K : Set (alternatingGroup (Fin 7))),
      orderOf x ≠ 4 :=
  A7KNoOrderFour

/-- The normalizer of `a7K` has order `72`. -/
theorem a7K_normalizer_card :
    Nat.card
      (Subgroup.normalizer (Work.A7.a7K : Set (alternatingGroup (Fin 7)))) = 72 := by
  rw [← Work.A7F.normalizer_V1.2]
  exact Work.A7F.normalizer_V1.1

/-! ## The main statement -/

theorem A7InvolutionLocal : Work.GW2.A7InvolutionLocalProp := by
  intro z hz
  refine ⟨Work.A7F.card_centralizer_of_involution z hz, ?_⟩
  obtain ⟨g, hg⟩ := isConj_iff.mp (Work.A7F.isConj_a7Invol_of_orderOf_two z hz)
  -- `hg : g * a7Invol * g⁻¹ = z`
  let ψ : alternatingGroup (Fin 7) ≃* alternatingGroup (Fin 7) := MulAut.conj g
  have hψapp : ψ Work.A7.a7Invol = z := by
    change (MulAut.conj g) Work.A7.a7Invol = z
    rw [MulAut.conj_apply]
    exact hg
  have hC : (Subgroup.centralizer ({Work.A7.a7Invol} : Set (alternatingGroup (Fin 7)))).map
      ψ.toMonoidHom =
      Subgroup.centralizer ({z} : Set (alternatingGroup (Fin 7))) := by
    rw [mapCentralizerSingleton ψ Work.A7.a7Invol, hψapp]
  have hKle : Work.A7.a7K ≤
      Subgroup.centralizer ({Work.A7.a7Invol} : Set (alternatingGroup (Fin 7))) :=
    a7K_le_centralizer_a7Invol
  have hKle' : Work.A7.a7K.map ψ.toMonoidHom ≤
      Subgroup.centralizer ({z} : Set (alternatingGroup (Fin 7))) := by
    rw [← hC]
    exact Subgroup.map_mono hKle
  have hCcard : Nat.card (Subgroup.centralizer
      ((Work.A7.a7K.map ψ.toMonoidHom) : Set (alternatingGroup (Fin 7)))) = 36 := by
    rw [← mapCentralizerSubgroup ψ Work.A7.a7K,
      Subgroup.card_map_of_injective ψ.injective, a7K_centralizer_card]
  refine ⟨Work.A7.a7K.map ψ.toMonoidHom, hKle', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `K` is normal in `C(z)`
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hKle').mpr ?_
    have hNmodel : Subgroup.centralizer ({Work.A7.a7Invol} : Set (alternatingGroup (Fin 7))) ≤
        Subgroup.normalizer (Work.A7.a7K : Set (alternatingGroup (Fin 7))) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKle).mp
        a7K_normal_in_centralizer_a7Invol
    calc Subgroup.centralizer ({z} : Set (alternatingGroup (Fin 7)))
        = (Subgroup.centralizer ({Work.A7.a7Invol} : Set (alternatingGroup (Fin 7)))).map
            ψ.toMonoidHom := hC.symm
      _ ≤ (Subgroup.normalizer (Work.A7.a7K : Set (alternatingGroup (Fin 7)))).map
            ψ.toMonoidHom := Subgroup.map_mono hNmodel
      _ = Subgroup.normalizer
            ((Work.A7.a7K.map ψ.toMonoidHom) : Set (alternatingGroup (Fin 7))) :=
            mapNormalizerSubgroup ψ Work.A7.a7K
  · -- `|K| = 3`
    rw [Subgroup.card_map_of_injective ψ.injective, Work.A7.card_a7K]
  · -- `|C(K)| = 36`
    exact hCcard
  · -- `|N(K)| = 72`
    rw [← mapNormalizerSubgroup ψ Work.A7.a7K,
      Subgroup.card_map_of_injective ψ.injective, a7K_normalizer_card]
  · -- every `2`-subgroup of `C(K)` has order at most `4`
    intro P hP h2
    have hdvd : Nat.card P ∣ 36 := by
      have h := Subgroup.card_subgroup_dvd_card (P.subgroupOf
        (Subgroup.centralizer ((Work.A7.a7K.map ψ.toMonoidHom) : Set (alternatingGroup (Fin 7)))))
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP).toEquiv, hCcard] at h
      exact h
    haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
    obtain ⟨n, hn⟩ := h2.exists_card_eq
    rw [hn] at hdvd ⊢
    have h4 : 2 ^ n ∣ 4 := by
      have hcop : Nat.Coprime (2 ^ n) 9 := (by norm_num : Nat.Coprime 2 9).pow_left n
      have h36 : (36 : ℕ) = 4 * 9 := by norm_num
      exact hcop.dvd_mul_right.mp (h36 ▸ hdvd)
    exact Nat.le_of_dvd (by norm_num) h4
  · -- no element of the centralizer of `K` has order `4`
    intro x hx hx4
    rw [← mapCentralizerSubgroup ψ Work.A7.a7K] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    refine a7K_no_order_four y hy ?_
    rw [← orderOf_injective ψ.toMonoidHom ψ.injective y, hyx, hx4]

end Work.AUTA7.A7
