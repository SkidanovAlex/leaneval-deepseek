import Mathlib
import Submission.Work.Hering.Step5.index_comap_ker_eq_card
import Submission.Work.Hering.Step5.noncomm_of_map_eq
import Submission.Work.Hering.Step5.map_inf_eq_bot

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# A non-abelian subgroup of order `21` inside the normalizer of `U`

Let `G` be a finite group and `U ≤ G` a subgroup such that the conjugation action of the
normalizer `N_G(U)` on `U` is surjective onto `MulAut U` (hypothesis `hsurj`), and such that
the centralizer `C_G(U)` is a `2`-group (`hC2`).  Given a non-abelian subgroup
`Λ ≤ MulAut U` of order `21` (`hΛ`, `hnab`), we produce a subgroup `L ≤ G` with

* `|L| = 21`,
* `L ≤ N_G(U)`,
* `L ⊓ C_G(U) = ⊥`,
* `L` non-abelian.

The argument is Schur--Zassenhaus.  Put `H = N_G(U)`, `C = C_G(U)`, and let
`φ : H →* MulAut U` be the conjugation map, with `φ.ker = C.subgroupOf H`
(`Subgroup.normalizerMonoidHom_ker`).  Let `M = Λ.comap φ ≤ H` be the preimage of `Λ`; then
`φ` restricts to a surjection `M → Λ` with kernel `(C.subgroupOf H).subgroupOf M`, so that
kernel has index `Nat.card Λ = 21` in `M` (`index_comap_ker_eq_card`).  Its cardinality is
`|C|`, a power of `2` (`hC2`), hence coprime to `21`; Schur--Zassenhaus
(`Subgroup.exists_right_complement'_of_coprime`) therefore gives `K ≤ M` with
`M = ker·K`, and `|K| = 21` while `K ⊓ ker = ⊥`.  The kernel of the restriction of `φ` to
`K` is trivial, so `K ≅ Λ`, and `K` is non-abelian (`noncomm_of_map_eq`).  Finally
`L = K.map (H.subtype.comp M.subtype) ≅ K` inherits everything, and `L ⊓ C = ⊥` because
`ker = C.subgroupOf M` (`map_inf_eq_bot`).
-/

namespace Work.Hering.Step5

open Subgroup

theorem exists_order21_le_normalizer {G : Type*} [Group G] [Finite G] {U : Subgroup G}
    (Λ : Subgroup (MulAut U)) (hΛ : Nat.card Λ = 21)
    (hnab : ∃ a b : ↥Λ, a * b ≠ b * a)
    (hsurj : Function.Surjective (Subgroup.normalizerMonoidHom U))
    (hC2 : IsPGroup 2 ↥(Subgroup.centralizer (U : Set G))) :
    ∃ L : Subgroup G, Nat.card L = 21 ∧ L ≤ Subgroup.normalizer (U : Set G) ∧
      L ⊓ Subgroup.centralizer (U : Set G) = ⊥ ∧ (∃ a b : ↥L, a * b ≠ b * a) := by
  let H : Subgroup G := Subgroup.normalizer (U : Set G)
  let C : Subgroup G := Subgroup.centralizer (U : Set G)
  let φ : H →* MulAut U := Subgroup.normalizerMonoidHom U
  have hker : φ.ker = C.subgroupOf H := Subgroup.normalizerMonoidHom_ker U
  have hφrange : φ.range = ⊤ := MonoidHom.range_eq_top.mpr hsurj
  have hCH : C ≤ H := Subgroup.centralizer_le_normalizer (U : Set G)
  let M : Subgroup H := Λ.comap φ
  have hCM' : C.subgroupOf H ≤ M := by
    intro x hx
    rw [Subgroup.mem_comap]
    have hx' : φ x = 1 := MonoidHom.mem_ker.mp (hker ▸ hx)
    rw [hx']
    exact Λ.one_mem
  let f : M →* MulAut U := φ.comp M.subtype
  have hfker : f.ker = (C.subgroupOf H).subgroupOf M := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have h1 : (x : H) ∈ φ.ker := hx
      rw [hker, Subgroup.mem_subgroupOf] at h1
      exact h1
    · intro hx
      have h1 : (x : H) ∈ C.subgroupOf H := Subgroup.mem_subgroupOf.mpr hx
      rw [← hker] at h1
      exact h1
  have hfrange : f.range = Λ := by
    change (φ.comp M.subtype).range = Λ
    rw [MonoidHom.range_comp, Subgroup.range_subtype, Subgroup.map_comap_eq, hφrange, top_inf_eq]
  have hidx : f.ker.index = 21 := by
    have h := index_comap_ker_eq_card φ hsurj Λ
    have hfk : f.ker = Subgroup.comap (Subgroup.comap φ Λ).subtype φ.ker := rfl
    rw [hΛ, ← hfk] at h
    exact h
  have hcard : Nat.card ↥f.ker = Nat.card ↥C := by
    rw [hfker]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCM').toEquiv).trans
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCH).toEquiv)
  have hcop : Nat.Coprime (Nat.card ↥f.ker) f.ker.index := by
    rw [hcard, hidx]
    obtain ⟨n, hn⟩ := isPGroup_iff_card_dvd_pow.mp hC2
    have h2 : Nat.Coprime (2 ^ n) 21 := (by norm_num : Nat.Coprime 2 21).pow_left n
    exact h2.coprime_dvd_left hn
  obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hKcard : Nat.card ↥K = 21 := ((hK.symm).index_eq_card).symm.trans hidx
  have hKdisj : K ⊓ f.ker = ⊥ := by
    have h := hK.disjoint
    rw [disjoint_iff] at h
    rwa [inf_comm]
  have hKnab : ∃ a b : ↥K, a * b ≠ b * a := by
    have hmap : Subgroup.map f K = Λ := by
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · calc Subgroup.map f K ≤ f.range := Subgroup.map_le_range f K
          _ = Λ := hfrange
      · rw [hΛ]
        have hg : Function.Injective (f.comp K.subtype) := by
          rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
          intro y hy
          rw [MonoidHom.mem_ker] at hy
          have hmem : (y : ↥M) ∈ K ⊓ f.ker := ⟨y.2, hy⟩
          rw [hKdisj] at hmem
          simpa using hmem
        have h2 : Nat.card ↥(Subgroup.map f K) = Nat.card ↥K := by
          have hr : (f.comp K.subtype).range = Subgroup.map f K := by
            rw [MonoidHom.range_comp, Subgroup.range_subtype]
          rw [← hr, MonoidHom.range_eq_map]
          rw [Subgroup.card_map_of_injective (K := (⊤ : Subgroup ↥K)) hg]
          exact Subgroup.card_top
        rw [h2, hKcard]
    exact noncomm_of_map_eq f Λ hmap hnab
  let ι : M →* G := H.subtype.comp M.subtype
  have hιinj : Function.Injective ι := (Subgroup.subtype_injective H).comp (Subgroup.subtype_injective M)
  refine ⟨Subgroup.map ι K, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hιinj]
    exact hKcard
  · rintro x ⟨k, -, rfl⟩
    exact Subtype.coe_prop (M.subtype k)
  · have hK' : K ⊓ (C.subgroupOf H).subgroupOf M = ⊥ := by
      rw [← hfker]; exact hKdisj
    exact map_inf_eq_bot hCH hCM' hK'
  · obtain ⟨a, b, hab⟩ := hKnab
    have e : ↥K ≃* ↥(Subgroup.map ι K) := Subgroup.equivMapOfInjective K ι hιinj
    exact ⟨e a, e b, fun hcon => hab (e.injective (by rw [map_mul, map_mul]; exact hcon))⟩

end Work.Hering.Step5
