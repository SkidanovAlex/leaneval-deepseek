import Mathlib
import Submission.Work.CORE4.Defs

namespace Work.CORE4.A7SI

open Subgroup

/-- **Relative index of the centralizer of an involution in a `2`-group covering `A₇`.**

If `E ≤ G` satisfies `E / Z(E) ≃* A₇` with `Z(E)` of odd order, and `t ∈ E` is an involution,
then the centralizer `E ⊓ C_G(t)` has index at least `105` in `E`.

The image `u` of `t` in `E/Z(E) ≅ A₇` is again an involution (because `t ∉ Z(E)`: `Z(E)` is odd
and `t` has order two), so `|C_{A₇}(u)| = 24` and `|A₇ : C_{A₇}(u)| = 2520/24 = 105`.  The
centralizer `A = C_E(t)` contains `Z(E)`, so `A/Z(E) = C_{E/Z(E)}(u)` lies in `C_{A₇}(u)`;
hence `|E : A| = |A₇ : A/Z(E)| ≥ |A₇ : C_{A₇}(u)| = 105`. -/
theorem RelIndexInfCentralizer {G : Type} [Group G] [Finite G] (E : Subgroup G) (t : G)
    (hA7 : Nonempty ((↥E ⧸ Subgroup.center ↥E) ≃* alternatingGroup (Fin 7)))
    (hZodd : Odd (Nat.card (Subgroup.center ↥E)))
    (htE : t ∈ E) (ht2 : orderOf t = 2)
    (ha7 : Work.GW2.A7ModelProp) :
    105 ≤ (E ⊓ Subgroup.centralizer ({t} : Set G)).relIndex E := by
  classical
  obtain ⟨eiso⟩ := hA7
  let Z : Subgroup ↥E := Subgroup.center ↥E
  let q : ↥E →* ↥E ⧸ Z := QuotientGroup.mk' Z
  let π : ↥E →* alternatingGroup (Fin 7) := eiso.toMonoidHom.comp q
  let tE : ↥E := ⟨t, htE⟩
  let u : alternatingGroup (Fin 7) := π tE
  let A : Subgroup ↥E := Subgroup.centralizer ({tE} : Set ↥E)
  have hπsurj : Function.Surjective π :=
    eiso.surjective.comp (QuotientGroup.mk'_surjective Z)
  have hker : π.ker = Z := by
    rw [show π = eiso.toMonoidHom.comp q from rfl,
      MonoidHom.ker_comp_of_injective q eiso.toMonoidHom eiso.injective,
      QuotientGroup.ker_mk']
  have hZA : Z ≤ A := Subgroup.center_le_centralizer ({tE} : Set ↥E)
  have hker_le_A : π.ker ≤ A := by rw [hker]; exact hZA
  have hAidx : A.index = (A.map π).index :=
    (Subgroup.index_map_eq (H := A) (f := π) hπsurj hker_le_A).symm
  -- `tE` is the involution `t` viewed in `↥E`
  have htE2 : orderOf tE = 2 := by
    have h : tE = (⟨t, htE⟩ : ↥E) := rfl
    rw [h, Subgroup.orderOf_mk, ht2]
  -- its image `u` in `A₇` is an involution
  have hu2 : orderOf u = 2 := by
    have hpow : u ^ 2 = 1 := by
      have h : tE ^ 2 = 1 := by rw [← htE2]; exact pow_orderOf_eq_one tE
      have h2 : u = π tE := rfl
      rw [h2, ← map_pow, h, map_one]
    have hne : u ≠ 1 := by
      intro h1
      have htEker : tE ∈ π.ker := by rw [MonoidHom.mem_ker]; exact h1
      rw [hker] at htEker
      have hdvd : orderOf tE ∣ Nat.card Z := Subgroup.orderOf_dvd_natCard _ htEker
      rw [htE2] at hdvd
      have hZcard : Nat.card Z = Nat.card (Subgroup.center ↥E) := rfl
      rw [hZcard] at hdvd
      exact (Nat.not_even_iff_odd.mpr hZodd) (even_iff_two_dvd.mpr hdvd)
    exact orderOf_eq_prime hpow hne
  -- the image of `A` lies in `C_{A₇}(u)`
  have hmaple : A.map π ≤ Subgroup.centralizer ({u} : Set (alternatingGroup (Fin 7))) := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    change π a * π tE = π tE * π a
    have hacomm : a * tE = tE * a := (Subgroup.mem_centralizer_singleton_iff).mp ha
    rw [← map_mul, ← map_mul, hacomm]
  -- `|A₇ : C_{A₇}(u)| = 105`
  have hCidx : (Subgroup.centralizer ({u} : Set (alternatingGroup (Fin 7)))).index = 105 := by
    calc (Subgroup.centralizer ({u} : Set (alternatingGroup (Fin 7)))).index
        = Nat.card (alternatingGroup (Fin 7)) /
            Nat.card (Subgroup.centralizer ({u} : Set (alternatingGroup (Fin 7)))) :=
          Subgroup.index_eq_card_div
            (H := Subgroup.centralizer ({u} : Set (alternatingGroup (Fin 7))))
      _ = 2520 / 24 := by rw [ha7.2.2.1 u hu2, ha7.1]
      _ = 105 := by norm_num
  have hpos : 0 < (A.map π).index := by
    rcases Nat.eq_zero_or_pos (A.map π).index with h | h
    · exfalso
      have hdvd : (A.map π).index ∣ Nat.card (alternatingGroup (Fin 7)) :=
        Subgroup.index_dvd_card (H := A.map π)
      rw [h, ha7.1] at hdvd
      exact absurd hdvd (by norm_num)
    · exact h
  have h105 : 105 ≤ (A.map π).index := by
    rw [← hCidx]
    exact Nat.le_of_dvd hpos (Subgroup.index_dvd_of_le hmaple)
  -- identify the abstract centralizer `A` with `E ⊓ C_G(t)`
  have hsub : (E ⊓ Subgroup.centralizer ({t} : Set G)).subgroupOf E = A := by
    show (E ⊓ Subgroup.centralizer ({t} : Set G)).subgroupOf E
      = Subgroup.centralizer ({⟨t, htE⟩} : Set ↥E)
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      have h1 : ((x : ↥E) : G) ∈ Subgroup.centralizer ({t} : Set G) := hx.2
      rw [Subgroup.mem_centralizer_iff] at h1
      apply Subtype.ext
      exact h1 t rfl
    · intro hx
      refine ⟨x.2, ?_⟩
      change ((x : ↥E) : G) ∈ Subgroup.centralizer ({t} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      have hh2 : (⟨t, htE⟩ : ↥E) * x = x * ⟨t, htE⟩ :=
        (Subgroup.mem_centralizer_iff).mp hx ⟨t, htE⟩ (by simp)
      exact congrArg (fun w : ↥E => (w : G)) hh2
  have hrel : (E ⊓ Subgroup.centralizer ({t} : Set G)).relIndex E = A.index := by
    rw [Subgroup.relIndex, hsub]
  rw [hrel, hAidx]
  exact h105

end Work.CORE4.A7SI
