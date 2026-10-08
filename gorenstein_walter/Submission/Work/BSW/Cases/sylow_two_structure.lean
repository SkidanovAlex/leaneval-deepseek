import Mathlib
import Submission.Work.BSW.Concl
import Submission.Work.BSW.Api.card_centralizer_of_card_K_two
import Submission.Work.BSW.Cases.bswK2Involution

namespace Work.BSW.Cases

open Subgroup

/-- **Bender 1974, §1**, the `|K| = 2` case: the Sylow 2-structure of `G`.

Since `|K| = 2`, `H = C_G(t) = K⟨s⟩` is a Klein four-group (`Work.BSW.Api.card_centralizer_of_card_K_two`
gives `|H| = 4`, and `Work.BSW.Cases.bswK2Involution` upgrades this to every involution, using that
all involutions are conjugate).  Consequently:

* every Sylow 2-subgroup `P` has order `4`: a nontrivial 2-group has a central involution `z`,
  which is conjugate to `t`, so `P ≤ C_G(z)` with `|C_G(z)| = 4`; and conversely some Sylow contains
  the 2-subgroup `C_G(t)` of order `4`;
* every involution has centralizer of order `4` (conjugation);
* if the involution `u` lies in the Sylow `P` then `P = C_G(u)`: `P` has order `4`, hence is
  commutative, so `P ≤ C_G(u)` and both have order `4`;
* distinct Sylow 2-subgroups meet trivially, since a nontrivial intersection contains an involution
  `u` forcing both to equal `C_G(u)`. -/
theorem sylow_two_structure {G : Type} [Group G] [Finite G] (t s : G) (K : Subgroup G)
    (h : Work.GW2.BSWHyps2 G t s K) (hk : Nat.card ↥K = 2) :
    (∀ P : Sylow 2 G, Nat.card ↥(P : Subgroup G) = 4) ∧
    (∀ u : G, orderOf u = 2 → Nat.card ↥(Subgroup.centralizer ({u} : Set G)) = 4) ∧
    (∀ (u : G) (P : Sylow 2 G), orderOf u = 2 → u ∈ (P : Subgroup G) →
      (P : Subgroup G) = Subgroup.centralizer ({u} : Set G)) ∧
    (∀ P Q : Sylow 2 G, P ≠ Q → (P : Subgroup G) ⊓ (Q : Subgroup G) = ⊥) := by
  -- Condition (iv) of `BSWHyps2`: every involution has centralizer of order `4`.
  have hC : ∀ u : G, orderOf u = 2 → Nat.card ↥(Subgroup.centralizer ({u} : Set G)) = 4 :=
    fun u hu => (Work.BSW.Cases.bswK2Involution h hk hu).1
  -- Every Sylow 2-subgroup has order `4`.
  have hP4 : ∀ P : Sylow 2 G, Nat.card ↥(P : Subgroup G) = 4 := by
    intro P
    refine le_antisymm ?_ ?_
    · -- upper bound: a central involution of `P` is conjugate to `t`, so `P ≤ C_G(z)`.
      by_cases hnt : Nontrivial ↥(P : Subgroup G)
      · haveI : Nontrivial ↥(P : Subgroup G) := hnt
        have hZnt : Nontrivial ↥(Subgroup.center ↥(P : Subgroup G)) :=
          IsPGroup.center_nontrivial (p := 2) P.isPGroup'
        have h2dvd : 2 ∣ Nat.card ↥(Subgroup.center ↥(P : Subgroup G)) := by
          have hZpg : IsPGroup 2 ↥(Subgroup.center ↥(P : Subgroup G)) :=
            P.isPGroup'.to_subgroup _
          rcases hZpg.card_eq_or_dvd with h1 | h2
          · exfalso
            have hlt : 1 < Nat.card ↥(Subgroup.center ↥(P : Subgroup G)) :=
              (Finite.one_lt_card_iff_nontrivial).mpr hZnt
            omega
          · exact h2
        obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card'
          (G := ↥(Subgroup.center ↥(P : Subgroup G))) 2 h2dvd
        let zG : G := (z : ↥(P : Subgroup G))
        have hzG2 : orderOf zG = 2 := by
          have h1 : orderOf (z : ↥(P : Subgroup G)) = orderOf z := Subgroup.orderOf_coe z
          have h2 : orderOf ((z : ↥(P : Subgroup G)) : G) = orderOf (z : ↥(P : Subgroup G)) :=
            Subgroup.orderOf_coe (z : ↥(P : Subgroup G))
          rw [show zG = ((z : ↥(P : Subgroup G)) : G) from rfl, h2, h1, hz]
        have hle : (P : Subgroup G) ≤ Subgroup.centralizer ({zG} : Set G) := by
          intro y hy
          rw [Subgroup.mem_centralizer_singleton_iff]
          have hcomm := (Subgroup.mem_center_iff.mp z.2) (⟨y, hy⟩ : ↥(P : Subgroup G))
          have hcomm' : (y : G) * zG = zG * y := by
            have := congrArg (Subtype.val (p := fun a : G => a ∈ (P : Subgroup G))) hcomm
            simpa [zG] using this
          exact hcomm'
        calc Nat.card ↥(P : Subgroup G)
            ≤ Nat.card ↥(Subgroup.centralizer ({zG} : Set G)) :=
              Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hle)
          _ = 4 := hC zG hzG2
      · -- a subsingleton subgroup is trivial, of order `1 ≤ 4`.
        have hsub : Subsingleton ↥(P : Subgroup G) := not_nontrivial_iff_subsingleton.mp hnt
        have h1 : Nat.card ↥(P : Subgroup G) = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
        omega
    · -- lower bound: some Sylow 2-subgroup contains the 2-group `C_G(t)` of order `4`.
      have hH4 : Nat.card ↥(Subgroup.centralizer ({t} : Set G)) = 4 :=
        Work.BSW.Api.card_centralizer_of_card_K_two h hk
      have hHpg : IsPGroup 2 ↥(Subgroup.centralizer ({t} : Set G)) :=
        IsPGroup.of_card (p := 2) (n := 2) (by rw [hH4]; norm_num)
      obtain ⟨Q, hQ⟩ := hHpg.exists_le_sylow
      have hQeqP : Nat.card ↥(Q : Subgroup G) = Nat.card ↥(P : Subgroup G) :=
        (Nat.card_congr (Sylow.equiv P Q).toEquiv).symm
      have h4dvdQ : 4 ∣ Nat.card ↥(Q : Subgroup G) := by
        rw [← hH4]; exact Subgroup.card_dvd_of_le hQ
      rw [← hQeqP]
      exact Nat.le_of_dvd Nat.card_pos h4dvdQ
  -- An involution lying in a Sylow 2-subgroup determines it.
  have hpart3 : ∀ (u : G) (P : Sylow 2 G), orderOf u = 2 → u ∈ (P : Subgroup G) →
      (P : Subgroup G) = Subgroup.centralizer ({u} : Set G) := by
    intro u P hu huP
    haveI : IsMulCommutative ↥(P : Subgroup G) :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by rw [hP4 P]; norm_num)
    have hle : (P : Subgroup G) ≤ Subgroup.centralizer ({u} : Set G) := by
      intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hh := IsMulCommutative.is_comm.comm (⟨y, hy⟩ : ↥(P : Subgroup G))
        (⟨u, huP⟩ : ↥(P : Subgroup G))
      have hh2 := congrArg (Subtype.val (p := fun a : G => a ∈ (P : Subgroup G))) hh
      simpa using hh2
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hC u hu, hP4 P]
  refine ⟨hP4, hC, hpart3, ?_⟩
  -- Distinct Sylow 2-subgroups meet trivially.
  intro P Q hne
  by_contra hbot
  have hSpg : IsPGroup 2 ↥((P : Subgroup G) ⊓ (Q : Subgroup G)) := P.isPGroup'.to_inf_left
  have hne1 : Nat.card ↥((P : Subgroup G) ⊓ (Q : Subgroup G)) ≠ 1 := by
    intro h1
    exact hbot ((Subgroup.eq_bot_iff_card _).mpr h1)
  have h2dvd : 2 ∣ Nat.card ↥((P : Subgroup G) ⊓ (Q : Subgroup G)) := by
    rcases hSpg.card_eq_or_dvd with h1 | h2
    · exact absurd h1 hne1
    · exact h2
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥((P : Subgroup G) ⊓ (Q : Subgroup G))) 2 h2dvd
  have hxG2 : orderOf (x : G) = 2 := (Subgroup.orderOf_coe x).trans hx
  have hPx := hpart3 (x : G) P hxG2 x.2.1
  have hQx := hpart3 (x : G) Q hxG2 x.2.2
  exact hne (Sylow.ext (hPx.trans hQx.symm))

end Work.BSW.Cases
