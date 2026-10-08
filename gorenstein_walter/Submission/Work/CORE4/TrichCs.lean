import Mathlib
import Submission.Work.CORE4.Defs27
import Submission.Work.CORE4.Case2EightQfacts
import Submission.Work.CORE4ULeP.normalizer_le_normalizer_Qsub

namespace Work.CORE4

open Subgroup

set_option linter.style.haveILetI false

/-! ## Auxiliary lemmas for `Work.CORE4.TrichCs`

The two group-theoretic inputs of part (b) of `TrichCs`, isolated so that they can be reused:
inside a *cyclic* group the elements of order dividing a prime `p` form the unique subgroup of
order `p`; and `H = C_G(t)` normalises `U = O(H)`. -/

/-- **Uniqueness of the order-`p` subgroup of a cyclic group.**  In a finite cyclic group `C`, an
element whose `p`-th power is `1` (`p` prime) lies in every subgroup of order `p`: the subgroup
`⟨x⟩` it generates has order `orderOf x ∣ p`, hence is trivial or of order `p`, and in a cyclic
group two subgroups of the same order coincide (`IsCyclic.subgroup_eq_iff_card_eq`). -/
theorem mem_of_pow_eq_one_of_card_eq_prime {C : Type} [Group C] [Finite C] [IsCyclic C]
    {p : ℕ} (hp : p.Prime) {H : Subgroup C} (hH : Nat.card H = p) {x : C} (hx : x ^ p = 1) :
    x ∈ H := by
  have hdvd : orderOf x ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hx
  rcases (Nat.dvd_prime hp).mp hdvd with h1 | hp'
  · rw [orderOf_eq_one_iff.mp h1]; exact H.one_mem
  · have hK : Subgroup.zpowers x = H := by
      refine (IsCyclic.subgroup_eq_iff_card_eq (H := Subgroup.zpowers x) (K := H)).mpr ?_
      rw [Nat.card_zpowers, hp', hH]
    rw [← hK]
    exact Subgroup.mem_zpowers x

/-- **Ambient form** of `mem_of_pow_eq_one_of_card_eq_prime`: if `K ≤ G` is cyclic, `P ≤ K` has
order the prime `p`, and `x ∈ K` satisfies `x ^ p = 1`, then `x ∈ P`. -/
theorem mem_of_pow_eq_one_of_le_cyclic {G : Type} [Group G] [Finite G] {K P : Subgroup G}
    (hcyc : IsCyclic ↥K) (hPK : P ≤ K) {p : ℕ} (hp : p.Prime) (hPcard : Nat.card P = p)
    {x : G} (hxK : x ∈ K) (hx : x ^ p = 1) : x ∈ P := by
  haveI : IsCyclic ↥K := hcyc
  have hcard : Nat.card (P.subgroupOf K) = p := by
    rw [← hPcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPK).toEquiv
  have hmem : (⟨x, hxK⟩ : ↥K) ∈ P.subgroupOf K :=
    mem_of_pow_eq_one_of_card_eq_prime (C := ↥K) hp hcard
      (Subtype.ext (by simpa using hx))
  exact Subgroup.mem_subgroupOf.mp hmem

/-- `H = C_G(t) ≤ N_G(U)`: `U = O(H)` is the odd core of `H`, hence normal in `H`. -/
private theorem H_le_normalizer_U {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G) :
    B.H ≤ Subgroup.normalizer (B.U : Set G) := by
  have hUH : B.U ≤ B.H := Subgroup.map_subtype_le (Work.GW2.oddCore ↥B.H)
  have hnorm : (B.U.subgroupOf B.H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hUH]
    intro h k hh hk
    obtain ⟨y, hy, rfl⟩ := hh
    exact ⟨⟨k, hk⟩ * y * ⟨k, hk⟩⁻¹,
      (Work.GW2.oddCore_normal ↥B.H).conj_mem y hy ⟨k, hk⟩, by simp⟩
  rw [Subgroup.le_normalizer_iff]
  intro m hm k hk
  exact (Subgroup.normal_subgroupOf_iff hUH).mp hnorm k m hk hm

/-- Design-27 leaf `Work.GW2.C27.TrichCsProp I` (see `CORE4/Defs27.lean`,
`Submission/Work/NOTES_LEAD_gw_design27.md` §3).  Unfolded statement at
`Submission/Work/_design_gw/Core27.lean:382`.

In words: with the §4 (1)–(6) data `C : Case2Ctx6 B` plus `Case2PrePlus`/`Case2SevenFacts`,
`p` prime, `P ≤ C.D.F` of order `p` and `A` the `(p,p)`-subgroup,
(a) `C.D.s` normalises `Qsub p B = Ω₁(Z₂(O_p(U)))`, and
(b) every `s`-fixed element of `Qsub p B` lies in `P`.

Proof: `s ∈ B.S ≤ B.H` and `U = O(H) ⊴ H`, so `s` normalises `U`, hence `O_p(U)`, `Z₂`, `Ω₁`.
For (b): `Qsub p B ≤ U ⊓ F(U)` and `x^p = 1` on `Qsub p B`; an `s`-fixed `x` lies in
`U ⊓ C(s) = D.B0` (`Case2Pre`), hence in `D.B0 ⊓ F(U) = D.F` (`Case2Data.F_def`); the cyclic
`D.F` (`Case2Ctx6.F_cyclic`) contains `P` of prime order `p`, so its unique order-`p` subgroup is
`P` and `x ∈ P`.

Reviewer caveat worth handling: `Odd p` is *not* a hypothesis, so rule out `p = 2` first (then
`A ≤ F ⊔ K ≤ U` would have order 4 against `|U|` odd — or ignore `A` and use `Case2EightObj`'s
`|A| = p²` with `A ≤ U`, `U` odd).  Must be sorry-free: `#print axioms Work.CORE4.TrichCs` =
`[propext, Classical.choice, Quot.sound]`. -/
theorem TrichCs (I : Work.GW2.C4Inputs) : Work.GW2.C27.TrichCsProp I := by
  intro G _ _ hbc B hcase C hplus h7 p P A hp hPF hPcard hObj
  refine ⟨?_, ?_⟩
  · -- (a) `s` lies in `N_G(Q)`: `s ∈ S ≤ H`, `U = O(H) ⊴ H`, and `Q` is characteristic in `U`.
    have hsS : C.D.s ∈ (B.S : Subgroup G) := C.D.s_mem.1
    have hsH : C.D.s ∈ B.H := Work.CORE4.bSetup_S_le_H B hsS
    have hsN : C.D.s ∈ Subgroup.normalizer (B.U : Set G) := H_le_normalizer_U B hsH
    exact Work.CORE4ULeP.normalizer_le_normalizer_Qsub p B hsN
  · -- (b) an `s`-fixed `x ∈ Q` lies in `B₀ ⊓ F(U) = F`, and `x ^ p = 1`; `F` is cyclic and
    -- contains `P` of order the prime `p`.
    intro x hxQ hfix
    have hQfacts :=
      Work.CORE4.Case2EightQfacts I G hbc B hcase C hplus h7 p P A hp hPF hPcard hObj
    have hxFU : x ∈ Work.GW2.fittingIn B.U := hQfacts.1 hxQ
    have hxU : x ∈ B.U := (Subgroup.map_subtype_le (Work.GW2.fitting ↥B.U)) hxFU
    have hxs : x ∈ Subgroup.centralizer ({C.D.s} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      calc C.D.s * x = (C.D.s * x * C.D.s⁻¹) * C.D.s := by group
        _ = x * C.D.s := by rw [hfix]
    have hxB0 : x ∈ C.D.B0 := by
      rw [C.pre.2.2.2.2.2.2.2]
      exact ⟨hxU, hxs⟩
    have hxF : x ∈ C.D.F := by
      rw [C.D.F_def]
      exact ⟨hxB0, hxFU⟩
    have hxp : x ^ p = 1 := hQfacts.2.2.1 x hxQ
    exact mem_of_pow_eq_one_of_le_cyclic C.F_cyclic hPF hp hPcard hxF hxp

end Work.CORE4
