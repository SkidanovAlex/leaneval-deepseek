import Mathlib
import Submission.Work.ZassenhausSuzuki.Odd.OddDefs
import Submission.Work.ZassenhausSuzuki.Odd.isCZ_basic
import Submission.Work.ZassenhausSuzuki.Odd.lt_inf_normalizer_of_lt_of_isPGroup
import Submission.Work.ZassenhausSuzuki.Odd.sylow_map_eq_of_le

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausSuzuki.Odd.isCZ_hall`

The subgroups `A ∈ ℱ` of `Work.ZassenhausSuzuki.Odd.IsCZ` are **Hall subgroups** of `G`:
`|A|` and `[G : A]` are coprime.  This is Huppert–Blackburn XI.10.4 (b) in the form used by the
counting argument of XI.11.6, namely *the centralizer of a non-identity strongly real element
which is not an involution is a Hall subgroup*.

The proof is the one of HB XI.10.4 (b) and uses only the self-centralizing property of such an
`A` (`Work.ZassenhausSuzuki.Odd.isCZ_basic`: `C_G(a) = A` for every `a ∈ A \ {1}`):

Suppose that a prime `p` divides both `|A|` and `[G : A]`.  Let `P` be a Sylow `p`-subgroup of
`A`, viewed inside `G`, and let `Q` be a Sylow `p`-subgroup of `G` containing `P`.  Then `P` is
not a Sylow `p`-subgroup of `G`, so `P < Q`; consequently the normalizer `M = N_Q(P)` of `P` in
`Q` is strictly bigger than `P` (`Work.ZassenhausSuzuki.Odd.lt_inf_normalizer_of_lt_of_isPGroup`)
and is a `p`-group.  As `P` is a maximal `p`-subgroup of `A`
(`Work.ZassenhausSuzuki.Odd.sylow_map_eq_of_le`), `A ⊓ M = P`.  Since `P ⊴ M`, some non-identity
`a ∈ P` is central in `M`, hence every element of `M` commutes with `a`; as `a ∈ A \ {1}` and
`C_G(a) = A`, this forces `M ≤ A`, so `M ≤ A ⊓ M = P`, contradicting `P < M`.

The mathematical content of the argument is isolated in the general statement
`coprime_card_index_of_centralizer_eq` below (a finite group and a subgroup `A` with
`C_G(a) = A` for all `a ∈ A \ {1}`), which is `A`-version of HB XI.10.4 (b) and is what the
counting argument of `Work.ZassenhausSuzuki.Odd.odd_isStronglyReal_of_suzuki` needs.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.ZassenhausSuzuki.Odd

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-- A non-trivial normal subgroup of a finite `p`-group meets the centre non-trivially
(class equation: a `p`-group is nilpotent, and every non-trivial normal subgroup of a nilpotent
group meets the centre). -/
private theorem exists_mem_center_of_isPGroup {p : ℕ} [Fact p.Prime] {P : Subgroup G}
    (hG : IsPGroup p G) [P.Normal] (hP : P ≠ ⊥) :
    ∃ a ∈ P, a ≠ 1 ∧ a ∈ Subgroup.center G := by
  haveI : Group.IsNilpotent G := hG.isNilpotent
  have h : P ⊓ Subgroup.center G ≠ ⊥ := Group.IsNilpotent.inf_center_ne_bot_of_normal hP
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h
  exact ⟨(a : G), a.2.1, fun h1 => ha (Subtype.ext h1), a.2.2⟩

/-- **Huppert–Blackburn XI.10.4 (b).**  Let `A` be a subgroup of a finite group `G` such that
every non-identity element of `A` is self-centralizing inside `A`
(`C_G(a) = A` for all `a ∈ A \ {1}`).  Then `A` is a Hall subgroup of `G`, i.e. `|A|` and
`[G : A]` are coprime.

(Equivalently: a `p`-subgroup of `A` is a Sylow `p`-subgroup of `G` as soon as it is a Sylow
`p`-subgroup of `A`.) -/
theorem coprime_card_index_of_centralizer_eq {A : Subgroup G}
    (hcent : ∀ a ∈ A, a ≠ 1 → Subgroup.centralizer ({a} : Set G) = A) :
    Nat.Coprime (Nat.card ↥A) A.index := by
  classical
  rw [Nat.coprime_iff_gcd_eq_one, Nat.eq_one_iff_not_exists_prime_dvd]
  -- suppose that the prime `p` divides both `|A|` and `[G : A]`
  intro p hp hpdvd
  have hpA : p ∣ Nat.card ↥A := hpdvd.trans (Nat.gcd_dvd_left _ _)
  have hpI : p ∣ A.index := hpdvd.trans (Nat.gcd_dvd_right _ _)
  haveI : Fact p.Prime := ⟨hp⟩
  -- a Sylow `p`-subgroup `P` of `A`, viewed in `G`
  let PA : Sylow p ↥A := Classical.arbitrary _
  let P : Subgroup G := (PA : Subgroup ↥A).map A.subtype
  have hP_isP : IsPGroup p P := (PA.isPGroup').map A.subtype
  have hP_le_A : P ≤ A := Subgroup.map_subtype_le _
  have hpP : p ∣ Nat.card ↥P := by
    rw [Subgroup.card_map_of_injective A.subtype_injective]
    exact Sylow.dvd_card_of_dvd_card PA hpA
  have hP_card_ne_one : Nat.card ↥P ≠ 1 := fun h1 => hp.not_dvd_one (h1 ▸ hpP)
  -- a Sylow `p`-subgroup `Q` of `G` containing `P`
  obtain ⟨Q, hP_le_Q⟩ := IsPGroup.exists_le_sylow hP_isP
  have hP_lt_Q : P < (Q : Subgroup G) := by
    refine lt_of_le_of_ne hP_le_Q (fun heq => ?_)
    have hpPindex : p ∣ P.index := by
      rw [← Subgroup.relIndex_mul_index hP_le_A]
      exact dvd_mul_of_dvd_right hpI _
    exact Sylow.not_dvd_index Q (heq ▸ hpPindex)
  -- the normalizer `M = N_Q(P)` of `P` inside `Q`
  let M : Subgroup G := Subgroup.normalizer (P : Set G) ⊓ (Q : Subgroup G)
  have hM_isP : IsPGroup p M := (Q.isPGroup').to_le inf_le_right
  have hP_le_M : P ≤ M := le_inf Subgroup.le_normalizer hP_le_Q
  have hM_gt_P : P < M :=
    lt_inf_normalizer_of_lt_of_isPGroup (Q := (Q : Subgroup G)) Q.isPGroup' hP_le_Q hP_lt_Q
  -- `P` is a maximal `p`-subgroup of `A`, hence `A ⊓ M = P`
  have hA_inter_M : A ⊓ M = P := by
    have hisP : IsPGroup p ↥(A ⊓ M) := hM_isP.to_le inf_le_right
    have hle : P ≤ A ⊓ M := le_inf hP_le_A hP_le_M
    exact sylow_map_eq_of_le PA hisP inf_le_left hle
  -- `P` is normal in `M`, so some non-identity `a ∈ P` is central in `M`
  haveI : (P.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hP_le_M).mpr inf_le_left
  have hsub_ne_bot : P.subgroupOf M ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥(P.subgroupOf M) = 1 := (Subgroup.eq_bot_iff_card _).mp hbot
    exact hP_card_ne_one (by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP_le_M).toEquiv]
      exact h1)
  obtain ⟨a, ha_mem, ha_ne, ha_center⟩ := exists_mem_center_of_isPGroup hM_isP hsub_ne_bot
  -- `a` is a non-identity element of `A`, so `C_G(a) = A`
  have haP : ((a : M) : G) ∈ P := Subgroup.mem_subgroupOf.mp ha_mem
  have haA : ((a : M) : G) ∈ A := hP_le_A haP
  have ha_ne_one : ((a : M) : G) ≠ 1 := fun h1 => ha_ne (Subtype.ext h1)
  have hcent_a : Subgroup.centralizer ({((a : M) : G)} : Set G) = A := hcent _ haA ha_ne_one
  -- every element of `M` commutes with `a`, hence lies in `A`
  have hM_le_A : M ≤ A := by
    intro m hm
    rw [← hcent_a]
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have hcomm : (⟨m, hm⟩ : M) * a = a * ⟨m, hm⟩ := Subgroup.mem_center_iff.mp ha_center ⟨m, hm⟩
    simpa using congrArg (Subtype.val) hcomm
  -- so `M ≤ A ⊓ M = P`, contradicting `P < M`
  exact not_le_of_gt hM_gt_P (by rw [← hA_inter_M]; exact le_inf hM_le_A le_rfl)

theorem isCZ_hall (h : Work.ZassenhausSuzuki.Odd.SzOddHyp H Q t)
    {A : Subgroup G} (hA : Work.ZassenhausSuzuki.Odd.IsCZ A) :
    Nat.Coprime (Nat.card ↥A) A.index :=
  coprime_card_index_of_centralizer_eq fun a ha ha1 => (isCZ_basic h hA).2.2 a ha ha1 |>.2

end Work.ZassenhausSuzuki.Odd
