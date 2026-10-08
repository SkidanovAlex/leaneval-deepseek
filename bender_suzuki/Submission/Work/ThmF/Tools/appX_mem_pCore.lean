import Mathlib
import Submission.Work.Fitting.Main

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Elements of `p`-power order in the Fitting subgroup lie in `O_p(G)`

Let `G` be a finite group, `p` a prime and `x ∈ F(G)` an element whose order is a power of `p`
(here: `orderOf x ∣ p ^ k` for some `k`).  Then `x ∈ O_p(G)`.

Mathematically: `F(G)` is nilpotent (`Work.Fitting.fitting_isNilpotent`), and in a finite
nilpotent group the elements of `p`-power order are exactly the elements of the (unique) Sylow
`p`-subgroup `Q`.  Since `F(G) ⊴ G` and `Q` is characteristic in the nilpotent group `F(G)`,
the image of `Q` in `G` is a normal `p`-subgroup of `G`, hence lies in `O_p(G)`
(`Work.Fitting.sylow_map_le_pCore`).

Formally we do not even need the uniqueness of the Sylow subgroup: `⟨x⟩ ≤ F(G)` is a `p`-group,
so it lies in *some* Sylow `p`-subgroup `Q` of `F(G)` by Sylow's first theorem
(`IsPGroup.exists_le_sylow`), and any such `Q` already maps into `O_p(G)`.
-/

set_option linter.style.haveILetI false

namespace Work.ThmF.Tools

theorem appX_mem_pCore {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {k : ℕ} {x : G}
    (hmem : x ∈ Work.Fitting.fitting G) (hord : orderOf x ∣ p ^ k) :
    x ∈ Work.Fitting.pCore p G := by
  classical
  have hp : p.Prime := Fact.out
  -- The order of `x` is a power of `p`.
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp hord
  -- `F(G)` is nilpotent.
  haveI hnil : Group.IsNilpotent ↥(Work.Fitting.fitting G) := Work.Fitting.fitting_isNilpotent G
  -- `x`, viewed as an element of the Fitting subgroup.
  let y : ↥(Work.Fitting.fitting G) := ⟨x, hmem⟩
  have hyval : (y : G) = x := rfl
  have hyord : orderOf y = p ^ j := by
    rw [← Subgroup.orderOf_coe (H := Work.Fitting.fitting G) y, hyval, hj]
  -- `⟨y⟩` is a `p`-subgroup of `F(G)`.
  have hcard : Nat.card ↥(Subgroup.zpowers y) = p ^ j := by
    rw [Nat.card_zpowers, hyord]
  have hpg : IsPGroup p ↥(Subgroup.zpowers y) := IsPGroup.of_card hcard
  -- By Sylow's first theorem it lies in some Sylow `p`-subgroup `Q` of `F(G)`.
  obtain ⟨Q, hQle⟩ := hpg.exists_le_sylow
  have hyQ : y ∈ (Q : Subgroup ↥(Work.Fitting.fitting G)) := hQle (Subgroup.mem_zpowers y)
  -- The image of `Q` in `G` is a normal `p`-subgroup of `G`, hence inside `O_p(G)`.
  have hxQ : x ∈ (Q : Subgroup ↥(Work.Fitting.fitting G)).map (Work.Fitting.fitting G).subtype :=
    Subgroup.mem_map.mpr ⟨y, hyQ, hyval⟩
  exact Work.Fitting.sylow_map_le_pCore (N := Work.Fitting.fitting G) inferInstance hp Q hxQ

end Work.ThmF.Tools
