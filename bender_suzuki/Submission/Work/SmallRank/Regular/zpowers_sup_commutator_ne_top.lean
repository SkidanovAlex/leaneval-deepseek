/-
# `Work.SmallRank.Regular.zpowers_sup_commutator_ne_top`

No element of a finite nonabelian `p`-group `G` together with the commutator subgroup generates
`G`.  Equivalently, the abelianization `G ⧸ G'` of a nonabelian `p`-group is never cyclic: a
`p`-group with cyclic abelianization is cyclic, hence abelian (here `G ⧸ G'` is even elementary
abelian of rank `≥ 2`).

The argument below works for any *nilpotent* group, and only uses nilpotency at the very end.
Write `H = ⟨x⟩`, `D = G' = γ₂(G) = ⊤.lowerCentralSeries 1` and `E = γ₃(G) = ⁅D, ⊤⁆`.  If
`H ⊔ D = ⊤` then

* `D = ⁅⊤, ⊤⁆ = ⁅H ⊔ D, ⊤⁆ = ⁅H, ⊤⁆ ⊔ ⁅D, ⊤⁆ = ⁅H, ⊤⁆ ⊔ E` (`Subgroup.commutator_sup_right`),
* `⁅H, ⊤⁆ ≤ E`, because for `h ∈ H` and `g = h' · d ∈ H · D = H ⊔ D` (here `D` is normal, so
  `H ⊔ D = H · D`)
  `⁅h, g⁆ = ⁅h, h'⁆ · h' · ⁅h, d⁆ · h'⁻¹` (`commutatorElement_mul_right_eq_mul_conj`), where
  `⁅h, h'⁆ = 1` since `H` is cyclic and `⁅h, d⁆ ∈ ⁅H, D⁆ ≤ ⁅⊤, D⁆ = E`;

so `D ≤ E`, i.e. `γ₂(G) ≤ γ₃(G)`.  Iterating (`lowerCentralSeries_one_le_add`) gives
`γ₂(G) ≤ γ_{k+1}(G)` for every `k`, and choosing `k` with `γ_{k+1}(G) = ⊥` (nilpotency) then yields
`G' = ⊥`.

A finite `p`-group is nilpotent (`IsPGroup.isNilpotent`), which is the only place `p` is used.
-/
import Mathlib
import Submission.Work.SmallRank.Regular.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Pointwise commutatorElement
open Subgroup

noncomputable section

namespace Work.SmallRank.Regular

/-- **Key step.**  Let `D = ⁅⊤, ⊤⁆` be the derived subgroup of a group `G`, `E = ⁅D, ⊤⁆ = γ₃(G)`,
and let `H ≤ G` be an abelian subgroup (here `⁅H, H⁆ = ⊥`) with `H ⊔ D = ⊤` (i.e. `G = H · G'`).
Then `D ≤ E`.

Both `D` and `E` are stated as variables so that the ambient group is not unfolded during type
class search. -/
theorem commutator_le_gamma3 {G : Type*} [Group G] {H D E : Subgroup G} [hDn : D.Normal]
    [hEn : E.Normal]
    (hD : D = ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆)
    (hE : E = ⁅D, (⊤ : Subgroup G)⁆)
    (hsup : H ⊔ D = ⊤) (hH : ⁅H, H⁆ = ⊥) :
    D ≤ E := by
  -- `D = ⁅H, ⊤⁆ ⊔ E`, and `⁅H, ⊤⁆ ≤ E`, so `D ≤ E`.
  have hDE : D = ⁅H, (⊤ : Subgroup G)⁆ ⊔ E := by
    calc D = ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ := hD
      _ = ⁅H ⊔ D, (⊤ : Subgroup G)⁆ := by rw [hsup]
      _ = ⁅H, (⊤ : Subgroup G)⁆ ⊔ ⁅D, (⊤ : Subgroup G)⁆ :=
            Subgroup.commutator_sup_right H D ⊤
      _ = ⁅H, (⊤ : Subgroup G)⁆ ⊔ E := by rw [hE]
  -- `⁅⊤, D⁆ = E` (used to locate `⁅h, d⁆`).
  have hE' : ⁅(⊤ : Subgroup G), D⁆ = E := by rw [Subgroup.commutator_comm, hE]
  have hHE : ⁅H, (⊤ : Subgroup G)⁆ ≤ E := by
    rw [Subgroup.commutator_le]
    intro h hh g _
    -- write `g = h' * d` with `h' ∈ H`, `d ∈ D`, using that `D` is normal in `G`.
    have hg : g ∈ H ⊔ D := by rw [hsup]; exact Subgroup.mem_top g
    rw [Subgroup.mem_sup_of_normal_right] at hg
    obtain ⟨h', hh', d, hd, rfl⟩ := hg
    rw [commutatorElement_mul_right_eq_mul_conj]
    have h1 : ⁅h, h'⁆ = 1 := by
      have : ⁅h, h'⁆ ∈ ⁅H, H⁆ := Subgroup.commutator_mem_commutator hh hh'
      rw [hH] at this
      exact Subgroup.mem_bot.mp this
    rw [h1, one_mul]
    have h2 : ⁅h, d⁆ ∈ E := by
      have hmem : ⁅h, d⁆ ∈ ⁅H, D⁆ := Subgroup.commutator_mem_commutator hh hd
      exact hE' ▸ Subgroup.commutator_mono_left le_top hmem
    exact hEn.conj_mem _ h2 h'
  rw [hDE]
  exact sup_le hHE le_rfl

/-- If `γ₂(G) ≤ γ₃(G)` then `γ₂(G) ≤ γ_{k+1}(G)` for every `k`. -/
lemma lowerCentralSeries_one_le_add {G : Type*} [Group G]
    (h12 : (⊤ : Subgroup G).lowerCentralSeries 1 ≤ (⊤ : Subgroup G).lowerCentralSeries 2) :
    ∀ k : ℕ, (⊤ : Subgroup G).lowerCentralSeries 1 ≤ (⊤ : Subgroup G).lowerCentralSeries (k + 1) := by
  intro k
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    have hk : (⊤ : Subgroup G).lowerCentralSeries 2 ≤ (⊤ : Subgroup G).lowerCentralSeries (k + 2) := by
      have hmono := Subgroup.commutator_mono_left
        (H₂ := (⊤ : Subgroup G).lowerCentralSeries (k + 1)) (K := (⊤ : Subgroup G)) ih
      simpa only [Subgroup.lowerCentralSeries_succ] using hmono
    exact h12.trans hk

/-- For a finite nonabelian `p`-group `G` and any `x : G`, the subgroup `⟨x⟩ · G'` is a proper
subgroup of `G`: the abelianization of a nonabelian `p`-group is not cyclic. -/
theorem zpowers_sup_commutator_ne_top {p : ℕ} (hp : p.Prime) {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup p G) (hnc : ¬ IsMulCommutative G) (x : G) :
    Subgroup.zpowers x ⊔ Work.SmallRank.commutator G ≠ ⊤ := by
  intro htop
  apply hnc
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hGnil : Group.IsNilpotent G := hG.isNilpotent
  haveI hDn : ((⊤ : Subgroup G).lowerCentralSeries 1).Normal :=
    Subgroup.lowerCentralSeries_normal ⊤ 1
  haveI hEn : ((⊤ : Subgroup G).lowerCentralSeries 2).Normal :=
    Subgroup.lowerCentralSeries_normal ⊤ 2
  -- `⟨x⟩` is cyclic, hence abelian.
  have hH : ⁅Subgroup.zpowers x, Subgroup.zpowers x⁆ = ⊥ := by
    rw [Subgroup.commutator_self_eq_bot_iff, isMulCommutative_iff]
    intro a b
    ext
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp a.2
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp b.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hm, ← hn, zpow_mul_comm]
  have hD : (⊤ : Subgroup G).lowerCentralSeries 1 = ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ := rfl
  have hE : (⊤ : Subgroup G).lowerCentralSeries 2
      = ⁅(⊤ : Subgroup G).lowerCentralSeries 1, (⊤ : Subgroup G)⁆ := rfl
  -- `Work.SmallRank.commutator G` is definitionally `⁅⊤, ⊤⁆ = γ₂(G)`.
  have hsup : Subgroup.zpowers x ⊔ (⊤ : Subgroup G).lowerCentralSeries 1 = ⊤ := htop
  have h12 : (⊤ : Subgroup G).lowerCentralSeries 1 ≤ (⊤ : Subgroup G).lowerCentralSeries 2 :=
    commutator_le_gamma3 hD hE hsup hH
  -- Nilpotency: `γ_n(G) = ⊥` for some `n`; the iteration gives `γ₂(G) ≤ γ_{n+1}(G) ≤ γ_n(G) = ⊥`.
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp hGnil
  have hiter := lowerCentralSeries_one_le_add h12 n
  have hanti : (⊤ : Subgroup G).lowerCentralSeries (n + 1) ≤
      (⊤ : Subgroup G).lowerCentralSeries n :=
    Subgroup.lowerCentralSeries_antitone ⊤ (Nat.le_succ n)
  have hbot : (⊤ : Subgroup G).lowerCentralSeries 1 = ⊥ :=
    le_bot_iff.mp (hiter.trans (hanti.trans (le_of_eq hn)))
  exact (commutator_eq_bot_iff G).mp (by rw [← Subgroup.top_lowerCentralSeries_one]; exact hbot)

end Work.SmallRank.Regular
