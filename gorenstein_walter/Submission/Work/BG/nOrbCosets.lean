import Mathlib
import Submission.Work.BG.Thm43Defs
import Submission.Work.BG.S_le_H
import Submission.Work.BG.splitglue.Split
import Submission.Work.BG.nOrbIndexDvdSix
import Submission.Work.BG.nOrbIndexOdd
import Submission.Work.BG.nOrbCosetIndexThree

namespace Work.BG

variable {G : Type} [Group G] [Finite G]

/-- Hypothesis 1.1 recalled: for `D.n = 2` the Sylow `2`-subgroup `S` of `G` is a Klein four
group, i.e. `|S| = 4` and every element of `S` is an involution.

The only ingredient is `D.dih : S ≃* DihedralGroup D.n` together with `DihedralGroup 2 ≅ V₄`
(Mathlib's `IsKleinFour (DihedralGroup 2)`, which gives both `|DihedralGroup 2| = 4` and
`w * w = 1`). -/
theorem BGData_isFourGroup (D : Work.GW2.BGData G) (hn : D.n = 2) :
    Work.GW2.IsFourGroup (D.S : Subgroup G) := by
  obtain ⟨e⟩ := D.dih
  rw [hn] at e
  refine ⟨?_, ?_⟩
  · rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  · intro v hv
    have h1 : e ⟨v, hv⟩ * e ⟨v, hv⟩ = 1 := IsKleinFour.mul_self _
    have h2 : (⟨v, hv⟩ : ↥(D.S : Subgroup G)) * ⟨v, hv⟩ = 1 := by
      apply e.injective
      rw [map_mul, h1, map_one]
    simpa [pow_two] using congrArg Subtype.val h2

/-- For `D.n = 2` the Sylow `2`-subgroup `S` of `G` is commutative, being a Klein four group:
from `x * x = y * y = (x * y) * (x * y) = 1` we get `x * y = (x * y)⁻¹ = y⁻¹ * x⁻¹ = y * x`. -/
theorem BGData_S_comm (D : Work.GW2.BGData G) (hn : D.n = 2) :
    ∀ x ∈ (D.S : Subgroup G), ∀ y ∈ (D.S : Subgroup G), x * y = y * x := by
  have h4 := BGData_isFourGroup D hn
  intro x hx y hy
  have hx2 : x * x = 1 := by simpa [pow_two] using h4.2 x hx
  have hy2 : y * y = 1 := by simpa [pow_two] using h4.2 y hy
  have hxy2 : (x * y) * (x * y) = 1 := by
    simpa [pow_two] using h4.2 (x * y) ((D.S : Subgroup G).mul_mem hx hy)
  calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right hxy2).symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [inv_eq_of_mul_eq_one_right hy2, inv_eq_of_mul_eq_one_right hx2]

/-- Group-theoretic input for `Work.GW2.C23.NOrbProp` when `D.n = 2` (so `S ≅ V₄`).

Writing `C = C_G(S)` and `N = N_G(S)`: the cube of every element of `N` lies in `C`, and `N` is
covered by the three cosets `C`, `xC`, `x²C` for every `x ∈ N ∖ C`.

Route sketch: `|N : C|` divides `|N : S|` which divides `|G : S|`, which is odd; and `N/C` acts
faithfully on the three nonidentity elements of `S` (an element of `N` centralizing all of them
centralizes `S = ⟨t₁, t₂⟩`), so `N/C` embeds into `Sym(3)`; hence `|N : C| = 1` or `3`, and
`x ∉ C` forces `3`.  Note: the ASM-world modules (`Work.FUS.*`, `Submission.Work.ASM.Defs`)
cannot be imported together with `Submission.Work.GLUE.Defs`; do not use them.

Where the pieces live: `|N : C| ∣ 6` is `Work.BG.nOrbIndexDvdSix` (faithful action of `N/C` on
the three non-identity elements of `S`), oddness of `|N : C|` is `Work.BG.nOrbIndexOdd` (Sylow),
so `|N : C| ∣ 3`; `Work.BG.nOrbCosetIndexThree` is the covering statement for a normal subgroup
of index `3`, and `Subgroup.pow_index_mem` gives `x ^ 3 ∈ C`. -/
theorem nOrbCosets {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G) (hn : D.n = 2) :
    (∀ x ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G),
        x ^ 3 ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G)) ∧
    (∀ x ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G),
      x ∉ Subgroup.centralizer ((D.S : Subgroup G) : Set G) →
      ∀ y ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G),
        y ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G) ∨
        (∃ c ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G), y = c * x) ∨
        (∃ c ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G), y = c * x ^ 2)) := by
  classical
  set V : Subgroup G := (D.S : Subgroup G) with hVdef
  set N : Subgroup G := Subgroup.normalizer (V : Set G) with hNdef
  set C : Subgroup G := Subgroup.centralizer (V : Set G) with hCdef
  have h4 := BGData_isFourGroup D hn
  have hcard : Nat.card ↥V = 4 := h4.1
  have hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := BGData_S_comm D hn
  have hCN : C ≤ N := Subgroup.centralizer_le_normalizer (V : Set G)
  have hidx6 : (C.subgroupOf N).index ∣ 6 := nOrbIndexDvdSix V hcard
  have hodd : Odd ((C.subgroupOf N).index) := nOrbIndexOdd D.S hcomm
  -- `|N : C|` is odd and divides `6`, hence divides `3`, hence is `1` or `3`.
  have hidx3 : (C.subgroupOf N).index ∣ 3 := by
    have hidx6' : (C.subgroupOf N).index ∣ 2 * 3 := by
      rw [show (2 : ℕ) * 3 = 6 by norm_num]
      exact hidx6
    exact hodd.coprime_two_right.dvd_mul_left.mp hidx6'
  have hcases : (C.subgroupOf N).index = 1 ∨ (C.subgroupOf N).index = 3 :=
    (Nat.dvd_prime Nat.prime_three).mp hidx3
  constructor
  · intro x hxN
    have hmem : (⟨x, hxN⟩ : ↥N) ^ 3 ∈ C.subgroupOf N := by
      rcases hcases with h1 | h3
      · rw [Subgroup.index_eq_one.mp h1]; exact Subgroup.mem_top _
      · rw [← h3]; exact Subgroup.pow_index_mem (C.subgroupOf N) ⟨x, hxN⟩
    simpa using (Subgroup.mem_subgroupOf.mp hmem)
  · intro x hxN hxC y hyN
    rcases hcases with h1 | h3
    · left
      have hmem : (⟨y, hyN⟩ : ↥N) ∈ C.subgroupOf N := by
        rw [Subgroup.index_eq_one.mp h1]; exact Subgroup.mem_top _
      simpa using (Subgroup.mem_subgroupOf.mp hmem)
    · have hxN' : (⟨x, hxN⟩ : ↥N) ∉ C.subgroupOf N := by
        intro h
        exact hxC (by simpa using (Subgroup.mem_subgroupOf.mp h))
      rcases nOrbCosetIndexThree (C.subgroupOf N) h3 hxN' ⟨y, hyN⟩ with
        hmem | ⟨c, hc, hce⟩ | ⟨c, hc, hce⟩
      · left
        simpa using (Subgroup.mem_subgroupOf.mp hmem)
      · right; left
        refine ⟨(c : G), Subgroup.mem_subgroupOf.mp hc, ?_⟩
        simpa using congrArg (fun z : ↥N => (z : G)) hce
      · right; right
        refine ⟨(c : G), Subgroup.mem_subgroupOf.mp hc, ?_⟩
        simpa using congrArg (fun z : ↥N => (z : G)) hce

end Work.BG
