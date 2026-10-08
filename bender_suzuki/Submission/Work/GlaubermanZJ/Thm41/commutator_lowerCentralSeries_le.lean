import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Commutators of terms of the lower central series

This file proves the classical fact that the lower central series is "multiplicative" for the
commutator:

`⁅S.lowerCentralSeries i, S.lowerCentralSeries j⁆ ≤ S.lowerCentralSeries (i + j + 1)`.

The key ingredient is the **three subgroups lemma** in the form `[A, B, C] ≤ N` with `N` a
normal subgroup:

* `commutator_commutator_le_of_rotate_of_normal` : if `⁅⁅H₂, H₃⁆, H₁⁆ ≤ N` and
  `⁅⁅H₃, H₁⁆, H₂⁆ ≤ N` for a normal subgroup `N`, then `⁅⁅H₁, H₂⁆, H₃⁆ ≤ N`.

It is obtained from Mathlib's `Subgroup.commutator_commutator_eq_bot_of_rotate` by passing to the
quotient `G ⧸ N`.

* `commutator_top_lowerCentralSeries_le` : the same fact for the lower central series of the
  whole group `G` (where all terms are normal), proved by induction on `j` using the three
  subgroups lemma.

* `commutator_lowerCentralSeries_le` : the general statement for an arbitrary subgroup `S`,
  obtained by applying the previous result inside `S` and pushing forward along `S.subtype`
  (using `Subgroup.top_subtype_lowerCentralSeries` and `Subgroup.map_commutator`).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped commutatorElement

namespace Work.GlaubermanZJ.Thm41

/-- **The three subgroups lemma, mod a normal subgroup.**  If a normal subgroup `N` contains
`⁅⁅H₂, H₃⁆, H₁⁆` and `⁅⁅H₃, H₁⁆, H₂⁆`, then it contains `⁅⁅H₁, H₂⁆, H₃⁆`.

This is a "mod `N`" version of Mathlib's `Subgroup.commutator_commutator_eq_bot_of_rotate`,
obtained by passing to the quotient by the normal subgroup `N`. -/
theorem commutator_commutator_le_of_rotate_of_normal {G : Type*} [Group G] {N H₁ H₂ H₃ : Subgroup G}
    [N.Normal] (h1 : ⁅⁅H₂, H₃⁆, H₁⁆ ≤ N) (h2 : ⁅⁅H₃, H₁⁆, H₂⁆ ≤ N) :
    ⁅⁅H₁, H₂⁆, H₃⁆ ≤ N := by
  let f := QuotientGroup.mk' N
  have hf : f.ker = N := QuotientGroup.ker_mk' N
  have h1' : ⁅⁅H₂.map f, H₃.map f⁆, H₁.map f⁆ = ⊥ := by
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff, hf]
    exact h1
  have h2' : ⁅⁅H₃.map f, H₁.map f⁆, H₂.map f⁆ = ⊥ := by
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff, hf]
    exact h2
  have h3' := Subgroup.commutator_commutator_eq_bot_of_rotate h1' h2'
  rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff, hf] at h3'
  exact h3'

/-- The lower central series of the whole group is multiplicative for the commutator:
`⁅γᵢ(G), γⱼ(G)⁆ ≤ γ_{i+j+1}(G)`, where `γₖ(G)` denotes `(⊤ : Subgroup G).lowerCentralSeries k`.

Proved by induction on `j`.  Both terms appearing in the three subgroups lemma are dealt with by
the induction hypothesis; all the subgroups involved are normal in `G` (they are characteristic),
so `commutator_commutator_le_of_rotate_of_normal` applies. -/
theorem commutator_top_lowerCentralSeries_le {G : Type*} [Group G] (i j : ℕ) :
    ⁅(⊤ : Subgroup G).lowerCentralSeries i, (⊤ : Subgroup G).lowerCentralSeries j⁆ ≤
      (⊤ : Subgroup G).lowerCentralSeries (i + j + 1) := by
  suffices H : ∀ j, ∀ i, ⁅(⊤ : Subgroup G).lowerCentralSeries i,
      (⊤ : Subgroup G).lowerCentralSeries j⁆ ≤ (⊤ : Subgroup G).lowerCentralSeries (i + j + 1)
    from H j i
  intro j
  induction j with
  | zero =>
    intro i
    rw [Subgroup.lowerCentralSeries_zero, add_zero, Subgroup.lowerCentralSeries_succ]
  | succ j ih =>
    intro i
    set N : Subgroup G := (⊤ : Subgroup G).lowerCentralSeries (i + j + 2) with hN
    haveI : N.Normal := by rw [hN]; infer_instance
    have hL : (⊤ : Subgroup G).lowerCentralSeries (i + (j + 1) + 1) = N := by
      rw [hN, show i + (j + 1) + 1 = i + j + 2 from by omega]
    have h1 : ⁅⁅(⊤ : Subgroup G), (⊤ : Subgroup G).lowerCentralSeries i⁆,
        (⊤ : Subgroup G).lowerCentralSeries j⁆ ≤ N := by
      have key : ⁅⁅(⊤ : Subgroup G), (⊤ : Subgroup G).lowerCentralSeries i⁆,
            (⊤ : Subgroup G).lowerCentralSeries j⁆
          = ⁅(⊤ : Subgroup G).lowerCentralSeries (i + 1),
            (⊤ : Subgroup G).lowerCentralSeries j⁆ := by
        rw [Subgroup.commutator_comm (⊤ : Subgroup G) ((⊤ : Subgroup G).lowerCentralSeries i),
          ← Subgroup.lowerCentralSeries_succ]
      rw [key, hN]
      exact (ih (i + 1)).trans (by rw [show (i + 1) + j + 1 = i + j + 2 by omega])
    have h2 : ⁅⁅(⊤ : Subgroup G).lowerCentralSeries i, (⊤ : Subgroup G).lowerCentralSeries j⁆,
        (⊤ : Subgroup G)⁆ ≤ N := by
      rw [hN]
      have key : (⊤ : Subgroup G).lowerCentralSeries (i + j + 2) =
          ⁅(⊤ : Subgroup G).lowerCentralSeries (i + j + 1), (⊤ : Subgroup G)⁆ := by
        rw [Subgroup.lowerCentralSeries_succ]
      rw [key]
      exact Subgroup.commutator_mono (ih i) le_rfl
    have h3 := commutator_commutator_le_of_rotate_of_normal (N := N) h1 h2
    rw [← Subgroup.lowerCentralSeries_succ] at h3
    rw [Subgroup.commutator_comm] at h3
    rw [hL]
    exact h3

/-- **Commutators of terms of the lower central series.** For any subgroup `S ≤ G` and all
`i j : ℕ`, `⁅S.lowerCentralSeries i, S.lowerCentralSeries j⁆ ≤ S.lowerCentralSeries (i + j + 1)`.

This is `commutator_top_lowerCentralSeries_le` applied to the group `S` and pushed forward along
`S.subtype`. -/
theorem commutator_lowerCentralSeries_le {G : Type*} [Group G] (S : Subgroup G) (i j : ℕ) :
    ⁅S.lowerCentralSeries i, S.lowerCentralSeries j⁆ ≤ S.lowerCentralSeries (i + j + 1) := by
  have h := commutator_top_lowerCentralSeries_le (G := S) i j
  have hmap := Subgroup.map_mono (f := S.subtype) h
  rwa [Subgroup.map_commutator, Subgroup.top_subtype_lowerCentralSeries,
    Subgroup.top_subtype_lowerCentralSeries, Subgroup.top_subtype_lowerCentralSeries] at hmap

end Work.GlaubermanZJ.Thm41
