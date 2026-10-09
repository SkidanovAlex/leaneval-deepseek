import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.prop5

/-- **The Three Subgroups Lemma**, in the form that will be needed for the lower central
series: if `⁅⁅H₂, H₃⁆, H₁⁆` and `⁅⁅H₃, H₁⁆, H₂⁆` are both contained in a normal subgroup `K`
then so is `⁅⁅H₁, H₂⁆, H₃⁆`.  This is proved by passing to the quotient `G ⧸ K`, where the
statement reduces to Mathlib's `Subgroup.commutator_commutator_eq_bot_of_rotate`. -/
theorem ssg_three_subgroups_le {G : Type*} [Group G] {H₁ H₂ H₃ K : Subgroup G} (hK : K.Normal)
    (h1 : ⁅⁅H₂, H₃⁆, H₁⁆ ≤ K) (h2 : ⁅⁅H₃, H₁⁆, H₂⁆ ≤ K) :
    ⁅⁅H₁, H₂⁆, H₃⁆ ≤ K := by
  let π : G →* G ⧸ K := QuotientGroup.mk' K
  have key : ∀ X : Subgroup G, X ≤ K → Subgroup.map π X = ⊥ := by
    intro X hX
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hX
  have h1' : ⁅⁅Subgroup.map π H₂, Subgroup.map π H₃⁆, Subgroup.map π H₁⁆ = ⊥ := by
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator]
    exact key _ h1
  have h2' : ⁅⁅Subgroup.map π H₃, Subgroup.map π H₁⁆, Subgroup.map π H₂⁆ = ⊥ := by
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator]
    exact key _ h2
  have hgoal : Subgroup.map π ⁅⁅H₁, H₂⁆, H₃⁆ = ⊥ := by
    rw [Subgroup.map_commutator, Subgroup.map_commutator]
    exact Subgroup.commutator_commutator_eq_bot_of_rotate h1' h2'
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hgoal
  exact hgoal

theorem commutator_lowerCentralSeries_le (P : Type*) [Group P] (m n : ℕ) :
    ⁅(⊤ : Subgroup P).lowerCentralSeries m, (⊤ : Subgroup P).lowerCentralSeries n⁆
      ≤ (⊤ : Subgroup P).lowerCentralSeries (m + n + 1) := by
  -- Classical statement in Mathlib's indexing: `⁅γ_m, γ_n⁆ ≤ γ_{m+n+1}` with `γ_0 = ⊤`.
  -- We prove it by induction on `n`, universally in `m`, using the Three Subgroups Lemma.
  have main : ∀ n m : ℕ,
      ⁅(⊤ : Subgroup P).lowerCentralSeries m, (⊤ : Subgroup P).lowerCentralSeries n⁆
        ≤ (⊤ : Subgroup P).lowerCentralSeries (m + n + 1) := by
    intro n
    induction n with
    | zero =>
      intro m
      simp
    | succ n ih =>
      intro m
      have hmn : (m + 1) + n + 1 = m + n + 2 := by omega
      have h1 : ⁅⁅(⊤ : Subgroup P), (⊤ : Subgroup P).lowerCentralSeries m⁆,
            (⊤ : Subgroup P).lowerCentralSeries n⁆
          ≤ (⊤ : Subgroup P).lowerCentralSeries (m + n + 2) := by
        rw [Subgroup.commutator_comm (⊤ : Subgroup P) ((⊤ : Subgroup P).lowerCentralSeries m),
            ← Subgroup.lowerCentralSeries_succ]
        simpa only [hmn] using ih (m + 1)
      have h2 : ⁅⁅(⊤ : Subgroup P).lowerCentralSeries m,
            (⊤ : Subgroup P).lowerCentralSeries n⁆, (⊤ : Subgroup P)⁆
          ≤ (⊤ : Subgroup P).lowerCentralSeries (m + n + 2) := by
        have h := Subgroup.commutator_mono (ih m) (le_refl (⊤ : Subgroup P))
        rw [← Subgroup.lowerCentralSeries_succ] at h
        exact h
      have hK : ((⊤ : Subgroup P).lowerCentralSeries (m + n + 2)).Normal := by infer_instance
      have h3 := ssg_three_subgroups_le (G := P)
        (H₁ := (⊤ : Subgroup P).lowerCentralSeries n) (H₂ := ⊤)
        (H₃ := (⊤ : Subgroup P).lowerCentralSeries m)
        (K := (⊤ : Subgroup P).lowerCentralSeries (m + n + 2)) hK h1 h2
      have hL : ⁅(⊤ : Subgroup P).lowerCentralSeries m,
            (⊤ : Subgroup P).lowerCentralSeries (n + 1)⁆
          = ⁅⁅(⊤ : Subgroup P).lowerCentralSeries n, (⊤ : Subgroup P)⁆,
              (⊤ : Subgroup P).lowerCentralSeries m⁆ := by
        rw [Subgroup.lowerCentralSeries_succ,
          Subgroup.commutator_comm ((⊤ : Subgroup P).lowerCentralSeries m)
            (⁅(⊤ : Subgroup P).lowerCentralSeries n, (⊤ : Subgroup P)⁆)]
      have hidx : m + (n + 1) + 1 = m + n + 2 := by omega
      rw [hL, hidx]
      exact h3
  exact main n m

end Work.SSGRoute.prop5
