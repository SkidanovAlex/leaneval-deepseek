import Mathlib
import Submission.Work.Fitting.Defs
import Submission.Work.Fitting.piCore_isPiNat

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `O_π(G) ⊓ O_σ(G) = 1` for disjoint `π`, `σ`

If no prime lies in both `π` and `σ`, then the `π`-core and the `σ`-core of a finite group
intersect trivially.  Indeed the intersection `K = O_π(G) ⊓ O_σ(G)` is contained in each core,
so `|K|` divides `|O_π(G)|` and `|O_σ(G)|`; by `piCore_isPiNat` these are a `π`-number and a
`σ`-number, hence `|K|` is both.  A prime divisor of `|K|` would then lie in `π ∩ σ`, which is
empty, so `|K| = 1` and `K = ⊥`.
-/

noncomputable section

open Classical

namespace Work.Fitting

theorem piCore_inf_eq_bot_of_coprime (π σ : ℕ → Prop) (G : Type*) [Group G] [Finite G]
    (h : ∀ p, π p → σ p → False) :
    Work.Fitting.piCore π G ⊓ Work.Fitting.piCore σ G = ⊥ := by
  -- `O_π(G)` is a `π`-group and `O_σ(G)` is a `σ`-group.
  have hπ : IsPiNat π (Nat.card ↥(piCore π G)) := piCore_isPiNat G π
  have hσ : IsPiNat σ (Nat.card ↥(piCore σ G)) := piCore_isPiNat G σ
  -- Hence `|O_π(G) ⊓ O_σ(G)|` is both a `π`-number and a `σ`-number.
  have hKπ : IsPiNat π (Nat.card ↥(piCore π G ⊓ piCore σ G)) :=
    isPiNat_of_dvd (Subgroup.card_dvd_of_le inf_le_left) hπ
  have hKσ : IsPiNat σ (Nat.card ↥(piCore π G ⊓ piCore σ G)) :=
    isPiNat_of_dvd (Subgroup.card_dvd_of_le inf_le_right) hσ
  -- A prime divisor would lie in both `π` and `σ`, which is impossible.
  have hcard : Nat.card ↥(piCore π G ⊓ piCore σ G) = 1 := by
    by_contra hne
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    exact h p (hKπ p hp hpdvd) (hKσ p hp hpdvd)
  rw [← Subgroup.card_eq_one]
  exact hcard

end Work.Fitting
