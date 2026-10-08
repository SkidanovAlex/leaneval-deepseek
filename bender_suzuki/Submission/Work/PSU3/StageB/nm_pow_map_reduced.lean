import Mathlib
import Submission.Work.PSU3.StageB.nm_pow_map
import Submission.Work.PSU3.StageB.Omega.API

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageB

theorem nm_pow_map_reduced {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) {n : ℕ} (fr : Work.PSU3.CoarseFrame H Q t n)
    (hcard : Nat.card ↥(Work.PSU3.StageB.FX n) = 2 ^ n - 1) (hn : 2 ≤ n) :
    ∃ μ : ℕ, 1 ≤ μ ∧ μ ≤ 2 ^ n - 2 ∧
      ∀ a : (Work.PSU3.E n)ˣ, Work.PSU3.σE (a : Work.PSU3.E n) = a → fr.nm a = a ^ μ := by
  classical
  -- `nm : Eˣ →* Eˣ` is a power map, say `a ↦ a ^ μ₀`, because `Eˣ` is cyclic.
  obtain ⟨μ₀, hμ₀⟩ := nm_pow_map n fr.nm
  -- `2 ^ n - 1 ≥ 3`.
  have hmpos : 0 < 2 ^ n - 1 := by
    have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  -- `nm` is injective on the fixed units `F*` (Peterfalvi's action of `K` on `Q₀`).
  have hinj : Function.Injective (nmF fr) := nmF_injective hS fr
  -- On `F*` the power map `(·) ^ μ₀` agrees with `nm`, hence is injective.
  have hpow : ∀ u : ↥(FX n), nmF fr u = u ^ μ₀ := by
    intro u
    apply Subtype.ext
    rw [nmF_coe, Subgroup.coe_pow]
    exact hμ₀ u.1
  -- The exponent `μ₀` is nonzero mod `|F*| = 2 ^ n - 1`, since otherwise `nm` would be trivial
  -- on `F*`, contradicting injectivity (`|F*| ≥ 3`).
  have hne : μ₀ % (2 ^ n - 1) ≠ 0 := by
    intro h0
    have hsub : Subsingleton ↥(FX n) := by
      refine ⟨fun u v => ?_⟩
      apply hinj
      rw [hpow u, hpow v]
      have key : ∀ u : ↥(FX n), u ^ μ₀ = 1 := by
        intro u
        rw [← pow_mod_natCard u μ₀, hcard, h0, pow_zero]
      rw [key u, key v]
    have hle : Nat.card ↥(FX n) ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr hsub
    rw [hcard] at hle
    have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  refine ⟨μ₀ % (2 ^ n - 1), Nat.pos_of_ne_zero hne, ?_, ?_⟩
  · have hlt := Nat.mod_lt μ₀ hmpos
    omega
  · intro a ha
    -- On the fixed units the exponents `μ₀` and `μ₀ % (2 ^ n - 1)` agree.
    have hpow_a : a ^ (μ₀ % (2 ^ n - 1)) = a ^ μ₀ := by
      have h := pow_mod_natCard (⟨a, ha⟩ : ↥(FX n)) μ₀
      rw [hcard] at h
      have h2 := congrArg (fun z : ↥(FX n) => (z : (E n)ˣ)) h
      rw [Subgroup.coe_pow, Subgroup.coe_pow] at h2
      simpa using h2
    rw [hμ₀ a]
    exact hpow_a.symm

end Work.PSU3.StageB
