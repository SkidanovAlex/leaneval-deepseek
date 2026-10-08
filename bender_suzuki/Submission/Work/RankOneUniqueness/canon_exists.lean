import Mathlib
import Submission.Work.RankOneUniqueness.Basic
import Submission.Work.RankOneUniqueness.exists_smul_t_eq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.RankOneUniqueness.canon_exists` — the Bruhat decomposition `G ∖ H = H·t·Q`

Every `g ∉ H` can be written `g = a·t·q` with `a ∈ H`, `q ∈ Q`.
Proof: by 2-transitivity there is `h₀ ∈ H` with `h₀ • (t • ∞) = g • ∞`, so `g⁻¹h₀t ∈ H`,
say `= a₀`; then `g = h₀·t·a₀⁻¹`.  Writing `a₀⁻¹ = q·d` (`Q·D`-factorisation) and using
`t·d = (t d t)·t` with `t d t ∈ H` gives `g = (h₀·(t d t))·t·(d⁻¹qd)`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Submission.Blueprint

namespace Work.RankOneUniqueness

theorem canon_exists {G : Type} [Group G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) {g : G} (hg : g ∉ H) :
    ∃ a ∈ H, ∃ q ∈ Q, g = a * t * q := by
  have h2 : t * t = 1 := mul_self_eq_one h
  have hω : g • pt H ≠ pt H := fun hc => hg ((smul_pt_iff H g).mp hc)
  obtain ⟨h₀, hh₀, hh₀eq⟩ := exists_smul_t_eq h (ω := g • pt H) hω
  have h1 : g⁻¹ * h₀ * t ∈ H := by
    have : (g⁻¹ * h₀ * t) • pt H = pt H := by
      have key := congrArg (fun ω => g⁻¹ • ω) hh₀eq
      simpa [smul_smul, mul_assoc] using key
    exact (smul_pt_iff H _).mp this
  set a₀ : G := g⁻¹ * h₀ * t with ha₀def
  have ha₀ : a₀ ∈ H := h1
  have hgeq : g = h₀ * t * a₀⁻¹ := by
    have key : h₀ * t = g * a₀ := by
      calc h₀ * t = g * (g⁻¹ * h₀ * t) := by group
        _ = g * a₀ := by rw [ha₀def]
    calc g = (g * a₀) * a₀⁻¹ := by group
      _ = (h₀ * t) * a₀⁻¹ := by rw [← key]
  obtain ⟨q, hq, d, hd, hqd⟩ := fact_exists h (H.inv_mem ha₀)
  have hdH : d ∈ H := (mem_twoPoint_iff.mp hd).1
  have hqd' : d⁻¹ * q * (d⁻¹)⁻¹ ∈ Q := conj_mem_of_mem h (H.inv_mem hdH) hq
  refine ⟨h₀ * (t * d * t), H.mul_mem hh₀ (t_mul_mul_t_mem_of_mem_twoPoint h2 hd),
    d⁻¹ * q * (d⁻¹)⁻¹, hqd', ?_⟩
  have hkey : (t * d * t) * t = t * d := by
    rw [mul_assoc (t * d) t t, h2, mul_one]
  have hstep : h₀ * t * (q * d) = (h₀ * (t * d * t)) * t * (d⁻¹ * q * (d⁻¹)⁻¹) := by
    calc h₀ * t * (q * d) = h₀ * ((t * d) * (d⁻¹ * q * (d⁻¹)⁻¹)) := by group
      _ = h₀ * ((t * d * t) * t * (d⁻¹ * q * (d⁻¹)⁻¹)) := by rw [hkey]
      _ = (h₀ * (t * d * t)) * t * (d⁻¹ * q * (d⁻¹)⁻¹) := by group
  calc g = h₀ * t * a₀⁻¹ := hgeq
    _ = h₀ * t * (q * d) := by rw [hqd]
    _ = (h₀ * (t * d * t)) * t * (d⁻¹ * q * (d⁻¹)⁻¹) := hstep

end Work.RankOneUniqueness
