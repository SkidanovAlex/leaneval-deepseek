import Mathlib
import Submission.Work.ZassenhausTwoGroup.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `D = H ∩ H^t` acts fixed point freely on `Q`

Feit's Lemma 3.1 wants `H = Q ⋊ D` to be a Frobenius group with kernel `Q`: every `1 ≠ d ∈ D`
has no non-trivial fixed point on `Q`.  In the rank-one Zassenhaus set-up this is the
three-point argument: if `d ∈ D = H ∩ H^t` commuted with `x ∈ Q#`, then `d` would fix the
three distinct points `H`, `tH` and `x·tH` of `Ω = G ⧸ H`, contradicting `IsZassenhaus H`
(and `x·tH ≠ H, tH` uses `Q ⊓ D = ⊥` and `t ∉ H`).
-/

set_option autoImplicit false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausTwoGroup

/-- Membership in `conj t H = t H t⁻¹`. -/
theorem mem_conj_conj {G : Type} [Group G] {H : Subgroup G} (t y : G) :
    y ∈ conj t H ↔ t⁻¹ * y * t ∈ H := by
  constructor
  · intro hy
    obtain ⟨h, hh, hhy⟩ := Subgroup.mem_map.mp hy
    rw [← hhy]
    simpa [MulAut.conj_apply, mul_assoc] using hh
  · intro hy
    exact Subgroup.mem_map.mpr ⟨t⁻¹ * y * t, hy, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem fpf_on_Q {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hz : Submission.Blueprint.IsZassenhaus H) :
    Work.ZassenhausTwoGroup.IsFpfOn (Submission.Blueprint.twoPoint H t) Q := by
  intro d hd hdne x hx hfix
  by_contra hx1
  set ω₁ : G ⧸ H := ((1 : G) : G ⧸ H) with hω₁
  set ω₂ : G ⧸ H := ((t : G) : G ⧸ H) with hω₂
  set ω₃ : G ⧸ H := (((x : G) * t : G) : G ⧸ H) with hω₃
  have hxH : (x : G) ∈ H := h.le hx
  have hdH : d ∈ H := hd.1
  have hdHt : d ∈ conj t H := hd.2
  have hdconj : t⁻¹ * d * t ∈ H := (mem_conj_conj t d).mp hdHt
  have h12 : ω₁ ≠ ω₂ := by
    rw [hω₁, hω₂]
    intro hab
    exact h.not_mem (by simpa using (QuotientGroup.eq.mp hab : (1 : G)⁻¹ * t ∈ H))
  have h13 : ω₁ ≠ ω₃ := by
    rw [hω₁, hω₃]
    intro hab
    have hmem : (1 : G)⁻¹ * (x * t) ∈ H := QuotientGroup.eq.mp hab
    have htH : t ∈ H := by
      have h1 : (x : G) * t ∈ H := by simpa using hmem
      have := H.mul_mem (H.inv_mem hxH) h1
      simpa [mul_assoc] using this
    exact h.not_mem htH
  have h23 : ω₂ ≠ ω₃ := by
    rw [hω₂, hω₃]
    intro hab
    have hmem : t⁻¹ * (x * t) ∈ H := QuotientGroup.eq.mp hab
    have hmem' : t⁻¹ * x * t ∈ H := by simpa [mul_assoc] using hmem
    have hxD : (x : G) ∈ twoPoint H t := ⟨hxH, (mem_conj_conj t x).mpr hmem'⟩
    have : (x : G) ∈ Q ⊓ twoPoint H t := ⟨hx, hxD⟩
    rw [h.inf_eq] at this
    exact hx1 (Subgroup.mem_bot.mp this)
  have hfixω₁ : d • ω₁ = ω₁ := by
    rw [hω₁]
    exact QuotientGroup.eq.mpr (by simpa using hdH)
  have hfixω₂ : d • ω₂ = ω₂ := by
    rw [hω₂]
    calc d • ((t : G) : G ⧸ H) = ((d * t : G) : G ⧸ H) := rfl
      _ = ((t * (t⁻¹ * d * t) : G) : G ⧸ H) := by
            congr 1
            group
      _ = t • (((t⁻¹ * d * t) : G) : G ⧸ H) := rfl
      _ = t • ((1 : G) : G ⧸ H) := by
            congr 1
            exact (QuotientGroup.eq.mpr (by simpa using hdconj)).symm
      _ = ((t : G) : G ⧸ H) := by simp
  have hfixω₃ : d • ω₃ = ω₃ := by
    rw [hω₃]
    have hdx : d * (x : G) = (x : G) * d := by
      calc d * (x : G) = d * x * d⁻¹ * d := by group
        _ = (x : G) * d := by rw [hfix]
    calc d • (((x : G) * t : G) : G ⧸ H)
        = ((d * ((x : G) * t) : G) : G ⧸ H) := rfl
      _ = (((x : G) * (d * t) : G) : G ⧸ H) := by
            congr 1
            calc d * (x * t) = (d * x) * t := by group
              _ = (x * d) * t := by rw [hdx]
              _ = x * (d * t) := by group
      _ = (x : G) • ((d * t : G) : G ⧸ H) := rfl
      _ = (x : G) • (d • ((t : G) : G ⧸ H)) := rfl
      _ = (x : G) • ω₂ := by rw [hfixω₂]
      _ = (((x : G) * t : G) : G ⧸ H) := rfl
  exact hdne (hz ω₁ ω₂ ω₃ h12 h13 h23 d hfixω₁ hfixω₂ hfixω₃)

end Work.ZassenhausTwoGroup
