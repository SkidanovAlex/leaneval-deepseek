import Mathlib
import Submission.Work.ZassenhausTwoGroup.normalizer_twoPoint

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausSuzuki.centralizer_le_normalizer_twoPoint`

In the split rank-one Zassenhaus set-up (`IsSplitRankOne H Q t`, `IsZassenhaus H`) the
centraliser of a non-identity element `k` of the two-point stabiliser `D = twoPoint H t`
normalises `D`.

The argument is purely geometric, on `Ω = G ⧸ H`.  Write `∞ = H` and let `k ∈ D`, `k ≠ 1`.

* `k` fixes `∞` (as `k ∈ H`) and the point `t • ∞` (as `k ∈ Hᵗ`).
* By the Zassenhaus condition (`IsZassenhaus H`) a non-identity element fixes at most two
  points, so `Fix(k) = {∞, t • ∞}` exactly (`hfix`).
* Every element `g` commuting with `k` therefore permutes `{∞, t • ∞}` (`hconj`): if `k • ω = ω`
  then `k • (g • ω) = g • (k • ω) = g • ω`.
* `D` is exactly the pointwise stabiliser of the pair `{∞, t • ∞}` (`hDmem`), and an element
  that permutes a set acts on its pointwise stabiliser by conjugation.  Hence `g ∈ N_G(D)`.

Nothing here uses finiteness.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Submission.Blueprint
open Work.ZassenhausTwoGroup.IsTIQ

namespace Work.ZassenhausSuzuki

lemma centralizer_le_normalizer_twoPoint {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hZ : Submission.Blueprint.IsZassenhaus H)
    {k : G} (hk : k ∈ Submission.Blueprint.twoPoint H t) (hk1 : k ≠ 1) :
    Subgroup.centralizer ({k} : Set G) ≤
      Subgroup.normalizer (Submission.Blueprint.twoPoint H t : Set G) := by
  obtain ⟨hkH, hkt⟩ := (mem_twoPoint_iff_smul H t k).mp hk
  have hkbase : k • basePt H = basePt H := smul_basePt_of_mem H hkH
  -- the fixed points of `k` are exactly `∞ = H` and `t • ∞`
  have hfix : ∀ ω : G ⧸ H, k • ω = ω → ω = basePt H ∨ ω = (t : G ⧸ H) := by
    intro ω hω
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hω1, hω2⟩ := hcon
    have hne_t : (t : G ⧸ H) ≠ basePt H := (basePt_ne_iff H t).mpr h.not_mem
    exact hk1 (hZ (basePt H) (t : G ⧸ H) ω hne_t.symm
      (fun hc => hω1 hc.symm) (fun hc => hω2 hc.symm) k hkbase hkt hω)
  -- membership in `D = twoPoint H t` is "fixes both `∞` and `t • ∞`"
  have hDmem : ∀ x : G, x ∈ Submission.Blueprint.twoPoint H t ↔
      x • basePt H = basePt H ∧ x • (t : G ⧸ H) = (t : G ⧸ H) := by
    intro x
    constructor
    · intro hx
      obtain ⟨hxH, hxt⟩ := (mem_twoPoint_iff_smul H t x).mp hx
      exact ⟨(smul_basePt_eq_iff H x).mpr hxH, hxt⟩
    · rintro ⟨hxb, hxt⟩
      exact (mem_twoPoint_iff_smul H t x).mpr ⟨(smul_basePt_eq_iff H x).mp hxb, hxt⟩
  -- any element commuting with `k` conjugates `D` into itself
  have hconj : ∀ y : G, y * k = k * y →
      ∀ x : G, x ∈ Submission.Blueprint.twoPoint H t →
        y * x * y⁻¹ ∈ Submission.Blueprint.twoPoint H t := by
    intro y hy x hx
    obtain ⟨hxb, hxt⟩ := (hDmem x).mp hx
    -- `y` permutes `{∞, t • ∞}` ...
    have hmap : ∀ ω : G ⧸ H, (ω = basePt H ∨ ω = (t : G ⧸ H)) →
        (y • ω = basePt H ∨ y • ω = (t : G ⧸ H)) := by
      intro ω hω
      refine hfix (y • ω) ?_
      have hωk : k • ω = ω := by
        rcases hω with hh | hh
        · rw [hh]; exact hkbase
        · rw [hh]; exact hkt
      calc k • (y • ω) = (k * y) • ω := (mul_smul k y ω).symm
        _ = (y * k) • ω := by rw [hy]
        _ = y • (k • ω) := mul_smul y k ω
        _ = y • ω := by rw [hωk]
    have hyinv_k : y⁻¹ * k = k * y⁻¹ := by
      have hh := congrArg (fun z => y⁻¹ * z * y⁻¹) hy
      rw [show y⁻¹ * (y * k) * y⁻¹ = k * y⁻¹ from by group,
          show y⁻¹ * (k * y) * y⁻¹ = y⁻¹ * k from by group] at hh
      exact hh.symm
    -- ... and so does `y⁻¹`
    have hmapinv : ∀ ω : G ⧸ H, (ω = basePt H ∨ ω = (t : G ⧸ H)) →
        (y⁻¹ • ω = basePt H ∨ y⁻¹ • ω = (t : G ⧸ H)) := by
      intro ω hω
      refine hfix (y⁻¹ • ω) ?_
      have hωk : k • ω = ω := by
        rcases hω with hh | hh
        · rw [hh]; exact hkbase
        · rw [hh]; exact hkt
      calc k • (y⁻¹ • ω) = (k * y⁻¹) • ω := (mul_smul k y⁻¹ ω).symm
        _ = (y⁻¹ * k) • ω := by rw [hyinv_k]
        _ = y⁻¹ • (k • ω) := mul_smul y⁻¹ k ω
        _ = y⁻¹ • ω := by rw [hωk]
    rw [hDmem]
    constructor
    · calc (y * x * y⁻¹) • basePt H
          = y • (x • (y⁻¹ • basePt H)) := by rw [mul_smul, mul_smul]
        _ = y • (y⁻¹ • basePt H) := by
              rcases hmapinv (basePt H) (Or.inl rfl) with hh | hh
              · rw [hh, hxb]
              · rw [hh, hxt]
        _ = basePt H := smul_inv_smul y (basePt H)
    · calc (y * x * y⁻¹) • (t : G ⧸ H)
          = y • (x • (y⁻¹ • (t : G ⧸ H))) := by rw [mul_smul, mul_smul]
        _ = y • (y⁻¹ • (t : G ⧸ H)) := by
              rcases hmapinv (t : G ⧸ H) (Or.inr rfl) with hh | hh
              · rw [hh, hxb]
              · rw [hh, hxt]
        _ = (t : G ⧸ H) := smul_inv_smul y (t : G ⧸ H)
  intro g hg
  have hgk : g * k = k * g := Subgroup.mem_centralizer_singleton_iff.mp hg
  have hginv_k : g⁻¹ * k = k * g⁻¹ := by
    have hh := congrArg (fun z => g⁻¹ * z * g⁻¹) hgk
    rw [show g⁻¹ * (g * k) * g⁻¹ = k * g⁻¹ from by group,
        show g⁻¹ * (k * g) * g⁻¹ = g⁻¹ * k from by group] at hh
    exact hh.symm
  refine Subgroup.mem_set_normalizer_iff.mpr (fun x => ⟨?_, ?_⟩)
  · exact hconj g hgk x
  · intro hx
    have hh := hconj g⁻¹ hginv_k (g * x * g⁻¹) hx
    simp only [inv_inv] at hh
    rwa [show g⁻¹ * (g * x * g⁻¹) * g = x from by group] at hh

end Work.ZassenhausSuzuki
