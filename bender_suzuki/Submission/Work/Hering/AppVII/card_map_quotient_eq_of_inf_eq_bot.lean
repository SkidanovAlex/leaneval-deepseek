import Mathlib
import Submission.Work.Hering.AppVII.Setup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

universe u

namespace Work.Hering.AppVII

/-- If `P ⊓ C = ⊥` then the canonical map `A → A ⧸ C` is injective on `P`, hence its
image `P.map (QuotientGroup.mk' C)` has the same cardinality as `P`. -/
theorem card_map_quotient_eq_of_inf_eq_bot {A : Type u} [Group A] (C P : Subgroup A) [C.Normal]
    (h : P ⊓ C = ⊥) : Nat.card ↥(P.map (QuotientGroup.mk' C)) = Nat.card ↥P := by
  -- The restriction of the quotient map to `P`.
  let f : ↥P →* A ⧸ C := (QuotientGroup.mk' C).comp P.subtype
  -- Its kernel is `P ⊓ C`, which is trivial by hypothesis.
  have hker : f.ker = ⊥ := by
    ext x
    rw [Subgroup.mem_bot, MonoidHom.mem_ker]
    constructor
    · intro hx
      have hxC : (x : A) ∈ C := by
        have h1 : (x : A) ∈ (QuotientGroup.mk' C).ker := by
          rw [MonoidHom.mem_ker]
          exact hx
        rwa [QuotientGroup.ker_mk'] at h1
      have hxPC : (x : A) ∈ P ⊓ C := ⟨x.2, hxC⟩
      rw [h] at hxPC
      exact Subtype.ext (by simpa using hxPC)
    · intro hx
      rw [hx]
      rfl
  have hf : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hker
  -- The image of `P` under the quotient map is the image of `⊤` under `f`.
  have hmap : (⊤ : Subgroup ↥P).map f = P.map (QuotientGroup.mk' C) := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_top, true_and]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨(x : A), x.2, hx⟩
    · rintro ⟨a, ha, hx⟩
      exact ⟨⟨a, ha⟩, hx⟩
  calc Nat.card ↥(P.map (QuotientGroup.mk' C))
      = Nat.card ↥((⊤ : Subgroup ↥P).map f) := by rw [hmap]
    _ = Nat.card ↥(⊤ : Subgroup ↥P) := Subgroup.card_map_of_injective hf
    _ = Nat.card ↥P := Subgroup.card_top

end Work.Hering.AppVII
