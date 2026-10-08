import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement

set_option linter.style.haveILetI false

/-- **Orbit counting for a `p`-group acting by conjugation.**

Let `P ≤ G` be a finite `p`-group (`hP`) and let `S ⊆ G` be a set containing `1` (`h1`)
and closed under conjugation by `P` (`hinv`).  If the only point of `S` fixed by all of `P`
(i.e. the only `s ∈ S` with `x * s * x⁻¹ = s` for every `x ∈ P`) is `1` (`hfix`), then
`p ∤ |S|`.

Proof.  `P` acts on the finite set `S` by `x • s = x * s * x⁻¹`.  Mathlib's
`IsPGroup.card_modEq_card_fixedPoints` says that the number of fixed points of a
`p`-group action is congruent mod `p` to the total cardinality.  The fixed points of this
action on `S` are exactly those `s` with `x * s * x⁻¹ = s` for all `x ∈ P`; by `hfix` this
is precisely `{1}`, so there is a unique fixed point.  Hence `|S| ≡ 1 [MOD p]`, and in
particular `p` cannot divide `|S|`. -/
theorem orbit_conj_unique_fixed {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {P : Subgroup G} (hP : IsPGroup p ↥P) {S : Set G} (h1 : (1 : G) ∈ S)
    (hinv : ∀ x ∈ P, ∀ s ∈ S, x * s * x⁻¹ ∈ S)
    (hfix : ∀ s ∈ S, (∀ x ∈ P, x * s * x⁻¹ = s) → s = 1) :
    ¬ p ∣ S.ncard := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- The conjugation action of `P` on the set `S`.
  letI instS : SMul ↥P ↥S := ⟨fun g s => ⟨g.1 * s.1 * g.1⁻¹, hinv g.1 g.2 s.1 s.2⟩⟩
  have hsmul : ∀ (g : ↥P) (s : ↥S), (g • s : ↥S).1 = g.1 * s.1 * g.1⁻¹ := fun g s => rfl
  letI : MulAction ↥P ↥S :=
  { toSMul := instS
    one_smul := by intro s; apply Subtype.ext; rw [hsmul]; simp
    mul_smul := by intro g h s; apply Subtype.ext; rw [hsmul, hsmul, hsmul]; push_cast; group }
  -- The fixed points of the action are exactly `{1}`.
  have hset : MulAction.fixedPoints ↥P ↥S = {⟨1, h1⟩} := by
    ext s
    rw [Set.mem_singleton_iff, MulAction.mem_fixedPoints]
    constructor
    · intro hs
      apply Subtype.ext
      apply hfix s.1 s.2
      intro x hx
      have h2 := hs ⟨x, hx⟩
      rw [Subtype.ext_iff] at h2
      rw [hsmul] at h2
      exact h2
    · intro hs g
      rw [hs]
      apply Subtype.ext
      rw [hsmul]; simp
  have hcard : Nat.card (MulAction.fixedPoints ↥P ↥S) = 1 := by
    rw [hset]; simp
  -- Congruence `|S| ≡ 1 [MOD p]`.
  have hmod : Nat.card ↥S ≡ 1 [MOD p] := by
    have := hP.card_modEq_card_fixedPoints ↥S
    rwa [hcard] at this
  intro hdvd
  have h0 : Nat.card ↥S ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr hdvd
  have h10 : (1 : ℕ) ≡ 0 [MOD p] := hmod.symm.trans h0
  exact hp.not_dvd_one (Nat.modEq_zero_iff_dvd.mp h10)

end Work.NormalComplement
