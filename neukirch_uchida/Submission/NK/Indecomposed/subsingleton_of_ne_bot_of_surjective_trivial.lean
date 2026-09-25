import Mathlib
import Submission.NK.Indecomposed.Defs
import Submission.NK.HasseTwist.subsingleton_of_surjective_prod

universe u

namespace NK.Indecomposed

/-- **Pairwise form of `NK.HasseTwist.subsingleton_of_surjective_prod`.**

If `S` has cardinality a prime `p` and there is a surjection `S → ∀ i, T i`, then two indices
`i j` at which the target factors have cardinality at least `p` must coincide.  The proof is
literally the proof of `NK.HasseTwist.subsingleton_of_surjective_prod` restricted to the single
pair `(i, j)`: the composite `S → T i × T j` is surjective, so `p * p ≤ Nat.card (T i × T j) ≤
Nat.card S = p`, which is impossible.

This refinement is what allows the cardinality hypothesis `p ≤ Nat.card (T i)` to be imposed only
at the *non-trivial* local groups — the trivial local group `⊥` is a factor of the target whose
`H²(⊥, Z/p)` is a point. -/
theorem eq_of_surjective_prod_of_le_card {ι : Type*} {T : ι → Type*} {S : Type*}
    (p : ℕ) (hp : p.Prime) (hS : Nat.card S = p) {i j : ι}
    (hTi : p ≤ Nat.card (T i)) (hTj : p ≤ Nat.card (T j))
    (f : S → ∀ i, T i) (hf : Function.Surjective f) : i = j := by
  classical
  by_contra hij
  have hSpos : 0 < Nat.card S := by rw [hS]; exact hp.pos
  obtain ⟨hNe, hFin⟩ := Nat.card_pos_iff.mp hSpos
  obtain ⟨s0⟩ := hNe
  -- the composite `S → T i × T j` is surjective
  have hsurj : Function.Surjective (fun s : S => (f s i, f s j)) := by
    rintro ⟨a, b⟩
    obtain ⟨s₁, hs₁⟩ := hf (Function.update (f s0) i a)
    have h1 : f s₁ i = a := by rw [hs₁, Function.update_self]
    obtain ⟨s₂, hs₂⟩ := hf (Function.update (f s₁) j b)
    have h2 : f s₂ j = b := by rw [hs₂, Function.update_self]
    have h3 : f s₂ i = f s₁ i := by rw [hs₂, Function.update_of_ne hij]
    exact ⟨s₂, by change (f s₂ i, f s₂ j) = (a, b); rw [h3, h1, h2]⟩
  have hcard : Nat.card (T i × T j) ≤ Nat.card S :=
    Nat.card_le_card_of_surjective (fun s : S => (f s i, f s j)) hsurj
  rw [hS, Nat.card_prod] at hcard
  have hle : p * p ≤ p := (Nat.mul_le_mul hTi hTj).trans hcard
  have hp1 : p ≤ 1 :=
    Nat.le_of_mul_le_mul_left (a := p) (b := 1) (c := p) (by simpa using hle) hp.pos
  have hp2 : 2 ≤ p := hp.two_le
  omega

theorem subsingleton_of_ne_bot_of_surjective_trivial {K K' : Type u} [Field K] [NumberField K]
    [Field K'] [Algebra K K'] [IsSepClosure K K'] (p : ℕ) (hp : p.Prime)
    (H : Subgroup Gal(K'/K))
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hcard : Nat.card (NK.BrauerHasse.H2Profinite (K := K) (K' := K') p H) = p)
    (hloc : ∀ V, V ∈ NK.HasseTwist.localGroupSubgroupsOver (K := K) (K' := K') H 𝔭 →
      V ≠ ⊥ → p ≤ Nat.card (NK.BrauerHasse.H2Profinite (K := K) (K' := K') p V))
    (hsurj : Function.Surjective (NK.Indecomposed.localisationToTrivial (K := K) (K' := K') p H 𝔭)) :
    ∀ V W, V ∈ NK.HasseTwist.localGroupSubgroupsOver (K := K) (K' := K') H 𝔭 →
      W ∈ NK.HasseTwist.localGroupSubgroupsOver (K := K) (K' := K') H 𝔭 →
      V ≠ ⊥ → W ≠ ⊥ → V = W := by
  intro V W hV hW hVne hWne
  have h := eq_of_surjective_prod_of_le_card
    (S := NK.BrauerHasse.H2Profinite (K := K) (K' := K') p H)
    (T := fun i : ↥(NK.HasseTwist.localGroupSubgroupsOver (K := K) (K' := K') H 𝔭) =>
      NK.BrauerHasse.H2Profinite (K := K) (K' := K') p i.1)
    (i := ⟨V, hV⟩) (j := ⟨W, hW⟩)
    p hp hcard (hloc V hV hVne) (hloc W hW hWne)
    (NK.Indecomposed.localisationToTrivial (K := K) (K' := K') p H 𝔭) hsurj
  exact Subtype.ext_iff.mp h

end NK.Indecomposed
