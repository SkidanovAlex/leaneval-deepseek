import Mathlib
import Submission.NK.Indecomposed.Defs
import Submission.NK.HasseTwist.subsingleton_of_surjective_prod

universe u

namespace NK.Indecomposed

/-- **The two-index rank count.**  If `S` has cardinality a prime `p`, `T i` and `T j` have
cardinality at least `p`, and there is a surjection `S → ∀ k, T k`, then `i = j`: otherwise the
composite `S → T i × T j` is surjective, so `p * p ≤ p`.

This is `NK.HasseTwist.subsingleton_of_surjective_prod` with the cardinality hypothesis imposed
only at the two indices being compared, which is the form in which it applies when the cardinality
hypothesis can only be checked on the *non-trivial* local groups. -/
theorem eq_of_surjective_of_card_le {ι : Type*} {T : ι → Type*} {S : Type*}
    (p : ℕ) (hp : p.Prime) (hS : Nat.card S = p) (i j : ι)
    (hi : p ≤ Nat.card (T i)) (hj : p ≤ Nat.card (T j))
    (f : S → ∀ k, T k) (hf : Function.Surjective f) : i = j := by
  classical
  have hSpos : 0 < Nat.card S := by rw [hS]; exact hp.pos
  obtain ⟨hNe, hFin⟩ := Nat.card_pos_iff.mp hSpos
  have hFinS : Finite S := hFin
  by_contra hij
  obtain ⟨s0⟩ := hNe
  have hsurj : Function.Surjective (fun s : S => (f s i, f s j)) := by
    rintro ⟨a, b⟩
    obtain ⟨s₁, hs₁⟩ := hf (Function.update (f s0) i a)
    have h1 : f s₁ i = a := by rw [hs₁, Function.update_self]
    obtain ⟨s₂, hs₂⟩ := hf (Function.update (f s₁) j b)
    have h2 : f s₂ j = b := by rw [hs₂, Function.update_self]
    have h3 : f s₂ i = f s₁ i := by rw [hs₂, Function.update_of_ne hij]
    exact ⟨s₂, by change (f s₂ i, f s₂ j) = (a, b); rw [h3, h1, h2]⟩
  have hcard : Nat.card (T i × T j) ≤ Nat.card S :=
    Nat.card_le_card_of_surjective _ hsurj
  rw [hS, Nat.card_prod] at hcard
  have hle : p * p ≤ p := (Nat.mul_le_mul hi hj).trans hcard
  have hp1 : p ≤ 1 :=
    Nat.le_of_mul_le_mul_left (a := p) (b := 1) (c := p) (by simpa using hle) hp.pos
  have hp2 : 2 ≤ p := hp.two_le
  omega

/-- **The rank count in the "non-trivial local groups" form.**

If the localisation to the local groups over `𝔭` is surjective, the source `H²(H, μ_p)` has exactly
`p` elements, and every *non-trivial* local group `V` over `𝔭` has `|H²(V, μ_p)| ≥ p`, then there is
at most one non-trivial local group of `H` over `𝔭`: any two distinct non-trivial local groups
`V ≠ W` would make the localisation surject onto `H²(V, μ_p) × H²(W, μ_p)`, of cardinality
`≥ p * p > p`, which is impossible from the `p`-element source.

This is Neukirch's rank count of `Submission/Work/HasseTwist/Localisation.lean` with the cardinality
hypothesis weakened to the non-trivial local groups — the only place it is available (and the only
place it is true): the local group `⊥` occurs exactly when the prime is decomposed, and
`H2Twist p ⊥` is a point (`NK.Indecomposed.subsingleton_h2Twist_bot`), so the hypothesis is false
there. -/
theorem subsingleton_of_ne_bot_of_surjective {K K' : Type u} [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] (p : ℕ) (hp : p.Prime)
    (H : Subgroup Gal(K'/K))
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hcard : Nat.card (NK.BrauerTwist.H2Twist (K := K) (K' := K') p H) = p)
    (hloc : ∀ V, V ∈ NK.HasseTwist.localGroupSubgroupsOver (K := K) (K' := K') H 𝔭 →
      V ≠ ⊥ → p ≤ Nat.card (NK.BrauerTwist.H2Twist (K := K) (K' := K') p V))
    (hsurj : Function.Surjective (NK.HasseTwist.localisationTo (K := K) (K' := K') p H 𝔭)) :
    ∀ V W, V ∈ NK.HasseTwist.localGroupSubgroupsOver (K := K) (K' := K') H 𝔭 →
      W ∈ NK.HasseTwist.localGroupSubgroupsOver (K := K) (K' := K') H 𝔭 →
      V ≠ ⊥ → W ≠ ⊥ → V = W := by
  intro V W hV hW hVne hWne
  have h := eq_of_surjective_of_card_le
    (T := fun A : ↥(NK.HasseTwist.localGroupSubgroupsOver (K := K) (K' := K') H 𝔭) =>
      NK.BrauerTwist.H2Twist (K := K) (K' := K') p A.1)
    p hp hcard ⟨V, hV⟩ ⟨W, hW⟩ (hloc V hV hVne) (hloc W hW hWne)
    (NK.HasseTwist.localisationTo (K := K) (K' := K') p H 𝔭) hsurj
  exact congrArg Subtype.val h

end NK.Indecomposed
