import Mathlib
import Submission.Work.Twist.stdGradingChart

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `chartAwayMap` and `chartAwayMapInv` are inverse to each other

`chartAwayMap 𝕜 n i` and `chartAwayMapInv 𝕜 n i` are both obtained from the *same* graded ring
automorphism `chartRename 𝕜 n i` (the coordinate transposition `X₀ ↔ X_i`) via
`HomogeneousLocalization.map`, the second one with the source and target away-localisations
swapped.  Since the transposition is an involution, `chartRename 𝕜 n i ∘ chartRename 𝕜 n i = id`,
and `HomogeneousLocalization.map` is functorial (`HomogeneousLocalization.map_comp`), the
composites are identities.

The mathematical content is therefore purely formal; the (only) technical difficulty is that
`HomogeneousLocalization.map g h` takes the *proof* `h : P ≤ Q.comap g` as an explicit argument, so
that a rewrite of the graded ring homomorphism `g` changes the type of `h`.  The two auxiliary
lemmas below isolate exactly that proof-irrelevance step.
-/

set_option autoImplicit false

namespace Work.Twist

open MvPolynomial HomogeneousLocalization

noncomputable section

/-- Two applications of `HomogeneousLocalization.map` agree as soon as the graded ring
homomorphisms agree: the `comap_le` proofs live in propositions, so they are irrelevant. -/
lemma twistAwayMap_map_congr {𝕜 : Type} [CommRing 𝕜] (n : ℕ)
    (P Q : Submonoid (MvPolynomial (Fin (n + 1)) 𝕜))
    {f g : stdGrading 𝕜 n →+*ᵍ stdGrading 𝕜 n} (hfg : f = g)
    (h₁ : P ≤ Q.comap f) (h₂ : P ≤ Q.comap g) :
    HomogeneousLocalization.map f h₁ = HomogeneousLocalization.map g h₂ := by
  cases hfg
  exact congrArg (HomogeneousLocalization.map f) (Subsingleton.elim h₁ h₂)

/-- `HomogeneousLocalization.map` along the identity graded ring homomorphism is the identity
ring homomorphism; the `comap_le` proof is irrelevant. -/
lemma twistAwayMap_map_id_of {𝕜 : Type} [CommRing 𝕜] (n : ℕ)
    (P : Submonoid (MvPolynomial (Fin (n + 1)) 𝕜))
    (h : P ≤ P.comap (GradedRingHom.id (stdGrading 𝕜 n))) :
    HomogeneousLocalization.map (GradedRingHom.id (stdGrading 𝕜 n)) (P := P) (Q := P) h =
      RingHom.id (HomogeneousLocalization (stdGrading 𝕜 n) P) := by
  have : h = le_rfl := Subsingleton.elim _ _
  rw [this]
  simp [HomogeneousLocalization.map_id]

theorem chartAwayMap_comp_chartAwayMapInv (𝕜 : Type) [CommRing 𝕜] (n : ℕ)
    (i : Fin (n + 1)) :
    (Work.Twist.chartAwayMap 𝕜 n i).comp (Work.Twist.chartAwayMapInv 𝕜 n i) =
      RingHom.id (HomogeneousLocalization.Away (Work.Twist.stdGrading 𝕜 n)
        (MvPolynomial.X (0 : Fin (n + 1)))) := by
  -- Unfold the two definitions: both are `HomogeneousLocalization.map` along `chartRename`.
  rw [show Work.Twist.chartAwayMap 𝕜 n i = HomogeneousLocalization.map (chartRename 𝕜 n i)
        (P := Submonoid.powers (MvPolynomial.X i))
        (Q := Submonoid.powers (MvPolynomial.X (0 : Fin (n+1)))) _ from rfl,
      show Work.Twist.chartAwayMapInv 𝕜 n i = HomogeneousLocalization.map (chartRename 𝕜 n i)
        (P := Submonoid.powers (MvPolynomial.X (0 : Fin (n+1))))
        (Q := Submonoid.powers (MvPolynomial.X i)) _ from rfl]
  -- Functoriality of `HomogeneousLocalization.map`.
  rw [← HomogeneousLocalization.map_comp (f := chartRename 𝕜 n i) (g := chartRename 𝕜 n i)]
  -- `chartRename` is an involution, so the composite graded ring hom is the identity.
  exact (twistAwayMap_map_congr n _ _ (chartRename_comp_self 𝕜 n i) _ le_rfl).trans
    (twistAwayMap_map_id_of n _ le_rfl)

end

end Work.Twist
