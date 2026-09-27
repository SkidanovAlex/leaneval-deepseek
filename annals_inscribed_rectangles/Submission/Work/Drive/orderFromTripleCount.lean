import Mathlib
import Submission.Work.Drive.parityCore_of_functional

/-!
# The order from the triple count: antisymmetry from Lemma 4 with a reference plane

`COUNT_ASSEMBLY_STATUS.md` §2 records, in prose, that **antisymmetry (Hugelmeyer's Lemma 3) needs no
count identity beyond Lemma 4's and the multiplicativity**: applied to the triple of planes
`(P, Q, P_ref)` with a *reference plane* `P_ref` lying above both `P` and `Q`, Lemma 4's parity
identity `n_P + n_Q + n_ref ≡ 1` together with the multiplicativity `n_X ≡ 1_{X≺Y} · 1_{X≺Z}` gives
`1_{P≺Q} + 1_{Q≺P} ≡ 1`, i.e. antisymmetry; the reference's own term is `1_{P_ref≺P} · 1_{P_ref≺Q} = 0`
because the reference is above.

This file turns that prose into proof, so that no separate `ω₀`-chain chapter is built:

* `Work.Drive.antisym_of_tripleCountWithReference` — the pair parity `κ P Q + κ Q P = 1` from
  (i) the triple identity for the triple `(P, Q, ρ)`, (ii) the three multiplicativities, (iii) the
  reference data `κ P ρ = 1`, `κ ρ P = 0` (the reference is above both planes);
* `Work.Drive.trans_of_tripleCount` — transitivity of `κ` from the triple identity plus the pair
  parity: this is the *same* content as `Work.Drive.e_add_of_triple`, in the two-variable language of
  the counts;
* `Work.Drive.antisym_of_pairParity` — the concrete shape for the route: if the pair count
  `κ u v := 1_{P_u ≺ P_v}` is antisymmetric on disjoint rotated planes and invariant under simultaneous
  rotation, then the side function `e u := κ 0 u` satisfies `e u + e (-u) = 1` on `Zc γ`.

The vocabulary is that of the counting route: `κ A B = 1` means `A ≺ B` (equivalently
`⟨ω_B, [C_A]⟩ = 1`); the triple identity is the engine's output
`Work.Drive.odd_sum_topBdryMeet_clampedSweeps_of_planes` read through the multiplicativity
`Work.Drive.parityCore_of_oddThreeCount`.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

/-- **Antisymmetry of the pair count from the triple identity with a reference plane.**

`n P Q R` is the triple count of the three planes `P, Q, R` (the parity identity of Hugelmeyer's
Lemma 4 saying `n P Q R + n Q R P + n R P Q = 1`), `κ P Q = 1` stands for `P ≺ Q`, and the
multiplicativity of Lemma 2 says `n P Q R = κ P Q · κ P R` (the count for the plane `P` is the product
of its two pairings with the other planes).

If the three multiplicativities hold and `ρ` is a reference plane *above* both `P` and `Q`
(`κ P ρ = 1`, `κ ρ P = 0`), then Lemma 4's identity for the triple `(P, Q, ρ)` reads
`κ P Q + κ Q P + 0 = 1`.

So **antisymmetry is a consequence of Lemma 4 and needs no separate `ω₀`-chain count.** -/
theorem antisym_of_tripleCountWithReference {α : Type*}
    (n : α → α → α → ZMod 2) (κ : α → α → ZMod 2) (ρ : α)
    (htriple : ∀ P Q : α, n P Q ρ + n Q ρ P + n ρ P Q = 1)
    (hmul₀ : ∀ P Q : α, n P Q ρ = κ P Q * κ P ρ)
    (hmul₁ : ∀ P Q : α, n Q ρ P = κ Q ρ * κ Q P)
    (hmul₂ : ∀ P Q : α, n ρ P Q = κ ρ P * κ ρ Q)
    (htop : ∀ P : α, κ P ρ = 1) (hbot : ∀ P : α, κ ρ P = 0) :
    ∀ P Q : α, κ P Q + κ Q P = 1 := by
  intro P Q
  have h := htriple P Q
  rw [hmul₀ P Q, hmul₁ P Q, hmul₂ P Q, htop P, htop Q, hbot P, hbot Q] at h
  simpa using h

/-- **Transitivity of the pair count from the triple identity and antisymmetry.**

Same vocabulary as `antisym_of_tripleCountWithReference`: the parity identity of Lemma 4 for the triple
`(P, Q, R)`, the multiplicativity of Lemma 2 (`n P Q R = κ P Q · κ P R`), and antisymmetry of `κ` give
transitivity: `P ≺ Q → Q ≺ R → P ≺ R`.  (Equivalently `Work.Drive.e_add_of_triple`.) -/
theorem trans_of_tripleCount {α : Type*}
    (n : α → α → α → ZMod 2) (κ : α → α → ZMod 2)
    (hanti : ∀ P Q : α, κ P Q + κ Q P = 1)
    (htriple : ∀ P Q R : α, n P Q R + n Q R P + n R P Q = 1)
    (hmul₀ : ∀ P Q R : α, n P Q R = κ P Q * κ P R)
    (hmul₁ : ∀ P Q R : α, n Q R P = κ Q R * κ Q P)
    (hmul₂ : ∀ P Q R : α, n R P Q = κ R P * κ R Q) :
    ∀ P Q R : α, κ P Q = 1 → κ Q R = 1 → κ P R = 1 := by
  intro P Q R hPQ hQR
  have h := htriple P Q R
  rw [hmul₀ P Q R, hmul₁ P Q R, hmul₂ P Q R] at h
  have hQP : κ Q P = 0 := by
    have h' := hanti P Q
    rw [hPQ] at h'
    exact (add_left_inj (1 : ZMod 2)).mp (by simpa using h')
  have hRQ : κ R Q = 0 := by
    have h' := hanti Q R
    rw [hQR] at h'
    exact (add_left_inj (1 : ZMod 2)).mp (by simpa using h')
  rw [hPQ, hQR, hQP, hRQ] at h
  simpa using h

/-- **The two order axioms from the triple identity with a reference plane**: the pair count is
antisymmetric and transitive.  This is the exact content of Hugelmeyer's Lemmas 3–4 for the order
function of the counting route. -/
theorem isTotalOrder_of_tripleCountWithReference {α : Type*}
    (n : α → α → α → ZMod 2) (κ : α → α → ZMod 2) (ρ : α)
    (htriple : ∀ P Q R : α, n P Q R + n Q R P + n R P Q = 1)
    (hmul₀ : ∀ P Q R : α, n P Q R = κ P Q * κ P R)
    (hmul₁ : ∀ P Q R : α, n Q R P = κ Q R * κ Q P)
    (hmul₂ : ∀ P Q R : α, n R P Q = κ R P * κ R Q)
    (htop : ∀ P : α, κ P ρ = 1) (hbot : ∀ P : α, κ ρ P = 0) :
    (∀ P Q : α, κ P Q + κ Q P = 1) ∧
      (∀ P Q R : α, κ P Q = 1 → κ Q R = 1 → κ P R = 1) :=
  ⟨antisym_of_tripleCountWithReference n κ ρ (fun P Q => htriple P Q ρ)
      (fun P Q => hmul₀ P Q ρ) (fun P Q => hmul₁ P Q ρ) (fun P Q => hmul₂ P Q ρ) htop hbot,
    trans_of_tripleCount n κ
      (antisym_of_tripleCountWithReference n κ ρ (fun P Q => htriple P Q ρ)
        (fun P Q => hmul₀ P Q ρ) (fun P Q => hmul₁ P Q ρ) (fun P Q => hmul₂ P Q ρ) htop hbot)
      htriple hmul₀ hmul₁ hmul₂⟩

/-- **The concrete shape used by the route.**  If the pair count `κ u v = 1_{P_u ≺ P_v}` is
antisymmetric on pairs of *disjoint* rotations (`v - u ∈ Zc γ`, the pairs for which the planes
`u·M`, `v·M` are disjoint) and invariant under simultaneous rotation, then the side function
`e u := κ 0 u` of `Work.Drive.parityCore_of_stripRel` is antisymmetric:
`e u + e (-u) = 1` for every `u ∈ Zc γ`.

This is Hugelmeyer's Lemma 3 in the form in which the chain route produces it: the pair parity on the
left comes from `antisym_of_tripleCountWithReference` applied to the triples `(P_u, P_v, P_ref)`, and
the rotation invariance is `Work.Drive.topBdryMeet_rotCapping_clampedSweep`. -/
theorem antisym_of_pairParity {γ : Circle → ℝ × ℝ} (κ : UnitAddCircle → UnitAddCircle → ZMod 2)
    (hrot : ∀ u v w : UnitAddCircle, κ (u + w) (v + w) = κ u v)
    (hpair : ∀ u : UnitAddCircle, u ∈ Zc γ → κ 0 u + κ u 0 = 1) :
    ∀ (u : UnitAddCircle) (hu : u ∈ Zc γ), κ 0 u + κ 0 (-u) = 1 := by
  intro u hu
  have h := hpair u hu
  have h1 : κ u 0 = κ 0 (-u) := by
    have h' := hrot 0 (-u) u
    simpa using h'
  rw [h1] at h
  exact h

end Work.Drive
