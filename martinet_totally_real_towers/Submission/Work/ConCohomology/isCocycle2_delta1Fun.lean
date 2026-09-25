/-
Copyright: the martinet_totally_real_towers team.

# The connecting `1 → 2` cochain of a short exact sequence of coefficient modules

For a short exact sequence `0 → A → B → C → 0` of `G`-modules and a `1`-cocycle `c : G → C`, the
raw connecting cochain `S.delta1Fun c` (built from an arbitrary set-theoretic section of the
projection `g`) is a `2`-cocycle.  This is the algebraic heart of the connecting homomorphism
`H¹(G,C) → H²(G,A)`: injectivity of `f` is what makes the construction independent of the choice
of section.

The proof is the standard diagram chase: writing `s y` for the chosen lift of `y ∈ C` and
`D(σ,τ) = f (S.delta1Fun c (σ,τ)) = σ • s(c τ) - s(c (σ*τ)) + s(c σ)`, the cocycle condition for
`c` (in the form `c (σ*τ) = c σ + σ • c τ`) shows first that every `D(σ,τ)` lies in the image of
`f` -- equivalently, applying `g` to `D(σ,τ)` gives `0` -- and then the alternating sum
`σ • D(τ,ρ) - D(σ*τ,ρ) + D(σ,τ*ρ) - D(σ,τ)` telescopes to `0`.  Since `f` is injective, this
proves `IsCocycle2 (S.delta1Fun c)`.
-/

import Mathlib
import Submission.Work.ConCohomology.Setup

namespace Work.ConCohomology

open Function

variable {G : Type*} [Group G] {A B C : Type*} [AddCommGroup A]
variable [AddCommGroup B] [AddCommGroup C]
variable [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]

/-- For an element `b` of `B` lying in the image of `f`, the chosen set-theoretic inverse
`S.invFun` really is a preimage of `b` under `f`. -/
lemma invFun_f_eq_delta1Fun_aux (S : CoeffSES G A B C) {b : B} (hb : ∃ a : A, S.f a = b) :
    S.f (S.invFun b) = b := by
  have h : S.invFun b = Classical.choose hb := by
    rw [CoeffSES.invFun_eq]
    exact dite_eq_left hb
  rw [h]
  exact Classical.choose_spec hb

/-- The connecting `1 → 2` cochain attached to a `1`-cocycle `c : G → C` is a `2`-cocycle. -/
lemma isCocycle2_delta1Fun {G : Type*} [Group G] {A B C : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [DistribMulAction G A] [DistribMulAction G B]
    [DistribMulAction G C] (S : CoeffSES G A B C) (c : G → C) (hc : IsCocycle1 c) :
    IsCocycle2 (S.delta1Fun c) := by
  intro σ τ ρ
  -- The `B`-valued expression whose `invFun` defines `S.delta1Fun c` lies in the image of `f`,
  -- because its image under `g` is the value of `d¹c`.
  have mem_image : ∀ σ τ : G,
      ∃ a : A, S.f a = σ • S.sect (c τ) - S.sect (c (σ * τ)) + S.sect (c σ) := by
    intro σ τ
    have h0 : S.g (σ • S.sect (c τ) - S.sect (c (σ * τ)) + S.sect (c σ)) = 0 := by
      simp only [EqHom.map_add, EqHom.map_sub, EqHom.map_smul, CoeffSES.g_sect]
      rw [hc σ τ]
      abel
    exact (S.exact _).mp h0
  -- Hence `f` inverts `invFun` on that expression.
  have key : ∀ σ τ : G, S.f (S.delta1Fun c (σ, τ)) =
      σ • S.sect (c τ) - S.sect (c (σ * τ)) + S.sect (c σ) := by
    intro σ τ
    rw [CoeffSES.delta1Fun_apply]
    exact invFun_f_eq_delta1Fun_aux S (mem_image σ τ)
  -- It remains to check that the alternating sum of the `f`-images telescopes to zero.
  apply S.injective_f
  simp only [EqHom.map_add, EqHom.map_sub, EqHom.map_smul, EqHom.map_zero, key,
    smul_add, smul_sub, mul_smul, mul_assoc]
  abel

end Work.ConCohomology
