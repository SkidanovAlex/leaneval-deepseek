import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_weyl_stab_rho_trivial
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_weyl_posRoots_fixes_rho
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_coords_same_sign

/-!
# Weyl descent for `E₈`: a nontrivial Weyl element sends some simple root to the negative cone

Weights `v : Fin 8 → ℤ` are written in the `ω`-basis (`v i = ⟨v, αᵢ∨⟩`), so that the simple
reflection at the node `i` acts by `(sᵢ v) j = v j - v i * A i j`, where `A = CartanMatrix.E₈`,
and the action attached to a word `L` is the `foldl` appearing in the statement.  The Weyl vector
is `ρ = fun _ => 1 = ω₀ + ⋯ + ω₇`, and the simple root `αᵢ` in `ω`-coordinates is the `i`-th row of
the Cartan matrix, `fun k => A i k`.  The `α`-coordinates of a weight `v` are `coords v = A⁻¹ v`,
i.e. `fun j => ∑ k, A⁻¹ j k * v k` (`coords_apply`).

The statement proved here is the **descent** input of the classical "fundamental chamber"
argument:

> if the word `L` of simple reflections does **not** fix the Weyl vector `ρ`, then some simple root
> `αᵢ` is sent into the negative cone: every `α`-coordinate of `w αᵢ` is `≤ 0`.

Equivalently, a nontrivial element of the Weyl group has a *right descent*: some `w αᵢ` is a
negative root.  This is the ingredient that lets one reduce the height `⟪wρ, ρ⟫` (which equals
`620` on `ρ`) and hence, by induction on the height, prove that a dominant weight dominates its
whole Weyl orbit in the cone order.

## Proof

Argue by contradiction.  Write `w = wact L` and let `uᵢ = w αᵢ`.  If no `uᵢ` lies in the negative
cone, then — since `uᵢ ≠ 0` and `qZ uᵢ = qZ αᵢ = 2`, so that the sign lemma
`E8_coords_same_sign` says the `α`-coordinates of `uᵢ` have constant sign — every `uᵢ` lies in the
*positive* cone.  Because `wact L` is `ℤ`-linear and every dominant weight is a non-negative
combination of the simple roots, `w` then preserves the positive cone, and a fortiori maps every
positive root into the positive roots (`qZ` is `W`-invariant and `w` is injective).  That is
exactly the hypothesis of `E8_weyl_posRoots_fixes_rho`, which gives `w ρ = ρ`, contradicting the
hypothesis.
-/

set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

open scoped BigOperators

namespace Commons.LinearAlgebra.Matrix.Cartan

/-- **Weyl descent.**  If a word `L` of simple reflections does not fix the Weyl vector
`ρ = fun _ => 1`, then some simple root is sent into the negative cone: there is `i` with
`(coords (w αᵢ)) j ≤ 0` for all `j`, i.e. all the `α`-coordinates of `w αᵢ` are nonpositive.

The operations are spelled out: `w v` is `L.foldl (fun w i => fun j => w j - w i * A i j) v`,
the simple root `αᵢ` is the row `fun k => A i k`, and the `α`-coordinates are computed with
`A⁻¹ = E8inv`. -/
theorem E8_weyl_descent (L : List (Fin 8))
    (hne : L.foldl (fun w (i : Fin 8) => fun j => w j - w i * CartanMatrix.E₈ i j) (fun _ => (1 : ℤ))
      ≠ fun _ => 1) :
    ∃ i : Fin 8, ∀ j, (∑ k, Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.E8inv j k *
      (L.foldl (fun w (i : Fin 8) => fun j => w j - w i * CartanMatrix.E₈ i j)
        (fun k => CartanMatrix.E₈ i k)) k) ≤ 0 := by
  by_contra hcon
  push_neg at hcon
  -- `hcon` in terms of `wact`/`alpha`/`coords`
  have hcon' : ∀ i : Fin 8, ∃ j, 0 < coords (wact L (alpha i)) j := by
    intro i
    obtain ⟨j, hj⟩ := hcon i
    refine ⟨j, ?_⟩
    -- the simple root `αᵢ` in `ω`-coordinates is the `i`-th row of the Cartan matrix
    have hal : alpha i = fun k => CartanMatrix.E₈ i k := funext fun k => alpha_apply i k
    rw [coords_apply, hal]
    exact hj
  -- The images of the simple roots are again roots of squared length two
  have hq : ∀ i : Fin 8, E8NormTwo.qZ (wact L (alpha i)) = 2 := by
    intro i
    rw [qZ_eq_bil, bil_wact, bil_apply, E8m_diag]
  have hne0 : ∀ i : Fin 8, wact L (alpha i) ≠ 0 := by
    intro i h0
    have h1 : alpha i = 0 := by
      have h2 := wact_reverse L (alpha i)
      rw [h0, wact_zero] at h2
      exact h2.symm
    have h3 : alpha i i = 2 := by rw [alpha_apply, E8m_diag]
    rw [h1] at h3
    exact absurd h3 (by norm_num)
  -- hence all of them lie in the positive cone, by the sign lemma
  have hsign : ∀ i : Fin 8, ∀ j, 0 ≤ coords (wact L (alpha i)) j := by
    intro i
    rcases E8_coords_same_sign (wact L (alpha i)) (hne0 i) (hq i) with h | h
    · exact h
    · exfalso
      obtain ⟨j, hj⟩ := hcon' i
      exact absurd (h j) (not_le.mpr hj)
  -- linearity: `w` preserves the whole positive cone
  have hcone : ∀ v : Fin 8 → ℤ, E8NormTwo.qZ v = 2 → v ≠ 0 → (∀ i, 0 ≤ coords v i) →
      (∀ i, 0 ≤ coords (wact L v) i) := by
    intro v _ _ hvc j
    have hvsum : v = ∑ i, (coords v i) • alpha i := by
      conv_lhs => rw [← mulVec_coords v]
      rw [mulVec_eq_sum]
    have hwv : wact L v = ∑ i, (coords v i) • wact L (alpha i) := by
      conv_lhs => rw [hvsum]
      rw [wact_sum_smul]
    rw [hwv, coords_sum_smul]
    simp only [Finset.sum_apply, Pi.smul_apply]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hvc i) (hsign i j))
  -- a `W`-element preserving the positive roots fixes `ρ`
  have hfix := E8_weyl_posRoots_fixes_rho L (fun v hv hv0 hvc => by
    have hvc' : ∀ i, 0 ≤ coords v i := fun i => by rw [coords_apply]; exact hvc i
    have h := hcone v hv hv0 hvc'
    intro i
    rw [← coords_apply]
    exact h i)
  exact hne hfix

end Commons.LinearAlgebra.Matrix.Cartan
