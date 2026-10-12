import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Submission.Work.BoseB4.Kafz_lower_bound
import Submission.Work.BoseB4.hW_H2nd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.Kafz_lower_bound_H2nd` — FS `thm:Kafz` as a lower bound for `eq:HLambdaSecond`

`Work.BoseB4.Kafz_H2nd` gives FS's `c`-number substitution for the box Hamiltonian
`Work.BoseB4.H2nd` (`eq:HLambdaSecond`) in the packaged form

  `⟪Ψ, 𝓗^{2nd}_Λ Ψ⟫ = ∫_ℂ ⟪Φ(split Ψ)(z), 𝓚(z) (Φ(split Ψ)(z))⟫ dν(z)`,
  `𝓚(z) = Work.BoseB4.K2ndSym D z`.

Feeding that into the abstract `c`-number lower bound `Work.BoseB4.Kafz_lower_bound`
(i.e. bounding the integrand pointwise by `c‖Φ(split Ψ)(z)‖²` and using the
Bargmann isometry `∫ ‖Φ Ψ z‖² dν(z) = ‖Ψ‖²`) yields the bound FS §9–§11 use:

    `c ‖Ψ‖² ≤ ⟪Ψ, 𝓗^{2nd}_Λ Ψ⟫`

whenever the anti-Wick symbol satisfies `c‖v‖² ≤ Re⟪v, 𝓚(z) v⟫` for all `z`, `v`.

## Route

* `Work.BoseB4.Split_inner` identifies the Bombieri form on the mode lattice with
  the ℓ² inner product of `FockCore (cfock (Excited m))`: `bomb m Ψ Ψ' = coreInner (split Ψ) (split Ψ')`;
* `Work.BoseB4.hW_H2nd` identifies `split ∘ H2nd D` with `K2ndC D ∘ split`;
* both expectations are therefore the ℓ² expectations of the abstract carrier, and
  `Kafz_lower_bound` (with `s = univ`, `p = Kpvec`, `q = Kqvec`, `B = Kvec D`)
  bounds the second by `c` times the first.
-/

noncomputable section

open scoped lp BigOperators

namespace Work.BoseB4

variable {m : ℕ} [NeZero m]

/-- `K2ndC` in the *application* form consumed by `Kafz_lower_bound`
(`K2ndC_eq_sum` plus `LinearMap.sum_apply`). -/
lemma K2ndC_apply_sum (D : H2ndData m) (Ψ : FockCore (cfock (Excited m))) :
    (K2ndC D) Ψ = ∑ i ∈ (Finset.univ : Finset (Fin 9)),
      monoOp (Kpvec i) (Kqvec i) (Kvec D i) Ψ := by
  rw [K2ndC_eq_sum, LinearMap.sum_apply]

/-- The Bombieri form of a mode-lattice state against itself is the squared norm
of its image under the condensate splitting. -/
lemma bomb_self_eq_norm_split (Ψ : RealFock m) :
    bomb m Ψ Ψ = ‖Embed (cfock (Excited m)) (split Ψ)‖ ^ 2 := by
  have h1 : (coreInner (split Ψ) (split Ψ)).re = bomb m Ψ Ψ := by
    rw [Split_inner]
    simp
  rw [← h1]
  simp only [coreInner]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) (Embed (cfock (Excited m)) (split Ψ))

/-- The Fock expectation of `eq:HLambdaSecond` is the real part of the ℓ²
expectation of its `c`-number substitute `K2ndC D` on the abstract carrier. -/
lemma bomb_H2nd_eq (D : H2ndData m) (Ψ : RealFock m) :
    bomb m Ψ (H2nd D Ψ) =
      (inner ℂ (Embed (cfock (Excited m)) (split Ψ))
        (Embed (cfock (Excited m)) ((K2ndC D) (split Ψ)))).re := by
  have h1 : coreInner (split Ψ) ((K2ndC D) (split Ψ))
      = ((bomb m Ψ (H2nd D Ψ) : ℝ) : ℂ) := by
    rw [← hW_H2nd D Ψ]
    exact Split_inner Ψ (H2nd D Ψ)
  have h2 : (coreInner (split Ψ) ((K2ndC D) (split Ψ))).re = bomb m Ψ (H2nd D Ψ) := by
    rw [h1]
    simp
  rw [← h2]
  simp only [coreInner]

theorem Kafz_lower_bound_H2nd {m : ℕ} [NeZero m] (D : Work.BoseB4.H2ndData m) (c : ℝ)
    (h : ∀ (z : ℂ) (v : Work.BoseB4.cfock (Work.BoseB4.Excited m)),
      c * ‖v‖ ^ 2 ≤ (inner ℂ v (Work.BoseB4.K2ndSym D z v)).re)
    (Ψ : Work.BoseB4.RealFock m) :
    c * Work.BoseB4.bomb m Ψ Ψ ≤ Work.BoseB4.bomb m Ψ (Work.BoseB4.H2nd D Ψ) := by
  have hmain := Kafz_lower_bound (E := cfock (Excited m)) (ι := Fin 9)
    (s := Finset.univ) (p := Kpvec) (q := Kqvec) (B := Kvec D) (c := c)
    (fun z v => by simpa only [K2ndSym] using h z v) (split Ψ)
  have hmain' : c * ‖Embed (cfock (Excited m)) (split Ψ)‖ ^ 2 ≤
      (inner ℂ (Embed (cfock (Excited m)) (split Ψ))
        (Embed (cfock (Excited m)) ((K2ndC D) (split Ψ)))).re := by
    simpa only [← K2ndC_apply_sum] using hmain
  rw [bomb_self_eq_norm_split, bomb_H2nd_eq]
  exact hmain'

end Work.BoseB4
