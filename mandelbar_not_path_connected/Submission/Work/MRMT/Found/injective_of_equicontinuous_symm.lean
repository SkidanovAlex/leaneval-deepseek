import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Found.norm_symm_sub_le

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

/-!
# Injectivity of a pointwise limit of homeomorphisms with equicontinuous inverses

Let `Fn : ℂ ≃ₜ ℂ` be a sequence of homeomorphisms of the plane, converging pointwise to a
map `φ`, and suppose the inverses `Fn⁻¹` are *equicontinuous* in the following uniform
sense: for every bound `N` and every `ε > 0` there is one `δ ∈ (0, 1/4]` which works for
*all* `n` simultaneously, on pairs `u, v` with `‖v‖ ≤ N`:

  `‖u - v‖ < δ ⟹ ‖Fn⁻¹ u - Fn⁻¹ v‖ < ε`.

Then `φ` is injective.

The proof is the one-line argument used in the multicorn paper: if `φ a = φ b`, both
sequences `Fn n a` and `Fn n b` converge to the common value `φ a = φ b`, so for large `n`
the points `u = Fn n a`, `v = Fn n b` are within `δ` of one another while `v` stays inside
the ball of radius `‖φ b‖ + 1`.  Applying the uniform estimate at those two points gives
`‖a - b‖ = ‖Fn⁻¹ (Fn a) - Fn⁻¹ (Fn b)‖ < ε` for *every* `ε > 0`, hence `a = b`.

Note that this step uses only the pointwise convergence and the (uniform in `n`)
equicontinuity of the inverses; the decay hypothesis `hdec`, the constant bounds `hCd`,
`hRd`, and the homeomorphism structure beyond `Fn⁻¹ ∘ Fn = id` play no role here.
-/

theorem injective_of_equicontinuous_symm {Fn : ℕ → ℂ ≃ₜ ℂ} {φ : ℂ → ℂ} {Cd Rd : ℝ}
    (hCd : 0 ≤ Cd) (hRd : 1 ≤ Rd)
    (hdec : ∀ n : ℕ, ∀ z : ℂ, Rd ≤ ‖z‖ → ‖Fn n z - z‖ ≤ Cd / ‖z‖)
    (hpt : ∀ z : ℂ, Filter.Tendsto (fun n => (Fn n : ℂ → ℂ) z) Filter.atTop (nhds (φ z)))
    (heq : ∀ N : ℝ, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 4 ∧
      ∀ n : ℕ, ∀ u v : ℂ, ‖v‖ ≤ N → ‖u - v‖ < δ →
        ‖((Fn n).symm : ℂ → ℂ) u - ((Fn n).symm : ℂ → ℂ) v‖ < ε) :
    Function.Injective φ := by
  intro a b hab
  by_contra hne
  have hpos : 0 < ‖a - b‖ := by
    rw [norm_pos_iff]
    intro h
    exact hne (sub_eq_zero.mp h)
  -- the uniform equicontinuity datum, at bound `‖φ b‖ + 1` and accuracy `‖a - b‖ / 2`
  obtain ⟨δ, hδpos, _hδle, hδ⟩ := heq (‖φ b‖ + 1) (‖a - b‖ / 2) (by linarith)
  have hδ4 : 0 < δ / 4 := by linarith
  -- the two convergent sequences `Fn n a → φ a` and `Fn n b → φ b = φ a`
  obtain ⟨n1, hn1⟩ := (Metric.tendsto_atTop.mp (hpt a)) (δ / 4) hδ4
  obtain ⟨n2, hn2⟩ := (Metric.tendsto_atTop.mp (hpt b)) (δ / 4) hδ4
  obtain ⟨n4, hn4⟩ := (Metric.tendsto_atTop.mp (hpt b)) 1 (by norm_num)
  set n : ℕ := max (max n1 n2) n4 with hn
  have hn1' : n1 ≤ n := by rw [hn]; exact le_trans (le_max_left n1 n2) (le_max_left _ _)
  have hn2' : n2 ≤ n := by rw [hn]; exact le_trans (le_max_right n1 n2) (le_max_left _ _)
  have hn4' : n4 ≤ n := by rw [hn]; exact le_max_right _ _
  have hda : dist ((Fn n : ℂ → ℂ) a) (φ a) < δ / 4 := hn1 n hn1'
  have hdb : dist ((Fn n : ℂ → ℂ) b) (φ b) < δ / 4 := hn2 n hn2'
  have hdb1 : dist ((Fn n : ℂ → ℂ) b) (φ b) < 1 := hn4 n hn4'
  have hmid : dist (φ a) ((Fn n : ℂ → ℂ) b) = dist (φ b) ((Fn n : ℂ → ℂ) b) := by rw [hab]
  -- for this `n`, the two image points are within `δ` of each other
  have hdist : ‖(Fn n : ℂ → ℂ) a - (Fn n : ℂ → ℂ) b‖ < δ := by
    have htri : dist ((Fn n : ℂ → ℂ) a) ((Fn n : ℂ → ℂ) b) ≤ δ / 4 + δ / 4 :=
      calc dist ((Fn n : ℂ → ℂ) a) ((Fn n : ℂ → ℂ) b)
          ≤ dist ((Fn n : ℂ → ℂ) a) (φ a) + dist (φ a) ((Fn n : ℂ → ℂ) b) :=
            dist_triangle _ _ _
        _ = dist ((Fn n : ℂ → ℂ) a) (φ a) + dist (φ b) ((Fn n : ℂ → ℂ) b) := by rw [hmid]
        _ = dist ((Fn n : ℂ → ℂ) a) (φ a) + dist ((Fn n : ℂ → ℂ) b) (φ b) := by
              rw [dist_comm (φ b) ((Fn n : ℂ → ℂ) b)]
        _ ≤ δ / 4 + δ / 4 := add_le_add hda.le hdb.le
    rw [dist_eq_norm] at htri
    linarith
  -- and `Fn n b` stays in the ball of radius `‖φ b‖ + 1`
  have hNb : ‖(Fn n : ℂ → ℂ) b‖ ≤ ‖φ b‖ + 1 := by
    have h1 : ‖(Fn n : ℂ → ℂ) b - φ b‖ < 1 := by
      rw [← dist_eq_norm]; exact hdb1
    have h2 : ‖(Fn n : ℂ → ℂ) b‖ ≤ ‖(Fn n : ℂ → ℂ) b - φ b‖ + ‖φ b‖ := by
      have hh := norm_add_le ((Fn n : ℂ → ℂ) b - φ b) (φ b)
      rwa [sub_add_cancel] at hh
    linarith
  -- the uniform inverse estimate applied to `u = Fn n a`, `v = Fn n b`
  have hfinal := hδ n ((Fn n : ℂ → ℂ) a) ((Fn n : ℂ → ℂ) b) hNb hdist
  have hs : ‖((Fn n).symm : ℂ → ℂ) ((Fn n : ℂ → ℂ) a)
      - ((Fn n).symm : ℂ → ℂ) ((Fn n : ℂ → ℂ) b)‖ = ‖a - b‖ := by
    simp
  rw [hs] at hfinal
  -- `‖a - b‖ < ‖a - b‖ / 2` is impossible
  linarith

end Work.MRMT.Found
