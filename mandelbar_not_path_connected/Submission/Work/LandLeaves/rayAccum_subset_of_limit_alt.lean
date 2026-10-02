import Mathlib
import Submission.Work.LandLeaves.Defs
import Submission.Work.LandLeaves.TypeGeometry
import Submission.Work.LandLeaves.exists_preimage_rayAccum
import Submission.Work.LandLeaves.eq_mod_one_of_rayAccum_of_angDouble_eq
import Submission.Work.LandLeaves.finite_of_ccBet_periodic_point_v2
import Submission.Work.LandLeaves.ccBet_angDouble_typeSet_fresh
import Submission.Work.LandLeaves.V2Anchor.Anchor
import Submission.Work.LandLeaves.FiniteTypeClosed

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Closedness of the type of a repelling periodic point (the `⊆ {y}` half)

`Work.LandLeaves.rayAccum_subset_of_limit_alt` : if `u n → θ` and *every* ray `R(u n)` has
accumulation set the singleton `{y}` (`y` a repelling periodic point of the tricorn, `φ` a Böttcher
coordinate), then `rayAccum c φ θ ⊆ {y}`.

## Route (the classical Goldberg–Milnor / Douady–Yoccoz route)

Write `typeSet c φ y = {ψ | rayAccum c φ ψ = {y}}` for the *type* of `y` and
`σ = (angDouble)^[2k] = fun t => Int.fract (4^k t)`.

1. **Anchor** (`Work.LandLeaves.V2Anchor.periodicTypeAngle_of_landingRay`): the hypothesis `h` at
   `n = 0` exhibits a ray landing at `y`, so by the Douady–Yoccoz / Milnor Thm 18.2 input there
   are `q > 0` and a *periodic* angle `p = Int.fract t` of `y` with `σ^[q] p = p`.
2. **The type is finite.**  The combinatorial core
   `Work.LandLeaves.finite_of_ccBet_periodic_point_v2` says: a subset `K ⊆ [0,1)` which is
   `σ`-invariant, on which `σ` is injective and onto, and on which `σ` preserves the strict cyclic
   betweenness `ccBet`, is finite as soon as it contains *one* `σ`-periodic point.  Its hypotheses
   are supplied by `rayAccum_angDouble_singleton_alt`, `exists_preimage_rayAccum`,
   `eq_mod_one_of_rayAccum_of_angDouble_eq` and the "no crossing" theorem
   `Work.LandLeaves.ccBet_angDouble_typeSet_fresh`.
   *Note*: order preservation alone does **not** force finiteness — the Sturmian counterexample
   of `NOTES_FALSE_orderPreserving_finiteness.md` — the anchor is essential.
3. **Finiteness ⟹ closedness.**  The type is `1`-periodic (`Work.FSeed.rayAccum_add_int`), so it is
   the finite union of the integral translates of its trace on `[0,1)`, hence closed
   (`Work.LandLeaves.isClosed_of_finite_type_alt`).
4. **Conclusion.**  `u n ∈ typeSet c φ y` and `u n → θ` with the type closed give
   `θ ∈ typeSet c φ y` (`IsClosed.mem_of_tendsto`), i.e. `rayAccum c φ θ = {y}`, whence the
   required inclusion.

The other half (`y ∈ rayAccum c φ θ`) is the separate, elementary lemma
`Work.LandLeaves.rayAccum_mem_of_limit`.
-/

namespace Work.LandLeaves

set_option maxHeartbeats 1000000

open Filter Set
open LeanEval.ComplexAnalysis (Tantibar)

/-- **Transfer of landing along the second return angle map**: if the ray at angle `θ` has
accumulation set the singleton `{y}` and `y` is a repelling periodic point of `T_c` of period `k`,
then the ray at angle `(angDouble)^[2k] θ` also lands at `y` (`τ = (T_c)^{2k}` fixes `y`). -/
theorem rayAccum_angDouble_singleton_alt {c : ℂ} {φ : ℂ → ℂ} {k : ℕ} {y : ℂ} {θ : ℝ}
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hrep : Work.Landing.IsRepelling c k y)
    (h : Work.Landing.rayAccum c φ θ = {y}) :
    Work.Landing.rayAccum c φ ((Work.Landing.angDouble)^[2 * k] θ) = {y} := by
  obtain ⟨hper, -⟩ := hrep
  have h2k : (Tantibar c)^[2 * k] y = y := by
    rw [show 2 * k = k + k from by ring, Function.iterate_add_apply, hper.2, hper.2]
  rw [Work.Landing.rayAccum_iterate hφ θ (2 * k), h, Set.image_singleton, h2k]

/-- **The `⊆ {y}` half of the closedness of the type of a repelling periodic point.**

If `u n → θ` and every ray `R(u n)` has accumulation set the singleton `{y}`, then
`rayAccum c φ θ ⊆ {y}`: the type of `y` is finite (Douady–Yoccoz anchor + Goldberg–Milnor
Lemma 2.2, the order preservation being `ccBet_angDouble_typeSet_fresh`), hence closed, so the
limit `θ` of type-angles — being in the closure — lies in the type, i.e. `rayAccum c φ θ = {y}`. -/
theorem rayAccum_subset_of_limit_alt {c : ℂ} {φ : ℂ → ℂ} {y : ℂ} {k : ℕ} {θ : ℝ} {u : ℕ → ℝ}
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hrep : Work.Landing.IsRepelling c k y)
    (hu : Filter.Tendsto u Filter.atTop (nhds θ))
    (h : ∀ n : ℕ, Work.Landing.rayAccum c φ (u n) = {y}) :
    Work.Landing.rayAccum c φ θ ⊆ {y} := by
  have hk : 0 < k := hrep.1.1
  -- the type of `y`, on the fundamental domain `[0,1)`
  set K : Set ℝ := {ψ : ℝ | Work.Landing.rayAccum c φ ψ = {y}} ∩ Set.Ico 0 1 with hK
  -- (1) the anchor: a periodic ray lands at `y`
  -- the anchor: some *periodic* ray lands at `y` (Douady--Yoccoz accessibility)
  obtain ⟨q, hq, t, htper, htacc⟩ :=
    V2Anchor.periodicTypeAngle_of_landingRay hφ hrep ⟨u 0, h 0⟩
  set p : ℝ := Int.fract t with hp
  have hpK : p ∈ K := by
    have hacc : Work.Landing.rayAccum c φ p = {y} := by
      rw [hp]
      exact (rayAccum_fract_alt c φ t).trans htacc
    exact ⟨hacc, by rw [hp]; exact Int.fract_nonneg t,
      by rw [hp]; exact Int.fract_lt_one t⟩
  have hpper : (fun x : ℝ => Int.fract ((4 : ℝ) ^ k * x))^[q] p = p := by
    have h1 : (Work.Landing.angDouble)^[2 * k * q] (Int.fract t) = Int.fract t := htper
    have h2 : (Work.Landing.angDouble)^[2 * k * q]
        = ((fun x : ℝ => Int.fract ((4 : ℝ) ^ k * x)))^[q] := by
      rw [Function.iterate_mul]
      congr 1
      funext x
      exact angDouble_iterate_two_mul hk x
    rw [h2] at h1
    rw [hp]
    exact h1
  -- (2) the four combinatorial hypotheses on `K`
  have hsub : ∀ x ∈ K, 0 ≤ x ∧ x < 1 := fun x hx => hx.2
  have hmap : ∀ x ∈ K, Int.fract ((4 : ℝ) ^ k * x) ∈ K := by
    intro x hx
    have hx' : Work.Landing.rayAccum c φ x = {y} := hx.1
    have hσ : Work.Landing.rayAccum c φ ((Work.Landing.angDouble)^[2 * k] x) = {y} :=
      rayAccum_angDouble_singleton_alt hφ hrep hx'
    have hfe : (Work.Landing.angDouble)^[2 * k] x = Int.fract ((4 : ℝ) ^ k * x) :=
      angDouble_iterate_two_mul hk x
    refine ⟨?_, Int.fract_nonneg _, Int.fract_lt_one _⟩
    rw [← hfe]
    exact hσ
  have hsurj : ∀ z ∈ K, ∃ x ∈ K, Int.fract ((4 : ℝ) ^ k * x) = z := by
    intro z hz
    have hz' : Work.Landing.rayAccum c φ z = {y} := hz.1
    obtain ⟨θ', hθ'acc, m, hm⟩ := exists_preimage_rayAccum hφ hrep hz'
    refine ⟨Int.fract θ', ?_, ?_⟩
    · refine ⟨?_, Int.fract_nonneg θ', Int.fract_lt_one θ'⟩
      exact (rayAccum_fract_alt c φ θ').trans hθ'acc
    · have hfrac : Int.fract ((4 : ℝ) ^ k * Int.fract θ') = Int.fract ((4 : ℝ) ^ k * θ') := by
        have hsh : (4 : ℝ) ^ k * θ'
            = (4 : ℝ) ^ k * Int.fract θ' + (((4 ^ k : ℕ) * ⌊θ'⌋ : ℤ) : ℝ) := by
          have h : θ' = Int.fract θ' + ((⌊θ'⌋ : ℤ) : ℝ) := by
            have := Int.fract_add_floor θ'
            linarith
          conv_lhs => rw [h]
          push_cast
          ring
        rw [hsh, Int.fract_add_intCast]
      rw [hfrac, hm, Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨hz.2.1, hz.2.2⟩]
  have hinj : ∀ x ∈ K, ∀ z ∈ K, Int.fract ((4 : ℝ) ^ k * x) = Int.fract ((4 : ℝ) ^ k * z) →
      x = z := by
    intro x hx z hz heq
    have hx' : Work.Landing.rayAccum c φ x = {y} := hx.1
    have hz' : Work.Landing.rayAccum c φ z = {y} := hz.1
    obtain ⟨m, hm⟩ := Int.fract_eq_fract.mp heq
    obtain ⟨mm, hmm⟩ := eq_mod_one_of_rayAccum_of_angDouble_eq hφ hrep hx' hz' ⟨m, by
      have := hm; push_cast at this ⊢; linarith⟩
    have hlt : (mm : ℝ) < 1 := by
      linarith [hmm, hx.2.2, hz.2.1]
    have hgt : (-1 : ℝ) < (mm : ℝ) := by
      linarith [hmm, hx.2.1, hz.2.2]
    have hmm0 : mm = 0 := by
      have h1 : mm < 1 := by exact_mod_cast hlt
      have h2 : -1 < mm := by exact_mod_cast hgt
      omega
    rw [hmm0, Int.cast_zero, add_zero] at hmm
    exact hmm
  have hord : ∀ a ∈ K, ∀ b ∈ K, ∀ x ∈ K, Work.LandLeaves.ccBet a b x →
      Work.LandLeaves.ccBet (Int.fract ((4 : ℝ) ^ k * a)) (Int.fract ((4 : ℝ) ^ k * b))
        (Int.fract ((4 : ℝ) ^ k * x)) := by
    intro a ha b hb x hx hab
    have hσ := ccBet_angDouble_typeSet_fresh hφ hrep ha.1 hb.1 hx.1 hab
    rw [angDouble_iterate_two_mul hk a, angDouble_iterate_two_mul hk b,
      angDouble_iterate_two_mul hk x] at hσ
    exact hσ
  -- (3) finiteness of the type
  --    (the hypotheses are restated with the literal spelling `↑(4 ^ k)` expected by
  --    `finite_of_ccBet_periodic_point_v2`; the two spellings agree by `push_cast`)
  have h4 : ((4 ^ k : ℕ) : ℝ) = (4 : ℝ) ^ k := by push_cast; ring
  have hmap' : ∀ x ∈ K, Int.fract (((4 ^ k : ℕ) : ℝ) * x) ∈ K := by
    intro x hx; simpa [h4] using hmap x hx
  have hsurj' : ∀ z ∈ K, ∃ x ∈ K, Int.fract (((4 ^ k : ℕ) : ℝ) * x) = z := by
    intro z hz
    obtain ⟨x, hx, hxz⟩ := hsurj z hz
    exact ⟨x, hx, by simpa [h4] using hxz⟩
  have hinj' : ∀ x ∈ K, ∀ z ∈ K,
      Int.fract (((4 ^ k : ℕ) : ℝ) * x) = Int.fract (((4 ^ k : ℕ) : ℝ) * z) → x = z := by
    intro x hx z hz h
    exact hinj x hx z hz (by simpa [h4] using h)
  have hord' : ∀ a ∈ K, ∀ b ∈ K, ∀ x ∈ K, Work.LandLeaves.ccBet a b x →
      Work.LandLeaves.ccBet (Int.fract (((4 ^ k : ℕ) : ℝ) * a))
        (Int.fract (((4 ^ k : ℕ) : ℝ) * b)) (Int.fract (((4 ^ k : ℕ) : ℝ) * x)) := by
    intro a ha b hb x hx hab
    simpa [h4] using hord a ha b hb x hx hab
  have hpper' : (fun x : ℝ => Int.fract (((4 ^ k : ℕ) : ℝ) * x))^[q] p = p := by
    simpa [h4] using hpper
  have hd4 : 2 ≤ 4 ^ k := by
    calc (2 : ℕ) ≤ 4 := by norm_num
      _ ≤ 4 ^ k := Nat.le_self_pow hk.ne' 4
  have hfin : K.Finite :=
    finite_of_ccBet_periodic_point_v2 (d := 4 ^ k) (K := K) hd4
      hsub hmap' hsurj' hinj' hord' hq hpK hpper'
  have hfin' : ({ψ : ℝ | Work.Landing.rayAccum c φ ψ = {y}} ∩ Set.Ico 0 1).Finite :=
    hK ▸ hfin
  -- (4) the type is closed, so the limit angle lies in it
  have hcl : IsClosed {ψ : ℝ | Work.Landing.rayAccum c φ ψ = {y}} :=
    isClosed_of_finite_type_alt hfin'
  have hθ : θ ∈ {ψ : ℝ | Work.Landing.rayAccum c φ ψ = {y}} :=
    hcl.mem_of_tendsto hu (Filter.Eventually.of_forall h)
  have hθ' : Work.Landing.rayAccum c φ θ = {y} := hθ
  rw [hθ']

end Work.LandLeaves
