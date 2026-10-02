import Mathlib
import Submission.Work.LANDCL.Defs
import Submission.Work.LandLeaves.Defs
import Submission.Work.LandLeaves.rayAccum_entry
import Submission.Work.LandLeaves.exists_local_repelling_branch
import Submission.Work.LandLeaves.isClosed_typeAngles
import Submission.Work.LandLeaves.finite_of_closedInCircle_invariant_injective
import Submission.Work.LandLeaves.exists_preimage_rayAccum
import Submission.Work.LandLeaves.eq_mod_one_of_rayAccum_of_angDouble_eq
import Submission.Work.LandLeaves.periodicAngle_of_finite_landingAngles

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# A ray landing at a repelling periodic point has a periodic angle

`Work.LandLeaves.periodicAngle_landsAt_repelling`: if `y` is a repelling periodic point of the
tricorn map `T_c` (odd period `k`) and the dynamic ray `R_c(θ)` lands at `y`, then some positive
multiple `2 * (k * q)` of `2 * k` is a period of the angle `Int.fract θ` under angle doubling.

## Structure of the proof

Everything is assembled here from the (proved) pieces of the area:

* **Finiteness of the type.**  The *type* of `y` is `T = {ψ | rayAccum c φ ψ = {y}}`; its
  normalised part `K = T ∩ Ico 0 1` is finite.  This is the classical input (Douady–Hubbard;
  Goldberg–Milnor II, Lemma 2.2) and is proved below from the pieces
  * `Work.LandLeaves.isClosed_typeAngles` (`T` is closed), so that
    `K ∪ {1} = (T ∪ {1}) ∩ Icc 0 1` is closed,
  * `σ := angDouble^[2k] = fun θ => Int.fract (4^k * θ)` maps `K` bijectively onto itself:
    invariance is `Work.LandLeaves.rayAccum_angDouble_of_isRepelling`, surjectivity is
    `Work.LandLeaves.exists_preimage_rayAccum`, injectivity (mod `1`, hence on `K`) is
    `Work.LandLeaves.eq_mod_one_of_rayAccum_of_angDouble_eq`,
  * `Work.LandLeaves.finite_of_closedInCircle_invariant_injective`: a set closed *in the circle*
    on which the `d`-tupling map (`d = 4^k ≥ 4`) is an injective self-map is finite.
* **Reduction to periodicity.**  `Work.LandLeaves.periodicAngle_of_finite_landingAngles`: the
  finite `σ`-invariant set `K` gives a return `σ^q (fract θ) = fract θ`, i.e.
  `PeriodicAngle (fract θ) (2 * k * q)`.
-/

namespace Work.LandLeaves

open Classical

/-- **Finiteness of the type of a repelling periodic point** (Goldberg–Milnor II, Lemma 2.2):
for a Böttcher coordinate `φ` of `T_c` and a repelling periodic point `y`, only finitely many
normalised angles `ψ ∈ [0,1)` have `rayAccum c φ ψ = {y}`.

The route is the *closedness* route of the area (`NOTES_FALSE_orderPreserving_finiteness.md`):
order preservation alone is not sufficient (Sturmian counterexamples), but closedness plus
invariance plus injectivity of the angle-doubling map is. -/
theorem finite_type_of_isRepelling {c : ℂ} {φ : ℂ → ℂ} {k : ℕ} {y : ℂ}
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hrep : Work.Landing.IsRepelling c k y) :
    ({ψ : ℝ | Work.Landing.rayAccum c φ ψ = {y}} ∩ Set.Ico 0 1).Finite := by
  set T : Set ℝ := {ψ : ℝ | Work.Landing.rayAccum c φ ψ = {y}} with hT
  set K : Set ℝ := T ∩ Set.Ico 0 1 with hK
  have hk : 0 < k := hrep.1.1
  have hTclosed : IsClosed T := by
    rw [hT]
    exact isClosed_typeAngles hφ hrep
  have hKclosed : IsClosed (K ∪ {1}) := by
    have hEq : K ∪ {1} = (T ∪ {1}) ∩ Set.Icc 0 1 := by
      ext x
      constructor
      · rintro (hx | hx)
        · exact ⟨Or.inl hx.1, ⟨hx.2.1, le_of_lt hx.2.2⟩⟩
        · rw [Set.mem_singleton_iff] at hx
          subst hx
          exact ⟨Or.inr rfl, by norm_num⟩
      · rintro ⟨hx | hx, hI⟩
        · rcases eq_or_lt_of_le hI.2 with h | h
          · exact Or.inr (Set.mem_singleton_iff.mpr h)
          · exact Or.inl ⟨hx, ⟨hI.1, h⟩⟩
        · rw [Set.mem_singleton_iff] at hx
          subst hx
          exact Or.inr rfl
    rw [hEq]
    exact (hTclosed.union isClosed_singleton).inter isClosed_Icc
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · rw [hKe]
    exact Set.finite_empty
  have hd : 2 ≤ 4 ^ k := by
    calc 2 ≤ 4 ^ 1 := by norm_num
      _ ≤ 4 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hmemT : ∀ ψ : ℝ, ψ ∈ T ↔ Work.Landing.rayAccum c φ ψ = {y} := by
    intro ψ; rw [hT]; exact Iff.rfl
  -- the angle map, in the form in which it appears in the goal of the finiteness lemma
  have hAng : ∀ θ : ℝ, Int.fract ((4 : ℝ) ^ k * θ) = (Work.Landing.angDouble)^[2 * k] θ :=
    fun θ => (angDouble_iterate_two_mul hk θ).symm
  refine finite_of_closedInCircle_invariant_injective (d := 4 ^ k) hd hKne ?_ hKclosed ?_ ?_ ?_
  · rintro x ⟨-, hxI⟩
    exact ⟨hxI.1, hxI.2⟩
  · -- invariance of the type under the second-return angle map
    rintro x ⟨hxT, hxI⟩
    refine ⟨?_, ?_⟩
    · rw [hmemT]
      push_cast
      rw [hAng x]
      rw [hmemT] at hxT
      exact rayAccum_angDouble_of_isRepelling hφ hrep hxT
    · push_cast
      exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  · -- surjectivity: every angle of the type has a preimage angle of the type
    rintro z ⟨hzT, hzI⟩
    obtain ⟨θ', hθ'T, m, hm⟩ := exists_preimage_rayAccum hφ hrep ((hmemT z).mp hzT)
    refine ⟨Int.fract θ', ⟨?_, ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩⟩, ?_⟩
    · rw [hmemT]
      rw [rayAccum_fract]
      exact hθ'T
    · have key : Int.fract ((4 : ℝ) ^ k * θ') = z := by
        rw [hm, Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨hzI.1, hzI.2⟩]
      have h1 : Int.fract ((4 : ℝ) ^ k * Int.fract θ') = Int.fract ((4 : ℝ) ^ k * θ') := by
        have hx : θ' = Int.fract θ' + ((⌊θ'⌋ : ℤ) : ℝ) := by
          have := Int.self_sub_fract (a := θ'); linarith
        conv_rhs => rw [hx]
        rw [mul_add]
        have hcast : (4 : ℝ) ^ k * ((⌊θ'⌋ : ℤ) : ℝ) = (((4 ^ k : ℤ) * ⌊θ'⌋ : ℤ) : ℝ) := by
          push_cast; ring
        rw [hcast, Int.fract_add_intCast]
      push_cast
      exact h1.trans key
  · -- injectivity on the type (modulo `1`, hence on `[0,1)`)
    rintro x ⟨hxT, hxI⟩ y' ⟨hyT, hyI⟩ hxy
    have hxT' : Work.Landing.rayAccum c φ x = {y} := (hmemT x).mp hxT
    have hyT' : Work.Landing.rayAccum c φ y' = {y} := (hmemT y').mp hyT
    push_cast at hxy
    have hmod : ∃ m : ℤ, (4 : ℝ) ^ k * x = (4 : ℝ) ^ k * y' + ↑m := by
      obtain ⟨m, hm⟩ := Int.fract_eq_fract.mp hxy
      exact ⟨m, by linarith [hm]⟩
    obtain ⟨mm, hmm⟩ := eq_mod_one_of_rayAccum_of_angDouble_eq hφ hrep hxT' hyT' hmod
    have hmm0 : mm = 0 := by
      have hlt : ((mm : ℤ) : ℝ) < 1 := by linarith [hmm, hxI.2, hyI.1]
      have hgt : (-1 : ℝ) < ((mm : ℤ) : ℝ) := by linarith [hmm, hxI.1, hyI.2]
      have hlt' : mm < 1 := by exact_mod_cast hlt
      have hgt' : -1 < mm := by exact_mod_cast hgt
      omega
    rw [hmm0, Int.cast_zero, add_zero] at hmm
    exact hmm

theorem periodicAngle_landsAt_repelling {c : ℂ} {θ : ℝ} {k : ℕ} {y : ℂ}
    (hrep : Work.Landing.IsRepelling c k y) (hland : Work.Landing.landsAt c θ y) :
    ∃ q : ℕ, 0 < q ∧ Work.Landing.PeriodicAngle (Int.fract θ) (2 * (k * q)) := by
  obtain ⟨φ, hφ, hland'⟩ := hland
  obtain ⟨q, hq, hper⟩ :=
    periodicAngle_of_finite_landingAngles (φ := φ) hφ hrep hland' (finite_type_of_isRepelling hφ hrep)
  exact ⟨q, hq, by rwa [Nat.mul_assoc] at hper⟩

end Work.LandLeaves
