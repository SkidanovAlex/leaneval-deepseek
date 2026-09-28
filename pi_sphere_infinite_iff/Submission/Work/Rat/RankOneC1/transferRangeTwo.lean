import Mathlib
import Submission.Work.RatHurewicz.coverRangeTransfer
import Submission.Work.Serre.Defs

/-!
# The finite-covering transfer above degree `1`

`Work.RatHurewicz.coverRangeTransfer` proves that if `p : E → X` is an `m`-sheeted covering
(`0 < m`) and `H_t(E;ℚ) = 0` for `0 < t ≤ M` then `H_t(X;ℚ) = 0` for `0 < t ≤ M`.

Here we need the variant in which the vanishing of `E` is only assumed from degree `2` on.  The
transfer argument of `Work.Serre.FiniteCover` is **degree-wise**: the chain-map identity
`τ ≫ p_# = m • id` furnishes, after applying `H_t`, the identity `(m : ℚ) • id = 0` on `H_t(X;ℚ)`
in each single degree `t`, and `m ≠ 0` in `ℚ`.  Hence the same proof applies verbatim with the
range starting at `2`.
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.Rat.RankOneC1

theorem transferRangeTwo {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    (p : C(E, X)) (hp : IsCoveringMap ⇑p) [PathConnectedSpace X]
    (m : ℕ) (hm : 0 < m) (hcard : ∀ x : X, Nat.card ↥(⇑p ⁻¹' {x}) = m) (M : ℕ)
    (hE : ∀ t : ℕ, 2 ≤ t → t ≤ M →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of E) t)) :
    ∀ t : ℕ, 2 ≤ t → t ≤ M →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of X) t) := by
  intro t ht htM
  let D : Work.Serre.FiniteCover.CoverData E X := ⟨p, hp, m, hm, hcard⟩
  have hhom := congrArg (fun (f : Work.Serre.ratChains (TopCat.of X) ⟶
      Work.Serre.ratChains (TopCat.of X)) => HomologicalComplex.homologyMap f t)
    (Work.Serre.FiniteCover.transferChain_comp_chainMap D)
  rw [HomologicalComplex.homologyMap_comp] at hhom
  rw [Work.Serre.FiniteCover.homologyMap_smul_id] at hhom
  have hpz : HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℚ (TopCat.of E) (TopCat.of X) (TopCat.ofHom D.p)) t = 0 :=
    IsZero.eq_zero_of_src (hE t ht htM) _
  rw [hpz, comp_zero] at hhom
  have hmm : (D.m : ℚ) • 𝟙 (Work.Serre.ratH (TopCat.of X) t) = 0 := hhom.symm
  have hid : 𝟙 (Work.Serre.ratH (TopCat.of X) t) = 0 := by
    have hmq : (D.m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp D.hm)
    calc 𝟙 (Work.Serre.ratH (TopCat.of X) t)
        = (D.m : ℚ)⁻¹ • ((D.m : ℚ) • 𝟙 (Work.Serre.ratH (TopCat.of X) t)) := by
          rw [smul_smul, inv_mul_cancel₀ hmq, one_smul]
      _ = 0 := by rw [hmm, smul_zero]
  exact (IsZero.iff_id_eq_zero _).mpr hid

end Work.Rat.RankOneC1
