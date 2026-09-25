import Mathlib
import Submission.Work.BourgainPlan.Maximal.dyCZ
import Submission.Work.BourgainPlan.Maximal.dyadicMaximal

/-!
# The sharp weak `(1,1)` bound for the dyadic maximal function

We prove

`lam * volume {x | ofReal lam < dyMax φ x} ≤ ∫⁻ x in {x | ofReal lam < dyMax φ x}, φ x`

for every `φ` with `∫⁻ φ < ∞` and every `lam > 0`.

This is the *sharp* (constant `1`) weak-type inequality for the dyadic maximal function — the form
in which the maximal estimate is consumed in Calderón–Zygmund / transference arguments (a "rising
sun"-type inequality), as opposed to the usual `(2/lam) ‖φ‖₁` bound.

The proof is the elementary Calderón–Zygmund decomposition: the level set is the disjoint union of
the maximal dyadic cells of `czMax φ (ofReal lam)`, and each such cell has `φ`-average `> lam`,
hence carries `φ`-mass at least `lam` times its volume.

The only non-trivial input from the library is `levelSet_eq_iUnion_czMax` (from `dyCZ`), exhibiting
the level set as the union of the maximal cells, together with `czMax_disjoint` (disjointness) and
`czMax_mem_czCells` (the average of a maximal cell exceeds the level).
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Work.BourgainPlan.Maximal

/-- If `a` is a nonzero, finite extended nonnegative real and `c < a⁻¹ * I`, then `c * a < I`. -/
lemma mul_inv_mul_lt {a c I : ENNReal} (h0 : a ≠ 0) (hinf : a ≠ ⊤) (h : c < a⁻¹ * I) :
    c * a < I := by
  have h1 : c * a < (a⁻¹ * I) * a := ENNReal.mul_lt_mul_left h0 hinf h
  have h2 : (a⁻¹ * I) * a = I := by
    rw [mul_comm (a⁻¹ * I) a, ← mul_assoc, ENNReal.mul_inv_cancel h0 hinf, one_mul]
  exact h2 ▸ h1

/-- **Sharp weak `(1,1)` bound for the dyadic maximal function.**
For `φ` with finite integral and `lam > 0`,
`lam · |{dyMax φ > lam}| ≤ ∫_{dyMax φ > lam} φ`. -/
theorem dyMaxSharpCZ {φ : ℝ → ENNReal} (hint : ∫⁻ x, φ x < ⊤) {lam : ℝ} (hlam : 0 < lam) : ENNReal.ofReal lam * MeasureTheory.volume {x : ℝ | ENNReal.ofReal lam < Work.BourgainPlan.Maximal.dyMax φ x} ≤ ∫⁻ x in {x : ℝ | ENNReal.ofReal lam < Work.BourgainPlan.Maximal.dyMax φ x}, φ x := by
  set c : ENNReal := ENNReal.ofReal lam with hcdef
  have hcpos : 0 < c := ENNReal.ofReal_pos.mpr hlam
  -- Each maximal cell carries `φ`-mass at least `c` times its volume.
  have hmain : ∀ p : {q : ℤ × ℤ // q ∈ czMax φ c},
      c * volume (dyCell p.1.1 p.1.2) ≤ ∫⁻ y in dyCell p.1.1 p.1.2, φ y := by
    intro p
    have hvolcell : volume (dyCell p.1.1 p.1.2) = ENNReal.ofReal ((2 : ℝ) ^ (p.1.1)) := by
      rw [dyCell, Real.volume_Ico, dyCell_len]
    have ha0 : ENNReal.ofReal ((2 : ℝ) ^ (p.1.1)) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (zpow_two_pos _)).ne'
    have haT : ENNReal.ofReal ((2 : ℝ) ^ (p.1.1)) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hmem : c < (ENNReal.ofReal ((2 : ℝ) ^ (p.1.1)))⁻¹
        * ∫⁻ y in dyCell p.1.1 p.1.2, φ y := by
      simpa only [czCells, Set.mem_ofPred_eq, ofReal_zpow_inv] using czMax_mem_czCells p.2
    have hstep := mul_inv_mul_lt ha0 haT hmem
    rw [hvolcell]
    exact hstep.le
  -- The maximal cells are pairwise disjoint and measurable.
  have hdisj : Pairwise (Function.onFun Disjoint
      fun p : {q : ℤ × ℤ // q ∈ czMax φ c} => dyCell p.1.1 p.1.2) := by
    intro p q hpq
    exact czMax_disjoint p.2 q.2 (fun h => hpq (Subtype.ext h))
  have hmeas : ∀ p : {q : ℤ × ℤ // q ∈ czMax φ c}, MeasurableSet (dyCell p.1.1 p.1.2) :=
    fun p => dyCell_measurable _ _
  -- The level set is exactly the disjoint union of the maximal cells.
  have hEeq : {x : ℝ | c < dyMax φ x}
      = ⋃ p : {q : ℤ × ℤ // q ∈ czMax φ c}, dyCell p.1.1 p.1.2 := by
    rw [levelSet_eq_iUnion_czMax (ψ := φ) hcpos hint]
    exact (Set.iUnion_subtype (p := fun q : ℤ × ℤ => q ∈ czMax φ c)
      (s := fun q => dyCell q.1.1 q.1.2)).symm
  have hvol : volume (⋃ p : {q : ℤ × ℤ // q ∈ czMax φ c}, dyCell p.1.1 p.1.2)
      = ∑' p : {q : ℤ × ℤ // q ∈ czMax φ c}, volume (dyCell p.1.1 p.1.2) :=
    measure_iUnion hdisj hmeas
  have hlint : ∫⁻ y in (⋃ p : {q : ℤ × ℤ // q ∈ czMax φ c}, dyCell p.1.1 p.1.2), φ y
      = ∑' p : {q : ℤ × ℤ // q ∈ czMax φ c}, ∫⁻ y in dyCell p.1.1 p.1.2, φ y :=
    lintegral_iUnion hmeas hdisj φ
  calc c * volume {x : ℝ | c < dyMax φ x}
      = c * volume (⋃ p : {q : ℤ × ℤ // q ∈ czMax φ c}, dyCell p.1.1 p.1.2) := by rw [hEeq]
    _ = c * ∑' p : {q : ℤ × ℤ // q ∈ czMax φ c}, volume (dyCell p.1.1 p.1.2) := by rw [hvol]
    _ = ∑' p : {q : ℤ × ℤ // q ∈ czMax φ c}, c * volume (dyCell p.1.1 p.1.2) :=
        ENNReal.tsum_mul_left.symm
    _ ≤ ∑' p : {q : ℤ × ℤ // q ∈ czMax φ c}, ∫⁻ y in dyCell p.1.1 p.1.2, φ y :=
        ENNReal.tsum_le_tsum hmain
    _ = ∫⁻ y in (⋃ p : {q : ℤ × ℤ // q ∈ czMax φ c}, dyCell p.1.1 p.1.2), φ y := hlint.symm
    _ = ∫⁻ y in {x : ℝ | c < dyMax φ x}, φ y := by rw [hEeq]

end Work.BourgainPlan.Maximal
