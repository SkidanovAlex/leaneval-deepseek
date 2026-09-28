import Mathlib
import Submission.Work.HP.ArchDefs
import Submission.Work.HP.tau_basic
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.volume_rNorm_ball

/-!
# Lattice tools (`Work.HP.lattice_tools`)

Five elementary facts used throughout the paper's Archimedean/lattice bookkeeping.

* the set of integer vectors of Euclidean norm `≤ A` is finite (discreteness of the
  coefficient lattice `ℤ^{N_{d,n}}`);
* the Euclidean unit ball `{w : rNorm w ≤ 1}` has nonzero, finite Lebesgue measure, and
  every ball of radius `r ≥ 0` has measure `r^{N_{d,n}}` times that of the unit ball;
* the closed half-balls around lattice points are `1`-separated, so a finite union of them
  inside `Y` has measure at most `volume Y`.

All measure-theoretic statements are for Lebesgue (= Haar) measure on the finite-dimensional real
vector space `Mon d n → ℝ`; the Euclidean norm `Work.HP.rNorm` is not Lean's default (sup) norm,
so the identification with `EuclideanSpace ℝ (Mon d n)` (through `WithLp.toLp 2`, a measure
preserving equivalence) is made explicit.
-/

set_option autoImplicit false

noncomputable section

namespace Work.HP

open MeasureTheory MvPolynomial
open scoped ENNReal

variable {ι : Type*} [Fintype ι]

/-! ## Elementary facts about `toR`, `eNorm`, `rNorm` -/

omit [Fintype ι] in
private lemma toR_sub (a b : ι → ℤ) : toR (a - b) = toR a - toR b := by
  ext i; simp [toR]

omit [Fintype ι] in
lemma toR_injective : Function.Injective (toR : (ι → ℤ) → (ι → ℝ)) := by
  intro a b h
  funext i
  exact Int.cast_injective (show (a i : ℝ) = (b i : ℝ) from congrFun h i)

lemma rNorm_toR_lt (a : ι → ℤ) : rNorm (toR a) = eNorm a := by
  simp only [rNorm, eNorm, toR]

private lemma one_le_eNorm {a : ι → ℤ} (ha : a ≠ 0) : 1 ≤ eNorm a := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  have hz : a i ≠ 0 := by simpa using hi
  have h1 : (1 : ℤ) ≤ |a i| := Int.one_le_abs hz
  have h2 : (1 : ℝ) ≤ |(a i : ℝ)| := by exact_mod_cast h1
  have h3 := MDBasic.abs_apply_le_eNorm a i
  linarith

/-! ## Lebesgue measure and the Euclidean structure of `ι → ℝ` -/

/-- `WithLp.toLp 2` is a measure preserving equivalence from `ι → ℝ` (with the product
Lebesgue measure) to the Euclidean space `EuclideanSpace ℝ ι`. -/
lemma volume_preimage_toLp (S : Set (EuclideanSpace ℝ ι)) (hS : MeasurableSet S) :
    volume (WithLp.toLp 2 ⁻¹' S) = volume S :=
  (PiLp.volume_preserving_toLp ι).measure_preimage hS.nullMeasurableSet

/-- The `rNorm` open ball is the `WithLp.toLp 2`-preimage of an open ball in `EuclideanSpace`. -/
lemma ball_eq_preimage (x : ι → ℝ) (r : ℝ) :
    {w : ι → ℝ | rNorm (w - x) < r}
      = WithLp.toLp 2 ⁻¹' (Metric.ball (WithLp.toLp 2 x : EuclideanSpace ℝ ι) r) := by
  ext w
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Metric.mem_ball, dist_eq_norm,
    show (WithLp.toLp 2 w : EuclideanSpace ℝ ι) - WithLp.toLp 2 x = WithLp.toLp 2 (w - x) from by
      ext i; simp]
  rw [rNorm_eq_normE]

/-- The `rNorm` closed ball at the origin is the `WithLp.toLp 2`-preimage of a closed ball. -/
lemma closedBall_zero_eq_preimage (r : ℝ) :
    {w : ι → ℝ | rNorm w ≤ r}
      = WithLp.toLp 2 ⁻¹' (Metric.closedBall (0 : EuclideanSpace ℝ ι) r) := by
  ext w
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm, sub_zero,
    rNorm_eq_normE]

end Work.HP

namespace Work.HP

open MeasureTheory MvPolynomial
open scoped ENNReal

theorem lattice_tools (d n : ℕ) (hn : 3 ≤ n) :
    (∀ A : ℝ, {v : Mon d n → ℤ | eNorm v ≤ A}.Finite) ∧
    (volume {w : Mon d n → ℝ | rNorm w ≤ 1} ≠ 0) ∧
    (volume {w : Mon d n → ℝ | rNorm w ≤ 1} ≠ ⊤) ∧
    (∀ (r : ℝ) (x : Mon d n → ℝ), 0 ≤ r →
        volume {w : Mon d n → ℝ | rNorm (w - x) ≤ r}
          = ENNReal.ofReal (r ^ NN d n) * volume {w : Mon d n → ℝ | rNorm w ≤ 1}) ∧
    (∀ (s : Set (Mon d n → ℤ)) (Y : Set (Mon d n → ℝ)), s.Finite →
        (∀ a ∈ s, {w : Mon d n → ℝ | rNorm (w - toR a) ≤ (1 / 2 : ℝ)} ⊆ Y) →
        (s.ncard : ENNReal) * volume {w : Mon d n → ℝ | rNorm w ≤ (1 / 2 : ℝ)} ≤ volume Y) := by
  have hne : Nonempty (Mon d n) :=
    ⟨⟨fun i => if i = 0 then (⟨d, Nat.lt_succ_self d⟩ : Fin (d + 1)) else 0, by
      rw [Finset.sum_eq_single (0 : Fin (n + 1))]
      · simp
      · intro b _ hb; simp [hb]
      · intro h; exact absurd (Finset.mem_univ _) h⟩⟩
  haveI := hne
  -- The measure of the Euclidean unit ball, in closed form.
  have hvol1 : volume {w : Mon d n → ℝ | rNorm w ≤ 1}
      = ENNReal.ofReal (√Real.pi ^ NN d n / Real.Gamma ((NN d n : ℝ) / 2 + 1)) := by
    rw [closedBall_zero_eq_preimage (ι := Mon d n) 1]
    rw [volume_preimage_toLp _ measurableSet_closedBall, EuclideanSpace.volume_closedBall]
    simp [NN]
  have hpos : 0 < √Real.pi ^ NN d n / Real.Gamma ((NN d n : ℝ) / 2 + 1) :=
    div_pos (pow_pos (Real.sqrt_pos.mpr Real.pi_pos) _)
      (Real.Gamma_pos_of_pos (by positivity))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro A
    exact MDBasic.finite_eNorm_le A
  · rw [hvol1]
    exact ENNReal.ofReal_ne_zero_iff.mpr hpos
  · rw [hvol1]
    exact ENNReal.ofReal_ne_top
  · intro r x hr
    exact volume_rNorm_ball x r hr
  · intro s Y hsfin hsub
    -- enumerate `s`
    set t := hsfin.toFinset with ht
    have hcoe : (↑t : Set (Mon d n → ℤ)) = s := hsfin.coe_toFinset
    have hcard : s.ncard = t.card := Set.ncard_eq_toFinset_card s hsfin
    -- the open half-balls around the lattice points
    set Bo : (Mon d n → ℤ) → Set (Mon d n → ℝ) := fun a => {w | rNorm (w - toR a) < 1 / 2}
      with hBo
    -- they are pairwise disjoint, because lattice points are `1`-separated
    have hdisj : Set.PairwiseDisjoint (↑t) Bo := by
      intro a ha b hb hab
      change Disjoint (Bo a) (Bo b)
      rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
      rintro w ⟨hwa, hwb⟩
      change rNorm (w - toR a) < 1 / 2 at hwa
      change rNorm (w - toR b) < 1 / 2 at hwb
      have h1 : (1 : ℝ) ≤ eNorm (a - b) := one_le_eNorm (sub_ne_zero.mpr hab)
      have h2 : rNorm (toR a - toR b) ≤ rNorm (w - toR a) + rNorm (w - toR b) := by
        have heq : toR a - toR b = (toR a - w) + (w - toR b) := by abel
        calc rNorm (toR a - toR b) = rNorm ((toR a - w) + (w - toR b)) := by rw [heq]
          _ ≤ rNorm (toR a - w) + rNorm (w - toR b) := rNorm_add_le _ _
          _ = rNorm (w - toR a) + rNorm (w - toR b) := by rw [rNorm_sub_comm (toR a) w]
      rw [← rNorm_toR_lt (a - b), toR_sub] at h1
      linarith
    -- each half-ball is measurable
    have hmeas : ∀ b ∈ t, MeasurableSet (Bo b) := by
      intro b _
      change MeasurableSet {w : Mon d n → ℝ | rNorm (w - toR b) < 1 / 2}
      rw [ball_eq_preimage]
      exact measurableSet_ball.preimage (PiLp.volume_preserving_toLp (Mon d n)).measurable
    -- all half-balls have the same measure, that of the closed half-ball at the origin
    have hvol_eq : ∀ b : Mon d n → ℤ,
        volume (Bo b) = volume {w : Mon d n → ℝ | rNorm w ≤ (1 / 2 : ℝ)} := by
      intro b
      change volume {w : Mon d n → ℝ | rNorm (w - toR b) < 1 / 2}
        = volume {w : Mon d n → ℝ | rNorm w ≤ (1 / 2 : ℝ)}
      have e1 : volume {w : Mon d n → ℝ | rNorm (w - toR b) < 1 / 2}
          = volume (Metric.ball (WithLp.toLp 2 (toR b) : EuclideanSpace ℝ (Mon d n))
              (1 / 2)) := by
        rw [ball_eq_preimage]
        exact volume_preimage_toLp _ measurableSet_ball
      have e2 : volume {w : Mon d n → ℝ | rNorm w ≤ (1 / 2 : ℝ)}
          = volume (Metric.closedBall (0 : EuclideanSpace ℝ (Mon d n)) (1 / 2)) := by
        rw [closedBall_zero_eq_preimage (ι := Mon d n) (1 / 2)]
        exact volume_preimage_toLp _ measurableSet_closedBall
      rw [e1, e2, Measure.addHaar_ball_center, Measure.addHaar_closedBall_eq_addHaar_ball]
    have hsum := measure_biUnion_finset (μ := volume) hdisj hmeas
    have hunion : (⋃ b ∈ t, Bo b) ⊆ Y := by
      intro w hw
      simp only [Set.mem_iUnion] at hw
      obtain ⟨b, hb, hwb⟩ := hw
      refine hsub b (hcoe ▸ hb) ?_
      change rNorm (w - toR b) ≤ 1 / 2
      exact le_of_lt hwb
    calc (s.ncard : ENNReal) * volume {w : Mon d n → ℝ | rNorm w ≤ (1 / 2 : ℝ)}
        = (t.card : ENNReal) * volume {w : Mon d n → ℝ | rNorm w ≤ (1 / 2 : ℝ)} := by
          rw [hcard]
      _ = ∑ b ∈ t, volume (Bo b) := by
          rw [Finset.sum_congr rfl (fun b _ => hvol_eq b), Finset.sum_const, nsmul_eq_mul]
      _ = volume (⋃ b ∈ t, Bo b) := hsum.symm
      _ ≤ volume Y := measure_mono hunion

end Work.HP
