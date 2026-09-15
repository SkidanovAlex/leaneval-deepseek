import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.Int.Star
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Separation.CompletelyRegular

namespace Commons.Analysis.Measure

open MeasureTheory Metric Set ENNReal
open Classical

/-- Superadditivity of the Lebesgue integral (for arbitrary, possibly non-measurable
functions) over a finite family: `∑ᵢ ∫ fᵢ ≤ ∫ ∑ᵢ fᵢ`. -/
lemma lintegral_finsetSum_le {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {ι : Type*} (s : Finset ι) (g : ι → α → ENNReal) :
    ∑ i ∈ s, ∫⁻ a, g i a ∂μ ≤ ∫⁻ a, ∑ i ∈ s, g i a ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
      rw [Finset.sum_insert has]
      calc ∫⁻ x, g a x ∂μ + ∑ i ∈ s, ∫⁻ x, g i x ∂μ
          ≤ ∫⁻ x, g a x ∂μ + ∫⁻ x, ∑ i ∈ s, g i x ∂μ := by gcongr
        _ ≤ ∫⁻ x, g a x + ∑ i ∈ s, g i x ∂μ := le_lintegral_add _ _
        _ = ∫⁻ x, ∑ i ∈ insert a s, g i x ∂μ := by
              apply lintegral_congr
              intro x
              rw [Finset.sum_insert has]

/-- A `Finset` of integers whose elements are pairwise at distance at most `L` (in `ℝ`) has at
most `⌊L⌋ + 1` elements. -/
lemma finset_int_card_le_floor_add_one {A : Finset ℤ} {L : ℝ} (hL : 0 ≤ L)
    (h : ∀ m ∈ A, ∀ m' ∈ A, |((m : ℝ) - (m' : ℝ))| ≤ L) :
    A.card ≤ ⌊L⌋.toNat + 1 := by
  rcases A.eq_empty_or_nonempty with hE | hne
  · rw [hE]; simp
  · have ha : A.min' hne ∈ A := A.min'_mem hne
    have hL0 : (0 : ℤ) ≤ ⌊L⌋ := Int.floor_nonneg.mpr hL
    have hsub : A ⊆ Finset.Icc (A.min' hne) (A.min' hne + ⌊L⌋) := by
      intro m hm
      rw [Finset.mem_Icc]
      refine ⟨A.min'_le m hm, ?_⟩
      have h1 : ((m : ℝ) - ((A.min' hne : ℤ) : ℝ)) ≤ L :=
        (abs_le.mp (h m hm (A.min' hne) ha)).2
      have h2 : ((m - A.min' hne : ℤ) : ℝ) ≤ L := by push_cast; linarith
      have h3 : m - A.min' hne ≤ ⌊L⌋ := Int.le_floor.mpr h2
      linarith
    calc A.card ≤ (Finset.Icc (A.min' hne) (A.min' hne + ⌊L⌋)).card := Finset.card_le_card hsub
      _ = (⌊L⌋ + 1).toNat := by
            rw [Int.card_Icc]
            congr 1
            ring
      _ = ⌊L⌋.toNat + 1 := Int.toNat_add_nat hL0 1

/-- **Multiplicity bound.** For each `z`, the number of indices `n ∈ s` whose ball of radius `r`
around `p n` contains `z` is at most `(⌊θ + r⌋ + 1)^d`, when the real parts of the centres are
within `θ` of the lattice points `2n + γ + 1`. -/
lemma filter_card_closedBall_le {d : ℕ} {r θ : ℝ} (hr0 : 0 ≤ r) (hθ : 0 ≤ θ)
    (γ : Fin d → ℝ) (s : Finset (Fin d → ℤ)) (p : (Fin d → ℤ) → (Fin d → ℂ))
    (hre : ∀ n ∈ s, ∀ i : Fin d, |(p n i).re - (2 * (n i : ℝ) + γ i + 1)| ≤ θ)
    (z : Fin d → ℂ) :
    (s.filter (fun n => z ∈ Metric.closedBall (p n) r)).card ≤ (⌊θ + r⌋.toNat + 1) ^ d := by
  classical
  set A : Finset (Fin d → ℤ) := s.filter (fun n => z ∈ Metric.closedBall (p n) r) with hA
  have hz : ∀ n ∈ A, ∀ i : Fin d, |(z i).re - (2 * (n i : ℝ) + γ i + 1)| ≤ θ + r := by
    intro n hn i
    rw [hA, Finset.mem_filter] at hn
    obtain ⟨hns, hnb⟩ := hn
    rw [Metric.mem_closedBall] at hnb
    have hdist : dist (z i) (p n i) ≤ r := (dist_pi_le_iff hr0).mp hnb i
    have h1 : |(z i).re - (p n i).re| ≤ r := by
      calc |(z i).re - (p n i).re| = |(z i - p n i).re| := by rw [Complex.sub_re]
        _ ≤ ‖z i - p n i‖ := Complex.abs_re_le_norm _
        _ = dist (z i) (p n i) := by rw [dist_eq_norm]
        _ ≤ r := hdist
    calc |(z i).re - (2 * (n i : ℝ) + γ i + 1)|
        = |((z i).re - (p n i).re) + ((p n i).re - (2 * (n i : ℝ) + γ i + 1))| := by ring_nf
      _ ≤ |(z i).re - (p n i).re| + |(p n i).re - (2 * (n i : ℝ) + γ i + 1)| := abs_add_le _ _
      _ ≤ r + θ := add_le_add h1 (hre n hns i)
      _ = θ + r := by ring
  have himg : ∀ i : Fin d, (A.image (fun n => n i)).card ≤ ⌊θ + r⌋.toNat + 1 := by
    intro i
    apply finset_int_card_le_floor_add_one (by linarith : (0:ℝ) ≤ θ + r)
    intro m hm m' hm'
    rw [Finset.mem_image] at hm hm'
    obtain ⟨n, hn, rfl⟩ := hm
    obtain ⟨n', hn', rfl⟩ := hm'
    have d1 := hz n hn i
    have d2 := hz n' hn' i
    have h4 : |(2 * (n i : ℝ) + γ i + 1) - (2 * (n' i : ℝ) + γ i + 1)| ≤ 2 * (θ + r) := by
      calc |(2 * (n i : ℝ) + γ i + 1) - (2 * (n' i : ℝ) + γ i + 1)|
          = |((2 * (n i : ℝ) + γ i + 1) - (z i).re)
              + ((z i).re - (2 * (n' i : ℝ) + γ i + 1))| := by ring_nf
        _ ≤ |(2 * (n i : ℝ) + γ i + 1) - (z i).re|
              + |(z i).re - (2 * (n' i : ℝ) + γ i + 1)| := abs_add_le _ _
        _ ≤ (θ + r) + (θ + r) := add_le_add (by rw [abs_sub_comm]; exact d1) d2
        _ = 2 * (θ + r) := by ring
    have h5 : |2 * ((n i : ℝ) - (n' i : ℝ))| ≤ 2 * (θ + r) := by
      have heq : (2 * (n i : ℝ) + γ i + 1) - (2 * (n' i : ℝ) + γ i + 1)
          = 2 * ((n i : ℝ) - (n' i : ℝ)) := by ring
      rwa [heq] at h4
    have : |((n i : ℝ) - (n' i : ℝ))| ≤ θ + r := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at h5
      linarith
    simpa using this
  have hsub : A ⊆ Fintype.piFinset (fun i : Fin d => A.image (fun n => n i)) := by
    intro n hn
    rw [Fintype.mem_piFinset]
    intro i
    exact Finset.mem_image.mpr ⟨n, hn, rfl⟩
  calc A.card ≤ (Fintype.piFinset (fun i : Fin d => A.image (fun n => n i))).card :=
        Finset.card_le_card hsub
    _ = ∏ i : Fin d, (A.image (fun n => n i)).card := Fintype.card_piFinset _
    _ ≤ ∏ _i : Fin d, (⌊θ + r⌋.toNat + 1) :=
        Finset.prod_le_prod (fun i _ => Nat.zero_le _) (fun i _ => himg i)
    _ = (⌊θ + r⌋.toNat + 1) ^ d := by simp [Finset.prod_const, Fintype.card_fin]

/-- The number of indices `n ∈ s` with `z ∈ closedBall (p n) r` is at most `(θ + r + 1)^d` as an
extended non-negative real. -/
lemma filter_card_closedBall_ennreal_le {d : ℕ} {r θ : ℝ} (hr0 : 0 ≤ r) (hθ : 0 ≤ θ)
    (γ : Fin d → ℝ) (s : Finset (Fin d → ℤ)) (p : (Fin d → ℤ) → (Fin d → ℂ))
    (hre : ∀ n ∈ s, ∀ i : Fin d, |(p n i).re - (2 * (n i : ℝ) + γ i + 1)| ≤ θ)
    (z : Fin d → ℂ) :
    ((s.filter (fun n => z ∈ Metric.closedBall (p n) r)).card : ENNReal)
      ≤ ENNReal.ofReal ((θ + r + 1) ^ d) := by
  classical
  have hcard := filter_card_closedBall_le hr0 hθ γ s p hre z
  have hf0 : (0 : ℤ) ≤ ⌊θ + r⌋ := Int.floor_nonneg.mpr (by linarith)
  have htoNat : ((⌊θ + r⌋.toNat : ℕ) : ℝ) = (⌊θ + r⌋ : ℝ) := by
    norm_cast
    exact Int.toNat_of_nonneg hf0
  have hbase : (((⌊θ + r⌋.toNat + 1 : ℕ)) : ℝ) ≤ θ + r + 1 := by
    have hfl := Int.floor_le (θ + r)
    push_cast
    rw [htoNat]
    linarith
  have hpow : ((((⌊θ + r⌋.toNat + 1) ^ d : ℕ)) : ℝ) ≤ (θ + r + 1) ^ d := by
    rw [Nat.cast_pow]
    exact pow_le_pow_left₀ (by positivity) hbase d
  calc ((s.filter (fun n => z ∈ Metric.closedBall (p n) r)).card : ENNReal)
      ≤ ((((⌊θ + r⌋.toNat + 1) ^ d : ℕ)) : ENNReal) := Nat.cast_le.mpr hcard
    _ = ENNReal.ofReal ((((⌊θ + r⌋.toNat + 1) ^ d : ℕ)) : ℝ) := (ENNReal.ofReal_natCast _).symm
    _ ≤ ENNReal.ofReal ((θ + r + 1) ^ d) := ENNReal.ofReal_le_ofReal hpow

/-- Multiplicity bound for balls centred near a `2ℤ^d`-lattice: if the centres have real parts
within `θ` of the cell centres `2n + γ + 1` and imaginary parts at distance at least `r` from
the boundary of the strip `{|Im z_i| ≤ Q}`, then the sum of the `lintegral`s over the balls of
radius `r` is at most `(θ+r+1)^d` times the `lintegral` over the strip. -/
theorem finset_ball_lintegral_strip_le {d : ℕ} (f : (Fin d → ℂ) → ENNReal)
    {r Q θ : ℝ} (hr0 : 0 ≤ r) (hθ : 0 ≤ θ)
    (γ : Fin d → ℝ) (s : Finset (Fin d → ℤ)) (p : (Fin d → ℤ) → (Fin d → ℂ))
    (hre : ∀ n ∈ s, ∀ i : Fin d, |(p n i).re - (2 * (n i : ℝ) + γ i + 1)| ≤ θ)
    (him : ∀ n ∈ s, ∀ i : Fin d, |(p n i).im| ≤ Q - r) :
    ∑ n ∈ s, ∫⁻ z in Metric.closedBall (p n) r, f z
      ≤ ENNReal.ofReal ((θ + r + 1) ^ d)
          * ∫⁻ z in {z : Fin d → ℂ | ∀ i : Fin d, |(z i).im| ≤ Q}, f z := by
  classical
  set c : ENNReal := ENNReal.ofReal ((θ + r + 1) ^ d) with hc
  set S : Set (Fin d → ℂ) := {z : Fin d → ℂ | ∀ i : Fin d, |(z i).im| ≤ Q} with hSdef
  have hSclosed : IsClosed S := by
    rw [hSdef]
    rw [show {z : Fin d → ℂ | ∀ i : Fin d, |(z i).im| ≤ Q}
        = ⋂ i : Fin d, {z : Fin d → ℂ | |(z i).im| ≤ Q} from by
      ext z; simp [Set.mem_iInter]]
    exact isClosed_iInter (fun i => isClosed_le
      (continuous_abs.comp (Complex.continuous_im.comp (continuous_apply i)))
      continuous_const)
  have hSmeas : MeasurableSet S := hSclosed.measurableSet
  have hBmeas : ∀ n : Fin d → ℤ, MeasurableSet (Metric.closedBall (p n) r) :=
    fun n => Metric.isClosed_closedBall.measurableSet
  have hBsub : ∀ n ∈ s, Metric.closedBall (p n) r ⊆ S := by
    intro n hn z hz
    rw [hSdef]
    rw [Metric.mem_closedBall] at hz
    have hzi : ∀ i : Fin d, dist (z i) (p n i) ≤ r := (dist_pi_le_iff hr0).mp hz
    intro i
    have h1 : |(z i).im - (p n i).im| ≤ r := by
      calc |(z i).im - (p n i).im| = |(z i - p n i).im| := by rw [Complex.sub_im]
        _ ≤ ‖z i - p n i‖ := Complex.abs_im_le_norm _
        _ = dist (z i) (p n i) := by rw [dist_eq_norm]
        _ ≤ r := hzi i
    calc |(z i).im| = |((z i).im - (p n i).im) + (p n i).im| := by ring_nf
      _ ≤ |(z i).im - (p n i).im| + |(p n i).im| := abs_add_le _ _
      _ ≤ r + (Q - r) := add_le_add h1 (him n hn i)
      _ = Q := by ring
  -- pointwise multiplicity bound
  have hpt : ∀ z : Fin d → ℂ,
      ∑ n ∈ s, (Metric.closedBall (p n) r).indicator f z ≤ c * S.indicator f z := by
    intro z
    by_cases hz : z ∈ S
    · rw [Set.indicator_of_mem hz f]
      have hsum : (∑ n ∈ s, (Metric.closedBall (p n) r).indicator (fun _ => (1:ENNReal)) z)
          = ((s.filter (fun n => z ∈ Metric.closedBall (p n) r)).card : ENNReal) := by
        rw [show (∑ n ∈ s, (Metric.closedBall (p n) r).indicator (fun _ => (1:ENNReal)) z)
            = ∑ n ∈ s, if z ∈ Metric.closedBall (p n) r then (1:ENNReal) else 0 from by
          apply Finset.sum_congr rfl
          intro n _
          rw [Set.indicator_apply]]
        rw [Finset.sum_boole]
      have hM : (∑ n ∈ s, (Metric.closedBall (p n) r).indicator (fun _ => (1:ENNReal)) z)
          ≤ c := hsum.trans_le (filter_card_closedBall_ennreal_le hr0 hθ γ s p hre z)
      calc ∑ n ∈ s, (Metric.closedBall (p n) r).indicator f z
          = ∑ n ∈ s, (Metric.closedBall (p n) r).indicator (fun _ => (1:ENNReal)) z * f z := by
            apply Finset.sum_congr rfl
            intro n _
            by_cases hnb : z ∈ Metric.closedBall (p n) r
            · rw [Set.indicator_of_mem hnb, Set.indicator_of_mem hnb, one_mul]
            · rw [Set.indicator_of_notMem hnb, Set.indicator_of_notMem hnb, zero_mul]
        _ = (∑ n ∈ s, (Metric.closedBall (p n) r).indicator (fun _ => (1:ENNReal)) z) * f z :=
            (Finset.sum_mul _ _ _).symm
        _ ≤ c * f z := by gcongr
    · rw [Set.indicator_of_notMem hz f, mul_zero]
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro n hn
      rw [Set.indicator_of_notMem]
      intro hmem
      exact hz (hBsub n hn hmem)
  calc ∑ n ∈ s, ∫⁻ z in Metric.closedBall (p n) r, f z
      = ∑ n ∈ s, ∫⁻ z, (Metric.closedBall (p n) r).indicator f z := by
        apply Finset.sum_congr rfl
        intro n _
        exact (lintegral_indicator (hBmeas n) f).symm
    _ ≤ ∫⁻ z, ∑ n ∈ s, (Metric.closedBall (p n) r).indicator f z :=
        lintegral_finsetSum_le s _
    _ ≤ ∫⁻ z, c * S.indicator f z := lintegral_mono hpt
    _ = c * ∫⁻ z, S.indicator f z := lintegral_const_mul' c _ ENNReal.ofReal_ne_top
    _ = c * ∫⁻ z in S, f z := by rw [lintegral_indicator hSmeas f]
    _ = ENNReal.ofReal ((θ + r + 1) ^ d)
          * ∫⁻ z in {z : Fin d → ℂ | ∀ i : Fin d, |(z i).im| ≤ Q}, f z := by
        rw [hc, hSdef]

end Commons.Analysis.Measure