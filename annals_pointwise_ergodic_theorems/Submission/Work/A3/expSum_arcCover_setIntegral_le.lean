import Mathlib
import Submission.Work.A3.integral_mArcKernel_pow_le
import Submission.Work.A3.majorArc_split
import Submission.Work.A3.sum_arc_number_bound

/-!
# The abstract arc-covering energy estimate (Area A3)

This module proves the *summation* step of the circle-method major-arc analysis:

if every point `θ ∈ A ∩ [0,1]` is covered by an arc `a/q` with `1 ≤ q ≤ M`, `-1 ≤ a ≤ q+1` on
which the exponential sum is dominated by the comparison kernel,

  `‖expSum Q N θ‖ ≤ C · q^{-δ} · mArcKernel N d (θ - a/q)`,   `d = Q.natDegree`,

then the `2s`-th moment of the exponential sum over `A ∩ [0,1]` satisfies

  `∫_{A ∩ [0,1]} ‖expSum Q N‖^{2s} ≤ C'^{2s} N^{2s-d}`

with a constant `C'` **independent of `A`, of `M` and of `N`**.  The point of the statement is the
uniformity in `M`: the witness `q` is summed with weight `q^{-2sδ}` and there are only `q + 3`
numerators `a` at level `q`, so the total weight of the arcs is `∑_{q ≤ M} (q+3) q^{-2sδ}`, which is
bounded uniformly in `M` precisely because `s δ > 1` (`Work.A3.sum_arc_number_bound`).

The proof is the standard finite-union bookkeeping (compare
`Work.A3.majorArc_contribution_of_pointwise`):

* the witness of every `θ ∈ A ∩ [0,1]` contributes one term of the finite double sum
  `F(θ) = ∑_{q ≤ M} ∑_{-1 ≤ a ≤ q+1} (C q^{-δ} mArcKernel N d (θ - a/q))^{2s}`, all of whose terms
  are nonnegative, so `‖expSum Q N θ‖^{2s} ≤ F(θ)` there;
* `F` is integrable (`mArcKernel N d` is dominated by `min N |β|^{-1/d}`, whose `2s`-th power is
  integrable because `d < 2s`), so `∫_{A∩[0,1]} ‖expSum‖^{2s} ≤ ∫_ℝ F`;
* `∫_ℝ F = ∑_{q ≤ M} (q+3) (C q^{-δ})^{2s} ∫_ℝ (mArcKernel N d)^{2s}` by
  `integral_finsetSum` and the translation invariance of Lebesgue measure, and
  `∫_ℝ (mArcKernel N d)^{2s} ≤ K^{2s} N^{2s-d}` uniformly in `N` and `s` by
  `Work.A3.integral_mArcKernel_pow_le` (`d ≥ 2`);
* the remaining sum is bounded by `K'` (`Work.A3.sum_arc_number_bound`), giving
  `C' = max 1 (C · K · max K' 1)`.
-/

set_option maxHeartbeats 1000000

namespace Work.A3

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators

noncomputable section

/-! ## Integrability of the powers of the comparison kernel -/

/-- The comparison kernel is bounded by `min N (|β|^{-1/d})` away from `β = 0`. -/
private lemma mArcKernel_le_min' {N d : ℕ} (hN : 1 ≤ N) (hd : 1 ≤ d) {β : ℝ} (hβ : β ≠ 0) :
    mArcKernel N d β ≤ min (N : ℝ) (|β| ^ (-(1 : ℝ) / (d : ℝ))) :=
  le_min (mArcKernel_le_N hN hd β) (mArcKernel_le hd hβ)

/-- The comparison kernel is continuous (for `N ≥ 1`, so that the base stays positive). -/
private lemma continuous_mArcKernel' (N d : ℕ) (hN : 1 ≤ N) :
    Continuous (fun u : ℝ => mArcKernel N d u) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  rw [show (fun u : ℝ => mArcKernel N d u)
      = fun u : ℝ => (|u| + (N : ℝ) ^ (-(d : ℝ))) ^ (-(1 : ℝ) / (d : ℝ)) from rfl]
  refine Continuous.rpow_const ?_ ?_
  · exact continuous_abs.add continuous_const
  · intro u
    exact Or.inl (ne_of_gt (by positivity : (0:ℝ) < |u| + (N:ℝ) ^ (-(d:ℝ))))

/-- Powers of the comparison kernel are integrable on `ℝ` when `d < 2s`. -/
private lemma integrable_mArcKernel_pow' {d N s : ℕ} (hd : 1 ≤ d) (hN : 1 ≤ N)
    (hds : d < 2 * s) : Integrable fun β : ℝ => (mArcKernel N d β) ^ (2 * s) := by
  refine Integrable.mono' (integrable_min_rpow 1 one_pos d hd N s hds) ?_ ?_
  · exact ((continuous_mArcKernel' N d hN).pow (2 * s)).aestronglyMeasurable
  · rw [MeasureTheory.ae_iff]
    refine measure_mono_null (t := {0}) (fun β hβ => ?_) (by simp)
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff] at hβ ⊢
    by_contra hne
    have hub : mArcKernel N d β ≤ min (N : ℝ) (1 * |β| ^ (-(1 : ℝ) / (d : ℝ))) :=
      le_min (mArcKernel_le_N hN hd β) (by rw [one_mul]; exact mArcKernel_le hd hne)
    have hpos : 0 ≤ mArcKernel N d β := le_of_lt (mArcKernel_pos hN hd β)
    exact hβ (by
      rw [Real.norm_of_nonneg (pow_nonneg hpos _)]
      exact pow_le_pow_left₀ hpos hub (2 * s))

/-! ## The dominating majorant of the arcs -/

/-- The finite sum of the pointwise arc bounds over all arcs `a/q` with `1 ≤ q ≤ M` and
`-1 ≤ a ≤ q+1`. -/
private def arcMaj (C δ : ℝ) (d N M s : ℕ) (θ : ℝ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 M, ∑ a ∈ Finset.Icc (-1 : ℤ) ((q : ℤ) + 1),
    (C * (q : ℝ) ^ (-δ) * mArcKernel N d (θ - (a : ℝ) / (q : ℝ))) ^ (2 * s)

/-- The majorant is nonnegative. -/
private lemma arcMaj_nonneg (C δ : ℝ) (d N M s : ℕ) (hC : 0 < C) (hN : 1 ≤ N) (hd : 1 ≤ d)
    (θ : ℝ) : 0 ≤ arcMaj C δ d N M s θ := by
  refine Finset.sum_nonneg fun q _ => Finset.sum_nonneg fun a _ => ?_
  exact pow_nonneg (mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg q) _))
    (le_of_lt (mArcKernel_pos hN hd _))) _

/-- Each single arc term is integrable. -/
private lemma integrable_arcTerm (C δ : ℝ) (d N s : ℕ) (q : ℕ) (a : ℤ)
    (hd : 1 ≤ d) (hN : 1 ≤ N) (hds : d < 2 * s) :
    Integrable (fun θ : ℝ =>
      (C * (q : ℝ) ^ (-δ) * mArcKernel N d (θ - (a : ℝ) / (q : ℝ))) ^ (2 * s)) := by
  have hbase : Integrable (fun θ : ℝ => (mArcKernel N d (θ - (a : ℝ) / (q : ℝ))) ^ (2 * s)) :=
    (integrable_mArcKernel_pow' hd hN hds).comp_sub_right _
  have h2 : Integrable (fun θ : ℝ => (C * (q : ℝ) ^ (-δ)) ^ (2 * s) *
      (mArcKernel N d (θ - (a : ℝ) / (q : ℝ))) ^ (2 * s)) :=
    hbase.const_mul _
  simpa only [mul_pow] using h2

/-- The majorant is integrable. -/
private lemma integrable_arcMaj (C δ : ℝ) (d N M s : ℕ) (hd : 1 ≤ d) (hN : 1 ≤ N)
    (hds : d < 2 * s) : Integrable (arcMaj C δ d N M s) := by
  unfold arcMaj
  refine integrable_finsetSum _ fun q _ => integrable_finsetSum _ fun a _ =>
    integrable_arcTerm C δ d N s q a hd hN hds

/-- The integral of the majorant over `ℝ`, computed term by term. -/
private lemma integral_arcMaj (C δ : ℝ) (d N M s : ℕ) (hd : 1 ≤ d) (hN : 1 ≤ N)
    (hds : d < 2 * s) :
    ∫ θ : ℝ, arcMaj C δ d N M s θ
      = ∑ q ∈ Finset.Icc 1 M, ((q : ℝ) + 3) *
          ((C * (q : ℝ) ^ (-δ)) ^ (2 * s) * ∫ β : ℝ, (mArcKernel N d β) ^ (2 * s)) := by
  have hterm : ∀ (q : ℕ) (a : ℤ),
      ∫ θ : ℝ, (C * (q : ℝ) ^ (-δ) * mArcKernel N d (θ - (a : ℝ) / (q : ℝ))) ^ (2 * s)
        = (C * (q : ℝ) ^ (-δ)) ^ (2 * s) * ∫ β : ℝ, (mArcKernel N d β) ^ (2 * s) := by
    intro q a
    have h1 : (fun θ : ℝ => (C * (q : ℝ) ^ (-δ) * mArcKernel N d
          (θ - (a : ℝ) / (q : ℝ))) ^ (2 * s))
        = fun θ : ℝ => (C * (q : ℝ) ^ (-δ)) ^ (2 * s) *
            (mArcKernel N d (θ - (a : ℝ) / (q : ℝ))) ^ (2 * s) := by
      funext θ
      rw [mul_pow]
    rw [h1, integral_const_mul,
      integral_sub_right_eq_self (f := fun β : ℝ => (mArcKernel N d β) ^ (2 * s))]
  have hcard : ∀ q : ℕ, (Finset.Icc (-1 : ℤ) ((q : ℤ) + 1)).card = q + 3 := by
    intro q
    rw [Int.card_Icc]
    have h1 : ((q : ℤ) + 1 + 1 - (-1)) = ((q + 3 : ℕ) : ℤ) := by push_cast; ring
    rw [h1, Int.toNat_natCast]
  have hsum : ∀ q : ℕ,
      (∫ θ : ℝ, ∑ a ∈ Finset.Icc (-1 : ℤ) ((q : ℤ) + 1),
          (C * (q : ℝ) ^ (-δ) * mArcKernel N d (θ - (a : ℝ) / (q : ℝ))) ^ (2 * s))
        = ((q : ℝ) + 3) * ((C * (q : ℝ) ^ (-δ)) ^ (2 * s) *
            ∫ β : ℝ, (mArcKernel N d β) ^ (2 * s)) := by
    intro q
    rw [integral_finsetSum _ (fun a _ => integrable_arcTerm C δ d N s q a hd hN hds)]
    trans ∑ a ∈ Finset.Icc (-1 : ℤ) ((q : ℤ) + 1),
        ((C * (q : ℝ) ^ (-δ)) ^ (2 * s) * ∫ β : ℝ, (mArcKernel N d β) ^ (2 * s))
    · exact Finset.sum_congr rfl fun a _ => hterm q a
    · rw [Finset.sum_const, hcard q, nsmul_eq_mul]
      push_cast
      ring
  have h1 : ∫ θ : ℝ, arcMaj C δ d N M s θ
      = ∑ q ∈ Finset.Icc 1 M, ∫ θ : ℝ, ∑ a ∈ Finset.Icc (-1 : ℤ) ((q : ℤ) + 1),
          (C * (q : ℝ) ^ (-δ) * mArcKernel N d (θ - (a : ℝ) / (q : ℝ))) ^ (2 * s) := by
    unfold arcMaj
    exact integral_finsetSum _ (fun q _ => integrable_finsetSum _ (fun a _ =>
      integrable_arcTerm C δ d N s q a hd hN hds))
  rw [h1]
  exact Finset.sum_congr rfl fun q _ => hsum q

/-! ## The main theorem -/

theorem expSum_arcCover_setIntegral_le (Q : Polynomial ℤ) (hd : 2 ≤ Polynomial.natDegree Q)
    {C δ : ℝ} (hC : 0 < C) (hδ : 0 < δ) {s : ℕ} (hs : 1 ≤ s)
    (hδs : 1 < (s : ℝ) * δ) (hds : Polynomial.natDegree Q < 2 * s) :
    ∃ C' > 0, ∀ (N M : ℕ) (A : Set ℝ), 1 ≤ N → MeasurableSet A →
      (∀ θ ∈ A ∩ Set.Icc (0 : ℝ) 1,
        ∃ q : ℕ, ∃ a : ℤ, 1 ≤ q ∧ q ≤ M ∧ a ∈ Finset.Icc (-1) ((q : ℤ) + 1) ∧
          ‖Work.A3.expSum Q N θ‖ ≤
            C * (q : ℝ) ^ (-δ) * Work.A3.mArcKernel N (Polynomial.natDegree Q)
              (θ - (a : ℝ) / (q : ℝ))) →
      ∫ θ in A ∩ Set.Icc (0 : ℝ) 1, ‖Work.A3.expSum Q N θ‖ ^ (2 * s)
        ≤ C' ^ (2 * s) * (N : ℝ) ^ (2 * s - Polynomial.natDegree Q) := by
  obtain ⟨K, hKpos, hKmom⟩ :=
    integral_mArcKernel_pow_le (d := Polynomial.natDegree Q) (s := s) hd hds
  obtain ⟨K', hK'pos, hKsum⟩ := sum_arc_number_bound hδ hδs
  have hd1 : 1 ≤ Polynomial.natDegree Q := le_trans (by norm_num) hd
  refine ⟨max 1 (C * K * max K' 1), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro N M A hN hA hcov
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  let F : ℝ → ℝ := arcMaj C δ (Polynomial.natDegree Q) N M s
  have hFint : Integrable F :=
    integrable_arcMaj C δ (Polynomial.natDegree Q) N M s hd1 hN hds
  have hFnonneg : 0 ≤ᵐ[volume] F := Filter.Eventually.of_forall fun θ =>
    arcMaj_nonneg C δ (Polynomial.natDegree Q) N M s hC hN hd1 θ
  have hIntVal : ∫ θ : ℝ, F θ
      = ∑ q ∈ Finset.Icc 1 M, ((q : ℝ) + 3) *
          ((C * (q : ℝ) ^ (-δ)) ^ (2 * s) *
            ∫ β : ℝ, (mArcKernel N (Polynomial.natDegree Q) β) ^ (2 * s)) :=
    integral_arcMaj C δ (Polynomial.natDegree Q) N M s hd1 hN hds
  have hIp := hKmom N hN
  have hpt : ∀ θ ∈ A ∩ Set.Icc (0 : ℝ) 1, ‖expSum Q N θ‖ ^ (2 * s) ≤ F θ := by
    rintro θ ⟨hθA, hθIcc⟩
    obtain ⟨q, a, hq1, hqM, hamem, hbd⟩ := hcov θ ⟨hθA, hθIcc⟩
    have hqmem : q ∈ Finset.Icc 1 M := Finset.mem_Icc.mpr ⟨hq1, hqM⟩
    have hterm : ‖expSum Q N θ‖ ^ (2 * s) ≤
        (C * (q : ℝ) ^ (-δ) * mArcKernel N (Polynomial.natDegree Q)
          (θ - (a : ℝ) / (q : ℝ))) ^ (2 * s) :=
      pow_le_pow_left₀ (norm_nonneg (expSum Q N θ)) hbd (2 * s)
    have hinner : (C * (q : ℝ) ^ (-δ) * mArcKernel N (Polynomial.natDegree Q)
          (θ - (a : ℝ) / (q : ℝ))) ^ (2 * s)
        ≤ ∑ a' ∈ Finset.Icc (-1 : ℤ) ((q : ℤ) + 1),
            (C * (q : ℝ) ^ (-δ) * mArcKernel N (Polynomial.natDegree Q)
              (θ - (a' : ℝ) / (q : ℝ))) ^ (2 * s) :=
      Finset.single_le_sum
        (f := fun a' : ℤ => (C * (q : ℝ) ^ (-δ) *
          mArcKernel N (Polynomial.natDegree Q) (θ - (a' : ℝ) / (q : ℝ))) ^ (2 * s))
        (fun a' _ => pow_nonneg (mul_nonneg (mul_nonneg hC.le
          (Real.rpow_nonneg (Nat.cast_nonneg q) (-δ)))
          (le_of_lt (mArcKernel_pos hN hd1 _))) (2 * s)) hamem
    have houter : (∑ a' ∈ Finset.Icc (-1 : ℤ) ((q : ℤ) + 1),
            (C * (q : ℝ) ^ (-δ) * mArcKernel N (Polynomial.natDegree Q)
              (θ - (a' : ℝ) / (q : ℝ))) ^ (2 * s)) ≤ F θ := by
      show (∑ a' ∈ Finset.Icc (-1 : ℤ) ((q : ℤ) + 1),
            (C * (q : ℝ) ^ (-δ) * mArcKernel N (Polynomial.natDegree Q)
              (θ - (a' : ℝ) / (q : ℝ))) ^ (2 * s)) ≤
          ∑ q' ∈ Finset.Icc 1 M, ∑ a' ∈ Finset.Icc (-1 : ℤ) ((q' : ℤ) + 1),
            (C * (q' : ℝ) ^ (-δ) * mArcKernel N (Polynomial.natDegree Q)
              (θ - (a' : ℝ) / (q' : ℝ))) ^ (2 * s)
      exact Finset.single_le_sum
        (f := fun q' : ℕ => ∑ a' ∈ Finset.Icc (-1 : ℤ) ((q' : ℤ) + 1),
          (C * (q' : ℝ) ^ (-δ) *
            mArcKernel N (Polynomial.natDegree Q) (θ - (a' : ℝ) / (q' : ℝ))) ^ (2 * s))
        (fun q' _ => Finset.sum_nonneg (fun a' _ => pow_nonneg (mul_nonneg (mul_nonneg hC.le
          (Real.rpow_nonneg (Nat.cast_nonneg q') (-δ)))
          (le_of_lt (mArcKernel_pos hN hd1 _))) (2 * s))) hqmem
    exact le_trans hterm (le_trans hinner houter)
  have hcont : Continuous fun θ : ℝ => ‖expSum Q N θ‖ ^ (2 * s) := by
    unfold expSum; fun_prop
  have hint_on : IntegrableOn (fun θ : ℝ => ‖expSum Q N θ‖ ^ (2 * s))
      (A ∩ Set.Icc (0 : ℝ) 1) volume :=
    (hcont.integrableOn_Icc).mono_set Set.inter_subset_right
  have hconst : (C * K) ^ (2 * s) * K' ≤ (max 1 (C * K * max K' 1)) ^ (2 * s) := by
    have hB : 1 ≤ max K' 1 := le_max_right _ _
    calc (C * K) ^ (2 * s) * K'
        ≤ (C * K) ^ (2 * s) * max K' 1 :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
      _ ≤ (C * K) ^ (2 * s) * (max K' 1) ^ (2 * s) :=
          mul_le_mul_of_nonneg_left (le_self_pow₀ hB (by omega)) (by positivity)
      _ = (C * K * max K' 1) ^ (2 * s) := by simp only [mul_pow]
      _ ≤ (max 1 (C * K * max K' 1)) ^ (2 * s) :=
          pow_le_pow_left₀ (by positivity) (le_max_right _ _) _
  calc ∫ θ in A ∩ Set.Icc (0 : ℝ) 1, ‖expSum Q N θ‖ ^ (2 * s)
      ≤ ∫ θ in A ∩ Set.Icc (0 : ℝ) 1, F θ :=
        setIntegral_mono_on hint_on (hFint.integrableOn.mono_set Set.inter_subset_right)
          (hA.inter measurableSet_Icc) hpt
    _ ≤ ∫ θ : ℝ, F θ := setIntegral_le_integral hFint hFnonneg
    _ = ∑ q ∈ Finset.Icc 1 M, ((q : ℝ) + 3) *
          ((C * (q : ℝ) ^ (-δ)) ^ (2 * s) *
            ∫ β : ℝ, (mArcKernel N (Polynomial.natDegree Q) β) ^ (2 * s)) := hIntVal
    _ ≤ ∑ q ∈ Finset.Icc 1 M, ((q : ℝ) + 3) *
          ((C * (q : ℝ) ^ (-δ)) ^ (2 * s) *
            (K ^ (2 * s) * (N : ℝ) ^ (2 * s - Polynomial.natDegree Q))) := by
        refine Finset.sum_le_sum ?_
        intro q _
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hIp
          (pow_nonneg (mul_nonneg hC.le
            (Real.rpow_nonneg (Nat.cast_nonneg q) (-δ))) _)) (by positivity)
    _ = (C ^ (2 * s) * (K ^ (2 * s) * (N : ℝ) ^ (2 * s - Polynomial.natDegree Q))) *
          (∑ q ∈ Finset.Icc 1 M, ((q : ℝ) + 3) *
            (q : ℝ) ^ (-(2 * (s : ℝ) * δ))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg q) (-δ) (2 * s)]
        have hexp2 : -δ * ((2 * s : ℕ) : ℝ) = -(2 * (s : ℝ) * δ) := by push_cast; ring
        rw [hexp2]
        ring
    _ = (C * K) ^ (2 * s) * (N : ℝ) ^ (2 * s - Polynomial.natDegree Q) *
          (∑ q ∈ Finset.Icc 1 M, ((q : ℝ) + 3) *
            (q : ℝ) ^ (-(2 * (s : ℝ) * δ))) := by
        rw [mul_pow]; ring
    _ ≤ (C * K) ^ (2 * s) * (N : ℝ) ^ (2 * s - Polynomial.natDegree Q) * K' :=
        mul_le_mul_of_nonneg_left (hKsum M) (by positivity)
    _ = ((C * K) ^ (2 * s) * K') * (N : ℝ) ^ (2 * s - Polynomial.natDegree Q) := by ring
    _ ≤ (max 1 (C * K * max K' 1)) ^ (2 * s) *
          (N : ℝ) ^ (2 * s - Polynomial.natDegree Q) :=
        mul_le_mul_of_nonneg_right hconst (by positivity)

end

end Work.A3
