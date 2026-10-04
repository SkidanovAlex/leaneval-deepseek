import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.T

open Filter
open scoped Topology

/-- If `Ψ t` solves the (eventual) linear system `Ψ t j = K t j - ∑ k, Ψ t k * A k j t` with
`A k j t₀ = 0` and `K`, `A` differentiable at `t₀`, then `Ψ` is differentiable at `t₀`.

Suggested route (do NOT differentiate the identity termwise before knowing that `Ψ` is
differentiable -- that is circular):
1. the identity, with `|A k j t| ≤ C * |t - t₀|` near `t₀` (differentiability of `A`) and
   `|K j t| ≤ C'` near `t₀` (continuity of `K`), gives
   `∑ j |Ψ t j| ≤ C'' + C * |t - t₀| * ∑ j |Ψ t j|`, hence `Ψ` is bounded near `t₀`;
2. the same identity then gives `Ψ t j → K t₀ j = Ψ t₀ j` since `A k j t → 0` and `Ψ` is bounded;
3. finally `Ψ t j - Ψ t₀ j = (K t j - K t₀ j) - ∑ k, Ψ t k * A k j t`, and
   `∑ k, Ψ t k * A k j t = ∑ k, Ψ t₀ k * (A k j t - (t-t₀) * h k j) + (t-t₀) * ∑ k, Ψ t₀ k * h k j
     + ∑ k, (Ψ t k - Ψ t₀ k) * A k j t`,
   where the first sum is `o(t-t₀)` by differentiability of `A`, and the third is `o(t-t₀)` by
   continuity of `Ψ` together with `A k j t = O(t-t₀)`. -/
theorem hasDerivAt_of_eventually_system
    {ι : Type*} [Fintype ι]
    {Ψ K : ℝ → ι → ℝ} {A : ι → ι → ℝ → ℝ} {t₀ : ℝ} {K' : ι → ℝ} {h : ι → ι → ℝ}
    (hA0 : ∀ k j, A k j t₀ = 0)
    (hident : ∀ᶠ t in 𝓝 t₀, ∀ j, Ψ t j = K t j - ∑ k, Ψ t k * A k j t)
    (hK : ∀ j, HasDerivAt (fun t ↦ K t j) (K' j) t₀)
    (hA : ∀ k j, HasDerivAt (A k j) (h k j) t₀)
    (j : ι) :
    HasDerivAt (fun t ↦ Ψ t j) (K' j - ∑ k, Ψ t₀ k * h k j) t₀ := by
  classical
  -- ## Step 1: `Ψ` is bounded near `t₀`.
  --
  -- `A k j t = O(t - t₀)` (differentiability and `A k j t₀ = 0`) and `K t j` is bounded near
  -- `t₀`; the identity then keeps `∑ j |Ψ t j|` bounded.
  have hbdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t in 𝓝 t₀, ∀ j, |Ψ t j| ≤ C := by
    set CK : ℝ := ∑ j, (|K t₀ j| + 1) with hCKdef
    set CA : ℝ := ∑ k, ∑ j, (|h k j| + 1) with hCAdef
    set N : ℝ := (Fintype.card ι : ℝ) with hNdef
    have hCK0 : 0 ≤ CK := by rw [hCKdef]; positivity
    have hN0 : 0 ≤ N := by rw [hNdef]; positivity
    have hKb : ∀ᶠ t in 𝓝 t₀, ∀ j, |K t j| ≤ CK := by
      rw [Filter.eventually_all]
      intro j
      have hj : Tendsto (fun t => |K t j|) (𝓝 t₀) (𝓝 (|K t₀ j|)) :=
        (hK j).continuousAt.tendsto.abs
      have hlt : ∀ᶠ t in 𝓝 t₀, |K t j| < |K t₀ j| + 1 :=
        hj.eventually (Iio_mem_nhds (lt_add_one _))
      filter_upwards [hlt] with t ht
      exact le_trans (le_of_lt ht) (by
        rw [hCKdef]
        exact Finset.single_le_sum (f := fun i => |K t₀ i| + 1) (fun i _ => by positivity)
          (Finset.mem_univ j))
    have hAb : ∀ᶠ t in 𝓝 t₀, ∀ k j, |A k j t| ≤ CA * |t - t₀| := by
      rw [Filter.eventually_all]
      intro k
      rw [Filter.eventually_all]
      intro j
      have hsmall : ∀ᶠ t in 𝓝 t₀, |A k j t - A k j t₀ - (t - t₀) * h k j| ≤ 1 * |t - t₀| := by
        have hh := (hA k j).isLittleO
        rw [Asymptotics.isLittleO_iff] at hh
        simpa using hh (by norm_num : (0:ℝ) < 1)
      filter_upwards [hsmall] with t ht
      have hsplit : |A k j t| ≤
          |A k j t - A k j t₀ - (t - t₀) * h k j| + |A k j t₀| + |(t - t₀) * h k j| := by
        have h1 := abs_add_le (A k j t - A k j t₀ - (t - t₀) * h k j)
          (A k j t₀ + (t - t₀) * h k j)
        have h2 := abs_add_le (A k j t₀) ((t - t₀) * h k j)
        have habs : |A k j t| =
            |A k j t - A k j t₀ - (t - t₀) * h k j + (A k j t₀ + (t - t₀) * h k j)| :=
          congrArg abs (by ring)
        rw [habs]
        linarith [h1, h2]
      have hCAj : 1 + |h k j| ≤ CA := by
        rw [hCAdef]
        have h1 : |h k j| + 1 ≤ ∑ j' ∈ Finset.univ, (|h k j'| + 1) :=
          Finset.single_le_sum (f := fun j' => |h k j'| + 1) (fun i _ => by positivity)
            (Finset.mem_univ j)
        have h2 : (∑ j' ∈ Finset.univ, (|h k j'| + 1)) ≤
            ∑ k' ∈ Finset.univ, (∑ j' ∈ Finset.univ, (|h k' j'| + 1)) :=
          Finset.single_le_sum (f := fun k' => ∑ j' ∈ Finset.univ, (|h k' j'| + 1))
            (fun i _ => by positivity) (Finset.mem_univ k)
        linarith [h1, h2]
      have h3 : |(t - t₀) * h k j| = |t - t₀| * |h k j| := abs_mul _ _
      have h4 : |A k j t₀| = 0 := by rw [hA0 k j, abs_zero]
      have hfin : |A k j t| ≤ |t - t₀| * (1 + |h k j|) := by
        nlinarith [hsplit, ht, h3, h4, abs_nonneg (t - t₀), abs_nonneg (h k j)]
      calc |A k j t| ≤ |t - t₀| * (1 + |h k j|) := hfin
        _ ≤ |t - t₀| * CA := mul_le_mul_of_nonneg_left hCAj (abs_nonneg _)
        _ = CA * |t - t₀| := by ring
    have hsm : ∀ᶠ t in 𝓝 t₀, N * CA * |t - t₀| < 1 / 2 := by
      have hct : ContinuousAt (fun t : ℝ => N * CA * |t - t₀|) t₀ := by
        have h1 : ContinuousAt (fun t : ℝ => |t - t₀|) t₀ :=
          continuous_abs.continuousAt.comp (continuousAt_id.sub continuousAt_const)
        exact h1.const_mul (N * CA)
      have hh := hct.tendsto.eventually
        (Iio_mem_nhds (show N * CA * |t₀ - t₀| < 1/2 by simp))
      simpa using hh
    refine ⟨2 * N * CK, ?_, ?_⟩
    · exact mul_nonneg (mul_nonneg (by norm_num) hN0) hCK0
    · filter_upwards [hident, hKb, hAb, hsm] with t hid hKbt hAbt hst
      set S : ℝ := ∑ j, |Ψ t j| with hSdef
      have hS0 : 0 ≤ S := by rw [hSdef]; positivity
      have hper : ∀ j, |Ψ t j| ≤ CK + CA * |t - t₀| * S := by
        intro j
        have hbase : |Ψ t j| ≤ CK + ∑ k, |Ψ t k| * (CA * |t - t₀|) := by
          calc |Ψ t j| = |K t j - ∑ k, Ψ t k * A k j t| := by rw [hid j]
            _ = |K t j + -(∑ k, Ψ t k * A k j t)| := by ring_nf
            _ ≤ |K t j| + |-(∑ k, Ψ t k * A k j t)| := abs_add_le _ _
            _ = |K t j| + |∑ k, Ψ t k * A k j t| := by rw [abs_neg]
            _ ≤ CK + ∑ k, |Ψ t k| * (CA * |t - t₀|) :=
                  add_le_add (hKbt j) (by
                    calc |∑ k, Ψ t k * A k j t| ≤ ∑ k, |Ψ t k * A k j t| :=
                          Finset.abs_sum_le_sum_abs (fun k => Ψ t k * A k j t) Finset.univ
                      _ ≤ ∑ k, |Ψ t k| * (CA * |t - t₀|) := by
                          apply Finset.sum_le_sum
                          intro k _
                          rw [abs_mul]
                          exact mul_le_mul_of_nonneg_left (hAbt k j) (abs_nonneg _))
        have hSsum : ∑ k, |Ψ t k| * (CA * |t - t₀|) = S * (CA * |t - t₀|) := by
          rw [hSdef]
          exact (Finset.sum_mul Finset.univ (fun k => |Ψ t k|) (CA * |t - t₀|)).symm
        calc |Ψ t j| ≤ CK + ∑ k, |Ψ t k| * (CA * |t - t₀|) := hbase
          _ = CK + S * (CA * |t - t₀|) := by rw [hSsum]
          _ = CK + CA * |t - t₀| * S := by ring
      have hSle : S ≤ N * CK + (N * CA * |t - t₀|) * S := by
        have h1 : S ≤ ∑ j : ι, (CK + CA * |t - t₀| * S) := by
          rw [hSdef]
          exact Finset.sum_le_sum (fun j _ => hper j)
        have h2 : ∑ j : ι, (CK + CA * |t - t₀| * S) = N * CK + N * (CA * |t - t₀| * S) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const, Finset.card_univ, hNdef]
          simp only [nsmul_eq_mul]
        calc S ≤ ∑ j : ι, (CK + CA * |t - t₀| * S) := h1
          _ = N * CK + N * (CA * |t - t₀| * S) := h2
          _ = N * CK + (N * CA * |t - t₀|) * S := by ring
      have hSfin : S ≤ 2 * N * CK := by
        have h1 : S / 2 ≤ N * CK := by nlinarith [hSle, hst, hS0]
        linarith
      intro j
      calc |Ψ t j| ≤ S := by
              rw [hSdef]
              exact Finset.single_le_sum (f := fun i => |Ψ t i|) (fun i _ => abs_nonneg _)
                (Finset.mem_univ j)
        _ ≤ 2 * N * CK := hSfin
  obtain ⟨C, _hC0, hCb⟩ := hbdd
  -- ## Step 2: each coordinate of `Ψ` is continuous at `t₀`.
  --
  -- `Ψ t j = K t j - ∑ k, Ψ t k * A k j t`, the summands tend to `0` (bounded times `A → 0`).
  have hcont : ∀ k, Tendsto (fun t => Ψ t k) (𝓝 t₀) (𝓝 (K t₀ k)) := by
    intro k
    have hterm : ∀ i, Tendsto (fun t => Ψ t i * A i k t) (𝓝 t₀) (𝓝 0) := by
      intro i
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hAcont : Tendsto (fun t => ‖A i k t‖) (𝓝 t₀) (𝓝 0) := by
        have hc : Tendsto (fun t => A i k t) (𝓝 t₀) (𝓝 (A i k t₀)) := (hA i k).continuousAt
        rw [hA0 i k] at hc
        simpa using hc.norm
      have hgoal : Tendsto (fun t => C * ‖A i k t‖) (𝓝 t₀) (𝓝 0) := by
        have := hAcont.const_mul C
        simpa using this
      refine squeeze_zero' ?_ ?_ hgoal
      · filter_upwards with t
        exact norm_nonneg _
      · filter_upwards [hCb] with t ht
        have h1 : ‖Ψ t i‖ ≤ C := by
          have := ht i
          simpa [Real.norm_eq_abs] using this
        calc ‖Ψ t i * A i k t‖ = ‖Ψ t i‖ * ‖A i k t‖ := norm_mul _ _
          _ ≤ C * ‖A i k t‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    have hsum : Tendsto (fun t => ∑ i, Ψ t i * A i k t) (𝓝 t₀) (𝓝 0) := by
      have := tendsto_finsetSum (Finset.univ : Finset ι) (fun i _ => hterm i)
      simpa using this
    have hKj : Tendsto (fun t => K t k) (𝓝 t₀) (𝓝 (K t₀ k)) := (hK k).continuousAt
    have hcomb : Tendsto (fun t => K t k - ∑ i, Ψ t i * A i k t) (𝓝 t₀) (𝓝 (K t₀ k)) := by
      have := hKj.sub hsum
      simpa using this
    refine hcomb.congr' ?_
    filter_upwards [hident] with t ht
    exact (ht k).symm
  -- ## Step 3: differentiate.
  --
  -- The identity at `t₀` itself: `∀ᶠ t in 𝓝 t₀, _` forces the statement at `t₀`
  -- (every neighbourhood of `t₀` contains `t₀`), so `Ψ t₀ = K t₀`.
  have hPsi0 : ∀ k, Ψ t₀ k = K t₀ k := by
    intro k
    have hh := hident.self_of_nhds k
    simpa [hA0] using hh
  have hsumA : HasDerivAt (fun t => ∑ k, Ψ t₀ k * A k j t) (∑ k, Ψ t₀ k * h k j) t₀ := by
    have hh := HasDerivAt.sum (u := Finset.univ) (fun k _ => (hA k j).const_mul (Ψ t₀ k))
    have hEq : (∑ k, (fun t => Ψ t₀ k * A k j t)) = (fun t => ∑ k, Ψ t₀ k * A k j t) := by
      funext t; simp [Finset.sum_apply]
    rw [hEq] at hh
    exact hh
  have hmain : HasDerivAt (fun t => K t j - ∑ k, Ψ t₀ k * A k j t)
      (K' j - ∑ k, Ψ t₀ k * h k j) t₀ := (hK j).sub hsumA
  have herr_littleO : (fun t => ∑ k, (Ψ t k - Ψ t₀ k) * A k j t) =o[𝓝 t₀] (fun t => t - t₀) := by
    have hsum : (∑ k, (fun t => (Ψ t k - Ψ t₀ k) * A k j t)) =o[𝓝 t₀] (fun t => t - t₀) := by
      apply Asymptotics.IsLittleO.sum
      intro k _
      have hfk : (fun t => Ψ t k - Ψ t₀ k) =o[𝓝 t₀] (fun _ => (1:ℝ)) := by
        rw [Asymptotics.isLittleO_one_iff ℝ]
        have hh := (hcont k).sub_const (Ψ t₀ k)
        simpa [hPsi0 k] using hh
      have hgk : (fun t => A k j t) =O[𝓝 t₀] (fun t => t - t₀) := by
        have hR : (fun t => A k j t - A k j t₀ - (t - t₀) * h k j) =O[𝓝 t₀] (fun t => t - t₀) :=
          (hA k j).isLittleO.isBigO
        have h2' : (fun t => h k j * (t - t₀)) =O[𝓝 t₀] (fun t => t - t₀) :=
          (Asymptotics.isBigO_refl (fun t => t - t₀) (𝓝 t₀)).const_mul_left (h k j)
        have h2 : (fun t => (t - t₀) * h k j) =O[𝓝 t₀] (fun t => t - t₀) :=
          h2'.congr_left (fun t => mul_comm (h k j) (t - t₀))
        have hsum2 := hR.add h2
        simpa [hA0 k j] using hsum2
      have hprod := hfk.mul_isBigO hgk
      simpa using hprod
    have hEq : (∑ k, (fun t => (Ψ t k - Ψ t₀ k) * A k j t))
        = (fun t => ∑ k, (Ψ t k - Ψ t₀ k) * A k j t) := by
      funext t; simp [Finset.sum_apply]
    rw [hEq] at hsum
    exact hsum
  have herr : HasDerivAt (fun t => ∑ k, (Ψ t k - Ψ t₀ k) * A k j t) 0 t₀ := by
    rw [hasDerivAt_iff_isLittleO]
    simpa using herr_littleO
  have hkey : HasDerivAt
      (fun t => (K t j - ∑ k, Ψ t₀ k * A k j t) - ∑ k, (Ψ t k - Ψ t₀ k) * A k j t)
      (K' j - ∑ k, Ψ t₀ k * h k j - 0) t₀ := hmain.sub herr
  have heq : (fun t => (K t j - ∑ k, Ψ t₀ k * A k j t) - ∑ k, (Ψ t k - Ψ t₀ k) * A k j t)
      =ᶠ[𝓝 t₀] (fun t => Ψ t j) := by
    filter_upwards [hident] with t ht
    rw [ht j]
    have hsplit : (∑ k, Ψ t k * A k j t) - (∑ k, Ψ t₀ k * A k j t)
        = ∑ k, (Ψ t k - Ψ t₀ k) * A k j t := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [← hsplit]
    ring
  simpa using heq.hasDerivAt_iff.mp hkey

end Work.Diff.T
