import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option autoImplicit false

namespace Commons.Analysis.Calculus

open Filter
open scoped Topology ENNReal

/-- Additivity of `liminf` for `ℝ≥0∞`-valued functions:
`liminf u + liminf v ≤ liminf (u + v)`, with no boundedness assumptions. -/
theorem le_liminf_add_ennreal {ι : Type*} {l : Filter ι} {u v : ι → ℝ≥0∞} :
    (Filter.liminf u l) + (Filter.liminf v l) ≤ Filter.liminf (u + v) l := by
  rcases l.eq_or_neBot with rfl | hl
  · simp
  rw [le_liminf_iff']
  intro c hc
  by_cases hu : Filter.liminf u l = 0
  · have : c < Filter.liminf v l := by simpa [hu] using hc
    filter_upwards [eventually_lt_of_lt_liminf this] with n hn
    show c ≤ u n + v n
    exact hn.le.trans (le_add_self)
  by_cases hv : Filter.liminf v l = 0
  · have : c < Filter.liminf u l := by simpa [hv, add_zero] using hc
    filter_upwards [eventually_lt_of_lt_liminf this] with n hn
    show c ≤ u n + v n
    exact hn.le.trans (le_self_add)
  · obtain ⟨a, ha, b, hb, hcab⟩ := ENNReal.exists_lt_add_of_lt_add hc hu hv
    filter_upwards [eventually_lt_of_lt_liminf ha, eventually_lt_of_lt_liminf hb] with n hn1 hn2
    show c ≤ u n + v n
    exact hcab.le.trans (add_le_add hn1.le hn2.le)

/-- The finite-sum version of `le_liminf_add_ennreal`: the sum of the `liminf`s of the summands
is at most the `liminf` of the sum. -/
theorem le_liminf_sum_ennreal {ι β : Type*} {l : Filter ι} (s : Finset β)
    (f : β → ι → ℝ≥0∞) :
    s.sum (fun b => Filter.liminf (f b) l) ≤
      Filter.liminf (fun n => s.sum (fun b => f b n)) l := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    rcases l.eq_or_neBot with rfl | hl
    · simp
    · haveI : l.NeBot := hl
      rw [Filter.liminf_const]
  | insert a s ha ih =>
    have h1 : (insert a s).sum (fun b => Filter.liminf (f b) l)
        = Filter.liminf (f a) l + s.sum (fun b => Filter.liminf (f b) l) :=
      Finset.sum_insert ha
    rw [h1]
    have h2 : (fun n => (insert a s).sum (fun b => f b n))
        = (fun n => f a n + s.sum (fun b => f b n)) := by
      funext n; exact Finset.sum_insert ha
    rw [h2]
    calc Filter.liminf (f a) l + s.sum (fun b => Filter.liminf (f b) l)
      _ ≤ Filter.liminf (f a) l + Filter.liminf (fun n => s.sum (fun b => f b n)) l := by
            gcongr
      _ ≤ Filter.liminf (fun n => f a n + s.sum (fun b => f b n)) l := le_liminf_add_ennreal

theorem lowerSemicontinuous_pairSum_inv_dist {N : ℕ} {E : Type*} [NormedAddCommGroup E]
    {ι : Type*} {l : Filter ι} {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i)
    {xs : ι → Fin N → E} {x : Fin N → E} (h : Filter.Tendsto xs l (nhds x)) :
    (∑ j, ∑ i < j, ENNReal.ofReal (m i * m j) * (ENNReal.ofReal (dist (x i) (x j)))⁻¹)
      ≤ Filter.liminf (fun n => ∑ j, ∑ i < j,
        ENNReal.ofReal (m i * m j) * (ENNReal.ofReal (dist (xs n i) (xs n j)))⁻¹) l := by
  rcases l.eq_or_neBot with rfl | hl
  · simp
  haveI : l.NeBot := hl
  -- Each individual pair term is lower semicontinuous: its `liminf` is at least its value.
  have key : ∀ (i j : Fin N),
      ENNReal.ofReal (m i * m j) * (ENNReal.ofReal (dist (x i) (x j)))⁻¹
        ≤ Filter.liminf (fun n => ENNReal.ofReal (m i * m j) *
            (ENNReal.ofReal (dist (xs n i) (xs n j)))⁻¹) l := by
    intro i j
    have hi : Filter.Tendsto (fun n => xs n i) l (𝓝 (x i)) :=
      ((continuous_apply i).tendsto x).comp h
    have hj : Filter.Tendsto (fun n => xs n j) l (𝓝 (x j)) :=
      ((continuous_apply j).tendsto x).comp h
    have hd : Filter.Tendsto (fun n => ENNReal.ofReal (dist (xs n i) (xs n j))) l
        (𝓝 (ENNReal.ofReal (dist (x i) (x j)))) :=
      ENNReal.tendsto_ofReal (hi.dist hj)
    have hlim : Filter.liminf (fun n => (ENNReal.ofReal (dist (xs n i) (xs n j)))⁻¹) l
        = (ENNReal.ofReal (dist (x i) (x j)))⁻¹ := by
      rw [← ENNReal.inv_limsup, hd.limsup_eq]
    have hmul := ENNReal.le_liminf_mul (f := l)
      (u := fun _ : ι => ENNReal.ofReal (m i * m j))
      (v := fun n => (ENNReal.ofReal (dist (xs n i) (xs n j)))⁻¹)
    simp only [Filter.liminf_const] at hmul
    rw [hlim] at hmul
    exact hmul
  -- Lower semicontinuity of the inner (fixed `j`) sum.
  have inner : ∀ j : Fin N,
      (∑ i < j, ENNReal.ofReal (m i * m j) * (ENNReal.ofReal (dist (x i) (x j)))⁻¹)
        ≤ Filter.liminf (fun n => ∑ i < j,
            ENNReal.ofReal (m i * m j) *
              (ENNReal.ofReal (dist (xs n i) (xs n j)))⁻¹) l := by
    intro j
    have h1 : (∑ i < j, ENNReal.ofReal (m i * m j) * (ENNReal.ofReal (dist (x i) (x j)))⁻¹)
        ≤ (Finset.Iio j).sum (fun i => Filter.liminf (fun n =>
            ENNReal.ofReal (m i * m j) *
              (ENNReal.ofReal (dist (xs n i) (xs n j)))⁻¹) l) :=
      Finset.sum_le_sum (fun i _ => key i j)
    have h2 := le_liminf_sum_ennreal (l := l) (Finset.Iio j)
        (fun i n => ENNReal.ofReal (m i * m j) *
              (ENNReal.ofReal (dist (xs n i) (xs n j)))⁻¹)
    exact h1.trans h2
  calc (∑ j, ∑ i < j, ENNReal.ofReal (m i * m j) * (ENNReal.ofReal (dist (x i) (x j)))⁻¹)
      = (Finset.univ : Finset (Fin N)).sum (fun j => (Finset.Iio j).sum (fun i =>
          ENNReal.ofReal (m i * m j) * (ENNReal.ofReal (dist (x i) (x j)))⁻¹)) := rfl
    _ ≤ (Finset.univ : Finset (Fin N)).sum (fun j => Filter.liminf (fun n =>
          (Finset.Iio j).sum (fun i => ENNReal.ofReal (m i * m j) *
              (ENNReal.ofReal (dist (xs n i) (xs n j)))⁻¹)) l) :=
        Finset.sum_le_sum (fun j _ => inner j)
    _ ≤ Filter.liminf (fun n => (Finset.univ : Finset (Fin N)).sum (fun j =>
          (Finset.Iio j).sum (fun i => ENNReal.ofReal (m i * m j) *
              (ENNReal.ofReal (dist (xs n i) (xs n j)))⁻¹))) l :=
        le_liminf_sum_ennreal (Finset.univ) (fun j n => (Finset.Iio j).sum (fun i =>
          ENNReal.ofReal (m i * m j) *
              (ENNReal.ofReal (dist (xs n i) (xs n j)))⁻¹))

end Commons.Analysis.Calculus