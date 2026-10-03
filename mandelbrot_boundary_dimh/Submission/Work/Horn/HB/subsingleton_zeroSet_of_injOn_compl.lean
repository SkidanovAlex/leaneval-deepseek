import Mathlib

/-!
# The zero set of a holomorphic function injective off that zero set is a subsingleton

Let `W ⊆ ℂ` be open (no connectedness assumed), `Ψ : ℂ → ℂ` holomorphic on `W`, and let

`F = {z ∈ W | Ψ z = 0}`

be its zero set inside `W`.  Assume moreover that no point `p ∈ F` is an interior point of its
level set (`hΨnlc`: `Ψ` is not eventually equal to `Ψ p = 0` near `p`), and that `Ψ` is injective
on the complement `W \ F`.  Then `F` has at most one element.

## The argument

Suppose `a ≠ b` are two distinct points of `F`.  Since `W` is open and `a, b ∈ W`, choose `r > 0`
with `ball a r ⊆ W`, `ball b r ⊆ W` and the two balls disjoint.

At `a` the function `Ψ` is analytic, `Ψ a = 0`, and is not eventually constant, so the local form
of the **open mapping theorem** (`AnalyticAt.eventually_constant_or_nhds_le_map_nhds_aux`) says
that `Ψ '' ball a r` is a neighbourhood of `0`; similarly for `b`.  Hence there is `δ > 0` so that
both images contain `ball 0 δ`.  Pick a nonzero `t ∈ ball 0 δ`; then there are `wa ∈ ball a r` and
`wb ∈ ball b r` with `Ψ wa = Ψ wb = t ≠ 0`.

Because `t ≠ 0`, neither `wa` nor `wb` lies in `F` (on `F`, `Ψ` vanishes): so `wa, wb ∈ W \ F`,
and `Ψ wa = Ψ wb` contradicts injectivity of `Ψ` on `W \ F`; but the two balls are disjoint, so
`wa ≠ wb`.  Contradiction.

Note that no finiteness of `F` is needed: the preimages produced by the open mapping theorem are
automatically *not* zeros of `Ψ`, hence lie in the complement of `F`.
-/

namespace Work.Horn.HB

open Filter Metric Set
open scoped Topology

/-- **Local open mapping, extracted.**  If `Ψ` is analytic at `a`, maps `a` to `0`, and is not
eventually equal to `Ψ a` near `a`, then the image of every ball around `a` contains a ball
around `0`. -/
lemma exists_ball_subset_image_of_not_locally_constant {Ψ : ℂ → ℂ} {a : ℂ}
    (ha : AnalyticAt ℂ Ψ a) (ha0 : Ψ a = 0)
    (hnlc : ¬ ∀ᶠ w in 𝓝 a, Ψ w = Ψ a) {r : ℝ} (hr : 0 < r) :
    ∃ δ > 0, Metric.ball 0 δ ⊆ Ψ '' Metric.ball a r := by
  have h := (ha.eventually_constant_or_nhds_le_map_nhds_aux).resolve_left hnlc
  have hmem : Ψ '' Metric.ball a r ∈ 𝓝 (Ψ a) :=
    h (Filter.mem_map.mpr (Filter.mem_of_superset (Metric.ball_mem_nhds a hr)
      (Set.subset_preimage_image Ψ _)))
  rw [ha0] at hmem
  obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp hmem
  exact ⟨δ, hδpos, hδsub⟩

theorem subsingleton_zeroSet_of_injOn_compl {W F : Set ℂ} {Ψ : ℂ → ℂ}
    (hWo : IsOpen W) (hΨan : ∀ z ∈ W, AnalyticAt ℂ Ψ z)
    (hF : F = {z : ℂ | z ∈ W ∧ Ψ z = 0})
    (hΨnlc : ∀ p ∈ F, ¬ Filter.Eventually (fun z => Ψ z = Ψ p) (nhds p))
    (hinj : Set.InjOn Ψ (W \ F)) : Set.Subsingleton F := by
  intro a ha b hb
  by_contra hab
  -- `a` and `b` are zeros of `Ψ` lying in `W`.
  have haWF : a ∈ W ∧ Ψ a = 0 := by rw [hF] at ha; exact ha
  have hbWF : b ∈ W ∧ Ψ b = 0 := by rw [hF] at hb; exact hb
  -- Balls around `a` and `b` inside `W`, disjoint.
  obtain ⟨ra, hra, hrasub⟩ := Metric.isOpen_iff.mp hWo a haWF.1
  obtain ⟨rb, hrb, hrbsub⟩ := Metric.isOpen_iff.mp hWo b hbWF.1
  have hdab : 0 < dist a b := dist_pos.mpr hab
  set r : ℝ := min (min ra rb) (dist a b / 4) with hrdef
  have hrpos : 0 < r := by
    rw [hrdef]
    exact lt_min (lt_min hra hrb) (by linarith)
  have hr_le_a : r ≤ ra := by
    rw [hrdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hr_le_b : r ≤ rb := by
    rw [hrdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hr_le_d : r ≤ dist a b / 4 := by
    rw [hrdef]; exact min_le_right _ _
  have hrsub_a : Metric.ball a r ⊆ W := (Metric.ball_subset_ball hr_le_a).trans hrasub
  have hrsub_b : Metric.ball b r ⊆ W := (Metric.ball_subset_ball hr_le_b).trans hrbsub
  have hdisj : Disjoint (Metric.ball a r) (Metric.ball b r) := by
    refine Metric.ball_disjoint_ball ?_
    linarith
  -- Open mapping at `a` and at `b`.
  obtain ⟨δa, hδapos, hδasub⟩ :=
    exists_ball_subset_image_of_not_locally_constant (hΨan a haWF.1) haWF.2
      (hΨnlc a ha) hrpos
  obtain ⟨δb, hδbpos, hδbsub⟩ :=
    exists_ball_subset_image_of_not_locally_constant (hΨan b hbWF.1) hbWF.2
      (hΨnlc b hb) hrpos
  -- A common nonzero value `t` in both images.
  have htpos : (0 : ℝ) < min δa δb / 2 := by
    have := lt_min hδapos hδbpos
    linarith
  set t : ℂ := ((min δa δb / 2 : ℝ) : ℂ) with htdef
  have ht_ne : t ≠ 0 := by
    rw [htdef]
    exact_mod_cast (ne_of_gt htpos)
  have ht_a : t ∈ Metric.ball (0 : ℂ) δa := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero, htdef, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos htpos]
    linarith [min_le_left δa δb]
  have ht_b : t ∈ Metric.ball (0 : ℂ) δb := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero, htdef, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos htpos]
    linarith [min_le_right δa δb]
  obtain ⟨wa, hwa_ball, hwa_img⟩ := hδasub ht_a
  obtain ⟨wb, hwb_ball, hwb_img⟩ := hδbsub ht_b
  have hwaW : wa ∈ W := hrsub_a hwa_ball
  have hwbW : wb ∈ W := hrsub_b hwb_ball
  -- The preimages are not zeros of `Ψ`, hence lie outside `F`.
  have hwa_notF : wa ∉ F := by
    intro h
    have hz : Ψ wa = 0 := by rw [hF] at h; exact h.2
    exact ht_ne (hwa_img.symm.trans hz)
  have hwb_notF : wb ∉ F := by
    intro h
    have hz : Ψ wb = 0 := by rw [hF] at h; exact h.2
    exact ht_ne (hwb_img.symm.trans hz)
  -- Injectivity off `F` forces the two preimages to coincide, contradicting disjointness.
  have heq : wa = wb := hinj ⟨hwaW, hwa_notF⟩ ⟨hwbW, hwb_notF⟩ (by rw [hwa_img, hwb_img])
  have hmem : wa ∈ Metric.ball b r := by rw [heq]; exact hwb_ball
  exact (Set.disjoint_left.mp hdisj) hwa_ball hmem

end Work.Horn.HB
