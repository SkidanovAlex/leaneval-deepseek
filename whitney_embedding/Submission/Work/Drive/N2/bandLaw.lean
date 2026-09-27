import Mathlib
import Submission.Work.Drive.Morse

/-!
# `bandLaw`: unit speed on the ball-free bands

The global assembly of the compact `n = 2` movie uses **one** flow `Φ*`
(`Work.Drive.N2.exists_modelAdapted_levelFlow_chartODE`), which advances `f` at unit speed on every
trajectory that avoids the model balls:

    `f (Φ* (t, y)) = f y + t`   when the trajectory `u ↦ Φ* (u, y)` on `Icc (min 0 t) (max 0 t)`
                                avoids the balls                                          (`hlevel`).

On a value band `(a,b)` which carries **no** ball value — a *ball-free band*, in the movie the bands
`(c i + 3η/4, c (i+1) - 3η/4)` between two windows and the idle parts of the windows — the
trajectories between band values are automatically ball-free, so the level law holds there for free.
This file proves that, in the general form in which the assembly consumes it: it is the lead's
`bandLaw` ("unit speed on ball-free bands and on the idle parts of windows, first exit time +
connectedness").

## The statement

`B` is the union of the *open* model balls (the set appearing in `hlevel`), `K` a **closed** set of
points whose `f`-values avoid the closed interval `Icc a b` — in the application `K` is the union of
the *closed* model balls, whose `f`-values lie in `[c i - r i², c i + r i²]`, so `B ⊆ K` and `K` is
closed and value-separated from the band.  If `x` has a band value and `f x + t` has a band value,
then the whole trajectory `u ↦ Φ* (u, x)`, `u ∈ Icc (min 0 t) (max 0 t)`, avoids `K` (hence `B`),
and the level law holds.

## The proof (no monotonicity is needed)

Suppose `t ≥ 0` and the trajectory meets `K`.  Let `w₀` be the *first* such time (the infimum of
`S = {w ∈ Icc 0 t | Φ (w,x) ∈ K}`, which lies in `S` because `S` is closed).  Below `w₀` the
trajectory is `K`-free, so the level law holds there; passing to the limit gives
`f (Φ (w₀,x)) = f x + w₀`, and `0 ≤ w₀ ≤ t` puts that value in `[a,b]`, contradicting
`f (Φ (w₀,x)) ∉ [a,b]`.  For `t ≤ 0` the same argument is run from the *last* entry (the supremum of
`S`) with the level law applied to the journey ending at `x`.
-/

namespace Work.Drive.N2

open Set Filter
open scoped Topology

variable {M : Type*} [TopologicalSpace M]

/-- **The forward case**: the trajectory from `x` up to time `t ≥ 0` avoids `K`. -/
theorem avoid_Icc_of_band {f : M → ℝ} {Φ : ℝ × M → M} {B K : Set M} {a b : ℝ}
    (hBK : B ⊆ K) (hKcl : IsClosed K) (hKval : ∀ y ∈ K, f y ∉ Set.Icc a b)
    (hf : Continuous f) (hΦcont : ∀ x : M, Continuous fun t : ℝ => Φ (t, x))
    (hΦ0 : ∀ y : M, Φ (0, y) = y)
    (hlevel : ∀ (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), Φ (u, y) ∉ B) → f (Φ (t, y)) = f y + t)
    {x : M} (hx : f x ∈ Set.Icc a b) {t : ℝ} (hxt : f x + t ∈ Set.Icc a b) :
    ∀ u ∈ Set.Icc (0:ℝ) t, Φ (u, x) ∉ K := by
  have hgcont : Continuous fun w : ℝ => f (Φ (w, x)) := hf.comp (hΦcont x)
  by_contra hbad
  push_neg at hbad
  obtain ⟨u, hu, hKu⟩ := hbad
  set S : Set ℝ := {w | w ∈ Set.Icc (0:ℝ) t ∧ Φ (w, x) ∈ K} with hS
  have hSne : S.Nonempty := ⟨u, hu, hKu⟩
  have hScl : IsClosed S := isClosed_Icc.inter (hKcl.preimage (hΦcont x))
  have hSbd : BddBelow S := ⟨0, fun w hw => hw.1.1⟩
  set w₀ : ℝ := sInf S with hw₀
  have hw₀S : w₀ ∈ S := hScl.csInf_mem hSne hSbd
  have hw₀0 : 0 < w₀ := by
    rcases eq_or_lt_of_le hw₀S.1.1 with h | h
    · exfalso
      have hmem : Φ (w₀, x) ∈ K := hw₀S.2
      rw [← h] at hmem
      rw [hΦ0] at hmem
      exact hKval x hmem hx
    · exact h
  have hw₀t : w₀ ≤ t := hw₀S.1.2
  -- the level law below `w₀`
  have hle : ∀ w : ℝ, 0 ≤ w → w < w₀ → f (Φ (w, x)) = f x + w := by
    intro w hw0 hww
    refine hlevel x w (fun u hu => ?_)
    have h2 : u ≤ w := by simpa [max_eq_right hw0] using hu.2
    have huI : u ∈ Set.Icc (0:ℝ) t :=
      ⟨by simpa [min_eq_left hw0] using hu.1, by linarith [h2, hww, hw₀t]⟩
    have huS : u ∉ S := by
      intro hmem
      have h3 : sInf S ≤ u := csInf_le hSbd hmem
      rw [← hw₀] at h3
      linarith
    exact fun hc => huS ⟨huI, hBK hc⟩
  -- the limit at `w₀`
  have hIoo : Set.Ioo (0:ℝ) w₀ ∈ 𝓝[Set.Iio w₀] w₀ := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    exact ⟨Set.Ioi 0, isOpen_Ioi.mem_nhds hw₀0, by
      rintro y ⟨hy1, hy2⟩
      exact ⟨hy1, hy2⟩⟩
  have hlim : f (Φ (w₀, x)) = f x + w₀ := by
    have h1 : Tendsto (fun w : ℝ => f (Φ (w, x))) (𝓝[Set.Iio w₀] w₀) (𝓝 (f (Φ (w₀, x)))) :=
      (hgcont.tendsto w₀).mono_left inf_le_left
    have h2 : Tendsto (fun w : ℝ => f (Φ (w, x))) (𝓝[Set.Iio w₀] w₀) (𝓝 (f x + w₀)) := by
      have hbase : Tendsto (fun w : ℝ => f x + w) (𝓝 w₀) (𝓝 (f x + w₀)) := by
        simpa using (tendsto_const_nhds.add tendsto_id)
      refine Tendsto.congr' ?_ (hbase.mono_left inf_le_left)
      filter_upwards [hIoo] with w hw
      exact (hle w (le_of_lt hw.1) hw.2).symm
    exact tendsto_nhds_unique' (l := 𝓝[Set.Iio w₀] w₀) (nhdsLT_neBot w₀) h1 h2
  have hval : f (Φ (w₀, x)) ∈ Set.Icc a b :=
    ⟨by rw [hlim]; linarith [hx.1],
     by rw [hlim]; linarith [hxt.2, hw₀t]⟩
  exact hKval (Φ (w₀, x)) hw₀S.2 hval

/-- **The backward case**: the trajectory from `x` down to time `t ≤ 0` avoids `K`. -/
theorem avoid_Icc_of_band' {f : M → ℝ} {Φ : ℝ × M → M} {B K : Set M} {a b : ℝ}
    (hBK : B ⊆ K) (hKcl : IsClosed K) (hKval : ∀ y ∈ K, f y ∉ Set.Icc a b)
    (hf : Continuous f) (hΦcont : ∀ x : M, Continuous fun t : ℝ => Φ (t, x))
    (hΦ0 : ∀ y : M, Φ (0, y) = y)
    (hcomp : ∀ (s t : ℝ) (y : M), Φ (s, Φ (t, y)) = Φ (s + t, y))
    (hlevel : ∀ (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), Φ (u, y) ∉ B) → f (Φ (t, y)) = f y + t)
    {x : M} (hx : f x ∈ Set.Icc a b) {t : ℝ} (ht : t ≤ 0) (hxt : f x + t ∈ Set.Icc a b) :
    ∀ u ∈ Set.Icc t 0, Φ (u, x) ∉ K := by
  have hgcont : Continuous fun w : ℝ => f (Φ (w, x)) := hf.comp (hΦcont x)
  by_contra hbad
  push_neg at hbad
  obtain ⟨u, hu, hKu⟩ := hbad
  set S : Set ℝ := {w | w ∈ Set.Icc t (0:ℝ) ∧ Φ (w, x) ∈ K} with hS
  have hSne : S.Nonempty := ⟨u, hu, hKu⟩
  have hScl : IsClosed S := isClosed_Icc.inter (hKcl.preimage (hΦcont x))
  have hSbd : BddAbove S := ⟨0, fun w hw => hw.1.2⟩
  set w₁ : ℝ := sSup S with hw₁
  have hw₁S : w₁ ∈ S := hScl.csSup_mem hSne hSbd
  have hw₁0 : w₁ < 0 := by
    rcases eq_or_lt_of_le hw₁S.1.2 with h | h
    · exfalso
      have hmem : Φ (w₁, x) ∈ K := hw₁S.2
      rw [h] at hmem
      rw [hΦ0] at hmem
      exact hKval x hmem hx
    · exact h
  have hw₁t : t ≤ w₁ := hw₁S.1.1
  -- the level law above `w₁`
  have hle : ∀ w : ℝ, w₁ < w → w ≤ 0 → f (Φ (w, x)) = f x + w := by
    intro w hw hw0
    have hwI : w ∈ Set.Icc t (0:ℝ) := ⟨by linarith [hw₁t, hw.le], hw0⟩
    have hfree : ∀ z ∈ Set.Icc (min 0 (-w)) (max 0 (-w)), Φ (z, Φ (w, x)) ∉ B := by
      intro z hz
      have hz2 : w + z ≤ 0 := by
        have hzle : z ≤ max 0 (-w) := hz.2
        rw [max_eq_right (by linarith : -w ≥ 0)] at hzle
        linarith
      have hzge0 : 0 ≤ z := by
        have hzge : min 0 (-w) ≤ z := hz.1
        rwa [min_eq_left (by linarith : (0:ℝ) ≤ -w)] at hzge
      have hznotS : w + z ∉ S := by
        intro hmem
        have h4 : w + z ≤ sSup S := le_csSup hSbd hmem
        rw [← hw₁] at h4
        linarith
      have hzI : w + z ∈ Set.Icc t (0:ℝ) :=
        ⟨by linarith [hw₁t, hw.le, hzge0], hz2⟩
      have hcomp' : Φ (z, Φ (w, x)) = Φ (w + z, x) := by
        rw [show w + z = z + w by ring]; exact hcomp z w x
      rw [hcomp']
      exact fun hc => hznotS ⟨hzI, hBK hc⟩
    have h := hlevel (Φ (w, x)) (-w) hfree
    have h0 : Φ (-w, Φ (w, x)) = x := by
      rw [show -w = (-w : ℝ) by rfl, hcomp, show -w + w = 0 by ring, hΦ0]
    rw [h0] at h
    linarith
  -- the limit at `w₁`
  have hIoo : Set.Ioo w₁ (0:ℝ) ∈ 𝓝[Set.Ioi w₁] w₁ := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    exact ⟨Set.Iio 0, isOpen_Iio.mem_nhds hw₁0, by
      rintro y ⟨hy1, hy2⟩
      exact ⟨hy2, hy1⟩⟩
  have hlim : f (Φ (w₁, x)) = f x + w₁ := by
    have h1 : Tendsto (fun w : ℝ => f (Φ (w, x))) (𝓝[Set.Ioi w₁] w₁) (𝓝 (f (Φ (w₁, x)))) :=
      (hgcont.tendsto w₁).mono_left inf_le_left
    have h2 : Tendsto (fun w : ℝ => f (Φ (w, x))) (𝓝[Set.Ioi w₁] w₁) (𝓝 (f x + w₁)) := by
      have hbase : Tendsto (fun w : ℝ => f x + w) (𝓝 w₁) (𝓝 (f x + w₁)) := by
        simpa using (tendsto_const_nhds.add tendsto_id)
      refine Tendsto.congr' ?_ (hbase.mono_left inf_le_left)
      filter_upwards [hIoo] with w hw
      exact (hle w hw.1 (le_of_lt hw.2)).symm
    exact tendsto_nhds_unique' (l := 𝓝[Set.Ioi w₁] w₁) (nhdsGT_neBot w₁) h1 h2
  have hval : f (Φ (w₁, x)) ∈ Set.Icc a b :=
    ⟨by rw [hlim]; linarith [hxt.1, hw₁t],
     by rw [hlim]; linarith [hx.2, hw₁S.1.2]⟩
  exact hKval (Φ (w₁, x)) hw₁S.2 hval

/-- **`bandLaw`: unit speed on a ball-free band.**

`B` is the union of the open model balls (the set of `hlevel`), `K` a closed set containing `B` whose
`f`-values avoid `Icc a b`.  If `x` has a band value and `f x + t` has a band value, then the whole
trajectory between the two times avoids `K` and the flow advances `f` at unit speed. -/
theorem bandLaw {f : M → ℝ} {Φ : ℝ × M → M} {B K : Set M} {a b : ℝ}
    (hBK : B ⊆ K) (hKcl : IsClosed K) (hKval : ∀ y ∈ K, f y ∉ Set.Icc a b)
    (hf : Continuous f) (hΦcont : ∀ x : M, Continuous fun t : ℝ => Φ (t, x))
    (hΦ0 : ∀ y : M, Φ (0, y) = y)
    (hcomp : ∀ (s t : ℝ) (y : M), Φ (s, Φ (t, y)) = Φ (s + t, y))
    (hlevel : ∀ (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), Φ (u, y) ∉ B) → f (Φ (t, y)) = f y + t)
    {x : M} (hx : f x ∈ Set.Icc a b) {t : ℝ} (hxt : f x + t ∈ Set.Icc a b) :
    (∀ u ∈ Set.Icc (min 0 t) (max 0 t), Φ (u, x) ∉ K) ∧ f (Φ (t, x)) = f x + t := by
  have havoid : ∀ u ∈ Set.Icc (min 0 t) (max 0 t), Φ (u, x) ∉ K := by
    rcases le_total 0 t with ht | ht
    · have h := avoid_Icc_of_band hBK hKcl hKval hf hΦcont hΦ0 hlevel hx hxt
      simpa [min_eq_left ht, max_eq_right ht] using h
    · have h := avoid_Icc_of_band' hBK hKcl hKval hf hΦcont hΦ0 hcomp hlevel hx ht hxt
      simpa [min_eq_right ht, max_eq_left ht] using h
  refine ⟨havoid, ?_⟩
  exact hlevel x t (fun u hu hc => havoid u hu (hBK hc))

end Work.Drive.N2
