import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS.StrongEps.EpsWPLim.Basic
import Submission.Work.FTS_RegExport.RXR1.classC_sub_hyp
import Submission.Work.FTS_RegExport.RXT.Slots.v2_theta_sup_uniform
import Submission.Work.Stability.ZcutSmoothCompact
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.StrongEps.EpsWPLim.gRHSStep =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsWPLim

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **The pointwise limit of `gRHS`.**  All the convergences required by the four blocks of
`gRHS`, with the two modulation constants converging separately. -/
theorem gRHS_tendsto {α : ℝ} {μ : ℕ → ℝ} {μl : ℝ} {lam : ℕ → ℝ} {laml : ℝ}
    {F : ℕ → Fn} {Fl : Fn} {Ψ : ℕ → Fn} {Ψl : Fn} {w : ℕ → Fn} {wl : Fn} {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hμ : Tendsto μ Filter.atTop (nhds μl))
    (hlam : Tendsto lam Filter.atTop (nhds laml))
    (hF : ∀ j i : ℕ, j + i ≤ 1 →
      Tendsto (fun n : ℕ => Work.Spaces.mixed j i (F n) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i Fl z θ)))
    (hw : ∀ j i : ℕ, j + i ≤ 1 →
      Tendsto (fun n : ℕ => Work.Spaces.mixed j i (w n) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i wl z θ)))
    (hTil : ∀ j i : ℕ, j + i ≤ 1 →
      Tendsto (fun n : ℕ => Work.Spaces.mixed j i
          (Work.Construction.PhiTil α (F n) (Ψ n)) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i (Work.Construction.PhiTil α Fl Ψl) z θ)))
    (hFK : Tendsto (fun n : ℕ => Work.Construction.FK (F n) z) Filter.atTop
      (nhds (Work.Construction.FK Fl z)))
    (hlw : ∀ z' ∈ Work.Spaces.Iz, Tendsto (fun n : ℕ => Work.Construction.L12 (w n) z')
      Filter.atTop (nhds (Work.Construction.L12 wl z')))
    (hmubar : Tendsto (fun n : ℕ => Work.Construction.mubar
      (Work.Construction.N0 α (F n) (w n)) (Work.Construction.N α (F n) (Ψ n))) Filter.atTop
      (nhds (Work.Construction.mubar (Work.Construction.N0 α Fl wl)
        (Work.Construction.N α Fl Ψl)))) :
    Tendsto (fun n : ℕ => Work.Construction.gRHS α (μ n) (lam n) (F n) (Ψ n) (w n) z θ)
      Filter.atTop (nhds (Work.Construction.gRHS α μl laml Fl Ψl wl z θ)) := by
  -- the three `μ`-free blocks
  have hN0 := Work.FTS.StrongEps.N0_tendsto (α := α) (F := F) (Flim := Fl) (w := w)
    (wlim := wl) (z := z) (θ := θ) (le_of_lt hz) hF hw hlw
  have hN := N_tendsto_of_PhiTil (α := α) (F := F) (Fl := Fl) (Ψ := Ψ) (Ψl := Ψl)
    (z := z) (θ := θ) hz hθ hF hFK hTil
  have hmb : Tendsto (fun n : ℕ => -(Work.Construction.mubar
      (Work.Construction.N0 α (F n) (w n)) (Work.Construction.N α (F n) (Ψ n)))
        * Work.Construction.AK α z θ) Filter.atTop
      (nhds (-(Work.Construction.mubar (Work.Construction.N0 α Fl wl)
        (Work.Construction.N α Fl Ψl)) * Work.Construction.AK α z θ)) :=
    (hmubar.neg.mul tendsto_const_nhds)
  -- the `Nstar` block
  have hw0 : Tendsto (fun n : ℕ => w n z θ) Filter.atTop (nhds (wl z θ)) := by
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero]
      using hw 0 0 (by norm_num)
  have hDz : Tendsto (fun n : ℕ => Work.Spaces.Dz (w n) z θ) Filter.atTop
      (nhds (Work.Spaces.Dz wl z θ)) := by
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
      Work.Spaces.DthIter_zero] using hw 1 0 (by norm_num)
  have hcoef : Tendsto (fun n : ℕ => μ n + lam n + μ n * lam n) Filter.atTop
      (nhds (μl + laml + μl * laml)) :=
    (hμ.add hlam).add (hμ.mul hlam)
  have hNs : Tendsto (fun n : ℕ => Work.Construction.Nstar (μ n) (lam n) (w n) z θ) Filter.atTop
      (nhds (Work.Construction.Nstar μl laml wl z θ)) := by
    have h : (fun n : ℕ => Work.Construction.Nstar (μ n) (lam n) (w n) z θ)
        = fun n : ℕ => -(μ n) * w n z θ
            - (μ n + lam n + μ n * lam n) * Work.Spaces.Dz (w n) z θ := by
      funext n
      simp only [Work.Construction.Nstar]
    rw [h]
    exact (hμ.neg.mul hw0).sub (hcoef.mul hDz)
  -- assemble
  have hfun : (fun n : ℕ => Work.Construction.gRHS α (μ n) (lam n) (F n) (Ψ n) (w n) z θ)
      = fun n : ℕ => -(Work.Construction.mubar (Work.Construction.N0 α (F n) (w n))
            (Work.Construction.N α (F n) (Ψ n))) * Work.Construction.AK α z θ
          + Work.Construction.N0 α (F n) (w n) z θ
          + Work.Construction.N α (F n) (Ψ n) z θ
          + Work.Construction.Nstar (μ n) (lam n) (w n) z θ := by
    funext n
    simp only [Work.Construction.gRHS]
  have hlim : Work.Construction.gRHS α μl laml Fl Ψl wl z θ
      = -(Work.Construction.mubar (Work.Construction.N0 α Fl wl)
            (Work.Construction.N α Fl Ψl)) * Work.Construction.AK α z θ
          + Work.Construction.N0 α Fl wl z θ
          + Work.Construction.N α Fl Ψl z θ
          + Work.Construction.Nstar μl laml wl z θ := by
    simp only [Work.Construction.gRHS]
  rw [hfun, hlim]
  exact ((hmb.add hN0).add hN).add hNs

end Work.FTS.StrongEps.EpsWPLim
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.StepFixedAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Auxiliary real-analysis lemmas for the corrected integrated cone step (`step_integrated_nonneg`)

Helpers used by `Submission/Work/FTS_RegExport/RXT/step_integrated_fix.lean`:

* uniform continuity, uniform in the index, of a finite family on a compact set, and of the
  sum `p ↦ ∑ k, |f k p|` (`rxtStep_exists_uniform_family`, `rxtStep_exists_uniform_sum`),
  with `rxtStep_exists_delta_fin` supplying the finite minimum of the moduli;
* the two-point mean value theorem in slope form valid also at `x = y`
  (`rxtStep_exists_slope_point`);
* elementary order lemmas (`rxtStep_abs_min_max_le`, `rxtStep_le_succ_mul`,
  `rxtStep_abs_le_succ_mul`, `rxtStep_abs_sub_le_abs_of_mem_Icc`,
  `rxtStep_abs_le_max_of_mem_Icc`, `rxtStep_dist_three_le`, `rxtStep_abs_add4_le`);
* `rxtStep_correction_le`: replacing a frozen value of `F` by its value at a point inside an
  interval integral.
-/

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS_RegExport.RXT

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## Elementary helpers -/


/-- If `x, y ∈ [a,b]` then `|x - y| ≤ |b - a|`. -/
lemma rxtStep_abs_sub_le_abs_of_mem_Icc {x y a b : ℝ} (hx : x ∈ Set.Icc a b)
    (hy : y ∈ Set.Icc a b) : |x - y| ≤ |b - a| := by
  have hab : a ≤ b := le_trans hy.1 hy.2
  have h : |b - a| = b - a := abs_of_nonneg (by linarith)
  rw [h, abs_sub_le_iff]
  exact ⟨by linarith [hx.2, hy.1], by linarith [hx.1, hy.2]⟩

/-- `h ≤ (A+1) * h` for `A, h ≥ 0`. -/
lemma rxtStep_le_succ_mul {A h : ℝ} (hA : 0 ≤ A) (hh : 0 ≤ h) : h ≤ (A + 1) * h := by
  have h1 : (0:ℝ) ≤ A * h := mul_nonneg hA hh
  have h2 : (A + 1) * h = A * h + h := by ring
  linarith [h1, h2.le]

/-- `|x| ≤ A * h ≤ (A+1) * h` for `A, h ≥ 0`. -/
lemma rxtStep_abs_le_succ_mul {x A h : ℝ} (hx : |x| ≤ A * h) (hA : 0 ≤ A) (hh : 0 ≤ h) :
    |x| ≤ (A + 1) * h := by
  have h2 : (A + 1) * h = A * h + h := by ring
  linarith [hx, hh, h2.le]

/-- `x ∈ [min a b, max a b]` with `|a| ≤ C` and `|b| ≤ C` gives `|x| ≤ C`. -/
lemma rxtStep_abs_min_max_le {x a b C : ℝ} (hx : x ∈ Set.Icc (min a b) (max a b))
    (ha : |a| ≤ C) (hb : |b| ≤ C) : |x| ≤ C := by
  refine abs_le.mpr ⟨?_, ?_⟩
  · have hmin : min a b ≤ x := hx.1
    have h1 : -C ≤ min a b :=
      le_min (by linarith [neg_abs_le a, ha]) (by linarith [neg_abs_le b, hb])
    linarith
  · have hmax : x ≤ max a b := hx.2
    have h2 : max a b ≤ C :=
      max_le (by linarith [le_abs_self a, ha]) (by linarith [le_abs_self b, hb])
    linarith

/-- The sup-distance of two triples, dominated componentwise. -/
lemma rxtStep_dist_three_le {a b c a' b' c' θ : ℝ} (hab : |a - a'| ≤ θ) (hbc : |b - b'| ≤ θ)
    (hcc : |c - c'| ≤ θ) : dist (a, (b, c)) (a', (b', c')) ≤ θ := by
  rw [Prod.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq]
  exact max_le hab (max_le hbc hcc)

/-- The two-point mean value theorem in slope form, valid also at `x = y`. -/
lemma rxtStep_exists_slope_point {g g' : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (g' x) x)
    (x y : ℝ) :
    ∃ c ∈ Set.Icc (min x y) (max x y), g y - g x = (y - x) * g' c := by
  have hcont : ∀ u v : ℝ, ContinuousOn g (Set.Icc u v) := fun u v =>
    (continuous_iff_continuousAt.mpr fun z => (hg z).continuousAt).continuousOn
  rcases lt_trichotomy x y with h | h | h
  · obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope g g' h (hcont x y) (fun z _ => hg z)
    refine ⟨c, ?_, ?_⟩
    · rw [min_eq_left h.le, max_eq_right h.le]
      exact ⟨hc.1.le, hc.2.le⟩
    · rw [hceq]; field_simp
  · subst h
    exact ⟨x, by simp, by simp⟩
  · obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope g g' h (hcont y x) (fun z _ => hg z)
    refine ⟨c, ?_, ?_⟩
    · rw [min_eq_right h.le, max_eq_left h.le]
      exact ⟨hc.1.le, hc.2.le⟩
    · rw [hceq]; field_simp; ring

/-- A finite family of positive numbers has a positive lower bound. -/
lemma rxtStep_exists_delta_fin {n : ℕ} (d : Fin n → ℝ) (hd : ∀ k, 0 < d k) :
    ∃ δ > 0, ∀ k, δ ≤ d k := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact ⟨1, one_pos, fun k => Fin.elim0 k⟩
  · have hn' : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    refine ⟨Finset.univ.inf' Finset.univ_nonempty d, ?_,
      fun k => Finset.inf'_le d (Finset.mem_univ k)⟩
    exact (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun k _ => hd k)

/-- Uniform continuity, uniform in the index, of a finite family continuous on a compact set. -/
lemma rxtStep_exists_uniform_family {n : ℕ} {f : Fin n → ℝ → ℝ → ℝ → ℝ}
    {K : Set (ℝ × ℝ × ℝ)} (hK : IsCompact K) {η : ℝ} (hη : 0 < η)
    (hf : ∀ k, ContinuousOn (fun p : ℝ × ℝ × ℝ => f k p.1 p.2.1 p.2.2) K) :
    ∃ δ > 0, ∀ p ∈ K, ∀ q ∈ K, dist p q < δ →
      ∀ k, |f k p.1 p.2.1 p.2.2 - f k q.1 q.2.1 q.2.2| < η := by
  have hδk : ∀ k, ∃ δ > 0, ∀ p ∈ K, ∀ q ∈ K, dist p q < δ →
      |f k p.1 p.2.1 p.2.2 - f k q.1 q.2.1 q.2.2| < η := by
    intro k
    obtain ⟨δ, hδ, hδ'⟩ :=
      (Metric.uniformContinuousOn_iff.mp (hK.uniformContinuousOn_of_continuous (hf k))) η hη
    exact ⟨δ, hδ, fun p hp q hq hpq => by
      have h := hδ' p hp q hq hpq
      rwa [Real.dist_eq] at h⟩
  choose d hd0 hd using hδk
  obtain ⟨δ, hδ0, hδle⟩ := rxtStep_exists_delta_fin d hd0
  exact ⟨δ, hδ0, fun p hp q hq hpq k => hd k p hp q hq (lt_of_lt_of_le hpq (hδle k))⟩

/-- Uniform continuity of `p ↦ ∑ k, |f k p|` on a compact set. -/
lemma rxtStep_exists_uniform_sum {n : ℕ} {f : Fin n → ℝ → ℝ → ℝ → ℝ}
    {K : Set (ℝ × ℝ × ℝ)} (hK : IsCompact K) {η : ℝ} (hη : 0 < η)
    (hf : ∀ k, ContinuousOn (fun p : ℝ × ℝ × ℝ => f k p.1 p.2.1 p.2.2) K) :
    ∃ δ > 0, ∀ p ∈ K, ∀ q ∈ K, dist p q < δ →
      |(∑ k, |f k p.1 p.2.1 p.2.2|) - (∑ k, |f k q.1 q.2.1 q.2.2|)| < η := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ × ℝ => ∑ k, |f k p.1 p.2.1 p.2.2|) K :=
    continuousOn_finset_sum Finset.univ (fun k _ => (hf k).abs)
  obtain ⟨δ, hδ, hδ'⟩ :=
    (Metric.uniformContinuousOn_iff.mp (hK.uniformContinuousOn_of_continuous hcont)) η hη
  exact ⟨δ, hδ, fun p hp q hq hpq => by
    have h := hδ' p hp q hq hpq
    rwa [Real.dist_eq] at h⟩

/-- `|a + b + c + d| ≤ |a| + |b| + |c| + |d|`. -/
lemma rxtStep_abs_add4_le (a b c d : ℝ) :
    |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  have h1 := abs_add_le (a + b + c) d
  have h2 := abs_add_le (a + b) c
  have h3 := abs_add_le a b
  linarith

/-- Replacing the frozen value of `F` by its value at a point: if `a` is continuous on
`[l,u]`, `F` is continuous on `[l,u]`, `|a| ≤ A` and `|c - F| ≤ η` there, then
`|(∫ a) * c - ∫ a * F| ≤ A * η * (u - l)`. -/
lemma rxtStep_correction_le {a F : ℝ → ℝ} {l u c A η : ℝ} (hlu : l ≤ u)
    (hac : ContinuousOn a (Set.uIcc l u)) (hFc : ContinuousOn F (Set.uIcc l u))
    (ha : ∀ x ∈ Set.Icc l u, |a x| ≤ A) (hΔ : ∀ x ∈ Set.Icc l u, |c - F x| ≤ η)
    (hA0 : 0 ≤ A) (hη0 : 0 ≤ η) :
    |(∫ x in l..u, a x) * c - ∫ x in l..u, a x * F x| ≤ A * η * (u - l) := by
  have hmulI : IntervalIntegrable (fun x => a x * F x) volume l u :=
    (hac.mul hFc).intervalIntegrable
  have hcI : IntervalIntegrable (fun x => a x * c) volume l u :=
    (hac.mul continuousOn_const).intervalIntegrable
  have h1 : (∫ x in l..u, a x) * c = ∫ x in l..u, a x * c :=
    (intervalIntegral.integral_mul_const c a).symm
  have h2 : (∫ x in l..u, a x * c) - (∫ x in l..u, a x * F x)
      = ∫ x in l..u, a x * (c - F x) := by
    rw [← intervalIntegral.integral_sub hcI hmulI]
    exact intervalIntegral.integral_congr (fun x _ => by ring)
  rw [h1, h2]
  calc |∫ x in l..u, a x * (c - F x)| ≤ ∫ x in l..u, |a x * (c - F x)| :=
        intervalIntegral.abs_integral_le_integral_abs hlu
    _ ≤ ∫ x in l..u, A * η := by
        refine intervalIntegral.integral_mono_on hlu ((hac.mul (continuousOn_const.sub hFc)).intervalIntegrable).abs
          intervalIntegrable_const ?_
        intro x hx
        rw [abs_mul]
        exact mul_le_mul (ha x hx) (hΔ x hx) (abs_nonneg _) hA0
    _ = A * η * (u - l) := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring

end Work.FTS_RegExport.RXT
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.slice_tau_modulus_weighted2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology

namespace Work.FTS_RegExport.RXT.Sys


end Work.FTS_RegExport.RXT.Sys
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.cone_induction =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.cone_induction` (leaf T1 of the RX-T chain)

The abstract **cone maximum principle**: from a one-step backward inequality `ConeStep n φ T A C F`
(whose cone half-widths shrink by `A·h` per time step `h`, with an arbitrarily small slack `ε·h`)
and an initial bound `K₀`, one gets the bound

`|φ k s ψ τ| ≤ exp (2 C τ) * (K₀ + τ F)`

for all components `k`, all points `s ψ` and all `τ ∈ [0,T]`.

Proof.  Fix the target `(s₀,ψ₀,τ₀)`, `τ₀ > 0`, and `η > 0`.  Discretise `[0,τ₀]` with mesh
`h = τ₀/N`, `N` large enough that `h < h₀(η)` and `C h ≤ 1/2`, where `h₀(η)` is the mesh
threshold supplied by `ConeStep` for the slack `η` and the box radius
`R = |s₀| + |ψ₀| + A τ₀ + 1`.  For `k : ℕ` let

`Z k = { supᵢ |φ i s ψ (k h)| : |s - s₀| ≤ A (τ₀ - k h), |ψ - ψ₀| ≤ A (τ₀ - k h) }`

(the level sets over the shrinking cones).  Every element of `Z (k+1)` comes from a point of the
`(k+1)`-cone; `ConeStep` applied at `τ = k h` moves that point back by at most `A h`, landing in
the `k`-cone, and yields, with `M = sSup (Z k)` and `B` the local supremum at the point,

`B ≤ M + h (C B + F) + η h`,   i.e.   `B ≤ (M + h (F+η)) (1 + 2 h C)`,

which is exactly the hypothesis of the scalar recursion `ConeAux.key_step`.  Hence
`sSup (Z k) ≤ Mfun (k h)` for `Mfun t = exp (2 C t) (K₀ + t (F+η))` by induction on `k ≤ N`, and
evaluating at `k = N` (where `N h = τ₀` and the cone has radius `0`) gives the claim with `F + η`.
Finally `η → 0`: the estimate holds for every `η > 0` and its left-hand side is fixed.
-/

noncomputable section

namespace Work.FTS_RegExport.RXT

open ConeAux

theorem cone_induction {n : ℕ} {φ : Fin n → ℝ → ℝ → ℝ → ℝ} {T A C F K₀ : ℝ}
    (hT : 0 < T) (hA : 0 ≤ A) (hC : 0 ≤ C) (hF : 0 ≤ F) (hK₀ : 0 ≤ K₀)
    (hcont : ∀ k s ψ, ContinuousOn (fun τ => φ k s ψ τ) (Set.Icc 0 T))
    (h0 : ∀ k s ψ, |φ k s ψ 0| ≤ K₀)
    (hstep : Work.FTS.RegExportIface.RXT.ConeStep n φ T A C F) :
    ∀ k s ψ, ∀ τ ∈ Set.Icc (0:ℝ) T, |φ k s ψ τ| ≤ Real.exp (2 * C * τ) * (K₀ + τ * F) := by
  intro k₀ s₀ ψ₀ τ₀ hτ₀
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact Fin.elim0 k₀
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rcases eq_or_lt_of_le hτ₀.1 with h0τ | hpos
  · rw [← h0τ]
    simpa using h0 k₀ s₀ ψ₀
  suffices hmain : ∀ η : ℝ, 0 < η →
      |φ k₀ s₀ ψ₀ τ₀| ≤ Real.exp (2 * C * τ₀) * (K₀ + τ₀ * (F + η)) by
    have hE : 0 < Real.exp (2 * C * τ₀) := Real.exp_pos _
    refine le_of_forall_pos_le_add (fun ε hε => ?_)
    have hden : 0 < Real.exp (2 * C * τ₀) * τ₀ := mul_pos hE hpos
    have h1 := hmain (ε / (Real.exp (2 * C * τ₀) * τ₀)) (div_pos hε hden)
    have halg : Real.exp (2 * C * τ₀) *
        (K₀ + τ₀ * (F + ε / (Real.exp (2 * C * τ₀) * τ₀)))
        = Real.exp (2 * C * τ₀) * (K₀ + τ₀ * F) + ε := by
      field_simp
      ring
    rw [halg] at h1
    linarith
  intro η hη
  have hFη : 0 ≤ F + η := by linarith
  -- the radius of the box on which the step hypothesis is invoked
  set Rb : ℝ := |s₀| + |ψ₀| + A * τ₀ + 1 with hRbdef
  obtain ⟨h₁, h₁pos, hstep₁⟩ := hstep Rb η hη
  -- the mesh
  obtain ⟨N, hNlt⟩ := exists_nat_gt (max (τ₀ / h₁) (2 * C * τ₀))
  have hNpos : (0 : ℝ) < (N : ℝ) :=
    lt_of_lt_of_le (lt_of_lt_of_le (div_pos hpos h₁pos) (le_max_left _ _)) hNlt.le
  set h : ℝ := τ₀ / (N : ℝ) with hhh
  have hhpos : 0 < h := div_pos hpos hNpos
  have hNh : (N : ℝ) * h = τ₀ := by rw [hhh]; field_simp
  have ht_eq : ∀ k : ℕ, ((k + 1 : ℕ) : ℝ) * h = (k : ℝ) * h + h := by
    intro k; push_cast; ring
  have hh_lt : h < h₁ := by
    have h2 : τ₀ / h₁ < (N : ℝ) := lt_of_le_of_lt (le_max_left _ _) hNlt
    have h3 : τ₀ < (N : ℝ) * h₁ := (div_lt_iff₀ h₁pos).mp h2
    rw [hhh, div_lt_iff₀ hNpos]
    linarith
  have hCh : C * h ≤ 1 / 2 := by
    have h2 : 2 * C * τ₀ < (N : ℝ) := lt_of_le_of_lt (le_max_right _ _) hNlt
    rw [hhh, show C * (τ₀ / (N : ℝ)) = (C * τ₀) / (N : ℝ) by ring, div_le_iff₀ hNpos]
    linarith
  -- the level sets of the shrinking cones
  let Mfun : ℝ → ℝ := fun t => Real.exp (2 * C * t) * (K₀ + t * (F + η))
  have hMfun : ∀ t : ℝ, Mfun t = Real.exp (2 * C * t) * (K₀ + t * (F + η)) := fun t => rfl
  let Z : ℕ → Set ℝ := fun k => {x : ℝ | ∃ s₁ ψ₁ : ℝ,
      |s₁ - s₀| ≤ A * (τ₀ - (k : ℝ) * h) ∧ |ψ₁ - ψ₀| ≤ A * (τ₀ - (k : ℝ) * h) ∧
      x = (Finset.univ : Finset (Fin n)).sup' Finset.univ_nonempty
            (fun i : Fin n => |φ i s₁ ψ₁ ((k : ℝ) * h)|)}
  have ht_le : ∀ k : ℕ, k ≤ N → (k : ℝ) * h ≤ τ₀ := by
    intro k hk
    calc (k : ℝ) * h ≤ (N : ℝ) * h :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hhpos.le
      _ = τ₀ := hNh
  have hZne : ∀ k : ℕ, k ≤ N → (Z k).Nonempty := by
    intro k hk
    refine ⟨_, s₀, ψ₀, ?_, ?_, rfl⟩
    · rw [sub_self, abs_zero]
      exact mul_nonneg hA (by linarith [ht_le k hk])
    · rw [sub_self, abs_zero]
      exact mul_nonneg hA (by linarith [ht_le k hk])
  -- the induction on the level index
  have hkey : ∀ k : ℕ, k ≤ N → BddAbove (Z k) ∧ sSup (Z k) ≤ Mfun ((k : ℝ) * h) := by
    intro k
    induction k with
    | zero =>
      intro _
      have hbk : ∀ x ∈ Z 0, x ≤ K₀ := by
        intro x hx
        obtain ⟨s₁, ψ₁, -, -, rfl⟩ := hx
        refine Finset.sup'_le Finset.univ_nonempty _ (fun i _ => ?_)
        simpa using h0 i s₁ ψ₁
      refine ⟨⟨K₀, hbk⟩, ?_⟩
      have hcs := csSup_le (hZne 0 (Nat.zero_le _)) hbk
      simpa [hMfun] using hcs
    | succ k ih =>
      intro hk1
      have hk : k ≤ N := le_trans (Nat.le_succ k) hk1
      obtain ⟨hbk, hsupk⟩ := ih hk
      have hk1_le : ((k + 1 : ℕ) : ℝ) * h ≤ τ₀ := ht_le (k + 1) hk1
      have hkh_le : (k : ℝ) * h ≤ τ₀ - h := by linarith [ht_eq k]
      have hkhT : (k : ℝ) * h < T := by linarith [hτ₀.2, hhpos]
      have hk1T : ((k + 1 : ℕ) : ℝ) * h ≤ T := by linarith [hτ₀.2]
      have hk1nn : 0 ≤ ((k + 1 : ℕ) : ℝ) * h := mul_nonneg (Nat.cast_nonneg _) hhpos.le
      have hb : ∀ x ∈ Z (k + 1), x ≤ Mfun (((k + 1 : ℕ) : ℝ) * h) := by
        intro x hx
        obtain ⟨s₁, ψ₁, hc1, hc2, rfl⟩ := hx
        set x : ℝ := (Finset.univ : Finset (Fin n)).sup' Finset.univ_nonempty
            (fun i : Fin n => |φ i s₁ ψ₁ (((k + 1 : ℕ) : ℝ) * h)|) with hxdef
        have hs1 : |s₁| ≤ Rb := by
          have h1 : |s₁| ≤ |s₁ - s₀| + |s₀| := by
            calc |s₁| = |(s₁ - s₀) + s₀| := by rw [sub_add_cancel]
              _ ≤ |s₁ - s₀| + |s₀| := abs_add_le _ _
          have h2 : A * (τ₀ - ((k + 1 : ℕ) : ℝ) * h) ≤ A * τ₀ :=
            mul_le_mul_of_nonneg_left (by linarith) hA
          rw [hRbdef]
          nlinarith [h1, hc1, h2, abs_nonneg ψ₀]
        have hw1 : |ψ₁| ≤ Rb := by
          have h1 : |ψ₁| ≤ |ψ₁ - ψ₀| + |ψ₀| := by
            calc |ψ₁| = |(ψ₁ - ψ₀) + ψ₀| := by rw [sub_add_cancel]
              _ ≤ |ψ₁ - ψ₀| + |ψ₀| := abs_add_le _ _
          have h2 : A * (τ₀ - ((k + 1 : ℕ) : ℝ) * h) ≤ A * τ₀ :=
            mul_le_mul_of_nonneg_left (by linarith) hA
          rw [hRbdef]
          nlinarith [h1, hc2, h2, abs_nonneg s₀]
        obtain ⟨s', ψ', hs', hw', himp⟩ :=
          hstep₁ ((k : ℝ) * h) ⟨mul_nonneg (Nat.cast_nonneg k) hhpos.le, hkhT⟩ h hhpos
            hh_lt (by rw [← ht_eq k]; exact hk1T) s₁ ψ₁ hs1 hw1
        have hcone_s : |s' - s₀| ≤ A * (τ₀ - (k : ℝ) * h) := by
          have h1 : |s' - s₀| ≤ |s' - s₁| + |s₁ - s₀| := by
            rw [show s' - s₀ = (s' - s₁) + (s₁ - s₀) by ring]
            exact abs_add_le _ _
          have h3 : A * (τ₀ - ((k + 1 : ℕ) : ℝ) * h) + A * h = A * (τ₀ - (k : ℝ) * h) := by
            rw [ht_eq k]; ring
          linarith [h1, hs', hc1, h3]
        have hcone_w : |ψ' - ψ₀| ≤ A * (τ₀ - (k : ℝ) * h) := by
          have h1 : |ψ' - ψ₀| ≤ |ψ' - ψ₁| + |ψ₁ - ψ₀| := by
            rw [show ψ' - ψ₀ = (ψ' - ψ₁) + (ψ₁ - ψ₀) by ring]
            exact abs_add_le _ _
          have h3 : A * (τ₀ - ((k + 1 : ℕ) : ℝ) * h) + A * h = A * (τ₀ - (k : ℝ) * h) := by
            rw [ht_eq k]; ring
          linarith [h1, hw', hc2, h3]
        have hM : ∀ j, |φ j s' ψ' ((k : ℝ) * h)| ≤ sSup (Z k) := by
          intro j
          refine le_trans (Finset.le_sup'
            (fun i : Fin n => |φ i s' ψ' ((k : ℝ) * h)|) (Finset.mem_univ j))
            (le_csSup hbk ?_)
          exact ⟨s', ψ', hcone_s, hcone_w, rfl⟩
        have hB : ∀ j, |φ j s₁ ψ₁ ((k : ℝ) * h + h)| ≤ x := by
          intro j
          rw [← ht_eq k]
          exact Finset.le_sup' (fun i : Fin n => |φ i s₁ ψ₁ (((k + 1 : ℕ) : ℝ) * h)|)
            (Finset.mem_univ j)
        have hconcl := himp (sSup (Z k)) x hM hB
        have hxle : x ≤ sSup (Z k) + h * (C * x + F) + η * h := by
          refine Finset.sup'_le Finset.univ_nonempty _ (fun j _ => ?_)
          rw [ht_eq k]
          exact hconcl j
        have hxle' : x ≤ Real.exp (2 * C * ((k : ℝ) * h)) * (K₀ + ((k : ℝ) * h) * (F + η))
            + h * (F + η) + h * C * x := by
          have h3 : Mfun ((k : ℝ) * h) =
              Real.exp (2 * C * ((k : ℝ) * h)) * (K₀ + ((k : ℝ) * h) * (F + η)) := hMfun _
          have h2 : h * (C * x + F) + η * h = h * (F + η) + h * C * x := by ring
          linarith [hxle, hsupk, h3]
        have hfin := key_step hK₀ hFη hC (mul_nonneg (Nat.cast_nonneg k) hhpos.le) hhpos.le
          hCh hxle'
        rw [ht_eq k]
        simpa [hMfun] using hfin
      refine ⟨⟨Mfun (((k + 1 : ℕ) : ℝ) * h), hb⟩, ?_⟩
      exact csSup_le (hZne (k + 1) hk1) hb
  -- evaluate at the last level
  obtain ⟨hbN, hsupN⟩ := hkey N le_rfl
  have hNh0 : τ₀ - (N : ℝ) * h = 0 := by rw [hNh]; ring
  have hmemN : (Finset.univ : Finset (Fin n)).sup' Finset.univ_nonempty
      (fun i : Fin n => |φ i s₀ ψ₀ τ₀|) ∈ Z N := by
    refine ⟨s₀, ψ₀, ?_, ?_, ?_⟩
    · rw [sub_self, abs_zero, hNh0, mul_zero]
    · rw [sub_self, abs_zero, hNh0, mul_zero]
    · rw [hNh]
  calc |φ k₀ s₀ ψ₀ τ₀|
      ≤ (Finset.univ : Finset (Fin n)).sup' Finset.univ_nonempty
          (fun i : Fin n => |φ i s₀ ψ₀ τ₀|) :=
        Finset.le_sup' (fun i : Fin n => |φ i s₀ ψ₀ τ₀|) (Finset.mem_univ k₀)
    _ ≤ sSup (Z N) := le_csSup hbN hmemN
    _ ≤ Mfun ((N : ℝ) * h) := hsupN
    _ = Real.exp (2 * C * τ₀) * (K₀ + τ₀ * (F + η)) := by rw [hNh]

end Work.FTS_RegExport.RXT
end
end
