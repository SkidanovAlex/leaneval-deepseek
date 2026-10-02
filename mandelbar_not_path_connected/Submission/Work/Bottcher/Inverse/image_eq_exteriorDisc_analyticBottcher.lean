/-
# The image of an analytic Böttcher coordinate is the exterior disc

Let `E = {z : ℂ | 0 < G_c z}` be the escape set (basin of infinity) of the tricorn
`T_c(w) = conj w ^ 2 + c`, and let `φ` be an analytic function on `E` whose modulus is the
exponential of the Green function, `‖φ z‖ = exp (G_c z)`.  Then `φ '' E = {w | 1 < ‖w‖}`.

The proof does not use the tangency hypothesis `φ z / z → 1`; the content is purely
"modulus + analyticity + topology of `E`":

* `E` is nonempty, open and preconnected (`isPreconnected_escapeSet`);
* `φ '' E ⊆ {w | 1 < ‖w‖}` because `‖φ z‖ = exp (G_c z) > 1` on `E`;
* `φ '' E` is **open** (open mapping theorem for a non-constant analytic function on the
  preconnected open set `E`; non-constancy follows from `‖φ z‖ = exp (G_c z)` and
  `G_c (T_c z) = 2 G_c z`);
* `φ '' E` is **closed in `{w | 1 < ‖w‖}`**: a convergent sequence `φ (z n) → w` with
  `‖w‖ > 1` has `G_c (z n) = log ‖φ (z n)‖` bounded, and the sublevel sets of `G_c` are
  bounded (`log_half_le_green`), so a subsequence of `z n` converges to a point `a` with
  `G_c a = log ‖w‖ > 0`, whence `a ∈ E` and `φ a = w`;
* `{w | 1 < ‖w‖}` is preconnected (it is the image of the half-plane `{Re z > 0}` under `exp`).

An open, relatively closed, nonempty subset of a preconnected set is the whole set, and the
claim follows.
-/
import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.Contraction.isPreconnected_escapeSet
import Submission.Work.Escape.continuous_green
import Submission.Work.Escape.log_half_le_green
import Submission.Work.Escape.Mandelbar

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Bottcher.Inverse

open Filter
open LeanEval.ComplexAnalysis (Tantibar)

/-- If the tricorn Green function is bounded by `M` at `z`, then `z` is bounded: off the
escaping region `‖z‖ ≤ max 2 ‖c‖` is already small, and on it `log (‖z‖ / 2) ≤ G_c z ≤ M`
(`log_half_le_green`). -/
theorem norm_le_of_green_le (c : ℂ) {M : ℝ} {z : ℂ} (hz : green c z ≤ M) :
    ‖z‖ ≤ max (max 2 ‖c‖) (2 * Real.exp M) := by
  by_cases hle : ‖z‖ ≤ max 2 ‖c‖
  · exact hle.trans (le_max_left _ _)
  · have h : max 2 ‖c‖ < ‖z‖ := lt_of_not_ge hle
    have hzreg : z ∈ Work.Escape.escapeRegion ‖c‖ := h
    have hlog := Work.Escape.log_half_le_green (Tantibar c) 2 ‖c‖
        (Work.Escape.monicGrowth_Tantibar c) le_rfl hzreg
    have h2 : (2 : ℝ) < ‖z‖ := (le_max_left 2 ‖c‖).trans_lt h
    have hpos : 0 < ‖z‖ / 2 := by linarith
    have hle' : Real.log (‖z‖ / 2) ≤ M := le_trans hlog hz
    have hexp : ‖z‖ / 2 ≤ Real.exp M := (Real.log_le_iff_le_exp hpos).mp hle'
    calc ‖z‖ = 2 * (‖z‖ / 2) := by ring
      _ ≤ 2 * Real.exp M := by linarith
      _ ≤ max (max 2 ‖c‖) (2 * Real.exp M) := le_max_right _ _

/-- The sublevel sets of the tricorn Green function are bounded. -/
theorem isBounded_green_sublevel (c : ℂ) (M : ℝ) :
    Bornology.IsBounded {z : ℂ | green c z ≤ M} :=
  isBounded_iff_forall_norm_le.mpr
    ⟨max (max 2 ‖c‖) (2 * Real.exp M), fun _ hz => norm_le_of_green_le c hz⟩

theorem image_eq_exteriorDisc_analyticBottcher (c : ℂ) (φ : ℂ → ℂ)
    (han : AnalyticOnNhd ℂ φ {z : ℂ | 0 < Work.Bottcher.green c z})
    (hmod : ∀ z : ℂ, 0 < Work.Bottcher.green c z → ‖φ z‖ = Real.exp (Work.Bottcher.green c z))
    (has : Filter.Tendsto (fun z : ℂ => φ z / z) (Filter.cocompact ℂ) (nhds (1 : ℂ))) :
    φ '' {z : ℂ | 0 < Work.Bottcher.green c z} = {w : ℂ | 1 < ‖w‖} := by
  have _has := has
  have hcont : Continuous (fun z : ℂ => green c z) := Work.Escape.continuous_green_Tantibar c
  have hEopen : IsOpen {z : ℂ | 0 < green c z} := isOpen_lt continuous_const hcont
  -- The escape set is nonempty: any sufficiently large point of `ℂ` lies in it.
  have hEne : ({z : ℂ | 0 < green c z}).Nonempty := by
    let K : ℝ := max (max 2 ‖c‖) 2 + 1
    have hKnn : 0 ≤ K := by
      have h2 : (2 : ℝ) ≤ max (max 2 ‖c‖) 2 := le_max_right _ _
      change 0 ≤ max (max 2 ‖c‖) 2 + 1
      linarith
    have hKnorm : ‖(K : ℂ)‖ = K := by
      rw [show ‖(K : ℂ)‖ = |K| from by simp, abs_of_nonneg hKnn]
    have hKgt : max 2 ‖c‖ < K := by
      have h1 : (max 2 ‖c‖ : ℝ) ≤ max (max 2 ‖c‖) 2 := le_max_left _ _
      change max 2 ‖c‖ < max (max 2 ‖c‖) 2 + 1
      linarith
    refine ⟨(K : ℂ), ?_⟩
    have hzreg : (K : ℂ) ∈ Work.Escape.escapeRegion ‖c‖ := by
      rw [Work.Escape.mem_escapeRegion, hKnorm]; exact hKgt
    have hlog := Work.Escape.log_half_le_green (Tantibar c) 2 ‖c‖
        (Work.Escape.monicGrowth_Tantibar c) le_rfl hzreg
    have hpos : 0 < Real.log (‖(K : ℂ)‖ / 2) := by
      apply Real.log_pos
      rw [hKnorm]
      have h2 : (2 : ℝ) < K := by
        have h1 : (2 : ℝ) ≤ max (max 2 ‖c‖) 2 := le_max_right _ _
        change (2 : ℝ) < max (max 2 ‖c‖) 2 + 1
        linarith
      linarith
    exact lt_of_lt_of_le hpos hlog
  -- `φ` is not constant on `E`, by `‖φ z‖ = exp (G_c z)` and `G_c (T_c z) = 2 G_c z`.
  have hnotconst : ¬ ∃ w, ∀ z ∈ {z : ℂ | 0 < green c z}, φ z = w := by
    rintro ⟨k, hk⟩
    obtain ⟨z, hz⟩ := hEne
    have hzp : 0 < green c z := hz
    have hcomp : green c (Tantibar c z) = 2 * green c z :=
      Work.Escape.green_Tantibar_comp c z
    have hTpos : 0 < green c (Tantibar c z) := by rw [hcomp]; linarith
    have hexp : Real.exp (green c z) = Real.exp (green c (Tantibar c z)) := by
      rw [← hmod z hzp, ← hmod (Tantibar c z) hTpos, hk z hz, hk (Tantibar c z) hTpos]
    rw [hcomp] at hexp
    have heq : green c z = 2 * green c z := Real.exp_injective hexp
    linarith
  -- `E` is preconnected, so the open mapping theorem gives openness of `φ '' E`.
  have hpreconn : IsPreconnected {z : ℂ | 0 < green c z} :=
    Work.Bottcher.Contraction.isPreconnected_escapeSet c
  have hopen : IsOpen (φ '' {z : ℂ | 0 < green c z}) := by
    rcases han.is_constant_or_isOpen hpreconn with hc | hop
    · exact absurd hc hnotconst
    · exact hop {z : ℂ | 0 < green c z} (subset_refl _) hEopen
  have hUsub : φ '' {z : ℂ | 0 < green c z} ⊆ {w : ℂ | 1 < ‖w‖} := by
    rintro y ⟨z, hz, rfl⟩
    change 1 < ‖φ z‖
    rw [hmod z hz]
    exact Real.one_lt_exp_iff.mpr hz
  -- `φ '' E` is closed in `{w | 1 < ‖w‖}`.
  have hcl : ∀ w : ℂ, 1 < ‖w‖ → w ∈ closure (φ '' {z : ℂ | 0 < green c z}) →
      w ∈ φ '' {z : ℂ | 0 < green c z} := by
    intro w hw hwcl
    rw [mem_closure_iff_seq_limit] at hwcl
    obtain ⟨u, hu_mem, hu_tend⟩ := hwcl
    simp only [Set.mem_image] at hu_mem
    choose z hzE hzφ using hu_mem
    have hM : 0 < ‖w‖ := lt_trans zero_lt_one hw
    have hge : (fun n => green c (z n)) = fun n => Real.log ‖u n‖ := by
      funext n
      rw [← hzφ n, hmod (z n) (hzE n), Real.log_exp]
    have hglim : Tendsto (fun n => green c (z n)) atTop (nhds (Real.log ‖w‖)) := by
      rw [hge]
      exact (hu_tend.norm).log hM.ne'
    have hbdd : ∀ᶠ n in atTop, green c (z n) ≤ Real.log ‖w‖ + 1 := by
      have hlt : ∀ᶠ n in atTop, green c (z n) < Real.log ‖w‖ + 1 :=
        hglim.eventually (isOpen_Iio.mem_nhds (lt_add_one _))
      exact hlt.mono fun _ hn => le_of_lt hn
    obtain ⟨a, ha_cl, ψ, hψ_mono, hψ_tend⟩ :=
      tendsto_subseq_of_frequently_bounded (isBounded_green_sublevel c (Real.log ‖w‖ + 1))
        hbdd.frequently
    have hSclosed : IsClosed {z : ℂ | green c z ≤ Real.log ‖w‖ + 1} :=
      isClosed_le hcont continuous_const
    rw [hSclosed.closure_eq] at ha_cl
    have hga : green c a = Real.log ‖w‖ := by
      have h1 : Tendsto (fun n => green c (z (ψ n))) atTop (nhds (green c a)) :=
        (hcont.tendsto a).comp hψ_tend
      have h2 : Tendsto (fun n => green c (z (ψ n))) atTop (nhds (Real.log ‖w‖)) :=
        hglim.comp hψ_mono.tendsto_atTop
      exact tendsto_nhds_unique h1 h2
    have haE : 0 < green c a := by rw [hga]; exact Real.log_pos hw
    refine ⟨a, haE, ?_⟩
    have h3 : Tendsto (fun n => φ (z (ψ n))) atTop (nhds (φ a)) :=
      Tendsto.comp ((han a haE).continuousAt) hψ_tend
    have h4 : Tendsto (fun n => φ (z (ψ n))) atTop (nhds w) := by
      have heq : (fun n => φ (z (ψ n))) = fun n => u (ψ n) := by
        funext n; exact hzφ (ψ n)
      rw [heq]
      exact hu_tend.comp hψ_mono.tendsto_atTop
    exact tendsto_nhds_unique h3 h4
  -- `{w | 1 < ‖w‖}` is preconnected, being the image of `{Re z > 0}` under `exp`.
  have hpreconnΩ : IsPreconnected {w : ℂ | 1 < ‖w‖} := by
    have hpre : IsPreconnected {z : ℂ | 0 < z.re} := (convex_halfSpace_re_gt 0).isPreconnected
    have himg : IsPreconnected (Complex.exp '' {z : ℂ | 0 < z.re}) :=
      hpre.image Complex.exp Complex.continuous_exp.continuousOn
    have hset : Complex.exp '' {z : ℂ | 0 < z.re} = {w : ℂ | 1 < ‖w‖} := by
      ext w
      constructor
      · rintro ⟨z, hz, rfl⟩
        change 1 < ‖Complex.exp z‖
        rw [Complex.norm_exp]
        exact Real.one_lt_exp_iff.mpr hz
      · intro hw
        refine ⟨Complex.log w, ?_, Complex.exp_log ?_⟩
        · change 0 < (Complex.log w).re
          rw [Complex.log_re]
          exact Real.log_pos hw
        · intro h; rw [h] at hw; exact absurd hw (by norm_num)
    rwa [hset] at himg
  apply Set.Subset.antisymm hUsub
  intro w hw
  have hVopen : IsOpen ((closure (φ '' {z : ℂ | 0 < green c z}))ᶜ) :=
    isClosed_closure.isOpen_compl
  have hdisj : Disjoint (φ '' {z : ℂ | 0 < green c z})
      ((closure (φ '' {z : ℂ | 0 < green c z}))ᶜ) :=
    Disjoint.mono_right (Set.compl_subset_compl_of_subset subset_closure) disjoint_compl_right
  have hunion : {w : ℂ | 1 < ‖w‖} ⊆ (φ '' {z : ℂ | 0 < green c z}) ∪
      ((closure (φ '' {z : ℂ | 0 < green c z}))ᶜ) := by
    intro y hy
    by_cases hy' : y ∈ closure (φ '' {z : ℂ | 0 < green c z})
    · exact Or.inl (hcl y hy hy')
    · exact Or.inr hy'
  rcases hpreconnΩ.subset_or_subset hopen hVopen hdisj hunion with hsub | hsub
  · exact hsub hw
  · exfalso
    obtain ⟨z0, hz0⟩ := hEne
    have hz0img : φ z0 ∈ φ '' {z : ℂ | 0 < green c z} := ⟨z0, hz0, rfl⟩
    have hout := hsub (hUsub hz0img)
    rw [Set.mem_compl_iff] at hout
    exact hout (subset_closure hz0img)

end Work.Bottcher.Inverse
