import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.GDelta.MetrizableSpace

/-!
# Derivative bounds for radial compositions `y ↦ ψ ‖y‖`

If `ψ : ℝ → ℝ` is smooth, vanishes on `(-∞, 1]`, and has bounded derivatives up to
order `a`, then the `a`-th iterated Fréchet derivative of the radial function
`y ↦ ψ ‖y‖` on an inner product space `E` is bounded.

The proof combines two ingredients.

* `iteratedFDeriv_norm_bound`: the iterated derivatives of the norm are bounded on the
  complement of the unit ball (by positive homogeneity, reducing to the compact unit sphere).
* `contDiff_radial_norm_of_eq_zero_on_Iic`: `y ↦ ψ ‖y‖` is smooth, because `ψ` vanishes in a
  neighbourhood of `0`, hiding the non-differentiability of the norm at the origin.

The Faà di Bruno estimate `norm_iteratedFDerivWithin_comp_le` is then applied on the set
`{y | 1/2 < ‖y‖}`; on the unit ball the function vanishes identically.
-/

namespace Commons.Analysis.Calculus

open Set Filter
open scoped Topology



/-- **Derivative bounds for the norm outside the unit ball.**  For every `n ≥ 1` the `n`-th
iterated derivative of the norm function is bounded on `{x | 1 ≤ ‖x‖}`. -/
theorem iteratedFDeriv_norm_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [ProperSpace E] (n : ℕ) (hn : 1 ≤ n) :
    ∃ K : ℝ, ∀ x : E, 1 ≤ ‖x‖ → ‖iteratedFDeriv ℝ n (fun y : E => ‖y‖) x‖ ≤ K := by
  let N : E → ℝ := fun y => ‖y‖
  let s : Set E := {0}ᶜ
  have hsopen : IsOpen s := isOpen_compl_singleton
  have hs : UniqueDiffOn ℝ s := hsopen.uniqueDiffOn
  have hN : ContDiffOn ℝ ⊤ N s :=
    fun z hz => (contDiffAt_norm (E := E) ℝ hz).contDiffWithinAt
  have hcont1 : ContinuousOn (fun z : E => iteratedFDeriv ℝ n N z) s := by
    have h1 : ContinuousOn (iteratedFDerivWithin ℝ n N s) s :=
      hN.continuousOn_iteratedFDerivWithin (m := n) le_top hs
    refine h1.congr ?_
    intro z hz
    exact (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := N) n hsopen hz).symm
  have hsub : Metric.sphere (0 : E) 1 ⊆ s := by
    intro z hz
    rw [Metric.mem_sphere, dist_zero_right] at hz
    simp only [s, mem_compl_iff, mem_singleton_iff]
    intro h; rw [h] at hz; simp at hz
  obtain ⟨K₀, hK₀⟩ := (isCompact_sphere (0 : E) 1).exists_bound_of_continuousOn
    ((hcont1.mono hsub).norm)
  refine ⟨max K₀ 0, fun x hx => ?_⟩
  have hK : ∀ z ∈ Metric.sphere (0 : E) 1, ‖iteratedFDeriv ℝ n N z‖ ≤ K₀ := by
    intro z hz
    have := hK₀ z hz
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using this
  have hK' : ∀ z ∈ Metric.sphere (0 : E) 1, ‖iteratedFDeriv ℝ n N z‖ ≤ max K₀ 0 :=
    fun z hz => (hK z hz).trans (le_max_left _ _)
  have hxpos : 0 < ‖x‖ := lt_of_lt_of_le zero_lt_one hx
  have hxne : x ≠ 0 := fun h => by rw [h, norm_zero] at hxpos; exact lt_irrefl 0 hxpos
  set t : ℝ := ‖x‖⁻¹ with htdef
  have htpos : 0 < t := by rw [htdef]; exact inv_pos.mpr hxpos
  have htle : t ≤ 1 := by rw [htdef, inv_le_one₀ hxpos]; exact hx
  have htx : ‖t • x‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos htpos, htdef, inv_mul_cancel₀ (ne_of_gt hxpos)]
  have hKtx : ‖iteratedFDeriv ℝ n N (t • x)‖ ≤ max K₀ 0 :=
    hK' (t • x) (by rw [Metric.mem_sphere, dist_zero_right]; exact htx)
  let g : E →L[ℝ] E := t • 1
  have hgapp : ∀ z : E, g z = t • z := fun z => by simp [g]
  have hgne : ∀ z : E, g z = 0 ↔ z = 0 := by
    intro z
    rw [hgapp z, smul_eq_zero]
    exact ⟨fun h => h.resolve_left (ne_of_gt htpos), fun h => Or.inr h⟩
  have hpre : g ⁻¹' s = s := by
    ext z
    simp only [mem_preimage, s, mem_compl_iff, mem_singleton_iff, hgne z]
  have hgnorm : ‖g‖ ≤ t := by
    rw [show g = t • (1 : E →L[ℝ] E) from rfl]
    calc ‖(t • 1 : E →L[ℝ] E)‖ = ‖t‖ * ‖(1 : E →L[ℝ] E)‖ := norm_smul t 1
      _ ≤ t * 1 := by
          rw [Real.norm_eq_abs, abs_of_pos htpos]
          exact mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le htpos.le
      _ = t := mul_one _
  have hxmem : x ∈ s := by
    simp only [s, mem_compl_iff, mem_singleton_iff]; exact hxne
  have hgxmem : g x ∈ s := by
    simp only [s, mem_compl_iff, mem_singleton_iff]
    exact fun h => hxne ((hgne x).mp h)
  have hcompid := g.iteratedFDerivWithin_comp_right (s := s) (f := N) hN hs
    (by rw [hpre]; exact hs) (x := x) hgxmem (i := n) le_top
  have hlhs : iteratedFDerivWithin ℝ n (N ∘ ⇑g) (g ⁻¹' s) x
      = t • iteratedFDerivWithin ℝ n N s x := by
    rw [hpre]
    have hcongr : (N ∘ ⇑g) = fun z : E => t • N z := by
      funext z
      rw [Function.comp_apply, hgapp z]
      simp only [N]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos htpos, smul_eq_mul]
    rw [hcongr]
    exact iteratedFDerivWithin_const_smul_apply (i := n) (a := t) (f := N)
      ((contDiffAt_norm (E := E) ℝ hxne).contDiffWithinAt) hs hxmem
  have hprod : ∏ _ : Fin n, ‖g‖ ≤ t ^ n := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_pow_left₀ (norm_nonneg _) hgnorm n
  have hnorm_rhs : ‖(iteratedFDerivWithin ℝ n N s (g x)).compContinuousLinearMap (fun _ => g)‖
      ≤ ‖iteratedFDerivWithin ℝ n N s (g x)‖ * t ^ n :=
    (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
      (mul_le_mul_of_nonneg_left hprod (norm_nonneg _))
  have hwithin_gx : iteratedFDerivWithin ℝ n N s (g x) = iteratedFDeriv ℝ n N (g x) :=
    iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := N) n hsopen hgxmem
  have hwithin_x : iteratedFDerivWithin ℝ n N s x = iteratedFDeriv ℝ n N x :=
    iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := N) n hsopen hxmem
  have key : t * ‖iteratedFDeriv ℝ n N x‖ ≤ ‖iteratedFDeriv ℝ n N (t • x)‖ * t ^ n := by
    calc t * ‖iteratedFDeriv ℝ n N x‖ = ‖t • iteratedFDeriv ℝ n N x‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
      _ = ‖t • iteratedFDerivWithin ℝ n N s x‖ := by rw [hwithin_x]
      _ = ‖iteratedFDerivWithin ℝ n (N ∘ ⇑g) (g ⁻¹' s) x‖ := by rw [hlhs]
      _ = ‖(iteratedFDerivWithin ℝ n N s (g x)).compContinuousLinearMap (fun _ => g)‖ := by
          rw [hcompid]
      _ ≤ ‖iteratedFDerivWithin ℝ n N s (g x)‖ * t ^ n := hnorm_rhs
      _ = ‖iteratedFDeriv ℝ n N (t • x)‖ * t ^ n := by rw [hwithin_gx, hgapp x]
  have htpow : t ^ n = t * t ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 from (Nat.sub_add_cancel hn).symm, pow_succ']
  have hmain : t * ‖iteratedFDerivWithin ℝ n N s x‖ ≤ t * (max K₀ 0 * t ^ (n - 1)) := by
    calc t * ‖iteratedFDerivWithin ℝ n N s x‖ = t * ‖iteratedFDeriv ℝ n N x‖ := by rw [hwithin_x]
      _ ≤ ‖iteratedFDeriv ℝ n N (t • x)‖ * t ^ n := key
      _ = t * (‖iteratedFDeriv ℝ n N (t • x)‖ * t ^ (n - 1)) := by rw [htpow]; ring
      _ ≤ t * (max K₀ 0 * t ^ (n - 1)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hKtx (pow_nonneg htpos.le _)) htpos.le
  have h2 : ‖iteratedFDerivWithin ℝ n N s x‖ ≤ max K₀ 0 * t ^ (n - 1) :=
    le_of_mul_le_mul_left hmain htpos
  have ht1 : t ^ (n - 1) ≤ 1 := pow_le_one₀ htpos.le htle
  have hK0 : 0 ≤ max K₀ 0 := le_max_right _ _
  rw [← hwithin_x]
  calc ‖iteratedFDerivWithin ℝ n N s x‖ ≤ max K₀ 0 * t ^ (n - 1) := h2
    _ ≤ max K₀ 0 * 1 := mul_le_mul_of_nonneg_left ht1 hK0
    _ = max K₀ 0 := mul_one _

/-- **Smoothness of a radial composition.**  If `ψ` is smooth and vanishes on `(-∞, 1]`, then
`y ↦ ψ ‖y‖` is smooth: the vanishing of `ψ` in a neighbourhood of `0` compensates for the
non-differentiability of the norm at the origin. -/
theorem contDiff_radial_norm_of_eq_zero_on_Iic {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ⊤ ψ)
    (hsupp : ∀ t : ℝ, t ≤ 1 → ψ t = 0) :
    ContDiff ℝ ⊤ (fun y : E => ψ ‖y‖) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds (0 : E) zero_lt_one] with y hy
    simp only [Metric.mem_ball, dist_zero_right] at hy
    exact hsupp _ hy.le
  · exact hψ.contDiffAt.comp x ((contDiffAt_norm (E := E) ℝ hx).comp x contDiffAt_id)

/-- **Global bound for the derivatives of a radial function.**

If `ψ : ℝ → ℝ` is smooth, vanishes on `(-∞, 1]`, and has bounded derivatives up to order
`a`, then the `a`-th iterated Fréchet derivative of `y ↦ ψ ‖y‖` is bounded on all of `E`.

The vanishing on `(-∞, 1]` makes `y ↦ ψ ‖y‖` identically zero on the unit ball, so only the
region `‖y‖ ≥ 1` matters; there the norm is smooth with bounded derivatives, and the Faà di
Bruno estimate `norm_iteratedFDerivWithin_comp_le` gives the result. -/
theorem radial_iteratedFDeriv_bound_of_eq_zero_on_Iic {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [ProperSpace E] {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ⊤ ψ)
    (hsupp : ∀ t : ℝ, t ≤ 1 → ψ t = 0) (a : ℕ)
    (hbd : ∀ k ≤ a, ∃ B : ℝ, ∀ t : ℝ, ‖iteratedFDeriv ℝ k ψ t‖ ≤ B) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : E, ‖iteratedFDeriv ℝ a (fun y : E => ψ ‖y‖) x‖ ≤ M := by
  classical
  -- A single constant bounding `ψ` and all its derivatives up to order `a`.
  obtain ⟨C, hCpos, hCbd⟩ : ∃ C : ℝ, 0 < C ∧
      ∀ k ≤ a, ∀ t : ℝ, ‖iteratedFDeriv ℝ k ψ t‖ ≤ C := by
    have haux : ∀ k : ℕ, ∃ B : ℝ, k ≤ a →
        ∀ t : ℝ, ‖iteratedFDeriv ℝ k ψ t‖ ≤ B := by
      intro k
      by_cases hk : k ≤ a
      · obtain ⟨B, hB⟩ := hbd k hk
        exact ⟨B, fun _ => hB⟩
      · exact ⟨1, fun h => absurd h hk⟩
    choose B hB using haux
    have hsum : 0 ≤ ∑ k ∈ Finset.range (a + 1), |B k| :=
      Finset.sum_nonneg (f := fun k => |B k|) (fun i _ => abs_nonneg _)
    refine ⟨(∑ k ∈ Finset.range (a + 1), |B k|) + 1, by linarith, fun k hk t => ?_⟩
    have hk' : k ∈ Finset.range (a + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hk)
    have h1 : ‖iteratedFDeriv ℝ k ψ t‖ ≤ B k := hB k hk t
    have h2 : B k ≤ |B k| := le_abs_self _
    have h3 : |B k| ≤ ∑ j ∈ Finset.range (a + 1), |B j| :=
      Finset.single_le_sum (f := fun j => |B j|) (fun j _ => abs_nonneg _) hk'
    linarith
  -- Uniform bounds for the derivatives of the norm on `{x | 1 ≤ ‖x‖}`.
  have haux2 : ∀ i : ℕ, ∃ K : ℝ, 1 ≤ i → i ≤ a → ∀ x : E, 1 ≤ ‖x‖ →
      ‖iteratedFDeriv ℝ i (fun z : E => ‖z‖) x‖ ≤ K := by
    intro i
    by_cases hi : 1 ≤ i
    · obtain ⟨K, hK⟩ := iteratedFDeriv_norm_bound (E := E) i hi
      exact ⟨K, fun _ _ => hK⟩
    · exact ⟨1, fun h => absurd h hi⟩
  choose K hK using haux2
  let D : ℝ := max 1 (∑ i ∈ Finset.range (a + 1), |K i|)
  have hD1 : 1 ≤ D := le_max_left _ _
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD1
  have hDK : ∀ i, 1 ≤ i → i ≤ a → K i ≤ D := by
    intro i hi1 hia
    refine (le_abs_self _).trans ?_
    exact (Finset.single_le_sum (f := fun j => |K j|) (fun j _ => abs_nonneg _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hia))).trans (le_max_right _ _)
  -- The function vanishes identically near the origin.
  have hzero : ∀ x : E, ‖x‖ < 1 →
      iteratedFDeriv ℝ a (fun y : E => ψ ‖y‖) x = 0 := by
    intro x hx
    have hev : (fun y : E => ψ ‖y‖) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      have hxball : x ∈ Metric.ball (0 : E) 1 := by
        rw [Metric.mem_ball, dist_zero_right]; exact hx
      filter_upwards [Metric.isOpen_ball.mem_nhds hxball] with y hy
      rw [Metric.mem_ball, dist_zero_right] at hy
      exact hsupp ‖y‖ hy.le
    have h2 : iteratedFDeriv ℝ a (fun _ : E => (0 : ℝ)) x = 0 := by
      rcases Nat.eq_zero_or_pos a with ha | ha
      · subst ha
        ext m
        simp
      · rw [iteratedFDeriv_const_of_ne (𝕜 := ℝ) ha.ne' (0 : ℝ)]
        simp
    exact ((Filter.EventuallyEq.iteratedFDeriv ℝ hev a).eq_of_nhds).trans h2
  -- The main estimate.
  have key : ∀ x : E,
      ‖iteratedFDeriv ℝ a (fun y : E => ψ ‖y‖) x‖ ≤ (a.factorial : ℝ) * C * D ^ a := by
    intro x
    by_cases hx : ‖x‖ < 1
    · rw [hzero x hx, norm_zero]
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hCpos.le) (pow_nonneg hDpos.le _)
    · simp only [not_lt] at hx
      set s : Set E := {z : E | (1 : ℝ) / 2 < ‖z‖} with hsdef
      have hsopen : IsOpen s := by
        rw [hsdef]; exact isOpen_lt continuous_const continuous_norm
      have hs : UniqueDiffOn ℝ s := hsopen.uniqueDiffOn
      have ht : UniqueDiffOn ℝ (Set.Ioi ((1 : ℝ) / 2)) := isOpen_Ioi.uniqueDiffOn
      have hms : MapsTo (fun z : E => ‖z‖) s (Set.Ioi ((1 : ℝ) / 2)) := fun z hz => hz
      have hxmem : x ∈ s := by
        rw [hsdef]; simp only [Set.mem_ofPred_eq]; linarith
      have hNdiff : ContDiffOn ℝ ⊤ (fun z : E => ‖z‖) s := by
        intro z hz
        have hz' : (1 : ℝ) / 2 < ‖z‖ := hz
        exact (contDiffAt_norm (E := E) ℝ
          (fun h => by rw [h, norm_zero] at hz'; norm_num at hz')).contDiffWithinAt
      have hC' : ∀ i, i ≤ a →
          ‖iteratedFDerivWithin ℝ i ψ (Set.Ioi ((1 : ℝ) / 2)) (‖x‖)‖ ≤ C := by
        intro i hi
        rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := ψ) i isOpen_Ioi
          (by simp only [Set.mem_Ioi]; linarith)]
        exact hCbd i hi (‖x‖)
      have hD' : ∀ i, 1 ≤ i → i ≤ a →
          ‖iteratedFDerivWithin ℝ i (fun z : E => ‖z‖) s x‖ ≤ D ^ i := by
        intro i hi1 hia
        rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := fun z : E => ‖z‖) i hsopen hxmem]
        refine (hK i hi1 hia x hx).trans ?_
        calc K i ≤ D := hDK i hi1 hia
          _ = D ^ 1 := (pow_one D).symm
          _ ≤ D ^ i := pow_le_pow_right₀ hD1 hi1
      have hcomp := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) (g := ψ)
        (f := fun z : E => ‖z‖) (n := a) (s := s) (t := Set.Ioi ((1 : ℝ) / 2))
        (x := x) (N := ⊤) hψ.contDiffOn hNdiff le_top ht hs hms hxmem (C := C) (D := D) hC' hD'
      simp only [Function.comp_def] at hcomp
      rwa [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := fun y : E => ψ ‖y‖) a hsopen hxmem]
        at hcomp
  exact ⟨max ((a.factorial : ℝ) * C * D ^ a) 1, lt_max_of_lt_right zero_lt_one,
    fun x => (key x).trans (le_max_left _ _)⟩

end Commons.Analysis.Calculus