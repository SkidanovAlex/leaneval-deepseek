import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Submission.Commons.Topology.Winding.winding_zero_of_unbounded_component

namespace Commons.Topology.Winding

set_option autoImplicit false

open Set Metric Filter
open scoped _root_.Topology

noncomputable section

/-- **A periodic function on `ℝ` depends only on its fractional part.** -/
theorem periodic_eq_fract {β : Type*} {f : ℝ → β} (h : Function.Periodic f 1) (t : ℝ) :
    f t = f (Int.fract t) := by
  have h' := h.int_mul ⌊t⌋ (Int.fract t)
  rw [mul_one, Int.fract_add_floor] at h'
  exact h'

/-- **Close zero-free periodic curves have the same vanishing of the winding number.** If `g` is a
continuous `1`-periodic zero-free curve with a periodic argument function, and `f` is a continuous
`1`-periodic curve which is *pointwise closer to `g` than `g` is to the origin*
(`‖f t - g t‖ < ‖g t‖` for all `t`), then `f` also admits a periodic argument function.

Indeed `W t := f t / g t` has `‖W t - 1‖ < 1`, hence `Re (W t) > 0`, so `arg (W t)` is continuous
and (because `f` and `g` are periodic) periodic; writing `f t = g t * W t` shows that
`θ t + arg (W t)` is a periodic argument for `f`. -/
theorem HasArg.of_close {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hfper : Function.Periodic f 1) (hgper : Function.Periodic g 1)
    (hgnz : ∀ t, g t ≠ 0) (hclose : ∀ t, ‖f t - g t‖ < ‖g t‖)
    (h : HasArg g 0) : HasArg f 0 := by
  obtain ⟨θ, hθc, hθper, hθrep⟩ := h
  simp only [sub_zero] at hθrep
  set W : ℝ → ℂ := fun t => f t / g t with hW
  have hWcont : Continuous W := by
    rw [hW]; exact hf.div hg hgnz
  have hWre : ∀ t, 0 < (W t).re := by
    intro t
    have hg0 : g t ≠ 0 := hgnz t
    have hnormg : 0 < ‖g t‖ := norm_pos_iff.mpr hg0
    have hsub : W t = 1 + (f t - g t) / g t := by
      rw [hW]
      field_simp
      ring
    have hc : ‖(f t - g t) / g t‖ < 1 := by
      rw [norm_div, div_lt_one hnormg]
      exact hclose t
    have hlow : -‖(f t - g t) / g t‖ ≤ ((f t - g t) / g t).re := by
      have hh := Complex.abs_re_le_norm ((f t - g t) / g t)
      rw [abs_le] at hh
      exact hh.1
    rw [hsub, Complex.add_re, Complex.one_re]
    linarith
  have hWper : ∀ t, W (t + 1) = W t := by
    intro t
    simp only [hW, hfper t, hgper t]
  have hWmul : ∀ t, g t * W t = f t := by
    intro t
    rw [hW]
    exact mul_div_cancel₀ (f t) (hgnz t)
  have hWexp : ∀ t, (‖W t‖ : ℂ) * Complex.exp ((Complex.arg (W t) : ℂ) * Complex.I) = W t :=
    fun t => Complex.norm_mul_exp_arg_mul_I (W t)
  refine ⟨fun t => θ t + Complex.arg (W t), ?_, ?_, ?_⟩
  · refine hθc.add ?_
    rw [continuous_iff_continuousAt]
    intro t
    exact (Complex.continuousAt_arg (Or.inl (hWre t))).comp hWcont.continuousAt
  · intro t
    simp only [hθper t, hWper t]
  · intro t
    simp only [sub_zero]
    have hnormmul : (‖g t‖ : ℂ) * (‖W t‖ : ℂ) = (‖f t‖ : ℂ) := by
      rw [← Complex.ofReal_mul, ← norm_mul, hWmul t]
    have hexpadd : Complex.exp ((θ t : ℂ) * Complex.I)
          * Complex.exp ((Complex.arg (W t) : ℂ) * Complex.I)
        = Complex.exp (((θ t + Complex.arg (W t) : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      rw [← add_mul, ← Complex.ofReal_add]
    calc f t = g t * W t := (hWmul t).symm
      _ = ((‖g t‖ : ℂ) * Complex.exp ((θ t : ℂ) * Complex.I)) * W t := by
            conv_lhs => rw [hθrep t]
      _ = ((‖g t‖ : ℂ) * Complex.exp ((θ t : ℂ) * Complex.I))
            * ((‖W t‖ : ℂ)
                * Complex.exp ((Complex.arg (W t) : ℂ) * Complex.I)) := by
            conv_lhs => rw [← hWexp t]
      _ = ((‖g t‖ : ℂ) * (‖W t‖ : ℂ))
            * (Complex.exp ((θ t : ℂ) * Complex.I)
                * Complex.exp ((Complex.arg (W t) : ℂ) * Complex.I)) := by ring
      _ = (‖f t‖ : ℂ) * Complex.exp (((θ t + Complex.arg (W t) : ℝ) : ℂ) * Complex.I) := by
            rw [hnormmul, hexpadd]

/-- **The set of parameters for which a periodic argument exists is locally constant.** More
precisely, if `g : ℝ → ℝ → ℂ` is jointly continuous, each `g s` is `1`-periodic and nowhere zero,
then for every `s₀` the assertion `HasArg (g s) 0` is constant for `s` in a neighbourhood of `s₀`.
This is proved by mapping each `g s` into `g s₀` through the positive-real factor `g s / g s₀`,
which continuously deforms periodic arguments. -/
theorem exists_shift_iff (g : ℝ → ℝ → ℂ) (hg : Continuous (fun p : ℝ × ℝ => g p.1 p.2))
    (hgper : ∀ s, Function.Periodic (g s) 1) (hgnz : ∀ s t, g s t ≠ 0) (s₀ : ℝ) :
    ∃ δ > 0, ∀ s, dist s s₀ < δ → (HasArg (g s) 0 ↔ HasArg (g s₀) 0) := by
  have hgcont : ∀ s, Continuous (g s) := fun s => by
    have h1 : Continuous (fun t : ℝ => g s t) :=
      hg.comp (continuous_const.prodMk continuous_id)
    exact h1
  classical
  obtain ⟨t₀, -, hmin⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_isMinOn
    ⟨0, by norm_num⟩ (continuous_norm.comp (hgcont s₀)).continuousOn
  set m : ℝ := ‖g s₀ t₀‖ with hm
  have hmpos : 0 < m := by rw [hm]; exact norm_pos_iff.mpr (hgnz s₀ t₀)
  have hred : ∀ s t, g s t = g s (Int.fract t) := fun s t => periodic_eq_fract (hgper s) t
  have hmle : ∀ t, m ≤ ‖g s₀ t‖ := by
    intro t
    have hft : Int.fract t ∈ Icc (0:ℝ) 1 :=
      ⟨Int.fract_nonneg t, le_of_lt (Int.fract_lt_one t)⟩
    have h1 : m ≤ ‖g s₀ (Int.fract t)‖ := by
      rw [hm]; exact hmin hft
    rwa [← hred s₀ t] at h1
  let fam : ℝ → ↥(Icc (0:ℝ) 1) → ℂ := fun s t => g s t.1
  have hfamcont : Continuous (Function.uncurry fam) := by
    change Continuous (fun p : ℝ × ↥(Icc (0:ℝ) 1) => g p.1 (p.2 : ℝ))
    have hinner : Continuous (fun p : ℝ × ↥(Icc (0:ℝ) 1) => (p.1, (p.2 : ℝ))) :=
      continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
    exact hg.comp hinner
  have htend := Continuous.tendstoUniformly fam hfamcont s₀
  have hu : {z : ℂ × ℂ | dist z.1 z.2 < m / 2} ∈ uniformity ℂ :=
    Metric.dist_mem_uniformity (by positivity)
  have hev : ∀ᶠ s in 𝓝 s₀, ∀ t : ↥(Icc (0:ℝ) 1), dist (fam s t) (fam s₀ t) < m / 2 := by
    filter_upwards [htend _ hu] with s hs t
    have := hs t
    rwa [dist_comm] at this
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨δ, hδpos, ?_⟩
  intro s hs
  have hbound : ∀ t : ℝ, dist (g s t) (g s₀ t) < m / 2 := by
    intro t
    have hft : Int.fract t ∈ Icc (0:ℝ) 1 :=
      ⟨Int.fract_nonneg t, le_of_lt (Int.fract_lt_one t)⟩
    have h1 : dist (g s (Int.fract t)) (g s₀ (Int.fract t)) < m / 2 := by
      have := hδ hs ⟨Int.fract t, hft⟩
      simpa [fam] using this
    rwa [hred s t, hred s₀ t]
  have hcl_fwd : ∀ t, ‖g s t - g s₀ t‖ < ‖g s₀ t‖ := by
    intro t
    have hb := hbound t
    have hm2 := hmle t
    rw [dist_eq_norm] at hb
    linarith
  have hcl_bwd : ∀ t, ‖g s₀ t - g s t‖ < ‖g s t‖ := by
    intro t
    have hb : ‖g s t - g s₀ t‖ < m / 2 := by
      have hh := hbound t
      rwa [dist_eq_norm] at hh
    have hm2 := hmle t
    have htri : ‖g s₀ t‖ ≤ ‖g s t - g s₀ t‖ + ‖g s t‖ := by
      have h' : ‖g s₀ t‖ ≤ ‖g s₀ t - g s t‖ + ‖g s t‖ := by
        simpa using norm_add_le (g s₀ t - g s t) (g s t)
      rwa [norm_sub_rev] at h'
    rw [norm_sub_rev]
    linarith
  refine ⟨?_, ?_⟩
  · intro hs1
    exact HasArg.of_close (hgcont s₀) (hgcont s) (hgper s₀) (hgper s) (hgnz s) hcl_bwd hs1
  · intro hs0
    exact HasArg.of_close (hgcont s) (hgcont s₀) (hgper s) (hgper s₀) (hgnz s₀) hcl_fwd hs0

/-- **The vanishing of the winding number is invariant under zero-free homotopies.** Let `F : ℝ × ℝ → ℂ` be continuous, `1`-periodic in its first variable and nowhere zero. Then the closed curve `t ↦ F (t, 0)` admits a continuous `1`-periodic argument function if and only if `t ↦ F (t, 1)` does.

Here `HasArg f p` (from `Commons.Topology.Winding.winding_zero_of_unbounded_component`) says that `t ↦ f t - p` admits a continuous `1`-periodic argument function, i.e. that this closed curve has winding number zero around `p`. The statement is the (easy) half of homotopy invariance of the winding number that is used to propagate "does not wind around the point" along a continuous deformation.

Suggested proof route: for each `s`, `Commons.Topology.Winding.exists_arg_lift_periodic` applied to `t ↦ F (t, s)` gives a continuous argument with drift `2*pi*k s` for some integer `k s`; `HasArg (·,s) 0` holds exactly when `k s = 0`. The function `s ↦ k s` is locally constant: near a fixed `s₀`, the curves `t ↦ F (t,s)` stay uniformly close to `t ↦ F (t,s₀)` (continuity on the compact `[0,1] × [0,1]`), and closeness of two uniformly close zero-free curves forces equality of their argument drifts. Since `[0,1]` is connected and preconnected, `k` is constant, and the claim follows. -/
theorem hasArg_homotopy_invariant
    {F : ℝ × ℝ → ℂ} (hF : Continuous F)
    (hper : ∀ t s, F (t+1, s) = F (t, s))
    (hnz : ∀ t s, F (t, s) ≠ 0) :
    (Commons.Topology.Winding.HasArg (fun t => F (t, 0)) 0 ↔
      Commons.Topology.Winding.HasArg (fun t => F (t, 1)) 0) := by
  let g : ℝ → ℝ → ℂ := fun s t => F (t, s)
  have hgjoint : Continuous (fun p : ℝ × ℝ => g p.1 p.2) := by
    apply hF.comp
    exact continuous_snd.prodMk continuous_fst
  have hgper : ∀ s, Function.Periodic (g s) 1 := fun s t => hper t s
  have hgnz : ∀ s t, g s t ≠ 0 := fun s t => hnz t s
  let B : Set ℝ := {s | HasArg (g s) 0}
  have hBopen : IsOpen B := by
    rw [isOpen_iff_mem_nhds]
    intro s₀ hs₀
    obtain ⟨δ, hδpos, hδ⟩ := exists_shift_iff g hgjoint hgper hgnz s₀
    filter_upwards [Metric.ball_mem_nhds s₀ hδpos] with s hs
    exact (hδ s hs).2 hs₀
  have hBclosed : IsClosed B := by
    rw [← isOpen_compl_iff]
    rw [isOpen_iff_mem_nhds]
    intro s₀ hs₀
    obtain ⟨δ, hδpos, hδ⟩ := exists_shift_iff g hgjoint hgper hgnz s₀
    filter_upwards [Metric.ball_mem_nhds s₀ hδpos] with s hs
    intro hsB
    exact hs₀ ((hδ s hs).1 hsB)
  have hpre : IsPreconnected (Icc (0:ℝ) 1) := isPreconnected_Icc
  have hsub : Icc (0:ℝ) 1 ⊆ B ∨ Icc (0:ℝ) 1 ⊆ Bᶜ :=
    hpre.subset_or_subset hBopen hBclosed.isOpen_compl disjoint_compl_right
      (by rw [union_compl_self]; exact subset_univ _)
  have h0 : (0:ℝ) ∈ Icc (0:ℝ) 1 := by norm_num
  have h1 : (1:ℝ) ∈ Icc (0:ℝ) 1 := by norm_num
  have hfin : (0:ℝ) ∈ B ↔ (1:ℝ) ∈ B := by
    rcases hsub with hsub | hsub
    · exact ⟨fun _ => hsub h1, fun _ => hsub h0⟩
    · exact ⟨fun hB => absurd hB (hsub h0), fun hB => absurd hB (hsub h1)⟩
  exact hfin

end

end Commons.Topology.Winding
