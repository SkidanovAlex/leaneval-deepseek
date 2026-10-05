import Mathlib

/-!
# B5: a uniform sign change across a positive ∂₃-derivative

Let `F : ℝ × (ℝ × ℝ) → ℝ` be `C¹`.  Write `(τ, (t, ρ))` for its argument.  Assume that

* `F (τ, (t, 0)) = 0` for `τ ∈ [0,1]` and all `t`;
* the derivative of the `ρ`-slice at `ρ = 0` is bounded below by a positive constant `δ`:
  `δ ≤ deriv (fun s => F (τ, (t, s))) 0` for `τ ∈ [0,1]` and all `t`;
* `F` is `2π`-periodic in the `t`-variable.

Then there is a uniform `ε > 0` such that `F (τ, (t, ρ)) < 0` for every `τ ∈ [0,1]`, every
real `t` and every `ρ ∈ (-ε, 0)`.

The mathematical content is the standard "compactness + mean value theorem" argument.  The
partial derivative `∂₃F`, written through `fderiv` as `pdsF`, is compactly uniform in the
`(τ, t)`-variables on the fundamental domain `[0,1] × [0, 2π]`; this yields a uniform lower
bound `δ/2` on a strip `|ρ| < ε` (the `pdsF_tube` lemma, proved by thickening a compact set
inside the open set `{∂₃F > δ/2}`).  The mean value theorem then turns that bound on the
derivative into the strict sign change of `F` itself on `ρ < 0`, with `F(τ,(t,0)) = 0` as the
base point (`exists_deriv_eq_slope`).  Periodicity of `F` in `t` reduces the arbitrary `t` to
the fundamental domain.

## Contents

* `pdsF`, `pdsF_continuous`, `pdsF_eq_deriv`: the partial derivative and its basic properties;
* `pdsF_tube`: the uniform positive lower bound on a strip;
* `exists_eps_neg_of_deriv_pos`: the requested lemma.
-/

open scoped ContDiff

set_option autoImplicit false

namespace Work.RPB.B5

/-- The partial derivative `∂₃F` of `F : ℝ × (ℝ × ℝ) → ℝ` in its last coordinate, written via
`fderiv` so that its joint continuity is immediate from `ContDiff ℝ 1 F`.  By the chain rule it
equals `deriv (fun s => F (τ, (t, s))) u`, see `pdsF_eq_deriv`. -/
noncomputable def pdsF (F : ℝ × (ℝ × ℝ) → ℝ) : ℝ × (ℝ × ℝ) → ℝ :=
  fun p => (fderiv ℝ F p) ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))

/-- `pdsF F` is continuous when `F` is `C¹`: it is the `C⁰` map `fderiv ℝ F` followed by
evaluation at the fixed direction `(0, (0, 1))`. -/
theorem pdsF_continuous (F : ℝ × (ℝ × ℝ) → ℝ) (hF : ContDiff ℝ 1 F) :
    Continuous (pdsF F) := by
  have h : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by norm_num)
  exact h.clm_apply continuous_const

/-- The `fderiv`-based partial derivative `pdsF` coincides with the ordinary derivative of the
`ρ`-slice.  This is the chain rule applied to `s ↦ (τ, (t, s))`, whose derivative is the
constant direction `(0, (0, 1))`. -/
theorem pdsF_eq_deriv (F : ℝ × (ℝ × ℝ) → ℝ) (hF : ContDiff ℝ 1 F) (τ t u : ℝ) :
    pdsF F (τ, (t, u)) = deriv (fun s : ℝ => F (τ, (t, s))) u := by
  have hF' : HasFDerivAt F (fderiv ℝ F (τ, (t, u))) (τ, (t, u)) :=
    ((hF.differentiable (by norm_num)).differentiableAt).hasFDerivAt
  have hφ : HasDerivAt (fun s : ℝ => (τ, (t, s))) ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) u :=
    (hasDerivAt_const (c := τ) u).prodMk
      ((hasDerivAt_const (c := t) u).prodMk (hasDerivAt_id u))
  have hcomp : HasDerivAt (F ∘ fun s : ℝ => (τ, (t, s)))
      ((fderiv ℝ F (τ, (t, u))) ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))) u :=
    hF'.comp_hasDerivAt u hφ
  have hcomp' : HasDerivAt (fun s : ℝ => F (τ, (t, s)))
      ((fderiv ℝ F (τ, (t, u))) ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))) u := by
    simpa [Function.comp_def] using hcomp
  unfold pdsF
  exact hcomp'.deriv.symm

/-- **Uniform lower bound on `∂₃F` on a strip.**  If `∂₃F ≥ δ > 0` at `ρ = 0` for every
`τ ∈ [0,1]` and every `t`, then there is `ε > 0` with `∂₃F (τ, (t, ρ)) > δ/2` for every
`τ ∈ [0,1]`, every `t ∈ [0, 2π]` and every `|ρ| < ε`.

The proof is the tube lemma: `K := [0,1] × [0,2π] × {0}` is compact and contained in the open
set `{pdsF F > δ/2}`; thickening `K` inside that open set produces the strip. -/
theorem pdsF_tube (F : ℝ × (ℝ × ℝ) → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hF : ContDiff ℝ 1 F)
    (hD : ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ t, δ ≤ deriv (fun s : ℝ => F (τ, (t, s))) 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) (2*Real.pi),
      ∀ u : ℝ, |u| < ε → δ/2 < pdsF F (τ, (t, u)) := by
  let s : Set (ℝ × (ℝ × ℝ)) :=
    Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) (2*Real.pi) ×ˢ ({0} : Set ℝ)
  have hK : IsCompact s := by
    show IsCompact (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) (2*Real.pi) ×ˢ ({0} : Set ℝ))
    exact isCompact_Icc.prod (isCompact_Icc.prod isCompact_singleton)
  have hUopen : IsOpen (pdsF F ⁻¹' Set.Ioi (δ/2)) :=
    isOpen_Ioi.preimage (pdsF_continuous F hF)
  have hsU : s ⊆ pdsF F ⁻¹' Set.Ioi (δ/2) := by
    intro x hx
    simp only [Set.mem_preimage, Set.mem_Ioi]
    have hx' : x.1 ∈ Set.Icc (0:ℝ) 1 ∧ x.2.1 ∈ Set.Icc (0:ℝ) (2*Real.pi) ∧ x.2.2 = 0 := by
      simpa [s, Set.mem_prod, Set.mem_Icc, Set.mem_singleton_iff] using hx
    obtain ⟨h1, h2, h3⟩ := hx'
    have hx_eq : x = (x.1, (x.2.1, 0)) := by ext <;> simp [h3]
    rw [hx_eq, pdsF_eq_deriv F hF]
    linarith [hD x.1 h1 x.2.1]
  obtain ⟨ε, hεpos, hεs⟩ := hK.exists_thickening_subset_open hUopen hsU
  refine ⟨ε, hεpos, ?_⟩
  intro τ hτ t ht u hu
  have hmem : (τ, (t, u)) ∈ Metric.thickening ε s := by
    rw [Metric.mem_thickening_iff]
    refine ⟨(τ, (t, 0)), ?_, ?_⟩
    · simp only [s, Set.mem_prod, Set.mem_Icc, Set.mem_singleton_iff]
      exact ⟨hτ, ht, trivial⟩
    · have hd : dist ((τ, (t, u)) : ℝ × (ℝ × ℝ)) (τ, (t, 0)) = |u| := by
        rw [Prod.dist_eq, Prod.dist_eq, dist_self, dist_self, Real.dist_eq, sub_zero]
        rw [max_eq_right (le_max_left 0 |u|), max_eq_right (abs_nonneg u)]
      rw [hd]; exact hu
  have := hεs hmem
  simp only [Set.mem_preimage, Set.mem_Ioi] at this
  exact this

theorem exists_eps_neg_of_deriv_pos (F : ℝ × (ℝ × ℝ) → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hF : ContDiff ℝ 1 F)
    (hper : ∀ τ t ρ, F (τ, (t + 2 * Real.pi, ρ)) = F (τ, (t, ρ)))
    (h0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, F (τ, (t, 0)) = 0)
    (hD : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, δ ≤ deriv (fun s : ℝ => F (τ, (t, s))) 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, ∀ ρ ∈ Set.Ioo (-ε) 0,
      F (τ, (t, ρ)) < 0 := by
  obtain ⟨ε, hεpos, htube⟩ := pdsF_tube F δ hδ hF hD
  refine ⟨ε, hεpos, ?_⟩
  intro τ hτ t ρ hρ
  -- Reduce the (arbitrary) time `t` to the fundamental domain `[0, 2π)` using periodicity.
  have hp : Function.Periodic (fun t => F (τ, (t, ρ))) (2 * Real.pi) := fun t => hper τ t ρ
  have hred : ∃ t' ∈ Set.Ico (0:ℝ) (2*Real.pi), F (τ, (t, ρ)) = F (τ, (t', ρ)) := by
    refine ⟨Int.fract (t / (2*Real.pi)) * (2*Real.pi), ?_, ?_⟩
    · rw [Set.mem_Ico]
      exact ⟨mul_nonneg (Int.fract_nonneg _) (by positivity),
        mul_lt_of_lt_one_left (by positivity) (Int.fract_lt_one _)⟩
    · have h2 : t = Int.fract (t / (2*Real.pi)) * (2*Real.pi)
          + ⌊t / (2*Real.pi)⌋ • (2*Real.pi) := by
        rw [zsmul_eq_mul (2*Real.pi), ← add_mul, Int.fract_add_floor]
        exact (div_mul_cancel₀ t (by positivity)).symm
      conv_lhs => rw [h2]
      exact (hp.zsmul ⌊t / (2*Real.pi)⌋) (Int.fract (t / (2*Real.pi)) * (2*Real.pi))
  obtain ⟨t', ht'mem, hft'⟩ := hred
  have ht'Icc : t' ∈ Set.Icc (0:ℝ) (2*Real.pi) := ⟨ht'mem.1, le_of_lt ht'mem.2⟩
  rw [hft']
  -- The fiber `f u = F (τ, (t', u))` and its mean value theorem.
  have hρlt : ρ < 0 := hρ.2
  have hdiff : Differentiable ℝ (fun u : ℝ => F (τ, (t', u))) := by
    have hFd : Differentiable ℝ F := hF.differentiable (by norm_num)
    fun_prop
  obtain ⟨c, hc_mem, hc_eq⟩ :=
    exists_deriv_eq_slope (fun u : ℝ => F (τ, (t', u))) hρlt
      hdiff.continuous.continuousOn hdiff.differentiableOn
  have hcabs : |c| < ε := by
    rw [abs_lt]; constructor <;> linarith [hc_mem.1, hc_mem.2, hρ.1]
  have hpdc : δ/2 < pdsF F (τ, (t', c)) := htube τ hτ t' ht'Icc c hcabs
  have hderivc : deriv (fun u : ℝ => F (τ, (t', u))) c = pdsF F (τ, (t', c)) :=
    (pdsF_eq_deriv F hF τ t' c).symm
  have hpos : 0 < deriv (fun u : ℝ => F (τ, (t', u))) c := by
    rw [hderivc]; linarith [hδ]
  -- The mean value theorem gives `F (τ, (t', ρ)) = f' c * ρ` with `f' c > 0` and `ρ < 0`.
  have hden : (0:ℝ) - ρ ≠ 0 := by linarith
  have hf0 : F (τ, (t', 0)) = 0 := h0 τ hτ t'
  have hmul : F (τ, (t', ρ)) = deriv (fun u : ℝ => F (τ, (t', u))) c * ρ := by
    have h2 : deriv (fun u : ℝ => F (τ, (t', u))) c * (0 - ρ)
        = F (τ, (t', 0)) - F (τ, (t', ρ)) := by
      rw [hc_eq, div_mul_cancel₀ _ hden]
    rw [hf0] at h2
    linarith
  rw [hmul]
  exact mul_neg_of_pos_of_neg hpos hρlt

end Work.RPB.B5
