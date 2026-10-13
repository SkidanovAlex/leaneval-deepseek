import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.RegPkgGal.R5Parts
import Submission.Work.FTS.RegExportIface.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXR1.hd1z2_limit`

The `z`-weighted vanishing of the fake-time derivative `∂_τ g` at `τ = 0`, at the corner
`(z, θ) → (0, 0)`:

  `z⁻¹ · ∂_τ (gS α (tauExt g))(z, θ, 0) → 0` as `z → 0⁺`, for every `θ ∈ Iθ`.

The proof has three ingredients.

* **The one-sided slope bound** (`abs_deriv_zero_le_of_slope_bound`): if `|G s - G 0| ≤ M s`
  for `0 < s < 1` then `|deriv G 0| ≤ M`.  If `G` is differentiable at `0` the slope tends to
  `deriv G 0` along `(0,1]` and the bound is the limit of the bounds; if not, `deriv G 0 = 0`
  by the totalisation of `deriv`.

* **The endpoints** `θ = 0, π/2` (`deriv_gS_tauExt_eq_zero_at_boundary`): `RegPkgMin.vanish`
  makes `g z 0 τ = g z (π/2) τ = 0` for `τ ≥ 0`, hence the `τ`-slice of `tauExt g` is
  identically zero at those angles and the derivative at `0` vanishes.

* **The interior** `0 < θ < π/2`: the hypothesis `hw` bounds the `τ`-differences of the slices
  of `g` by `C z^{3/2}/(1+z)² |τ - τ'|`, which is exactly the slope bound for
  `s ↦ gS α (tauExt g) z θ s` on `(0,1)`; the slope bound yields
  `|∂_τ(gS α (tauExt g))(z,θ,0)| ≤ C z^{3/2}/(1+z)²`, and multiplication by `z⁻¹` gives
  `C z^{1/2}/(1+z)² ≤ C z^{1/2} → 0`.

* The final limit is taken along `𝓝[(0,0)] (Ioi 0 ×ˢ univ)`; since the function only depends on
  the first coordinate, the one-dimensional eventual bound is lifted by
  `eventually_nhdsWithin_fst` and closed with `Metric.tendsto_nhds`.
-/

noncomputable section

open scoped Topology
open Filter

namespace Work.FTS_RegExport.RXR1

set_option autoImplicit false

/-- **A one-sided slope bound bounds the derivative at `0`.**  If `|G s - G 0| ≤ M · s` for
`s ∈ (0,1)`, then `|deriv G 0| ≤ M`.  (No hypothesis on the left of `0` is needed: if `G` is not
differentiable at `0` then `deriv G 0 = 0`.) -/
lemma abs_deriv_zero_le_of_slope_bound {G : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ s ∈ Set.Ioo (0:ℝ) 1, |G s - G 0| ≤ M * s) : |deriv G 0| ≤ M := by
  by_cases hd : DifferentiableAt ℝ G 0
  · -- `G` is differentiable at `0`: the slope bound passes to the limit along `(0,1)`
    have hslope : Filter.Tendsto (slope G 0) (𝓝[>] (0:ℝ)) (𝓝 (deriv G 0)) :=
      (hd.hasDerivAt.tendsto_slope).mono_left (nhdsWithin_mono 0 (fun x hx => ne_of_gt hx))
    have hev : ∀ᶠ s in 𝓝[>] (0:ℝ), ‖slope G 0 s‖ ≤ M := by
      filter_upwards [self_mem_nhdsWithin,
        Filter.Eventually.filter_mono nhdsWithin_le_nhds
          (Ioo_mem_nhds (by norm_num : (-1:ℝ) < 0) (by norm_num : (0:ℝ) < 1))] with s hs hsI
      have hs0 : 0 < s := hs
      have h1 : slope G 0 s = (G s - G 0) / s := by rw [slope_def_field, sub_zero]
      rw [h1, div_eq_mul_inv, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hs0)]
      calc |G s - G 0| * s⁻¹ ≤ (M * s) * s⁻¹ :=
            mul_le_mul_of_nonneg_right (h s ⟨hs0, hsI.2⟩) (le_of_lt (inv_pos.mpr hs0))
        _ = M := by rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hs0), mul_one]
    have hnorm : ‖deriv G 0‖ ≤ M := le_of_tendsto hslope.norm hev
    rwa [Real.norm_eq_abs] at hnorm
  · -- `G` is not differentiable at `0`: the derivative is the junk value `0`
    rw [deriv_zero_of_not_differentiableAt hd, abs_zero]
    exact hM

/-- **Lifting an eventual statement in `z` to the two-dimensional filter
`𝓝[(0,0)] (Ioi 0 ×ˢ univ)`**, using that `Prod.fst` is continuous. -/
lemma eventually_nhdsWithin_fst {P : ℝ → Prop}
    (h : ∀ᶠ z in nhdsWithin (0:ℝ) (Set.Ioi 0), P z) :
    ∀ᶠ p : ℝ × ℝ in nhdsWithin (0,0) (Set.Ioi (0:ℝ) ×ˢ Set.univ), P p.1 := by
  rw [nhdsWithin, Filter.eventually_inf_principal] at h
  rw [nhdsWithin, Filter.eventually_inf_principal]
  have h2 : ∀ᶠ p : ℝ × ℝ in 𝓝 ((0:ℝ),(0:ℝ)), (0 < p.1 → P p.1) :=
    (continuous_fst.tendsto ((0:ℝ),(0:ℝ))).eventually h
  filter_upwards [h2] with p hp hpS
  exact hp hpS.1

/-- **At the angular endpoints `θ = 0`, `π/2` the family `gS α (tauExt g)` is identically zero in
the fake time**, when the datum `g` vanishes on the two boundary rays `θ = 0`, `θ = π/2`
(the `vanish` clause of `RegPkgMin`).  Hence the `τ`-derivative at `0` vanishes. -/
lemma deriv_gS_tauExt_eq_zero_at_boundary {α : ℝ} {g : Work.FTS.Galerkin.Fam}
    (hvanish : ∀ τ, 0 ≤ τ → ∀ z, 0 ≤ z → g z 0 τ = 0 ∧ g z (Real.pi / 2) τ = 0)
    {θ : ℝ} (hθbd : θ = 0 ∨ θ = Real.pi / 2) :
    ∀ z : ℝ, 0 < z →
      deriv (fun s => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ s) 0 = 0 := by
  have hθ0 : 0 ≤ θ := by rcases hθbd with h | h <;> rw [h] <;> linarith [Real.pi_pos]
  have hθπ : θ ≤ Real.pi / 2 := by rcases hθbd with h | h <;> rw [h] <;> linarith [Real.pi_pos]
  have hval : ∀ (s : ℝ) (z : ℝ), 0 ≤ s → 0 ≤ z → g z θ s = 0 := by
    intro s z hs hz
    rcases hθbd with h | h <;> rw [h]
    · exact (hvanish s hs z hz).1
    · exact (hvanish s hs z hz).2
  intro z hz
  have hfun : (fun s => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ s)
      = fun _ => (0:ℝ) := by
    have hEq : Set.EqOn (fun s => g z θ s) (fun _ => (0:ℝ)) (Set.Ici 0) :=
      fun s hs => hval s z hs hz.le
    have hd0 : derivWithin (fun s => g z θ s) (Set.Ici 0) 0 = 0 := by
      rw [derivWithin_congr hEq (by simpa using hval 0 z le_rfl hz.le)]
      exact congrFun (derivWithin_const (Set.Ici (0:ℝ)) (0:ℝ)) 0
    funext s
    have hgs : Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ s
        = Work.FTS.FinalV2.tauExt g z θ s := by
      simp [Work.FTS.FinalV2.gS, hz, hθ0, hθπ]
    rw [hgs]
    by_cases hs : s < 0
    · -- the left branch of `tauExt` is the affine extension with slope `derivWithin … = 0`
      rw [Work.FTS.FinalV2.tauExt_of_neg g hs, hd0, hval 0 z le_rfl hz.le]
      ring
    · rw [Work.FTS.FinalV2.tauExt_of_nonneg g (not_lt.mp hs)]
      exact hval s z (not_lt.mp hs) hz.le
  rw [hfun, deriv_const]

theorem hd1z2_limit {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (H5 : ∀ S > 0, Work.FTS.RegPkgGal.R5Parts α S
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))
      (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)))
    (hw : ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ τ' ∈ Set.Icc (0:ℝ) 1,
      ∀ b a : ℕ, a + b ≤ 1 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ - Work.FTS.Galerkin.slice g τ') z θ| ≤
          C * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) * |τ - τ'|) :
    ∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto
      (fun p : ℝ × ℝ => p.1⁻¹ * deriv
        (fun s => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) p.1 θ s) 0)
      (nhdsWithin (0, 0) (Set.prod (Set.Ioi (0:ℝ)) Set.univ)) (nhds 0) := by
  intro θ hθ
  have hθ0 : 0 ≤ θ := hθ.1
  have hθπ : θ ≤ Real.pi / 2 := hθ.2
  have hreg : Work.FTS.StrongGlobal.RegPkgMin (Work.FTS.Regularity.pExp α) g := hOK.1.1
  have hvan : ∀ τ, 0 ≤ τ → ∀ z, 0 ≤ z → g z 0 τ = 0 ∧ g z (Real.pi / 2) τ = 0 :=
    fun τ hτ z hz => hreg.vanish τ hτ z hz
  -- on the quadrant `gS α (tauExt g)` agrees with `tauExt g`
  have hGval : ∀ z s : ℝ, 0 < z →
      Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ s
        = Work.FTS.FinalV2.tauExt g z θ s := by
    intro z s hz
    simp [Work.FTS.FinalV2.gS, hz, hθ0, hθπ]
  rcases eq_or_lt_of_le hθ0 with hθeq | hθpos
  · -- `θ = 0`
    subst hθeq
    have hkey := deriv_gS_tauExt_eq_zero_at_boundary (α := α) (g := g) hvan (Or.inl rfl)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with p hp
    rw [hkey p.1 hp.1, mul_zero]
  rcases eq_or_lt_of_le hθπ with hθeq2 | hθlt
  · -- `θ = π/2`
    subst hθeq2
    have hkey := deriv_gS_tauExt_eq_zero_at_boundary (α := α) (g := g) hvan (Or.inr rfl)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with p hp
    rw [hkey p.1 hp.1, mul_zero]
  · -- `0 < θ < π/2`: the slope hypothesis `hw`
    obtain ⟨C, hC0, hC⟩ := hw
    have hident : ∀ z : ℝ, 0 < z →
        z⁻¹ * (C * (z ^ ((3:ℝ)/2) / (1+z)^2)) = C * (Real.sqrt z / (1+z)^2) := by
      intro z hz
      have h3 : z ^ ((3:ℝ)/2) = z * Real.sqrt z := by
        rw [show (3:ℝ)/2 = 1 + 1/2 by norm_num, Real.rpow_add hz, Real.rpow_one,
          ← Real.sqrt_eq_rpow]
      rw [h3]
      field_simp
    -- the `τ`-derivative at `0` obeys the `3/2`-weight
    have hderiv : ∀ z : ℝ, 0 < z →
        |deriv (fun s => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ s) 0|
          ≤ C * (z ^ ((3:ℝ)/2) / (1+z)^2) := by
      intro z hz
      refine abs_deriv_zero_le_of_slope_bound
        (mul_nonneg hC0 (div_nonneg (Real.rpow_nonneg hz.le _) (sq_nonneg _))) ?_
      intro s hs
      have hs0 : 0 < s := hs.1
      have hsle : 0 ≤ s := hs0.le
      have hGs : Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ s = g z θ s := by
        rw [hGval z s hz, Work.FTS.FinalV2.tauExt_of_nonneg g hsle]
      have hG0 : Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ 0 = g z θ 0 := by
        rw [hGval z 0 hz, Work.FTS.FinalV2.tauExt_of_nonneg g le_rfl]
      rw [hGs, hG0]
      have h1 := hC s ⟨hsle, hs.2.le⟩ 0 ⟨le_rfl, zero_le_one⟩ 0 0 (by norm_num)
        z θ hz hθpos hθlt
      simpa [Work.Spaces.mixed, sub_zero, abs_of_nonneg hsle] using h1
    -- divide by `z`: the weight becomes `z^{1/2}/(1+z)² ≤ z^{1/2}`
    have hbound : ∀ p : ℝ × ℝ, 0 < p.1 →
        ‖p.1⁻¹ * deriv
          (fun s => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) p.1 θ s) 0‖
          ≤ C * Real.sqrt p.1 := by
      intro p hp
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.mpr hp)]
      calc p.1⁻¹ * |deriv
            (fun s => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) p.1 θ s) 0|
          ≤ p.1⁻¹ * (C * (p.1 ^ ((3:ℝ)/2) / (1+p.1)^2)) :=
            mul_le_mul_of_nonneg_left (hderiv p.1 hp) (le_of_lt (inv_pos.mpr hp))
        _ = C * (Real.sqrt p.1 / (1+p.1)^2) := hident p.1 hp
        _ ≤ C * Real.sqrt p.1 := mul_le_mul_of_nonneg_left
            (div_le_self (Real.sqrt_nonneg p.1) (one_le_pow₀ (by linarith))) hC0
    rw [Metric.tendsto_nhds]
    intro ε hε
    have htend : Filter.Tendsto (fun z : ℝ => C * Real.sqrt z)
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (𝓝 0) := by
      have h1 : Filter.Tendsto (fun z : ℝ => Real.sqrt z)
          (nhdsWithin (0:ℝ) (Set.Ioi 0)) (𝓝 0) := by
        simpa using (Real.continuous_sqrt.tendsto 0).mono_left nhdsWithin_le_nhds
      simpa using (tendsto_const_nhds.mul h1)
    have hev0 : ∀ᶠ z in nhdsWithin (0:ℝ) (Set.Ioi 0), C * Real.sqrt z < ε :=
      htend.eventually (Iio_mem_nhds hε)
    have hev : ∀ᶠ p : ℝ × ℝ in nhdsWithin (0,0) (Set.Ioi (0:ℝ) ×ˢ Set.univ),
        0 < p.1 → C * Real.sqrt p.1 < ε :=
      eventually_nhdsWithin_fst (P := fun z => 0 < z → C * Real.sqrt z < ε)
        (hev0.mono (fun z hz _ => hz))
    filter_upwards [hev, self_mem_nhdsWithin] with p hp hpmem
    rw [dist_zero_right]
    exact lt_of_le_of_lt (hbound p hpmem.1) (hp hpmem.1)

end Work.FTS_RegExport.RXR1
