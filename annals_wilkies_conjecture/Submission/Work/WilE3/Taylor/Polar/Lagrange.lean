import Mathlib
import Submission.Work.WilE3.Defs
import Submission.Work.WilE3.Taylor.Polar.Basic

namespace Work.WilE3.Taylor

set_option autoImplicit false
open Classical Topology
open WilkiesDesign.E

/-
  annals_wilkies_conjecture, AREA E3: the polar set of the Łojasiewicz argument, part 2 — the
  Lagrange step (`∇Φ x ∥ ∇g x` at a constrained extremum, via Mathlib's multiplier theorem), the
  two-sided first-order condition on a closed shell (`fderiv_eq_zero_of_localMin_shell`), and the
  resulting polar form `Polar.of_localMin_shell`: the shell minimisers of `Φ` lie on the polar set.
-/

variable {k : ℕ}

/-- The gradient vector vanishes iff the Fréchet derivative does. -/
theorem grad_eq_zero_iff (Φ : (Fin k → ℝ) → ℝ) (x : Fin k → ℝ) :
    grad Φ x = 0 ↔ fderiv ℝ Φ x = 0 := by
  constructor
  · intro h
    ext v
    rw [zero_apply]
    have hv : v = ∑ i, v i • (Pi.single i (1 : ℝ) : Fin k → ℝ) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hv]
    rw [map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smul, smul_eq_mul]
    have := congrFun h i
    simp only [grad, Pi.zero_apply] at this
    rw [this, mul_zero]
  · intro h
    funext i
    simp only [grad, Pi.zero_apply]
    rw [h, zero_apply]

/-- **The Lagrange step.**  If `x` is a local extremum of `Φ` on the level set `{y | g y = g x}` of a
strictly differentiable `g` and `fderiv ℝ g x ≠ 0`, then `∇Φ x` and `∇g x` are parallel.  This is the
step that puts the minimisers of `Φ` on the shells `{dist (·, Z) = ρ}` into the polar set. -/
theorem fderiv_parallel_of_isLocalExtrOn {Φ g : (Fin k → ℝ) → ℝ} {x : Fin k → ℝ}
    (hextr : IsLocalExtrOn Φ {y | g y = g x} x)
    (hΦ : HasStrictFDerivAt Φ (fderiv ℝ Φ x) x)
    (hg : HasStrictFDerivAt g (fderiv ℝ g x) x) (hg0 : fderiv ℝ g x ≠ 0) :
    ∃ c : ℝ, fderiv ℝ Φ x = c • fderiv ℝ g x := by
  obtain ⟨a, b, hab, hab0⟩ := hextr.exists_multipliers_of_hasStrictFDerivAt_1d hg hΦ
  have hb : b ≠ 0 := by
    intro hb0
    have hzero : a • fderiv ℝ g x = 0 := by
      have h := hab0
      rw [hb0, zero_smul, add_zero] at h
      exact h
    rcases smul_eq_zero.mp hzero with ha0 | hgzero
    · exact hab (by simp [ha0, hb0])
    · exact hg0 hgzero
  refine ⟨-(b⁻¹ * a), ?_⟩
  have h2 : b • fderiv ℝ Φ x = -(a • fderiv ℝ g x) := by
    have h := hab0
    rw [add_comm] at h
    exact eq_neg_of_add_eq_zero_left h
  rw [← inv_smul_smul₀ hb (fderiv ℝ Φ x), h2, smul_neg, smul_smul]
  exact (neg_smul _ _).symm

/-- **The Lagrange step, vector form.**  With the notation of `grad`, a local extremum of `Φ` on a
level set of `g` at a point where `∇g x ≠ 0` has `grad Φ x ∥ grad g x`. -/
theorem grad_parallel_of_isLocalExtrOn {Φ g : (Fin k → ℝ) → ℝ} {x : Fin k → ℝ}
    (hextr : IsLocalExtrOn Φ {y | g y = g x} x)
    (hΦ : HasStrictFDerivAt Φ (fderiv ℝ Φ x) x)
    (hg : HasStrictFDerivAt g (fderiv ℝ g x) x) (hg0 : grad g x ≠ 0) :
    ∃ c : ℝ, grad Φ x = c • grad g x := by
  have hgne : fderiv ℝ g x ≠ 0 := fun h => hg0 ((grad_eq_zero_iff g x).mpr h)
  obtain ⟨c, hc⟩ := fderiv_parallel_of_isLocalExtrOn hextr hΦ hg hgne
  refine ⟨c, funext fun i => ?_⟩
  have := congrArg (fun (L : (Fin k → ℝ) →L[ℝ] ℝ) => L (Pi.single i (1 : ℝ))) hc
  simpa [grad, Pi.smul_apply, smul_eq_mul] using this

/-- **The Lagrange step in polar form.**  If `x` is a local extremum of `Φ` on a level set
`{y | g y = g x}` of a strictly differentiable `g` whose gradient at `x` is parallel to `x - z`
(the case of the *sphere* constraint `g = ‖· - z‖`, where `∇g x = (x - z)/‖x - z‖`), then
`Polar Φ x z`.  This is how the minimisers of `Φ` on the shells `{dist (·, Z) = ρ}` land on the
polar set. -/
theorem Polar.of_isLocalExtrOn {Φ g : (Fin k → ℝ) → ℝ} {x z : Fin k → ℝ}
    (hextr : IsLocalExtrOn Φ {y | g y = g x} x)
    (hΦ : HasStrictFDerivAt Φ (fderiv ℝ Φ x) x)
    (hg : HasStrictFDerivAt g (fderiv ℝ g x) x) (hg0 : grad g x ≠ 0)
    (hz : Φ z = 0) (hpar : ∃ μ : ℝ, grad g x = μ • (x - z)) :
    Polar Φ x z := by
  obtain ⟨c, hc⟩ := grad_parallel_of_isLocalExtrOn hextr hΦ hg hg0
  obtain ⟨μ, hμ⟩ := hpar
  refine Polar.of_smul Φ hz (c := c * μ) ?_
  rw [hc, hμ, smul_smul]

/-- **The shell step in normal-cone (Lagrange) form.**

Let `x₀` be a local minimiser of `Φ` on a closed set `S` — in the application, the closed superlevel
set `S_ρ = {x | ρ ≤ dist (x, Z)}` of the distance to the zero set.  If a direction `v` *and* its
opposite both stay in `S` for small positive times (the tangents of a smooth boundary point of `S`),
then `∇Φ x₀ ⊥ v`.

Applied to every `v ⊥ (x₀ - z₀)`, where `z₀` is a nearest point of `Z` to `x₀`, this is the
normal-cone form of the Lagrange step: `∇Φ x₀ ∈ ((x₀ - z₀)^⊥)^⊥ = ℝ • (x₀ - z₀)`, i.e.
`∇Φ x₀ ∥ x₀ - z₀`.  This is the step that routes the shell minimisers of `Φ` into the polar set `Q`
*without* pretending that the nearest point is locally constant (which it is not: for `Z` a line and
`x₀` off it the nearest point slides); the hypothesis that both tangential directions are feasible
is exactly what the "smooth boundary at `x₀`" hypothesis buys, and it can fail at cusps of the
shell. -/
theorem fderiv_eq_zero_of_localMin_shell {k : ℕ} {Φ : (Fin k → ℝ) → ℝ}
    {S : Set (Fin k → ℝ)} {x₀ v : Fin k → ℝ} (hΦ : HasFDerivAt Φ (fderiv ℝ Φ x₀) x₀)
    (hmin : IsLocalMinOn Φ S x₀)
    (hv : ∀ᶠ t in 𝓝[>] (0 : ℝ), x₀ + t • v ∈ S ∧ x₀ - t • v ∈ S) :
    fderiv ℝ Φ x₀ v = 0 := by
  have key : ∀ w : Fin k → ℝ, (∀ᶠ t in 𝓝[>] (0 : ℝ), x₀ + t • w ∈ S) →
      0 ≤ fderiv ℝ Φ x₀ w := by
    intro w hw
    by_contra hlt
    push Not at hlt
    set g : ℝ → ℝ := fun t => Φ (x₀ + t • w) with hg
    have hgd : HasDerivAt g (fderiv ℝ Φ x₀ w) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => x₀ + t • w) w 0 := by
        simpa using (((hasDerivAt_id (0 : ℝ)).smul_const w).const_add x₀)
      have hΦ' : HasFDerivAt Φ (fderiv ℝ Φ x₀) (x₀ + (0 : ℝ) • w) := by simpa using hΦ
      have h2 := hΦ'.comp_hasDerivAt 0 h1
      rw [hg]
      exact h2
    -- the right difference quotient is negative near `0`
    have hquot : ∀ᶠ t in 𝓝[>] (0 : ℝ), t⁻¹ * (g t - g 0) < 0 := by
      have h := hgd.tendsto_slope_zero_right.eventually (isOpen_Iio.mem_nhds hlt)
      filter_upwards [h] with t ht
      simpa [smul_eq_mul] using ht
    -- the minimiser inequality
    have hmem : ∀ᶠ t in 𝓝[>] (0 : ℝ), Φ x₀ ≤ Φ (x₀ + t • w) := by
      have hcont : Filter.Tendsto (fun t : ℝ => x₀ + t • w) (𝓝[>] (0 : ℝ)) (𝓝 x₀) := by
        have hc : Continuous fun t : ℝ => x₀ + t • w :=
          continuous_const.add (continuous_id.smul continuous_const)
        simpa using (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
      have h2 : Filter.Tendsto (fun t : ℝ => x₀ + t • w) (𝓝[>] (0 : ℝ)) (𝓝[S] x₀) :=
        tendsto_nhdsWithin_iff.mpr ⟨hcont, hw⟩
      exact h2.eventually hmin
    -- combine
    have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), (0 : ℝ) < t := self_mem_nhdsWithin
    rcases (hpos.and (hmem.and hquot)).exists with ⟨t, htpos, htmem, htq⟩
    have hneg : g t - g 0 < 0 := by
      have h1 : t * (t⁻¹ * (g t - g 0)) < 0 := mul_neg_of_pos_of_neg htpos htq
      rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt htpos), one_mul] at h1
    have hlt2 : Φ (x₀ + t • w) < Φ x₀ := by
      have hneg' : Φ (x₀ + t • w) - Φ x₀ < 0 := by simpa [hg] using hneg
      linarith
    linarith
  have h1 : 0 ≤ fderiv ℝ Φ x₀ v := key v (hv.mono fun t ht => ht.1)
  have h2 : 0 ≤ fderiv ℝ Φ x₀ (-v) :=
    key (-v) (hv.mono fun t ht => by simpa [smul_neg, sub_eq_add_neg] using ht.2)
  rw [map_neg] at h2
  linarith

/-- A linear functional vanishing on the kernel of a nonzero linear functional is a multiple of
it.  (The elementary argument: pick `v₀` with `φ v₀ ≠ 0`; for every `v`, the vector
`v - φ v • ((φ v₀)⁻¹ • v₀)` lies in `ker φ`, hence in `ker ψ`, which gives
`ψ v = ψ ((φ v₀)⁻¹ • v₀) * φ v`.) -/
theorem exists_smul_of_ker_le_ker {E : Type*} [AddCommGroup E] [Module ℝ E]
    {φ ψ : E →ₗ[ℝ] ℝ} (hφ : φ ≠ 0) (h : LinearMap.ker φ ≤ LinearMap.ker ψ) :
    ∃ c : ℝ, ψ = c • φ := by
  have hne : ∃ v : E, φ v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hφ (LinearMap.ext hcon)
  obtain ⟨v₀, hv₀⟩ := hne
  refine ⟨ψ ((φ v₀)⁻¹ • v₀), ?_⟩
  ext v
  have h1 : φ (v - φ v • ((φ v₀)⁻¹ • v₀)) = 0 := by
    simp [map_sub, map_smul, smul_eq_mul, inv_mul_cancel₀ hv₀]
  have h2 := LinearMap.mem_ker.mp (h (LinearMap.mem_ker.mpr h1))
  rw [map_sub, map_smul, map_smul] at h2
  show ψ v = (ψ ((φ v₀)⁻¹ • v₀)) * (φ v)
  have h3 : ψ v = φ v * ((φ v₀)⁻¹ * ψ v₀) := by
    simpa [smul_eq_mul, mul_assoc] using sub_eq_zero.mp h2
  rw [map_smul, smul_eq_mul, h3]
  ring

/-- The Fréchet derivative of `Φ` at `x` is the "dot product with the gradient"
`v ↦ ∑ i, v i * (grad Φ x) i`. -/
theorem fderiv_eq_sum_grad {Φ : (Fin k → ℝ) → ℝ} (x v : Fin k → ℝ) :
    fderiv ℝ Φ x v = ∑ i, v i * grad Φ x i := by
  conv_lhs => rw [show v = ∑ i, v i • (Pi.single i (1 : ℝ) : Fin k → ℝ) from by
    funext j; simp [Finset.sum_apply, Pi.single_apply]]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul]
  rfl

/-- **Item 6 of the road: the linear-algebra bridge from the shell step to the polar form.**
If the Fréchet derivative of `Φ` at `x₀` kills every vector whose explicit dot product
`∑ i, v i * w i` with `w` vanishes, then `∇Φ x₀ ∥ w` (for `w ≠ 0`).  Combined with
`fderiv_eq_zero_of_localMin_shell` this converts the shell step into `Polar Φ x₀ z₀`. -/
theorem grad_parallel_of_forall_fderiv_eq_zero {Φ : (Fin k → ℝ) → ℝ} {x₀ w : Fin k → ℝ}
    (hw : w ≠ 0)
    (h : ∀ v : Fin k → ℝ, (∑ i, v i * w i) = 0 → fderiv ℝ Φ x₀ v = 0) :
    ∃ c : ℝ, grad Φ x₀ = c • w := by
  set W : (Fin k → ℝ) →ₗ[ℝ] ℝ := ∑ i, w i • LinearMap.proj i with hW
  have hWv : ∀ v : Fin k → ℝ, W v = ∑ i, w i * v i := by
    intro v
    simp [hW, LinearMap.sum_apply, LinearMap.proj_apply, smul_eq_mul]
  have hWne : W ≠ 0 := by
    intro h0
    apply hw
    funext j
    have := congrArg (fun (φ : (Fin k → ℝ) →ₗ[ℝ] ℝ) => φ (Pi.single j (1 : ℝ))) h0
    rw [LinearMap.zero_apply, hWv] at this
    simpa [Pi.single_apply] using this
  have hker : LinearMap.ker W ≤ LinearMap.ker (fderiv ℝ Φ x₀).toLinearMap := by
    intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    rw [hWv] at hv
    have hv' : ∑ i, v i * w i = 0 := by
      calc ∑ i, v i * w i = ∑ i, w i * v i := Finset.sum_congr rfl fun i _ => by ring
        _ = 0 := hv
    exact h v hv'
  obtain ⟨c, hc⟩ := exists_smul_of_ker_le_ker hWne hker
  refine ⟨c, ?_⟩
  funext j
  have := congrArg (fun (ψ : (Fin k → ℝ) →ₗ[ℝ] ℝ) => ψ (Pi.single j (1 : ℝ))) hc
  simp only [LinearMap.smul_apply, smul_eq_mul] at this
  have hWj : W (Pi.single j (1 : ℝ)) = w j := by
    rw [hWv]; simp [Pi.single_apply]
  have hgradj : (↑(fderiv ℝ Φ x₀) : (Fin k → ℝ) →ₗ[ℝ] ℝ) (Pi.single j (1 : ℝ)) = grad Φ x₀ j := rfl
  rw [hWj, hgradj] at this
  simpa [Pi.smul_apply, smul_eq_mul] using this

/-- **The polar form of the shell step.**  If `x₀` is a local minimiser of `Φ` on `S`, the
tangential directions to `S` at `x₀` (those orthogonal to `x₀ - z₀`) are feasible in both senses,
and `z₀ ∈ Z` (`Φ z₀ = 0`), then `Polar Φ x₀ z₀`.  This is the composite of
`fderiv_eq_zero_of_localMin_shell` and the linear-algebra bridge: the shell minimisers of `Φ` lie on
the polar set `Q`. -/
theorem Polar.of_localMin_shell {Φ : (Fin k → ℝ) → ℝ} {S : Set (Fin k → ℝ)} {x₀ z₀ : Fin k → ℝ}
    (hΦ : HasFDerivAt Φ (fderiv ℝ Φ x₀) x₀) (hmin : IsLocalMinOn Φ S x₀)
    (hfeas : ∀ v : Fin k → ℝ, (∑ i, v i * (x₀ - z₀) i) = 0 →
      ∀ᶠ t in 𝓝[>] (0 : ℝ), x₀ + t • v ∈ S ∧ x₀ - t • v ∈ S)
    (hz : Φ z₀ = 0) (hne : x₀ - z₀ ≠ 0) :
    Polar Φ x₀ z₀ := by
  obtain ⟨c, hc⟩ := grad_parallel_of_forall_fderiv_eq_zero (Φ := Φ) (x₀ := x₀) (w := x₀ - z₀) hne
    (fun v hv => fderiv_eq_zero_of_localMin_shell hΦ hmin (hfeas v hv))
  exact Polar.of_smul Φ hz (c := c) hc


end Work.WilE3.Taylor
