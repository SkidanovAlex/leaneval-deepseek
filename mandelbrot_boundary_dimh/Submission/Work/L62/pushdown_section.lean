import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.basic
import Submission.Work.L62.avail_descent_upper

namespace Work.L62

open MandelDim Set Filter Topology
open scoped Topology

noncomputable section

/-- If `σ w - w - β → 0` as `w` runs off to the upper end, then `pushdown σ` is differentiable
at `0` with derivative `π β`.  The point is that for `ζ → 0` the principal lift
`w = log ζ/(2πi)` escapes to the upper end while `ζ = π w → 0`, and

`pushdown σ ζ = π (σ w) = π (σ w - w - β) · π w · π β = ζ · π β · (1 + o(1))`. -/
theorem hasDerivAt_pushdown_of_tendsto {β : ℂ} {σ : ℂ → ℂ}
    (hasymp : Filter.Tendsto (fun w => σ w - w - β) MandelDim.upperEnd (nhds 0)) :
    HasDerivAt (MandelDim.pushdown σ) (MandelDim.piExp β) 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hmain : Filter.Tendsto (fun ζ : ℂ => ζ⁻¹ * MandelDim.pushdown σ ζ) (𝓝[≠] (0 : ℂ))
      (𝓝 (MandelDim.piExp β)) := by
    have hcomp : Filter.Tendsto
        (fun ζ : ℂ => σ (Complex.log ζ / (2 * Real.pi * Complex.I))
          - Complex.log ζ / (2 * Real.pi * Complex.I) - β) (𝓝[≠] (0 : ℂ)) (𝓝 0) :=
      hasymp.comp Work.Horn.MandelDim.tendsto_log_div_upperEnd
    have hpicont : Filter.Tendsto MandelDim.piExp (𝓝 (0 : ℂ)) (𝓝 1) := by
      have hc : Continuous MandelDim.piExp := by unfold MandelDim.piExp; fun_prop
      simpa [MandelDim.piExp] using hc.tendsto 0
    have h3 : Filter.Tendsto
        (fun ζ : ℂ => MandelDim.piExp (σ (Complex.log ζ / (2 * Real.pi * Complex.I))
          - Complex.log ζ / (2 * Real.pi * Complex.I) - β)) (𝓝[≠] (0 : ℂ)) (𝓝 1) :=
      hpicont.comp hcomp
    have h4 : Filter.Tendsto
        (fun ζ : ℂ => MandelDim.piExp β * MandelDim.piExp
          (σ (Complex.log ζ / (2 * Real.pi * Complex.I))
            - Complex.log ζ / (2 * Real.pi * Complex.I) - β)) (𝓝[≠] (0 : ℂ))
        (𝓝 (MandelDim.piExp β)) := by
      have h := (tendsto_const_nhds (x := MandelDim.piExp β) (f := 𝓝[≠] (0 : ℂ))).mul h3
      simpa using h
    refine Filter.Tendsto.congr' ?_ h4
    filter_upwards [self_mem_nhdsWithin] with ζ hζ
    have hζne : ζ ≠ 0 := by simpa using hζ
    set w : ℂ := Complex.log ζ / (2 * Real.pi * Complex.I) with hwdef
    have hpush : MandelDim.pushdown σ ζ = MandelDim.piExp (σ w) :=
      Work.Horn.MandelDim.pushdown_of_ne σ hζne
    have hsplit : MandelDim.piExp (σ w)
        = MandelDim.piExp (σ w - w - β) * MandelDim.piExp (w + β) := by
      rw [← Work.Repel.PushdownHolo.piExp_mul]
      congr 1
      ring
    have hwb : MandelDim.piExp (w + β)
        = MandelDim.piExp w * MandelDim.piExp β := Work.Repel.PushdownHolo.piExp_mul w β
    have hw : MandelDim.piExp w = ζ := Work.Horn.MandelDim.piExp_log_div ζ hζne
    rw [hpush, hsplit, hwb, hw]
    field_simp
  refine Filter.Tendsto.congr' ?_ hmain
  filter_upwards [self_mem_nhdsWithin] with ζ hζ
  rw [slope_def_field, Work.Horn.MandelDim.pushdown_zero σ, sub_zero, sub_zero, div_eq_inv_mul]

theorem pushdown_section {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {β : ℂ} (hβ : 0 < β.im) {σ : ℂ → ℂ}
    (hσdiff : DifferentiableOn ℂ σ hd.Bu)
    (hσmem : ∀ w ∈ hd.Bu, σ w ∈ hd.Bu)
    (hσsec : ∀ w ∈ hd.Bu, d.E (σ w) - β = w)
    (hσT : ∀ w ∈ hd.Bu, σ (w + 1) = σ w + 1)
    (hasym : Filter.Tendsto (fun w => σ w - w - β) MandelDim.upperEnd (nhds 0)) :
    DifferentiableOn ℂ (MandelDim.pushdown σ) (insert 0 (MandelDim.piExp '' hd.Bu)) ∧
    Set.MapsTo (MandelDim.pushdown σ) (insert 0 (MandelDim.piExp '' hd.Bu))
      (insert 0 (MandelDim.piExp '' hd.Bu)) ∧
    MandelDim.pushdown σ 0 = 0 ∧ deriv (MandelDim.pushdown σ) 0 = MandelDim.piExp β ∧
    (∀ w ∈ hd.Bu, MandelDim.pushdown σ (MandelDim.piExp w) = MandelDim.piExp (σ w)) := by
  have hT : MandelDim.IsTInvariant hd.Bu := hd.Bu_T
  have heqB : ∀ w ∈ hd.Bu, w + 1 ∈ hd.Bu → σ (w + 1) = σ w + 1 := fun w hw _ => hσT w hw
  have hderiv : HasDerivAt (MandelDim.pushdown σ) (MandelDim.piExp β) 0 :=
    hasDerivAt_pushdown_of_tendsto hasym
  refine ⟨?_, ?_, Work.Horn.MandelDim.pushdown_zero σ, hderiv.deriv, ?_⟩
  · -- holomorphy on `{0} ∪ π '' Bu`
    have hholo : DifferentiableOn ℂ (MandelDim.pushdown σ) (MandelDim.piExp '' hd.Bu) :=
      Work.Repel.pushdown_holo ⟨hT, hσT⟩ hσdiff
    intro ζ hζ
    rw [Set.mem_insert_iff] at hζ
    rcases hζ with rfl | hζ
    · exact hderiv.differentiableAt.differentiableWithinAt
    · rcases hholo ζ hζ with ⟨f', hf'⟩
      exact ⟨f', (hasFDerivWithinAt_insert).mpr hf'⟩
  · -- self-map
    intro ζ hζ
    rw [Set.mem_insert_iff] at hζ
    rcases hζ with rfl | hζ
    · exact Or.inl (Work.Horn.MandelDim.pushdown_zero σ)
    · obtain ⟨w, hw, rfl⟩ := hζ
      exact Or.inr ⟨σ w, hσmem w hw, (Work.Horn.MandelDim.pushdown_piExp hT heqB hw).symm⟩
  · -- the `π`-identity
    intro w hw
    exact Work.Horn.MandelDim.pushdown_piExp hT heqB hw

end

end Work.L62
