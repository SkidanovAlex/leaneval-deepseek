import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.L62.l62c_basic
import Submission.Work.Horn.basic
import Submission.Work.Repel.pushdown_holo

namespace Work.L62

open MandelDim Set Filter Topology
open scoped Topology

noncomputable section

/-- **Descent of an available upper section.**  Let `σ` be a holomorphic, `T`-equivariant
self-map of the upper horn `Bu` which is a section of `Ẽ - β` (`d.E (σ w) - β = w`) and which is
asymptotically the translation by `β` at the upper end (`σ w - w - β → 0`).  Then `σ` descends
through `π = piExp` to a holomorphic self-map `H = pushdown σ` of `Ω₀ = {0} ∪ π '' Bu` with
`H 0 = 0`, `H'(0) = π β` and `(pushdown (Ẽ - β)) ∘ H = id`.

`H := pushdown σ` already carries all this: `pushdown_piExp` identifies `H (π w) = π (σ w)`,
`pushdown_holo` gives holomorphy on `π '' Bu`, and the derivative at `0` comes from the
asymptotics, since for `ζ → 0` the principal lift `log ζ/(2πi)` escapes to the upper end. -/
theorem avail_descent_upper {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {β : ℂ} {σ : ℂ → ℂ}
    (hσ : DifferentiableOn ℂ σ hd.Bu) (hmem : ∀ w ∈ hd.Bu, σ w ∈ hd.Bu)
    (hsec : ∀ w ∈ hd.Bu, d.E (σ w) - β = w)
    (heq : ∀ w ∈ hd.Bu, σ (w + 1) = σ w + 1)
    (hasymp : Filter.Tendsto (fun w => σ w - w - β) MandelDim.upperEnd (nhds 0)) :
    ∃ H : ℂ → ℂ, H 0 = 0 ∧
      DifferentiableOn ℂ H (insert 0 (MandelDim.piExp '' hd.Bu)) ∧
      (∀ ζ ∈ insert 0 (MandelDim.piExp '' hd.Bu),
        H ζ ∈ insert 0 (MandelDim.piExp '' hd.Bu)) ∧
      HasDerivAt H (MandelDim.piExp β) 0 ∧
      (∀ ζ ∈ insert 0 (MandelDim.piExp '' hd.Bu),
        MandelDim.pushdown (fun u => d.E u - β) (H ζ) = ζ) := by
  have hT : MandelDim.IsTInvariant hd.Bu := hd.Bu_T
  have heqB : ∀ w ∈ hd.Bu, w + 1 ∈ hd.Bu → σ (w + 1) = σ w + 1 := fun w hw _ => heq w hw
  -- the derivative at `0`
  have hderiv : HasDerivAt (MandelDim.pushdown σ) (MandelDim.piExp β) 0 := by
    rw [hasDerivAt_iff_tendsto_slope]
    -- the slope tends to `π β`
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
    rw [slope_def_field, Work.Horn.MandelDim.pushdown_zero σ, sub_zero, sub_zero,
      div_eq_inv_mul]
  refine ⟨MandelDim.pushdown σ, Work.Horn.MandelDim.pushdown_zero σ, ?_, ?_, hderiv, ?_⟩
  · -- holomorphy on `{0} ∪ π '' Bu`
    have hholo : DifferentiableOn ℂ (MandelDim.pushdown σ) (MandelDim.piExp '' hd.Bu) :=
      Work.Repel.pushdown_holo ⟨hT, heq⟩ hσ
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
      exact Or.inr ⟨σ w, hmem w hw, (Work.Horn.MandelDim.pushdown_piExp hT heqB hw).symm⟩
  · -- the section relation pushes down
    intro ζ hζ
    rw [Set.mem_insert_iff] at hζ
    rcases hζ with rfl | hζ
    · rw [Work.Horn.MandelDim.pushdown_zero σ]
      exact Work.Horn.MandelDim.pushdown_zero _
    · obtain ⟨w, hw, rfl⟩ := hζ
      have hHw : MandelDim.pushdown σ (MandelDim.piExp w) = MandelDim.piExp (σ w) :=
        Work.Horn.MandelDim.pushdown_piExp hT heqB hw
      have hEeq : ∀ u ∈ hd.Bu, u + 1 ∈ hd.Bu →
          (fun u => d.E u - β) (u + 1) = (fun u => d.E u - β) u + 1 := by
        intro u hu _
        show d.E (u + 1) - β = d.E u - β + 1
        rw [E_add_one_Bu d hd hu]
        ring
      rw [hHw, Work.Horn.MandelDim.pushdown_piExp hT hEeq (hmem w hw)]
      simp [hsec w hw]

end

end Work.L62
