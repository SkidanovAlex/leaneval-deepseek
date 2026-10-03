import Mathlib
import Submission.Work.Horn.germF0_base
import Submission.Work.Horn.false_of_const_on_upper_unbounded
import Submission.Work.Horn.false_of_const_on_lower_unbounded

namespace Work.Horn

open MandelDim Set Metric Filter

/-- The lifted horn map `E = Φ ∘ φ` of a `ParabData` is nowhere locally constant on `Bu ∪ Bl`.
If `E` were constant on a neighbourhood of some `w ∈ Bu ∪ Bl`, then by analytic continuation on the
connected component `C` of `d.DE` containing `w` (which contains the half plane `{η < Im}` when
`w ∈ Bu`, resp. `{Im < -η}` when `w ∈ Bl`, because `Bu` and `Bl` are preconnected and contain those
half planes) `E` would take the value `E w` at points of `C` of arbitrarily large `|Im|`; the end
asymptotics `d.E_upper` (`E w - w → 0`) and `d.E_lower` (`E w - w → cl`) forbid this. -/
theorem E_not_locally_const {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {B : Set ℂ} {η : ℝ} {Bu Bl : Set ℂ}
    (hBu : Bu = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (Complex.I * (η + 1)))
    (hBl : Bl = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (-(Complex.I * (η + 1))))
    (hsub : Bu ∪ Bl ⊆ d.DE) (hup : {w : ℂ | η < w.im} ⊆ Bu) (hlo : {w : ℂ | w.im < -η} ⊆ Bl) :
    ∀ w ∈ Bu ∪ Bl, ¬ (∀ᶠ u in nhds w, d.E u = d.E w) := by
  intro w hw hconst
  have hwDE : w ∈ d.DE := hsub hw
  -- `DE` is open and `E` is analytic on it.
  have hDEopen : IsOpen d.DE := by
    rw [show d.DE = d.Dφ ∩ d.φ ⁻¹' MandelDim.ParabolicBasin f₀ D₀ from rfl]
    exact d.φ_holo.continuousOn.isOpen_inter_preimage d.Dφ_open (isOpen_parabolicBasin f₀ D₀)
  have hDE : DifferentiableOn ℂ d.E d.DE := differentiableOn_E d
  have hAn : AnalyticOnNhd ℂ d.E (connectedComponentIn d.DE w) := fun x hx =>
    hDE.analyticAt (hDEopen.mem_nhds (connectedComponentIn_subset d.DE w hx))
  -- Identity principle: `E ≡ E w` on the whole component `C` of `DE` through `w`.
  have hconstC : EqOn d.E (fun _ => d.E w) (connectedComponentIn d.DE w) :=
    AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hAn analyticOnNhd_const
      isPreconnected_connectedComponentIn (mem_connectedComponentIn hwDE)
      (show d.E =ᶠ[nhds w] (fun _ => d.E w) from hconst)
  rcases hw with hwBu | hwBl
  · -- `w ∈ Bu`: the component contains the half plane `{η < im}`.
    have hpre : IsPreconnected Bu := hBu ▸ isPreconnected_connectedComponentIn
    have hCsub : Bu ⊆ connectedComponentIn d.DE w :=
      hpre.subset_connectedComponentIn hwBu (fun x hx => hsub (Or.inl hx))
    have hhalf : {x : ℂ | η < x.im} ⊆ connectedComponentIn d.DE w := fun x hx => hCsub (hup hx)
    refine false_of_const_on_upper_unbounded (E := d.E) (C := connectedComponentIn d.DE w)
      (c := d.E w) (fun M => ?_) (fun u hu => hconstC hu) d.E_upper
    let z : ℂ := Complex.I * ((max M η + 1 : ℝ) : ℂ)
    have hzim : z.im = max M η + 1 := by simp [z, Complex.mul_im]
    refine ⟨z, hhalf ?_, ?_⟩
    · show η < z.im
      rw [hzim]; linarith [le_max_right M η]
    · rw [hzim]; linarith [le_max_left M η]
  · -- `w ∈ Bl`: the component contains the half plane `{im < -η}`.
    have hpre : IsPreconnected Bl := hBl ▸ isPreconnected_connectedComponentIn
    have hCsub : Bl ⊆ connectedComponentIn d.DE w :=
      hpre.subset_connectedComponentIn hwBl (fun x hx => hsub (Or.inr hx))
    have hhalf : {x : ℂ | x.im < -η} ⊆ connectedComponentIn d.DE w := fun x hx => hCsub (hlo hx)
    refine false_of_const_on_lower_unbounded (E := d.E) (C := connectedComponentIn d.DE w)
      (c := d.E w) (fun M => ?_) (fun u hu => hconstC hu) d.E_lower
    let z : ℂ := Complex.I * ((min M (-η) - 1 : ℝ) : ℂ)
    have hzim : z.im = min M (-η) - 1 := by simp [z, Complex.mul_im]
    refine ⟨z, hhalf ?_, ?_⟩
    · show z.im < -η
      rw [hzim]; linarith [min_le_right M (-η)]
    · rw [hzim]; linarith [min_le_left M (-η)]

end Work.Horn
