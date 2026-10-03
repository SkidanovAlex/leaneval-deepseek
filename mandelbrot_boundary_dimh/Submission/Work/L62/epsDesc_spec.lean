import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.basic
import Submission.Work.L62.l62c_head
import Submission.Work.L62.l62c_basic

/-!
# `Work.L62.epsDesc_spec` — the descended correction `d.E - id`

`Work.L62.epsDesc d hd` (defined in `Submission/Work/L62/l62c_head.lean`) is the `1`-periodic
correction `d.E - id` descended to the cylinder: for `ζ ∈ π '' hd.Bu` it is `d.E w - w` for any
lift `w ∈ hd.Bu` of `ζ`, extended by `0` at `0`.

Here we prove that it is continuous on `insert 0 (π '' hd.Bu)` and that it really is the descent
of `d.E - id`.  The proof has four ingredients:

* `E_add_int_Bu` — `d.E` commutes with integer shifts on the `T`-invariant `hd.Bu`;
* `log_div_mem_Bu` — the principal lift `ζ ↦ log ζ / (2πi)` of a point of `π '' hd.Bu` again
  lies in `hd.Bu` (it is a lift, hence an integer translate of any lift in `hd.Bu`);
* `epsDesc_lift_independent` — the value `d.E w - w` depends only on `π w` for `w ∈ hd.Bu`;
* `localSection_piExp` — a local continuous section `lam` of `π` through any `w₀`, used to make
  `d.E ∘ lam - lam` — hence `epsDesc` — continuous at every point of `π '' hd.Bu`;
  continuity at `0` is the upper-end limit `ParabData.E_upper` composed with the principal lift,
  which tends to the upper end as `ζ → 0`.
-/

namespace Work.L62

open MandelDim Set Filter Topology
open scoped Topology

noncomputable section

variable {g₀ : ℂ → ℂ} {D : Set ℂ}

/-! ## Integer shifts of `d.E` on the horn -/

/-- `d.E` commutes with integer shifts on the `T`-invariant horn `hd.Bu` (iterated
`E_add_one_Bu`). -/
theorem E_add_int_Bu (d : MandelDim.ParabData g₀ D) (hd : MandelDim.HornData d) {w : ℂ}
    (hw : w ∈ hd.Bu) (k : ℤ) : d.E (w + (k : ℂ)) = d.E w + (k : ℂ) :=
  Work.Horn.MandelDim.E_add_int hd.Bu_T (fun _u hu _ => E_add_one_Bu d hd hu) hw k

/-! ## The principal lift of a point of `π '' hd.Bu` -/

/-- The principal lift `ζ ↦ log ζ / (2πi)` of a point of `π '' hd.Bu` again lies in `hd.Bu`:
it is a lift of `ζ ≠ 0`, hence differs from any lift in `hd.Bu` by an integer, and `hd.Bu` is
`T`-invariant. -/
theorem log_div_mem_Bu (d : MandelDim.ParabData g₀ D) (hd : MandelDim.HornData d) {ζ : ℂ}
    (hζ : ζ ∈ MandelDim.piExp '' hd.Bu) :
    Complex.log ζ / (2 * Real.pi * Complex.I) ∈ hd.Bu := by
  obtain ⟨w, hw, rfl⟩ := hζ
  have hlift : MandelDim.piExp (Complex.log (MandelDim.piExp w) / (2 * Real.pi * Complex.I))
      = MandelDim.piExp w :=
    Work.Horn.MandelDim.piExp_log_div _ (Work.Horn.MandelDim.piExp_ne_zero w)
  obtain ⟨k, hk⟩ := Work.Horn.MandelDim.piExp_eq_iff.mp hlift
  rw [hk]
  exact Work.Horn.MandelDim.IsTInvariant.add_int hd.Bu_T hw k

/-- **The correction descends.**  Two lifts in the `T`-invariant horn `hd.Bu` of the same
cylinder point give the same value of `d.E - id`. -/
theorem epsDesc_lift_independent (d : MandelDim.ParabData g₀ D) (hd : MandelDim.HornData d)
    {w w' : ℂ} (_hw : w ∈ hd.Bu) (hw' : w' ∈ hd.Bu)
    (h : MandelDim.piExp w = MandelDim.piExp w') : d.E w - w = d.E w' - w' := by
  obtain ⟨k, hk⟩ := Work.Horn.MandelDim.piExp_eq_iff.mp h
  rw [hk, E_add_int_Bu d hd hw' k]
  ring

/-- The descent of the correction `d.E - id` to the cylinder, evaluated through the principal
lift: on `hd.Bu` the value at `π w` is `d.E w - w`. -/
theorem epsDesc_piExp (d : MandelDim.ParabData g₀ D) (hd : MandelDim.HornData d) {w : ℂ}
    (hw : w ∈ hd.Bu) : epsDesc d hd (MandelDim.piExp w) = d.E w - w := by
  have hlift : MandelDim.piExp (Complex.log (MandelDim.piExp w) / (2 * Real.pi * Complex.I))
      = MandelDim.piExp w :=
    Work.Horn.MandelDim.piExp_log_div _ (Work.Horn.MandelDim.piExp_ne_zero w)
  obtain ⟨k, hk⟩ := Work.Horn.MandelDim.piExp_eq_iff.mp hlift
  rw [epsDesc, ite_eq_right (Work.Horn.MandelDim.piExp_ne_zero w), hk,
    E_add_int_Bu d hd hw k]
  ring

/-! ## A local section of `π` -/

/-- `π (a + b) = π a · π b`. -/
theorem piExp_add' (a b : ℂ) :
    MandelDim.piExp (a + b) = MandelDim.piExp a * MandelDim.piExp b := by
  rw [MandelDim.piExp, MandelDim.piExp, MandelDim.piExp, ← Complex.exp_add]
  congr 1
  ring

/-- **Local section of `π`.**  The explicit map `lam z = w₀ + log (z / π w₀) / (2πi)` is
continuous at `π w₀`, fixes `w₀` there, satisfies `π (lam z) = z` for every `z ≠ 0`, and maps a
neighbourhood of `π w₀` into any prescribed ball around `w₀`. -/
theorem localSection_piExp {w₀ : ℂ} {r : ℝ} (hr : 0 < r) :
    ∃ lam : ℂ → ℂ, ContinuousAt lam (MandelDim.piExp w₀) ∧ lam (MandelDim.piExp w₀) = w₀ ∧
      (∀ z : ℂ, z ≠ 0 → MandelDim.piExp (lam z) = z) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℂ, z ∈ Metric.ball (MandelDim.piExp w₀) δ →
        lam z ∈ Metric.ball w₀ r := by
  have hne : MandelDim.piExp w₀ ≠ 0 := Work.Horn.MandelDim.piExp_ne_zero w₀
  let lam : ℂ → ℂ := fun z =>
    w₀ + Complex.log (z / MandelDim.piExp w₀) / (2 * Real.pi * Complex.I)
  have hcont : ContinuousAt lam (MandelDim.piExp w₀) := by
    have hz : MandelDim.piExp w₀ / MandelDim.piExp w₀ ∈ Complex.slitPlane := by
      rw [div_self hne]; exact Complex.one_mem_slitPlane
    have h1 : ContinuousAt (fun z : ℂ => Complex.log (z / MandelDim.piExp w₀))
        (MandelDim.piExp w₀) :=
      (continuousAt_id.div_const _).clog hz
    exact (h1.div_const (2 * Real.pi * Complex.I)).const_add w₀
  have hval : lam (MandelDim.piExp w₀) = w₀ := by
    show w₀ + Complex.log (MandelDim.piExp w₀ / MandelDim.piExp w₀) / (2 * Real.pi * Complex.I)
      = w₀
    rw [div_self hne, Complex.log_one, zero_div, add_zero]
  have hsect : ∀ z : ℂ, z ≠ 0 → MandelDim.piExp (lam z) = z := by
    intro z hz
    show MandelDim.piExp
      (w₀ + Complex.log (z / MandelDim.piExp w₀) / (2 * Real.pi * Complex.I)) = z
    rw [piExp_add',
      Work.Horn.MandelDim.piExp_log_div (z / MandelDim.piExp w₀) (div_ne_zero hz hne)]
    field_simp
  refine ⟨lam, hcont, hval, hsect, ?_⟩
  have hball : lam ⁻¹' Metric.ball w₀ r ∈ 𝓝 (MandelDim.piExp w₀) := by
    have h := hcont
    change Tendsto lam (𝓝 (MandelDim.piExp w₀)) (𝓝 (lam (MandelDim.piExp w₀))) at h
    rw [hval] at h
    exact h (Metric.ball_mem_nhds w₀ hr)
  exact Metric.mem_nhds_iff.mp hball

/-! ## Continuity of `epsDesc` -/

/-- `epsDesc` is continuous at `0` within `π '' hd.Bu`: this is the upper end.  Along `π '' hd.Bu`
the principal lift `ζ ↦ log ζ / (2πi)` tends to the upper end (`Im → +∞`) as `ζ → 0`, and
`d.E w - w → 0` there (`ParabData.E_upper`). -/
theorem continuousWithinAt_epsDesc_zero (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) :
    ContinuousWithinAt (epsDesc d hd) (MandelDim.piExp '' hd.Bu) 0 := by
  have hsub : MandelDim.piExp '' hd.Bu ⊆ ({0}ᶜ : Set ℂ) := by
    rintro ζ ⟨w, -, rfl⟩
    exact Work.Horn.MandelDim.piExp_ne_zero w
  have hEupper : Tendsto (fun w : ℂ => d.E w - w) upperEnd (𝓝 0) := by
    simpa only [MandelDim.ParabData.E] using d.E_upper
  have hcomp : Tendsto (fun ζ : ℂ => d.E (Complex.log ζ / (2 * Real.pi * Complex.I))
        - Complex.log ζ / (2 * Real.pi * Complex.I)) (𝓝[≠] (0 : ℂ)) (𝓝 0) :=
    hEupper.comp Work.Horn.MandelDim.tendsto_log_div_upperEnd
  have hcomp' : Tendsto (fun ζ : ℂ => d.E (Complex.log ζ / (2 * Real.pi * Complex.I))
        - Complex.log ζ / (2 * Real.pi * Complex.I))
      (nhdsWithin (0 : ℂ) (MandelDim.piExp '' hd.Bu)) (𝓝 0) :=
    hcomp.mono_left (nhdsWithin_mono 0 hsub)
  have hev : ∀ᶠ ζ in nhdsWithin (0 : ℂ) (MandelDim.piExp '' hd.Bu),
      d.E (Complex.log ζ / (2 * Real.pi * Complex.I))
        - Complex.log ζ / (2 * Real.pi * Complex.I) = epsDesc d hd ζ := by
    filter_upwards [self_mem_nhdsWithin] with ζ hζ
    obtain ⟨w, -, rfl⟩ := hζ
    rw [epsDesc, ite_eq_right (Work.Horn.MandelDim.piExp_ne_zero w)]
  have h0 : epsDesc d hd 0 = 0 := by simp [epsDesc]
  have hmain : Tendsto (epsDesc d hd) (nhdsWithin (0 : ℂ) (MandelDim.piExp '' hd.Bu))
      (𝓝 (epsDesc d hd 0)) := by
    rw [h0]
    exact Tendsto.congr' hev hcomp'
  exact hmain

/-- `epsDesc` is continuous at every point of `π '' hd.Bu`: a local continuous section `lam` of
`π` turns `epsDesc` into the honest continuous function `d.E ∘ lam - lam`, and
`epsDesc_lift_independent` says the two agree near the point. -/
theorem continuousWithinAt_epsDesc_of_mem (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {ζ₀ : ℂ} (hζ₀ : ζ₀ ∈ MandelDim.piExp '' hd.Bu) :
    ContinuousWithinAt (epsDesc d hd) (MandelDim.piExp '' hd.Bu) ζ₀ := by
  have hζ₀ne : ζ₀ ≠ 0 := by
    obtain ⟨w, -, rfl⟩ := hζ₀
    exact Work.Horn.MandelDim.piExp_ne_zero w
  have hpiw : MandelDim.piExp (Complex.log ζ₀ / (2 * Real.pi * Complex.I)) = ζ₀ :=
    Work.Horn.MandelDim.piExp_log_div ζ₀ hζ₀ne
  have hw₀ : Complex.log ζ₀ / (2 * Real.pi * Complex.I) ∈ hd.Bu := log_div_mem_Bu d hd hζ₀
  obtain ⟨r, hr, hballr⟩ := Metric.mem_nhds_iff.mp (hd.Bu_open.mem_nhds hw₀)
  obtain ⟨lam, hlam_cont, hlam_val, hlam_sect, δ, hδ, hδball⟩ :=
    localSection_piExp (w₀ := Complex.log ζ₀ / (2 * Real.pi * Complex.I)) hr
  rw [hpiw] at hlam_cont hlam_val hδball
  have hEdiff : DifferentiableOn ℂ d.E hd.Bu :=
    d.Φ_holo.comp (d.φ_holo.mono fun w hw => (hd.sub (Or.inl hw)).1)
      fun w hw => (hd.sub (Or.inl hw)).2
  have hlam_mem : lam ζ₀ ∈ hd.Bu := by rw [hlam_val]; exact hw₀
  have hcont_f : ContinuousAt (fun z : ℂ => d.E (lam z) - lam z) ζ₀ := by
    have h2 : ContinuousAt (fun z : ℂ => d.E (lam z)) ζ₀ :=
      (hEdiff.continuousOn.continuousAt (hd.Bu_open.mem_nhds hlam_mem)).comp hlam_cont
    exact h2.sub hlam_cont
  have hev : (fun z : ℂ => d.E (lam z) - lam z)
      =ᶠ[nhdsWithin ζ₀ (MandelDim.piExp '' hd.Bu)] (epsDesc d hd) := by
    show ∀ᶠ z in nhdsWithin ζ₀ (MandelDim.piExp '' hd.Bu), d.E (lam z) - lam z = epsDesc d hd z
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Metric.ball_mem_nhds ζ₀ hδ] with z hzball hzU
    have hzne : z ≠ 0 := by
      obtain ⟨w, -, rfl⟩ := hzU
      exact Work.Horn.MandelDim.piExp_ne_zero w
    have hzBu : lam z ∈ hd.Bu := hballr (hδball z hzball)
    have hlifts : MandelDim.piExp (lam z)
        = MandelDim.piExp (Complex.log z / (2 * Real.pi * Complex.I)) := by
      rw [hlam_sect z hzne, Work.Horn.MandelDim.piExp_log_div z hzne]
    rw [epsDesc, ite_eq_right hzne]
    exact epsDesc_lift_independent d hd hzBu (log_div_mem_Bu d hd hzU) hlifts
  have hx : epsDesc d hd ζ₀ = d.E (lam ζ₀) - lam ζ₀ := by
    rw [epsDesc, ite_eq_right hζ₀ne, ← hlam_val]
  exact hcont_f.continuousWithinAt.congr_of_eventuallyEq hev.symm hx

/-! ## The descended correction `d.E - id` is continuous and descends -/

/-- **The descended correction `d.E - id` is continuous and descends.**

`Work.L62.epsDesc` is the `1`-periodic correction descended to the cylinder: for `ζ ∈ π '' Bu` it is
`d.E w - w` for any lift `w ∈ Bu` of `ζ` (well defined by `E_add_one_Bu` + `hd.Bu_T`), extended by
`0` at `0` (its limit at the upper end, `ParabData.E_upper`), and defined concretely in
`Submission/Work/L62/l62c_head.lean` via the principal lift `ζ ↦ log ζ / (2πi)`, which lands in the
`T`-invariant `Bu` whenever `ζ ∈ π '' Bu`.

Conclusion: `epsDesc` is continuous on `insert 0 (π '' hd.Bu)`, and on `hd.Bu` it is the descent of
`d.E - id`.  Consequence (the intended use): `epsDesc` is *bounded on the compact subsets* of
`π '' hd.Bu`, which is what turns the joint continuity `Work.L62.cylinder_model` of
`(β, ζ) ↦ H β ζ` into β-uniform bounds on the head of the chain of Lemma 6.2
(`W (j+1) = σ_β '' W j` with `σ_β` the section of `d.E - β`, using
`σ_β w = w + β - epsDesc (π (σ_β w))`). -/
theorem epsDesc_spec {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) :
    ContinuousOn (Work.L62.epsDesc d hd) (Set.insert 0 (MandelDim.piExp '' hd.Bu)) ∧
      (∀ w ∈ hd.Bu, MandelDim.piExp w ≠ 0 →
        d.E w - w = Work.L62.epsDesc d hd (MandelDim.piExp w)) := by
  constructor
  · intro ζ hζ
    rcases hζ with h0 | hζU
    · rw [h0]
      exact (continuousWithinAt_epsDesc_zero d hd).insert
    · exact (continuousWithinAt_epsDesc_of_mem d hd hζU).insert'
  · intro w hw _
    exact (epsDesc_piExp d hd hw).symm

end

end Work.L62
