import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.L62.exists_section_horn
import Submission.Work.L62.cartan
import Submission.Work.L62.branch_unique
import Submission.Work.L62.l62c_basic
import Submission.Work.L62.section_unique
import Submission.Work.Horn.basic
import Submission.Work.Horn.pushdown_differentiableOn_punctured
import Submission.Work.Repel.pushdown_holo
import Submission.Work.Repel.pushdown_deriv
import Submission.Work.L62.deep_preimage_deep
import Submission.Work.L62.tau0_Bl_geometry

/-!
# `Work.L62.avail_down`: availability of the lower horn forces `Im β < Im cl`

Shishikura's Lemma 6.2 pairs every `β ∈ ℂ/ℤ` with the end (`Bu` or `Bl`) of the horn map whose
domain avoids the critical value of `ĥ = Ẽ - β`.  This file proves the *lower*-end case:
if `Bl` avoids the critical class `v + ℤ - β`, then the drift of the inverse branch at the lower
end is strictly negative in imaginary part, i.e. `β.im < cl.im`, where `cl` is the lower-end
limit of `Ẽ - id`.

Route (the mirror of the upper-end case, carried out in the `τ₀`-coordinate `w = -1/ζ`):

* `deep_preimage_deep` gives the deep inverse branch `u` of `ĥ = d.E - β` on a deep half plane;
* `exists_section_horn_Bl` + `section_unique` produce a global holomorphic section `σ : Bl → Bl`
  of `ĥ` agreeing with `u` on that half plane; hence `σ` is `T`-equivariant (identity theorem) and
  drifts by `β - cl` at the lower end;
* pushing down (`pushdown_holo`) and reflecting with `τ₀` gives a holomorphic self-map `Hr` of the
  bounded domain `Ω = {0} ∪ τ₀(π(Bl))` with `Hr 0 = 0` and `deriv Hr 0 = exp (-2πi(β - cl))`;
* `Work.L62.cartan` gives `‖deriv Hr 0‖ ≤ 1`, i.e. `Im β ≤ Im cl`; in the equality case `Hr` is a
  bijection of `Ω`, which makes `pushdown d.E` injective on `π '' Bl`, contradicting the
  infinite-degree field `HornData.inf_l`.
-/

namespace Work.L62

open MandelDim Set Filter Topology Metric
open Work.Horn.MandelDim
open scoped Topology

noncomputable section

/-! ## Elementary facts about `π`, `τ₀` -/

lemma piExp_neg' (z : ℂ) : MandelDim.piExp (-z) = (MandelDim.piExp z)⁻¹ := by
  rw [MandelDim.piExp, MandelDim.piExp,
    show 2 * ↑Real.pi * Complex.I * -z = -(2 * ↑Real.pi * Complex.I * z) by ring,
    Complex.exp_neg]

lemma piExp_mul' (a b : ℂ) : MandelDim.piExp (a + b) = MandelDim.piExp a * MandelDim.piExp b :=
  Work.Repel.piExp_add a b

lemma ad_tau0_piExp (z : ℂ) : MandelDim.tau0 (MandelDim.piExp z) = -(MandelDim.piExp (-z)) := by
  simp only [MandelDim.tau0]
  rw [div_eq_mul_inv, neg_mul, one_mul, piExp_neg']

lemma tau0_ne_zero {z : ℂ} (hz : z ≠ 0) : MandelDim.tau0 z ≠ 0 := by
  simp only [MandelDim.tau0]
  exact div_ne_zero (by norm_num) hz

lemma tau0_invol (z : ℂ) (hz : z ≠ 0) : MandelDim.tau0 (MandelDim.tau0 z) = z := by
  simp only [MandelDim.tau0]
  field_simp

lemma differentiableAt_tau0 {z : ℂ} (hz : z ≠ 0) : DifferentiableAt ℂ MandelDim.tau0 z := by
  have h1 : MandelDim.tau0 = fun z : ℂ => (-1 : ℂ) / z := rfl
  rw [h1]
  exact (differentiableAt_const (c := (-1 : ℂ))).div differentiableAt_id (by simpa using hz)

/-- The `π`-image of an open set is open (`π = exp ∘ (2πi ·)` is a composition of open maps). -/
lemma ad_isOpen_piExp_image {D : Set ℂ} (hD : IsOpen D) :
    IsOpen (MandelDim.piExp '' D) := by
  have hπ : MandelDim.piExp = Complex.exp ∘ (fun z : ℂ => 2 * Real.pi * Complex.I * z) := rfl
  rw [hπ]
  exact (Complex.isOpenMap_exp.comp
    (Homeomorph.mulLeft₀ (2 * Real.pi * Complex.I) (by simp)).isOpenMap) D hD

/-! ## The section of `ĥ = d.E - β` over the lower component -/

/-- Lower-component analogue of `Work.L62.exists_section_horn`. -/
theorem exists_section_horn_Bl {g₀ : ℂ → ℂ} {D : Set ℂ} (d : ParabData g₀ D)
    (hd : HornData d) {β : ℂ} {Y : Set ℂ} (hYo : IsOpen Y)
    (hYsc : SimplyConnectedSpace Y) (havoid : ∀ ζ ∈ Y, ∀ k : ℤ, ζ + β ≠ hd.v + (k : ℂ))
    {y₀ : ℂ} (hy₀ : y₀ ∈ Y) {x₀ : ℂ} (hx₀ : x₀ ∈ hd.Bl) (hxy : d.E x₀ - β = y₀) :
    ∃ σ : ℂ → ℂ, DifferentiableOn ℂ σ Y ∧ σ y₀ = x₀ ∧
      (∀ y ∈ Y, σ y ∈ hd.Bl ∧ d.E (σ y) - β = y) := by
  have hsub : hd.Bl ⊆ d.DE := fun w hw => hd.sub (Or.inr hw)
  have hφdiff : DifferentiableOn ℂ d.φ hd.Bl := d.φ_holo.mono (fun w hw => (hsub hw).1)
  have hE : DifferentiableOn ℂ d.E hd.Bl :=
    d.Φ_holo.comp hφdiff (fun w hw => (hsub hw).2)
  have hp : DifferentiableOn ℂ (fun z => d.E z - β) hd.Bl := hE.sub (differentiableOn_const β)
  have hcov : IsCoveringMapOn (fun z : hd.Bl => d.E z - β) Y :=
    (hd.cov_l.homeomorph_comp (Homeomorph.subRight β)).mono (fun y hy k => havoid y hy k)
  obtain ⟨σ, hσd, hσ0, hσ⟩ := lift_section hd.Bl_open hp hYo hYsc hcov hy₀ hx₀ hxy
  exact ⟨σ, hσd, hσ0, fun y hy => ⟨(hσ y hy).1, (hσ y hy).2⟩⟩

theorem avail_down {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {β cl : ℂ}
    (hcl : Filter.Tendsto (fun w => d.E w - w) MandelDim.lowerEnd (nhds cl))
    (havoid : ∀ w ∈ hd.Bl, ∀ k : ℤ, w + β ≠ hd.v + (k : ℂ)) : β.im < cl.im := by
  classical
  -- ## 0. the deep inverse branch of `ĥ = d.E - β`
  have hDopen : IsOpen {w : ℂ | d.η₀ < |w.im|} :=
    isOpen_lt continuous_const Complex.continuous_im.abs
  have hYsub : {w : ℂ | w.im < -|d.η₀| - 1} ⊆ {w : ℂ | d.η₀ < |w.im|} := by
    intro w hw
    simp only [Set.mem_ofPred_eq] at hw ⊢
    rw [abs_of_neg (by linarith [abs_nonneg d.η₀])]
    have h1 : d.η₀ ≤ |d.η₀| := le_abs_self d.η₀
    linarith
  have hgdiff : DifferentiableOn ℂ (fun v : ℂ => (d.E v - v) - cl) {w : ℂ | d.η₀ < |w.im|} :=
    ((Work.Horn.differentiableOn_E_abs_im_gt d).sub differentiableOn_id).sub_const cl
  have hglim : Filter.Tendsto (fun v : ℂ => (d.E v - v) - cl)
      (Filter.comap Complex.im Filter.atBot) (nhds 0) := by
    have h1 := hcl.sub_const cl
    rw [sub_self] at h1
    simpa [MandelDim.lowerEnd] using h1
  obtain ⟨L, Lz, hLY, hLA', hLzA, u, hud, hu1, hu2, hu3⟩ :=
    deep_preimage_deep (c := cl - β) hDopen hYsub hgdiff hglim (-hd.η - 1) (-hd.η - 1)
  -- ## 1. bookkeeping for the deep half planes
  have hLη : L < -hd.η := by linarith
  have hLzη : Lz < -hd.η := by linarith
  have huBl : ∀ z : ℂ, z.im < Lz → u z ∈ hd.Bl := by
    intro z hz
    apply hd.lower
    show (u z).im < -hd.η
    linarith [(hu1 z hz).1]
  have hsol : ∀ z : ℂ, z.im < Lz → d.E (u z) - β = z := by
    intro z hz
    have h := (hu1 z hz).2
    linear_combination h
  have hHdBl : ∀ z : ℂ, z.im < Lz → z ∈ hd.Bl := by
    intro z hz
    apply hd.lower
    show z.im < -hd.η
    linarith
  have huT : ∀ z : ℂ, z.im < Lz → u (z + 1) = u z + 1 := by
    intro z hz
    have hz1 : (z + 1).im < Lz := by simpa using hz
    have hper : ∀ v : ℂ, v.im < L → (d.E (v + 1) - (v + 1)) - cl = (d.E v - v) - cl := by
      intro v hv
      have hvBl : v ∈ hd.Bl := by
        apply hd.lower
        show v.im < -hd.η
        linarith
      rw [E_add_one_Bl d hd hvBl]
      ring
    have h1 : (u z + 1) + (cl - β) + ((d.E (u z + 1) - (u z + 1)) - cl) = z + 1 := by
      rw [hper (u z) (hu1 z hz).1]
      have h := (hu1 z hz).2
      linear_combination h
    exact (hu2 (z + 1) hz1 (u z + 1) (by simpa using (hu1 z hz).1) h1).symm
  -- ## 2. the global section through the deep point
  obtain ⟨y₀ : ℂ, hy₀ : y₀.im < Lz⟩ : ∃ y : ℂ, y.im < Lz := ⟨(Lz - 1) * Complex.I, by simp⟩
  set x₀ : ℂ := u y₀ with hx₀def
  have hx₀Bl : x₀ ∈ hd.Bl := by rw [hx₀def]; exact huBl y₀ hy₀
  have hx₀eq : d.E x₀ - β = y₀ := by rw [hx₀def]; exact hsol y₀ hy₀
  obtain ⟨σ, hσd, hσy₀, hσsec⟩ :=
    exists_section_horn_Bl d hd hd.Bl_open hd.Bl_sc havoid (hHdBl y₀ hy₀) hx₀Bl hx₀eq
  -- ## 3. `σ = u` on the deep half plane
  have hHdopen : IsOpen {z : ℂ | z.im < Lz} := isOpen_lt Complex.continuous_im continuous_const
  have hpBl : DifferentiableOn ℂ (fun z => d.E z - β) hd.Bl := by
    have hsub : hd.Bl ⊆ d.DE := fun w hw => hd.sub (Or.inr hw)
    exact (d.Φ_holo.comp (d.φ_holo.mono (fun w hw => (hsub hw).1))
      (fun w hw => (hsub hw).2)).sub (differentiableOn_const β)
  have hσu : ∀ z : ℂ, z.im < Lz → σ z = u z :=
    section_unique hd.Bl_open hHdopen
      (convex_halfSpace_im_lt Lz).isPreconnected
      (fun z hz => hHdBl z hz) hpBl
      (hσd.mono (fun z hz => hHdBl z hz)) hud
      (fun y hy => hσsec y (hHdBl y hy))
      (fun y hy => ⟨huBl y hy, hsol y hy⟩) hy₀ (by rw [hσy₀, hx₀def])
  -- ## 4. `σ` is `T`-equivariant on `hd.Bl`
  have hσT : ∀ w ∈ hd.Bl, σ (w + 1) = σ w + 1 := by
    set F : ℂ → ℂ := fun w => σ (w + 1) - σ w - 1 with hFdef
    have hFd : DifferentiableOn ℂ F hd.Bl := by
      have h1 : DifferentiableOn ℂ (fun w => σ (w + 1)) hd.Bl :=
        hσd.comp (differentiableOn_id.add (differentiableOn_const 1))
          (fun w hw => (hd.Bl_T w).mp hw)
      exact ((h1.sub hσd).sub (differentiableOn_const 1))
    have hF0 : ∀ z : ℂ, z.im < Lz → F z = 0 := by
      intro z hz
      have hz1 : (z + 1).im < Lz := by simpa using hz
      simp only [hFdef]
      rw [hσu (z + 1) hz1, hσu z hz, huT z hz]
      ring
    have hEq := (hFd.analyticOnNhd hd.Bl_open).eqOn_of_preconnected_of_eventuallyEq
      analyticOnNhd_const hd.Bl_conn.isPreconnected (hHdBl y₀ hy₀)
      (Filter.eventually_of_mem (hHdopen.mem_nhds hy₀) (fun z hz => hF0 z hz))
    intro w hw
    have h := hEq hw
    simp only [hFdef, Pi.zero_apply] at h
    linear_combination h
  -- ## 5. the drift of `σ` at the lower end
  have hdrift : Filter.Tendsto (fun z : ℂ => σ z - z - (β - cl)) lowerEnd (nhds 0) := by
    have h1 : ∀ᶠ z : ℂ in lowerEnd, z.im < Lz := by
      rw [MandelDim.lowerEnd, Filter.eventually_comap]
      refine Filter.mem_atBot_sets.mpr ⟨Lz - 1, fun t ht a ha => ?_⟩
      linarith
    have h2 : Filter.Tendsto (fun z : ℂ => u z - z + (cl - β)) lowerEnd (nhds 0) := by
      simpa [MandelDim.lowerEnd] using hu3
    refine h2.congr' ?_
    filter_upwards [h1] with z hz
    rw [hσu z hz]
    ring
  -- ## 6. the pushdown and its functional equation
  have hHd : DifferentiableOn ℂ (MandelDim.pushdown σ) (MandelDim.piExp '' hd.Bl) :=
    Work.Repel.pushdown_holo ⟨hd.Bl_T, fun w hw => hσT w hw⟩ hσd
  have hHfun : ∀ v : ℂ, v ∈ hd.Bl →
      MandelDim.pushdown σ (MandelDim.piExp v) = MandelDim.piExp (σ v) :=
    fun v hv => Work.Horn.MandelDim.pushdown_piExp hd.Bl_T (fun w hw _ => hσT w hw) hv
  have hgfun : ∀ v : ℂ, v ∈ hd.Bl →
      MandelDim.pushdown d.E (MandelDim.piExp v) = MandelDim.piExp (d.E v) :=
    fun v hv => Work.Horn.MandelDim.pushdown_piExp hd.Bl_T (fun w hw _ => E_add_one_Bl d hd hw) hv
  have hcyl : ∀ v : ℂ, v ∈ hd.Bl →
      MandelDim.pushdown d.E (MandelDim.pushdown σ (MandelDim.piExp v)) =
        MandelDim.piExp v * MandelDim.piExp β := by
    intro v hv
    have hEqv : d.E (σ v) = v + β := by
      have h := (hσsec v hv).2
      linear_combination h
    rw [hHfun v hv, hgfun (σ v) (hσsec v hv).1, hEqv]
    exact piExp_mul' v β
  -- ## 7. the reflected self-map of the bounded domain `Ω`
  obtain ⟨hΩopen, hΩbdd, hΩpc, -, -⟩ := tau0_Bl_geometry d hd
  set Ω : Set ℂ := insert 0 (MandelDim.tau0 '' (MandelDim.piExp '' hd.Bl)) with hΩdef
  have h0Ω : (0 : ℂ) ∈ Ω := by rw [hΩdef]; exact Or.inl rfl
  set Hr : ℂ → ℂ :=
    fun w => if w = 0 then 0 else MandelDim.tau0 (MandelDim.pushdown σ (MandelDim.tau0 w))
    with hHrdef
  have hHr0 : Hr 0 = 0 := by simp [hHrdef]
  have hHrval : ∀ w : ℂ, w ≠ 0 →
      Hr w = MandelDim.tau0 (MandelDim.pushdown σ (MandelDim.tau0 w)) := by
    intro w hw; rw [hHrdef]; simp only [if_neg hw]
  have htau0mem : ∀ w : ℂ, w ∈ Ω → w ≠ 0 → MandelDim.tau0 w ∈ MandelDim.piExp '' hd.Bl := by
    intro w hw hw0
    rw [hΩdef] at hw
    rcases hw with h | h
    · exact absurd h hw0
    · obtain ⟨ζ, hζ, rfl⟩ := h
      have hζ0 : ζ ≠ 0 := by
        rcases hζ with ⟨a, -, ha⟩
        exact fun h => piExp_ne_zero a (ha.trans h)
      rw [tau0_invol ζ hζ0]
      exact hζ
  have hHrΩ : MapsTo Hr Ω Ω := by
    intro w hw
    by_cases hw0 : w = 0
    · rw [hw0, hHr0]; exact h0Ω
    · have hmem : MandelDim.tau0 w ∈ MandelDim.piExp '' hd.Bl := htau0mem w hw hw0
      obtain ⟨v, hv, hvw⟩ := hmem
      rw [hHrval w hw0]
      have hHv : MandelDim.pushdown σ (MandelDim.tau0 w) = MandelDim.piExp (σ v) := by
        rw [← hvw, hHfun v hv]
      rw [hHv]
      exact Or.inr ⟨MandelDim.piExp (σ v), ⟨σ v, (hσsec v hv).1, rfl⟩, rfl⟩
  have hHr_ne : ∀ w : ℂ, w ≠ 0 → Hr w ≠ 0 := by
    intro w hw
    rw [hHrval w hw]
    have htw : MandelDim.tau0 w ≠ 0 := tau0_ne_zero hw
    rw [Work.Horn.MandelDim.pushdown_of_ne σ htw]
    exact tau0_ne_zero (piExp_ne_zero _)
  -- conjugation: `H (τ₀ z) = τ₀ (Hr z)`
  have hconj : ∀ z : ℂ, z ≠ 0 →
      MandelDim.pushdown σ (MandelDim.tau0 z) = MandelDim.tau0 (Hr z) := by
    intro z hz0
    have htw : MandelDim.tau0 z ≠ 0 := tau0_ne_zero hz0
    have hne : MandelDim.pushdown σ (MandelDim.tau0 z) ≠ 0 := by
      rw [Work.Horn.MandelDim.pushdown_of_ne σ htw]
      exact piExp_ne_zero _
    rw [hHrval z hz0]
    exact (tau0_invol _ hne).symm
  -- ## 8. `Hr` is holomorphic on `Ω` with `deriv Hr 0 = exp (-2πi (β - cl))`
  have hπBl_open : IsOpen (MandelDim.piExp '' hd.Bl) := ad_isOpen_piExp_image hd.Bl_open
  have hHr_diffAt : ∀ w ∈ Ω, w ≠ 0 → DifferentiableAt ℂ Hr w := by
    intro w hw hw0
    have hmem : MandelDim.tau0 w ∈ MandelDim.piExp '' hd.Bl := htau0mem w hw hw0
    have hne : MandelDim.pushdown σ (MandelDim.tau0 w) ≠ 0 := by
      rw [Work.Horn.MandelDim.pushdown_of_ne σ (tau0_ne_zero hw0)]
      exact piExp_ne_zero _
    have h1 : DifferentiableAt ℂ
        (fun w => MandelDim.tau0 (MandelDim.pushdown σ (MandelDim.tau0 w))) w :=
      (differentiableAt_tau0 hne).comp w
        ((hHd.differentiableAt (hπBl_open.mem_nhds hmem)).comp w (differentiableAt_tau0 hw0))
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_compl_singleton.mem_nhds (by simpa using hw0)] with z hz
    rw [hHrval z hz]
  have hderiv : HasDerivAt Hr (Complex.exp (-(2 * Real.pi * Complex.I * (β - cl)))) 0 := by
    rw [hasDerivAt_iff_tendsto_slope]
    have hsl : slope Hr 0 = fun w : ℂ => w⁻¹ * Hr w := by
      funext w
      simp only [slope, hHr0, vsub_eq_sub, sub_zero, smul_eq_mul]
    rw [hsl]
    have hlogt : Filter.Tendsto (fun w : ℂ =>
        Complex.log (MandelDim.tau0 w) / (2 * Real.pi * Complex.I))
        (𝓝[≠] (0 : ℂ)) lowerEnd := by
      rw [MandelDim.lowerEnd, Filter.tendsto_comap_iff, Filter.tendsto_atBot]
      intro c
      rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
      refine ⟨Real.exp (2 * Real.pi * c), Real.exp_pos _, fun w hw hwne => ?_⟩
      simp only [Function.comp_apply]
      have hτ0 : ‖MandelDim.tau0 w‖ = 1 / ‖w‖ := by
        simp only [MandelDim.tau0]
        rw [norm_div, norm_neg, norm_one]
      have him : (Complex.log (MandelDim.tau0 w) / (2 * Real.pi * Complex.I)).im
          = -(Real.log ‖MandelDim.tau0 w‖) / (2 * Real.pi) := by
        rw [Complex.div_im, Complex.log_re, Complex.log_im]
        have h1 : (2 * ↑Real.pi * Complex.I : ℂ).re = 0 := by simp
        have h2 : (2 * ↑Real.pi * Complex.I : ℂ).im = 2 * Real.pi := by simp
        have h3 : Complex.normSq ((2 : ℂ) * ↑Real.pi * Complex.I) = (2 * Real.pi) ^ 2 := by
          rw [show ((2 : ℂ) * ↑Real.pi * Complex.I) = ↑(2 * Real.pi) * Complex.I by
            push_cast; ring]
          rw [Complex.normSq_apply]; simp; ring
        rw [h1, h2, h3]; field_simp; ring
      rw [him, hτ0, one_div, Real.log_inv, neg_neg]
      have hw' : ‖w‖ < Real.exp (2 * Real.pi * c) := by
        rw [dist_eq_norm, sub_zero] at hw; exact hw
      have hlog : Real.log ‖w‖ < 2 * Real.pi * c := by
        have h := Real.log_lt_log (norm_pos_iff.mpr hwne) hw'
        rwa [Real.log_exp] at h
      have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
      rw [div_le_iff₀ h2π]
      linarith
    have hdrift2 : Filter.Tendsto (fun w : ℂ =>
        σ (Complex.log (MandelDim.tau0 w) / (2 * Real.pi * Complex.I))
          - Complex.log (MandelDim.tau0 w) / (2 * Real.pi * Complex.I) - (β - cl))
        (𝓝[≠] (0 : ℂ)) (nhds 0) := hdrift.comp hlogt
    have hexp : Filter.Tendsto (fun w : ℂ => Complex.exp (-(2 * Real.pi * Complex.I *
        (σ (Complex.log (MandelDim.tau0 w) / (2 * Real.pi * Complex.I))
          - Complex.log (MandelDim.tau0 w) / (2 * Real.pi * Complex.I)))))
        (𝓝[≠] (0 : ℂ)) (nhds (Complex.exp (-(2 * Real.pi * Complex.I * (β - cl))))) := by
      have hA : Filter.Tendsto (fun w : ℂ => -(2 * Real.pi * Complex.I) *
          (σ (Complex.log (MandelDim.tau0 w) / (2 * Real.pi * Complex.I))
            - Complex.log (MandelDim.tau0 w) / (2 * Real.pi * Complex.I) - (β - cl)))
          (𝓝[≠] (0 : ℂ)) (nhds 0) := by
        simpa using hdrift2.const_mul (-(2 * Real.pi * Complex.I))
      have hB : Filter.Tendsto (fun w : ℂ => -(2 * Real.pi * Complex.I * (β - cl)) +
          (-(2 * Real.pi * Complex.I) *
            (σ (Complex.log (MandelDim.tau0 w) / (2 * Real.pi * Complex.I))
              - Complex.log (MandelDim.tau0 w) / (2 * Real.pi * Complex.I) - (β - cl))))
          (𝓝[≠] (0 : ℂ)) (nhds (-(2 * Real.pi * Complex.I * (β - cl)))) := by
        simpa using (tendsto_const_nhds.add hA)
      have hpt : ∀ w : ℂ, Complex.exp (-(2 * Real.pi * Complex.I * (β - cl)) +
          (-(2 * Real.pi * Complex.I) *
            (σ (Complex.log (MandelDim.tau0 w) / (2 * Real.pi * Complex.I))
              - Complex.log (MandelDim.tau0 w) / (2 * Real.pi * Complex.I) - (β - cl)))) =
          Complex.exp (-(2 * Real.pi * Complex.I *
            (σ (Complex.log (MandelDim.tau0 w) / (2 * Real.pi * Complex.I))
              - Complex.log (MandelDim.tau0 w) / (2 * Real.pi * Complex.I)))) := by
        intro w
        congr 1
        ring
      exact Filter.Tendsto.congr hpt
        (Complex.continuous_exp.continuousAt.tendsto.comp hB)
    have hcongr : (fun w : ℂ => w⁻¹ * Hr w) =ᶠ[𝓝[≠] (0 : ℂ)]
        (fun w : ℂ => Complex.exp (-(2 * Real.pi * Complex.I *
          (σ (Complex.log (MandelDim.tau0 w) / (2 * Real.pi * Complex.I))
            - Complex.log (MandelDim.tau0 w) / (2 * Real.pi * Complex.I))))) := by
      filter_upwards [self_mem_nhdsWithin] with w hwne
      set u' : ℂ := Complex.log (MandelDim.tau0 w) / (2 * Real.pi * Complex.I) with hu'def
      have htw0 : MandelDim.tau0 w ≠ 0 := tau0_ne_zero hwne
      have hpi : MandelDim.piExp u' = MandelDim.tau0 w := by
        rw [hu'def]; exact Work.Horn.MandelDim.piExp_log_div _ htw0
      have hHval : MandelDim.pushdown σ (MandelDim.tau0 w) = MandelDim.piExp (σ u') := by
        rw [Work.Horn.MandelDim.pushdown_of_ne σ htw0, hu'def]
      have hweq : w = -(MandelDim.piExp u')⁻¹ := by
        have h1 : MandelDim.piExp u' * (-w) = 1 := by
          have h : MandelDim.tau0 w = -1 / w := rfl
          rw [h, neg_div] at hpi
          rw [hpi, neg_mul_neg]
          exact div_mul_cancel₀ 1 hwne
        have h2 : MandelDim.piExp u' = (-w)⁻¹ := eq_inv_of_mul_eq_one_left h1
        rw [h2, inv_inv]
        ring
      have hA' : Hr w = -(MandelDim.piExp (-(σ u'))) := by
        rw [hHrval w hwne, hHval, tau0_piExp, MandelDim.piExp]
        congr 1
        congr 1
        ring
      have hB' : w = -(MandelDim.piExp (-u')) := by
        rw [hweq, ← piExp_neg' u']
      rw [hA', hB', inv_neg, neg_mul_neg, piExp_neg' u', inv_inv, ← piExp_mul', MandelDim.piExp]
      congr 1
      ring_nf
    exact hexp.congr' hcongr.symm
  have hHrd : DifferentiableOn ℂ Hr Ω := by
    intro w hw
    by_cases hw0 : w = 0
    · rw [hw0]
      exact hderiv.differentiableAt.differentiableWithinAt
    · exact (hHr_diffAt w hw hw0).differentiableWithinAt
  -- ## 9. Cartan
  have hcart := Work.L62.cartan hΩopen hΩbdd hΩpc hHrd hHrΩ h0Ω hHr0
  have hnorm : ‖deriv Hr 0‖ = Real.exp (2 * Real.pi * (β.im - cl.im)) := by
    have hre : (-(2 * Real.pi * Complex.I * (β - cl))).re = 2 * Real.pi * (β.im - cl.im) := by
      simp only [Complex.neg_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im]
      norm_num
    rw [hderiv.deriv, Complex.norm_exp, hre]
  have hle : β.im ≤ cl.im := by
    have h1 := hcart.1
    rw [hnorm] at h1
    have h2 := Real.exp_le_one_iff.mp h1
    have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
    have h3 : β.im - cl.im ≤ 0 := by
      by_contra h'
      push_neg at h'
      have h4 : 0 < 2 * Real.pi * (β.im - cl.im) := mul_pos h2π h'
      linarith
    linarith
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · -- equality case: `Hr` is a bijection, so `pushdown d.E` is injective on `π '' Bl`
    exfalso
    have h1 : ‖deriv Hr 0‖ = 1 := by rw [hnorm, heq]; simp
    obtain ⟨hsurj, -⟩ := hcart.2 h1
    have hsurjH : ∀ v : ℂ, v ∈ MandelDim.piExp '' hd.Bl →
        ∃ v' : ℂ, v' ∈ hd.Bl ∧ MandelDim.pushdown σ (MandelDim.piExp v') = v := by
      intro v hv
      obtain ⟨a, ha, haτ⟩ := hv
      have hvM : v ∈ MandelDim.piExp '' hd.Bl := ⟨a, ha, haτ⟩
      have hv0 : v ≠ 0 := by rw [← haτ]; exact piExp_ne_zero a
      have htv : MandelDim.tau0 v ∈ Ω := by
        rw [hΩdef]; exact Or.inr ⟨v, hvM, rfl⟩
      obtain ⟨x, hxΩ, hxu⟩ := hsurj htv
      have hx0 : x ≠ 0 := by
        intro h; rw [h, hHr0] at hxu; exact tau0_ne_zero hv0 hxu.symm
      have hxτ : x ∈ MandelDim.tau0 '' (MandelDim.piExp '' hd.Bl) := by
        rw [hΩdef] at hxΩ
        rcases hxΩ with h | h
        · exact absurd h hx0
        · exact h
      obtain ⟨w, hw, hwx⟩ := hxτ
      obtain ⟨b, hb, hbw⟩ := hw
      have hb0 : MandelDim.piExp b ≠ 0 := piExp_ne_zero b
      have hwb : w ≠ 0 := by rw [← hbw]; exact hb0
      have hxw : MandelDim.tau0 x = w := by rw [← hwx, tau0_invol w hwb]
      have hkey := hconj x hx0
      rw [hxu] at hkey
      rw [tau0_invol v hv0] at hkey
      rw [hxw, ← hbw] at hkey
      exact ⟨b, hb, hkey⟩
    have hinj : ∀ a ∈ MandelDim.piExp '' hd.Bl, ∀ b ∈ MandelDim.piExp '' hd.Bl,
        MandelDim.pushdown d.E a = MandelDim.pushdown d.E b → a = b := by
      intro a ha b hb hab
      obtain ⟨va, hva, hHa⟩ := hsurjH a ha
      obtain ⟨vb, hvb, hHb⟩ := hsurjH b hb
      have hcylA : MandelDim.pushdown d.E a = MandelDim.piExp va * MandelDim.piExp β := by
        rw [← hHa]; exact hcyl va hva
      have hcylB : MandelDim.pushdown d.E b = MandelDim.piExp vb * MandelDim.piExp β := by
        rw [← hHb]; exact hcyl vb hvb
      have hEq : MandelDim.piExp va = MandelDim.piExp vb := by
        rw [hcylA, hcylB] at hab
        exact mul_right_cancel₀ (piExp_ne_zero β) hab
      rw [← hHa, ← hHb, hEq]
    obtain ⟨ζ₁, hζ₁, ζ₂, hζ₂, hne⟩ := (hd.inf_l 0).nontrivial
    obtain ⟨w₁, hw₁, hw₁ζ⟩ := hζ₁
    obtain ⟨w₂, hw₂, hw₂ζ⟩ := hζ₂
    have hg₁ : MandelDim.pushdown d.E ζ₁ = 1 := by
      rw [← hw₁ζ]
      rw [Work.Horn.MandelDim.pushdown_piExp hd.Bl_T (fun u hu _ => E_add_one_Bl d hd hu) hw₁.1,
        hw₁.2, MandelDim.piExp]
      simp
    have hg₂ : MandelDim.pushdown d.E ζ₂ = 1 := by
      rw [← hw₂ζ]
      rw [Work.Horn.MandelDim.pushdown_piExp hd.Bl_T (fun u hu _ => E_add_one_Bl d hd hu) hw₂.1,
        hw₂.2, MandelDim.piExp]
      simp
    exact hne (hinj ζ₁ ⟨w₁, hw₁.1, hw₁ζ⟩ ζ₂ ⟨w₂, hw₂.1, hw₂ζ⟩ (by rw [hg₁, hg₂]))

end

end Work.L62
