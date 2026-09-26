import Mathlib
import Submission.Work.Smooth.SphereJordan.riemannMapping

/-!
# The inverse of an injective holomorphic function is holomorphic

Route to `caratheodory_jordan` (see the Wikipedia proof of Carathéodory's theorem): the Riemann
mapping theorem supplies a biholomorphism `g : U → 𝔻`; for the boundary-correspondence proof (the
length–area estimate) one needs the *inverse* `f = g⁻¹ : 𝔻 → U` to be holomorphic.

This file proves that, in the general form needed:

* `Work.Smooth.SphereJordan.Caratheodory.exists_analytic_inverse` — if `g` is holomorphic and
  injective on an open preconnected `U` (with at least two points) and `Set.BijOn g U V`, then the
  inverse of `g` is holomorphic on `V`.  The proof is the standard one:
  * `f` is continuous because a non-constant holomorphic `g` is an open map
    (`AnalyticOnNhd.is_constant_or_isOpen`);
  * where `deriv g ≠ 0`, `f` is analytic at `g z` by the inverse function theorem in the
    `AnalyticAt.analyticAt_comp_iff_of_deriv_ne_zero` form;
  * the zeros of `deriv g` are isolated (else `deriv g ≡ 0` on the open preconnected `U` by the
    identity theorem, making `g` constant, contradicting injectivity), so at the remaining points
    `f` is differentiable off a punctured neighbourhood and continuous, and Riemann's removable
    singularity theorem (`Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`)
    applies.

* `Work.Smooth.SphereJordan.Caratheodory.exists_analytic_bijOn_ball_domain` — the packaged form for
  a bounded simply connected domain `U`: there are `f, g` inverse bijections between `𝔻` and `U`,
  both holomorphic.
-/

noncomputable section

open Set Metric Filter

open scoped Topology

namespace Work.Smooth.SphereJordan.Caratheodory

/-- **The inverse of an injective holomorphic function is holomorphic.**

If `g : ℂ → ℂ` is holomorphic on the open preconnected set `U`, injective on `U`, with `g '' U = V`,
then there is `f` with `Set.BijOn f V U`, holomorphic on `V`, and `f ∘ g = id` on `U`,
`g ∘ f = id` on `V`.

(`hUnt` — that `U` has at least two points — rules out the constant case; it holds automatically for
a nonempty open `U`.) -/
theorem exists_analytic_inverse {U V : Set ℂ} (hUo : IsOpen U) (hUp : IsPreconnected U)
    (hUnt : ∃ x ∈ U, ∃ y ∈ U, x ≠ y) {g : ℂ → ℂ} (hg : Set.BijOn g U V)
    (hga : AnalyticOnNhd ℂ g U) :
    ∃ f : ℂ → ℂ, Set.BijOn f V U ∧ AnalyticOnNhd ℂ f V ∧
      (∀ z ∈ U, f (g z) = z) ∧ (∀ w ∈ V, g (f w) = w) := by
  classical
  -- non-constancy of `g`
  have hnonconst : ¬ ∃ w, ∀ z ∈ U, g z = w := by
    rintro ⟨w, hw⟩
    obtain ⟨x, hx, y, hy, hxy⟩ := hUnt
    exact hxy (hg.injOn hx hy (by rw [hw x hx, hw y hy]))
  have hgopen : ∀ s ⊆ U, IsOpen s → IsOpen (g '' s) :=
    (AnalyticOnNhd.is_constant_or_isOpen hga hUp).resolve_left hnonconst
  -- the inverse
  let f : ℂ → ℂ := fun w => if hw : w ∈ V then (hg.surjOn hw).choose else 0
  have hf_mem : ∀ w ∈ V, f w ∈ U := by
    intro w hw
    simp only [f, dif_pos hw]
    exact ((hg.surjOn hw).choose_spec).1
  have hg_f : ∀ w ∈ V, g (f w) = w := by
    intro w hw
    simp only [f, dif_pos hw]
    exact ((hg.surjOn hw).choose_spec).2
  have hf_g : ∀ z ∈ U, f (g z) = z := by
    intro z hz
    have hgz : g z ∈ V := hg.mapsTo hz
    simp only [f, dif_pos hgz]
    have hspec := (hg.surjOn hgz).choose_spec
    exact hg.injOn hspec.1 hz hspec.2
  -- continuity of `f` on `V`
  have hf_contAt : ∀ w ∈ V, ContinuousAt f w := by
    intro w₀ hw₀
    have hz₀ : f w₀ ∈ U := hf_mem w₀ hw₀
    obtain ⟨ρ, hρ, hρU⟩ := Metric.isOpen_iff.mp hUo (f w₀) hz₀
    rw [Metric.continuousAt_iff]
    intro ε hε
    have hρε : 0 < min ρ ε := lt_min hρ hε
    have hWopen : IsOpen (g '' Metric.ball (f w₀) (min ρ ε)) :=
      hgopen _ (fun z hz => hρU (Metric.ball_subset_ball (min_le_left _ _) hz))
        Metric.isOpen_ball
    have hWmem : g (f w₀) ∈ g '' Metric.ball (f w₀) (min ρ ε) :=
      ⟨f w₀, Metric.mem_ball_self hρε, rfl⟩
    obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp hWopen _ hWmem
    refine ⟨δ, hδ, fun w hw => ?_⟩
    have hw' : w ∈ Metric.ball (g (f w₀)) δ := by
      rw [Metric.mem_ball, hg_f w₀ hw₀]
      exact hw
    obtain ⟨z, hz, hzw⟩ := hδsub hw'
    have hzU : z ∈ U := hρU (Metric.ball_subset_ball (min_le_left _ _) hz)
    have hfw : f w = z := by rw [← hzw, hf_g z hzU]
    have hzd : dist z (f w₀) < min ρ ε := hz
    rw [hfw]
    exact lt_of_lt_of_le hzd (min_le_right _ _)
  have hf_cont : ContinuousOn f V := fun w hw => (hf_contAt w hw).continuousWithinAt
  -- isolated zeros of `deriv g`
  have hZiso : ∀ z ∈ U, deriv g z = 0 → ∀ᶠ w in 𝓝[≠] z, deriv g w ≠ 0 := by
    intro z hz hz0
    rcases (hga z hz).deriv.eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      have hzero : U.EqOn (deriv g) 0 :=
        AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero hga.deriv hUp hz h
      obtain ⟨x, hx, y, hy, hxy⟩ := hUnt
      exact hxy (hg.injOn hx hy
        (hUo.is_const_of_deriv_eq_zero hUp hga.differentiableOn hzero hx hy))
    · exact h
  -- where `deriv g ≠ 0`, the inverse is analytic
  have hcaseA : ∀ z ∈ U, deriv g z ≠ 0 → AnalyticAt ℂ f (g z) := by
    intro z hz hzne
    have hcomp : AnalyticAt ℂ (fun y => f (g y)) z := by
      refine (analyticAt_congr ?_).mpr analyticAt_id
      filter_upwards [hUo.mem_nhds hz] with y hy
      exact hf_g y hy
    exact (analyticAt_comp_iff_of_deriv_ne_zero (f := g) (g := f) (x := z)
      (hga z hz) hzne).mp hcomp
  -- at a zero of `deriv g`, removable singularity
  have hcaseB : ∀ z ∈ U, deriv g z = 0 → AnalyticAt ℂ f (g z) := by
    intro z hz hz0
    obtain ⟨ρ, hρ, hρU⟩ := Metric.isOpen_iff.mp hUo z hz
    obtain ⟨ρ', hρ', hρ'sub⟩ :=
      (nhdsWithin_hasBasis nhds_basis_ball ({z}ᶜ)).mem_iff.mp (hZiso z hz hz0)
    have hρm : 0 < min ρ ρ' := lt_min hρ hρ'
    have hWopen : IsOpen (g '' Metric.ball z (min ρ ρ')) :=
      hgopen _ (fun y hy => hρU (Metric.ball_subset_ball (min_le_left _ _) hy))
        Metric.isOpen_ball
    have hWmem : g z ∈ g '' Metric.ball z (min ρ ρ') :=
      ⟨z, Metric.mem_ball_self hρm, rfl⟩
    refine Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_
      (hf_contAt (g z) (hg.mapsTo hz))
    filter_upwards [nhdsWithin_le_nhds (hWopen.mem_nhds hWmem), self_mem_nhdsWithin]
      with w hw hwne
    obtain ⟨y, hy, hyw⟩ := hw
    have hyU : y ∈ U := hρU (Metric.ball_subset_ball (min_le_left _ _) hy)
    have hyne : y ≠ z := fun h => hwne (by simp [← hyw, h])
    have hyρ : y ∈ Metric.ball z ρ' :=
      Metric.ball_subset_ball (min_le_right _ _) hy
    have hderiv : deriv g y ≠ 0 :=
      hρ'sub ⟨hyρ, by simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hyne⟩
    have hthis : AnalyticAt ℂ f w := by rw [← hyw]; exact hcaseA y hyU hderiv
    exact hthis.differentiableAt
  -- assemble
  have hf_an : AnalyticOnNhd ℂ f V := by
    intro w hw
    rw [← hg_f w hw]
    by_cases h0 : deriv g (f w) = 0
    · exact hcaseB (f w) (hf_mem w hw) h0
    · exact hcaseA (f w) (hf_mem w hw) h0
  refine ⟨f, ⟨?_, ?_, ?_⟩, hf_an, hf_g, hg_f⟩
  · intro w hw
    exact hf_mem w hw
  · intro w hw w' hw' heq
    rw [← hg_f w hw, ← hg_f w' hw', heq]
  · intro z hz
    exact ⟨g z, hg.mapsTo hz, hf_g z hz⟩

/-- **The Riemann mapping theorem in both directions**: for an open, nonempty, bounded, simply
connected `U ⊆ ℂ` there are holomorphic inverse bijections between the unit disc and `U`. -/
theorem exists_analytic_bijOn_ball_domain {U : Set ℂ} (hUo : IsOpen U) (hUne : U.Nonempty)
    (hUb : Bornology.IsBounded U) (hUc : SimplyConnectedSpace U) :
    ∃ f g : ℂ → ℂ, Set.BijOn f (Metric.ball 0 1) U ∧ Set.BijOn g U (Metric.ball 0 1) ∧
      AnalyticOnNhd ℂ f (Metric.ball 0 1) ∧ AnalyticOnNhd ℂ g U ∧
      (∀ z ∈ U, f (g z) = z) ∧ (∀ w ∈ Metric.ball 0 1, g (f w) = w) := by
  have hUp : IsPreconnected U := isPreconnected_of_isSimplyConnected hUc
  have hU : U ≠ Set.univ := by
    intro h
    obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp hUb
    obtain ⟨x, hx⟩ := hUne
    have hy : x + (((|C| + 1 : ℝ)) : ℂ) ∈ U := by rw [h]; trivial
    have hd := hC hx hy
    have h1 : dist x (x + (((|C| + 1 : ℝ)) : ℂ)) = |C| + 1 := by
      have h2 : x - (x + (((|C| + 1 : ℝ)) : ℂ)) = -(((|C| + 1 : ℝ)) : ℂ) := by ring
      rw [dist_eq_norm, h2, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith [abs_nonneg C])]
    have : |C| + 1 ≤ C := h1 ▸ hd
    linarith [le_abs_self C]
  obtain ⟨g, hg, hgd⟩ := Work.Smooth.SphereJordan.riemannMapping hUo hUne hUc hU
  have hga : AnalyticOnNhd ℂ g U := hgd.analyticOnNhd hUo
  -- `U` has at least two points (it is nonempty and open)
  have hUnt : ∃ x ∈ U, ∃ y ∈ U, x ≠ y := by
    obtain ⟨x, hx⟩ := hUne
    obtain ⟨ρ, hρ, hρU⟩ := Metric.isOpen_iff.mp hUo x hx
    refine ⟨x, hx, x + (((ρ / 2) : ℝ) : ℂ), hρU ?_, ?_⟩
    · have h2 : x + (((ρ / 2 : ℝ)) : ℂ) - x = (((ρ / 2 : ℝ)) : ℂ) := by ring
      rw [Metric.mem_ball, dist_eq_norm, h2, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
      linarith
    · intro hcon
      have h4 : x + (((ρ / 2 : ℝ)) : ℂ) - x = 0 := by rw [← hcon, sub_self]
      have h3 : (((ρ / 2 : ℝ)) : ℂ) = 0 := by
        rw [add_sub_cancel_left] at h4
        exact h4
      have h5 : (ρ / 2 : ℝ) = 0 := by exact_mod_cast h3
      linarith
  obtain ⟨f, hfbij, hfa, hfg, hgf⟩ := exists_analytic_inverse hUo hUp hUnt hg hga
  exact ⟨f, g, hfbij, hg, hfa, hga, hfg, hgf⟩

end Work.Smooth.SphereJordan.Caratheodory
