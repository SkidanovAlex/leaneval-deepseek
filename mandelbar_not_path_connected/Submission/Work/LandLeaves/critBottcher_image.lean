/-
# The image of the critical Böttcher coordinate is an exterior disc

Let `critDomain c = {z | G_c 0 < G_c z}` be the critical domain of the tricorn
`T_c(z) = conj z ^ 2 + c` and let `varphiCrit c` be a critical Böttcher coordinate of `T_c`,
i.e. an analytic function on `critDomain c` whose modulus is the exponential of the Green
function, `‖varphiCrit c z‖ = exp (G_c z)`.  Then

  `varphiCrit c '' critDomain c = {w : ℂ | exp (G_c 0) < ‖w‖}`.

The proof is the level-`G_c 0` version of `Work.Bottcher.Inverse.image_eq_exteriorDisc_analyticBottcher`
(the escaping set `{0 < G_c z}` and the value `1` there are replaced by the critical domain
`{G_c 0 < G_c z}` and the critical value `exp (G_c 0)`); the content is purely
"modulus + analyticity + topology of the critical domain":

* `critDomain c` is nonempty, open and preconnected (`ParamRaysCrit`);
* the image is contained in the exterior disc `{exp (G_c 0) < ‖w‖}` because
  `‖varphiCrit c z‖ = exp (G_c z) > exp (G_c 0)` on the critical domain;
* it is **open** (open mapping theorem; non-constancy of `varphiCrit c` follows from
  `G_c (T_c z) = 2 G_c z > G_c z` on `critDomain c`);
* it is **relatively closed** in the exterior disc: a convergent sequence of image points
  `w_n → w` with `exp (G_c 0) < ‖w‖` has `G_c (z_n) = log ‖w_n‖` bounded, the sublevel sets of
  `G_c` are bounded (`Work.Bottcher.Inverse.isBounded_green_sublevel`), so a subsequence of
  `z_n` converges to a point `a` with `G_c a = log ‖w‖ > G_c 0`, i.e. `a ∈ critDomain c`,
  and continuity of `varphiCrit c` at `a` gives `varphiCrit c a = w`;
* the exterior disc is preconnected (image of the half-plane `{Re z > G_c 0}` under `exp`).

An open, relatively closed, nonempty subset of a preconnected set is the whole set.
-/
import Mathlib
import Submission.Work.Bottcher.CritBottcherExists
import Submission.Work.Bottcher.Inverse.image_eq_exteriorDisc_analyticBottcher
import Submission.Work.ParamRaysCrit.All

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

open Filter
open scoped Real Topology ComplexConjugate
open LeanEval.ComplexAnalysis (Tantibar)

/-- The sublevel sets of the parameter Green function are bounded.  (Transported from the
`Work.Bottcher` Green function via `green_eq_greenFun`.) -/
theorem isBounded_greenFun_sublevel (c : ℂ) (M : ℝ) :
    Bornology.IsBounded {z : ℂ | Work.ParamRays.greenFun c z ≤ M} := by
  have h := Work.Bottcher.Inverse.isBounded_green_sublevel c M
  have hset : {z : ℂ | Work.ParamRays.greenFun c z ≤ M}
      = {z : ℂ | Work.Bottcher.green c z ≤ M} := by
    ext z
    simp only [Set.mem_ofPred_eq]
    rw [Work.Bottcher.Contraction.green_eq_greenFun]
  rw [hset]
  exact h

/-- The parameter Green function is continuous in the point. -/
theorem continuous_greenFun (c : ℂ) :
    Continuous (fun z : ℂ => Work.ParamRays.greenFun c z) := by
  have h : Continuous (fun z : ℂ => Work.Bottcher.green c z) :=
    Work.Escape.continuous_green_Tantibar c
  rw [show (fun z : ℂ => Work.ParamRays.greenFun c z)
      = fun z : ℂ => Work.Bottcher.green c z from
    funext fun z => (Work.Bottcher.CritBasic.green_eq c z).symm]
  exact h

/-- **The image of a critical Böttcher coordinate is the exterior disc of its critical value.**
If `φ` is analytic on `critDomain c` and `‖φ z‖ = exp (G_c z)` there, then `φ` maps the
critical domain onto `{w | exp (G_c 0) < ‖w‖}`. -/
theorem image_eq_exteriorDisc_of_critDomain (c : ℂ) (φ : ℂ → ℂ)
    (han : AnalyticOnNhd ℂ φ (Work.ParamRays.critDomain c))
    (hmod : ∀ z : ℂ, z ∈ Work.ParamRays.critDomain c →
      ‖φ z‖ = Real.exp (Work.ParamRays.greenFun c z)) :
    φ '' Work.ParamRays.critDomain c
      = {w : ℂ | Real.exp (Work.ParamRays.greenFun c 0) < ‖w‖} := by
  set E : Set ℂ := Work.ParamRays.critDomain c with hE
  have hEopen : IsOpen E := Work.ParamRays.isOpen_critDomain c
  have hEpre : IsPreconnected E := Work.ParamRays.isPreconnected_critDomain c
  have hEne : E.Nonempty := by
    obtain ⟨z, -, hz⟩ := Work.ParamRays.exists_mem_critDomain_gt_norm c 0
    exact ⟨z, hz⟩
  have hcont : Continuous (fun z : ℂ => Work.ParamRays.greenFun c z) :=
    continuous_greenFun c
  have hTgreen : ∀ z : ℂ, Work.ParamRays.greenFun c (Tantibar c z)
      = 2 * Work.ParamRays.greenFun c z := by
    intro z
    have h := Work.ParamRays.greenFun_orbit c z 1
    rw [Work.ParamRays.orbit_one] at h
    simpa using h
  -- `φ` is not constant on the critical domain, by `G_c (T_c z) = 2 G_c z ≠ G_c z`.
  have hnotconst : ¬ ∃ k, ∀ z ∈ E, φ z = k := by
    rintro ⟨k, hk⟩
    obtain ⟨z, hz⟩ := hEne
    have hzp : Work.ParamRays.paramPotential c < Work.ParamRays.greenFun c z :=
      Work.ParamRays.mem_critDomain.mp hz
    have hzpos : 0 < Work.ParamRays.greenFun c z :=
      lt_of_le_of_lt (Work.ParamRays.paramPotential_nonneg c) hzp
    have hT : Tantibar c z ∈ E := Work.ParamRays.Tantibar_mem_critDomain hz
    have hexp : Real.exp (Work.ParamRays.greenFun c z)
        = Real.exp (Work.ParamRays.greenFun c (Tantibar c z)) := by
      rw [← hmod z hz, ← hmod (Tantibar c z) hT, hk z hz, hk (Tantibar c z) hT]
    rw [hTgreen z] at hexp
    have heq : Work.ParamRays.greenFun c z = 2 * Work.ParamRays.greenFun c z :=
      Real.exp_injective hexp
    linarith
  -- Openness of the image (open mapping theorem on the preconnected domain).
  have hopen : IsOpen (φ '' E) := by
    rcases han.is_constant_or_isOpen hEpre with hc | hop
    · exact absurd hc hnotconst
    · exact hop E (subset_refl E) hEopen
  have hUsub : φ '' E ⊆ {w : ℂ | Real.exp (Work.ParamRays.greenFun c 0) < ‖w‖} := by
    rintro y ⟨z, hz, rfl⟩
    change Real.exp (Work.ParamRays.greenFun c 0) < ‖φ z‖
    rw [hmod z hz]
    exact Real.exp_lt_exp.mpr (Work.ParamRays.mem_critDomain.mp hz)
  -- Relative closedness of the image in the exterior disc.
  have hcl : ∀ w : ℂ, Real.exp (Work.ParamRays.greenFun c 0) < ‖w‖ →
      w ∈ closure (φ '' E) → w ∈ φ '' E := by
    intro w hw hwcl
    rw [mem_closure_iff_seq_limit] at hwcl
    obtain ⟨u, hu_mem, hu_tend⟩ := hwcl
    simp only [Set.mem_image] at hu_mem
    choose z hzE hzφ using hu_mem
    have hM : 0 < ‖w‖ := lt_of_lt_of_le (Real.exp_pos _) hw.le
    have hge : (fun n => Work.ParamRays.greenFun c (z n)) = fun n => Real.log ‖u n‖ := by
      funext n
      rw [← hzφ n, hmod (z n) (hzE n), Real.log_exp]
    have hglim : Tendsto (fun n => Work.ParamRays.greenFun c (z n)) atTop
        (nhds (Real.log ‖w‖)) := by
      rw [hge]
      exact (hu_tend.norm).log hM.ne'
    have hbdd : ∀ᶠ n in atTop, Work.ParamRays.greenFun c (z n) ≤ Real.log ‖w‖ + 1 := by
      have hlt : ∀ᶠ n in atTop, Work.ParamRays.greenFun c (z n) < Real.log ‖w‖ + 1 :=
        hglim.eventually (isOpen_Iio.mem_nhds (lt_add_one _))
      exact hlt.mono fun _ hn => le_of_lt hn
    obtain ⟨a, ha_cl, ψ, hψ_mono, hψ_tend⟩ :=
      tendsto_subseq_of_frequently_bounded
        (isBounded_greenFun_sublevel c (Real.log ‖w‖ + 1)) hbdd.frequently
    have hSclosed : IsClosed {z : ℂ | Work.ParamRays.greenFun c z ≤ Real.log ‖w‖ + 1} :=
      isClosed_le hcont continuous_const
    rw [hSclosed.closure_eq] at ha_cl
    have hga : Work.ParamRays.greenFun c a = Real.log ‖w‖ := by
      have h1 : Tendsto (fun n => Work.ParamRays.greenFun c (z (ψ n))) atTop
          (nhds (Work.ParamRays.greenFun c a)) :=
        (hcont.tendsto a).comp hψ_tend
      have h2 : Tendsto (fun n => Work.ParamRays.greenFun c (z (ψ n))) atTop
          (nhds (Real.log ‖w‖)) :=
        hglim.comp hψ_mono.tendsto_atTop
      exact tendsto_nhds_unique h1 h2
    have haE : a ∈ E := by
      have hmem : a ∈ Work.ParamRays.critDomain c := by
        rw [Work.ParamRays.mem_critDomain, hga]
        exact (Real.lt_log_iff_exp_lt hM).mpr hw
      exact hmem
    refine ⟨a, haE, ?_⟩
    have h3 : Tendsto (fun n => φ (z (ψ n))) atTop (nhds (φ a)) :=
      Tendsto.comp ((han a haE).continuousAt) hψ_tend
    have h4 : Tendsto (fun n => φ (z (ψ n))) atTop (nhds w) := by
      have heq : (fun n => φ (z (ψ n))) = fun n => u (ψ n) := by
        funext n; exact hzφ (ψ n)
      rw [heq]
      exact hu_tend.comp hψ_mono.tendsto_atTop
    exact tendsto_nhds_unique h3 h4
  -- The exterior disc is preconnected: the image of `{Re z > G_c 0}` under `exp`.
  have hpreconnΩ : IsPreconnected {w : ℂ | Real.exp (Work.ParamRays.greenFun c 0) < ‖w‖} := by
    have hpre : IsPreconnected {z : ℂ | Work.ParamRays.greenFun c 0 < z.re} :=
      (convex_halfSpace_re_gt _).isPreconnected
    have himg : IsPreconnected (Complex.exp '' {z : ℂ | Work.ParamRays.greenFun c 0 < z.re}) :=
      hpre.image Complex.exp Complex.continuous_exp.continuousOn
    have hset : Complex.exp '' {z : ℂ | Work.ParamRays.greenFun c 0 < z.re}
        = {w : ℂ | Real.exp (Work.ParamRays.greenFun c 0) < ‖w‖} := by
      ext w
      constructor
      · rintro ⟨z, hz, rfl⟩
        change Real.exp (Work.ParamRays.greenFun c 0) < ‖Complex.exp z‖
        rw [Complex.norm_exp]
        exact Real.exp_lt_exp.mpr hz
      · intro hw
        have hpos : 0 < ‖w‖ := lt_of_lt_of_le (Real.exp_pos _) hw.le
        refine ⟨Complex.log w, ?_, Complex.exp_log (norm_ne_zero_iff.mp hpos.ne')⟩
        change Work.ParamRays.greenFun c 0 < (Complex.log w).re
        rw [Complex.log_re]
        exact (Real.lt_log_iff_exp_lt hpos).mpr hw
    rwa [hset] at himg
  apply Set.Subset.antisymm hUsub
  intro w hw
  have hVopen : IsOpen ((closure (φ '' E))ᶜ) := isClosed_closure.isOpen_compl
  have hdisj : Disjoint (φ '' E) ((closure (φ '' E))ᶜ) :=
    Disjoint.mono_right (Set.compl_subset_compl_of_subset subset_closure) disjoint_compl_right
  have hunion : {w : ℂ | Real.exp (Work.ParamRays.greenFun c 0) < ‖w‖} ⊆
      (φ '' E) ∪ ((closure (φ '' E))ᶜ) := by
    intro y hy
    by_cases hy' : y ∈ closure (φ '' E)
    · exact Or.inl (hcl y hy hy')
    · exact Or.inr hy'
  rcases hpreconnΩ.subset_or_subset hopen hVopen hdisj hunion with hsub | hsub
  · exact hsub hw
  · exfalso
    obtain ⟨z0, hz0⟩ := hEne
    have hz0img : φ z0 ∈ φ '' E := ⟨z0, hz0, rfl⟩
    have hout := hsub (hUsub hz0img)
    rw [Set.mem_compl_iff] at hout
    exact hout (subset_closure hz0img)

theorem critBottcher_image (c : ℂ) :
    Work.Bottcher.varphiCrit c '' Work.ParamRays.critDomain c
      = {w : ℂ | Real.exp (Work.ParamRays.greenFun c 0) < ‖w‖} := by
  refine image_eq_exteriorDisc_of_critDomain c (Work.Bottcher.varphiCrit c)
    (Work.Bottcher.analyticOnNhd_varphiCrit c) ?_
  intro z hz
  rw [Work.Bottcher.norm_varphiCrit hz, Work.Bottcher.CritBasic.green_eq]

end Work.LandLeaves
