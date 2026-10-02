/-
# Injectivity of the critical Böttcher coordinate on the critical domain

The canonical critical Böttcher coordinate `Work.Bottcher.varphiCrit c` of the tricorn
`T_c(z) = z̄² + c` is **injective** on the critical domain
`Work.ParamRays.critDomain c = {z | G_c 0 < G_c z}`.

The classical proof is the one of `Work.Bottcher.Inverse.injOn_analyticBottcher`, but run on the
critical domain instead of the escaping set: a critical Böttcher coordinate `φ` satisfies

* `φ (p_c z) = φ z ^ 4` on `critDomain c` for the holomorphic quartic `p_c = T_c ∘ T_c`,
* `‖φ z‖ = exp (G_c z)` and `φ z ≠ 0` there,
* `φ` is **odd** there: `φ (-z) = -φ z`,
* and coincides with the explicit product formula `Work.Bottcher.bottcher c` far out.

The last two are the only non-formal inputs:

* oddness is the ratio argument: `ρ z = φ (-z) / φ z` is continuous on the preconnected domain
  `critDomain c` (since `T_c` is even, `ρ` takes values in `{±1}` there) and equals `-1` at one
  far point, where `φ` is the odd product formula;
* `φ = bottcher c` beyond `farThresh c = max (Work.NAKANE.farRadius ‖c‖) (farR c)` is
  `Work.Bottcher.Core.eq_bottcher_of_analytic_tail`, whose hypotheses hold on the whole tail
  because `{farRadius ‖c‖ < ‖z‖} ⊆ critDomain c`
  (`Work.NAKANE.BottcherFar.mem_critDomain_of_farRadius_lt`).

Given two points with the same `φ`-value, their `p_c`-orbits have equal `φ`-values; beyond the
threshold the product formula is injective (`Work.Bottcher.Inverse.bottcher_injOn_far`), so the
two orbits meet; descending one `p_c`-step at a time (`pMap_eq_imp_eq_critDomain` below, a
critical-domain version of `Work.Bottcher.Inverse.pMap_eq_imp_eq`, where the two extra preimages
of a point are excluded by oddness and non-vanishing) gives the result.
-/
import Mathlib
import Submission.Work.Bottcher.CritBottcherExists
import Submission.Work.Bottcher.Inverse.injOn_analyticBottcher
import Submission.Work.Bottcher.Inverse.pMap_eq_imp_eq
import Submission.Work.ParamRaysCrit.All
import Submission.Work.Bottcher.Core.eq_bottcher_of_analytic_tail
import Submission.Work.NAKANE.BottcherFar.mem_critDomain_of_farRadius_lt
import Submission.Work.NAKANE.BottcherFar.jointVarphi_eq_jointBottcher_of_far
import Submission.Work.Bottcher.Inverse.injOn_far

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter
open scoped Topology ComplexConjugate

namespace Work.LandLeaves.CritInj

open LeanEval.ComplexAnalysis (Tantibar)

noncomputable section

/-! ## The far threshold

Beyond `farThresh c` the canonical coordinate is the explicit product formula. -/

/-- The radius beyond which every point of the plane lies in the critical domain
(`Work.NAKANE.farRadius ‖c‖`) *and* the product formula is injective
(`Work.Bottcher.Inverse.farR`). -/
noncomputable def farThresh (c : ℂ) : ℝ :=
  max (Work.NAKANE.farRadius ‖c‖) (Work.Bottcher.Inverse.farR c)

theorem farThresh_pos (c : ℂ) : 0 < farThresh c :=
  lt_of_lt_of_le (Work.Bottcher.Inverse.farR_pos c) (le_max_right _ _)

theorem farRadius_le_farThresh (c : ℂ) : Work.NAKANE.farRadius ‖c‖ ≤ farThresh c :=
  le_max_left _ _

theorem farR_le_farThresh (c : ℂ) : Work.Bottcher.Inverse.farR c ≤ farThresh c :=
  le_max_right _ _

/-- **Far out the canonical coordinate is the product formula.**  For `‖z‖ > farThresh c` one has
`varphiCrit c z = bottcher c z`. -/
theorem far_eq_bottcher (c : ℂ) {z : ℂ} (hz : farThresh c < ‖z‖) :
    Work.Bottcher.varphiCrit c z = Work.Bottcher.bottcher c z := by
  have hR : Work.NAKANE.farRadius ‖c‖ < ‖z‖ :=
    lt_of_le_of_lt (farRadius_le_farThresh c) hz
  refine Work.Bottcher.Core.eq_bottcher_of_analytic_tail c (Work.NAKANE.farRadius ‖c‖)
    (Work.NAKANE.BottcherFar.escapeRadius_le_farRadius c) (Work.Bottcher.varphiCrit c)
    ?_ ?_ ?_ ?_ z hR
  · exact (Work.Bottcher.analyticOnNhd_varphiCrit c).mono
      (fun w hw => Work.NAKANE.BottcherFar.mem_critDomain_of_farRadius_lt hw)
  · intro w hw
    have hwc : w ∈ Work.ParamRays.critDomain c :=
      Work.NAKANE.BottcherFar.mem_critDomain_of_farRadius_lt hw
    have h1 : Tantibar c w ∈ Work.ParamRays.critDomain c :=
      Work.ParamRays.Tantibar_mem_critDomain hwc
    rw [Work.Bottcher.pMap_eq_iterate_two, show (2 : ℕ) = 1 + 1 from rfl,
      Function.iterate_add_apply, Function.iterate_one,
      Work.Bottcher.varphiCrit_comm_Tantibar h1, Work.Bottcher.varphiCrit_comm_Tantibar hwc]
    simp only [map_pow, Complex.conj_conj]
    ring
  · intro w hw
    exact Work.Bottcher.norm_varphiCrit (Work.NAKANE.BottcherFar.mem_critDomain_of_farRadius_lt hw)
  · exact Work.Bottcher.varphiCrit_div_tendsto_one c

/-- Far out the canonical coordinate is injective. -/
theorem injOn_farThresh (c : ℂ) {a b : ℂ} (ha : farThresh c < ‖a‖) (hb : farThresh c < ‖b‖)
    (h : Work.Bottcher.varphiCrit c a = Work.Bottcher.varphiCrit c b) : a = b := by
  rw [far_eq_bottcher c ha, far_eq_bottcher c hb] at h
  exact Work.Bottcher.Inverse.bottcher_injOn_far c
    (le_of_lt (lt_of_le_of_lt (farR_le_farThresh c) ha))
    (le_of_lt (lt_of_le_of_lt (farR_le_farThresh c) hb)) h

/-! ## Elementary invariance of the critical domain -/

/-- The Green function is even, in the `ParamRays` vocabulary. -/
theorem greenFun_neg (c z : ℂ) : Work.ParamRays.greenFun c (-z) = Work.ParamRays.greenFun c z := by
  rw [← Work.Bottcher.CritBasic.green_eq, ← Work.Bottcher.CritBasic.green_eq,
    Work.Bottcher.Inverse.green_neg]

/-- The critical domain is invariant under `z ↦ -z` (the Green function is even). -/
theorem neg_mem_critDomain (c : ℂ) {z : ℂ} (hz : z ∈ Work.ParamRays.critDomain c) :
    -z ∈ Work.ParamRays.critDomain c := by
  rw [Work.ParamRays.mem_critDomain] at hz ⊢
  rwa [greenFun_neg c z]

/-- The critical domain is invariant under the quartic `p_c`. -/
theorem pMap_mem_critDomain (c : ℂ) {z : ℂ} (hz : z ∈ Work.ParamRays.critDomain c) :
    Work.Bottcher.pMap c z ∈ Work.ParamRays.critDomain c := by
  rw [← Work.Bottcher.CritBasic.critDomain_eq] at hz ⊢
  exact Work.Bottcher.CritBasic.pMap_mem_CritDomain hz

/-- The critical domain is invariant along the `p_c`-orbit. -/
theorem pMap_iterate_mem_critDomain (c : ℂ) {z : ℂ} (hz : z ∈ Work.ParamRays.critDomain c)
    (k : ℕ) : (Work.Bottcher.pMap c)^[k] z ∈ Work.ParamRays.critDomain c := by
  induction k with
  | zero => simpa using hz
  | succ k ih => rw [Function.iterate_succ_apply']; exact pMap_mem_critDomain c ih

/-- The `p_c`-Böttcher equation of the canonical coordinate on the critical domain. -/
theorem varphiCrit_comm_pMap {c z : ℂ} (hz : z ∈ Work.ParamRays.critDomain c) :
    Work.Bottcher.varphiCrit c (Work.Bottcher.pMap c z) = (Work.Bottcher.varphiCrit c z) ^ 4 := by
  have h1 : Tantibar c z ∈ Work.ParamRays.critDomain c :=
    Work.ParamRays.Tantibar_mem_critDomain hz
  rw [Work.Bottcher.pMap_eq_iterate_two, show (2 : ℕ) = 1 + 1 from rfl,
    Function.iterate_add_apply, Function.iterate_one,
    Work.Bottcher.varphiCrit_comm_Tantibar h1, Work.Bottcher.varphiCrit_comm_Tantibar hz]
  simp only [map_pow, Complex.conj_conj]
  ring

/-! ## Oddness on the critical domain -/

/-- `T_c (-z) = T_c z`: the tricorn is an even function. -/
theorem Tantibar_neg (c z : ℂ) : Tantibar c (-z) = Tantibar c z := by
  simp [Tantibar]

/-- **The canonical coordinate is odd on the critical domain.**  The ratio
`ρ z = φ (-z) / φ z` is continuous on the preconnected critical domain, takes values in `{±1}`
there (`φ (T_c (-z)) = φ (T_c z)`), and equals `-1` at a far point of the critical domain, where
`φ` is the odd product formula. -/
theorem varphiCrit_neg (c : ℂ) {z : ℂ} (hz : z ∈ Work.ParamRays.critDomain c) :
    Work.Bottcher.varphiCrit c (-z) = -Work.Bottcher.varphiCrit c z := by
  set D : Set ℂ := Work.ParamRays.critDomain c with hD
  have hnegmem : Set.MapsTo (fun w : ℂ => -w) D D := fun w hw => neg_mem_critDomain c hw
  have hcont : ContinuousOn
      (fun w : ℂ => Work.Bottcher.varphiCrit c (-w) / Work.Bottcher.varphiCrit c w) D :=
    ((Work.Bottcher.varphiCrit_continuousOn c).comp continuous_neg.continuousOn hnegmem).div
      (Work.Bottcher.varphiCrit_continuousOn c)
      (fun w hw => Work.Bottcher.varphiCrit_ne_zero hw)
  have hpre : IsPreconnected
      ((fun w : ℂ => Work.Bottcher.varphiCrit c (-w) / Work.Bottcher.varphiCrit c w) '' D) :=
    (Work.ParamRays.isPreconnected_critDomain c).image _ hcont
  have hsub : (fun w : ℂ => Work.Bottcher.varphiCrit c (-w) / Work.Bottcher.varphiCrit c w) '' D ⊆
      {ζ : ℂ | ∃ n : ℕ, ζ ^ 2 ^ n = 1} := by
    rintro ζ ⟨w, hw, rfl⟩
    refine ⟨1, ?_⟩
    have hsq : Work.Bottcher.varphiCrit c (-w) ^ 2 = Work.Bottcher.varphiCrit c w ^ 2 := by
      have hT : Tantibar c (-w) = Tantibar c w := Tantibar_neg c w
      have h2 := Work.Bottcher.varphiCrit_comm_Tantibar (neg_mem_critDomain c hw)
      rw [hT] at h2
      have h3 := Work.Bottcher.varphiCrit_comm_Tantibar hw
      have h4 : (starRingEnd ℂ) (Work.Bottcher.varphiCrit c (-w)) ^ 2 =
          (starRingEnd ℂ) (Work.Bottcher.varphiCrit c w) ^ 2 := by rw [← h2, ← h3]
      have h5 := congrArg (starRingEnd ℂ) h4
      simpa using h5
    have hgoal : (Work.Bottcher.varphiCrit c (-w) / Work.Bottcher.varphiCrit c w) ^ 2 = 1 := by
      rw [div_pow, hsq, div_self (pow_ne_zero 2 (Work.Bottcher.varphiCrit_ne_zero hw))]
    simpa using hgoal
  have hsingle : ((fun w : ℂ => Work.Bottcher.varphiCrit c (-w) / Work.Bottcher.varphiCrit c w)
      '' D).Subsingleton :=
    Work.ParamRays.isPreconnected_subsingleton_of_pow_two_pow_eq_one hpre hsub
  obtain ⟨z₀, hz₀, hz₀D⟩ := Work.ParamRays.exists_mem_critDomain_gt_norm c (farThresh c)
  have hz₀thin : farThresh c < ‖-z₀‖ := by rwa [norm_neg]
  have hz₀ne : z₀ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz₀
    exact absurd hz₀ (not_lt.mpr (le_of_lt (farThresh_pos c)))
  have hval : Work.Bottcher.varphiCrit c (-z₀) / Work.Bottcher.varphiCrit c z₀ = -1 := by
    rw [far_eq_bottcher c hz₀thin, far_eq_bottcher c hz₀, Work.Bottcher.Inverse.bottcher_neg]
    have hbne : Work.Bottcher.bottcher c z₀ ≠ 0 := by
      rw [Work.Bottcher.bottcher]
      exact mul_ne_zero hz₀ne (Complex.exp_ne_zero _)
    rw [neg_div, div_self hbne]
  have hzD : z ∈ D := hz
  have h := (hsingle ⟨z, hzD, rfl⟩ ⟨z₀, hz₀D, rfl⟩).trans hval
  rw [div_eq_iff (Work.Bottcher.varphiCrit_ne_zero hzD)] at h
  simpa using h

/-! ## One-step descent on the critical domain -/

/-- **Two points of the critical domain with the same `p_c`-image and the same `φ`-value
coincide.**  This is `Work.Bottcher.Inverse.pMap_eq_imp_eq` with its hypotheses (oddness, the
antiholomorphic Böttcher equation, non-vanishing) required only on the critical domain — all the
points fed to them in the descent below are `p_c`-iterates of points of the critical domain. -/
theorem pMap_eq_imp_eq_critDomain (c : ℂ) (φ : ℂ → ℂ)
    (hodd : ∀ z : ℂ, z ∈ Work.ParamRays.critDomain c → φ (-z) = -φ z)
    (hT : ∀ z : ℂ, z ∈ Work.ParamRays.critDomain c →
      φ (Tantibar c z) = (starRingEnd ℂ) (φ z) ^ 2)
    (hZne : ∀ z : ℂ, z ∈ Work.ParamRays.critDomain c → φ z ≠ 0)
    {u v : ℂ} (hu : u ∈ Work.ParamRays.critDomain c) (hv : v ∈ Work.ParamRays.critDomain c)
    (hp : Work.Bottcher.pMap c u = Work.Bottcher.pMap c v) (hφ : φ u = φ v) : u = v := by
  -- `a = -a` forces `a = 0`.
  have key : ∀ a : ℂ, a = -a → a = 0 := by
    intro a ha
    have h : a + a = 0 := (eq_neg_iff_add_eq_zero).mp ha
    have h2 : (2 : ℂ) * a = 0 := by rw [two_mul]; exact h
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
  -- The quartic factorisation of the difference.
  have hfac : (u - v) * (u + v) * (u ^ 2 + v ^ 2 + 2 * (starRingEnd ℂ) c) = 0 := by
    have h := Work.Bottcher.Inverse.pMap_sub_pMap c u v
    rw [hp, sub_self] at h
    exact h.symm
  rcases mul_eq_zero.mp hfac with h12 | h3
  · rcases mul_eq_zero.mp h12 with huv | huv
    · exact sub_eq_zero.mp huv
    · -- `u + v = 0`, i.e. `v = -u`, is incompatible with oddness.
      have hv_eq : v = -u := eq_neg_of_add_eq_zero_right huv
      have hphi_neg : φ u = -φ u := by
        have h1 : φ u = φ (-u) := by rw [← hv_eq, hφ]
        exact h1.trans (hodd u hu)
      exact absurd (key (φ u) hphi_neg) (hZne u hu)
  · -- `u² + v² + 2 conj c = 0`, i.e. `T_c u = -T_c v`.
    have hTuv : Tantibar c u + Tantibar c v = 0 := by
      have hc : (starRingEnd ℂ) u ^ 2 + (starRingEnd ℂ) v ^ 2 + 2 * c = 0 := by
        have h := congrArg (starRingEnd ℂ) h3
        simp only [map_add, map_mul, map_pow, map_ofNat, map_zero, starRingEnd_self_apply] at h
        exact h
      simp only [Tantibar]
      linear_combination hc
    have hTv : Tantibar c v = -Tantibar c u := eq_neg_of_add_eq_zero_right hTuv
    have hTmem : Tantibar c u ∈ Work.ParamRays.critDomain c :=
      Work.ParamRays.Tantibar_mem_critDomain hu
    have hphiT_eq : φ (Tantibar c u) = φ (Tantibar c v) := by
      rw [hT u hu, hT v hv, hφ]
    have hphiT_neg : φ (Tantibar c v) = -φ (Tantibar c u) := by
      rw [hTv]; exact hodd (Tantibar c u) hTmem
    have hphi_neg : φ (Tantibar c u) = -φ (Tantibar c u) := hphiT_eq.trans hphiT_neg
    exact absurd (key (φ (Tantibar c u)) hphi_neg) (hZne (Tantibar c u) hTmem)

end

end Work.LandLeaves.CritInj

namespace Work.LandLeaves

/-- **The critical Böttcher coordinate is injective on the critical domain.**

Two points `z₁, z₂` of `critDomain c` with `varphiCrit c z₁ = varphiCrit c z₂`: the `p_c`-orbits
of `z₁` and `z₂` carry the same `varphiCrit`-values (the `p_c`-Böttcher equation
`varphiCrit_comm_pMap`), and once they are far beyond `farThresh c` the canonical coordinate is
the explicit product formula, which is injective there (`bottcher_injOn_far`); hence the orbits
meet, and descending one `p_c`-step at a time with the critical-domain descent lemma
`pMap_eq_imp_eq_critDomain` (oddness is `varphiCrit_neg`, non-vanishing is
`varphiCrit_ne_zero`) gives `z₁ = z₂`. -/
theorem critBottcher_injOn_critDomain (c : ℂ) :
    Set.InjOn (Work.Bottcher.varphiCrit c) (Work.ParamRays.critDomain c) := by
  intro z₁ hz₁ z₂ hz₂ hφ
  let u : ℕ → ℂ := fun k => (Work.Bottcher.pMap c)^[k] z₁
  let v : ℕ → ℂ := fun k => (Work.Bottcher.pMap c)^[k] z₂
  let W : ℂ := Work.Bottcher.varphiCrit c z₁
  have hu_succ : ∀ k : ℕ, u (k + 1) = Work.Bottcher.pMap c (u k) := by
    intro k
    simp only [u]
    exact Function.iterate_succ_apply' (Work.Bottcher.pMap c) k z₁
  have hv_succ : ∀ k : ℕ, v (k + 1) = Work.Bottcher.pMap c (v k) := by
    intro k
    simp only [v]
    exact Function.iterate_succ_apply' (Work.Bottcher.pMap c) k z₂
  have humem : ∀ k : ℕ, u k ∈ Work.ParamRays.critDomain c := by
    intro k
    simp only [u]
    exact CritInj.pMap_iterate_mem_critDomain c hz₁ k
  have hvmem : ∀ k : ℕ, v k ∈ Work.ParamRays.critDomain c := by
    intro k
    simp only [v]
    exact CritInj.pMap_iterate_mem_critDomain c hz₂ k
  -- the `varphiCrit`-values along the two orbits
  have hφu : ∀ k : ℕ, Work.Bottcher.varphiCrit c (u k) = W ^ (4 ^ k) := by
    intro k
    induction k with
    | zero => simp only [u, Function.iterate_zero_apply, pow_zero, pow_one]; rfl
    | succ k ih =>
        rw [hu_succ k, CritInj.varphiCrit_comm_pMap (humem k), ih, ← pow_mul, pow_succ]
  have hφv : ∀ k : ℕ, Work.Bottcher.varphiCrit c (v k) = W ^ (4 ^ k) := by
    intro k
    induction k with
    | zero => simp only [v, Function.iterate_zero_apply, pow_zero, pow_one]; exact hφ.symm
    | succ k ih =>
        rw [hv_succ k, CritInj.varphiCrit_comm_pMap (hvmem k), ih, ← pow_mul, pow_succ]
  -- both orbits reach the far region
  have hu_tend : Tendsto u atTop (cocompact ℂ) := by
    simp only [u]
    exact Work.Bottcher.Contraction.tendsto_iterate_pMap_cocompact_of_mem_CritDomain c
      (by rw [Work.Bottcher.CritBasic.critDomain_eq]; exact hz₁)
  have hv_tend : Tendsto v atTop (cocompact ℂ) := by
    simp only [v]
    exact Work.Bottcher.Contraction.tendsto_iterate_pMap_cocompact_of_mem_CritDomain c
      (by rw [Work.Bottcher.CritBasic.critDomain_eq]; exact hz₂)
  have hnrmu : Tendsto (fun k : ℕ => ‖u k‖) atTop atTop :=
    (tendsto_norm_cocompact_atTop (E := ℂ)).comp hu_tend
  have hnrmv : Tendsto (fun k : ℕ => ‖v k‖) atTop atTop :=
    (tendsto_norm_cocompact_atTop (E := ℂ)).comp hv_tend
  have hev : ∀ᶠ k : ℕ in atTop, CritInj.farThresh c < ‖u k‖ ∧ CritInj.farThresh c < ‖v k‖ :=
    (hnrmu.eventually (eventually_gt_atTop (CritInj.farThresh c))).and
      (hnrmv.eventually (eventually_gt_atTop (CritInj.farThresh c)))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  have hN' := hN N le_rfl
  have hfar_eq : u N = v N :=
    CritInj.injOn_farThresh c hN'.1 hN'.2 (by rw [hφu N, hφv N])
  -- descend from `u N = v N` to `z₁ = z₂`
  have hdescend : ∀ k : ℕ, u k = v k → z₁ = z₂ := by
    intro k
    induction k with
    | zero => intro h; simpa only [u, v, Function.iterate_zero_apply] using h
    | succ k ih =>
        intro h
        have h1 : Work.Bottcher.pMap c (u k) = Work.Bottcher.pMap c (v k) := by
          rw [← hu_succ k, ← hv_succ k]
          exact h
        have h2 : Work.Bottcher.varphiCrit c (u k) = Work.Bottcher.varphiCrit c (v k) := by
          rw [hφu k, hφv k]
        exact ih (CritInj.pMap_eq_imp_eq_critDomain c (Work.Bottcher.varphiCrit c)
          (fun z hz => CritInj.varphiCrit_neg c hz)
          (fun z hz => Work.Bottcher.varphiCrit_comm_Tantibar hz)
          (fun z hz => Work.Bottcher.varphiCrit_ne_zero hz)
          (humem k) (hvmem k) h1 h2)
  exact hdescend N hfar_eq

end Work.LandLeaves
