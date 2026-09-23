import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
import Submission.Commons.Analysis.ODE.exists_uniform_local_solution_linearODE
import Submission.Commons.Analysis.ODE.norm_le_exp_mul_norm_of_linearODE
import Submission.Commons.Analysis.ODE.exists_uniform_secondOrderODE_solution_in_open

namespace Commons.Analysis.ODE

open Set
open scoped NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Uniqueness for the linear ODE `y' = A t (y t)` on a closed interval `[a, b]`, where the
derivative hypothesis holds on the whole closed interval. -/
theorem eqOn_of_hasDerivAt_linearODE {A : ℝ → E →L[ℝ] E} {M : ℝ≥0}
    {a b t₀ : ℝ} (hM : ∀ t ∈ Icc a b, ‖A t‖ ≤ M) (ht₀ : t₀ ∈ Icc a b) {y z : ℝ → E}
    (hy : ∀ t ∈ Icc a b, HasDerivAt y (A t (y t)) t)
    (hz : ∀ t ∈ Icc a b, HasDerivAt z (A t (z t)) t) (heq : y t₀ = z t₀) :
    EqOn y z (Icc a b) := by
  have hlip : ∀ t ∈ Icc a b, LipschitzOnWith M (fun y : E => A t y) univ := fun t ht =>
    (ContinuousLinearMap.lipschitzWith_of_opNorm_le (hM t ht)).lipschitzOnWith
  rcases lt_or_eq_of_le ht₀.1 with hat₀ | hat₀
  · rcases lt_or_eq_of_le ht₀.2 with ht₀b | ht₀b
    · exact ODE_solution_unique_of_mem_Icc (v := fun t y => A t y) (s := fun _ => univ)
        (K := M) (f := y) (g := z) (t₀ := t₀)
        (fun t ht => hlip t (Ioo_subset_Icc_self ht)) ⟨hat₀, ht₀b⟩
        (HasDerivAt.continuousOn hy)
        (fun t ht => hy t (Ioo_subset_Icc_self ht))
        (fun _ _ => trivial)
        (HasDerivAt.continuousOn hz)
        (fun t ht => hz t (Ioo_subset_Icc_self ht))
        (fun _ _ => trivial) heq
    · have hb : y b = z b := by rw [← ht₀b]; exact heq
      exact ODE_solution_unique_of_mem_Icc_left (v := fun t y => A t y) (s := fun _ => univ)
        (K := M) (f := y) (g := z)
        (fun t ht => hlip t (Ioc_subset_Icc_self ht))
        (HasDerivAt.continuousOn hy)
        (fun t ht => (hy t (Ioc_subset_Icc_self ht)).hasDerivWithinAt)
        (fun _ _ => trivial)
        (HasDerivAt.continuousOn hz)
        (fun t ht => (hz t (Ioc_subset_Icc_self ht)).hasDerivWithinAt)
        (fun _ _ => trivial) hb
  · have ha : y a = z a := by rw [hat₀]; exact heq
    exact ODE_solution_unique_of_mem_Icc_right (v := fun t y => A t y) (s := fun _ => univ)
      (K := M) (f := y) (g := z)
      (fun t ht => hlip t (Ico_subset_Icc_self ht))
      (HasDerivAt.continuousOn hy)
      (fun t ht => (hy t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
      (fun _ _ => trivial)
      (HasDerivAt.continuousOn hz)
      (fun t ht => (hz t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
      (fun _ _ => trivial) ha

/-- Existence of solutions of a bounded continuous time-dependent linear ODE on a symmetric open
window `(t₀ - T, t₀ + T)`. -/
theorem exists_solution_window_of_continuous_linearODE [CompleteSpace E]
    {A : ℝ → E →L[ℝ] E} (hAc : Continuous A) {M : ℝ≥0} (hM : ∀ t, ‖A t‖ ≤ M)
    {t₀ : ℝ} {y₀ : E} {T : ℝ} (hT : 0 < T) :
    ∃ y : ℝ → E, y t₀ = y₀ ∧ ∀ t ∈ Ioo (t₀ - T) (t₀ + T), HasDerivAt y (A t (y t)) t := by
  classical
  -- ## A priori radius
  set R : ℝ := ‖y₀‖ * Real.exp ((M : ℝ) * T) + 1 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; positivity
  have hy₀R : ‖y₀‖ ≤ R := by
    rw [hRdef]
    have h1 : (1 : ℝ) ≤ Real.exp ((M : ℝ) * T) := Real.one_le_exp (by positivity)
    nlinarith [norm_nonneg y₀, Real.exp_pos ((M : ℝ) * T)]
  -- ## Uniform local existence
  obtain ⟨ε₀, hε₀pos, hε₀le1, hloc₀⟩ := exists_uniform_local_solution_linearODE hAc hM hRpos.le
  set ε : ℝ := min ε₀ (T / 2) with hεdef
  have hεpos : 0 < ε := lt_min hε₀pos (by linarith)
  have hεε₀ : ε ≤ ε₀ := min_le_left _ _
  have hεT : ε ≤ T / 2 := min_le_right _ _
  have hε1 : ε ≤ 1 := le_trans hεε₀ hε₀le1
  have hloc : ∀ (t₁ : ℝ) (x₁ : E), ‖x₁‖ ≤ R → ∃ α : ℝ → E, α t₁ = x₁ ∧
      ∀ t ∈ Icc (t₁ - ε) (t₁ + ε),
        HasDerivWithinAt α (A t (α t)) (Icc (t₁ - ε) (t₁ + ε)) t := by
    intro t₁ x₁ hx
    obtain ⟨α, hα, hαd⟩ := hloc₀ t₁ x₁ hx
    have hsub : Icc (t₁ - ε) (t₁ + ε) ⊆ Icc (t₁ - ε₀) (t₁ + ε₀) :=
      Icc_subset_Icc (by linarith) (by linarith)
    exact ⟨α, hα, fun t ht => (hαd t (hsub ht)).mono hsub⟩
  -- a convenience conversion
  have hmemwin : ∀ (x c : ℝ), x ∈ Ioo (t₀ - c) (t₀ + c) ↔ |x - t₀| < c := by
    intro x c
    rw [mem_Ioo, abs_lt]
    constructor <;> intro h <;> exact ⟨by linarith [h.1], by linarith [h.2]⟩
  -- ## The set of admissible window radii
  let S : Set ℝ := {c | 0 ≤ c ∧ c ≤ T ∧ ∃ z : ℝ → E, z t₀ = y₀ ∧
      ∀ t ∈ Ioo (t₀ - c) (t₀ + c), HasDerivAt z (A t (z t)) t}
  have hSmem : ∀ c : ℝ, c ∈ S ↔ 0 ≤ c ∧ c ≤ T ∧ ∃ z : ℝ → E, z t₀ = y₀ ∧
      ∀ t ∈ Ioo (t₀ - c) (t₀ + c), HasDerivAt z (A t (z t)) t := fun c => by
    simp only [S, mem_ofPred_eq]
  have hεS : ε ∈ S := by
    rw [hSmem]
    refine ⟨hεpos.le, by linarith, ?_⟩
    obtain ⟨α, hα, hαd⟩ := hloc t₀ y₀ hy₀R
    exact ⟨α, hα, fun t ht => (hαd t (Ioo_subset_Icc_self ht)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)⟩
  have hSne : S.Nonempty := ⟨ε, hεS⟩
  have hSbdd : BddAbove S := ⟨T, fun c hc => ((hSmem c).mp hc).2.1⟩
  set cstar : ℝ := sSup S with hcstardef
  have hcstar_ge : ε ≤ cstar := le_csSup hSbdd hεS
  have hcstar_pos : 0 < cstar := lt_of_lt_of_le hεpos hcstar_ge
  have hcstar_le : cstar ≤ T := csSup_le hSne (fun c hc => ((hSmem c).mp hc).2.1)
  -- ## Solutions attached to each element of `S`
  have hex : ∀ c : ℝ, c ∈ S → ∃ z : ℝ → E, z t₀ = y₀ ∧
      ∀ t ∈ Ioo (t₀ - c) (t₀ + c), HasDerivAt z (A t (z t)) t :=
    fun c hc => ((hSmem c).mp hc).2.2
  let sol : ℝ → ℝ → E := fun c => if hc : c ∈ S then (hex c hc).choose else fun _ => y₀
  have hsol0 : ∀ (c : ℝ) (hc : c ∈ S), sol c t₀ = y₀ := fun c hc => by
    simp only [sol, dif_pos hc]
    exact (hex c hc).choose_spec.1
  have hsold : ∀ (c : ℝ) (hc : c ∈ S) (u : ℝ), u ∈ Ioo (t₀ - c) (t₀ + c) →
      HasDerivAt (sol c) (A u (sol c u)) u := fun c hc u hu => by
    simp only [sol, dif_pos hc]
    exact (hex c hc).choose_spec.2 u hu
  have hcompat : ∀ (c c' : ℝ) (hc : c ∈ S) (hc' : c' ∈ S),
      EqOn (sol c) (sol c') (Ioo (t₀ - min c c') (t₀ + min c c')) := by
    intro c c' hc hc'
    by_cases hmin : 0 < min c c'
    · refine ODE_solution_unique_of_mem_Ioo (v := fun t y => A t y) (s := fun _ => univ) (K := M)
        (t₀ := t₀) (a := t₀ - min c c') (b := t₀ + min c c')
        (fun t _ => (ContinuousLinearMap.lipschitzWith_of_opNorm_le (hM t)).lipschitzOnWith)
        ⟨by linarith, by linarith⟩
        (fun u hu => ⟨hsold c hc u ⟨by linarith [hu.1, min_le_left c c'],
          by linarith [hu.2, min_le_left c c']⟩, trivial⟩)
        (fun u hu => ⟨hsold c' hc' u ⟨by linarith [hu.1, min_le_right c c'],
          by linarith [hu.2, min_le_right c c']⟩, trivial⟩)
        (by rw [hsol0 c hc, hsol0 c' hc'])
    · intro u hu
      exfalso
      linarith [hu.1, hu.2, not_lt.mp hmin]
  -- ## The solution built from the supremum
  have hltS : ∀ c : ℝ, c < cstar → ∃ c' ∈ S, c < c' :=
    fun c hc => (lt_csSup_iff hSbdd hSne).mp hc
  let Cd : ℝ → ℝ := fun t => if h : |t - t₀| < cstar then (hltS |t - t₀| h).choose else ε
  have hCd_mem : ∀ t : ℝ, |t - t₀| < cstar → Cd t ∈ S := fun t h => by
    simp only [Cd, dif_pos h]; exact (hltS |t - t₀| h).choose_spec.1
  have hCd_gt : ∀ t : ℝ, |t - t₀| < cstar → |t - t₀| < Cd t := fun t h => by
    simp only [Cd, dif_pos h]; exact (hltS |t - t₀| h).choose_spec.2
  have hCd_le : ∀ t : ℝ, |t - t₀| < cstar → Cd t ≤ cstar := fun t h =>
    le_csSup hSbdd (hCd_mem t h)
  let zstar : ℝ → E := fun t => sol (Cd t) t
  have hzstar_ev : ∀ t : ℝ, |t - t₀| < cstar → zstar =ᶠ[𝓝 t] sol (Cd t) := by
    intro t ht
    have htwin : t ∈ Ioo (t₀ - Cd t) (t₀ + Cd t) := (hmemwin t (Cd t)).mpr (hCd_gt t ht)
    filter_upwards [isOpen_Ioo.mem_nhds htwin] with u hu
    have hut : |u - t₀| < Cd t := (hmemwin u (Cd t)).mp hu
    have huc : |u - t₀| < cstar := lt_of_lt_of_le hut (hCd_le t ht)
    have hmin : |u - t₀| < min (Cd u) (Cd t) := lt_min (hCd_gt u huc) hut
    exact hcompat (Cd u) (Cd t) (hCd_mem u huc) (hCd_mem t ht)
      ((hmemwin u (min (Cd u) (Cd t))).mpr hmin)
  have hzstar0 : zstar t₀ = y₀ := by
    have h : |t₀ - t₀| < cstar := by simp [hcstar_pos]
    show sol (Cd t₀) t₀ = y₀
    exact hsol0 (Cd t₀) (hCd_mem t₀ h)
  have hzstar_deriv : ∀ t : ℝ, |t - t₀| < cstar → HasDerivAt zstar (A t (zstar t)) t := by
    intro t ht
    have htwin : t ∈ Ioo (t₀ - Cd t) (t₀ + Cd t) := (hmemwin t (Cd t)).mpr (hCd_gt t ht)
    have h1 : HasDerivAt (sol (Cd t)) (A t (sol (Cd t) t)) t :=
      hsold (Cd t) (hCd_mem t ht) t htwin
    have h2 : zstar t = sol (Cd t) t := (hzstar_ev t ht).eq_of_nhds
    have h3 : HasDerivAt zstar (A t (sol (Cd t) t)) t :=
      h1.congr_of_eventuallyEq (hzstar_ev t ht)
    rwa [← h2] at h3
  -- ## Extension step
  have hext : cstar < T → ∃ c' ∈ S, cstar < c' := by
    intro hcsT
    set ε₂ : ℝ := min ε ((T - cstar) / 3) with hε₂def
    have hε₂pos : 0 < ε₂ := lt_min hεpos (by linarith)
    have hε₂ε : ε₂ ≤ ε := min_le_left _ _
    have hε₂bound : 3 * ε₂ ≤ T - cstar := by
      have h := min_le_right ε ((T - cstar) / 3); linarith
    have hε₂cstar : ε₂ ≤ cstar := le_trans hε₂ε hcstar_ge
    have hloc₂ : ∀ (t₁ : ℝ) (x₁ : E), ‖x₁‖ ≤ R → ∃ α : ℝ → E, α t₁ = x₁ ∧
        ∀ t ∈ Icc (t₁ - ε₂) (t₁ + ε₂),
          HasDerivWithinAt α (A t (α t)) (Icc (t₁ - ε₂) (t₁ + ε₂)) t := by
      intro t₁ x₁ hx
      obtain ⟨α, hα, hαd⟩ := hloc t₁ x₁ hx
      have hsub : Icc (t₁ - ε₂) (t₁ + ε₂) ⊆ Icc (t₁ - ε) (t₁ + ε) :=
        Icc_subset_Icc (by linarith) (by linarith)
      exact ⟨α, hα, fun t ht => (hαd t (hsub ht)).mono hsub⟩
    -- the a priori bound
    have hzstarR : ∀ t ∈ Ioo (t₀ - cstar) (t₀ + cstar), ‖zstar t‖ ≤ R := by
      intro t ht
      have htabs : |t - t₀| < cstar := (hmemwin t cstar).mp ht
      have hd : ∀ s ∈ Icc (min t₀ t) (max t₀ t), HasDerivAt zstar (A s (zstar s)) s := by
        intro s hs
        have hsabs : |s - t₀| < cstar := by
          have hs' : s ∈ Ioo (t₀ - cstar) (t₀ + cstar) := by
            rcases le_total t₀ t with h | h
            · rw [min_eq_left h, max_eq_right h] at hs
              exact ⟨by linarith [hs.1], by linarith [hs.2, (abs_lt.mp htabs).2]⟩
            · rw [min_eq_right h, max_eq_left h] at hs
              exact ⟨by linarith [hs.1, (abs_lt.mp htabs).1], by linarith [hs.2]⟩
          exact (hmemwin s cstar).mp hs'
        exact hzstar_deriv s hsabs
      have hgr := norm_le_exp_mul_norm_of_linearODE hM hd
      have hexp : Real.exp ((M : ℝ) * |t - t₀|) ≤ Real.exp ((M : ℝ) * T) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [htabs, hcstar_le]) M.coe_nonneg)
      calc ‖zstar t‖ ≤ ‖zstar t₀‖ * Real.exp ((M : ℝ) * |t - t₀|) := hgr
        _ = ‖y₀‖ * Real.exp ((M : ℝ) * |t - t₀|) := by rw [hzstar0]
        _ ≤ ‖y₀‖ * Real.exp ((M : ℝ) * T) := mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
        _ ≤ R := by rw [hRdef]; linarith
    -- the two restart points
    set t₁ : ℝ := t₀ + cstar - ε₂ / 3 with ht₁def
    set t₂ : ℝ := t₀ - cstar + ε₂ / 3 with ht₂def
    have ht₂t₁ : t₂ < t₁ := by rw [ht₁def, ht₂def]; linarith
    have ht₁mem : t₁ ∈ Ioo (t₀ - cstar) (t₀ + cstar) := by
      rw [ht₁def]; exact ⟨by linarith, by linarith⟩
    have ht₂mem : t₂ ∈ Ioo (t₀ - cstar) (t₀ + cstar) := by
      rw [ht₂def]; exact ⟨by linarith, by linarith⟩
    have ht₁abs : |t₁ - t₀| < cstar := (hmemwin t₁ cstar).mp ht₁mem
    have ht₂abs : |t₂ - t₀| < cstar := (hmemwin t₂ cstar).mp ht₂mem
    obtain ⟨αR, hαR0, hαRd⟩ := hloc₂ t₁ (zstar t₁) (hzstarR t₁ ht₁mem)
    obtain ⟨αL, hαL0, hαLd⟩ := hloc₂ t₂ (zstar t₂) (hzstarR t₂ ht₂mem)
    have hαR' : ∀ t ∈ Ioo (t₁ - ε₂) (t₁ + ε₂), HasDerivAt αR (A t (αR t)) t := fun t ht =>
      (hαRd t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    have hαL' : ∀ t ∈ Ioo (t₂ - ε₂) (t₂ + ε₂), HasDerivAt αL (A t (αL t)) t := fun t ht =>
      (hαLd t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    have hαReq : αR =ᶠ[𝓝 t₁] zstar := by
      refine ODE_solution_unique_of_eventually (v := fun t : ℝ => A t) (s := fun _ => univ)
        (K := M) (t₀ := t₁) (f := αR) (g := zstar) ?_ ?_ ?_ ?_
      · exact Filter.Eventually.of_forall fun t =>
          (ContinuousLinearMap.lipschitzWith_of_opNorm_le (hM t)).lipschitzOnWith
      · filter_upwards [Ioo_mem_nhds (by linarith [hε₂pos] : t₁ - ε₂ < t₁)
          (by linarith [hε₂pos] : t₁ < t₁ + ε₂)] with u hu
        exact ⟨hαR' u hu, trivial⟩
      · filter_upwards [isOpen_Ioo.mem_nhds ht₁mem] with u hu
        exact ⟨hzstar_deriv u ((hmemwin u cstar).mp hu), trivial⟩
      · rw [hαR0]
    have hαLeq : αL =ᶠ[𝓝 t₂] zstar := by
      refine ODE_solution_unique_of_eventually (v := fun t : ℝ => A t) (s := fun _ => univ)
        (K := M) (t₀ := t₂) (f := αL) (g := zstar) ?_ ?_ ?_ ?_
      · exact Filter.Eventually.of_forall fun t =>
          (ContinuousLinearMap.lipschitzWith_of_opNorm_le (hM t)).lipschitzOnWith
      · filter_upwards [Ioo_mem_nhds (by linarith [hε₂pos] : t₂ - ε₂ < t₂)
          (by linarith [hε₂pos] : t₂ < t₂ + ε₂)] with u hu
        exact ⟨hαL' u hu, trivial⟩
      · filter_upwards [isOpen_Ioo.mem_nhds ht₂mem] with u hu
        exact ⟨hzstar_deriv u ((hmemwin u cstar).mp hu), trivial⟩
      · rw [hαL0]
    -- the glued solution
    set winner : ℝ → E := fun u => if u < t₁ then zstar u else αR u with hwinnerdef
    set w : ℝ → E := fun u => if u < t₂ then αL u else winner u with hwdef
    have hwin_ev : winner =ᶠ[𝓝 t₂] zstar := by
      filter_upwards [Ioo_mem_nhds (by linarith : t₂ - 1 < t₂) ht₂t₁] with u hu
      simp only [hwinnerdef, if_pos hu.2]
    have hwin_ev₁ : winner =ᶠ[𝓝 t₁] zstar := by
      filter_upwards [isOpen_Ioo.mem_nhds ht₁mem, hαReq] with u hu hα
      by_cases h : u < t₁
      · simp only [hwinnerdef, if_pos h]
      · simp only [hwinnerdef, if_neg h, hα]
    have hwin_deriv : HasDerivAt winner (A t₂ (winner t₂)) t₂ := by
      have h₁ : HasDerivAt zstar (A t₂ (zstar t₂)) t₂ := hzstar_deriv t₂ ht₂abs
      have h₂ := h₁.congr_of_eventuallyEq hwin_ev
      rwa [← hwin_ev.eq_of_nhds] at h₂
    have hwin_deriv₁ : HasDerivAt αR (A t₁ (αR t₁)) t₁ :=
      hαR' t₁ ⟨by linarith [hε₂pos], by linarith [hε₂pos]⟩
    have hw₂ : w t₂ = winner t₂ := by simp only [hwdef, if_neg (lt_irrefl t₂)]
    have hglue₂ : HasDerivAt w (A t₂ (w t₂)) t₂ := by
      have h := hasDerivAt_ite_lt_of_eventuallyEq (w₁ := αL) (w₂ := winner) (τ := t₂)
        (hαLeq.trans hwin_ev.symm) hwin_deriv
      have h' : HasDerivAt w (A t₂ (winner t₂)) t₂ := by simpa only [hwdef] using h
      rwa [← hw₂] at h'
    have hevW₁ : w =ᶠ[𝓝 t₁] (fun t => if t < t₁ then winner t else αR t) := by
      filter_upwards [Ioo_mem_nhds ht₂t₁ (by linarith : t₁ < t₁ + 1)] with t ht
      have ht₂t : ¬ (t < t₂) := not_lt.mpr (le_of_lt ht.1)
      by_cases h : t < t₁
      · simp only [hwdef, hwinnerdef, if_neg ht₂t, if_pos h]
      · simp only [hwdef, hwinnerdef, if_neg ht₂t, if_neg h]
    have hw₁ : w t₁ = αR t₁ := by
      simp only [hwdef, hwinnerdef, hαR0, if_neg (not_lt.mpr (le_of_lt ht₂t₁)), if_neg (lt_irrefl t₁)]
    have hglue₁ : HasDerivAt w (A t₁ (w t₁)) t₁ := by
      have h := hasDerivAt_ite_lt_of_eventuallyEq (w₁ := winner) (w₂ := αR) (τ := t₁)
        (hwin_ev₁.trans (hαReq.symm)) hwin_deriv₁
      have h₂ : HasDerivAt w (A t₁ (αR t₁)) t₁ := h.congr_of_eventuallyEq hevW₁
      rwa [← hw₁] at h₂
    have hwderiv : ∀ u ∈ Ioo (t₀ - cstar - 2 * ε₂ / 3) (t₀ + cstar + 2 * ε₂ / 3),
        HasDerivAt w (A u (w u)) u := by
      intro u hu
      have hlow : t₂ - ε₂ = t₀ - cstar - 2 * ε₂ / 3 := by rw [ht₂def]; ring
      have hhigh : t₁ + ε₂ = t₀ + cstar + 2 * ε₂ / 3 := by rw [ht₁def]; ring
      rcases lt_trichotomy u t₂ with h | h | h
      · -- left of t₂
        have huL : u ∈ Ioo (t₂ - ε₂) (t₂ + ε₂) := by
          refine ⟨?_, by linarith⟩
          rw [hlow]; exact hu.1
        have hev : w =ᶠ[𝓝 u] αL := by
          filter_upwards [isOpen_Iio.mem_nhds h] with v hv
          simp only [Set.mem_Iio] at hv
          simp only [hwdef, if_pos hv]
        have hwu : w u = αL u := by simp only [hwdef, if_pos h]
        rw [hwu]
        exact (hαL' u huL).congr_of_eventuallyEq hev
      · subst h
        exact hglue₂
      · by_cases h₂ : u < t₁
        · -- between t₂ and t₁
          have huM : |u - t₀| < cstar := by
            have : u ∈ Ioo (t₀ - cstar) (t₀ + cstar) := by
              constructor <;> linarith [hu.1, hu.2, ht₁def, ht₂def, hε₂pos]
            exact (hmemwin u cstar).mp this
          have hev : w =ᶠ[𝓝 u] zstar := by
            filter_upwards [isOpen_Ioo.mem_nhds (⟨h, h₂⟩ : u ∈ Ioo t₂ t₁)] with v hv
            have hv2 : ¬ (v < t₂) := not_lt.mpr hv.1.le
            simp only [hwdef, hv2, if_false, hwinnerdef, if_pos hv.2]
          have hwu : w u = zstar u := by
            simp only [hwdef, if_neg (not_lt.mpr h.le), hwinnerdef, if_pos h₂]
          rw [hwu]
          exact (hzstar_deriv u huM).congr_of_eventuallyEq hev
        · rcases lt_or_eq_of_le (not_lt.mp h₂) with hlt | heq
          · -- right of t₁
            have huR : u ∈ Ioo (t₁ - ε₂) (t₁ + ε₂) := by
              refine ⟨by linarith, ?_⟩
              rw [hhigh]; exact hu.2
            have hev : w =ᶠ[𝓝 u] αR := by
              filter_upwards [isOpen_Ioi.mem_nhds hlt] with v hv
              have hv' : t₁ < v := hv
              have hv2 : ¬ (v < t₂) := not_lt.mpr (by linarith)
              simp only [hwdef, hv2, if_false, hwinnerdef, if_neg (not_lt.mpr hv'.le)]
            have hwu : w u = αR u := by
              simp only [hwdef, if_neg (not_lt.mpr h.le), hwinnerdef, if_neg h₂]
            rw [hwu]
            exact (hαR' u huR).congr_of_eventuallyEq hev
          · subst heq
            exact hglue₁
    have hw0 : w t₀ = y₀ := by
      have h1 : ¬ (t₀ < t₂) := by rw [ht₂def]; linarith [hε₂cstar]
      have h2 : t₀ < t₁ := by rw [ht₁def]; linarith [hε₂cstar]
      simp only [hwdef, if_neg h1, hwinnerdef, if_pos h2]
      exact hzstar0
    refine ⟨cstar + 2 * ε₂ / 3, ⟨by linarith [hcstar_pos], by linarith, w, hw0, ?_⟩,
      by linarith⟩
    intro u hu
    have hu' : u ∈ Ioo (t₀ - cstar - 2 * ε₂ / 3) (t₀ + cstar + 2 * ε₂ / 3) := by
      constructor <;> linarith [hu.1, hu.2]
    exact hwderiv u hu'
  -- ## Conclusion
  have hcstarT : cstar = T := by
    by_contra hne
    have hlt : cstar < T := lt_of_le_of_ne hcstar_le hne
    obtain ⟨c', hc'S, hlt'⟩ := hext hlt
    have := le_csSup hSbdd hc'S
    linarith
  have hcstarS : cstar ∈ S := ⟨hcstar_pos.le, hcstar_le, zstar, hzstar0, fun t ht =>
    hzstar_deriv t ((hmemwin t cstar).mp ht)⟩
  obtain ⟨-, -, y, hy0, hyd⟩ := (hSmem cstar).mp hcstarS
  exact ⟨y, hy0, by rw [← hcstarT]; exact hyd⟩

/-- **Existence and uniqueness for the linear ODE `y' = A t (y t)`.**  If `A : ℝ → E →L[ℝ] E` is
continuous on `[a, b]`, then for every initial datum `y₀` at time `t₀ ∈ [a, b]` there is a solution
of `y' = A t (y t)` which is differentiable on all of `[a, b]`, and any two such solutions agree on
`[a, b]`.  (The uniqueness clause must be stated with the derivative hypothesis on the *closed*
interval `[a, b]`: with `HasDerivAt` only on the open interval `(a, b)` the values at the endpoints
are unconstrained and the statement is false.  The reduction for a second order linear system
`y'' = B t (y t) + A t (y' t)` is obtained by applying this to `E × E` and the operator
`(p, v) ↦ (v, B t p + A t v)`.) -/
theorem exists_linearODE_solution_Icc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {A : ℝ → E →L[ℝ] E} {a b t₀ : ℝ} (hab : a < b)
    (hA : ContinuousOn A (Icc a b)) (ht₀ : t₀ ∈ Icc a b) (y₀ : E) :
    ∃ y : ℝ → E, y t₀ = y₀ ∧ (∀ t ∈ Icc a b, HasDerivAt y (A t (y t)) t) ∧
      ∀ z : ℝ → E, z t₀ = y₀ → (∀ t ∈ Icc a b, HasDerivAt z (A t (z t)) t) →
        EqOn z y (Icc a b) := by
  -- clamp the coefficient to `[a, b]`
  set A' : ℝ → E →L[ℝ] E := fun t => A (max a (min b t)) with hA'def
  have hc_cont : Continuous fun t : ℝ => max a (min b t) := by fun_prop
  have hc_mem : ∀ t : ℝ, max a (min b t) ∈ Icc a b := fun t =>
    ⟨le_max_left _ _, max_le hab.le (min_le_left b t)⟩
  have hc_eq : ∀ t ∈ Icc a b, max a (min b t) = t := fun t ht => by
    rw [min_eq_right ht.2, max_eq_right ht.1]
  have hA'cont : Continuous A' := by
    rw [hA'def]
    exact hA.comp_continuous hc_cont hc_mem
  have hA'eq : ∀ t ∈ Icc a b, A' t = A t := fun t ht => by
    show A (max a (min b t)) = A t
    rw [hc_eq t ht]
  have hcont_norm : ContinuousOn (fun t : ℝ => ‖A t‖) (Icc a b) :=
    continuous_norm.comp_continuousOn hA
  obtain ⟨s, hs, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (f := fun t : ℝ => ‖A t‖) ⟨a, le_rfl, le_of_lt hab⟩ hcont_norm
  set M : ℝ≥0 := ⟨max 0 ‖A s‖, le_max_left _ _⟩ with hMdef
  have hA'bound : ∀ t : ℝ, ‖A' t‖ ≤ (M : ℝ) := fun t => by
    have h1 : ‖A (max a (min b t))‖ ≤ ‖A s‖ := hmax (hc_mem t)
    have h2 : ‖A s‖ ≤ (M : ℝ) := le_max_right _ _
    rw [hA'def]
    exact le_trans h1 h2
  -- the window
  set T : ℝ := max |t₀ - a| |b - t₀| + 1 with hTdef
  have hTpos : 0 < T := by rw [hTdef]; positivity
  have hTa : |t₀ - a| < T := by rw [hTdef]; linarith [le_max_left |t₀ - a| |b - t₀|]
  have hTb : |b - t₀| < T := by rw [hTdef]; linarith [le_max_right |t₀ - a| |b - t₀|]
  have hmem : ∀ t ∈ Icc a b, t ∈ Ioo (t₀ - T) (t₀ + T) := fun t ht => by
    constructor
    · have h1 : t₀ - T < t₀ - |t₀ - a| := by linarith
      have h2 : t₀ - |t₀ - a| ≤ a := by linarith [le_abs_self (t₀ - a)]
      linarith [h1, h2, ht.1]
    · have h1 : t₀ + |b - t₀| < t₀ + T := by linarith
      have h2 : b ≤ t₀ + |b - t₀| := by linarith [le_abs_self (b - t₀)]
      linarith [h1, h2, ht.2]
  obtain ⟨y, hy0, hyd⟩ :=
    exists_solution_window_of_continuous_linearODE hA'cont hA'bound hTpos
  have hyA : ∀ t ∈ Icc a b, HasDerivAt y (A t (y t)) t := fun t ht => by
    have h := hyd t (hmem t ht)
    rwa [hA'eq t ht] at h
  refine ⟨y, hy0, hyA, ?_⟩
  intro z hz0 hz
  have hMA : ∀ t ∈ Icc a b, ‖A t‖ ≤ (M : ℝ) := fun t ht => by
    rw [← hA'eq t ht]; exact hA'bound t
  exact eqOn_of_hasDerivAt_linearODE hMA ht₀ hz hyA (by rw [hy0, hz0])

end Commons.Analysis.ODE