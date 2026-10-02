import Mathlib
import Submission.Work.ThomBordism.Grassmann.P2Base.Frame
import Submission.Work.ThomBordism.Grassmann.P2Base.Gauge
import Submission.Work.ThomBordism.Grassmann.P2Base.coefL
import Submission.Work.ThomBordism.Grassmann.PlaneEval

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

/-!
# The plane of `p2Map` is the complex span of `(Λ, Λ')`

The four real frame vectors `p2VecC s a` of the plane of the representative `s` all lie in the
complex span of `(Λ(s), Λ'(s))`, and the chart evaluation of that plane, transported back to `ℂ⁶`
by `cE6.symm`, lies in the same complex span.
-/

namespace Work.ThomBordism.Grassmann.P2Base

open Work.TangentClasses

noncomputable section

/-! ## The frame vectors -/

theorem p2VecB_mem_span (s : E5) (i : Fin 2 ⊕ Fin 2) :
    p2VecB s i ∈ Submodule.span ℂ ({lamL s, lamR s} : Set E6) := by
  have hL : lamL s ∈ Submodule.span ℂ ({lamL s, lamR s} : Set E6) :=
    Submodule.subset_span (by simp)
  have hR : lamR s ∈ Submodule.span ℂ ({lamL s, lamR s} : Set E6) :=
    Submodule.subset_span (by simp)
  have hu : lamUnit s ∈ Submodule.span ℂ ({lamL s, lamR s} : Set E6) := by
    rw [lamUnit]
    exact Submodule.smul_mem _ _ hL
  have hw : wUnit s ∈ Submodule.span ℂ ({lamL s, lamR s} : Set E6) := by
    rw [wUnit]
    refine Submodule.smul_mem _ _ ?_
    rw [wVec]
    exact Submodule.sub_mem _ hR (Submodule.smul_mem _ _ hu)
  rcases i with b | b
  · rw [p2VecB_inl]
    fin_cases b
    · simpa using hu
    · simpa using Submodule.smul_mem _ Complex.I hu
  · rw [p2VecB_inr]
    fin_cases b
    · simpa using hw
    · simpa using Submodule.smul_mem _ Complex.I hw

theorem p2VecCMemSpan (s : E5) (a : Fin 4) :
    p2VecC s a ∈ Submodule.span ℂ ({lamL s, lamR s} : Set E6) :=
  p2VecB_mem_span s (finSumFinEquiv.symm a)

/-! ## The chart evaluation lies in the real span of the frame -/

theorem evalChartO_mem_span {k m : ℕ} (S : ChartIdx k m) (f : Stiefel k m)
    (hf : f ∈ chartSet S) (v : Amb k) :
    Work.ThomBordism.Grassmann.evalChartO S
        ⟨Quotient.mk'' f, (mem_baseSet_iff S f).mpr hf⟩ v
      ∈ Submodule.span ℝ (Set.range (f.1 : Fin k → Amb (k + m))) := by
  rw [evalChartO_spec S f hf, coordEval]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (coordVec_mem_span S f i))

/-! ## Transporting back by `cE6.symm` -/

theorem cE6_symm_mem_span (s : E5) {y : Amb 12}
    (hy : y ∈ Submodule.span ℝ (Set.range (fun a : Fin 4 => cE6 (p2VecC s a)))) :
    cE6.symm y ∈ Submodule.span ℂ ({lamL s, lamR s} : Set E6) := by
  have h1 : Submodule.span ℝ (Set.range (fun a : Fin 4 => cE6 (p2VecC s a)))
      = Submodule.map (cE6 : E6 →ₗ[ℝ] Amb 12)
          (Submodule.span ℝ (Set.range (p2VecC s))) := by
    rw [Submodule.map_span]
    congr 1
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨p2VecC s a, ⟨a, rfl⟩, rfl⟩
    · rintro ⟨x, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, rfl⟩
  rw [h1] at hy
  obtain ⟨w, hw, hwy⟩ := Submodule.mem_map.mp hy
  rw [← hwy]
  have hsym : cE6.symm (((cE6 : E6 →ₗ[ℝ] Amb 12)) w) = w :=
    LinearIsometryEquiv.symm_apply_apply (cE6 : E6 ≃ₗᵢ[ℝ] Amb 12) w
  rw [hsym]
  have hle : Submodule.span ℝ (Set.range (p2VecC s)) ≤
      (Submodule.span ℂ ({lamL s, lamR s} : Set E6)).restrictScalars ℝ :=
    Submodule.span_le.mpr (fun z hz => by
      obtain ⟨a, rfl⟩ := hz
      exact p2VecCMemSpan s a)
  exact hle hw

/-- **The `cE6.symm`-image of the chart evaluation of the plane of `p2Map x` lies in the complex
span of `(Λ(s), Λ'(s))`**, where `s` is any chart representative of `x`. -/
theorem cE6SymmEvalChartOMem (S : ChartIdx 4 8) (t : Fin 5)
    (x : Work.Projective.CP 4) (hx : x ∈ Work.Projective.chartSet t)
    (hS : p2Map x ∈ baseSet S) (c : Amb 4) :
    cE6.symm (evalChartO S ⟨p2Map x, hS⟩ c) ∈
      Submodule.span ℂ ({lamL (rep4 t x), lamR (rep4 t x)} : Set E6) := by
  set f : Stiefel 4 8 := p2StiefelF ⟨repF t x, repF_ne_zero t x⟩ with hfdef
  have hmk : (Quotient.mk'' f : OG 4 8) = p2Map x := by
    rw [hfdef]
    change ogMk 4 8 (p2StiefelF ⟨repF t x, repF_ne_zero t x⟩) = p2Map x
    rw [← p2Map_apply ⟨repF t x, repF_ne_zero t x⟩,
      show Projectivization.mk' ℂ ⟨repF t x, repF_ne_zero t x⟩ = x from
        cpMk_repF t x hx]
  have hfmem : f ∈ chartSet S := (mem_baseSet_iff S f).mp (hmk.symm ▸ hS)
  have hfval : (f.1 : Fin 4 → Amb 12) = fun a => cE6 (p2VecC (rep4 t x) a) := by
    rw [hfdef]
    rfl
  have hPt : (⟨p2Map x, hS⟩ : ↥(baseSet S)) =
      ⟨(Quotient.mk'' f), (mem_baseSet_iff S f).mpr hfmem⟩ := Subtype.ext hmk.symm
  refine cE6_symm_mem_span (rep4 t x) ?_
  rw [hPt, evalChartO_spec S f hfmem, coordEval]
  rw [show Submodule.span ℝ (Set.range (fun a : Fin 4 => cE6 (p2VecC (rep4 t x) a)))
      = Submodule.span ℝ (Set.range (f.1 : Fin 4 → Amb 12)) from by rw [hfval]]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (coordVec_mem_span S f i))

/-! ## The real span of the frame is the complex span of `(Λ, Λ')` -/

theorem complex_smul_eq_E6 (μ : ℂ) (u : E6) :
    μ • u = μ.re • u + μ.im • (Complex.I • u) := by
  conv_lhs => rw [← Complex.re_add_im μ]
  rw [add_smul, mul_smul]
  rfl

theorem I_smul_p2VecC_mem (s : E5) (a : Fin 4) :
    Complex.I • p2VecC s a ∈ Submodule.span ℝ (Set.range (p2VecC s)) := by
  obtain ⟨b, rfl⟩ : ∃ b : Fin 2 ⊕ Fin 2, finSumFinEquiv b = a :=
    Equiv.surjective (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4) a
  rcases b with b | b
  · rw [p2VecC, Equiv.symm_apply_apply, p2VecB_inl]
    have hb : b = 0 ∨ b = 1 := by omega
    rcases hb with hb | hb
    · rw [hb, twoE_zero]
      have h : Complex.I • lamUnit s = p2VecC s (p2Idx (Sum.inl 1)) := by
        rw [p2VecC_inl, twoE_one]
      rw [h]
      exact Submodule.subset_span ⟨_, rfl⟩
    · rw [hb, twoE_one, I_smul_I_smul]
      have h : lamUnit s = p2VecC s (p2Idx (Sum.inl 0)) := by
        rw [p2VecC_inl, twoE_zero]
      rw [h]
      exact Submodule.neg_mem _ (Submodule.subset_span ⟨_, rfl⟩)
  · rw [p2VecC, Equiv.symm_apply_apply, p2VecB_inr]
    have hb : b = 0 ∨ b = 1 := by omega
    rcases hb with hb | hb
    · rw [hb, twoE_zero]
      have h : Complex.I • wUnit s = p2VecC s (p2Idx (Sum.inr 1)) := by
        rw [p2VecC_inr, twoE_one]
      rw [h]
      exact Submodule.subset_span ⟨_, rfl⟩
    · rw [hb, twoE_one, I_smul_I_smul]
      have h : wUnit s = p2VecC s (p2Idx (Sum.inr 0)) := by
        rw [p2VecC_inr, twoE_zero]
      rw [h]
      exact Submodule.neg_mem _ (Submodule.subset_span ⟨_, rfl⟩)

theorem I_smul_mem_span_p2VecC (s : E5) {x : E6}
    (hx : x ∈ Submodule.span ℝ (Set.range (p2VecC s))) :
    Complex.I • x ∈ Submodule.span ℝ (Set.range (p2VecC s)) := by
  refine Submodule.span_induction
    (p := fun y _ => Complex.I • y ∈ Submodule.span ℝ (Set.range (p2VecC s)))
    ?_ ?_ ?_ ?_ hx
  · rintro z ⟨a, rfl⟩
    exact I_smul_p2VecC_mem s a
  · rw [smul_zero]
    exact Submodule.zero_mem _
  · intro y z hy hz ihy ihz
    rw [smul_add]
    exact Submodule.add_mem _ ihy ihz
  · intro c y hy ihy
    rw [smul_comm]
    exact Submodule.smul_mem _ c ihy

theorem complex_smul_mem_span_p2VecC (s : E5) (c : ℂ) {x : E6}
    (hx : x ∈ Submodule.span ℝ (Set.range (p2VecC s))) :
    c • x ∈ Submodule.span ℝ (Set.range (p2VecC s)) := by
  have h1 : c.re • x ∈ Submodule.span ℝ (Set.range (p2VecC s)) := Submodule.smul_mem _ _ hx
  have h2 : c.im • (Complex.I • x) ∈ Submodule.span ℝ (Set.range (p2VecC s)) :=
    Submodule.smul_mem _ _ (I_smul_mem_span_p2VecC s hx)
  have hsum := Submodule.add_mem _ h1 h2
  rwa [← complex_smul_eq_E6 c x] at hsum

theorem span_p2VecC_eq_span (s : E5) (hs : s ≠ 0) :
    Submodule.span ℝ (Set.range (p2VecC s))
      = (Submodule.span ℂ ({lamL s, lamR s} : Set E6)).restrictScalars ℝ := by
  have hN : Submodule.span ℂ (Set.range (p2VecC s))
      = Submodule.span ℂ ({lamL s, lamR s} : Set E6) := by
    apply le_antisymm
    · exact Submodule.span_le.mpr (fun z hz => by
        obtain ⟨a, rfl⟩ := hz
        exact p2VecCMemSpan s a)
    · refine Submodule.span_le.mpr ?_
      rintro z (hz : z = lamL s ∨ z = lamR s)
      rcases hz with rfl | rfl
      · have h1 : lamL s = (((‖lamL s‖ : ℝ)) : ℂ) • p2VecC s (p2Idx (Sum.inl 0)) := by
          rw [p2VecC_inl, twoE_zero]
          exact lamL_eq_smul_lamUnit s hs
        rw [h1]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
      · have hw : wVec s = (((‖wVec s‖ : ℝ)) : ℂ) • p2VecC s (p2Idx (Sum.inr 0)) := by
          rw [p2VecC_inr, twoE_zero, wUnit, smul_smul]
          have hne : (((‖wVec s‖ : ℝ)) : ℂ) ≠ 0 := by
            have h : ‖wVec s‖ ≠ 0 := norm_ne_zero_iff.mpr (wVec_ne_zero s hs)
            exact_mod_cast h
          rw [mul_inv_cancel₀ hne, one_smul]
        have h2 : lamR s = wVec s
            + (inner ℂ (lamUnit s) (lamR s)) • p2VecC s (p2Idx (Sum.inl 0)) := by
          rw [p2VecC_inl, twoE_zero, ← sub_eq_iff_eq_add, wVec]
        rw [h2, hw]
        exact Submodule.add_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
  rw [← hN]
  apply le_antisymm
  · exact Submodule.span_le.mpr (fun z hz => by
      obtain ⟨a, rfl⟩ := hz
      exact Submodule.subset_span ⟨a, rfl⟩)
  · intro x hx
    refine Submodule.span_induction
      (p := fun y _ => y ∈ Submodule.span ℝ (Set.range (p2VecC s))) ?_ ?_ ?_ ?_ hx
    · rintro z ⟨a, rfl⟩
      exact Submodule.subset_span ⟨a, rfl⟩
    · exact Submodule.zero_mem _
    · intro y z hy hz ihy ihz
      exact Submodule.add_mem _ ihy ihz
    · intro c y hy ihy
      exact complex_smul_mem_span_p2VecC s c ihy

theorem map_cE6_span_p2VecC (s : E5) :
    Submodule.span ℝ (Set.range (fun a : Fin 4 => cE6 (p2VecC s a)))
      = Submodule.map (cE6 : E6 →ₗ[ℝ] Amb 12)
          (Submodule.span ℝ (Set.range (p2VecC s))) := by
  rw [Submodule.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨p2VecC s a, ⟨a, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, rfl⟩

theorem memPlane_p2Stiefel (s : E5) (hs : s ≠ 0) {v : E6}
    (hv : v ∈ Submodule.span ℂ ({lamL s, lamR s} : Set E6)) :
    memPlane (ogMk 4 8 (p2Stiefel ⟨s, hs⟩)) (cE6 v) := by
  refine ⟨p2Stiefel ⟨s, hs⟩, rfl, ?_⟩
  rw [p2Stiefel_val]
  change cE6 v ∈ Submodule.span ℝ (Set.range (fun a : Fin 4 => cE6 (p2VecC s a)))
  rw [map_cE6_span_p2VecC]
  exact Submodule.mem_map.mpr ⟨v, (span_p2VecC_eq_span s hs).symm ▸ hv, rfl⟩

theorem memPlane_p2Map {t : Fin 5} {x : Work.Projective.CP 4}
    (hx : x ∈ Work.Projective.chartSet t) {v : E6}
    (hv : v ∈ Submodule.span ℂ ({lamL (rep4 t x), lamR (rep4 t x)} : Set E6)) :
    memPlane (p2Map x) (cE6 v) := by
  have hf : p2StiefelF ⟨repF t x, repF_ne_zero t x⟩
      = p2Stiefel ⟨rep4 t x, rep4_ne_zero t x⟩ := Subtype.ext rfl
  have hx' : Projectivization.mk' ℂ ⟨repF t x, repF_ne_zero t x⟩ = x := cpMk_repF t x hx
  have hmk : p2Map x = ogMk 4 8 (p2Stiefel ⟨rep4 t x, rep4_ne_zero t x⟩) := by
    conv_lhs => rw [← hx']
    rw [p2Map_apply, hf]
  rw [hmk]
  exact memPlane_p2Stiefel (rep4 t x) (rep4_ne_zero t x) hv

end

end Work.ThomBordism.Grassmann.P2Base
