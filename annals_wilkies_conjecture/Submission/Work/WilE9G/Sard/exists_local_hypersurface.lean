import Mathlib
import Submission.Work.WilE9G.Sard.Basic

set_option autoImplicit false

namespace Work.WilE9G.Sard

open Filter
open scoped Topology

/-- The function `z ↦ l (D^j f(z) (u₁, …, u_j))` (with `l` a continuous linear functional and
`u` a fixed family of vectors) is analytic wherever `f` is. -/
private theorem analyticOn_iteratedFDeriv_eval' {n m j : ℕ} {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {U : Set (Fin n → ℝ)} (hU : IsOpen U) (hf : AnalyticOn ℝ f U)
    (l : (Fin m → ℝ) →L[ℝ] ℝ) (u : Fin j → (Fin n → ℝ)) :
    AnalyticOn ℝ (fun z => l ((iteratedFDeriv ℝ j f z) u)) U := by
  have hfN : AnalyticOnNhd ℝ f U := (hU.analyticOn_iff_analyticOnNhd).mp hf
  have hderiv : AnalyticOnNhd ℝ (iteratedFDeriv ℝ j f) U :=
    hfN.iteratedFDeriv_of_isOpen hU j
  have hcomp :=
    (l.comp (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Fin n → ℝ) (Fin m → ℝ) u))
      |>.comp_analyticOnNhd hderiv
  have hcomp2 : AnalyticOnNhd ℝ (fun z => l ((iteratedFDeriv ℝ j f z) u)) U := by
    refine hcomp.congr hU ?_
    intro z hz
    rfl
  exact hcomp2.analyticOn

/-- The directional derivative of `z ↦ l (D^j f(z) (u))` in the direction `v` is
`l (D^{j+1} f(z) (v, u₁, …, u_j))`. -/
private theorem fderiv_iteratedFDeriv_eval' {n m j : ℕ} {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {U : Set (Fin n → ℝ)} (hU : IsOpen U) (hf : AnalyticOn ℝ f U) {z : Fin n → ℝ} (hz : z ∈ U)
    (l : (Fin m → ℝ) →L[ℝ] ℝ) (u : Fin j → (Fin n → ℝ)) (v : Fin n → ℝ) :
    (fderiv ℝ (fun z => l ((iteratedFDeriv ℝ j f z) u)) z) v
      = l ((iteratedFDeriv ℝ (j+1) f z) (Fin.cons v u)) := by
  have hfN : AnalyticOnNhd ℝ f U := (hU.analyticOn_iff_analyticOnNhd).mp hf
  have hAN : AnalyticOnNhd ℝ (iteratedFDeriv ℝ j f) U := hfN.iteratedFDeriv_of_isOpen hU j
  have hAd : DifferentiableAt ℝ (iteratedFDeriv ℝ j f) z := (hAN z hz).differentiableAt
  have h1 : HasFDerivAt (fun y => (iteratedFDeriv ℝ j f y) u)
      ((fderiv ℝ (iteratedFDeriv ℝ j f) z).flipMultilinear u) z :=
    hAd.hasFDerivAt.continuousMultilinear_apply_const u
  have h2 : HasFDerivAt (fun y => l ((iteratedFDeriv ℝ j f y) u))
      (l.comp ((fderiv ℝ (iteratedFDeriv ℝ j f) z).flipMultilinear u)) z :=
    HasFDerivAt.comp z (ContinuousLinearMap.hasFDerivAt l) h1
  rw [h2.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flipMultilinear_apply_apply,
    iteratedFDeriv_succ_apply_left, Fin.cons_zero, Fin.tail_cons]

/-- **Local hypersurface stratification of the flat locus.**  Let `f` be analytic on the open set
`U` and let `z ∈ U` with `Df z = 0` while some iterated derivative of `f` at `z` does not vanish.
Then there is an order `j ≥ 1` at which the vanishing stops (all derivatives of order `≤ j` vanish
at `z`), and a single analytic function `h` on an open neighbourhood `B` of `z` such that
`∇h ≠ 0` on `B`, `h z = 0`, and `h` vanishes on the locus where all derivatives up to order `j`
vanish.  Here `h` is a directional derivative of order `j` of `f`, so it is *identically* zero on
that locus; no claim is made that the locus is a smooth hypersurface. -/
theorem exists_local_hypersurface {n m : ℕ} {f : (Fin n → ℝ) → (Fin m → ℝ)} {U : Set (Fin n → ℝ)}
    (hU : IsOpen U) (hf : AnalyticOn ℝ f U) {z : Fin n → ℝ} (hz : z ∈ U)
    (h0 : fderiv ℝ f z = 0)
    (hnot : ¬ (∀ i, 1 ≤ i → iteratedFDeriv ℝ i f z = 0)) :
    ∃ (j : ℕ) (h : (Fin n → ℝ) → ℝ) (B : Set (Fin n → ℝ)),
      1 ≤ j ∧ IsOpen B ∧ z ∈ B ∧ B ⊆ U ∧ AnalyticOn ℝ h B ∧ h z = 0 ∧
      (∀ w ∈ B, fderiv ℝ h w ≠ 0) ∧
      (∀ w ∈ B, (∀ i, 1 ≤ i → i ≤ j → iteratedFDeriv ℝ i f w = 0) → h w = 0) ∧
      (∀ i, 1 ≤ i → i ≤ j → iteratedFDeriv ℝ i f z = 0) := by
  classical
  -- the first derivative vanishes at `z`
  have hone : iteratedFDeriv ℝ 1 f z = 0 := by
    ext w
    rw [iteratedFDeriv_one_apply]
    simp [h0]
  -- some order has a non-vanishing derivative at `z`
  have hmem : ∃ i : ℕ, 1 ≤ i ∧ iteratedFDeriv ℝ i f z ≠ 0 := by
    by_contra hcon
    exact hnot fun i hi => by
      by_contra hne
      exact hcon ⟨i, hi, hne⟩
  -- the minimal such order `J`, all smaller positive orders vanishing
  obtain ⟨J, hJ1, hJne, hJmin⟩ :
      ∃ J : ℕ, 1 ≤ J ∧ iteratedFDeriv ℝ J f z ≠ 0 ∧
        ∀ i, 1 ≤ i → i < J → iteratedFDeriv ℝ i f z = 0 := by
    refine ⟨Nat.find hmem, (Nat.find_spec hmem).1, (Nat.find_spec hmem).2, ?_⟩
    intro i hi1 hiJ
    by_contra hne
    have := Nat.find_min' hmem ⟨hi1, hne⟩
    omega
  have hJne1 : J ≠ 1 := by
    intro hJ
    refine hJne ?_
    rw [hJ]
    exact hone
  have hJ2 : 2 ≤ J := by omega
  -- write `J = k + 1`
  obtain ⟨k, rfl⟩ : ∃ k, J = k + 1 := ⟨J - 1, (Nat.sub_add_cancel hJ1).symm⟩
  have hk1 : 1 ≤ k := by omega
  -- extract a non-zero value of `D^{k+1} f z`
  have hm : ∃ mm : Fin (k+1) → (Fin n → ℝ), (iteratedFDeriv ℝ (k+1) f z) mm ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hJne (ContinuousMultilinearMap.ext hcon)
  obtain ⟨mm, hmne⟩ := hm
  -- and a coordinate in which that value is non-zero
  obtain ⟨kk, hkk⟩ : ∃ kk : Fin m, ((iteratedFDeriv ℝ (k+1) f z) mm) kk ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hmne (funext hcon)
  set l : (Fin m → ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) kk with hl
  -- the candidate hypersurface function: the `k`-th directional derivative along `tail mm`
  have hana : AnalyticOn ℝ (fun w => l ((iteratedFDeriv ℝ k f w) (Fin.tail mm))) U :=
    analyticOn_iteratedFDeriv_eval' hU hf l (Fin.tail mm)
  have hN : AnalyticOnNhd ℝ (fun w => l ((iteratedFDeriv ℝ k f w) (Fin.tail mm))) U :=
    (hU.analyticOn_iff_analyticOnNhd).mp hana
  have hcont : ContinuousAt
      (fun w => fderiv ℝ (fun w => l ((iteratedFDeriv ℝ k f w) (Fin.tail mm))) w) z :=
    (hN.fderiv_of_isOpen hU).continuousOn.continuousAt (hU.mem_nhds hz)
  -- it vanishes at `z`
  have hzvan : iteratedFDeriv ℝ k f z = 0 := hJmin k hk1 (Nat.lt_succ_self k)
  have hz0 : (fun w => l ((iteratedFDeriv ℝ k f w) (Fin.tail mm))) z = 0 := by
    simp [hzvan]
  -- its gradient at `z` does not vanish
  have hfdval : (fderiv ℝ (fun w => l ((iteratedFDeriv ℝ k f w) (Fin.tail mm))) z) (mm 0)
      = l ((iteratedFDeriv ℝ (k+1) f z) mm) := by
    rw [fderiv_iteratedFDeriv_eval' hU hf hz l (Fin.tail mm) (mm 0), Fin.cons_self_tail]
  have hlne : l ((iteratedFDeriv ℝ (k+1) f z) mm) ≠ 0 := by
    rw [hl, ContinuousLinearMap.proj_apply]
    exact hkk
  have hfdne : fderiv ℝ (fun w => l ((iteratedFDeriv ℝ k f w) (Fin.tail mm))) z ≠ 0 := by
    intro hzero
    exact hlne (by simpa [hzero] using hfdval.symm)
  have hmem_nhds : ({0}ᶜ : Set ((Fin n → ℝ) →L[ℝ] ℝ)) ∈
      𝓝 (fderiv ℝ (fun w => l ((iteratedFDeriv ℝ k f w) (Fin.tail mm))) z) :=
    isOpen_compl_singleton.mem_nhds (by simpa using hfdne)
  -- an open ball on which the gradient stays non-zero and which is contained in `U`
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (hcont.preimage_mem_nhds hmem_nhds) (hU.mem_nhds hz))
  refine ⟨k, (fun w => l ((iteratedFDeriv ℝ k f w) (Fin.tail mm))), Metric.ball z ε,
    hk1, Metric.isOpen_ball, Metric.mem_ball_self hε, ?_, ?_, hz0, ?_, ?_, ?_⟩
  · exact fun w hw => (hball hw).2
  · exact hana.mono fun w hw => (hball hw).2
  · exact fun w hw => (hball hw).1
  · intro w hw hvan
    have hzw : iteratedFDeriv ℝ k f w = 0 := hvan k hk1 le_rfl
    simp [hzw]
  · exact fun i hi1 hik => hJmin i hi1 (Nat.lt_succ_of_le hik)

end Work.WilE9G.Sard
