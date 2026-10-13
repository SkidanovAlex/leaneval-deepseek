import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE5.Basic
import Submission.Work.WilE9.Ift.AppendCLM
import Submission.Work.WilE5.Strat.flatConormalTools
import Submission.Work.WilE7.Auxiliary.fibreFDeriv
import Submission.Work.WilE7.Auxiliary.rangePiEqTopOfRank
import Submission.Work.WilE7.Auxiliary.levelSetEqNearOfKerLe

open Classical Filter
open scoped Topology

namespace Work.WilE7.Auxiliary

/-! ## Helpers for the fibre level-set comparison

The proof compares the two fibre level sets over the base point
`projFirst p q z` of the systems `c'` (with polynomials `h'`) and `c` (with polynomials `h`).
The two maps `G y = (eaEval c' (h' b) (projFirst, y))_b` and
`F y = (eaEval c (h a) (projFirst, y))_a` are analytic on the fibre, `hz` makes `G`
vanish at `projSnd p q z`, `hrank`/`hrank'` make their differentials surjective
(`fibreFDeriv` + `rangePiEqTopOfRank`), `hker` says the kernel of `DG` is contained in
the kernel of `DF`, and then the chart lemma `levelSetEqNearOfKerLeGeneral` upgrades the
one-sided vanishing `hvan` to an equivalence of level sets.

`hgp` for `F` is *not* assumed: this is handled by a case split on whether `F` vanishes at
the base point.  If it does, the chart lemma applies; if not, both level sets are
eventually empty (so the iff holds vacuously), `F` being continuous. -/

/-- `Fin.append (projFirst p q z) (projSnd p q z) = z`. -/
private lemma appendPP {p q : ℕ} (z : Fin (p + q) → ℝ) :
    Fin.append (WilkiesDesign.E.projFirst p q z) (WilkiesDesign.E.projSnd p q z) = z := by
  funext i
  refine Fin.addCases (fun i' => ?_) (fun l => ?_) i
  · simp [WilkiesDesign.E.projFirst, Fin.append_left]
  · simp [WilkiesDesign.E.projSnd, Fin.append_right]

/-- The fibre restriction `y' ↦ eaEval c Q (Fin.append x y')` of an EA polynomial is analytic. -/
private lemma analyticAt_fibreEval {p q r : ℕ} (c : WilkiesDesign.E.EAChain (p + q) r)
    (Q : WilkiesDesign.E.EAPoly (p + q) r) (x : Fin p → ℝ) (y : Fin q → ℝ) :
    AnalyticAt ℝ (fun y' : Fin q → ℝ => WilkiesDesign.E.eaEval c Q (Fin.append x y')) y := by
  have h1 : AnalyticAt ℝ (fun y' : Fin q → ℝ => (x, y')) y :=
    analyticAt_const.prod analyticAt_id
  have h2 : AnalyticAt ℝ (fun w : (Fin p → ℝ) × (Fin q → ℝ) =>
      (Work.WilE9.Ift.appendCLM p q) w) (x, y) :=
    (Work.WilE9.Ift.appendCLM p q).analyticAt (x, y)
  have h2' : AnalyticAt ℝ (fun y' : Fin q → ℝ => Fin.append x y') y := by
    have h := h2.comp h1
    simpa [Function.comp_def, Work.WilE9.Ift.appendCLM_apply] using h
  have h3 : AnalyticAt ℝ (fun w : Fin (p + q) → ℝ => WilkiesDesign.E.eaEval c Q w)
      (Fin.append x y) := Work.WilE5.Strat.analyticAt_eaEval c Q (Fin.append x y)
  exact h3.comp h2'

/-- The value at `b` of `v ↦ ∑ l, A b l • proj l`, read through the linear-map coercion (the
form in which it appears after rewriting `fderiv` by `fibreFDeriv`). -/
private lemma piCLM_coe_apply {m q : ℕ} (A : Fin m → Fin q → ℝ) (v : Fin q → ℝ) (b : Fin m) :
    (((ContinuousLinearMap.pi (fun b : Fin m => ∑ l : Fin q, A b l •
        (ContinuousLinearMap.proj l : (Fin q → ℝ) →L[ℝ] ℝ))) : (Fin q → ℝ) →ₗ[ℝ] (Fin m → ℝ)) v) b
      = ∑ l, A b l * v l := by
  show ((ContinuousLinearMap.pi (fun b : Fin m => ∑ l : Fin q, A b l •
        (ContinuousLinearMap.proj l : (Fin q → ℝ) →L[ℝ] ℝ))) v) b = ∑ l, A b l * v l
  rw [ContinuousLinearMap.pi_apply]
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]

theorem fibreLevelSetEq {p q : ℕ} {j j' r r' : ℕ} (c : WilkiesDesign.E.EAChain (p + q) r)
    (c' : WilkiesDesign.E.EAChain (p + q) r') (h : Fin j → WilkiesDesign.E.EAPoly (p + q) r)
    (h' : Fin j' → WilkiesDesign.E.EAPoly (p + q) r') (l : Fin q) (z : Fin (p + q) → ℝ)
    (heq : j = j')
    (hz : ∀ b, WilkiesDesign.E.eaEval c' (h' b) z = 0)
    (hrank : (Matrix.of fun (a : Fin j) (l' : Fin q) =>
        WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c (Work.WilE5.yDir p l') (h a)) z).rank = j)
    (hrank' : (Matrix.of fun (b : Fin j') (l' : Fin q) =>
        WilkiesDesign.E.eaEval c' (WilkiesDesign.E.eaD c' (Work.WilE5.yDir p l') (h' b)) z).rank = j')
    (hker : ∀ v : Fin q → ℝ,
      (∀ b, ∑ l', WilkiesDesign.E.eaEval c' (WilkiesDesign.E.eaD c' (Work.WilE5.yDir p l') (h' b)) z * v l' = 0) →
      (∀ a, ∑ l', WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c (Work.WilE5.yDir p l') (h a)) z * v l' = 0))
    (hvan : ∀ᶠ y in nhds (WilkiesDesign.E.projSnd p q z),
      (∀ b, WilkiesDesign.E.eaEval c' (h' b) (Fin.append (WilkiesDesign.E.projFirst p q z) y) = 0) →
      (∀ a, WilkiesDesign.E.eaEval c (h a) (Fin.append (WilkiesDesign.E.projFirst p q z) y) = 0)) :
    ∀ᶠ y in nhds (WilkiesDesign.E.projSnd p q z),
      ((∀ b, WilkiesDesign.E.eaEval c' (h' b) (Fin.append (WilkiesDesign.E.projFirst p q z) y) = 0) ↔
       (∀ a, WilkiesDesign.E.eaEval c (h a) (Fin.append (WilkiesDesign.E.projFirst p q z) y) = 0)) := by
  classical
  set G : (Fin q → ℝ) → (Fin j' → ℝ) := fun y b =>
    WilkiesDesign.E.eaEval c' (h' b) (Fin.append (WilkiesDesign.E.projFirst p q z) y) with hG
  set F : (Fin q → ℝ) → (Fin j → ℝ) := fun y a =>
    WilkiesDesign.E.eaEval c (h a) (Fin.append (WilkiesDesign.E.projFirst p q z) y) with hF
  set A' : Fin j' → Fin q → ℝ := fun b l' =>
    WilkiesDesign.E.eaEval c' (WilkiesDesign.E.eaD c' (Work.WilE5.yDir p l') (h' b)) z with hA'
  set A : Fin j → Fin q → ℝ := fun a l' =>
    WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c (Work.WilE5.yDir p l') (h a)) z with hA
  have hGderiv : fderiv ℝ G (WilkiesDesign.E.projSnd p q z) =
      ContinuousLinearMap.pi (fun b : Fin j' => ∑ l' : Fin q, A' b l' •
          (ContinuousLinearMap.proj l' : (Fin q → ℝ) →L[ℝ] ℝ)) := by
    rw [hG]
    exact Work.WilE7.Aux.fibreFDeriv c' h' z
  have hFderiv : fderiv ℝ F (WilkiesDesign.E.projSnd p q z) =
      ContinuousLinearMap.pi (fun a : Fin j => ∑ l' : Fin q, A a l' •
          (ContinuousLinearMap.proj l' : (Fin q → ℝ) →L[ℝ] ℝ)) := by
    rw [hF]
    exact Work.WilE7.Aux.fibreFDeriv c h z
  have hGan : ∀ y, AnalyticAt ℝ G y := by
    intro y
    rw [hG]
    exact AnalyticAt.pi (fun b => analyticAt_fibreEval c' (h' b) (WilkiesDesign.E.projFirst p q z) y)
  have hFan : ∀ y, AnalyticAt ℝ F y := by
    intro y
    rw [hF]
    exact AnalyticAt.pi (fun a => analyticAt_fibreEval c (h a) (WilkiesDesign.E.projFirst p q z) y)
  have hsurjG : (fderiv ℝ G (WilkiesDesign.E.projSnd p q z)).range = ⊤ := by
    have h := Work.WilE7.Aux.rangePiEqTopOfRank A' hrank'
    rw [← hGderiv] at h
    exact h
  have hsurjF : (fderiv ℝ F (WilkiesDesign.E.projSnd p q z)).range = ⊤ := by
    have h := Work.WilE7.Aux.rangePiEqTopOfRank A hrank
    rw [← hFderiv] at h
    exact h
  have hkerGF : (fderiv ℝ G (WilkiesDesign.E.projSnd p q z)).ker ≤
      (fderiv ℝ F (WilkiesDesign.E.projSnd p q z)).ker := by
    intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    have hvb : ∀ b, ∑ l', A' b l' * v l' = 0 := by
      intro b
      have hb : ((↑(fderiv ℝ G (WilkiesDesign.E.projSnd p q z))
          : (Fin q → ℝ) →ₗ[ℝ] (Fin j' → ℝ)) v) b = 0 := by
        simpa only [Pi.zero_apply] using congrFun hv b
      rw [hGderiv] at hb
      rw [piCLM_coe_apply] at hb
      simpa using hb
    have hva := hker v hvb
    have h3 : (↑(fderiv ℝ F (WilkiesDesign.E.projSnd p q z))
        : (Fin q → ℝ) →ₗ[ℝ] (Fin j → ℝ)) v = 0 := by
      rw [hFderiv]
      funext a
      rw [piCLM_coe_apply]
      simpa using hva a
    exact h3
  have hdim : Module.finrank ℝ (fderiv ℝ G (WilkiesDesign.E.projSnd p q z)).ker =
      Module.finrank ℝ (fderiv ℝ F (WilkiesDesign.E.projSnd p q z)).ker := by
    have h1 := LinearMap.finrank_range_add_finrank_ker
      ((fderiv ℝ G (WilkiesDesign.E.projSnd p q z)) : (Fin q → ℝ) →ₗ[ℝ] (Fin j' → ℝ))
    have h2 := LinearMap.finrank_range_add_finrank_ker
      ((fderiv ℝ F (WilkiesDesign.E.projSnd p q z)) : (Fin q → ℝ) →ₗ[ℝ] (Fin j → ℝ))
    rw [hsurjG, finrank_top] at h1
    rw [hsurjF, finrank_top] at h2
    simp only [Module.finrank_fin_fun ℝ] at h1 h2
    omega
  have hG0 : G (WilkiesDesign.E.projSnd p q z) = 0 := by
    funext b
    simp only [hG, appendPP]
    exact hz b
  have hvan' : ∀ᶠ y in nhds (WilkiesDesign.E.projSnd p q z), G y = 0 → F y = 0 := by
    filter_upwards [hvan] with y hy hGy
    have h1 : ∀ b, WilkiesDesign.E.eaEval c' (h' b)
        (Fin.append (WilkiesDesign.E.projFirst p q z) y) = 0 := by
      intro b
      simpa only [hG, Pi.zero_apply] using congrFun hGy b
    funext a
    simpa only [hF, Pi.zero_apply] using hy h1 a
  have hgoal : ∀ᶠ y in nhds (WilkiesDesign.E.projSnd p q z), (G y = 0 ↔ F y = 0) := by
    by_cases hF0 : F (WilkiesDesign.E.projSnd p q z) = 0
    · exact Work.WilE7.Aux.levelSetEqNearOfKerLeGeneral G F (WilkiesDesign.E.projSnd p q z)
        hGan hFan hG0 hF0 hsurjG hsurjF hkerGF hdim hvan'
    · have hFcont : ContinuousAt F (WilkiesDesign.E.projSnd p q z) := (hFan _).continuousAt
      have hFne : ∀ᶠ y in nhds (WilkiesDesign.E.projSnd p q z), F y ≠ 0 :=
        hFcont.eventually_ne hF0
      filter_upwards [hvan', hFne] with y hv hne
      exact ⟨fun h => absurd (hv h) hne, fun h => absurd h hne⟩
  filter_upwards [hgoal] with y hy
  simpa only [hG, hF, Pi.zero_apply, funext_iff] using hy

end Work.WilE7.Auxiliary
