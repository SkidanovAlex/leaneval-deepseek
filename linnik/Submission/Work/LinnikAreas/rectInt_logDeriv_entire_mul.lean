import Mathlib
import Submission.Work.LinnikAreas.ZetaTentPrelude
import Submission.Commons.Analysis.Complex.divisor_subBall_factor
import Submission.Work.LinnikAreas.logDeriv_finprod_zpow
import Submission.Work.LinnikAreas.rectInt_finset_inv_sub_mul_entire

open Complex MeasureTheory intervalIntegral Filter
open scoped Real Topology BigOperators

namespace Work.LinnikAreas

open Commons.NumberTheory.DirichletCharacter

noncomputable section

/-!
# The argument principle on a rectangle for an entire function and an entire kernel

For `f` and `G` entire with `f` not identically zero and `f` zero-free on the boundary of the
axis-parallel rectangle with corners `z, w`,

  `∮_{∂R} logDeriv f · G = 2πi · Σ_{ρ ∈ R} ord_ρ(f) · G(ρ)`,

the sum running over the zeros of `f` strictly inside the rectangle, weighted by their order.

The proof factors `f = P · g` on `ℂ`, where `P z = ∏ᶠ u, (z - u) ^ d u` is built from the divisor
`d` of `f` on the closed rectangle and `g` is entire and zero-free on the rectangle; on the
boundary `logDeriv f = (Σᶠ u, d u · (s-u)⁻¹) + logDeriv g`, and Cauchy-Goursat kills the second
term while the first is evaluated by residues.
-/

theorem rectInt_logDeriv_entire_mul {f G : ℂ → ℂ} (hf : Differentiable ℂ f) (hG : Differentiable ℂ G)
    (hf0 : ∃ x : ℂ, f x ≠ 0) {z w : ℂ} (hzre : z.re < w.re) (hzim : z.im < w.im)
    (hnz : ∀ s ∈ Commons.NumberTheory.DirichletCharacter.rectBoundary z w, f s ≠ 0) :
    Commons.NumberTheory.DirichletCharacter.rectInt z w (fun s => logDeriv f s * G s) =
      (2 * (Real.pi : ℂ) * Complex.I) *
        ∑ᶠ ρ : ℂ, (if z.re < ρ.re ∧ ρ.re < w.re ∧ z.im < ρ.im ∧ ρ.im < w.im
          then ((analyticOrderNatAt f ρ : ℕ) : ℂ) * G ρ else 0) := by
  classical
  set V : Set ℂ := rectSet z w with hV
  have hVc : IsCompact V := by
    rw [hV]
    exact (isCompact_uIcc (a := z.re) (b := w.re)).reProdIm
      (isCompact_uIcc (a := z.im) (b := w.im))
  have hf_an : AnalyticOnNhd ℂ f Set.univ := fun x _ => hf.analyticAt x
  have htop : ∀ x : ℂ, meromorphicOrderAt f x ≠ ⊤ := by
    obtain ⟨x, hx⟩ := hf0
    have hx' : meromorphicOrderAt f x ≠ ⊤ :=
      Commons.Analysis.Complex.meromorphicOrderAt_ne_top_of_analytic_ne_zero (hf.analyticAt x) hx
    have h := (MeromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall (f := f) (U := Set.univ)
      hf_an.meromorphicOn isConnected_univ).mp ⟨⟨x, trivial⟩, hx'⟩
    intro y
    exact h ⟨y, trivial⟩
  have hfin : (MeromorphicOn.divisor f V).support.Finite :=
    (MeromorphicOn.divisor f V).finiteSupport hVc
  obtain ⟨g, hg_an, hg_nz, hg_eq⟩ :=
    Commons.Analysis.Complex.factor_subBall_divisor (U := Set.univ) (V := V) (Set.subset_univ V)
      hf_an.meromorphicOn (fun x _ => htop x) hf_an hfin
  let d : ℂ → ℤ := fun u => MeromorphicOn.divisor f V u
  have hd_fin : d.HasFiniteSupport := by
    simpa only [d, Function.HasFiniteSupport] using hfin
  have hd_nonneg : ∀ u : ℂ, 0 ≤ d u := by
    intro u
    exact (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (f := f) (U := V)
        (fun x _ => hf.analyticAt x)) u
  let P : ℂ → ℂ := fun y => ∏ᶠ u : ℂ, (y - u) ^ d u
  have hPfun : P = (∏ᶠ u : ℂ, (· - u) ^ d u) := by
    rw [show P = (fun y : ℂ => ∏ᶠ u : ℂ, (y - u) ^ d u) from rfl,
      Function.FactorizedRational.finprod_eq_fun hd_fin]
  have hP_an : AnalyticOnNhd ℂ P Set.univ := by
    intro y _
    rw [hPfun]
    exact Function.FactorizedRational.analyticAt (d := d) (hd_nonneg y)
  have hfg : f = fun y => P y * g y := by
    funext y
    simpa only [P, d] using hg_eq y trivial
  have hfl : (Function.support d).Finite := hd_fin
  let S : Finset ℂ := hfl.toFinset
  have hS_mem : ∀ u : ℂ, u ∈ S ↔ d u ≠ 0 := by
    intro u
    show u ∈ hfl.toFinset ↔ d u ≠ 0
    rw [Set.Finite.mem_toFinset, Function.mem_support]
  have hz_zero : ∀ u : ℂ, u ∈ S → f u = 0 := by
    intro u hu
    have hdu : d u ≠ 0 := (hS_mem u).mp hu
    have hsupp : u ∈ Function.support d := by rwa [Function.mem_support]
    have huV : u ∈ V := (MeromorphicOn.divisor f V).supportWithinDomain hsupp
    have hord : d u = (analyticOrderNatAt f u : ℤ) :=
      Commons.NumberTheory.DirichletCharacter.divisor_eq_analyticOrderNatAt (U := V)
        (fun x _ => hf.analyticAt x) huV
    have hnat : analyticOrderNatAt f u ≠ 0 := by
      intro h0
      refine hdu ?_
      rw [hord, h0]
      norm_num
    exact apply_eq_zero_of_analyticOrderNatAt_ne_zero hnat
  have hds_of_boundary : ∀ s ∈ rectBoundary z w, d s = 0 := by
    intro s hs
    by_contra h
    exact hnz s hs (hz_zero s ((hS_mem s).mpr h))
  have hlogdec : ∀ s ∈ rectBoundary z w,
      logDeriv f s = (∑ᶠ u : ℂ, (d u : ℂ) * (s - u)⁻¹) + logDeriv g s := by
    intro s hs
    have hsV : s ∈ V := by
      rw [hV]; exact rectBoundary_subset_rectSet hzre hzim hs
    have hds : d s = 0 := hds_of_boundary s hs
    have hPs : P s ≠ 0 := by
      rw [hPfun]
      exact Function.FactorizedRational.ne_zero (d := d) hds
    have hgs : g s ≠ 0 := hg_nz s hsV
    have hPd : DifferentiableAt ℂ P s := (hP_an s trivial).differentiableAt
    have hgd : DifferentiableAt ℂ g s := (hg_an s trivial).differentiableAt
    calc logDeriv f s = logDeriv (fun y => P y * g y) s := by rw [hfg]
      _ = logDeriv P s + logDeriv g s := logDeriv_mul s hPs hgs hPd hgd
      _ = (∑ᶠ u : ℂ, (d u : ℂ) * (s - u)⁻¹) + logDeriv g s := by
            rw [logDeriv_finprod_zpow (d := d) hd_fin hds]
  let A : ℂ → ℂ := fun s => (∑ᶠ u : ℂ, (d u : ℂ) * (s - u)⁻¹) * G s
  let B : ℂ → ℂ := fun s => logDeriv g s * G s
  have hA_eq : A = fun s => (∑ u ∈ S, (d u : ℂ) * (s - u)⁻¹) * G s := by
    funext s
    show (∑ᶠ u : ℂ, (d u : ℂ) * (s - u)⁻¹) * G s =
      (∑ u ∈ S, (d u : ℂ) * (s - u)⁻¹) * G s
    rw [finsum_eq_sum_of_support_subset (s := S)
      (f := fun u : ℂ => (d u : ℂ) * (s - u)⁻¹)]
    intro u hu
    by_contra huS
    have hd0 : d u = 0 := by
      by_contra hne
      exact huS ((hS_mem u).mpr hne)
    exact hu (by simp [hd0])
  have hA_cont : ∀ s ∈ rectBoundary z w, ContinuousAt A s := by
    intro s hs
    rw [hA_eq]
    refine ContinuousAt.mul ?_ (hG s).continuousAt
    refine tendsto_finsetSum S ?_
    intro u hu
    have hsu : s - u ≠ 0 := by
      rintro h0
      exact hnz s hs (by rw [sub_eq_zero.mp h0]; exact hz_zero u hu)
    exact ContinuousAt.mul continuousAt_const
      (ContinuousAt.inv₀ (f := fun x : ℂ => x - u) (by fun_prop) hsu)
  have hB_cont : ∀ s ∈ rectBoundary z w, ContinuousAt B s := by
    intro s hs
    have hsV : s ∈ V := by rw [hV]; exact rectBoundary_subset_rectSet hzre hzim hs
    have hgs : g s ≠ 0 := hg_nz s hsV
    have hlog : ContinuousAt (fun y : ℂ => logDeriv g y) s := by
      rw [show (fun y : ℂ => logDeriv g y) = fun y : ℂ => deriv g y / g y from
        funext fun y => logDeriv_apply g y]
      exact ((hg_an s trivial).deriv.continuousAt).div (hg_an s trivial).continuousAt hgs
    exact hlog.mul (hG s).continuousAt
  have hdec : ∀ s ∈ rectBoundary z w, logDeriv f s * G s = A s + B s := by
    intro s hs
    show logDeriv f s * G s =
      (∑ᶠ u : ℂ, (d u : ℂ) * (s - u)⁻¹) * G s + logDeriv g s * G s
    rw [hlogdec s hs, add_mul]
  obtain ⟨a1, a2, a3, a4⟩ := intervalIntegrable_of_boundary_continuousAt hA_cont
  obtain ⟨b1, b2, b3, b4⟩ := intervalIntegrable_of_boundary_continuousAt hB_cont
  have hsplit : rectInt z w (fun s => A s + B s) = rectInt z w A + rectInt z w B :=
    rectInt_add'' a1 b1 a2 b2 a3 b3 a4 b4
  have hB0 : rectInt z w B = 0 := by
    apply rectInt_eq_zero_of_differentiableOn
    intro s hsV
    have hgs : g s ≠ 0 := hg_nz s hsV
    have hlog : AnalyticAt ℂ (fun y : ℂ => logDeriv g y) s := by
      rw [show (fun y : ℂ => logDeriv g y) = fun y : ℂ => deriv g y / g y from
        funext fun y => logDeriv_apply g y]
      exact ((hg_an s trivial).deriv).div (hg_an s trivial) hgs
    exact ((hlog.mul (hG.analyticAt s)).differentiableAt).differentiableWithinAt
  have hS_nb : ∀ u ∈ S, u ∉ rectBoundary z w := by
    intro u hu
    exact fun h => hnz u h (hz_zero u hu)
  have hA_val : rectInt z w A =
      ∑ u ∈ S, (d u : ℂ) * (if z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im
        then G u * (2 * (Real.pi : ℂ) * Complex.I) else 0) := by
    rw [hA_eq]
    exact rectInt_finset_inv_sub_mul_entire hG hzre hzim S (fun u => (d u : ℂ)) hS_nb
  have hmain : rectInt z w (fun s => logDeriv f s * G s) =
      ∑ u ∈ S, (d u : ℂ) * (if z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im
        then G u * (2 * (Real.pi : ℂ) * Complex.I) else 0) := by
    rw [rectInt_congr_boundary' hdec, hsplit, hA_val, hB0, add_zero]
  have e1 : (∑ u ∈ S, (d u : ℂ) * (if z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im
        then G u * (2 * (Real.pi : ℂ) * Complex.I) else 0)) =
      (2 * (Real.pi : ℂ) * Complex.I) *
        (∑ u ∈ S, (if z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im
          then (d u : ℂ) * G u else 0)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    by_cases h : z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h]; ring
  have e2 : (∑ u ∈ S, (if z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im
          then (d u : ℂ) * G u else 0)) =
      ∑ᶠ ρ : ℂ, (if z.re < ρ.re ∧ ρ.re < w.re ∧ z.im < ρ.im ∧ ρ.im < w.im
        then (d ρ : ℂ) * G ρ else 0) := by
    refine (finsum_eq_sum_of_support_subset (s := S)
      (f := fun ρ : ℂ => if z.re < ρ.re ∧ ρ.re < w.re ∧ z.im < ρ.im ∧ ρ.im < w.im
        then (d ρ : ℂ) * G ρ else 0) ?_).symm
    intro ρ hρ
    by_contra hS
    have hd0 : d ρ = 0 := by
      by_contra hne
      exact hS ((hS_mem ρ).mpr hne)
    exact hρ (by simp [hd0])
  have e3 : (∑ᶠ ρ : ℂ, (if z.re < ρ.re ∧ ρ.re < w.re ∧ z.im < ρ.im ∧ ρ.im < w.im
        then (d ρ : ℂ) * G ρ else 0)) =
      ∑ᶠ ρ : ℂ, (if z.re < ρ.re ∧ ρ.re < w.re ∧ z.im < ρ.im ∧ ρ.im < w.im
        then ((analyticOrderNatAt f ρ : ℕ) : ℂ) * G ρ else 0) := by
    apply finsum_congr
    intro ρ
    by_cases h : z.re < ρ.re ∧ ρ.re < w.re ∧ z.im < ρ.im ∧ ρ.im < w.im
    · rw [if_pos h, if_pos h]
      have hρV : ρ ∈ V := by
        rw [hV]
        refine mem_rectSet ?_ ?_
        · rw [Set.uIcc_of_le hzre.le]; exact ⟨le_of_lt h.1, le_of_lt h.2.1⟩
        · rw [Set.uIcc_of_le hzim.le]; exact ⟨le_of_lt h.2.2.1, le_of_lt h.2.2.2⟩
      have hord : d ρ = (analyticOrderNatAt f ρ : ℤ) :=
        Commons.NumberTheory.DirichletCharacter.divisor_eq_analyticOrderNatAt (U := V)
          (fun x _ => hf.analyticAt x) hρV
      rw [hord]
      norm_num
    · rw [if_neg h, if_neg h]
  rw [hmain, e1, e2, e3]

end

end Work.LinnikAreas
