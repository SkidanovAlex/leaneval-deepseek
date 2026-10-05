import Mathlib
import Submission.Work.RPA3.A3Defs
import Submission.Work.RPA3.TubularDefs
import Submission.Work.RPA3.Symp
import Submission.Work.RPA3.theta_std
import Submission.Work.RPA3.theta_per
import Submission.Work.RPA3.contDiff_thetaP
import Submission.Work.RPA3.exists_local_chart
import Submission.Work.RPA3.TubularHDefs
import Submission.Work.RPA3.H0_slab
import Submission.Work.RPA3.hamVF_lipschitz_bounded
import Submission.Work.RPA3.closure_theta_smallStrip_Icc

open scoped Topology

namespace Work.RPA3

/-! ## The time cut-off `χ_τ` -/

/-- The cut-off in the time variable: `1` on `[0,1]` and `0` outside `(-1/2, 3/2)`. -/
noncomputable def cutTau (t : ℝ) : ℝ :=
  Real.smoothTransition (2 * t + 1) * Real.smoothTransition (3 - 2 * t)

theorem cutTau_contDiff (n : ℕ) : ContDiff ℝ n cutTau := by
  unfold cutTau
  exact (Real.smoothTransition.contDiff.comp (by fun_prop)).mul
    (Real.smoothTransition.contDiff.comp (by fun_prop))

theorem cutTau_one {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : cutTau t = 1 := by
  unfold cutTau
  rw [Real.smoothTransition.one_of_one_le (show (1 : ℝ) ≤ 2 * t + 1 by linarith),
    Real.smoothTransition.one_of_one_le (show (1 : ℝ) ≤ 3 - 2 * t by linarith), mul_one]

theorem cutTau_zero_of_le {t : ℝ} (h : t ≤ -1 / 2) : cutTau t = 0 := by
  unfold cutTau
  rw [Real.smoothTransition.zero_of_nonpos (show 2 * t + 1 ≤ 0 by linarith), zero_mul]

theorem cutTau_zero_of_ge {t : ℝ} (h : 3 / 2 ≤ t) : cutTau t = 0 := by
  unfold cutTau
  rw [Real.smoothTransition.zero_of_nonpos (show 3 - 2 * t ≤ 0 by linarith), mul_zero]

theorem cutTau_abs_zero {t : ℝ} (h : 3 / 2 ≤ |t|) : cutTau t = 0 := by
  rcases lt_or_ge 0 t with ht | ht
  · exact cutTau_zero_of_ge (by rw [abs_of_nonneg (le_of_lt ht)] at h; linarith)
  · exact cutTau_zero_of_le (by rw [abs_of_nonpos ht] at h; linarith)

theorem cutTau_ne_zero_mem {t : ℝ} (h : cutTau t ≠ 0) : t ∈ Set.Ioo (-1 : ℝ) 2 := by
  by_contra hc
  rw [Set.mem_Ioo, not_and_or] at hc
  apply h
  rcases hc with hc | hc
  · exact cutTau_zero_of_le (by have := not_lt.mp hc; linarith)
  · exact cutTau_zero_of_ge (by have := not_lt.mp hc; linarith)

/-! ## Smoothness of `H0` -/

/-- **`H0` is `C⁴` for `τ` in the open interval `(-1,2)`.**  Near a point of the tube the witness is
provided by the local chart of `T.chart` (or by the explicit inverse `y ↦ (q₁ y, q₂ y, -p y)` in
the standard region `|x| > X₀`), and away from the tube `H0` vanishes on a neighbourhood by
`closure_theta_smallStrip_Icc`. -/
theorem H0_contDiffAt_aux (L : Work.RPA3.LagFamilyAll) (F : Work.RPA3.FluxPrimitive L)
    (T : Work.RPA3.TubularData L) (τ : ℝ) (hτ : τ ∈ Set.Ioo (-1 : ℝ) 2) (y : Work.RPA3.PS) :
    ContDiffAt ℝ 4 (fun p : ℝ × Work.RPA3.PS => Work.RPA3.H0 L F T p.1 p.2) (τ, y) := by
  by_cases hW : HasWitness L T τ y
  · obtain ⟨w₀, hw₀ε, hw₀θ⟩ := hW
    by_cases hx : |w₀.1.1| ≤ L.X0 + 1
    · -- ## The chart near a witness with `|x| ≤ X₀ + 1`
      obtain ⟨U, σ, hUopen, hmem, hσ, hσcd, hsr⟩ :=
        T.chart (τ, w₀) ⟨le_of_lt hτ.1, le_of_lt hτ.2⟩ hx (by simpa using hw₀ε)
      have hmemU : (τ, y) ∈ U := by
        have h1 : thetaP L (τ, w₀) = (τ, y) := by
          simp only [thetaP, thetaZ, hw₀θ]
        simpa [h1] using hmem
      have hστ : σ (τ, y) = w₀ := by
        have h1 : thetaP L (τ, w₀) = (τ, y) := by
          simp only [thetaP, thetaZ, hw₀θ]
        rw [← h1]; exact hσ
      have hστ' : (σ (τ, y)).2 = w₀.2 := congrArg Prod.snd hστ
      -- the model function on the chart
      set Φ : ℝ × PS → ℝ := fun p => cutXi T.ε ((σ p).2) * F.h p.1 (σ p).1 with hΦdef
      have hsnd : ContDiffOn ℝ 7 (fun p : ℝ × PS => (σ p).2) U :=
        (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (ℝ × ℝ)).contDiff.comp_contDiffOn hσcd
      have hfst : ContDiffOn ℝ 7 (fun p : ℝ × PS => (σ p).1) U :=
        (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (ℝ × ℝ)).contDiff.comp_contDiffOn hσcd
      have hcut : ContDiffOn ℝ 7 (fun p : ℝ × PS => cutXi T.ε ((σ p).2)) U :=
        (cutXi_contDiff T.ε 7).comp_contDiffOn hsnd
      have harg : ContDiffOn ℝ 7 (fun p : ℝ × PS => (p.1, (σ p).1)) U :=
        (contDiff_fst : ContDiff ℝ 7 (fun p : ℝ × PS => p.1)).contDiffOn.prodMk hfst
      have hFh : ContDiffOn ℝ 7 (fun p : ℝ × PS => F.h p.1 (σ p).1) U :=
        F.smooth.comp_contDiffOn harg
      have hΦcd : ContDiffOn ℝ 4 Φ U := (hcut.mul hFh).of_le (by norm_num)
      have hΦ : ContDiffAt ℝ 4 Φ (τ, y) := hΦcd.contDiffAt (hUopen.mem_nhds hmemU)
      -- `H0` agrees with the model function near `(τ,y)`
      have hev : (fun p : ℝ × PS => H0 L F T p.1 p.2) =ᶠ[𝓝 (τ, y)] Φ := by
        have hU' : U ∩ {p : ℝ × PS | p.1 ∈ Set.Ioo (-1 : ℝ) 2} ∩
            {p : ℝ × PS | ‖(σ p).2‖ < T.ε} ∈ 𝓝 (τ, y) := by
          refine Filter.inter_mem (Filter.inter_mem (hUopen.mem_nhds hmemU) ?_) ?_
          · exact (isOpen_Ioo.preimage continuous_fst).mem_nhds hτ
          · have hσc : ContinuousAt σ (τ, y) :=
              hσcd.continuousOn.continuousAt (hUopen.mem_nhds hmemU)
            have hcont : ContinuousAt (fun p : ℝ × PS => ‖(σ p).2‖) (τ, y) :=
              (continuous_norm.comp continuous_snd).continuousAt.comp hσc
            have hlt : ‖(σ (τ, y)).2‖ < T.ε := by rw [hστ']; exact hw₀ε
            exact hcont.preimage_mem_nhds ((isOpen_lt continuous_id continuous_const).mem_nhds hlt)
        filter_upwards [hU'] with p hp
        obtain ⟨⟨hpU, hpτ⟩, hpξ⟩ := hp
        have hwit : HasWitness L T p.1 p.2 := by
          refine ⟨σ p, hpξ, ?_⟩
          have h2 : (thetaP L (p.1, σ p)).2 = p.2 := congrArg Prod.snd (hsr p hpU)
          rwa [thetaP_apply, thetaZ_apply] at h2
        have hwit_eq : wit L T p.1 p.2 hwit = σ p :=
          witness_unique L T ⟨le_of_lt hpτ.1, le_of_lt hpτ.2⟩
            (wit_spec L T p.1 p.2 hwit) ⟨hpξ, by
              have h2 : (thetaP L (p.1, σ p)).2 = p.2 := congrArg Prod.snd (hsr p hpU)
              rwa [thetaP_apply, thetaZ_apply] at h2⟩
        rw [H0_of L F T p.1 p.2 hwit, hwit_eq]
      exact hΦ.congr_of_eventuallyEq hev
    · -- ## The standard region `|x| > X₀ + 1`
      push_neg at hx
      have hxX0 : L.X0 ≤ |w₀.1.1| := by linarith
      have hyθ : y = ((w₀.1.1, w₀.1.2), (-w₀.2.1, -w₀.2.2)) := by
        rw [← hw₀θ, theta_std L τ w₀.1.1 w₀.1.2 w₀.2 hxX0]
      have hy1 : L.X0 < |y.1.1| := by rw [hyθ]; simpa using (by linarith : L.X0 < |w₀.1.1|)
      have hy2 : ‖y.2‖ < T.ε := by
        rw [hyθ]
        simpa [Prod.norm_def] using hw₀ε
      -- the explicit model function
      set Ψ : ℝ × PS → ℝ :=
        fun p => cutXi T.ε (-p.2.2) * F.h p.1 (p.2.1.1, p.2.1.2) with hΨdef
      have hΨcd : ContDiff ℝ 4 Ψ := by
        rw [hΨdef]
        have h1 : ContDiff ℝ 4 (fun p : ℝ × PS => cutXi T.ε (-p.2.2)) :=
          (cutXi_contDiff T.ε 4).comp (by fun_prop)
        have h2 : ContDiff ℝ 4 (fun p : ℝ × PS => F.h p.1 (p.2.1.1, p.2.1.2)) := by
          have hg : ContDiff ℝ 4 (fun p : ℝ × PS => (p.1, (p.2.1.1, p.2.1.2))) := by fun_prop
          exact (F.smooth.of_le (by norm_num)).comp hg
        exact h1.mul h2
      have hev : (fun p : ℝ × PS => H0 L F T p.1 p.2) =ᶠ[𝓝 (τ, y)] Ψ := by
        have hV : {p : ℝ × PS | L.X0 < |p.2.1.1|} ∩
            {p : ℝ × PS | p.1 ∈ Set.Ioo (-1 : ℝ) 2} ∩
            {p : ℝ × PS | ‖p.2.2‖ < T.ε} ∈ 𝓝 (τ, y) := by
          refine Filter.inter_mem (Filter.inter_mem ?_ ?_) ?_
          · exact (isOpen_lt continuous_const (by fun_prop)).mem_nhds hy1
          · exact (isOpen_Ioo.preimage continuous_fst).mem_nhds hτ
          · exact (isOpen_lt (by fun_prop : Continuous (fun p : ℝ × PS => ‖p.2.2‖))
              continuous_const).mem_nhds hy2
        filter_upwards [hV] with p hp
        obtain ⟨⟨hpx, hpτ⟩, hpξ⟩ := hp
        have hζε : ‖(-p.2.2)‖ < T.ε := by rwa [norm_neg]
        have hζθ : theta L p.1 p.2.1.1 p.2.1.2 (-p.2.2) = p.2 := by
          rw [theta_std L p.1 p.2.1.1 p.2.1.2 (-p.2.2) (le_of_lt hpx)]
          simp
        have hwit : HasWitness L T p.1 p.2 := ⟨((p.2.1.1, p.2.1.2), -p.2.2), hζε, hζθ⟩
        have hwit_eq : wit L T p.1 p.2 hwit = ((p.2.1.1, p.2.1.2), -p.2.2) :=
          witness_unique L T ⟨le_of_lt hpτ.1, le_of_lt hpτ.2⟩
            (wit_spec L T p.1 p.2 hwit) ⟨hζε, hζθ⟩
        rw [H0_of L F T p.1 p.2 hwit, hwit_eq]
      exact hΨcd.contDiffAt.congr_of_eventuallyEq hev
  · -- ## No witness: `H0` vanishes on a neighbourhood
    have hnotmem : (τ, y) ∉ closure {q : ℝ × PS | q.1 ∈ Set.Icc (-1 : ℝ) 2 ∧
        ∃ w : PS, ‖w.2‖ < T.ε / 2 ∧ theta L q.1 w.1.1 w.1.2 w.2 = q.2} := by
      intro hmem
      exact hW (closure_theta_smallStrip_Icc L T hmem)
    have hev : (fun p : ℝ × PS => H0 L F T p.1 p.2) =ᶠ[𝓝 (τ, y)] (fun _ => 0) := by
      have hcomp : (closure {q : ℝ × PS | q.1 ∈ Set.Icc (-1 : ℝ) 2 ∧
          ∃ w : PS, ‖w.2‖ < T.ε / 2 ∧ theta L q.1 w.1.1 w.1.2 w.2 = q.2})ᶜ ∈ 𝓝 (τ, y) :=
        (isClosed_closure.isOpen_compl).mem_nhds hnotmem
      filter_upwards [hcomp, (isOpen_Ioo.preimage continuous_fst).mem_nhds hτ] with p hp hpτ
      by_contra hne
      have hwit : HasWitness L T p.1 p.2 := by
        by_contra hh
        exact hne (H0_of_not L F T p.1 p.2 hh)
      have hsmall : ‖(wit L T p.1 p.2 hwit).2‖ < T.ε / 2 := by
        by_contra hh
        rw [not_lt] at hh
        exact hne (H0_eq_zero_of_witness_far L F T p.1 p.2 hwit hh)
      exact hp (subset_closure ⟨⟨le_of_lt hpτ.1, le_of_lt hpτ.2⟩, wit L T p.1 p.2 hwit, hsmall,
        theta_wit L T p.1 p.2 hwit⟩)
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-- D2, the tubular Hamiltonian.  From the flux primitive F (F.h is the primitive of
-ω(∂_τℓ,·) along the family, 2π-periodic in t, vanishing for |x| ≥ X₀) and the tubular data T
(uniform injectivity radius ε for the searched strip, and the local C⁷ inverse charts of thetaP),
there is H : ℝ → PS → ℝ which is C⁴, 2π-periodic in q₂, supported in the slab
|q₁| + |p₁| + |p₂| ≤ R, whose Hamiltonian vector field is bounded and jointly Lipschitz in (t,y),
and whose directional derivatives along the family satisfy, for τ ∈ [0,1],
dH(∂_xℓ) = -ω(∂_τℓ, ∂_xℓ) and dH(∂_tℓ) = -ω(∂_τℓ, ∂_tℓ) (equivalently H = h along the family).

Construction.  Fix smooth cut-offs χτ with χτ = 1 on [0,1] and χτ = 0 off (-1,2), and χξ with
χξ = 1 on [0, T.ε/4] and χξ = 0 on [T.ε/2, ∞).  Let D be the set of z : PS with t ∈ [0,2π] and
‖z.2‖ ≤ T.ε/2 (with x unrestricted), and let val z be χξ ‖z.2‖ times F.h τ (z.1.1, z.1.2).  Define
H τ y as χτ τ times the value val of a witness z ∈ D with Tk k (thetaZ L τ z) = y, and 0 if there is
no witness.  Well-definedness: two witnesses in D for the same y differ by a period in t (T.inj,
using ‖ξ‖ ≤ ε/2 < ε), and val is invariant under the period by F.per.  Periodicity in q₂ of H:
Tk-saturation is built in (Tk (k+1) also witnesses Tk 1 y).  Support: val vanishes for |x| ≥ X₀
(F.van) and for ‖z.2‖ ≥ T.ε/2 (χξ), and the coordinates q₁,p₁,p₂ of theta are bounded on the image
of the compact piece with |x| ≤ X₀ (the Tk-shift moves only q₂).  Smoothness: near a point covered by
a chart use χτ τ times val composed with the C⁷ chart σ of T.chart (which needs |x| ≤ X₀+1); far from
the family (|x| ≥ X₀) the chart is explicit, σ y = (q₁ y, q₂ y, -p y), by theta_std; and H vanishes
near a point with no witness in D because the image of D is closed (compactness in the q₂-direction
via the boundedness of the q₂-coordinate of theta, and boundedness of x from q₁ ∘ theta).  Generation:
at ξ = 0 the witness of ℓ τ (x,t) is ((x,t),0) and the cut-offs equal 1 for τ ∈ [0,1], so
H τ (ℓ τ (x,t)) = F.h τ (x,t); differentiating along x and along t gives the two identities by F.dx
and F.dt.  Lipschitz and bounded: H is C⁴ with support in |t| ≤ 2 and the slab and is periodic in q₂,
so the derivative of hamVF (H t) is bounded uniformly in t. -/
theorem exists_tubular_H (L : Work.RPA3.LagFamilyAll) (F : Work.RPA3.FluxPrimitive L)
    (T : Work.RPA3.TubularData L) :
    ∃ H : ℝ → Work.RPA3.PS → ℝ, ContDiff ℝ 4 (fun z : ℝ × Work.RPA3.PS => H z.1 z.2) ∧
      (∀ t x, H t (Work.RPA3.Tk 1 x) = H t x) ∧
      (∃ R, ∀ t x, R ≤ |x.1.1| + |x.2.1| + |x.2.2| → H t x = 0) ∧
      (∃ K : NNReal, LipschitzWith K (fun p : ℝ × Work.RPA3.PS => Work.RPA3.hamVF (H p.1) p.2)) ∧
      (∃ M : ℝ, ∀ t x, ‖Work.RPA3.hamVF (H t) x‖ ≤ M) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ x t,
        deriv (fun s => H τ (L.ℓ τ (x + s, t))) 0 =
          -Work.RPA3.symp (deriv (fun σ => L.ℓ σ (x, t)) τ) (deriv (fun y => L.ℓ τ (y, t)) x) ∧
        deriv (fun s => H τ (L.ℓ τ (x, t + s))) 0 =
          -Work.RPA3.symp (deriv (fun σ => L.ℓ σ (x, t)) τ) (deriv (fun s => L.ℓ τ (x, s)) t)) := by
  obtain ⟨R0, hR0⟩ := H0_slab L F T
  have hsmooth : ContDiff ℝ 4
      (fun z : ℝ × PS => cutTau z.1 * H0 L F T z.1 z.2) := by
    rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : p.1 ∈ Set.Ioo (-1 : ℝ) 2
    · have h1 : ContDiffAt ℝ 4 (fun z : ℝ × PS => cutTau z.1) p :=
        (cutTau_contDiff 4).contDiffAt.comp p (by fun_prop)
      exact h1.mul (H0_contDiffAt_aux L F T p.1 hp p.2)
    · have hev : (fun z : ℝ × PS => cutTau z.1 * H0 L F T z.1 z.2) =ᶠ[𝓝 p] (fun _ => 0) := by
        rw [Set.mem_Ioo, not_and_or] at hp
        rcases hp with hp | hp
        · have hopen : IsOpen {z : ℝ × PS | z.1 < -1 / 2} :=
            isOpen_lt continuous_fst continuous_const
          have hmem : p.1 < -1 / 2 := by have := not_lt.mp hp; linarith
          filter_upwards [hopen.mem_nhds hmem] with z hz
          rw [cutTau_zero_of_le (le_of_lt hz), zero_mul]
        · have hopen : IsOpen {z : ℝ × PS | (3 / 2 : ℝ) < z.1} :=
            isOpen_lt continuous_const continuous_fst
          have hmem : (3 / 2 : ℝ) < p.1 := by have := not_lt.mp hp; linarith
          filter_upwards [hopen.mem_nhds hmem] with z hz
          rw [cutTau_zero_of_ge (le_of_lt hz), zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have hper : ∀ t x, cutTau t * H0 L F T t (Tk 1 x) = cutTau t * H0 L F T t x := by
    intro t x
    by_cases ht : t ∈ Set.Icc (-1 : ℝ) 2
    · rw [H0_Tk L F T ht 1 x]
    · have h0 : cutTau t = 0 := by
        rw [Set.mem_Icc, not_and_or] at ht
        rcases ht with ht | ht
        · exact cutTau_zero_of_le (by have := not_le.mp ht; linarith)
        · exact cutTau_zero_of_ge (by have := not_le.mp ht; linarith)
      rw [h0, zero_mul, zero_mul]
  have hsT : ∃ R : ℝ, ∀ t x, R ≤ |t| → cutTau t * H0 L F T t x = 0 :=
    ⟨3 / 2, fun t x h => by rw [cutTau_abs_zero h, zero_mul]⟩
  have hsR : ∃ R : ℝ, ∀ t x, R ≤ |x.1.1| + |x.2.1| + |x.2.2| →
      cutTau t * H0 L F T t x = 0 := by
    refine ⟨R0, fun t x hx => ?_⟩
    by_cases ht : t ∈ Set.Icc (-1 : ℝ) 2
    · rw [hR0 t ht x hx, mul_zero]
    · have h0 : cutTau t = 0 := by
        rw [Set.mem_Icc, not_and_or] at ht
        rcases ht with ht | ht
        · exact cutTau_zero_of_le (by have := not_le.mp ht; linarith)
        · exact cutTau_zero_of_ge (by have := not_le.mp ht; linarith)
      rw [h0, zero_mul]
  refine ⟨fun τ y => cutTau τ * H0 L F T τ y, hsmooth, hper, hsR, ?_, ?_, ?_⟩
  · exact (hamVF_lipschitz_bounded _ hsmooth hper hsT hsR).1
  · exact (hamVF_lipschitz_bounded _ hsmooth hper hsT hsR).2
  · intro τ hτ x t
    have hτ' : τ ∈ Set.Icc (-1 : ℝ) 2 := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    have hone : cutTau τ = 1 := cutTau_one hτ.1 hτ.2
    constructor
    · have heq : (fun s : ℝ => cutTau τ * H0 L F T τ (L.ℓ τ (x + s, t)))
          = fun s : ℝ => F.h τ (x + s, t) := by
        funext s
        rw [H0_ell L F T hτ' (x + s) t, hone, one_mul]
      rw [heq]
      rw [show (fun s : ℝ => F.h τ (x + s, t)) = fun s : ℝ => F.h τ (s + x, t) from by
        funext s; rw [add_comm]]
      rw [deriv_comp_add_const (fun y : ℝ => F.h τ (y, t)) x 0, zero_add]
      exact F.dx τ x t
    · have heq : (fun s : ℝ => cutTau τ * H0 L F T τ (L.ℓ τ (x, t + s)))
          = fun s : ℝ => F.h τ (x, t + s) := by
        funext s
        rw [H0_ell L F T hτ' x (t + s), hone, one_mul]
      rw [heq]
      rw [show (fun s : ℝ => F.h τ (x, t + s)) = fun s : ℝ => F.h τ (x, s + t) from by
        funext s; rw [add_comm]]
      rw [deriv_comp_add_const (fun s : ℝ => F.h τ (x, s)) t 0, zero_add]
      exact F.dt τ x t

end Work.RPA3
