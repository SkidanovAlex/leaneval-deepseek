import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_EllLimOK.ProducerH.MixedJets.mixed_jets_le_Xn6
import Submission.Work.FTS_EllLimOK.ProducerH.MixedJets.pkgCos_le4
import Submission.Work.FTS_EllLimOK.ProducerH.slotBd_phiTil
import Submission.Work.FTS_EllLimOK.RulingELF
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.Spaces.HProductRule_bad_term
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH.H2

open Set Filter Work.Spaces
open Work.FTS.StrongGlobal
open scoped Real Topology

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Congruence of the slice derivatives

These two lemmas let one replace a function by another that agrees on a neighbourhood of the
slice: they are the tool for moving `Clairaut` equalities under a further differentiation. -/

theorem pz_congr_ev {u v : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ∀ᶠ z' in 𝓝 z, u z' θ = v z' θ) : pz u z θ = pz v z θ := by
  have h' : (fun z' => u z' θ) =ᶠ[𝓝 z] (fun z' => v z' θ) := h
  simpa only [pz] using h'.deriv_eq

theorem pth_congr_ev {u v : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ∀ᶠ θ' in 𝓝 θ, u z θ' = v z θ') : pth u z θ = pth v z θ := by
  have h' : (fun θ' => u z θ') =ᶠ[𝓝 θ] (fun θ' => v z θ') := h
  simpa only [pth] using h'.deriv_eq

/-! ## The mean-value bound in one variable -/

/-- The mean-value inequality for a smooth function on an open convex set, in the form used
everywhere below. -/
theorem abs_sub_le_of_deriv_bound {u : ℝ → ℝ} {s : Set ℝ} {x y C : ℝ} {n : WithTop ℕ∞}
    (hsopen : IsOpen s) (hsm : ContDiffOn ℝ n u s) (hn : n ≠ 0)
    (hb : ∀ t ∈ s, ‖deriv u t‖ ≤ C) (hs : Convex ℝ s) (hx : x ∈ s) (hy : y ∈ s) :
    |u x - u y| ≤ C * |x - y| := by
  have hdiff : ∀ t ∈ s, DifferentiableAt ℝ u t := fun t ht =>
    (hsm.contDiffAt (hsopen.mem_nhds ht)).differentiableAt hn
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hb hs hx hy
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
  rw [abs_sub_comm (u y) (u x), abs_sub_comm y x] at h
  exact h

/-- The angular mean-value bound for a function smooth on the open quadrant: the difference of
the two `θ`-slices at fixed `z` is controlled by the sup bound on `∂_θ`. -/
theorem abs_slice_theta_bound {u : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.SmoothOpen u)
    {z θ θ' C : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hθ' : θ' ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hb : ∀ s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |pth u z s| ≤ C) :
    |u z θ - u z θ'| ≤ C * |θ - θ'| :=
  abs_sub_le_of_deriv_bound isOpen_Ioo (h.curry_θ hz)
    (by simp [Work.Stability.smoothOrder])
    (fun s hs => by rw [Real.norm_eq_abs]; exact hb s hs) (convex_Ioo _ _) hθ hθ'

/-- The radial mean-value bound for a function smooth on the open quadrant: the difference of
the two `z`-slices at fixed `θ` is controlled by the sup bound on `∂_z`. -/
theorem abs_slice_z_bound {u : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.SmoothOpen u)
    {a b z z' θ C : ℝ} (ha : 0 < a) (hz : z ∈ Set.Ioo a b) (hz' : z' ∈ Set.Ioo a b)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hb : ∀ s ∈ Set.Ioo a b, |pz u s θ| ≤ C) : |u z θ - u z' θ| ≤ C * |z - z'| := by
  have hsub : Set.Ioo a b ⊆ Set.Ioi (0 : ℝ) := fun t ht => by
    simp only [Set.mem_Ioi]; linarith [ht.1, ha]
  exact abs_sub_le_of_deriv_bound isOpen_Ioo ((h.curry_z hθ).mono hsub)
    (by simp [Work.Stability.smoothOrder])
    (fun s hs => by rw [Real.norm_eq_abs]; exact hb s hs) (convex_Ioo _ _) hz hz'

/-! ## Elementary real-power bookkeeping -/

/-- For `0 ≤ t ≤ r ≤ 1` and `0 < β ≤ β₀`: `t ^ β₀ ≤ r ^ β`. -/
theorem rpow_le_rpow_of_bounds {t r β₀ β : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r) (hr1 : r ≤ 1)
    (hβ0 : 0 < β) (hββ₀ : β ≤ β₀) : t ^ β₀ ≤ r ^ β := by
  rcases eq_or_lt_of_le ht0 with h | h
  · subst h
    rw [Real.zero_rpow (by linarith : β₀ ≠ 0)]
    exact Real.rpow_nonneg (le_trans ht0 htr) _
  · refine le_trans ?_ (Real.rpow_le_rpow h.le htr hβ0.le)
    exact Real.rpow_le_rpow_of_exponent_ge h (le_trans htr hr1) hββ₀

/-- For `0 ≤ r ≤ 1` and `0 < β ≤ 1`: `r ≤ r ^ β`. -/
theorem le_rpow_self {r β : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    r ≤ r ^ β := by
  rcases eq_or_lt_of_le hr0 with h | h
  · subst h; rw [Real.zero_rpow (ne_of_gt hβ0)]
  · exact le_trans (le_of_eq (Real.rpow_one r).symm)
      (Real.rpow_le_rpow_of_exponent_ge h hr1 hβ1)

/-! ## The third-order Clairaut rearrangements

On the open quadrant the four third-order mixed derivatives of a smooth function coalesce in
the way needed for the angular/radial Lipschitz bounds of the second-order components. -/

theorem third_order_rearrange {Ψ : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z θ : ℝ} (hz : 0 < z) (hθm : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    pz (pth (pz Ψ)) z θ = pth (pz (pz Ψ)) z θ ∧
    pz (pz (pth Ψ)) z θ = pth (pz (pz Ψ)) z θ ∧
    pth (pz (pth Ψ)) z θ = pth (pth (pz Ψ)) z θ ∧
    pz (pth (pth Ψ)) z θ = pth (pth (pz Ψ)) z θ := by
  have hcd : ∀ z' θ' : ℝ, 0 < z' → θ' ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      ContDiffAt ℝ 2 (Function.uncurry Ψ) (z', θ') := fun z' θ' hz' hθ' =>
    (h.forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz', hθ'.1, hθ'.2⟩))
  have h1 : pz (pth (pz Ψ)) z θ = pth (pz (pz Ψ)) z θ :=
    Work.Spaces.pz_pth_comm (f := pz Ψ) ((h.pz.forall 2).contDiffAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
        (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθm.1, hθm.2⟩)))
  have hev : ∀ᶠ z' in 𝓝 z, pz (pth Ψ) z' θ = pth (pz Ψ) z' θ := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact Work.Spaces.pz_pth_comm (hcd z' θ hz' hθm)
  have h2 : pz (pz (pth Ψ)) z θ = pth (pz (pz Ψ)) z θ := by
    rw [pz_congr_ev hev, h1]
  have hev2 : ∀ᶠ θ' in 𝓝 θ, pz (pth Ψ) z θ' = pth (pz Ψ) z θ' := by
    filter_upwards [isOpen_Ioo.mem_nhds hθm] with θ' hθ'
    exact Work.Spaces.pz_pth_comm (hcd z θ' hz hθ')
  have h3 : pth (pz (pth Ψ)) z θ = pth (pth (pz Ψ)) z θ := pth_congr_ev hev2
  have h4a : pz (pth (pth Ψ)) z θ = pth (pz (pth Ψ)) z θ :=
    Work.Spaces.pz_pth_comm (f := pth Ψ) ((h.pth.forall 2).contDiffAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
        (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθm.1, hθm.2⟩)))
  exact ⟨h1, h2, h3, by rw [h4a, ← h3]⟩

/-- On the interior of the box, the within-jet over the **closed** box coincides with the
ordinary iterated derivative. -/
theorem iteratedFDerivWithin_cbox_eq {a b : ℝ} (hab : a < b) {F : ℝ × ℝ → ℝ}
    (hcd : ContDiffOn ℝ 2 F (Work.FTS_EllLimOK.cbox a b)) {x : ℝ × ℝ}
    (hx : x ∈ Set.Ioo a b ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    iteratedFDerivWithin ℝ 2 F (Work.FTS_EllLimOK.cbox a b) x = iteratedFDeriv ℝ 2 F x := by
  have hOp : IsOpen (Set.Ioo a b ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo.prod isOpen_Ioo
  have hsub : Set.Ioo a b ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Work.FTS_EllLimOK.cbox a b := by
    intro p hp
    exact Work.FTS_EllLimOK.mem_cbox.mpr
      ⟨⟨le_of_lt hp.1.1, le_of_lt hp.1.2⟩, ⟨le_of_lt hp.2.1, le_of_lt hp.2.2⟩⟩
  have h1 := iteratedFDerivWithin_subset (𝕜 := ℝ) (n := 2)
    (s := Set.Ioo a b ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) (t := Work.FTS_EllLimOK.cbox a b)
    (f := F) (x := x) hsub hOp.uniqueDiffOn
    (Work.FTS_EllLimOK.BoxDataH.uniqueDiffOn_cbox hab) hcd hx
  have h2 := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
    (s := Set.Ioo a b ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) (f := F) 2 hOp hx
  exact h1.symm.trans h2

theorem clause3 {α Ce : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hE : Work.FTS_EllLimOK.ProducerH.H2.Ctx α Ce E) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hdata : Work.FTS_EllLimOK.ProducerH.H2.BoxData α Ce E a b)
    (hc1 : ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α g →
      ContDiffOn ℝ 2 (Function.uncurry (E g)) (Work.FTS_EllLimOK.cbox a b)) :
    ∃ K : ℝ, 0 < K ∧ ∃ β : ℝ, 0 < β ∧ ∀ g : Work.FTS.Galerkin.Fn,
      Work.FTS.ClassC.ClassC α g →
      ∀ p ∈ Work.FTS_EllLimOK.cbox a b, ∀ q ∈ Work.FTS_EllLimOK.cbox a b,
        ‖iteratedFDerivWithin ℝ 2 (Function.uncurry (E g)) (Work.FTS_EllLimOK.cbox a b) p
          - iteratedFDerivWithin ℝ 2 (Function.uncurry (E g)) (Work.FTS_EllLimOK.cbox a b) q‖
          ≤ K * Work.FTS.StrongGlobal.Xn6 α g * ‖p - q‖ ^ β := by
  obtain ⟨K₀, hK₀, β₀, hβ₀, hmod, hrates, hlim, hhol⟩ := hdata
  obtain ⟨Cb, hCb, hratesb⟩ := hrates
  obtain ⟨Kh, hKh, βh, hβh, hholb⟩ := hhol
  obtain ⟨Km, hKm, hmix⟩ :=
    Work.FTS_EllLimOK.ProducerH.MixedJets.mixed_jets_le_Xn6 hα hα4 hE
  have hb0 : 0 < b := lt_trans ha hab
  have hnum : 0 ≤ Km + b * Cb + 3 * b ^ 2 * Cb := by positivity
  have hC₃nn : 0 ≤ (Km + b * Cb + 3 * b ^ 2 * Cb) / a ^ 3 :=
    div_nonneg hnum (by positivity)
  have hβpos : 0 < min βh 1 := lt_min hβh one_pos
  refine ⟨6 * Cb + (Km + b * Cb + 3 * b ^ 2 * Cb) / a ^ 3 + Kh + 8 * Cb + 1, ?_,
    min βh 1, hβpos, ?_⟩
  · linarith [hCb, hKh, hC₃nn]
  intro g hg
  have hSm : Work.FTS.EllipticEst.SmoothOpen (E g) := (hE g hg).1.2.1
  have hXnn : 0 ≤ Xn6 α g := Xn6_nonneg α g
  refine Support.extend_holder_from_interior
    (F := fun p : ℝ × ℝ => iteratedFDerivWithin ℝ 2 (Function.uncurry (E g))
      (Work.FTS_EllLimOK.cbox a b) p)
    (K := (6 * Cb + (Km + b * Cb + 3 * b ^ 2 * Cb) / a ^ 3 + Kh + 8 * Cb + 1) * Xn6 α g)
    hab hβpos ?_ ?_
  · exact (hc1 g hg).continuousOn_iteratedFDerivWithin (m := 2) (by norm_num)
      (Work.FTS_EllLimOK.BoxDataH.uniqueDiffOn_cbox hab)
  · rintro ⟨z, θ⟩ hp ⟨z', θ'⟩ hq
    have hzI : z ∈ Set.Ioo a b := hp.1
    have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := hp.2
    have hzI' : z' ∈ Set.Ioo a b := hq.1
    have hθI' : θ' ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := hq.2
    have hz0 : 0 < z := lt_trans ha hzI.1
    have hz0' : 0 < z' := lt_trans ha hzI'.1
    have hzc : z ∈ Set.Icc a b := ⟨le_of_lt hzI.1, le_of_lt hzI.2⟩
    have hzc' : z' ∈ Set.Icc a b := ⟨le_of_lt hzI'.1, le_of_lt hzI'.2⟩
    have hOpB : IsOpen (Set.Ioo a b ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      isOpen_Ioo.prod isOpen_Ioo
    have hcd : ∀ z₀ ∈ Set.Ioo a b, ∀ θ₀ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        ContDiffAt ℝ 2 (Function.uncurry (E g)) (z₀, θ₀) := fun z₀ hz₀ θ₀ hθ₀ =>
      (hSm.forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
        (Work.FTS.EllipticEst.mem_Q0.mpr ⟨lt_trans ha hz₀.1, hθ₀.1, hθ₀.2⟩))
    -- the pointwise bounds of `RatesWith`, as functions of the running variable
    have h7z : ∀ s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |pth (pz (pz (E g))) z s| ≤ Cb * Xn6 α g := fun s hs =>
      (hratesb g hg z hzc s hs).2.2.2.2.2.2.1
    have h8z : ∀ s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |pth (pth (pz (E g))) z s| ≤ Cb * Xn6 α g := fun s hs =>
      (hratesb g hg z hzc s hs).2.2.2.2.2.2.2.1
    have h7w : ∀ s ∈ Set.Ioo a b,
        |pth (pz (pz (E g))) s θ'| ≤ Cb * Xn6 α g := fun s hs =>
      (hratesb g hg s ⟨le_of_lt hs.1, le_of_lt hs.2⟩ θ' hθI').2.2.2.2.2.2.1
    have h8w : ∀ s ∈ Set.Ioo a b,
        |pth (pth (pz (E g))) s θ'| ≤ Cb * Xn6 α g := fun s hs =>
      (hratesb g hg s ⟨le_of_lt hs.1, le_of_lt hs.2⟩ θ' hθI').2.2.2.2.2.2.2.1
    -- the third radial derivative of `Ψ`
    have h3rd : ∀ s ∈ Set.Ioo a b, |pzIter 3 (E g) s θ'|
        ≤ ((Km + b * Cb + 3 * b ^ 2 * Cb) / a ^ 3) * Xn6 α g := by
      intro s hs
      have hsIcc : s ∈ Set.Icc a b := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
      obtain ⟨h1, -, h3, -, -, -, -, -⟩ := hratesb g hg s hsIcc θ' hθI'
      have h4 := Support.pzIter_three_bound (Ψ := E g) hSm ha hsIcc hθI' (z := s) (θ := θ')
        (hmix g hg 3 0 (by norm_num) s θ'
          (show (s, θ') ∈ Work.Construction.Qd from ⟨lt_trans ha hs.1, hθI'.1, hθI'.2⟩)) h1 h3
      calc |pzIter 3 (E g) s θ'|
          ≤ (Km * Xn6 α g + b * (Cb * Xn6 α g) + 3 * b ^ 2 * (Cb * Xn6 α g)) / a ^ 3 := h4
        _ = ((Km + b * Cb + 3 * b ^ 2 * Cb) / a ^ 3) * Xn6 α g := by ring
    -- the value bound on the open box
    have hVfun : ∀ z₀ ∈ Set.Ioo a b, ∀ θ₀ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        ‖iteratedFDeriv ℝ 2 (Function.uncurry (E g)) (z₀, θ₀)‖
          ≤ 4 * (Cb * Xn6 α g) := by
      intro z₀ hz₀ θ₀ hθ₀
      have hle := Work.FTS_EllLimOK.ProducerH.BoxAux.norm_iterDF2_le
        (F := Function.uncurry (E g)) (Support.fderiv_fderiv_uncurry_eq (f := E g) (hcd z₀ hz₀ θ₀ hθ₀))
      obtain ⟨-, -, h3, h4, h5, h6, -⟩ :=
        hratesb g hg z₀ ⟨le_of_lt hz₀.1, le_of_lt hz₀.2⟩ θ₀ hθ₀
      calc ‖iteratedFDeriv ℝ 2 (Function.uncurry (E g)) (z₀, θ₀)‖
          ≤ |pz (pz (E g)) z₀ θ₀| + |pth (pz (E g)) z₀ θ₀| + |pz (pth (E g)) z₀ θ₀|
            + |pth (pth (E g)) z₀ θ₀| := hle
        _ ≤ Cb * Xn6 α g + Cb * Xn6 α g + Cb * Xn6 α g + Cb * Xn6 α g := by linarith
        _ = 4 * (Cb * Xn6 α g) := by ring
    -- the jet bound at the two interior points
    have hjet : ‖iteratedFDerivWithin ℝ 2 (Function.uncurry (E g)) (Work.FTS_EllLimOK.cbox a b)
            (z, θ)
        - iteratedFDerivWithin ℝ 2 (Function.uncurry (E g)) (Work.FTS_EllLimOK.cbox a b)
            (z', θ')‖
        ≤ |pz (pz (E g)) z θ - pz (pz (E g)) z' θ'|
          + |pth (pz (E g)) z θ - pth (pz (E g)) z' θ'|
          + |pz (pth (E g)) z θ - pz (pth (E g)) z' θ'|
          + |pth (pth (E g)) z θ - pth (pth (E g)) z' θ'| := by
      have h1 : iteratedFDerivWithin ℝ 2 (Function.uncurry (E g)) (Work.FTS_EllLimOK.cbox a b)
            (z, θ)
          = iteratedFDeriv ℝ 2 (Function.uncurry (E g)) (z, θ) :=
        iteratedFDerivWithin_cbox_eq hab (hc1 g hg) (F := Function.uncurry (E g)) hp
      have h2 : iteratedFDerivWithin ℝ 2 (Function.uncurry (E g)) (Work.FTS_EllLimOK.cbox a b)
            (z', θ')
          = iteratedFDeriv ℝ 2 (Function.uncurry (E g)) (z', θ') :=
        iteratedFDerivWithin_cbox_eq hab (hc1 g hg) (F := Function.uncurry (E g)) hq
      rw [h1, h2]
      exact Support.norm_iterDF2_sub_le (F := Function.uncurry (E g))
        (Support.fderiv_fderiv_uncurry_eq (hcd z hzI θ hθI)) (Support.fderiv_fderiv_uncurry_eq (hcd z' hzI' θ' hθI'))
    -- the four componentwise angular/radial bounds
    have hAθ : |pz (pz (E g)) z θ - pz (pz (E g)) z θ'| ≤ Cb * Xn6 α g * |θ - θ'| :=
      abs_slice_theta_bound (u := pz (pz (E g))) (hSm.pz.pz) hz0 hθI hθI' (fun s hs => h7z s hs)
    have hAz : |pz (pz (E g)) z θ' - pz (pz (E g)) z' θ'|
        ≤ ((Km + b * Cb + 3 * b ^ 2 * Cb) / a ^ 3 * Xn6 α g) * |z - z'| :=
      abs_slice_z_bound (u := pz (pz (E g))) (hSm.pz.pz) ha hzI hzI' hθI' (C := ((Km + b * Cb + 3 * b ^ 2 * Cb) / a ^ 3) * Xn6 α g)
        (fun s hs => h3rd s hs)
    have hBθ : |pth (pz (E g)) z θ - pth (pz (E g)) z θ'| ≤ Cb * Xn6 α g * |θ - θ'| :=
      abs_slice_theta_bound (u := pth (pz (E g))) (hSm.pz.pth) hz0 hθI hθI' (fun s hs => h8z s hs)
    have hBz : |pth (pz (E g)) z θ' - pth (pz (E g)) z' θ'| ≤ Cb * Xn6 α g * |z - z'| :=
      abs_slice_z_bound (u := pth (pz (E g))) (hSm.pz.pth) ha hzI hzI' hθI' (fun s hs => by
        rw [(third_order_rearrange hSm (lt_trans ha hs.1) hθI').1]
        exact h7w s hs)
    have hCθ : |pz (pth (E g)) z θ - pz (pth (E g)) z θ'| ≤ Cb * Xn6 α g * |θ - θ'| :=
      abs_slice_theta_bound (u := pz (pth (E g))) (hSm.pth.pz) hz0 hθI hθI' (fun s hs => by
        rw [(third_order_rearrange hSm hz0 hs).2.2.1]
        exact h8z s hs)
    have hCz : |pz (pth (E g)) z θ' - pz (pth (E g)) z' θ'| ≤ Cb * Xn6 α g * |z - z'| :=
      abs_slice_z_bound (u := pz (pth (E g))) (hSm.pth.pz) ha hzI hzI' hθI' (fun s hs => by
        rw [(third_order_rearrange hSm (lt_trans ha hs.1) hθI').2.1]
        exact h7w s hs)
    have hDθ : |pth (pth (E g)) z θ - pth (pth (E g)) z θ'|
        ≤ Kh * Xn6 α g * |θ - θ'| ^ βh := by
      have h := hholb g hg z hzc θ hθI θ' hθI'
      simpa only [pth] using h
    have hDz : |pth (pth (E g)) z θ' - pth (pth (E g)) z' θ'| ≤ Cb * Xn6 α g * |z - z'| :=
      abs_slice_z_bound (u := pth (pth (E g))) (hSm.pth.pth) ha hzI hzI' hθI' (fun s hs => by
        rw [(third_order_rearrange hSm (lt_trans ha hs.1) hθI').2.2.2]
        exact h8w s hs)
    -- the two coordinates are bounded by the norm
    have hr0 : 0 ≤ ‖(z, θ) - (z', θ')‖ := norm_nonneg _
    have hθr : |θ - θ'| ≤ ‖(z, θ) - (z', θ')‖ := by
      have h := norm_snd_le ((z, θ) - (z', θ'))
      rwa [Real.norm_eq_abs] at h
    have hzr : |z - z'| ≤ ‖(z, θ) - (z', θ')‖ := by
      have h := norm_fst_le ((z, θ) - (z', θ'))
      rwa [Real.norm_eq_abs] at h
    by_cases hr : ‖(z, θ) - (z', θ')‖ ≤ 1
    · -- small separation
      have hrr : ‖(z, θ) - (z', θ')‖ ≤ ‖(z, θ) - (z', θ')‖ ^ (min βh 1) :=
        le_rpow_self hr0 hr hβpos (min_le_right _ _)
      have hθr' : |θ - θ'| ≤ ‖(z, θ) - (z', θ')‖ ^ (min βh 1) := le_trans hθr hrr
      have hzr' : |z - z'| ≤ ‖(z, θ) - (z', θ')‖ ^ (min βh 1) := le_trans hzr hrr
      have hθβ : |θ - θ'| ^ βh ≤ ‖(z, θ) - (z', θ')‖ ^ (min βh 1) :=
        rpow_le_rpow_of_bounds (abs_nonneg _) hθr hr hβpos (min_le_left _ _)
      have hA : |pz (pz (E g)) z θ - pz (pz (E g)) z' θ'|
          ≤ (Cb + (Km + b * Cb + 3 * b ^ 2 * Cb) / a ^ 3) * Xn6 α g
              * ‖(z, θ) - (z', θ')‖ ^ (min βh 1) := by
        have h1 := abs_sub_le (pz (pz (E g)) z θ) (pz (pz (E g)) z θ') (pz (pz (E g)) z' θ')
        have h2 : Cb * Xn6 α g * |θ - θ'|
            ≤ Cb * Xn6 α g * ‖(z, θ) - (z', θ')‖ ^ (min βh 1) :=
          mul_le_mul_of_nonneg_left hθr' (mul_nonneg hCb.le hXnn)
        have h3 : ((Km + b * Cb + 3 * b ^ 2 * Cb) / a ^ 3) * Xn6 α g * |z - z'|
            ≤ ((Km + b * Cb + 3 * b ^ 2 * Cb) / a ^ 3) * Xn6 α g
              * ‖(z, θ) - (z', θ')‖ ^ (min βh 1) :=
          mul_le_mul_of_nonneg_left hzr' (mul_nonneg hC₃nn hXnn)
        calc |pz (pz (E g)) z θ - pz (pz (E g)) z' θ'|
            ≤ |pz (pz (E g)) z θ - pz (pz (E g)) z θ'|
              + |pz (pz (E g)) z θ' - pz (pz (E g)) z' θ'| := h1
          _ ≤ Cb * Xn6 α g * |θ - θ'|
              + ((Km + b * Cb + 3 * b ^ 2 * Cb) / a ^ 3) * Xn6 α g * |z - z'| :=
              add_le_add hAθ hAz
          _ ≤ Cb * Xn6 α g * ‖(z, θ) - (z', θ')‖ ^ (min βh 1)
              + ((Km + b * Cb + 3 * b ^ 2 * Cb) / a ^ 3) * Xn6 α g
                * ‖(z, θ) - (z', θ')‖ ^ (min βh 1) := add_le_add h2 h3
          _ = (Cb + (Km + b * Cb + 3 * b ^ 2 * Cb) / a ^ 3) * Xn6 α g
                * ‖(z, θ) - (z', θ')‖ ^ (min βh 1) := by ring
      have hB : |pth (pz (E g)) z θ - pth (pz (E g)) z' θ'|
          ≤ 2 * Cb * Xn6 α g * ‖(z, θ) - (z', θ')‖ ^ (min βh 1) := by
        have h1 := abs_sub_le (pth (pz (E g)) z θ) (pth (pz (E g)) z θ') (pth (pz (E g)) z' θ')
        have h2 : Cb * Xn6 α g * |θ - θ'|
            ≤ Cb * Xn6 α g * ‖(z, θ) - (z', θ')‖ ^ (min βh 1) :=
          mul_le_mul_of_nonneg_left hθr' (mul_nonneg hCb.le hXnn)
        have h3 : Cb * Xn6 α g * |z - z'|
            ≤ Cb * Xn6 α g * ‖(z, θ) - (z', θ')‖ ^ (min βh 1) :=
          mul_le_mul_of_nonneg_left hzr' (mul_nonneg hCb.le hXnn)
        calc |pth (pz (E g)) z θ - pth (pz (E g)) z' θ'|
            ≤ |pth (pz (E g)) z θ - pth (pz (E g)) z θ'|
              + |pth (pz (E g)) z θ' - pth (pz (E g)) z' θ'| := h1
          _ ≤ Cb * Xn6 α g * |θ - θ'| + Cb * Xn6 α g * |z - z'| := add_le_add hBθ hBz
          _ ≤ Cb * Xn6 α g * ‖(z, θ) - (z', θ')‖ ^ (min βh 1)
              + Cb * Xn6 α g * ‖(z, θ) - (z', θ')‖ ^ (min βh 1) := add_le_add h2 h3
          _ = 2 * Cb * Xn6 α g * ‖(z, θ) - (z', θ')‖ ^ (min βh 1) := by ring
      have hC : |pz (pth (E g)) z θ - pz (pth (E g)) z' θ'|
          ≤ 2 * Cb * Xn6 α g * ‖(z, θ) - (z', θ')‖ ^ (min βh 1) := by
        have h1 := abs_sub_le (pz (pth (E g)) z θ) (pz (pth (E g)) z θ') (pz (pth (E g)) z' θ')
        have h2 : Cb * Xn6 α g * |θ - θ'|
            ≤ Cb * Xn6 α g * ‖(z, θ) - (z', θ')‖ ^ (min βh 1) :=
          mul_le_mul_of_nonneg_left hθr' (mul_nonneg hCb.le hXnn)
        have h3 : Cb * Xn6 α g * |z - z'|
            ≤ Cb * Xn6 α g * ‖(z, θ) - (z', θ')‖ ^ (min βh 1) :=
          mul_le_mul_of_nonneg_left hzr' (mul_nonneg hCb.le hXnn)
        calc |pz (pth (E g)) z θ - pz (pth (E g)) z' θ'|
            ≤ |pz (pth (E g)) z θ - pz (pth (E g)) z θ'|
              + |pz (pth (E g)) z θ' - pz (pth (E g)) z' θ'| := h1
          _ ≤ Cb * Xn6 α g * |θ - θ'| + Cb * Xn6 α g * |z - z'| := add_le_add hCθ hCz
          _ ≤ Cb * Xn6 α g * ‖(z, θ) - (z', θ')‖ ^ (min βh 1)
              + Cb * Xn6 α g * ‖(z, θ) - (z', θ')‖ ^ (min βh 1) := add_le_add h2 h3
          _ = 2 * Cb * Xn6 α g * ‖(z, θ) - (z', θ')‖ ^ (min βh 1) := by ring
      have hD : |pth (pth (E g)) z θ - pth (pth (E g)) z' θ'|
          ≤ (Kh + Cb) * Xn6 α g * ‖(z, θ) - (z', θ')‖ ^ (min βh 1) := by
        have h1 := abs_sub_le (pth (pth (E g)) z θ) (pth (pth (E g)) z θ')
          (pth (pth (E g)) z' θ')
        have h2 : Kh * Xn6 α g * |θ - θ'| ^ βh
            ≤ Kh * Xn6 α g * ‖(z, θ) - (z', θ')‖ ^ (min βh 1) :=
          mul_le_mul_of_nonneg_left hθβ (mul_nonneg hKh.le hXnn)
        have h3 : Cb * Xn6 α g * |z - z'|
            ≤ Cb * Xn6 α g * ‖(z, θ) - (z', θ')‖ ^ (min βh 1) :=
          mul_le_mul_of_nonneg_left hzr' (mul_nonneg hCb.le hXnn)
        calc |pth (pth (E g)) z θ - pth (pth (E g)) z' θ'|
            ≤ |pth (pth (E g)) z θ - pth (pth (E g)) z θ'|
              + |pth (pth (E g)) z θ' - pth (pth (E g)) z' θ'| := h1
          _ ≤ Kh * Xn6 α g * |θ - θ'| ^ βh + Cb * Xn6 α g * |z - z'| := add_le_add hDθ hDz
          _ ≤ Kh * Xn6 α g * ‖(z, θ) - (z', θ')‖ ^ (min βh 1)
              + Cb * Xn6 α g * ‖(z, θ) - (z', θ')‖ ^ (min βh 1) := add_le_add h2 h3
          _ = (Kh + Cb) * Xn6 α g * ‖(z, θ) - (z', θ')‖ ^ (min βh 1) := by ring
      have hsum : |pz (pz (E g)) z θ - pz (pz (E g)) z' θ'|
            + |pth (pz (E g)) z θ - pth (pz (E g)) z' θ'|
            + |pz (pth (E g)) z θ - pz (pth (E g)) z' θ'|
            + |pth (pth (E g)) z θ - pth (pth (E g)) z' θ'|
          ≤ (6 * Cb + (Km + b * Cb + 3 * b ^ 2 * Cb) / a ^ 3 + Kh) * Xn6 α g
              * ‖(z, θ) - (z', θ')‖ ^ (min βh 1) := by
        nlinarith [hA, hB, hC, hD]
      refine le_trans (le_trans hjet hsum) ?_
      have hle : (6 * Cb + (Km + b * Cb + 3 * b ^ 2 * Cb) / a ^ 3 + Kh) * Xn6 α g
          ≤ (6 * Cb + (Km + b * Cb + 3 * b ^ 2 * Cb) / a ^ 3 + Kh + 8 * Cb + 1) * Xn6 α g :=
        mul_le_mul_of_nonneg_right (by linarith [hCb.le]) hXnn
      exact mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg hr0 _)
    · -- large separation: the value bound
      rw [not_le] at hr
      have hr1 : 1 ≤ ‖(z, θ) - (z', θ')‖ := le_of_lt hr
      have hR1 : 1 ≤ ‖(z, θ) - (z', θ')‖ ^ (min βh 1) := Real.one_le_rpow hr1 hβpos.le
      have hD2 : iteratedFDerivWithin ℝ 2 (Function.uncurry (E g)) (Work.FTS_EllLimOK.cbox a b)
            (z, θ)
          = iteratedFDeriv ℝ 2 (Function.uncurry (E g)) (z, θ) :=
        iteratedFDerivWithin_cbox_eq hab (hc1 g hg) (F := Function.uncurry (E g)) hp
      have hD2' : iteratedFDerivWithin ℝ 2 (Function.uncurry (E g)) (Work.FTS_EllLimOK.cbox a b)
            (z', θ')
          = iteratedFDeriv ℝ 2 (Function.uncurry (E g)) (z', θ') :=
        iteratedFDerivWithin_cbox_eq hab (hc1 g hg) (F := Function.uncurry (E g)) hq
      rw [hD2, hD2']
      have hV1 := hVfun z hzI θ hθI
      have hV2 := hVfun z' hzI' θ' hθI'
      have hcoef : 0 ≤ (6 * Cb + (Km + b * Cb + 3 * b ^ 2 * Cb) / a ^ 3 + Kh + 8 * Cb + 1)
          * Xn6 α g := by
        have : 0 ≤ (6 * Cb + (Km + b * Cb + 3 * b ^ 2 * Cb) / a ^ 3 + Kh + 8 * Cb + 1) := by
          linarith [hCb.le, hKh.le, hC₃nn]
        exact mul_nonneg this hXnn
      calc ‖iteratedFDeriv ℝ 2 (Function.uncurry (E g)) (z, θ)
            - iteratedFDeriv ℝ 2 (Function.uncurry (E g)) (z', θ')‖
          ≤ ‖iteratedFDeriv ℝ 2 (Function.uncurry (E g)) (z, θ)‖
            + ‖iteratedFDeriv ℝ 2 (Function.uncurry (E g)) (z', θ')‖ := norm_sub_le _ _
        _ ≤ 4 * (Cb * Xn6 α g) + 4 * (Cb * Xn6 α g) := add_le_add hV1 hV2
        _ ≤ (6 * Cb + (Km + b * Cb + 3 * b ^ 2 * Cb) / a ^ 3 + Kh + 8 * Cb + 1) * Xn6 α g := by
              nlinarith [hXnn, hCb.le, hC₃nn, hKh.le]
        _ ≤ (6 * Cb + (Km + b * Cb + 3 * b ^ 2 * Cb) / a ^ 3 + Kh + 8 * Cb + 1) * Xn6 α g
              * ‖(z, θ) - (z', θ')‖ ^ (min βh 1) := by
              calc (6 * Cb + (Km + b * Cb + 3 * b ^ 2 * Cb) / a ^ 3 + Kh + 8 * Cb + 1) * Xn6 α g
                  = (6 * Cb + (Km + b * Cb + 3 * b ^ 2 * Cb) / a ^ 3 + Kh + 8 * Cb + 1)
                    * Xn6 α g * 1 := by ring
                _ ≤ (6 * Cb + (Km + b * Cb + 3 * b ^ 2 * Cb) / a ^ 3 + Kh + 8 * Cb + 1)
                    * Xn6 α g * ‖(z, θ) - (z', θ')‖ ^ (min βh 1) :=
                    mul_le_mul_of_nonneg_left hR1 hcoef

end Work.FTS_EllLimOK.ProducerH.H2
