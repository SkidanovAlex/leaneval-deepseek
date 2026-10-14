import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.Prop.l0_first
import Submission.Work.FTS.GalBasis.hk_sq_api
import Submission.Work.FTS.GalFields.RHS.SharpAux.HonTerms.Base
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS.LocDataExt.Zfar5
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS.StrongGlobal.Global
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS_EllLimOK.BoxDataH.BoxUniform
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.PkgRepair
import Submission.Work.FTS_EllLimOK.RulingELF
import Submission.Work.FTS_EllLimOK.SlotSup.slot_jets_sup_le
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sin_two_rpow
-- ===== merged: Submission.Work.FTS_EllLimOK.BoxDataH.boxUniform2_of_pkgBoxH =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.BoxDataH

theorem boxUniform2_of_pkgBoxH {α : ℝ} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hbox : Work.FTS_EllLimOK.RulingELF.PkgBoxH α E)
    {a b B : ℝ} (ha : 0 < a) (hab : a < b) {fn : ℕ → Work.FTS.Galerkin.Fn}
    (hclass : ∀ n, Work.FTS.ClassC.ClassC α (fn n))
    (hB : ∀ n, Work.FTS.StrongGlobal.Xn6 α (fn n) ≤ B) :
    Work.FTS_EllLimOK.BoxDataH.BoxUniform2 a b (fun n z θ => E (fn n) z θ) := by
  obtain ⟨K, β, hK, hβ, hb⟩ := hbox a b ha hab.le
  refine ⟨K * max B 0 + 1, β, hβ, ?_, ?_, ?_⟩
  · intro n
    exact (hb (fn n) (hclass n)).1
  · intro n k hk p hp
    have h2 : Work.FTS.StrongGlobal.Xn6 α (fn n) ≤ max B 0 := le_trans (hB n) (le_max_left _ _)
    have hle : K * Work.FTS.StrongGlobal.Xn6 α (fn n) ≤ K * max B 0 :=
      mul_le_mul_of_nonneg_left h2 hK.le
    calc ‖iteratedFDerivWithin ℝ k (Function.uncurry (E (fn n))) (cbox a b) p‖
        ≤ K * Work.FTS.StrongGlobal.Xn6 α (fn n) := (hb (fn n) (hclass n)).2.1 hab k hk p hp
      _ ≤ K * max B 0 := hle
      _ ≤ K * max B 0 + 1 := by linarith
  · intro n p hp q hq
    have h2 : Work.FTS.StrongGlobal.Xn6 α (fn n) ≤ max B 0 := le_trans (hB n) (le_max_left _ _)
    have hr : (0 : ℝ) ≤ ‖p - q‖ ^ β := Real.rpow_nonneg (norm_nonneg _) _
    have hle : K * Work.FTS.StrongGlobal.Xn6 α (fn n) ≤ K * max B 0 :=
      mul_le_mul_of_nonneg_left h2 hK.le
    calc ‖iteratedFDerivWithin ℝ 2 (Function.uncurry (E (fn n))) (cbox a b) p
          - iteratedFDerivWithin ℝ 2 (Function.uncurry (E (fn n))) (cbox a b) q‖
        ≤ K * Work.FTS.StrongGlobal.Xn6 α (fn n) * ‖p - q‖ ^ β :=
          (hb (fn n) (hclass n)).2.2 hab p hp q hq
      _ ≤ (K * max B 0) * ‖p - q‖ ^ β := mul_le_mul_of_nonneg_right hle hr
      _ ≤ (K * max B 0 + 1) * ‖p - q‖ ^ β := mul_le_mul_of_nonneg_right (by linarith) hr

end Work.FTS_EllLimOK.BoxDataH
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.H2.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH.H2

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The standing hypothesis** of the L3 producer: for every class-`C` profile `g` the
operator `E` produces a stream function `Ψ = E g` carrying the level-`8` existence class and
the two frozen packages (at the given constants `α`, `Ce`). -/
abbrev Ctx (α Ce : ℝ) (E : Fn →ₗ[ℝ] Fn) : Prop :=
  ∀ g : Fn, Work.FTS.ClassC.ClassC α g →
    Work.FTS.EllExist.EllClassOk 8 α g (E g) ∧
      Work.FTS.VocabO.EllPkgGo α Ce g (E g) ∧
      Work.FTS.ClassC.EllPkgK α 6 Ce g (E g)

/-- The angular distance `mm θ = min θ (π/2 - θ)` to the nearer endpoint. -/
def mm (θ : ℝ) : ℝ := min θ (π / 2 - θ)


theorem mm_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) : 0 < mm θ :=
  lt_min hθ.1 (by linarith [hθ.2])

theorem mm_le_theta (θ : ℝ) : mm θ ≤ θ := min_le_left _ _

theorem mm_le_pi_sub (θ : ℝ) : mm θ ≤ π / 2 - θ := min_le_right _ _

theorem mm_le_one {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (π / 2)) : mm θ ≤ 1 := by
  have hπ : π / 2 ≤ 1 ∨ True := Or.inr trivial
  rcases le_total θ (π / 2 - θ) with h | h
  · rw [mm, min_eq_left h]
    nlinarith [hθ.2, Real.pi_lt_four]
  · rw [mm, min_eq_right h]
    nlinarith [Real.pi_lt_four]


theorem Xn6_nonneg (α : ℝ) (g : Fn) : 0 ≤ Work.FTS.StrongGlobal.Xn6 α g :=
  Work.Spaces.HkNorm_nonneg α 6 g

end Work.FTS_EllLimOK.ProducerH.H2
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.H2.Support.extend_holder_from_interior =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH.H2.Support

open scoped Topology
open Filter Set

set_option autoImplicit false

/-- **Hölder continuity extends from a dense subset.**  If `F` is continuous on `s` and
`β`-Hölder (with constant `K`) on a subset `t ⊆ s` whose closure contains `s`, then `F` is
`β`-Hölder with the same constant on all of `s`.

The proof picks, for `p, q ∈ s`, sequences `u n, v n ∈ t` with `u n → p`, `v n → q`
(Fréchet–Urysohn), applies the interior bound and passes to the limit: both sides converge,
using the continuity of `F` on `s` and of `x ↦ x ^ β` at nonnegative points. -/
theorem holderOn_of_dense {X : Type*} [NormedAddCommGroup X] [FrechetUrysohnSpace X]
    {E : Type*} [NormedAddCommGroup E] {F : X → E} {t s : Set X} {K β : ℝ}
    (hβ : 0 < β) (hts : t ⊆ s) (hdense : s ⊆ closure t) (hcont : ContinuousOn F s)
    (hint : ∀ p ∈ t, ∀ q ∈ t, ‖F p - F q‖ ≤ K * ‖p - q‖ ^ β) :
    ∀ p ∈ s, ∀ q ∈ s, ‖F p - F q‖ ≤ K * ‖p - q‖ ^ β := by
  intro p hp q hq
  obtain ⟨u, hu_mem, hu_tend⟩ := mem_closure_iff_seq_limit.mp (hdense hp)
  obtain ⟨v, hv_mem, hv_tend⟩ := mem_closure_iff_seq_limit.mp (hdense hq)
  have hu_s : ∀ n, u n ∈ s := fun n => hts (hu_mem n)
  have hv_s : ∀ n, v n ∈ s := fun n => hts (hv_mem n)
  have huW : Tendsto u atTop (𝓝[s] p) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within u hu_tend
      (Eventually.of_forall hu_s)
  have hvW : Tendsto v atTop (𝓝[s] q) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within v hv_tend
      (Eventually.of_forall hv_s)
  have hlhs : Tendsto (fun n => ‖F (u n) - F (v n)‖) atTop (𝓝 ‖F p - F q‖) :=
    ((Filter.Tendsto.comp (hcont.continuousWithinAt hp) huW).sub
      (Filter.Tendsto.comp (hcont.continuousWithinAt hq) hvW)).norm
  have hrhs : Tendsto (fun n => K * ‖u n - v n‖ ^ β) atTop (𝓝 (K * ‖p - q‖ ^ β)) :=
    (((Real.continuousAt_rpow_const (‖p - q‖) β (Or.inr hβ.le)).tendsto.comp
      ((hu_tend.sub hv_tend).norm))).const_mul K
  exact le_of_tendsto_of_tendsto' hlhs hrhs
    (fun n => hint (u n) (hu_mem n) (v n) (hv_mem n))

theorem extend_holder_from_interior {a b K β : ℝ}
    {E : Type*} [NormedAddCommGroup E] {F : ℝ × ℝ → E} (hab : a < b) (hβ : 0 < β)
    (hcont : ContinuousOn F (Work.FTS_EllLimOK.cbox a b))
    (hint : ∀ p ∈ (Set.Ioo a b ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)),
      ∀ q ∈ (Set.Ioo a b ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)),
      ‖F p - F q‖ ≤ K * ‖p - q‖ ^ β) :
    ∀ p ∈ Work.FTS_EllLimOK.cbox a b, ∀ q ∈ Work.FTS_EllLimOK.cbox a b,
      ‖F p - F q‖ ≤ K * ‖p - q‖ ^ β := by
  -- the open quadrant `(a,b) × (0,π/2)` is dense in the closed box `[a,b] × [0,π/2]`
  have hdense : Work.FTS_EllLimOK.cbox a b ⊆
      closure (Set.Ioo a b ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    rw [closure_prod_eq, closure_Ioo (ne_of_lt hab), closure_Ioo (ne_of_lt Real.pi_div_two_pos)]
    intro x hx
    simpa only [Work.FTS_EllLimOK.cbox] using hx
  refine holderOn_of_dense hβ ?_ hdense hcont hint
  intro x hx
  exact ⟨⟨hx.1.1.le, hx.1.2.le⟩, ⟨hx.2.1.le, hx.2.2.le⟩⟩

end Work.FTS_EllLimOK.ProducerH.H2.Support
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.H2.bounds_rates_aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH.H2

set_option autoImplicit false

/-! ## Elementary helpers for `bounds_rates`

The proof reduces every conjunct to one of three inputs:

* the radial rate `psiDz_rate` (`|D_z^j (E g)| ≤ C·𝓧·min θ (π/2-θ)`, `j ≤ 2`), which gives the
  plain `∂_z`-bounds after dividing by `z ≥ a₀`;
* the *plain* second angular derivatives `second_theta_deriv_le_Xn6` (`|∂_θ² (E g)| ≤ K·𝓧`) and
  `second_theta_deriv_DzIter_le_Xn6` (`|∂_θ² (D_z^a (E g))| ≤ K·𝓧`, `a ≤ 2`), which bound the
  angular derivatives of the mixed quantities; the mixed quantities themselves are then obtained
  from their value at the midpoint `θ = π/4` (where `sin 2θ = 1`) by the interpolation inequality
  `slice_interp`;
* the value at `θ = π/4`, where the normalised mixed jets `D_z^j D_θ^i` of `mixed_jets_le_Xn6`
  control the plain derivatives.
-/

/-- The midpoint `π/4` of the angular interval. -/
theorem br_quarter_mem : (π / 4 : ℝ) ∈ Set.Ioo (0 : ℝ) (π / 2) :=
  ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

/-- `|a - b| ≤ |a| + |b|`. -/
theorem br_abs_sub_le_abs_add_abs (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rw [abs_sub_le_iff]
  constructor <;> linarith [le_abs_self a, neg_le_abs a, le_abs_self b, neg_le_abs b]

/-- `sin (2·(π/4)) = 1`. -/
theorem br_sin_two_quarter : Real.sin (2 * (π / 4)) = 1 := by
  rw [show 2 * (π / 4) = π / 2 from by ring, Real.sin_pi_div_two]

/-- `D_z^j (D_θ f) = sin(2θ) · D_z^j (∂_θ f)`: the angular normalisation commutes with the
radial iterates. -/
theorem br_dzIter_dth_eq (f : ℝ → ℝ → ℝ) (j : ℕ) :
    Work.Spaces.DzIter j (Work.Spaces.Dth f)
      = fun z θ => Real.sin (2 * θ) * Work.Spaces.DzIter j (Work.Spaces.pth f) z θ := by
  induction j with
  | zero => rfl
  | succ k ih =>
      funext z θ
      show z * deriv (fun z' => Work.Spaces.DzIter k (Work.Spaces.Dth f) z' θ) z
        = Real.sin (2 * θ)
            * (z * deriv (fun z' => Work.Spaces.DzIter k (Work.Spaces.pth f) z' θ) z)
      have hfun : (fun z' => Work.Spaces.DzIter k (Work.Spaces.Dth f) z' θ)
          = fun z' => Real.sin (2 * θ) * Work.Spaces.DzIter k (Work.Spaces.pth f) z' θ := by
        funext z'
        exact congrFun (congrFun ih z') θ
      rw [hfun, deriv_const_mul_field]
      ring

/-- At the midpoint, the normalised mixed jet `D_z^j D_θ f` is the plain iterate
`D_z^j (∂_θ f)`. -/
theorem br_mixed_quarter_eq (f : ℝ → ℝ → ℝ) (j : ℕ) (z : ℝ) :
    Work.Spaces.mixed j 1 f z (π / 4) = Work.Spaces.DzIter j (Work.Spaces.pth f) z (π / 4) := by
  have h := congrFun (congrFun (br_dzIter_dth_eq f j) z) (π / 4)
  rw [br_sin_two_quarter, one_mul] at h
  exact h

/-- At the midpoint, the plain angular derivative is the normalised one. -/
theorem br_pth_quarter_eq (f : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Spaces.pth f z (π / 4) = Work.Spaces.mixed 0 1 f z (π / 4) := by
  show Work.Spaces.pth f z (π / 4)
    = Real.sin (2 * (π / 4)) * Work.Spaces.pth f z (π / 4)
  rw [br_sin_two_quarter, one_mul]

/-- The interpolation inequality: a function on `(0,π/2)` whose derivative is bounded by `C` is
bounded by its value at `π/4` plus `C·(π/2)`. -/
theorem br_slice_interp {f : ℝ → ℝ} {C : ℝ}
    (hd : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), DifferentiableAt ℝ f θ)
    (hb : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), |deriv f θ| ≤ C)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    |f θ| ≤ |f (π / 4)| + C * (π / 2) := by
  have hq : (π / 4 : ℝ) ∈ Set.Ioo (0 : ℝ) (π / 2) := br_quarter_mem
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hb (π / 4) hq)
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.Ioo (0 : ℝ) (π / 2))
    hd hb (convex_Ioo 0 (π / 2)) hθ hq
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
  have hdist : |π / 4 - θ| ≤ π / 2 := by
    rw [abs_le]; constructor <;> linarith [hθ.1, hθ.2, Real.pi_pos]
  have h5 : |f θ - f (π / 4)| ≤ C * (π / 2) := by
    have h5' : |f (π / 4) - f θ| ≤ C * (π / 2) :=
      le_trans h (mul_le_mul_of_nonneg_left hdist hC0)
    rwa [abs_sub_comm] at h5'
  have hsplit : f θ = (f θ - f (π / 4)) + f (π / 4) := by ring
  calc |f θ| = |(f θ - f (π / 4)) + f (π / 4)| := by conv_lhs => rw [hsplit]
    _ ≤ |f θ - f (π / 4)| + |f (π / 4)| := abs_add_le _ _
    _ ≤ C * (π / 2) + |f (π / 4)| := by linarith
    _ = |f (π / 4)| + C * (π / 2) := by ring

/-- `∂_θ²` of `θ ↦ c·h(z,θ)` (`c` independent of `θ`). -/
theorem br_deriv_deriv_const_mul (c z θ : ℝ) (h : ℝ → ℝ → ℝ) :
    deriv (deriv (fun θ' => c * h z θ')) θ = c * deriv (deriv (fun θ' => h z θ')) θ := by
  have h1 : ∀ x : ℝ, deriv (fun θ' => c * h z θ') x = c * deriv (fun θ' => h z θ') x :=
    fun x => deriv_const_mul_field (v := fun θ' => h z θ') (x := x) c
  show deriv (fun θ' => deriv (fun θ'' => c * h z θ'') θ') θ
    = c * deriv (fun θ' => deriv (fun θ'' => h z θ'') θ') θ
  rw [show (fun θ' => deriv (fun θ'' => c * h z θ'') θ')
      = fun θ' => c * deriv (fun θ'' => h z θ'') θ' from funext h1]
  exact deriv_const_mul_field (v := fun θ' => deriv (fun θ'' => h z θ'') θ') (x := θ) c

/-- Second-order congruence of the slice derivatives on the open interval. -/
theorem br_deriv_deriv_congr_slice {F G : ℝ → ℝ} {θ : ℝ}
    (h : ∀ θ' ∈ Set.Ioo (0 : ℝ) (π / 2), F θ' = G θ')
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) : deriv (deriv F) θ = deriv (deriv G) θ := by
  have h1 : deriv F =ᶠ[𝓝 θ] deriv G := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    exact Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hθ') h)
  exact Filter.EventuallyEq.deriv_eq h1

/-- First-order congruence of the slice derivatives on the open interval. -/
theorem br_deriv_congr_slice {F G : ℝ → ℝ} {θ : ℝ}
    (h : ∀ θ' ∈ Set.Ioo (0 : ℝ) (π / 2), F θ' = G θ')
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) : deriv F θ = deriv G θ :=
  Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hθ) h)

/-- Clairaut for the plain slice derivatives, in the open-quadrant class. -/
theorem br_pz_pth_eq_of_smoothOpen {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    Work.Spaces.pz (Work.Spaces.pth f) z θ = Work.Spaces.pth (Work.Spaces.pz f) z θ := by
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have h2 : ContDiffAt ℝ 2 (Function.uncurry f) (z, θ) :=
    (hf.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)).of_le
      (by simp [Work.Stability.smoothOrder])
  exact Work.FTS.GalBasis.GalApprox.pzIter_pthIter_comm h2 1 1 (by norm_num)

/-- Clairaut at the second radial order. -/
theorem br_pzIter_two_pth_comm_of_smoothOpen {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    Work.Spaces.pzIter 2 (Work.Spaces.pth f) z θ
      = Work.Spaces.pth (Work.Spaces.pzIter 2 f) z θ := by
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have h3 : ContDiffAt ℝ 3 (Function.uncurry f) (z, θ) :=
    (hf.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)).of_le
      (by simp [Work.Stability.smoothOrder])
  exact Work.FTS.GalBasis.GalApprox.pzIter_pthIter_comm h3 2 1 (by norm_num)

/-- The comparison `x ≤ A / c` from `z·x ≤ A`, for `0 < c ≤ z`. -/
theorem br_le_div_const {x A z c : ℝ} (hz : 0 < z) (hA : 0 ≤ A) (hc : 0 < c) (hcz : c ≤ z)
    (h : z * x ≤ A) : x ≤ A / c := by
  have hx : x ≤ A / z := by
    rw [le_div_iff₀ hz]
    calc x * z = z * x := by ring
      _ ≤ A := h
  rw [le_div_iff₀ hc]
  calc x * c ≤ (A / z) * c := mul_le_mul_of_nonneg_right hx hc.le
    _ = A * c / z := by ring
    _ ≤ A * z / z := by
        apply div_le_div_of_nonneg_right _ hz.le
        exact mul_le_mul_of_nonneg_left hcz hA
    _ = A := by field_simp

/-- Squeezing a bound `a ≤ A·𝓧·f₀` into `a ≤ C·𝓧·f₁`. -/
theorem br_squeeze_rate {a A C X f₀ f₁ : ℝ} (h : a ≤ A * X * f₀) (hA0 : 0 ≤ A)
    (hA : A ≤ C) (hX : 0 ≤ X) (hf₀ : 0 ≤ f₀) (hf : f₀ ≤ f₁) : a ≤ C * X * f₁ := by
  have hC0 : 0 ≤ C := le_trans hA0 hA
  calc a ≤ A * X * f₀ := h
    _ ≤ C * X * f₀ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA hX) hf₀
    _ ≤ C * X * f₁ := mul_le_mul_of_nonneg_left hf (mul_nonneg hC0 hX)

/-- Squeezing a bound `a ≤ A·𝓧` into `a ≤ C·𝓧`. -/
theorem br_squeeze_plain {a A C X : ℝ} (h : a ≤ A * X) (hA0 : 0 ≤ A) (hA : A ≤ C)
    (hX : 0 ≤ X) : a ≤ C * X := le_trans h (mul_le_mul_of_nonneg_right hA hX)


end Work.FTS_EllLimOK.ProducerH.H2
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.pkgCos_of_ellClassOk =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FTS_EllLimOK.ProducerH.pkgCos_of_ellClassOk` — producer `L1` of `HasPkgH`

The pinning field `PkgCos α E := ∀ g ∈ ClassC α, HkMem α 0 (PhiTil α g (E g) / cos θ)` of the
repaired package `HasPkgH` (`RulingELF`), derived from the level-`8` existence class
`∀ g ∈ ClassC, EllClassOk 8 α g (E g)`.

## Route

Fix `g ∈ ClassC α` and put `Ψ := E g`, so that `EllClassOk 8 α g Ψ` gives

* `IsBslSol α g Ψ` (the law, the Dirichlet data and the decay),
* `SmoothOpen Ψ` (honest `C^∞` on the open quadrant),
* `EllWeakPos α 8 (orthSource g) (shiftSing α g Ψ)`.

* **The shifted unknown is in `ℋ⁰`** after division by `cos θ`.  The weak class descends to
  level `0` (`EllWeakPos_descend`), and the *proved* first-order Step 1 of `prop:L2`
  (`Prop.l0_first`) gives `HkMem α 0 (shiftSing α g Ψ / cos θ)`.
* **The singular part of the shift is in `ℋ⁰`**.  Writing `Gsing = Gstar + Gbar` with
  `Gstar α g = -(1/(4α))·L₁₂ g`, the exact identity
  `shiftSing α g Ψ = PhiTil α g Ψ + Gbar α g · sin 2θ` holds, so on the open quadrant
  `PhiTil / cos θ = shiftSing / cos θ - 2·Gbar·sin θ`.
* The `Gbar`-term is handled by the *weighted Hardy bound* of the `GbarLayer` certificate
  (`layer_Gbar_rDzIter_bound`): `∫_0^∞ w² Ḡ² < ∞`, which is exactly the hypothesis of the
  membership `HkMem α 0 (2·Ḡ·sin θ)` proved here by domination with the majorant
  `8 w² Ḡ² sin(2θ)^{-η}` (`sin(2θ)^{-η}` is integrable on `Iθ` because `η = 99/100 < 1`).
* `HkMem α 0` is then closed under subtraction (`GalBasis.hkMem_sub_open`, whose two
  `SmoothOpen` hypotheses hold: `shiftSing/cos` is smooth by `gsing_certs_classC` +
  `smoothOpen_div_cos`, and `2·Ḡ·sin θ` is smooth by `sep_mul`), and the integrands of
  `PhiTil/cos` and of `shiftSing/cos - 2·Ḡ·sin θ` agree pointwise (at `θ = π/2`, where `1/cos`
  is junk and the two functions differ, the angular factor `w z / sin(2θ)^{η/2}` vanishes).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH

set_option autoImplicit false

/-! ## The algebraic identities -/

/-- **The exact identity `PhiTil α g Ψ = shiftSing α g Ψ - Gbar α g · sin 2θ`.**  It is the
definitional bookkeeping `Gsing = Gstar + Gbar`, `Gstar = -(1/(4α))·L₁₂`,
`Theta = (1/(4α))·sin 2θ·L₁₂`, and it holds for *all* `z, θ` (no division). -/
private theorem phiTil_eq_shiftSing_sub (α : ℝ) (g Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Construction.PhiTil α g Ψ z θ
      = Work.FTS.EllExist.shiftSing α g Ψ z θ
        - Work.Elliptic.Gbar α g z * Real.sin (2 * θ) := by
  have hL : Work.Construction.L12 g z = Work.Elliptic.L12 g z := by
    rw [Work.Construction.L12, Work.Elliptic.L12_eq_FM]
    rfl
  rw [Work.FTS.EllExist.shiftSing_apply, Work.Construction.PhiTil, Work.Construction.Theta,
      Work.Elliptic.Gsing, Work.Elliptic.Gstar, Work.Construction.s2, hL]
  ring

/-! ## The `ℋ⁰`-integrand at level `0` -/

/-- At level `0` the `ℋ⁰`-integrand has exactly one summand. -/
private theorem hkIntegrand_zero_unfold (α : ℝ) (X : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 X z θ
      = (X z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp only [Work.Spaces.HkIntegrand]
  norm_num

/-- Two functions whose *weighted* values agree at `(z,θ)` have the same `ℋ⁰`-integrand there. -/
private theorem hkIntegrand_zero_congr {α : ℝ} {X Y : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : X z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
       = Y z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) :
    Work.Spaces.HkIntegrand α 0 X z θ = Work.Spaces.HkIntegrand α 0 Y z θ := by
  rw [hkIntegrand_zero_unfold α X z θ, hkIntegrand_zero_unfold α Y z θ, h]

/-- **`HkMem` only depends on the `ℋ^k`-integrand.** -/
private theorem hkMem_congr_integrand {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ, Work.Spaces.HkIntegrand α k f z θ = Work.Spaces.HkIntegrand α k g z θ)
    (hf : Work.Spaces.HkMem α k f) : Work.Spaces.HkMem α k g := by
  constructor
  · intro z hz
    exact (hf.1 z hz).congr (Filter.Eventually.of_forall fun θ => h z θ)
  · refine hf.2.congr (Filter.Eventually.of_forall fun z => ?_)
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => h z θ)

/-! ## The angular weight -/

private theorem sq_div_rpow (w s : ℝ) (hs : 0 ≤ s) :
    (w / s ^ (Work.Spaces.eta / 2)) ^ 2 = w ^ 2 * s ^ (-(Work.Spaces.eta)) := by
  have hb : (s ^ (Work.Spaces.eta / 2)) ^ 2 = s ^ Work.Spaces.eta := by
    rw [← Real.rpow_natCast, show ((2 : ℕ) : ℝ) = 2 by norm_num]
    rw [← Real.rpow_mul hs (Work.Spaces.eta / 2) (2 : ℝ)]
    norm_num
  rw [div_pow, hb, Real.rpow_neg hs]
  ring

/-- The pointwise domination of the `ℋ⁰`-integrand of `2·R(z)·sin θ` by
`8·w(z)²·R(z)²·sin(2θ)^{-η}`: the angular factor is `4 sin²θ ≤ 4`. -/
private theorem bound_two_mul_sin {wz Rz s θ : ℝ} (hs : 0 ≤ s) :
    (2 * Rz * Real.sin θ * (wz / s ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ 8 * wz ^ 2 * Rz ^ 2 * s ^ (-(Work.Spaces.eta)) := by
  have h1 : (wz / s ^ (Work.Spaces.eta / 2)) ^ 2 = wz ^ 2 * s ^ (-(Work.Spaces.eta)) :=
    sq_div_rpow wz s hs
  have h2 : (2 * Rz * Real.sin θ * (wz / s ^ (Work.Spaces.eta / 2))) ^ 2
      = 4 * Rz ^ 2 * Real.sin θ ^ 2 * (wz / s ^ (Work.Spaces.eta / 2)) ^ 2 := by ring
  rw [h2, h1]
  have h3 : Real.sin θ ^ 2 ≤ 1 := Real.sin_sq_le_one θ
  have h4 : 0 ≤ s ^ (-(Work.Spaces.eta)) := Real.rpow_nonneg hs _
  have hR : (0 : ℝ) ≤ Rz ^ 2 := sq_nonneg Rz
  have hW : (0 : ℝ) ≤ wz ^ 2 := sq_nonneg wz
  have h5 : 4 * Rz ^ 2 * Real.sin θ ^ 2 * (wz ^ 2 * s ^ (-(Work.Spaces.eta)))
      ≤ 4 * Rz ^ 2 * 1 * (wz ^ 2 * s ^ (-(Work.Spaces.eta))) := by
    have h6 : (0 : ℝ) ≤ 4 * Rz ^ 2 := by linarith
    have h7 : (0 : ℝ) ≤ wz ^ 2 * s ^ (-(Work.Spaces.eta)) := mul_nonneg hW h4
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 h6) h7
  have h9 : 4 * Rz ^ 2 * 1 * (wz ^ 2 * s ^ (-(Work.Spaces.eta)))
      ≤ 8 * wz ^ 2 * Rz ^ 2 * s ^ (-(Work.Spaces.eta)) := by
    have h10 : (0 : ℝ) ≤ Rz ^ 2 * wz ^ 2 * s ^ (-(Work.Spaces.eta)) :=
      mul_nonneg (mul_nonneg hR hW) h4
    nlinarith [h10]
  linarith [h5, h9]

/-! ## The membership `HkMem α 0 (2·R·sin θ)` -/

/-- **`2·R(z)·sin θ ∈ ℋ⁰`** for a radial `R` that is `C^∞` on `(0,∞)` and has
`∫_0^∞ w² R² < ∞`.  This is the Hardy-type input supplied by the `GbarLayer` certificate for
`R = Gbar α g`: the angular weight `sin(2θ)^{-η}` is integrable on `Iθ` (`η < 1`), so the
majorant `8 w² R² sin(2θ)^{-η}` has integrable slices and integrable slice-integral. -/
private theorem hkMem_two_mul_sin {α : ℝ} {R : ℝ → ℝ}
    (hRsm : ∀ m : ℕ, ContDiffOn ℝ m R (Set.Ioi 0))
    (hint : MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (R z) ^ 2) Work.Spaces.Iz) :
    Work.Spaces.HkMem α 0 (fun z θ => 2 * R z * Real.sin θ) := by
  have heta1 : -1 < -(Work.Spaces.eta) := by rw [Work.Spaces.eta]; norm_num
  have heta0 : -(Work.Spaces.eta) ≤ 0 := by rw [Work.Spaces.eta]; norm_num
  have hsinInt : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
    (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) heta1 heta0).1
  have hSm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => 2 * R z * Real.sin θ) := by
    have hsep := Work.FTS.EllipticEst.SmoothOpen.sep_mul (g := R)
      (χ := fun θ : ℝ => 2 * Real.sin θ) hRsm (by fun_prop)
    have hfun : (fun z θ : ℝ => R z * (2 * Real.sin θ))
        = fun z θ : ℝ => 2 * R z * Real.sin θ := by
      funext z θ; ring
    rwa [hfun] at hsep
  refine Work.FTS.LocData.HkMem_of_majorant α 0
    (f := fun z θ => 2 * R z * Real.sin θ)
    (M := fun z θ => 8 * (Work.Spaces.w z) ^ 2 * (R z) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
    (hSm.continuousOn_HkIntegrand α 0) ?_ ?_ ?_
  · intro z _
    have h := hsinInt.const_mul (8 * (Work.Spaces.w z) ^ 2 * (R z) ^ 2)
    refine MeasureTheory.IntegrableOn.congr_fun h (fun θ _ => by ring) measurableSet_Icc
  · have hMfun : (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        8 * (Work.Spaces.w z) ^ 2 * (R z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        = fun z : ℝ =>
            (8 * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
              * ((Work.Spaces.w z) ^ 2 * (R z) ^ 2) := by
      funext z
      rw [show (fun θ : ℝ => 8 * (Work.Spaces.w z) ^ 2 * (R z) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          = fun θ : ℝ => (8 * (Work.Spaces.w z) ^ 2 * (R z) ^ 2)
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) from by funext θ; ring]
      rw [MeasureTheory.integral_const_mul]
      ring
    rw [hMfun]
    exact hint.const_mul _
  · intro z _ θ hθ
    have hs : 0 ≤ Real.sin (2 * θ) := by
      refine Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], ?_⟩
      have := hθ.2; linarith [Real.pi_pos]
    rw [hkIntegrand_zero_unfold]
    exact bound_two_mul_sin hs

/-! ## Smoothness of the shifted unknown divided by `cos θ` -/

/-- `shiftSing α g Ψ / cos θ` is `C^∞` on the open quadrant: `shiftSing α g Ψ = Ψ + Gsing·sin 2θ`
with `Gsing α g` of class `C^∞` on `(0,∞)` (`gsing_certs_classC`), and `cos θ ≠ 0` on `Q0`. -/
private theorem smoothOpen_shiftSing_div_cos {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {g : Work.FTS.Galerkin.Fn} (hg : Work.FTS.ClassC.ClassC α g) {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.FTS.EllExist.shiftSing α g Ψ z θ / Real.cos θ) := by
  have hGsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gsing α g) (Set.Ioi 0) :=
    (Work.FTS.ClassC.gsing_certs_classC hα hα1 hg).2.1
  have hsep : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Elliptic.Gsing α g z * Real.sin (2 * θ)) :=
    Work.FTS.EllipticEst.SmoothOpen.sep_mul (g := Work.Elliptic.Gsing α g)
      (χ := fun θ : ℝ => Real.sin (2 * θ)) hGsm (by fun_prop)
  have hsum : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Ψ z θ + Work.Elliptic.Gsing α g z * Real.sin (2 * θ)) :=
    Work.FTS.EllipticEst.smoothOpen_add hΨ hsep
  have h2 : (fun z θ : ℝ => Work.FTS.EllExist.shiftSing α g Ψ z θ / Real.cos θ)
      = fun z θ : ℝ => (Ψ z θ + Work.Elliptic.Gsing α g z * Real.sin (2 * θ)) / Real.cos θ := by
    funext z θ
    rw [Work.FTS.EllExist.shiftSing_apply]
  rw [h2]
  exact Work.FTS_EllLimOK.Pinning.smoothOpen_div_cos hsum

/-! ## The producer -/

theorem pkgCos_of_ellClassOk :
    ∃ α₁ : ℝ, 0 < α₁ ∧ ∀ α : ℝ, 0 < α → α ≤ α₁ →
      ∀ E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn,
        (∀ g : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α g →
          Work.FTS.EllExist.EllClassOk 8 α g (E g)) →
        Work.FTS_EllLimOK.PkgCos α E := by
  refine ⟨1 / 4, by norm_num, ?_⟩
  intro α hα hα4 E hE g hg
  have hα1 : α ≤ 1 := by linarith
  -- the level-`8` existence class of `E g`
  have hΨsm : Work.FTS.EllipticEst.SmoothOpen (E g) := (hE g hg).2.1
  have hw8 : Work.FTS.EllipticEst.TT.EllWeakPos α 8 (Work.Elliptic.orthSource g)
      (Work.FTS.EllExist.shiftSing α g (E g)) := (hE g hg).2.2
  -- `g ∈ ℋ⁰`
  have hg0 : Work.Spaces.HkMem α 0 g :=
    Work.FTS.EllipticEst.TT.HkMem_descend_open (k := 0) (l := 10) (by norm_num)
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall g).mp hg.reg) hg.mem10
  -- the weighted `L²`-integrability of `Ḡ(α,g)` (the Hardy bound of the `GbarLayer` certificate)
  have hGbarInt : MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (Work.Elliptic.Gbar α g z) ^ 2) Work.Spaces.Iz := by
    have h1 := (Work.FTS.EllipticEst.Cert.GbarLayer.layer_Gbar_rDzIter_bound α hα hα1 0 g
      hg.reg hg0 0 le_rfl).1
    simpa only [Work.FTS.EllipticEst.rDzIter_zero] using h1
  have hGbarSm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gbar α g) (Set.Ioi 0) :=
    (Work.FTS.ClassC.gsing_certs_classC hα hα1 hg).2.2.1
  have hGsin : Work.Spaces.HkMem α 0
      (fun z θ => 2 * Work.Elliptic.Gbar α g z * Real.sin θ) :=
    hkMem_two_mul_sin hGbarSm hGbarInt
  -- the weak class at level `0`
  have hw0 : Work.FTS.EllipticEst.TT.EllWeakPos α 0 (Work.Elliptic.orthSource g)
      (Work.FTS.EllExist.shiftSing α g (E g)) :=
    Work.FTS.EllSol.PkgK5.EllWeakPos_descend (l := 0) (K := 8) (by norm_num) hw8
  -- Step 1 of `prop:L2`: the shifted unknown divided by `cos θ` is in `ℋ⁰`
  obtain ⟨C, _, hl0⟩ := Work.FTS.EllipticEst.Prop.l0_first
  have hShift : Work.Spaces.HkMem α 0
      (fun z θ => Work.FTS.EllExist.shiftSing α g (E g) z θ / Real.cos θ) :=
    (hl0 α (Work.Elliptic.orthSource g) (Work.FTS.EllExist.shiftSing α g (E g))
      hα hα4 hw0).2.1
  -- smoothness of the two summands
  have hShiftSm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.FTS.EllExist.shiftSing α g (E g) z θ / Real.cos θ) :=
    smoothOpen_shiftSing_div_cos hα hα1 hg hΨsm
  have hGsinSm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => 2 * Work.Elliptic.Gbar α g z * Real.sin θ) := by
    have hsep := Work.FTS.EllipticEst.SmoothOpen.sep_mul (g := Work.Elliptic.Gbar α g)
      (χ := fun θ : ℝ => 2 * Real.sin θ) hGbarSm (by fun_prop)
    have hfun : (fun z θ : ℝ => Work.Elliptic.Gbar α g z * (2 * Real.sin θ))
        = fun z θ : ℝ => 2 * Work.Elliptic.Gbar α g z * Real.sin θ := by
      funext z θ; ring
    rwa [hfun] at hsep
  -- `PhiTil/cos` agrees with the difference of the two summands
  have hU : Work.Spaces.HkMem α 0
      (fun z θ => Work.FTS.EllExist.shiftSing α g (E g) z θ / Real.cos θ
        - 2 * Work.Elliptic.Gbar α g z * Real.sin θ) :=
    Work.FTS.GalBasis.hkMem_sub_open α 0 hShiftSm hGsinSm hShift hGsin
  refine hkMem_congr_integrand (α := α) (k := 0) ?_ hU
  intro z θ
  refine hkIntegrand_zero_congr ?_
  by_cases hcos : Real.cos θ = 0
  · -- `cos θ = 0`: the angular weight vanishes on both sides
    have hs : Real.sin (2 * θ) = 0 := by rw [Real.sin_two_mul, hcos]; ring
    have hc : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0 := by
      rw [hs, Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)]
    simp only [hc, div_zero, mul_zero]
  · -- `cos θ ≠ 0`: `PhiTil/cos = shiftSing/cos - 2·Ḡ·sin θ`
    have h1 : Work.Construction.PhiTil α g (E g) z θ / Real.cos θ
        = Work.FTS.EllExist.shiftSing α g (E g) z θ / Real.cos θ
          - 2 * Work.Elliptic.Gbar α g z * Real.sin θ := by
      rw [phiTil_eq_shiftSing_sub α g (E g) z θ, Work.FTS.EllExist.shiftSing_apply]
      field_simp [hcos]
      rw [Real.sin_two_mul]
      ring
    rw [h1]

end Work.FTS_EllLimOK.ProducerH
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.slotBd_phiTil =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH

/-- `SlotBd` for `Φ̃ = PhiTil α g (E g)`: the `U`-slot `Uprime α Φ̃ = Uop α Φ̃ / sin 2θ` and the
`V`-slot `Vop Φ̃` have sup bounds on the open quadrant in terms of the package's `ℋ⁶`-bounds.
Route: `EllPkgK α 6 Ce g (E g)` gives `HQo α 6` (i.e. `SmoothOpen ∧ HkMem α 6`) of both slots with
`HkNorm α 6 (slot) ≤ Ce * Xn6 α g`, and
`Work.FTS_EllLimOK.SlotSup.slot_jets_sup_le` gives `|D_z^b D_θ^a f| ≤ C(α) * HkNorm α 6 f` for
`a + b ≤ 4`; SlotBd needs `D_z^j Uprime` (j ≤ 2), `mixed 0 1 Uprime = D_θ U'`, and `D_z^j Vop`
(j ≤ 1).  Note `Uprime α Φ̃ = Uop α Φ̃ / s2` definitionally, and `mixed b 0 = DzIter b`. -/
theorem slotBd_phiTil {α Ce : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn) (g : Work.FTS.Galerkin.Fn),
      Work.FTS.ClassC.ClassC α g → Work.FTS.ClassC.EllPkgK α 6 Ce g (E g) →
      Work.FTS.StreamBdryIface.SlotBd α (Work.Construction.PhiTil α g (E g))
        (K * (Ce * Work.FTS.StrongGlobal.Xn6 α g)) := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS_EllLimOK.SlotSup.slot_jets_sup_le α hα hα1
  refine ⟨C, hCpos, ?_⟩
  intro E g hg hK
  -- The two slots are exactly the ones packaged by `EllPkgK α 6 Ce g (E g)`.
  have hUmem : Work.FTS.VocabO.HQo α 6 (fun z θ =>
      Work.Construction.Uop α (Work.Construction.PhiTil α g (E g)) z θ
        / Work.Construction.s2 θ) := hK.U.1
  have hVmem : Work.FTS.VocabO.HQo α 6
      (Work.Construction.Vop (Work.Construction.PhiTil α g (E g))) := hK.V.1
  have hUnorm : Work.Spaces.HkNorm α 6 (fun z θ =>
      Work.Construction.Uop α (Work.Construction.PhiTil α g (E g)) z θ
        / Work.Construction.s2 θ) ≤ Ce * Work.FTS.StrongGlobal.Xn6 α g := hK.U.2
  have hVnorm : Work.Spaces.HkNorm α 6
      (Work.Construction.Vop (Work.Construction.PhiTil α g (E g)))
        ≤ Ce * Work.FTS.StrongGlobal.Xn6 α g := hK.V.2
  -- `HkNorm ≥ 0`, so the package forces the scale factor to be nonnegative.
  have hMnn : 0 ≤ Ce * Work.FTS.StrongGlobal.Xn6 α g := by
    have h1 : (0 : ℝ) ≤ Work.Spaces.HkNorm α 6 (fun z θ =>
        Work.Construction.Uop α (Work.Construction.PhiTil α g (E g)) z θ
          / Work.Construction.s2 θ) := Work.Spaces.HkNorm_nonneg _ _ _
    linarith
  -- `Uprime` is the `U`-slot, definitionally.
  have hUeq : Work.FTS.StreamBdryIface.Uprime α (Work.Construction.PhiTil α g (E g))
      = (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α g (E g)) z θ
          / Work.Construction.s2 θ) := rfl
  intro z θ hzθ
  obtain ⟨hz, hθ0, hθ2⟩ : 0 < z ∧ 0 < θ ∧ θ < Real.pi / 2 := by
    simpa only [Work.Construction.Qd, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] using hzθ
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    have h := hC (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α g (E g)) z θ
        / Work.Construction.s2 θ) hUmem.1 hUmem.2 j 0 (by omega) z θ hz hθ0 hθ2
    have hb := mul_le_mul_of_nonneg_left hUnorm hCpos.le
    calc |Work.Spaces.DzIter j (Work.FTS.StreamBdryIface.Uprime α
          (Work.Construction.PhiTil α g (E g))) z θ|
        = |Work.Spaces.mixed j 0 (fun z θ => Work.Construction.Uop α
            (Work.Construction.PhiTil α g (E g)) z θ / Work.Construction.s2 θ) z θ| := by
          rw [hUeq, Work.Spaces.mixed_zero_right]
      _ ≤ C * Work.Spaces.HkNorm α 6 (fun z θ => Work.Construction.Uop α
            (Work.Construction.PhiTil α g (E g)) z θ / Work.Construction.s2 θ) := h
      _ ≤ C * (Ce * Work.FTS.StrongGlobal.Xn6 α g) := hb
  · have h := hC (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α g (E g)) z θ
        / Work.Construction.s2 θ) hUmem.1 hUmem.2 0 1 (by omega) z θ hz hθ0 hθ2
    have hb := mul_le_mul_of_nonneg_left hUnorm hCpos.le
    calc |Work.Spaces.mixed 0 1 (Work.FTS.StreamBdryIface.Uprime α
          (Work.Construction.PhiTil α g (E g))) z θ|
        = |Work.Spaces.mixed 0 1 (fun z θ => Work.Construction.Uop α
            (Work.Construction.PhiTil α g (E g)) z θ / Work.Construction.s2 θ) z θ| := by
          rw [hUeq]
      _ ≤ C * Work.Spaces.HkNorm α 6 (fun z θ => Work.Construction.Uop α
            (Work.Construction.PhiTil α g (E g)) z θ / Work.Construction.s2 θ) := h
      _ ≤ C * (Ce * Work.FTS.StrongGlobal.Xn6 α g) := hb
  · intro j hj
    have h := hC (Work.Construction.Vop (Work.Construction.PhiTil α g (E g)))
        hVmem.1 hVmem.2 j 0 (by omega) z θ hz hθ0 hθ2
    have hb := mul_le_mul_of_nonneg_left hVnorm hCpos.le
    calc |Work.Spaces.DzIter j (Work.Construction.Vop
          (Work.Construction.PhiTil α g (E g))) z θ|
        = |Work.Spaces.mixed j 0 (Work.Construction.Vop
            (Work.Construction.PhiTil α g (E g))) z θ| := by
          rw [Work.Spaces.mixed_zero_right]
      _ ≤ C * Work.Spaces.HkNorm α 6 (Work.Construction.Vop
            (Work.Construction.PhiTil α g (E g))) := h
      _ ≤ C * (Ce * Work.FTS.StrongGlobal.Xn6 α g) := hb

end Work.FTS_EllLimOK.ProducerH
end
