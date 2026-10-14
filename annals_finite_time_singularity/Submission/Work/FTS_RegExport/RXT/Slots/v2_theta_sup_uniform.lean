import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.regQo_const_mul
import Submission.Work.FTS.StrongPersist.L3Aux.bcoefRadBound
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_RegExport.C4.Dth_mixed_eq_C4
import Submission.Work.FTS_RegExport.RXA1w.Helpers
import Submission.Work.FTS_RegExport.THL.mixed_slice_pointwise_le_noTrace
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.EpsEngine.ZTracesAux.integrable_pth_sq_sin_gen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EpsEngine.ZTracesAux

/-- The angular integrand `(∂_θ(D_z^bD_θ^af)(s,·))² · sin(2·)^{2-γ}` is integrable on `Iθ`
as soon as `((D_z^bD_θ^{a+1}f)(s,·) · w(s))² sin(2·)^{-γ}` is dominated pointwise by
`HkIntegrand α m f s ·` and `∂_θ(D_z^bD_θ^af)` is identified with
`D_z^bD_θ^{a+1}f / sin(2·)` on the interior: on `(0,π/2)` one has
`(X/c)² c^{2-γ} = ((X·w)² c^{-γ}) / w²`, and the right-hand side is integrable because
`HkIntegrand α m f s ·` is (`hmem`) — the factor `w(s)² > 0` is a constant in `θ`. -/
theorem integrable_pth_sq_sin_gen {α : ℝ} {f : ℝ → ℝ → ℝ} {m : ℕ}
    (hmem : Work.Spaces.HkMem α m f) (b a : ℕ) {s : ℝ} (hs : 0 < s)
    (hcont : ContinuousOn (fun σ => Work.Spaces.pth (Work.Spaces.mixed b a f) s σ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hpoint : ∀ σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Work.Spaces.mixed b (a + 1) f s σ * Work.Spaces.w s) ^ 2
        * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) ≤ Work.Spaces.HkIntegrand α m f s σ)
    (hident : ∀ σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Spaces.pth (Work.Spaces.mixed b a f) s σ
        = Work.Spaces.mixed b (a + 1) f s σ / Real.sin (2 * σ)) :
    MeasureTheory.IntegrableOn
      (fun σ => (Work.Spaces.pth (Work.Spaces.mixed b a f) s σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
  have hsI : s ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hs.le
  have hsin_cont : ContinuousOn (fun σ : ℝ => Real.sin (2 * σ))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hu_cont : ContinuousOn
      (fun σ => (Work.Spaces.pth (Work.Spaces.mixed b a f) s σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (hcont.pow 2).mul (hsin_cont.rpow_const
      (fun σ hσ => Or.inl (ne_of_gt (Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ))))
  have hwne : (Work.Spaces.w s) ^ 2 ≠ 0 := by
    have h := Work.FTS_RegExport.RXT.Slots.w_pos_aux hs
    positivity
  refine (hmem.1 s hsI).div_const ((Work.Spaces.w s) ^ 2) |>.mono'
    (Work.FTS_RegExport.RXT.Slots.aesm_Iθ_of_continuousOn_Ioo_aux hu_cont) ?_
  filter_upwards [Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hσ
  have hsin : 0 < Real.sin (2 * σ) := Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin.le _)),
    hident σ hσ]
  have hkey : (Work.Spaces.mixed b (a + 1) f s σ / Real.sin (2 * σ)) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
      = ((Work.Spaces.mixed b (a + 1) f s σ * Work.Spaces.w s) ^ 2
          * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))) / (Work.Spaces.w s) ^ 2 := by
    have h1 : (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
        = (Real.sin (2 * σ)) ^ 2
          * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) := by
      rw [show (2 : ℝ) - Work.Spaces.gam α = 2 + (-(Work.Spaces.gam α)) by ring,
        Real.rpow_add hsin, Real.rpow_ofNat]
    rw [h1, div_pow, mul_pow, eq_div_iff hwne]
    field_simp
  rw [hkey]
  exact div_le_div_of_nonneg_right (hpoint σ hσ) (sq_nonneg _)

end Work.FTS.EpsEngine.ZTracesAux
end
end
-- ===== merged: Submission.Work.FTS.EpsEngine.ZTracesAux.integrable_slot_sq_gen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EpsEngine.ZTracesAux

/-- The `θ`-slice of the square of a mixed slot is integrable on `Iθ` once its `w`-weighted
square is dominated by the `ℋ^m`-integrand, whose `θ`-slice is integrable by `HkMem`.

The only analytic input is a.e. strong measurability of the slice, supplied by the continuity
hypothesis on the open interval `(0,π/2)` (which agrees with `Iθ` up to the null set of the
two endpoints). -/
theorem integrable_slot_sq_gen {α : ℝ} {f : ℝ → ℝ → ℝ} {m : ℕ}
    (hmem : Work.Spaces.HkMem α m f) (b a : ℕ) {s : ℝ} (hs : 0 < s)
    (hcont : ContinuousOn (fun σ => Work.Spaces.mixed b a f s σ) (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hpoint : ∀ σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Work.Spaces.mixed b a f s σ * Work.Spaces.w s) ^ 2 ≤ Work.Spaces.HkIntegrand α m f s σ) :
    MeasureTheory.IntegrableOn (fun σ => (Work.Spaces.mixed b a f s σ) ^ 2) Work.Spaces.Iθ := by
  have hsI : s ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hs.le
  refine (hmem.1 s hsI).div_const ((Work.Spaces.w s) ^ 2) |>.mono'
    (Work.FTS_RegExport.RXT.Slots.aesm_Iθ_of_continuousOn_Ioo_aux (hcont.pow 2)) ?_
  filter_upwards [Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hσ
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hwne : (Work.Spaces.w s) ^ 2 ≠ 0 := by
    have h := Work.FTS_RegExport.RXT.Slots.w_pos_aux hs
    positivity
  have hkey : (Work.Spaces.mixed b a f s σ) ^ 2
      = (Work.Spaces.mixed b a f s σ * Work.Spaces.w s) ^ 2 / (Work.Spaces.w s) ^ 2 := by
    rw [mul_pow, eq_div_iff hwne]
  rw [hkey]
  exact div_le_div_of_nonneg_right (hpoint σ hσ) (sq_nonneg _)

end Work.FTS.EpsEngine.ZTracesAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.EllPkgCls_sub =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EComparison

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The class `EllPkgCls` is closed under differences.**  If `(F₁, Ψ₁)` and `(F₂, Ψ₂)` are both
controlled by the packages, and the `L₁₂`-part of the source is additive
(`Theta α (F₁ - F₂) = Theta α F₁ - Theta α F₂` on the half-line `z ∈ Iz`, which is the content of
the delegated `EComparison.L12_sub_HkMem`), then so is the pair
`(F₁ - F₂, Ψ₁ - Ψ₂)`.

`EllPkgCls α Ce F Ψ` (in `Submission.Work.FTS.StrongEps.EComparison.Reduction`) is the membership
half of the two elliptic packages, with the packages' slot shape kept: `SmoothOpen Ψ`, the elliptic
law `IsBslSol α F Ψ`, and `HQo α 6` of `Rop α (PhiTil α F Ψ)`, of `Uop α (PhiTil α F Ψ) / sin 2θ`
and of `Vop (PhiTil α F Ψ)` (`HQo α 6 X = SmoothOpen X ∧ HkMem α 6 X`).  (An earlier form of the
class dropped the smoothness halves; a review pointed out that this blocks the closure, so the
`HQo` slots are the ones to use.)

Ingredients (all on disk, `sorry`-free):
* `SmoothOpen` is closed under subtraction (`Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_sub'`);
* `IsBslSol α (F₁ - F₂) (Ψ₁ - Ψ₂)` from `IsBslSol α F₁ Ψ₁`, `IsBslSol α F₂ Ψ₂`: the pointwise law is
  `Work.FTS.EllipticEst.bslOp_sub` (the `C²`-at-a-point hypotheses come from `SmoothOpen` of the two
  stream functions at a point of the open quadrant, and `Real.cos θ ≠ 0` holds there), and the two
  Dirichlet conjuncts and the `z`-decay conjunct are difference-stable;
* the three `ℋ⁶`-memberships and their smoothness: `PhiTil α (F₁ - F₂) (Ψ₁ - Ψ₂) = PhiTil α F₁ Ψ₁ -
  PhiTil α F₂ Ψ₂` by the hypothesis on `Theta` (and only on `z > 0`, where it is needed: the weights
  `Work.Spaces.w` and `Work.Spaces.Wt` vanish at `z = 0`, so `HkIntegrand α k f 0 θ = 0` for every
  `f`, and `HkSq α k`/`HkMem α k` see only `z ∈ Iz`), and `Rop α`, `Uop α`, `Vop` are additive in
  their argument at every point of the open quadrant.  The `pz`-additivity is *not* a consequence
  of the smoothness of the two `PhiTil`s (their `z`-regularity is not available: the `L₁₂`-part is
  an integral of the source over `(z,∞)`); it is supplied here by the `V`-slot, whose smoothness
  forces `z ↦ L₁₂(Fᵢ)(z)` to be differentiable on `(0,∞)` (`differentiableAt_L12_of_Vop`), and
  hence the `z`-derivative of `PhiTil α (F₁-F₂)(Ψ₁-Ψ₂)` to split.  `HQo α 6` of the difference then
  follows from `HQo α 6` of the two summands (`smoothOpen_sub_bsl` for the smoothness,
  `HkMem_sub_of_HkMem` for the membership, plus the open-quadrant congruence
  `Cert.GbarSin.HkMem_congr_Q0`).  The case `α = 0` is degenerate (`Theta 0 F = 0`, so
  `PhiTil 0 F Ψ = Ψ`) and is handled by `EllPkgCls_sub_zero`. -/
theorem EllPkgCls_sub {α Ce : ℝ} {F₁ F₂ Ψ₁ Ψ₂ : Work.FTS.Galerkin.Fn}
    (h₁ : Work.FTS.StrongEps.EComparison.EllPkgCls α Ce F₁ Ψ₁)
    (h₂ : Work.FTS.StrongEps.EComparison.EllPkgCls α Ce F₂ Ψ₂)
    (hΘ : ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      Work.Construction.Theta α (fun z θ => F₁ z θ - F₂ z θ) z θ
        = Work.Construction.Theta α F₁ z θ - Work.Construction.Theta α F₂ z θ) :
    Work.FTS.StrongEps.EComparison.EllPkgCls α Ce
      (fun z θ => F₁ z θ - F₂ z θ) (fun z θ => Ψ₁ z θ - Ψ₂ z θ) := by
  rcases eq_or_ne α 0 with hα0 | hαne
  · subst hα0
    exact EllPkgCls_sub_zero h₁ h₂
  · set A : Fn := Work.Construction.PhiTil α (fun z θ => F₁ z θ - F₂ z θ)
      (fun z θ => Ψ₁ z θ - Ψ₂ z θ) with hA
    set P₁ : Fn := Work.Construction.PhiTil α F₁ Ψ₁ with hP₁
    set P₂ : Fn := Work.Construction.PhiTil α F₂ Ψ₂ with hP₂
    -- the value identity `A = P₁ - P₂` on the open half-line
    have hAeq : ∀ z, 0 < z → ∀ θ, A z θ = P₁ z θ - P₂ z θ := by
      intro z hz θ
      rw [hA, hP₁, hP₂]
      simp only [Work.Construction.PhiTil]
      rw [hΘ z (Set.mem_Ici.mpr (le_of_lt hz)) θ]
      ring
    -- the `L₁₂`-differentiabilities on `(0,∞)`, from the `V`-slots
    have hd₁ : ∀ z, 0 < z → DifferentiableAt ℝ (fun z' => Work.Construction.L12 F₁ z') z :=
      fun z hz => differentiableAt_L12_of_Vop hαne h₁.1 h₁.2.2.2.2.1 hz
    have hd₂ : ∀ z, 0 < z → DifferentiableAt ℝ (fun z' => Work.Construction.L12 F₂ z') z :=
      fun z hz => differentiableAt_L12_of_Vop hαne h₂.1 h₂.2.2.2.2.1 hz
    have hlin : ∀ z, 0 < z → Work.Construction.L12 (fun z θ => F₁ z θ - F₂ z θ) z
        = Work.Construction.L12 F₁ z - Work.Construction.L12 F₂ z :=
      fun z hz => L12_sub_of_Theta hαne hΘ z (Set.mem_Ioi.mpr hz)
    have hu₁ : ∀ z, 0 < z → DifferentiableAt ℝ
        (fun z' => (1 / (4 * α)) * Work.Construction.L12 F₁ z') z :=
      fun z hz => (hd₁ z hz).const_mul _
    have hu₂ : ∀ z, 0 < z → DifferentiableAt ℝ
        (fun z' => (1 / (4 * α)) * Work.Construction.L12 F₂ z') z :=
      fun z hz => (hd₂ z hz).const_mul _
    have huU : ∀ z, 0 < z → DifferentiableAt ℝ
        (fun z' => (1 / (4 * α))
          * Work.Construction.L12 (fun z θ => F₁ z θ - F₂ z θ) z') z := by
      intro z hz
      refine (((hd₁ z hz).sub (hd₂ z hz)).const_mul (1 / (4 * α))).congr_of_eventuallyEq ?_
      filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
      simp only [Pi.sub_apply]
      rw [hlin z' (Set.mem_Ioi.mp hz')]
    -- the `z`-derivative split on the open quadrant
    have hsplit_z : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
        Work.Spaces.pz A z θ = Work.Spaces.pz P₁ z θ - Work.Spaces.pz P₂ z θ := by
      intro z θ hz h0 h1
      have hA' : Work.Spaces.pz A z θ
          = Work.Spaces.pz (fun z θ => Ψ₁ z θ - Ψ₂ z θ) z θ
            - deriv (fun z' => (1 / (4 * α)) * Real.sin (2 * θ)
                * Work.Construction.L12 (fun z θ => F₁ z θ - F₂ z θ) z') z := by
        rw [hA]
        exact pz_PhiTil_eq (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_sub' h₁.1 h₂.1)
          (huU z hz) hz h0 h1
      have hP₁' : Work.Spaces.pz P₁ z θ
          = Work.Spaces.pz Ψ₁ z θ
            - deriv (fun z' => (1 / (4 * α)) * Real.sin (2 * θ)
                * Work.Construction.L12 F₁ z') z := by
        rw [hP₁]
        exact pz_PhiTil_eq h₁.1 (hu₁ z hz) hz h0 h1
      have hP₂' : Work.Spaces.pz P₂ z θ
          = Work.Spaces.pz Ψ₂ z θ
            - deriv (fun z' => (1 / (4 * α)) * Real.sin (2 * θ)
                * Work.Construction.L12 F₂ z') z := by
        rw [hP₂]
        exact pz_PhiTil_eq h₂.1 (hu₂ z hz) hz h0 h1
      -- the `z`-derivative of the `L₁₂`-slot splits
      have hdU : DifferentiableAt ℝ (fun z' => Work.Construction.L12
          (fun z θ => F₁ z θ - F₂ z θ) z') z := by
        refine ((hd₁ z hz).sub (hd₂ z hz)).congr_of_eventuallyEq ?_
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        simp only [Pi.sub_apply]
        exact hlin z' (Set.mem_Ioi.mp hz')
      have hB₁ : DifferentiableAt ℝ (fun z' => (1 / (4 * α)) * Real.sin (2 * θ)
          * Work.Construction.L12 F₁ z') z :=
        ((hu₁ z hz).const_mul (Real.sin (2 * θ))).congr_of_eventuallyEq
          (Filter.Eventually.of_forall (fun z' => by ring))
      have hB₂ : DifferentiableAt ℝ (fun z' => (1 / (4 * α)) * Real.sin (2 * θ)
          * Work.Construction.L12 F₂ z') z :=
        ((hu₂ z hz).const_mul (Real.sin (2 * θ))).congr_of_eventuallyEq
          (Filter.Eventually.of_forall (fun z' => by ring))
      have hBU : DifferentiableAt ℝ (fun z' => (1 / (4 * α)) * Real.sin (2 * θ)
          * Work.Construction.L12 (fun z θ => F₁ z θ - F₂ z θ) z') z :=
        ((huU z hz).const_mul (Real.sin (2 * θ))).congr_of_eventuallyEq
          (Filter.Eventually.of_forall (fun z' => by ring))
      have hevU : (fun z' => (1 / (4 * α)) * Real.sin (2 * θ)
            * Work.Construction.L12 (fun z θ => F₁ z θ - F₂ z θ) z')
          =ᶠ[𝓝 z] (fun z' => (1 / (4 * α)) * Real.sin (2 * θ) * Work.Construction.L12 F₁ z')
            - (fun z' => (1 / (4 * α)) * Real.sin (2 * θ) * Work.Construction.L12 F₂ z') := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        simp only [Pi.sub_apply]
        rw [hlin z' (Set.mem_Ioi.mp hz')]
        ring
      rw [hA', hP₁', hP₂', pz_sub h₁.1 h₂.1 hz h0 h1, hevU.deriv_eq, deriv_sub hB₁ hB₂]
      ring
    -- the `θ`-derivative split on the open quadrant
    have hsplit_t : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
        Work.Spaces.pth A z θ = Work.Spaces.pth P₁ z θ - Work.Spaces.pth P₂ z θ := by
      intro z θ hz h0 h1
      have hA' : Work.Spaces.pth A z θ
          = Work.Spaces.pth (fun z θ => Ψ₁ z θ - Ψ₂ z θ) z θ
            - deriv (fun θ' => (1 / (4 * α)) * Real.sin (2 * θ')
                * Work.Construction.L12 (fun z θ => F₁ z θ - F₂ z θ) z) θ := by
        rw [hA]
        exact pth_PhiTil_eq (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_sub' h₁.1 h₂.1)
          hz h0 h1
      have hP₁' : Work.Spaces.pth P₁ z θ
          = Work.Spaces.pth Ψ₁ z θ
            - deriv (fun θ' => (1 / (4 * α)) * Real.sin (2 * θ')
                * Work.Construction.L12 F₁ z) θ := by
        rw [hP₁]
        exact pth_PhiTil_eq h₁.1 hz h0 h1
      have hP₂' : Work.Spaces.pth P₂ z θ
          = Work.Spaces.pth Ψ₂ z θ
            - deriv (fun θ' => (1 / (4 * α)) * Real.sin (2 * θ')
                * Work.Construction.L12 F₂ z) θ := by
        rw [hP₂]
        exact pth_PhiTil_eq h₂.1 hz h0 h1
      rw [hA', hP₁', hP₂', pth_sub h₁.1 h₂.1 hz h0 h1,
        deriv_const_sin_two_mul, deriv_const_sin_two_mul, deriv_const_sin_two_mul,
        hlin z hz]
      ring
    obtain ⟨hsR, hsU, hsV⟩ := slot_identities (α := α) (A := A) (P₁ := P₁) (P₂ := P₂)
      (fun z θ hz h0 h1 => hAeq z hz θ) hsplit_z hsplit_t
    refine ⟨Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_sub' h₁.1 h₂.1, ?_, ?_, ?_, ?_⟩
    · -- the elliptic law
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro z hz θ h0 h1
        have hc : Real.cos θ ≠ 0 :=
          ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩)
        have hC2₁ : ContDiffAt ℝ 2 (Function.uncurry Ψ₁) (z, θ) :=
          (h₁.1.forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds ⟨hz, h0, h1⟩)
        have hC2₂ : ContDiffAt ℝ 2 (Function.uncurry Ψ₂) (z, θ) :=
          (h₂.1.forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds ⟨hz, h0, h1⟩)
        rw [Work.FTS.EllipticEst.bslOp_sub α Ψ₁ Ψ₂ z θ hc hC2₁ hC2₂,
          h₁.2.1.1 z hz θ h0 h1, h₂.2.1.1 z hz θ h0 h1]
      · intro z
        show Ψ₁ z 0 - Ψ₂ z 0 = 0
        rw [h₁.2.1.2.1 z, h₂.2.1.2.1 z]
        ring
      · intro z
        show Ψ₁ z (π / 2) - Ψ₂ z (π / 2) = 0
        rw [h₁.2.1.2.2.1 z, h₂.2.1.2.2.1 z]
        ring
      · intro θ hθ
        simpa using (h₁.2.1.2.2.2 θ hθ).sub (h₂.2.1.2.2.2 θ hθ)
    · -- the `ℛ`-slot
      exact HQo_sub_of_slot 6 h₁.2.2.1 h₂.2.2.1
        (fun z θ hz h0 h1 => (hsR z θ hz h0 h1).symm)
    · -- the `U`-slot
      refine HQo_sub_of_slot 6 h₁.2.2.2.1 h₂.2.2.2.1 (fun z θ hz h0 h1 => ?_)
      rw [← sub_div, ← hsU z θ hz h0 h1]
    · -- the `V`-slot
      exact HQo_sub_of_slot 6 h₁.2.2.2.2 h₂.2.2.2.2
        (fun z θ hz h0 h1 => (hsV z θ hz h0 h1).symm)

end Work.FTS.StrongEps.EComparison
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.TransO.SlotsMemO =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.TransO

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## `SmoothOpen` as a finite-order class -/

/-- `SmoothOpen` (genuine `C^∞` on the open quadrant) gives the finite-order class `Q0Sm n`. -/
theorem Q0Sm_of_smoothOpen {X : Fn} (h : Work.FTS.EllipticEst.SmoothOpen X) (n : ℕ) :
    Work.FTS.CoercivityFix.Transfer.Q0Sm n X :=
  h.of_le (m := (((n : ℕ)) : WithTop ℕ∞)) (WithTop.coe_le_coe.mpr le_top)

/-- `D_θf` and `D_zf` are in `Q0Sm n` for every `n` when `f` is `SmoothOpen`. -/
theorem Q0Sm_Dth_Dz_O {f : Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f) (n : ℕ) :
    Work.FTS.CoercivityFix.Transfer.Q0Sm n (Work.Spaces.Dth f) ∧
      Work.FTS.CoercivityFix.Transfer.Q0Sm n (Work.Spaces.Dz f) :=
  ⟨Work.FTS.CoercivityFix.Transfer.Q0Sm.dth
      (Q0Sm_of_smoothOpen hf (n + 1)),
    Work.FTS.CoercivityFix.Transfer.Q0Sm.dz
      (Q0Sm_of_smoothOpen hf (n + 1))⟩

/-! ## The two clean-operator slots are `C^∞` on the open quadrant -/

/-- **`𝓛̂(D_θf)` is `C^∞` on the open quadrant** for `SmoothOpen f`.  This is the `SmoothOpen`
twin of `E1Parts.contDiffOn_uncurry_Lhat_Dth` (which asks for `SmoothQuad f`, a class the
route's slices do not satisfy). -/
theorem contDiffOn_uncurry_Lhat_Dth_O {f : Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f)))
      Work.Construction.Qd := by
  have hV : IsOpen Work.Construction.Qd := isOpen_Ioi.prod isOpen_Ioo
  have hDth : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.Dth f)) Work.Construction.Qd :=
    Work.FTS.LocData.contDiffOn_Dth hV hf
  have hpz : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pz (Work.Spaces.Dth f))) Work.Construction.Qd :=
    Work.FTS.LocData.contDiffOn_pz hV hDth
  have hDthDth : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.Dth (Work.Spaces.Dth f))) Work.Construction.Qd :=
    Work.FTS.LocData.contDiffOn_Dth hV hDth
  have hne : ∀ p ∈ Work.Construction.Qd, (1 : ℝ) + p.1 ≠ 0 := by
    intro p hp
    have hp1 : (0 : ℝ) < p.1 := hp.1
    linarith
  have hfun : Function.uncurry (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f))
      = fun p : ℝ × ℝ =>
          Function.uncurry (Work.Spaces.Dth f) p
            + p.1 * Function.uncurry (Work.Spaces.pz (Work.Spaces.Dth f)) p
            - 2 * Function.uncurry (Work.Spaces.Dth f) p / (1 + p.1)
            - 3 * Function.uncurry (Work.Spaces.Dth (Work.Spaces.Dth f)) p / (1 + p.1) := by
    funext p
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair]
    rw [Work.FTS.CoercivityFix.Lhat_eq]
    simp only [Work.Spaces.Dz]
  rw [hfun]
  exact (((hDth.add (contDiffOn_fst.mul hpz)).sub
      ((contDiffOn_const.mul hDth).div (contDiffOn_const.add contDiffOn_fst) hne)).sub
    ((contDiffOn_const.mul hDthDth).div (contDiffOn_const.add contDiffOn_fst) hne))

/-- **`𝓛̂(D_zf)` is `C^∞` on the open quadrant** for `SmoothOpen f` (the `SmoothOpen` twin of
`E2_pkg.contDiffOn_uncurry_Lhat_Dz`). -/
theorem contDiffOn_uncurry_Lhat_Dz_O {f : Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f)))
      Work.Construction.Qd := by
  have hV : IsOpen Work.Construction.Qd := isOpen_Ioi.prod isOpen_Ioo
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.Dz f)) Work.Construction.Qd :=
    Work.FTS.LocData.contDiffOn_Dz hV hf
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pz (Work.Spaces.Dz f))) Work.Construction.Qd :=
    Work.FTS.LocData.contDiffOn_pz hV h1
  have h3 : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.Dth (Work.Spaces.Dz f))) Work.Construction.Qd :=
    Work.FTS.LocData.contDiffOn_Dth hV h1
  have hne : ∀ p ∈ Work.Construction.Qd, (1 : ℝ) + p.1 ≠ 0 := by
    intro p hp
    have hp1 : (0 : ℝ) < p.1 := hp.1
    linarith
  have hfun : Function.uncurry (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f))
      = fun p : ℝ × ℝ =>
          Function.uncurry (Work.Spaces.Dz f) p
            + p.1 * Function.uncurry (Work.Spaces.pz (Work.Spaces.Dz f)) p
            - 2 * Function.uncurry (Work.Spaces.Dz f) p / (1 + p.1)
            - 3 * Function.uncurry (Work.Spaces.Dth (Work.Spaces.Dz f)) p / (1 + p.1) := by
    funext p
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair]
    rw [Work.FTS.CoercivityFix.Lhat_eq]
    simp only [Work.Spaces.Dz]
  rw [hfun]
  exact (((h1.add (contDiffOn_fst.mul h2)).sub
      ((contDiffOn_const.mul h1).div (contDiffOn_const.add contDiffOn_fst) hne)).sub
    ((contDiffOn_const.mul h3).div (contDiffOn_const.add contDiffOn_fst) hne))

/-- `Q0Sm n` of the two clean-operator slots, for `SmoothOpen f`. -/
theorem Q0Sm_Lhat_slots_O {f : Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f) (n : ℕ) :
    Work.FTS.CoercivityFix.Transfer.Q0Sm n
        (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f)) ∧
      Work.FTS.CoercivityFix.Transfer.Q0Sm n
        (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f)) :=
  ⟨(contDiffOn_uncurry_Lhat_Dth_O hf).of_le (WithTop.coe_le_coe.mpr le_top),
    (contDiffOn_uncurry_Lhat_Dz_O hf).of_le (WithTop.coe_le_coe.mpr le_top)⟩

/-! ## The `ℋⁿ`-membership of the four slots -/

/-- **The four slot memberships of the transfer on the open class**: for `CoerAdmO α f` and
`n ≤ 3`, the `ℋⁿ`-honesty of `𝓛̂(D_θf)`, `𝓛̂(D_zf)`, `D_θf`, `D_zf`.

This is the open-class twin of `Transfer/LevelPkgInst.HkMem_slots` (which asks for `CoerAdm`).
The `D_θ`/`D_z` slots come from the `RegQo`-port `regQo_dth_dz`, and the two clean-operator
slots from `Lhat_RegQo`. -/
theorem HkMem_slots_O (α : ℝ) (hα : 0 < α) {n : ℕ} (hn : n ≤ 3) {f : Fn}
    (hf : CoerAdmO α f) :
    Work.Spaces.HkMem α n (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f))
      ∧ Work.Spaces.HkMem α n (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f))
      ∧ Work.Spaces.HkMem α n (Work.Spaces.Dth f)
      ∧ Work.Spaces.HkMem α n (Work.Spaces.Dz f) := by
  have h5 : RegQo α 5 f := hf.1
  have h1 : RegQo α (n + 1) f := regQo_mono (by omega) h5
  have h2 : RegQo α (n + 2) f := regQo_mono (by omega) h5
  obtain ⟨hdth1, hdz1⟩ := regQo_dth_dz hα h1
  obtain ⟨hdth2, hdz2⟩ := regQo_dth_dz hα h2
  have hLth : RegQo α n (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f)) :=
    Work.FTS.StrongEps.EpsE4Thr.Lhat_RegQo α hα n hdth2
  have hLdz : RegQo α n (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f)) :=
    Work.FTS.StrongEps.EpsE4Thr.Lhat_RegQo α hα n hdz2
  exact ⟨hLth.2.1, hLdz.2.1, hdth1.2.1, hdz1.2.1⟩

end Work.FTS.StrongEps.EpsE4Thr.TransO
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXA1w.abs_mixed_le_HkNorm_C4_w_proved =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# RX-A1w — the weighted interior `L^∞`–`ℋ⁴` trade-off at the finite order `C⁴`

For `0 < β ≤ 1` there is `C = C(β) ≥ 0` such that every `C⁴` datum `f` on the open quadrant
which is honestly in `ℋ⁴` and satisfies the boundary traces `BdryTraces β 4` obeys

`|D_z^bD_θ^a f (z,θ)| ≤ C · z^{3/2}/(1+z)² · |f|_{ℋ⁴}`   for `a + b ≤ 2`, `z > 0`, `0 < θ < π/2`.

The chain (see the sibling modules `AgmonZ`, `Helpers`, `AngularHardy`, `SliceAgmon`):

1. angular Hardy at the fixed radial variable `z` (`angular_hardy_C4`);
2. the weighted radial Agmon inequality in `z` (`agmonZ_weight`) on the resulting angular
   slice, with the two Agmon energy slots dominated by the `ℋ⁴`-integrand
   (`mixed_slice_pointwise_le`);
3. Tonelli (`HkSqSwap_C4`) sums the resulting a.e. bound over the angle.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXA1w

theorem abs_mixed_le_HkNorm_C4_w_proved {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Work.FTS.Galerkin.Fn,
      ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0 →
      Work.Spaces.HkMem β 4 f → Work.FTS.Nonlin.BdryTraces β 4 f →
      ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed b a f z θ| ≤
          C * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) * Work.Spaces.HkNorm β 4 f := by
  have hγ1 : 0 < Work.Spaces.gam β - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
  refine ⟨Real.sqrt (500 / (Work.Spaces.gam β - 1)), Real.sqrt_nonneg _, ?_⟩
  intro f h4 hmem htr b a hab z θ hz hθ0 hθ1
  have hHT := angular_hardy_C4 hβ hβ1 h4 hmem htr b a hab hz θ ⟨hθ0, hθ1⟩
  obtain ⟨hswap, hTint, -⟩ := Work.FTS_RegExport.C4.HkSqSwap_C4 h4 hmem
  have hrhs : MeasureTheory.Integrable
      (fun σ => 5 * (z ^ 3 / (1 + z) ^ 4)
        * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand β 4 f s σ))
      (volume.restrict Work.Spaces.Iθ) := hTint.const_mul _
  have hmono := integral_mono_of_nonneg
    (ae_restrict_of_forall_mem measurableSet_Icc fun σ hσ =>
      mul_nonneg (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg hσ) _) (sq_nonneg _))
    hrhs (mixed_slice_pointwise_le hβ h4 hmem htr b a hab hz)
  have hIntegral : (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β))
        * (Work.Spaces.mixed b (a + 1) f z σ) ^ 2)
      ≤ 5 * (z ^ 3 / (1 + z) ^ 4) * Work.Spaces.HkSq β 4 f := by
    calc (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β))
          * (Work.Spaces.mixed b (a + 1) f z σ) ^ 2)
        ≤ ∫ σ in Work.Spaces.Iθ, 5 * (z ^ 3 / (1 + z) ^ 4)
            * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand β 4 f s σ) := hmono
      _ = 5 * (z ^ 3 / (1 + z) ^ 4)
            * (∫ σ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz,
                Work.Spaces.HkIntegrand β 4 f s σ) := by
          rw [MeasureTheory.integral_const_mul]
      _ = 5 * (z ^ 3 / (1 + z) ^ 4) * Work.Spaces.HkSq β 4 f := by rw [hswap]
  have hK : 0 ≤ 100 / (Work.Spaces.gam β - 1) := div_nonneg (by norm_num) hγ1.le
  have hmain : (Work.Spaces.mixed b a f z θ) ^ 2
      ≤ (500 / (Work.Spaces.gam β - 1)) * (z ^ 3 / (1 + z) ^ 4) * Work.Spaces.HkSq β 4 f := by
    have h1 : (100 / (Work.Spaces.gam β - 1))
          * (5 * (z ^ 3 / (1 + z) ^ 4) * Work.Spaces.HkSq β 4 f)
        = (500 / (Work.Spaces.gam β - 1)) * (z ^ 3 / (1 + z) ^ 4)
          * Work.Spaces.HkSq β 4 f := by ring
    rw [← h1]
    exact le_trans hHT (mul_le_mul_of_nonneg_left hIntegral hK)
  have hC0 : 0 ≤ 500 / (Work.Spaces.gam β - 1) := div_nonneg (by norm_num) hγ1.le
  have hA0 : 0 ≤ z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2 :=
    div_nonneg (Real.rpow_nonneg hz.le _) (by positivity)
  have hA0sq : (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) ^ 2 = z ^ 3 / (1 + z) ^ 4 := by
    rw [div_pow]
    congr 1
    · rw [← Real.rpow_natCast (z ^ ((3 : ℝ) / 2)) 2, ← Real.rpow_mul hz.le]
      norm_num
    · ring
  have hsq : (Work.Spaces.mixed b a f z θ) ^ 2
      ≤ (Real.sqrt (500 / (Work.Spaces.gam β - 1)) * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)
          * Real.sqrt (Work.Spaces.HkSq β 4 f)) ^ 2 := by
    calc (Work.Spaces.mixed b a f z θ) ^ 2
        ≤ (500 / (Work.Spaces.gam β - 1)) * (z ^ 3 / (1 + z) ^ 4)
            * Work.Spaces.HkSq β 4 f := hmain
      _ = (500 / (Work.Spaces.gam β - 1))
            * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) ^ 2 * Work.Spaces.HkSq β 4 f := by
          rw [hA0sq]
      _ = (Real.sqrt (500 / (Work.Spaces.gam β - 1)) * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)
            * Real.sqrt (Work.Spaces.HkSq β 4 f)) ^ 2 := by
          rw [mul_pow, mul_pow, Real.sq_sqrt hC0, Real.sq_sqrt (Work.Spaces.HkSq_nonneg β 4 f)]
          <;> try ring
  have hfin : |Work.Spaces.mixed b a f z θ|
      ≤ Real.sqrt (500 / (Work.Spaces.gam β - 1)) * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)
          * Work.Spaces.HkNorm β 4 f := by
    have hnn : 0 ≤ Real.sqrt (500 / (Work.Spaces.gam β - 1))
        * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) * Real.sqrt (Work.Spaces.HkSq β 4 f) :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hA0) (Real.sqrt_nonneg _)
    calc |Work.Spaces.mixed b a f z θ|
        = Real.sqrt ((Work.Spaces.mixed b a f z θ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((Real.sqrt (500 / (Work.Spaces.gam β - 1))
            * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)
            * Real.sqrt (Work.Spaces.HkSq β 4 f)) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt (500 / (Work.Spaces.gam β - 1)) * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)
            * Real.sqrt (Work.Spaces.HkSq β 4 f) := Real.sqrt_sq hnn
      _ = Real.sqrt (500 / (Work.Spaces.gam β - 1)) * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)
            * Work.Spaces.HkNorm β 4 f := rfl
  exact hfin

end Work.FTS_RegExport.RXA1w
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.HkMinSlices =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.HkMinSlices`

The `θ`-slice energies of the admissible slots of `HkIntegrand α 4`: for a datum which is `C⁴`
on the open quadrant and honestly in `ℋ⁴`, the slice energy `σ ↦ ∫_Iz (D_z^jD_θ^if · w)²` is
integrable, dominated slicewise by the `ℋ⁴`-integrand, and its `θ`-integral is at most
`HkSq α 4 f`.  The `Wt`-weighted version is provided for the mixed slots.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The two delegated helpers, repointed to their proved siblings -/

theorem tmp_slot_slice_data {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 f) (j i : ℕ)
    (hadm : (1 ≤ i ∧ i + j ≤ 4) ∨ (i = 0 ∧ j ≤ 4)) :
    AEMeasurable
        (fun σ => ∫ s in Work.Spaces.Iz,
          (Work.Spaces.mixed j i f s σ) ^ 2 * (Work.Spaces.w s) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) ∧
      (∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        MeasureTheory.IntegrableOn
          (fun s => (Work.Spaces.mixed j i f s σ) ^ 2 * (Work.Spaces.w s) ^ 2) Work.Spaces.Iz) ∧
      (∫ σ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz,
          (Work.Spaces.mixed j i f s σ) ^ 2 * (Work.Spaces.w s) ^ 2)
        ≤ Work.Spaces.HkSq α 4 f :=
  slot_slice_data hα h4 hmem j i hadm

theorem tmp_slot_slice_data_Wt {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 f) (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) :
    AEMeasurable
        (fun σ => ∫ s in Work.Spaces.Iz,
          (Work.Spaces.mixed j i f s σ * Work.Spaces.Wt α s σ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) ∧
      (∫ σ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz,
          (Work.Spaces.mixed j i f s σ * Work.Spaces.Wt α s σ) ^ 2)
        ≤ Work.Spaces.HkSq α 4 f :=
  slot_slice_data_Wt hα h4 hmem j i hi hij

/-! ## Slice energies of the admissible slots -/

/-- The `θ`-slice energy of an admissible slot: integrable, dominated slicewise by the
`ℋ⁴`-integrand, with `θ`-integral bounded by `HkSq`. -/
theorem slot_slice_all {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 f) (j i : ℕ) (hadm : FTSAdm j i) :
    MeasureTheory.Integrable
        (fun σ => ∫ x in Work.Spaces.Iz,
          (Work.Spaces.mixed j i f x σ) ^ 2 * (Work.Spaces.w x) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) ∧
      (∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        MeasureTheory.IntegrableOn
          (fun x => (Work.Spaces.mixed j i f x σ) ^ 2 * (Work.Spaces.w x) ^ 2)
          Work.Spaces.Iz) ∧
      (∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        (∫ x in Work.Spaces.Iz, (Work.Spaces.mixed j i f x σ) ^ 2 * (Work.Spaces.w x) ^ 2)
          ≤ (∫ x in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f x σ)) ∧
      (∫ σ in Work.Spaces.Iθ, ∫ x in Work.Spaces.Iz,
          (Work.Spaces.mixed j i f x σ) ^ 2 * (Work.Spaces.w x) ^ 2)
        ≤ Work.Spaces.HkSq α 4 f := by
  obtain ⟨hae, hint, hbound⟩ := tmp_slot_slice_data (α := α) hα h4 hmem j i hadm
  obtain ⟨hNfin, hNint, hNae⟩ := Work.FTS_RegExport.C4.HkSqSwap_C4 h4 hmem
  have hcmp : ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (∫ x in Work.Spaces.Iz, (Work.Spaces.mixed j i f x σ) ^ 2 * (Work.Spaces.w x) ^ 2)
        ≤ (∫ x in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f x σ) := by
    filter_upwards [hNae, Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hN hσ
    refine MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun x => by positivity) hN ?_
    exact Eventually.of_forall fun x => slot_pointwise_le hα j i hadm x hσ
  refine ⟨?_, hint, hcmp, hbound⟩
  refine MeasureTheory.Integrable.mono' hNint hae.aestronglyMeasurable ?_
  filter_upwards [hcmp] with σ hσ
  rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg fun x => by positivity)]
  exact hσ

/-- The same for the `Wt`-weighted mixed slots. -/
theorem slot_slice_Wt_all {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 f) (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) :
    MeasureTheory.Integrable
        (fun σ => ∫ x in Work.Spaces.Iz,
          (Work.Spaces.mixed j i f x σ * Work.Spaces.Wt α x σ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) ∧
      (∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        (∫ x in Work.Spaces.Iz, (Work.Spaces.mixed j i f x σ * Work.Spaces.Wt α x σ) ^ 2)
          ≤ (∫ x in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f x σ)) ∧
      (∫ σ in Work.Spaces.Iθ, ∫ x in Work.Spaces.Iz,
          (Work.Spaces.mixed j i f x σ * Work.Spaces.Wt α x σ) ^ 2)
        ≤ Work.Spaces.HkSq α 4 f := by
  obtain ⟨hae, hbound⟩ := tmp_slot_slice_data_Wt (α := α) hα h4 hmem j i hi hij
  obtain ⟨hNfin, hNint, hNae⟩ := Work.FTS_RegExport.C4.HkSqSwap_C4 h4 hmem
  have hcmp : ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (∫ x in Work.Spaces.Iz, (Work.Spaces.mixed j i f x σ * Work.Spaces.Wt α x σ) ^ 2)
        ≤ (∫ x in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f x σ) := by
    filter_upwards [hNae] with σ hN
    refine MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun x => sq_nonneg _) hN ?_
    exact Eventually.of_forall fun x =>
      Work.Spaces.sq_le_HkIntegrand_mixed α 4 f x σ i j hi hij
  refine ⟨?_, hcmp, hbound⟩
  refine MeasureTheory.Integrable.mono' hNint hae.aestronglyMeasurable ?_
  filter_upwards [hcmp] with σ hσ
  rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg fun x => sq_nonneg _)]
  exact hσ

end Work.FTS_RegExport.RXT
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Slots.v2_theta_sup_uniform =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.Slots

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The target -/

theorem v2_theta_sup_uniform {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ f : ℝ → ℝ → ℝ,
      ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0 →
      Work.Spaces.HkMem α 4 f →
      ∀ b a : ℕ, a + b ≤ 3 → ∀ s : ℝ, 0 < s → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.mixed b a f s θ * Work.Spaces.w s) ^ 2
        ≤ K * (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s σ) := by
  have hγpos : 0 < Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam]; linarith
  refine ⟨8 / Real.pi + 200 / (Work.Spaces.gam α - 1), ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ 8 / Real.pi := by positivity
    have h2 : (0 : ℝ) ≤ 200 / (Work.Spaces.gam α - 1) :=
      div_nonneg (by norm_num) hγpos.le
    linarith
  intro f h4 hmem b a hab s hs θ hθ0 hθ1
  have hsI : s ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hs.le
  have hθmem : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hWnn : (0 : ℝ) ≤ Work.Spaces.w s := w_nonneg_aux s
  -- the two hypotheses of the angular bound
  have hderiv : ∀ σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun σ' => Work.Spaces.mixed b a f s σ')
        (Work.Spaces.pth (Work.Spaces.mixed b a f) s σ) σ := by
    intro σ hσ
    exact ((Work.FTS_RegExport.RXA1w.contDiffOn_slice_mixed h4 b a 1 (by omega) hs).differentiableOn
      (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hσ) |>.hasDerivAt
  have hgc : ContinuousOn (fun σ => Work.Spaces.pth (Work.Spaces.mixed b a f) s σ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := continuousOn_pth_mixed_slice_aux h4 b a (by omega) hs
  have hI1 := integrable_slot_sq_aux hα h4 hmem b a hab hs
  have hI2 := integrable_pth_sq_sin_aux hα h4 hmem b a hab hs
  have hγ1 : 1 < Work.Spaces.gam α := Work.Spaces.one_lt_gam hα
  have hγ2 : Work.Spaces.gam α ≤ 2 := by rw [Work.Spaces.gam]; linarith
  have hang := angular_meanVar_aux (γ := Work.Spaces.gam α) hγ1 hγ2 hderiv hgc hI1 hI2 θ hθmem
  -- the scalar bounds
  have hAeq : (∫ σ in Work.Spaces.Iθ, (Work.Spaces.mixed b a f s σ) ^ 2) * (Work.Spaces.w s) ^ 2
      = ∫ σ in Work.Spaces.Iθ, (Work.Spaces.mixed b a f s σ * Work.Spaces.w s) ^ 2 := by
    rw [mul_comm, ← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae (Eventually.of_forall fun σ => by ring)
  have hAle : (∫ σ in Work.Spaces.Iθ, (Work.Spaces.mixed b a f s σ) ^ 2) * (Work.Spaces.w s) ^ 2
      ≤ ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s σ := by
    rw [hAeq]
    refine MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun σ => sq_nonneg _)
      (hmem.1 s hsI) ?_
    filter_upwards [Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hσ
    exact slot_le_HkIntegrand_aux hα b a (by omega) s hσ
  have hBeq : (∫ σ in Work.Spaces.Iθ,
          (Work.Spaces.pth (Work.Spaces.mixed b a f) s σ) ^ 2
            * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) * (Work.Spaces.w s) ^ 2
      = ∫ σ in Work.Spaces.Iθ, (Work.Spaces.mixed b (a + 1) f s σ * Work.Spaces.w s) ^ 2
          * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) := by
    rw [mul_comm, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hσ
    have hsin : 0 < Real.sin (2 * σ) := Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ
    have hpth : Work.Spaces.pth (Work.Spaces.mixed b a f) s σ
        = Work.Spaces.mixed b (a + 1) f s σ / Real.sin (2 * σ) := by
      have hD := Work.FTS_RegExport.C4.Dth_mixed_eq_C4 h4 b a (by omega) hs hσ
      rw [Work.Spaces.Dth] at hD
      rw [eq_div_iff (ne_of_gt hsin), mul_comm]
      exact hD
    rw [hpth]
    have h2 : (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
        = (Real.sin (2 * σ)) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) := by
      rw [show (2 : ℝ) - Work.Spaces.gam α = 2 + (-(Work.Spaces.gam α)) by ring,
        Real.rpow_add hsin, Real.rpow_ofNat]
    have e1 : (Work.Spaces.mixed b (a + 1) f s σ / Real.sin (2 * σ)) ^ 2
        = (Work.Spaces.mixed b (a + 1) f s σ) ^ 2 / (Real.sin (2 * σ)) ^ 2 :=
      div_pow _ _ 2
    have hwne : Work.Spaces.w s ≠ 0 := ne_of_gt (w_pos_aux hs)
    rw [e1, h2]
    field_simp <;> ring_nf
  have hBle : (∫ σ in Work.Spaces.Iθ,
          (Work.Spaces.pth (Work.Spaces.mixed b a f) s σ) ^ 2
            * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) * (Work.Spaces.w s) ^ 2
      ≤ ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s σ := by
    rw [hBeq]
    refine MeasureTheory.integral_mono_of_nonneg ?_ (hmem.1 s hsI) ?_
    · filter_upwards [Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hσ
      exact mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (le_of_lt (Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ)) _)
    · filter_upwards [Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hσ
      exact slot_sin_le_HkIntegrand_aux hα b a (by omega) s hσ
  have hGle : (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (Work.Spaces.gam α - 2))
      ≤ 100 / (Work.Spaces.gam α - 1) := Work.Spaces.integral_sin_rpow α hα hα1
  have hGnn : 0 ≤ ∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (Work.Spaces.gam α - 2) := by
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hσ
    exact Real.rpow_nonneg (le_of_lt (Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ)) _
  have hHnn : 0 ≤ ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s σ :=
    MeasureTheory.integral_nonneg fun σ => Work.Spaces.HkIntegrand_nonneg α 4 f s σ
  have hAnn : 0 ≤ ∫ σ in Work.Spaces.Iθ, (Work.Spaces.mixed b a f s σ) ^ 2 :=
    MeasureTheory.integral_nonneg fun σ => sq_nonneg _
  have hBnn : 0 ≤ ∫ σ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.mixed b a f) s σ) ^ 2
      * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) := by
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hσ
    exact mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (le_of_lt (Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ)) _)
  -- assembly
  have h3 : (0 : ℝ) ≤ 8 / Real.pi := by positivity
  have h4 : (0 : ℝ) ≤ 2 * (∫ σ in Work.Spaces.Iθ,
      (Real.sin (2 * σ)) ^ (Work.Spaces.gam α - 2)) := by linarith
  have h5 : 2 * (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (Work.Spaces.gam α - 2))
      ≤ 200 / (Work.Spaces.gam α - 1) := by
    have h5a : 2 * (100 / (Work.Spaces.gam α - 1)) = 200 / (Work.Spaces.gam α - 1) := by
      field_simp <;> norm_num
    linarith
  calc (Work.Spaces.mixed b a f s θ * Work.Spaces.w s) ^ 2
      = (Work.Spaces.mixed b a f s θ) ^ 2 * (Work.Spaces.w s) ^ 2 := by ring
    _ ≤ ((8 / Real.pi) * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.mixed b a f s σ) ^ 2)
          + 2 * (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (Work.Spaces.gam α - 2))
            * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.mixed b a f) s σ) ^ 2
              * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)))
        * (Work.Spaces.w s) ^ 2 := mul_le_mul_of_nonneg_right hang (sq_nonneg _)
    _ = (8 / Real.pi) * ((∫ σ in Work.Spaces.Iθ, (Work.Spaces.mixed b a f s σ) ^ 2)
            * (Work.Spaces.w s) ^ 2)
        + 2 * (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (Work.Spaces.gam α - 2))
            * ((∫ σ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.mixed b a f) s σ) ^ 2
                * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) * (Work.Spaces.w s) ^ 2) := by
      ring
    _ ≤ (8 / Real.pi) * (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s σ)
        + 2 * (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (Work.Spaces.gam α - 2))
            * (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s σ) :=
      add_le_add (mul_le_mul_of_nonneg_left hAle h3) (mul_le_mul_of_nonneg_left hBle h4)
    _ ≤ (8 / Real.pi + 200 / (Work.Spaces.gam α - 1))
          * (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s σ) := by
      have h6 := mul_le_mul_of_nonneg_right h5 hHnn
      have h7 : (8 / Real.pi) * (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s σ)
            + (200 / (Work.Spaces.gam α - 1))
              * (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s σ)
          = (8 / Real.pi + 200 / (Work.Spaces.gam α - 1))
              * (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s σ) := by
        ring
      linarith [h6, h7]

end Work.FTS_RegExport.RXT.Slots
end
end
