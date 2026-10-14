import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.CoercivityFix.PsiMul.PsiZop
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_psi_mul_open
import Submission.Work.FTS.StrongEps.EpsZero.Nstar_zero_classC
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBound
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundCore
import Submission.Work.FTS.StrongPersist.N6_prod
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_RegExport.C4.Dth_mixed_eq_C4
import Submission.Work.FTS_RegExport.RXA1w.Helpers
import Submission.Work.FTS_RegExport.RXR1.classC_sub_hyp
import Submission.Work.FTS_RegExport.RXT.radial_noDecay_le
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.EpsEngine.ZTracesAux.continuousOn_pth_mixed_slice_gen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine.ZTracesAux

/-!
# Continuity of the angular slice of `∂_θ (D_z^b D_θ^a f)`

Let `f` be of class `C^N` on the **open** quadrant `Q0 = (0,∞) × (0,π/2)` and let
`a + b + 1 ≤ N`.  Then for every fixed `s > 0` the angular slice

  `σ ↦ ∂_θ (D_z^b D_θ^a f) (s, σ)`

is continuous on `(0, π/2)`.

This is the general-`N` form of what the `C⁴`-versions of the slice calculus
(`Work.FTS_RegExport.RXA1w.continuousOn_pth_mixed_slice_aux`,
`Work.FTS_RegExport.C4.Dth_mixed_eq_C4`) provide, and it is what the finite-order engine
`Work.FTS.StrongEps.contDiffOn_uncurry_pth_fin` is designed for: the mixed slot
`D_z^b D_θ^a f` is `C¹` on the open quadrant `Q0` as soon as `f` is `C^{1+a+b}` there
(`Work.FTS_RegExport.RXA1w.contDiffOn_uncurry_mixed_shift`), and *one* further `∂_θ` of a
`C¹` function on an open set is continuous on that set.  Restricting to the slice `z = s`
with `s > 0` (so that the slice lies in `Q0`) concludes.

No endpoint information at `θ = 0, π/2` is used or produced: the statement is genuinely an
*open-interval* one, consistent with `ContDiffOn` on the open quadrant.
-/

/-- **The angular slice of `∂_θ(D_z^bD_θ^a f)` is continuous on `(0,π/2)`.** -/
theorem continuousOn_pth_mixed_slice_gen {f : ℝ → ℝ → ℝ} {N : ℕ}
    (hF : ContDiffOn ℝ N (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (b a : ℕ) (hab : a + b + 1 ≤ N) {s : ℝ} (hs : 0 < s) :
    ContinuousOn (fun σ => Work.Spaces.pth (Work.Spaces.mixed b a f) s σ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  -- `f` is `C^{1+a+b}`, which is all that the identity `N ≥ a+b+1` gives us.
  have hab1 : 1 + a + b ≤ N := by omega
  have h1 : ContDiffOn ℝ (1 + a + b) (Function.uncurry f) Work.FTS.EllipticEst.Q0 :=
    hF.of_le (Nat.cast_le.mpr hab1)
  -- hence the mixed slot `D_z^b D_θ^a f` is `C¹` on the open quadrant …
  have hG : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.mixed b a f))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS_RegExport.RXA1w.contDiffOn_uncurry_mixed_shift
      Work.FTS.EllipticEst.isOpen_Q0 b a 1 h1
  -- … and therefore its `θ`-partial is `C⁰`, i.e. continuous, on the open quadrant.
  have hp : ContinuousOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.mixed b a f)))
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.StrongEps.contDiffOn_uncurry_pth_fin Work.FTS.EllipticEst.isOpen_Q0 hG).continuousOn
  -- The slice `σ ↦ (s, σ)` maps `(0,π/2)` into `Q0` because `s > 0`.
  have hlin : ContinuousOn (fun σ : ℝ => (s, σ)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (continuous_const.prodMk continuous_id).continuousOn
  have hmaps : Set.MapsTo (fun σ : ℝ => (s, σ)) (Set.Ioo (0 : ℝ) (Real.pi / 2))
      Work.FTS.EllipticEst.Q0 := fun σ hσ => Work.FTS.EllipticEst.mem_Q0.mpr ⟨hs, hσ⟩
  refine (hp.comp hlin hmaps).congr (fun σ _ => rfl)

end Work.FTS.EpsEngine.ZTracesAux
end
-- ===== merged: Submission.Work.FTS.EpsEngine.ZTracesAux.slot_le_HkIntegrand_gen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# A mixed/radial slot with the bare weight `w` is dominated by `HkIntegrand`

The `H^k` weight attached to a mixed derivative `D_z^b D_θ^a` is `Wt = w · sin(2θ)^{-γ/2}`
(for `a ≥ 1`) resp. `w · sin(2θ)^{-η/2}` (for the pure `D_z`-slots).  Both weights are at
least `w` on the open quadrant, because `sin(2θ) ≤ 1` there.  Hence the squared slot with the
*unweighted* factor `w` is still dominated by the corresponding term of `HkIntegrand`, which
is what `slot_le_HkIntegrand_gen` records.
-/

namespace Work.FTS.EpsEngine.ZTracesAux

theorem slot_le_HkIntegrand_gen {α : ℝ} (hα : 0 < α)
    {f : ℝ → ℝ → ℝ} {m : ℕ} (b a : ℕ) (hab : a + b ≤ m) (s : ℝ) {σ : ℝ}
    (hσ : σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Work.Spaces.mixed b a f s σ * Work.Spaces.w s) ^ 2 ≤ Work.Spaces.HkIntegrand α m f s σ := by
  have hsin_pos : 0 < Real.sin (2 * σ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hσ.1]) (by linarith [hσ.2, Real.pi_pos])
  have hsin_le : Real.sin (2 * σ) ≤ 1 := Real.sin_le_one _
  have hw_nonneg : 0 ≤ Work.Spaces.w s := by
    rw [Work.Spaces.w]
    exact div_nonneg (sq_nonneg _) (sq_nonneg _)
  rcases Nat.eq_zero_or_pos a with ha | ha
  · -- pure `D_z`-slot: compare with the `η/2`-weighted term of `HkIntegrand`
    subst ha
    have hab' : b ≤ m := by omega
    have hmain := Work.Spaces.sq_le_HkIntegrand_z α m f s σ b hab'
    have ht_pos : 0 < (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2) :=
      Real.rpow_pos_of_pos hsin_pos _
    have ht_le : (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2) ≤ 1 := by
      refine Real.rpow_le_one hsin_pos.le hsin_le ?_
      rw [Work.Spaces.eta]
      norm_num
    have hwle : Work.Spaces.w s
        ≤ Work.Spaces.w s / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2) := by
      rw [le_div_iff₀ ht_pos]
      exact mul_le_of_le_one_right hw_nonneg ht_le
    simp only [Work.Spaces.mixed_zero_right]
    calc (Work.Spaces.DzIter b f s σ * Work.Spaces.w s) ^ 2
        = (Work.Spaces.DzIter b f s σ) ^ 2 * (Work.Spaces.w s) ^ 2 := by ring
      _ ≤ (Work.Spaces.DzIter b f s σ) ^ 2
            * (Work.Spaces.w s / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2)) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hw_nonneg hwle 2) (sq_nonneg _)
      _ = (Work.Spaces.DzIter b f s σ
            * (Work.Spaces.w s / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by ring
      _ ≤ Work.Spaces.HkIntegrand α m f s σ := hmain
  · -- mixed slot (`a ≥ 1`): compare with the `γ/2`-weighted term of `HkIntegrand`
    have hgam : 0 ≤ Work.Spaces.gam α := by
      rw [Work.Spaces.gam]; linarith
    have hc : -(Work.Spaces.gam α / 2) ≤ 0 := by linarith
    have hwt : 1 ≤ (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α / 2)) := by
      have h := Real.rpow_le_rpow_of_nonpos hsin_pos hsin_le hc
      simpa using h
    have hwt_sq : 1 ≤ ((Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2 := by
      have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hwt 2
      simpa using h
    have hsq_le : (Work.Spaces.w s) ^ 2 ≤ (Work.Spaces.Wt α s σ) ^ 2 := by
      rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow]
      simpa using mul_le_mul_of_nonneg_left hwt_sq (sq_nonneg (Work.Spaces.w s))
    have hmain := Work.Spaces.sq_le_HkIntegrand_mixed α m f s σ a b ha hab
    calc (Work.Spaces.mixed b a f s σ * Work.Spaces.w s) ^ 2
        = (Work.Spaces.mixed b a f s σ) ^ 2 * (Work.Spaces.w s) ^ 2 := by ring
      _ ≤ (Work.Spaces.mixed b a f s σ) ^ 2 * (Work.Spaces.Wt α s σ) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq_le (sq_nonneg _)
      _ = (Work.Spaces.mixed b a f s σ * Work.Spaces.Wt α s σ) ^ 2 := by ring
      _ ≤ Work.Spaces.HkIntegrand α m f s σ := hmain

end Work.FTS.EpsEngine.ZTracesAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.EllPkgClsSlots =====
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

/-- **The slot identities**: if `A = P₁ - P₂` as functions on the open quadrant and both the
`z`- and the `θ`-derivatives split there, then `Rop`, `Uop` and `Vop` are additive on
`(A, P₁, P₂)`. -/
theorem slot_identities {α : ℝ} {A P₁ P₂ : Fn}
    (hval : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → A z θ = P₁ z θ - P₂ z θ)
    (hpz : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.pz A z θ = Work.Spaces.pz P₁ z θ - Work.Spaces.pz P₂ z θ)
    (hpth : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.pth A z θ = Work.Spaces.pth P₁ z θ - Work.Spaces.pth P₂ z θ) :
    (∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
        Work.Construction.Rop α A z θ
          = Work.Construction.Rop α P₁ z θ - Work.Construction.Rop α P₂ z θ)
      ∧ (∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
        Work.Construction.Uop α A z θ
          = Work.Construction.Uop α P₁ z θ - Work.Construction.Uop α P₂ z θ)
      ∧ (∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
        Work.Construction.Vop A z θ
          = Work.Construction.Vop P₁ z θ - Work.Construction.Vop P₂ z θ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z θ hz h0 h1
    simp only [Work.Construction.Rop]
    rw [hval z θ hz h0 h1, hpz z θ hz h0 h1, hpth z θ hz h0 h1]
    ring
  · intro z θ hz h0 h1
    simp only [Work.Construction.Uop]
    rw [hval z θ hz h0 h1, hpz z θ hz h0 h1]
    ring
  · intro z θ hz h0 h1
    simp only [Work.Construction.Vop]
    rw [hval z θ hz h0 h1, hpth z θ hz h0 h1]
    ring

/-- **The `HQo`-slot of a difference**: if `X₁`, `X₂` are of class `HQo α k` and the function
`X₁ - X₂` agrees with `A` on the open quadrant, then `A` is of class `HQo α k`. -/
theorem HQo_sub_of_slot {α : ℝ} (k : ℕ) {X₁ X₂ A : Fn}
    (h₁ : Work.FTS.VocabO.HQo α k X₁) (h₂ : Work.FTS.VocabO.HQo α k X₂)
    (h : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → X₁ z θ - X₂ z θ = A z θ) :
    Work.FTS.VocabO.HQo α k A := by
  refine ⟨?_, ?_⟩
  · refine Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (Work.FTS.EllipticEst.Cert.smoothOpen_sub_bsl h₁.1 h₂.1) ?_
    intro z θ hz h0 h1
    exact h z θ hz h0 h1
  · exact Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α k
      (Work.FTS.StrongPersist.H6Pair6Aux.HkMem_sub_of_HkMem α k h₁.1 h₂.1 h₁.2 h₂.2)
      (fun z hz θ hθ => h z θ hz hθ.1 hθ.2)

/-- **`L₁₂`-additivity on the half-line, from the additivity of `Theta`.** -/
theorem L12_sub_of_Theta {α : ℝ} (hα : α ≠ 0) {F₁ F₂ : Fn}
    (hΘ : ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      Work.Construction.Theta α (fun z θ => F₁ z θ - F₂ z θ) z θ
        = Work.Construction.Theta α F₁ z θ - Work.Construction.Theta α F₂ z θ) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Construction.L12 (fun z θ => F₁ z θ - F₂ z θ) z
        = Work.Construction.L12 F₁ z - Work.Construction.L12 F₂ z := by
  intro z hz
  have hzIz : z ∈ Work.Spaces.Iz := by
    have hle : (0 : ℝ) ≤ z := le_of_lt (show (0 : ℝ) < z from hz)
    simpa only [Work.Spaces.Iz, Set.mem_Ici] using hle
  have h := hΘ z hzIz (π / 4)
  simp only [Work.Construction.Theta, Work.Construction.s2] at h
  have hsin : Real.sin (2 * (π / 4)) = 1 := by
    rw [show 2 * (π / 4) = π / 2 from by ring, Real.sin_pi_div_two]
  rw [hsin, mul_one] at h
  have hc : (1 / (4 * α)) ≠ 0 := by
    have h4 : (4 * α : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hα
    simpa using inv_ne_zero h4
  have h'' : (1 / (4 * α)) * (Work.Construction.L12 (fun z θ => F₁ z θ - F₂ z θ) z
      - (Work.Construction.L12 F₁ z - Work.Construction.L12 F₂ z)) = 0 := by linarith
  rcases mul_eq_zero.mp h'' with h1 | h2
  · exact absurd h1 hc
  · linarith [sub_eq_zero.mp h2]

/-- **The `α = 0` case.**  Here `Theta 0 F = 0`, so `PhiTil 0 F Ψ = Ψ` for every `F` and the
`V`-slot machinery is not needed: only the splits of the two stream functions themselves enter. -/
theorem EllPkgCls_sub_zero {Ce : ℝ} {F₁ F₂ Ψ₁ Ψ₂ : Fn}
    (h₁ : EllPkgCls 0 Ce F₁ Ψ₁) (h₂ : EllPkgCls 0 Ce F₂ Ψ₂) :
    EllPkgCls 0 Ce (fun z θ => F₁ z θ - F₂ z θ) (fun z θ => Ψ₁ z θ - Ψ₂ z θ) := by
  have hPhi : ∀ F Ψ : Fn, Work.Construction.PhiTil 0 F Ψ = Ψ := by
    intro F Ψ
    funext z θ
    simp only [Work.Construction.PhiTil, Work.Construction.Theta, Work.Construction.s2]
    norm_num
  have hR₁ : Work.FTS.VocabO.HQo 0 6 (Work.Construction.Rop 0 Ψ₁) := by
    rw [← hPhi F₁ Ψ₁]; exact h₁.2.2.1
  have hR₂ : Work.FTS.VocabO.HQo 0 6 (Work.Construction.Rop 0 Ψ₂) := by
    rw [← hPhi F₂ Ψ₂]; exact h₂.2.2.1
  have hU₁ : Work.FTS.VocabO.HQo 0 6
      (fun z θ => Work.Construction.Uop 0 Ψ₁ z θ / Work.Construction.s2 θ) := by
    rw [← hPhi F₁ Ψ₁]; exact h₁.2.2.2.1
  have hU₂ : Work.FTS.VocabO.HQo 0 6
      (fun z θ => Work.Construction.Uop 0 Ψ₂ z θ / Work.Construction.s2 θ) := by
    rw [← hPhi F₂ Ψ₂]; exact h₂.2.2.2.1
  have hV₁ : Work.FTS.VocabO.HQo 0 6 (Work.Construction.Vop Ψ₁) := by
    rw [← hPhi F₁ Ψ₁]; exact h₁.2.2.2.2
  have hV₂ : Work.FTS.VocabO.HQo 0 6 (Work.Construction.Vop Ψ₂) := by
    rw [← hPhi F₂ Ψ₂]; exact h₂.2.2.2.2
  have hval : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      (fun z θ => Ψ₁ z θ - Ψ₂ z θ) z θ = Ψ₁ z θ - Ψ₂ z θ := fun _ _ _ _ _ => rfl
  have hpz : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.pz (fun z θ => Ψ₁ z θ - Ψ₂ z θ) z θ
        = Work.Spaces.pz Ψ₁ z θ - Work.Spaces.pz Ψ₂ z θ :=
    fun z θ hz h0 h1 => pz_sub h₁.1 h₂.1 hz h0 h1
  have hpth : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.pth (fun z θ => Ψ₁ z θ - Ψ₂ z θ) z θ
        = Work.Spaces.pth Ψ₁ z θ - Work.Spaces.pth Ψ₂ z θ :=
    fun z θ hz h0 h1 => pth_sub h₁.1 h₂.1 hz h0 h1
  obtain ⟨hsR, hsU, hsV⟩ := slot_identities (α := 0)
    (A := fun z θ => Ψ₁ z θ - Ψ₂ z θ) (P₁ := Ψ₁) (P₂ := Ψ₂) hval hpz hpth
  have hgoal : Work.Construction.PhiTil 0 (fun z θ => F₁ z θ - F₂ z θ)
      (fun z θ => Ψ₁ z θ - Ψ₂ z θ) = fun z θ => Ψ₁ z θ - Ψ₂ z θ :=
    hPhi (fun z θ => F₁ z θ - F₂ z θ) (fun z θ => Ψ₁ z θ - Ψ₂ z θ)
  refine ⟨Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_sub' h₁.1 h₂.1, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro z hz θ h0 h1
      have hc : Real.cos θ ≠ 0 :=
        ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩)
      have hC2₁ : ContDiffAt ℝ 2 (Function.uncurry Ψ₁) (z, θ) :=
        (h₁.1.forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds ⟨hz, h0, h1⟩)
      have hC2₂ : ContDiffAt ℝ 2 (Function.uncurry Ψ₂) (z, θ) :=
        (h₂.1.forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds ⟨hz, h0, h1⟩)
      rw [Work.FTS.EllipticEst.bslOp_sub 0 Ψ₁ Ψ₂ z θ hc hC2₁ hC2₂,
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
  · rw [hgoal]
    exact HQo_sub_of_slot 6 hR₁ hR₂ (fun z θ hz h0 h1 => (hsR z θ hz h0 h1).symm)
  · rw [hgoal]
    refine HQo_sub_of_slot 6 hU₁ hU₂ (fun z θ hz h0 h1 => ?_)
    rw [← sub_div, ← hsU z θ hz h0 h1]
  · rw [hgoal]
    exact HQo_sub_of_slot 6 hV₁ hV₂ (fun z θ hz h0 h1 => (hsV z θ hz h0 h1).symm)

end Work.FTS.StrongEps.EComparison
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.Lhat_RegQo =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! # `𝓛̂` preserves the open-quadrant coercivity class `RegQo`

`Lhat f = 𝓛f − Transport f = f + D_z f − 2f/(1+z) − 3 D_θ f/(1+z)` (`CoercivityFix.Lhat_eq`),
so `RegQo α m (Lhat f)` follows from `RegQo α (m+1) f` componentwise:

* **smoothness** `SmoothOpen (Lhat f)` is `H6Aux.smoothOpen_Lhat`;
* **`ℋ^m`-membership** is the pointwise integrand domination `H6Aux.Lhat_mem`
  (`HkIntegrand α m (Lhat f) ≤ C·HkIntegrand α (m+1) f`);
* **boundary traces**: each of the four summands of `Lhat f` is a `RegQo`-port of `f`
  (`f` and `D_z f` by `regQo_dth_dz`, the two radial multiples `2f/(1+z)`, `3D_θf/(1+z)` by
  the open radial-multiplier lemma `TracesAux.BdryTraces_psi_mul_open` with `ψ = 1/(1+z)`),
  and `BdryTraces` is closed under sums, scalar multiples and differences
  (`ClassC.bdryTraces_add`, `ClassC.bdryTraces_smul`). -/

/-- `ψ(z) = 1/(1+z)` is `C^n` on `(0,∞)` for every `n` — the smoothness input of
`TracesAux.BdryTraces_psi_mul_open`. -/
private theorem contDiffOn_oneDiv_fts :
    ∀ n : ℕ, ContDiffOn ℝ n (fun z : ℝ => 1 / (1 + z)) (Set.Ioi 0) := by
  intro n
  refine ContDiffOn.div contDiffOn_const (contDiffOn_const.add contDiffOn_id) ?_
  intro z hz
  have hz0 : (0 : ℝ) < z := hz
  positivity

/-- A radial multiplier (`C^n` on `(0,∞)` for every `n`) preserves `SmoothOpen`. -/
private theorem smoothOpen_psi_mul_fts {ψ : ℝ → ℝ}
    (hψ : ∀ n : ℕ, ContDiffOn ℝ n ψ (Set.Ioi 0))
    {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => ψ z * g z θ) := by
  refine (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr fun n => ?_
  have h1 : ContDiffOn ℝ n (fun p : ℝ × ℝ => ψ p.1) Work.FTS.EllipticEst.Q0 :=
    (hψ n).comp contDiff_fst.contDiffOn (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
  have h2 : ContDiffOn ℝ n (fun p : ℝ × ℝ => g p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    hg.forall n
  exact h1.mul h2

/-- `BdryTraces` is closed under multiplication by a constant, in the pointwise form (the frozen
`ClassC.bdryTraces_smul` is stated with `c • f`). -/
private theorem bdryTraces_const_mul_fts {α : ℝ} {k : ℕ} {f : Fn} (c : ℝ)
    (hf : Work.FTS.Nonlin.BdryTraces α k f) :
    Work.FTS.Nonlin.BdryTraces α k (fun z θ => c * f z θ) :=
  Work.FTS.ClassC.bdryTraces_smul (α := α) (k := k) hf c

/-- **`RegQo` is preserved by the clean operator `𝓛̂ = 𝓛 − Transport`.** -/
theorem Lhat_RegQo (α : ℝ) (hα : 0 < α) (m : ℕ) {f : Work.FTS.Galerkin.Fn}
    (hf : Work.FTS.StrongEps.EpsE4Thr.RegQo α (m + 1) f) :
    Work.FTS.StrongEps.EpsE4Thr.RegQo α m (Work.FTS.CoercivityFix.Lhat f) := by
  obtain ⟨hsm, hmem, hbd⟩ := hf
  have hf' : Work.FTS.StrongEps.EpsE4Thr.RegQo α (m + 1) f := ⟨hsm, hmem, hbd⟩
  refine ⟨Work.FTS.StrongPersist.H6Aux.smoothOpen_Lhat hsm,
    Work.FTS.StrongPersist.H6Aux.Lhat_mem α hα m hsm hmem, ?_⟩
  -- the traces of `f` at level `m`, and the two `RegQo`-ports at level `m`
  have hf_tr : Work.FTS.Nonlin.BdryTraces α m f :=
    Work.FTS.ClassC.bdryTraces_mono (k := m) (l := m + 1) (by omega) hbd
  obtain ⟨hdth, hdz⟩ := regQo_dth_dz hα hf'
  have htZ : Work.FTS.Nonlin.BdryTraces α m (Work.Spaces.Dz f) := hdz.2.2
  have htT : Work.FTS.Nonlin.BdryTraces α m (Work.Spaces.Dth f) := hdth.2.2
  -- the `Zop`-iterate bound for `ψ(z) = 1/(1+z)` up to order `m`
  obtain ⟨K, hK0, hKb⟩ := Work.FTS.CoercivityFix.PsiMul.zop_psi_bound m
  -- the first radial multiple `2f/(1+z)`
  have h2sm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => 2 * f z θ) := hsm.const_mul' 2
  have h2tr : Work.FTS.Nonlin.BdryTraces α m (fun z θ => 2 * f z θ) :=
    bdryTraces_const_mul_fts 2 hf_tr
  have hXsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (1 / (1 + z)) * (2 * f z θ)) :=
    smoothOpen_psi_mul_fts (ψ := fun z => 1 / (1 + z)) contDiffOn_oneDiv_fts h2sm
  have hXtr : Work.FTS.Nonlin.BdryTraces α m
      (fun z θ => (1 / (1 + z)) * (2 * f z θ)) :=
    TracesAux.BdryTraces_psi_mul_open (k := m)
      (ψ := fun z => 1 / (1 + z)) (K := K) (x := fun z θ => 2 * f z θ)
      hK0 hKb contDiffOn_oneDiv_fts h2sm h2tr
  -- the second radial multiple `3D_θf/(1+z)`
  have h3sm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => 3 * Work.Spaces.Dth f z θ) := hsm.Dth.const_mul' 3
  have h3tr : Work.FTS.Nonlin.BdryTraces α m
      (fun z θ => 3 * Work.Spaces.Dth f z θ) := bdryTraces_const_mul_fts 3 htT
  have hYsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (1 / (1 + z)) * (3 * Work.Spaces.Dth f z θ)) :=
    smoothOpen_psi_mul_fts (ψ := fun z => 1 / (1 + z)) contDiffOn_oneDiv_fts h3sm
  have hYtr : Work.FTS.Nonlin.BdryTraces α m
      (fun z θ => (1 / (1 + z)) * (3 * Work.Spaces.Dth f z θ)) :=
    TracesAux.BdryTraces_psi_mul_open (k := m)
      (ψ := fun z => 1 / (1 + z)) (K := K) (x := fun z θ => 3 * Work.Spaces.Dth f z θ)
      hK0 hKb contDiffOn_oneDiv_fts h3sm h3tr
  -- the summand `f + D_z f`
  have hPsm : Work.FTS.EllipticEst.SmoothOpen (f + Work.Spaces.Dz f) :=
    Work.FTS.EllipticEst.smoothOpen_add (f := f) (g := Work.Spaces.Dz f) hsm hsm.Dz
  have hPtr : Work.FTS.Nonlin.BdryTraces α m (f + Work.Spaces.Dz f) :=
    Work.FTS.ClassC.bdryTraces_add (f := f) (g := Work.Spaces.Dz f) hsm hsm.Dz hf_tr htZ
  -- the sum of the two radial multiples, and its negative
  have hQsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      (1 / (1 + z)) * (2 * f z θ) + (1 / (1 + z)) * (3 * Work.Spaces.Dth f z θ)) :=
    Work.FTS.EllipticEst.smoothOpen_add
      (f := fun z θ => (1 / (1 + z)) * (2 * f z θ))
      (g := fun z θ => (1 / (1 + z)) * (3 * Work.Spaces.Dth f z θ)) hXsm hYsm
  have hQtr : Work.FTS.Nonlin.BdryTraces α m (fun z θ =>
      (1 / (1 + z)) * (2 * f z θ) + (1 / (1 + z)) * (3 * Work.Spaces.Dth f z θ)) :=
    Work.FTS.ClassC.bdryTraces_add
      (f := fun z θ => (1 / (1 + z)) * (2 * f z θ))
      (g := fun z θ => (1 / (1 + z)) * (3 * Work.Spaces.Dth f z θ)) hXsm hYsm hXtr hYtr
  have hNQsm : Work.FTS.EllipticEst.SmoothOpen ((-1 : ℝ) •
      (fun z θ => (1 / (1 + z)) * (2 * f z θ)
        + (1 / (1 + z)) * (3 * Work.Spaces.Dth f z θ))) :=
    hQsm.const_mul' (-1)
  have hNQtr : Work.FTS.Nonlin.BdryTraces α m ((-1 : ℝ) •
      (fun z θ => (1 / (1 + z)) * (2 * f z θ)
        + (1 / (1 + z)) * (3 * Work.Spaces.Dth f z θ))) :=
    Work.FTS.ClassC.bdryTraces_smul hQtr (-1)
  -- the operator unfolds to that combination
  have hL : Work.FTS.CoercivityFix.Lhat f = (f + Work.Spaces.Dz f) + (-1 : ℝ) •
      (fun z θ => (1 / (1 + z)) * (2 * f z θ)
        + (1 / (1 + z)) * (3 * Work.Spaces.Dth f z θ)) := by
    funext z θ
    rw [Work.FTS.CoercivityFix.Lhat_eq]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hL]
  exact Work.FTS.ClassC.bdryTraces_add (f := f + Work.Spaces.Dz f)
    (g := (-1 : ℝ) • (fun z θ => (1 / (1 + z)) * (2 * f z θ)
      + (1 / (1 + z)) * (3 * Work.Spaces.Dth f z θ)))
    hPsm hNQsm hPtr hNQtr

end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXA1w.AngularHardy =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The angular Hardy inequality for a mixed slot at the finite order `C⁴`

`angular_hardy_C4`: for a datum `f` which is `C⁴` on the open quadrant, honestly in `ℋ⁴` and
satisfying the boundary traces, and for `a + b ≤ 2`, `z > 0`, `θ ∈ (0,π/2)`,

  `(D_z^bD_θ^af(z,θ))² ≤ (100/(γ-1)) ∫_σ sin(2σ)^{-γ} (D_z^bD_θ^{a+1}f(z,σ))² dσ`.

The proof uses the `C¹`-slice angular Hardy inequality `hardyTheta_slice_C1` on the `θ`-slice
of the slot, the identity `∂_θ = D_θ / sin(2·)` and `D_θ(D_z^bD_θ^af) = D_z^bD_θ^{a+1}f`
(`Dth_mixed_eq_C4`).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXA1w

/-- The identity `∂_θ u = D_θ u / sin(2·)` on the open interval. -/
private lemma pth_eq_Dth_div {u : ℝ → ℝ → ℝ} {z σ : ℝ} (hσ : 0 < Real.sin (2 * σ)) :
    Work.Spaces.pth u z σ = Work.Spaces.Dth u z σ / Real.sin (2 * σ) := by
  rw [show Work.Spaces.Dth u z σ = Real.sin (2 * σ) * Work.Spaces.pth u z σ from rfl]
  field_simp

/-- The exponent identity `sin(2σ)^{2-γ} = sin(2σ)² · sin(2σ)^{-γ}`. -/
private lemma sin_rpow_split {β : ℝ} {σ : ℝ} (hσ : 0 < Real.sin (2 * σ)) :
    (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam β)
      = (Real.sin (2 * σ)) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β)) := by
  rw [show (2 - Work.Spaces.gam β) = ((2 : ℕ) : ℝ) + (-(Work.Spaces.gam β)) by
    push_cast; ring, Real.rpow_add hσ, Real.rpow_natCast]

theorem angular_hardy_C4 {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {f : ℝ → ℝ → ℝ}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem β 4 f) (htr : Work.FTS.Nonlin.BdryTraces β 4 f)
    (b a : ℕ) (hab : a + b ≤ 2) {z : ℝ} (hz : 0 < z) (θ : ℝ)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Work.Spaces.mixed b a f z θ) ^ 2 ≤
      (100 / (Work.Spaces.gam β - 1)) *
        ∫ σ in Work.Spaces.Iθ,
          (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β))
            * (Work.Spaces.mixed b (a + 1) f z σ) ^ 2 := by
  have hgam_ne : Work.Spaces.gam β ≠ 0 := ne_of_gt (Work.Spaces.gam_pos hβ)
  have hslice := contDiffOn_slice_mixed h4 b a 1 (by omega) hz
  have hpth : ContDiffOn ℝ 1
      (fun θ' => Work.Spaces.pth (Work.Spaces.mixed b a f) z θ') (Set.Ioo 0 (Real.pi / 2)) := by
    have h2 : ContDiffOn ℝ 1
        (Function.uncurry (Work.Spaces.pth (Work.Spaces.mixed b a f)))
        Work.FTS.EllipticEst.Q0 :=
      Work.FTS.StrongEps.contDiffOn_uncurry_pth_fin Work.FTS.EllipticEst.isOpen_Q0
        (contDiffOn_uncurry_mixed_Q0 h4 b a 2 (by omega))
    exact Work.FTS.StrongEps.EComparison.contDiffOn_slice_t hz h2
  have h0 : Filter.Tendsto (fun θ' => Work.Spaces.mixed b a f z θ') (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    Work.FTS.H2.tendsto_nhdsGT_zero_of_traces β hβ
      ((htr a b (by omega)).2 z (Set.mem_Ioi.mpr hz) |>.1)
  have hHk := hmem.1 z (Set.mem_Ici.mpr hz.le)
  have hbound : ∀ σ ∈ Work.Spaces.Iθ,
      (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β)) * (Work.Spaces.mixed b (a + 1) f z σ) ^ 2
        ≤ Work.Spaces.HkIntegrand β 4 f z σ := by
    intro σ hσ
    rcases eq_or_lt_of_le hσ.1 with h0' | hpos
    · subst h0'
      rw [show Real.sin (2 * (0 : ℝ)) = 0 by simp,
        Real.zero_rpow (neg_ne_zero.mpr hgam_ne), zero_mul]
      exact Work.Spaces.HkIntegrand_nonneg β 4 f z 0
    rcases eq_or_lt_of_le hσ.2 with h1' | hlt
    · subst h1'
      rw [show Real.sin (2 * (Real.pi / 2)) = 0 by
          rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi],
        Real.zero_rpow (neg_ne_zero.mpr hgam_ne), zero_mul]
      exact Work.Spaces.HkIntegrand_nonneg β 4 f z (Real.pi / 2)
    · have hσ' : σ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hpos, hlt⟩
      have hsin : 0 < Real.sin (2 * σ) := Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ'
      have hm1 : (Work.Spaces.mixed b (a + 1) f z σ) ^ 2
          ≤ (Work.Spaces.mixed b (a + 1) f z σ * Work.Spaces.w z) ^ 2 := by
        rw [mul_pow]
        simpa using mul_le_mul_of_nonneg_left (Work.FTS.H2.one_le_w_sq hz)
          (sq_nonneg (Work.Spaces.mixed b (a + 1) f z σ))
      have hm2 := mixed_slot_sq_w_le_HkIntegrand (f := f) hβ b (a + 1) (by omega) (by omega)
        z hσ'
      calc (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β))
            * (Work.Spaces.mixed b (a + 1) f z σ) ^ 2
          ≤ (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β))
              * ((Work.Spaces.mixed b (a + 1) f z σ * Work.Spaces.w z) ^ 2) :=
            mul_le_mul_of_nonneg_left hm1 (Real.rpow_nonneg hsin.le _)
        _ = (Work.Spaces.mixed b (a + 1) f z σ * Work.Spaces.w z) ^ 2
              * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β)) := by ring
        _ ≤ ((Real.sin (2 * σ)) ^ (Work.Spaces.gam β) * Work.Spaces.HkIntegrand β 4 f z σ)
              * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β)) :=
            mul_le_mul_of_nonneg_right hm2 (Real.rpow_nonneg hsin.le _)
        _ = Work.Spaces.HkIntegrand β 4 f z σ := by
            have hassoc : ((Real.sin (2 * σ)) ^ (Work.Spaces.gam β)
                  * Work.Spaces.HkIntegrand β 4 f z σ)
                  * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β))
                = Work.Spaces.HkIntegrand β 4 f z σ
                  * ((Real.sin (2 * σ)) ^ (Work.Spaces.gam β)
                    * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β))) := by ring
            rw [hassoc, ← Real.rpow_add hsin,
              show Work.Spaces.gam β + -(Work.Spaces.gam β) = 0 by ring,
              Real.rpow_zero, mul_one]
  have haesm : AEStronglyMeasurable
      (fun σ => (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β))
        * (Work.Spaces.mixed b (a + 1) f z σ) ^ 2) (volume.restrict Work.Spaces.Iθ) := by
    refine Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam β))
        * (Work.Spaces.mixed b (a + 1) f p.1 p.2) ^ 2) ?_ hz
    have hm : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed b (a + 1) f p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      (contDiffOn_uncurry_mixed_Q0 h4 b (a + 1) 0 (by omega)).continuousOn
    have hs : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam β)))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
        (fun p hp => Or.inl (ne_of_gt (Work.FTS.H2.sin_two_pos_of_mem_Ioo hp.2)))
    exact hs.mul (hm.pow 2)
  have hintW : MeasureTheory.IntegrableOn
      (fun σ => (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β))
        * (Work.Spaces.mixed b (a + 1) f z σ) ^ 2) Work.Spaces.Iθ :=
    hHk.mono' haesm (ae_restrict_of_forall_mem measurableSet_Icc fun σ hσ => by
      rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg hσ) _)
        (sq_nonneg _))]
      exact hbound σ hσ)
  have hint : MeasureTheory.IntegrableOn
      (fun σ => (Work.Spaces.pth (Work.Spaces.mixed b a f) z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam β)) Work.Spaces.Iθ := by
    refine hintW.congr ?_
    rw [Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo fun σ hσ => ?_
    have hsin : 0 < Real.sin (2 * σ) := Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ
    have hD : Work.Spaces.Dth (Work.Spaces.mixed b a f) z σ
        = Work.Spaces.mixed b (a + 1) f z σ :=
      Work.FTS_RegExport.C4.Dth_mixed_eq_C4 h4 b a (by omega) hz hσ
    show (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β)) * (Work.Spaces.mixed b (a + 1) f z σ) ^ 2
        = (Work.Spaces.pth (Work.Spaces.mixed b a f) z σ) ^ 2
          * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam β)
    rw [pth_eq_Dth_div hsin, hD, sin_rpow_split (β := β) hsin]
    field_simp <;> try ring
  have hHardy := Work.FTS_RegExport.C4.hardyTheta_slice_C1 (g := Work.Spaces.mixed b a f)
    hβ hβ1 hz hslice hpth h0 hint θ hθ
  have hcongr : (∫ σ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.mixed b a f) z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam β))
      = ∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β))
          * (Work.Spaces.mixed b (a + 1) f z σ) ^ 2 := by
    refine Work.FTS.EllipticEst.setIntegral_Iθ_congr_of_forall_Ioo fun σ hσ => ?_
    have hsin : 0 < Real.sin (2 * σ) := Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ
    have hD : Work.Spaces.Dth (Work.Spaces.mixed b a f) z σ
        = Work.Spaces.mixed b (a + 1) f z σ :=
      Work.FTS_RegExport.C4.Dth_mixed_eq_C4 h4 b a (by omega) hz hσ
    rw [pth_eq_Dth_div hsin, hD, sin_rpow_split (β := β) hsin]
    field_simp <;> try ring
  rw [← hcongr]
  exact hHardy

end Work.FTS_RegExport.RXA1w
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXA1w.SliceAgmon =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The a.e. weighted slice bound

`mixed_slice_pointwise_le`: for `a + b ≤ 2` and `z > 0`,

  `sin(2σ)^{-γ} (D_z^bD_θ^{a+1}f(z,σ))² ≤ 5 z³/(1+z)⁴ · ∫_s HkIntegrand β 4 f s σ`  a.e. in `σ`.

This is the weighted radial Agmon inequality `agmonZ_weight` applied to the radial slice
`s ↦ D_z^bD_θ^{a+1}f(s,σ)`, whose two Agmon integrals are dominated by the `ℋ⁴`-integrand
through `mixed_slot_sq_w_le_HkIntegrand`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXA1w

/-- `(1+z)⁴/z³ = w(z)² · z`. -/
private lemma w_sq_mul_eq {z : ℝ} : (1 + z) ^ 4 / z ^ 3 = (Work.Spaces.w z) ^ 2 * z := by
  rw [Work.Spaces.w, div_pow]
  field_simp

theorem mixed_slice_pointwise_le {β : ℝ} (hβ : 0 < β)
    {f : ℝ → ℝ → ℝ} (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem β 4 f) (htr : Work.FTS.Nonlin.BdryTraces β 4 f)
    (b a : ℕ) (hab : a + b ≤ 2) {z : ℝ} (hz : 0 < z) :
    ∀ᵐ σ ∂(volume.restrict Work.Spaces.Iθ),
      (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β))
          * (Work.Spaces.mixed b (a + 1) f z σ) ^ 2
        ≤ 5 * (z ^ 3 / (1 + z) ^ 4)
            * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand β 4 f s σ) := by
  filter_upwards [Work.FTS_RegExport.C4.ae_integrableOn_mixed_sq_w_C4 hβ h4 hmem b (a + 1)
      (by omega) (by omega),
    Work.FTS_RegExport.C4.ae_integrableOn_mixed_sq_w_C4 hβ h4 hmem (b + 1) (a + 1)
      (by omega) (by omega),
    Work.FTS_RegExport.C4.ae_integrableOn_HkIntegrand_slice_C4 h4 hmem,
    Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hIntA hIntB hIntHk hσ
  have hsin : 0 < Real.sin (2 * σ) := Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ
  have hint1 : MeasureTheory.IntegrableOn
      (fun x => (Work.Spaces.mixed b (a + 1) f x σ * Work.Spaces.w x) ^ 2)
      Work.Spaces.Iz :=
    hIntA.congr (Filter.Eventually.of_forall fun x => by
      show (Work.Spaces.mixed b (a + 1) f x σ) ^ 2 * (Work.Spaces.w x) ^ 2
          = (Work.Spaces.mixed b (a + 1) f x σ * Work.Spaces.w x) ^ 2
      rw [mul_pow])
  have hint2 : MeasureTheory.IntegrableOn
      (fun x => (x * deriv (fun s => Work.Spaces.mixed b (a + 1) f s σ) x
        * Work.Spaces.w x) ^ 2) Work.Spaces.Iz :=
    hIntB.congr (Filter.Eventually.of_forall fun x => by
      show (Work.Spaces.mixed (b + 1) (a + 1) f x σ) ^ 2 * (Work.Spaces.w x) ^ 2
          = (x * deriv (fun s => Work.Spaces.mixed b (a + 1) f s σ) x * Work.Spaces.w x) ^ 2
      rw [show x * deriv (fun s => Work.Spaces.mixed b (a + 1) f s σ) x
          = Work.Spaces.mixed (b + 1) (a + 1) f x σ from rfl, mul_pow])
  have hdec : Filter.Tendsto
      (fun x => x * (Work.Spaces.mixed b (a + 1) f x σ * Work.Spaces.w x) ^ 2)
      Filter.atTop (𝓝 0) := ((htr (a + 1) b (by omega)).1 σ hσ).2
  have hcd : ContDiffOn ℝ 1 (fun s => Work.Spaces.mixed b (a + 1) f s σ) (Set.Ioi 0) :=
    Work.FTS.StrongEps.EComparison.contDiffOn_slice_z hσ
      (contDiffOn_uncurry_mixed_Q0 h4 b (a + 1) 1 (by omega))
  have hvderiv : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun s => Work.Spaces.mixed b (a + 1) f s σ)
        (deriv (fun s => Work.Spaces.mixed b (a + 1) f s σ) x) x := by
    intro x hx
    exact ((hcd.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds hx)).hasDerivAt
  have hagmon := agmonZ_weight hz hvderiv hint1 hint2 hdec
  have hagmon' : (Work.Spaces.mixed b (a + 1) f z σ) ^ 2 * (Work.Spaces.w z) ^ 2 * z
      ≤ 4 * (∫ x in Work.Spaces.Iz,
            (Work.Spaces.mixed b (a + 1) f x σ * Work.Spaces.w x) ^ 2)
          + ∫ x in Work.Spaces.Iz,
              (x * deriv (fun s => Work.Spaces.mixed b (a + 1) f s σ) x
                * Work.Spaces.w x) ^ 2 := hagmon
  have hA_le : (∫ x in Work.Spaces.Iz,
        (Work.Spaces.mixed b (a + 1) f x σ * Work.Spaces.w x) ^ 2)
      ≤ (Real.sin (2 * σ)) ^ (Work.Spaces.gam β)
          * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand β 4 f s σ) := by
    rw [← MeasureTheory.integral_const_mul]
    refine integral_mono_of_nonneg
      (ae_restrict_of_forall_mem measurableSet_Ici fun x _ => sq_nonneg _)
      (hIntHk.const_mul _)
      (ae_restrict_of_forall_mem measurableSet_Ici fun x _ =>
        mixed_slot_sq_w_le_HkIntegrand (f := f) hβ b (a + 1) (by omega) (by omega) x hσ)
  have hB_le : (∫ x in Work.Spaces.Iz,
        (x * deriv (fun s => Work.Spaces.mixed b (a + 1) f s σ) x * Work.Spaces.w x) ^ 2)
      ≤ (Real.sin (2 * σ)) ^ (Work.Spaces.gam β)
          * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand β 4 f s σ) := by
    have heq : (∫ x in Work.Spaces.Iz,
          (x * deriv (fun s => Work.Spaces.mixed b (a + 1) f s σ) x
            * Work.Spaces.w x) ^ 2)
        = ∫ x in Work.Spaces.Iz,
            (Work.Spaces.mixed (b + 1) (a + 1) f x σ * Work.Spaces.w x) ^ 2 :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by
        show (x * deriv (fun s => Work.Spaces.mixed b (a + 1) f s σ) x * Work.Spaces.w x) ^ 2
            = (Work.Spaces.mixed (b + 1) (a + 1) f x σ * Work.Spaces.w x) ^ 2
        rw [show x * deriv (fun s => Work.Spaces.mixed b (a + 1) f s σ) x
            = Work.Spaces.mixed (b + 1) (a + 1) f x σ from rfl])
    rw [heq, ← MeasureTheory.integral_const_mul]
    refine integral_mono_of_nonneg
      (ae_restrict_of_forall_mem measurableSet_Ici fun x _ => sq_nonneg _)
      (hIntHk.const_mul _)
      (ae_restrict_of_forall_mem measurableSet_Ici fun x _ =>
        mixed_slot_sq_w_le_HkIntegrand (f := f) hβ (b + 1) (a + 1) (by omega) (by omega) x hσ)
  have hsum : (Work.Spaces.mixed b (a + 1) f z σ) ^ 2 * (Work.Spaces.w z) ^ 2 * z
      ≤ 5 * ((Real.sin (2 * σ)) ^ (Work.Spaces.gam β)
          * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand β 4 f s σ)) := by
    refine le_trans hagmon' ?_
    have h5 : (4 : ℝ) * ((Real.sin (2 * σ)) ^ (Work.Spaces.gam β)
          * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand β 4 f s σ))
        + (Real.sin (2 * σ)) ^ (Work.Spaces.gam β)
          * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand β 4 f s σ)
        = 5 * ((Real.sin (2 * σ)) ^ (Work.Spaces.gam β)
          * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand β 4 f s σ)) := by ring
    have := add_le_add (mul_le_mul_of_nonneg_left hA_le (by norm_num : (0 : ℝ) ≤ 4)) hB_le
    linarith [this, h5]
  have hρpos : 0 < (Work.Spaces.w z) ^ 2 * z := by
    have h1 := Work.FTS.H2.one_le_w_sq hz
    nlinarith [hz, h1]
  have hcancel : (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β))
      * (Real.sin (2 * σ)) ^ (Work.Spaces.gam β) = 1 := by
    rw [← Real.rpow_add hsin, show -(Work.Spaces.gam β) + Work.Spaces.gam β = 0 by ring,
      Real.rpow_zero]
  have hcount : 0 ≤ (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β))
      / ((Work.Spaces.w z) ^ 2 * z) :=
    div_nonneg (Real.rpow_nonneg hsin.le _) hρpos.le
  have h2 := mul_le_mul_of_nonneg_left hsum hcount
  have hL : (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β)) / ((Work.Spaces.w z) ^ 2 * z)
        * ((Work.Spaces.mixed b (a + 1) f z σ) ^ 2 * (Work.Spaces.w z) ^ 2 * z)
      = (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β))
        * (Work.Spaces.mixed b (a + 1) f z σ) ^ 2 := by
    have hwz : Work.Spaces.w z ≠ 0 := by
      intro h0; rw [h0] at hρpos; simp at hρpos
    have hz0 : z ≠ 0 := ne_of_gt hz
    field_simp <;> try ring
  have hR : (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β)) / ((Work.Spaces.w z) ^ 2 * z)
        * (5 * ((Real.sin (2 * σ)) ^ (Work.Spaces.gam β)
          * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand β 4 f s σ)))
      = 5 * (z ^ 3 / (1 + z) ^ 4)
          * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand β 4 f s σ) := by
    rw [← w_sq_mul_eq]
    have h1 : (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β)) / ((1 + z) ^ 4 / z ^ 3)
        = z ^ 3 / (1 + z) ^ 4 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β)) := by
      field_simp <;> try ring
    rw [h1]
    have h2 : z ^ 3 / (1 + z) ^ 4 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β))
          * (5 * ((Real.sin (2 * σ)) ^ (Work.Spaces.gam β)
            * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand β 4 f s σ)))
        = 5 * (z ^ 3 / (1 + z) ^ 4)
            * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand β 4 f s σ)
            * ((Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β))
              * (Real.sin (2 * σ)) ^ (Work.Spaces.gam β)) := by ring
    rw [h2, hcancel, mul_one]
  rw [hL, hR] at h2
  exact h2

end Work.FTS_RegExport.RXA1w
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.HkMinPrep =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.HkMinPrep`

Elementary preparation for the pointwise bound `hkMem_pointwise_min`: the weight `w` is
nonnegative, the a.e. transfer from the open angular interval `(0,π/2)` to `Iθ`, the algebraic
comparison `(a b)² ≤ (a c)²` for `0 ≤ b ≤ c`, the notion of an *admissible slot* of
`HkIntegrand α 4`, and the pointwise domination of an admissible slot by the integrand.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- `w ≥ 0` everywhere. -/
theorem w_nonneg (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]; positivity

/-- `volume.restrict Iθ = volume.restrict (Ioo 0 (π/2))`. -/
theorem restrict_Iθ_eq_restrict_Ioo :
    MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  rw [Work.Spaces.Iθ]
  exact (Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
      (b := Real.pi / 2))).symm

/-- An a.e. statement on `Iθ` holds if it holds at every interior angle. -/
theorem ae_restrict_Iθ_of_Ioo {p : ℝ → Prop}
    (h : ∀ σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), p σ) :
    ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), p σ := by
  rw [restrict_Iθ_eq_restrict_Ioo]
  exact ae_restrict_of_forall_mem measurableSet_Ioo h

/-- A function continuous on the open angular interval is a.e. strongly measurable for
`volume.restrict Iθ`. -/
theorem aestrongly_Iθ_of_continuousOn {u : ℝ → ℝ}
    (h : ContinuousOn u (Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    MeasureTheory.AEStronglyMeasurable u (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  rw [restrict_Iθ_eq_restrict_Ioo]
  exact h.aestronglyMeasurable measurableSet_Ioo

/-- The interval integral over `Ioi 0` is the set integral over `Iz = Ici 0`. -/
theorem integral_Ioi_eq_integral_Iz (f : ℝ → ℝ) :
    (∫ x in Set.Ioi (0 : ℝ), f x) = ∫ x in Work.Spaces.Iz, f x := by
  rw [Work.Spaces.Iz, MeasureTheory.restrict_Ioi_eq_restrict_Ici]

/-- `(a b)² ≤ (a c)²` for `0 ≤ b ≤ c`. -/
theorem sq_mul_le_sq_mul {a b c : ℝ} (hb : 0 ≤ b) (hbc : b ≤ c) : (a * b) ^ 2 ≤ (a * c) ^ 2 := by
  have h1 : b ^ 2 ≤ c ^ 2 := by nlinarith
  calc (a * b) ^ 2 = a ^ 2 * b ^ 2 := by ring
    _ ≤ a ^ 2 * c ^ 2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg a)
    _ = (a * c) ^ 2 := by ring

/-- The slots of `HkIntegrand α 4`: the mixed ones (`1 ≤ i`, `i + j ≤ 4`) and the pure radial
ones (`i = 0`, `j ≤ 4`). -/
def FTSAdm (j i : ℕ) : Prop := (1 ≤ i ∧ i + j ≤ 4) ∨ (i = 0 ∧ j ≤ 4)

/-- At an interior angle, the plain-`w`-weighted square of an admissible slot is dominated by
the `ℋ⁴`-integrand. -/
theorem slot_pointwise_le {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ} (j i : ℕ) (hadm : FTSAdm j i)
    (x : ℝ) {σ : ℝ} (hσ : σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Work.Spaces.mixed j i f x σ) ^ 2 * (Work.Spaces.w x) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 f x σ := by
  have hsin0 : 0 < Real.sin (2 * σ) := Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ
  have hsinle : Real.sin (2 * σ) ≤ 1 := Real.sin_le_one _
  rcases hadm with ⟨hi1, hij⟩ | ⟨hi0, hj4⟩
  · -- mixed slot: compare with the `Wt`-weighted slot
    have hbase := Work.Spaces.sq_le_HkIntegrand_mixed α 4 f x σ i j hi1 hij
    have hle : (Work.Spaces.mixed j i f x σ * Work.Spaces.w x) ^ 2
        ≤ (Work.Spaces.mixed j i f x σ * Work.Spaces.Wt α x σ) ^ 2 := by
      refine sq_mul_le_sq_mul (a := Work.Spaces.mixed j i f x σ) (w_nonneg x) ?_
      have hspos : 0 < (Real.sin (2 * σ)) ^ (Work.Spaces.gam α / 2) :=
        Real.rpow_pos_of_pos hsin0 _
      have hsle : (Real.sin (2 * σ)) ^ (Work.Spaces.gam α / 2) ≤ 1 :=
        Real.rpow_le_one hsin0.le hsinle (by have := Work.Spaces.gam_pos hα; linarith)
      have hone : (1 : ℝ) ≤ (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α / 2)) := by
        rw [Real.rpow_neg hsin0.le]
        simpa [one_div] using one_le_one_div hspos hsle
      calc Work.Spaces.w x = Work.Spaces.w x * 1 := (mul_one _).symm
        _ ≤ Work.Spaces.w x * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α / 2)) :=
            mul_le_mul_of_nonneg_left hone (w_nonneg x)
        _ = Work.Spaces.w x * Work.Spaces.wTheta α σ := rfl
    calc (Work.Spaces.mixed j i f x σ) ^ 2 * (Work.Spaces.w x) ^ 2
        = (Work.Spaces.mixed j i f x σ * Work.Spaces.w x) ^ 2 := by ring
      _ ≤ (Work.Spaces.mixed j i f x σ * Work.Spaces.Wt α x σ) ^ 2 := hle
      _ ≤ Work.Spaces.HkIntegrand α 4 f x σ := hbase
  · -- pure radial slot
    subst hi0
    have hbase := Work.Spaces.sq_le_HkIntegrand_z α 4 f x σ j (by omega)
    have hle : (Work.Spaces.DzIter j f x σ * Work.Spaces.w x) ^ 2
        ≤ (Work.Spaces.DzIter j f x σ
            * (Work.Spaces.w x / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      refine sq_mul_le_sq_mul (a := Work.Spaces.DzIter j f x σ) (w_nonneg x) ?_
      have hspos : 0 < (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2) :=
        Real.rpow_pos_of_pos hsin0 _
      have hsle : (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2) ≤ 1 :=
        Real.rpow_le_one hsin0.le hsinle (by have := Work.Spaces.eta_pos; linarith)
      calc Work.Spaces.w x = Work.Spaces.w x * 1 := (mul_one _).symm
        _ ≤ Work.Spaces.w x * (1 / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2)) :=
            mul_le_mul_of_nonneg_left (one_le_one_div hspos hsle) (w_nonneg x)
        _ = Work.Spaces.w x / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2) := by ring
    calc (Work.Spaces.mixed j 0 f x σ) ^ 2 * (Work.Spaces.w x) ^ 2
        = (Work.Spaces.DzIter j f x σ * Work.Spaces.w x) ^ 2 := by
          rw [Work.Spaces.mixed_zero_right]; ring
      _ ≤ _ := hle
      _ ≤ Work.Spaces.HkIntegrand α 4 f x σ := hbase

end Work.FTS_RegExport.RXT
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Slots.v2_theta_sup_aux =====
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

/-! ## Elementary helpers on the weight `w` -/

theorem w_nonneg_aux (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]; positivity

theorem w_pos_aux {z : ℝ} (hz : 0 < z) : 0 < Work.Spaces.w z := by
  rw [Work.Spaces.w]; positivity

theorem sq_mul_le_sq_mul_aux {a b c : ℝ} (hb : 0 ≤ b) (hbc : b ≤ c) :
    (a * b) ^ 2 ≤ (a * c) ^ 2 := by
  have h1 : b ^ 2 ≤ c ^ 2 := by nlinarith
  calc (a * b) ^ 2 = a ^ 2 * b ^ 2 := by ring
    _ ≤ a ^ 2 * c ^ 2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg a)
    _ = (a * c) ^ 2 := by ring

/-! ## The angular interval, its interior, and a.e. strong measurability -/

theorem restrict_Iθ_eq_Ioo_aux :
    MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  rw [Work.Spaces.Iθ]
  exact (MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume)
      (a := (0 : ℝ)) (b := Real.pi / 2))).symm

theorem aesm_Iθ_of_continuousOn_Ioo_aux {u : ℝ → ℝ}
    (hu : ContinuousOn u (Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    AEStronglyMeasurable u (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  rw [restrict_Iθ_eq_Ioo_aux]
  exact hu.aestronglyMeasurable measurableSet_Ioo

/-! ## The `θ`-slice of a function continuous on the open quadrant -/

theorem continuousOn_slice_of_continuousOn_Q0_aux {g : ℝ → ℝ → ℝ}
    (hg : ContinuousOn (Function.uncurry g) Work.FTS.EllipticEst.Q0) {s : ℝ} (hs : 0 < s) :
    ContinuousOn (fun θ => g s θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hlin : ContinuousOn (fun θ : ℝ => (s, θ)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (continuous_const.prodMk continuous_id).continuousOn
  have hmaps : Set.MapsTo (fun θ : ℝ => (s, θ)) (Set.Ioo (0 : ℝ) (Real.pi / 2))
      Work.FTS.EllipticEst.Q0 := fun θ hθ => Work.FTS.EllipticEst.mem_Q0.mpr ⟨hs, hθ⟩
  exact (hg.comp hlin hmaps).congr (fun θ _ => rfl)

/-- The interior `θ`-slice of `∂_θ(D_z^bD_θ^af)` is continuous: on the open quadrant it equals
`(D_z^bD_θ^{a+1}f)/sin(2θ)` (`Dth_mixed_eq_C4`), and both factors are continuous there. -/
theorem continuousOn_pth_mixed_slice_aux {f : ℝ → ℝ → ℝ}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (b a : ℕ) (hab : a + b + 1 ≤ 4) {s : ℝ} (hs : 0 < s) :
    ContinuousOn (fun σ => Work.Spaces.pth (Work.Spaces.mixed b a f) s σ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hm : ContinuousOn (fun σ => Work.Spaces.mixed b (a + 1) f s σ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    continuousOn_slice_of_continuousOn_Q0_aux
      ((Work.FTS_RegExport.RXA1w.contDiffOn_uncurry_mixed_Q0 h4 b (a + 1) 0 (by omega)).continuousOn)
      hs
  have hsin : ContinuousOn (fun σ : ℝ => Real.sin (2 * σ)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hdiv := hm.div hsin (fun σ hσ => ne_of_gt (Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ))
  refine hdiv.congr (fun σ hσ => ?_)
  have hD := Work.FTS_RegExport.C4.Dth_mixed_eq_C4 h4 b a hab hs hσ
  rw [Work.Spaces.Dth] at hD
  simp only [Pi.div_apply]
  rw [eq_div_iff (ne_of_gt (Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ)), mul_comm]
  exact hD

/-! ## Pointwise domination of a slot by the `ℋ⁴`-integrand -/

/-- At an interior angle the `w`-weighted square of the slot `D_z^bD_θ^a f` (`a + b ≤ 4`) is
dominated by `HkIntegrand α 4 f`: for `a ≥ 1` the slot occurs in the mixed sum with the full
weight `W = w·sin(2θ)^{-γ/2}` (and `sin^γ ≤ 1`), for `a = 0` it occurs in the `D_z`-sum with
`w/sin^{η/2}` (and `sin^{η/2} ≤ 1`). -/
theorem slot_le_HkIntegrand_aux {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ} (b a : ℕ)
    (hab : a + b ≤ 4) (s : ℝ) {σ : ℝ} (hσ : σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Work.Spaces.mixed b a f s σ * Work.Spaces.w s) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 f s σ := by
  have hsin : 0 < Real.sin (2 * σ) := Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ
  have hsinle : Real.sin (2 * σ) ≤ 1 := Real.sin_le_one _
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    rw [Work.Spaces.mixed_zero_right]
    refine le_trans ?_ (Work.Spaces.sq_le_HkIntegrand_z α 4 f s σ b (by omega))
    refine sq_mul_le_sq_mul_aux (w_nonneg_aux s) ?_
    have hspos : 0 < (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hsin _
    have hsle : (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2) ≤ 1 :=
      Real.rpow_le_one hsin.le hsinle (by have := Work.Spaces.eta_pos; linarith)
    calc Work.Spaces.w s = Work.Spaces.w s * 1 := (mul_one _).symm
      _ ≤ Work.Spaces.w s * (1 / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2)) :=
          mul_le_mul_of_nonneg_left (one_le_one_div hspos hsle) (w_nonneg_aux s)
      _ = Work.Spaces.w s / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2) := by ring
  · refine le_trans
      (Work.FTS_RegExport.RXA1w.mixed_slot_sq_w_le_HkIntegrand hα b a ha (by omega) s hσ) ?_
    have hsinγ : Real.sin (2 * σ) ^ (Work.Spaces.gam α) ≤ 1 :=
      Real.rpow_le_one hsin.le hsinle (Work.Spaces.gam_pos hα).le
    calc Real.sin (2 * σ) ^ (Work.Spaces.gam α) * Work.Spaces.HkIntegrand α 4 f s σ
        ≤ 1 * Work.Spaces.HkIntegrand α 4 f s σ :=
          mul_le_mul_of_nonneg_right hsinγ (Work.Spaces.HkIntegrand_nonneg α 4 f s σ)
      _ = Work.Spaces.HkIntegrand α 4 f s σ := one_mul _

/-- The companion bound for the `θ`-derivative slot: `(D_z^bD_θ^{a+1}f · w)² sin(2θ)^{-γ}`
is the `Wt`-weighted mixed slot of order `a + 1`, hence dominated by `HkIntegrand α 4 f`. -/
theorem slot_sin_le_HkIntegrand_aux {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ} (b a : ℕ)
    (hab : a + 1 + b ≤ 4) (s : ℝ) {σ : ℝ} (hσ : σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Work.Spaces.mixed b (a + 1) f s σ * Work.Spaces.w s) ^ 2
        * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
      ≤ Work.Spaces.HkIntegrand α 4 f s σ := by
  have hsin : 0 < Real.sin (2 * σ) := Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ
  have h1 := Work.Spaces.sq_le_HkIntegrand_mixed α 4 f s σ (a + 1) b (by omega) (by omega)
  have hid : (Work.Spaces.mixed b (a + 1) f s σ * Work.Spaces.Wt α s σ) ^ 2
      = (Work.Spaces.mixed b (a + 1) f s σ * Work.Spaces.w s) ^ 2
        * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) := by
    have hsq : ((Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
        = (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) := by
      rw [sq, ← Real.rpow_add hsin,
        show -(Work.Spaces.gam α / 2) + -(Work.Spaces.gam α / 2) = -(Work.Spaces.gam α) by ring]
    rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow, mul_pow, hsq]
    ring
  rw [hid] at h1
  exact h1

/-! ## Integrability of the two angular integrands of the mean–variation bound -/

theorem integrable_slot_sq_aux {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 f) (b a : ℕ) (hab : a + b ≤ 3) {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun σ => (Work.Spaces.mixed b a f s σ) ^ 2) Work.Spaces.Iθ := by
  have hsI : s ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hs.le
  refine (hmem.1 s hsI).div_const ((Work.Spaces.w s) ^ 2) |>.mono'
    (aesm_Iθ_of_continuousOn_Ioo_aux
      (((Work.FTS_RegExport.RXA1w.contDiffOn_slice_mixed h4 b a 1 (by omega) hs).continuousOn).pow 2))
    ?_
  filter_upwards [Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hσ
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hkey : (Work.Spaces.mixed b a f s σ) ^ 2
      = (Work.Spaces.mixed b a f s σ * Work.Spaces.w s) ^ 2 / (Work.Spaces.w s) ^ 2 := by
    rw [mul_pow, eq_div_iff (by have := w_pos_aux hs; positivity)]
  rw [hkey]
  exact div_le_div_of_nonneg_right
    (slot_le_HkIntegrand_aux hα b a (by omega) s hσ) (sq_nonneg _)

theorem integrable_pth_sq_sin_aux {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 f) (b a : ℕ) (hab : a + b ≤ 3) {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun σ => (Work.Spaces.pth (Work.Spaces.mixed b a f) s σ) ^ 2
      * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
  have hsI : s ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hs.le
  have hcont : ContinuousOn
      (fun σ => (Work.Spaces.pth (Work.Spaces.mixed b a f) s σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    ((continuousOn_pth_mixed_slice_aux h4 b a (by omega) hs).pow 2).mul
      (((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
        (fun σ hσ => Or.inl (ne_of_gt (Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ))))
  refine (hmem.1 s hsI).div_const ((Work.Spaces.w s) ^ 2) |>.mono'
    (aesm_Iθ_of_continuousOn_Ioo_aux hcont) ?_
  filter_upwards [Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hσ
  have hsin : 0 < Real.sin (2 * σ) := Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin.le _))]
  have hpth : Work.Spaces.pth (Work.Spaces.mixed b a f) s σ
      = Work.Spaces.mixed b (a + 1) f s σ / Real.sin (2 * σ) := by
    have hD := Work.FTS_RegExport.C4.Dth_mixed_eq_C4 h4 b a (by omega) hs hσ
    rw [Work.Spaces.Dth] at hD
    rw [eq_div_iff (ne_of_gt hsin), mul_comm]
    exact hD
  rw [hpth]
  have hkey : (Work.Spaces.mixed b (a + 1) f s σ / Real.sin (2 * σ)) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
      = ((Work.Spaces.mixed b (a + 1) f s σ * Work.Spaces.w s) ^ 2
          * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))) / (Work.Spaces.w s) ^ 2 := by
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
  rw [hkey]
  exact div_le_div_of_nonneg_right
    (slot_sin_le_HkIntegrand_aux hα b a (by omega) s hσ) (sq_nonneg _)

/-! ## The angular mean–variation bound -/

/-- `(x^{p/2})² = x^p` for `x > 0`. -/
private theorem rpow_sq_aux {x p : ℝ} (hx : 0 < x) : (x ^ (p / 2)) ^ 2 = x ^ p := by
  rw [sq, ← Real.rpow_add hx, show p / 2 + p / 2 = p by ring]

/-- **Cauchy–Schwarz against the angular weight on `(a,b]`.**  For `0 < a`, `b < π/2` and
`a ≤ b`,

  `(∫_{(a,b]} g')² ≤ (∫_{(a,b]} g'² sin(2θ)^{2-γ}) (∫_{(a,b]} sin(2θ)^{γ-2})`.

On the closure of `(a,b]` the weight `sin(2·)` is bounded below by `sin(2a) > 0`, so both factors
`g' sin(2·)^{(2-γ)/2}` and `sin(2·)^{(γ-2)/2}` are continuous there and square integrable, and
`Work.Spaces.cs_integral` applies. -/
theorem cs_Ioc_aux {γ : ℝ} {g' : ℝ → ℝ}
    (hg'c : ContinuousOn g' (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hint2 : MeasureTheory.IntegrableOn
      (fun θ => g' θ ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)) Work.Spaces.Iθ)
    (hGint : MeasureTheory.IntegrableOn
      (fun θ => (Real.sin (2 * θ)) ^ (γ - 2)) Work.Spaces.Iθ)
    {a b : ℝ} (ha : 0 < a) (hb : b < Real.pi / 2) (hab : a ≤ b) :
    (∫ x in Set.Ioc a b, g' x) ^ 2
      ≤ (∫ x in Set.Ioc a b, g' x ^ 2 * (Real.sin (2 * x)) ^ (2 - γ))
        * (∫ x in Set.Ioc a b, (Real.sin (2 * x)) ^ (γ - 2)) := by
  have hsub : Set.Ioc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
    ⟨lt_trans ha hx.1, lt_of_le_of_lt hx.2 hb⟩
  have hsubIθ : Set.Ioc a b ⊆ Work.Spaces.Iθ := fun x hx =>
    ⟨le_of_lt (lt_trans ha hx.1), le_of_lt (lt_of_le_of_lt hx.2 hb)⟩
  have hsinpos : ∀ x ∈ Set.Ioc a b, 0 < Real.sin (2 * x) := fun x hx =>
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1, ha])
      (by linarith [hx.2, hb, Real.pi_pos])
  have hsincont : ContinuousOn (fun x : ℝ => Real.sin (2 * x)) (Set.Ioc a b) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  set A : ℝ → ℝ := fun x => g' x * (Real.sin (2 * x)) ^ ((2 - γ) / 2) with hA
  set B : ℝ → ℝ := fun x => (Real.sin (2 * x)) ^ ((γ - 2) / 2) with hB
  have hAcont : ContinuousOn A (Set.Ioc a b) :=
    (hg'c.mono hsub).mul (hsincont.rpow_const (fun x hx => Or.inl (ne_of_gt (hsinpos x hx))))
  have hBcont : ContinuousOn B (Set.Ioc a b) :=
    hsincont.rpow_const (fun x hx => Or.inl (ne_of_gt (hsinpos x hx)))
  have hAesm : AEStronglyMeasurable A (MeasureTheory.volume.restrict (Set.Ioc a b)) :=
    hAcont.aestronglyMeasurable measurableSet_Ioc
  have hBesm : AEStronglyMeasurable B (MeasureTheory.volume.restrict (Set.Ioc a b)) :=
    hBcont.aestronglyMeasurable measurableSet_Ioc
  have hsqA : ∀ x ∈ Set.Ioc a b, A x ^ 2 = g' x ^ 2 * (Real.sin (2 * x)) ^ (2 - γ) := by
    intro x hx
    simp only [hA]
    rw [mul_pow, rpow_sq_aux (hsinpos x hx)]
  have hsqB : ∀ x ∈ Set.Ioc a b, B x ^ 2 = (Real.sin (2 * x)) ^ (γ - 2) := by
    intro x hx
    simp only [hB]
    rw [rpow_sq_aux (hsinpos x hx)]
  have hprod : ∀ x ∈ Set.Ioc a b, A x * B x = g' x := by
    intro x hx
    simp only [hA, hB]
    rw [mul_assoc, ← Real.rpow_add (hsinpos x hx),
      show (2 - γ) / 2 + (γ - 2) / 2 = 0 by ring, Real.rpow_zero, mul_one]
  have hA2int : MeasureTheory.Integrable (fun x => A x ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioc a b)) :=
    (hint2.mono_set hsubIθ).congr
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => (hsqA x hx).symm))
  have hB2int : MeasureTheory.Integrable (fun x => B x ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioc a b)) :=
    (hGint.mono_set hsubIθ).congr
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => (hsqB x hx).symm))
  have hMemA : MeasureTheory.MemLp A 2 (MeasureTheory.volume.restrict (Set.Ioc a b)) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hAesm).mpr hA2int
  have hMemB : MeasureTheory.MemLp B 2 (MeasureTheory.volume.restrict (Set.Ioc a b)) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hBesm).mpr hB2int
  have hcs := Work.Spaces.cs_integral (u := A) (v := B) (s := Set.Ioc a b) hMemA hMemB
  have hleft : (∫ x in Set.Ioc a b, A x * B x) = ∫ x in Set.Ioc a b, g' x :=
    MeasureTheory.integral_congr_ae
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc hprod)
  rw [← hleft]
  refine le_trans hcs (le_of_eq ?_)
  congr 1
  · exact MeasureTheory.integral_congr_ae
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => hsqA x hx))
  · exact MeasureTheory.integral_congr_ae
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => hsqB x hx))

/-- **Angular mean–variation (Agmon) bound on the open interval.**  If `g` has derivative `g'`
on `(0,π/2)`, `g'` is continuous there, and both `g²` and `g'² sin(2θ)^{2-γ}` are integrable
on `Iθ` (the latter being the case for `1 < γ ≤ 2`), then for every interior `θ`

  `g θ² ≤ (8/π) ∫_{Iθ} g² + 2 (∫_{Iθ} sin(2θ)^{γ-2}) (∫_{Iθ} g'² sin(2θ)^{2-γ})`.

The companion angle `θ₀` minimising `g²` on the fixed interval `[π/8,3π/8] ⊂ (0,π/2)` gives
`g(θ₀)² ≤ (4/π)∫_{Iθ} g²` (min ≤ average), and the fundamental theorem of calculus together
with Cauchy–Schwarz against the weight `sin(2θ)^{γ-2}` bounds the variation
`(g θ - g θ₀)² ≤ (∫_{Iθ} sin^{γ-2})(∫_{Iθ} g'² sin^{2-γ})`; combine with
`g θ² ≤ 2(g θ - g θ₀)² + 2g(θ₀)²`. -/
theorem angular_meanVar_aux {γ : ℝ} (hγ1 : 1 < γ) (hγ2 : γ ≤ 2) {g g' : ℝ → ℝ}
    (hg : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt g (g' θ) θ)
    (hg'c : ContinuousOn g' (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hint1 : MeasureTheory.IntegrableOn (fun θ => g θ ^ 2) Work.Spaces.Iθ)
    (hint2 : MeasureTheory.IntegrableOn (fun θ => g' θ ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ))
      Work.Spaces.Iθ) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      g θ ^ 2 ≤ (8 / Real.pi) * (∫ θ in Work.Spaces.Iθ, g θ ^ 2)
        + 2 * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (γ - 2))
          * (∫ θ in Work.Spaces.Iθ, g' θ ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)) := by
  have hGint : MeasureTheory.IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (γ - 2))
      Work.Spaces.Iθ :=
    (Work.Spaces.sin_two_rpow (γ - 2) (by linarith) (by linarith)).1
  have hGnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (γ - 2) := by
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [Work.FTS.H2.ae_mem_Ioo_Iθ] with θ hθ
    exact Real.rpow_nonneg (le_of_lt (Work.FTS.H2.sin_two_pos_of_mem_Ioo hθ)) _
  -- the companion interval and the minimising angle
  set J : Set ℝ := Set.Icc (Real.pi / 8) (3 * Real.pi / 8) with hJ
  have hJsub : J ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    intro x hx
    rw [hJ] at hx
    exact ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩
  have hJsubIθ : J ⊆ Work.Spaces.Iθ := by
    intro x hx
    rw [hJ] at hx
    exact ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩
  have hJcont : ContinuousOn (fun σ => (g σ) ^ 2) J := fun x hx =>
    (((hg x (hJsub hx)).continuousAt).pow 2).continuousWithinAt
  obtain ⟨θ₀, hθ₀J, hθ₀min⟩ := IsCompact.exists_isMinOn isCompact_Icc
    ⟨Real.pi / 8, Set.left_mem_Icc.mpr (by linarith [Real.pi_pos])⟩ hJcont
  have hθ₀pos : 0 < θ₀ := by linarith [hθ₀J.1, Real.pi_pos]
  have hθ₀lt : θ₀ < Real.pi / 2 := by linarith [hθ₀J.2, Real.pi_pos]
  -- Step 1: the value at the companion angle is controlled by the average
  have hvolJ : (MeasureTheory.volume : MeasureTheory.Measure ℝ).real J = Real.pi / 4 := by
    rw [hJ, MeasureTheory.Measure.real_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    ring
  have hstep1 : (g θ₀) ^ 2 * (Real.pi / 4) ≤ ∫ σ in Work.Spaces.Iθ, (g σ) ^ 2 := by
    have hconstInt : (∫ σ in J, (g θ₀) ^ 2) = (g θ₀) ^ 2 * (Real.pi / 4) := by
      rw [MeasureTheory.setIntegral_const, hvolJ, smul_eq_mul, mul_comm]
    have hmono1 : (∫ σ in J, (g θ₀) ^ 2) ≤ ∫ σ in J, (g σ) ^ 2 :=
      MeasureTheory.setIntegral_mono_on
        (MeasureTheory.integrableOn_const
          (by rw [hJ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
        (hint1.mono_set hJsubIθ) measurableSet_Icc (fun σ hσ => hθ₀min hσ)
    have hmono2 : (∫ σ in J, (g σ) ^ 2) ≤ ∫ σ in Work.Spaces.Iθ, (g σ) ^ 2 :=
      MeasureTheory.setIntegral_mono_set hint1 (Eventually.of_forall fun σ => sq_nonneg _)
        (Filter.Eventually.of_forall hJsubIθ)
    rw [hconstInt] at hmono1
    linarith
  intro θ hθ
  have hθpos : 0 < θ := hθ.1
  have hθlt : θ < Real.pi / 2 := hθ.2
  -- Step 2: the variation, by the fundamental theorem of calculus and Cauchy–Schwarz
  have huIcc : ∀ x ∈ Set.uIcc θ₀ θ, x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    intro x hx
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨lt_of_lt_of_le (lt_min hθ₀pos hθpos) (le_trans (min_le_left _ _) h1),
        lt_of_le_of_lt (le_trans h2 (le_max_right _ _)) (max_lt hθ₀lt hθlt)⟩
    · exact ⟨lt_of_lt_of_le (lt_min hθ₀pos hθpos) (le_trans (min_le_right _ _) h1),
        lt_of_le_of_lt (le_trans h2 (le_max_left _ _)) (max_lt hθ₀lt hθlt)⟩
  have hder_on : ∀ x ∈ Set.uIcc θ₀ θ, HasDerivAt g (g' x) x := fun x hx => hg x (huIcc x hx)
  have hcont_on : ContinuousOn g' (Set.uIcc θ₀ θ) := hg'c.mono huIcc
  have hftc : (∫ σ in θ₀..θ, g' σ) = g θ - g θ₀ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hder_on hcont_on.intervalIntegrable
  have hapos : 0 < min θ₀ θ := lt_min hθ₀pos hθpos
  have hblt : max θ₀ θ < Real.pi / 2 := max_lt hθ₀lt hθlt
  have hcs := cs_Ioc_aux (γ := γ) hg'c hint2 hGint hapos hblt min_le_max
  have hconv : (∫ σ in θ₀..θ, g' σ) ^ 2
      = (∫ σ in Set.Ioc (min θ₀ θ) (max θ₀ θ), g' σ) ^ 2 := by
    rcases lt_trichotomy θ₀ θ with h | h | h
    · rw [min_eq_left h.le, max_eq_right h.le, intervalIntegral.integral_of_le h.le]
    · subst h
      rw [min_self, max_self, Set.Ioc_self, MeasureTheory.setIntegral_empty,
        intervalIntegral.integral_same]
    · rw [min_eq_right h.le, max_eq_left h.le, intervalIntegral.integral_symm θ θ₀,
        intervalIntegral.integral_of_le h.le]
      ring
  have hnnG : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun σ => (Real.sin (2 * σ)) ^ (γ - 2)) := by
    filter_upwards [Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hσ
    exact Real.rpow_nonneg (le_of_lt (Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ)) _
  have hnnB : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun σ => g' σ ^ 2 * (Real.sin (2 * σ)) ^ (2 - γ)) := by
    filter_upwards [Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hσ
    exact mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (le_of_lt (Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ)) _)
  have hsub_ae : Set.Ioc (min θ₀ θ) (max θ₀ θ) ≤ᵐ[MeasureTheory.volume] Work.Spaces.Iθ :=
    Filter.Eventually.of_forall fun x hx =>
      ⟨le_of_lt (lt_trans hapos hx.1), le_of_lt (lt_of_le_of_lt hx.2 hblt)⟩
  have hSin : ∀ x ∈ Set.Ioc (min θ₀ θ) (max θ₀ θ), 0 < Real.sin (2 * x) := fun x hx =>
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1, hapos])
      (by linarith [hx.2, hblt, Real.pi_pos])
  have hB1 : (∫ σ in Set.Ioc (min θ₀ θ) (max θ₀ θ), (Real.sin (2 * σ)) ^ (γ - 2))
      ≤ ∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (γ - 2) :=
    MeasureTheory.setIntegral_mono_set hGint hnnG hsub_ae
  have hB2 : (∫ σ in Set.Ioc (min θ₀ θ) (max θ₀ θ),
          g' σ ^ 2 * (Real.sin (2 * σ)) ^ (2 - γ))
      ≤ ∫ σ in Work.Spaces.Iθ, g' σ ^ 2 * (Real.sin (2 * σ)) ^ (2 - γ) :=
    MeasureTheory.setIntegral_mono_set hint2 hnnB hsub_ae
  have hnn1 : 0 ≤ ∫ σ in Set.Ioc (min θ₀ θ) (max θ₀ θ), (Real.sin (2 * σ)) ^ (γ - 2) := by
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with σ hσ
    rw [Set.mem_Ioc] at hσ
    exact Real.rpow_nonneg (le_of_lt (hSin σ (Set.mem_Ioc.mpr hσ))) _
  have hnn2 : 0 ≤ ∫ σ in Set.Ioc (min θ₀ θ) (max θ₀ θ),
      g' σ ^ 2 * (Real.sin (2 * σ)) ^ (2 - γ) := by
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with σ hσ
    rw [Set.mem_Ioc] at hσ
    exact mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (le_of_lt (hSin σ (Set.mem_Ioc.mpr hσ))) _)
  have hvariation : (g θ - g θ₀) ^ 2
      ≤ (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (γ - 2))
        * (∫ σ in Work.Spaces.Iθ, g' σ ^ 2 * (Real.sin (2 * σ)) ^ (2 - γ)) := by
    rw [← hftc, hconv]
    refine le_trans hcs ?_
    calc (∫ σ in Set.Ioc (min θ₀ θ) (max θ₀ θ), g' σ ^ 2 * (Real.sin (2 * σ)) ^ (2 - γ))
          * (∫ σ in Set.Ioc (min θ₀ θ) (max θ₀ θ), (Real.sin (2 * σ)) ^ (γ - 2))
        ≤ (∫ σ in Work.Spaces.Iθ, g' σ ^ 2 * (Real.sin (2 * σ)) ^ (2 - γ))
          * (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (γ - 2)) :=
          mul_le_mul hB2 hB1 hnn1 (MeasureTheory.integral_nonneg_of_ae hnnB)
      _ = (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (γ - 2))
          * (∫ σ in Work.Spaces.Iθ, g' σ ^ 2 * (Real.sin (2 * σ)) ^ (2 - γ)) := by ring
  -- Step 3: combine the value at `θ₀` with the variation
  have hcomb : (g θ) ^ 2 ≤ 2 * (g θ - g θ₀) ^ 2 + 2 * (g θ₀) ^ 2 := by
    nlinarith [sq_nonneg (g θ - 2 * g θ₀)]
  have hcompañon : (g θ₀) ^ 2
      ≤ (4 / Real.pi) * (∫ σ in Work.Spaces.Iθ, (g σ) ^ 2) := by
    have hπ4 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
    have h1 : (g θ₀) ^ 2
        ≤ (∫ σ in Work.Spaces.Iθ, (g σ) ^ 2) / (Real.pi / 4) :=
      (le_div_iff₀ hπ4).mpr hstep1
    have h2 : (∫ σ in Work.Spaces.Iθ, (g σ) ^ 2) / (Real.pi / 4)
        = (4 / Real.pi) * (∫ σ in Work.Spaces.Iθ, (g σ) ^ 2) := by
      field_simp <;> ring
    linarith [h1, h2]
  calc (g θ) ^ 2 ≤ 2 * (g θ - g θ₀) ^ 2 + 2 * (g θ₀) ^ 2 := hcomb
    _ ≤ 2 * ((∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (γ - 2))
            * (∫ σ in Work.Spaces.Iθ, g' σ ^ 2 * (Real.sin (2 * σ)) ^ (2 - γ)))
          + 2 * ((4 / Real.pi) * (∫ σ in Work.Spaces.Iθ, (g σ) ^ 2)) := by
        linarith [hvariation, hcompañon]
    _ = (8 / Real.pi) * (∫ σ in Work.Spaces.Iθ, (g σ) ^ 2)
          + 2 * (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (γ - 2))
            * (∫ σ in Work.Spaces.Iθ, g' σ ^ 2 * (Real.sin (2 * σ)) ^ (2 - γ)) := by
        ring_nf

end Work.FTS_RegExport.RXT.Slots
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.slot_slice_data =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 800000

/-! ## The pointwise domination of a slot by the `ℋ⁴`-integrand

Both kinds of slot occurring in `slot_slice_data` — a mixed slot `D_z^j D_θ^i f` with `1 ≤ i`
and a pure radial slot `D_z^j f` — are dominated, on the open quadrant, by the single
`ℋ⁴`-integrand `HkIntegrand α 4 f`:

* for a mixed slot the angular weight `w_θ = sin(2θ)^{-γ/2}` of `HkIntegrand` is `≥ 1` there
  (`Work.FTS.StrongEps.SupPort.AuxMixSq.mixed_sq_w_le_HkIntegrand`);
* for a pure radial slot the extra factor `sin(2θ)^{-η} ≥ 1` in the matching summand of
  `HkIntegrand` is discarded (`Work.Spaces.Slots.one_le_sin_two_rpow_neg_eta`).

This single pointwise inequality is what makes all three conjuncts of `slot_slice_data` follow
from the two `C⁴` inputs `h4` (smoothness of `f` on the open quadrant) and `hmem`
(honesty of the `ℋ⁴`-norm), together with `Work.FTS_RegExport.C4.HkSqSwap_C4`. -/

/-- A pure radial slot with the radial weight `w` is dominated by the `ℋ⁴`-integrand on the
open quadrant (the angular factor `sin(2θ)^{-η}` of the corresponding summand is `≥ 1`). -/
theorem dzSlot_sq_w_le_HkIntegrand {α : ℝ} {f : ℝ → ℝ → ℝ} {j : ℕ} (hj : j ≤ 4) {s θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (Work.Spaces.DzIter j f s θ) ^ 2 * (Work.Spaces.w s) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 f s θ := by
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hone : (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    Work.Spaces.Slots.one_le_sin_two_rpow_neg_eta hθ.1 hθ.2
  have hkey := Work.Spaces.sq_le_HkIntegrand_z α 4 f s θ j hj
  have heq : (Work.Spaces.DzIter j f s θ
      * (Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.DzIter j f s θ) ^ 2 * (Work.Spaces.w s) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    have hs : 0 ≤ Real.sin (2 * θ) := hsin.le
    have hsq : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
        = (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
      norm_num
    rw [mul_pow, div_pow, hsq, div_eq_mul_inv, ← Real.rpow_neg hs (Work.Spaces.eta)]
    ring
  calc (Work.Spaces.DzIter j f s θ) ^ 2 * (Work.Spaces.w s) ^ 2
      = (Work.Spaces.DzIter j f s θ) ^ 2 * (Work.Spaces.w s) ^ 2 * 1 := by ring
    _ ≤ (Work.Spaces.DzIter j f s θ) ^ 2 * (Work.Spaces.w s) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
        mul_le_mul_of_nonneg_left hone (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = (Work.Spaces.DzIter j f s θ
          * (Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := heq.symm
    _ ≤ Work.Spaces.HkIntegrand α 4 f s θ := hkey

/-- Every admissible slot `(j,i)` of `slot_slice_data` is dominated by the `ℋ⁴`-integrand on
the open quadrant. -/
theorem slot_sq_w_le_HkIntegrand {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ} (j i : ℕ)
    (hadm : (1 ≤ i ∧ i + j ≤ 4) ∨ (i = 0 ∧ j ≤ 4)) {s σ : ℝ}
    (hσ : σ ∈ Set.Ioo 0 (π / 2)) :
    (Work.Spaces.mixed j i f s σ) ^ 2 * (Work.Spaces.w s) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 f s σ := by
  rcases hadm with ⟨hi, hij⟩ | ⟨hi0, hj⟩
  · exact Work.FTS.StrongEps.SupPort.AuxMixSq.mixed_sq_w_le_HkIntegrand hα j i hi hij hσ
  · subst hi0
    simpa only [Work.Spaces.mixed_zero_right] using
      dzSlot_sq_w_le_HkIntegrand (α := α) (f := f) (j := j) hj (s := s) (θ := σ) hσ

/-! ## The main statement -/

theorem slot_slice_data {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
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
        ≤ Work.Spaces.HkSq α 4 f := by
  -- The two disjuncts of `hadm` both give `i + j ≤ 4`, which is all the smoothness API needs.
  have hsum : i + j ≤ 4 := by rcases hadm with ⟨_, h⟩ | ⟨h, hj⟩ <;> omega
  -- The angular-slice integrability of the `ℋ⁴`-integrand and the value of its two-fold
  -- integral come from the `C⁴` Tonelli exchange.
  obtain ⟨hswap, hIntHkθ, hAeIntHk⟩ := Work.FTS_RegExport.C4.HkSqSwap_C4 h4 hmem
  -- Joint continuity of the (uncurried) slot integrand on the open quadrant.
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.mixed j i f p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have hmix : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i f p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      Work.FTS.StrongEps.continuousOn_mixed_of_contDiffOn h4 hsum
    have hw : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      Work.FTS_RegExport.C4.continuousOn_w_sq.comp continuousOn_fst (fun p hp => hp.1)
    exact (hmix.pow 2).mul hw
  -- Measurability of the parametrised radial integral, from a.e. strong measurability of the
  -- uncurried integrand and `AEStronglyMeasurable.integral_prod_right'`.
  have hAEM : AEMeasurable (fun σ => ∫ s in Work.Spaces.Iz,
      (Work.Spaces.mixed j i f s σ) ^ 2 * (Work.Spaces.w s) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have hG : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ =>
        (Work.Spaces.mixed j i f p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      Work.Spaces.aesm_of_continuousOn_Qd _ hcont
    have h2 : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ =>
        (Work.Spaces.mixed j i f p.2 p.1) ^ 2 * (Work.Spaces.w p.2) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iz)) := hG.prod_swap
    have h3 := h2.integral_prod_right'
    exact h3.aemeasurable
  refine ⟨hAEM, ?_, ?_⟩
  · -- A.e. (in the angle) integrability of the radial slice, by domination from the integrable
    -- radial slice of the `ℋ⁴`-integrand.
    filter_upwards [Work.FTS_RegExport.C4.ae_integrableOn_HkIntegrand_slice_C4 h4 hmem,
      Work.FTS_RegExport.C4.ae_mem_Ioo_of_Iθ] with σ hIntσ hσ
    refine MeasureTheory.Integrable.mono' hIntσ
      (Work.FTS_RegExport.C4.aesm_zslice_mixed_sq_w_C4 h4 j i hsum hσ) ?_
    exact Filter.Eventually.of_forall fun s => by
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      exact slot_sq_w_le_HkIntegrand hα j i hadm hσ
  · -- The two-fold bound, by monotonicity of the two iterated integrals against the
    -- `ℋ⁴`-integrand whose two-fold integral is `HkSq α 4 f`.
    have hbound : ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        (∫ s in Work.Spaces.Iz,
          (Work.Spaces.mixed j i f s σ) ^ 2 * (Work.Spaces.w s) ^ 2)
        ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ := by
      filter_upwards [hAeIntHk, Work.FTS_RegExport.C4.ae_mem_Ioo_of_Iθ] with σ hIntσ hσ
      refine MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun s => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hIntσ ?_
      exact Filter.Eventually.of_forall fun s => slot_sq_w_le_HkIntegrand hα j i hadm hσ
    calc ∫ σ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz,
          (Work.Spaces.mixed j i f s σ) ^ 2 * (Work.Spaces.w s) ^ 2
        ≤ ∫ σ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz,
            Work.Spaces.HkIntegrand α 4 f s σ :=
          MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun σ => integral_nonneg fun s =>
              mul_nonneg (sq_nonneg _) (sq_nonneg _)) hIntHkθ hbound
      _ = Work.Spaces.HkSq α 4 f := hswap

end

end Work.FTS_RegExport.RXT
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.slot_slice_data_Wt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT

/-- **The `θ`-slice data of one `W`-weighted mixed slot.**

For `f` of class `C⁴` on the open quadrant `Q0 = (0,∞) × (0,π/2)` which is honestly in `ℋ⁴`
(`Work.Spaces.HkMem α 4 f`), and for every mixed slot `D_z^j D_θ^i f` with `1 ≤ i` and
`i + j ≤ 4`, the angular function

  `σ ↦ ∫_s (D_z^jD_θ^if (s,σ) · W(s,σ))²`

is a.e. strongly measurable (in particular `AEMeasurable`), and its integral over `Iθ` is
bounded by `HkSq α 4 f`.

The argument is a single pointwise domination followed by two monotonicity steps:
the slot is one summand of `HkIntegrand α 4 f` (`Work.Spaces.sq_le_HkIntegrand_mixed`), so
`(D_z^jD_θ^if · W)² ≤ HkIntegrand α 4 f` pointwise; the `z`-slices of `HkIntegrand` are
integrable for a.e. `σ` and its `σ`-partial integral is integrable with total mass `HkSq α 4 f`
(`Work.FTS_RegExport.C4.HkSqSwap_C4`); monotonicity of the integral in each variable then
gives the bound.  Measurability of the `σ`-partial integral comes from the continuity of the
slot on the open quadrant (`Work.FTS.StrongEps.continuousOn_mixed_of_contDiffOn` and
`Work.FTS.StrongEps.continuousOn_Wt_Q0_fin`), which upgrades to a.e. strong measurability for
the product of the restricted measures (`Work.Spaces.aesm_of_continuousOn_Qd`), together with
`AEStronglyMeasurable.integral_prod_right'`. -/
theorem slot_slice_data_Wt {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 f) (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) :
    AEMeasurable
        (fun σ => ∫ s in Work.Spaces.Iz,
          (Work.Spaces.mixed j i f s σ * Work.Spaces.Wt α s σ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) ∧
      (∫ σ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz,
          (Work.Spaces.mixed j i f s σ * Work.Spaces.Wt α s σ) ^ 2)
        ≤ Work.Spaces.HkSq α 4 f := by
  obtain ⟨hswap, hGint, hGslice⟩ := Work.FTS_RegExport.C4.HkSqSwap_C4 (α := α) h4 hmem
  -- ## Continuity of the uncurried weighted slot on the open quadrant
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      Work.FTS.EllipticEst.Q0 :=
    ((Work.FTS.StrongEps.continuousOn_mixed_of_contDiffOn h4 hij).mul
      (Work.FTS.StrongEps.continuousOn_Wt_Q0_fin α)).pow 2
  have haesm1 : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _
      (by simpa only [Work.FTS.EllipticEst.Q0] using hcont)
  -- ## A.e. strong measurability of the `σ`-partial integral
  have haesm2 : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (Work.Spaces.mixed j i f p.2 p.1 * Work.Spaces.Wt α p.2 p.1) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iz)) :=
    haesm1.prod_swap
  have hΦsm : AEStronglyMeasurable (fun σ : ℝ => ∫ s in Work.Spaces.Iz,
      (Work.Spaces.mixed j i f s σ * Work.Spaces.Wt α s σ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    haesm2.integral_prod_right'
  -- ## Pointwise domination by the `ℋ⁴`-integrand, a.e. in the angle
  have hbound : ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (∫ s in Work.Spaces.Iz,
          (Work.Spaces.mixed j i f s σ * Work.Spaces.Wt α s σ) ^ 2)
        ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ := by
    filter_upwards [hGslice] with σ hσ
    exact MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun s => sq_nonneg _) hσ
      (Filter.Eventually.of_forall fun s =>
        Work.Spaces.sq_le_HkIntegrand_mixed α 4 f s σ i j hi hij)
  -- ## Integrability of the `σ`-partial integral (needed for the a.e. bookkeeping)
  have hΦint : Integrable (fun σ : ℝ => ∫ s in Work.Spaces.Iz,
      (Work.Spaces.mixed j i f s σ * Work.Spaces.Wt α s σ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine hGint.mono' hΦsm ?_
    filter_upwards [hbound] with σ hσ
    rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg fun s => sq_nonneg _)]
    exact hσ
  refine ⟨hΦsm.aemeasurable, ?_⟩
  calc (∫ σ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz,
          (Work.Spaces.mixed j i f s σ * Work.Spaces.Wt α s σ) ^ 2)
      ≤ ∫ σ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz,
          Work.Spaces.HkIntegrand α 4 f s σ :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun σ =>
            MeasureTheory.integral_nonneg fun s => sq_nonneg _)
          hGint hbound
    _ = Work.Spaces.HkSq α 4 f := hswap

end Work.FTS_RegExport.RXT
end
end
-- ===== merged: Submission.Work.FTS_RegExport.THL.mixed_slice_pointwise_le_noTrace =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The trace-free weighted slice bound `mixed_slice_pointwise_le_noTrace`

This is the `BdryTraces`-free version of
`Work.FTS_RegExport.RXA1w.mixed_slice_pointwise_le`: for `a + b ≤ 2` and `z > 0`,

  `sin(2σ)^{-γ} (D_z^bD_θ^{a+1}f(z,σ))² ≤ 5 z³/(1+z)⁴ · ∫_s HkIntegrand β 4 f s σ`  a.e. in `σ`,

from only `ContDiffOn ℝ 4 (uncurry f) Q0` and `HkMem β 4 f`.

The only place where the source proof uses the boundary traces is the radial Agmon
inequality, whose statement `Work.FTS_RegExport.RXA1w.agmonZ_weight` carries the extra
hypothesis `x (v x w x)² → 0` at `+∞`.  Its replacement
`Work.FTS_RegExport.RXT.Slots.v2_agmonZ_noDecay` removes that hypothesis (integrability of
`(v w)²` alone forces small values of `x (v x w x)²` at arbitrarily large `x`), at the price
of integrating over `Ioi z` instead of `Iz`; since `Ioi z ⊆ Iz` for `z > 0`, the
`HkIntegrand`-domination goes through unchanged.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.THL

/-- `(1+z)⁴/z³ = w(z)² · z`. -/
private lemma w_sq_mul_eq {z : ℝ} : (1 + z) ^ 4 / z ^ 3 = (Work.Spaces.w z) ^ 2 * z := by
  rw [Work.Spaces.w, div_pow]
  field_simp

theorem mixed_slice_pointwise_le_noTrace {β : ℝ} (hβ : 0 < β)
    {f : ℝ → ℝ → ℝ} (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem β 4 f) (b a : ℕ) (hab : a + b ≤ 2) {z : ℝ} (hz : 0 < z) :
    ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β))
          * (Work.Spaces.mixed b (a + 1) f z σ) ^ 2
        ≤ 5 * (z ^ 3 / (1 + z) ^ 4)
            * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand β 4 f s σ) := by
  have hzIoi : Set.Ioi z ⊆ Work.Spaces.Iz := fun x hx => le_of_lt (lt_trans hz hx)
  filter_upwards [Work.FTS_RegExport.C4.ae_integrableOn_mixed_sq_w_C4 hβ h4 hmem b (a + 1)
      (by omega) (by omega),
    Work.FTS_RegExport.C4.ae_integrableOn_mixed_sq_w_C4 hβ h4 hmem (b + 1) (a + 1)
      (by omega) (by omega),
    Work.FTS_RegExport.C4.ae_integrableOn_HkIntegrand_slice_C4 h4 hmem,
    Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hIntA hIntB hIntHk hσ
  have hsin : 0 < Real.sin (2 * σ) := Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ
  have hint1 : MeasureTheory.IntegrableOn
      (fun x => (Work.Spaces.mixed b (a + 1) f x σ * Work.Spaces.w x) ^ 2)
      Work.Spaces.Iz :=
    hIntA.congr (Filter.Eventually.of_forall fun x => by
      show (Work.Spaces.mixed b (a + 1) f x σ) ^ 2 * (Work.Spaces.w x) ^ 2
          = (Work.Spaces.mixed b (a + 1) f x σ * Work.Spaces.w x) ^ 2
      rw [mul_pow])
  have hint2 : MeasureTheory.IntegrableOn
      (fun x => (x * deriv (fun s => Work.Spaces.mixed b (a + 1) f s σ) x
        * Work.Spaces.w x) ^ 2) Work.Spaces.Iz :=
    hIntB.congr (Filter.Eventually.of_forall fun x => by
      show (Work.Spaces.mixed (b + 1) (a + 1) f x σ) ^ 2 * (Work.Spaces.w x) ^ 2
          = (x * deriv (fun s => Work.Spaces.mixed b (a + 1) f s σ) x * Work.Spaces.w x) ^ 2
      rw [show x * deriv (fun s => Work.Spaces.mixed b (a + 1) f s σ) x
          = Work.Spaces.mixed (b + 1) (a + 1) f x σ from rfl, mul_pow])
  have hcd : ContDiffOn ℝ 1 (fun s => Work.Spaces.mixed b (a + 1) f s σ) (Set.Ioi 0) :=
    Work.FTS.StrongEps.EComparison.contDiffOn_slice_z hσ
      (Work.FTS_RegExport.RXA1w.contDiffOn_uncurry_mixed_Q0 h4 b (a + 1) 1 (by omega))
  have hvderiv : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun s => Work.Spaces.mixed b (a + 1) f s σ)
        (deriv (fun s => Work.Spaces.mixed b (a + 1) f s σ) x) x := by
    intro x hx
    exact ((hcd.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds hx)).hasDerivAt
  have hagmon := Work.FTS_RegExport.RXT.Slots.v2_agmonZ_noDecay hz hvderiv hint1 hint2
  have hagmon' : (Work.Spaces.mixed b (a + 1) f z σ) ^ 2 * (Work.Spaces.w z) ^ 2 * z
      ≤ 4 * (∫ x in Set.Ioi z,
            (Work.Spaces.mixed b (a + 1) f x σ * Work.Spaces.w x) ^ 2)
          + ∫ x in Set.Ioi z,
              (x * deriv (fun s => Work.Spaces.mixed b (a + 1) f s σ) x
                * Work.Spaces.w x) ^ 2 := hagmon
  have hA_le_Iz : (∫ x in Work.Spaces.Iz,
        (Work.Spaces.mixed b (a + 1) f x σ * Work.Spaces.w x) ^ 2)
      ≤ (Real.sin (2 * σ)) ^ (Work.Spaces.gam β)
          * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand β 4 f s σ) := by
    rw [← MeasureTheory.integral_const_mul]
    refine integral_mono_of_nonneg
      (ae_restrict_of_forall_mem measurableSet_Ici fun x _ => sq_nonneg _)
      (hIntHk.const_mul _)
      (ae_restrict_of_forall_mem measurableSet_Ici fun x _ =>
        Work.FTS_RegExport.RXA1w.mixed_slot_sq_w_le_HkIntegrand (f := f) hβ b (a + 1)
          (by omega) (by omega) x hσ)
  have hA_le : (∫ x in Set.Ioi z,
        (Work.Spaces.mixed b (a + 1) f x σ * Work.Spaces.w x) ^ 2)
      ≤ (Real.sin (2 * σ)) ^ (Work.Spaces.gam β)
          * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand β 4 f s σ) := by
    refine le_trans ?_ hA_le_Iz
    exact MeasureTheory.setIntegral_mono_set hint1
      (Filter.Eventually.of_forall fun x => sq_nonneg _)
      (Filter.Eventually.of_forall fun x hx => hzIoi hx)
  have hB_le_Iz : (∫ x in Work.Spaces.Iz,
        (Work.Spaces.mixed (b + 1) (a + 1) f x σ * Work.Spaces.w x) ^ 2)
      ≤ (Real.sin (2 * σ)) ^ (Work.Spaces.gam β)
          * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand β 4 f s σ) := by
    rw [← MeasureTheory.integral_const_mul]
    refine integral_mono_of_nonneg
      (ae_restrict_of_forall_mem measurableSet_Ici fun x _ => sq_nonneg _)
      (hIntHk.const_mul _)
      (ae_restrict_of_forall_mem measurableSet_Ici fun x _ =>
        Work.FTS_RegExport.RXA1w.mixed_slot_sq_w_le_HkIntegrand (f := f) hβ (b + 1) (a + 1)
          (by omega) (by omega) x hσ)
  have hB_le : (∫ x in Set.Ioi z,
        (x * deriv (fun s => Work.Spaces.mixed b (a + 1) f s σ) x * Work.Spaces.w x) ^ 2)
      ≤ (Real.sin (2 * σ)) ^ (Work.Spaces.gam β)
          * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand β 4 f s σ) := by
    have heq : (∫ x in Set.Ioi z,
          (x * deriv (fun s => Work.Spaces.mixed b (a + 1) f s σ) x
            * Work.Spaces.w x) ^ 2)
        = ∫ x in Set.Ioi z,
            (Work.Spaces.mixed (b + 1) (a + 1) f x σ * Work.Spaces.w x) ^ 2 :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by
        show (x * deriv (fun s => Work.Spaces.mixed b (a + 1) f s σ) x * Work.Spaces.w x) ^ 2
            = (Work.Spaces.mixed (b + 1) (a + 1) f x σ * Work.Spaces.w x) ^ 2
        rw [show x * deriv (fun s => Work.Spaces.mixed b (a + 1) f s σ) x
            = Work.Spaces.mixed (b + 1) (a + 1) f x σ from rfl])
    rw [heq]
    exact le_trans (MeasureTheory.setIntegral_mono_set hint2
        (Filter.Eventually.of_forall fun x => sq_nonneg _)
        (Filter.Eventually.of_forall fun x hx => hzIoi hx)) hB_le_Iz
  have hsum : (Work.Spaces.mixed b (a + 1) f z σ) ^ 2 * (Work.Spaces.w z) ^ 2 * z
      ≤ 5 * ((Real.sin (2 * σ)) ^ (Work.Spaces.gam β)
          * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand β 4 f s σ)) := by
    refine le_trans hagmon' ?_
    have h5 : (4 : ℝ) * ((Real.sin (2 * σ)) ^ (Work.Spaces.gam β)
          * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand β 4 f s σ))
        + (Real.sin (2 * σ)) ^ (Work.Spaces.gam β)
          * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand β 4 f s σ)
        = 5 * ((Real.sin (2 * σ)) ^ (Work.Spaces.gam β)
          * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand β 4 f s σ)) := by ring
    have := add_le_add (mul_le_mul_of_nonneg_left hA_le (by norm_num : (0 : ℝ) ≤ 4)) hB_le
    linarith [this, h5]
  have hρpos : 0 < (Work.Spaces.w z) ^ 2 * z := by
    have h1 := Work.FTS.H2.one_le_w_sq hz
    nlinarith [hz, h1]
  have hcancel : (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β))
      * (Real.sin (2 * σ)) ^ (Work.Spaces.gam β) = 1 := by
    rw [← Real.rpow_add hsin, show -(Work.Spaces.gam β) + Work.Spaces.gam β = 0 by ring,
      Real.rpow_zero]
  have hcount : 0 ≤ (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β))
      / ((Work.Spaces.w z) ^ 2 * z) :=
    div_nonneg (Real.rpow_nonneg hsin.le _) hρpos.le
  have h2 := mul_le_mul_of_nonneg_left hsum hcount
  have hL : (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β)) / ((Work.Spaces.w z) ^ 2 * z)
        * ((Work.Spaces.mixed b (a + 1) f z σ) ^ 2 * (Work.Spaces.w z) ^ 2 * z)
      = (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β))
        * (Work.Spaces.mixed b (a + 1) f z σ) ^ 2 := by
    have hwz : Work.Spaces.w z ≠ 0 := by
      intro h0; rw [h0] at hρpos; simp at hρpos
    have hz0 : z ≠ 0 := ne_of_gt hz
    field_simp <;> try ring
  have hR : (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β)) / ((Work.Spaces.w z) ^ 2 * z)
        * (5 * ((Real.sin (2 * σ)) ^ (Work.Spaces.gam β)
          * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand β 4 f s σ)))
      = 5 * (z ^ 3 / (1 + z) ^ 4)
          * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand β 4 f s σ) := by
    rw [← w_sq_mul_eq]
    have h1 : (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β)) / ((1 + z) ^ 4 / z ^ 3)
        = z ^ 3 / (1 + z) ^ 4 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β)) := by
      field_simp <;> try ring
    rw [h1]
    have h2 : z ^ 3 / (1 + z) ^ 4 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β))
          * (5 * ((Real.sin (2 * σ)) ^ (Work.Spaces.gam β)
            * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand β 4 f s σ)))
        = 5 * (z ^ 3 / (1 + z) ^ 4)
            * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand β 4 f s σ)
            * ((Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β))
              * (Real.sin (2 * σ)) ^ (Work.Spaces.gam β)) := by ring
    rw [h2, hcancel, mul_one]
  rw [hL, hR] at h2
  exact h2

end Work.FTS_RegExport.THL
end
end
