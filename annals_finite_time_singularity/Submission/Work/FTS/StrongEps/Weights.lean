import Mathlib.Algebra.GroupWithZero.Action.Pi
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Filter.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.LocData6.zfarR_jet_le6_of_jets
import Submission.Work.FTS.LocDataExt.LocG5
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.FTS.Vocab
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.SlotJets.slotPthSliceLe
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.CutFactorFderivZero
-- ===== merged: Submission.Work.FTS.LocData6.LocG6Aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData6

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The generic-`h` form of the majorant (the order-`6` `HkIntegrand_locG_le_gen`) -/



/-! ## The pointwise `ℋ⁶`-majorant of `locG` -/

/-- **The pointwise `ℋ⁶`-majorant of the localised datum** `locG α L β (hLoc α)`, from the
order-`6` jet bound of `zfarR L`, the angular bound and the majorant of the bump.  This is the
order-`6` instance of `Work.FTS.LocDataExt.HkIntegrand_locG_le5`. -/
theorem HkIntegrand_locG6_le (α L β : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hL : 1 ≤ L) {A Rθ : ℝ}
    (hA : 0 ≤ A) (hRθ : 0 ≤ Rθ)
    (hAz : ∀ j ≤ 6, ∀ z ∈ Set.Ici L, ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ| ≤ A / z)
    (hΓ : ∀ i ≤ 6, ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
        ≤ Rθ * (Work.Spaces.Gam α θ) ^ 2)
    {Kb : ℝ} (hKb0 : 0 ≤ Kb)
    (hKb : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 (Work.FTS.LocData.hLoc α) z θ
        ≤ Kb * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)) z θ
        ≤ K * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2 := by
  obtain ⟨K₁, hK₁, h₁⟩ := HkIntegrand_zfar6_le α L hα hL hA hRθ hAz hΓ
  refine ⟨2 * K₁ + 2 * β ^ 2 * Kb, by nlinarith [hK₁, hKb0, sq_nonneg β], fun z hz θ hθ => ?_⟩
  -- the two separable pieces of `locG`
  have hcpos : 0 < Work.Spaces.c α := by
    exact lt_of_lt_of_le (by norm_num) (Work.FTS.LocData.c_ge_three_fifths α hα hα1)
  have hs1 : Work.FTS.LocData.SmoothQuad
      (fun z θ => (-(α / Work.Spaces.c α) * Work.FTS.LocDataExt.zfarR L z)
        * Work.Spaces.Gam α θ) :=
    Work.FTS.LocDataExt.smoothQuad_sepGam (α := α) (by
      refine (ContDiffOn.const_smul (-(α / Work.Spaces.c α))
        (Work.FTS.LocDataExt.contDiffOn_zfarR L)).congr (fun z _ => ?_)
      simp [smul_eq_mul])
  have hs2 : Work.FTS.LocData.SmoothQuad
      (fun z θ => (β * Work.FTS.LocData.bumpZ z) * Work.Spaces.Gam α θ) :=
    Work.FTS.LocDataExt.smoothQuad_sepGam (α := α) (by
      refine (ContDiffOn.const_smul β
        (Work.FTS.LocData.contDiff_bumpZ.contDiffOn)).congr (fun z _ => ?_)
      simp [smul_eq_mul])
  -- the bump piece as the `β`-multiple of `hLoc α`
  have hp2 : Work.Spaces.HkIntegrand α 6
      (fun z θ => (β * Work.FTS.LocData.bumpZ z) * Work.Spaces.Gam α θ) z θ
      = β ^ 2 * Work.Spaces.HkIntegrand α 6 (Work.FTS.LocData.hLoc α) z θ := by
    rw [show (fun z θ => (β * Work.FTS.LocData.bumpZ z) * Work.Spaces.Gam α θ)
        = fun z θ => β * Work.FTS.LocData.hLoc α z θ from by
      funext z θ
      rw [Work.FTS.LocData.hLoc_apply]
      ring]
    exact Work.FTS.LocData.HkIntegrand_const_mul α 6 β (Work.FTS.LocData.hLoc α) z θ
  have hA2 : (Work.Spaces.HkIntegrand α 6
        (fun z θ => (β * Work.FTS.LocData.bumpZ z) * Work.Spaces.Gam α θ) z θ)
      ≤ β ^ 2 * (Kb * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2) := by
    rw [hp2]
    exact mul_le_mul_of_nonneg_left (hKb z hz θ hθ) (sq_nonneg β)
  rw [Work.FTS.LocDataExt.locG_split α L β]
  refine (Work.FTS.LocData.HkIntegrand_add_le α 6 hs1 hs2 hz hθ).trans ?_
  refine (add_le_add (mul_le_mul_of_nonneg_left (h₁ z hz θ hθ) (by norm_num))
    (mul_le_mul_of_nonneg_left hA2 (by norm_num))).trans ?_
  refine le_of_eq ?_
  ring

/-! ## Membership in `ℋ⁶` -/

/-- **The localised datum lies in `ℋ⁶`**, from the order-`6` jet inputs. -/
theorem HkMem_locG6 (α L β : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hL : 1 ≤ L) {A Rθ : ℝ}
    (hA : 0 ≤ A) (hRθ : 0 ≤ Rθ)
    (hAz : ∀ j ≤ 6, ∀ z ∈ Set.Ici L, ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ| ≤ A / z)
    (hΓ : ∀ i ≤ 6, ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
        ≤ Rθ * (Work.Spaces.Gam α θ) ^ 2)
    {Kb : ℝ} (hKb0 : 0 ≤ Kb)
    (hKb : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 (Work.FTS.LocData.hLoc α) z θ
        ≤ Kb * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2) :
    Work.Spaces.HkMem α 6 (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)) := by
  obtain ⟨K, hK, hmaj⟩ := HkIntegrand_locG6_le α L β hα hα1 hL hA hRθ hAz hΓ hKb0 hKb
  refine Work.FTS.LocData.HkMem_of_majorant
    (f := Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α))
    (M := fun z θ => K * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2) α 6
    (Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α 6 _
      (Work.FTS.LocData.SmoothQuad_locG α L β hα hα1 (Work.FTS.LocData.SmoothQuad_hLoc α)))
    ?_ ?_ ?_
  · exact (Work.FTS.LocData.integrableOn_angMaj_majorant α K hα hα1).1
  · exact (Work.FTS.LocData.integrableOn_angMaj_majorant α K hα hα1).2
  · intro z hz θ hθ
    exact hmaj z hz θ hθ

/-! ## The boundary traces at order `6` -/

/-- **The vanishing boundary traces of the localised datum at order `6`**: the generic
`Work.FTS.LocDataExt.bdryTraces_locG` at `k = 6`. -/
theorem bdryTraces_locG6 (α L β : ℝ) (hα : 0 < α) (hL : 1 ≤ L) {CΓ CF : ℝ}
    (hCΓ : 0 ≤ CΓ) (hCF : 0 ≤ CF)
    (hΓ : ∀ i ≤ 6, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ|
        ≤ CΓ * Work.Spaces.Gam α θ)
    (hF : ∀ b ≤ 6, ∀ z : ℝ, 1 ≤ z → ∀ θ : ℝ,
      |Work.Spaces.DzIter b (fun z _ => Work.FM.Fstar z) z θ| ≤ CF / z) :
    Work.FTS.Nonlin.BdryTraces α 6
      (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)) :=
  Work.FTS.LocDataExt.bdryTraces_locG α L β hα hL (k := 6) hCΓ hCF hΓ hF

/-! ## `RegQ α 6` -/

/-- **The localised datum lies in `RegQ α 6`**, from the order-`6` jet inputs (the `Ici L` jet
bound of `zfarR L`, the angular bound and the majorant of the bump). -/
theorem regQ_locG6_of_jets (α L β : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hL : 1 ≤ L) {A Rθ : ℝ}
    (hA : 0 ≤ A) (hRθ : 0 ≤ Rθ)
    (hAz : ∀ j ≤ 6, ∀ z ∈ Set.Ici L, ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ| ≤ A / z)
    (hΓ : ∀ i ≤ 6, ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
        ≤ Rθ * (Work.Spaces.Gam α θ) ^ 2)
    (hΓabs : ∀ i ≤ 6, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ|
        ≤ 100000 * Work.Spaces.Gam α θ)
    {Kb : ℝ} (hKb0 : 0 ≤ Kb)
    (hKb : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 (Work.FTS.LocData.hLoc α) z θ
        ≤ Kb * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2)
    {CF : ℝ} (hCF : 0 ≤ CF)
    (hF : ∀ b ≤ 6, ∀ z : ℝ, 1 ≤ z → ∀ θ : ℝ,
      |Work.Spaces.DzIter b (fun z _ => Work.FM.Fstar z) z θ| ≤ CF / z) :
    Work.FTS.Nonlin.RegQ α 6 (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)) :=
  ⟨Work.FTS.LocData.SmoothQuad_locG α L β hα hα1 (Work.FTS.LocData.SmoothQuad_hLoc α),
    HkMem_locG6 α L β hα hα1 hL hA hRθ hAz hΓ hKb0 hKb,
    bdryTraces_locG6 α L β hα hL (by norm_num) hCF hΓabs hF⟩

end Work.FTS.LocData6
end
end
-- ===== merged: Submission.Work.FTS.LocData6.ZfarJetIci6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData6

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The `D_z`-jets of `zfarR L` decay like `1/z` on all of `[L,∞)`**: on `[L,2L]` from the
Leibniz bound `hAz`, beyond `2L` from the jets of `FM.Fstar` (with which `zfarR L` agrees
there). -/
theorem zfarR_jet_le6_Ici (L : ℝ) (hL : 1 ≤ L) {A CF : ℝ} (hA : 0 ≤ A) (hCF : 0 ≤ CF)
    (hAz : ∀ j ≤ 6, ∀ z ∈ Set.Icc L (2 * L), ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ| ≤ A / z)
    (hF : ∀ j ≤ 6, ∀ z : ℝ, 1 ≤ z → ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FM.Fstar z) z θ| ≤ CF / z) :
    ∀ j ≤ 6, ∀ z ∈ Set.Ici L, ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ| ≤ max A CF / z := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  intro j hj z hz θ
  have hzpos : 0 < z := lt_of_lt_of_le hLpos hz
  by_cases h : z ≤ 2 * L
  · have h1 := hAz j hj z ⟨hz, h⟩ θ
    refine h1.trans ?_
    exact div_le_div_of_nonneg_right (le_max_left A CF) (le_of_lt hzpos)
  · push_neg at h
    have hev : ∀ᶠ z' in 𝓝 z, Work.FTS.LocDataExt.zfarR L z' = Work.FM.Fstar z' := by
      filter_upwards [(isOpen_lt continuous_const continuous_id).mem_nhds h] with z' hz'
      exact Work.FTS.LocDataExt.zfarR_eq_FM_Fstar_of_ge hLpos (le_of_lt hz')
    rw [Work.FTS.LocDataExt.DzIter_z_congr_of_eventuallyEq
      (σ := fun z => Work.FM.Fstar z) hev j θ]
    have h1 := hF j hj z (by linarith) θ
    refine h1.trans ?_
    exact div_le_div_of_nonneg_right (le_max_right A CF) (le_of_lt hzpos)

/-- **The unconditional order-`6` jet bound of the far factor**: there is `A > 0` such that
`|D_z^j (zfarR L) z| ≤ A/z` for every `L ≥ 1`, every `j ≤ 6`, every `z ≥ L` and every `θ`. -/
theorem zfarR_jet_le6_clean :
    ∃ A : ℝ, 0 < A ∧ ∀ L : ℝ, 1 ≤ L → ∀ j : ℕ, j ≤ 6 →
      ∀ z ∈ Set.Ici L, ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ| ≤ A / z := by
  obtain ⟨Cu, hCu1, hCu⟩ := oneSubChi_jet_le6
  obtain ⟨Cv, hCvpos, hCvle⟩ := FM_Fstar_jet_le6
  have hIcc := zfarR_jet_le6_of_jets hCu1 hCvpos hCu hCvle
  refine ⟨max (64 * Cu * Cv) Cv, by positivity, fun L hL j hj z hz θ => ?_⟩
  exact zfarR_jet_le6_Ici L hL (by positivity) (le_of_lt hCvpos)
    (fun j hj z hz θ => hIcc L hL j hj z hz θ)
    (fun j hj z hz θ => hCvle j hj z hz θ) j hj z hz θ

end Work.FTS.LocData6
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.LimApproxSE =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice muDyn)

set_option autoImplicit false

/-- **The approximation clause of the strong output at the horizon `[0,T]`** (the G2 clause of the
FinalV2 design): there are class-`C` families `gn`, a uniform `ℋ⁶`-bound `B` and a uniform
`ℋ⁴`-Lipschitz modulus `L` such that the `ℋ⁴`-size of `gn` is uniformly `≤ C₀α²`, its `τ`-modulus
is `≤ L|τ-τ'|`, every mixed slot of order `≤ 4` converges pointwise on `Qd` to that of `g`, and the
modulation converges.

This is the horizon-restricted form: it is what an `EpsLimPkg` can carry (`EpsLimPkg` is stated on
`[0,T]` and glued across the covering pieces of `Assembly.lean`). -/
def LimApproxOn (α C₀ T : ℝ) (Φs : Fn) (E : Fn → Fn) (g : Fam) : Prop :=
  ∃ (gn : ℕ → Fam) (B L : ℝ),
    (∀ n : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.ClassC.ClassC α (slice (gn n) τ) ∧
        Work.FTS.Nonlin.Xn α (slice (gn n) τ) ≤ C₀ * α ^ 2 ∧
        Work.FTS.StrongGlobal.Xn6 α (slice (gn n) τ) ≤ B) ∧
    (∀ n : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ τ' ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.Nonlin.Xn α (slice (gn n) τ - slice (gn n) τ') ≤ L * |τ - τ'|) ∧
    (∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ j i : ℕ, j + i ≤ 4 → ∀ z θ,
      (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i (slice (gn n) τ) z θ) Filter.atTop
        (𝓝 (Work.Spaces.mixed j i (slice g τ) z θ))) ∧
    (∀ τ ∈ Set.Icc (0 : ℝ) T,
      Filter.Tendsto (fun n : ℕ => muDyn α (Work.FTS.Nonlin.PsiCan Φs E (gn n)) (gn n) τ)
        Filter.atTop (𝓝 (muDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g τ)))

/-- **The approximation clause of the strong output** (the `FinalV2.LimApprox` shape, with the
`∀ T > 0` quantifier outermost). -/
def LimApproxSE (α C₀ : ℝ) (Φs : Fn) (E : Fn → Fn) (g : Fam) : Prop :=
  ∀ T : ℝ, 0 < T → LimApproxOn α C₀ T Φs E g

/-- The horizon-restricted form is monotone in the horizon. -/
theorem LimApproxOn.mono {α C₀ T T' : ℝ} {Φs : Fn} {E : Fn → Fn} {g : Fam}
    (h : LimApproxOn α C₀ T Φs E g) (hT : T' ≤ T) (hT0 : 0 ≤ T') :
    LimApproxOn α C₀ T' Φs E g := by
  obtain ⟨gn, B, L, hb, hlip, hjet, hmu⟩ := h
  refine ⟨gn, B, L, ?_, ?_, ?_, ?_⟩
  · intro n τ hτ
    exact hb n τ ⟨hτ.1, le_trans hτ.2 hT⟩
  · intro n τ hτ τ' hτ'
    exact hlip n τ ⟨hτ.1, le_trans hτ.2 hT⟩ τ' ⟨hτ'.1, le_trans hτ'.2 hT⟩
  · intro τ hτ j i hji z θ hzθ
    exact hjet τ ⟨hτ.1, le_trans hτ.2 hT⟩ j i hji z θ hzθ
  · intro τ hτ
    exact hmu τ ⟨hτ.1, le_trans hτ.2 hT⟩


end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.PZero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## The normalising constant and the projection -/

/-- The normalising constant of `P₀`: the `L₁₂`-value of the correction profile `bump` at `z = 0`.
It is strictly positive (`pzNorm_pos`, `PZeroAux/PzNormPos.lean`). -/
noncomputable def pzNorm : ℝ := Work.Construction.L12 bump 0

/-- **The projection `P₀` of the design's §(B)**: `P₀ f = f − (L₁₂ f 0 / L₁₂(bump)(0)) • bump`.

Its defining property is `L₁₂(P₀ f)(0) = 0` (`Pz_l12`), which is what the `l12` clause of
`ClassC`/`H6Adm` needs; `P₀` is the identity on profiles with `L₁₂ f 0 = 0` (`Pz_self_of_l12`). -/
noncomputable def Pz (f : Fn) : Fn :=
  f - (Work.Construction.L12 f 0 / pzNorm) • bump

/-- The pointwise form of `Pz`. -/
theorem Pz_apply (f : Fn) (z θ : ℝ) :
    Pz f z θ = f z θ - (Work.Construction.L12 f 0 / pzNorm) * bump z θ := by
  simp only [Pz, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

/-- `P₀` is the identity on the profiles whose `L₁₂`-zero-mode vanishes — the reason the projection
is invisible on the *limiting* right-hand side (the μ̄-identity) and on class-`C` profiles. -/
theorem Pz_self_of_l12 {f : Fn} (h : Work.Construction.L12 f 0 = 0) : Pz f = f := by
  simp only [Pz, h, zero_div, zero_smul, sub_zero]




end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.Weights =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

set_option autoImplicit false

/-- The angular factor `sin(2θ)^{-η}` of the `D_z`-slots. -/
def sEtaW (θ : ℝ) : ℝ := Real.sin (2 * θ) ^ (-(Work.Spaces.eta))

/-- The angular factor `sin(2θ)^{-γ}` of the mixed slots. -/
def sGamW (α θ : ℝ) : ℝ := Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))



/-- The `z`-part of both weights. -/
def wtZ (z : ℝ) : ℝ := Work.Spaces.w z ^ 2



theorem wtZ_nonneg (z : ℝ) : 0 ≤ wtZ z := by
  rw [wtZ]; positivity

/-- `sin (2θ) > 0` on the open quadrant. -/
theorem sin_two_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_mem_Ioo ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- `sin (2θ) ≥ 0` on the closed quadrant. -/
theorem sin_two_nonneg {θ : ℝ} (hθ : θ ∈ Set.Icc 0 (π / 2)) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

theorem wtZ_pos {z : ℝ} (hz : 0 < z) : 0 < wtZ z := by
  rw [wtZ, Work.Spaces.w]
  exact pow_pos (div_pos (by positivity) (pow_pos hz 2)) 2



theorem sEtaW_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < sEtaW θ := by
  rw [sEtaW]
  exact Real.rpow_pos_of_pos (sin_two_pos hθ) _

theorem sGamW_pos {α : ℝ} {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < sGamW α θ := by
  rw [sGamW]
  exact Real.rpow_pos_of_pos (sin_two_pos hθ) _





end Work.FTS.StrongEps
end
end
