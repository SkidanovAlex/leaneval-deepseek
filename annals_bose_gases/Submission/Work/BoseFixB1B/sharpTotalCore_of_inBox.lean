import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1B.repairedPerSectorBoundG_of_sectorCountBox
import Submission.Work.BoseFixB1B.tendsto_cutProd_nCountB
import Submission.Work.BoseFixB1B.totalDemandDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.sharpTotalCore_of_inBox`

The **sharp extension of the total-density per-box demand**: from FS's `thm:smallbox` at
*normalised, in-box smooth* states (`Work.BoseFixB1B.InBoxTotal` — the corpus's spelling of the
in-box form of `PerBoxFTotal`) derive the same inequality at the **sharp** in-box states
`1_{B(u)^k}·ψ` of a smooth permutation-invariant fibre `ψ`.

## The route

The sharp state is not a `BoxState` (it is only piecewise smooth), so the in-box hypothesis cannot
be applied to it directly.  Instead the state is approximated by the smooth product states
`Φ_δ = (∏ᵢ γ_δ(xᵢ))·ψ` of the cutoff family `γ_δ` of the sliding box `B(u) = dlBox ℓ d u`
(`exists_smoothCutoffB`), which *are* `BoxState`s:

* for `δ > 0` with positive box mass `m_δ = ∫_{abox}Φ_δ²`, the normalised state
  `m_δ^{-1/2}·Φ_δ` is an in-box normalised `BoxState`, so `InBoxTotal` gives
  `totalDemand(m_δ^{-1/2}Φ_δ) ≤ fibreWord(m_δ^{-1/2}Φ_δ)`, and the `2`-homogeneity of both sides
  (`totalDemand_const_mul`, `fibreWord_smul`) strips the normalisation;
* the inequality is closed under the limit `δ → 0⁺`: the word converges to its sharp value along
  the approximants (`fibreWord_tendsto_cutProd`) and so does the demand
  (`tendsto_totalDemand_cutProd`, built here from the mass convergence `tendsto_cutProd_mass` and
  the density-numerator convergence `tendsto_cutProd_nCountB`), after which
  `le_of_tendsto_of_tendsto` gives the sharp inequality;
* when the sharp mass vanishes both sides vanish (`totalDemand_eq_zero_of_normB_eq_zero`,
  `sharpState_ae_zero_aux` and `fibreWord_ae_eq_zero`).

The `ε₀` of the conclusion has to be shrunk to also carry the dilute-regime facts
`R ≤ ℓd/16`, `R ≤ ℓ·chiR0` needed by the integrability of the potential density in
`fibreWord_tendsto_cutProd` (`regime_sideAt_ge`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.FockBridge Work.PerSector Work.SlotWord

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. Homogeneity of the demand and the vanishing of a zero-mass demand -/

/-- **`normB` is `2`-homogeneous in the state.** -/
lemma normB_const_mul {v : E3 → ℝ} {μ : ℝ} {k : ℕ} (Ψ : Submission.BoseGases.X k → ℝ) (t : ℝ) :
    Work.BoseBoxFix.normB v μ k (fun x => t * Ψ x)
      = t ^ 2 * Work.BoseBoxFix.normB v μ k Ψ := by
  unfold Work.BoseBoxFix.normB Work.BoseKinLoc.sqNormB
  rw [show (fun x : Submission.BoseGases.X k => (t * Ψ x) ^ 2)
      = (fun x => t ^ 2 * (Ψ x) ^ 2) from by funext x; ring]
  rw [MeasureTheory.integral_const_mul]

/-- **The total in-box density is invariant under a non-zero scaling of the state.** -/
lemma chiDensB_const_mul {v : E3 → ℝ} {μ : ℝ} {k : ℕ} (u : E3)
    (Ψ : Submission.BoseGases.X k → ℝ) {t : ℝ} (ht : t ≠ 0) :
    chiDensB (v := v) μ u (fun x => t * Ψ x) = chiDensB (v := v) μ u Ψ := by
  unfold chiDensB
  rw [normB_const_mul]
  rw [show (fun x : Submission.BoseGases.X k => (t * Ψ x) ^ 2
        * Work.BoseFixB1.nCountB (PBM v μ) (PBℓ v μ) (PBd v μ) u x)
      = (fun x => t ^ 2 * ((Ψ x) ^ 2
        * Work.BoseFixB1.nCountB (PBM v μ) (PBℓ v μ) (PBd v μ) u x)) from by
        funext x; ring]
  rw [MeasureTheory.integral_const_mul]
  rw [show Work.SmallBoxSliding.chiMass (PBM v μ) (PBℓ v μ) (PBd v μ) u
        * (t ^ 2 * Work.BoseBoxFix.normB v μ k Ψ)
      = t ^ 2 * (Work.SmallBoxSliding.chiMass (PBM v μ) (PBℓ v μ) (PBd v μ) u
        * Work.BoseBoxFix.normB v μ k Ψ) from by ring]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 ht)

/-- **The demand is `2`-homogeneous in the state** (for a non-zero scaling). -/
theorem totalDemand_const_mul {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R c₁ C μ : ℝ} {k : ℕ}
    (u : E3) (Ψ : Submission.BoseGases.X k → ℝ) {t : ℝ} (ht : t ≠ 0) :
    totalDemand v h R c₁ C μ u (fun x => t * Ψ x)
      = t ^ 2 * totalDemand v h R c₁ C μ u Ψ := by
  unfold totalDemand
  rw [chiDensB_const_mul u Ψ ht, normB_const_mul]
  ring

/-- **A state of vanishing `normB` has vanishing demand** (every term of the demand carries the
factor `normB`). -/
theorem totalDemand_eq_zero_of_normB_eq_zero {v : E3 → ℝ} {h : Work.UBB.ScatSol v}
    {R c₁ C μ : ℝ} {k : ℕ} (u : E3) (Ψ : Submission.BoseGases.X k → ℝ)
    (h0 : Work.BoseBoxFix.normB v μ k Ψ = 0) :
    totalDemand v h R c₁ C μ u Ψ = 0 := by
  unfold totalDemand
  rw [h0]
  ring

/-! ## 2. Convergence of the `psiWeight`-image of a convergent density -/

/-- `t ↦ psiWeight 1 μ t` is continuous at every limit point `χ₀ ≥ 0` (`μ > 0` keeps the
denominator `1 + t μ⁻¹` away from `0`). -/
lemma tendsto_psiWeight_one {β : Type*} {l : Filter β} {μ : ℝ} {χ : β → ℝ} {χ₀ : ℝ}
    (hχ : Filter.Tendsto χ l (nhds χ₀)) (hμ : 0 < μ) (hχ₀ : 0 ≤ χ₀) :
    Filter.Tendsto (fun δ => Work.SmallBoxSliding.psiWeight 1 μ (χ δ)) l
      (nhds (Work.SmallBoxSliding.psiWeight 1 μ χ₀)) := by
  have h1 : Filter.Tendsto (fun δ => (χ δ - μ) ^ 2) l (nhds ((χ₀ - μ) ^ 2)) :=
    (hχ.sub_const μ).pow 2
  have h2 : Filter.Tendsto (fun δ => 1 + χ δ * μ⁻¹) l (nhds (1 + χ₀ * μ⁻¹)) :=
    (hχ.mul_const μ⁻¹).const_add 1
  have h3 : (1 + χ₀ * μ⁻¹) ≠ 0 := by
    have : 0 < 1 + χ₀ * μ⁻¹ := by positivity
    linarith
  have h4 : Filter.Tendsto (fun δ => (χ δ - μ) ^ 2 / (1 + χ δ * μ⁻¹)) l
      (nhds ((χ₀ - μ) ^ 2 / (1 + χ₀ * μ⁻¹))) := by
    have hh := h1.div h2 h3
    exact hh.congr (fun δ => rfl)
  simpa only [Work.SmallBoxSliding.psiWeight, one_mul] using h4

/-! ## 3. Convergence of the demand along the cutoff approximants -/

/-- **The total in-box density converges along the cutoff approximants**, from the convergence of
the numerator (`hnum`) and of `normB` (`hnorm`) whenever the sharp density is non-zero
(`chiMass = 0` makes both sides vanish identically). -/
lemma tendsto_chiDensB_cutProd {v : E3 → ℝ} {μ : ℝ} {u : E3} {k : ℕ}
    {ψ : Submission.BoseGases.X k → ℝ} {γ : ℝ → E3 → ℝ}
    (hnum : Filter.Tendsto
      (fun δ : ℝ => ∫ x in Submission.BoseGases.abox k (PBℓ v μ),
          (cutProd (γ δ) ψ x) ^ 2 * Work.BoseFixB1.nCountB (PBM v μ) (PBℓ v μ) (PBd v μ) u x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (∫ x in Submission.BoseGases.abox k (PBℓ v μ),
          (sharpBoxState (PBB v μ u) ψ x) ^ 2
            * Work.BoseFixB1.nCountB (PBM v μ) (PBℓ v μ) (PBd v μ) u x)))
    (hnorm : Filter.Tendsto (fun δ : ℝ => Work.BoseBoxFix.normB v μ k (cutProd (γ δ) ψ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (Work.BoseBoxFix.normB v μ k (sharpBoxState (PBB v μ u) ψ))))
    (hmass : Work.BoseBoxFix.normB v μ k (sharpBoxState (PBB v μ u) ψ) ≠ 0) :
    Filter.Tendsto (fun δ : ℝ => chiDensB (v := v) μ u (cutProd (γ δ) ψ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (chiDensB (v := v) μ u (sharpBoxState (PBB v μ u) ψ))) := by
  rcases eq_or_ne (Work.SmallBoxSliding.chiMass (PBM v μ) (PBℓ v μ) (PBd v μ) u) 0 with hχ | hχ
  · have hz : ∀ Φ : Submission.BoseGases.X k → ℝ, chiDensB (v := v) μ u Φ = 0 := by
      intro Φ
      simp only [chiDensB, hχ, zero_mul, div_zero]
    simp only [hz]
    exact tendsto_const_nhds
  · have hfun : ∀ δ : ℝ, chiDensB (v := v) μ u (cutProd (γ δ) ψ)
        = (∫ x in Submission.BoseGases.abox k (PBℓ v μ),
            (cutProd (γ δ) ψ x) ^ 2 * Work.BoseFixB1.nCountB (PBM v μ) (PBℓ v μ) (PBd v μ) u x)
          / (Work.SmallBoxSliding.chiMass (PBM v μ) (PBℓ v μ) (PBd v μ) u
              * Work.BoseBoxFix.normB v μ k (cutProd (γ δ) ψ)) := by
      intro δ; simp only [chiDensB]
    have hfun' : chiDensB (v := v) μ u (sharpBoxState (PBB v μ u) ψ)
        = (∫ x in Submission.BoseGases.abox k (PBℓ v μ),
            (sharpBoxState (PBB v μ u) ψ x) ^ 2
              * Work.BoseFixB1.nCountB (PBM v μ) (PBℓ v μ) (PBd v μ) u x)
          / (Work.SmallBoxSliding.chiMass (PBM v μ) (PBℓ v μ) (PBd v μ) u
              * Work.BoseBoxFix.normB v μ k (sharpBoxState (PBB v μ u) ψ)) := by
      simp only [chiDensB]
    have hq := hnum.div
      (hnorm.const_mul (Work.SmallBoxSliding.chiMass (PBM v μ) (PBℓ v μ) (PBd v μ) u))
      (mul_ne_zero hχ hmass)
    rw [hfun']
    exact hq.congr (fun δ => (hfun δ).symm)

/-- **The demand converges along the cutoff approximants** to the demand of the sharp box state. -/
theorem tendsto_totalDemand_cutProd {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R c₁ C μ : ℝ}
    {u : E3} {k : ℕ} {ψ : Submission.BoseGases.X k → ℝ} {γ : ℝ → E3 → ℝ}
    (hμ : 0 < μ)
    (hnum : Filter.Tendsto
      (fun δ : ℝ => ∫ x in Submission.BoseGases.abox k (PBℓ v μ),
          (cutProd (γ δ) ψ x) ^ 2 * Work.BoseFixB1.nCountB (PBM v μ) (PBℓ v μ) (PBd v μ) u x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (∫ x in Submission.BoseGases.abox k (PBℓ v μ),
          (sharpBoxState (PBB v μ u) ψ x) ^ 2
            * Work.BoseFixB1.nCountB (PBM v μ) (PBℓ v μ) (PBd v μ) u x)))
    (hnorm : Filter.Tendsto (fun δ : ℝ => Work.BoseBoxFix.normB v μ k (cutProd (γ δ) ψ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (Work.BoseBoxFix.normB v μ k (sharpBoxState (PBB v μ u) ψ))))
    (hmass : Work.BoseBoxFix.normB v μ k (sharpBoxState (PBB v μ u) ψ) ≠ 0) :
    Filter.Tendsto (fun δ : ℝ => totalDemand v h R c₁ C μ u (cutProd (γ δ) ψ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (totalDemand v h R c₁ C μ u (sharpBoxState (PBB v μ u) ψ))) := by
  have hχd := tendsto_chiDensB_cutProd (v := v) (μ := μ) (u := u) (k := k) (ψ := ψ) (γ := γ)
    hnum hnorm hmass
  have hχd0 : 0 ≤ chiDensB (v := v) μ u (sharpBoxState (PBB v μ u) ψ) := by
    simp only [chiDensB]
    refine div_nonneg (MeasureTheory.integral_nonneg (fun x => ?_))
      (mul_nonneg (Work.SmallBoxSliding.chiMass_nonneg _ _ _ _) (Work.BoseFixB1.normB_nonneg _))
    simp only [Work.BoseFixB1.nCountB]
    exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  have hF := tendsto_psiWeight_one hχd hμ hχd0
  have h1 : Filter.Tendsto
      (fun δ : ℝ => c₁ * (PBW h μ u * Work.SmallBoxSliding.psiWeight 1 μ
            (chiDensB (v := v) μ u (cutProd (γ δ) ψ)))
          * Work.BoseBoxFix.normB v μ k (cutProd (γ δ) ψ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (c₁ * (PBW h μ u * Work.SmallBoxSliding.psiWeight 1 μ
            (chiDensB (v := v) μ u (sharpBoxState (PBB v μ u) ψ)))
          * Work.BoseBoxFix.normB v μ k (sharpBoxState (PBB v μ u) ψ))) :=
    ((hF.const_mul (PBW h μ u)).const_mul c₁).mul hnorm
  have h2 : Filter.Tendsto
      (fun δ : ℝ => (1 / 2) * μ ^ 2 * PBW h μ u
          * Work.BoseBoxFix.normB v μ k (cutProd (γ δ) ψ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds ((1 / 2) * μ ^ 2 * PBW h μ u
          * Work.BoseBoxFix.normB v μ k (sharpBoxState (PBB v μ u) ψ))) :=
    hnorm.const_mul ((1 / 2) * μ ^ 2 * PBW h μ u)
  have h3 : Filter.Tendsto
      (fun δ : ℝ => C * (μ ^ 2 * (_root_.BoseGases.a v)
            * ((R / (PBℓ v μ * PBd v μ)) ^ 2 + PBΓ v μ)) * PBV v μ u
          * Work.BoseBoxFix.normB v μ k (cutProd (γ δ) ψ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (C * (μ ^ 2 * (_root_.BoseGases.a v)
            * ((R / (PBℓ v μ * PBd v μ)) ^ 2 + PBΓ v μ)) * PBV v μ u
          * Work.BoseBoxFix.normB v μ k (sharpBoxState (PBB v μ u) ψ))) :=
    hnorm.const_mul (C * (μ ^ 2 * (_root_.BoseGases.a v)
            * ((R / (PBℓ v μ * PBd v μ)) ^ 2 + PBΓ v μ)) * PBV v μ u)
  have h4 : Filter.Tendsto
      (fun δ : ℝ => C * μ * (_root_.BoseGases.a v)
          * Work.BoseBoxFix.normB v μ k (cutProd (γ δ) ψ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (C * μ * (_root_.BoseGases.a v)
          * Work.BoseBoxFix.normB v μ k (sharpBoxState (PBB v μ u) ψ))) :=
    hnorm.const_mul (C * μ * (_root_.BoseGases.a v))
  have htot := h1.sub h2 |>.sub h3 |>.sub h4
  simpa only [totalDemand] using htot

/-! ## 4. The sharp total core -/

/-- **The sharp total core, from the in-box total per-box bound.**  The `∀`-body of
`sharpTotalCore_of_inBox`: at the given `ε₀` (already small enough for the dilute regime) the
demand of the sharp in-box state is dominated by the sliding word. -/
theorem sharpTotalCore_body {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R c₁ C ε₀ : ℝ}
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v)
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v)
    (hbody : ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        (u : E3),
        0 < Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) →
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
        (∀ᵐ x ∂(MeasureTheory.volume.restrict
            (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))),
          (Φ : Submission.BoseGases.X n → ℝ) x ≠ 0 →
            ∀ i : Fin n, x i ∈ Submission.BoseGases.dlBox
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) →
        (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2) = 1 →
        PerBoxFTotal v h R c₁ C μ n Φ u)
    {μ : ℝ} (hAdm : Work.BoseBoxFix.Adm v ε₀ μ)
    (hR16 : R ≤ PBℓ v μ * PBd v μ / 16) (hRχ : R ≤ PBℓ v μ * Submission.BoseGases.chiR0)
    (k : ℕ) (ψ : Submission.BoseGases.X k → ℝ) (hψcd : ContDiff ℝ (⊤ : ENat) ψ)
    (hψperm : Submission.BoseGases.PermInvariant k ψ) (u : E3)
    (hu : u ∈ Work.SmallBoxSliding.goodSet (PBℓ v μ) (PBd v μ) μ) :
    totalDemand v h R c₁ C μ u (sharpBoxState (PBB v μ u) ψ)
      ≤ Work.SlotWord.fibreWord h (PBM v μ) k (PBℓ v μ) (PBd v μ) (PBeT v μ)
          (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) μ u (sharpBoxState (PBB v μ u) ψ) := by
  classical
  have hμ0 : 0 < μ := hAdm.1
  have hL : 0 < PBℓ v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < PBd v μ := Work.BoseFixB1.adm_d_pos hAdm
  rcases eq_or_ne (Work.BoseBoxFix.normB v μ k (sharpBoxState (PBB v μ u) ψ)) 0 with hm0 | hm0
  · -- the degenerate case: both sides vanish
    have h1 : totalDemand v h R c₁ C μ u (sharpBoxState (PBB v μ u) ψ) = 0 :=
      totalDemand_eq_zero_of_normB_eq_zero u (sharpBoxState (PBB v μ u) ψ) hm0
    have h2 : Work.SlotWord.fibreWord h (PBM v μ) k (PBℓ v μ) (PBd v μ) (PBeT v μ)
        (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) μ u (sharpBoxState (PBB v μ u) ψ) = 0 := by
      refine fibreWord_ae_eq_zero h (PBM v μ) k (PBℓ v μ) (PBd v μ) (PBeT v μ)
        (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) μ u hL ?_
      refine sharpState_ae_zero_aux u hψcd.continuous ?_
      simpa only [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB, PBB] using hm0
    rw [h1, h2]
  · -- the nondegenerate case: the cutoff approximants and the limit
    have hmpos : 0 < Work.BoseBoxFix.normB v μ k (sharpBoxState (PBB v μ u) ψ) :=
      lt_of_le_of_ne (Work.BoseFixB1.normB_nonneg _) (Ne.symm hm0)
    have hmpos' : 0 < ∫ x in Submission.BoseGases.abox k (PBℓ v μ),
        (sharpBoxState (PBB v μ u) ψ x) ^ 2 := by
      simpa only [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB, PBB] using hmpos
    obtain ⟨K, γ, hcut⟩ :=
      exists_isCutFamily_of_smoothCutoff (exists_smoothCutoffB hL hd u)
    -- the cutoff family and the sup bound of `ψ`
    obtain ⟨Cb, hCb⟩ := (abox_compact k hL).exists_bound_of_continuousOn
      hψcd.continuous.continuousOn
    have hψb : ∀ x ∈ Submission.BoseGases.abox k (PBℓ v μ), |ψ x| ≤ max Cb 0 := by
      intro x hx
      rw [← Real.norm_eq_abs]
      exact le_trans (hCb x hx) (le_max_left _ _)
    have hpot : MeasureTheory.IntegrableOn
        (fun x : Submission.BoseGases.X k => Submission.BoseGases.qLHSden k (PBℓ v μ) μ
          (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v)
          (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u) x)
        (Submission.BoseGases.abox k (PBℓ v μ)) :=
      integrable_qLHSden_regime (h := h) (M := PBM v μ) (ℓ := PBℓ v μ) (d := PBd v μ)
        (μ := μ) (R0 := R) (one_le_PBM v μ) hL hd hv1 hR hv_supp hR16 hRχ u
    -- the three convergences
    have hnum := tendsto_cutProd_nCountB (k := k) (L := PBℓ v μ) (d := PBd v μ) (u := u)
      (M := PBM v μ) (ψ := ψ) (K := K) (γ := γ) hL hd hcut hψcd.continuous
    have hconvM : Filter.Tendsto (fun δ : ℝ => ∫ x in Submission.BoseGases.abox k (PBℓ v μ),
        (cutProd (γ δ) ψ x) ^ 2) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (∫ x in Submission.BoseGases.abox k (PBℓ v μ),
          (sharpBoxState (PBB v μ u) ψ x) ^ 2)) :=
      tendsto_cutProd_mass hL hd hcut hψcd.continuous
    have hnorm : Filter.Tendsto (fun δ : ℝ => Work.BoseBoxFix.normB v μ k (cutProd (γ δ) ψ))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (Work.BoseBoxFix.normB v μ k (sharpBoxState (PBB v μ u) ψ))) := by
      simpa only [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB, PBB] using hconvM
    have hTD := tendsto_totalDemand_cutProd (v := v) (h := h) (R := R) (c₁ := c₁) (C := C)
      (μ := μ) (u := u) (k := k) (ψ := ψ) (γ := γ) hμ0 hnum hnorm hm0
    have hFW := fibreWord_tendsto_cutProd h (PBM v μ) k (PBℓ v μ) (PBd v μ) (PBeT v μ)
      (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) μ u hL hd hcut hψcd (le_max_right Cb 0)
      hψb hpot
    -- the eventual inequality along the approximants
    have hev : ∀ᶠ δ : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        totalDemand v h R c₁ C μ u (cutProd (γ δ) ψ)
          ≤ Work.SlotWord.fibreWord h (PBM v μ) k (PBℓ v μ) (PBd v μ) (PBeT v μ)
              (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) μ u (cutProd (γ δ) ψ) := by
      filter_upwards [hconvM.eventually (Ioi_mem_nhds hmpos'), self_mem_nhdsWithin]
        with δ hδm hδpos
      set t : ℝ := (Real.sqrt (∫ x in Submission.BoseGases.abox k (PBℓ v μ),
        (cutProd (γ δ) ψ x) ^ 2))⁻¹ with ht
      have htne : t ≠ 0 := inv_ne_zero (Real.sqrt_pos_of_pos hδm).ne'
      -- the normalised approximant is a `BoxState` with all the in-box side conditions
      have hcdδ : ContDiff ℝ (⊤ : ENat) (fun x : Submission.BoseGases.X k =>
          t * cutProd (γ δ) ψ x) :=
        contDiff_const.mul (contDiff_cutProd (hcut.2 δ hδpos).1 hψcd)
      have hpermδ : PermInvariant k (fun x : Submission.BoseGases.X k =>
          t * cutProd (γ δ) ψ x) := by
        intro σ x
        show t * cutProd (γ δ) ψ (Submission.BoseGases.actPerm k σ x)
          = t * cutProd (γ δ) ψ x
        congr 1
        simp only [cutProd_apply]
        rw [hψperm σ x]
        congr 1
        simpa only [Submission.BoseGases.actPerm] using
          Equiv.prod_comp σ (fun j : Fin k => γ δ (x j))
      have hmassδ : 0 < ∫ x in Submission.BoseGases.abox k (PBℓ v μ),
          (t * cutProd (γ δ) ψ x) ^ 2 := by
        rw [show (fun x : Submission.BoseGases.X k => (t * cutProd (γ δ) ψ x) ^ 2)
            = (fun x => t ^ 2 * (cutProd (γ δ) ψ x) ^ 2) from by funext x; ring]
        rw [MeasureTheory.integral_const_mul]
        exact mul_pos (sq_pos_of_ne_zero htne) hδm
      have hneδ : (fun x : Submission.BoseGases.X k => t * cutProd (γ δ) ψ x) ≠ 0 := by
        intro hzero
        have h0 : (∫ x in Submission.BoseGases.abox k (PBℓ v μ),
            (t * cutProd (γ δ) ψ x) ^ 2) = 0 := by
          have hfun : (fun x : Submission.BoseGases.X k => (t * cutProd (γ δ) ψ x) ^ 2)
              = 0 := by
            funext x
            rw [congrFun hzero x]
            simp
          rw [hfun]
          simp
        linarith
      have hnormδ : (∫ x in Submission.BoseGases.abox k (PBℓ v μ),
          (t * cutProd (γ δ) ψ x) ^ 2) = 1 := by
        rw [show (fun x : Submission.BoseGases.X k => (t * cutProd (γ δ) ψ x) ^ 2)
            = (fun x => t ^ 2 * (cutProd (γ δ) ψ x) ^ 2) from by funext x; ring]
        rw [MeasureTheory.integral_const_mul]
        have ht2 : t ^ 2 = (∫ x in Submission.BoseGases.abox k (PBℓ v μ),
            (cutProd (γ δ) ψ x) ^ 2)⁻¹ := by
          rw [ht, inv_pow, Real.sq_sqrt hδm.le]
        rw [ht2, inv_mul_cancel₀ (ne_of_gt hδm)]
      have hsuppδ : ∀ᵐ x ∂(MeasureTheory.volume.restrict
            (Submission.BoseGases.abox k (PBℓ v μ))),
          (fun x : Submission.BoseGases.X k => t * cutProd (γ δ) ψ x) x ≠ 0 →
            ∀ i : Fin k, x i ∈ PBB v μ u := by
        refine Filter.Eventually.of_forall (fun x hx i => ?_)
        have hcp : cutProd (γ δ) ψ x ≠ 0 := by
          intro h0
          exact hx (by simp only [h0, mul_zero])
        rw [cutProd_apply] at hcp
        have hγ : γ δ (x i) ≠ 0 := by
          intro h0
          exact hcp (by rw [Finset.prod_eq_zero (Finset.mem_univ i) h0, zero_mul])
        exact (hcut.2 δ hδpos).2.1 (subset_tsupport _ (Function.mem_support.mpr hγ))
      -- the in-box hypothesis at the normalised approximant
      let hΦbd : Work.BoseKinLoc.BoxState k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) :=
        { toFun := fun x : Submission.BoseGases.X k => t * cutProd (γ δ) ψ x,
          contDiff := hcdδ, symm := hpermδ, nezero := hneδ }
      have hPer : PerBoxFTotal v h R c₁ C μ k hΦbd u :=
        hbody μ hAdm k hΦbd u
          (by simpa only [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB, PBℓ] using hmassδ)
          (by simpa only [PBℓ, PBd] using hu)
          (by simpa only [PBℓ, PBd, PBB] using hsuppδ)
          (by simpa only [PBℓ] using hnormδ)
      have hTDle : totalDemand v h R c₁ C μ u (fun x => t * cutProd (γ δ) ψ x)
          ≤ Work.BoseFixB1.sbWord h μ u (fun x => t * cutProd (γ δ) ψ x) :=
        (totalDemand_le_iff_PerBoxFTotal hΦbd u).mp hPer
      have hTDle' : totalDemand v h R c₁ C μ u (fun x => t * cutProd (γ δ) ψ x)
          ≤ Work.SlotWord.fibreWord h (PBM v μ) k (PBℓ v μ) (PBd v μ) (PBeT v μ)
              (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) μ u
              (fun x => t * cutProd (γ δ) ψ x) := by
        rw [fibreWord_eq_sbWord]
        exact hTDle
      -- strip the normalisation
      have hTw : totalDemand v h R c₁ C μ u (fun x => t * cutProd (γ δ) ψ x)
          = t ^ 2 * totalDemand v h R c₁ C μ u (cutProd (γ δ) ψ) :=
        totalDemand_const_mul u (cutProd (γ δ) ψ) htne
      have hFw : Work.SlotWord.fibreWord h (PBM v μ) k (PBℓ v μ) (PBd v μ) (PBeT v μ)
              (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) μ u
              (fun x => t * cutProd (γ δ) ψ x)
          = t ^ 2 * Work.SlotWord.fibreWord h (PBM v μ) k (PBℓ v μ) (PBd v μ) (PBeT v μ)
              (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) μ u (cutProd (γ δ) ψ) :=
        fibreWord_smul h (PBM v μ) k (PBℓ v μ) (PBd v μ) (PBeT v μ)
          (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) μ u t (cutProd (γ δ) ψ)
      have hkey : t ^ 2 * totalDemand v h R c₁ C μ u (cutProd (γ δ) ψ)
          ≤ t ^ 2 * Work.SlotWord.fibreWord h (PBM v μ) k (PBℓ v μ) (PBd v μ) (PBeT v μ)
              (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) μ u (cutProd (γ δ) ψ) := by
        rw [← hTw, ← hFw]
        exact hTDle'
      exact le_of_mul_le_mul_left hkey (sq_pos_of_ne_zero htne)
    exact le_of_tendsto_of_tendsto hTD hFW hev

/-! ## 5. The target -/

theorem sharpTotalCore_of_inBox {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ}
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v)
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) (hIn : Work.BoseFixB1B.InBoxTotal v h R) :
    ∃ ε₀ c₁ C : ℝ, 0 < c₁ ∧ 0 ≤ C ∧ 0 < ε₀ ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (k : ℕ) (ψ : Submission.BoseGases.X k → ℝ), ContDiff ℝ (⊤ : ENat) ψ →
          Submission.BoseGases.PermInvariant k ψ →
          ∀ u : EuclideanSpace ℝ (Fin 3),
            u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) μ →
            Work.BoseFixB1B.totalDemand v h R c₁ C μ u
                (Work.BoseFixB1B.sharpBoxState (Work.BoseFixB1B.PBB v μ u) ψ)
              ≤ Work.SlotWord.fibreWord h (Work.BoseFixB1B.PBM v μ) k
                  (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) (Work.BoseFixB1B.PBeT v μ)
                  (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) μ u
                  (Work.BoseFixB1B.sharpBoxState (Work.BoseFixB1B.PBB v μ u) ψ) := by
  classical
  obtain ⟨c₁, C, ε₀, hc₁, hC, hε₀, hbody⟩ := hIn
  obtain ⟨εr, hεr, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  refine ⟨min ε₀ εr, c₁, C, hc₁, hC, lt_min hε₀ hεr, ?_⟩
  intro μ hμ k ψ hψcd hψperm u hu
  have hμ0 : 0 < μ := hμ.1
  have hAdm : Work.BoseBoxFix.Adm v ε₀ μ :=
    ⟨hμ0, le_trans hμ.2.1 (min_le_left _ _), hμ.2.2⟩
  obtain ⟨hR16, hRχ⟩ := hreg μ hμ0 (le_trans hμ.2.1 (min_le_right _ _))
  exact sharpTotalCore_body (v := v) (h := h) (R := R) (c₁ := c₁) (C := C) (ε₀ := ε₀)
    hv hv1 hvrad hR hv_supp hav hbody hAdm hR16 hRχ k ψ hψcd hψperm u hu

end Work.BoseFixB1B
