import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.cubeArityAux
import Submission.Work.BoseB1Cube.inBoxRoute
import Submission.Work.BoseFixB1.Cube.Loc.sbWordCube_fibreSplit_of_integrable
import Submission.Work.BoseFixB1S.matchedWindowSmul
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.cubeAritySharp` — the smooth → sharp extension at the cube window

The `InBoxCubeRow` of `Submission/Work/BoseB1Cube/inBoxRoute.lean` is stated for **smooth** states
localised in the sliding box; the arity passage (`cubePerBox_of_inBoxCubeRow`) needs it for the
**sharp** states `1_{B(u)^k}·ψ` obtained as fibres of a slot piece.  This module performs that
extension, exactly as `Work.BoseFixB1B.sharpTotalCore_of_inBox` does at the ball window:

* the approximants `cutProd (γ δ) ψ = (∏ᵢ γ_δ(xᵢ))ψ` of the cutoff family `γ_δ` of `B(u)`
  (`exists_smoothCutoffB`) are smooth, localised and (after normalisation) admissible for the
  in-box row;
* the demand and the word both converge along them (`tendsto_perBoxCubeLHSFun_cutProd`,
  `CutProdConv`), so `le_of_tendsto_of_tendsto` passes the row to the sharp state.

`CutProdConv` is exactly the statement delegated as `Work.BoseB1Cube.tendsto_sbWordCube_cutProd`;
the target file discharges it.  The degenerate case (zero sharp mass) is handled by the vanishing of
`sbWordCube` on a.e.-zero states.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.FockBridge Work.PerSector Work.SlotWord Work.BoseFixB1B
open Work.BoseFixB1

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

/-! ## 1. The two statements entering the extension -/

/-- **The word converges along the cutoff approximants of the sharp state** — the statement proved
in `Work.BoseB1Cube.tendsto_sbWordCube_cutProd`, recorded here as a `Prop` so that the extension can
be assembled before (and independently of) its proof. -/
def CutProdConv (v : E3 → ℝ) (h : ScatSol v) (R : ℝ) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
    ∀ u : E3, u ∈ Work.SmallBoxSliding.goodSet (PBℓ v μ) (PBd v μ) μ →
    ∀ (k : ℕ) (ψ : X k → ℝ) {K Cb : ℝ} {γ : ℝ → E3 → ℝ},
      ContDiff ℝ (⊤ : ENat) ψ → 0 ≤ Cb →
      (∀ x ∈ abox k (PBℓ v μ), |ψ x| ≤ Cb) →
      IsCutFamily (PBℓ v μ) (PBd v μ) u K γ →
      Tendsto (fun δ : ℝ => Work.BoseFixB1B.sbWordCube v h μ u (cutProd (γ δ) ψ))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (Work.BoseFixB1B.sbWordCube v h μ u
          (sharpBoxState (dlBox (PBℓ v μ) (PBd v μ) u) ψ)))

/-- **The in-box row, at fixed constants** — the body of `InBoxCubeRow`. -/
def InBoxCubeRowBody (v : E3 → ℝ) (h : ScatSol v) (R c₁ C ε₀ : ℝ) : Prop :=
  ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
    ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (PBℓ v μ)) (u : E3),
      u ∈ Work.SmallBoxSliding.goodSet (PBℓ v μ) (PBd v μ) μ →
      (∀ᵐ x ∂(volume.restrict (abox n (PBℓ v μ))),
        (Φ : X n → ℝ) x ≠ 0 → ∀ i : Fin n, x i ∈ dlBox (PBℓ v μ) (PBd v μ) u) →
      (∫ x in abox n (PBℓ v μ), ((Φ : X n → ℝ) x) ^ 2) = 1 →
      Work.BoseFixB1S.PerBoxFCube v h R c₁ C μ n Φ u

/-- **The cutoff-approximant convergence of the word, at a fixed threshold** — the body of
`CutProdConv`. -/
def CutProdConvBody (v : E3 → ℝ) (h : ScatSol v) (R ε₀ : ℝ) : Prop :=
  ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
    ∀ u : E3, u ∈ Work.SmallBoxSliding.goodSet (PBℓ v μ) (PBd v μ) μ →
    ∀ (k : ℕ) (ψ : X k → ℝ) {K Cb : ℝ} {γ : ℝ → E3 → ℝ},
      ContDiff ℝ (⊤ : ENat) ψ → 0 ≤ Cb →
      (∀ x ∈ abox k (PBℓ v μ), |ψ x| ≤ Cb) →
      IsCutFamily (PBℓ v μ) (PBd v μ) u K γ →
      Tendsto (fun δ : ℝ => Work.BoseFixB1B.sbWordCube v h μ u (cutProd (γ δ) ψ))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (Work.BoseFixB1B.sbWordCube v h μ u
          (sharpBoxState (dlBox (PBℓ v μ) (PBd v μ) u) ψ)))

/-- **The in-box row at the sharp states, at fixed constants** — the body of `SharpCubeRow`. -/
def SharpCubeRowBody (v : E3 → ℝ) (h : ScatSol v) (R c₁ C ε₀ : ℝ) : Prop :=
  ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
    ∀ (k : ℕ) (ψ : X k → ℝ), ContDiff ℝ (⊤ : ENat) ψ →
      Submission.BoseGases.PermInvariant k ψ →
      ∀ u : E3, u ∈ Work.SmallBoxSliding.goodSet (PBℓ v μ) (PBd v μ) μ →
        perBoxCubeLHSFun v h R c₁ C μ k
          (sharpBoxState (dlBox (PBℓ v μ) (PBd v μ) u) ψ) u
        ≤ Work.BoseFixB1B.sbWordCube v h μ u
            (sharpBoxState (dlBox (PBℓ v μ) (PBd v μ) u) ψ)

/-- **The in-box row at the sharp states** — `InBoxCubeRow` with the smoothness/localisation
hypotheses replaced by the sharp box indicator. -/
def SharpCubeRow (v : E3 → ℝ) (h : ScatSol v) (R : ℝ) : Prop :=
  ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (k : ℕ) (ψ : X k → ℝ), ContDiff ℝ (⊤ : ENat) ψ →
        Submission.BoseGases.PermInvariant k ψ →
        ∀ u : E3, u ∈ Work.SmallBoxSliding.goodSet (PBℓ v μ) (PBd v μ) μ →
          perBoxCubeLHSFun v h R c₁ C μ k
            (sharpBoxState (dlBox (PBℓ v μ) (PBd v μ) u) ψ) u
          ≤ Work.BoseFixB1B.sbWordCube v h μ u
              (sharpBoxState (dlBox (PBℓ v μ) (PBd v μ) u) ψ)

/-! ## 2. The matched word vanishes on a.e.-zero states -/

/-- **The matched word vanishes on a state that is `0` a.e. on the analysis box** — the cube twin of
`Work.BoseFixB1B.fibreWord_ae_eq_zero`, from the three slot lemmas. -/
theorem sbWordCube_eq_zero_of_ae_eq_zero {v : E3 → ℝ} {h : ScatSol v} {μ : ℝ} {u : E3} {N : ℕ}
    (hℓ : 0 < PBℓ v μ) (hd : 0 < PBd v μ) (hN : 0 < N) {Ψ : X N → ℝ} (hΨm : Measurable Ψ)
    (hΨ : Ψ =ᵐ[(volume : Measure (X N)).restrict (abox N (PBℓ v μ))] 0) :
    Work.BoseFixB1B.sbWordCube v h μ u Ψ = 0 := by
  have hA : MeasurableSet (bA v μ u) :=
    Work.SmallBoxSliding.measurableSet_dlBox (bSide v μ) (bD v μ) u
  have hAc : bA v μ u ⊆ acube (bSide v μ) :=
    Work.SmallBoxSliding.dlBox_subset_acube (bSide v μ) (bD v μ) u
  have hM1 : 1 ≤ bM v μ := Work.BoseFixB1B.one_le_PBM v μ
  have hχA : ∀ z : E3, z ∉ bA v μ u → chiSmallB (bM v μ) (bSide v μ) (bD v μ) u z = 0 :=
    fun z hz => by
      by_contra hne
      exact hz (Work.SlotWord.chiSmallB_support_mem_dlBox hM1 hℓ hd hne)
  rcases lt_or_ge 0 (bSide v μ) with hpos | hnonpos
  · have hgap : Work.UBBInputs8.cnPlusBoxInd (bSide v μ) (bA v μ u) (bV v μ u) Ψ = 0 :=
      Work.BoseFixB1.Cube.Loc.cnPlusBoxInd_eq_zero_of_ae_eq_zero (a := bSide v μ) (A := bA v μ u)
        (V := bV v μ u) hpos hA hAc hΨm hΨ
    have hspec : Work.UBBInputs8.tBdiagFormInd (bSide v μ) (bA v μ u) (bV v μ u)
        (chiSmallB (bM v μ) (bSide v μ) (bD v μ) u) (fsKinCoeff (sbCut μ (a v))) Ψ = 0 :=
      Work.BoseFixB1.Cube.Loc.tBdiagFormInd_eq_zero_of_ae_eq_zero (N := N) (a := bSide v μ)
        (V := bV v μ u) (A := bA v μ u) hA hAc hχA hΨ
    have hpot : sbPot h μ u Ψ = 0 := by
      rw [Work.BoseFixB1.sbPot, Work.SmallBoxSliding.qLHSwordB, Submission.BoseGases.qLHSword]
      rw [MeasureTheory.integral_congr_ae ?_, MeasureTheory.integral_zero]
      filter_upwards [hΨ] with x hx
      simp only [Pi.zero_apply] at hx
      rw [hx]
      ring
    unfold Work.BoseFixB1B.sbWordCube Work.BoseFixB1B.sbKinCube Work.BoseFixB1B.cubeSpectral
      Work.UBBInputs8.tBwordKinInd
    rw [hgap, hspec, hpot]
    ring
  · -- a degenerate box: every slot integrates over a null box
    have hzero : Work.BoseFixB1B.sbWordCube v h μ u Ψ = 0 :=
      Work.BoseFixB1.Cube.Loc.sbWordCube_eq_zero_of_bSide_nonpos u hN hnonpos
    exact hzero

/-- **A sharp state of vanishing mass is `0` a.e.** (its mass is the box integral of its square;
integrability of the square follows from continuity on the compact box). -/
lemma sharpState_ae_zero_of_normB_eq_zero {v : E3 → ℝ} {μ : ℝ} {u : E3} {k : ℕ} {ψ : X k → ℝ}
    (hψc : Continuous ψ)
    (hm0 : Work.BoseBoxFix.normB v μ k (sharpBoxState (dlBox (PBℓ v μ) (PBd v μ) u) ψ) = 0) :
    sharpBoxState (dlBox (PBℓ v μ) (PBd v μ) u) ψ
      =ᵐ[(volume : Measure (X k)).restrict (abox k (PBℓ v μ))] 0 :=
  Work.BoseFixB1B.sharpState_ae_zero_aux (L := PBℓ v μ) (d := PBd v μ) u hψc
    (by simpa only [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB] using hm0)

/-! ## 3. The extension -/

/-- **Smooth → sharp at the cube window.**  From the in-box row (for smooth, normalised, localised
states) and the convergence of the word along the cutoff approximants, the row holds at the sharp
states `1_{B(u)^k}·ψ`. -/
theorem sharpCubeRow_body {v : E3 → ℝ} {h : ScatSol v} {R c₁ C ε₀ : ℝ}
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v)
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v) (hε₀ : 0 < ε₀)
    (hinB : InBoxCubeRowBody v h R c₁ C ε₀) (hconvB : CutProdConvBody v h R ε₀) :
    SharpCubeRowBody v h R c₁ C ε₀ := by
  classical
  intro μ hμ k ψ hψcd hψperm u hu
  have hμ0 : 0 < μ := hμ.1
  have hℓ : 0 < PBℓ v μ := Work.BoseFixB1.adm_ell_pos hμ
  have hd : 0 < PBd v μ := Work.BoseFixB1.adm_d_pos hμ
  rcases eq_or_ne (Work.BoseBoxFix.normB v μ k
      (sharpBoxState (dlBox (PBℓ v μ) (PBd v μ) u) ψ)) 0 with hm0 | hm0
  · -- degenerate case: both sides vanish
    have hae := sharpState_ae_zero_of_normB_eq_zero (v := v) (μ := μ) (u := u) hψcd.continuous hm0
    have hword : Work.BoseFixB1B.sbWordCube v h μ u
        (sharpBoxState (dlBox (PBℓ v μ) (PBd v μ) u) ψ) = 0 := by
      rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        exact Work.BoseB1Cube.sbWordCube_zero_particle (v := v) h μ u _
      · exact sbWordCube_eq_zero_of_ae_eq_zero hℓ hd (Nat.pos_of_ne_zero hk0)
          (hψcd.continuous.measurable.indicator (Work.PerSector.slotBox_measurable
            (Work.SmallBoxSliding.measurableSet_dlBox (PBℓ v μ) (PBd v μ) u))) hae
    have hdem : perBoxCubeLHSFun v h R c₁ C μ k
        (sharpBoxState (dlBox (PBℓ v μ) (PBd v μ) u) ψ) u = 0 := by
      rw [perBoxCubeLHSFun_eq]
      have hI : (∫ x in abox k (PBℓ v μ),
          (sharpBoxState (dlBox (PBℓ v μ) (PBd v μ) u) ψ x) ^ 2
            * demandWeight (v := v) μ u x) = 0 := by
        rw [MeasureTheory.integral_congr_ae ?_, MeasureTheory.integral_zero]
        filter_upwards [hae] with x hx
        simp only [Pi.zero_apply] at hx
        rw [hx]
        ring
      rw [hI, hm0]
      ring
    rw [hword, hdem]

  · -- nondegenerate case: the cutoff approximants and the limit
    have hmpos : 0 < Work.BoseBoxFix.normB v μ k (sharpBoxState (dlBox (PBℓ v μ) (PBd v μ) u) ψ) :=
      lt_of_le_of_ne (Work.BoseFixB1.normB_nonneg _) (Ne.symm hm0)
    obtain ⟨K, γ, hcut⟩ := Work.BoseFixB1B.exists_isCutFamily_of_smoothCutoff
      (Work.BoseFixB1B.exists_smoothCutoffB hℓ hd u)
    -- the sup bound of `ψ` on the box
    obtain ⟨Cb0, hCb0⟩ := (abox_compact k hℓ).exists_bound_of_continuousOn hψcd.continuous.continuousOn
    set Cb : ℝ := max Cb0 0 with hCbdef
    have hCb : 0 ≤ Cb := le_max_right _ _
    have hψb : ∀ x ∈ abox k (PBℓ v μ), |ψ x| ≤ Cb := by
      intro x hx
      rw [← Real.norm_eq_abs]
      exact le_trans (hCb0 x hx) (le_max_left _ _)
    -- the two convergences
    have hdem := tendsto_perBoxCubeLHSFun_cutProd (v := v) (h := h) (R := R) (c₁ := c₁) (C := C)
      hμ0 hℓ hd hcut hψcd hCb hψb
    have hword := hconvB μ hμ u hu k ψ hψcd hCb hψb hcut
    have hmass := Work.BoseFixB1B.tendsto_cutProd_mass (k := k) (L := PBℓ v μ) (d := PBd v μ)
      (u := u) (ψ := ψ) (K := K) (γ := γ) hℓ hd hcut hψcd.continuous
    refine le_of_tendsto_of_tendsto hdem hword ?_
    filter_upwards [hmass.eventually (Ioi_mem_nhds hmpos), self_mem_nhdsWithin] with δ hδm hδpos
    -- the normalised approximant
    set t : ℝ := (Real.sqrt (∫ x in abox k (PBℓ v μ), (cutProd (γ δ) ψ x) ^ 2))⁻¹ with ht
    have htne : t ≠ 0 := inv_ne_zero (Real.sqrt_pos_of_pos hδm).ne'
    have hcdδ : ContDiff ℝ (⊤ : ENat) (fun x : X k => t * cutProd (γ δ) ψ x) :=
      contDiff_const.mul (Work.BoseFixB1B.contDiff_cutProd (hcut.2 δ hδpos).1 hψcd)
    have hpermδ : Submission.BoseGases.PermInvariant k (fun x : X k => t * cutProd (γ δ) ψ x) := by
      intro σ x
      show t * cutProd (γ δ) ψ (Submission.BoseGases.actPerm k σ x)
        = t * cutProd (γ δ) ψ x
      congr 1
      simp only [Work.BoseFixB1B.cutProd_apply]
      rw [hψperm σ x]
      congr 1
      simpa only [Submission.BoseGases.actPerm] using
        Equiv.prod_comp σ (fun j : Fin k => γ δ (x j))
    have hmassδ : 0 < ∫ x in abox k (PBℓ v μ), (t * cutProd (γ δ) ψ x) ^ 2 := by
      rw [show (fun x : X k => (t * cutProd (γ δ) ψ x) ^ 2)
          = (fun x => t ^ 2 * (cutProd (γ δ) ψ x) ^ 2) from by funext x; ring]
      rw [MeasureTheory.integral_const_mul]
      exact mul_pos (sq_pos_of_ne_zero htne) hδm
    have hneδ : (fun x : X k => t * cutProd (γ δ) ψ x) ≠ 0 := by
      intro hzero
      have h0 : (∫ x in abox k (PBℓ v μ), (t * cutProd (γ δ) ψ x) ^ 2) = 0 := by
        have hfun : (fun x : X k => (t * cutProd (γ δ) ψ x) ^ 2) = 0 := by
          funext x
          rw [congrFun hzero x]
          simp
        rw [hfun]
        simp
      linarith
    have hnormδ : (∫ x in abox k (PBℓ v μ), (t * cutProd (γ δ) ψ x) ^ 2) = 1 := by
      rw [show (fun x : X k => (t * cutProd (γ δ) ψ x) ^ 2)
          = (fun x => t ^ 2 * (cutProd (γ δ) ψ x) ^ 2) from by funext x; ring]
      rw [MeasureTheory.integral_const_mul]
      have ht2 : t ^ 2 = (∫ x in abox k (PBℓ v μ), (cutProd (γ δ) ψ x) ^ 2)⁻¹ := by
        rw [ht, inv_pow, Real.sq_sqrt hδm.le]
      rw [ht2, inv_mul_cancel₀ (ne_of_gt hδm)]
    have hsuppδ : ∀ᵐ x ∂(volume.restrict (abox k (PBℓ v μ))),
        (fun x : X k => t * cutProd (γ δ) ψ x) x ≠ 0 → ∀ i : Fin k, x i ∈ dlBox (PBℓ v μ) (PBd v μ) u := by
      refine Eventually.of_forall (fun x hx i => ?_)
      have hcp : cutProd (γ δ) ψ x ≠ 0 := by
        intro h0
        exact hx (by simp only [h0, mul_zero])
      rw [Work.BoseFixB1B.cutProd_apply] at hcp
      have hγ : γ δ (x i) ≠ 0 := by
        intro h0
        exact hcp (by rw [Finset.prod_eq_zero (Finset.mem_univ i) h0, zero_mul])
      exact (hcut.2 δ hδpos).2.1 (subset_tsupport _ (Function.mem_support.mpr hγ))
    -- the in-box row at the normalised approximant
    let Φbd : Work.BoseKinLoc.BoxState k (sideAt μ (a v)) :=
      { toFun := fun x : X k => t * cutProd (γ δ) ψ x,
        contDiff := hcdδ, symm := hpermδ, nezero := hneδ }
    have hPer : Work.BoseFixB1S.PerBoxFCube v h R c₁ C μ k Φbd u :=
      hinB μ hμ k Φbd u hu
        (by simpa only [Φbd] using hsuppδ)
        (by simpa only [Φbd, Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB] using hnormδ)
    have hrow : perBoxCubeLHSFun v h R c₁ C μ k (fun x : X k => t * cutProd (γ δ) ψ x) u
        ≤ Work.BoseFixB1B.sbWordCube v h μ u (fun x : X k => t * cutProd (γ δ) ψ x) := by
      have h1 := (perBoxFCube_iff (v := v) (h := h) (R := R) (c₁ := c₁) (C := C) (μ := μ)
        (n := k) Φbd u).mp hPer
      simpa only [perBoxCubeLHS_eq_fun, Φbd] using h1
    -- strip the normalisation
    rw [perBoxCubeLHSFun_const_mul (v := v) (h := h) (R := R) (c₁ := c₁) (C := C) (μ := μ)
        (n := k) (cutProd (γ δ) ψ) u t,
      Work.BoseFixB1S.sbWordCube_smul h u (cutProd (γ δ) ψ) t] at hrow
    exact le_of_mul_le_mul_left hrow (by positivity : 0 < t ^ 2)


end Work.BoseB1Cube
