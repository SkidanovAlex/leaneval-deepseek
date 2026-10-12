import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.NomRowDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.nomArbAux` — the **nominal** arity passage (piece B of
# `nominalPerBoxRow`)

Holder: `Submission/Work/BoseB1Cube/nomRowArbState.lean`
(the node `Work.BoseB1Cube.NomRowArbState v h R`).

The corpus's arity passage (`Work.BoseB1Cube.cubePerBox_of_inBoxCubeRow` +
`cubeArityAssembly.cubePerBox_of_pieces`) runs the per-slot fibre decomposition of the
**smooth-count** demand `perBoxCubeLHSFun`.  Piece B is the same passage in the **nominal**
(indicator-count) spelling, i.e. for the demand `nomRow` / the `F`-weight
`ψ(1,μ, boxIndCount(x)/|B|)`.

The module supplies

* `nomCoeff` and `nomRow_eq_coeff` — the demand is the state-independent coefficient
  `nomCoeff` times the state's `abox`-mass (this is why the nominal per-slot row needs the
  **mass** fibre factorisation in addition to the word one);
* `nomRow_const_mul` — the demand is `2`-homogeneous in the state;
* `NomInBoxRowBody` / `NomSharpRowBody` — the in-box row and the sharp (indicator-truncated)
  row in the nominal spelling;
* `perBoxFNom_le_iff_nomRow` — for an a.e.-in-box `BoxState` the nominal `PerBoxFNom` **is**
  `nomRow ≤ sbWordCube` (the in-box collapse of the configuration-level count);
* `tendsto_nomRow_cutProd` — the demand converges along the smooth-cutoff approximants of the
  sharp state (immediate from `Work.BoseFixB1B.tendsto_cutProd_mass`, because the nominal
  demand is the mass times a constant);
* `nomSharpRow_body` — smooth in-box row + word convergence ⟹ the sharp in-box row.

Nothing here is analytic: the one genuinely analytic step (the word convergence) is the PROVED
`Work.BoseB1Cube.tendsto_sbWordCube_cutProd`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1
  Work.SmallBoxSliding Work.BoseKinLoc Work.PerSector Work.SlotWord Work.BoseFixB1B

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false

open Classical

/-! ## 1. The demand coefficient and its homogeneity -/

/-- **The state-independent coefficient of the nominal per-box demand.**  The `F`-weight of the
nominal row is read at the *configuration* level; at the level of the whole `abox`-mass only the
coefficient `c₁·∬w_{1,B}·ψ(1,μp, n/|B|) − ½μp²∬w_{1,B} − E` survives, and it is the same for every
state of `n` particles. -/
noncomputable def nomCoeff (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R c₁ C μ : ℝ) (u : E3)
    (k : ℕ) : ℝ :=
  c₁ * (nomW v h μ u * Work.SmallBoxSliding.psiWeight 1 μ ((k : ℝ) / nomV v μ u))
    - (1 / 2) * μ ^ 2 * nomW v h μ u - nomESlot v R C μ μ u

/-- The nominal demand is the coefficient times the `abox`-mass. -/
theorem nomRow_eq_coeff (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R c₁ C μ : ℝ) (n : ℕ) (u : E3)
    (Ψ : X n → ℝ) :
    nomRow v h R c₁ C μ μ n u Ψ
      = nomCoeff v h R c₁ C μ u n
        * (∫ x in abox n (sideAt μ (a v)), (Ψ x) ^ 2) := by
  rw [nomRow_eq, nomCoeff]

/-- The nominal demand is `2`-homogeneous in the state. -/
theorem nomRow_const_mul {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R c₁ C μ : ℝ} {n : ℕ} {u : E3}
    (Ψ : X n → ℝ) (t : ℝ) :
    nomRow v h R c₁ C μ μ n u (fun x => t * Ψ x) = t ^ 2 * nomRow v h R c₁ C μ μ n u Ψ := by
  rw [nomRow_eq_coeff, nomRow_eq_coeff,
    show (∫ x in abox n (sideAt μ (a v)), (t * Ψ x) ^ 2)
        = t ^ 2 * ∫ x in abox n (sideAt μ (a v)), (Ψ x) ^ 2 from
      Work.BoseFixB1S.normB_smul' Ψ t]
  ring

/-- The coefficient is monotone in `c₁` (the `F`-weight is nonnegative). -/
theorem nomCoeff_mono_c₁ {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R C μ c₁ c₁' : ℝ} {u : E3}
    (k : ℕ) (hc : c₁' ≤ c₁) (hW : 0 ≤ nomW v h μ u)
    (hψ : 0 ≤ Work.SmallBoxSliding.psiWeight 1 μ ((k : ℝ) / nomV v μ u)) :
    nomCoeff v h R c₁' C μ u k ≤ nomCoeff v h R c₁ C μ u k := by
  rw [nomCoeff, nomCoeff]
  have : c₁' * (nomW v h μ u * Work.SmallBoxSliding.psiWeight 1 μ ((k : ℝ) / nomV v μ u))
      ≤ c₁ * (nomW v h μ u * Work.SmallBoxSliding.psiWeight 1 μ ((k : ℝ) / nomV v μ u)) :=
    mul_le_mul_of_nonneg_right hc (mul_nonneg hW hψ)
  linarith

/-! ## 2. The two rows of the nominal passage -/

/-- **The nominal in-box row, at fixed constants.**  `nomRow ≤ sbWordCube` for every a.e.-in-box
`BoxState` on the good set, at the slot `μ`.  This is exactly the hypothesis of
`Work.BoseB1Cube.NomRowArbState` read at an in-box state (`perBoxFNom_le_iff_nomRow`). -/
def NomInBoxRowBody (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R c₁ C ε₀ : ℝ) : Prop :=
  ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
    ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (PBℓ v μ)) (u : E3),
      u ∈ goodSet (PBℓ v μ) (PBd v μ) μ →
      (∀ᵐ x ∂((volume : Measure (X n)).restrict (abox n (PBℓ v μ))),
        (Φ : X n → ℝ) x ≠ 0 → ∀ i : Fin n, x i ∈ dlBox (PBℓ v μ) (PBd v μ) u) →
      nomRow v h R c₁ C μ μ n u (Φ : X n → ℝ)
        ≤ Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ)

/-- **The nominal in-box row at the sharp states** — the input of the per-slot fibre step
(`nomCoeff_slot_le_word`). -/
def NomSharpRowBody (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R c₁ C ε₀ : ℝ) : Prop :=
  ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
    ∀ (k : ℕ) (ψ : X k → ℝ), ContDiff ℝ (⊤ : ENat) ψ → Submission.BoseGases.PermInvariant k ψ →
      ∀ u : E3, u ∈ goodSet (PBℓ v μ) (PBd v μ) μ →
        nomRow v h R c₁ C μ μ k u (Work.BoseFixB1B.sharpBoxState (PBB v μ u) ψ)
          ≤ Work.BoseFixB1B.sbWordCube v h μ u (Work.BoseFixB1B.sharpBoxState (PBB v μ u) ψ)

/-! ## 3. The in-box collapse of the nominal row -/

/-- **At an a.e.-in-box `BoxState` the configuration-level count is the constant `n`**, so the
nominal `PerBoxFNom` *is* the state-level row `nomRow ≤ sbWordCube`. -/
theorem perBoxFNom_le_iff_nomRow {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R c₁ C μ : ℝ} {n : ℕ}
    {u : E3} {Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))}
    (hloc : ∀ᵐ x ∂((volume : Measure (X n)).restrict (abox n (sideAt μ (a v)))),
      (Φ : X n → ℝ) x ≠ 0 → ∀ i : Fin n, x i ∈ dlBox (sideAt μ (a v)) ((paramsAt μ (a v)).d) u) :
    PerBoxFNom v h R c₁ C μ μ n Φ u ↔
      nomRow v h R c₁ C μ μ n u (Φ : X n → ℝ)
        ≤ Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ) := by
  classical
  have hI : (∫ x in abox n (sideAt μ (a v)), (Φ : X n → ℝ) x ^ 2
        * Work.SmallBoxSliding.psiWeight 1 μ
            (boxIndCount (sideAt μ (a v)) (paramsAt μ (a v)).d u x
              / Work.SmallBoxSliding.boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u))
      = Work.SmallBoxSliding.psiWeight 1 μ
          ((n : ℝ) / Work.SmallBoxSliding.boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u)
        * (∫ x in abox n (sideAt μ (a v)), (Φ : X n → ℝ) x ^ 2) := by
    rw [show (∫ x in abox n (sideAt μ (a v)), (Φ : X n → ℝ) x ^ 2
          * Work.SmallBoxSliding.psiWeight 1 μ
              (boxIndCount (sideAt μ (a v)) (paramsAt μ (a v)).d u x
                / Work.SmallBoxSliding.boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u))
        = ∫ x in abox n (sideAt μ (a v)), (Work.SmallBoxSliding.psiWeight 1 μ
              ((n : ℝ) / Work.SmallBoxSliding.boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u)
            * (Φ : X n → ℝ) x ^ 2) from ?_]
    · rw [MeasureTheory.integral_const_mul]
    · refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hloc] with x hx
      by_cases h0 : (Φ : X n → ℝ) x = 0
      · rw [h0]; ring
      · have hx' : ∀ i : Fin n, x i ∈ dlBox (sideAt μ (a v)) ((paramsAt μ (a v)).d) u := hx h0
        have hcount : boxIndCount (sideAt μ (a v)) (paramsAt μ (a v)).d u x = (n : ℝ) := by
          rw [boxIndCount]
          rw [Finset.sum_congr rfl (fun i _ => Set.indicator_of_mem (hx' i) (fun _ => (1 : ℝ)))]
          simp
        rw [hcount]
        ring
  constructor
  · intro hper
    rw [PerBoxFNom, hI] at hper
    rw [nomRow_eq]
    simp only [nomW, nomV, nomESlot, nomChi, nomGamma, Work.BoseBoxFix.normB,
      Work.BoseKinLoc.sqNormB] at hper ⊢
    ring_nf at hper ⊢
    linarith
  · intro hrow
    rw [PerBoxFNom, hI]
    rw [nomRow_eq] at hrow
    simp only [nomW, nomV, nomESlot, nomChi, nomGamma, Work.BoseBoxFix.normB,
      Work.BoseKinLoc.sqNormB] at hrow ⊢
    ring_nf at hrow ⊢
    linarith

/-! ## 4. Convergence of the nominal demand along the cutoff approximants -/

/-- The nominal demand converges along the smooth-cutoff approximants of the sharp state: it is
`nomCoeff` times the state's `abox`-mass, so this is `Work.BoseFixB1B.tendsto_cutProd_mass`. -/
theorem tendsto_nomRow_cutProd {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R c₁ C μ : ℝ} {n : ℕ}
    {u : E3} {ψ : X n → ℝ} {K : ℝ} {γ : ℝ → E3 → ℝ}
    (hℓ : 0 < PBℓ v μ) (hd : 0 < PBd v μ)
    (hcut : Work.BoseFixB1B.IsCutFamily (PBℓ v μ) (PBd v μ) u K γ) (hψ : Continuous ψ) :
    Tendsto (fun δ : ℝ => nomRow v h R c₁ C μ μ n u (Work.BoseFixB1B.cutProd (γ δ) ψ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (nomRow v h R c₁ C μ μ n u
        (Work.BoseFixB1B.sharpBoxState (dlBox (PBℓ v μ) (PBd v μ) u) ψ))) := by
  have hmass := Work.BoseFixB1B.tendsto_cutProd_mass (k := n) (L := PBℓ v μ) (d := PBd v μ)
    (u := u) (ψ := ψ) (K := K) (γ := γ) hℓ hd hcut hψ
  have h2 := hmass.const_mul (nomCoeff v h R c₁ C μ u n)
  simpa only [nomRow_eq_coeff] using h2

/-! ## 5. Smooth ⟹ sharp in the nominal spelling -/

/-- **Smooth in-box row ⟹ sharp in-box row**, in the nominal spelling.  The proof is the nominal
transcript of `Work.BoseB1Cube.sharpCubeRow_body`: approximate the sharp state
`1_{B^k}·ψ` by the normalised products `cutProd (γ δ) ψ`, apply the in-box row there, and pass to
the limit along the two convergences (demand: `tendsto_nomRow_cutProd`; word:
`CutProdConvBody`, discharged by `Work.BoseB1Cube.tendsto_sbWordCube_cutProd`).  The degenerate
case (vanishing sharp mass) is handled by the vanishing of `sbWordCube` on a.e.-zero states. -/
theorem nomSharpRow_body {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R c₁ C ε₀ : ℝ}
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v)
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v) (hε₀ : 0 < ε₀)
    (hinB : NomInBoxRowBody v h R c₁ C ε₀) (hconvB : CutProdConvBody v h R ε₀) :
    NomSharpRowBody v h R c₁ C ε₀ := by
  classical
  intro μ hμ k ψ hψcd hψperm u hu
  have hμ0 : 0 < μ := hμ.1
  have hℓ : 0 < PBℓ v μ := Work.BoseFixB1.adm_ell_pos hμ
  have hd : 0 < PBd v μ := Work.BoseFixB1.adm_d_pos hμ
  rcases eq_or_ne (Work.BoseBoxFix.normB v μ k (Work.BoseFixB1B.sharpBoxState (PBB v μ u) ψ))
      0 with hm0 | hm0
  · -- degenerate case: the demand vanishes and so does the word
    have hae := sharpState_ae_zero_of_normB_eq_zero (v := v) (μ := μ) (u := u)
      hψcd.continuous hm0
    have hm0' : (∫ x in abox k (sideAt μ (a v)),
        (Work.BoseFixB1B.sharpBoxState (PBB v μ u) ψ x) ^ 2) = 0 := by
      simpa only [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB] using hm0
    have hword : Work.BoseFixB1B.sbWordCube v h μ u
        (Work.BoseFixB1B.sharpBoxState (PBB v μ u) ψ) = 0 := by
      rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        exact sbWordCube_zero_particle (v := v) h μ u _
      · refine sbWordCube_eq_zero_of_ae_eq_zero (v := v) (h := h) (μ := μ)
          (u := u) (N := k) hℓ hd (Nat.pos_of_ne_zero hk0) ?_ hae
        exact hψcd.continuous.measurable.indicator (Work.PerSector.slotBox_measurable
          (ι := Fin k) (Work.SmallBoxSliding.measurableSet_dlBox (PBℓ v μ) (PBd v μ) u))
    rw [hword, nomRow_eq_coeff, hm0']
    norm_num
  · -- nondegenerate case: the cutoff approximants and the limit
    have hmpos : 0 < Work.BoseBoxFix.normB v μ k
        (Work.BoseFixB1B.sharpBoxState (PBB v μ u) ψ) :=
      lt_of_le_of_ne (Work.BoseFixB1.normB_nonneg _) (Ne.symm hm0)
    obtain ⟨K, γ, hcut⟩ := Work.BoseFixB1B.exists_isCutFamily_of_smoothCutoff
      (Work.BoseFixB1B.exists_smoothCutoffB hℓ hd u)
    obtain ⟨Cb0, hCb0⟩ := (abox_compact k hℓ).exists_bound_of_continuousOn hψcd.continuous.continuousOn
    set Cb : ℝ := max Cb0 0 with hCbdef
    have hCb : 0 ≤ Cb := le_max_right _ _
    have hψb : ∀ x ∈ abox k (PBℓ v μ), |ψ x| ≤ Cb := by
      intro x hx
      rw [← Real.norm_eq_abs]
      exact le_trans (hCb0 x hx) (le_max_left _ _)
    have hdem := tendsto_nomRow_cutProd (v := v) (h := h) (R := R) (c₁ := c₁) (C := C)
      (μ := μ) (n := k) (u := u) (ψ := ψ) (K := K) (γ := γ) hℓ hd hcut hψcd.continuous
    have hword := hconvB μ hμ u hu k ψ hψcd hCb hψb hcut
    have hmass := Work.BoseFixB1B.tendsto_cutProd_mass (k := k) (L := PBℓ v μ) (d := PBd v μ)
      (u := u) (ψ := ψ) (K := K) (γ := γ) hℓ hd hcut hψcd.continuous
    refine le_of_tendsto_of_tendsto hdem hword ?_
    filter_upwards [hmass.eventually (Ioi_mem_nhds hmpos), self_mem_nhdsWithin] with δ hδm hδpos
    -- the normalised approximant
    set t : ℝ := (Real.sqrt (∫ x in abox k (PBℓ v μ),
      (Work.BoseFixB1B.cutProd (γ δ) ψ x) ^ 2))⁻¹ with ht
    have htne : t ≠ 0 := inv_ne_zero (Real.sqrt_pos_of_pos hδm).ne'
    have hcdδ : ContDiff ℝ (⊤ : ENat)
        (fun x : X k => t * Work.BoseFixB1B.cutProd (γ δ) ψ x) :=
      contDiff_const.mul (Work.BoseFixB1B.contDiff_cutProd (hcut.2 δ hδpos).1 hψcd)
    have hpermδ : Submission.BoseGases.PermInvariant k
        (fun x : X k => t * Work.BoseFixB1B.cutProd (γ δ) ψ x) := by
      intro σ x
      show t * Work.BoseFixB1B.cutProd (γ δ) ψ (Submission.BoseGases.actPerm k σ x)
        = t * Work.BoseFixB1B.cutProd (γ δ) ψ x
      congr 1
      simp only [Work.BoseFixB1B.cutProd_apply]
      rw [hψperm σ x]
      congr 1
      simpa only [Submission.BoseGases.actPerm] using
        Equiv.prod_comp σ (fun j : Fin k => γ δ (x j))
    have hmassδ : 0 < ∫ x in abox k (PBℓ v μ),
        (t * Work.BoseFixB1B.cutProd (γ δ) ψ x) ^ 2 := by
      rw [show (fun x : X k => (t * Work.BoseFixB1B.cutProd (γ δ) ψ x) ^ 2)
          = (fun x => t ^ 2 * (Work.BoseFixB1B.cutProd (γ δ) ψ x) ^ 2) from by funext x; ring]
      rw [MeasureTheory.integral_const_mul]
      exact mul_pos (sq_pos_of_ne_zero htne) hδm
    have hnormδ : (∫ x in abox k (PBℓ v μ),
        (t * Work.BoseFixB1B.cutProd (γ δ) ψ x) ^ 2) = 1 := by
      rw [show (fun x : X k => (t * Work.BoseFixB1B.cutProd (γ δ) ψ x) ^ 2)
          = (fun x => t ^ 2 * (Work.BoseFixB1B.cutProd (γ δ) ψ x) ^ 2) from by funext x; ring]
      rw [MeasureTheory.integral_const_mul]
      have ht2 : t ^ 2 = (∫ x in abox k (PBℓ v μ),
          (Work.BoseFixB1B.cutProd (γ δ) ψ x) ^ 2)⁻¹ := by
        rw [ht, inv_pow, Real.sq_sqrt hδm.le]
      rw [ht2, inv_mul_cancel₀ (ne_of_gt hδm)]
    have hneδ : (fun x : X k => t * Work.BoseFixB1B.cutProd (γ δ) ψ x) ≠ 0 := by
      intro hzero
      have h0 : (∫ x in abox k (PBℓ v μ),
          (t * Work.BoseFixB1B.cutProd (γ δ) ψ x) ^ 2) = 0 := by
        have hfun : (fun x : X k => (t * Work.BoseFixB1B.cutProd (γ δ) ψ x) ^ 2) = 0 := by
          funext x
          rw [congrFun hzero x]
          simp
        rw [hfun]
        simp
      linarith [hmassδ]
    have hsuppδ : ∀ᵐ x ∂((volume : Measure (X k)).restrict (abox k (PBℓ v μ))),
        (fun x : X k => t * Work.BoseFixB1B.cutProd (γ δ) ψ x) x ≠ 0 →
          ∀ i : Fin k, x i ∈ dlBox (PBℓ v μ) (PBd v μ) u := by
      refine Eventually.of_forall (fun x hx i => ?_)
      have hcp : Work.BoseFixB1B.cutProd (γ δ) ψ x ≠ 0 := by
        intro h0
        exact hx (by simp only [h0, mul_zero])
      rw [Work.BoseFixB1B.cutProd_apply] at hcp
      have hγ : γ δ (x i) ≠ 0 := by
        intro h0
        exact hcp (by rw [Finset.prod_eq_zero (Finset.mem_univ i) h0, zero_mul])
      exact (hcut.2 δ hδpos).2.1 (subset_tsupport _ (Function.mem_support.mpr hγ))
    -- the in-box row at the normalised approximant
    let Φbd : Work.BoseKinLoc.BoxState k (sideAt μ (a v)) :=
      { toFun := fun x : X k => t * Work.BoseFixB1B.cutProd (γ δ) ψ x,
        contDiff := hcdδ, symm := hpermδ, nezero := hneδ }
    have hPer := hinB μ hμ k Φbd u hu (by simpa only [Φbd] using hsuppδ)
    have hrow : nomRow v h R c₁ C μ μ k u
          (fun x : X k => t * Work.BoseFixB1B.cutProd (γ δ) ψ x)
        ≤ Work.BoseFixB1B.sbWordCube v h μ u
          (fun x : X k => t * Work.BoseFixB1B.cutProd (γ δ) ψ x) := hPer
    -- strip the normalisation
    rw [nomRow_const_mul, Work.BoseFixB1S.sbWordCube_smul] at hrow
    exact le_of_mul_le_mul_left hrow (by positivity : 0 < t ^ 2)

/-! ## 6. The per-slot fibre step -/

/-- **The per-slot row of the nominal passage**: the coefficient times the slot mass is dominated by
the matched word of the slot piece.  The three inputs are exactly the three proved/delegated pieces:

* `hsharp` (`NomSharpRowBody`) — the row at the sharp in-box state of each fibre;
* `hmasse` — the **mass** fibre factorisation (`normB_slotFibre`), which is what lets the constant
  coefficient come out of the `y`-integral;
* `hworde` — the **word** fibre factorisation (`sbWordCube_slotFibre`).

Nothing else is used: the pointwise sharp row is integrated in `y`, the coefficient is a constant,
and the two factorisations identify the two endpoints. -/
theorem nomCoeff_slot_le_word {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R c₁ C ε₀ μ : ℝ}
    (hAdm : Work.BoseBoxFix.Adm v ε₀ μ) (u : E3) (hu : u ∈ goodSet (PBℓ v μ) (PBd v μ) μ)
    {n : ℕ} (Φ : Work.BoseKinLoc.BoxState n (PBℓ v μ))
    (hsharp : NomSharpRowBody v h R c₁ C ε₀)
    (hmasse : ∀ (S : Finset (Fin n)) (e : SlotIn n S ≃ Fin S.card), 0 < S.card →
      MeasureTheory.Integrable
        (fun y : SlotOut n S → E3 => ∫ x in abox S.card (PBℓ v μ),
          (Work.BoseFixB1B.sharpBoxState (PBB v μ u)
            (slotFibreState S e (Φ : X n → ℝ) y) x) ^ 2)
        ((volume : Measure (SlotOut n S → E3)).restrict (slotOutside (PBℓ v μ) (PBB v μ u) S))
      ∧ (∫ x in abox n (PBℓ v μ), (slotPiece (PBB v μ u) S (Φ : X n → ℝ) x) ^ 2)
        = ∫ y in slotOutside (PBℓ v μ) (PBB v μ u) S,
            ∫ x in abox S.card (PBℓ v μ),
              (Work.BoseFixB1B.sharpBoxState (PBB v μ u)
                (slotFibreState S e (Φ : X n → ℝ) y) x) ^ 2)
    (hworde : ∀ (S : Finset (Fin n)) (e : SlotIn n S ≃ Fin S.card), 0 < S.card →
      MeasureTheory.Integrable
        (fun y : SlotOut n S → E3 => Work.BoseFixB1B.sbWordCube v h μ u
          (Work.BoseFixB1B.sharpBoxState (PBB v μ u)
            (slotFibreState S e (Φ : X n → ℝ) y)))
        ((volume : Measure (SlotOut n S → E3)).restrict (slotOutside (PBℓ v μ) (PBB v μ u) S))
      ∧ Work.BoseFixB1B.sbWordCube v h μ u (slotPiece (PBB v μ u) S (Φ : X n → ℝ))
        = ∫ y in slotOutside (PBℓ v μ) (PBB v μ u) S,
            Work.BoseFixB1B.sbWordCube v h μ u
              (Work.BoseFixB1B.sharpBoxState (PBB v μ u)
                (slotFibreState S e (Φ : X n → ℝ) y)))
    (S : Finset (Fin n)) (hS : 0 < S.card) (e : SlotIn n S ≃ Fin S.card) :
    nomCoeff v h R c₁ C μ u S.card
        * (∫ x in abox n (PBℓ v μ), (slotPiece (PBB v μ u) S (Φ : X n → ℝ) x) ^ 2)
      ≤ Work.BoseFixB1B.sbWordCube v h μ u (slotPiece (PBB v μ u) S (Φ : X n → ℝ)) := by
  classical
  obtain ⟨hmI, hmE⟩ := hmasse S e hS
  obtain ⟨hwI, hwE⟩ := hworde S e hS
  -- the pointwise sharp row at each fibre
  have hpt : ∀ᵐ y ∂((volume : Measure (SlotOut n S → E3)).restrict
      (slotOutside (PBℓ v μ) (PBB v μ u) S)),
      nomCoeff v h R c₁ C μ u S.card
          * (∫ x in abox S.card (PBℓ v μ),
              (Work.BoseFixB1B.sharpBoxState (PBB v μ u)
                (slotFibreState S e (Φ : X n → ℝ) y) x) ^ 2)
        ≤ Work.BoseFixB1B.sbWordCube v h μ u
            (Work.BoseFixB1B.sharpBoxState (PBB v μ u)
              (slotFibreState S e (Φ : X n → ℝ) y)) :=
    Eventually.of_forall (fun y => by
      have hrow := hsharp μ hAdm S.card (slotFibreState S e (Φ : X n → ℝ) y)
        (Work.PerSector.contDiff_slotFibreState S e Φ.contDiff y)
        (Work.BoseFixB1B.permInvariant_slotFibreState S e Φ.symm y) u hu
      rwa [nomRow_eq_coeff] at hrow)
  have hInt1 : MeasureTheory.Integrable
      (fun y : SlotOut n S → E3 => nomCoeff v h R c₁ C μ u S.card
        * (∫ x in abox S.card (PBℓ v μ),
            (Work.BoseFixB1B.sharpBoxState (PBB v μ u)
              (slotFibreState S e (Φ : X n → ℝ) y) x) ^ 2))
      ((volume : Measure (SlotOut n S → E3)).restrict (slotOutside (PBℓ v μ) (PBB v μ u) S)) :=
    hmI.const_mul _
  have hmono := MeasureTheory.integral_mono_ae hInt1 hwI hpt
  have hcI : (∫ y in slotOutside (PBℓ v μ) (PBB v μ u) S,
        nomCoeff v h R c₁ C μ u S.card
          * (∫ x in abox S.card (PBℓ v μ),
              (Work.BoseFixB1B.sharpBoxState (PBB v μ u)
                (slotFibreState S e (Φ : X n → ℝ) y) x) ^ 2))
      = nomCoeff v h R c₁ C μ u S.card
        * (∫ y in slotOutside (PBℓ v μ) (PBB v μ u) S,
            ∫ x in abox S.card (PBℓ v μ),
              (Work.BoseFixB1B.sharpBoxState (PBB v μ u)
                (slotFibreState S e (Φ : X n → ℝ) y) x) ^ 2) :=
    MeasureTheory.integral_const_mul _ _
  rw [hcI, ← hmE, ← hwE] at hmono
  exact hmono

end Work.BoseB1Cube
