import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.BoseBoxFock.PCFU.Achan_dzero_split
import Submission.Work.BoseBoxFock.PCFU.Bchan_eq_imageSum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false

/-!
# `Work.BoseBoxFock.PCFU.Bchan_dzero_split`

The `d = 0` split of the `(B)`-channel at the image sum of the low cut-off kernel — the exact
`(B)`-twin of the proved `Work.BoseBoxFock.PCFU.Achan_dzero_split`.

`Bchan_eq_imageSum` writes the `(B)`-channel as

    Bchan = ℓ⁶ ∫_x G x · ∫_{u ∈ acube ℓ} (Σ'_d Κ(u − x_j + ℓ•latVec d))·Q_jP_iΘ(x[j↦u]) ,

with `G x = Θ x·χ_Λ(x j)·KχfrU(x j)` and `Κ = lowKer fc κ`.  The present module performs the
**exact** split of the image sum into its `d = 0` term and the rest: by
`int_imageSum_eq_lowKer_add` the inner integral is

    ∫_{u} Κ(x_j − u)·Q_jP_iΘ(x[j↦u])  +  ∫_{u} (Σ'_{d ≠ 0} Κ(u − x_j + ℓ•latVec d))·Q_jP_iΘ(x[j↦u]) ,

and by `lowSlot_eq_lowKer` the first summand is *exactly* the word factor
`lowSlot fc κ ℓ j (Q_jP_iΘ) x`.  Distributing `∫_x G·` over the sum (additivity of the Bochner
integral, both pieces bounded by `‖G‖·(kernel bound)·ℓ³`) gives the target identity

    Bchan = ℓ⁶ ∫_x G x·lowSlot fc κ ℓ j (Q_jP_iΘ) x
          + ℓ⁶ ∫_x G x·∫_{u ∈ acube ℓ} (Σ'_{d ≠ 0} Κ(u − x_j + ℓ•latVec d))·Q_jP_iΘ(x[j↦u]) .

The proof transcribes the `(A)`-channel proof verbatim; the only differences are the weight `G`
(measurability, the bound `Cθ·(√chiNormSq)⁻¹·Σ_k|Ŵ₁(k)χ̂(ℓκ_k)|` and the box-support) and the
starting point `Bchan_eq_imageSum` in place of `Achan_eq_imageSum`.
-/

/-! ## 1. Auxiliary lemmas -/

/-- **A measurable bounded function supported in a set of finite measure is integrable.** -/
private theorem integrable_of_bounded_support_bcs {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} (hs : μ s < ⊤) {f : α → ℂ} (hm : Measurable f)
    (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) (hsup : Function.support f ⊆ s) : Integrable f μ := by
  obtain ⟨C, hC⟩ := hb
  refine (MeasureTheory.integrableOn_iff_integrable_of_support_subset (μ := μ) (s := s)
    (f := f) hsup).mp ?_
  exact MeasureTheory.IntegrableOn.of_bound (s := s) (μ := μ) hs
    hm.aestronglyMeasurable.restrict (max C 0)
    (Filter.Eventually.of_forall fun x => le_trans (hC x) (le_max_left _ _))

/-- `latVec 0 = 0`. -/
private lemma latVec_zero_bcs : Work.BoseBoxFock.latVec (0 : Fin 3 → ℤ) = (0 : E3) := by
  ext i
  simp [Work.BoseBoxFock.latVec]

/-- `‖↑r‖ = |r|` for a real `r` seen in `ℂ`. -/
private lemma complexNorm_ofReal_bcs (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| :=
  norm_ofReal_eq_abs r

/-- **Summability of the image sum** of the low-momentum kernel along the lattice.  `lowKer_decay`
gives `(1 + ‖·‖)^{-4}` decay, which is summable on `ℤ³` (`summable_shift_latVec`). -/
private lemma summable_image_lowKer_bcs {fc : Work.BoseBoxFix.LowCut} {κ ℓ : ℝ} (hκ : 0 < κ)
    (hℓ : 0 < ℓ) (z : E3) :
    Summable (fun d : Fin 3 → ℤ =>
      ((lowKer fc κ (z + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ)) := by
  obtain ⟨C, hC0, hC⟩ := lowKer_decay fc hκ 2
  have h4 : ∀ q : E3, (0 : ℝ) < (1 + ‖q‖) ^ 4 := fun q => by positivity
  refine Work.BoseBoxFock.summable_shift_latVec (Φ := fun q : E3 => ((lowKer fc κ q : ℝ) : ℂ))
    (C := C) hC0 (fun q => ?_) hℓ z
  rw [complexNorm_ofReal_bcs, ← Real.norm_eq_abs]
  calc ‖lowKer fc κ q‖
      = ((1 + ‖q‖) ^ 4)⁻¹ * ((1 + ‖q‖) ^ 4 * ‖lowKer fc κ q‖) := by
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (h4 q)), one_mul]
    _ ≤ ((1 + ‖q‖) ^ 4)⁻¹ * C := mul_le_mul_of_nonneg_left (hC q) (inv_nonneg.mpr (h4 q).le)
    _ = C * (1 + ‖q‖) ^ (-((4 : ℕ) : ℤ)) := by rw [zpow_neg, zpow_natCast]; ring

/-- **The image sum in the `s`-frame form**: `Σ'_d Κ(z + ℓ•latVec d) = (Ksfr z + 1)/ℓ³`
(`Ksfr_eq_lowKer`). -/
private lemma imageSum_eq_Ksfr_bcs {v : E3 → ℝ} {fc : Work.BoseBoxFix.LowCut} {μ : ℝ} {N : ℕ}
    (hℓ : 0 < Work.BoseBoxFock.ellH v μ)
    (hκ : 0 < ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
    (hN : 2 * (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹) * Work.BoseBoxFock.ellH v μ
          / (2 * Real.pi) ≤ (N : ℝ)) (z : E3) :
    (∑' d : Fin 3 → ℤ, ((lowKer fc
        (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
          * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
        (z + Work.BoseBoxFock.ellH v μ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
      = (Work.BoseBoxFock.Ksfr v fc μ N z + 1) / ((Work.BoseBoxFock.ellH v μ : ℂ) ^ 3) := by
  have h := Ksfr_eq_lowKer (v := v) (fc := fc) (μ := μ) (N := N) hℓ hκ hN z
  have h3 : ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3 ≠ 0 := by
    rw [← Complex.ofReal_pow, ne_eq, Complex.ofReal_eq_zero]
    exact pow_ne_zero 3 (ne_of_gt hℓ)
  rw [eq_div_iff h3, h]
  ring

/-- **Uniform bound on the `s`-frame form** of the image sum. -/
private lemma KsfrImg_norm_le_bcs {v : E3 → ℝ} {fc : Work.BoseBoxFix.LowCut} {μ : ℝ} {N : ℕ}
    {C : ℝ} (hℓ : 0 < Work.BoseBoxFock.ellH v μ)
    (hC : ∀ z, ‖Work.BoseBoxFock.Ksfr v fc μ N z‖ ≤ C) (z : E3) :
    ‖(Work.BoseBoxFock.Ksfr v fc μ N z + 1) / ((Work.BoseBoxFock.ellH v μ : ℂ) ^ 3)‖
      ≤ (C + 1) / (Work.BoseBoxFock.ellH v μ) ^ 3 := by
  rw [norm_div]
  have h3 : ‖((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3‖ = (Work.BoseBoxFock.ellH v μ) ^ 3 := by
    rw [← Complex.ofReal_pow]
    rw [show ‖(((Work.BoseBoxFock.ellH v μ) ^ 3 : ℝ) : ℂ)‖
        = |(Work.BoseBoxFock.ellH v μ) ^ 3| from complexNorm_ofReal_bcs _]
    exact abs_of_nonneg (by positivity)
  rw [h3]
  gcongr
  calc ‖Work.BoseBoxFock.Ksfr v fc μ N z + 1‖
        ≤ ‖Work.BoseBoxFock.Ksfr v fc μ N z‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    _ ≤ C + 1 := by rw [norm_one]; exact add_le_add (hC z) le_rfl

/-- **The `d ≠ 0` tail of the image sum** is the full sum minus the `d = 0` term, written in the
`Ksfr` form. -/
private lemma tail_eq_lowKer_bcs {v : E3 → ℝ} {fc : Work.BoseBoxFix.LowCut} {μ : ℝ} {N : ℕ}
    (hℓ : 0 < Work.BoseBoxFock.ellH v μ)
    (hκ : 0 < ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
    (hN : 2 * (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹) * Work.BoseBoxFock.ellH v μ
          / (2 * Real.pi) ≤ (N : ℝ)) (z : E3) :
    (∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ) else ((lowKer fc
        (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
          * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
        (z + Work.BoseBoxFock.ellH v μ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
      = (Work.BoseBoxFock.Ksfr v fc μ N z + 1) / ((Work.BoseBoxFock.ellH v μ : ℂ) ^ 3)
        - ((lowKer fc (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
              * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹) z : ℝ) : ℂ) := by
  have hsumm := summable_image_lowKer_bcs (fc := fc) (κ := ((Work.BoseBox.paramsAt μ
      (BoseGases.a v)).d ^ 2 * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
    (ℓ := Work.BoseBoxFock.ellH v μ) hκ hℓ z
  have h := hsumm.tsum_eq_add_tsum_ite (0 : Fin 3 → ℤ)
  have h' : (∑' d : Fin 3 → ℤ, ((lowKer fc
        (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
          * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
        (z + Work.BoseBoxFock.ellH v μ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
      = ((lowKer fc (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
            * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹) z : ℝ) : ℂ)
        + ∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ) else ((lowKer fc
            (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
              * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
            (z + Work.BoseBoxFock.ellH v μ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ) := by
    simpa [latVec_zero_bcs, smul_zero, add_zero] using h
  have h'' : (∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ) else ((lowKer fc
        (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
          * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
        (z + Work.BoseBoxFock.ellH v μ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
      = (∑' d : Fin 3 → ℤ, ((lowKer fc
          (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
            * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
          (z + Work.BoseBoxFock.ellH v μ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
        - ((lowKer fc (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
              * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹) z : ℝ) : ℂ) := by
    rw [h']; ring
  rw [h'', imageSum_eq_Ksfr_bcs (v := v) (fc := fc) (μ := μ) (N := N) hℓ hκ hN z]

/-! ## 2. The target -/

theorem Bchan_dzero_split {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ)
    (hℓ : 0 < Work.BoseBoxFock.ellH v μ)
    (hκ : 0 < ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
    (hN : 2 * (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹) * Work.BoseBoxFock.ellH v μ
          / (2 * Real.pi) ≤ (N : ℝ))
    (Θ : Submission.BoseGases.X n → ℝ) (hΘ : Submission.BoseGases.PermInvariant n Θ)
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, |Θ x| ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ)) :
    (∫ q : Submission.BoseGases.X n
          × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)),
        ((Θ q.1 : ℝ) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (q.1 i)
          * Work.BoseBoxFock.PCFU.ChBU v h fc fu μ N q.2.1 (q.1 j) q.2.2
          * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ))
      = ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 6
          * (∫ x : Submission.BoseGases.X n,
              ((Θ x : ℝ) : ℂ)
                * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x j) : ℝ) : ℂ)
                * Work.BoseBoxFock.PCFU.KχfrU v h μ fu N (x j)
                * ((Work.BoseBoxFix.lowSlot fc
                      (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
                      (Work.BoseBoxFock.ellH v μ) j
                      (Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                        (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ)) x : ℝ) : ℂ))
        + ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 6
          * (∫ x : Submission.BoseGases.X n,
              ((Θ x : ℝ) : ℂ)
                * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x j) : ℝ) : ℂ)
                * Work.BoseBoxFock.PCFU.KχfrU v h μ fu N (x j)
                * (∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
                    (∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ)
                        else ((Work.BoseBoxFock.PCFU.lowKer fc
                          (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                            * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
                          (u - x j + Work.BoseBoxFock.ellH v μ
                            • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
                      * ((Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                          (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ)
                          (Function.update x j u) : ℝ) : ℂ))) := by
  obtain ⟨Cθ, hCθ⟩ := hΘb
  have hCθ0 : 0 ≤ Cθ := le_trans (abs_nonneg (Θ 0)) (hCθ 0)
  -- abbreviations
  set ℓ : ℝ := Work.BoseBoxFock.ellH v μ with hℓdef
  set κ : ℝ := ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
      * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹ with hκdef
  have hℓpos : 0 < ℓ := hℓ
  have hκpos : 0 < κ := hκ
  have hΘs' : Function.support Θ ⊆ Submission.BoseGases.abox n ℓ := hΘs
  set ψ : Submission.BoseGases.X n → ℝ :=
      Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ) with hψdef
  set G : Submission.BoseGases.X n → ℂ := fun x =>
      ((Θ x : ℝ) : ℂ)
        * ((Work.BoseK15.corpusBox.chiLam ℓ (x j) : ℝ) : ℂ)
        * Work.BoseBoxFock.PCFU.KχfrU v h μ fu N (x j) with hGdef
  set L1 : Submission.BoseGases.X n → ℝ :=
      fun x => Work.BoseBoxFix.lowSlot fc κ ℓ j ψ x with hL1def
  set J : Submission.BoseGases.X n → ℂ := fun x =>
      ∫ u in Submission.BoseGases.acube ℓ,
        (∑' d : Fin 3 → ℤ, ((lowKer fc κ (u - x j + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
          * ((ψ (Function.update x j u) : ℝ) : ℂ) with hJdef
  set J1 : Submission.BoseGases.X n → ℂ := fun x =>
      ∫ u in Submission.BoseGases.acube ℓ,
        ((lowKer fc κ (x j - u) : ℝ) : ℂ)
          * ((ψ (Function.update x j u) : ℝ) : ℂ) with hJ1def
  set J2 : Submission.BoseGases.X n → ℂ := fun x =>
      ∫ u in Submission.BoseGases.acube ℓ,
        (∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ)
            else ((lowKer fc κ (u - x j + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
          * ((ψ (Function.update x j u) : ℝ) : ℂ) with hJ2def
  set J2' : Submission.BoseGases.X n → ℂ := fun x =>
      ∫ u in Submission.BoseGases.acube ℓ,
        (((Work.BoseBoxFock.Ksfr v fc μ N (u - x j) + 1) / ((ℓ : ℂ) ^ 3))
            - ((lowKer fc κ (u - x j) : ℝ) : ℂ))
          * ((ψ (Function.update x j u) : ℝ) : ℂ) with hJ2'def
  -- the state `ψ = Q_j P_i Θ`
  have hPabs : ∀ x : Submission.BoseGases.X n, |Submission.BoseGases.aP ℓ i Θ x| ≤ Cθ :=
    fun x => Work.BoseBoxFock.Weak.aP_abs_le hℓpos i hCθ0 hCθ x
  have hψabs : ∀ y : Submission.BoseGases.X n, |ψ y| ≤ 2 * Cθ := by
    intro y
    rw [hψdef]
    exact Work.BoseBoxFock.Weak.aQ_abs_le hℓpos j hCθ0 hPabs y
  have hψm : Measurable ψ := by
    rw [hψdef]
    exact Work.BoseBoxFock.Weak.aQ_measurable j (Work.BoseBoxFock.Weak.aP_measurable i hΘm)
  have hψb : ∃ C : ℝ, ∀ y : Submission.BoseGases.X n, ‖ψ y‖ ≤ C :=
    ⟨2 * Cθ, fun y => by rw [Real.norm_eq_abs]; exact hψabs y⟩
  -- the `G`-facts
  set Kw : ℝ := ∑ k : Work.BoseBoxFock.Lab N,
      |Work.BoseBoxFock.W1h v h μ fu N k * Work.BoseBoxFock.hatChih v μ N k| with hKwdef
  have hKw0 : 0 ≤ Kw := by rw [hKwdef]; exact Finset.sum_nonneg fun k _ => abs_nonneg _
  set Ks : ℝ := ∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab N),
      |Work.BoseBoxFock.fLh v fc μ N s| with hKsdef
  have hKs0 : 0 ≤ Ks := by rw [hKsdef]; exact Finset.sum_nonneg fun s _ => abs_nonneg _
  set CG : ℝ := Cθ * (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ * Kw with hCGdef
  have hCG0 : 0 ≤ CG := by
    rw [hCGdef]
    exact mul_nonneg (mul_nonneg hCθ0 (inv_nonneg.mpr (Real.sqrt_nonneg _))) hKw0
  have hGm : Measurable G := by
    rw [hGdef]
    have h1 : Measurable fun x : Submission.BoseGases.X n => ((Θ x : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp hΘm
    have h3 : Measurable fun x : Submission.BoseGases.X n =>
        ((Work.BoseK15.corpusBox.chiLam ℓ (x j) : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp
        (((Work.BoseB4.BoxData.chiLam_cont _ _).measurable).comp (measurable_pi_apply j))
    have h4 : Measurable fun x : Submission.BoseGases.X n =>
        Work.BoseBoxFock.PCFU.KχfrU v h μ fu N (x j) :=
      (measurable_KχfrU v h μ fu N).comp (measurable_pi_apply j)
    exact (h1.mul h3).mul h4
  have hGb : ∀ x : Submission.BoseGases.X n, ‖G x‖ ≤ CG := by
    intro x
    have hA : ‖((Θ x : ℝ) : ℂ)‖ ≤ Cθ := by
      rw [show ‖((Θ x : ℝ) : ℂ)‖ = |Θ x| from by simp]
      exact hCθ x
    have hC : (0 : ℝ) ≤ (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ :=
      inv_nonneg.mpr (Real.sqrt_nonneg _)
    rw [hCGdef, hGdef, hKwdef]
    rw [show ‖((Θ x : ℝ) : ℂ)
          * ((Work.BoseK15.corpusBox.chiLam ℓ (x j) : ℝ) : ℂ)
          * Work.BoseBoxFock.PCFU.KχfrU v h μ fu N (x j)‖
        = ‖((Θ x : ℝ) : ℂ)‖
          * ‖((Work.BoseK15.corpusBox.chiLam ℓ (x j) : ℝ) : ℂ)‖
          * ‖Work.BoseBoxFock.PCFU.KχfrU v h μ fu N (x j)‖ from by
      rw [norm_mul, norm_mul]]
    exact mul_le_mul
      (mul_le_mul hA (norm_chiLam_le ℓ (x j)) (norm_nonneg _) hCθ0)
      (norm_KχfrU_le v h μ fu N (x j)) (norm_nonneg _)
      (mul_nonneg hCθ0 hC)
  have hGs : Function.support G ⊆ Submission.BoseGases.abox n ℓ := by
    intro x hx
    apply hΘs'
    intro h0
    exact hx (by rw [hGdef]; simp [h0])
  -- bounds on the two pieces of the inner integral
  obtain ⟨-, Cnlk, hCnlk0, hCnlkAbs⟩ := lowKer_regular fc hκpos
  have hCψ0 : 0 ≤ 2 * Cθ := by linarith
  have hJ1b : ∀ x : Submission.BoseGases.X n, ‖J1 x‖ ≤ Cnlk * (2 * Cθ) * ℓ ^ 3 := by
    intro x
    rw [hJ1def]
    haveI : IsFiniteMeasure ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) :=
      MeasureTheory.isFiniteMeasure_restrict.mpr
        (ne_of_lt (Submission.BoseGases.acube_lt_top ℓ hℓpos.le))
    have hbd : ∀ᵐ u ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)),
        ‖((lowKer fc κ (x j - u) : ℝ) : ℂ) * ((ψ (Function.update x j u) : ℝ) : ℂ)‖
          ≤ Cnlk * (2 * Cθ) := by
      filter_upwards with u
      rw [norm_mul, complexNorm_ofReal_bcs, complexNorm_ofReal_bcs]
      exact mul_le_mul (hCnlkAbs _) (hψabs _) (abs_nonneg _) hCnlk0
    have hfin := MeasureTheory.norm_integral_le_of_norm_le_const
      (μ := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) hbd
    rw [Submission.BoseGases.real_volume_acube ℓ hℓpos.le] at hfin
    exact hfin
  have hImgb : ∀ z : E3,
      ‖(Work.BoseBoxFock.Ksfr v fc μ N z + 1) / ((ℓ : ℂ) ^ 3)‖ ≤ (Ks + 1) / ℓ ^ 3 := by
    intro z
    have h1 := KsfrImg_norm_le_bcs (v := v) (fc := fc) (μ := μ) (N := N) (C := Ks) hℓpos
      (fun y => by rw [hKsdef]; exact norm_Ksfr_le y) z
    rwa [hℓdef]
  have hJ2b : ∀ x : Submission.BoseGases.X n,
      ‖J2' x‖ ≤ ((Ks + 1) / ℓ ^ 3 + Cnlk) * (2 * Cθ) * ℓ ^ 3 := by
    intro x
    rw [hJ2'def]
    haveI : IsFiniteMeasure ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) :=
      MeasureTheory.isFiniteMeasure_restrict.mpr
        (ne_of_lt (Submission.BoseGases.acube_lt_top ℓ hℓpos.le))
    have hbd : ∀ᵐ u ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)),
        ‖(((Work.BoseBoxFock.Ksfr v fc μ N (u - x j) + 1) / ((ℓ : ℂ) ^ 3))
            - ((lowKer fc κ (u - x j) : ℝ) : ℂ)) * ((ψ (Function.update x j u) : ℝ) : ℂ)‖
          ≤ ((Ks + 1) / ℓ ^ 3 + Cnlk) * (2 * Cθ) := by
      filter_upwards with u
      rw [norm_mul, complexNorm_ofReal_bcs]
      refine mul_le_mul ?_ (hψabs _) (abs_nonneg _)
        (add_nonneg (div_nonneg (by linarith) (by positivity)) hCnlk0)
      calc ‖(Work.BoseBoxFock.Ksfr v fc μ N (u - x j) + 1) / ((ℓ : ℂ) ^ 3)
              - ((lowKer fc κ (u - x j) : ℝ) : ℂ)‖
          ≤ ‖(Work.BoseBoxFock.Ksfr v fc μ N (u - x j) + 1) / ((ℓ : ℂ) ^ 3)‖
              + ‖((lowKer fc κ (u - x j) : ℝ) : ℂ)‖ := norm_sub_le _ _
        _ ≤ (Ks + 1) / ℓ ^ 3 + Cnlk :=
            add_le_add (hImgb _) (by rw [complexNorm_ofReal_bcs]; exact hCnlkAbs _)
    have hfin := MeasureTheory.norm_integral_le_of_norm_le_const
      (μ := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) hbd
    rw [Submission.BoseGases.real_volume_acube ℓ hℓpos.le] at hfin
    exact hfin
  -- the pointwise split of the image sum
  have hsplit : ∀ x : Submission.BoseGases.X n, J x = J1 x + J2 x := by
    intro x
    rw [hJdef, hJ1def, hJ2def]
    exact int_imageSum_eq_lowKer_add (fc := fc) (κ := κ) (ℓ := ℓ) hκpos hℓpos (n := n) j ψ
      hψm hψb x
  -- the `d = 0` piece is the word factor `lowSlot`
  have hJ1pt : ∀ x : Submission.BoseGases.X n, J1 x = ((L1 x : ℝ) : ℂ) := by
    intro x
    have hfib_m : AEStronglyMeasurable (fun z : E3 => ψ (Function.update x j z)) volume :=
      (hψm.comp (by fun_prop : Measurable (fun z : E3 => Function.update x j z))).aestronglyMeasurable
    have hfib_b : ∀ z ∈ Submission.BoseGases.acube ℓ, |ψ (Function.update x j z)| ≤ 2 * Cθ :=
      fun z _ => hψabs _
    have hL := lowSlot_eq_lowKer (fc := fc) (κ := κ) (ℓ := ℓ) (Ψ := ψ) hκpos hℓpos (n := n) j x
      hfib_m hfib_b hCψ0
    rw [hJ1def]
    simp only [hL1def]
    rw [hL]
    rw [show (∫ u in Submission.BoseGases.acube ℓ,
          ((lowKer fc κ (x j - u) : ℝ) : ℂ) * ((ψ (Function.update x j u) : ℝ) : ℂ))
        = ∫ u in Submission.BoseGases.acube ℓ,
            (((lowKer fc κ (x j - u) * ψ (Function.update x j u) : ℝ)) : ℂ) from by
      refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
        (fun u _ => ?_)
      rw [Complex.ofReal_mul]]
    rw [show (∫ u in Submission.BoseGases.acube ℓ,
          ((lowKer fc κ (x j - u) * ψ (Function.update x j u) : ℝ) : ℂ))
        = ((∫ u in Submission.BoseGases.acube ℓ,
            lowKer fc κ (x j - u) * ψ (Function.update x j u) : ℝ) : ℂ) from
      integral_ofReal]
    congr 1
    rw [show (∫ u in Submission.BoseGases.acube ℓ,
          lowKer fc κ (x j - u) * ψ (Function.update x j u))
        = ∫ u : E3, (Submission.BoseGases.acube ℓ).indicator
            (fun u => lowKer fc κ (x j - u) * ψ (Function.update x j u)) u from
      (MeasureTheory.integral_indicator (μ := (volume : Measure E3))
        (Submission.BoseGases.acube_measurable ℓ)).symm]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    by_cases hu : u ∈ Submission.BoseGases.acube ℓ
    · simp only [Set.indicator_of_mem hu]
    · simp only [Set.indicator_of_notMem hu, mul_zero]
  -- the `d ≠ 0` piece is the shifted frame form
  have hJ2pt : ∀ x : Submission.BoseGases.X n, J2 x = J2' x := by
    intro x
    rw [hJ2def, hJ2'def]
    refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
      (fun u _ => ?_)
    rw [tail_eq_lowKer_bcs (v := v) (fc := fc) (μ := μ) (N := N) hℓ hκ hN (u - x j)]
  -- integrability of the two pieces, against the weight `G`
  have hJ1int : Integrable (fun x : Submission.BoseGases.X n => G x * J1 x)
      (volume : Measure (Submission.BoseGases.X n)) := by
    have hK1m : Measurable (fun p : Submission.BoseGases.X n × E3 =>
        ((lowKer fc κ (p.1 j - p.2) : ℝ) : ℂ)) :=
      Complex.measurable_ofReal.comp (((lowKer_regular fc hκpos).1.measurable).comp
        (by fun_prop : Measurable (fun p : Submission.BoseGases.X n × E3 => p.1 j - p.2)))
    have hψ2m : Measurable (fun p : Submission.BoseGases.X n × E3 =>
        ((ψ (Function.update p.1 j p.2) : ℝ) : ℂ)) :=
      Complex.measurable_ofReal.comp (hψm.comp
        (by fun_prop : Measurable (fun p : Submission.BoseGases.X n × E3 =>
          Function.update p.1 j p.2)))
    have hjoint : Measurable (fun p : Submission.BoseGases.X n × E3 =>
        G p.1 * (((lowKer fc κ (p.1 j - p.2) : ℝ) : ℂ)
          * ((ψ (Function.update p.1 j p.2) : ℝ) : ℂ))) :=
      (hGm.comp measurable_fst).mul (hK1m.mul hψ2m)
    have hSm : StronglyMeasurable (fun x : Submission.BoseGases.X n =>
        ∫ u : E3, G x * (((lowKer fc κ (x j - u) : ℝ) : ℂ)
            * ((ψ (Function.update x j u) : ℝ) : ℂ))
          ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))) :=
      hjoint.stronglyMeasurable.integral_prod_right'
        (ν := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))
    have hfs : (fun x : Submission.BoseGases.X n =>
        ∫ u : E3, G x * (((lowKer fc κ (x j - u) : ℝ) : ℂ)
            * ((ψ (Function.update x j u) : ℝ) : ℂ))
          ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)))
        = fun x : Submission.BoseGases.X n => G x * J1 x := by
      funext x
      rw [hJ1def, MeasureTheory.integral_const_mul]
    rw [hfs] at hSm
    refine integrable_of_bounded_support_bcs (s := Submission.BoseGases.abox n ℓ)
      (Submission.BoseGases.abox_lt_top n ℓ hℓpos.le) hSm.measurable ?_ ?_
    · exact ⟨CG * (Cnlk * (2 * Cθ) * ℓ ^ 3), fun x => by
        rw [norm_mul]
        exact mul_le_mul (hGb x) (hJ1b x) (norm_nonneg _) hCG0⟩
    · intro x hx
      rw [Function.mem_support] at hx
      exact hGs (Function.mem_support.mpr (fun h0 => hx (by rw [h0, zero_mul])))
  have hJ2int : Integrable (fun x : Submission.BoseGases.X n => G x * J2' x)
      (volume : Measure (Submission.BoseGases.X n)) := by
    have hKm : Measurable (fun p : Submission.BoseGases.X n × E3 =>
        (Work.BoseBoxFock.Ksfr v fc μ N (p.2 - p.1 j) + 1) / ((ℓ : ℂ) ^ 3)) :=
      (((continuous_Ksfr.comp (by fun_prop : Continuous (fun p : Submission.BoseGases.X n × E3 =>
          p.2 - p.1 j))).add continuous_const).measurable).div_const _
    have hK1m : Measurable (fun p : Submission.BoseGases.X n × E3 =>
        ((lowKer fc κ (p.2 - p.1 j) : ℝ) : ℂ)) :=
      Complex.measurable_ofReal.comp (((lowKer_regular fc hκpos).1.measurable).comp
        (by fun_prop : Measurable (fun p : Submission.BoseGases.X n × E3 => p.2 - p.1 j)))
    have hψ2m : Measurable (fun p : Submission.BoseGases.X n × E3 =>
        ((ψ (Function.update p.1 j p.2) : ℝ) : ℂ)) :=
      Complex.measurable_ofReal.comp (hψm.comp
        (by fun_prop : Measurable (fun p : Submission.BoseGases.X n × E3 =>
          Function.update p.1 j p.2)))
    have hjoint : Measurable (fun p : Submission.BoseGases.X n × E3 =>
        G p.1 * ((((Work.BoseBoxFock.Ksfr v fc μ N (p.2 - p.1 j) + 1) / ((ℓ : ℂ) ^ 3))
            - ((lowKer fc κ (p.2 - p.1 j) : ℝ) : ℂ))
          * ((ψ (Function.update p.1 j p.2) : ℝ) : ℂ))) :=
      (hGm.comp measurable_fst).mul ((hKm.sub hK1m).mul hψ2m)
    have hSm : StronglyMeasurable (fun x : Submission.BoseGases.X n =>
        ∫ u : E3, G x * ((((Work.BoseBoxFock.Ksfr v fc μ N (u - x j) + 1) / ((ℓ : ℂ) ^ 3))
            - ((lowKer fc κ (u - x j) : ℝ) : ℂ))
          * ((ψ (Function.update x j u) : ℝ) : ℂ))
          ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))) :=
      hjoint.stronglyMeasurable.integral_prod_right'
        (ν := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))
    have hfs : (fun x : Submission.BoseGases.X n =>
        ∫ u : E3, G x * ((((Work.BoseBoxFock.Ksfr v fc μ N (u - x j) + 1) / ((ℓ : ℂ) ^ 3))
            - ((lowKer fc κ (u - x j) : ℝ) : ℂ))
          * ((ψ (Function.update x j u) : ℝ) : ℂ))
          ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)))
        = fun x : Submission.BoseGases.X n => G x * J2' x := by
      funext x
      rw [hJ2'def, MeasureTheory.integral_const_mul]
    rw [hfs] at hSm
    refine integrable_of_bounded_support_bcs (s := Submission.BoseGases.abox n ℓ)
      (Submission.BoseGases.abox_lt_top n ℓ hℓpos.le) hSm.measurable ?_ ?_
    · exact ⟨CG * (((Ks + 1) / ℓ ^ 3 + Cnlk) * (2 * Cθ) * ℓ ^ 3), fun x => by
        rw [norm_mul]
        exact mul_le_mul (hGb x) (hJ2b x) (norm_nonneg _) hCG0⟩
    · intro x hx
      rw [Function.mem_support] at hx
      exact hGs (Function.mem_support.mpr (fun h0 => hx (by rw [h0, zero_mul])))
  have hint1 : Integrable (fun x : Submission.BoseGases.X n => G x * ((L1 x : ℝ) : ℂ))
      (volume : Measure (Submission.BoseGases.X n)) :=
    hJ1int.congr (Filter.Eventually.of_forall fun x => by
      show G x * J1 x = G x * ((L1 x : ℝ) : ℂ); rw [hJ1pt x])
  have hint2 : Integrable (fun x : Submission.BoseGases.X n => G x * J2 x)
      (volume : Measure (Submission.BoseGases.X n)) :=
    hJ2int.congr (Filter.Eventually.of_forall fun x => by
      show G x * J2' x = G x * J2 x; rw [hJ2pt x])
  have hkey : (∫ x : Submission.BoseGases.X n, G x * J x)
      = (∫ x : Submission.BoseGases.X n, G x * ((L1 x : ℝ) : ℂ))
        + ∫ x : Submission.BoseGases.X n, G x * J2 x := by
    have hpt : ∀ x : Submission.BoseGases.X n,
        G x * J x = G x * ((L1 x : ℝ) : ℂ) + G x * J2 x := by
      intro x
      rw [hsplit x, hJ1pt x]
      ring
    rw [show (∫ x : Submission.BoseGases.X n, G x * J x)
        = ∫ x : Submission.BoseGases.X n, (G x * ((L1 x : ℝ) : ℂ) + G x * J2 x) from
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
    exact MeasureTheory.integral_add hint1 hint2
  have hB := Bchan_eq_imageSum hij v h fc fu μ N hℓ hκ hN Θ hΘ hΘm ⟨Cθ, hCθ⟩ hΘs
  calc (∫ q : Submission.BoseGases.X n
          × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)),
        ((Θ q.1 : ℝ) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (q.1 i)
          * Work.BoseBoxFock.PCFU.ChBU v h fc fu μ N q.2.1 (q.1 j) q.2.2
          * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ))
      = ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 6
          * (∫ x : Submission.BoseGases.X n, G x * J x) := hB
    _ = ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 6
          * ((∫ x : Submission.BoseGases.X n, G x * ((L1 x : ℝ) : ℂ))
              + ∫ x : Submission.BoseGases.X n, G x * J2 x) := by rw [hkey]
    _ = ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 6
          * (∫ x : Submission.BoseGases.X n, G x * ((L1 x : ℝ) : ℂ))
        + ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 6
          * (∫ x : Submission.BoseGases.X n, G x * J2 x) := by ring
    _ = ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 6
          * (∫ x : Submission.BoseGases.X n,
              ((Θ x : ℝ) : ℂ)
                * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x j) : ℝ) : ℂ)
                * Work.BoseBoxFock.PCFU.KχfrU v h μ fu N (x j)
                * ((Work.BoseBoxFix.lowSlot fc
                      (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
                      (Work.BoseBoxFock.ellH v μ) j
                      (Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                        (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ)) x : ℝ) : ℂ))
        + ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 6
          * (∫ x : Submission.BoseGases.X n,
              ((Θ x : ℝ) : ℂ)
                * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x j) : ℝ) : ℂ)
                * Work.BoseBoxFock.PCFU.KχfrU v h μ fu N (x j)
                * (∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
                    (∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ)
                        else ((Work.BoseBoxFock.PCFU.lowKer fc
                          (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                            * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
                          (u - x j + Work.BoseBoxFock.ellH v μ
                            • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
                      * ((Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                          (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ)
                          (Function.update x j u) : ℝ) : ℂ))) := by
        simp only [hGdef, hL1def, hJ2def, hψdef, hℓdef, hκdef]

end Work.BoseBoxFock.PCFU
