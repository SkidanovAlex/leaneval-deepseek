/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.Lemma38Step5

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# GLYZ §3.4: the ξ'-UNIFORM constants of the lane, and the lane at a fixed enlargement

`Lemma38Step5.exists_asymAV_le_proj` produces its plate enlargement `Λ₀` by `Classical.choose`, so
the enlargement is opaque and — worse — *ξ'-dependent*, while the degree-`l` model hypothesis (the
induction hypothesis of the outer induction on the degree) can only be supplied at a *fixed*
enlargement.  This module removes that obstruction by re-proving the geometric ingredients with the
quantifier over `ξ'` *inside* the existential, so that a single witness serves every `ξ' ∈ [0,1]`.

The uniform versions (all proved here; each is the corresponding `Projection`/`AsymFine`/
`CurveDecLocStep`/`Lemma38Step5` lemma with the `obtain` hoisted above the `∀ ξ'`):

* `torsion_projCurveDeriv_uniform` — the torsion lower bound of the projected curve;
* `CurveTaylor_projCurveDeriv_uniform` — its Taylor remainder;
* `projMapLin_image_plate_subset_uniform` — GLYZ's `P(U_J) ⊆ C·U_{J,P∘Γ}`;
* `exists_isFourierRep_restrict_translate_uniform` — the class transport of a block sum to `H + z`;
* `exists_isFourierRep_subBlk_intervalCurve_uniform` — its reparametrised form;
* `projConstants_uniform` — the pair `(cL, R)` of §3.4;
* `exists_class_subBlk_uniform` — the class of the re-parametrised sub-block sums at the translate.

The global constants extracted from them (`projCL`, `projRR`, `classCB`) then give

* `laneLam k l hk hl hlk` — the fixed plate enlargement of the lane (dominant over
  `lamProj l k (projCL …)` and `8 · classCB …`);
* `laneEnl k l hk hl hlk` — the fixed model enlargement the lane needs,
  `towerEnlP l (projCL …) (projRR …) (2 · laneLam …)`;
* `laneK k l hk hl hlk` — the level gap above which `2 · laneLam ≤ 2^(M−m)`;
* **`asymAV_le_proj_explicit`** — lane 4 with both discharges at the *fixed* enlargement `laneLam`
  and the model hypothesis at the *fixed* enlargement `laneEnl`.
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Submission.Vinogradov


/-- **The torsion of the projected curve, uniformly in `ξ'`.** -/
theorem torsion_projCurveDeriv_uniform (k l : ℕ) (hl : 1 ≤ l) (hlk : l ≤ k) :
    ∃ c : ℝ, 0 < c ∧ ∀ ξ' ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      1 / 4 ≤ |t - ξ'| →
      c ≤ (Matrix.gram ℝ
        (fun j : Fin l => projCurveDeriv k l (torsionVec k l hlk ξ') (j.val + 1) t)).det := by
  obtain ⟨c, hc, h⟩ :=
    Commons.Analysis.MomentCurve.projected_torsion_det_orthogonal k l hl hlk
  refine ⟨c, hc, ?_⟩
  intro ξ' hξ' t ht hsep
  have hgram := gram_projMapLin_eq_gram_starProjection
    (orthonormal_torsionVec k l hlk ξ') (span_torsionVec k l hlk ξ')
    (fun j : Fin l => gammaDeriv k (j.val + 1) t)
  simp only [projCurveDeriv]
  rw [hgram]
  have hV : Submodule.span ℝ (Set.range (fun i : Fin (k - l) =>
      (WithLp.equiv 2 (Fin k → ℝ)).symm (Commons.Analysis.MomentCurve.gam k ξ' (i.val + 1))))
      = torsionSpan k l ξ' := by
    rw [torsionSpan]
    congr 1
  have hmain := h ξ' t hξ'.1 hξ'.2 ht.1 ht.2 (by rwa [abs_sub_comm] at hsep)
  rw [hV] at hmain
  have harg : ∀ j : Fin l, (WithLp.equiv 2 (Fin k → ℝ)).symm
      (Commons.Analysis.MomentCurve.gam k t (j.val + 1)) = gammaDeriv k (j.val + 1) t :=
    fun j => (gammaDeriv_eq_lpSymm_gam k (j.val + 1) t).symm
  simpa only [torsionCompl, harg] using hmain

/-- **The Taylor remainder of the projected curve, uniformly in `ξ'`.** -/
theorem CurveTaylor_projCurveDeriv_uniform (k l : ℕ) (hl : 1 ≤ l) (hlk : l ≤ k) :
    ∃ R : ℝ, 0 < R ∧ ∀ ξ' ∈ Set.Icc (0 : ℝ) 1,
      CurveTaylor l (projCurveDeriv k l (torsionVec k l hlk ξ')) R := by
  obtain ⟨C, hC, htail⟩ := Commons.Analysis.MomentCurve.gammaDeriv_taylor_tail k
  have hk1 : 1 ≤ k := le_trans hl hlk
  have hkpos : 0 < Real.sqrt k := Real.sqrt_pos.mpr (by exact_mod_cast hk1)
  refine ⟨Real.sqrt k * C, mul_pos hkpos hC, ?_⟩
  intro ξ' hξ' i m t u him hml ht hu
  set b : Fin l → E k := torsionVec k l hlk ξ' with hbdef
  have hb : Orthonormal ℝ b := orthonormal_torsionVec k l hlk ξ'
  set w : E k := (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm
      (Commons.Analysis.MomentCurve.gam k (t + u) i
        - ∑ j ∈ Finset.Icc i m, (u ^ (j - i) / ((j - i).factorial : ℝ))
            • Commons.Analysis.MomentCurve.gam k t j) with hw
  have hterm : ∀ (j : ℕ) (s : ℝ), projCurveDeriv k l b j s
      = projMapLin k l b ((WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm
          (Commons.Analysis.MomentCurve.gam k s j)) := fun j s => projCurveDeriv_eq_lpSymm k l b j s
  have hsum : (∑ j ∈ Finset.Icc i m, (u ^ (j - i) / ((j - i).factorial : ℝ))
        • projCurveDeriv k l b j t)
      = projMapLin k l b (∑ j ∈ Finset.Icc i m, (u ^ (j - i) / ((j - i).factorial : ℝ))
          • (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm
              (Commons.Analysis.MomentCurve.gam k t j)) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, hterm j t]
  have hsub : projCurveDeriv k l b i (t + u)
        - ∑ j ∈ Finset.Icc i m, (u ^ (j - i) / ((j - i).factorial : ℝ))
            • projCurveDeriv k l b j t
      = projMapLin k l b w := by
    rw [hterm i (t + u), hsum, ← map_sub]
    congr 1
    have hsum' : (∑ j ∈ Finset.Icc i m, (u ^ (j - i) / ((j - i).factorial : ℝ))
          • (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm
              (Commons.Analysis.MomentCurve.gam k t j))
        = (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm
            (∑ j ∈ Finset.Icc i m, (u ^ (j - i) / ((j - i).factorial : ℝ))
              • Commons.Analysis.MomentCurve.gam k t j) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [map_smul]
    rw [hsum', ← map_sub, hw]
  rw [hsub]
  refine (norm_projMapLin_le k l hb w).trans ?_
  have hwn : ‖w‖ ≤ Real.sqrt k * ‖Commons.Analysis.MomentCurve.gam k (t + u) i
      - ∑ j ∈ Finset.Icc i m, (u ^ (j - i) / ((j - i).factorial : ℝ))
          • Commons.Analysis.MomentCurve.gam k t j‖ := by
    rw [hw]
    exact norm_lpSymm_le k _
  refine hwn.trans ?_
  calc Real.sqrt k * ‖Commons.Analysis.MomentCurve.gam k (t + u) i
        - ∑ j ∈ Finset.Icc i m, (u ^ (j - i) / ((j - i).factorial : ℝ))
            • Commons.Analysis.MomentCurve.gam k t j‖
      ≤ Real.sqrt k * (C * |u| ^ (m + 1 - i)) :=
        mul_le_mul_of_nonneg_left
          (htail i m t u him (le_trans hml hlk) (by rw [abs_of_nonneg ht.1]; exact ht.2) hu)
          (Real.sqrt_nonneg k)
    _ = Real.sqrt k * C * |u| ^ (m + 1 - i) := by ring



/-- **The plate inclusion, uniformly in `ξ'`.** -/
theorem projMapLin_image_plate_subset_uniform (k l : ℕ) (hl : 1 ≤ l) (hlk : l ≤ k) :
    ∃ lam : ℝ, 1 ≤ lam ∧ ∀ ξ' ∈ Set.Icc (0 : ℝ) 1, ∀ (δ t : ℝ), 0 < δ → δ ≤ 1 →
      t ∈ Set.Icc (0 : ℝ) 1 → 1 / 4 ≤ |t - ξ'| →
      projMapLin k l (torsionVec k l hlk ξ') '' plate k δ t
        ⊆ curvePlate l (projCurveDeriv k l (torsionVec k l hlk ξ')) (lam * δ) t := by
  obtain ⟨c, hc, htor⟩ := torsion_projCurveDeriv_uniform k l hl hlk
  set c' : ℝ := c / ((l : ℝ) * ((l - 1).factorial : ℝ)
    * (Real.sqrt l * (Real.sqrt k * (k.factorial : ℝ))) ^ (2 * l - 1) * Real.sqrt l) with hc'def
  have hfact : (0 : ℝ) < ((l - 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (l - 1)
  have hsqrtl1 : 1 ≤ Real.sqrt l := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast hl)
  have hsqrtlpos : 0 < Real.sqrt l := lt_of_lt_of_le zero_lt_one hsqrtl1
  have hA1 : 1 ≤ Real.sqrt k * (k.factorial : ℝ) := by
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (le_trans hl hlk)
    have h1 : 1 ≤ Real.sqrt k := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hk1
    have h2 : 1 ≤ (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ Real.sqrt k * (k.factorial : ℝ) := mul_le_mul h1 h2 zero_le_one (by positivity)
  have hKpos : 0 < (l : ℝ) * ((l - 1).factorial : ℝ)
      * (Real.sqrt l * (Real.sqrt k * (k.factorial : ℝ))) ^ (2 * l - 1) * Real.sqrt l := by
    refine mul_pos (mul_pos (mul_pos ?_ hfact) ?_) hsqrtlpos
    · exact_mod_cast hl
    · have hA2 : 1 ≤ Real.sqrt l * (Real.sqrt k * (k.factorial : ℝ)) := by
        calc (1 : ℝ) = 1 * 1 := by ring
          _ ≤ Real.sqrt l * (Real.sqrt k * (k.factorial : ℝ)) :=
              mul_le_mul hsqrtl1 hA1 zero_le_one (Real.sqrt_nonneg l)
      exact pow_pos (lt_of_lt_of_le zero_lt_one hA2) _
  have hc'pos : 0 < c' := by rw [hc'def]; exact div_pos hc hKpos
  refine ⟨1 + ((k : ℝ) * (Real.sqrt k * (k.factorial : ℝ)) + 1) / c', by
    have h0 : (0 : ℝ) ≤ ((k : ℝ) * (Real.sqrt k * (k.factorial : ℝ)) + 1) / c' :=
      div_nonneg (by positivity) hc'pos.le
    linarith, ?_⟩
  intro ξ' hξ' δ t hδ0 hδ1 ht hsep
  have hbd : ∀ i : ℕ, i ≤ l + 1 → ∀ j : Fin l,
      |projCurveDeriv k l (torsionVec k l hlk ξ') i t j| ≤ Real.sqrt k * (k.factorial : ℝ) :=
    fun i hi j => CurveBounded_projCurveDeriv k l hlk (orthonormal_torsionVec k l hlk ξ') i hi t ht j
  have hball := ball_subset_curvePlate_of_bounded_torsion_at (D := projCurveDeriv k l
      (torsionVec k l hlk ξ')) (A := Real.sqrt k * (k.factorial : ℝ)) (c := c) (t := t)
    hl hc hA1 hbd (htor ξ' hξ' t ht hsep)
  have hsub := projMapLin_image_plate_subset hl hlk (orthonormal_torsionVec k l hlk ξ')
    ht hc'pos hball hδ0 hδ1
  refine hsub.trans (curvePlate_mono (δ := (1 + ((k : ℝ) * (Real.sqrt k * (k.factorial : ℝ)) + 1) / c')
    * δ) (mul_nonneg (by
      have h0 : (0 : ℝ) ≤ ((k : ℝ) * (Real.sqrt k * (k.factorial : ℝ)) + 1) / c' :=
        div_nonneg (by positivity) hc'pos.le
      linarith) hδ0.le) le_rfl)

/-- **The class transport, uniformly in `ξ'`.** -/
theorem exists_isFourierRep_restrict_translate_uniform (k l : ℕ) (hk : 1 ≤ k) (hl : 1 ≤ l)
    (hlk : l ≤ k) :
    ∃ lam : ℝ, 1 ≤ lam ∧ ∀ ξ' ∈ Set.Icc (0 : ℝ) 1, ∀ {N b' : ℕ}, 2 ≤ b' → b' ≤ N →
      ∀ (J : Fin (2 ^ b')) (z : E k) (f : Fin (2 ^ N) → E k → ℂ),
      (∀ i, IsFourierRep k (piecePlate k (2 ^ N) i) (f i)) →
      1 / 4 ≤ |pieceCenter (2 ^ b') J - ξ'| →
      IsFourierRep l
        (curvePlate l (projCurveDeriv k l (torsionVec k l hlk ξ'))
          (lam * (8 * plateHalf b')) (pieceCenter (2 ^ b') J))
        (fun y => ∑ i ∈ blkFin N b' J,
          f i (projEmbedLin k l (torsionVec k l hlk ξ') y + z)) := by
  obtain ⟨lam, hlam, hlam'⟩ := projMapLin_image_plate_subset_uniform k l hl hlk
  refine ⟨lam, hlam, ?_⟩
  intro ξ' hξ' N b' hb' hb'N J z f hf hsep
  have hblk := isFourierRep_sum_blkFin hk hb' hb'N J f hf
  have hiso := isFourierRep_proj_map k l (torsionVec k l hlk ξ') z hblk
  refine hiso.mono ?_
  intro ξ hξ
  exact hlam' ξ' hξ' (8 * plateHalf b') (pieceCenter (2 ^ b') J)
    (mul_pos (by norm_num) (plateHalf_pos b'))
    (plateHalf_two_le_one hb')
    (pieceCenter_mem_Icc (2 ^ b') Nat.one_le_two_pow J)
    hsep hξ

/-- **The class transport for the reparametrised sub-blocks, uniformly in `ξ'`.** -/
theorem exists_isFourierRep_subBlk_intervalCurve_uniform (k l : ℕ) (hk : 1 ≤ k) (hl : 1 ≤ l)
    (hlk : l ≤ k) :
    ∃ lam : ℝ, 1 ≤ lam ∧ ∀ ξ' ∈ Set.Icc (0 : ℝ) 1, ∀ {N m M : ℕ} (h2m : 2 ≤ m) (hmM : m ≤ M)
      (hMN : M ≤ N) (q : Fin (2 ^ m))
      (hsep : ∀ j : Fin (2 ^ (M - m)),
        1 / 4 ≤ |pieceCenter (2 ^ M) (subIdx m M hmM q j) - ξ'|)
      (z : E k) (f : Fin (2 ^ N) → E k → ℂ),
      (∀ i, IsFourierRep k (piecePlate k (2 ^ N) i) (f i)) →
      ∀ j : Fin (2 ^ (M - m)),
        IsFourierRep l
          (curvePlate l
            (intervalCurve l (((q : ℕ) : ℝ) / (2 : ℝ) ^ m) (1 / (2 : ℝ) ^ m)
              (projCurveDeriv k l (torsionVec k l hlk ξ')))
            (lam * (8 * plateHalf M) * (2 : ℝ) ^ m) (pieceCenter (2 ^ (M - m)) j))
          (fun y => ∑ i ∈ blkFin N M (subIdx m M hmM q j),
              f i (projEmbedLin k l (torsionVec k l hlk ξ') y + z)) := by
  obtain ⟨lam, hlam, hlam'⟩ := exists_isFourierRep_restrict_translate_uniform k l hk hl hlk
  refine ⟨lam, hlam, ?_⟩
  intro ξ' hξ' N m M h2m hmM hMN q hsep z f hf j
  have hM2 : 2 ≤ M := le_trans h2m hmM
  have hblk := hlam' ξ' hξ' hM2 hMN (subIdx m M hmM q j) z f hf (hsep j)
  have hδ : (1 / (2 : ℝ) ^ m) * (lam * (8 * plateHalf M) * (2 : ℝ) ^ m)
      = lam * (8 * plateHalf M) := by
    field_simp
  have hset : curvePlate l (projCurveDeriv k l (torsionVec k l hlk ξ'))
        (lam * (8 * plateHalf M)) (pieceCenter (2 ^ M) (subIdx m M hmM q j))
      = curvePlate l
          (intervalCurve l (((q : ℕ) : ℝ) / (2 : ℝ) ^ m) (1 / (2 : ℝ) ^ m)
            (projCurveDeriv k l (torsionVec k l hlk ξ')))
          (lam * (8 * plateHalf M) * (2 : ℝ) ^ m) (pieceCenter (2 ^ (M - m)) j) := by
    rw [pieceCenter_subIdx hmM q j]
    rw [curvePlate_intervalCurve, hδ]
  rw [← hset]
  exact hblk


/-- **The geometric constants of the projected curve, uniformly in `ξ'`.** -/
theorem projConstants_uniform (k l : ℕ) (hl : 1 ≤ l) (hlk : l ≤ k) :
    ∃ cL : ℝ, 0 < cL ∧ ∃ R : ℝ, 0 < R ∧ ∀ ξ' ∈ Set.Icc (0 : ℝ) 1,
      (∀ t ∈ Set.Icc (0 : ℝ) 1, 1 / 4 ≤ |t - ξ'| →
        PlateLowerAt l (projCurveDeriv k l (torsionVec k l hlk ξ')) cL t) ∧
      CurveTaylorTop l (projCurveDeriv k l (torsionVec k l hlk ξ')) R := by
  obtain ⟨c, hc, htor⟩ := torsion_projCurveDeriv_uniform k l hl hlk
  obtain ⟨R, hR, htay⟩ := CurveTaylor_projCurveDeriv_uniform k l hl hlk
  refine ⟨c / tubeK l (Real.sqrt k * (k.factorial : ℝ)), ?_, R, hR, ?_⟩
  · refine div_pos hc (tubeK_pos hl ?_)
    exact one_le_mul_of_one_le_of_one_le
      (Real.one_le_sqrt.mpr (by exact_mod_cast le_trans hl hlk))
      (by exact_mod_cast Nat.factorial_pos k)
  · intro ξ' hξ'
    refine ⟨?_, curveTaylorTop_of_curveTaylor (htay ξ' hξ')⟩
    intro t ht hsep
    refine plateLowerAt_of_torsion (D := projCurveDeriv k l (torsionVec k l hlk ξ')) hl hc
      (one_le_mul_of_one_le_of_one_le
        (Real.one_le_sqrt.mpr (by exact_mod_cast le_trans hl hlk))
        (by exact_mod_cast Nat.factorial_pos k))
      (fun i hi j =>
        CurveBounded_projCurveDeriv k l hlk (orthonormal_torsionVec k l hlk ξ') i hi t ht j)
      (htor ξ' hξ' t ht hsep)

/-- **The class of the sub-block sums at the translate, uniformly in `ξ'`.** -/
theorem exists_class_subBlk_uniform {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k) :
    ∃ lamB : ℝ, 1 ≤ lamB ∧ ∀ ξ' ∈ Set.Icc (0 : ℝ) 1, ∀ {N m M : ℕ} (h2m : 2 ≤ m) (hmM : m ≤ M)
      (hMN : M ≤ N) (q : Fin (2 ^ m))
      (hsep : ∀ j : Fin (2 ^ (M - m)),
        1 / 4 ≤ |pieceCenter (2 ^ M) (subIdx m M hmM q j) - ξ'|)
      {lam : ℝ} (hlam8 : 8 * lamB ≤ lam)
      (u : E k) (f : Fin (2 ^ N) → E k → ℂ),
      (∀ i, IsFourierRep k (piecePlate k (2 ^ N) i) (f i)) →
      ∀ j : Fin (2 ^ (M - m)),
        IsFourierRep l
          (curvePlate l
            (intervalCurve l (((q : ℕ) : ℝ) / (2 : ℝ) ^ m) (1 / (2 : ℝ) ^ m)
              (projCurveDeriv k l (torsionVec k l hlk ξ')))
            (lam / (2 * ((2 ^ (M - m) : ℕ) : ℝ))) (pieceCenter (2 ^ (M - m)) j))
          (fun y => ∑ i ∈ blkFin N M (subIdx m M hmM q j),
            f i (u + projEmbedLin k l (torsionVec k l hlk ξ') y)) := by
  obtain ⟨lamB, hlamB1, hlamB⟩ := exists_isFourierRep_subBlk_intervalCurve_uniform k l hk hl hlk
  refine ⟨lamB, hlamB1, ?_⟩
  intro ξ' hξ' N m M h2m hmM hMN q hsep lam hlam8 u f hf j
  have h0 := hlamB ξ' hξ' h2m hmM hMN q hsep u f hf j
  have hflip : IsFourierRep l
      (curvePlate l
        (intervalCurve l (((q : ℕ) : ℝ) / (2 : ℝ) ^ m) (1 / (2 : ℝ) ^ m)
          (projCurveDeriv k l (torsionVec k l hlk ξ')))
        (lamB * (8 * plateHalf M) * (2 : ℝ) ^ m) (pieceCenter (2 ^ (M - m)) j))
      (fun y => ∑ i ∈ blkFin N M (subIdx m M hmM q j),
        f i (u + projEmbedLin k l (torsionVec k l hlk ξ') y)) :=
    IsFourierRep.congr h0 fun y => Finset.sum_congr rfl fun i _ => by rw [add_comm]
  refine IsFourierRep.mono ?_ hflip
  refine curvePlate_mono ?_ ?_
  · have hp : (0 : ℝ) ≤ 8 * plateHalf M := by
      rw [plateHalf]; positivity
    exact mul_nonneg (mul_nonneg (le_trans zero_le_one hlamB1) hp) (by positivity)
  · have hmtp : (0 : ℝ) < ((2 ^ (M - m) : ℕ) : ℝ) := by positivity
    have hph' : 8 * plateHalf M * (2 : ℝ) ^ m = 4 / ((2 ^ (M - m) : ℕ) : ℝ) := by
      have hcast : ((2 ^ (M - m) : ℕ) : ℝ) = (2 : ℝ) ^ (M - m) := by push_cast; ring
      have h2 : (2 : ℝ) ^ (M + 1) = (2 : ℝ) ^ (M - m) * (2 : ℝ) ^ m * 2 := by
        rw [← pow_add, ← pow_succ]
        congr 1
        omega
      rw [plateHalf, hcast, h2]
      field_simp
      ring
    have h4 : 4 * lamB ≤ lam / 2 := by linarith [hlam8]
    calc lamB * (8 * plateHalf M) * (2 : ℝ) ^ m
        = lamB * (8 * plateHalf M * (2 : ℝ) ^ m) := mul_assoc _ _ _
      _ = lamB * (4 / ((2 ^ (M - m) : ℕ) : ℝ)) := by rw [hph']
      _ = (4 * lamB) / ((2 ^ (M - m) : ℕ) : ℝ) := by ring
      _ ≤ (lam / 2) / ((2 ^ (M - m) : ℕ) : ℝ) := div_le_div_of_nonneg_right h4 hmtp.le
      _ = lam / (2 * ((2 ^ (M - m) : ℕ) : ℝ)) := by ring

/-! ## The global constants of the §3.4 assembly -/

/-- The (ξ'-uniform) torsion constant of the projected curve. -/
noncomputable def projCL (k l : ℕ) (hl : 1 ≤ l) (hlk : l ≤ k) : ℝ :=
  Classical.choose (projConstants_uniform k l hl hlk)

/-- The (ξ'-uniform) Taylor constant of the projected curve. -/
noncomputable def projRR (k l : ℕ) (hl : 1 ≤ l) (hlk : l ≤ k) : ℝ :=
  Classical.choose (Classical.choose_spec (projConstants_uniform k l hl hlk)).2

lemma projCL_pos (k l : ℕ) (hl : 1 ≤ l) (hlk : l ≤ k) : 0 < projCL k l hl hlk :=
  (Classical.choose_spec (projConstants_uniform k l hl hlk)).1

lemma projRR_pos (k l : ℕ) (hl : 1 ≤ l) (hlk : l ≤ k) : 0 < projRR k l hl hlk :=
  (Classical.choose_spec (Classical.choose_spec (projConstants_uniform k l hl hlk)).2).1

lemma projConstants_spec (k l : ℕ) (hl : 1 ≤ l) (hlk : l ≤ k) :
    ∀ ξ' ∈ Set.Icc (0 : ℝ) 1,
      (∀ t ∈ Set.Icc (0 : ℝ) 1, 1 / 4 ≤ |t - ξ'| →
        PlateLowerAt l (projCurveDeriv k l (torsionVec k l hlk ξ')) (projCL k l hl hlk) t) ∧
      CurveTaylorTop l (projCurveDeriv k l (torsionVec k l hlk ξ')) (projRR k l hl hlk) :=
  (Classical.choose_spec (Classical.choose_spec (projConstants_uniform k l hl hlk)).2).2

/-- The (ξ'-uniform) plate-enlargement constant of the class transport. -/
noncomputable def classCB (k l : ℕ) (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k) : ℝ :=
  Classical.choose (exists_class_subBlk_uniform hk hl hlk)

lemma one_le_classCB (k l : ℕ) (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k) :
    1 ≤ classCB k l hk hl hlk :=
  (Classical.choose_spec (exists_class_subBlk_uniform hk hl hlk)).1

lemma classCB_spec (k l : ℕ) (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k) :
    ∀ ξ' ∈ Set.Icc (0 : ℝ) 1, ∀ {N m M : ℕ} (h2m : 2 ≤ m) (hmM : m ≤ M) (hMN : M ≤ N)
      (q : Fin (2 ^ m))
      (hsep : ∀ j : Fin (2 ^ (M - m)),
        1 / 4 ≤ |pieceCenter (2 ^ M) (subIdx m M hmM q j) - ξ'|)
      {lam : ℝ} (hlam8 : 8 * classCB k l hk hl hlk ≤ lam)
      (u : E k) (f : Fin (2 ^ N) → E k → ℂ),
      (∀ i, IsFourierRep k (piecePlate k (2 ^ N) i) (f i)) →
      ∀ j : Fin (2 ^ (M - m)),
        IsFourierRep l
          (curvePlate l
            (intervalCurve l (((q : ℕ) : ℝ) / (2 : ℝ) ^ m) (1 / (2 : ℝ) ^ m)
              (projCurveDeriv k l (torsionVec k l hlk ξ')))
            (lam / (2 * ((2 ^ (M - m) : ℕ) : ℝ))) (pieceCenter (2 ^ (M - m)) j))
          (fun y => ∑ i ∈ blkFin N M (subIdx m M hmM q j),
            f i (u + projEmbedLin k l (torsionVec k l hlk ξ') y)) :=
  (Classical.choose_spec (exists_class_subBlk_uniform hk hl hlk)).2

/-- **The fixed plate enlargement of the §3.4 lane**, valid for every `ξ' ∈ [0,1]`. -/
noncomputable def laneLam (k l : ℕ) (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k) : ℝ :=
  max (lamProj l k (projCL k l hl hlk)) (8 * classCB k l hk hl hlk)

lemma one_le_laneLam (k l : ℕ) (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k) :
    1 ≤ laneLam k l hk hl hlk :=
  le_trans (one_le_lamProj l k _) (le_max_left _ _)

lemma lamProj_le_laneLam (k l : ℕ) (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k) :
    lamProj l k (projCL k l hl hlk) ≤ laneLam k l hk hl hlk := le_max_left _ _

lemma classCB_le_laneLam (k l : ℕ) (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k) :
    8 * classCB k l hk hl hlk ≤ laneLam k l hk hl hlk := le_max_right _ _

/-- **The model enlargement needed by the §3.4 lane** (the tower's enlargement at the lane's plate
scale).  The degree-`l` induction hypothesis must be available at this enlargement. -/
noncomputable def laneEnl (k l : ℕ) (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k) : ℝ :=
  towerEnlP l (projCL k l hl hlk) (projRR k l hl hlk) (2 * laneLam k l hk hl hlk)

/-- The level gap above which the lane's arithmetic side condition `2 Λ ≤ 2^(M-m)` holds. -/
noncomputable def laneK (k l : ℕ) (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k) : ℕ :=
  Classical.choose (exists_two_mul_le_two_pow (laneLam k l hk hl hlk))

lemma laneK_spec (k l : ℕ) (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k) :
    ∀ {n : ℕ}, laneK k l hk hl hlk ≤ n → 2 * laneLam k l hk hl hlk ≤ (2 : ℝ) ^ n :=
  Classical.choose_spec (exists_two_mul_le_two_pow (laneLam k l hk hl hlk))

/-- **The §3.4 lane at the explicit (ξ'-uniform) enlargement `laneLam`.**  This is lane 4 with both
side conditions discharged at the *fixed* enlargement `laneLam k l hk hl hlk`, and with the degree-`l`
model hypothesis taken at the fixed enlargement `laneEnl k l hk hl hlk`. -/
theorem asymAV_le_proj_explicit {k l N m M m' : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k)
    (h2m : 2 ≤ m) (hmM : m ≤ M) (hMN : M ≤ N)
    {ξ' : ℝ} (hξ' : ξ' ∈ Set.Icc (0 : ℝ) 1) (q : Fin (2 ^ m))
    (hsepI : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      1 / 4 ≤ |((q : ℕ) : ℝ) / (2 : ℝ) ^ m + (1 / (2 : ℝ) ^ m) * t - ξ'|)
    (hsep : ∀ j : Fin (2 ^ (M - m)),
      1 / 4 ≤ |pieceCenter (2 ^ M) (subIdx m M hmM q j) - ξ'|)
    (hM : M = refLvl l k m') (h4 : 4 ≤ 2 ^ (M - m))
    (hlam2 : 2 * laneLam k l hk hl hlk ≤ (2 : ℝ) ^ (M - m))
    {a₀ εm A : ℝ} (ha1 : 1 ≤ a₀) (hεm : 0 < εm) (hA : 0 ≤ A)
    (hm : 1 ≤ m)
    {f : Fin (2 ^ N) → E k → ℂ}
    (hf : ∀ i, IsFourierRep k (piecePlate k (2 ^ N) i) (f i))
    {r : ℝ} (hrR : hBallR k l m' ≤ r)
    (hmMod : ∀ M' : ℕ, 1 ≤ M' → DecLinScale l M' (laneEnl k l hk hl hlk)
      (ENNReal.ofReal (a₀ * (M' : ℝ) ^ εm))) :
    ∃ C : ℝ≥0∞, ∀ u : E k,
      (∫⁻ w in Metric.ball (0 : E l) r,
          (‖∑ i ∈ blkFin N m q,
            f i (u + projEmbedLin k l (torsionVec k l hlk ξ') w)‖₊ : ℝ≥0∞) ^ (plExp l))
        ≤ ENNReal.ofReal ((volume (Metric.ball (0 : E l) r)).toReal) * C ^ (plExp l)
          * (∑ J ∈ subBlkLvl m M q,
              (tentNorm l A 0 r (fun y : E l => ∑ i ∈ blkFin N M J,
                f i (u + projEmbedLin k l (torsionVec k l hlk ξ') y))) ^ (2 / plExp l))
            ^ (plExp l / 2) := by
  have hcL : 0 < projCL k l hl hlk := projCL_pos k l hl hlk
  have hR : 0 < projRR k l hl hlk := projRR_pos k l hl hlk
  have hplate := (projConstants_spec k l hl hlk ξ' hξ').1
  have htay := (projConstants_spec k l hl hlk ξ' hξ').2
  have hcast : (((2 ^ (M - m) : ℕ)) : ℝ) = (2 : ℝ) ^ (M - m) := by push_cast; ring
  have hρ : (2 : ℝ) ^ (l + 2) ≤ projCL k l hl hlk * (1 / (2 : ℝ) ^ m) ^ l
      * (hBallR k l m' / (((2 ^ (M - m) : ℕ)) : ℝ) ^ l) * (laneLam k l hk hl hlk) ^ l := by
    rw [hcast]
    exact hρlR_mono hl hlk hcL hmM hM (lamProj_le_laneLam k l hk hl hlk)
  have hge : (((2 ^ (M - m) : ℕ)) : ℝ) ^ l ≤ hBallR k l m' := hBallR_ge_pow (l := l) hM
  have hmMod' : ∀ M' : ℕ, 1 ≤ M' →
      DecLinScale l M' (towerEnlP l (projCL k l hl hlk) (projRR k l hl hlk)
        (2 * laneLam k l hk hl hlk)) (ENNReal.ofReal (a₀ * (M' : ℝ) ^ εm)) := hmMod
  obtain ⟨C, hdec⟩ := curveDecLocR_intervalCurve_proj hl hlk hξ' hcL hR hplate htay
    ha1 hεm (one_le_laneLam k l hk hl hlk) hm hmM h4 q hsepI hlam2 hge hρ hA hmMod'
  refine ⟨C, fun u => ?_⟩
  have hclass := classCB_spec k l hk hl hlk ξ' hξ' h2m hmM hMN q hsep
    (classCB_le_laneLam k l hk hl hlk) u f hf
  exact asymAV_le_curveDecLocR hl hlk hmM hMN q (u := u) hA hrR hdec hclass


end Submission.Vinogradov
