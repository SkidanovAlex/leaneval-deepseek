import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.boxMassGeOfGate
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB1Cube

/-- **The box-volume gate with a free constant.**  For every prescribed `M₀ > 0` there is a
diluteness threshold `ε₀ > 0` such that for every admissible `μ`, every `u ∈ goodSet` with
`a v ≤ μ · PBW h μ u` (the "large window" gate of the sliding-box analysis), the sliding box
volume is at least `M₀/μ`:  `M₀ ≤ μ · |B(u)|`.

This is `Work.BoseB1Cube.boxMassGeOfGate` with the fixed constant `64` replaced by an arbitrary
prescribed `M₀`.  PROOF RECIPE (adapt the PROVED `boxMassGeOfGate` verbatim; the only changes are
(i) the sliver parameter `ε` is now free, and (ii) the non-sliver branch is bounded directly via
`shortSideBetaGeom` instead of `boxMassGeArith`):

* from the gate and the PROVED sharp mass law `w1MassB_le_sharp` at `δ = 1`
  (`v h hv hv1 hvrad hR hv_supp hav (δ := 1) (by norm_num)`) get `1/(16π) ≤ μ · chiMass M ℓ d u`
  (exactly as in `boxMassGeOfGate`'s `hchi`);
* take `ε := min (1/2) (Real.sqrt (1 / (16 * Real.pi * C * M₀)))` where `C > 0` is the constant of
  the PROVED `chiMassLeSliverCube` at `M = Work.BoseBox.mValue` (`M_eq_mValue`);
  set `ε₀ := min (min εs εg) (min 1 (ε^3/M₀)^(323/148))` where `t = μ * (a v)^3`;
* **sliver branch** `∀ x, x ∈ dlBox ℓ d u → ℓ(1/2-ε) ≤ ‖x‖`: `chiMass ≤ C ε² V` by
  `chiMassLeSliverCube`, so `1/(16π) ≤ μ C ε² V`, giving `μ V ≥ 1/(16π C ε²) ≥ M₀`;
* **non-sliver branch** `∃ x ∈ dlBox ℓ d u, ‖x‖ < ℓ(1/2-ε)`: from the PROVED `shortSideBetaGeom`
  we get `shortSide ℓ d u j < ℓ*d → max 0 (|((ℓ*d)•u)_j| - ℓ*d/2) = ℓ/2 - shortSide … j`, together
  with `Work.BoseB1Cube.max_sub_le_abs_coord`; hence for every `j`,
  `shortSide ℓ d u j ≥ min (ℓ*d) (ℓ*ε) ≥ ℓ*d*ε`.  With the PROVED
  `Work.BoseFixB1S.oneBodyB1.sqrtW.boxMassProdB1` (`boxMass ℓ d u = ∏ j, shortSide ℓ d u j`)
  this gives `V ≥ (ℓ*d*ε)^3`.  Finally the PROVED
  `Work.BoseFixB1.mu_d_mul_sideAt_cube_eq` gives `μ * (ℓ*d)^3 = fsXp (μ * (a v)^3) (-148)`
  (`= t^(-148/323)`), which is `≥ M₀/ε^3` for `t ≤ (ε^3/M₀)^(323/148)` (use `fsXp_le_fsXp` /
  `Real.rpow_le_rpow_of_nonpos`); so `μ V ≥ ε^3 * M₀/ε^3 = M₀`. -/
theorem boxMassGeGateArb {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) (M₀ : ℝ) (hM₀ : 0 < M₀) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ u : EuclideanSpace ℝ (Fin 3),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) μ →
        (_root_.BoseGases.a v) ≤ μ * Work.BoseFixB1B.PBW h μ u →
        M₀ ≤ μ * Work.BoseFixB1B.PBBV v μ u := by
  -- 1. the sharp mass law at `δ = 1`
  obtain ⟨εs, hεs, hsharp⟩ :=
    w1MassB_le_sharp h hv hv1 hvrad hR hv_supp hav (δ := 1) (by norm_num)
  -- 2. the sliver constant
  obtain ⟨C, hCpos, hCsliver⟩ := chiMassLeSliverCube (M := Work.BoseBox.mValue)
    (by norm_num [Work.BoseBox.mValue])
  -- 3. the parameter gates
  obtain ⟨εg, hεg, _, hparams⟩ := ellParamGatesGe (v := v) hav
  -- 4. the free sliver parameter, tuned to `M₀`
  set ε : ℝ := min (1 / 2) (Real.sqrt (1 / (16 * Real.pi * C * M₀))) with hεdef
  have hεpos : 0 < ε := lt_min (by norm_num) (Real.sqrt_pos.mpr (by positivity))
  have hεle : ε ≤ 1 / 2 := min_le_left _ _
  have hεsq : C * ε ^ 2 ≤ 1 / (16 * Real.pi * M₀) := by
    have hlt : ε ≤ Real.sqrt (1 / (16 * Real.pi * C * M₀)) := min_le_right _ _
    have hnn : (0 : ℝ) ≤ 1 / (16 * Real.pi * C * M₀) := by positivity
    have h2 : ε ^ 2 ≤ 1 / (16 * Real.pi * C * M₀) := by
      calc ε ^ 2 ≤ (Real.sqrt (1 / (16 * Real.pi * C * M₀))) ^ 2 :=
            pow_le_pow_left₀ hεpos.le hlt 2
        _ = 1 / (16 * Real.pi * C * M₀) := Real.sq_sqrt hnn
    calc C * ε ^ 2 ≤ C * (1 / (16 * Real.pi * C * M₀)) :=
          mul_le_mul_of_nonneg_left h2 hCpos.le
      _ = 1 / (16 * Real.pi * M₀) := by field_simp
  -- 5. the diluteness threshold
  refine ⟨min (min εs εg) (min 1 ((ε ^ 3 / M₀) ^ (323 / 148 : ℝ))),
    lt_min (lt_min hεs hεg)
      (lt_min one_pos (Real.rpow_pos_of_pos (div_pos (pow_pos hεpos 3) hM₀) _)), ?_⟩
  intro μ hAdm u hu hg
  have htle : μ * (_root_.BoseGases.a v) ^ 3 ≤ (ε ^ 3 / M₀) ^ (323 / 148 : ℝ) :=
    le_trans hAdm.2.1 (le_trans (min_le_right _ _) (min_le_right _ _))
  have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
  have ha : 0 < _root_.BoseGases.a v := Work.BoseFixB1.adm_a_pos hAdm
  have hAdms : Work.BoseBoxFix.Adm v εs μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_left _ _) (min_le_left _ _))
  have hAdmg : Work.BoseBoxFix.Adm v εg μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_left _ _) (min_le_right _ _))
  obtain ⟨hgA, _, hgd2, _, _⟩ := hparams μ hAdmg
  have hℓpos : 0 < Work.BoseFixB1B.PBℓ v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hdpos : 0 < Work.BoseFixB1B.PBd v μ := Work.BoseFixB1.adm_d_pos hAdm
  have hd1 : Work.BoseFixB1B.PBd v μ ≤ 1 := le_trans hgd2 (by norm_num)
  have hreg : μ ^ (-(1 / 3 : ℝ)) ≤ Work.BoseFixB1B.PBℓ v μ * Work.BoseFixB1B.PBd v μ := by
    linarith
  -- the gate bounds the cutoff mass from below
  have hchi : 1 / (16 * Real.pi) ≤ μ * Work.SmallBoxSliding.chiMass (Work.BoseFixB1B.PBM v μ)
      (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) u := by
    have h2 := hsharp μ hAdms u
    have h3 : (1 + (1 : ℝ)) * (8 * Real.pi * _root_.BoseGases.a v)
          * Work.SmallBoxSliding.chiMass (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
              (Work.BoseFixB1B.PBd v μ) u
        = 16 * Real.pi * _root_.BoseGases.a v
          * Work.SmallBoxSliding.chiMass (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
              (Work.BoseFixB1B.PBd v μ) u := by ring
    rw [h3] at h2
    have h4 : _root_.BoseGases.a v ≤ μ * (16 * Real.pi * _root_.BoseGases.a v
        * Work.SmallBoxSliding.chiMass (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
            (Work.BoseFixB1B.PBd v μ) u) :=
      le_trans hg (mul_le_mul_of_nonneg_left h2 hμ.le)
    have h5 : (1 : ℝ) ≤ 16 * Real.pi * μ
        * Work.SmallBoxSliding.chiMass (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
            (Work.BoseFixB1B.PBd v μ) u := by
      have h6 : (1 : ℝ) * _root_.BoseGases.a v
          ≤ (16 * Real.pi * μ
              * Work.SmallBoxSliding.chiMass (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
                  (Work.BoseFixB1B.PBd v μ) u) * _root_.BoseGases.a v := by
        calc (1 : ℝ) * _root_.BoseGases.a v = _root_.BoseGases.a v := by ring
          _ ≤ μ * (16 * Real.pi * _root_.BoseGases.a v
              * Work.SmallBoxSliding.chiMass (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
                  (Work.BoseFixB1B.PBd v μ) u) := h4
          _ = (16 * Real.pi * μ
              * Work.SmallBoxSliding.chiMass (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
                  (Work.BoseFixB1B.PBd v μ) u) * _root_.BoseGases.a v := by ring
      exact le_of_mul_le_mul_right h6 ha
    have hpos : (0 : ℝ) < 16 * Real.pi := by positivity
    rw [div_le_iff₀ hpos]
    calc (1 : ℝ) = 1 := rfl
      _ ≤ 16 * Real.pi * μ
          * Work.SmallBoxSliding.chiMass (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
              (Work.BoseFixB1B.PBd v μ) u := h5
      _ = μ * Work.SmallBoxSliding.chiMass (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
              (Work.BoseFixB1B.PBd v μ) u * (16 * Real.pi) := by ring
  show M₀ ≤ μ * Work.SmallBoxSliding.boxMass (Work.BoseFixB1B.PBℓ v μ)
    (Work.BoseFixB1B.PBd v μ) u
  by_cases hsl : ∀ x : EuclideanSpace ℝ (Fin 3), x ∈ Submission.BoseGases.dlBox
      (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) u →
      (Work.BoseFixB1B.PBℓ v μ) * (1 / 2 - ε) ≤ ‖x‖
  · -- SLIVER CASE: the cutoff mass is tiny, so the box must be large
    have hsl' := hCsliver hℓpos hdpos hεpos hεle u hsl
    have hCε2pos : 0 < C * ε ^ 2 := mul_pos hCpos (pow_pos hεpos 2)
    have h2 : M₀ * (C * ε ^ 2) ≤ 1 / (16 * Real.pi) := by
      calc M₀ * (C * ε ^ 2) ≤ M₀ * (1 / (16 * Real.pi * M₀)) :=
            mul_le_mul_of_nonneg_left hεsq hM₀.le
        _ = 1 / (16 * Real.pi) := by field_simp
    have hchain : 1 / (16 * Real.pi) ≤ μ * (C * ε ^ 2)
        * Work.SmallBoxSliding.boxMass (Work.BoseFixB1B.PBℓ v μ)
            (Work.BoseFixB1B.PBd v μ) u := by
      calc 1 / (16 * Real.pi) ≤ μ * Work.SmallBoxSliding.chiMass (Work.BoseFixB1B.PBM v μ)
            (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) u := hchi
        _ ≤ μ * (C * ε ^ 2 * Work.SmallBoxSliding.boxMass (Work.BoseFixB1B.PBℓ v μ)
              (Work.BoseFixB1B.PBd v μ) u) := mul_le_mul_of_nonneg_left hsl' hμ.le
        _ = μ * (C * ε ^ 2) * Work.SmallBoxSliding.boxMass (Work.BoseFixB1B.PBℓ v μ)
              (Work.BoseFixB1B.PBd v μ) u := by ring
    have h4 : M₀ * (C * ε ^ 2) ≤ (μ * Work.SmallBoxSliding.boxMass (Work.BoseFixB1B.PBℓ v μ)
        (Work.BoseFixB1B.PBd v μ) u) * (C * ε ^ 2) := by
      calc M₀ * (C * ε ^ 2) ≤ 1 / (16 * Real.pi) := h2
        _ ≤ μ * (C * ε ^ 2) * Work.SmallBoxSliding.boxMass (Work.BoseFixB1B.PBℓ v μ)
              (Work.BoseFixB1B.PBd v μ) u := hchain
        _ = (μ * Work.SmallBoxSliding.boxMass (Work.BoseFixB1B.PBℓ v μ)
              (Work.BoseFixB1B.PBd v μ) u) * (C * ε ^ 2) := by ring
    exact le_of_mul_le_mul_right h4 hCε2pos
  · -- NON-SLIVER CASE: the box reaches the ball, and the geometry gives `V ≥ (ℓ d ε)³`
    push Not at hsl
    obtain ⟨x, hxmem, hxlt⟩ := hsl
    obtain ⟨_, _, hβnn, hclip, hcons⟩ :=
      shortSideBetaGeom (ℓ := Work.BoseFixB1B.PBℓ v μ) (d := Work.BoseFixB1B.PBd v μ)
        (μ := μ) (ε := ε) hℓpos hdpos hd1 hgd2 hμ hreg hεpos.le hεle hu hxmem hxlt.le
    -- every short side is at least `ℓ d ε`
    have hside : ∀ j : Fin 3, Work.BoseFixB1B.PBℓ v μ * Work.BoseFixB1B.PBd v μ * ε
        ≤ Work.SmallBoxSliding.shortSide (Work.BoseFixB1B.PBℓ v μ)
            (Work.BoseFixB1B.PBd v μ) u j := by
      intro j
      rcases lt_or_ge (Work.SmallBoxSliding.shortSide (Work.BoseFixB1B.PBℓ v μ)
        (Work.BoseFixB1B.PBd v μ) u j) (Work.BoseFixB1B.PBℓ v μ * Work.BoseFixB1B.PBd v μ)
        with hcase | hcase
      · set e : ℝ := max 0 (|((Work.BoseFixB1B.PBℓ v μ * Work.BoseFixB1B.PBd v μ) • u).ofLp j|
            - Work.BoseFixB1B.PBℓ v μ * Work.BoseFixB1B.PBd v μ / 2) with hedef
        have henn : 0 ≤ e := by rw [hedef]; exact hβnn j
        have hsum : e ^ 2 ≤ ∑ k : Fin 3, (max 0 (|((Work.BoseFixB1B.PBℓ v μ
              * Work.BoseFixB1B.PBd v μ) • u).ofLp k| - Work.BoseFixB1B.PBℓ v μ
                * Work.BoseFixB1B.PBd v μ / 2)) ^ 2 := by
          rw [hedef]
          exact Finset.single_le_sum (s := Finset.univ) (a := j)
            (f := fun k : Fin 3 => (max 0 (|((Work.BoseFixB1B.PBℓ v μ
              * Work.BoseFixB1B.PBd v μ) • u).ofLp k| - Work.BoseFixB1B.PBℓ v μ
                * Work.BoseFixB1B.PBd v μ / 2)) ^ 2)
            (fun k _ => sq_nonneg _) (Finset.mem_univ j)
        have hle2 : e ^ 2 ≤ (Work.BoseFixB1B.PBℓ v μ * (1 / 2 - ε)) ^ 2 := by
          refine le_trans hsum ?_
          calc ∑ k : Fin 3, (max 0 (|((Work.BoseFixB1B.PBℓ v μ
                  * Work.BoseFixB1B.PBd v μ) • u).ofLp k|
                  - Work.BoseFixB1B.PBℓ v μ * Work.BoseFixB1B.PBd v μ / 2)) ^ 2
              ≤ (Work.BoseFixB1B.PBℓ v μ) ^ 2 * (1 / 2 - ε) ^ 2 := hcons
            _ = (Work.BoseFixB1B.PBℓ v μ * (1 / 2 - ε)) ^ 2 := by ring
        have hb : 0 ≤ Work.BoseFixB1B.PBℓ v μ * (1 / 2 - ε) :=
          mul_nonneg hℓpos.le (by linarith)
        have hle : e ≤ Work.BoseFixB1B.PBℓ v μ * (1 / 2 - ε) :=
          (pow_le_pow_iff_left₀ henn hb (by norm_num : (2 : ℕ) ≠ 0)).mp hle2
        have heq := hclip j hcase
        rw [← hedef] at heq
        have hshort : Work.SmallBoxSliding.shortSide (Work.BoseFixB1B.PBℓ v μ)
            (Work.BoseFixB1B.PBd v μ) u j = Work.BoseFixB1B.PBℓ v μ / 2 - e := by linarith
        rw [hshort]
        have h0 : 0 ≤ Work.BoseFixB1B.PBℓ v μ * ε := mul_nonneg hℓpos.le hεpos.le
        have hs1 : Work.BoseFixB1B.PBℓ v μ * Work.BoseFixB1B.PBd v μ * ε
            ≤ Work.BoseFixB1B.PBℓ v μ * ε := by
          have h1 : Work.BoseFixB1B.PBℓ v μ * Work.BoseFixB1B.PBd v μ * ε
              = (Work.BoseFixB1B.PBℓ v μ * ε) * Work.BoseFixB1B.PBd v μ := by ring
          rw [h1]
          calc (Work.BoseFixB1B.PBℓ v μ * ε) * Work.BoseFixB1B.PBd v μ
              ≤ (Work.BoseFixB1B.PBℓ v μ * ε) * 1 :=
                mul_le_mul_of_nonneg_left hd1 h0
            _ = Work.BoseFixB1B.PBℓ v μ * ε := by ring
        have hs2 : Work.BoseFixB1B.PBℓ v μ * ε ≤ Work.BoseFixB1B.PBℓ v μ / 2 - e := by
          linarith
        linarith
      · have h0 : 0 ≤ Work.BoseFixB1B.PBℓ v μ * Work.BoseFixB1B.PBd v μ :=
          mul_nonneg hℓpos.le hdpos.le
        calc Work.BoseFixB1B.PBℓ v μ * Work.BoseFixB1B.PBd v μ * ε
            ≤ Work.BoseFixB1B.PBℓ v μ * Work.BoseFixB1B.PBd v μ * 1 :=
              mul_le_mul_of_nonneg_left (by linarith) h0
          _ = Work.BoseFixB1B.PBℓ v μ * Work.BoseFixB1B.PBd v μ := by ring
          _ ≤ Work.SmallBoxSliding.shortSide (Work.BoseFixB1B.PBℓ v μ)
                (Work.BoseFixB1B.PBd v μ) u j := hcase
    -- hence `V ≥ (ℓ d ε)³`
    have hV : (Work.BoseFixB1B.PBℓ v μ * Work.BoseFixB1B.PBd v μ * ε) ^ 3
        ≤ Work.SmallBoxSliding.boxMass (Work.BoseFixB1B.PBℓ v μ)
            (Work.BoseFixB1B.PBd v μ) u := by
      rw [Work.BoseFixB1S.oneBodyB1.sqrtW.boxMassProdB1 hℓpos hdpos hd1 u]
      have hnn : 0 ≤ Work.BoseFixB1B.PBℓ v μ * Work.BoseFixB1B.PBd v μ * ε :=
        mul_nonneg (mul_nonneg hℓpos.le hdpos.le) hεpos.le
      calc (Work.BoseFixB1B.PBℓ v μ * Work.BoseFixB1B.PBd v μ * ε) ^ 3
          = ∏ _j : Fin 3, (Work.BoseFixB1B.PBℓ v μ * Work.BoseFixB1B.PBd v μ * ε) := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        _ ≤ ∏ j : Fin 3, max 0 (Work.SmallBoxSliding.shortSide (Work.BoseFixB1B.PBℓ v μ)
              (Work.BoseFixB1B.PBd v μ) u j) :=
            Finset.prod_le_prod₀ (fun _ _ => hnn) (fun j _ => le_trans (hside j) (le_max_right 0 _))
    -- the cube scale from the parameter block
    have hcube : μ * (Work.BoseFixB1B.PBℓ v μ * Work.BoseFixB1B.PBd v μ) ^ 3
        = Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-148) := by
      have hh := Work.BoseFixB1.mu_d_mul_sideAt_cube_eq (A := _root_.BoseGases.a v) (μ := μ)
        hav hμ
      rw [show Work.BoseFixB1B.PBℓ v μ = Work.BoseBox.sideAt μ (_root_.BoseGases.a v) from rfl,
        show Work.BoseFixB1B.PBd v μ = (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d from rfl,
        mul_comm (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d]
      exact hh
    -- the threshold comparison
    have ht0 : 0 < μ * (_root_.BoseGases.a v) ^ 3 := mul_pos hμ (pow_pos hav 3)
    have hfs : M₀ / ε ^ 3 ≤ Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-148) := by
      have hbase : 0 < ε ^ 3 / M₀ := div_pos (pow_pos hεpos 3) hM₀
      have h1 : ((ε ^ 3 / M₀) ^ (323 / 148 : ℝ)) ^ ((-148 : ℝ) / 323)
          ≤ (μ * (_root_.BoseGases.a v) ^ 3) ^ ((-148 : ℝ) / 323) :=
        Real.rpow_le_rpow_of_nonpos ht0 htle (by norm_num)
      have h2 : ((ε ^ 3 / M₀) ^ (323 / 148 : ℝ)) ^ ((-148 : ℝ) / 323) = M₀ / ε ^ 3 := by
        rw [← Real.rpow_mul hbase.le]
        have h3 : (323 : ℝ) / 148 * ((-148 : ℝ) / 323) = -1 := by norm_num
        rw [h3, Real.rpow_neg_one, inv_div]
      rw [h2] at h1
      simpa only [Work.BoseBox.fsXp] using h1
    have heps3 : ε ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hεpos)
    calc M₀ = M₀ / ε ^ 3 * ε ^ 3 := (div_mul_cancel₀ M₀ heps3).symm
      _ = ε ^ 3 * (M₀ / ε ^ 3) := by ring
      _ ≤ ε ^ 3 * Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-148) :=
            mul_le_mul_of_nonneg_left hfs (pow_nonneg hεpos.le 3)
      _ = μ * (Work.BoseFixB1B.PBℓ v μ * Work.BoseFixB1B.PBd v μ) ^ 3 * ε ^ 3 := by
            rw [hcube]; ring
      _ = μ * (Work.BoseFixB1B.PBℓ v μ * Work.BoseFixB1B.PBd v μ * ε) ^ 3 := by ring
      _ ≤ μ * Work.SmallBoxSliding.boxMass (Work.BoseFixB1B.PBℓ v μ)
            (Work.BoseFixB1B.PBd v μ) u := mul_le_mul_of_nonneg_left hV hμ.le

end Work.BoseB1Cube
