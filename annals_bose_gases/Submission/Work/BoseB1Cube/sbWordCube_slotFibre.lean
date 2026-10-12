import ChallengeDeps
import Submission.Work.BoseB1Cube.cubeAritySharp
import Submission.Work.BoseB1Cube.sbKinCube_slotFibre
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.sbWordCube_slotFibre`

**The fibre factorisation of the matched sliding word `sbWordCube`**: for every admissible `μ`,
every `u ∈ goodSet`, every box state `Φ`, every slot set `S` with `0 < S.card` and every transport
`e : SlotIn n S ≃ Fin S.card`, the word of the slot piece is the `y`-integral, over the outside
configurations `slotOutside ℓ (B(u)) S`, of the word of the transported sharp fibre
`sharpBoxState (B(u)) (slotFibreState S e Φ y)`, and that fibre integrand is Bochner integrable.

## Proof

`sbWordCube = sbKinCube + sbPot` splits into three independent halves, each of which is an already
proved corpus statement:

* the **kinetic** half (`sbKinCube = bGapCoeff·n₊ + cubeSpectral`) is
  `Work.BoseB1Cube.sbKinCube_slotFibre` — both the factorisation and the integrability of the fibre
  integrand;
* the **potential** factorisation is `Work.SlotWord.qLHSword_slotFibre`, whose hypotheses are the
  support conditions of the localised kernels `wSmallPair`/`wSmall1Pair` (both sides of `chiSmallB`)
  and the **dilute-regime integrability** of the slot-piece-weighted density
  (`Work.BoseFixB1B.integrableOn_slotPiece_sq_qLHSden`), which is where the diluteness threshold
  `ε₀` is spent: it needs `R ≤ ℓd/16` and `R ≤ ℓ·chiR0`, supplied by
  `Work.BoseFixB1.regime_sideAt_ge` for `μ(a v)³` small enough;
* the potential fibre **integrability** is `Work.BoseFixB1B.slotPotFibreIntegrable`, again from the
  same density integrability.

The identification of the two fibres, `pieceFibre B S e Φ y = sharpBoxState B (slotFibreState S e Φ y)`
on `slotOutside ℓ B S`, is `Work.BoseFixB1B.pieceFibre_eq_sharpBoxState`.
-/

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal
open Work.BoseFixB1B Work.SmallBoxSliding Work.PerSector Work.SlotWord

set_option maxHeartbeats 1000000

namespace Work.BoseB1Cube

theorem sbWordCube_slotFibre {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ u : EuclideanSpace ℝ (Fin 3),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseFixB1B.PBℓ v μ))
        (S : Finset (Fin n)), 0 < S.card → ∀ e : Work.PerSector.SlotIn n S ≃ Fin S.card,
        MeasureTheory.Integrable
          (fun y : Work.PerSector.SlotOut n S → EuclideanSpace ℝ (Fin 3) =>
            Work.BoseFixB1B.sbWordCube v h μ u
              (Work.BoseFixB1B.sharpBoxState (Work.BoseFixB1B.PBB v μ u)
                (Work.PerSector.slotFibreState S e (Φ : Submission.BoseGases.X n → ℝ) y)))
          ((MeasureTheory.volume : MeasureTheory.Measure
            (Work.PerSector.SlotOut n S → EuclideanSpace ℝ (Fin 3))).restrict
            (Work.PerSector.slotOutside (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBB v μ u) S))
        ∧ Work.BoseFixB1B.sbWordCube v h μ u
            (Work.PerSector.slotPiece (Work.BoseFixB1B.PBB v μ u) S (Φ : Submission.BoseGases.X n → ℝ))
          = ∫ y in Work.PerSector.slotOutside (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBB v μ u) S,
              Work.BoseFixB1B.sbWordCube v h μ u
                (Work.BoseFixB1B.sharpBoxState (Work.BoseFixB1B.PBB v μ u)
                  (Work.PerSector.slotFibreState S e (Φ : Submission.BoseGases.X n → ℝ) y)) := by
  classical
  -- ### the diluteness thresholds: the kinetic half and the FS regime
  obtain ⟨εr, hεr, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  obtain ⟨εk, hεk, hkinAll⟩ := sbKinCube_slotFibre h hv hv1 hvrad hR hv_supp hav
  refine ⟨min εk εr, lt_min hεk hεr, ?_⟩
  intro μ hAdm u hu n Φ S hS e
  have hε0 : 0 < min εk εr := lt_min hεk hεr
  have hμk : Work.BoseBoxFix.Adm v εk μ :=
    ⟨hAdm.1, le_trans hAdm.2.1 (min_le_left _ _), hAdm.2.2⟩
  have hμr : Work.BoseBoxFix.Adm v εr μ :=
    ⟨hAdm.1, le_trans hAdm.2.1 (min_le_right _ _), hAdm.2.2⟩
  obtain ⟨hR16, hRχ⟩ := hreg μ hAdm.1 hμr.2.1
  have hL : 0 < PBℓ v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < PBd v μ := Work.BoseFixB1.adm_d_pos hAdm
  have hM1 : 1 ≤ PBM v μ := one_le_PBM v μ
  have hBmeas : MeasurableSet (PBB v μ u) :=
    Work.SmallBoxSliding.measurableSet_dlBox (PBℓ v μ) (PBd v μ) u
  have houtm : MeasurableSet (slotOutside (PBℓ v μ) (PBB v μ u) S) :=
    Work.SlotWord.measurableSet_slotOutside (PBℓ v μ) hBmeas S
  -- ### the kinetic half of the fibre factorisation (with its integrability)
  obtain ⟨hkinI, hkinE⟩ := hkinAll μ hμk u hu n Φ S hS e
  have hkinE' : (∫ y in slotOutside (PBℓ v μ) (PBB v μ u) S,
        sbKinCube v μ u (pieceFibre (PBB v μ u) S e (Φ : Submission.BoseGases.X n → ℝ) y))
      = sbKinCube v μ u (slotPiece (PBB v μ u) S (Φ : Submission.BoseGases.X n → ℝ)) :=
    hkinE.symm
  -- ### the potential half
  have hgi : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n =>
        (slotPiece (PBB v μ u) S (Φ : Submission.BoseGases.X n → ℝ) x) ^ 2
          * Submission.BoseGases.qLHSden n (PBℓ v μ) μ
              (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v)
              (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u) x)
      (Submission.BoseGases.abox n (PBℓ v μ)) :=
    Work.BoseFixB1B.integrableOn_slotPiece_sq_qLHSden (v := v) (h := h) (R := R)
      (ε₀ := min εk εr) (μ := μ) hv hv1 hvrad hR hv_supp hav hε0 hAdm hR16 hRχ hu Φ S
  have hsupp1 : ∀ x : EuclideanSpace ℝ (Fin 3), x ∉ PBB v μ u →
      ∀ y : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u x y = 0 :=
    fun x hx y => Work.SlotWord.wSmall1Pair_support_left hM1 hL hd u hx y
  have hsupp2 : ∀ x y : EuclideanSpace ℝ (Fin 3),
      (x ∉ PBB v μ u ∨ y ∉ PBB v μ u) →
      Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v x y = 0 := by
    intro x y hxy
    rcases hxy with hx | hy
    · exact Work.SlotWord.wSmallPair_support_left hM1 hL hd u v hx y
    · have h0 : Submission.BoseGases.chiSmallB (PBM v μ) (PBℓ v μ) (PBd v μ) u y = 0 := by
        by_contra hne
        exact hy (Work.SlotWord.chiSmallB_support_mem_dlBox hM1 hL hd hne)
      rw [Submission.BoseGases.wSmallPair, h0, mul_zero]
  have hpotI := Work.BoseFixB1B.slotPotFibreIntegrable (v := v) (h := h) (R := R)
    (ε₀ := min εk εr) (c := 0) (C := 0) (μ := μ) (u := u) (n := n)
    hv hv1 hvrad hR hv_supp hav hε0 hAdm hu Φ S e hgi
  have hpotFac := Work.SlotWord.qLHSword_slotFibre (N := n) (PBℓ v μ) (PBd v μ) μ u S
    (Φ : Submission.BoseGases.X n → ℝ) e
    (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v)
    (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u) hsupp1 hsupp2 hgi
  have hpotFac'' : Submission.BoseGases.qLHSword (N := n) (PBℓ v μ) μ
      (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v)
      (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u)
      (slotPiece (PBB v μ u) S (Φ : Submission.BoseGases.X n → ℝ))
      = ∫ y in slotOutside (PBℓ v μ) (PBB v μ u) S,
          Submission.BoseGases.qLHSword (N := S.card) (PBℓ v μ) μ
            (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v)
            (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u)
            (pieceFibre (PBB v μ u) S e (Φ : Submission.BoseGases.X n → ℝ) y) := by
    simpa only [PBB, pieceFibre] using hpotFac
  -- ### the fibre word is integrable (sum of the two halves)
  have hInt_word : MeasureTheory.Integrable
      (fun y : SlotOut n S → EuclideanSpace ℝ (Fin 3) =>
        sbWordCube v h μ u (pieceFibre (PBB v μ u) S e (Φ : Submission.BoseGases.X n → ℝ) y))
      ((MeasureTheory.volume : MeasureTheory.Measure
        (SlotOut n S → EuclideanSpace ℝ (Fin 3))).restrict
        (slotOutside (PBℓ v μ) (PBB v μ u) S)) := by
    have hsum : MeasureTheory.Integrable
        (fun y : SlotOut n S → EuclideanSpace ℝ (Fin 3) =>
          sbKinCube v μ u (pieceFibre (PBB v μ u) S e (Φ : Submission.BoseGases.X n → ℝ) y)
            + Submission.BoseGases.qLHSword (N := S.card) (PBℓ v μ) μ
                (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v)
                (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u)
                (pieceFibre (PBB v μ u) S e (Φ : Submission.BoseGases.X n → ℝ) y))
        ((MeasureTheory.volume : MeasureTheory.Measure
          (SlotOut n S → EuclideanSpace ℝ (Fin 3))).restrict
          (slotOutside (PBℓ v μ) (PBB v μ u) S)) := hkinI.add hpotI
    refine hsum.congr ?_
    filter_upwards with y
    simp only [sbWordCube, Work.BoseFixB1.sbPot, Work.SmallBoxSliding.qLHSwordB]
  -- ### the target's first conjunct: the same at the sharp fibre
  have hInt_g : MeasureTheory.Integrable
      (fun y : SlotOut n S → EuclideanSpace ℝ (Fin 3) =>
        sbWordCube v h μ u
          (sharpBoxState (PBB v μ u)
            (slotFibreState S e (Φ : Submission.BoseGases.X n → ℝ) y)))
      ((MeasureTheory.volume : MeasureTheory.Measure
        (SlotOut n S → EuclideanSpace ℝ (Fin 3))).restrict
        (slotOutside (PBℓ v μ) (PBB v μ u) S)) :=
    hInt_word.congr (by
      filter_upwards [MeasureTheory.ae_restrict_mem houtm] with y hy
      congr 1
      funext x
      exact Work.BoseFixB1B.pieceFibre_eq_sharpBoxState u S e
        (Φ : Submission.BoseGases.X n → ℝ) y
        (fun j => (Work.PerSector.mem_slotOutside_iff.mp hy).2 j) x)
  -- ### the factorisation of the fibre word
  have hword : (∫ y in slotOutside (PBℓ v μ) (PBB v μ u) S,
        sbWordCube v h μ u (pieceFibre (PBB v μ u) S e (Φ : Submission.BoseGases.X n → ℝ) y))
      = sbWordCube v h μ u (slotPiece (PBB v μ u) S (Φ : Submission.BoseGases.X n → ℝ)) := by
    have hsplit : (fun y : SlotOut n S → EuclideanSpace ℝ (Fin 3) =>
          sbWordCube v h μ u (pieceFibre (PBB v μ u) S e (Φ : Submission.BoseGases.X n → ℝ) y))
        = fun y => sbKinCube v μ u
              (pieceFibre (PBB v μ u) S e (Φ : Submission.BoseGases.X n → ℝ) y)
            + Submission.BoseGases.qLHSword (N := S.card) (PBℓ v μ) μ
                (Submission.BoseGases.wSmallPair (PBM v μ) (PBℓ v μ) (PBd v μ) u v)
                (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u)
                (pieceFibre (PBB v μ u) S e (Φ : Submission.BoseGases.X n → ℝ) y) := by
      funext y
      simp only [sbWordCube, Work.BoseFixB1.sbPot, Work.SmallBoxSliding.qLHSwordB]
    rw [hsplit, MeasureTheory.integral_add hkinI hpotI, hkinE', ← hpotFac'']
    simp only [sbWordCube, Work.BoseFixB1.sbPot, Work.SmallBoxSliding.qLHSwordB]
  -- ### the two fibre integrands agree on the outside configurations
  have hcongr : (∫ y in slotOutside (PBℓ v μ) (PBB v μ u) S,
        sbWordCube v h μ u (pieceFibre (PBB v μ u) S e (Φ : Submission.BoseGases.X n → ℝ) y))
      = ∫ y in slotOutside (PBℓ v μ) (PBB v μ u) S,
          sbWordCube v h μ u
            (sharpBoxState (PBB v μ u)
              (slotFibreState S e (Φ : Submission.BoseGases.X n → ℝ) y)) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem houtm] with y hy
    congr 1
    funext x
    exact Work.BoseFixB1B.pieceFibre_eq_sharpBoxState u S e
      (Φ : Submission.BoseGases.X n → ℝ) y
      (fun j => (Work.PerSector.mem_slotOutside_iff.mp hy).2 j) x
  exact ⟨hInt_g, hword.symm.trans hcongr⟩

end Work.BoseB1Cube
