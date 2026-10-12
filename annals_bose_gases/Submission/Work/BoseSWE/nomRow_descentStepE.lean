import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseSWE.nomBracketE
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseSWE

/-- **The state-level `n = m·n₀ + n''` descent step at the nominal row, with the slack `ErrE`.**

This is the `E`-twin of the PROVED `Work.BoseB1Cube.nomRow_descentStep`
(`Submission/Work/BoseB1Cube/nomRowDescent.lean`, second half): copy its proof verbatim, with the
following three changes.

1. The hypothesis `hGRP` carries the slack `ErrE v CE μ n'` inside its bracket (it is the row
   `((1/18)μ(n'/V)W − ErrE v CE μ n')·∫Ψ² ≤ sbWordCube`, exactly the `hGRP` of
   `Work.BoseSWE.perBoxFNomE_inBox_of_windowRowsE`); the hypothesis `hREM` is *unchanged*
   (`nomE` is definitionally `nomESlot v R C μ μ u`).
2. In the twin the two per-size rows become the two group rows
   `hB1 : (G₁)·∫Ψ² ≤ sbWordCube` with `G₁ = (1/18)μ(n₀/nomV)W` and
   `hB2 : (G₂)·∫Ψ² ≤ sbWordCube` with `G₂ = ¼(σ−μ)²W − ½μ²W − nomESlot v R C μ μ u`, and then
   `Work.BoseB1Cube.sbWordCube_descent_atSizes` is invoked with `G₁`, `G₂`.  Here one instead takes
   `G₁ = (1/18)μ(n₀/nomV)W − ErrE v CE μ n₀` (the descent is generic in the two rows, so the call
   is verbatim); `hB1` is then exactly `hGRP` at `n₀`.
3. The final arithmetic replaces `Work.BoseB1Cube.nomBracket_le_groupBracket` by the PROVED
   `Work.BoseSWE.nomBracket_le_groupBracketE` (in `Submission/Work/BoseSWE/nomBracketE.lean`) with
   `CE := CE`, `av := a v`, `d80 := (Work.BoseFixB1.bD v μ)^80`, and the conclusion carries the
   extra term `− ErrE v CE μ (m·n₀+nr)·∫Φ²`; at the end `linarith [hmul, hdesc, herr]` where
   `herr : 0 ≤ ErrE v CE μ (m·n₀+nr) * ∫Φ²` is `mul_nonneg (ErrE_nonneg hCE hav.le hμ.le) hNnn`.
   (`hWnn`, `hNnn`, `hnrR`, `hμ`, `hVpos`, `hR16`, `hRχ`, `hn₀ub` are the twin's own local facts.)
   Note (reviewer 2): `linarith` alone does not identify `ErrE v CE μ N * ∫` with
   `CE·(a v)·μ·N·(bD v μ)^80 * ∫` — `unfold ErrE` / `simp only [ErrE]` is needed at the end. -/
theorem nomRow_descentStepE {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v)
    {Cn ε₀ C CE : ℝ} (hCn : 2 ≤ Cn) (hε₀ : 0 < ε₀) (hC : 0 ≤ C) (hCE : 0 ≤ CE)
    (hGRP : ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n' : ℕ) (Ψ : Submission.BoseGases.X n' → ℝ)
        (u : EuclideanSpace ℝ (Fin 3)),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
        ContDiff ℝ (⊤ : ℕ∞) Ψ →
        (∀ᵐ x ∂(MeasureTheory.volume.restrict
            (Submission.BoseGases.abox n' (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))),
          Ψ x ≠ 0 → ∀ i : Fin n', x i ∈ Submission.BoseGases.dlBox
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) →
        Cn * μ * Work.BoseB1Cube.nomV v μ u ≤ (n' : ℝ) →
        (n' : ℝ) ≤ 2 * Cn * μ * Work.BoseB1Cube.nomV v μ u →
        ((1 / 18) * μ * ((n' : ℝ) / Work.BoseB1Cube.nomV v μ u) * Work.BoseB1Cube.nomW v h μ u
            - Work.BoseSWE.ErrE v CE μ n')
            * (∫ x in Submission.BoseGases.abox n' (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                (Ψ x) ^ 2)
          ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ)
    (hREM : ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n' : ℕ) (Ψ : Submission.BoseGases.X n' → ℝ)
        (u : EuclideanSpace ℝ (Fin 3)),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
        ContDiff ℝ (⊤ : ℕ∞) Ψ →
        (∀ᵐ x ∂(MeasureTheory.volume.restrict
            (Submission.BoseGases.abox n' (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))),
          Ψ x ≠ 0 → ∀ i : Fin n', x i ∈ Submission.BoseGases.dlBox
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) →
        (n' : ℝ) ≤ 2 * Cn * μ * Work.BoseB1Cube.nomV v μ u →
        ((1 / 4) * (((n' : ℝ) / Work.BoseB1Cube.nomV v μ u) - μ) ^ 2 - (1 / 2) * μ ^ 2)
            * Work.BoseB1Cube.nomW v h μ u
            * (∫ x in Submission.BoseGases.abox n' (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                (Ψ x) ^ 2)
          - Work.BoseB1Cube.nomE v R C μ u
            * (∫ x in Submission.BoseGases.abox n' (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                (Ψ x) ^ 2)
          ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ)
    {μ : ℝ} (hAdm : Work.BoseBoxFix.Adm v ε₀ μ) (u : EuclideanSpace ℝ (Fin 3))
    (hu : u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)
    (hVpos : 0 < Work.BoseB1Cube.nomV v μ u)
    (hR16 : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
              * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d / 16)
    (hRχ : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0)
    {n₀ : ℕ} (hn₀lb : Cn * μ * Work.BoseB1Cube.nomV v μ u ≤ (n₀ : ℝ))
    (hn₀ub : (n₀ : ℝ) ≤ 2 * Cn * μ * Work.BoseB1Cube.nomV v μ u)
    {m nr : ℕ} (hnr : nr < n₀)
    (Φ : Work.BoseKinLoc.BoxState (m * n₀ + nr) (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
    (hloc : ∀ᵐ x ∂(MeasureTheory.volume.restrict
        (Submission.BoseGases.abox (m * n₀ + nr) (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))),
      (Φ : Submission.BoseGases.X (m * n₀ + nr) → ℝ) x ≠ 0 →
        ∀ i : Fin (m * n₀ + nr), x i ∈ Submission.BoseGases.dlBox
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) :
    Work.BoseB1Cube.nomRow v h R (1 / 40) C μ μ (m * n₀ + nr) u
        (Φ : Submission.BoseGases.X (m * n₀ + nr) → ℝ)
      - Work.BoseSWE.ErrE v CE μ (m * n₀ + nr)
        * (∫ x in Submission.BoseGases.abox (m * n₀ + nr)
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            ((Φ : Submission.BoseGases.X (m * n₀ + nr) → ℝ) x) ^ 2)
      ≤ Work.BoseFixB1B.sbWordCube v h μ u
          (Φ : Submission.BoseGases.X (m * n₀ + nr) → ℝ) := by
  classical
  have hμ : 0 < μ := hAdm.1
  have hWnn : 0 ≤ Work.BoseB1Cube.nomW v h μ u :=
    Work.BoseFixB1.w1MassB_nonneg (v := v) h hv hvrad hR hv_supp
      (Work.BoseFixB1.adm_ell_pos hAdm) (Work.BoseFixB1.adm_d_pos hAdm) u
  have hNnn : 0 ≤ ∫ x in Submission.BoseGases.abox (m * n₀ + nr)
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      ((Φ : Submission.BoseGases.X (m * n₀ + nr) → ℝ) x) ^ 2 :=
    MeasureTheory.integral_nonneg (fun x => sq_nonneg _)
  have hnrR : (nr : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast le_of_lt hnr
  -- the two group rows
  have hB1 : ∀ (Ψ : Submission.BoseGases.X n₀ → ℝ), ContDiff ℝ (⊤ : ℕ∞) Ψ →
      (∀ᵐ x ∂(MeasureTheory.volume.restrict
          (Submission.BoseGases.abox n₀ (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))),
        Ψ x ≠ 0 → ∀ i : Fin n₀, x i ∈ Submission.BoseGases.dlBox
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) →
      ((1 / 18) * μ * ((n₀ : ℝ) / Work.BoseB1Cube.nomV v μ u) * Work.BoseB1Cube.nomW v h μ u
          - ErrE v CE μ n₀)
        * (∫ x in Submission.BoseGases.abox n₀ (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            (Ψ x) ^ 2)
        ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ :=
    fun Ψ hΨ hl => hGRP μ hAdm n₀ Ψ u hu hΨ hl hn₀lb hn₀ub
  have hB2 : ∀ (Ψ : Submission.BoseGases.X nr → ℝ), ContDiff ℝ (⊤ : ℕ∞) Ψ →
      (∀ᵐ x ∂(MeasureTheory.volume.restrict
          (Submission.BoseGases.abox nr (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))),
        Ψ x ≠ 0 → ∀ i : Fin nr, x i ∈ Submission.BoseGases.dlBox
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) →
      (((1 / 4) * (((nr : ℝ) / Work.BoseB1Cube.nomV v μ u) - μ) ^ 2 - (1 / 2) * μ ^ 2)
          * Work.BoseB1Cube.nomW v h μ u - Work.BoseB1Cube.nomESlot v R C μ μ u)
        * (∫ x in Submission.BoseGases.abox nr (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            (Ψ x) ^ 2)
        ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ := by
    intro Ψ hΨ hl
    have hrem := hREM μ hAdm nr Ψ u hu hΨ hl (le_trans hnrR hn₀ub)
    have hrow : (((1 / 4) * (((nr : ℝ) / Work.BoseB1Cube.nomV v μ u) - μ) ^ 2 - (1 / 2) * μ ^ 2)
          * Work.BoseB1Cube.nomW v h μ u)
          * (∫ x in Submission.BoseGases.abox nr (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              (Ψ x) ^ 2)
        - Work.BoseB1Cube.nomESlot v R C μ μ u
          * (∫ x in Submission.BoseGases.abox nr (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              (Ψ x) ^ 2)
        ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ := hrem
    calc (((1 / 4) * (((nr : ℝ) / Work.BoseB1Cube.nomV v μ u) - μ) ^ 2 - (1 / 2) * μ ^ 2)
            * Work.BoseB1Cube.nomW v h μ u - Work.BoseB1Cube.nomESlot v R C μ μ u)
          * (∫ x in Submission.BoseGases.abox nr (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              (Ψ x) ^ 2)
        = (((1 / 4) * (((nr : ℝ) / Work.BoseB1Cube.nomV v μ u) - μ) ^ 2 - (1 / 2) * μ ^ 2)
              * Work.BoseB1Cube.nomW v h μ u)
            * (∫ x in Submission.BoseGases.abox nr (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                (Ψ x) ^ 2)
          - Work.BoseB1Cube.nomESlot v R C μ μ u
            * (∫ x in Submission.BoseGases.abox nr (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                (Ψ x) ^ 2) := by ring
      _ ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ := hrow
  -- FS's descent at the two group sizes, with the slack
  have hdesc := Work.BoseB1Cube.sbWordCube_descent_atSizes (v := v) h hv hv1 hvrad hR hv_supp
    hav hAdm hR16 hRχ u
    ((1 / 18) * μ * ((n₀ : ℝ) / Work.BoseB1Cube.nomV v μ u) * Work.BoseB1Cube.nomW v h μ u
      - ErrE v CE μ n₀)
    (((1 / 4) * (((nr : ℝ) / Work.BoseB1Cube.nomV v μ u) - μ) ^ 2 - (1 / 2) * μ ^ 2)
      * Work.BoseB1Cube.nomW v h μ u - Work.BoseB1Cube.nomESlot v R C μ μ u)
    hB1 hB2 Φ.contDiff hloc
  -- the scalar bracket comparison, with the slack
  have hbracket := nomBracket_le_groupBracketE (μ := μ) (V := Work.BoseB1Cube.nomV v μ u)
    (W := Work.BoseB1Cube.nomW v h μ u) (E := Work.BoseB1Cube.nomESlot v R C μ μ u)
    (Cn := Cn) (CE := CE) (av := _root_.BoseGases.a v) (d80 := (Work.BoseFixB1.bD v μ) ^ 80)
    (n₀ := n₀) (n'' := nr) (m := m)
    hμ hVpos hWnn hCn hn₀lb (by exact_mod_cast hnr) hCE hav.le (by positivity)
  rw [Work.BoseB1Cube.nomRow_eq]
  have hfinal : ((1 / 40) * (Work.BoseB1Cube.nomW v h μ u
        * Work.SmallBoxSliding.psiWeight 1 μ
            (((m * n₀ + nr : ℕ) : ℝ) / Work.BoseB1Cube.nomV v μ u))
      - (1 / 2) * μ ^ 2 * Work.BoseB1Cube.nomW v h μ u
      - Work.BoseB1Cube.nomESlot v R C μ μ u)
      * (∫ x in Submission.BoseGases.abox (m * n₀ + nr)
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
          ((Φ : Submission.BoseGases.X (m * n₀ + nr) → ℝ) x) ^ 2)
      - ErrE v CE μ (m * n₀ + nr)
        * (∫ x in Submission.BoseGases.abox (m * n₀ + nr)
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            ((Φ : Submission.BoseGases.X (m * n₀ + nr) → ℝ) x) ^ 2)
      ≤ Work.BoseFixB1B.sbWordCube v h μ u
          (Φ : Submission.BoseGases.X (m * n₀ + nr) → ℝ) := by
    -- `nomBracket_le_groupBracketE` with the slack `ErrE` (definitionally the expanded form)
    have hbr : (1 / 40) * (Work.BoseB1Cube.nomW v h μ u
          * Work.SmallBoxSliding.psiWeight 1 μ
              (((m * n₀ + nr : ℕ) : ℝ) / Work.BoseB1Cube.nomV v μ u))
        - (1 / 2) * μ ^ 2 * Work.BoseB1Cube.nomW v h μ u
        - Work.BoseB1Cube.nomESlot v R C μ μ u
        - ErrE v CE μ (m * n₀ + nr)
        ≤ (m : ℝ) * ((1 / 18) * μ * ((n₀ : ℝ) / Work.BoseB1Cube.nomV v μ u)
            * Work.BoseB1Cube.nomW v h μ u - ErrE v CE μ n₀)
          + (((1 / 4) * (((nr : ℝ) / Work.BoseB1Cube.nomV v μ u) - μ) ^ 2 - (1 / 2) * μ ^ 2)
              * Work.BoseB1Cube.nomW v h μ u - Work.BoseB1Cube.nomESlot v R C μ μ u) :=
      hbracket
    have hmul := le_trans (mul_le_mul_of_nonneg_right hbr hNnn) hdesc
    calc ((1 / 40) * (Work.BoseB1Cube.nomW v h μ u
            * Work.SmallBoxSliding.psiWeight 1 μ
                (((m * n₀ + nr : ℕ) : ℝ) / Work.BoseB1Cube.nomV v μ u))
          - (1 / 2) * μ ^ 2 * Work.BoseB1Cube.nomW v h μ u
          - Work.BoseB1Cube.nomESlot v R C μ μ u)
          * (∫ x in Submission.BoseGases.abox (m * n₀ + nr)
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              ((Φ : Submission.BoseGases.X (m * n₀ + nr) → ℝ) x) ^ 2)
        - ErrE v CE μ (m * n₀ + nr)
          * (∫ x in Submission.BoseGases.abox (m * n₀ + nr)
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              ((Φ : Submission.BoseGases.X (m * n₀ + nr) → ℝ) x) ^ 2)
        = ((1 / 40) * (Work.BoseB1Cube.nomW v h μ u
              * Work.SmallBoxSliding.psiWeight 1 μ
                  (((m * n₀ + nr : ℕ) : ℝ) / Work.BoseB1Cube.nomV v μ u))
            - (1 / 2) * μ ^ 2 * Work.BoseB1Cube.nomW v h μ u
            - Work.BoseB1Cube.nomESlot v R C μ μ u
            - ErrE v CE μ (m * n₀ + nr))
          * (∫ x in Submission.BoseGases.abox (m * n₀ + nr)
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              ((Φ : Submission.BoseGases.X (m * n₀ + nr) → ℝ) x) ^ 2) := by ring
      _ ≤ Work.BoseFixB1B.sbWordCube v h μ u
            (Φ : Submission.BoseGases.X (m * n₀ + nr) → ℝ) := hmul
  exact hfinal

end Work.BoseSWE
