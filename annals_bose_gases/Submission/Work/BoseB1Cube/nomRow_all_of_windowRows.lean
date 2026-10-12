import ChallengeDeps
import Submission.Work.BoseB1Cube.nomRowDescent
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB1Cube

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1
  Work.SmallBoxSliding Work.BoseKinLoc Work.BoseFixB1B

/-- **FS's `n = m·n₀ + n''` grouping at the nominal row, for an arbitrary particle count.**

The proof is FS `final_v2.tex` ll. 3990–4055: choose the group size `n₀ = ⌈C_n μ|B(u)|⌉₊`
(so that `C_n μ|B(u)| ≤ n₀ ≤ 2 C_n μ|B(u)|`, using `1 ≤ μ|B(u)|` on the good set), write
`n = m·n₀ + n''` with `m = n/n₀`, `n'' = n % n₀` (`Nat.div_add_mod`), substitute this identity
(`subst`, which reindexes the state `Φ` for free) and apply the state-level descent
`nomRow_descentStep` to the two per-size window rows `hGRP` (at `n₀`) and `hREM` (at `n''`).

The threshold `ε₁` is `min ε₀ (min ε_reg 1)` where `ε_reg` is the diluteness threshold of
`Work.BoseFixB1.regime_sideAt_ge` (making the box side large enough for the descent's geometric
hypotheses `R ≤ ℓd/16`, `R ≤ ℓ·chiR0`) and `1` makes `μ(a v)³ ≤ 1`, giving both the positivity of
the box volume (`boxMass_pos_of_goodSet`) and `1 ≤ μ|B(u)|`
(`one_le_mu_boxMassGood`) on the good set. -/
theorem nomRow_all_of_windowRows {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v)
    {Cn ε₀ C : ℝ} (hCn : 2 ≤ Cn) (hε₀ : 0 < ε₀) (hC : 0 ≤ C)
    (hGRP : ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n' : ℕ) (Ψ : Submission.BoseGases.X n' → ℝ) (u : EuclideanSpace ℝ (Fin 3)),
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
        (1 / 18) * μ * ((n' : ℝ) / Work.BoseB1Cube.nomV v μ u)
            * Work.BoseB1Cube.nomW v h μ u
            * (∫ x in Submission.BoseGases.abox n' (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                (Ψ x) ^ 2)
          ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ)
    (hREM : ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n' : ℕ) (Ψ : Submission.BoseGases.X n' → ℝ) (u : EuclideanSpace ℝ (Fin 3)),
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
          ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ ε₀ ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₁ μ →
        ∀ (n : ℕ)
          (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : EuclideanSpace ℝ (Fin 3)),
          u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
          (∀ᵐ x ∂(MeasureTheory.volume.restrict
              (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))),
            (Φ : Submission.BoseGases.X n → ℝ) x ≠ 0 →
              ∀ i : Fin n, x i ∈ Submission.BoseGases.dlBox
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) →
          Work.BoseB1Cube.nomRow v h R (1 / 40) C μ μ n u (Φ : Submission.BoseGases.X n → ℝ)
            ≤ Work.BoseFixB1B.sbWordCube v h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
  classical
  -- the diluteness threshold of the geometric regime
  obtain ⟨εr, hεrpos, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  refine ⟨min ε₀ (min εr 1), lt_min hε₀ (lt_min hεrpos zero_lt_one), min_le_left _ _, ?_⟩
  intro μ hAdm n Φ u hu hloc
  have hμ : 0 < μ := hAdm.1
  -- the same state is admissible at the two smaller thresholds
  have hAdm₀ : Work.BoseBoxFix.Adm v ε₀ μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hεr : μ * (a v) ^ 3 ≤ εr :=
    le_trans hAdm.2.1 (le_trans (min_le_right _ _) (min_le_left _ _))
  have hε1 : μ * (a v) ^ 3 ≤ 1 :=
    le_trans hAdm.2.1 (le_trans (min_le_right _ _) (min_le_right _ _))
  -- the geometric hypotheses of the descent
  obtain ⟨hR16, hRχ⟩ := hreg μ hμ hεr
  have hℓ : 0 < sideAt μ (a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (paramsAt μ (a v)).d := Work.BoseFixB1.adm_d_pos hAdm
  have hVpos : 0 < nomV v μ u :=
    Work.BoseFixB1.boxMass_pos_of_goodSet hℓ hd hμ hu
  -- `1 ≤ μ|B(u)|` on the good set, hence the window `n₀` is non-empty
  have hμV : 1 ≤ μ * nomV v μ u :=
    Work.BoseFixB1.SectorAux.one_le_mu_boxMassGood (a := a v) hav hμ hε1 hu
  have hxge : 1 ≤ Cn * μ * nomV v μ u := by
    have h : 2 * (μ * nomV v μ u) ≤ Cn * (μ * nomV v μ u) :=
      mul_le_mul_of_nonneg_right hCn (le_trans zero_le_one hμV)
    nlinarith [h, hμV]
  have hxpos : 0 < Cn * μ * nomV v μ u := lt_of_lt_of_le zero_lt_one hxge
  -- the group size, the number of full groups and the remainder (no `let`-bindings, so that the
  -- final `subst` can reindex the state)
  have hex : ∃ n₀ : ℕ, Cn * μ * nomV v μ u ≤ (n₀ : ℝ)
      ∧ (n₀ : ℝ) ≤ 2 * Cn * μ * nomV v μ u ∧ 0 < n₀ := by
    refine ⟨⌈Cn * μ * nomV v μ u⌉₊, Nat.le_ceil _, ?_, Nat.ceil_pos.mpr hxpos⟩
    have h : (⌈Cn * μ * nomV v μ u⌉₊ : ℝ) < Cn * μ * nomV v μ u + 1 :=
      Nat.ceil_lt_add_one hxpos.le
    linarith
  obtain ⟨n₀, hn₀lb, hn₀ub, hn₀pos⟩ := hex
  obtain ⟨m, nr, hmn, hnrlt⟩ :
      ∃ m nr : ℕ, n = m * n₀ + nr ∧ nr < n₀ :=
    ⟨n / n₀, n % n₀,
      (by rw [Nat.mul_comm]; exact (Nat.div_add_mod n n₀).symm),
      Nat.mod_lt n hn₀pos⟩
  subst hmn
  -- now the goal is at the canonical index `m * n₀ + nr`
  exact nomRow_descentStep (v := v) h hv hv1 hvrad hR hv_supp hav hCn hε₀ hC hGRP hREM
    hAdm₀ u hu hVpos hR16 hRχ hn₀lb hn₀ub hnrlt Φ hloc

end Work.BoseB1Cube
