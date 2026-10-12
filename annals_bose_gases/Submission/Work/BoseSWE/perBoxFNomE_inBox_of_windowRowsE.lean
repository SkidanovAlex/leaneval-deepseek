import ChallengeDeps
import Submission.Work.BoseSWE.nomRow_descentStepE
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseSWE

/-- **F3a of the `BoseSWE` route**: the `n = m·n₀ + n''` descent with the slack.  Recipe
(`Submission/Work/BoseSWE/BRIEF.md` §6): copy `Work.BoseB1Cube.nomBracket_le_groupBracket`,
`nomRow_descentStep`, `nomRow_all_of_windowRows` and `perBoxFNom_inBox_of_windowRows`; the generic
`Work.BoseB1Cube.sbWordCube_descent_atSizes` applies verbatim to the two group rows
`G₁ = (1/18)μ(n₀/V)W − ErrE v CE μ n₀` and `G₂ = ¼(σ−μ)²W − ½μ²W − nomESlot`.  The one new
arithmetic fact is the `E`-version of `nomBracket_le_groupBracket`, which follows from the twin
plus the slack's superadditivity `m·ErrE v CE μ n₀ ≤ ErrE v CE μ (m·n₀ + n'')`. -/
theorem perBoxFNomE_inBox_of_windowRowsE {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : Work.UBB.ScatSol v) (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v)
    {Cn ε₀ C CE : ℝ} (hCn : 3 ≤ Cn) (hε₀ : 0 < ε₀) (hC : 0 ≤ C) (hCE : 0 ≤ CE)
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
          Work.BoseSWE.PerBoxFNomE v h R (1 / 40) C CE μ μ n Φ u := by
  classical
  -- the diluteness threshold of the geometric regime
  obtain ⟨εr, hεrpos, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  refine ⟨min ε₀ (min εr 1), lt_min hε₀ (lt_min hεrpos zero_lt_one), min_le_left _ _, ?_⟩
  intro μ hAdm n Φ u hu hloc
  have hμ : 0 < μ := hAdm.1
  have hAdm₀ : Work.BoseBoxFix.Adm v ε₀ μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hεr : μ * (_root_.BoseGases.a v) ^ 3 ≤ εr :=
    le_trans hAdm.2.1 (le_trans (min_le_right _ _) (min_le_left _ _))
  have hε1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 :=
    le_trans hAdm.2.1 (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨hR16, hRχ⟩ := hreg μ hμ hεr
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := Work.BoseFixB1.adm_d_pos hAdm
  have hVpos : 0 < Work.BoseB1Cube.nomV v μ u :=
    Work.BoseFixB1.boxMass_pos_of_goodSet hℓ hd hμ hu
  have hμV : 1 ≤ μ * Work.BoseB1Cube.nomV v μ u :=
    Work.BoseFixB1.SectorAux.one_le_mu_boxMassGood (a := _root_.BoseGases.a v) hav hμ hε1 hu
  have hCn2 : 2 ≤ Cn := le_trans (by norm_num) hCn
  have hxge : 1 ≤ Cn * μ * Work.BoseB1Cube.nomV v μ u := by
    have h : 2 * (μ * Work.BoseB1Cube.nomV v μ u) ≤ Cn * (μ * Work.BoseB1Cube.nomV v μ u) :=
      mul_le_mul_of_nonneg_right hCn2 (le_trans zero_le_one hμV)
    nlinarith [h, hμV]
  have hxpos : 0 < Cn * μ * Work.BoseB1Cube.nomV v μ u := lt_of_lt_of_le zero_lt_one hxge
  -- the group size, the number of full groups and the remainder
  have hex : ∃ n₀ : ℕ, Cn * μ * Work.BoseB1Cube.nomV v μ u ≤ (n₀ : ℝ)
      ∧ (n₀ : ℝ) ≤ 2 * Cn * μ * Work.BoseB1Cube.nomV v μ u ∧ 0 < n₀ := by
    refine ⟨⌈Cn * μ * Work.BoseB1Cube.nomV v μ u⌉₊, Nat.le_ceil _, ?_,
      Nat.ceil_pos.mpr hxpos⟩
    have h : (⌈Cn * μ * Work.BoseB1Cube.nomV v μ u⌉₊ : ℝ)
        < Cn * μ * Work.BoseB1Cube.nomV v μ u + 1 := Nat.ceil_lt_add_one hxpos.le
    linarith
  obtain ⟨n₀, hn₀lb, hn₀ub, hn₀pos⟩ := hex
  obtain ⟨m, nr, hmn, hnrlt⟩ : ∃ m nr : ℕ, n = m * n₀ + nr ∧ nr < n₀ :=
    ⟨n / n₀, n % n₀, (by rw [Nat.mul_comm]; exact (Nat.div_add_mod n n₀).symm),
      Nat.mod_lt n hn₀pos⟩
  subst hmn
  -- the state-level descent at the two group sizes, with the slack
  have hrow := Work.BoseSWE.nomRow_descentStepE (v := v) h hv hv1 hvrad hR hv_supp hav
    hCn2 hε₀ hC hCE hGRP hREM hAdm₀ u hu hVpos hR16 hRχ hn₀lb hn₀ub hnrlt Φ hloc
  rw [PerBoxFNomE_iff_row, Work.BoseB1Cube.perBoxRow_eq_nomRow (Φ := Φ) hloc]
  simp only [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
  exact hrow

end Work.BoseSWE
