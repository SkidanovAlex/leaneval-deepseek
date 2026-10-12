import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1B.sbWord_descent_twoBlock
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory
open scoped Real Topology BigOperators ENNReal

namespace Work.BoseFixB1B

local notation "E3" => EuclideanSpace ℝ (Fin 3)

noncomputable section

/-!
# `Work.BoseFixB1B.sbWord_descent_grouped` — the `m`-block descent for `sbWord`

`sbWord_slice_superadd_regime_holds` (FS Step E, the *grouping* step at the sliding box) says
that the `(N₁+N₂)`-particle word dominates the sum of the two block-slice integrals:

    sbWord h μ u Φ ≥ ∫_w sbWord h μ u (slice_w Φ) + ∫_u sbWord h μ u (slice'_u Φ).

`sbWord_descent_twoBlock` turns this into the *two*-block descent `(g₁+g₂)∫Φ² ≤ sbWord Φ` from
the per-particle-number lower bounds `g₁∫Ψ² ≤ sbWord Ψ` (all `Ψ` on `N₁` slots) and
`g₂∫Ψ² ≤ sbWord Ψ` (all `Ψ` on `N₂` slots).

This file iterates that step: peeling one block of `n'` coordinates at a time from an
`(m·n' + n'')`-particle state, each peeling level `∫_w sbWord(slice_w)` is bounded below by `g₁`
times the *full* mass `∫Φ²` — because the block split is measure preserving, so
`∫_w ∫_y Φ(merge(y,w))² = ∫Φ²` at *every* level — while the final leftover block of `n''`
coordinates is bounded by `g₂∫Φ²`.  Summing the `m` levels gives the grouped bound

    (m·g₁ + g₂)·∫Φ² ≤ sbWord h μ u Φ .

The induction is carried out in the right-nested presentation `groupedIdx M n' n''` of the
particle number, whose recursion `groupedIdx (M+1) n' n'' = n' + groupedIdx M n' n''` is
*definitional*, so that the block decomposition of the `(M+1)`-step syntactically matches
`mergeBlock`'s `N₁ + N₂`.
-/

/-- The right-nested presentation of the descent particle number `M·n' + n''`:

`groupedIdx M n' n'' = n' + (n' + (… + n''))`  (`M` copies of `n'` in front of `n''`).

It is chosen so that the recursion `groupedIdx (M+1) n' n'' = n' + groupedIdx M n' n''` holds
*definitionally*, which lets the block decomposition of the induction step apply directly. -/
def groupedIdx : ℕ → ℕ → ℕ → ℕ
  | 0, _, n'' => n''
  | Nat.succ M, n', n'' => n' + groupedIdx M n' n''

theorem groupedIdx_succ (M n' n'' : ℕ) :
    groupedIdx (M + 1) n' n'' = n' + groupedIdx M n' n'' := rfl

theorem groupedIdx_eq (M n' n'' : ℕ) : groupedIdx M n' n'' = M * n' + n'' := by
  induction M generalizing n' n'' with
  | zero => simp [groupedIdx]
  | succ M ih => rw [groupedIdx_succ, ih, Nat.succ_mul]; omega

theorem groupedIdx_eq' (M n' n'' : ℕ) : groupedIdx M n' n'' = n'' + n' * M := by
  rw [groupedIdx_eq, Nat.mul_comm]; omega

theorem sbWord_descent_grouped {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) {ε₀ μ : ℝ} (hAdm : Work.BoseBoxFix.Adm v ε₀ μ)
    (hR16 : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d / 16)
    (hRχ : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) (g1 g2 : ℝ)
    (hB1 : ∀ {N : ℕ} (Ψ : Submission.BoseGases.X N → ℝ), ContDiff ℝ (⊤ : ℕ∞) Ψ →
      (∀ᵐ x ∂(MeasureTheory.volume.restrict
          (Submission.BoseGases.abox N (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))),
        Ψ x ≠ 0 → ∀ i : Fin N, x i ∈ Submission.BoseGases.dlBox
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) →
      g1 * (∫ x in Submission.BoseGases.abox N (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              (Ψ x) ^ 2) ≤ Work.BoseFixB1.sbWord h μ u Ψ)
    (hB2 : ∀ {N : ℕ} (Ψ : Submission.BoseGases.X N → ℝ), ContDiff ℝ (⊤ : ℕ∞) Ψ →
      (∀ᵐ x ∂(MeasureTheory.volume.restrict
          (Submission.BoseGases.abox N (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))),
        Ψ x ≠ 0 → ∀ i : Fin N, x i ∈ Submission.BoseGases.dlBox
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) →
      g2 * (∫ x in Submission.BoseGases.abox N (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              (Ψ x) ^ 2) ≤ Work.BoseFixB1.sbWord h μ u Ψ)
    {N m n' n'' : ℕ} (hN : N = m * n' + n'')
    {Φ : Submission.BoseGases.X N → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hin : ∀ᵐ x ∂(MeasureTheory.volume.restrict
        (Submission.BoseGases.abox N (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))),
      Φ x ≠ 0 → ∀ i : Fin N, x i ∈ Submission.BoseGases.dlBox
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) :
    ((m : ℝ) * g1 + g2) * (∫ x in Submission.BoseGases.abox N
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)), (Φ x) ^ 2)
      ≤ Work.BoseFixB1.sbWord h μ u Φ := by
  -- abbreviations: `let` bindings are definitionally transparent, so every lemma below applies
  -- with the literal expressions of the statement.
  let ℓ : ℝ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
  let V : Set E3 := Submission.BoseGases.dlBox
    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
  have hℓpos : 0 < ℓ := Work.BoseFixB1.adm_ell_pos hAdm
  -- the induction on the number `M` of peeled blocks of size `n'`
  have key : ∀ M (n' n'' : ℕ) (N : ℕ), N = groupedIdx M n' n'' →
      ∀ (Φ : Submission.BoseGases.X N → ℝ), ContDiff ℝ (⊤ : ℕ∞) Φ →
      (∀ᵐ x ∂(MeasureTheory.volume.restrict
          (Submission.BoseGases.abox N ℓ)),
        Φ x ≠ 0 → ∀ i : Fin N, x i ∈ V) →
      ((M : ℝ) * g1 + g2) *
        (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2)
        ≤ Work.BoseFixB1.sbWord h μ u Φ := by
    intro M
    induction M with
    | zero =>
      -- `groupedIdx 0 n' n'' = n''`: this is exactly `hB2`
      intro n' n'' N hN Φ hΦ hloc
      subst hN
      simpa only [Nat.cast_zero, zero_mul, zero_add] using hB2 Φ hΦ hloc
    | succ M ih =>
      intro n' n'' N hN Φ hΦ hin
      subst hN
      -- unfold the recursion of the index: `groupedIdx (M+1) n' n'' = n' + groupedIdx M n' n''`
      -- (a `defeq`-based `change`, since `Φ`, `hin` depend on the index)
      change (((M + 1 : ℕ) : ℝ) * g1 + g2) *
          (∫ x in Submission.BoseGases.abox (n' + groupedIdx M n' n'') ℓ, (Φ x) ^ 2)
          ≤ Work.BoseFixB1.sbWord h μ u Φ
      have hΦc : Continuous Φ := hΦ.continuous
      -- integrability of `Φ²` on the full box (the box is compact and `Φ` is continuous)
      have hGint : IntegrableOn
          (fun x : Submission.BoseGases.X (n' + groupedIdx M n' n'') => (Φ x) ^ 2)
          (Submission.BoseGases.abox (n' + groupedIdx M n' n'') ℓ) volume :=
        Submission.BoseGases.integrableOn_abox_of_continuous hℓpos (hΦc.pow 2)
      -- the a.e. localisation statement pulls back to the product of the two block boxes
      have hprodP : ∀ᵐ p ∂((volume.restrict (Submission.BoseGases.abox n' ℓ)).prod
            (volume.restrict (Submission.BoseGases.abox (groupedIdx M n' n'') ℓ))),
          Φ (Submission.BoseGases.mergeBlock n' (groupedIdx M n' n'') p) ≠ 0 →
            ∀ i : Fin (n' + groupedIdx M n' n''),
              Submission.BoseGases.mergeBlock n' (groupedIdx M n' n'') p i ∈ V :=
        ae_prod_abox_of_ae_abox (N1 := n') (N2 := groupedIdx M n' n'') (ℓ := ℓ)
          (P := fun x : Submission.BoseGases.X (n' + groupedIdx M n' n'') =>
            Φ x ≠ 0 → ∀ i : Fin (n' + groupedIdx M n' n''), x i ∈ V) hin
      have hsec := ae_sections_prod (N1 := n') (N2 := groupedIdx M n' n'') (ℓ := ℓ)
        (P := fun x : Submission.BoseGases.X (n' + groupedIdx M n' n'') =>
          Φ x ≠ 0 → ∀ i : Fin (n' + groupedIdx M n' n''), x i ∈ V) hprodP
      -- the localisation of each block along the sections of the product
      have hcont1 : ∀ᵐ w ∂(volume.restrict
            (Submission.BoseGases.abox (groupedIdx M n' n'') ℓ)),
          ∀ᵐ y ∂(volume.restrict (Submission.BoseGases.abox n' ℓ)),
            Φ (Submission.BoseGases.mergeBlock n' (groupedIdx M n' n'') (y, w)) ≠ 0 →
              ∀ j : Fin n', y j ∈ V :=
        hsec.1.mono fun w hw => hw.mono fun y hy => fun hne j => by
          have h1 := hy hne (Fin.castAdd (groupedIdx M n' n'') j)
          rwa [mergeBlock_apply_castAdd (y, w) j] at h1
      have hcont2 : ∀ᵐ y ∂(volume.restrict (Submission.BoseGases.abox n' ℓ)),
          ∀ᵐ w ∂(volume.restrict (Submission.BoseGases.abox (groupedIdx M n' n'') ℓ)),
            Φ (Submission.BoseGases.mergeBlock n' (groupedIdx M n' n'') (y, w)) ≠ 0 →
              ∀ j : Fin (groupedIdx M n' n''), w j ∈ V :=
        hsec.2.mono fun y hy => hy.mono fun w hw => fun hne j => by
          have h1 := hw hne (Fin.natAdd n' j)
          rwa [mergeBlock_apply_natAdd (y, w) j] at h1
      -- the `g₁`-bound on the first-block slices (`N₁ = n'`), a.e. in the second block variable
      have hae1 : ∀ᵐ w ∂(volume.restrict
            (Submission.BoseGases.abox (groupedIdx M n' n'') ℓ)),
          g1 * (∫ y in Submission.BoseGases.abox n' ℓ,
              (Φ (Submission.BoseGases.mergeBlock n' (groupedIdx M n' n'') (y, w))) ^ 2)
            ≤ Work.BoseFixB1.sbWord h μ u
                (fun y => Φ (Submission.BoseGases.mergeBlock
                  n' (groupedIdx M n' n'') (y, w))) := by
        filter_upwards [hcont1] with w hw
        exact hB1 (N := n')
          (fun y => Φ (Submission.BoseGases.mergeBlock n' (groupedIdx M n' n'') (y, w)))
          (Work.KinPSuperadd.slice_contDiff_infty_fst hΦ w) hw
      -- the induction hypothesis on the second-block slices (`N₂ = groupedIdx M n' n''`),
      -- a.e. in the first block variable
      have hae2 : ∀ᵐ y ∂(volume.restrict (Submission.BoseGases.abox n' ℓ)),
          ((M : ℝ) * g1 + g2) * (∫ w in Submission.BoseGases.abox
              (groupedIdx M n' n'') ℓ,
              (Φ (Submission.BoseGases.mergeBlock n' (groupedIdx M n' n'') (y, w))) ^ 2)
            ≤ Work.BoseFixB1.sbWord h μ u
                (fun w => Φ (Submission.BoseGases.mergeBlock
                  n' (groupedIdx M n' n'') (y, w))) := by
        filter_upwards [hcont2] with y hy
        exact ih n' n'' (groupedIdx M n' n'') rfl
          (fun w => Φ (Submission.BoseGases.mergeBlock n' (groupedIdx M n' n'') (y, w)))
          (Work.KinPSuperadd.slice_contDiff_infty_snd hΦ y) hy
      -- integrability of the two mass slices, from the product integrability of `Φ²`
      have hprodG := integrable_prod_merge_of_integrableOn_abox (N1 := n')
        (N2 := groupedIdx M n' n'') (ℓ := ℓ)
        (G := fun x : Submission.BoseGases.X (n' + groupedIdx M n' n'') => (Φ x) ^ 2) hGint
      have hmass1 : IntegrableOn
          (fun w : Submission.BoseGases.X (groupedIdx M n' n'') =>
            ∫ y in Submission.BoseGases.abox n' ℓ,
              (Φ (Submission.BoseGases.mergeBlock n' (groupedIdx M n' n'') (y, w))) ^ 2)
          (Submission.BoseGases.abox (groupedIdx M n' n'') ℓ) volume :=
        hprodG.integral_prod_right
      have hmass2 : IntegrableOn (fun y : Submission.BoseGases.X n' =>
            ∫ w in Submission.BoseGases.abox (groupedIdx M n' n'') ℓ,
              (Φ (Submission.BoseGases.mergeBlock n' (groupedIdx M n' n'') (y, w))) ^ 2)
          (Submission.BoseGases.abox n' ℓ) volume :=
        hprodG.integral_prod_left
      -- integrability of the two slice words
      have hS1 : IntegrableOn
          (fun w : Submission.BoseGases.X (groupedIdx M n' n'') =>
            Work.BoseFixB1.sbWord h μ u
              (fun y => Φ (Submission.BoseGases.mergeBlock
                n' (groupedIdx M n' n'') (y, w))))
          (Submission.BoseGases.abox (groupedIdx M n' n'') ℓ) volume := by
        have hkin := (Work.BoseFixB1B.sbKin_slice_slotSplit (v := v) h hv hv1 hvrad hR hv_supp
          hav hAdm u).int₁ (N1 := n') (N2 := groupedIdx M n' n'') Φ hΦ
        have hpot := (Work.BoseFixB1S.sbPot_slice_integrable_regime (v := v) h hv hv1 hvrad hR
          hv_supp hav hAdm hR16 hRχ u (N₁ := n') (N₂ := groupedIdx M n' n'') hΦ).1
        exact hkin.add hpot
      have hS2 : IntegrableOn
          (fun y : Submission.BoseGases.X n' =>
            Work.BoseFixB1.sbWord h μ u
              (fun w => Φ (Submission.BoseGases.mergeBlock
                n' (groupedIdx M n' n'') (y, w))))
          (Submission.BoseGases.abox n' ℓ) volume := by
        have hkin := (Work.BoseFixB1B.sbKin_slice_slotSplit (v := v) h hv hv1 hvrad hR hv_supp
          hav hAdm u).int₂ (N1 := n') (N2 := groupedIdx M n' n'') Φ hΦ
        have hpot := (Work.BoseFixB1S.sbPot_slice_integrable_regime (v := v) h hv hv1 hvrad hR
          hv_supp hav hAdm hR16 hRχ u (N₁ := n') (N₂ := groupedIdx M n' n'') hΦ).2
        exact hkin.add hpot
      -- the two integrated bounds against the two slice integrals of the grouping
      have hA : ((M : ℝ) * g1 + g2) *
            (∫ x in Submission.BoseGases.abox (n' + groupedIdx M n' n'') ℓ, (Φ x) ^ 2)
          ≤ ∫ y in Submission.BoseGases.abox n' ℓ,
              Work.BoseFixB1.sbWord h μ u
                (fun w => Φ (Submission.BoseGases.mergeBlock
                  n' (groupedIdx M n' n'') (y, w))) := by
        have hI2 : IntegrableOn (fun y : Submission.BoseGases.X n' =>
            ((M : ℝ) * g1 + g2) *
              (∫ w in Submission.BoseGases.abox (groupedIdx M n' n'') ℓ,
                (Φ (Submission.BoseGases.mergeBlock
                  n' (groupedIdx M n' n'') (y, w))) ^ 2))
            (Submission.BoseGases.abox n' ℓ) volume := hmass2.const_mul _
        have hmono := integral_mono_ae (μ := volume.restrict (Submission.BoseGases.abox n' ℓ))
          hI2 hS2 hae2
        calc ((M : ℝ) * g1 + g2) *
              (∫ x in Submission.BoseGases.abox (n' + groupedIdx M n' n'') ℓ, (Φ x) ^ 2)
            = ∫ y in Submission.BoseGases.abox n' ℓ,
                ((M : ℝ) * g1 + g2) *
                  (∫ w in Submission.BoseGases.abox (groupedIdx M n' n'') ℓ,
                    (Φ (Submission.BoseGases.mergeBlock
                      n' (groupedIdx M n' n'') (y, w))) ^ 2) := by
              rw [integral_const_mul,
                aboxFubini_slice (N1 := n') (N2 := groupedIdx M n' n'') ℓ
                  (fun x : Submission.BoseGases.X (n' + groupedIdx M n' n'') =>
                    (Φ x) ^ 2) hGint]
          _ ≤ _ := hmono
      have hB : g1 * (∫ x in Submission.BoseGases.abox (n' + groupedIdx M n' n'') ℓ,
            (Φ x) ^ 2)
          ≤ ∫ w in Submission.BoseGases.abox (groupedIdx M n' n'') ℓ,
              Work.BoseFixB1.sbWord h μ u
                (fun y => Φ (Submission.BoseGases.mergeBlock
                  n' (groupedIdx M n' n'') (y, w))) := by
        have hI1 : IntegrableOn (fun w : Submission.BoseGases.X (groupedIdx M n' n'') =>
            g1 * (∫ y in Submission.BoseGases.abox n' ℓ,
              (Φ (Submission.BoseGases.mergeBlock
                n' (groupedIdx M n' n'') (y, w))) ^ 2))
            (Submission.BoseGases.abox (groupedIdx M n' n'') ℓ) volume :=
          hmass1.const_mul g1
        have hmono := integral_mono_ae (μ := volume.restrict
          (Submission.BoseGases.abox (groupedIdx M n' n'') ℓ)) hI1 hS1 hae1
        calc g1 * (∫ x in Submission.BoseGases.abox (n' + groupedIdx M n' n'') ℓ,
              (Φ x) ^ 2)
            = ∫ w in Submission.BoseGases.abox (groupedIdx M n' n'') ℓ,
                g1 * (∫ y in Submission.BoseGases.abox n' ℓ,
                  (Φ (Submission.BoseGases.mergeBlock
                    n' (groupedIdx M n' n'') (y, w))) ^ 2) := by
              rw [integral_const_mul,
                aboxFubini_slice_swapped (N1 := n') (N2 := groupedIdx M n' n'') ℓ
                  (fun x : Submission.BoseGases.X (n' + groupedIdx M n' n'') =>
                    (Φ x) ^ 2) hGint]
          _ ≤ _ := hmono
      -- the word-level grouping (FS Step E) at the sliding box
      -- (ascribed in terms of `ℓ`, so that `linarith` sees the same atoms as `hA`/`hB`)
      have hsuper : Work.BoseFixB1.sbWord h μ u Φ ≥
          (∫ w in Submission.BoseGases.abox (groupedIdx M n' n'') ℓ,
              Work.BoseFixB1.sbWord h μ u
                (fun y => Φ (Submission.BoseGases.mergeBlock
                  n' (groupedIdx M n' n'') (y, w))))
          + (∫ y in Submission.BoseGases.abox n' ℓ,
              Work.BoseFixB1.sbWord h μ u
                (fun w => Φ (Submission.BoseGases.mergeBlock
                  n' (groupedIdx M n' n'') (y, w)))) :=
        sbWord_slice_superadd_regime_holds (v := v) h hv hv1 hvrad hR hv_supp hav
          hAdm hR16 hRχ u (N₁ := n') (N₂ := groupedIdx M n' n'') (Φ := Φ) hΦ
      -- assemble: one peeled block contributes `g₁∫Φ²`, the induction hypothesis `g₂ + M g₁`
      have hcast : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      have hsplit : (((M : ℝ) + 1) * g1 + g2) *
            (∫ x in Submission.BoseGases.abox (n' + groupedIdx M n' n'') ℓ, (Φ x) ^ 2)
          = ((M : ℝ) * g1 + g2) *
              (∫ x in Submission.BoseGases.abox (n' + groupedIdx M n' n'') ℓ, (Φ x) ^ 2)
            + g1 * (∫ x in Submission.BoseGases.abox (n' + groupedIdx M n' n'') ℓ,
                (Φ x) ^ 2) := by
        ring
      rw [hsplit]
      linarith [hA, hB, hsuper]
  -- transport the statement's particle number `N = m·n' + n''` to the recursion's index
  have hN' : N = groupedIdx m n' n'' := by rw [hN, groupedIdx_eq]
  exact key m n' n'' N hN' Φ hΦ hin

end

end Work.BoseFixB1B
