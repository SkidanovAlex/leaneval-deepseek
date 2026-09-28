import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero
import Submission.Work.HP.Transf.Basic
import Submission.Work.HP.Transf.indep_of_le_finrank
import Submission.Work.HP.Transf.PieceRankDrop
import Submission.Work.HP.Transf.PiecePairOne
import Submission.Work.HP.Transf.PieceSection
import Submission.Work.HP.Transf.PieceCoset
import Submission.Work.HP.Transf.PieceDualNe

/-!
# Transference: `λ_r(L) · λ₁(dual L) ≤ C`

The `r`-th successive minimum of a discrete lattice `L ⊆ ℝ^ι` times the first successive minimum
of its dual lattice is bounded by a constant depending only on `ι` and `r`.

The proof is an induction on the rank `R` of `L` (established in `main_ind`), with constant
`trConst R`:

* if `λ₁(dual L) = 0` any `R` independent vectors of `L` work;
* otherwise pick a shortest dual vector `v` up to a factor `3/2`, normalized so that
  `⟪v, ·⟫ : L → ℤ` is onto (`exists_pairing_one`), say `⟪v,w⟫ = 1`, and let `L₀ = L ∩ v^⊥`;
* `dualLat L₀` is nonzero (`exists_dual_ne_zero`) and `λ₁(dualLat L₀) ≥ μ/4`
  (`lamR_dual_section`), so the induction hypothesis applied to `L₀` yields `R` independent
  vectors of `L₀` of norm at most `4 · trConst R / μ`;
* the unit coset of `L₀` in `L` contains a vector `w'` with
  `‖w'‖² ≤ (½ Σ‖g_j‖)² + 1/‖v‖²` (`exists_coset_short`), which is independent from the `g_j`.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace Work.HP.Transf

section Helpers

variable {ι : Type*} [Fintype ι]

/-- The section lattice `L ∩ v^⊥` of a discrete lattice is discrete. -/
lemma discreteTopology_secLat (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L] (v : ι → ℝ) :
    DiscreteTopology (secLat v L) :=
  DiscreteTopology.of_subset (s := (L : Set (ι → ℝ)))
    (t := ((secLat v L : Submodule ℤ (ι → ℝ)) : Set (ι → ℝ))) inferInstance
    (fun _ hy => (mem_secLat.mp hy).1)

/-- **The induction.** A discrete lattice `L` of rank `R` has `R` independent vectors of norm at
most `trConst R / λ₁(dual L)`. -/
theorem main_ind : ∀ (R : ℕ) (L : Submodule ℤ (ι → ℝ)), DiscreteTopology L → rkR L = R →
    ∃ f : Fin R → (ι → ℝ), (∀ j, f j ∈ L) ∧ LinearIndependent ℝ f ∧
      ∀ j, rNorm (f j) * lamR (dualLat L) 1 ≤ trConst R := by
  intro R
  induction R with
  | zero =>
      intro L _ _
      exact ⟨fun j => j.elim0, fun j => j.elim0, linearIndependent_empty_type, fun j => j.elim0⟩
  | succ R ih =>
      intro L hL hrank
      haveI : DiscreteTopology L := hL
      set μ : ℝ := lamR (dualLat L) 1 with hμdef
      by_cases hμ : μ = 0
      · obtain ⟨f, hfL, hfLI⟩ := indep_of_le_finrank L (k := R + 1) (by rw [hrank])
        exact ⟨f, hfL, hfLI, fun j => by
          rw [hμ, mul_zero]
          exact le_of_lt (trConst_pos _)⟩
      · have hμpos : 0 < μ := lt_of_le_of_ne (lamR_nonneg _ _) (Ne.symm hμ)
        have hex : ∃ v ∈ dualLat L, v ≠ 0 := exists_ne_zero_of_lamR_ne_zero _ hμ
        obtain ⟨v, hv, hv0, hvb⟩ :=
          exists_norm_le_of_lamR_lt (dualLat L) hex (c := 3 / 2 * μ) (by linarith)
        obtain ⟨w, hwL, hvw⟩ := exists_pairing_one L v hv hv0 μ hμdef.symm hμpos hvb
        have hrd : rkR (secLat v L) = R := by
          have h := finrank_span_secLat L v w hv hwL hvw
          change rkR (secLat v L) + 1 = rkR L at h
          rw [hrank] at h
          omega
        have hL0 : DiscreteTopology (secLat v L) := discreteTopology_secLat L v
        obtain ⟨g, hgL0, hgli, hgb⟩ := ih (secLat v L) hL0 hrd
        -- the `g j` span the real span of the section
        have hspan_eq : Submodule.span ℝ (Set.range g)
            = Submodule.span ℝ ((secLat v L : Submodule ℤ (ι → ℝ)) : Set (ι → ℝ)) := by
          have hle : Submodule.span ℝ (Set.range g)
              ≤ Submodule.span ℝ ((secLat v L : Submodule ℤ (ι → ℝ)) : Set (ι → ℝ)) :=
            Submodule.span_mono (Set.range_subset_iff.mpr hgL0)
          refine le_antisymm hle ?_
          refine ((Submodule.eq_of_le_of_finrank_eq hle ?_).ge)
          have h1 : Module.finrank ℝ (Submodule.span ℝ (Set.range g)) = R := by
            rw [finrank_span_eq_card hgli, Fintype.card_fin]
          have h2 : Module.finrank ℝ
              (Submodule.span ℝ ((secLat v L : Submodule ℤ (ι → ℝ)) : Set (ι → ℝ))) = R := by
            rw [← hrd, rkR]
          rw [h1, h2]
        -- bound on the norms of the `g j`
        have hgμ : ∀ j : Fin R, rNorm (g j) * μ ≤ 4 * trConst R := by
          intro j
          rcases R with _ | R'
          · exact j.elim0
          · haveI : DiscreteTopology (secLat v L) := hL0
            have hne0 : ∃ u ∈ dualLat (secLat v L), u ≠ 0 := by
              refine exists_dual_ne_zero (secLat v L) ?_
              rw [hrd]
              omega
            have h4 : μ / 4 ≤ lamR (dualLat (secLat v L)) 1 :=
              lamR_dual_section L v w hv hv0 hwL hvw μ hμdef.symm hvb hne0
            have h9 := hgb j
            have hg0 : 0 ≤ rNorm (g j) := rNorm_nonneg _
            nlinarith [h4, h9, hg0]
        have hsum_g : ∑ j, rNorm (g j) ≤ (R : ℝ) * (4 * trConst R / μ) := by
          calc ∑ j, rNorm (g j) ≤ ∑ _j : Fin R, (4 * trConst R / μ) :=
                Finset.sum_le_sum fun j _ => (le_div_iff₀ hμpos).mpr (hgμ j)
            _ = (R : ℝ) * (4 * trConst R / μ) := by simp
        obtain ⟨w', hw'L, hvw', hw'norm⟩ :=
          exists_coset_short L v w hv hwL hvw R g hgL0 hgli hspan_eq
        have hvμ : μ ≤ rNorm v := hμdef.trans_le (lamR_le_rNorm _ hv hv0)
        -- norm bound for the coset vector
        have hw'bound : rNorm w' * μ ≤ 2 * (R : ℝ) * trConst R + 1 := by
          have hμne : μ ≠ 0 := ne_of_gt hμpos
          have hμ2 : (0 : ℝ) < μ ^ 2 := pow_pos hμpos 2
          have hhalf : (∑ j, rNorm (g j)) / 2 ≤ ((R : ℝ) * (4 * trConst R / μ)) / 2 := by linarith
          have hsq1 : ((∑ j, rNorm (g j)) / 2) ^ 2
              ≤ (((R : ℝ) * (4 * trConst R / μ)) / 2) ^ 2 := by
            have h0 : 0 ≤ (∑ j, rNorm (g j)) / 2 :=
              div_nonneg (Finset.sum_nonneg fun j _ => rNorm_nonneg _) (by norm_num)
            have h1 := mul_self_le_mul_self h0 hhalf
            simpa only [pow_two] using h1
          have hvinv : 1 / rNorm v ^ 2 ≤ 1 / μ ^ 2 := by
            refine one_div_le_one_div_of_le (by positivity) ?_
            nlinarith [hvμ, hμpos]
          have hb : rNorm w' ^ 2 ≤ (((R : ℝ) * (4 * trConst R / μ)) / 2) ^ 2 + 1 / μ ^ 2 :=
            hw'norm.trans (add_le_add hsq1 hvinv)
          have hmul := mul_le_mul_of_nonneg_right hb (le_of_lt hμ2)
          have hone : (1 / μ ^ 2) * μ ^ 2 = 1 := by field_simp
          have hmain : (rNorm w' * μ) ^ 2
              ≤ (2 * (R : ℝ) * trConst R) ^ 2 + 1 := by
            have h1 : (rNorm w' * μ) ^ 2 = rNorm w' ^ 2 * μ ^ 2 := by ring
            have h2 : (((R : ℝ) * (4 * trConst R / μ)) / 2) ^ 2 * μ ^ 2
                = (2 * (R : ℝ) * trConst R) ^ 2 := by
              field_simp
              ring
            nlinarith [hmul, hone, h1, h2]
          have hfin : (rNorm w' * μ) ^ 2 ≤ (2 * (R : ℝ) * trConst R + 1) ^ 2 := by
            have h1 := trConst_pos R
            have h2 : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg R
            nlinarith [hmain, sq_nonneg (2 * (R : ℝ) * trConst R)]
          have hsqle := sq_le_sq.mp hfin
          have hnn : 0 ≤ rNorm w' * μ := mul_nonneg (rNorm_nonneg _) (le_of_lt hμpos)
          have hrhs : 0 ≤ 2 * (R : ℝ) * trConst R + 1 := by
            have h1 := trConst_pos R
            have h2 : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg R
            nlinarith
          rwa [abs_of_nonneg hnn, abs_of_nonneg hrhs] at hsqle
        have hw'le : rNorm w' * μ ≤ trConst (R + 1) := by
          refine hw'bound.trans ?_
          rw [trConst_succ]
          have h1 := trConst_pos R
          have h2 : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg R
          nlinarith
        -- assemble
        refine ⟨Fin.snoc g w', ?_, ?_, ?_⟩
        · intro j
          rcases Fin.eq_castSucc_or_eq_last j with ⟨m, rfl⟩ | rfl
          · simpa using (mem_secLat.mp (hgL0 m)).1
          · simpa using hw'L
        · refine LinearIndependent.finSnoc hgli ?_
          intro hmem
          have hle : Submodule.span ℝ (Set.range g) ≤ (dotRL v).ker := by
            rw [hspan_eq, Submodule.span_le]
            intro y hy
            exact LinearMap.mem_ker.mpr hy.2
          have h0 : dotR v w' = 0 := hle hmem
          rw [hvw'] at h0
          norm_num at h0
        · intro j
          rcases Fin.eq_castSucc_or_eq_last j with ⟨m, rfl⟩ | rfl
          · simpa using (hgμ m).trans (four_trConst_le R)
          · simpa using hw'le

end Helpers

/-- **Mahler transference, elementary form.** For every `r` there is `C > 0` such that every
discrete `ℤ`-submodule `L ⊆ ℝ^ι` of rank at least `r` has `r` linearly independent vectors of
norm at most `C / λ₁(dual L)`. -/
theorem lamR_dual_le {ι : Type*} [Fintype ι] (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : Submodule ℤ (ι → ℝ)), DiscreteTopology L →
      r ≤ Module.finrank ℝ (Submodule.span ℝ (L : Set (ι → ℝ))) →
      ∃ f : Fin r → (ι → ℝ), (∀ j, f j ∈ L) ∧ LinearIndependent ℝ f ∧
        ∀ j, rNorm (f j) * lamR (dualLat L) 1 ≤ C := by
  refine ⟨trConst (Fintype.card ι), trConst_pos _, fun L hL hr => ?_⟩
  obtain ⟨g, hgL, hgli, hgb⟩ := main_ind (rkR L) L hL rfl
  exact ⟨fun j => g (Fin.castLE hr j), fun j => hgL _,
    hgli.comp _ (Fin.castLE_injective hr), fun j => (hgb _).trans (trConst_mono (rkR_le_card L))⟩

end Work.HP.Transf
