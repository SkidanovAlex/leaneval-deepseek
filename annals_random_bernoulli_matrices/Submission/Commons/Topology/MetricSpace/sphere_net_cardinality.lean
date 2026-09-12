import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Order.CompletePartialOrder

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Metric
open scoped ENNReal

namespace Commons.Topology.MetricSpace

-- ============================================================
-- Helper 1: measure core for Finsets
-- ============================================================
lemma sphere_net_cardinality_finset_le (d : ℕ) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (s : Finset (EuclideanSpace ℝ (Fin d)))
    (hs : ∀ c ∈ s, ‖c‖ = 1)
    (hsep : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → ε ≤ ‖c - d‖) :
    (s.card : ℝ) ≤ (3 / ε) ^ d := by
  classical
  let μ : Measure (EuclideanSpace ℝ (Fin d)) := volume
  let δ : ℝ := ε / 2
  let ρ : ℝ := 1 + ε / 2
  have hδpos : 0 < δ := by dsimp [δ]; linarith
  have hρpos : 0 < ρ := by dsimp [ρ]; linarith
  set A := ⋃ c ∈ s, ball (c : EuclideanSpace ℝ (Fin d)) δ with hA
  have D : (s : Set (EuclideanSpace ℝ (Fin d))).PairwiseDisjoint
      (fun c : EuclideanSpace ℝ (Fin d) => ball c δ) := by
    intro c hc d hd hcd
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    have hsepcd := hsep c hc d hd hcd
    dsimp [δ] at hsepcd ⊢
    linarith
  have A_subset : A ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) ρ := by
    refine iUnion₂_subset fun c hc => ?_
    apply ball_subset_ball'
    calc
      δ + dist c 0 ≤ δ + 1 := by
        rw [dist_zero_right]
        have hc1 : ‖c‖ = 1 := hs c hc
        linarith
      _ = ρ := by dsimp [ρ, δ]; ring
  have I :
      (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin d))) *
          μ (ball 0 1) ≤
        ENNReal.ofReal (ρ ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin d))) * μ (ball 0 1) := by
    calc
      (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin d))) *
          μ (ball 0 1) = μ A := by
        rw [hA, measure_biUnion_finset D fun c _ => measurableSet_ball]
        simp only [μ.addHaar_ball_of_pos _ hδpos]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball (0 : EuclideanSpace ℝ (Fin d)) ρ) := measure_mono A_subset
      _ = ENNReal.ofReal (ρ ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin d))) * μ (ball 0 1) := by
        simp only [μ.addHaar_ball_of_pos _ hρpos]
  have J :
      (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin d))) ≤
        ENNReal.ofReal (ρ ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin d))) :=
    (ENNReal.mul_le_mul_iff_left (measure_ball_pos _ _ zero_lt_one).ne' measure_ball_lt_top.ne).1 I
  have hfinrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := by simp
  have hδnonneg : 0 ≤ δ ^ d := pow_nonneg (le_of_lt hδpos) d
  have hρnonneg : 0 ≤ ρ ^ d := pow_nonneg (le_of_lt hρpos) d
  have J' : (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ d) ≤ ENNReal.ofReal (ρ ^ d) := by
    simpa [hfinrank] using J
  have hto : ((s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ d)).toReal ≤ ρ ^ d := by
    exact ENNReal.toReal_le_of_le_ofReal hρnonneg J'
  have h1 : (s.card : ℝ) * (δ ^ d) ≤ ρ ^ d := by
    simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hδnonneg] using hto
  have hδpow : 0 < δ ^ d := pow_pos hδpos d
  have h2 : (s.card : ℝ) ≤ ρ ^ d / δ ^ d := by
    exact (le_div_iff₀ hδpow).mpr h1
  have hle2 : (2 : ℝ) / ε + 1 ≤ 3 / ε := by
    rw [le_div_iff₀ hε0]
    field_simp [hε0.ne']
    nlinarith [hε1]
  calc
    (s.card : ℝ) ≤ (ρ / δ) ^ d := by
      rwa [← div_pow] at h2
    _ ≤ (3 / ε) ^ d := by
      have hbase : ρ / δ = (2 : ℝ) / ε + 1 := by
        dsimp [ρ, δ]
        field_simp [hε0.ne']
      rw [hbase]
      exact pow_le_pow_left₀ (by positivity) hle2 d

-- ============================================================
-- Helper 2: Set version of the bound
-- ============================================================
lemma sphere_net_cardinality_finite_le (d : ℕ) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (T : Set (EuclideanSpace ℝ (Fin d))) (hT : T.Finite)
    (hs : ∀ x ∈ T, ‖x‖ = 1)
    (hsep : ∀ ⦃x : EuclideanSpace ℝ (Fin d)⦄, x ∈ T → ∀ ⦃y : EuclideanSpace ℝ (Fin d)⦄,
      y ∈ T → x ≠ y → ε ≤ ‖x - y‖) :
    (T.ncard : ℝ) ≤ (3 / ε) ^ d := by
  classical
  let A : Finset (EuclideanSpace ℝ (Fin d)) := hT.toFinset
  have hAcard : T.ncard = A.card := by
    dsimp [A]
    exact Set.ncard_eq_toFinset_card T hT
  have hfin := sphere_net_cardinality_finset_le d ε hε0 hε1 A
    (fun c hc => hs c (by simpa [A] using hc))
    (fun c hc d hd hcd => hsep (by simpa [A] using hc) (by simpa [A] using hd) hcd)
  rwa [← hAcard] at hfin

-- ============================================================
-- Main theorem
-- ============================================================
theorem sphere_net_cardinality :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (d : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 →
        ∃ S : Set (EuclideanSpace ℝ (Fin d)),
          S.Finite ∧
          (∀ x : EuclideanSpace ℝ (Fin d), x ∈ S → ‖x‖ = 1) ∧
          (∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ = 1 → ∃ x ∈ S, ‖y - x‖ ≤ ε) ∧
          (S.ncard : ℝ) ≤ (C / ε) ^ d := by
  classical
  refine ⟨3, by norm_num, ?_⟩
  intro d ε hε0 hε1
  let E := EuclideanSpace ℝ (Fin d)
  let sph : Set E := {y : E | ‖y‖ = 1}
  let Fam : Set (Set E) :=
    {A : Set E | A ⊆ sph ∧
      ∀ ⦃x : E⦄, x ∈ A → ∀ ⦃y : E⦄, y ∈ A → x ≠ y → ε ≤ ‖x - y‖}
  have hub : ∀ c : Set (Set E), c ⊆ Fam → IsChain (· ⊆ ·) c →
      ∃ ub ∈ Fam, ∀ s ∈ c, s ⊆ ub := by
    intro c hcFam hchain
    refine ⟨⋃₀ c, ?_, ?_⟩
    · change (⋃₀ c) ⊆ sph ∧
        ∀ ⦃x : E⦄, x ∈ ⋃₀ c → ∀ ⦃y : E⦄, y ∈ ⋃₀ c → x ≠ y → ε ≤ ‖x - y‖
      constructor
      · intro x hx
        rcases hx with ⟨A, hAc, hxA⟩
        have hAFam : A ∈ Fam := hcFam hAc
        have hA_pair : A ⊆ sph ∧
            ∀ ⦃x : E⦄, x ∈ A → ∀ ⦃y : E⦄, y ∈ A → x ≠ y → ε ≤ ‖x - y‖ := by
          simpa [Fam] using hAFam
        exact hA_pair.1 hxA
      · intro x hx y hy hxy
        rcases hx with ⟨Ax, hAxc, hxAx⟩
        rcases hy with ⟨Ay, hAyc, hyAy⟩
        have hAxFam : Ax ∈ Fam := hcFam hAxc
        have hAyFam : Ay ∈ Fam := hcFam hAyc
        have hAx_pair : Ax ⊆ sph ∧
            ∀ ⦃x : E⦄, x ∈ Ax → ∀ ⦃y : E⦄, y ∈ Ax → x ≠ y → ε ≤ ‖x - y‖ := by
          simpa [Fam] using hAxFam
        have hAy_pair : Ay ⊆ sph ∧
            ∀ ⦃x : E⦄, x ∈ Ay → ∀ ⦃y : E⦄, y ∈ Ay → x ≠ y → ε ≤ ‖x - y‖ := by
          simpa [Fam] using hAyFam
        by_cases heq : Ax = Ay
        · subst Ay
          exact hAx_pair.2 hxAx hyAy hxy
        · rcases hchain hAxc hAyc heq with hlt | hlt
          · -- Ax ⊆ Ay
            exact hAy_pair.2 (hlt hxAx) hyAy hxy
          · -- Ay ⊆ Ax
            exact hAx_pair.2 hxAx (hlt hyAy) hxy
    · intro s hs
      exact subset_sUnion_of_mem hs
  rcases zorn_subset Fam hub with ⟨S, hS⟩
  -- hS : Maximal (· ∈ Fam) S
  have hS_Fam : S ∈ Fam := hS.1
  have hS_mem : S ⊆ sph ∧
      ∀ ⦃x : E⦄, x ∈ S → ∀ ⦃y : E⦄, y ∈ S → x ≠ y → ε ≤ ‖x - y‖ := by
    simpa [Fam] using hS_Fam
  have hS_sph : S ⊆ sph := hS_mem.1
  have hS_sep : ∀ ⦃x : E⦄, x ∈ S → ∀ ⦃y : E⦄, y ∈ S → x ≠ y → ε ≤ ‖x - y‖ := hS_mem.2
  have hS_sphere : ∀ x : EuclideanSpace ℝ (Fin d), x ∈ S → ‖x‖ = 1 := by
    intro x hx
    exact hS_sph hx
  have hcover : ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ = 1 → ∃ x ∈ S, ‖y - x‖ ≤ ε := by
    intro y hy
    by_cases hyS : y ∈ S
    · refine ⟨y, hyS, ?_⟩
      rw [sub_self, norm_zero]
      exact le_of_lt hε0
    · by_contra hnone
      push Not at hnone
      have hsep_insert : ∀ ⦃x : E⦄, x ∈ insert y S → ∀ ⦃z : E⦄, z ∈ insert y S →
          x ≠ z → ε ≤ ‖x - z‖ := by
        intro x hx z hz hxz
        by_cases hxy : x = y
        · subst x
          have hzS : z ∈ S := by
            rcases Set.mem_insert_iff.mp hz with rfl | hzS
            · exact (hxz rfl).elim
            · exact hzS
          exact le_of_lt (hnone z hzS)
        · have hxS : x ∈ S := by
            rcases Set.mem_insert_iff.mp hx with rfl | hxS
            · exact (hxy rfl).elim
            · exact hxS
          by_cases hzy : z = y
          · subst z
            rw [norm_sub_rev]
            exact le_of_lt (hnone x hxS)
          · have hzS : z ∈ S := by
              rcases Set.mem_insert_iff.mp hz with rfl | hzS
              · exact (hzy rfl).elim
              · exact hzS
            exact hS_sep hxS hzS hxz
      have hsub_insert : insert y S ⊆ sph := by
        intro x hx
        rcases Set.mem_insert_iff.mp hx with rfl | hxS
        · exact hy
        · exact hS_sph hxS
      have hinsertFam : insert y S ∈ Fam := by
        change insert y S ⊆ sph ∧
          ∀ ⦃x : E⦄, x ∈ insert y S → ∀ ⦃z : E⦄, z ∈ insert y S → x ≠ z → ε ≤ ‖x - z‖
        exact ⟨hsub_insert, hsep_insert⟩
      have hmax : insert y S ⊆ S := hS.2 hinsertFam (subset_insert y S)
      have hyS' : y ∈ S := hmax (by simp)
      exact hyS hyS'
  -- finiteness / bound
  have hfinite_bound : ∀ T : Set E, T.Finite → T ⊆ S → (T.ncard : ℝ) ≤ (3 / ε) ^ d := by
    intro T hTfin hTS
    exact sphere_net_cardinality_finite_le d ε hε0 hε1 T hTfin
      (fun x hx => hS_sphere x (hTS hx))
      (fun ⦃x⦄ hx ⦃y⦄ hy hxy => hS_sep (hTS hx) (hTS hy) hxy)
  by_cases hS_fin : S.Finite
  · have hbound : (S.ncard : ℝ) ≤ (3 / ε) ^ d := hfinite_bound S hS_fin (subset_rfl)
    refine ⟨S, hS_fin, ?_, ?_, ?_⟩
    · intro x hx
      exact hS_sphere x hx
    · intro y hy
      exact hcover y hy
    · simpa using hbound
  · exfalso
    rcases exists_nat_gt ((3 / ε) ^ d) with ⟨M, hM⟩
    have hSinf : S.Infinite := by simpa using hS_fin  -- hS_fin : ¬ S.Finite; Infinite probably = ¬Finite
    rcases (Set.Infinite.exists_subset_ncard_eq hSinf M) with ⟨T, hTS, hTfin, hTcard⟩
    have hTbound : (T.ncard : ℝ) ≤ (3 / ε) ^ d := hfinite_bound T hTfin hTS
    have hc1 : (M : ℝ) ≤ (3 / ε) ^ d := by
      rwa [hTcard] at hTbound
    linarith

end Commons.Topology.MetricSpace