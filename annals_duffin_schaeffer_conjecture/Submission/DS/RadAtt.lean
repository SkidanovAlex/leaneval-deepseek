import Submission.DS.CatlinDiv

open scoped Nat ENNReal NNReal
open Set
open DuffinSchaefferConjecture

/-!
# Sup-attainment for the rad-values under a uniform `ψ ≤ 1/2` bound

To lift a solution `(a, q)` of the `ξ`-inequality to a solution `(m, n)` of the
`ψ`-inequality (paper §2, direction `𝒞 ⊆ 𝒦`), we need, for every `q`, an actual
multiple `n` of `q` at which the supremum `rad ψ q = sup {ψ(n)/n : q ∣ n}` is
attained.
-/

namespace Submission.DS

open ENNReal

/-- If `ψ ≤ 1/2` everywhere then for every `q` the sup `rad ψ q` is attained at some
multiple `n` of `q`. -/
lemma rad_att {ψ : ℕ+ → ℝ≥0} (hle : ∀ q, ψ q ≤ (1 / 2 : ℝ≥0)) (q : ℕ+) :
    ∃ n : ℕ+, q ∣ n ∧ rad ψ q = (ψ n : ℝ≥0∞) / (n : ℝ≥0∞) := by
  classical
  let f : ℕ+ → ℝ≥0∞ := fun n => (ψ n : ℝ≥0∞) / (n : ℝ≥0∞)
  let S : Set ℝ≥0∞ := {r | ∃ n : ℕ+, q ∣ n ∧ r = f n}
  have hrad : rad ψ q = sSup S := rfl
  have hS_of_f : ∀ n : ℕ+, q ∣ n → f n ∈ S := by
    intro n hd
    exact ⟨n, hd, rfl⟩
  have hL : rad ψ q < ∞ := rad_lt_top_of_le_half hle q
  by_cases hL0 : rad ψ q = 0
  · -- The value at `n = q` is 0, so it attains the sup.
    have h1 : rad ψ q ≤ f q := by
      rw [hL0]
      exact bot_le
    have h2 : f q ≤ rad ψ q := by
      rw [hrad]
      exact le_sSup (hS_of_f q dvd_rfl)
    exact ⟨q, dvd_rfl, le_antisymm h1 h2⟩
  · -- `rad ψ q > 0`: cut off the tail below `rad/2` and take the maximum of the
    -- (finite!) set of multiples whose value is at least `rad/2`.
    have hLpos : 0 < rad ψ q := by
      exact lt_of_le_of_ne (by positivity : (0 : ℝ≥0∞) ≤ rad ψ q) (by intro h; exact hL0 h.symm)
    let t : ℝ≥0∞ := rad ψ q / 2
    have htpos : 0 < t := ENNReal.half_pos hL0
    have htlt : t < rad ψ q := ENNReal.half_lt_self hL0 (ne_of_lt hL)
    have ht_ne0 : t ≠ 0 := ne_of_gt htpos
    have ht_neT : t ≠ ∞ := ne_of_lt (lt_of_le_of_lt (le_of_lt htlt) hL)
    let half : ℝ≥0∞ := ((1 / 2 : ℝ≥0) : ℝ≥0∞)
    have hval_le_half_div : ∀ n : ℕ+, f n ≤ half / (n : ℝ≥0∞) := by
      intro n
      exact ENNReal.div_le_div (ENNReal.coe_le_coe.mpr (hle n)) le_rfl
    let F : Set ℕ+ := {n : ℕ+ | q ∣ n ∧ t ≤ f n}
    -- F is finite: multiples with a value ≥ t are bounded by `half / t`.
    have hF_bound : ∀ n : ℕ+, n ∈ F → (n : ℝ≥0∞) ≤ half / t := by
      intro n hnF
      have hd : q ∣ n := hnF.1
      have htle : t ≤ f n := hnF.2
      have hf : f n ≤ half / (n : ℝ≥0∞) := hval_le_half_div n
      have htle' : t ≤ half / (n : ℝ≥0∞) := le_trans htle hf
      have hn_ne0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (PNat.ne_zero n : (n : ℕ) ≠ 0)
      have hn_neT : (n : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top (n : ℕ)
      have htn : t * (n : ℝ≥0∞) ≤ half := by
        calc
          t * (n : ℝ≥0∞) ≤ (half / (n : ℝ≥0∞)) * (n : ℝ≥0∞) := by
            exact mul_le_mul_left htle' (n : ℝ≥0∞)
          _ = (half * (n : ℝ≥0∞)⁻¹) * (n : ℝ≥0∞) := by rfl
          _ = half * ((n : ℝ≥0∞)⁻¹ * (n : ℝ≥0∞)) := by rw [mul_assoc]
          _ = half * 1 := by rw [ENNReal.inv_mul_cancel hn_ne0 hn_neT]
          _ = half := by rw [mul_one]
      calc
        (n : ℝ≥0∞) = 1 * (n : ℝ≥0∞) := by rw [one_mul]
        _ = (t⁻¹ * t) * (n : ℝ≥0∞) := by rw [← ENNReal.inv_mul_cancel ht_ne0 ht_neT]
        _ = t⁻¹ * (t * (n : ℝ≥0∞)) := by rw [mul_assoc]
        _ ≤ t⁻¹ * half := by exact mul_le_mul_of_nonneg_left htn (by positivity)
        _ = half / t := by rw [div_eq_mul_inv, mul_comm]
    have hF_finite : F.Finite := by
      have hB : half / t < ∞ := by
        exact ENNReal.div_lt_top (by exact ENNReal.coe_ne_top) ht_ne0
      rcases ENNReal.exists_nat_gt (ne_of_lt hB) with ⟨N, hN⟩
      let T : Set ℕ+ := {n : ℕ+ | (n : ℕ) < N}
      have hT_finite : T.Finite := by
        refine (Set.finite_image_iff (Set.injOn_of_injective PNat.coe_injective (s := T))).1 ?_
        have himg : ((fun q : ℕ+ => (q : ℕ)) '' T) ⊆ {m : ℕ | m < N} := by
          intro m hm
          rcases hm with ⟨q, hq, rfl⟩
          exact hq
        exact (Set.finite_lt_nat N).subset himg
      refine hT_finite.subset ?_
      intro n hnF
      have hltB : (n : ℝ≥0∞) < (N : ℝ≥0∞) := lt_of_le_of_lt (hF_bound n hnF) hN
      exact_mod_cast hltB
    -- F is non-empty: otherwise every value is `< t < rad`, contradicting the sup.
    have hF_ne : F.Nonempty := by
      by_contra hne
      have hsup_le_t : sSup S ≤ t := by
        apply sSup_le
        intro r hr
        rcases hr with ⟨n, hd, rfl⟩
        have hnot : ¬ t ≤ f n := by
          intro htle
          exact hne ⟨n, hd, htle⟩
        exact le_of_lt (lt_of_not_ge hnot)
      have hle : rad ψ q ≤ t := by
        rw [hrad]
        exact hsup_le_t
      exact (not_le_of_gt htlt) hle
    -- Take the maximal element of the finite set F.
    let sF : Finset ℕ+ := hF_finite.toFinset
    have hsF_ne : sF.Nonempty := (hF_finite.toFinset_nonempty).mpr hF_ne
    rcases Finset.exists_max_image sF f hsF_ne with ⟨n0, hn0s, hmax⟩
    have hn0F : n0 ∈ F := (hF_finite.mem_toFinset).mp hn0s
    refine ⟨n0, hn0F.1, ?_⟩
    change rad ψ q = f n0
    apply le_antisymm
    · rw [hrad]
      apply sSup_le
      intro r hr
      rcases hr with ⟨n, hd, rfl⟩
      by_cases hmem : n ∈ F
      · have hns : n ∈ sF := (hF_finite.mem_toFinset).mpr hmem
        exact hmax n hns
      · have hnot : ¬ t ≤ f n := by
          intro htle
          exact hmem ⟨hd, htle⟩
        have hlt : f n < t := lt_of_not_ge hnot
        exact le_trans (le_of_lt hlt) hn0F.2
    · rw [hrad]
      exact le_sSup (hS_of_f n0 hn0F.1)

end Submission.DS
