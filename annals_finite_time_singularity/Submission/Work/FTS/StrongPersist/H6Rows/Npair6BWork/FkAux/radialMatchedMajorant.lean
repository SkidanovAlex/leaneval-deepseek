import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux.radialHkIntegrand_majorant_cd6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux.radial_zslot_le_cd6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux.radial_mslot_le_cd6

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
## The proof

For a radial factor `r` and an arbitrary `g`, assuming the two Leibniz rules for the
product `(z,θ) ↦ r z · g z θ`, the level-`6` weighted integrand of the product is bounded
at a point `(z,θ)` by a universal constant times the **matched** radial sum

`∑_{b ≤ 6} (D_z^b r z)² · HkIntegrand α (6-b) g z θ`,

in which each radial derivative is paired with the *remaining* budget `6 - b` of
derivatives of `g`.  The proof is a two-slot Cauchy–Schwarz: the pure `D_z`-slots and the
mixed slots are each expanded by their Leibniz rule, bounded termwise by the corresponding
slot of `HkIntegrand α (6-b) g` (`sq_le_HkIntegrand_z` / `sq_le_HkIntegrand_mixed` at level
`6 - b`), and then the radial factors are collected into the matched sum.
-/

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

set_option maxHeartbeats 1600000

/-- Every binomial coefficient `n.choose k` with `n ≤ 6` is at most `2^6 = 64`. -/
private theorem choose_le_64 {n k : ℕ} (hn : n ≤ 6) : (n.choose k : ℝ) ≤ 64 := by
  have h2 : 2 ^ n ≤ 64 := by
    calc 2 ^ n ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hn
      _ = 64 := by norm_num
  exact_mod_cast le_trans (Nat.choose_le_two_pow n k) h2

/-- The arithmetic tail: `k ≤ 7` and `S ≥ 0` give `k · (4096 S) ≤ 200704 S`. -/
private theorem arith_le {k S : ℝ} (hk : k ≤ 7) (hS : 0 ≤ S) :
    k * (4096 * S) ≤ 200704 * S := by
  have h1 : k * S ≤ 7 * S := mul_le_mul_of_nonneg_right hk hS
  nlinarith [h1]

/-- The **pure `D_z`-slot** of the matched majorant: for `i ≤ 6`, the squared weighted
`D_z^i` of the product is bounded by `200704` times the matched radial sum. -/
private theorem zslot_matched {α : ℝ} {r : ℝ → ℝ} {g : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hDz : ∀ j : ℕ, j ≤ 6 →
      Work.Spaces.DzIter j (fun z θ => r z * g z θ) z θ
        = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
            * (Work.Elliptic.DzdIter b r z * Work.Spaces.DzIter (j - b) g z θ))
    (i : ℕ) (hi : i ≤ 6) :
    (Work.Spaces.DzIter i (fun z θ => r z * g z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ 200704 * (∑ b ∈ Finset.range 7, (Work.Elliptic.DzdIter b r z) ^ 2
            * Work.Spaces.HkIntegrand α (6 - b) g z θ) := by
  set S : ℝ := ∑ b ∈ Finset.range 7, (Work.Elliptic.DzdIter b r z) ^ 2
        * Work.Spaces.HkIntegrand α (6 - b) g z θ with hSdef
  have hSnn : 0 ≤ S := by
    rw [hSdef]
    exact Finset.sum_nonneg fun b _ => mul_nonneg (sq_nonneg _)
      (Work.Spaces.HkIntegrand_nonneg α (6 - b) g z θ)
  set Y : ℕ → ℝ := fun b => (i.choose b : ℝ)
      * (Work.Elliptic.DzdIter b r z
          * (Work.Spaces.DzIter (i - b) g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))) with hY
  have hexp : Work.Spaces.DzIter i (fun z θ => r z * g z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      = ∑ b ∈ Finset.range (i + 1), Y b := by
    rw [hDz i hi, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by simp only [hY]; ring
  rw [hexp]
  have hcs : (∑ b ∈ Finset.range (i + 1), Y b) ^ 2
      ≤ ((i : ℝ) + 1) * ∑ b ∈ Finset.range (i + 1), (Y b) ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (i + 1)) (fun _ : ℕ => (1 : ℝ)) Y
    have hcard : ((Finset.range (i + 1)).card : ℝ) = (i : ℝ) + 1 := by
      rw [Finset.card_range]; push_cast; ring
    simpa [hcard] using h
  have hper : ∀ b ∈ Finset.range (i + 1), (Y b) ^ 2 ≤ 4096 * ((Work.Elliptic.DzdIter b r z) ^ 2
        * Work.Spaces.HkIntegrand α (6 - b) g z θ) := by
    intro b hb
    rw [Finset.mem_range] at hb
    have hsub : i - b ≤ 6 - b := by omega
    have hch : (i.choose b : ℝ) ^ 2 ≤ 64 ^ 2 :=
      pow_le_pow_left₀ (by positivity) (choose_le_64 (by omega)) 2
    have hYsq : (Y b) ^ 2 = (i.choose b : ℝ) ^ 2 * (Work.Elliptic.DzdIter b r z) ^ 2
        * (Work.Spaces.DzIter (i - b) g z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      simp only [hY]; ring
    rw [hYsq]
    calc (i.choose b : ℝ) ^ 2 * (Work.Elliptic.DzdIter b r z) ^ 2
          * (Work.Spaces.DzIter (i - b) g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ (64 ^ 2 * (Work.Elliptic.DzdIter b r z) ^ 2) * Work.Spaces.HkIntegrand α (6 - b) g z θ :=
          mul_le_mul (mul_le_mul hch le_rfl (sq_nonneg _) (sq_nonneg _))
            (Work.Spaces.sq_le_HkIntegrand_z α (6 - b) g z θ (i - b) hsub)
            (sq_nonneg _) (by positivity)
      _ = 4096 * ((Work.Elliptic.DzdIter b r z) ^ 2
            * Work.Spaces.HkIntegrand α (6 - b) g z θ) := by ring
  have hsum : ∑ b ∈ Finset.range (i + 1), (Y b) ^ 2 ≤ 4096 * S := by
    rw [hSdef, Finset.mul_sum]
    calc ∑ b ∈ Finset.range (i + 1), (Y b) ^ 2
        ≤ ∑ b ∈ Finset.range (i + 1), 4096 * ((Work.Elliptic.DzdIter b r z) ^ 2
            * Work.Spaces.HkIntegrand α (6 - b) g z θ) := Finset.sum_le_sum hper
      _ ≤ ∑ b ∈ Finset.range 7, 4096 * ((Work.Elliptic.DzdIter b r z) ^ 2
            * Work.Spaces.HkIntegrand α (6 - b) g z θ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
            (fun b _ _ => mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg _)
              (Work.Spaces.HkIntegrand_nonneg α (6 - b) g z θ)))
  have hk : (i : ℝ) + 1 ≤ 7 := by
    have : i + 1 ≤ 7 := by omega
    exact_mod_cast this
  calc (∑ b ∈ Finset.range (i + 1), Y b) ^ 2
      ≤ ((i : ℝ) + 1) * ∑ b ∈ Finset.range (i + 1), (Y b) ^ 2 := hcs
    _ ≤ ((i : ℝ) + 1) * (4096 * S) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ 200704 * S := arith_le hk hSnn

/-- The **mixed slot** of the matched majorant: for `1 ≤ i`, `i + j ≤ 6`, the squared
weighted `D_z^j D_θ^i` of the product is bounded by `200704` times the matched radial
sum. -/
private theorem mslot_matched {α : ℝ} {r : ℝ → ℝ} {g : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hMx : ∀ j i : ℕ, 1 ≤ i → i + j ≤ 6 →
      Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ
        = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
            * (Work.Elliptic.DzdIter b r z * Work.Spaces.mixed (j - b) i g z θ))
    (i j : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 6) :
    (Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ 200704 * (∑ b ∈ Finset.range 7, (Work.Elliptic.DzdIter b r z) ^ 2
            * Work.Spaces.HkIntegrand α (6 - b) g z θ) := by
  set S : ℝ := ∑ b ∈ Finset.range 7, (Work.Elliptic.DzdIter b r z) ^ 2
        * Work.Spaces.HkIntegrand α (6 - b) g z θ with hSdef
  have hSnn : 0 ≤ S := by
    rw [hSdef]
    exact Finset.sum_nonneg fun b _ => mul_nonneg (sq_nonneg _)
      (Work.Spaces.HkIntegrand_nonneg α (6 - b) g z θ)
  set Y : ℕ → ℝ := fun b => (j.choose b : ℝ)
      * (Work.Elliptic.DzdIter b r z * (Work.Spaces.mixed (j - b) i g z θ * Work.Spaces.Wt α z θ))
      with hY
  have hexp : Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ * Work.Spaces.Wt α z θ
      = ∑ b ∈ Finset.range (j + 1), Y b := by
    rw [hMx j i hi hij, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by simp only [hY]; ring
  rw [hexp]
  have hcs : (∑ b ∈ Finset.range (j + 1), Y b) ^ 2
      ≤ ((j : ℝ) + 1) * ∑ b ∈ Finset.range (j + 1), (Y b) ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (j + 1)) (fun _ : ℕ => (1 : ℝ)) Y
    have hcard : ((Finset.range (j + 1)).card : ℝ) = (j : ℝ) + 1 := by
      rw [Finset.card_range]; push_cast; ring
    simpa [hcard] using h
  have hper : ∀ b ∈ Finset.range (j + 1), (Y b) ^ 2 ≤ 4096 * ((Work.Elliptic.DzdIter b r z) ^ 2
        * Work.Spaces.HkIntegrand α (6 - b) g z θ) := by
    intro b hb
    rw [Finset.mem_range] at hb
    have hsub : i + (j - b) ≤ 6 - b := by omega
    have hch : (j.choose b : ℝ) ^ 2 ≤ 64 ^ 2 :=
      pow_le_pow_left₀ (by positivity) (choose_le_64 (by omega)) 2
    have hYsq : (Y b) ^ 2 = (j.choose b : ℝ) ^ 2 * (Work.Elliptic.DzdIter b r z) ^ 2
        * (Work.Spaces.mixed (j - b) i g z θ * Work.Spaces.Wt α z θ) ^ 2 := by
      simp only [hY]; ring
    rw [hYsq]
    calc (j.choose b : ℝ) ^ 2 * (Work.Elliptic.DzdIter b r z) ^ 2
          * (Work.Spaces.mixed (j - b) i g z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ (64 ^ 2 * (Work.Elliptic.DzdIter b r z) ^ 2) * Work.Spaces.HkIntegrand α (6 - b) g z θ :=
          mul_le_mul (mul_le_mul hch le_rfl (sq_nonneg _) (sq_nonneg _))
            (Work.Spaces.sq_le_HkIntegrand_mixed α (6 - b) g z θ i (j - b) hi hsub)
            (sq_nonneg _) (by positivity)
      _ = 4096 * ((Work.Elliptic.DzdIter b r z) ^ 2
            * Work.Spaces.HkIntegrand α (6 - b) g z θ) := by ring
  have hsum : ∑ b ∈ Finset.range (j + 1), (Y b) ^ 2 ≤ 4096 * S := by
    rw [hSdef, Finset.mul_sum]
    calc ∑ b ∈ Finset.range (j + 1), (Y b) ^ 2
        ≤ ∑ b ∈ Finset.range (j + 1), 4096 * ((Work.Elliptic.DzdIter b r z) ^ 2
            * Work.Spaces.HkIntegrand α (6 - b) g z θ) := Finset.sum_le_sum hper
      _ ≤ ∑ b ∈ Finset.range 7, 4096 * ((Work.Elliptic.DzdIter b r z) ^ 2
            * Work.Spaces.HkIntegrand α (6 - b) g z θ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
            (fun b _ _ => mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg _)
              (Work.Spaces.HkIntegrand_nonneg α (6 - b) g z θ)))
  have hk : (j : ℝ) + 1 ≤ 7 := by
    have : j + 1 ≤ 7 := by omega
    exact_mod_cast this
  calc (∑ b ∈ Finset.range (j + 1), Y b) ^ 2
      ≤ ((j : ℝ) + 1) * ∑ b ∈ Finset.range (j + 1), (Y b) ^ 2 := hcs
    _ ≤ ((j : ℝ) + 1) * (4096 * S) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ 200704 * S := arith_le hk hSnn

theorem radialMatchedMajorant :
    ∃ C : ℝ, 0 < C ∧ ∀ {α : ℝ} {r : ℝ → ℝ} {g : ℝ → ℝ → ℝ},
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → ∀ j : ℕ, j ≤ 6 →
        Work.Spaces.DzIter j (fun z θ => r z * g z θ) z θ
          = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
              * (Work.Elliptic.DzdIter b r z * Work.Spaces.DzIter (j - b) g z θ)) →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → ∀ j i : ℕ, 1 ≤ i → i + j ≤ 6 →
        Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ
          = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
              * (Work.Elliptic.DzdIter b r z * Work.Spaces.mixed (j - b) i g z θ)) →
      ∀ {z θ : ℝ}, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.HkIntegrand α 6 (fun z θ => r z * g z θ) z θ
        ≤ C * ∑ b ∈ Finset.range 7, (Work.Elliptic.DzdIter b r z) ^ 2
            * Work.Spaces.HkIntegrand α (6 - b) g z θ := by
  refine ⟨10 ^ 8, by norm_num, ?_⟩
  intro α r g hDz hMx z θ hz hθ0 hθ1
  -- the matched radial sum `S`
  set S : ℝ := ∑ b ∈ Finset.range 7, (Work.Elliptic.DzdIter b r z) ^ 2
        * Work.Spaces.HkIntegrand α (6 - b) g z θ with hSdef
  have hSnn : 0 ≤ S := by
    rw [hSdef]
    exact Finset.sum_nonneg fun b _ => mul_nonneg (sq_nonneg _)
      (Work.Spaces.HkIntegrand_nonneg α (6 - b) g z θ)
  -- decompose the level-`6` integrand into its two slot sums
  conv_lhs => simp only [Work.Spaces.HkIntegrand]
  -- ## the seven pure `D_z`-slots
  have hA : (∑ i ∈ Finset.range 7, (Work.Spaces.DzIter i (fun z θ => r z * g z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ 7 * (200704 * S) := by
    calc (∑ i ∈ Finset.range 7, (Work.Spaces.DzIter i (fun z θ => r z * g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ ∑ _i ∈ Finset.range 7, (200704 * S) :=
          Finset.sum_le_sum fun i hi =>
            zslot_matched (fun j hj => hDz z θ hz hθ0 hθ1 j hj) i (by
              have := Finset.mem_range.mp hi; omega)
      _ = 7 * (200704 * S) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  -- ## the (`≤ 49`) mixed slots
  have hB : (∑ i ∈ Finset.range 7, ∑ j ∈ Finset.range 7,
        (if 1 ≤ i ∧ i + j ≤ 6 then (Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ
          * Work.Spaces.Wt α z θ) ^ 2 else 0))
      ≤ 49 * (200704 * S) := by
    calc (∑ i ∈ Finset.range 7, ∑ j ∈ Finset.range 7,
          (if 1 ≤ i ∧ i + j ≤ 6 then (Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
        ≤ ∑ _i ∈ Finset.range 7, ∑ _j ∈ Finset.range 7, (200704 * S) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          by_cases hc : 1 ≤ i ∧ i + j ≤ 6
          · rw [ite_eq_left hc]
            exact mslot_matched (fun j i hi hij => hMx z θ hz hθ0 hθ1 j i hi hij) i j hc.1 hc.2
          · rw [ite_eq_right hc]
            exact mul_nonneg (by norm_num) hSnn
      _ = 49 * (200704 * S) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  -- ## the assembly
  have htot : 7 * (200704 * S) + 49 * (200704 * S) ≤ 10 ^ 8 * S := by
    nlinarith [hSnn]
  linarith [hA, hB, htot]

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
