import Mathlib
import Submission.Work.BMF.adi_all_defs
import Submission.Work.BMF.adi_count
import Submission.Work.BMF.bike_count_arc
import Submission.Work.BMF.arc_count_ge
import Submission.Work.BMF.primesIn_half_card_le_all
import Submission.Work.BMF.good_bike_aux
import Submission.Work.BMF.bikeSet_arith
import Submission.Work.BMF.adjQ_sum_lower

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Finset Real

variable {k : ℕ} {f : ℕ → ℂ} {c C X L P₁ P₂ : ℝ}

/-- The number of ordered `q`-adjacent pairs of vertices of the quadruple graph. -/
noncomputable def adjCount (D : QuadData k f c C X L P₁ P₂) (q : ℕ) : ℝ :=
  ∑ i : GVert D, ∑ j : GVert D, (if GAdjQ D q i j then (1 : ℝ) else 0)

lemma adjCount_nonneg (D : QuadData k f c C X L P₁ P₂) (q : ℕ) : 0 ≤ adjCount D q := by
  unfold adjCount
  refine Finset.sum_nonneg (fun i _ => ?_)
  refine Finset.sum_nonneg (fun j _ => ?_)
  split <;> norm_num

theorem bikeSet_sum_lower (k ℓ : ℕ) (hℓ : 2 ≤ ℓ) (heven : Even ℓ) :
    ∃ c₂₀ P₀ : ℝ, 0 < c₂₀ ∧ 0 < P₀ ∧
      ∀ (f : ℕ → ℂ) (c C X L P₁ P₂ : ℝ) (D : Work.BMF.QuadData k f c C X L P₁ P₂),
        P₀ ≤ P₁ → 0 < P₁ → 0 < c → 2 ≤ P₂ → 0 < L → 0 < X →
        8000 * P₁ ^ 2 < X / L → 3 ≤ X / L → X / L ≤ P₁ ^ (ℓ - 1) →
        (Fintype.card (Work.BMF.GVert D) : ℝ) ≤ X / L →
        c * Work.BMF.pi0 P₁ ^ 2 * (X / L) ≤ (D.edges.card : ℝ) →
        c₂₀ * c ^ (4 * ℓ + 2) * Work.BMF.pi0 P₂ * (Work.BMF.pi0 P₁ ^ 2) ^ (2 * ℓ + 1) / (X / L) ≤
          ∑ q ∈ Work.BMF.primesIn (P₂ / 2) P₂, ((Work.BMF.bikeSet D q ℓ).card : ℝ) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := primesIn_half_card_le_all
  refine ⟨1 / (2 * C₁ ^ (2 * ℓ)), 2, by positivity, by norm_num, ?_⟩
  intro f c C X L P₁ P₂ D hP₀ hP₁ hc hP₂ hL hX hbig hN3 hNle hcardV hEdges
  have hP₁2 : 2 ≤ P₁ := hP₀
  have hpi0₁ : 0 < pi0 P₁ := pi0_pos hP₁2
  have hpi0₂ : 0 < pi0 P₂ := pi0_pos hP₂
  have hNpos : 0 < X / L := by linarith
  have hB0nn : 0 ≤ c ^ 2 * pi0 P₂ * pi0 P₁ ^ 2 * (X / L) := by positivity
  -- positivity of the number of vertices
  have hcard_edges_pos : 0 < D.edges.card := by
    have h0 : (0:ℝ) < c * pi0 P₁ ^ 2 * (X / L) := by positivity
    have h1 : (0:ℝ) < (D.edges.card : ℝ) := lt_of_lt_of_le h0 hEdges
    exact_mod_cast h1
  obtain ⟨e0, he0⟩ := Finset.card_pos.mp hcard_edges_pos
  have hfam_ne : D.fam.Nonempty := ⟨e0.x₂, (D.geom e0 he0).x₂_mem⟩
  have hn_pos : (0:ℝ) < (Fintype.card (GVert D) : ℝ) := by
    rw [fintype_card_GVert]
    exact_mod_cast Finset.card_pos.mpr hfam_ne
  -- double-counting lower bound for `∑_q adjCount D q`
  have hBge : c ^ 2 * pi0 P₂ * pi0 P₁ ^ 2 * (X / L) ≤
      ∑ q ∈ primesIn (P₂ / 2) P₂, adjCount D q := by
    simpa only [adjCount] using adjQ_sum_lower D hc hP₁ hL hbig hP₂ hEdges
  have hB0pos : 0 < c ^ 2 * pi0 P₂ * pi0 P₁ ^ 2 * (X / L) := by positivity
  have hQpos : 0 < ((primesIn (P₂ / 2) P₂).card : ℝ) := by
    by_contra h
    have hcard0 : (primesIn (P₂ / 2) P₂).card = 0 := by
      have hle : (primesIn (P₂ / 2) P₂).card ≤ 0 := by
        exact_mod_cast (not_lt.mp h : ((primesIn (P₂ / 2) P₂).card : ℝ) ≤ 0)
      exact Nat.le_zero.mp hle
    have hemp : primesIn (P₂ / 2) P₂ = ∅ := Finset.card_eq_zero.mp hcard0
    have hz : (∑ q ∈ primesIn (P₂ / 2) P₂, adjCount D q) = 0 := by rw [hemp]; simp
    linarith [hBge, hB0pos, hz]
  -- power-mean inequality
  have hpm : (∑ q ∈ primesIn (P₂ / 2) P₂, adjCount D q) ^ (2 * ℓ + 1) /
        ((primesIn (P₂ / 2) P₂).card : ℝ) ^ (2 * ℓ) ≤
      ∑ q ∈ primesIn (P₂ / 2) P₂, (adjCount D q) ^ (2 * ℓ + 1) :=
    pow_sum_div_card_le_sum_pow (s := primesIn (P₂ / 2) P₂) (f := fun q => adjCount D q)
      (fun q _ => adjCount_nonneg D q) (2 * ℓ)
  -- Chebyshev bound for `#primesIn (P₂/2) P₂`
  have hQcard : ((primesIn (P₂ / 2) P₂).card : ℝ) ≤ C₁ * pi0 P₂ := hC₁ P₂ hP₂
  -- per-prime bicycle lower bound
  have hbike : ∀ q : ℕ, (adjCount D q) ^ (2 * ℓ + 1) /
        (Fintype.card (GVert D) : ℝ) ^ (2 * ℓ + 2) / 2 ≤ ((bikeSet D q ℓ).card : ℝ) := by
    intro q
    have h := bike_count_arc D q ℓ heven
    simpa only [adjCount, Matrix.of_apply] using h
  have hsum_bike : ∑ q ∈ primesIn (P₂ / 2) P₂,
        (adjCount D q) ^ (2 * ℓ + 1) / (Fintype.card (GVert D) : ℝ) ^ (2 * ℓ + 2) / 2
      ≤ ∑ q ∈ primesIn (P₂ / 2) P₂, ((bikeSet D q ℓ).card : ℝ) :=
    Finset.sum_le_sum (fun q _ => hbike q)
  -- numerator bound: B₀^{2ℓ+1}/#Q^{2ℓ} ≤ ∑ adjCount^{2ℓ+1}
  have hkey : (c ^ 2 * pi0 P₂ * pi0 P₁ ^ 2 * (X / L)) ^ (2 * ℓ + 1) /
        ((primesIn (P₂ / 2) P₂).card : ℝ) ^ (2 * ℓ) ≤
      ∑ q ∈ primesIn (P₂ / 2) P₂, (adjCount D q) ^ (2 * ℓ + 1) := by
    have hpow : (c ^ 2 * pi0 P₂ * pi0 P₁ ^ 2 * (X / L)) ^ (2 * ℓ + 1) ≤
        (∑ q ∈ primesIn (P₂ / 2) P₂, adjCount D q) ^ (2 * ℓ + 1) :=
      pow_le_pow_left₀ hB0nn hBge _
    exact le_trans (div_le_div_of_nonneg_right hpow (by positivity)) hpm
  -- the chain
  calc 1 / (2 * C₁ ^ (2 * ℓ)) * c ^ (4 * ℓ + 2) * pi0 P₂ * (pi0 P₁ ^ 2) ^ (2 * ℓ + 1) / (X / L)
      = (c ^ 2 * pi0 P₂ * pi0 P₁ ^ 2 * (X / L)) ^ (2 * ℓ + 1) /
          (2 * (C₁ * pi0 P₂) ^ (2 * ℓ) * (X / L) ^ (2 * ℓ + 2)) :=
        bikeSet_arith ℓ (ne_of_gt hNpos) (ne_of_gt hC₁pos) (ne_of_gt hpi0₂)
    _ ≤ (c ^ 2 * pi0 P₂ * pi0 P₁ ^ 2 * (X / L)) ^ (2 * ℓ + 1) /
          (2 * (C₁ * pi0 P₂) ^ (2 * ℓ) * (Fintype.card (GVert D) : ℝ) ^ (2 * ℓ + 2)) := by
        have hbpos : 0 < 2 * (C₁ * pi0 P₂) ^ (2 * ℓ) * (Fintype.card (GVert D) : ℝ) ^ (2 * ℓ + 2) := by
          positivity
        refine div_le_div₀ (pow_nonneg hB0nn _) le_rfl hbpos ?_
        have hp : (Fintype.card (GVert D) : ℝ) ^ (2 * ℓ + 2) ≤ (X / L) ^ (2 * ℓ + 2) :=
          pow_le_pow_left₀ hn_pos.le hcardV _
        exact mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ (c ^ 2 * pi0 P₂ * pi0 P₁ ^ 2 * (X / L)) ^ (2 * ℓ + 1) /
          (2 * ((primesIn (P₂ / 2) P₂).card : ℝ) ^ (2 * ℓ) *
            (Fintype.card (GVert D) : ℝ) ^ (2 * ℓ + 2)) := by
        have hdpos : 0 < 2 * ((primesIn (P₂ / 2) P₂).card : ℝ) ^ (2 * ℓ) *
            (Fintype.card (GVert D) : ℝ) ^ (2 * ℓ + 2) := by
          have h1 : 0 < ((primesIn (P₂ / 2) P₂).card : ℝ) ^ (2 * ℓ) := pow_pos hQpos _
          have h2 : 0 < (Fintype.card (GVert D) : ℝ) ^ (2 * ℓ + 2) := pow_pos hn_pos _
          positivity
        refine div_le_div₀ (pow_nonneg hB0nn _) le_rfl hdpos ?_
        have hp : ((primesIn (P₂ / 2) P₂).card : ℝ) ^ (2 * ℓ) ≤ (C₁ * pi0 P₂) ^ (2 * ℓ) :=
          pow_le_pow_left₀ (by positivity) hQcard _
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by norm_num))
          (by positivity)
    _ ≤ (∑ q ∈ primesIn (P₂ / 2) P₂, (adjCount D q) ^ (2 * ℓ + 1)) /
          (2 * (Fintype.card (GVert D) : ℝ) ^ (2 * ℓ + 2)) := by
        have hstep := div_le_div_of_nonneg_right hkey
          (by positivity : (0:ℝ) ≤ 2 * (Fintype.card (GVert D) : ℝ) ^ (2 * ℓ + 2))
        rw [div_div] at hstep
        calc (c ^ 2 * pi0 P₂ * pi0 P₁ ^ 2 * (X / L)) ^ (2 * ℓ + 1) /
              (2 * ((primesIn (P₂ / 2) P₂).card : ℝ) ^ (2 * ℓ) *
                (Fintype.card (GVert D) : ℝ) ^ (2 * ℓ + 2))
            = (c ^ 2 * pi0 P₂ * pi0 P₁ ^ 2 * (X / L)) ^ (2 * ℓ + 1) /
              (((primesIn (P₂ / 2) P₂).card : ℝ) ^ (2 * ℓ) *
                (2 * (Fintype.card (GVert D) : ℝ) ^ (2 * ℓ + 2))) := by
                rw [show (2 * ((primesIn (P₂ / 2) P₂).card : ℝ) ^ (2 * ℓ) *
                    (Fintype.card (GVert D) : ℝ) ^ (2 * ℓ + 2))
                  = ((primesIn (P₂ / 2) P₂).card : ℝ) ^ (2 * ℓ) *
                    (2 * (Fintype.card (GVert D) : ℝ) ^ (2 * ℓ + 2)) by ring]
          _ ≤ (∑ q ∈ primesIn (P₂ / 2) P₂, (adjCount D q) ^ (2 * ℓ + 1)) /
              (2 * (Fintype.card (GVert D) : ℝ) ^ (2 * ℓ + 2)) := hstep
    _ = ∑ q ∈ primesIn (P₂ / 2) P₂,
          (adjCount D q) ^ (2 * ℓ + 1) / (Fintype.card (GVert D) : ℝ) ^ (2 * ℓ + 2) / 2 := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl (fun q _ => ?_)
        rw [div_div]
        ring_nf
    _ ≤ ∑ q ∈ primesIn (P₂ / 2) P₂, ((bikeSet D q ℓ).card : ℝ) := hsum_bike

end Work.BMF
