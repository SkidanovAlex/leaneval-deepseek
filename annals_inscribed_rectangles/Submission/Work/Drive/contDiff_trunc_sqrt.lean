import Mathlib
import Submission.Work.Drive.sqrt_subst_fderiv_bound
import Submission.Work.Drive.subst_iteratedFDeriv_bound
import Submission.Work.Drive.contDiffAt_trunc_sqrt_assembly

namespace Work.Drive

open Set Filter Topology
open scoped ContDiff

/-- The open half-space `{0 < t} ⊂ X × ℝ`. -/
private def s2 (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] : Set (X × ℝ) :=
  {p | 0 < p.2}

/-- The substitution `(x,t) ↦ (x, √t)`. -/
private noncomputable def theta (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :
    X × ℝ → X × ℝ := fun y => (y.1, Real.sqrt y.2)

/-- `g` is smooth on the open half-space `{0 < t}`. -/
theorem contDiffOn_trunc_sqrt_trunc {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {S : X × ℝ → E}
    (hS : ∀ z : X × ℝ, 0 < z.2 → ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S z) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : X × ℝ => if 0 < p.2 then S (p.1, Real.sqrt p.2) else 0)
      (univ ×ˢ Ioi (0 : ℝ)) := by
  have hon : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S (univ ×ˢ Ioi (0 : ℝ)) :=
    fun z hz => (hS z hz.2).contDiffWithinAt
  have hθ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (theta X) (univ ×ˢ Ioi (0 : ℝ)) := by
    apply ContDiffOn.prodMk contDiffOn_fst
    apply ContDiffOn.sqrt contDiffOn_snd
    intro q hq
    exact ne_of_gt hq.2
  have hcomp : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : X × ℝ => S (q.1, Real.sqrt q.2)) (univ ×ˢ Ioi (0 : ℝ)) :=
    hon.comp hθ (fun q hq => by
      simp only [mem_prod, mem_univ, true_and]
      exact Real.sqrt_pos.2 hq.2)
  exact hcomp.congr (fun q hq => by
    have hq2 : (0 : ℝ) < q.2 := hq.2
    simp only [hq2, if_true])

theorem contDiff_trunc_sqrt {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {S : X × ℝ → E} {K m : ℕ}
    (hKm : 2 * m + 2 ≤ K)
    (hS : ∀ z : X × ℝ, 0 < z.2 → ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S z)
    (hb : ∀ x₀ : X, ∃ C δ : ℝ, 0 < δ ∧ ∀ x : X, ‖x - x₀‖ < δ → ∀ t : ℝ, 0 < t → t < δ →
      ∀ j : ℕ, j ≤ K → ‖iteratedFDeriv ℝ j S (x, t)‖ ≤ C * t ^ (K - j)) :
    ContDiff ℝ m (fun p : X × ℝ => if 0 < p.2 then S (p.1, Real.sqrt p.2) else 0) := by
  obtain ⟨b, hb0, hbb⟩ := sqrt_subst_fderiv_bound X
  obtain ⟨c, hc0, hc⟩ := subst_iteratedFDeriv_bound (X := X) b hb0
    (fun m z hz0 hz1 => hbb z hz0 hz1 m)
  have hSon : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S (univ ×ˢ Ioi (0 : ℝ)) :=
    fun z hz => (hS z hz.2).contDiffWithinAt
  have hsmooth := contDiffOn_trunc_sqrt_trunc (X := X) (E := E) hS
  rw [contDiff_iff_contDiffAt]
  intro z
  rcases lt_trichotomy z.2 0 with hlt | heq | hgt
  · have hev : (fun p : X × ℝ => if 0 < p.2 then S (p.1, Real.sqrt p.2) else 0)
        =ᶠ[𝓝 z] (fun _ => (0 : E)) := by
      filter_upwards [isOpen_lt continuous_snd continuous_const |>.mem_nhds hlt] with y hy
      rw [if_neg (not_lt.mpr hy.le)]
    exact (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq hev
  · have hz0 : z = (z.1, (0 : ℝ)) := Prod.ext rfl heq
    rw [hz0]
    obtain ⟨C0, δ0, hδ0, hC0⟩ := hb z.1
    refine contDiffAt_trunc_sqrt_assembly (x₀ := z.1)
      (C := fun k => c k * ((k + 1 : ℕ) : ℝ) * max C0 0)
      (δ := min (min δ0 (δ0 ^ 2)) 1) hKm ?_ ?_ ?_ ?_ hsmooth ?_
    · intro k
      exact mul_nonneg (mul_nonneg (hc0 k) (by positivity)) (le_max_right _ _)
    · exact lt_min (lt_min hδ0 (pow_pos hδ0 2)) one_pos
    · exact min_le_right _ _
    · intro w hw
      rw [if_neg (not_lt.mpr hw)]
    · intro w hw1 hw2 hw3 k hk
      have hs2 : IsOpen (s2 X) := isOpen_lt continuous_const continuous_snd
      have hw3' : w.2 < min δ0 (δ0 ^ 2) := lt_of_lt_of_le hw3 (min_le_left _ _)
      have hwδ0 : w.2 < δ0 := lt_of_lt_of_le hw3' (min_le_left _ _)
      have hwδ02 : w.2 < δ0 ^ 2 := lt_of_lt_of_le hw3' (min_le_right _ _)
      have hw1' : ‖w.1 - z.1‖ < δ0 :=
        lt_of_lt_of_le hw1 (le_trans (min_le_left _ _) (min_le_left _ _))
      have hwle1 : w.2 ≤ 1 := le_trans (le_of_lt hw3) (min_le_right _ _)
      have hsq_lt : Real.sqrt w.2 < δ0 := by
        have := Real.sqrt_lt_sqrt (le_of_lt hw2) hwδ02
        rwa [Real.sqrt_sq (le_of_lt hδ0)] at this
      have hwpos : 0 < Real.sqrt w.2 := Real.sqrt_pos.2 hw2
      have hgeq : iteratedFDeriv ℝ k
            (fun p : X × ℝ => if 0 < p.2 then S (p.1, Real.sqrt p.2) else 0) w
          = iteratedFDeriv ℝ k (fun p : X × ℝ => S (p.1, Real.sqrt p.2)) w := by
        rw [← show iteratedFDerivWithin ℝ k
              (fun p : X × ℝ => if 0 < p.2 then S (p.1, Real.sqrt p.2) else 0) (s2 X) w
            = iteratedFDeriv ℝ k
              (fun p : X × ℝ => if 0 < p.2 then S (p.1, Real.sqrt p.2) else 0) w
            from iteratedFDerivWithin_of_isOpen k hs2 hw2,
          ← show iteratedFDerivWithin ℝ k (fun p : X × ℝ => S (p.1, Real.sqrt p.2)) (s2 X) w
            = iteratedFDeriv ℝ k (fun p : X × ℝ => S (p.1, Real.sqrt p.2)) w
            from iteratedFDerivWithin_of_isOpen k hs2 hw2]
        refine iteratedFDerivWithin_congr (𝕜 := ℝ) (s := s2 X) ?_ (show w ∈ s2 X from hw2) k
        intro q hq
        have hq2 : (0 : ℝ) < q.2 := hq
        simp only [hq2, if_true]
      rw [hgeq]
      have hck := hc k E S hSon w hw2 hwle1
      have hterm : ∀ j ∈ Finset.range (k + 1),
          ‖iteratedFDeriv ℝ j S (w.1, Real.sqrt w.2)‖ / (Real.sqrt w.2) ^ (2 * k - j)
            ≤ max C0 0 * (Real.sqrt w.2) ^ (K - 2 * k) := by
        intro j hj
        rw [Finset.mem_range] at hj
        have hjk : j ≤ k := Nat.lt_succ_iff.mp hj
        have hjmK : j ≤ K := le_trans hjk (le_trans hk (by omega))
        have hbnd := hC0 w.1 hw1' (Real.sqrt w.2) hwpos hsq_lt j hjmK
        have hpow : (Real.sqrt w.2) ^ (K - j) / (Real.sqrt w.2) ^ (2 * k - j)
            = (Real.sqrt w.2) ^ (K - 2 * k) := by
          rw [div_eq_mul_inv, ← pow_sub₀ _ (ne_of_gt hwpos) (by omega)]
          congr 1
          omega
        calc ‖iteratedFDeriv ℝ j S (w.1, Real.sqrt w.2)‖
                / (Real.sqrt w.2) ^ (2 * k - j)
            ≤ (C0 * (Real.sqrt w.2) ^ (K - j)) / (Real.sqrt w.2) ^ (2 * k - j) :=
              div_le_div_of_nonneg_right hbnd (by positivity)
          _ = C0 * ((Real.sqrt w.2) ^ (K - j) / (Real.sqrt w.2) ^ (2 * k - j)) := by ring
          _ = C0 * (Real.sqrt w.2) ^ (K - 2 * k) := by rw [hpow]
          _ ≤ max C0 0 * (Real.sqrt w.2) ^ (K - 2 * k) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      calc ‖iteratedFDeriv ℝ k (fun p : X × ℝ => S (p.1, Real.sqrt p.2)) w‖
          ≤ c k * ∑ j ∈ Finset.range (k + 1),
              ‖iteratedFDeriv ℝ j S (w.1, Real.sqrt w.2)‖ / (Real.sqrt w.2) ^ (2 * k - j) := hck
        _ ≤ c k * ∑ _j ∈ Finset.range (k + 1),
              max C0 0 * (Real.sqrt w.2) ^ (K - 2 * k) := by
              apply mul_le_mul_of_nonneg_left _ (hc0 k)
              exact Finset.sum_le_sum (fun j hj => hterm j hj)
        _ = c k * (((k + 1 : ℕ) : ℝ) * (max C0 0 * (Real.sqrt w.2) ^ (K - 2 * k))) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ = (c k * ((k + 1 : ℕ) : ℝ) * max C0 0) * (Real.sqrt w.2) ^ (K - 2 * k) := by ring
  · exact (hsmooth.contDiffAt ((isOpen_univ.prod isOpen_Ioi).mem_nhds ⟨mem_univ _, hgt⟩)).of_le
      (WithTop.coe_le_coe.mpr le_top)

end Work.Drive
