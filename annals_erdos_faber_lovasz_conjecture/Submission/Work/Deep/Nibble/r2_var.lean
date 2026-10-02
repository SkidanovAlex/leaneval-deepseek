import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.r2_setup
import Submission.Work.Deep.Nibble.r2_own_b
import Submission.Work.Deep.Nibble.r2_var_aux
import Submission.Work.Deep.Nibble.shares_sum_le

/-!
# The variance of the round-2 statistics

`Work.Deep.Nibble.r2_var`: the variance of the number of kept edges is exactly `|𝓖| p (1-p)`,
and the variance of the collision multiplicity `collMult` is at most `4 r θ |V|`.

Both come from the double-sum expansion of the variance (`variance_sum`):

* the number of kept edges is a sum of independent indicators, so only the diagonal terms of the
  double sum survive;
* the collision multiplicity is a sum of the `ssf 𝓖 v = k_v 1[k_v ≥ 2]` over the vertices, whose
  covariance is non-zero exactly for pairs of vertices lying in a common edge (at most one, by
  linearity), where it is bounded by `p(1-p)` using the frozen-measure computation
  `cov_le_of_share`; for a fixed vertex `u` the number of such partners is at most
  `(r-1)·d(u)` (`shares_sum_le`), and `∑_u d(u) ≤ 2 D |V|` by the degree hypothesis.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Deep.Nibble

open Work.Deep.Reed

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The pairwise covariance of the collision-multiplicity summands, bounded by the probability
that the two vertices share an edge with the prescribed edge. -/
lemma cov_le_of_pair (𝓖 : Set (Set V)) {r : ℕ} (hr : 2 ≤ r) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ ≤ 1 / 2) {D : ℕ} (hD : 1 ≤ D) (hp0 : 0 ≤ θ / (D : ℝ)) (hp1 : θ / (D : ℝ) ≤ 1)
    (hlin : HLin 𝓖) (huni : HUnif 𝓖 r) (hdeg : ∀ v : V, (hd 𝓖 v : ℝ) ≤ 2 * (D : ℝ))
    {u v : V} (hvu : v ≠ u) :
    (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).exp (fun ω => ssf 𝓖 u ω * ssf 𝓖 v ω)
      - (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).exp (ssf 𝓖 u)
        * (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).exp (ssf 𝓖 v)
      ≤ ((θ / (D : ℝ)) * (1 - θ / (D : ℝ)))
        * (if ((thruF 𝓖 u) ∩ (thruF 𝓖 v)).Nonempty then (1 : ℝ) else 0) := by
  classical
  have hpnn : 0 ≤ (θ / (D : ℝ)) * (1 - θ / (D : ℝ)) :=
    mul_nonneg hp0 (by linarith)
  by_cases h : ((thruF 𝓖 u) ∩ (thruF 𝓖 v)).Nonempty
  · rw [if_pos h]
    obtain ⟨g, hg⟩ := h
    have hgu : g ∈ thruF 𝓖 u := (Finset.mem_inter.mp hg).1
    have hgv : g ∈ thruF 𝓖 v := (Finset.mem_inter.mp hg).2
    have hcov := cov_le_of_share 𝓖 hr hθ0 hθ1 hD hp0 hp1 hlin huni hdeg (Ne.symm hvu) hgu hgv
    nlinarith [hcov, hpnn]
  · rw [if_neg h]
    have hdisj : Disjoint (thruF 𝓖 u) (thruF 𝓖 v) := by
      rw [Finset.disjoint_iff_inter_eq_empty, Finset.not_nonempty_iff_eq_empty.mp h]
    rw [cov_eq_zero_of_disjoint 𝓖 hp0 hp1 hdisj]
    simp

/-- **The variance of the collision multiplicity** is at most `4 r θ |V|`. -/
theorem r2_var_collMult (𝓖 : Set (Set V)) {r : ℕ} (hr : 2 ≤ r) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ ≤ 1 / 2) {D : ℕ} (hD : 1 ≤ D) (hp0 : 0 ≤ θ / (D : ℝ)) (hp1 : θ / (D : ℝ) ≤ 1)
    (hlin : HLin 𝓖) (huni : HUnif 𝓖 r) (hdeg : ∀ v : V, (hd 𝓖 v : ℝ) ≤ 2 * (D : ℝ)) :
    variance (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1)
        (fun ω => ((collMult 𝓖 ω : ℕ) : ℝ))
      ≤ 4 * (r : ℝ) * θ * (Fintype.card V : ℝ) := by
  classical
  set C : V → V → ℝ := fun u v =>
    (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).exp (fun ω => ssf 𝓖 u ω * ssf 𝓖 v ω)
      - (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).exp (ssf 𝓖 u)
        * (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).exp (ssf 𝓖 v) with hCdef
  have hvar : variance (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1)
      (fun ω => ((collMult 𝓖 ω : ℕ) : ℝ)) = ∑ u : V, ∑ v : V, C u v := by
    rw [show (fun ω : 𝓖 → Bool => ((collMult 𝓖 ω : ℕ) : ℝ))
        = (fun ω => ∑ v : V, ssf 𝓖 v ω) from funext fun ω => collMult_cast 𝓖 ω]
    rw [variance_sum]
  have hsplit : (∑ u : V, ∑ v : V, C u v)
      = (∑ u : V, C u u) + ∑ u : V, ∑ v ∈ Finset.univ.erase u, C u v := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finset.sum_erase_add (s := (Finset.univ : Finset V)) (f := fun v => C u v)
      (Finset.mem_univ u), add_comm]
  -- ### the diagonal
  have hdiag : (∑ u : V, C u u) ≤ (Fintype.card V : ℝ) * (8 * θ ^ 2) := by
    calc (∑ u : V, C u u) ≤ ∑ _u : V, 8 * θ ^ 2 :=
          Finset.sum_le_sum fun u _ => cov_self_le 𝓖 hr hθ0 hθ1 hD hp0 hp1 hlin huni hdeg u
      _ = (Fintype.card V : ℝ) * (8 * θ ^ 2) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- ### the off-diagonal
  have hpnn : 0 ≤ (θ / (D : ℝ)) * (1 - θ / (D : ℝ)) :=
    mul_nonneg hp0 (by linarith)
  have hoff : (∑ u : V, ∑ v ∈ Finset.univ.erase u, C u v)
      ≤ (θ / (D : ℝ)) * (1 - θ / (D : ℝ))
        * ∑ u : V, (((r : ℝ) - 1) * (hd 𝓖 u : ℝ)) := by
    calc (∑ u : V, ∑ v ∈ Finset.univ.erase u, C u v)
        ≤ ∑ u : V, (θ / (D : ℝ)) * (1 - θ / (D : ℝ))
            * ∑ v ∈ Finset.univ.erase u,
              (if ((thruF 𝓖 u) ∩ (thruF 𝓖 v)).Nonempty then (1 : ℝ) else 0) := by
          refine Finset.sum_le_sum fun u _ => ?_
          calc (∑ v ∈ Finset.univ.erase u, C u v)
              ≤ ∑ v ∈ Finset.univ.erase u, ((θ / (D : ℝ)) * (1 - θ / (D : ℝ)))
                  * (if ((thruF 𝓖 u) ∩ (thruF 𝓖 v)).Nonempty then (1 : ℝ) else 0) :=
                Finset.sum_le_sum fun v hv =>
                  cov_le_of_pair 𝓖 hr hθ0 hθ1 hD hp0 hp1 hlin huni hdeg
                    (Finset.mem_erase.mp hv).1
            _ = (θ / (D : ℝ)) * (1 - θ / (D : ℝ))
                  * ∑ v ∈ Finset.univ.erase u,
                    (if ((thruF 𝓖 u) ∩ (thruF 𝓖 v)).Nonempty then (1 : ℝ) else 0) := by
                rw [Finset.mul_sum]
      _ ≤ ∑ u : V, (θ / (D : ℝ)) * (1 - θ / (D : ℝ))
            * (((r : ℝ) - 1) * (hd 𝓖 u : ℝ)) := by
          refine Finset.sum_le_sum fun u _ => ?_
          exact mul_le_mul_of_nonneg_left (shares_sum_le 𝓖 hlin huni u) hpnn
      _ = (θ / (D : ℝ)) * (1 - θ / (D : ℝ))
            * ∑ u : V, (((r : ℝ) - 1) * (hd 𝓖 u : ℝ)) := by
          rw [Finset.mul_sum]
  have hdegsum : (∑ u : V, (hd 𝓖 u : ℝ)) ≤ (Fintype.card V : ℝ) * (2 * (D : ℝ)) := by
    calc (∑ u : V, (hd 𝓖 u : ℝ)) ≤ ∑ _u : V, 2 * (D : ℝ) :=
          Finset.sum_le_sum fun u _ => hdeg u
      _ = (Fintype.card V : ℝ) * (2 * (D : ℝ)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hoff2 : (θ / (D : ℝ)) * (1 - θ / (D : ℝ)) * ∑ u : V, (((r : ℝ) - 1) * (hd 𝓖 u : ℝ))
      ≤ (θ / (D : ℝ)) * (1 - θ / (D : ℝ)) * (((r : ℝ) - 1)
          * ((Fintype.card V : ℝ) * (2 * (D : ℝ)))) := by
    have h1 : (0 : ℝ) ≤ θ / (D : ℝ) := hp0
    have h2 : (0 : ℝ) ≤ 1 - θ / (D : ℝ) := by linarith
    have h3 : (0 : ℝ) ≤ (r : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
      linarith
    have h4 : (∑ u : V, (((r : ℝ) - 1) * (hd 𝓖 u : ℝ)))
        = ((r : ℝ) - 1) * ∑ u : V, (hd 𝓖 u : ℝ) := by rw [Finset.mul_sum]
    rw [h4]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg h1 h2)
    exact mul_le_mul_of_nonneg_left hdegsum h3
  -- ### the final arithmetic
  have hn : (0 : ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
  have hrn : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hpD : (θ / (D : ℝ)) * (D : ℝ) = θ := by
    field_simp
  have hoffbound : (θ / (D : ℝ)) * (1 - θ / (D : ℝ)) * (((r : ℝ) - 1)
      * ((Fintype.card V : ℝ) * (2 * (D : ℝ)))) ≤ 2 * θ * ((r : ℝ) - 1) * (Fintype.card V : ℝ) := by
    have h2 : (1 - θ / (D : ℝ)) ≤ 1 := by linarith [hp0]
    have h3 : (0 : ℝ) ≤ (r : ℝ) - 1 := by linarith
    have h6 : (0 : ℝ) ≤ ((r : ℝ) - 1) * (Fintype.card V : ℝ) := mul_nonneg h3 hn
    have h7 : (0 : ℝ) ≤ 2 * ((r : ℝ) - 1) * (Fintype.card V : ℝ) := by linarith [h6]
    calc (θ / (D : ℝ)) * (1 - θ / (D : ℝ)) * (((r : ℝ) - 1)
            * ((Fintype.card V : ℝ) * (2 * (D : ℝ))))
        = ((θ / (D : ℝ)) * (D : ℝ))
            * (2 * (1 - θ / (D : ℝ)) * ((r : ℝ) - 1) * (Fintype.card V : ℝ)) := by ring
      _ = θ * (2 * (1 - θ / (D : ℝ)) * ((r : ℝ) - 1) * (Fintype.card V : ℝ)) := by rw [hpD]
      _ ≤ θ * (2 * 1 * ((r : ℝ) - 1) * (Fintype.card V : ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hθ0)
          calc 2 * (1 - θ / (D : ℝ)) * ((r : ℝ) - 1) * (Fintype.card V : ℝ)
              = (1 - θ / (D : ℝ)) * (2 * ((r : ℝ) - 1) * (Fintype.card V : ℝ)) := by ring
            _ ≤ 1 * (2 * ((r : ℝ) - 1) * (Fintype.card V : ℝ)) := mul_le_mul_of_nonneg_right h2 h7
            _ = 2 * 1 * ((r : ℝ) - 1) * (Fintype.card V : ℝ) := by ring
      _ = 2 * θ * ((r : ℝ) - 1) * (Fintype.card V : ℝ) := by ring
  have hdiagbound : (Fintype.card V : ℝ) * (8 * θ ^ 2) ≤ 2 * (r : ℝ) * θ * (Fintype.card V : ℝ) := by
    have h4 : 4 * θ ≤ (r : ℝ) := by linarith
    have h5 : (0 : ℝ) ≤ θ * (Fintype.card V : ℝ) := mul_nonneg (le_of_lt hθ0) hn
    nlinarith [h4, h5, hn, mul_nonneg h5 (le_of_lt hθ0)]
  have hoffbound2 : 2 * θ * ((r : ℝ) - 1) * (Fintype.card V : ℝ)
      ≤ 2 * (r : ℝ) * θ * (Fintype.card V : ℝ) := by
    have h5 : (0 : ℝ) ≤ θ * (Fintype.card V : ℝ) := mul_nonneg (le_of_lt hθ0) hn
    nlinarith [h5, hrn, mul_nonneg h5 (le_of_lt hθ0)]
  rw [hvar, hsplit]
  have h1 : (∑ u : V, ∑ v ∈ Finset.univ.erase u, C u v)
      ≤ 2 * θ * ((r : ℝ) - 1) * (Fintype.card V : ℝ) := le_trans hoff (le_trans hoff2 hoffbound)
  have h2 : (∑ u : V, C u u) ≤ 2 * (r : ℝ) * θ * (Fintype.card V : ℝ) := le_trans hdiag hdiagbound
  have h3 : (∑ u : V, ∑ v ∈ Finset.univ.erase u, C u v)
      ≤ 2 * (r : ℝ) * θ * (Fintype.card V : ℝ) := le_trans h1 hoffbound2
  linarith [h2, h3]

/-- **The variance of the round-2 statistics.** -/
theorem r2_var {V : Type*} [Fintype V] [DecidableEq V] (𝓖 : Set (Set V)) {r : ℕ} (hr : 2 ≤ r)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 2) {D : ℕ} (hD : 1 ≤ D)
    (hp0 : 0 ≤ θ / (D : ℝ)) (hp1 : θ / (D : ℝ) ≤ 1)
    (hlin : Work.Deep.Nibble.HLin 𝓖) (huni : Work.Deep.Nibble.HUnif 𝓖 r)
    (hdeg : ∀ v : V, (Work.Deep.Nibble.hd 𝓖 v : ℝ) ≤ 2 * (D : ℝ)) :
    Work.Deep.Nibble.variance (Work.Deep.Nibble.edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1)
        (fun ω => ((Work.Deep.Nibble.keptF 𝓖 ω).card : ℝ))
      = (Nat.card 𝓖 : ℝ) * (θ / (D : ℝ)) * (1 - θ / (D : ℝ))
  ∧ Work.Deep.Nibble.variance (Work.Deep.Nibble.edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1)
        (fun ω => ((Work.Deep.Nibble.collMult 𝓖 ω : ℕ) : ℝ))
      ≤ 4 * (r : ℝ) * θ * (Fintype.card V : ℝ) :=
  ⟨r2_var_keptF 𝓖 hp0 hp1, r2_var_collMult 𝓖 hr hθ0 hθ1 hD hp0 hp1 hlin huni hdeg⟩

end Work.Deep.Nibble
