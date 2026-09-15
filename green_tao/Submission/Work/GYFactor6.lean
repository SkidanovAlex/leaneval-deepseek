import Submission.Work.GYFactor5
import Submission.Commons.NumberTheory.Zeta.hasProd_E3_eq_zeta_ratio
import Submission.Commons.Analysis.Complex.continuousOn_tprod_one_add_nat
import Submission.Commons.Analysis.Complex.differentiableOn_tprod_one_add_nat

/-!
# Green–Tao §10: the smoothed local factors `G₁`, `G₂`, `G₃` and `∏_p E_p`

This file constructs, for the §10 application, the three factors of Green–Tao's Euler product
`∏_p E_p = G₁ G₂ G₃` (their Lemma 10.3):

* `G₁ = ∏_p E_p^{(1)}`, an Euler product converging on the strip `-1/(6m) < Re z_j`: because the
  raw `tprod` is only defined where it converges, we multiply each factor by a smooth cutoff
  `kapCut` that is `≡ 1` on the strip and `≡ 0` outside a slightly larger region — this makes the
  product GLOBALLY continuous and holomorphic, which is what `zeta_bound_m_strip` needs;
* `G₂ = ∏_p E_p^{(2)}`, a finitely supported product (only the primes `p | W` contribute), hence
  globally continuous and holomorphic with no cutoff;
* `G₃ = ∏_p E_p^{(3)} = ∏_j ζ(1+z_j+z'_j)/(ζ(1+z_j)ζ(1+z'_j))` (Green–Tao (10.9)), the ratio of
  zeta values, holomorphic on `Re z_j > 0` (already in the commons as `tprod_E3_eq_zeta_ratio`).
-/

open Finset Filter
open Commons.NumberTheory.Sieve
open scoped BigOperators Topology

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace GYMaj
namespace BoxAvg

variable {m t : ℕ}
variable {W Amax : ℕ} {A : Fin m → Fin t → ℤ} {b : Fin m → ℤ}

/-! ## 1. Local helpers: continuity and holomorphy of `∏' n, (1 + f n x)` -/

/-! ## 2. The cutoff `kapCut` -/

/-- The cutoff ramp: `0` for `x ≤ -1/(6m)` and `1` for `x ≥ -1/(12m)`. -/
noncomputable def chiCut (m : ℕ) (x : ℝ) : ℝ := max 0 (min 1 (12 * (m : ℝ) * x + 2))

lemma continuous_chiCut (m : ℕ) : Continuous (chiCut m) := by
  unfold chiCut; fun_prop

lemma chiCut_nonneg (m : ℕ) (x : ℝ) : 0 ≤ chiCut m x := le_max_left _ _

lemma chiCut_le_one (m : ℕ) (x : ℝ) : chiCut m x ≤ 1 :=
  max_le (by norm_num) (min_le_left _ _)

lemma chiCut_eq_one {m : ℕ} (hm : 1 ≤ m) {x : ℝ} (hx : -(1 / (12 * (m : ℝ))) ≤ x) :
    chiCut m x = 1 := by
  have hm0 : (0 : ℝ) < 12 * (m : ℝ) := by positivity
  have h2 : (12 : ℝ) * (m : ℝ) * (-(1 / (12 * (m : ℝ)))) = -1 := by
    field_simp <;> ring
  have h1 : 1 ≤ 12 * (m : ℝ) * x + 2 := by
    have h := mul_le_mul_of_nonneg_left hx (le_of_lt hm0)
    rw [h2] at h
    linarith
  unfold chiCut
  rw [min_eq_left h1, max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]

lemma chiCut_eq_zero {m : ℕ} (hm : 1 ≤ m) {x : ℝ} (hx : x ≤ -(1 / (6 * (m : ℝ)))) :
    chiCut m x = 0 := by
  have hm0 : (0 : ℝ) < 12 * (m : ℝ) := by positivity
  have h2 : (12 : ℝ) * (m : ℝ) * (-(1 / (6 * (m : ℝ)))) = -2 := by
    field_simp <;> ring
  have h1 : 12 * (m : ℝ) * x + 2 ≤ 0 := by
    have h := mul_le_mul_of_nonneg_left hx (le_of_lt hm0)
    rw [h2] at h
    linarith
  unfold chiCut
  rw [min_eq_right (by linarith), max_eq_left h1]

lemma chiCut_pos {m : ℕ} (hm : 1 ≤ m) {x : ℝ} (hx : -(1 / (6 * (m : ℝ))) < x) :
    0 < chiCut m x := by
  have hm0 : (0 : ℝ) < 12 * (m : ℝ) := by positivity
  have h2 : (12 : ℝ) * (m : ℝ) * (-(1 / (6 * (m : ℝ)))) = -2 := by
    field_simp <;> ring
  have h1 : 0 < 12 * (m : ℝ) * x + 2 := by
    have h := mul_lt_mul_of_pos_left hx hm0
    rw [h2] at h
    linarith
  unfold chiCut
  exact lt_of_lt_of_le (lt_min (by norm_num) h1) (le_max_right _ _)

/-- The `m`-fold cutoff, `≡ 1` when all `Re z_j ≥ -1/(12m)` and `≡ 0` when some
`Re z_j ≤ -1/(6m)`. -/
noncomputable def kapCut (m : ℕ) (z : Fin m → ℂ) : ℝ := ∏ j, chiCut m ((z j).re)

lemma kapCut_nonneg (m : ℕ) (z : Fin m → ℂ) : 0 ≤ kapCut m z :=
  Finset.prod_nonneg (fun j _ => chiCut_nonneg m _)

lemma kapCut_le_one (m : ℕ) (z : Fin m → ℂ) : kapCut m z ≤ 1 :=
  Finset.prod_le_one (fun j _ => chiCut_nonneg m _) (fun j _ => chiCut_le_one m _)

lemma continuous_kapCut (m : ℕ) : Continuous (kapCut m) := by
  unfold kapCut chiCut; fun_prop

lemma kapCut_eq_one {m : ℕ} (hm : 1 ≤ m) {z : Fin m → ℂ}
    (hz : ∀ j, -(1 / (12 * (m : ℝ))) ≤ (z j).re) : kapCut m z = 1 := by
  unfold kapCut
  refine Finset.prod_eq_one (fun j _ => ?_)
  exact chiCut_eq_one hm (hz j)

lemma kapCut_eq_zero {m : ℕ} (hm : 1 ≤ m) {z : Fin m → ℂ} {j : Fin m}
    (hz : (z j).re ≤ -(1 / (6 * (m : ℝ)))) : kapCut m z = 0 := by
  unfold kapCut
  exact Finset.prod_eq_zero (Finset.mem_univ j) (chiCut_eq_zero hm hz)

lemma kapCut_pos {m : ℕ} (hm : 1 ≤ m) {z : Fin m → ℂ}
    (hz : ∀ j, -(1 / (6 * (m : ℝ))) < (z j).re) : 0 < kapCut m z := by
  unfold kapCut
  exact Finset.prod_pos (fun j _ => chiCut_pos hm (hz j))


/-! ## 3. The local factors (definitions) -/

/-- The first local factor `G₁ = ∏_p E_p^{(1)}` (Green–Tao Lemma 10.3). -/
noncomputable def G1u (W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ)
    (z z' : Fin m → ℂ) : ℂ :=
  ∏' n : ℕ, E1p W A b z z' n

/-- The second local factor `G₂ = ∏_p E_p^{(2)}` (finitely supported: only the primes `p ∣ W`). -/
noncomputable def G2u (W : ℕ) (z z' : Fin m → ℂ) : ℂ :=
  ∏' n : ℕ, E2p W z z' n

/-- Green–Tao's `G₃ = ∏_j ζ(1+z_j+z'_j)/(ζ(1+z_j)ζ(1+z'_j))` (their (10.9)). -/
noncomputable def G3R (z z' : Fin m → ℂ) : ℂ :=
  ∏ j, riemannZeta (1 + z j + z' j) / (riemannZeta (1 + z j) * riemannZeta (1 + z' j))


/-- `1/(6m) > 0`. -/
lemma sixth_pos {m : ℕ} (hm : 1 ≤ m) : (0 : ℝ) < 1 / (6 * (m : ℝ)) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  positivity

/-- The size hypotheses `2σ₀m < 1`, `4σ₀ < 1` hold for `σ₀ = 1/(6m)`. -/
lemma sixth_small {m : ℕ} (hm : 1 ≤ m) :
    4 * (1 / (6 * (m : ℝ))) < 1 ∧ 2 * (1 / (6 * (m : ℝ))) * (m : ℝ) < 1 := by
  have hm1R : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  constructor
  · rw [show (4 : ℝ) * (1 / (6 * (m : ℝ))) = 4 / (6 * (m : ℝ)) by ring,
      div_lt_one (by positivity)]
    linarith
  · rw [show (2 : ℝ) * (1 / (6 * (m : ℝ))) * (m : ℝ) = 2 * (m : ℝ) / (6 * (m : ℝ)) by ring,
      div_lt_one (by positivity)]
    linarith

/-- `G₁ = ∏_p E_p^{(1)}` is multipliable on the strip. -/
lemma multipliable_E1p (H : LocHyp W Amax A b) {z z' : Fin m → ℂ}
    (hz : ∀ j, -(1 / (6 * (m : ℝ))) < (z j).re)
    (hz' : ∀ j, -(1 / (6 * (m : ℝ))) < (z' j).re) :
    Multipliable (fun n : ℕ => E1p W A b z z' n) := by
  obtain ⟨h4, h2m⟩ := sixth_small H.hm
  have hsum := E1p_summable H (by positivity) h4 h2m (fun j => le_of_lt (hz j))
    (fun j => le_of_lt (hz' j))
  exact (multipliable_one_add_of_summable hsum).congr (fun n => by ring)

/-- `G₂ = ∏_p E_p^{(2)}` is multipliable (it is finitely supported). -/
lemma multipliable_E2p (H : LocHyp W Amax A b) (z z' : Fin m → ℂ) :
    Multipliable (fun n : ℕ => E2p W z z' n) := by
  have h : ∀ᶠ n : ℕ in Filter.atTop, ‖(E2p W z z' n - 1 : ℂ)‖ ≤ (0 : ℝ) := by
    rw [Filter.eventually_atTop]
    refine ⟨W + 1, fun n hn => ?_⟩
    have hnd : ¬ n ∣ W := fun hd => by
      have := Nat.le_of_dvd H.hW0 hd
      omega
    rw [E2p, if_neg (fun hc => hnd hc.2), sub_self, norm_zero]
  exact (multipliable_one_add_of_summable
    (Summable.of_norm_bounded_eventually_nat (summable_zero : Summable (fun _ : ℕ => (0 : ℝ))) h).norm).congr
    (fun n => by ring)

/-- `G₂` is the finite product over the divisors of `W`. -/
lemma G2u_eq_prod (H : LocHyp W Amax A b) (z z' : Fin m → ℂ) :
    G2u W z z' = ∏ n ∈ W.divisors, E2p W z z' n := by
  rw [G2u]
  refine tprod_eq_prod (s := W.divisors) (fun n hn => ?_)
  have hnd : ¬ n ∣ W := by
    intro hd
    exact hn (Nat.mem_divisors.mpr ⟨hd, ne_of_gt H.hW0⟩)
  rw [E2p, if_neg (fun hc => hnd hc.2)]

/-- **Green–Tao (10.8) + (10.9): the factorisation of the §10 Euler product** into the three
local factors, on the region `Re z_j, Re z'_j > 1` where everything converges absolutely. -/
theorem tprod_eulerFactor_eq (H : LocHyp W Amax A b) {z z' : Fin m → ℂ}
    (hz : ∀ j, 1 < (z j).re) (hz' : ∀ j, 1 < (z' j).re) :
    (∏' p : ℕ, eulerFactor m (vSys W A b) z z' p)
      = G1u W A b z z' * G2u W z z' * G3R z z' := by
  have hpt : ∀ p : ℕ, eulerFactor m (vSys W A b) z z' p
      = E1p W A b z z' p * E2p W z z' p * E3p z z' p := fun p =>
    eulerFactor_eq_E1p_mul_E2p_mul_E3p H (σ₀ := 1 / 4) (by norm_num)
      (z := z) (z' := z') (fun j => by linarith [hz j]) (fun j => by linarith [hz' j]) p
  have hpos := sixth_pos H.hm
  have hM1 : Multipliable (fun p : ℕ => E1p W A b z z' p) :=
    multipliable_E1p H (fun j => by linarith [hz j, hpos])
      (fun j => by linarith [hz' j, hpos])
  have hM2 : Multipliable (fun p : ℕ => E2p W z z' p) := multipliable_E2p H z z'
  have h3 := Commons.NumberTheory.Zeta.hasProd_E3_eq_zeta_ratio m z z'
    (fun j => by linarith [hz j]) (fun j => by linarith [hz' j])
  have hres : HasProd (fun p : ℕ => E1p W A b z z' p * E2p W z z' p * E3p z z' p)
      (G1u W A b z z' * G2u W z z' * G3R z z') :=
    (hM1.hasProd.mul hM2.hasProd).mul h3
  exact (hres.congr_fun (fun p => (hpt p))).tprod_eq

end BoxAvg
end GYMaj
