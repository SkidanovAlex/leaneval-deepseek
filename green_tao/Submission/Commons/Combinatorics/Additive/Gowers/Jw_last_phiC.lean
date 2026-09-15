import Mathlib
import Submission.Commons.Combinatorics.Additive.Gowers.gvn_weighted
import Submission.Commons.Combinatorics.Additive.AP.sum_phiC_cover

open scoped BigOperators

namespace Commons.Combinatorics.Additive.Gowers

open Commons.Combinatorics.Additive.AP (sum_phiC_cover)

/-- Distribution of a coefficient: `∑ (1 - A * B t) * u t = ∑ u t - A * ∑ u t * B t`. -/
private lemma sum_one_sub_mul {M : Type*} [CommRing M] {n : ℕ} (A : M) (B u : Fin n → M) :
    (∑ t, (1 - A * B t) * u t) = (∑ t, u t) - A * (∑ t, u t * B t) := by
  have h : ∀ t : Fin n, (1 - A * B t) * u t = u t - A * (u t * B t) := by
    intro t; ring
  rw [Finset.sum_congr rfl (fun t _ => h t), Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- **The last stage of the weighted Green--Tao quantity for the general linear
reparametrisation `φ_i(y) = ∑_t y_t - c_i ∑_t y_t / c_{t+1}`** associated with an injective
`c : Fin k → ZMod p` with `c 0 = 0`: it equals `p^{-2}` times the `k`-term AP sum with shifts
`c_0, …, c_{k-1}`. -/
theorem Jw_last_phiC {p : ℕ} [Fact p.Prime] {k : ℕ} (hk : 3 ≤ k) (hkp : k ≤ p)
    (c : Fin k → ZMod p) (hc : Function.Injective c) (hc0 : c ⟨0, by omega⟩ = 0)
    (f : Fin k → ZMod p → ℝ) (ν : ZMod p → ℝ) :
    GVNW.Jw (ZMod p) k (fun i y => ∑ t : Fin (k-1), (1 - c i * (c ⟨t.val+1, by omega⟩)⁻¹) * y t)
        f ν (k-1) (by omega)
      = ((p:ℝ)^2)⁻¹ * (∑ x : ZMod p, ∑ r : ZMod p, ∏ i : Fin k, f i (x + c i * r)) := by
  have hpne : (p:ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hcard : (Fintype.card (Fin (k-1) → ZMod p) : ℝ) = (p : ℝ)^(k-1) :=
    GVNW.card_fun_zmod (p:=p) (k-1)
  have hsum : (∑ u : Fin (k-1) → ZMod p, ∏ i : Fin k, f i
        (∑ t : Fin (k-1), (1 - c i * (c ⟨t.val+1, by omega⟩)⁻¹) * u t))
      = (p : ℝ)^(k-3) * (∑ x : ZMod p, ∑ r : ZMod p, ∏ i : Fin k, f i (x + c i * r)) := by
    have hcov := sum_phiC_cover (p:=p) hk c hc hc0
      (fun a b : ZMod p => ∏ i : Fin k, f i (a - c i * b))
    have hL : (∑ u : Fin (k-1) → ZMod p, ∏ i : Fin k, f i
          (∑ t : Fin (k-1), (1 - c i * (c ⟨t.val+1, by omega⟩)⁻¹) * u t))
        = (∑ u : Fin (k-1) → ZMod p, ∏ i : Fin k, f i
            ((∑ t, u t) - c i * (∑ t, u t * (c ⟨t.val+1, by omega⟩)⁻¹))) := by
      apply Finset.sum_congr rfl; intro u _
      apply Finset.prod_congr rfl; intro i _
      congr 1
      exact sum_one_sub_mul (c i) (fun t => (c ⟨t.val+1, by omega⟩)⁻¹) u
    have h1 : (∑ q : ZMod p × ZMod p, ∏ i : Fin k, f i (q.1 - c i * q.2))
        = (∑ q : ZMod p × ZMod p, ∏ i : Fin k, f i (q.1 + c i * q.2)) := by
      calc (∑ q : ZMod p × ZMod p, ∏ i : Fin k, f i (q.1 - c i * q.2))
          = (∑ q : ZMod p × ZMod p, ∏ i : Fin k, f i
              ((Equiv.prodCongr (Equiv.refl (ZMod p)) (Equiv.neg (ZMod p)) q).1
                + c i * (Equiv.prodCongr (Equiv.refl (ZMod p))
                    (Equiv.neg (ZMod p)) q).2)) := by
            apply Finset.sum_congr rfl; intro q _
            obtain ⟨a, b⟩ := q
            apply Finset.prod_congr rfl; intro i _
            have hfst : (Equiv.prodCongr (Equiv.refl (ZMod p)) (Equiv.neg (ZMod p)) (a, b)).1
                = a := rfl
            have hsnd : (Equiv.prodCongr (Equiv.refl (ZMod p)) (Equiv.neg (ZMod p)) (a, b)).2
                = -b := rfl
            rw [hfst, hsnd]
            congr 1
            ring
        _ = (∑ q : ZMod p × ZMod p, ∏ i : Fin k, f i (q.1 + c i * q.2)) :=
            Equiv.sum_comp (Equiv.prodCongr (Equiv.refl (ZMod p)) (Equiv.neg (ZMod p)))
              (fun q : ZMod p × ZMod p => ∏ i : Fin k, f i (q.1 + c i * q.2))
    have h2 : (∑ q : ZMod p × ZMod p, ∏ i : Fin k, f i (q.1 + c i * q.2))
        = (∑ x : ZMod p, ∑ r : ZMod p, ∏ i : Fin k, f i (x + c i * r)) := by
      rw [Fintype.sum_prod_type]
    rw [hL, hcov, h1, h2]
  rw [GVNW.Jw_last (X := ZMod p) (k := k) (by omega)
      (fun i y => ∑ t : Fin (k-1), (1 - c i * (c ⟨t.val+1, by omega⟩)⁻¹) * y t) f ν (by omega)]
  unfold GVNgen.av
  rw [hcard, hsum]
  have hc1 : ((p:ℝ)^(k-1))⁻¹ * (p:ℝ)^(k-3) = ((p:ℝ)^2)⁻¹ := by
    have hsplit : (p:ℝ)^(k-1) = (p:ℝ)^2 * (p:ℝ)^(k-3) := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit, mul_inv, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hpne), mul_one]
  rw [← mul_assoc, hc1]

end Commons.Combinatorics.Additive.Gowers
