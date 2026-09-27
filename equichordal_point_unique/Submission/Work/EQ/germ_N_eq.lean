import Mathlib
import Submission.Work.EQ.Defs

/-!
# `germ_N_eq`: a rational germ for `h` has numerator `c * X` and denominator value `-c`

If the stable germ `h` (`h 0 = 0`, `h' 0 = -1`) of the equichordal half map agrees near `0`
with the rational function `N / D` (`D 0 ≠ 0`) and the numerator `N` has no root besides `0`,
then `N` is a non-zero multiple of `X` and `D 0 = -N.leadingCoeff`.

The proof is elementary and only uses `h 0 = 0`, `h' 0 = -1` and the analyticity of `h`:

* differentiating the eventual identity `h u * D u = N u` at `u = 0` gives
  `-D 0 + h 0 * D' 0 = N' 0`, and since all roots of `N` vanish, `N = c * X ^ k` with
  `k = N.natDegree`, so `N' 0 = c * k * 0 ^ (k - 1)`;
* `N 0 = 0` (from the same identity, by continuity) forces `k ≥ 1`;
* if `k ≥ 2` then `N' 0 = 0`, contradicting `D 0 ≠ 0`; hence `k = 1` and `D 0 = -c`.
-/

namespace Work.EQ

open Filter Polynomial

/-- A nonzero complex polynomial all of whose roots are `0` is `C (leadingCoeff) * X ^ natDegree`.

Over an algebraically closed field `p = C p.leadingCoeff * ∏ (X - C z)`, and every factor of the
product is `X` because every root is `0`. -/
private lemma eq_C_mul_X_pow_of_forall_root_eq_zero {p : Polynomial ℂ} (hp : p ≠ 0)
    (h : ∀ z : ℂ, Polynomial.eval z p = 0 → z = 0) :
    p = Polynomial.C p.leadingCoeff * Polynomial.X ^ p.natDegree := by
  have hsplit := IsAlgClosed.splits p
  have hprod : (p.roots.map (fun z => Polynomial.X - Polynomial.C z)).prod
      = Polynomial.X ^ p.natDegree := by
    have hmap : p.roots.map (fun z => Polynomial.X - Polynomial.C z)
        = Multiset.replicate p.roots.card Polynomial.X := by
      rw [← Multiset.map_const' p.roots Polynomial.X]
      exact Multiset.map_congr rfl (fun z hz => by
        have hz0 : z = 0 := h z (by
          have := (Polynomial.mem_roots hp).mp hz
          simpa [Polynomial.IsRoot.def] using this)
        rw [hz0]; simp)
    rw [hmap, Multiset.prod_replicate, hsplit.natDegree_eq_card_roots]
  conv_lhs => rw [hsplit.eq_prod_roots]
  rw [hprod]

theorem germ_N_eq {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : Work.EQ.IsStableGerm a h r) {N D : Polynomial ℂ} (hD0 : Polynomial.eval 0 D ≠ 0)
    (hDN : ∀ᶠ u in nhds (0 : ℂ), h u * Polynomial.eval u D = Polynomial.eval u N) (hN : N ≠ 0)
    (hroots : ∀ z : ℂ, Polynomial.eval z N = 0 → z = 0) :
    ∃ c : ℂ, c ≠ 0 ∧ N = Polynomial.C c * Polynomial.X ∧ Polynomial.eval 0 D = -c := by
  obtain ⟨hr, hana, hh0, hhderiv, _him, _hfe⟩ := hh
  -- `0` lies in the disc of analyticity of `h`
  have hmem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_self]; exact hr
  have hcont : ContinuousAt h 0 := (hana 0 hmem).continuousAt
  have hDcont : ContinuousAt (fun u : ℂ => Polynomial.eval u D) 0 :=
    (Polynomial.differentiableAt (p := D) (x := 0)).continuousAt
  have hNcont : ContinuousAt (fun u : ℂ => Polynomial.eval u N) 0 :=
    (Polynomial.differentiableAt (p := N) (x := 0)).continuousAt
  -- Step 1: `N 0 = 0`, from the eventual identity and the continuity of both sides at `0`.
  have hN0 : Polynomial.eval 0 N = 0 := by
    have hFcont : ContinuousAt (fun u : ℂ => h u * Polynomial.eval u D - Polynomial.eval u N) 0 :=
      (hcont.mul hDcont).sub hNcont
    have hFev : (fun u : ℂ => h u * Polynomial.eval u D - Polynomial.eval u N)
        =ᶠ[nhds (0 : ℂ)] (fun _ => (0 : ℂ)) := by
      filter_upwards [hDN] with u hu
      rw [hu, sub_self]
    have hlim : Tendsto (fun u : ℂ => h u * Polynomial.eval u D - Polynomial.eval u N)
        (nhds (0 : ℂ)) (nhds (0 : ℂ)) :=
      tendsto_const_nhds.congr' hFev.symm
    have h0 := tendsto_nhds_unique hFcont.tendsto hlim
    have h1 := sub_eq_zero.mp h0
    rw [hh0, zero_mul] at h1
    exact h1.symm
  -- Step 2: `N = c * X ^ k` with `c = N.leadingCoeff ≠ 0` and `k = N.natDegree`.
  set c : ℂ := N.leadingCoeff with hc
  set k : ℕ := N.natDegree with hk
  have hc0 : c ≠ 0 := by rw [hc]; exact Polynomial.leadingCoeff_ne_zero.mpr hN
  have hNeq : N = Polynomial.C c * Polynomial.X ^ k := by
    rw [hc, hk]
    exact eq_C_mul_X_pow_of_forall_root_eq_zero hN hroots
  have hkpos : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · exfalso
      have hNc : Polynomial.eval 0 N = c := by rw [hNeq, hk0]; simp
      rw [hN0] at hNc
      exact hc0 hNc.symm
    · exact hkpos
  -- Step 3: differentiate the eventual identity at `0`.
  have hhder : HasDerivAt h (-1) 0 := by
    have h1 : HasDerivAt h (deriv h 0) 0 := (hana 0 hmem).differentiableAt.hasDerivAt
    rwa [hhderiv] at h1
  have hprod : HasDerivAt (fun u : ℂ => h u * Polynomial.eval u D)
      (-1 * Polynomial.eval 0 D + h 0 * Polynomial.eval 0 D.derivative) 0 :=
    hhder.mul (Polynomial.hasDerivAt D 0)
  have hder : deriv (fun u : ℂ => h u * Polynomial.eval u D) 0
      = deriv (fun u : ℂ => Polynomial.eval u N) 0 :=
    Filter.EventuallyEq.deriv_eq (show (fun u : ℂ => h u * Polynomial.eval u D)
      =ᶠ[nhds (0 : ℂ)] (fun u : ℂ => Polynomial.eval u N) from hDN)
  have key : -Polynomial.eval 0 D = (c * (k : ℂ)) * (0 : ℂ) ^ (k - 1) := by
    have h1 : deriv (fun u : ℂ => h u * Polynomial.eval u D) 0
        = -1 * Polynomial.eval 0 D + h 0 * Polynomial.eval 0 D.derivative := hprod.deriv
    have h2 : deriv (fun u : ℂ => Polynomial.eval u N) 0 = Polynomial.eval 0 N.derivative :=
      (Polynomial.hasDerivAt N 0).deriv
    have h3 : Polynomial.eval 0 N.derivative = (c * (k : ℂ)) * (0 : ℂ) ^ (k - 1) := by
      rw [hNeq, Polynomial.derivative_C_mul_X_pow]
      simp
    have h4 : -1 * Polynomial.eval 0 D + h 0 * Polynomial.eval 0 D.derivative
        = (c * (k : ℂ)) * (0 : ℂ) ^ (k - 1) := by
      rw [← h1, hder, h2, h3]
    rw [hh0] at h4
    simpa using h4
  -- Step 4: `k = 1`, and then `D 0 = -c`.
  rcases eq_or_lt_of_le hkpos with hk1 | hk2
  · have hk1' : k = 1 := hk1.symm
    refine ⟨c, hc0, by simpa [hk1'] using hNeq, ?_⟩
    have h5 : -Polynomial.eval 0 D = c := by simpa [hk1'] using key
    exact neg_eq_iff_eq_neg.mp h5
  · exfalso
    have hpow : (0 : ℂ) ^ (k - 1) = 0 := zero_pow (by omega : k - 1 ≠ 0)
    have h5 : -Polynomial.eval 0 D = 0 := by simpa [hpow] using key
    exact hD0 (neg_eq_zero.mp h5)

end Work.EQ
