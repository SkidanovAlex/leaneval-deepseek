import Mathlib
import Submission.Work.A3.polydiff_spec
import Submission.Work.A3.norm_completeSum_sq_le
import Submission.Work.A3.sum_shift_eq
import Submission.Work.A3.linear_completeSum_bound
import Submission.Work.A3.sum_factorization_rpow_le
import Submission.Work.A3.completeSum_prod_bound
import Submission.Work.A3.card_primeFactors_rpow_le

/-!
# Power saving for complete exponential sums (Area A3 of the circle method)

For a polynomial `Q ∈ ℤ[X]` of degree `d ≥ 2` there are `δ > 0` and `C` with

`‖completeSum Q a q‖ ≤ C * q ^ (1 - δ)`      (`q ≥ 1`, `(a, q) = 1`),

where `completeSum Q a q = ∑_{r < q} e(-2πi a Q(r)/q)`
(`Submission/Work/A3/Circle.lean`).  This is the "complete sums are power-saving" input of the
Hardy–Littlewood circle method for polynomial exponential sums.

## The proof

Everything is Weyl differencing, with the degree as the induction variable.  For a prime power
modulus `p ^ ν` the key identity is

`‖completeSum g a (p^ν)‖ ^ 2 ≤ ∑_{h < p^ν} ‖∑_{r < p^ν} e(-2πi a (g(r+h) - g(r))/p^ν)‖`
(`norm_completeSum_sq_le`), and for the differenced sums one uses the divided difference
`polydiff g h = (g(X+h) - g(X))/h` (`CSPoly.polydiff`, with its degree and leading coefficient
computed by `polydiff_spec`):  writing `h = p^k u` with `p ∤ u`, the shift identity
`sum_shift_eq_general` turns the shift by `h` into `p^k` times a complete sum of `polydiff g h`
modulo the *smaller* prime power `p^(ν-k)`, and `polydiff g h` has degree `e - 1` and leading
coefficient `e * lc g` — independent of `h`.  That makes the induction on the degree close:
`prime_pow_bound` proves that for every degree `e ≥ 1` there are `A ≥ 1` and `θ, η ∈ (0, 1/2]` with

`‖completeSum g a (p^ν)‖ ≤ A * gcd(e! * |lc g|, p^ν)^θ * p^(ν (1-η))`

for every prime `p`, every `ν ≥ 1` and every `a` prime to `p`; the only thing that grows is the
power saving, `η ↦ η/2`, and the `!`-factor `e!` is exactly what keeps track of the leading
coefficients along the differencing.  The count of the shifts of a given `p`-adic valuation
(`sum_factorization_rpow_le`) shows that the sum over `h` costs only a constant.

The passage from prime powers to an arbitrary modulus is the Chinese remainder theorem
(`completeSum_mul_eq`) plus the bookkeeping `ω(q)`-versus-`q` of `card_primeFactors_rpow_le`:
`completeSum_prod_bound` gives `C₀^{ω(q)} * q^(1-η)`, and the number of distinct prime factors is
sub-polynomial, so it is absorbed by letting `δ = η/2`.
-/

open Polynomial Finset
open scoped Real

namespace Work.A3

noncomputable section

/-- The differenced exponential sum `T_h = Σ_{r<n} e(-2πi a (g(r+h) - g(r))/n)`. -/

def shiftSum (g : Polynomial ℤ) (a : ℤ) (n : ℕ) (h : ℕ) : ℂ :=
  ∑ r ∈ Finset.range n,
    Complex.exp (-(2 * Real.pi * Complex.I) *
      (((a * (g.eval ((r : ℤ) + (h : ℤ)) - g.eval (r : ℤ)) : ℤ) : ℝ) / (n : ℝ)))

lemma norm_shiftSum_le (g : Polynomial ℤ) (a : ℤ) (n : ℕ) (h : ℕ) :
    ‖shiftSum g a n h‖ ≤ (n : ℝ) := by
  have h1 : (∑ r ∈ Finset.range n, ‖Complex.exp (-(2 * Real.pi * Complex.I) *
        (((a * (g.eval ((r : ℤ) + (h : ℤ)) - g.eval (r : ℤ)) : ℤ) : ℝ) / ((n : ℕ) : ℝ)))‖)
      = (n : ℝ) := by
    rw [show (∑ r ∈ Finset.range n, ‖Complex.exp (-(2 * Real.pi * Complex.I) *
        (((a * (g.eval ((r : ℤ) + (h : ℤ)) - g.eval (r : ℤ)) : ℤ) : ℝ) / ((n : ℕ) : ℝ)))‖)
        = ∑ _r ∈ Finset.range n, (1:ℝ) from ?_]
    · simp
    · apply Finset.sum_congr rfl; intro r _
      rw [Complex.norm_exp]; simp
  have h2 := norm_sum_le (Finset.range n) (fun r => Complex.exp (-(2 * Real.pi * Complex.I) *
        (((a * (g.eval ((r : ℤ) + (h : ℤ)) - g.eval (r : ℤ)) : ℤ) : ℝ) / ((n : ℕ) : ℝ))))
  rw [h1] at h2
  exact h2

lemma natCast_pow_rpow (p ν : ℕ) (r : ℝ) :
    (((p ^ ν : ℕ) : ℝ)) ^ r = (p : ℝ) ^ ((ν : ℝ) * r) := by
  rw [Nat.cast_pow, ← Real.rpow_natCast, Real.rpow_mul (by positivity)]

lemma sqrt_rpow_eq (x : ℝ) (hx : 0 ≤ x) (r : ℝ) : Real.sqrt (x ^ r) = x ^ (r / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  ring_nf

/-- **Per-prime-power saving.**  For every degree `e ≥ 1` there are `A ≥ 1`, `θ, η ∈ (0, 1/2]`
such that every complete exponential sum of a degree `e` polynomial `g` modulo `p ^ ν` with
`p ∤ a` satisfies `‖completeSum g a (p^ν)‖ ≤ A · gcd(e! |lc g|, p^ν)^θ · p^{ν(1-η)}`. -/
theorem prime_pow_bound : ∀ e : ℕ, 1 ≤ e → ∃ (A θ η : ℝ), 1 ≤ A ∧ 0 < θ ∧ θ ≤ 1 ∧ 0 < η ∧
    η ≤ 1 / 2 ∧
    ∀ (p ν : ℕ) (g : Polynomial ℤ) (a : ℤ), p.Prime → 1 ≤ ν → g.natDegree = e →
      ¬ ((p : ℤ) ∣ a) →
      ‖completeSum g a (p ^ ν)‖ ≤ A *
        ((Nat.gcd (e.factorial * g.leadingCoeff.natAbs) (p ^ ν) : ℕ) : ℝ) ^ θ *
        (p : ℝ) ^ ((ν : ℝ) * (1 - η)) := by
  intro e
  induction e with
  | zero => intro h; omega
  | succ k ih =>
    intro _
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · -- base case, e = 1
      subst hk0
      refine ⟨1, 1/2, 1/2, le_refl 1, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
      intro p ν g a hp hν hdeg ha
      have hb := linear_completeSum_bound g hp hν hdeg a ha
      simp only [zero_add, Nat.factorial_one, one_mul]
      calc ‖completeSum g a (p ^ ν)‖
          ≤ ((Nat.gcd (g.leadingCoeff.natAbs) (p ^ ν) : ℕ) : ℝ) ^ (1/2 : ℝ) *
              (((p ^ ν : ℕ) : ℝ)) ^ (1/2 : ℝ) := hb
        _ = ((Nat.gcd (g.leadingCoeff.natAbs) (p ^ ν) : ℕ) : ℝ) ^ (1/2 : ℝ) *
              (p : ℝ) ^ ((ν:ℝ) * (1 / 2)) := by rw [natCast_pow_rpow]
        _ = ((Nat.gcd (g.leadingCoeff.natAbs) (p ^ ν) : ℕ) : ℝ) ^ (1/2 : ℝ) *
              (p : ℝ) ^ ((ν:ℝ) * (1 - 1/2)) := by norm_num
    · -- induction step, e = k+1 ≥ 2
      obtain ⟨A', θ', η', hA'1, hθ'0, hθ'1, hη'0, hη'1, IH⟩ := ih hkpos
      refine ⟨Real.sqrt (1 + 4 * A'), θ' / 2, η' / 2, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [Real.one_le_sqrt]; linarith
      · linarith
      · linarith
      · linarith
      · linarith
      · intro p ν g a hp hν hdeg ha
        have hpR1 : (1:ℝ) < (p:ℝ) := by exact_mod_cast (by have := hp.two_le; omega : 1 < p)
        have hpR0 : (0:ℝ) < (p:ℝ) := by linarith
        have hn1 : 1 ≤ p ^ ν := Nat.one_le_pow ν p (by have := hp.two_le; omega)
        set D : ℕ := Nat.gcd ((k+1).factorial * g.leadingCoeff.natAbs) (p ^ ν) with hD
        have hD1 : (1:ℝ) ≤ (D:ℝ) := by
          have h1 : 1 ≤ D := by
            rw [hD]
            exact Nat.one_le_iff_ne_zero.mpr
              (Nat.gcd_ne_zero_right (pow_ne_zero ν (by have := hp.two_le; omega)))
          exact_mod_cast h1
        -- the per-shift bounds
        have hTne : ∀ h ∈ (Finset.range (p^ν)).filter (fun h => ¬ (h = 0)),
            ‖shiftSum g a (p^ν) h‖ ≤
              A' * (D:ℝ)^θ' * (p:ℝ)^(ν:ℝ) *
                (p:ℝ)^(-(((ν - h.factorization p : ℕ):ℝ) * η')) := by
          intro h hh
          simp only [Finset.mem_filter, Finset.mem_range] at hh
          obtain ⟨hhlt, hhne⟩ := hh
          have hv_lt : h.factorization p < ν := by
            by_contra hc
            rw [not_lt] at hc
            have hdvd : p ^ ν ∣ h := (hp.pow_dvd_iff_le_factorization hhne).mpr hc
            have hle : p ^ ν ≤ h := Nat.le_of_dvd (Nat.pos_of_ne_zero hhne) hdvd
            omega
          set v : ℕ := h.factorization p with hv
          set u : ℕ := h / p ^ v with hud
          have hpvdvd : p ^ v ∣ h := (hp.pow_dvd_iff_le_factorization hhne).mpr (le_refl v)
          have hheq : p ^ v * u = h := by rw [hud]; exact Nat.mul_div_cancel' hpvdvd
          have hvle : v ≤ ν := by omega
          have hu_not : ¬ ((p : ℤ) ∣ (u : ℤ)) := by
            intro hdiv
            have hpdu : p ∣ u := by exact_mod_cast hdiv
            have hdvd : p ^ (v + 1) ∣ h := by
              rw [← hheq, pow_succ]
              exact mul_dvd_mul_left _ hpdu
            have h2 := (hp.pow_dvd_iff_le_factorization hhne).mp hdvd
            rw [hv] at h2
            omega
          have hcast : (h : ℤ) = (p : ℤ) ^ v * (u : ℤ) := by
            rw [← hheq]; push_cast; ring
          have hshift := sum_shift_eq_general g a (u : ℤ) p ν v hp (le_of_lt hv_lt)
          have hshift' : shiftSum g a (p^ν) h =
              ((p : ℂ) ^ v) * completeSum (polydiff g ((p:ℤ)^v * (u:ℤ))) (a * (u:ℤ))
                (p ^ (ν - v)) := by
            simp only [shiftSum, hcast]
            exact hshift
          have hu0 : u ≠ 0 := by
            intro h0
            rw [h0, mul_zero] at hheq
            exact hhne hheq.symm
          have hpd_ne : ((p : ℤ) ^ v * (u : ℤ)) ≠ 0 :=
            mul_ne_zero (pow_ne_zero _ (by exact_mod_cast (show p ≠ 0 by have := hp.two_le; omega)))
              (by exact_mod_cast hu0)
          obtain ⟨hpdeval, hpddeg, hpd_lc⟩ :=
            polydiff_spec g ((p:ℤ)^v * (u:ℤ)) hdeg (by omega) hpd_ne
          have hIH := IH p (ν - v) (polydiff g ((p:ℤ)^v * (u:ℤ))) (a * (u:ℤ)) hp (by omega)
            hpddeg (by
              intro hdiv
              have hpp : Prime ((p:ℤ)) := Nat.prime_iff_prime_int.mp hp
              rcases (hpp.dvd_mul).mp hdiv with h1 | h1
              · exact ha h1
              · exact hu_not h1)
          have hgcdkey : k.factorial * (polydiff g ((p:ℤ)^v * (u:ℤ))).leadingCoeff.natAbs
              = (k+1).factorial * g.leadingCoeff.natAbs := by
            rw [hpd_lc, Int.natAbs_mul, Int.natAbs_natCast, Nat.factorial_succ]
            ring
          have hgcdle : ((Nat.gcd (k.factorial *
                (polydiff g ((p:ℤ)^v * (u:ℤ))).leadingCoeff.natAbs) (p^(ν-v)) : ℕ) : ℝ) ≤ (D:ℝ) := by
            have hdvdpow : p^(ν-v) ∣ p^ν := by
              have h2 : p^ν = p^(ν-v) * p^v := by
                conv_lhs => rw [show ν = (ν - v) + v by omega]
                rw [pow_add]
              rw [h2]
              exact dvd_mul_right _ _
            have hdiv : Nat.gcd ((k+1).factorial * g.leadingCoeff.natAbs) (p^(ν-v)) ∣ D := by
              rw [hD]
              exact Nat.gcd_dvd_gcd_of_dvd_right _ hdvdpow
            have hle : Nat.gcd ((k+1).factorial * g.leadingCoeff.natAbs) (p^(ν-v)) ≤ D :=
              Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ (by positivity)) hdiv
            rw [hgcdkey]
            exact_mod_cast hle
          have hnorm : ‖shiftSum g a (p^ν) h‖ ≤
              A' * (D:ℝ)^θ' * (p:ℝ)^(ν:ℝ) *
                (p:ℝ)^(-(((ν - v : ℕ) : ℝ) * η')) := by
            have h1 : ‖shiftSum g a (p^ν) h‖ =
                (p:ℝ)^(v:ℝ) * ‖completeSum (polydiff g ((p:ℤ)^v*(u:ℤ))) (a*(u:ℤ)) (p^(ν-v))‖ := by
              rw [hshift', norm_mul, norm_pow, Complex.norm_natCast, ← Real.rpow_natCast]
            have h2 : ‖completeSum (polydiff g ((p:ℤ)^v*(u:ℤ))) (a*(u:ℤ)) (p^(ν-v))‖ ≤
                A' * (D:ℝ)^θ' * (p:ℝ)^(((ν-v:ℕ):ℝ)*(1-η')) := by
              have h3 : ((Nat.gcd (k.factorial *
                    (polydiff g ((p:ℤ)^v * (u:ℤ))).leadingCoeff.natAbs) (p^(ν-v)) : ℕ) : ℝ) ^ θ'
                  ≤ (D:ℝ)^θ' :=
                Real.rpow_le_rpow (by positivity) hgcdle (le_of_lt hθ'0)
              calc ‖completeSum (polydiff g ((p:ℤ)^v*(u:ℤ))) (a*(u:ℤ)) (p^(ν-v))‖
                  ≤ A' * ((Nat.gcd (k.factorial *
                        (polydiff g ((p:ℤ)^v * (u:ℤ))).leadingCoeff.natAbs) (p^(ν-v)) : ℕ) : ℝ) ^ θ'
                      * (p:ℝ)^(((ν-v:ℕ):ℝ)*(1-η')) := hIH
                _ ≤ A' * (D:ℝ)^θ' * (p:ℝ)^(((ν-v:ℕ):ℝ)*(1-η')) := by
                      apply mul_le_mul_of_nonneg_right _ (by positivity)
                      exact mul_le_mul_of_nonneg_left h3 (by linarith)
            calc ‖shiftSum g a (p^ν) h‖
                = (p:ℝ)^(v:ℝ) *
                    ‖completeSum (polydiff g ((p:ℤ)^v*(u:ℤ))) (a*(u:ℤ)) (p^(ν-v))‖ := h1
              _ ≤ (p:ℝ)^(v:ℝ) *
                    (A' * (D:ℝ)^θ' * (p:ℝ)^(((ν-v:ℕ):ℝ)*(1-η'))) :=
                  mul_le_mul_of_nonneg_left h2 (by positivity)
              _ = A' * (D:ℝ)^θ' * (p:ℝ)^(ν:ℝ) *
                    (p:ℝ)^(-(((ν - v : ℕ) : ℝ) * η')) := by
                  have hsub : ((ν - v : ℕ) : ℝ) = (ν:ℝ) - (v:ℝ) := Nat.cast_sub hvle
                  rw [show (p:ℝ)^(v:ℝ) * (A' * (D:ℝ)^θ' * (p:ℝ)^(((ν-v:ℕ):ℝ)*(1-η')))
                        = (p:ℝ)^(v:ℝ) * (p:ℝ)^(((ν-v:ℕ):ℝ)*(1-η')) * (A' * (D:ℝ)^θ') from by ring,
                    ← Real.rpow_add hpR0 (v:ℝ) (((ν-v:ℕ):ℝ)*(1-η')),
                    show (v:ℝ) + ((ν - v : ℕ) : ℝ) * (1 - η') =
                      (ν:ℝ) + (-(((ν - v : ℕ) : ℝ) * η')) from by rw [hsub]; ring,
                    Real.rpow_add hpR0]
                  ring
          exact hnorm
        -- the sum
        have hsum : ∑ h ∈ Finset.range (p^ν), ‖shiftSum g a (p^ν) h‖ ≤
            ((p^ν:ℕ):ℝ) + A' * (D:ℝ)^θ' * (p:ℝ)^(ν:ℝ) * (4 * (p:ℝ)^((ν:ℝ)*(1-η'))) := by
          rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (p^ν)) (fun h => h = 0)]
          have h0mem : 0 ∈ Finset.range (p^ν) := Finset.mem_range.mpr (by omega)
          have hz : ∑ h ∈ (Finset.range (p^ν)).filter (fun h => h = 0), ‖shiftSum g a (p^ν) h‖
              ≤ ((p^ν:ℕ):ℝ) := by
            rw [Finset.filter_eq', if_pos h0mem, Finset.sum_singleton]
            exact norm_shiftSum_le g a (p^ν) 0
          have hne : ∑ h ∈ (Finset.range (p^ν)).filter (fun h => ¬ (h = 0)),
                ‖shiftSum g a (p^ν) h‖ ≤
              A' * (D:ℝ)^θ' * (p:ℝ)^(ν:ℝ) * (4 * (p:ℝ)^((ν:ℝ)*(1-η'))) := by
            calc ∑ h ∈ (Finset.range (p^ν)).filter (fun h => ¬ (h = 0)),
                  ‖shiftSum g a (p^ν) h‖
                ≤ ∑ h ∈ (Finset.range (p^ν)).filter (fun h => ¬ (h = 0)),
                    A' * (D:ℝ)^θ' * (p:ℝ)^(ν:ℝ) *
                      (p:ℝ)^(-(((ν - h.factorization p : ℕ):ℝ) * η')) :=
                  Finset.sum_le_sum hTne
              _ = A' * (D:ℝ)^θ' * (p:ℝ)^(ν:ℝ) *
                    ∑ h ∈ (Finset.range (p^ν)).filter (fun h => ¬ (h = 0)),
                      (p:ℝ)^(-(((ν - h.factorization p : ℕ):ℝ) * η')) := by
                  rw [Finset.mul_sum]
              _ ≤ A' * (D:ℝ)^θ' * (p:ℝ)^(ν:ℝ) * (4 * (p:ℝ)^((ν:ℝ)*(1-η'))) := by
                  apply mul_le_mul_of_nonneg_left _ (by positivity)
                  exact sum_factorization_rpow_le p ν hp hη'0 hη'1
          exact add_le_add hz hne
        -- reduce to the final shape
        have hpnu : ((p^ν:ℕ):ℝ) ≤ (D:ℝ)^θ' * (p:ℝ)^((2:ℝ)*(ν:ℝ) - (ν:ℝ)*η') := by
          rw [show ((p^ν:ℕ):ℝ) = (((p^ν:ℕ):ℝ))^((1:ℝ)) by rw [Real.rpow_one], natCast_pow_rpow]
          have h2 : (p:ℝ)^((ν:ℝ)*1) ≤ (p:ℝ)^((2:ℝ)*(ν:ℝ) - (ν:ℝ)*η') := by
            rw [Real.rpow_le_rpow_left_iff hpR1]
            have hν0 : (0:ℝ) ≤ (ν:ℝ) := Nat.cast_nonneg ν
            nlinarith [hη'0, hη'1, hν0]
          calc (p:ℝ)^((ν:ℝ)*1) ≤ (p:ℝ)^((2:ℝ)*(ν:ℝ) - (ν:ℝ)*η') := h2
            _ = 1 * (p:ℝ)^((2:ℝ)*(ν:ℝ) - (ν:ℝ)*η') := by ring
            _ ≤ (D:ℝ)^θ' * (p:ℝ)^((2:ℝ)*(ν:ℝ) - (ν:ℝ)*η') := by
                apply mul_le_mul_of_nonneg_right _ (by positivity)
                have hDθ : (1:ℝ) ≤ (D:ℝ)^θ' := by
                  have h1 := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hD1 (le_of_lt hθ'0)
                  rwa [Real.one_rpow] at h1
                exact hDθ
        have h4A : A' * (D:ℝ)^θ' * (p:ℝ)^(ν:ℝ) * (4 * (p:ℝ)^((ν:ℝ)*(1-η')))
            ≤ 4 * A' * (D:ℝ)^θ' * (p:ℝ)^((2:ℝ)*(ν:ℝ) - (ν:ℝ)*η') := by
          have h2 : (p:ℝ)^(ν:ℝ) * (p:ℝ)^((ν:ℝ)*(1-η')) = (p:ℝ)^((2:ℝ)*(ν:ℝ) - (ν:ℝ)*η') := by
            rw [← Real.rpow_add hpR0]
            congr 1
            ring
          have heq : A' * (D:ℝ)^θ' * (p:ℝ)^(ν:ℝ) * (4 * (p:ℝ)^((ν:ℝ)*(1-η')))
              = 4 * A' * (D:ℝ)^θ' * (p:ℝ)^((2:ℝ)*(ν:ℝ) - (ν:ℝ)*η') := by
            rw [show A' * (D:ℝ)^θ' * (p:ℝ)^(ν:ℝ) * (4 * (p:ℝ)^((ν:ℝ)*(1-η')))
                  = 4 * (A' * (D:ℝ)^θ') * ((p:ℝ)^(ν:ℝ) * (p:ℝ)^((ν:ℝ)*(1-η'))) from by ring, h2]
            ring
          exact le_of_eq heq
        have hfinal : ∑ h ∈ Finset.range (p^ν), ‖shiftSum g a (p^ν) h‖ ≤
            (1 + 4 * A') * (D:ℝ)^θ' * (p:ℝ)^((2:ℝ)*(ν:ℝ) - (ν:ℝ)*η') := by
          calc ∑ h ∈ Finset.range (p^ν), ‖shiftSum g a (p^ν) h‖
              ≤ ((p^ν:ℕ):ℝ) + A' * (D:ℝ)^θ' * (p:ℝ)^(ν:ℝ) *
                  (4 * (p:ℝ)^((ν:ℝ)*(1-η'))) := hsum
            _ ≤ (D:ℝ)^θ' * (p:ℝ)^((2:ℝ)*(ν:ℝ) - (ν:ℝ)*η') +
                  4 * A' * (D:ℝ)^θ' * (p:ℝ)^((2:ℝ)*(ν:ℝ) - (ν:ℝ)*η') :=
                  add_le_add hpnu h4A
            _ = (1 + 4 * A') * (D:ℝ)^θ' * (p:ℝ)^((2:ℝ)*(ν:ℝ) - (ν:ℝ)*η') := by ring
        -- final
        have hsqrt : Real.sqrt ((1 + 4 * A') * (D:ℝ)^θ' * (p:ℝ)^((2:ℝ)*(ν:ℝ) - (ν:ℝ)*η'))
            = Real.sqrt (1 + 4*A') * (D:ℝ)^(θ'/2) * (p:ℝ)^((ν:ℝ)*(1-η'/2)) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
            sqrt_rpow_eq D (by positivity), sqrt_rpow_eq p (by positivity)]
          rw [show ((2:ℝ)*(ν:ℝ) - (ν:ℝ)*η')/2 = (ν:ℝ)*(1-η'/2) by ring]
        calc ‖completeSum g a (p ^ ν)‖
            = Real.sqrt (‖completeSum g a (p ^ ν)‖^2) := (Real.sqrt_sq (norm_nonneg _)).symm
          _ ≤ Real.sqrt ((1 + 4 * A') * (D:ℝ)^θ' * (p:ℝ)^((2:ℝ)*(ν:ℝ) - (ν:ℝ)*η')) := by
              apply Real.sqrt_le_sqrt
              exact le_trans (norm_completeSum_sq_le g a hn1) hfinal
          _ = Real.sqrt (1 + 4*A') * (D:ℝ)^(θ'/2) * (p:ℝ)^((ν:ℝ)*(1-η'/2)) := hsqrt
          _ = Real.sqrt (1 + 4 * A') *
                ((Nat.gcd ((k+1).factorial * g.leadingCoeff.natAbs) (p ^ ν) : ℕ) : ℝ) ^ (θ'/2) *
                (p:ℝ)^((ν:ℝ) * (1 - η'/2)) := by rw [hD]


theorem completeSum_power_saving (Q : Polynomial ℤ) (hd : 2 ≤ Polynomial.natDegree Q) :
    ∃ (δ : ℝ) (C : ℝ), 0 < δ ∧ 0 < C ∧ ∀ (q : ℕ) (a : ℤ), 1 ≤ q → IsCoprime a (q : ℤ) →
      ‖Work.A3.completeSum Q a q‖ ≤ C * (q : ℝ) ^ (1 - δ) := by
  obtain ⟨A, θ, η, hA, hθ0, hθ1, hη0, hη1, H⟩ := prime_pow_bound Q.natDegree (by omega)
  set M : ℕ := Q.natDegree.factorial * Q.leadingCoeff.natAbs with hM
  have hQlc : Q.leadingCoeff ≠ 0 := by
    intro h
    rw [Polynomial.leadingCoeff_eq_zero] at h
    rw [h] at hd
    simp at hd
  have hM1 : 1 ≤ M := by
    rw [hM]
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Int.natAbs_ne_zero.mpr hQlc))
  set C₀ : ℝ := A * (M:ℝ)^θ with hC₀
  have hC₀1 : 1 ≤ C₀ := by
    rw [hC₀]
    have hMr : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM1
    have h1 : (1:ℝ) ≤ (M:ℝ)^θ := by
      have h2 := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hMr (le_of_lt hθ0)
      rwa [Real.one_rpow] at h2
    nlinarith [hA, h1]
  have hpp : ∀ (p ν : ℕ) (a : ℤ), p.Prime → 1 ≤ ν → IsCoprime a ((p^ν : ℕ) : ℤ) →
      ‖completeSum Q a (p^ν)‖ ≤ C₀ * ((p^ν : ℕ) : ℝ) ^ (1 - η) := by
    intro p ν a hp hν ha
    have hpnd : ¬ ((p:ℤ) ∣ a) := by
      intro hpa
      have hg : Int.gcd a ((p^ν : ℕ) : ℤ) = 1 := Int.isCoprime_iff_gcd_eq_one.mp ha
      have hpg : p ∣ Int.gcd a ((p^ν : ℕ) : ℤ) :=
        Int.dvd_gcd hpa (by exact_mod_cast dvd_pow_self p (by omega))
      rw [hg] at hpg
      have h1 : p ≤ 1 := Nat.le_of_dvd (by norm_num) hpg
      have hp2 : 2 ≤ p := hp.two_le
      omega
    have hb := H p ν Q a hp hν rfl hpnd
    have hgcd : ((Nat.gcd (Q.natDegree.factorial * Q.leadingCoeff.natAbs) (p^ν) : ℕ) : ℝ) ≤ (M:ℝ) := by
      rw [hM]
      have hpos : 0 < Q.natDegree.factorial * Q.leadingCoeff.natAbs :=
        Nat.mul_pos (Nat.factorial_pos _) (Int.natAbs_pos.mpr hQlc)
      exact_mod_cast Nat.gcd_le_left (p^ν) hpos
    have hgcdθ : ((Nat.gcd (Q.natDegree.factorial * Q.leadingCoeff.natAbs) (p^ν) : ℕ) : ℝ)^θ
        ≤ (M:ℝ)^θ := Real.rpow_le_rpow (by positivity) hgcd (le_of_lt hθ0)
    calc ‖completeSum Q a (p^ν)‖
        ≤ A * ((Nat.gcd (Q.natDegree.factorial * Q.leadingCoeff.natAbs) (p^ν) : ℕ) : ℝ)^θ *
            (p:ℝ)^((ν:ℝ)*(1-η)) := hb
      _ ≤ A * (M:ℝ)^θ * (p:ℝ)^((ν:ℝ)*(1-η)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_left hgcdθ (by linarith)
      _ = C₀ * ((p^ν : ℕ) : ℝ) ^ (1 - η) := by
            rw [hC₀, ← natCast_pow_rpow]
  obtain ⟨D, hDpos, hDle⟩ := card_primeFactors_rpow_le C₀ hC₀1 (by linarith : 0 < η/2)
  refine ⟨η/2, max D 1, by linarith, lt_max_of_lt_right zero_lt_one, ?_⟩
  intro q a hq ha
  have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  calc ‖completeSum Q a q‖ ≤ C₀ ^ q.primeFactors.card * (q:ℝ)^(1-η) :=
        completeSum_prod_bound Q C₀ η hC₀1 hη0 hpp q a hq ha
    _ ≤ D * (q:ℝ)^(η/2) * (q:ℝ)^(1-η) :=
        mul_le_mul_of_nonneg_right (hDle q hq) (by positivity)
    _ = D * (q:ℝ)^(1 - η/2) := by
        rw [mul_assoc, ← Real.rpow_add hq0]
        congr 2
        ring
    _ ≤ max D 1 * (q:ℝ)^(1 - η/2) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

end

end Work.A3
