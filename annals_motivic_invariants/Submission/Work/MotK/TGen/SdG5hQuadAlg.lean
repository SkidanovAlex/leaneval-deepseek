import Mathlib
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.TGen

theorem SdG5hQuadAlg {K : Type} [Field K] (h5 : ringChar K ≠ 5)
    (g1 g2 g3 g4 g5 p q r s t : K)
    (h1 : g1 ≠ 0) (h2 : g2 ≠ 0) (h3 : g3 ≠ 0) (hpq : p * q ≠ 0)
    (hQ1 : p ^ 4 - 3 * p ^ 2 * r + r ^ 2 = 0)
    (hQ3 : p ^ 3 * s + 3 * p ^ 2 * q * r - 4 * p * r * s - 2 * q * r ^ 2 = 0)
    (hD : g4 * q = g1 * (4 * p * q ^ 3 - 6 * p * q * t - 3 * q ^ 2 * s + 2 * s * t))
    (hE : g4 * s = g1 * (3 * p ^ 2 * q * t + 3 * p * q ^ 2 * s - 4 * p * s * t + q ^ 3 * r
      - 4 * q * r * t - 2 * q * s ^ 2))
    (hF : g2 = g1 * (2 * p * r ^ 2 - p ^ 3 * r))
    (hG : g5 = -g1 * (4 * p ^ 3 * q - 3 * p ^ 2 * s - 6 * p * q * r + 2 * r * s)) :
    g5 ^ 2 = 5 * g2 * g4 := by
  obtain ⟨hp, hq⟩ := mul_ne_zero_iff.mp hpq
  have hp2 : p ^ 2 ≠ 0 := pow_ne_zero 2 hp
  have h4 : p ^ 4 ≠ 0 := pow_ne_zero 4 hp
  have h5K : (5 : K) ≠ 0 := fun h => h5 (CharP.ringChar_of_prime_eq_zero (by norm_num) h)
  set rho : K := r / p ^ 2 with hrhodef
  have hr : r = p ^ 2 * rho := by rw [hrhodef, mul_div_cancel₀ r hp2]
  have hρ : rho ^ 2 - 3 * rho + 1 = 0 := by
    have hQ1' := hQ1
    rw [hr] at hQ1'
    have key : p ^ 4 * (rho ^ 2 - 3 * rho + 1) = 0 := by linear_combination hQ1'
    exact (mul_eq_zero.mp key).resolve_left h4
  have hfact : (4 * rho - 1) * (4 * rho - 11) = -5 := by linear_combination (16 : K) * hρ
  have h4rho : 4 * rho - 1 ≠ 0 := by
    intro hz
    have hzero : (5 : K) = 0 := by
      have hh := hfact
      rw [hz, zero_mul] at hh
      exact neg_eq_zero.mp hh.symm
    exact h5K hzero
  have h14rho : (1 : K) - 4 * rho ≠ 0 := by
    rw [show (1 : K) - 4 * rho = -(4 * rho - 1) by ring]
    exact neg_ne_zero.mpr h4rho
  have hs : s = p * q * (2 - rho) := by
    have key : p * ((p ^ 2 - 4 * r) * s - p * q * (3 * r - 2 * p ^ 2)) = 0 := by
      linear_combination (norm := first | refl_ring1 | ring1) hQ3 + (2 * q) * hQ1
    have key2 : (p ^ 2 - 4 * r) * s - p * q * (3 * r - 2 * p ^ 2) = 0 :=
      (mul_eq_zero.mp key).resolve_left hp
    rw [hr] at key2
    have key3 : p ^ 2 * ((1 - 4 * rho) * s - p * q * (3 * rho - 2)) = 0 := by
      linear_combination (norm := first | refl_ring1 | ring1) key2
    have key4 : (1 - 4 * rho) * s - p * q * (3 * rho - 2) = 0 :=
      (mul_eq_zero.mp key3).resolve_left hp2
    have hfac : (2 - rho) * (1 - 4 * rho) = 3 * rho - 2 := by linear_combination (4 : K) * hρ
    rw [← hfac] at key4
    have hkey4 : (1 - 4 * rho) * (s - p * q * (2 - rho)) = 0 := by linear_combination key4
    exact sub_eq_zero.mp ((mul_eq_zero.mp hkey4).resolve_left h14rho)
  have hrel : s * (4 * p * q ^ 3 - 6 * p * q * t - 3 * q ^ 2 * s + 2 * s * t)
      - q * (3 * p ^ 2 * q * t + 3 * p * q ^ 2 * s - 4 * p * s * t + q ^ 3 * r
        - 4 * q * r * t - 2 * q * s ^ 2) = 0 := by
    have h3 : g1 * (4 * p * q ^ 3 - 6 * p * q * t - 3 * q ^ 2 * s + 2 * s * t) * s
        = g1 * (3 * p ^ 2 * q * t + 3 * p * q ^ 2 * s - 4 * p * s * t + q ^ 3 * r
            - 4 * q * r * t - 2 * q * s ^ 2) * q := by
      have e1 : g4 * q * s
          = g1 * (4 * p * q ^ 3 - 6 * p * q * t - 3 * q ^ 2 * s + 2 * s * t) * s := by
        rw [hD]
      have e2 : g4 * s * q
          = g1 * (3 * p ^ 2 * q * t + 3 * p * q ^ 2 * s - 4 * p * s * t + q ^ 3 * r
              - 4 * q * r * t - 2 * q * s ^ 2) * q := by
        rw [hE]
      rw [← e1, ← e2]; ring
    have hthis : g1 * ((4 * p * q ^ 3 - 6 * p * q * t - 3 * q ^ 2 * s + 2 * s * t) * s
        - (3 * p ^ 2 * q * t + 3 * p * q ^ 2 * s - 4 * p * s * t + q ^ 3 * r
            - 4 * q * r * t - 2 * q * s ^ 2) * q) = 0 := by
      linear_combination (norm := first | refl_ring1 | ring1) h3
    have hzero := (mul_eq_zero.mp hthis).resolve_left h1
    linear_combination (norm := first | refl_ring1 | ring1) hzero
  have ht : t = q ^ 2 * (3 - rho) := by
    have hrel' : (4 * rho - 1) * t = q ^ 2 * (1 + rho) := by
      have key : p ^ 2 * q ^ 2 * ((4 * rho - 1) * t - q ^ 2 * (1 + rho)) = 0 := by
        rw [hr, hs] at hrel
        linear_combination (norm := first | refl_ring1 | ring1) hrel + (p ^ 2 * q ^ 2 * (q ^ 2 - 2 * t)) * hρ
      have key2 : (4 * rho - 1) * t - q ^ 2 * (1 + rho) = 0 :=
        (mul_eq_zero.mp key).resolve_left (mul_ne_zero hp2 (pow_ne_zero 2 hq))
      exact sub_eq_zero.mp key2
    have hfac : (4 * rho - 1) * (3 - rho) = 1 + rho := by linear_combination (-4 : K) * hρ
    rw [← hfac] at hrel'
    have hthis : (4 * rho - 1) * (t - q ^ 2 * (3 - rho)) = 0 := by linear_combination hrel'
    exact sub_eq_zero.mp ((mul_eq_zero.mp hthis).resolve_left h4rho)
  have hkey : q * (4 * p ^ 3 * q - 3 * p ^ 2 * s - 6 * p * q * r + 2 * r * s) ^ 2
      = 5 * (2 * p * r ^ 2 - p ^ 3 * r) * (4 * p * q ^ 3 - 6 * p * q * t - 3 * q ^ 2 * s
          + 2 * s * t) := by
    rw [hr, hs, ht]
    linear_combination (norm := first | refl_ring1 | ring1) (-4 * p ^ 6 * q ^ 3 * (4 * rho ^ 2 + 8 * rho - 1)) * hρ
  have hg4 : g4 = g1 * (4 * p * q ^ 3 - 6 * p * q * t - 3 * q ^ 2 * s + 2 * s * t) / q := by
    rw [eq_div_iff hq]; exact hD
  rw [hG, hF, hg4]
  have hg : 5 * (g1 * (2 * p * r ^ 2 - p ^ 3 * r))
        * (g1 * (4 * p * q ^ 3 - 6 * p * q * t - 3 * q ^ 2 * s + 2 * s * t) / q)
      = (5 * (g1 * (2 * p * r ^ 2 - p ^ 3 * r))
        * (g1 * (4 * p * q ^ 3 - 6 * p * q * t - 3 * q ^ 2 * s + 2 * s * t))) / q := by
    ring_nf
  rw [hg, eq_div_iff hq]
  linear_combination (norm := first | refl_ring1 | ring1) (g1 ^ 2) * hkey

end Work.MotK.TGen
