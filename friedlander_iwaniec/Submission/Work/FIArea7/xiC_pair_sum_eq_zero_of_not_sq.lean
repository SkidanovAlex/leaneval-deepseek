import Mathlib
import Submission.Work.FIArea7.sum_xiGaussMod_units
import Submission.Work.FIArea7.jacobiSym_sq_add_sq
import Submission.Work.FIArea7.sum_xiC_coprime
import Submission.Work.FIArea7.sum_jacobiSym_eq_zero_of_oddPart_not_sq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea7

open Finset
open scoped BigOperators

noncomputable section

/-! ## Auxiliary facts -/

/-- `|z|² = (Re z)² + (Im z)²` in `ℕ` (with `natAbs`). -/
lemma gnorm_eq_reSq_add_imSq (z : GaussianInt) :
    Work.FIPlan.gnorm z = z.re.natAbs ^ 2 + z.im.natAbs ^ 2 := by
  have h1 : z.re * z.re = ((z.re.natAbs ^ 2 : ℕ) : ℤ) := by
    rw [← Int.natAbs_mul_self (a := z.re)]; push_cast; ring
  have h2 : z.im * z.im = ((z.im.natAbs ^ 2 : ℕ) : ℤ) := by
    rw [← Int.natAbs_mul_self (a := z.im)]; push_cast; ring
  rw [Work.FIPlan.gnorm, Zsqrtd.norm_def]
  have h3 : z.re * z.re - -1 * z.im * z.im
      = ((z.re.natAbs ^ 2 + z.im.natAbs ^ 2 : ℕ) : ℤ) := by
    rw [show z.re * z.re - -1 * z.im * z.im = z.re * z.re + z.im * z.im by ring]
    rw [h1, h2]; push_cast; ring
  rw [h3, Int.natAbs_natCast]

/-- The Jacobi symbol `(m | N)` depends on `m` only through its class in `ZMod N`:
it agrees with the value read off the canonical representative of `(m : ZMod N)`. -/
lemma jacobiSym_zmod_val (m : ℤ) (N : ℕ) [NeZero N] :
    jacobiSym (((m : ZMod N)).val : ℤ) N = jacobiSym m N := by
  rw [ZMod.val_intCast]
  exact (jacobiSym.mod_left m N).symm

/-- **The Jacobi symbol `(·|q)` is nontrivial on units for odd non-square `q`.**  Proof: the
complete sum `Σ_{x mod q} (x|q)` vanishes (`Sint_eq_zero_of_odd_not_sq`), the terms are `0` on
non-units, so the sum over the units vanishes; if every unit had value `1` the sum would be the
positive number `φ(q)`. -/
lemma jacobiSym_exists_neg_one (q : ℕ) (hodd : Odd q) (hq1 : 1 < q)
    (hsq : ∀ k : ℕ, q ≠ k ^ 2) :
    ∃ n : ℤ, IsCoprime (q : ℤ) n ∧ jacobiSym n q = -1 := by
  have hq0 : q ≠ 0 := by omega
  have hSint : Sint q = 0 := Sint_eq_zero_of_odd_not_sq q (by omega) hodd (fun k => hsq k)
  have hsum : ∑ x ∈ Finset.range q, (jacobiSym (x : ℤ) q : ℝ) = 0 := by
    have h := Sint_eq_real q
    rw [hSint] at h
    simpa using h.symm
  have hex : ∃ x ∈ Finset.range q, jacobiSym (x : ℤ) q = -1 := by
    by_contra hcon
    push Not at hcon
    have hnonneg : ∀ x ∈ Finset.range q, (0 : ℝ) ≤ (jacobiSym (x : ℤ) q : ℝ) := by
      intro x hx
      rcases jacobiSym.trichotomy (x : ℤ) q with h | h | h
      · rw [h]; norm_num
      · rw [h]; norm_num
      · exact absurd h (hcon x hx)
    have hall := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum
    have h1mem : (1 : ℕ) ∈ Finset.range q := Finset.mem_range.mpr hq1
    have h1 := hall 1 h1mem
    simp only [Nat.cast_one, jacobiSym.one_left, Int.cast_one] at h1
    exact one_ne_zero h1
  obtain ⟨x, hxmem, hxJ⟩ := hex
  have hxgcd : Int.gcd (x : ℤ) (q : ℤ) = 1 := by
    by_contra h
    have h0 := (jacobiSym.eq_zero_iff (a := (x : ℤ)) (b := q)).mpr ⟨hq0, h⟩
    rw [h0] at hxJ
    norm_num at hxJ
  refine ⟨(x : ℤ), ?_, hxJ⟩
  rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
  exact hxgcd

/-- The product symbol `ξ_{w₁}(p)·ξ_{w₂}(p)`. -/
def xiCPair (q : ℕ) (w1 w2 : GaussianInt) (p : ZMod q × ZMod q) : ℂ :=
  xiC q w1 p * xiC q w2 p

/-- **`ξ_w` on the axis `(n, 0)` is the Jacobi symbol `(n | N)`** (for `ε_w = 1`, `N = |w|²`). -/
lemma xiC_inl_eq (N q : ℕ) [NeZero N] [NeZero q] (w : GaussianInt)
    (hd : N ∣ q) (hN : Work.FIPlan.gnorm w = N)
    (hε : jacobiSym w.re (Work.FIPlan.gnorm w) = 1) (n : ℤ) :
    xiC q w ((n : ZMod q), (0 : ZMod q)) = (jacobiSym n N : ℂ) := by
  have hε' : jacobiSym w.re N = 1 := by rw [← hN]; exact hε
  rw [xiC_cast_eq (N := N) (q := q) w hN ((n : ZMod q), (0 : ZMod q))]
  rw [show (ZMod.cast ((n : ZMod q)) : ZMod N) = (n : ZMod N) from
      ZMod.cast_intCast hd n]
  simp only [ZMod.cast_zero]
  rw [xiC_eq_linform N w hN ((n : ZMod N), (0 : ZMod N))]
  simp only [mul_zero, add_zero]
  have hz : (w.re : ZMod N) * (n : ZMod N) = ((w.re * n : ℤ) : ZMod N) := by
    push_cast; ring
  rw [hz, jacobiSym_zmod_val (w.re * n) N, jacobiSym.mul_left, hε', one_mul]

/-! ## The main theorem -/

/-- **The complete symbol sum of *FI* Lemma 21.1 vanishes unless the modulus is a perfect square.** For `w₁, w₂` primary with `(Re wᵢ, Im wᵢ) = 1` and `|wᵢ|² = Nᵢ`, if `N₁N₂` is not a perfect square then the complete sum of `ξ_{w₁}ξ_{w₂}` over `(ZMod (N₁N₂))²` vanishes.  Proof: `ξ_w` is multiplicative (`Work.FIArea7.xiC_mul_eps`, with `ε_w = (Re w | |w|²) = 1` by `jacobiSym_sq_add_sq`), hence so is `G = ξ_{w₁}ξ_{w₂}`.  For `n` coprime to `q := N₁N₂` the map `p ↦ (n·p₁, n·p₂)` is a bijection of `(ZMod q)²`, so `Σ_p G p = G (n,0) · Σ_p G p`; and `G (n,0) = ξ_{w₁}(n)ξ_{w₂}(n) = (n|N₁)(n|N₂) = (n|q)`.  Taking `n` with `(n|q) = -1` (`Work.FIArea7.jacobiSym_exists_eq_neg_one`, using that `q` is odd) gives `2·Σ_p G p = 0`. -/
theorem xiC_pair_sum_eq_zero_of_not_sq (N1 N2 : ℕ) [NeZero N1] [NeZero N2] (w1 w2 : GaussianInt)
    (h1 : Work.FIPlan.IsPrimary w1) (h2 : Work.FIPlan.IsPrimary w2)
    (hp1 : IsCoprime w1.re w1.im) (hp2 : IsCoprime w2.re w2.im)
    (hN1 : Work.FIPlan.gnorm w1 = N1) (hN2 : Work.FIPlan.gnorm w2 = N2)
    (hsq : ¬ ∃ s : ℕ, N1 * N2 = s ^ 2) :
    ∑ p : ZMod (N1 * N2) × ZMod (N1 * N2),
        Work.FIArea7.xiC (N1 * N2) w1 p * Work.FIArea7.xiC (N1 * N2) w2 p = 0 := by
  change ∑ p : ZMod (N1 * N2) × ZMod (N1 * N2), xiCPair (N1 * N2) w1 w2 p = 0
  -- `ε_w = 1` for primary primitive `w`
  have hε1 : jacobiSym w1.re (Work.FIPlan.gnorm w1) = 1 := by
    have h := jacobiSym_sq_add_sq (u := w1.re) (v := w1.im) h1.1 h1.2.1 hp1
    rw [natAbs_sq_add_sq, ← gnorm_eq_reSq_add_imSq w1] at h
    exact h
  have hε2 : jacobiSym w2.re (Work.FIPlan.gnorm w2) = 1 := by
    have h := jacobiSym_sq_add_sq (u := w2.re) (v := w2.im) h2.1 h2.2.1 hp2
    rw [natAbs_sq_add_sq, ← gnorm_eq_reSq_add_imSq w2] at h
    exact h
  have hd1 : Work.FIPlan.gnorm w1 ∣ N1 * N2 := by rw [hN1]; exact dvd_mul_right N1 N2
  have hd2 : Work.FIPlan.gnorm w2 ∣ N1 * N2 := by rw [hN2]; exact dvd_mul_left N2 N1
  -- `q = N₁N₂` is odd and `> 1`
  have hodd1 : Odd N1 := by
    rw [← hN1, gnorm_eq_reSq_add_imSq]
    exact (h1.1.natAbs.pow).add_even (Nat.even_pow.mpr ⟨h1.2.1.natAbs, by norm_num⟩)
  have hodd2 : Odd N2 := by
    rw [← hN2, gnorm_eq_reSq_add_imSq]
    exact (h2.1.natAbs.pow).add_even (Nat.even_pow.mpr ⟨h2.2.1.natAbs, by norm_num⟩)
  have hqodd : Odd (N1 * N2) := hodd1.mul hodd2
  have hq1 : 1 < N1 * N2 := by
    rcases Nat.lt_or_ge 1 (N1 * N2) with h | h
    · exact h
    · exfalso
      have h1' : N1 * N2 = 1 := by
        have := Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne N1))
          (Nat.pos_of_ne_zero (NeZero.ne N2))
        omega
      exact hsq ⟨1, by rw [h1']; norm_num⟩
  have hsq' : ∀ k : ℕ, N1 * N2 ≠ k ^ 2 := fun k hk => hsq ⟨k, hk⟩
  -- a unit `n` with `(n | N₁N₂) = -1`
  obtain ⟨n, hcop, hjs⟩ := jacobiSym_exists_neg_one (N1 * N2) hqodd hq1 hsq'
  obtain ⟨a, b, hab⟩ := hcop
  have hn1 : (b : ZMod (N1 * N2)) * (n : ZMod (N1 * N2)) = 1 := by
    have hq0' : (((N1 * N2 : ℕ) : ℤ) : ZMod (N1 * N2)) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd ((N1 * N2 : ℕ) : ℤ) (N1 * N2)).mpr (dvd_refl _)
    have h : ((a * ((N1 * N2 : ℕ) : ℤ) + b * n : ℤ) : ZMod (N1 * N2)) = 1 := by
      rw [hab]; simp
    rw [Int.cast_add, Int.cast_mul, Int.cast_mul, hq0', mul_zero, zero_add] at h
    exact h
  have hn2 : (n : ZMod (N1 * N2)) * (b : ZMod (N1 * N2)) = 1 :=
    (mul_comm (n : ZMod (N1 * N2)) (b : ZMod (N1 * N2))).trans hn1
  -- multiplication by the unit `(n,0)` is a bijection of `(ZMod q)²` under `gaussMul`
  let ein : (ZMod (N1 * N2) × ZMod (N1 * N2)) ≃ (ZMod (N1 * N2) × ZMod (N1 * N2)) :=
    { toFun := fun p => ((n : ZMod (N1 * N2)) * p.1, (n : ZMod (N1 * N2)) * p.2)
      invFun := fun p => ((b : ZMod (N1 * N2)) * p.1, (b : ZMod (N1 * N2)) * p.2)
      left_inv := by
        intro p
        apply Prod.ext
        · show (b : ZMod (N1 * N2)) * ((n : ZMod (N1 * N2)) * p.1) = p.1
          rw [← mul_assoc, hn1, one_mul]
        · show (b : ZMod (N1 * N2)) * ((n : ZMod (N1 * N2)) * p.2) = p.2
          rw [← mul_assoc, hn1, one_mul]
      right_inv := by
        intro p
        apply Prod.ext
        · show (n : ZMod (N1 * N2)) * ((b : ZMod (N1 * N2)) * p.1) = p.1
          rw [← mul_assoc, hn2, one_mul]
        · show (n : ZMod (N1 * N2)) * ((b : ZMod (N1 * N2)) * p.2) = p.2
          rw [← mul_assoc, hn2, one_mul] }
  have he_gm : ∀ p : ZMod (N1 * N2) × ZMod (N1 * N2),
      ein p = gaussMul ((n : ZMod (N1 * N2)), (0 : ZMod (N1 * N2))) p := by
    intro p
    show ((n : ZMod (N1 * N2)) * p.1, (n : ZMod (N1 * N2)) * p.2)
        = gaussMul ((n : ZMod (N1 * N2)), (0 : ZMod (N1 * N2))) p
    simp [gaussMul]
  -- `G` is multiplicative
  have hGmul : ∀ p p' : ZMod (N1 * N2) × ZMod (N1 * N2),
      xiCPair (N1 * N2) w1 w2 (gaussMul p p')
        = xiCPair (N1 * N2) w1 w2 p * xiCPair (N1 * N2) w1 w2 p' := by
    intro p p'
    have e1 := xiC_mul_of_eps_one (N1 * N2) hd1 hε1 p p'
    have e2 := xiC_mul_of_eps_one (N1 * N2) hd2 hε2 p p'
    simp only [xiCPair]
    rw [← e1, ← e2]
    ring
  have key : ∑ p : ZMod (N1 * N2) × ZMod (N1 * N2), xiCPair (N1 * N2) w1 w2 p
      = xiCPair (N1 * N2) w1 w2 ((n : ZMod (N1 * N2)), (0 : ZMod (N1 * N2)))
          * ∑ p : ZMod (N1 * N2) × ZMod (N1 * N2), xiCPair (N1 * N2) w1 w2 p := by
    conv_lhs => rw [(Equiv.sum_comp ein (xiCPair (N1 * N2) w1 w2)).symm]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [he_gm p]
    exact hGmul ((n : ZMod (N1 * N2)), (0 : ZMod (N1 * N2))) p
  -- `G (n, 0) = (n | N₁N₂) = -1`
  have hGn : xiCPair (N1 * N2) w1 w2 ((n : ZMod (N1 * N2)), (0 : ZMod (N1 * N2))) = -1 := by
    have e1 := xiC_inl_eq N1 (N1 * N2) w1 (dvd_mul_right N1 N2) hN1 hε1 n
    have e2 := xiC_inl_eq N2 (N1 * N2) w2 (dvd_mul_left N2 N1) hN2 hε2 n
    calc xiCPair (N1 * N2) w1 w2 ((n : ZMod (N1 * N2)), (0 : ZMod (N1 * N2)))
        = (jacobiSym n N1 : ℂ) * (jacobiSym n N2 : ℂ) := by
          simp only [xiCPair]; rw [e1, e2]
      _ = ((jacobiSym n N1 * jacobiSym n N2 : ℤ) : ℂ) := by push_cast; ring
      _ = ((jacobiSym n (N1 * N2) : ℤ) : ℂ) := by rw [jacobiSym.mul_right n N1 N2]
      _ = -1 := by rw [hjs]; norm_num
  have hS : ∑ p : ZMod (N1 * N2) × ZMod (N1 * N2), xiCPair (N1 * N2) w1 w2 p
      = -1 * ∑ p : ZMod (N1 * N2) × ZMod (N1 * N2), xiCPair (N1 * N2) w1 w2 p := by
    have h := key
    rw [hGn] at h
    exact h
  have hmain : (2 : ℂ) * (∑ p : ZMod (N1 * N2) × ZMod (N1 * N2),
      xiCPair (N1 * N2) w1 w2 p) = 0 := by
    have e : (∑ p : ZMod (N1 * N2) × ZMod (N1 * N2), xiCPair (N1 * N2) w1 w2 p)
        = -(∑ p : ZMod (N1 * N2) × ZMod (N1 * N2), xiCPair (N1 * N2) w1 w2 p) := by
      calc (∑ p : ZMod (N1 * N2) × ZMod (N1 * N2), xiCPair (N1 * N2) w1 w2 p)
          = -1 * (∑ p : ZMod (N1 * N2) × ZMod (N1 * N2), xiCPair (N1 * N2) w1 w2 p) := hS
        _ = -(∑ p : ZMod (N1 * N2) × ZMod (N1 * N2), xiCPair (N1 * N2) w1 w2 p) := by ring
    linear_combination e
  exact (mul_eq_zero.mp hmain).resolve_left (by norm_num)

end

end Work.FIArea7
