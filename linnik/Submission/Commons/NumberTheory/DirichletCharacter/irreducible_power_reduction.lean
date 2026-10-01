import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Star
import Mathlib.FieldTheory.KummerExtension
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Algebraic reduction of the Weil-bound hypothesis

This file proves `Commons.NumberTheory.DirichletCharacter.irreducible_power_reduction`.

Along the way it establishes the general form of Capelli's theorem over an arbitrary
field (`capelli_irreducible`), which Mathlib only has for characteristic zero / odd `n`.
-/


open Polynomial IntermediateField PowerBasis

namespace Commons.NumberTheory.DirichletCharacter

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

lemma repr_deg2 {a : K} {x : E} (hx : minpoly K x = X ^ 2 - C a) (y : K⟮x⟯) :
    ∃ u v : K, y = algebraMap K K⟮x⟯ u + algebraMap K K⟮x⟯ v * AdjoinSimple.gen K x := by
  have hint : IsIntegral K x :=
    minpoly.ne_zero_iff.mp (by rw [hx]; exact (monic_X_pow_sub_C a (by norm_num)).ne_zero)
  have hdim : (adjoin.powerBasis hint).dim = 2 := by
    rw [adjoin.powerBasis_dim, hx, natDegree_X_pow_sub_C]
  obtain ⟨f, hfdeg, hfy⟩ := PowerBasis.exists_eq_aeval (adjoin.powerBasis hint) y
  rw [hdim] at hfdeg
  rw [adjoin.powerBasis_gen hint] at hfy
  refine ⟨f.coeff 0, f.coeff 1, ?_⟩
  have hf : f = C (f.coeff 0) + C (f.coeff 1) * X := by
    ext n
    rcases n with _ | _ | n
    · simp
    · simp
    · have h : f.coeff (n + 2) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
      simp [h]
  rw [hfy, hf]
  simp [aeval_C, aeval_X]

lemma gen_notMem_range {a : K} {x : E} (hx : minpoly K x = X ^ 2 - C a) :
    AdjoinSimple.gen K x ∉ (algebraMap K K⟮x⟯).range := by
  have hint : IsIntegral K (AdjoinSimple.gen K x) :=
    minpoly.ne_zero_iff.mp (by rw [minpoly_gen, hx]; exact (monic_X_pow_sub_C a (by norm_num)).ne_zero)
  rw [← minpoly.two_le_natDegree_iff hint]
  rw [minpoly_gen, hx, natDegree_X_pow_sub_C]

lemma gen_pair {a : K} {x : E} (hx : minpoly K x = X ^ 2 - C a) {w z : K}
    (h : algebraMap K K⟮x⟯ w + algebraMap K K⟮x⟯ z * AdjoinSimple.gen K x = 0) :
    w = 0 ∧ z = 0 := by
  by_cases hz : z = 0
  · subst hz
    simp only [map_zero, zero_mul, add_zero] at h
    exact ⟨(algebraMap K K⟮x⟯).injective (by simpa using h), rfl⟩
  · exfalso
    have hz0 : algebraMap K K⟮x⟯ z ≠ 0 := by
      intro h0
      exact hz ((algebraMap K K⟮x⟯).injective (by rw [h0, map_zero]))
    have h2 : algebraMap K K⟮x⟯ z * AdjoinSimple.gen K x = algebraMap K K⟮x⟯ (-w) := by
      rw [map_neg]
      exact eq_neg_of_add_eq_zero_right h
    have h3 : AdjoinSimple.gen K x = algebraMap K K⟮x⟯ (-w) / algebraMap K K⟮x⟯ z := by
      rw [eq_div_iff hz0, mul_comm, h2]
    exact gen_notMem_range hx ⟨-w/z, by rw [h3, map_div₀]⟩

lemma gen_sq {a : K} {x : E} (hx : minpoly K x = X ^ 2 - C a) :
    (AdjoinSimple.gen K x) ^ 2 = algebraMap K K⟮x⟯ a := by
  have h := minpoly.aeval K (AdjoinSimple.gen K x)
  rw [minpoly_gen, hx] at h
  simpa [sub_eq_zero] using h

lemma expansion {a : K} {x : E} (hx : minpoly K x = X ^ 2 - C a) (u v : K) :
    (algebraMap K K⟮x⟯ u + algebraMap K K⟮x⟯ v * AdjoinSimple.gen K x) ^ 2 =
      algebraMap K K⟮x⟯ (u^2 + v^2*a) + algebraMap K K⟮x⟯ (2*u*v) * AdjoinSimple.gen K x := by
  have hα2 := gen_sq hx
  simp only [add_sq, mul_pow, hα2, map_add, map_mul, map_pow, map_ofNat]
  ring

lemma two_cast_zero {x : E} (h2 : (2:K) = 0) : (2 : K⟮x⟯) = 0 := by
  rw [← map_ofNat (algebraMap K K⟮x⟯) 2, h2, map_zero]

set_option linter.unusedSimpArgs false in
lemma sq_root_mem_neg4 {a : K} {x : E} (hx : minpoly K x = X ^ 2 - C a) (h2 : (2:K) ≠ 0)
    {y : K⟮x⟯} (hy : y ^ 2 = AdjoinSimple.gen K x) : ∃ w : K, a = -4 * w ^ 4 := by
  obtain ⟨u, v, huv⟩ := repr_deg2 hx y
  have hy2 : y^2 = algebraMap K K⟮x⟯ (u^2+v^2*a) + algebraMap K K⟮x⟯ (2*u*v) * AdjoinSimple.gen K x := by
    rw [huv]; exact expansion hx u v
  have hpair : algebraMap K K⟮x⟯ (u^2+v^2*a) + algebraMap K K⟮x⟯ (2*u*v - 1) * AdjoinSimple.gen K x = 0 := by
    have hconv : algebraMap K K⟮x⟯ (u^2+v^2*a) + algebraMap K K⟮x⟯ (2*u*v - 1) * AdjoinSimple.gen K x
        = (algebraMap K K⟮x⟯ (u^2+v^2*a) + algebraMap K K⟮x⟯ (2*u*v) * AdjoinSimple.gen K x) - AdjoinSimple.gen K x := by
      rw [map_sub, map_one]; ring
    rw [hconv, ← hy2, hy]; ring
  obtain ⟨hw, hz⟩ := gen_pair hx hpair
  have hzu : 2*u*v = 1 := sub_eq_zero.mp hz
  have h4 : 4*u^2*v^2 = 1 := by linear_combination (2*u*v + 1) * hzu
  refine ⟨u, ?_⟩
  linear_combination 4*u^2 * hw - a * h4

lemma char2_sq_ne_gen {a : K} {x : E} (hx : minpoly K x = X ^ 2 - C a) (h2 : (2:K) = 0)
    {y : K⟮x⟯} : y ^ 2 ≠ AdjoinSimple.gen K x := by
  obtain ⟨u, v, huv⟩ := repr_deg2 hx y
  intro hy
  have h2L := two_cast_zero (x := x) h2
  have hy2 : y^2 = algebraMap K K⟮x⟯ (u^2+v^2*a) := by
    rw [huv]
    have hα2 := gen_sq hx
    simp only [add_sq, mul_pow, hα2, map_add, map_mul, map_pow, map_ofNat, h2L, mul_zero, add_zero]
    ring
  exact gen_notMem_range hx ⟨u^2+v^2*a, by rw [← hy2, hy]⟩

end Commons.NumberTheory.DirichletCharacter

namespace Commons.NumberTheory.DirichletCharacter

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

lemma eight_ne_zero (h2 : (2:K) ≠ 0) : (8:K) ≠ 0 := by
  have h4 : (4:K) = 2*2 := by norm_num
  have h4nz : (4:K) ≠ 0 := by rw [h4]; exact mul_ne_zero h2 h2
  have h8 : (8:K) = 4*2 := by norm_num
  rw [h8]; exact mul_ne_zero h4nz h2

lemma sixtyfour_ne_zero (h2 : (2:K) ≠ 0) : (64:K) ≠ 0 := by
  have h8 := eight_ne_zero h2
  have h64 : (64:K) = 8*8 := by norm_num
  rw [h64]; exact mul_ne_zero h8 h8

lemma neg4_root_mem_neg4 {a : K} {x : E} (hx : minpoly K x = X ^ 2 - C a) (h2 : (2:K) ≠ 0)
    {y : K⟮x⟯} (hy : -4 * y ^ 4 = AdjoinSimple.gen K x) : ∃ w : K, a = -4 * w ^ 4 := by
  obtain ⟨u, v, huv⟩ := repr_deg2 hx y
  set s : K := u^2 + v^2*a with hs
  set t : K := 2*u*v with ht
  have hy2 : y^2 = algebraMap K K⟮x⟯ s + algebraMap K K⟮x⟯ t * AdjoinSimple.gen K x := by
    rw [huv, hs, ht]; exact expansion hx u v
  have hy4 : y^4 = algebraMap K K⟮x⟯ (s^2+t^2*a) + algebraMap K K⟮x⟯ (2*s*t) * AdjoinSimple.gen K x := by
    rw [show y^4 = (y^2)^2 by ring, hy2]; exact expansion hx s t
  have hpair : algebraMap K K⟮x⟯ (-4*(s^2+t^2*a)) + algebraMap K K⟮x⟯ (-8*s*t - 1) * AdjoinSimple.gen K x = 0 := by
    have h1 : algebraMap K K⟮x⟯ (-4*(s^2+t^2*a)) = -4 * algebraMap K K⟮x⟯ (s^2+t^2*a) := by
      rw [show (-4:K)*(s^2+t^2*a) = -4*(s^2+t^2*a) by ring]
      simp only [map_mul, map_neg, map_ofNat]
    have h2 : algebraMap K K⟮x⟯ (-8*s*t - 1) = -4 * algebraMap K K⟮x⟯ (2*s*t) - 1 := by
      rw [show (-8:K)*s*t - 1 = -4*(2*s*t) - 1 by ring]
      simp only [map_sub, map_mul, map_neg, map_ofNat, map_one]
    have hconv : algebraMap K K⟮x⟯ (-4*(s^2+t^2*a)) + algebraMap K K⟮x⟯ (-8*s*t - 1) * AdjoinSimple.gen K x
        = -4 * (algebraMap K K⟮x⟯ (s^2+t^2*a) + algebraMap K K⟮x⟯ (2*s*t) * AdjoinSimple.gen K x) - AdjoinSimple.gen K x := by
      rw [h1, h2]; ring
    rw [hconv, ← hy4, hy]; ring
  obtain ⟨hw, hz⟩ := gen_pair hx hpair
  have hs2 : s^2 + t^2*a = 0 := by
    have h4 : (4:K) = 2*2 := by norm_num
    have h4nz : (-4:K) ≠ 0 := by
      rw [show (-4:K) = -(4:K) by norm_num, neg_ne_zero]; rw [h4]; exact mul_ne_zero h2 h2
    exact (mul_eq_zero.mp hw).resolve_left h4nz
  have h64 : 64*s^2*t^2 = 1 := by linear_combination (-8*s*t + 1) * hz
  have hmain : a * (64*t^4) = -1 := by linear_combination 64*t^2 * hs2 - h64
  have ht0 : t ≠ 0 := by
    intro ht'
    rw [ht'] at h64
    norm_num at h64
  refine ⟨1/(4*t), ?_⟩
  have h64nz : (64:K) ≠ 0 := sixtyfour_ne_zero h2
  have hgoal : -4 * (1/(4*t))^4 = (-1 : K)/(64*t^4) := by
    field_simp
    rw [show (4:K)^3 = 64 by norm_num, div_self h64nz]
  rw [hgoal]
  exact (eq_div_iff (mul_ne_zero h64nz (pow_ne_zero 4 ht0))).mpr hmain

end Commons.NumberTheory.DirichletCharacter

namespace Commons.NumberTheory.DirichletCharacter

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

lemma norm_gen {a : K} {x : E} (hx : minpoly K x = X ^ 2 - C a) :
    Algebra.norm K (AdjoinSimple.gen K x) = -a := by
  have hint : IsIntegral K x :=
    minpoly.ne_zero_iff.mp (by rw [hx]; exact (monic_X_pow_sub_C a (by norm_num)).ne_zero)
  rw [← adjoin.powerBasis_gen hint, Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly]
  rw [adjoin.powerBasis_gen hint, minpoly_gen, hx]
  have hdim : (adjoin.powerBasis hint).dim = 2 := by
    rw [adjoin.powerBasis_dim, hx, natDegree_X_pow_sub_C]
  rw [hdim]
  simp [coeff_X_pow]

end Commons.NumberTheory.DirichletCharacter

namespace Commons.NumberTheory.DirichletCharacter

open Polynomial IntermediateField

private theorem capelli_aux :
    ∀ (n : ℕ) (K : Type*) [Field K] (a : K), 1 ≤ n →
      (∀ q : ℕ, q.Prime → q ∣ n → ∀ b : K, b ^ q ≠ a) →
      (4 ∣ n → ∀ b : K, -4 * b ^ 4 ≠ a) →
      Irreducible (Polynomial.X ^ n - Polynomial.C a) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro K instK a hn h1 h2
    by_cases h2n : 2 ∣ n
    · set n' := n / 2 with hn'def
      have hn'_eq : n' * 2 = n := by rw [hn'def]; exact Nat.div_mul_cancel h2n
      have hn'dvd : n' ∣ n := ⟨2, hn'_eq.symm⟩
      have hn'_pos : 1 ≤ n' := by
        rw [hn'def]
        exact Nat.div_pos (Nat.le_of_dvd (by omega) h2n) (by norm_num)
      have hIrr : Irreducible (Polynomial.X ^ (n' * 2) - Polynomial.C a) := by
        apply X_pow_mul_sub_C_irreducible (m := 2) (n := n')
        · exact X_pow_sub_C_irreducible_of_prime Nat.prime_two (h1 2 Nat.prime_two h2n)
        · intro E instE instAlg x hx
          refine IH n' ?_ (K⟮x⟯) (AdjoinSimple.gen K x) hn'_pos ?_ ?_
          · omega
          · intro r hr hrn' b hb
            rcases eq_or_ne r 2 with rfl | hr2
            · by_cases hchar : (2 : K) = 0
              · exact absurd hb (char2_sq_ne_gen hx hchar)
              · obtain ⟨w, hw⟩ := sq_root_mem_neg4 hx hchar hb
                have h4n : 4 ∣ n := by
                  obtain ⟨k, hk⟩ := hrn'
                  exact ⟨k, by rw [← hn'_eq, hk]; ring⟩
                exact h2 h4n w hw.symm
            · have hrodd : Odd r := hr.odd_of_ne_two hr2
              have hb' : (Algebra.norm K b) ^ r = Algebra.norm K (AdjoinSimple.gen K x) := by
                rw [← map_pow, hb]
              have hc : (-(Algebra.norm K b)) ^ r = a := by
                rw [Odd.neg_pow hrodd, hb', norm_gen hx]; ring
              exact h1 r hr (dvd_trans hrn' hn'dvd) _ hc
          · intro h4n' b hb
            by_cases hchar : (2 : K) = 0
            · exfalso
              have ha0 : a ≠ 0 := by
                have h := h1 2 Nat.prime_two h2n 0
                simp only [zero_pow (by norm_num : (2:ℕ) ≠ 0)] at h
                exact Ne.symm h
              have h4L : (-4 : K⟮x⟯) = 0 := by
                have h4K : (4:K) = 0 := by
                  rw [show (4:K) = 2*2 by norm_num, hchar, zero_mul]
                rw [show (-4:K⟮x⟯) = -(4:K⟮x⟯) by norm_num,
                  ← map_ofNat (algebraMap K K⟮x⟯) 4, h4K, map_zero, neg_zero]
              rw [h4L, zero_mul] at hb
              have hg0 : AdjoinSimple.gen K x = 0 := hb.symm
              have hgsq := gen_sq hx
              rw [hg0] at hgsq
              simp only [zero_pow (by norm_num : (2:ℕ) ≠ 0)] at hgsq
              exact ha0 ((algebraMap K K⟮x⟯).injective (by rw [← hgsq, map_zero]))
            · obtain ⟨w, hw⟩ := neg4_root_mem_neg4 hx hchar hb
              have h4n : 4 ∣ n := by
                obtain ⟨k, hk⟩ := h4n'
                exact ⟨2*k, by rw [← hn'_eq, hk]; ring⟩
              exact h2 h4n w hw.symm
      rwa [hn'_eq] at hIrr
    · have hodd : Odd n := by
        rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
        exact h2n
      exact X_pow_sub_C_irreducible_of_odd hodd h1

end Commons.NumberTheory.DirichletCharacter

namespace Commons.NumberTheory.DirichletCharacter

open Polynomial




end Commons.NumberTheory.DirichletCharacter

namespace Commons.NumberTheory.DirichletCharacter

theorem capelli_irreducible {K : Type*} [Field K] {n : ℕ} (hn : 1 ≤ n) {a : K}
    (h1 : ∀ q : ℕ, q.Prime → q ∣ n → ∀ b : K, b ^ q ≠ a)
    (h2 : 4 ∣ n → ∀ b : K, -4 * b ^ 4 ≠ a) :
    Irreducible (Polynomial.X ^ n - Polynomial.C a) :=
  capelli_aux n K a hn h1 h2

/-- Algebraic reduction of the Weil-bound hypothesis: if `F` is not a constant times
an `m`-th power, then `m` has a divisor `g` with `F = c * G ^ g`, `G` monic, the
`gcd(m/g, multiplicities of G)` equals `1` (equivalently `G` is not a constant times a
`d`-th power for any `d > 1` dividing `m/g`), `X ^ (m/g) - G` is irreducible over
`(ZMod p)[X]`, and `G` has the same distinct roots as `F`. -/
theorem irreducible_power_reduction (p : ℕ) [Fact p.Prime] (m : ℕ) (hm : 2 ≤ m)
    (F : Polynomial (ZMod p)) (hF : F ≠ 0) (hd : 1 ≤ F.natDegree)
    (hnd : ∀ (c : ZMod p) (H : Polynomial (ZMod p)), F ≠ Polynomial.C c * H ^ m) :
    ∃ (e : ℕ) (G : Polynomial (ZMod p)) (c : ZMod p), 2 ≤ e ∧ e ∣ m ∧ c ≠ 0 ∧ G.Monic ∧
      F = Polynomial.C c * G ^ (m / e) ∧
      (∀ (d : ℕ), d ∣ e → 1 < d →
        ∀ (c' : ZMod p) (H : Polynomial (ZMod p)), G ≠ Polynomial.C c' * H ^ d) ∧
      Irreducible (Polynomial.X ^ e - Polynomial.C G) ∧
      (F.rootSet (AlgebraicClosure (ZMod p))).ncard =
        (G.rootSet (AlgebraicClosure (ZMod p))).ncard := by
  classical
  let S : Finset ℕ := m.divisors.filter (fun k => ∃ c H, F = Polynomial.C c * H ^ k)
  have hSne : S.Nonempty := by
    refine ⟨1, ?_⟩
    exact Finset.mem_filter.mpr
      ⟨Nat.one_mem_divisors.mpr (by omega), 1, F, by rw [pow_one, map_one, one_mul]⟩
  set k := S.max' hSne with hkdef
  have hkS : k ∈ S := hkdef ▸ Finset.max'_mem S hSne
  have hkmax : ∀ k' ∈ S, k' ≤ k := fun k' hk' => hkdef ▸ Finset.le_max' S k' hk'
  obtain ⟨hkdiv, c₀, H, hFH⟩ := Finset.mem_filter.mp hkS
  obtain ⟨hkdiv, hm0⟩ := Nat.mem_divisors.mp hkdiv
  have hkpos : 0 < k := Nat.pos_of_dvd_of_pos hkdiv (by omega)
  have hkne : k ≠ 0 := hkpos.ne'
  have hc₀ : c₀ ≠ 0 := fun h => hF (by rw [hFH, h, map_zero, zero_mul])
  have hH : H ≠ 0 := fun hH0 => hF (by rw [hFH, hH0, zero_pow hkne, mul_zero])
  set aH := H.leadingCoeff with haHdef
  have haH0 : aH ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hH
  set G : Polynomial (ZMod p) := Polynomial.C aH⁻¹ * H with hGdef
  have hGmonic : G.Monic := by
    change G.leadingCoeff = 1
    rw [hGdef, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, inv_mul_cancel₀ haH0]
  have hHG : H = Polynomial.C aH * G := by
    rw [hGdef, ← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ haH0, Polynomial.C_1, one_mul]
  have hFG : F = Polynomial.C (c₀ * aH ^ k) * G ^ k := by
    rw [hFH, hHG, mul_pow, ← Polynomial.C_pow, ← mul_assoc, ← Polynomial.C_mul]
  set e := m / k with hedef
  have hme : k * e = m := by rw [hedef]; exact Nat.mul_div_cancel' hkdiv
  have hepos : 0 < e := Nat.div_pos (Nat.le_of_dvd (by omega) hkdiv) hkpos
  have hedvd : e ∣ m := ⟨k, by rw [← hme, mul_comm]⟩
  have hkm : k ≠ m := fun hkm => hnd c₀ H (by rw [hFH, hkm])
  have hcos : m / e = k := by
    rw [← hme, mul_comm k e, Nat.mul_div_cancel_left k hepos]
  have he2 : 2 ≤ e := by
    have hklt : k < m := lt_of_le_of_ne (Nat.le_of_dvd (by omega) hkdiv) hkm
    have h1 : 1 < e := Nat.lt_of_mul_lt_mul_left (by rw [hme, mul_one]; exact hklt)
    omega
  have hGne : G ≠ 0 := hGmonic.ne_zero
  have hpow : ∀ (d : ℕ), d ∣ e → 1 < d →
      ∀ (c' : ZMod p) (H : Polynomial (ZMod p)), G ≠ Polynomial.C c' * H ^ d := by
    intro d hde hd1 c' H' hGH'
    have hdk : d * k ∣ m := by
      obtain ⟨j, hj⟩ := hde
      refine ⟨j, ?_⟩
      rw [← hme, hj]; ring
    have hdkS : d * k ∈ S := by
      refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdk, by omega⟩, c₀ * aH ^ k * c' ^ k, H', ?_⟩
      rw [hFG, hGH', mul_pow, ← Polynomial.C_pow, ← pow_mul, ← mul_assoc, ← Polynomial.C_mul]
    have hle := hkmax (d * k) hdkS
    nlinarith [hd1, hkpos]
  refine ⟨e, G, c₀ * aH ^ k, he2, hedvd, mul_ne_zero hc₀ (pow_ne_zero k haH0), hGmonic, ?_, hpow, ?_, ?_⟩
  · rw [hFG, hcos]
  · -- irreducibility
    have hinj : Function.Injective
        (algebraMap (Polynomial (ZMod p)) (FractionRing (Polynomial (ZMod p)))) :=
      IsFractionRing.injective _ _
    have hmon : (Polynomial.X ^ e - Polynomial.C G).Monic :=
      Polynomial.monic_X_pow_sub_C G (by omega)
    refine (hmon.irreducible_iff_irreducible_map_fraction_map
      (K := FractionRing (Polynomial (ZMod p)))).mpr ?_
    have hmap : (Polynomial.X ^ e - Polynomial.C G).map
          (algebraMap (Polynomial (ZMod p)) (FractionRing (Polynomial (ZMod p))))
        = Polynomial.X ^ e - Polynomial.C
            (algebraMap (Polynomial (ZMod p)) (FractionRing (Polynomial (ZMod p))) G) := by
      simp
    rw [hmap]
    refine capelli_irreducible (by omega) ?_ ?_
    · intro q hq hqe b hb
      have hint : IsIntegral (Polynomial (ZMod p)) b := by
        refine ⟨Polynomial.X ^ q - Polynomial.C G, Polynomial.monic_X_pow_sub_C G hq.ne_zero, ?_⟩
        rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, sub_eq_zero]
        exact hb
      obtain ⟨b₀, hb₀⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
      have hb0 : b₀ ^ q = G := by
        refine hinj ?_
        rw [map_pow, hb₀, hb]
      exact (hpow q hqe hq.one_lt 1 b₀) (by rw [map_one, one_mul, hb0])
    · intro h4e b hb
      by_cases h4z : (-4 : ZMod p) = 0
      · exfalso
        have h4zL : (-4 : FractionRing (Polynomial (ZMod p))) = 0 := by
          rw [show (-4 : FractionRing (Polynomial (ZMod p)))
              = algebraMap (ZMod p) (FractionRing (Polynomial (ZMod p))) (-4) by
                rw [map_neg, map_ofNat]]
          rw [h4z, map_zero]
        rw [h4zL, zero_mul] at hb
        exact hGne (hinj (by rw [← hb, map_zero]))
      · have h4aL : algebraMap (Polynomial (ZMod p)) (FractionRing (Polynomial (ZMod p)))
            (Polynomial.C (-4 : ZMod p)) = (-4 : FractionRing (Polynomial (ZMod p))) := by
          simp only [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply, map_neg, map_ofNat]
        have h4neL : (-4 : FractionRing (Polynomial (ZMod p))) ≠ 0 := by
          rw [← h4aL]
          intro h
          have hC : (Polynomial.C (-4 : ZMod p) : Polynomial (ZMod p)) = Polynomial.C 0 :=
            hinj (by simpa using h)
          exact h4z (Polynomial.C_injective hC)
        have hinv : algebraMap (Polynomial (ZMod p)) (FractionRing (Polynomial (ZMod p)))
            (Polynomial.C ((-4 : ZMod p)⁻¹)) = ((-4 : FractionRing (Polynomial (ZMod p))))⁻¹ := by
          apply eq_inv_of_mul_eq_one_left
          rw [← h4aL, ← map_mul, ← Polynomial.C_mul, inv_mul_cancel₀ h4z, Polynomial.C_1, map_one]
        have hb4 : b ^ 4 = algebraMap (Polynomial (ZMod p)) (FractionRing (Polynomial (ZMod p)))
            (Polynomial.C ((-4 : ZMod p)⁻¹) * G) := by
          rw [map_mul, hinv, eq_inv_mul_iff_mul_eq₀ h4neL]
          exact hb
        obtain ⟨b₀, hb₀⟩ : ∃ b₀ : Polynomial (ZMod p),
            algebraMap (Polynomial (ZMod p)) (FractionRing (Polynomial (ZMod p))) b₀ = b :=
          IsIntegrallyClosed.isIntegral_iff.mp (IsIntegral.of_pow (n := 4) (by norm_num) (by
            rw [hb4]; exact isIntegral_algebraMap))
        have hb0 : b₀ ^ 4 = Polynomial.C ((-4 : ZMod p)⁻¹) * G := by
          refine hinj ?_
          rw [map_pow, hb₀, hb4]
        have hG : G = Polynomial.C (-4 : ZMod p) * b₀ ^ 4 := by
          rw [hb0, ← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ h4z, Polynomial.C_1, one_mul]
        exact (hpow 4 h4e (by norm_num) (-4) b₀) hG
  · have hroots : F.rootSet (AlgebraicClosure (ZMod p)) = G.rootSet (AlgebraicClosure (ZMod p)) := by
      have hkey : ∀ x : AlgebraicClosure (ZMod p), (Polynomial.aeval x) F
          = algebraMap (ZMod p) (AlgebraicClosure (ZMod p)) (c₀ * aH ^ k)
            * ((Polynomial.aeval x) G) ^ k := by
        intro x
        rw [hFG]
        simp
      ext x
      rw [Polynomial.mem_rootSet, Polynomial.mem_rootSet]
      constructor
      · rintro ⟨-, hx⟩
        rw [hkey] at hx
        refine ⟨hGne, ?_⟩
        rcases mul_eq_zero.mp hx with h | h
        · exact absurd ((algebraMap (ZMod p) (AlgebraicClosure (ZMod p))).injective
            (by rw [h, map_zero]))
            (mul_ne_zero hc₀ (pow_ne_zero k haH0))
        · exact (pow_eq_zero_iff hkne).mp h
      · rintro ⟨-, hx⟩
        refine ⟨hF, ?_⟩
        rw [hkey, hx, zero_pow hkne, mul_zero]
    rw [hroots]


end Commons.NumberTheory.DirichletCharacter