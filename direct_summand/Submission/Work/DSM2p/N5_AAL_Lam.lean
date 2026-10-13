import Mathlib
import Submission.Work.DSM2p.LamOne
import Submission.Work.DSM2p.AAL_N
import Submission.Work.DSM2p.N5b_exists_approx
import Submission.Work.DSM2p.N5b_mem_of_map_mem
import Submission.Work.DSM2p.N5d_frobInj_scaled
import Submission.Work.DSM2p.N5c_exists_monic_root
import Submission.Work.DSM2p.N3_ker_aeval
import Submission.Work.DSM2p.N5e_descent
import Submission.Work.DSM2p.N1_monic_isSMulRegular_quot
import Submission.Work.DSM2p.N5f_isSMulRegular_quot_map
import Submission.Work.DSM2p.exists_sub_pow_eq_sub_pow_add_prime_mul
import Submission.Work.DSM2p.N5_helpers
import Submission.Work.DSM2p.N5_step
import Submission.Work.DSM2p.N5a_PERFD_Lam1_Q
import Submission.Work.DSM2p.N5_AAL_Lam_a
import Submission.Work.DSM2p.N5_AAL_Lam_b

/-!
# Node `N5` of the M2p design: the AAL data on `Λ = A[T^{1/p^∞}]`

This module proves `Work.DSM2p.N5_AAL_Lam`, the descent of the output of André's approximation
lemma (`AAL_N`) from the `p`-adic completion `Λ̂` of `Λ = Lam1 A p = A[T^{1/p^∞}]` back to `Λ`.

## The statement

For `F ∈ A[X]` monic and `m ≥ 1` there are `q : ℕ → Λ`, `t`, `N` with `N > 0` such that

* (a) `q (j+1) ^ p - q j ∈ (ϖ_0^{m+1})`;
* (b) `q j - g_j(T^{1/p^n}) ∈ (ϖ_{j+t})` for some monic `g_j` (in fact `n = j` and `g_j` is the
  monic root produced by `N5c`);
* (c) `δ ^ N ∈ ϖ_0 · Λ[F(T)/ϖ_0^m]`, where `δ = (F(T) - q_0)/ϖ_0^m`;
* (d) `δ ^ N ∈ ϖ_0 · Λ[q_0/ϖ_0^m]`.

## Proof

`AAL_N` is applied to the perfectoid ring `Λ̂ = AdicCompletion (p) Λ` (whose perfectoid structure
is `N5a_PERFD_Lam1_Q`) with `P := F(T)`, producing `Qr : ℕ → Λ̂` and `N > 0` with
`Qr (j+1)^p = Qr j`, `(F(T) - Qr 0)^N ∈ ϖ_0 Λ̂` and the two localized divisibility statements in
`Λ̂[1/ϖ_0]`.  The elements `q j ∈ Λ` are lifts of `Qr j` modulo `ϖ_0^K`, `K := mN + m + 1`
(`N5b`); this gives (a) (`N5_AAL_Lam_a`), and produces the `(F(T) - q_0)` input of (b)
(`N5_AAL_Lam_b`).

The localized statements are transported to polynomial statements in `Λ̂[X]` with the help of `N3`
over `Λ̂` (identifying the kernel of `X ↦ a/π^e` with `(π^e X - a)`), using the regularity of
`F(T)` modulo `ϖ_0` (`N1` + `N5f`) and of `Qr 0` modulo `ϖ_t` (from (b), `N1` and `N5f`).
`N5e` descends the resulting ideal membership from `Λ̂[X]` to `Λ[X]`, and finally the elementary
computation `adjoin_mem_of_span_mem` converts `C(a^N) ∈ (C(ϖ_0^k)) ⊔ (w)` into the divisibility
statements (c) and (d).
-/

open scoped Classical

namespace Work.DSM2p

universe u

/-! ## The main theorem -/

theorem N5_AAL_Lam (A : Type*) [CommRing A] (p : ℕ) [Fact p.Prime]
    (P : DSMap.PerfectoidData p A) (F : Polynomial A) (hF : F.Monic) (m : ℕ) (hm : 1 ≤ m) :
    ∃ (q : ℕ → Lam1 A p) (t N : ℕ), 0 < N ∧
      (∀ j, q (j + 1) ^ p - q j ∈
        Ideal.span {algebraMap A (Lam1 A p) (P.ϖ 0 ^ (m + 1))}) ∧
      (∀ j, ∃ n : ℕ, ∃ g : Polynomial A, g.Monic ∧
        q j - Polynomial.aeval (T1 A p n) g ∈
          Ideal.span {algebraMap A (Lam1 A p) (P.ϖ (j + t))}) ∧
      (∃ v ∈ Algebra.adjoin (Lam1 A p)
          {frac A p (P.ϖ 0) (Polynomial.aeval (T1 A p 0) F) m},
        frac A p (P.ϖ 0) (Polynomial.aeval (T1 A p 0) F - q 0) m ^ N =
          algebraMap A (Lam1Loc A p (P.ϖ 0)) (P.ϖ 0) * v) ∧
      (∃ v ∈ Algebra.adjoin (Lam1 A p) {frac A p (P.ϖ 0) (q 0) m},
        frac A p (P.ϖ 0) (Polynomial.aeval (T1 A p 0) F - q 0) m ^ N =
          algebraMap A (Lam1Loc A p (P.ϖ 0)) (P.ϖ 0) * v) := by
  classical
  -- the `p`-adic completion of `Λ` and its perfectoid structure
  let D := AdicCompletion (Ideal.span {(p : Lam1 A p)}) (Lam1 A p)
  obtain ⟨Q, hQ⟩ := N5a_PERFD_Lam1_Q A p P
  set PD : D := algebraMap (Lam1 A p) D (Polynomial.aeval (T1 A p 0) F) with hPD
  -- André's approximation lemma on `Λ̂`
  obtain ⟨Qr, N, hNpos, hQrroot, h1, h23⟩ := AAL_N p D Q PD m
  obtain ⟨h2, h3⟩ := h23
  -- the unit with `ϖ_0 ^ p = p · u`
  obtain ⟨v0, hv0⟩ := P.unit
  let vu : (Lam1 A p)ˣ := Units.map (algebraMap A (Lam1 A p)) v0
  have hπe : (algebraMap A (Lam1 A p) (P.ϖ 0)) ^ p = (p : Lam1 A p) * (vu : Lam1 A p) := by
    show algebraMap A (Lam1 A p) (P.ϖ 0) ^ p
      = (p : Lam1 A p) * algebraMap A (Lam1 A p) (v0 : A)
    rw [← map_pow, hv0, map_mul, map_natCast]
  have hφπ : algebraMap (Lam1 A p) D (algebraMap A (Lam1 A p) (P.ϖ 0)) = Q.ϖ 0 := by
    rw [← IsScalarTower.algebraMap_apply A (Lam1 A p) D (P.ϖ 0), hQ 0]
  have hπreg : IsSMulRegular (Lam1 A p) (algebraMap A (Lam1 A p) (P.ϖ 0)) :=
    Lam1_varpi_regular A p P 0
  have hϖDreg : IsSMulRegular D (Q.ϖ 0) := varpi_zero_isSMulRegular p Q
  -- exponents
  let K : ℕ := m * N + m + 1
  have hK1 : 1 ≤ K := by simp only [K]; omega
  have hm1K : m + 1 ≤ K := by simp only [K]; omega
  have hleK : m * N + 1 ≤ K := by simp only [K]; omega
  have hKadd : K = m * N + 1 + m := by simp only [K]; ring
  -- the lifts `q j` of `Qr j` modulo `ϖ_0 ^ K`
  have hlift : ∀ j, ∃ c : Lam1 A p, Qr j - algebraMap (Lam1 A p) D c ∈ Ideal.span {Q.ϖ 0 ^ K} := by
    intro j
    obtain ⟨c, hc⟩ := N5b_exists_approx (R := Lam1 A p) p (algebraMap A (Lam1 A p) (P.ϖ 0)) p vu
      hπe (Fact.out : p.Prime).one_le K (Qr j)
    refine ⟨c, ?_⟩
    rw [map_pow, hφπ] at hc
    exact hc
  choose q hq using hlift
  -- (a)
  have ha : ∀ j, q (j + 1) ^ p - q j ∈
      Ideal.span {algebraMap A (Lam1 A p) (P.ϖ 0 ^ (m + 1))} :=
    N5_AAL_Lam_a A p P m Q hQ Qr hQrroot q K hm1K hq
  -- `F(T) - q 0 ∈ (ϖ_N)`
  set a0 : Lam1 A p := Polynomial.aeval (T1 A p 0) F - q 0 with ha0
  have hFq : Polynomial.aeval (T1 A p 0) F - q 0 ∈
      Ideal.span {algebraMap A (Lam1 A p) (P.ϖ N)} := by
    have hstep1 : (algebraMap (Lam1 A p) D a0) ^ N ∈ Ideal.span {Q.ϖ 0} := by
      have hcorr : algebraMap (Lam1 A p) D a0 - (PD - Qr 0)
          = Qr 0 - algebraMap (Lam1 A p) D (q 0) := by
        rw [ha0, RingHom.map_sub, ← hPD]; ring
      have hcorrmem : algebraMap (Lam1 A p) D a0 - (PD - Qr 0) ∈ Ideal.span {Q.ϖ 0 ^ K} := by
        rw [hcorr]; exact hq 0
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hcorrmem
      have hdecomp : algebraMap (Lam1 A p) D a0 = (PD - Qr 0) + (Q.ϖ 0) ^ K * c := by
        linear_combination hc
      rw [hdecomp]
      obtain ⟨r, hr⟩ := sub_dvd_pow_sub_pow ((PD - Qr 0) + (Q.ϖ 0) ^ K * c) (PD - Qr 0) N
      have hsplit : ((PD - Qr 0) + (Q.ϖ 0) ^ K * c) ^ N
          = (PD - Qr 0) ^ N + ((Q.ϖ 0) ^ K * c) * r := by
        have hsub : ((PD - Qr 0) + (Q.ϖ 0) ^ K * c) - (PD - Qr 0) = (Q.ϖ 0) ^ K * c := by ring
        rw [hsub] at hr
        linear_combination hr
      rw [hsplit]
      refine Ideal.add_mem _ h1 ?_
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (mem_span_singleton_pow (Q.ϖ 0) hK1))
    have hstep2 : a0 ^ N ∈ Ideal.span {algebraMap A (Lam1 A p) (P.ϖ 0)} := by
      have hkey : algebraMap (Lam1 A p) D (a0 ^ N) ∈
          Ideal.span {algebraMap (Lam1 A p) D ((algebraMap A (Lam1 A p) (P.ϖ 0)) ^ 1)} := by
        rw [map_pow, pow_one, hφπ]
        exact hstep1
      have h := N5b_mem_of_map_mem (R := Lam1 A p) p (algebraMap A (Lam1 A p) (P.ϖ 0)) p vu hπe
        (Fact.out : p.Prime).one_le hπreg 1 (a0 ^ N) hkey
      rwa [pow_one] at h
    have hstep3 : a0 ^ (p ^ N) ∈ Ideal.span {algebraMap A (Lam1 A p) (P.ϖ 0)} := by
      have hle : N ≤ p ^ N := by
        have h1 : N < 2 ^ N := Nat.lt_two_pow_self
        have h2 : 2 ^ N ≤ p ^ N := Nat.pow_le_pow_left (Fact.out : p.Prime).two_le N
        omega
      have heq : a0 ^ (p ^ N) = a0 ^ N * a0 ^ (p ^ N - N) := by
        rw [← pow_add, Nat.add_sub_cancel' hle]
      rw [heq]
      exact Ideal.mul_mem_right _ _ hstep2
    have := varpi_iterate_mem A p P a0 0 N (by simpa using hstep3)
    simpa [ha0] using this
  -- (b)
  have hb : ∀ j, ∃ n : ℕ, ∃ g : Polynomial A, g.Monic ∧
      q j - Polynomial.aeval (T1 A p n) g ∈
        Ideal.span {algebraMap A (Lam1 A p) (P.ϖ (j + N))} :=
    N5_AAL_Lam_b A p P F hF m q N hNpos ha hFq
  -- `q 0` is close to a monic element modulo `ϖ_N`
  obtain ⟨n0, g0, hg0monic, hg0mem⟩ := hb 0
  -- the N5b hypotheses for the exponent `m * N + 1`
  have hinjN : ∀ c : Lam1 A p,
      algebraMap (Lam1 A p) D c ∈
        Ideal.span {(algebraMap (Lam1 A p) D (algebraMap A (Lam1 A p) (P.ϖ 0))) ^ (m * N + 1)} →
      c ∈ Ideal.span {(algebraMap A (Lam1 A p) (P.ϖ 0)) ^ (m * N + 1)} := by
    intro c hc
    refine N5b_mem_of_map_mem (R := Lam1 A p) p (algebraMap A (Lam1 A p) (P.ϖ 0)) p vu hπe
      (Fact.out : p.Prime).one_le hπreg (m * N + 1) c ?_
    rwa [map_pow]
  have hsurjN : ∀ d : D, ∃ c : Lam1 A p, d - algebraMap (Lam1 A p) D c ∈
      Ideal.span {(algebraMap (Lam1 A p) D (algebraMap A (Lam1 A p) (P.ϖ 0))) ^ (m * N + 1)} := by
    intro d
    obtain ⟨c, hc⟩ := N5b_exists_approx (R := Lam1 A p) p (algebraMap A (Lam1 A p) (P.ϖ 0)) p vu
      hπe (Fact.out : p.Prime).one_le (m * N + 1) d
    exact ⟨c, by rwa [map_pow] at hc⟩
  -- the localization `Λ̂[1/ϖ_0]` is injective over `Λ̂`
  have hinjD : Function.Injective (algebraMap D (Localization.Away (Q.ϖ 0))) := by
    intro a b hab
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (Q.ϖ 0) hab
    have hreg : ∀ n : ℕ, IsSMulRegular D ((Q.ϖ 0) ^ n) := by
      intro n
      induction n with
      | zero => rw [pow_zero]; exact IsUnit.isSMulRegular D isUnit_one
      | succ n ih => rw [pow_succ]; exact ih.mul hϖDreg
    exact hreg n hn
  -- regularity of `F(T)` modulo `ϖ_0` over `Λ̂`  (N5f + N1)
  have hinj1 : ∀ c : Lam1 A p,
      algebraMap (Lam1 A p) D c ∈ Ideal.span {algebraMap (Lam1 A p) D (algebraMap A (Lam1 A p) (P.ϖ 0))} →
      c ∈ Ideal.span {algebraMap A (Lam1 A p) (P.ϖ 0)} := by
    intro c hc
    have hkey : algebraMap (Lam1 A p) D c ∈
        Ideal.span {algebraMap (Lam1 A p) D ((algebraMap A (Lam1 A p) (P.ϖ 0)) ^ 1)} := by
      rwa [pow_one]
    have h := N5b_mem_of_map_mem (R := Lam1 A p) p (algebraMap A (Lam1 A p) (P.ϖ 0)) p vu hπe
      (Fact.out : p.Prime).one_le hπreg 1 c hkey
    rwa [pow_one] at h
  have hsurj1 : ∀ d : D, ∃ c : Lam1 A p, d - algebraMap (Lam1 A p) D c ∈
      Ideal.span {algebraMap (Lam1 A p) D (algebraMap A (Lam1 A p) (P.ϖ 0))} := by
    intro d
    obtain ⟨c, hc⟩ := N5b_exists_approx (R := Lam1 A p) p (algebraMap A (Lam1 A p) (P.ϖ 0)) p vu
      hπe (Fact.out : p.Prime).one_le 1 d
    exact ⟨c, by rwa [pow_one] at hc⟩
  have hmonic1 : IsSMulRegular (Lam1 A p ⧸ Ideal.span {algebraMap A (Lam1 A p) (P.ϖ 0)})
      (Ideal.Quotient.mk (Ideal.span {algebraMap A (Lam1 A p) (P.ϖ 0)})
        (Polynomial.aeval (T1 A p 0) F)) := by
    have h0 := N1_monic_isSMulRegular_quot A p (Ideal.span {P.ϖ 0}) 0 F hF
    have hmap : (Ideal.span {P.ϖ 0}).map (algebraMap A (Lam1 A p))
        = Ideal.span {algebraMap A (Lam1 A p) (P.ϖ 0)} := by
      rw [Ideal.map_span, Set.image_singleton]
    rwa [hmap] at h0
  have hPDreg : IsSMulRegular (D ⧸ Ideal.span {Q.ϖ 0})
      (Ideal.Quotient.mk (Ideal.span {Q.ϖ 0}) PD) := by
    have h5f := N5f_isSMulRegular_quot_map (C := Lam1 A p) (D := D)
      (algebraMap (Lam1 A p) D) (algebraMap A (Lam1 A p) (P.ϖ 0))
      (Polynomial.aeval (T1 A p 0) F) hinj1 hsurj1 hmonic1
    have h1' : Ideal.span {algebraMap (Lam1 A p) D (algebraMap A (Lam1 A p) (P.ϖ 0))}
        = Ideal.span {Q.ϖ 0} := by rw [hφπ]
    rw [h1', ← hPD] at h5f
    exact h5f
  -- the `N3` presentation of `Λ̂[F(T)/ϖ_0^m]`
  have hkerF : RingHom.ker (Polynomial.aeval (algebraMap D (Localization.Away (Q.ϖ 0)) PD
      * IsLocalization.Away.invSelf (Q.ϖ 0) ^ m)).toRingHom
      = Ideal.span {Polynomial.C ((Q.ϖ 0) ^ m) * Polynomial.X - Polynomial.C PD} := by
    have hx : algebraMap D (Localization.Away (Q.ϖ 0)) ((Q.ϖ 0) ^ m)
        * (algebraMap D (Localization.Away (Q.ϖ 0)) PD
          * IsLocalization.Away.invSelf (Q.ϖ 0) ^ m)
        = algebraMap D (Localization.Away (Q.ϖ 0)) PD := by
      calc algebraMap D (Localization.Away (Q.ϖ 0)) ((Q.ϖ 0) ^ m)
            * (algebraMap D (Localization.Away (Q.ϖ 0)) PD
              * IsLocalization.Away.invSelf (Q.ϖ 0) ^ m)
          = algebraMap D (Localization.Away (Q.ϖ 0)) PD
            * ((algebraMap D (Localization.Away (Q.ϖ 0)) (Q.ϖ 0)) ^ m
              * IsLocalization.Away.invSelf (Q.ϖ 0) ^ m) := by
            rw [map_pow]; ring
        _ = algebraMap D (Localization.Away (Q.ϖ 0)) PD := by
            rw [← mul_pow, IsLocalization.Away.mul_invSelf, one_pow, mul_one]
    exact N3_ker_aeval (C := D) (L := Localization.Away (Q.ϖ 0)) hinjD (Q.ϖ 0) PD m hm
      (IsLocalization.Away.algebraMap_isUnit (Q.ϖ 0)) hPDreg _ hx
  -- the polynomial membership over `Λ̂[X]` for (c)
  obtain ⟨vF, hvF, heqF⟩ := Submodule.mem_map.mp h2
  have heqF' : (algebraMap D (Localization.Away (Q.ϖ 0)) (PD - Qr 0)
      * IsLocalization.Away.invSelf (Q.ϖ 0) ^ m) ^ N
      = algebraMap D (Localization.Away (Q.ϖ 0)) (Q.ϖ 0) * vF := by
    rw [← heqF, LinearMap.mulLeft_apply]
  obtain ⟨hDF, hmemF⟩ := poly_mem_of_ker (Q.ϖ 0) m N (PD - Qr 0) _ _ hkerF hvF heqF'
  -- correct `PD - Qr 0` to `PD - φ(q 0)`
  have hδ : (PD - algebraMap (Lam1 A p) D (q 0)) - (PD - Qr 0) ∈ Ideal.span {Q.ϖ 0 ^ K} := by
    have h2' : (PD - algebraMap (Lam1 A p) D (q 0)) - (PD - Qr 0)
        = Qr 0 - algebraMap (Lam1 A p) D (q 0) := by ring
    rw [h2']; exact hq 0
  have hKpow : (Q.ϖ 0) ^ K ∈ Ideal.span {(Q.ϖ 0) ^ (m * N + 1)} := by
    rw [show (Q.ϖ 0) ^ K = (Q.ϖ 0) ^ (m * N + 1) * (Q.ϖ 0) ^ (K - (m * N + 1)) from by
      rw [← pow_add, Nat.add_sub_cancel' hleK]]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hδpow : (PD - algebraMap (Lam1 A p) D (q 0)) ^ N - (PD - Qr 0) ^ N
      ∈ Ideal.span {(Q.ϖ 0) ^ (m * N + 1)} :=
    (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hKpow))
      (pow_sub_pow_mem_of_sub_mem hδ N)
  have hCd : Polynomial.C ((PD - algebraMap (Lam1 A p) D (q 0)) ^ N)
      - Polynomial.C ((PD - Qr 0) ^ N) ∈ Ideal.span {Polynomial.C ((Q.ϖ 0) ^ (m * N + 1))} := by
    rw [← Polynomial.C_sub, span_C_singleton_eq_map, Ideal.mem_map_C_iff]
    intro n
    rw [Polynomial.coeff_C]
    by_cases hn : n = 0
    · rw [if_pos hn]; exact hδpow
    · rw [if_neg hn]; exact Ideal.zero_mem _
  have hmemFD : Polynomial.C ((PD - algebraMap (Lam1 A p) D (q 0)) ^ N) ∈
      Ideal.span {Polynomial.C ((Q.ϖ 0) ^ (m * N + 1))} ⊔
        Ideal.span {Polynomial.C ((Q.ϖ 0) ^ m) * Polynomial.X - Polynomial.C PD} := by
    have h1' : Polynomial.C ((PD - Qr 0) ^ N) ∈
        Ideal.span {Polynomial.C ((Q.ϖ 0) ^ (m * N + 1))} ⊔
          Ideal.span {Polynomial.C ((Q.ϖ 0) ^ m) * Polynomial.X - Polynomial.C PD} :=
      Submodule.mem_sup.mpr
        ⟨Polynomial.C ((Q.ϖ 0) ^ (m * N + 1)) * hDF,
          Ideal.mul_mem_right hDF
            (Ideal.span {Polynomial.C ((Q.ϖ 0) ^ (m * N + 1))})
            (Ideal.subset_span (Set.mem_singleton
              (Polynomial.C ((Q.ϖ 0) ^ (m * N + 1))))),
          Polynomial.C ((PD - Qr 0) ^ N)
            - Polynomial.C ((Q.ϖ 0) ^ (m * N + 1)) * hDF,
          hmemF, by ring⟩
    have h3' : Polynomial.C ((PD - algebraMap (Lam1 A p) D (q 0)) ^ N)
        = (Polynomial.C ((PD - algebraMap (Lam1 A p) D (q 0)) ^ N)
            - Polynomial.C ((PD - Qr 0) ^ N)) + Polynomial.C ((PD - Qr 0) ^ N) := by ring
    rw [h3']
    exact Ideal.add_mem _ (Ideal.mem_sup_left hCd) h1'
  -- regularity of `Qr 0` modulo `ϖ_N` over `Λ̂` (from (b) + N5f + N1)
  have hπe2 : (algebraMap A (Lam1 A p) (P.ϖ N)) ^ (p ^ (N + 1))
      = (p : Lam1 A p) * (vu : Lam1 A p) := by
    rw [Nat.pow_succ', mul_comm p (p ^ N), pow_mul, Lam1_varpi_pow A p P N, hπe]
  have hinj2 : ∀ c : Lam1 A p,
      algebraMap (Lam1 A p) D c ∈ Ideal.span {algebraMap (Lam1 A p) D (algebraMap A (Lam1 A p) (P.ϖ N))} →
      c ∈ Ideal.span {algebraMap A (Lam1 A p) (P.ϖ N)} := by
    intro c hc
    have hkey : algebraMap (Lam1 A p) D c ∈
        Ideal.span {algebraMap (Lam1 A p) D ((algebraMap A (Lam1 A p) (P.ϖ N)) ^ 1)} := by
      rwa [pow_one]
    have h := N5b_mem_of_map_mem (R := Lam1 A p) p (algebraMap A (Lam1 A p) (P.ϖ N)) (p ^ (N + 1))
      vu hπe2 (Nat.one_le_pow (N + 1) p (Fact.out : p.Prime).pos) (Lam1_varpi_regular A p P N)
      1 c hkey
    rwa [pow_one] at h
  have hsurj2 : ∀ d : D, ∃ c : Lam1 A p, d - algebraMap (Lam1 A p) D c ∈
      Ideal.span {algebraMap (Lam1 A p) D (algebraMap A (Lam1 A p) (P.ϖ N))} := by
    intro d
    obtain ⟨c, hc⟩ := N5b_exists_approx (R := Lam1 A p) p (algebraMap A (Lam1 A p) (P.ϖ N))
      (p ^ (N + 1)) vu hπe2 (Nat.one_le_pow (N + 1) p (Fact.out : p.Prime).pos) 1 d
    exact ⟨c, by rwa [pow_one] at hc⟩
  have hmonic2 : IsSMulRegular (Lam1 A p ⧸ Ideal.span {algebraMap A (Lam1 A p) (P.ϖ N)})
      (Ideal.Quotient.mk (Ideal.span {algebraMap A (Lam1 A p) (P.ϖ N)})
        (Polynomial.aeval (T1 A p n0) g0)) := by
    have h0 := N1_monic_isSMulRegular_quot A p (Ideal.span {P.ϖ N}) n0 g0 hg0monic
    have hmap : (Ideal.span {P.ϖ N}).map (algebraMap A (Lam1 A p))
        = Ideal.span {algebraMap A (Lam1 A p) (P.ϖ N)} := by
      rw [Ideal.map_span, Set.image_singleton]
    rwa [hmap] at h0
  have hQr0reg : IsSMulRegular (D ⧸ Ideal.span {Q.ϖ N})
      (Ideal.Quotient.mk (Ideal.span {Q.ϖ N}) (Qr 0)) := by
    have h5f := N5f_isSMulRegular_quot_map (C := Lam1 A p) (D := D) (algebraMap (Lam1 A p) D)
      (algebraMap A (Lam1 A p) (P.ϖ N)) (Polynomial.aeval (T1 A p n0) g0) hinj2 hsurj2 hmonic2
    have hN' : algebraMap (Lam1 A p) D (algebraMap A (Lam1 A p) (P.ϖ N)) = Q.ϖ N := by
      rw [← IsScalarTower.algebraMap_apply A (Lam1 A p) D (P.ϖ N), hQ N]
    rw [hN'] at h5f
    -- the images of `Qr 0` and of `φ (aeval (T1 n0) g0)` agree
    have himg : Ideal.Quotient.mk (Ideal.span {Q.ϖ N}) (Qr 0)
        = Ideal.Quotient.mk (Ideal.span {Q.ϖ N})
            (algebraMap (Lam1 A p) D (Polynomial.aeval (T1 A p n0) g0)) := by
      rw [Ideal.Quotient.eq]
      have hmemq : algebraMap (Lam1 A p) D (q 0 - Polynomial.aeval (T1 A p n0) g0)
          ∈ Ideal.span {Q.ϖ N} := by
        obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp (by simpa using hg0mem)
        rw [← hs, map_mul, hN', mul_comm]
        exact Ideal.mul_mem_right (algebraMap (Lam1 A p) D s) (Ideal.span {Q.ϖ N})
          (Ideal.mem_span_singleton_self (Q.ϖ N))
      have hsplit : Qr 0 - algebraMap (Lam1 A p) D (Polynomial.aeval (T1 A p n0) g0)
          = (Qr 0 - algebraMap (Lam1 A p) D (q 0))
            + algebraMap (Lam1 A p) D (q 0 - Polynomial.aeval (T1 A p n0) g0) := by
        rw [RingHom.map_sub]; ring
      rw [hsplit]
      refine Ideal.add_mem _ ?_ hmemq
      have hKmem2 : (Q.ϖ 0) ^ K ∈ Ideal.span {Q.ϖ N} := by
        have h0N : Q.ϖ 0 ∈ Ideal.span {Q.ϖ N} := by
          rw [← varpi_pow_root p Q N]
          exact (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr
            (Ideal.mem_span_singleton_self (Q.ϖ N))))
            (mem_span_singleton_pow (Q.ϖ N) (Nat.one_le_pow N p (Fact.out : p.Prime).pos))
        exact (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr h0N))
          (mem_span_singleton_pow (Q.ϖ 0) hK1)
      exact (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hKmem2)) (hq 0)
    rw [himg]
    exact h5f
  -- the `N3` presentation of `Λ̂[Qr 0/ϖ_0^m]`, with base `ϖ_N`
  have hkerQ : RingHom.ker (Polynomial.aeval (algebraMap D (Localization.Away (Q.ϖ 0)) (Qr 0)
      * IsLocalization.Away.invSelf (Q.ϖ 0) ^ m)).toRingHom
      = Ideal.span {Polynomial.C ((Q.ϖ 0) ^ m) * Polynomial.X - Polynomial.C (Qr 0)} := by
    have hunitQ : IsUnit (algebraMap D (Localization.Away (Q.ϖ 0)) (Q.ϖ N)) := by
      refine isUnit_of_isUnit_pow (n := p ^ N) (pow_pos (Fact.out : p.Prime).pos N) ?_
      rw [← map_pow, varpi_pow_root p Q N]
      exact IsLocalization.Away.algebraMap_isUnit (Q.ϖ 0)
    have hle1 : Submonoid.powers (Q.ϖ 0) ≤ Submonoid.powers (Q.ϖ N) := by
      intro x hx
      rw [Submonoid.mem_powers_iff] at hx ⊢
      obtain ⟨k, rfl⟩ := hx
      exact ⟨k * p ^ N, by rw [mul_comm k (p ^ N), pow_mul, varpi_pow_root p Q N]⟩
    have hle2 : ∀ r ∈ Submonoid.powers (Q.ϖ N),
        IsUnit ((algebraMap D (Localization.Away (Q.ϖ 0))) r) := by
      intro x hx
      rw [Submonoid.mem_powers_iff] at hx
      obtain ⟨k, rfl⟩ := hx
      rw [map_pow]
      exact hunitQ.pow k
    haveI hLocQ : IsLocalization.Away (Q.ϖ N) (Localization.Away (Q.ϖ 0)) :=
      IsLocalization.of_le (M := Submonoid.powers (Q.ϖ 0)) (Submonoid.powers (Q.ϖ N))
        hle1 hle2
    have hπeQ : (Q.ϖ N) ^ (m * p ^ N) = (Q.ϖ 0) ^ m := by
      rw [mul_comm m (p ^ N), pow_mul, varpi_pow_root p Q N]
    have hx : algebraMap D (Localization.Away (Q.ϖ 0)) ((Q.ϖ N) ^ (m * p ^ N))
        * (algebraMap D (Localization.Away (Q.ϖ 0)) (Qr 0)
          * IsLocalization.Away.invSelf (Q.ϖ 0) ^ m)
        = algebraMap D (Localization.Away (Q.ϖ 0)) (Qr 0) := by
      rw [hπeQ]
      calc algebraMap D (Localization.Away (Q.ϖ 0)) ((Q.ϖ 0) ^ m)
            * (algebraMap D (Localization.Away (Q.ϖ 0)) (Qr 0)
              * IsLocalization.Away.invSelf (Q.ϖ 0) ^ m)
          = algebraMap D (Localization.Away (Q.ϖ 0)) (Qr 0)
            * ((algebraMap D (Localization.Away (Q.ϖ 0)) (Q.ϖ 0)) ^ m
              * IsLocalization.Away.invSelf (Q.ϖ 0) ^ m) := by
            rw [map_pow]; ring
        _ = algebraMap D (Localization.Away (Q.ϖ 0)) (Qr 0) := by
            rw [← mul_pow, IsLocalization.Away.mul_invSelf, one_pow, mul_one]
    have h3c := N3_ker_aeval (C := D) (L := Localization.Away (Q.ϖ 0)) hinjD (Q.ϖ N) (Qr 0)
      (m * p ^ N) (Nat.mul_pos (by omega : 0 < m) (pow_pos (Fact.out : p.Prime).pos N))
      hunitQ hQr0reg _ hx
    rwa [hπeQ] at h3c
  -- the polynomial membership over `Λ̂[X]` for (d)
  obtain ⟨vQ, hvQ, heqQ⟩ := Submodule.mem_map.mp h3
  have heqQ' : (algebraMap D (Localization.Away (Q.ϖ 0)) (PD - Qr 0)
      * IsLocalization.Away.invSelf (Q.ϖ 0) ^ m) ^ N
      = algebraMap D (Localization.Away (Q.ϖ 0)) (Q.ϖ 0) * vQ := by
    rw [← heqQ, LinearMap.mulLeft_apply]
  obtain ⟨hDQ, hmemQ⟩ := poly_mem_of_ker (Q.ϖ 0) m N (PD - Qr 0) _ _ hkerQ hvQ heqQ'
  have hCdQ : Polynomial.C ((PD - algebraMap (Lam1 A p) D (q 0)) ^ N)
      - Polynomial.C ((PD - Qr 0) ^ N) ∈ Ideal.span {Polynomial.C ((Q.ϖ 0) ^ (m * N + 1))} := hCd
  have hmemQD : Polynomial.C ((PD - algebraMap (Lam1 A p) D (q 0)) ^ N) ∈
      Ideal.span {Polynomial.C ((Q.ϖ 0) ^ (m * N + 1))} ⊔
        Ideal.span {Polynomial.C ((Q.ϖ 0) ^ m) * Polynomial.X - Polynomial.C (Qr 0)} := by
    have h1' : Polynomial.C ((PD - Qr 0) ^ N) ∈
        Ideal.span {Polynomial.C ((Q.ϖ 0) ^ (m * N + 1))} ⊔
          Ideal.span {Polynomial.C ((Q.ϖ 0) ^ m) * Polynomial.X - Polynomial.C (Qr 0)} :=
      Submodule.mem_sup.mpr
        ⟨Polynomial.C ((Q.ϖ 0) ^ (m * N + 1)) * hDQ,
          Ideal.mul_mem_right hDQ
            (Ideal.span {Polynomial.C ((Q.ϖ 0) ^ (m * N + 1))})
            (Ideal.subset_span (Set.mem_singleton
              (Polynomial.C ((Q.ϖ 0) ^ (m * N + 1))))),
          Polynomial.C ((PD - Qr 0) ^ N)
            - Polynomial.C ((Q.ϖ 0) ^ (m * N + 1)) * hDQ,
          hmemQ, by ring⟩
    have h3' : Polynomial.C ((PD - algebraMap (Lam1 A p) D (q 0)) ^ N)
        = (Polynomial.C ((PD - algebraMap (Lam1 A p) D (q 0)) ^ N)
            - Polynomial.C ((PD - Qr 0) ^ N)) + Polynomial.C ((PD - Qr 0) ^ N) := by ring
    rw [h3']
    exact Ideal.add_mem _ (Ideal.mem_sup_left hCdQ) h1'
  -- the ideal generated by the `Qr 0`-presentation agrees with the `q 0`-presentation
  have hpoly_eq : Ideal.span {Polynomial.C ((Q.ϖ 0) ^ (m * N + 1))} ⊔
        Ideal.span {Polynomial.C ((Q.ϖ 0) ^ m) * Polynomial.X - Polynomial.C (Qr 0)}
      = Ideal.span {Polynomial.C ((Q.ϖ 0) ^ (m * N + 1))} ⊔
        Ideal.span {Polynomial.C ((Q.ϖ 0) ^ m) * Polynomial.X
          - Polynomial.C (algebraMap (Lam1 A p) D (q 0))} := by
    refine sup_span_eq_of_sub_mem _ ?_
    have hweq : Polynomial.C ((Q.ϖ 0) ^ m) * Polynomial.X - Polynomial.C (Qr 0)
        - (Polynomial.C ((Q.ϖ 0) ^ m) * Polynomial.X
            - Polynomial.C (algebraMap (Lam1 A p) D (q 0)))
        = Polynomial.C (algebraMap (Lam1 A p) D (q 0) - Qr 0) := by
      rw [show Polynomial.C ((Q.ϖ 0) ^ m) * Polynomial.X - Polynomial.C (Qr 0)
          - (Polynomial.C ((Q.ϖ 0) ^ m) * Polynomial.X
              - Polynomial.C (algebraMap (Lam1 A p) D (q 0)))
          = Polynomial.C (algebraMap (Lam1 A p) D (q 0)) - Polynomial.C (Qr 0) from by ring,
        ← Polynomial.C_sub]
    rw [hweq, span_C_singleton_eq_map, Ideal.mem_map_C_iff]
    intro n
    rw [Polynomial.coeff_C]
    by_cases hn : n = 0
    · rw [if_pos hn]
      have hmem : algebraMap (Lam1 A p) D (q 0) - Qr 0 ∈ Ideal.span {Q.ϖ 0 ^ K} := by
        have h2' : algebraMap (Lam1 A p) D (q 0) - Qr 0
            = -(Qr 0 - algebraMap (Lam1 A p) D (q 0)) := by ring
        rw [h2']; exact neg_mem (hq 0)
      exact (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hKpow)) hmem
    · rw [if_neg hn]; exact Ideal.zero_mem _
  -- descent of the two memberships to `Λ[X]`  (N5e)
  set wF : Polynomial (Lam1 A p) := Polynomial.C ((algebraMap A (Lam1 A p) (P.ϖ 0)) ^ m)
      * Polynomial.X - Polynomial.C (Polynomial.aeval (T1 A p 0) F) with hwF
  set wQ : Polynomial (Lam1 A p) := Polynomial.C ((algebraMap A (Lam1 A p) (P.ϖ 0)) ^ m)
      * Polynomial.X - Polynomial.C (q 0) with hwQ
  have hmapF : wF.map (algebraMap (Lam1 A p) D)
      = Polynomial.C ((Q.ϖ 0) ^ m) * Polynomial.X - Polynomial.C PD := by
    rw [hwF, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
      Polynomial.map_C, map_pow, hφπ, ← hPD]
  have hmapQ : wQ.map (algebraMap (Lam1 A p) D)
      = Polynomial.C ((Q.ϖ 0) ^ m) * Polynomial.X
        - Polynomial.C (algebraMap (Lam1 A p) D (q 0)) := by
    rw [hwQ, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
      Polynomial.map_C, map_pow, hφπ]
  have hmapa0 : (Polynomial.C (a0 ^ N)).map (algebraMap (Lam1 A p) D)
      = Polynomial.C ((PD - algebraMap (Lam1 A p) D (q 0)) ^ N) := by
    rw [Polynomial.map_C, map_pow, ha0, RingHom.map_sub, ← hPD]
  have hdesF : Polynomial.C (a0 ^ N) ∈
      Ideal.span {Polynomial.C ((algebraMap A (Lam1 A p) (P.ϖ 0)) ^ (m * N + 1))} ⊔
        Ideal.span {wF} := by
    refine N5e_descent (algebraMap (Lam1 A p) D) (algebraMap A (Lam1 A p) (P.ϖ 0)) (m * N + 1)
      hinjN hsurjN wF (Polynomial.C (a0 ^ N)) ?_
    rw [hmapa0, hmapF, hφπ]
    exact hmemFD
  have hdesQ : Polynomial.C (a0 ^ N) ∈
      Ideal.span {Polynomial.C ((algebraMap A (Lam1 A p) (P.ϖ 0)) ^ (m * N + 1))} ⊔
        Ideal.span {wQ} := by
    refine N5e_descent (algebraMap (Lam1 A p) D) (algebraMap A (Lam1 A p) (P.ϖ 0)) (m * N + 1)
      hinjN hsurjN wQ (Polynomial.C (a0 ^ N)) ?_
    rw [hmapa0, hmapQ, hφπ]
    rw [← hpoly_eq]
    exact hmemQD
  -- convert to the divisibility statements (c) and (d)
  have hc : ∃ v ∈ Algebra.adjoin (Lam1 A p)
        {frac A p (P.ϖ 0) (Polynomial.aeval (T1 A p 0) F) m},
      frac A p (P.ϖ 0) (Polynomial.aeval (T1 A p 0) F - q 0) m ^ N =
        algebraMap A (Lam1Loc A p (P.ϖ 0)) (P.ϖ 0) * v := by
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hdesF
    have hdiv : Polynomial.C ((algebraMap A (Lam1 A p) (P.ϖ 0)) ^ (m * N + 1)) ∣ x :=
      (Ideal.mem_span_singleton (x := x)
        (y := Polynomial.C ((algebraMap A (Lam1 A p) (P.ϖ 0)) ^ (m * N + 1)))).mp hx
    obtain ⟨h, hh⟩ := hdiv
    refine adjoin_mem_of_span_mem A p P (Polynomial.aeval (T1 A p 0) F - q 0)
      (Polynomial.aeval (T1 A p 0) F) m N h ?_
    have : Polynomial.C ((Polynomial.aeval (T1 A p 0) F - q 0) ^ N)
        - Polynomial.C ((algebraMap A (Lam1 A p) (P.ϖ 0)) ^ (m * N + 1)) * h = y := by
      rw [← hxy, hh]; ring
    rw [this, ← hwF]
    exact hy
  have hd : ∃ v ∈ Algebra.adjoin (Lam1 A p) {frac A p (P.ϖ 0) (q 0) m},
      frac A p (P.ϖ 0) (Polynomial.aeval (T1 A p 0) F - q 0) m ^ N =
        algebraMap A (Lam1Loc A p (P.ϖ 0)) (P.ϖ 0) * v := by
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hdesQ
    have hdiv : Polynomial.C ((algebraMap A (Lam1 A p) (P.ϖ 0)) ^ (m * N + 1)) ∣ x :=
      (Ideal.mem_span_singleton (x := x)
        (y := Polynomial.C ((algebraMap A (Lam1 A p) (P.ϖ 0)) ^ (m * N + 1)))).mp hx
    obtain ⟨h, hh⟩ := hdiv
    refine adjoin_mem_of_span_mem A p P (Polynomial.aeval (T1 A p 0) F - q 0) (q 0) m N h ?_
    have : Polynomial.C ((Polynomial.aeval (T1 A p 0) F - q 0) ^ N)
        - Polynomial.C ((algebraMap A (Lam1 A p) (P.ϖ 0)) ^ (m * N + 1)) * h = y := by
      rw [← hxy, hh]; ring
    rw [this, ← hwQ]
    exact hy
  exact ⟨q, N, N, hNpos, ha, hb, hc, hd⟩

end Work.DSM2p
