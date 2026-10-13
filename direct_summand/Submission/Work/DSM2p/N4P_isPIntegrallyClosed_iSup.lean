import Mathlib
import Submission.Work.DSM2p.Basic
import Submission.Work.DSM2p.N4a_isPIntegrallyClosed_of_frobInj
import Submission.Work.DSM2p.N4b_expand_pow_root
import Submission.Work.DSM2p.N4c_poly_frobInj
import Submission.Work.DSM2p.N4d_expand_F_sub
import Submission.Work.DSM2p.N4e_sub_pow_sub_pow_mem
import Submission.Work.DSM2p.N4f_aeval_sub_mem
import Submission.Work.DSM2p.N4g_aeval_mem

/-!
# `Work.DSM2p.N4P_isPIntegrallyClosed_iSup`

The assembled variant of node **N4** of the H2 design
(`sources/dsmap/direct_summand_m2p_h2_design.md`, §2): the union `U = ⨆_j C[x_j]` of the
presentations `C[x_j] ≅ C[X]/(s_j X - q_j)` of `L` is `p`-integrally closed in `L`.

Unlike `N4_isPIntegrallyClosed_iSup`, which carried local `tmp_` stubs, this module assembles the
proof from the separately proved pieces `N4a`–`N4g`; the remaining gap of the `tmp_` version —
the coefficientwise Frobenius injectivity on `C[X]` (`N4c`) — is proved here from the
coefficientwise congruence `N4P_coeff_pow_prime_mem`, also proved here.

## The mathematics

`U` is p-integrally closed in `L` by the Frobenius-mod-`ϖ₁` argument (`N4a`): given `y ∈ U` and
`c ∈ U` with `y ^ p = ϖ₁ ^ p * c`, one shows `y = ϖ₁ * c'` with `c' ∈ U`.  Writing `y` and `c`
in a common stage `C[x_j]` as `y = g(x_j)`, `c = h(x_j)`, the relation lifts to a polynomial
identity
`g ^ p - ϖ₁ ^ p * h ∈ (s_j X - q_j)  in  C[X]`,
i.e. `g ^ p - ϖ₁ ^ p * h = r * (s_j X - q_j)`.  Applying Frobenius (`X ↦ X ^ p`) and the
relations `(s_{j+1}) ^ p = s_j`, `q_{j+1} ^ p ≡ q_j mod (s_j ϖ₁ ^ p)` turns this into
`(expand g) ^ p ≡ (F_{j+1} * r') ^ p mod (ϖ₁ ^ p)`,
where `F_{j+1} = s_{j+1} X - q_{j+1}` and `expand` is the `p`-th power map of `X`.  Coefficientwise
Frobenius injectivity modulo `ϖ₁` — the content of `N4P_poly_frobInj`, reduced here to the
congruence `(H ^ p).coeff (i * p) ≡ (H.coeff i) ^ p mod (p)` — then gives
`expand g ∈ (ϖ₁) + (F_{j+1})`, and evaluating at `x_{j+1}` produces the required cofactor in `U`.
-/

namespace Work.DSM2p

open Polynomial

/-! ## Local helpers -/

/-- Difference relation between consecutive stages: `x j = x (j+1)^p - ϖ₁^p * b`. -/
theorem N4P_x_rel {C L : Type*} [CommRing C] [CommRing L] [Algebra C L]
    (p : ℕ) (ϖ₁ : C) (s q : ℕ → C) (x : ℕ → L)
    (hs : ∀ j, s (j + 1) ^ p = s j)
    (hsL : ∀ j, IsUnit (algebraMap C L (s j)))
    (hx : ∀ j, algebraMap C L (s j) * x j = algebraMap C L (q j))
    (hq : ∀ j, q (j + 1) ^ p - q j ∈ Ideal.span {s j * ϖ₁ ^ p}) (j : ℕ) :
    ∃ b : C, x j = x (j + 1) ^ p - algebraMap C L (ϖ₁ ^ p * b) := by
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (hq j)
  refine ⟨b, ?_⟩
  have h1 : algebraMap C L (s j) * x (j + 1) ^ p = algebraMap C L (q (j + 1) ^ p) := by
    have h : algebraMap C L (s j) = (algebraMap C L (s (j + 1))) ^ p := by rw [← hs j, map_pow]
    rw [h, ← mul_pow, hx (j + 1), map_pow]
  have h2 : algebraMap C L (q (j + 1) ^ p)
      = algebraMap C L (q j) + algebraMap C L (s j) * algebraMap C L (ϖ₁ ^ p * b) := by
    have hqb : q (j + 1) ^ p = q j + b * (s j * ϖ₁ ^ p) := by rw [hb]; ring
    rw [hqb]
    simp only [map_add, map_mul]
    ring
  have hmain : algebraMap C L (s j) * x (j + 1) ^ p
      = algebraMap C L (s j) * (x j + algebraMap C L (ϖ₁ ^ p * b)) := by
    rw [h1, h2, ← hx j, map_mul]
    ring
  have hcancel := IsUnit.mul_left_cancel (hsL j) hmain
  rw [hcancel]
  ring

/-! ## Coefficientwise Frobenius modulo `p` -/

/-- **Coefficientwise Frobenius modulo `p`.**  If `p` is prime, then for every polynomial `H`
over a commutative ring `C` the coefficient of `X ^ (i * p)` in `H ^ p` is congruent to the
`p`-th power of the `i`-th coefficient of `H` modulo `p`.

This is the elementary form of "Frobenius is coefficientwise" used in `N4P_poly_frobInj`: the
coefficient of `X ^ (i * p)` in `H ^ p` is the sum over ordered `p`-tuples of exponents summing
to `i * p`; the constant tuple `(i, …, i)` contributes exactly `(H.coeff i) ^ p`, and every other
`p`-tuple of exponents appears in an orbit of `p` distinct tuples (a `p`-cycle) of the same
product, so its total contribution is a multiple of `p`.

The proof below avoids orbit counting: it is an induction on the polynomial, where the
additive step is `(f + g) ^ p ≡ f ^ p + g ^ p (mod p)` (`exists_add_pow_prime_eq`). -/
theorem N4P_coeff_pow_prime_mem {C : Type*} [CommRing C] (p : ℕ) (hp : p.Prime)
    (H : Polynomial C) (i : ℕ) :
    (H ^ p).coeff (i * p) - (H.coeff i) ^ p ∈ Ideal.span {(p : C)} := by
  induction H using Polynomial.induction_on' with
  | add f g hf hg =>
      obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp f g
      obtain ⟨w, hw⟩ := exists_add_pow_prime_eq hp (f.coeff i) (g.coeff i)
      have hW : (↑p : Polynomial C) * f * g * r = Polynomial.C (p : C) * (f * g * r) := by
        rw [Polynomial.C_eq_natCast]; ring
      rw [hr, hW]
      simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul]
      have hkey : (f ^ p).coeff (i * p) + (g ^ p).coeff (i * p)
            + (p : C) * ((f * g * r).coeff (i * p)) - (f.coeff i + g.coeff i) ^ p
          = ((f ^ p).coeff (i * p) - (f.coeff i) ^ p)
            + ((g ^ p).coeff (i * p) - (g.coeff i) ^ p)
            + (p : C) * ((f * g * r).coeff (i * p) - f.coeff i * g.coeff i * w) := by
        rw [hw]; ring
      rw [hkey]
      exact Ideal.add_mem _ (Ideal.add_mem _ hf hg)
        (Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton (p : C))))
  | monomial n a =>
      rw [Polynomial.monomial_pow, Polynomial.coeff_monomial, Polynomial.coeff_monomial]
      by_cases h : n = i
      · rw [h]; simp
      · have hnp : ¬ (n * p = i * p) := fun hc => h (Nat.mul_right_cancel hp.pos hc)
        simp [h, hnp, zero_pow hp.ne_zero]

/-- **Coefficientwise Frobenius injectivity on `C[X]`** (node `N4c` of the H2 design).

If `(p : C) ∈ (ϖ₁ ^ p)` and `b ^ p ∈ (ϖ₁ ^ p)` implies `b ∈ (ϖ₁)` for all `b : C`, then the
same statement holds coefficientwise for polynomials: `H ^ p ∈ (C ϖ₁ ^ p)` implies
`H ∈ (C ϖ₁)`.

Indeed, if `H ^ p = C (ϖ₁ ^ p) * G` then every coefficient of `H ^ p` lies in `(ϖ₁ ^ p)`; in
particular, by `N4P_coeff_pow_prime_mem`,
`(H.coeff i) ^ p ≡ (H ^ p).coeff (i * p) mod (p)`, and `(p : C) ∈ (ϖ₁ ^ p)` by hypothesis, so
`(H.coeff i) ^ p ∈ (ϖ₁ ^ p)` and hence `H.coeff i ∈ (ϖ₁)`.  The conclusion follows by
coefficientwise membership. -/
theorem N4P_poly_frobInj {C : Type*} [CommRing C] (p : ℕ) [Fact p.Prime]
    (ϖ₁ : C) (hp : (p : C) ∈ Ideal.span {ϖ₁ ^ p})
    (hinjF : ∀ b : C, b ^ p ∈ Ideal.span {ϖ₁ ^ p} → b ∈ Ideal.span {ϖ₁})
    (H : Polynomial C) (hH : H ^ p ∈ Ideal.span {Polynomial.C (ϖ₁ ^ p)}) :
    H ∈ Ideal.span {Polynomial.C ϖ₁} := by
  have hpp : p.Prime := Fact.out
  -- the coefficients of `H ^ p` all lie in `(ϖ₁ ^ p)`
  have hcoeff_mem : ∀ n : ℕ, (H ^ p).coeff n ∈ Ideal.span {ϖ₁ ^ p} := by
    intro n
    obtain ⟨G, hG⟩ := Ideal.mem_span_singleton'.mp hH
    have hGn : (H ^ p).coeff n = ϖ₁ ^ p * G.coeff n := by
      rw [← hG, show G * Polynomial.C (ϖ₁ ^ p) = Polynomial.C (ϖ₁ ^ p) * G from mul_comm _ _,
        Polynomial.coeff_C_mul]
    rw [hGn]
    exact Ideal.mul_mem_right (G.coeff n) _ (Ideal.subset_span (Set.mem_singleton (ϖ₁ ^ p)))
  -- coefficientwise conclusion
  have hcoeff : ∀ i : ℕ, H.coeff i ∈ Ideal.span {ϖ₁} := by
    intro i
    refine hinjF _ ?_
    have hle := (Ideal.span_singleton_le_iff_mem (Ideal.span {ϖ₁ ^ p})).mpr hp
    have hc := N4P_coeff_pow_prime_mem p hpp H i
    have key : (H.coeff i) ^ p
        = (H ^ p).coeff (i * p) - ((H ^ p).coeff (i * p) - (H.coeff i) ^ p) := by ring
    rw [key]
    exact Ideal.sub_mem _ (hcoeff_mem _) (hle hc)
  rw [← Polynomial.sum_C_mul_X_pow_eq H, Polynomial.sum_def]
  refine Ideal.sum_mem _ fun n _ => ?_
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp (hcoeff n)
  have hCn : Polynomial.C (H.coeff n) ∈ Ideal.span {Polynomial.C ϖ₁} := by
    refine Ideal.mem_span_singleton'.mpr ⟨Polynomial.C y, ?_⟩
    rw [← Polynomial.C_mul, hy]
  exact Ideal.mul_mem_right _ _ hCn

/-! ## The main theorem -/

theorem N4P_isPIntegrallyClosed_iSup {C L : Type*} [CommRing C] [CommRing L] [Algebra C L]
    (p : ℕ) [Fact p.Prime]
    (hinj : Function.Injective (algebraMap C L)) (ϖ₁ : C)
    (hϖL : IsUnit (algebraMap C L ϖ₁))
    (hgen : ∀ z : L, ∃ k : ℕ, ∃ c : C, algebraMap C L (ϖ₁ ^ k) * z = algebraMap C L c)
    (hp : (p : C) ∈ Ideal.span {ϖ₁ ^ p})
    (hsurj : ∀ c : C, ∃ b : C, c - b ^ p ∈ Ideal.span {ϖ₁ ^ p})
    (hinjF : ∀ b : C, b ^ p ∈ Ideal.span {ϖ₁ ^ p} → b ∈ Ideal.span {ϖ₁})
    (s q : ℕ → C) (x : ℕ → L)
    (hs : ∀ j, s (j + 1) ^ p = s j) (hsL : ∀ j, IsUnit (algebraMap C L (s j)))
    (hx : ∀ j, algebraMap C L (s j) * x j = algebraMap C L (q j))
    (hq : ∀ j, q (j + 1) ^ p - q j ∈ Ideal.span {s j * ϖ₁ ^ p})
    (hker : ∀ j, RingHom.ker (Polynomial.aeval (R := C) (x j)).toRingHom =
      Ideal.span {Polynomial.C (s j) * Polynomial.X - Polynomial.C (q j)}) :
    IsPIntegrallyClosedIn p (⨆ j, (Algebra.adjoin C {x j}).toSubring) := by
  have hpp : p.Prime := Fact.out
  have hp1 : 0 < p := hpp.pos
  -- `hinj` is inherited from the source statement (used upstream, in the presentations `hker`).
  have _ : Function.Injective (algebraMap C L) := hinj
  let S : ℕ → Subring L := fun j => (Algebra.adjoin C {x j}).toSubring
  change IsPIntegrallyClosedIn p (⨆ j, S j)
  -- ## Monotonicity of the stages
  have hxmem : ∀ j, x j ∈ Algebra.adjoin C {x (j + 1)} := by
    intro j
    obtain ⟨b, hb⟩ := N4P_x_rel p ϖ₁ s q x hs hsL hx hq j
    rw [hb]
    exact Subalgebra.sub_mem _ (Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton _)) p)
      (Subalgebra.algebraMap_mem _ _)
  have hstep : ∀ j, S j ≤ S (j + 1) := by
    intro j z hz
    rw [Subalgebra.mem_toSubring] at hz ⊢
    exact (Algebra.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (hxmem j))) hz
  have hmono : Monotone S := monotone_nat_of_le_succ hstep
  have hdir : Directed (· ≤ ·) S :=
    fun i j => ⟨max i j, hmono (le_max_left i j), hmono (le_max_right i j)⟩
  have hcmem : ∀ c : C, algebraMap C L c ∈ ⨆ j, S j := fun c =>
    le_iSup S 0 (by rw [Subalgebra.mem_toSubring]; exact Subalgebra.algebraMap_mem _ c)
  have hxU : ∀ j, x j ∈ ⨆ j, S j := fun j =>
    le_iSup S j (by rw [Subalgebra.mem_toSubring]; exact Algebra.subset_adjoin (Set.mem_singleton _))
  refine N4a_isPIntegrallyClosed_of_frobInj p (⨆ j, S j) (algebraMap C L ϖ₁) (hcmem ϖ₁) hϖL ?_ ?_
  · intro z
    obtain ⟨k, c, hc⟩ := hgen z
    exact ⟨k, by rw [← map_pow, hc]; exact hcmem c⟩
  · intro y hyU
    rintro ⟨c, hcU, hyc⟩
    -- ## Put `y` and `c` in a common stage
    obtain ⟨J0, hyJ0⟩ := (Subring.mem_iSup_of_directed (S := S) hdir).mp hyU
    obtain ⟨K0, hcK0⟩ := (Subring.mem_iSup_of_directed (S := S) hdir).mp hcU
    set JN : ℕ := max J0 K0
    have hyJN : y ∈ S JN := hmono (le_max_left J0 K0) hyJ0
    have hcJN : c ∈ S JN := hmono (le_max_right J0 K0) hcK0
    rw [Subalgebra.mem_toSubring, Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range]
      at hyJN hcJN
    obtain ⟨g, hg⟩ := hyJN
    obtain ⟨h, hh⟩ := hcJN
    -- ## The polynomial relation `g^p - ϖ₁^p h ∈ (C (s JN) X - C (q JN))`
    have hgpoly : g ^ p - Polynomial.C (ϖ₁ ^ p) * h ∈
        Ideal.span {Polynomial.C (s JN) * Polynomial.X - Polynomial.C (q JN)} := by
      rw [← hker JN]
      apply (RingHom.mem_ker).mp
      change (Polynomial.aeval (R := C) (x JN)) (g ^ p - Polynomial.C (ϖ₁ ^ p) * h) = 0
      rw [map_sub, map_mul, map_pow, Polynomial.aeval_C, hg, hh]
      rw [map_pow, hyc]
      ring
    -- ## The polynomial core
    set FJ : Polynomial C := Polynomial.C (s JN) * Polynomial.X - Polynomial.C (q JN) with hFJ
    set F1 : Polynomial C :=
      Polynomial.C (s (JN + 1)) * Polynomial.X - Polynomial.C (q (JN + 1)) with hF1
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hgpoly
    -- hr : r * FJ = g^p - C (ϖ₁^p) * h
    obtain ⟨r', hr'⟩ := N4b_expand_pow_root p ϖ₁ hp hsurj r
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hr'
    -- hw : w * C (ϖ₁^p) = expand p r - r'^p
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp
      (N4d_expand_F_sub (p := p) ϖ₁ (s JN) (s (JN + 1)) (q JN) (q (JN + 1)) hp
        (hs JN) (hq JN))
    -- hz : z * C (ϖ₁^p) = expand p FJ - F1^p
    have hrE : (Polynomial.expand C p) g ^ p
        = (Polynomial.expand C p) r * (Polynomial.expand C p) FJ
          + Polynomial.C (ϖ₁ ^ p) * (Polynomial.expand C p) h := by
      have h' := congrArg (Polynomial.expand C p) hr
      simp only [map_mul, map_sub, map_pow, Polynomial.expand_C] at h'
      rw [← Polynomial.C_pow] at h'
      rw [h']; ring
    have hdexp : (Polynomial.expand C p) FJ = F1 ^ p + z * Polynomial.C (ϖ₁ ^ p) := by
      have h' : (Polynomial.expand C p) FJ - F1 ^ p = z * Polynomial.C (ϖ₁ ^ p) := hz.symm
      rw [← h']; ring
    have hwexp : (Polynomial.expand C p) r = r' ^ p + w * Polynomial.C (ϖ₁ ^ p) := by
      have h' : (Polynomial.expand C p) r - r' ^ p = w * Polynomial.C (ϖ₁ ^ p) := hw.symm
      rw [← h']; ring
    have hmain : (Polynomial.expand C p) g ^ p - (F1 * r') ^ p ∈
        Ideal.span {Polynomial.C (ϖ₁ ^ p)} := by
      have hsub : (Polynomial.expand C p) g ^ p - (F1 * r') ^ p
          = ((Polynomial.expand C p) h + z * r' ^ p + w * F1 ^ p
              + z * w * Polynomial.C (ϖ₁ ^ p)) * Polynomial.C (ϖ₁ ^ p) := by
        rw [hrE, hdexp, hwexp]
        ring
      rw [hsub]
      exact Ideal.mem_span_singleton'.mpr ⟨_, rfl⟩
    have hpI : (p : Polynomial C) ∈ Ideal.span {Polynomial.C (ϖ₁ ^ p)} := by
      obtain ⟨x0, hx0⟩ := Ideal.mem_span_singleton'.mp hp
      exact Ideal.mem_span_singleton'.mpr
        ⟨Polynomial.C x0, by rw [← Polynomial.C_mul, hx0]; exact map_natCast (Polynomial.C) p⟩
    have hple : Ideal.span {(p : Polynomial C)} ≤ Ideal.span {Polynomial.C (ϖ₁ ^ p)} :=
      (Ideal.span_singleton_le_iff_mem _).mpr hpI
    have hHp : ((Polynomial.expand C p) g - F1 * r') ^ p ∈
        Ideal.span {Polynomial.C (ϖ₁ ^ p)} := by
      have he := hple (N4e_sub_pow_sub_pow_mem p hpp ((Polynomial.expand C p) g) (F1 * r'))
      have hEq : ((Polynomial.expand C p) g - F1 * r') ^ p
          = ((Polynomial.expand C p) g ^ p - (F1 * r') ^ p)
            + (((Polynomial.expand C p) g - F1 * r') ^ p
                - ((Polynomial.expand C p) g ^ p - (F1 * r') ^ p)) := by ring
      rw [hEq]
      exact Ideal.add_mem _ hmain he
    have hG : (Polynomial.expand C p) g - F1 * r' ∈ Ideal.span {Polynomial.C ϖ₁} :=
      N4P_poly_frobInj p ϖ₁ hp hinjF _ hHp
    have hfin : (Polynomial.expand C p) g ∈ Ideal.span {Polynomial.C ϖ₁} ⊔ Ideal.span {F1} :=
      Submodule.mem_sup.mpr
        ⟨_, hG, F1 * r', Ideal.mem_span_singleton.mpr ⟨r', rfl⟩, by ring⟩
    -- ## Evaluate at `x (JN+1)`
    obtain ⟨A, hA, B, hB, hAB⟩ := Submodule.mem_sup.mp hfin
    obtain ⟨A', hA'⟩ := Ideal.mem_span_singleton'.mp hA
    obtain ⟨B', hB'⟩ := Ideal.mem_span_singleton'.mp hB
    have hBzero : (Polynomial.aeval (x (JN + 1))) B = 0 := by
      rw [← hB', map_mul]
      have h1 : (Polynomial.aeval (x (JN + 1))) F1 = 0 := by
        rw [hF1]
        simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
        rw [hx (JN + 1)]
        ring
      rw [h1, mul_zero]
    have hAval : (Polynomial.aeval (x (JN + 1))) A
        = algebraMap C L ϖ₁ * (Polynomial.aeval (x (JN + 1))) A' := by
      rw [← hA', map_mul, Polynomial.aeval_C]
      ring
    have hsum : (Polynomial.aeval (x (JN + 1))) ((Polynomial.expand C p) g)
        = algebraMap C L ϖ₁ * (Polynomial.aeval (x (JN + 1))) A' := by
      rw [← hAB, map_add, hAval, hBzero, add_zero]
    have hA'U : (Polynomial.aeval (x (JN + 1))) A' ∈ ⨆ j, S j :=
      N4g_aeval_mem _ hcmem (hxU (JN + 1)) A'
    -- ## The difference `y - g((x (JN+1))^p)`
    obtain ⟨sc, hscU, hsc⟩ :=
      N4f_aeval_sub_mem (⨆ j, S j) hcmem (hxU JN) (Subring.pow_mem _ (hxU (JN + 1)) p) g
    obtain ⟨b, hb⟩ := N4P_x_rel p ϖ₁ s q x hs hsL hx hq JN
    have hδeq : x JN - x (JN + 1) ^ p
        = -(algebraMap C L ϖ₁ * algebraMap C L (ϖ₁ ^ (p - 1) * b)) := by
      rw [hb]
      have hpow : ϖ₁ ^ p * b = ϖ₁ * (ϖ₁ ^ (p - 1) * b) := by
        rw [← pow_sub_one_mul (n := p) hpp.ne_zero]
        ring
      rw [hpow, map_mul, map_mul]
      ring
    have hdy : y - (Polynomial.aeval (x (JN + 1))) ((Polynomial.expand C p) g)
        = algebraMap C L ϖ₁ * (-(algebraMap C L (ϖ₁ ^ (p - 1) * b) * sc)) := by
      rw [← hg, Polynomial.expand_aeval, hsc, hδeq]
      ring
    have hfinU : -(algebraMap C L (ϖ₁ ^ (p - 1) * b) * sc) ∈ ⨆ j, S j :=
      (⨆ j, S j).neg_mem ((⨆ j, S j).mul_mem (hcmem _) hscU)
    refine ⟨-(algebraMap C L (ϖ₁ ^ (p - 1) * b) * sc) + (Polynomial.aeval (x (JN + 1))) A',
      (⨆ j, S j).add_mem hfinU hA'U, ?_⟩
    rw [mul_add, ← hdy, ← hsum]
    ring

end Work.DSM2p
