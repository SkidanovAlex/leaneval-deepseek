import Mathlib
import Submission.Work.BSW.S3.Defs
import Submission.Work.BSW.S3.S31setup
import Submission.Work.BSW.Cases.S31core
import Submission.Work.BSW.Api.card_sup_zpowers
import Submission.Work.BSW.Api.ncard_involutions_eq_index
import Submission.Work.BSW.S3.normalizerStruct
import Submission.Work.BSW.Api.normalizer_K_eq
import Submission.Work.BSW.Cases.Order.centralizerSingletonEqK
import Submission.Work.BSW.Cases.bswS32Setup
import Submission.Work.BSW.Cases.bswS32Count
import Submission.Work.BSW.Cases.bswS32Hall
import Submission.Work.BSW.Cases.bswS32Pow2
import Submission.Work.BSW.Cases.bswS32Bijection
import Submission.Work.BSW.Cases.bswS32U

set_option linter.style.haveILetI false

namespace Work.BSW.Cases

open scoped Pointwise
open Subgroup Work.GW2
open Work.BSW.S3

variable {G : Type} [Group G] [Finite G] {t s x : G} {K : Subgroup G}

/-- The centralizer of an element equals that of its inverse. -/
theorem bswS32_centralizer_singleton_inv {G : Type} [Group G] (a : G) :
    Subgroup.centralizer ({a⁻¹} : Set G) = Subgroup.centralizer ({a} : Set G) := by
  ext c
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h2 := congrArg (fun z => a * z * a) h
    simpa [mul_assoc] using h2.symm
  · intro h
    have h2 := congrArg (fun z => a⁻¹ * z * a⁻¹) h
    simpa [mul_assoc] using h2.symm

/-- If `y` inverts `m`, then `y⁻¹` normalizes the centralizer of `m`. -/
theorem bswS32_conjSub_inv_centralizer {G : Type} [Group G] {m y : G}
    (hinv : y⁻¹ * m * y = m⁻¹) :
    Work.GW2.conjSub y⁻¹ (Subgroup.centralizer ({m} : Set G)) =
      Subgroup.centralizer ({m} : Set G) := by
  have hc : (MulAut.conj y⁻¹) m = m⁻¹ := by rw [MulAut.conj_apply, inv_inv, hinv]
  rw [← centralizer_conjSub y⁻¹ m, hc, bswS32_centralizer_singleton_inv m]

/-- A conjugate of an involution is an involution. -/
theorem bswS32_orderOf_conj_inv {G : Type} [Group G] {t d : G} (ht : orderOf t = 2) :
    orderOf (d⁻¹ * t * d) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu2 : (d⁻¹ * t * d) * (d⁻¹ * t * d) = 1 := by
    rw [show d⁻¹ * t * d * (d⁻¹ * t * d) = d⁻¹ * (t * t) * d by group,
      Work.BSW.mul_self_eq_one_of_orderOf_eq_two ht]
    group
  have hu1 : d⁻¹ * t * d ≠ 1 := by
    intro h1
    have ht1 : t = 1 := by
      have h2 := congrArg (fun z => d * z * d⁻¹) h1
      simpa [mul_assoc] using h2
    rw [ht1, orderOf_one] at ht
    exact absurd ht (by decide)
  exact orderOf_eq_prime (by simpa [pow_two] using hu2) hu1

/-- Bender 1974 §3.2 (lemma `InvertM`): an involution `y` inverting a non-identity element
`m ∈ M = N_G(C_G(x))` commutes with an involution of `M`.

If `m` has even order, `u = m ^ (orderOf m / 2)` is such an involution (`bswS32Pow2`).  If `m`
has odd order and `m ∈ F = C_G(x)`, then `y` normalizes `C_G(m) = F`, so `y ∈ M` and `u = y`
works.  Otherwise `m` has odd order and `m ∉ F`: writing `M = F(K ⊓ M)` (Bender §3.1(ii),
`normalizerStruct`) as `m = c * k₀` with `c ∈ F`, `k₀ ∈ K ⊓ M`, the map
`d ↦ d⁻¹ k₀ d k₀⁻¹` is a bijection of `F` (`bswS32Bijection`, since `C_G(k₀) = K` and
`F ⊓ K = ⊥`), so `m = d⁻¹ k₀ d` for some `d ∈ F`.  Hence `C_G(m) = K^d`, `y` normalizes it,
and therefore `y ∈ N_G(K)^d = H^d = C_G(d⁻¹ t d)`: the involution `u = d⁻¹ t d ∈ M` works. -/
theorem bswS32InvertM_local (h : BSWHyps2 G t s K) (hx : x ∉ Work.BSW.HG t)
    (hinv : t⁻¹ * x * t = x⁻¹) :
    ∀ m : G, m ∈ Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G) → m ≠ 1 →
      ∀ y : G, orderOf y = 2 → y⁻¹ * m * y = m⁻¹ →
        ∃ u : G, u ∈ Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G) ∧
          orderOf u = 2 ∧ y * u = u * y := by
  intro m hmM hm1 y hy2 hyinv
  rcases Nat.even_or_odd (orderOf m) with heven | hodd
  · -- `m` has even order: take `u = m ^ (orderOf m / 2)`, an involution inverted by `y`
    obtain ⟨hu2, hcomm⟩ := bswS32Pow2 hm1 heven hyinv
    exact ⟨m ^ (orderOf m / 2), (NF x).pow_mem hmM _, hu2, hcomm⟩
  by_cases hmF : m ∈ CF x
  · -- `m ∈ F`: `y` normalizes `C_G(m) = F`, so `y ∈ M` and `u = y` works
    have hCm : Subgroup.centralizer ({m} : Set G) = CF x :=
      centralizer_eq_of_mem_centralizer h hx hinv m hmF hm1
    have hcs := bswS32_conjSub_inv_centralizer hyinv
    have hyn : y⁻¹ ∈ Subgroup.normalizer (Subgroup.centralizer ({m} : Set G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      simpa [Work.GW2.conjSub] using hcs
    have hyN : y ∈ NF x := by
      have h1 : y ∈ Subgroup.normalizer (Subgroup.centralizer ({m} : Set G) : Set G) := by
        simpa using
          (Subgroup.normalizer (Subgroup.centralizer ({m} : Set G) : Set G)).inv_mem hyn
      have h2 : Subgroup.normalizer (Subgroup.centralizer ({m} : Set G) : Set G) = NF x := by
        rw [hCm]
      rwa [h2] at h1
    exact ⟨y, hyN, hy2, rfl⟩
  · -- `m ∉ F`, odd order: write `m = c * k₀` and conjugate `k₀` back to `m`
    -- factorization `M = F ⊔ (K ⊓ M) = F * (K ⊓ M)`
    have hN_le : K ⊓ NF x ≤ Subgroup.normalizer (CF x : Set G) := inf_le_right
    have hcoe : (↑(CF x ⊔ (K ⊓ NF x)) : Set G) =
        (CF x : Set G) * ((K ⊓ NF x : Subgroup G) : Set G) :=
      Subgroup.coe_mul_of_right_le_normalizer_left (CF x) (K ⊓ NF x) hN_le
    have hm_prod : m ∈ (CF x : Set G) * ((K ⊓ NF x : Subgroup G) : Set G) := by
      have hm_sup : m ∈ (CF x ⊔ (K ⊓ NF x) : Subgroup G) := by
        rw [← normalizerStruct h hx hinv]; exact hmM
      rw [← hcoe]
      exact hm_sup
    obtain ⟨c, hcF, k0, hk0, hck⟩ := Set.mem_mul.mp hm_prod
    have hk0K : k0 ∈ K := hk0.1
    have hk0M : k0 ∈ NF x := hk0.2
    have hk0_ne1 : k0 ≠ 1 := by
      intro h1
      rw [h1, mul_one] at hck
      exact hmF (hck ▸ hcF)
    have hk0_net : k0 ≠ t := by
      intro h1
      have hm2 : m * m = 1 := by
        rw [← hck, h1]
        calc (c * t) * (c * t) = c * (t * c * t) := by group
          _ = c * c⁻¹ := by rw [inverts_centralizer h hx hinv c hcF]
          _ = 1 := mul_inv_cancel c
      have hdvd : orderOf m ∣ 2 := by
        rw [orderOf_dvd_iff_pow_eq_one]; simpa [pow_two] using hm2
      have hle : orderOf m ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
      obtain ⟨e, he⟩ := hodd
      rw [he] at hle
      have he0 : e = 0 := by omega
      have h1' : orderOf m = 1 := by rw [he, he0]; norm_num
      exact hm1 (orderOf_eq_one_iff.mp h1')
    have hCk0 : Subgroup.centralizer ({k0} : Set G) = K :=
      Work.BSW.Cases.Order.centralizerSingletonEqK h hk0K hk0_ne1 hk0_net
    -- the bijection on `F`
    obtain ⟨d, hdF, hdk⟩ :=
      bswS32Bijection (F := CF x) (K := K) (k := k0)
        (fun a ha b hb => CF_comm h hx hinv ha hb) hk0M hCk0
        (inf_K_centralizer_eq_bot h hx) c hcF
    have hmd : m = d⁻¹ * k0 * d := by rw [← hck, ← hdk]; group
    -- `C_G(m) = K^d`, so `y ∈ N_G(K^d) = H^d = C_G(t^d)`
    have hconj : (MulAut.conj d⁻¹) k0 = d⁻¹ * k0 * d := by
      rw [MulAut.conj_apply, inv_inv]
    have hCm_eq : Subgroup.centralizer ({m} : Set G) =
        Work.GW2.conjSub d⁻¹ K := by
      rw [hmd, ← hconj, centralizer_conjSub, hCk0]
    have hyCm : y ∈ Subgroup.normalizer (Subgroup.centralizer ({m} : Set G) : Set G) := by
      have hcs := bswS32_conjSub_inv_centralizer hyinv
      have hyi : y⁻¹ ∈ Subgroup.normalizer (Subgroup.centralizer ({m} : Set G) : Set G) := by
        rw [Subgroup.mem_normalizer_iff_map_conj_eq]
        simpa [Work.GW2.conjSub] using hcs
      simpa using
        (Subgroup.normalizer (Subgroup.centralizer ({m} : Set G) : Set G)).inv_mem hyi
    have hyN' : y ∈ Subgroup.normalizer (Work.GW2.conjSub d⁻¹ K : Set G) := by
      have h1 := hyCm
      rwa [hCm_eq] at h1
    have hyH : y ∈ Work.GW2.conjSub d⁻¹ (Subgroup.centralizer ({t} : Set G)) := by
      have h1 : Subgroup.normalizer (Work.GW2.conjSub d⁻¹ K : Set G) =
          Work.GW2.conjSub d⁻¹ (Subgroup.centralizer ({t} : Set G)) := by
        rw [← normalizer_conjSub d⁻¹ K, Work.BSW.Api.normalizer_K_eq h]
      rwa [h1] at hyN'
    have hyu : y ∈ Subgroup.centralizer ({(MulAut.conj d⁻¹) t} : Set G) := by
      rwa [← centralizer_conjSub d⁻¹ t] at hyH
    refine ⟨(MulAut.conj d⁻¹) t, ?_, ?_, ?_⟩
    · have hdM : d ∈ NF x := Subgroup.le_normalizer hdF
      rw [MulAut.conj_apply, inv_inv]
      exact (NF x).mul_mem ((NF x).mul_mem ((NF x).inv_mem hdM) (t_mem_NF h hx hinv)) hdM
    · rw [MulAut.conj_apply, inv_inv]
      exact bswS32_orderOf_conj_inv (Work.BSW.orderOf_t h)
    · exact Subgroup.mem_centralizer_singleton_iff.mp hyu

/-- Bender 1974 §3.2 (the coset count), as designed in `Submission/Work/BSW/S3/Defs.lean`
(`BSWS32Prop`). With `F = C_G(x)`, `M = N_G(F)`, `f = |F|`, `n = |K ⊓ M|`, `m = |G:M|`,
`I = |G:C_G(t)|`:

* every involution `u ∈ M` has `C_M(u) = M ∩ M^g` of order `n` for `g ∈ C_G(u) ∖ C_M(u)`
  (using `F ∩ M^g = 1`), the coset `Mg` contains exactly `n` elements of `C_G(u)` and no element
  commuting with another involution of `M`; the cosets meeting a centralizer of an involution of
  `M` in a full `n`-set are `f(2k/n − 1)` and `M` itself, giving `1 + f(2k/n − 1) ≤ m`;
* the further cosets are `F`-invariant (free orbits), giving `f ∣ m − (1 + f(2k/n − 1))`;
* the involutions not in `M` number `I − f(k+1)` and each further coset contains at most one,
  giving `f(k+1) ≤ I` and `I − f(k+1) ≤ m − (1 + f(2k/n − 1))`. -/
theorem bswS32 : Work.BSW.BSWS32Prop := by
  intro G _ _ t s K x h hx hinv
  have hHall := (bswS32Hall h hx hinv).2
  have hcardC : ∀ u : G, orderOf u = 2 → u ∈ NF x →
      Nat.card ↥(Subgroup.centralizer ({u} : Set G)) = 2 * Nat.card K :=
    fun u hu _ => card_centralizer_eq h hu
  have hU := bswS32U h hx hinv
  have hInvertM := bswS32InvertM_local h hx hinv
  exact ⟨claim1 (x := x) h hx hinv hHall hcardC,
    claim2 (x := x) h hx hinv hHall hcardC,
    claim3 (x := x) h hx hinv hU,
    claim4 (x := x) h hx hinv hHall hcardC hU hInvertM⟩

end Work.BSW.Cases
