import Mathlib
import Submission.Work.CORE4.NotA7Defs
import Submission.Work.CORE4.A7Split
import Submission.Work.CORE4.Case2SevenAux

namespace Work.CORE4.NotA7

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- A finite subgroup of odd order that normalizes a subgroup of order `3` centralizes it.

`K` is cyclic, so `Aut(K)` has order `Nat.totient 3 = 2`; the conjugation homomorphism
`N(K) →* MulAut K` therefore has image of order dividing `|H|` (odd) and dividing `2`. -/
theorem le_centralizer_of_le_normalizer_of_card_three {G : Type} [Group G] [Finite G]
    {H K : Subgroup G} (hK : Nat.card ↥K = 3)
    (hN : H ≤ Subgroup.normalizer (K : Set G)) (hodd : Odd (Nat.card ↥H)) :
    H ≤ Subgroup.centralizer (K : Set G) := by
  intro x hx
  haveI : IsCyclic ↥K := isCyclic_of_prime_card hK
  have hcardAut : Nat.card (MulAut ↥K) = 2 := by
    rw [IsCyclic.card_mulAut, hK, Nat.totient_prime Nat.prime_three]
  have hmemN : x ∈ Subgroup.normalizer (K : Set G) := hN hx
  have hφx : (Subgroup.normalizerMonoidHom K) ⟨x, hmemN⟩ = 1 := by
    have h2 : orderOf ((Subgroup.normalizerMonoidHom K) ⟨x, hmemN⟩) ∣ 2 := by
      have := Subgroup.orderOf_dvd_natCard (⊤ : Subgroup (MulAut ↥K))
        (Subgroup.mem_top ((Subgroup.normalizerMonoidHom K) ⟨x, hmemN⟩))
      rw [Subgroup.card_top, hcardAut] at this
      exact this
    have h1 : orderOf ((Subgroup.normalizerMonoidHom K) ⟨x, hmemN⟩) ∣ orderOf x := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← map_pow]
      have hpow : (⟨x, hmemN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ orderOf x = 1 := by
        rw [← Subgroup.orderOf_mk x hmemN, pow_orderOf_eq_one]
      rw [hpow, map_one]
    have h3 : orderOf ((Subgroup.normalizerMonoidHom K) ⟨x, hmemN⟩) ∣ Nat.card ↥H :=
      h1.trans (Subgroup.orderOf_dvd_natCard H hx)
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact orderOf_eq_one_iff.mp h
    · exfalso
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (h ▸ h3))
  have hker : (⟨x, hmemN⟩ : ↥(Subgroup.normalizer (K : Set G))) ∈
      (Subgroup.normalizerMonoidHom K).ker :=
    MonoidHom.mem_ker.mpr hφx
  rw [Subgroup.normalizerMonoidHom_ker] at hker
  exact Subgroup.mem_subgroupOf.mp hker

/-- **C10.A3' part 1** (Bender 1981, §4, p. 226: "by (7) and (8), `U` is a 3-group"):
`U = O(H)` is a `3`-group.

Hypotheses: `Hyp9 G B C` (BenderCtx, `Case2 B`, `Case2PrePlus`, `Case2SevenFacts`,
`Case2EightAll`) and `A7Facts1 C.D` (`|K| = 3`, `|F| = 3`, `K₀ = K`, `π(F(U)) = {3}`).

Route.
* `F(U) = fittingIn B.U` is a `3`-group: `primesOf (fittingIn B.U) = B.piFU = {3}`
  (`Case2SevenFacts` conjunct 2 with `K₀ = K`); use Mathlib's
  `isPGroup_iff_primeFactors_card_subset`.
* `K` is a `3`-group (`|K| = 3`) and `B₀ = C_{U ⊓ M}(s)` is a `3`-group: `B₀` normalizes `K`
  (as `B₀ ≤ U ⊓ M` and `K ⊴ U ⊓ M`, `Work.CORE4.Case2Data.K_normal_in_UinfM`) and normalizes `F`
  (`B₀ ≤ M = N_G(F)`, `Case2Pre.N_F`); both have order `3`, and `B₀` has odd order, so a finite
  odd-order group acting by conjugation on a group of order `3` acts trivially: the conjugation
  map into `MulAut ↥K` has image of order dividing `|B₀|` and dividing
  `Nat.card (MulAut ↥K) = Nat.totient 3 = 2` (Mathlib `IsCyclic.card_mulAut`,
  `isCyclic_of_prime_card`), hence trivial.  So `B₀ ≤ B.U ⊓ centralizer (D.K0 ⊔ D.F)`, whose
  prime set is `B.piFU = {3}` (`Case2SevenFacts` conjunct 3).
* `N := (B₀ ⊔ K) ⊔ F(U) = (U ⊓ M) ⊔ F(U)` satisfies `N.relIndex B.U ≤ 3` by `Case2EightAll`
  at `p = 3`, `P = F` (the eighth conjunct of `Case2EightFacts` is
  `(D.B0 ⊔ D.K ⊔ fittingIn B.U).relIndex B.U ≤ p`), and `N` is a `3`-group: `B₀ ⊔ K` by
  `IsPGroup.to_sup_of_normal_right'` (`B₀ ≤ N_G(K)`), then join with `F(U) ⊴ U`.
* `|U| = N.relIndex B.U * |N|` (`Subgroup.relIndex_mul_card`), `|N| = 3^a`, and the index divides
  `|U|` (odd) while being `≤ 3`, so it is `1` or `3`; hence `|U| ∣ 3^(a+1)` and
  `IsPGroup.of_card_dvd_pow` finishes. -/
theorem A3UU3 (I : Work.GW2.C4Inputs) : ∀ (G : Type) [Group G] [Finite G]
    (B : Work.GW2.BenderSetup G) (C : Work.GW2.Case2Ctx6 B),
    Work.GW2.Hyp9 G B C → Work.GW2.A7Facts1 C.D → IsPGroup 3 B.U := by
  intro G _ _ B C hHyp hf1
  obtain ⟨hbc, hcase2, hplus, hseven, height⟩ := hHyp
  obtain ⟨hKcard, hFcard, hK0eq, hpiFU⟩ := hf1
  have hpre : Work.GW2.Case2Pre B C.D := C.pre
  -- ## 1. `F(U)` is a `3`-group: `π(F(U)) = B.piFU = {3}`.
  have hFU : IsPGroup 3 (Work.GW2.fittingIn B.U) := by
    have hpf : (Nat.card ↥(Work.GW2.fittingIn B.U)).primeFactors = ({3} : Finset ℕ) := by
      have h1 : Work.GW2.primesOf (Work.GW2.fittingIn B.U) = {3} := hpiFU
      ext p
      exact (Set.ext_iff.mp h1 p).trans (Set.mem_singleton_iff.trans Finset.mem_singleton.symm)
    rw [isPGroup_iff_primeFactors_card_subset (by norm_num : (3 : ℕ) ≠ 0),
      show (3 : ℕ).primeFactors = {3} from
        (Nat.primeFactors_prime_pow (k := 1) (by norm_num) Nat.prime_three)]
    exact le_of_eq hpf
  -- ## 2. `K` is a `3`-group.
  have hK3 : IsPGroup 3 C.D.K := IsPGroup.of_card (n := 1) (by rw [hKcard, pow_one])
  -- ## 3. `B₀` normalizes `K` and `F` (both of order `3`) and has odd order, so it centralizes
  --        both of them; hence it lies in `U ⊓ C_U(K₀F)`, whose prime set is `{3}`.
  have hB0leU : C.D.B0 ≤ B.U := le_trans (C.D.B0_le B) inf_le_left
  have hB0odd : Odd (Nat.card ↥C.D.B0) :=
    Odd.of_dvd_nat B.U_odd (Subgroup.card_dvd_of_le hB0leU)
  have hB0normK : C.D.B0 ≤ Subgroup.normalizer ((C.D.K : Subgroup G) : Set G) :=
    le_trans (C.D.B0_le B)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (C.D.K_le B)).mp
        (Work.CORE4.Case2Data.K_normal_in_UinfM I B C.D))
  have hB0cK : C.D.B0 ≤ Subgroup.centralizer ((C.D.K : Subgroup G) : Set G) :=
    le_centralizer_of_le_normalizer_of_card_three hKcard hB0normK hB0odd
  have hB0normF : C.D.B0 ≤ Subgroup.normalizer ((C.D.F : Subgroup G) : Set G) := by
    rw [Work.GW2.Case2Pre.N_F B C.D hpre]
    exact le_trans (C.D.B0_le B) inf_le_right
  have hB0cF : C.D.B0 ≤ Subgroup.centralizer ((C.D.F : Subgroup G) : Set G) :=
    le_centralizer_of_le_normalizer_of_card_three hFcard hB0normF hB0odd
  have hB0cKF : C.D.B0 ≤
      Subgroup.centralizer (((C.D.K0 ⊔ C.D.F : Subgroup G)) : Set G) := by
    rw [hK0eq]
    exact Subgroup.le_centralizer_iff.mpr
      (sup_le (Subgroup.le_centralizer_iff.mp hB0cK) (Subgroup.le_centralizer_iff.mp hB0cF))
  have hB0leC : C.D.B0 ≤
      B.U ⊓ Subgroup.centralizer (((C.D.K0 ⊔ C.D.F : Subgroup G)) : Set G) :=
    le_inf hB0leU hB0cKF
  have hC3 : IsPGroup 3
      ↥(B.U ⊓ Subgroup.centralizer (((C.D.K0 ⊔ C.D.F : Subgroup G)) : Set G)) := by
    have hpf : (Nat.card ↥(B.U ⊓ Subgroup.centralizer
        (((C.D.K0 ⊔ C.D.F : Subgroup G)) : Set G))).primeFactors = ({3} : Finset ℕ) := by
      have h1 : Work.GW2.primesOf (B.U ⊓ Subgroup.centralizer
          (((C.D.K0 ⊔ C.D.F : Subgroup G)) : Set G)) = {3} := by
        rw [hseven.2.2.1, hpiFU]
      ext p
      exact (Set.ext_iff.mp h1 p).trans (Set.mem_singleton_iff.trans Finset.mem_singleton.symm)
    rw [isPGroup_iff_primeFactors_card_subset (by norm_num : (3 : ℕ) ≠ 0),
      show (3 : ℕ).primeFactors = {3} from
        (Nat.primeFactors_prime_pow (k := 1) (by norm_num) Nat.prime_three)]
    exact le_of_eq hpf
  have hB03 : IsPGroup 3 C.D.B0 := hC3.to_le hB0leC
  -- ## 4. `N := (B₀ ⊔ K) ⊔ F(U)` is a `3`-group of index `≤ 3` in `U`.
  have hB0K3 : IsPGroup 3 ↥(C.D.B0 ⊔ C.D.K) :=
    IsPGroup.to_sup_of_normal_right' hB03 hK3 hB0normK
  have hFUleU : Work.GW2.fittingIn B.U ≤ B.U := Subgroup.map_subtype_le _
  have hB0KleU : C.D.B0 ⊔ C.D.K ≤ B.U := sup_le hB0leU (C.D.K_le_U B)
  have hNleU : C.D.B0 ⊔ C.D.K ⊔ Work.GW2.fittingIn B.U ≤ B.U :=
    sup_le hB0KleU hFUleU
  have hNnorm : C.D.B0 ⊔ C.D.K ≤
      Subgroup.normalizer ((Work.GW2.fittingIn B.U : Subgroup G) : Set G) :=
    le_trans hB0KleU
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hFUleU).mp
        (Work.CORE4.fittingIn_subgroupOf_normal B.U))
  have hN3 : IsPGroup 3 ↥(C.D.B0 ⊔ C.D.K ⊔ Work.GW2.fittingIn B.U) :=
    IsPGroup.to_sup_of_normal_right' hB0K3 hFU hNnorm
  obtain ⟨A, _hObjA, hFactsA⟩ := height 3 C.D.F Nat.prime_three le_rfl hFcard
  have hIdx : (C.D.B0 ⊔ C.D.K ⊔ Work.GW2.fittingIn B.U).relIndex B.U ≤ 3 :=
    hFactsA.2.2.2.2.2.2.2.2.1
  -- ## 5. `|U| = N.relIndex B.U * |N|`, `|N| = 3^a`, `N.relIndex B.U ∈ {1, 3}`.
  have hcard_rel : (C.D.B0 ⊔ C.D.K ⊔ Work.GW2.fittingIn B.U).relIndex B.U *
      Nat.card ↥(C.D.B0 ⊔ C.D.K ⊔ Work.GW2.fittingIn B.U) = Nat.card ↥B.U := by
    have h := Subgroup.relIndex_mul_card (C.D.B0 ⊔ C.D.K ⊔ Work.GW2.fittingIn B.U) B.U
    rwa [inf_of_le_left hNleU] at h
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 3)
    (G := ↥(C.D.B0 ⊔ C.D.K ⊔ Work.GW2.fittingIn B.U))).mp hN3
  have hUcard : Nat.card ↥B.U =
      (C.D.B0 ⊔ C.D.K ⊔ Work.GW2.fittingIn B.U).relIndex B.U * 3 ^ a := by
    rw [← hcard_rel, ha]
  have hrelodd : Odd ((C.D.B0 ⊔ C.D.K ⊔ Work.GW2.fittingIn B.U).relIndex B.U) := by
    refine Odd.of_dvd_nat B.U_odd ?_
    rw [← hcard_rel]
    exact dvd_mul_right _ _
  obtain ⟨k, hk⟩ := hrelodd
  have hcases : (C.D.B0 ⊔ C.D.K ⊔ Work.GW2.fittingIn B.U).relIndex B.U = 1 ∨
      (C.D.B0 ⊔ C.D.K ⊔ Work.GW2.fittingIn B.U).relIndex B.U = 3 := by omega
  rcases hcases with h1 | h3
  · exact IsPGroup.of_card (n := a) (by rw [hUcard, h1, one_mul])
  · exact IsPGroup.of_card (n := a + 1)
      (by rw [hUcard, h3, pow_succ]; exact Nat.mul_comm 3 (3 ^ a))

end Work.CORE4.NotA7
