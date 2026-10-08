import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2SevenAux

namespace Work.CORE4

open Subgroup

variable {G : Type} [Group G] [Finite G]

/-! ## Structural facts about the §4 objects `F` and `K`

Bender, p. 225: `F = B₀ ⊓ F(U)` and `K = I_{U⊓M}(s)` are cyclic, `K ⊴ U ⊓ M` (1.5(iii)) and
`F ⊴ M` (from `N_G(F) = M`, §4 (5)); an element of `F ⊓ K` is centralized *and* inverted by `s`,
hence of order dividing `2`, while `K ≤ U` has odd order, so `F ⊓ K = 1` and the two subgroups
commute.  Consequently `F ⊔ K ≅ F × K` and `P ⊔ Kp` (for the `p`-torsion subgroups `P ≤ F`,
`Kp ≤ K`) is the subgroup of type `(p,p)` of Bender's (8). -/

/-- `M ≤ N_G(F)`, directly from `N_G(F) = M` (`§4 (5)`). -/
theorem M_le_normalizer_F_c4 (B : Work.GW2.BenderSetup G) (D : Work.GW2.Case2Data B)
    (hpre : Work.GW2.Case2Pre B D) : D.M ≤ Subgroup.normalizer (D.F : Set G) := by
  rw [Work.GW2.Case2Pre.N_F B D hpre]

/-- `M` normalizes `F` elementwise. -/
theorem M_conj_mem_F_c4 (B : Work.GW2.BenderSetup G) (D : Work.GW2.Case2Data B)
    (hpre : Work.GW2.Case2Pre B D) : ∀ m ∈ D.M, ∀ f ∈ D.F, m * f * m⁻¹ ∈ D.F :=
  Subgroup.le_normalizer_iff.mp (M_le_normalizer_F_c4 B D hpre)

/-- `U ⊓ M` normalizes `K` elementwise (`K ⊴ U ⊓ M`, Bender 1.5(iii)). -/
theorem UinfM_conj_mem_K_c4 (I : Work.GW2.C4Inputs) (B : Work.GW2.BenderSetup G)
    (D : Work.GW2.Case2Data B) : ∀ x ∈ B.U ⊓ D.M, ∀ k ∈ D.K, x * k * x⁻¹ ∈ D.K :=
  fun x hx k hk =>
    (Subgroup.normal_subgroupOf_iff (Work.GW2.Case2Data.K_le B D)).mp
      (Case2Data.K_normal_in_UinfM I B D) k x hk hx

/-- `F ≤ N_G(K)`. -/
theorem F_le_normalizer_K_c4 (I : Work.GW2.C4Inputs) (B : Work.GW2.BenderSetup G)
    (D : Work.GW2.Case2Data B) : D.F ≤ Subgroup.normalizer (D.K : Set G) :=
  Subgroup.le_normalizer_iff.mpr fun x hf k hk =>
    UinfM_conj_mem_K_c4 I B D x (Work.GW2.Case2Data.F_le_UinfM B D hf) k hk

/-- `F ⊓ K = ⊥`: an element of `F` is centralized by `s` (`F ≤ B₀ = C_{U⊓M}(s)`) and an element
of `K = I_{U⊓M}(s)` is inverted by `s`, so it has order dividing `2`; but `K ≤ U` has odd order. -/
theorem F_inf_K_eq_bot_c4 (B : Work.GW2.BenderSetup G) (D : Work.GW2.Case2Data B) :
    D.F ⊓ D.K = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hxF, hxK⟩ := Subgroup.mem_inf.mp hx
  have hcent : D.s * x * D.s⁻¹ = x := by
    have hxB0 : x ∈ D.B0 := Work.GW2.Case2Data.F_le_B0 B D hxF
    rw [D.B0_def] at hxB0
    have hc := (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hxB0).2) D.s (by simp)
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  have hinv : D.s * x * D.s⁻¹ = x⁻¹ :=
    (show x ∈ Work.GW2.invSet (B.U ⊓ D.M) D.s from by rw [← D.K_def]; exact hxK).2
  have hxeq : x = x⁻¹ := hcent.symm.trans hinv
  have hsq : x * x = 1 := by
    have h := congrArg (fun t => t * x) hxeq
    rw [inv_mul_cancel] at h
    exact h
  have hdvd2 : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hsq)
  have hodd : Odd (orderOf x) :=
    Odd.of_dvd_nat B.U_odd
      (Subgroup.orderOf_dvd_natCard B.U (Work.GW2.Case2Data.K_le_U B D hxK))
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
  · exact orderOf_eq_one_iff.mp h
  · exact absurd (h ▸ (even_iff_two_dvd.mpr dvd_rfl)) (Nat.not_even_iff_odd.mpr hodd)

/-- `F` and `K` commute elementwise. -/
theorem F_commute_K_c4 (I : Work.GW2.C4Inputs) (B : Work.GW2.BenderSetup G)
    (D : Work.GW2.Case2Data B) (hpre : Work.GW2.Case2Pre B D) :
    ∀ f ∈ D.F, ∀ k ∈ D.K, f * k = k * f := by
  intro f hf k hk
  have h1 : f * k * f⁻¹ ∈ D.K :=
    UinfM_conj_mem_K_c4 I B D f (Work.GW2.Case2Data.F_le_UinfM B D hf) k hk
  have h2 : k * f * k⁻¹ ∈ D.F :=
    M_conj_mem_F_c4 B D hpre k (Work.GW2.Case2Data.K_le_M B D hk) f hf
  have hcK : f * k * f⁻¹ * k⁻¹ ∈ D.K := D.K.mul_mem h1 (D.K.inv_mem hk)
  have hcF : f * k * f⁻¹ * k⁻¹ ∈ D.F := by
    have h2' : (k * f * k⁻¹)⁻¹ ∈ D.F := D.F.inv_mem h2
    have h2'' : k * f⁻¹ * k⁻¹ ∈ D.F := by
      simpa only [mul_inv_rev, inv_inv, mul_assoc] using h2'
    simpa only [mul_assoc] using D.F.mul_mem hf h2''
  have hcone : f * k * f⁻¹ * k⁻¹ = 1 := by
    have hb : f * k * f⁻¹ * k⁻¹ ∈ (⊥ : Subgroup G) := by
      rw [← F_inf_K_eq_bot_c4 B D]
      exact Subgroup.mem_inf.mpr ⟨hcF, hcK⟩
    exact Subgroup.mem_bot.mp hb
  have h3 : f * k * f⁻¹ = k := by
    have h := eq_inv_of_mul_eq_one_right hcone
    exact (inv_inj.mp h).symm
  have := congrArg (· * f) h3
  simpa [mul_assoc] using this

/-- `p ∣ |K|`: `p ∣ |F|` (as `P ≤ F` has order `p`), `F ≤ F(U)` and `π(F(U)) = π(K₀)` (Bender §4
(7)), so `p ∣ |K₀|`, hence `p ∣ |K|`. -/
theorem prime_dvd_card_K_c4 (B : Work.GW2.BenderSetup G) (D : Work.GW2.Case2Data B)
    (h7 : Work.GW2.Case2SevenFacts B D) {p : ℕ} (hp : p.Prime)
    (hpF : p ∣ Nat.card ↥D.F) : p ∣ Nat.card ↥D.K := by
  have hpFU : p ∣ Nat.card ↥(Work.GW2.fittingIn B.U) :=
    hpF.trans (Subgroup.card_dvd_of_le (Work.GW2.Case2Data.F_le_fitting B D))
  have hpPiFU : p ∈ B.piFU := by
    refine Nat.mem_primeFactors.mpr ⟨hp, hpFU, ?_⟩
    exact Nat.card_ne_zero.mpr ⟨⟨1, (Work.GW2.fittingIn B.U).one_mem⟩, inferInstance⟩
  have hpK0 : p ∈ Work.GW2.primesOf D.K0 := h7.2.1.symm ▸ hpPiFU
  exact (Nat.mem_primeFactors.mp hpK0).2.1.trans
    (Subgroup.card_dvd_of_le (inf_le_right : Work.GW2.fittingIn B.U ⊓ D.K ≤ D.K))

/-! ## Two abstract lemmas about a direct product of cyclic subgroups -/

/-- An element of a subgroup of order `p` has `p`-th power `1`. -/
theorem pow_eq_one_of_card_eq {p : ℕ} {P : Subgroup G} (hcard : Nat.card ↥P = p) {x : G}
    (hx : x ∈ P) : x ^ p = 1 := by
  have h : orderOf x ∣ p := by
    rw [← hcard]
    exact Subgroup.orderOf_dvd_natCard P hx
  exact orderOf_dvd_iff_pow_eq_one.mp h

/-- If `P` and `Kp` meet trivially and `P ≤ N_G(Kp)`, then `P ⊔ Kp` has `|P| · |Kp|` elements
(every element of `P ⊔ Kp` is a product of an element of `P` and one of `Kp`). -/
theorem card_sup_of_disjoint_normalizer {P Kp : Subgroup G}
    (hdisj : P ⊓ Kp = ⊥) (hN : P ≤ Subgroup.normalizer (Kp : Set G)) :
    Nat.card ↥(P ⊔ Kp) = Nat.card ↥P * Nat.card ↥Kp := by
  rw [← Nat.card_prod]
  refine Nat.card_congr (Equiv.ofBijective (fun z : ↥P × ↥Kp =>
    (⟨(z.1 : G) * z.2, Subgroup.mul_mem_sup z.1.2 z.2.2⟩ : ↥(P ⊔ Kp))) ⟨?_, ?_⟩).symm
  · intro z w h
    have hzw : (z.1 : G) * z.2 = (w.1 : G) * w.2 := congrArg Subtype.val h
    have hmem : (z.2 : G) * (w.2 : G)⁻¹ = (z.1 : G)⁻¹ * w.1 := by
      have h' : (z.2 : G) = (z.1 : G)⁻¹ * ((w.1 : G) * w.2) := by
        have h'' := congrArg (fun t => (z.1 : G)⁻¹ * t) hzw
        simpa [mul_assoc] using h''
      rw [h']
      simp [mul_assoc]
    have hP : (z.1 : G)⁻¹ * w.1 ∈ P := P.mul_mem (P.inv_mem z.1.2) w.1.2
    have hKp : (z.1 : G)⁻¹ * w.1 ∈ Kp := by
      rw [← hmem]
      exact Kp.mul_mem z.2.2 (Kp.inv_mem w.2.2)
    have hone : (z.1 : G)⁻¹ * w.1 = 1 := by
      have hb : (z.1 : G)⁻¹ * w.1 ∈ (⊥ : Subgroup G) := by
        rw [← hdisj]
        exact Subgroup.mem_inf.mpr ⟨hP, hKp⟩
      exact Subgroup.mem_bot.mp hb
    have h1 : (z.1 : G) = (w.1 : G) := by
      have h := congrArg (fun t : G => (z.1 : G) * t) hone
      simpa using h.symm
    have h2 : (z.2 : G) = (w.2 : G) := by
      refine mul_left_cancel (a := (z.1 : G)) ?_
      rw [hzw, h1]
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  · intro w
    have hw : (w : G) ∈ (↑(P ⊔ Kp) : Set G) := w.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right P Kp hN] at hw
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hw
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩

/-- **Abstract object half of §4 (8).**  If `F, K ≤ G` meet trivially, `F` normalizes `K` and all
elements of `F` and `K` commute, and if `P ≤ F` and `Kp ≤ K` are the sets of elements of order
dividing the prime `p` (so `P` and `Kp` are the `p`-torsion subgroups of `F` resp. `K`) of order
`p`, then `P ⊔ Kp` is the unique subgroup of `F ⊔ K` of order `p ^ 2` and exponent `p`, and it
contains `P`. -/
theorem Case2EightPpSupUnique (F K P Kp : Subgroup G) (p : ℕ)
    (hdisj : F ⊓ K = ⊥) (hleN : F ≤ Subgroup.normalizer (K : Set G))
    (hcomm : ∀ f ∈ F, ∀ k ∈ K, f * k = k * f)
    (hP_le : P ≤ F) (hKp_le : Kp ≤ K)
    (hP_omega : ∀ x ∈ F, x ^ p = 1 ↔ x ∈ P)
    (hKp_omega : ∀ x ∈ K, x ^ p = 1 ↔ x ∈ Kp)
    (hP_card : Nat.card ↥P = p) (hKp_card : Nat.card ↥Kp = p) :
    P ≤ P ⊔ Kp ∧ P ⊔ Kp ≤ F ⊔ K ∧ Nat.card ↥(P ⊔ Kp) = p ^ 2 ∧
      (∀ x ∈ P ⊔ Kp, x ^ p = 1) ∧
      ∀ A' : Subgroup G, A' ≤ F ⊔ K → Nat.card ↥A' = p ^ 2 →
        (∀ x ∈ A', x ^ p = 1) → A' = P ⊔ Kp := by
  have hPKdisj : P ⊓ Kp = ⊥ := by
    have h := inf_le_inf hP_le hKp_le
    rw [hdisj] at h
    exact le_bot_iff.mp h
  -- `P` normalizes `Kp`
  have hPNKp : P ≤ Subgroup.normalizer (Kp : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro x hx y hy
    have hxyK : x * y * x⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hleN (hP_le hx)) y).mp (hKp_le hy)
    have hpow : (x * y * x⁻¹) ^ p = 1 := by
      have hpoweq : (x * y * x⁻¹) ^ p = x * y ^ p * x⁻¹ := by
        have h := map_pow (MulAut.conj x) y p
        rw [MulAut.conj_apply, MulAut.conj_apply] at h
        exact h.symm
      rw [hpoweq, (hKp_omega y (hKp_le hy)).mpr hy, mul_one, mul_inv_cancel]
    exact (hKp_omega (x * y * x⁻¹) hxyK).mp hpow
  -- every element of `P ⊔ Kp` is a product `x * y` with `x ∈ P`, `y ∈ Kp`
  have hdecompPK : ∀ z ∈ P ⊔ Kp, ∃ x ∈ P, ∃ y ∈ Kp, x * y = z := by
    intro z hz
    have hz' : z ∈ (↑(P ⊔ Kp) : Set G) := hz
    rw [Subgroup.coe_mul_of_left_le_normalizer_right P Kp hPNKp] at hz'
    exact Set.mem_mul.mp hz'
  have hcard : Nat.card ↥(P ⊔ Kp) = p ^ 2 := by
    rw [card_sup_of_disjoint_normalizer hPKdisj hPNKp, hP_card, hKp_card, pow_two]
  refine ⟨le_sup_left, sup_le (le_trans hP_le le_sup_left) (le_trans hKp_le le_sup_right),
    hcard, ?_, ?_⟩
  · intro z hz
    obtain ⟨x, hxP, y, hyKp, rfl⟩ := hdecompPK z hz
    have hxp : x ^ p = 1 := (hP_omega x (hP_le hxP)).mpr hxP
    have hyp : y ^ p = 1 := (hKp_omega y (hKp_le hyKp)).mpr hyKp
    have hc : Commute x y := hcomm x (hP_le hxP) y (hKp_le hyKp)
    rw [hc.mul_pow, hxp, hyp, one_mul]
  · intro A' hA'le hA'card hA'exp
    have hsub : A' ≤ P ⊔ Kp := by
      intro z hz
      have hz' : z ∈ (↑(F ⊔ K) : Set G) := hA'le hz
      rw [Subgroup.coe_mul_of_left_le_normalizer_right F K hleN] at hz'
      obtain ⟨f, hf, k, hk, hfk⟩ := Set.mem_mul.mp hz'
      have hzA : f * k ∈ A' := by rw [hfk]; exact hz
      have hzp : (f * k) ^ p = 1 := hA'exp _ hzA
      have hc : Commute f k := hcomm f hf k hk
      rw [hc.mul_pow] at hzp
      have hfp : f ^ p = 1 := by
        have hmem : f ^ p ∈ F ⊓ K := by
          refine Subgroup.mem_inf.mpr ⟨F.pow_mem hf p, ?_⟩
          rw [eq_inv_of_mul_eq_one_left hzp]
          exact K.inv_mem (K.pow_mem hk p)
        have hb : f ^ p ∈ (⊥ : Subgroup G) := by rw [← hdisj]; exact hmem
        exact Subgroup.mem_bot.mp hb
      have hkp : k ^ p = 1 := by
        have hmem : k ^ p ∈ F ⊓ K := by
          refine Subgroup.mem_inf.mpr ⟨?_, K.pow_mem hk p⟩
          rw [eq_inv_of_mul_eq_one_right hzp]
          exact F.inv_mem (F.pow_mem hf p)
        have hb : k ^ p ∈ (⊥ : Subgroup G) := by rw [← hdisj]; exact hmem
        exact Subgroup.mem_bot.mp hb
      rw [← hfk]
      exact Subgroup.mul_mem_sup ((hP_omega f hf).mp hfp) ((hKp_omega k hk).mp hkp)
    exact Subgroup.eq_of_le_of_card_ge hsub (by rw [hcard, hA'card])

/-- **The `p`-torsion of a cyclic subgroup.**  A cyclic subgroup `K ≤ G` whose order is divisible
by the prime `p` has a subgroup of order `p`, consisting exactly of its elements of order dividing
`p`: if `K` is generated by `g` and `d = |K| / p`, it is `⟨g ^ d⟩`. -/
theorem CyclicOmegaPrime (K : Subgroup G) (p : ℕ) (hK : IsCyclic ↥K) (hp : p.Prime)
    (hdvd : p ∣ Nat.card ↥K) :
    ∃ Kp : Subgroup G, Kp ≤ K ∧ Nat.card ↥Kp = p ∧ ∀ x ∈ K, x ^ p = 1 ↔ x ∈ Kp := by
  obtain ⟨g, hg⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top K).mp hK
  have hord : orderOf g = Nat.card ↥K := by rw [← Nat.card_zpowers, hg]
  have hnpos : 0 < Nat.card ↥K := Nat.card_pos
  set d : ℕ := Nat.card ↥K / p with hddef
  have hd : Nat.card ↥K = d * p := (Nat.div_mul_cancel hdvd).symm
  have hdpos : 0 < d := Nat.div_pos (Nat.le_of_dvd hnpos hdvd) hp.pos
  have hdvd_d : d ∣ Nat.card ↥K := ⟨p, hd⟩
  have hcard : Nat.card ↥(Subgroup.zpowers (g ^ d)) = p := by
    rw [Nat.card_zpowers, orderOf_pow, hord, hd, Nat.gcd_eq_right (dvd_mul_right d p),
      Nat.mul_div_cancel_left p hdpos]
  refine ⟨Subgroup.zpowers (g ^ d), ?_, hcard, ?_⟩
  · rw [Subgroup.zpowers_le, ← hg]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers g) d
  · intro x hxK
    constructor
    · intro hxp
      have hx' : x ∈ Subgroup.zpowers g := by rw [hg]; exact hxK
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx'
      set gc : ℕ := Nat.gcd (Nat.card ↥K) k.natAbs with hgc
      have hordx : orderOf x = Nat.card ↥K / gc := by
        rw [← hk, orderOf_zpow, hord]
      have hdiv : Nat.card ↥K / gc ∣ p := by
        rw [← hordx]
        exact orderOf_dvd_iff_pow_eq_one.mpr hxp
      have hdgcd : d ∣ gc := by
        have hgc_dvd : gc ∣ Nat.card ↥K := Nat.gcd_dvd_left _ _
        have hdm : Nat.card ↥K / gc * gc = Nat.card ↥K := Nat.div_mul_cancel hgc_dvd
        rcases (Nat.dvd_prime hp).mp hdiv with h1 | h1
        · have h2 : Nat.card ↥K = gc := by
            rw [h1, one_mul] at hdm
            exact hdm.symm
          rw [← h2]
          exact hdvd_d
        · have h3 : p * gc = p * d := by
            rw [h1] at hdm
            rw [hdm, hd]
            exact Nat.mul_comm d p
          have h4 : gc = d := Nat.mul_left_cancel hp.pos h3
          rw [h4]
      have hdk : (d : ℤ) ∣ k := by
        have h1 : d ∣ k.natAbs := hdgcd.trans (Nat.gcd_dvd_right _ _)
        have h2 : ((d : ℤ)).natAbs ∣ k.natAbs := by simpa using h1
        exact Int.natAbs_dvd_natAbs.mp h2
      have hle := Subgroup.zpowers_le_zpowers_of_dvd g (m := k) (n := (d : ℤ)) hdk
      have hx1 : x ∈ Subgroup.zpowers (g ^ k) := by
        rw [← hk]
        exact Subgroup.mem_zpowers (g ^ k)
      have h2 : x ∈ Subgroup.zpowers (g ^ (d : ℤ)) := hle hx1
      rwa [zpow_natCast] at h2
    · intro hxKp
      exact pow_eq_one_of_card_eq hcard hxKp

/-! ## The object half of Bender's §4 (8) -/

/-- Bender 1981, §4 (8), object half: for every prime `p` and every `P ≤ D.F` of order `p` there
is a subgroup `A ≤ D.F ⊔ D.K` of order `p ^ 2`, exponent `p`, containing `P`, and unique with
these properties in `D.F ⊔ D.K` (i.e. `Case2EightObj D p P A`). -/
theorem Case2EightObjExists (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G → ∀ B : Work.GW2.BenderSetup G,
      Work.GW2.Case2 B → ∀ C : Work.GW2.Case2Ctx6 B, Work.GW2.Case2PrePlus B C.D →
        Work.GW2.Case2SevenFacts B C.D →
        ∀ (p : ℕ) (P : Subgroup G), p.Prime → P ≤ C.D.F → Nat.card P = p →
          ∃ A : Subgroup G, Work.GW2.Case2EightObj C.D p P A := by
  intro G _ _ _ B _ C _ h7 p P hp hPle hPcard
  have hpF : p ∣ Nat.card ↥C.D.F := by
    rw [← hPcard]
    exact Subgroup.card_dvd_of_le hPle
  obtain ⟨Kp, hKp_le, hKp_card, hKp_omega⟩ :=
    CyclicOmegaPrime C.D.K p C.pre.K_cyclic hp (prime_dvd_card_K_c4 B C.D h7 hp hpF)
  obtain ⟨Fp, hFp_le, hFp_card, hFp_omega⟩ := CyclicOmegaPrime C.D.F p C.F_cyclic hp hpF
  have hP_le_Fp : P ≤ Fp := fun x hx =>
    (hFp_omega x (hPle hx)).mp (pow_eq_one_of_card_eq hPcard hx)
  have hPFp : P = Fp :=
    Subgroup.eq_of_le_of_card_ge hP_le_Fp (by rw [hFp_card, hPcard])
  have hP_omega : ∀ x ∈ C.D.F, x ^ p = 1 ↔ x ∈ P := by
    intro x hx
    rw [hPFp]
    exact hFp_omega x hx
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    Case2EightPpSupUnique C.D.F C.D.K P Kp p (F_inf_K_eq_bot_c4 B C.D)
      (F_le_normalizer_K_c4 I B C.D) (F_commute_K_c4 I B C.D C.pre)
      hPle hKp_le hP_omega hKp_omega hPcard hKp_card
  exact ⟨P ⊔ Kp, hp, hPle, hPcard, h2, h3, h4, h1, h5⟩

end Work.CORE4
