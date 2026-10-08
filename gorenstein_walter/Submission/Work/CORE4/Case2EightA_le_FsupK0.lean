import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2EightObjExists

namespace Work.CORE4

open Subgroup

/-! ## Two elementary group-theoretic ingredients

* `omegaPrime_le_of_card_dvd`: if `K₀ ≤ K`, `p ∣ |K₀|` and `Kp ≤ K` is the `p`-torsion of `K`
  (elements of `K` of order dividing `p`, of order exactly `p`), then `Kp ≤ K₀` — `K₀` contains an
  element of order `p` (Cauchy), and `Kp`, of prime order `p`, has no proper nontrivial subgroups.
* `prime_dvd_card_K0_c4`: `p ∣ |K₀|` from §4 (7) — if `p ∣ |F|` then `p ∈ π(F(U)) = π(K₀)`,
  since `F ≤ F(U)`. -/

/-- The `p`-torsion `Kp` of a group `K` of order `p` lies in every subgroup `K₀ ≤ K` of order
divisible by `p`. -/
theorem omegaPrime_le_of_card_dvd {G : Type} [Group G] [Finite G]
    {K K0 Kp : Subgroup G} {p : ℕ} (hp : p.Prime) (hK0 : K0 ≤ K)
    (hpK0 : p ∣ Nat.card ↥K0) (hKp_card : Nat.card ↥Kp = p)
    (hKp_omega : ∀ x ∈ K, x ^ p = 1 ↔ x ∈ Kp) : Kp ≤ K0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype ↥K0 := Fintype.ofFinite _
  -- Cauchy in `K₀`: an element of order `p`
  obtain ⟨y, hyK0, hyord⟩ : ∃ y ∈ K0, orderOf y = p := by
    have hdvd' : p ∣ Fintype.card ↥K0 := by rw [← Nat.card_eq_fintype_card]; exact hpK0
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card p hdvd'
    exact ⟨(y : G), y.2, by rw [Subgroup.orderOf_coe]; exact hy⟩
  have hyK : y ∈ K := hK0 hyK0
  have hyp : y ^ p = 1 := by rw [← hyord]; exact orderOf_dvd_iff_pow_eq_one.mp dvd_rfl
  have hyKp : y ∈ Kp := (hKp_omega y hyK).mp hyp
  -- `⟨y⟩ ≤ Kp ⊓ K₀` has order `p`, so `Kp ⊓ K₀ = Kp` has order `p`
  have hzy : Subgroup.zpowers y ≤ Kp ⊓ K0 :=
    le_inf (Subgroup.zpowers_le.mpr hyKp) (Subgroup.zpowers_le.mpr hyK0)
  have hcard_y : Nat.card ↥(Subgroup.zpowers y) = p := by
    rw [Nat.card_zpowers]; exact hyord
  have hge : p ≤ Nat.card ↥(Kp ⊓ K0) := by
    rw [← hcard_y]
    exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hzy)
  have hle : Nat.card ↥(Kp ⊓ K0) ≤ p := by
    have h := Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le (inf_le_left : Kp ⊓ K0 ≤ Kp))
    rwa [hKp_card] at h
  have hcard_inf : Nat.card ↥(Kp ⊓ K0) = p := le_antisymm hle hge
  have heq : Kp ⊓ K0 = Kp :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcard_inf, hKp_card])
  intro x hx
  exact (Subgroup.mem_inf.mp (heq ▸ hx)).2

/-- `p ∣ |K₀|` from Bender §4 (7): `p ∣ |F|` with `F ≤ F(U)` gives `p ∈ π(F(U)) = π(K₀)`
(second conjunct of `Case2SevenFacts`). -/
theorem prime_dvd_card_K0_c4 {G : Type} [Group G] [Finite G]
    (B : Work.GW2.BenderSetup G) (D : Work.GW2.Case2Data B)
    (h7 : Work.GW2.Case2SevenFacts B D) {p : ℕ} (hp : p.Prime)
    (hpF : p ∣ Nat.card ↥D.F) : p ∣ Nat.card ↥D.K0 := by
  have hpFU : p ∣ Nat.card ↥(Work.GW2.fittingIn B.U) :=
    hpF.trans (Subgroup.card_dvd_of_le (Work.GW2.Case2Data.F_le_fitting B D))
  have hpPiFU : p ∈ B.piFU := by
    refine Nat.mem_primeFactors.mpr ⟨hp, hpFU, ?_⟩
    exact Nat.card_ne_zero.mpr ⟨⟨1, (Work.GW2.fittingIn B.U).one_mem⟩, inferInstance⟩
  have hpK0mem : p ∈ Work.GW2.primesOf D.K0 := h7.2.1.symm ▸ hpPiFU
  exact (Nat.mem_primeFactors.mp hpK0mem).2.1

/-- Bender 1981, §4 (8): the `(p,p)`-subgroup `A` of `F ⊔ K` of §4(8) actually lies in
`F ⊔ K₀`, `K₀ = F(U) ⊓ K` (the `p`-torsion of `K` is contained in `K₀` because `p ∣ |K₀|` and
`K` is cyclic). -/
theorem Case2EightA_le_FsupK0 (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G → ∀ B : Work.GW2.BenderSetup G,
      Work.GW2.Case2 B → ∀ C : Work.GW2.Case2Ctx6 B, Work.GW2.Case2PrePlus B C.D →
        Work.GW2.Case2SevenFacts B C.D →
        ∀ (p : ℕ) (P A : Subgroup G), p.Prime → P ≤ C.D.F → Nat.card P = p →
          Work.GW2.Case2EightObj C.D p P A → A ≤ C.D.F ⊔ C.D.K0 := by
  intro G _ _ _ B _ C _ h7 p P A hp hPF hPcard hObj
  obtain ⟨_, _, _, hAle, hAcard, hAexp, _, hAuniq⟩ := hObj
  -- `p ∣ |F|`, then `p ∣ |K|` (whose `p`-torsion we need) and `p ∣ |K₀|`
  have hpF : p ∣ Nat.card ↥C.D.F := by
    rw [← hPcard]; exact Subgroup.card_dvd_of_le hPF
  have hpK : p ∣ Nat.card ↥C.D.K := prime_dvd_card_K_c4 B C.D h7 hp hpF
  have hpK0 : p ∣ Nat.card ↥C.D.K0 := prime_dvd_card_K0_c4 B C.D h7 hp hpF
  -- the `p`-torsion subgroups of `K` and of `F` (cyclic, so unique of order `p`)
  obtain ⟨Kp, hKp_le, hKp_card, hKp_omega⟩ :=
    CyclicOmegaPrime C.D.K p C.pre.K_cyclic hp hpK
  obtain ⟨Fp, hFp_le, hFp_card, hFp_omega⟩ :=
    CyclicOmegaPrime C.D.F p C.F_cyclic hp hpF
  have hP_le_Fp : P ≤ Fp := fun x hx =>
    (hFp_omega x (hPF hx)).mp (pow_eq_one_of_card_eq hPcard hx)
  have hPFp : P = Fp :=
    Subgroup.eq_of_le_of_card_ge hP_le_Fp (by rw [hFp_card, hPcard])
  have hP_omega : ∀ x ∈ C.D.F, x ^ p = 1 ↔ x ∈ P := by
    intro x hx
    rw [hPFp]
    exact hFp_omega x hx
  -- `P ⊔ Kp` is the *unique* subgroup of `F ⊔ K` of order `p ^ 2` and exponent `p`
  obtain ⟨-, hPK_le, hPK_card, hPK_exp, huniq⟩ :=
    Case2EightPpSupUnique C.D.F C.D.K P Kp p (F_inf_K_eq_bot_c4 B C.D)
      (F_le_normalizer_K_c4 I B C.D) (F_commute_K_c4 I B C.D C.pre)
      hPF hKp_le hP_omega hKp_omega hPcard hKp_card
  have hAeq : A = P ⊔ Kp := huniq A hAle hAcard hAexp
  -- `Kp ≤ K₀`: the `p`-torsion of `K` is the unique subgroup of `K` of order `p`, and `p ∣ |K₀|`
  have hKp_K0 : Kp ≤ C.D.K0 :=
    omegaPrime_le_of_card_dvd hp inf_le_right hpK0 hKp_card hKp_omega
  rw [hAeq]
  exact sup_le (le_trans hPF le_sup_left) (le_trans hKp_K0 le_sup_right)

end Work.CORE4
