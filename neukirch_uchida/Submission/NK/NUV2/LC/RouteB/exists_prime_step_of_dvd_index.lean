import Mathlib
import Submission.NK.NUV2.LC.RouteB.Defs

set_option linter.style.haveILetI false

namespace NK.NUV2.LC.RouteB

/-- **The abstract Sylow step for finite groups.**  Let `Q` be a finite group, `p` a prime and
`P ≤ Q` a `p`-subgroup whose index in `Q` is divisible by `p`.  Then `P` is normal in a subgroup
`K` of `Q` with `[K : P] = p`.

Proof: write `|P| = p ^ n` (so `n` is the `p`-adic valuation of `|P|`).  Since
`|Q| = [Q : P] · p ^ n` and `p ∣ [Q : P]`, we have `p ^ (n+1) ∣ |Q|`, so
`Sylow.prime_pow_dvd_card_normalizer` gives `p ^ (n+1) ∣ |N_Q(P)|`; Sylow's first theorem inside
`N_Q(P)` produces `K ≤ N_Q(P)` with `|K| = p ^ (n+1)` and `P ≤ K`.  Then `P ◁ K` because
`K ≤ N_Q(P)`, and `[K : P] = p` by comparing cardinalities. -/
theorem exists_normal_supergroup_relIndex_prime {Q : Type*} [Group Q] [Finite Q] {p : ℕ}
    (hp : p.Prime) {P : Subgroup Q} (hP : IsPGroup p P) (hdvd : p ∣ P.index) :
    ∃ K : Subgroup Q, P ≤ K ∧ (P.subgroupOf K).Normal ∧ P.relIndex K = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hcardQ : p ^ (n + 1) ∣ Nat.card Q := by
    obtain ⟨m, hm⟩ := hdvd
    refine ⟨m, ?_⟩
    rw [pow_succ', ← Subgroup.index_mul_card P, hn, hm]
    ring
  have hN : p ^ (n + 1) ∣ Nat.card ↥(Subgroup.normalizer (P : Set Q)) :=
    Sylow.prime_pow_dvd_card_normalizer hcardQ hn
  let N : Subgroup Q := Subgroup.normalizer (P : Set Q)
  have hcardN : Nat.card ↥(P.subgroupOf N) = p ^ n := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer)).toEquiv, hn]
  obtain ⟨K', hK'card, hK'le⟩ :=
    Sylow.exists_subgroup_card_pow_succ (G := ↥N) (H := P.subgroupOf N) hN hcardN
  let K : Subgroup Q := K'.map N.subtype
  have hPK : P ≤ K := by
    calc P = (P.subgroupOf N).map N.subtype := by
            rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr Subgroup.le_normalizer]
      _ ≤ K'.map N.subtype := Subgroup.map_mono hK'le
  have hKN : K ≤ Subgroup.normalizer (P : Set Q) := Subgroup.map_subtype_le K'
  refine ⟨K, hPK, ?_, ?_⟩
  · rw [Subgroup.normal_subgroupOf_iff_le_normalizer hPK]; exact hKN
  · have hcardK : Nat.card ↥(P.subgroupOf K) = p ^ n := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPK).toEquiv, hn]
    have hcardK' : Nat.card ↥K = p ^ (n + 1) := by
      rw [← Nat.card_congr (Subgroup.equivMapOfInjective K' N.subtype N.subtype_injective).toEquiv,
        hK'card]
    rw [Subgroup.relIndex]
    have h := Subgroup.index_mul_card (P.subgroupOf K)
    rw [hcardK, hcardK', pow_succ'] at h
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos n) h

/-- **The finite Sylow step, in the Galois setting.**  Let `C ◁ O₁` be subgroups of `Gal(K'/K)`
with `C` of finite index in `O₁`, let `C ≤ O₂ ≤ O₁`, and let `p` be a prime dividing the index
`[O₁ : O₂]`.  Then there are subgroups `R₁, X` with

`C ≤ R₁ ≤ O₂`, `R₁ ≤ X ≤ O₁`, `R₁ ◁ X`, `[O₂ : R₁]` prime to `p`, and `[X : R₁] = p`.

(Classical argument: pass to the finite quotient `Q := O₁/C` and let `R ⊆ Q` be the image of
`O₂`, so `p ∣ [Q : R]`.  Let `P_R ∈ Syl_p(R)` and let `P ∈ Syl_p(Q)` be a Sylow containing `P_R`
(`IsPGroup.exists_le_sylow`); then `P_R ⊊ P`, so `P_R ⊊ N_P(P_R)` (normalizer condition for the
finite `p`-group `P`), and Cauchy in the finite group `N_P(P_R)/P_R` gives `P_R ◁ X̄ ≤ N_P(P_R)`
with `[X̄ : P_R] = p`.  Now take `R₁, X` to be the preimages in `O₁` of `P_R` and `X̄`.  Note
`[O₂ : R₁] = [R : P_R]` is prime to `p` because `P_R` is a Sylow subgroup of `R`, and `C ≤ R₁`
because `C` is the kernel of `O₁ ↠ Q`.) -/
theorem exists_prime_step_of_dvd_index (p : ℕ) (hp : p.Prime) {K K' : Type}
    [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    {O₁ O₂ C : Subgroup Gal(K'/K)} (hCO₂ : C ≤ O₂) (hO₂O₁ : O₂ ≤ O₁)
    (hCnormal : (C.subgroupOf O₁).Normal)
    (hCfin : (C.subgroupOf O₁).FiniteIndex)
    (hdiv : p ∣ (O₂.subgroupOf O₁).index) :
    ∃ R₁ X : Subgroup Gal(K'/K), C ≤ R₁ ∧ R₁ ≤ O₂ ∧ R₁ ≤ X ∧ X ≤ O₁ ∧
      (R₁.subgroupOf X).Normal ∧ Nat.Coprime (R₁.relIndex O₂) p ∧ R₁.relIndex X = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hCO₁ : C ≤ O₁ := le_trans hCO₂ hO₂O₁
  -- the finite quotient `Q = O₁ / C`
  let N : Subgroup ↥O₁ := C.subgroupOf O₁
  haveI hNnormal : N.Normal := hCnormal
  haveI hNfin : N.FiniteIndex := hCfin
  let φ : ↥O₁ →* (↥O₁ ⧸ N) := QuotientGroup.mk' N
  have hφker : φ.ker = N := QuotientGroup.ker_mk' N
  have hφsurj : Function.Surjective φ := QuotientGroup.mk'_surjective N
  -- the image `R` of `O₂` and a Sylow `p`-subgroup `P_R ≤ R`, pushed forward to `Q`
  let R : Subgroup (↥O₁ ⧸ N) := (O₂.subgroupOf O₁).map φ
  have hker_le : φ.ker ≤ O₂.subgroupOf O₁ := by
    rw [hφker]
    exact Subgroup.subgroupOf_mono O₁ hCO₂
  have hRindex : R.index = (O₂.subgroupOf O₁).index :=
    Subgroup.index_map_eq (O₂.subgroupOf O₁) hφsurj hker_le
  have hdvdR : p ∣ R.index := by rw [hRindex]; exact hdiv
  obtain ⟨S⟩ := Sylow.nonempty (p := p) (G := ↥R)
  let P_R : Subgroup (↥O₁ ⧸ N) := ((S : Subgroup ↥R)).map R.subtype
  have hPRp : IsPGroup p P_R := (S.isPGroup').map R.subtype
  have hPRle : P_R ≤ R := Subgroup.map_subtype_le _
  have hdvdPR : p ∣ P_R.index := by
    have h1 : R.index ∣ P_R.index :=
      ⟨P_R.relIndex R, by rw [mul_comm, Subgroup.relIndex_mul_index hPRle]⟩
    exact dvd_trans hdvdR h1
  obtain ⟨K, hPRK, hPRKnormal, hPRKindex⟩ :=
    exists_normal_supergroup_relIndex_prime hp hPRp hdvdPR
  -- `O₂` is the preimage of `R`
  have hRcomap : R.comap φ = O₂.subgroupOf O₁ := by
    rw [Subgroup.comap_map_eq, sup_eq_left, hφker]
    exact Subgroup.subgroupOf_mono O₁ hCO₂
  have hO₂eq : (R.comap φ).map O₁.subtype = O₂ := by
    rw [hRcomap, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hO₂O₁]
  have hCeq : (C.subgroupOf O₁).map O₁.subtype = C := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hCO₁]
  -- the preimages `R₁` and `X`
  have hR₁le : (P_R.comap φ).map O₁.subtype ≤ O₂ := by
    rw [← hO₂eq]
    exact Subgroup.map_mono (Subgroup.comap_mono hPRle)
  have hR₁X : (P_R.comap φ).map O₁.subtype ≤ (K.comap φ).map O₁.subtype :=
    Subgroup.map_mono (Subgroup.comap_mono hPRK)
  have hXle : (K.comap φ).map O₁.subtype ≤ O₁ := Subgroup.map_subtype_le _
  have hC_le_R₁ : C ≤ (P_R.comap φ).map O₁.subtype := by
    rw [← hCeq]
    refine Subgroup.map_mono ?_
    intro x hx
    rw [Subgroup.mem_comap]
    have hx1 : φ x = 1 := by
      rw [← MonoidHom.mem_ker, hφker]
      exact hx
    rw [hx1]
    exact P_R.one_mem
  have hnorm : ((P_R.comap φ).map O₁.subtype).subgroupOf
      ((K.comap φ).map O₁.subtype) |>.Normal := by
    rw [Subgroup.normal_subgroupOf_iff hR₁X]
    intro h k hh hk
    obtain ⟨wh, hwh, hwh_eq⟩ := Subgroup.mem_map.mp hh
    obtain ⟨wk, hwk, hwk_eq⟩ := Subgroup.mem_map.mp hk
    rw [Subgroup.mem_map]
    refine ⟨wk * wh * wk⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
      have hwkK : φ wk ∈ K := Subgroup.mem_comap.mp hwk
      have hwhP : φ wh ∈ P_R := Subgroup.mem_comap.mp hwh
      have hKn : K ≤ Subgroup.normalizer (P_R : Set _) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hPRK).mp hPRKnormal
      have hmem : φ wk ∈ Subgroup.normalizer (P_R : Set _) := hKn hwkK
      exact ((Subgroup.mem_normalizer_iff.mp hmem) (φ wh)).mp hwhP
    · rw [map_mul, map_mul, map_inv, hwh_eq, hwk_eq]
  have hmapR : Subgroup.map φ (R.comap φ) = R := by
    rw [Subgroup.map_comap_eq, MonoidHom.range_eq_top_of_surjective φ hφsurj, top_inf_eq]
  have hmapK : Subgroup.map φ (K.comap φ) = K := by
    rw [Subgroup.map_comap_eq, MonoidHom.range_eq_top_of_surjective φ hφsurj, top_inf_eq]
  have hrelPR : P_R.relIndex R = S.index := by
    have htop : Subgroup.map R.subtype ⊤ = R := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have h1 : P_R.relIndex (Subgroup.map R.subtype ⊤) =
        (S : Subgroup ↥R).relIndex ⊤ :=
      Subgroup.relIndex_map_map_of_injective (S : Subgroup ↥R) ⊤ R.subtype_injective
    rw [htop, Subgroup.relIndex_top_right] at h1
    exact h1
  have hcop : Nat.Coprime (((P_R.comap φ).map O₁.subtype).relIndex O₂) p := by
    rw [← hO₂eq, Subgroup.relIndex_map_map_of_injective _ _ O₁.subtype_injective,
      Subgroup.relIndex_comap, hmapR, hrelPR]
    exact (hp.coprime_iff_not_dvd.mpr S.not_dvd_index).symm
  have hidx : ((P_R.comap φ).map O₁.subtype).relIndex ((K.comap φ).map O₁.subtype) = p := by
    rw [Subgroup.relIndex_map_map_of_injective _ _ O₁.subtype_injective,
      Subgroup.relIndex_comap, hmapK, hPRKindex]
  exact ⟨_, _, hC_le_R₁, hR₁le, hR₁X, hXle, hnorm, hcop, hidx⟩

end NK.NUV2.LC.RouteB
