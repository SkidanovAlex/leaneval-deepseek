import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# A `p`-group acting faithfully on an elementary abelian group of order `≤ p ^ 2` has order `≤ p`

`Work.SmallRank.card_le_prime_of_pgroup_mulAut`: if `A` is a finite commutative group of exponent
dividing the prime `p` with `|A| ≤ p ^ 2`, then any finite `p`-group `G` acting faithfully on `A`
(through a homomorphism `φ : G →* MulAut A`) has `|G| ≤ p`.

This is the "`p`-part of `Aut A` is at most `p` when `|A| ≤ p ^ 2` and `A` is elementary abelian"
statement, in the form in which the FT 3.9 / Huppert III.12.4 argument consumes it (`Aut A` has no
subgroup of order `p ^ 2`).

## Proof

Fix the action of `G` on `A` induced by `φ` (a `MulDistribMulAction`), and let `V = A ^ G` be the
fixed point subgroup.  Write `|A| = p ^ n`, `n ≤ 2`.

* `V` is a subgroup and `|A| ≡ |V| (mod p)`, so (in the nontrivial case) `p ∣ |V|`.
* If `V = A` the action is trivial, so `φ g = 1` for every `g` and, `φ` being injective, `G` is
  trivial.
* Otherwise `V < A`, so `p ≤ |V| < |A| = p ^ n`, forcing `n = 2`, i.e. `|A| = p ^ 2`.  Pick
  `a₀ ∉ V`.  Then `⟨a₀⟩ · V` has order `> p` and divides `p ^ 2`, hence equals `A`; therefore any
  `g` fixing `a₀` fixes all of `A`, so `g = 1`.  The orbit map `g ↦ g • a₀` is thus injective into
  `A ∖ V`, giving `|G| ≤ |A ∖ V| < |A| = p ^ 2`; as `|G| = p ^ k` this forces `k ≤ 1`, i.e.
  `|G| ≤ p`.
-/

open scoped Classical

namespace Work.SmallRank

theorem card_le_prime_of_pgroup_mulAut {p : ℕ} (hp : p.Prime) {A : Type*} [CommGroup A] [Finite A]
    (hexp : ∀ a : A, a ^ p = 1) (hcard : Nat.card A ≤ p ^ 2)
    {G : Type*} [Group G] [Finite G] (hG : IsPGroup p G) (φ : G →* MulAut A)
    (hφ : Function.Injective φ) : Nat.card G ≤ p := by
  haveI : Fact p.Prime := ⟨hp⟩
  classical
  -- The action of `G` on `A`, induced by `φ`.
  letI : MulDistribMulAction G A := MulDistribMulAction.compHom A φ
  letI : MulAction G A := MulDistribMulAction.toMulAction
  have hsmul : ∀ (g : G) (a : A), g • a = φ g a := fun g a => rfl
  -- `A` is a `p`-group.
  have hApg : IsPGroup p A := fun a => ⟨1, by rw [pow_one]; exact hexp a⟩
  -- The fixed point subgroup.
  let V : Subgroup A :=
    { carrier := {a | ∀ g : G, g • a = a}
      one_mem' := by intro g; rw [smul_one]
      mul_mem' := by intro a b ha hb g; rw [smul_mul', ha g, hb g]
      inv_mem' := by intro a ha g; rw [smul_inv', ha g] }
  have hVmem : ∀ a : A, a ∈ V ↔ ∀ g : G, g • a = a := fun a => Iff.rfl
  have hVsub : (V : Set A) = MulAction.fixedPoints G A := by ext a; exact hVmem a
  have hVcard : Nat.card V = Nat.card (MulAction.fixedPoints G A) :=
    congrArg (fun s : Set A => Nat.card s) hVsub
  have hcongr : Nat.card A ≡ Nat.card V [MOD p] := by
    have hmod := hG.card_modEq_card_fixedPoints A
    rw [← hVcard] at hmod
    exact hmod
  by_cases hVtop : V = ⊤
  · -- The action is trivial, hence `G` is trivial.
    have htriv : ∀ g : G, φ g = 1 := by
      intro g
      apply MulEquiv.ext
      intro a
      have ha : a ∈ V := by rw [hVtop]; exact Subgroup.mem_top a
      have h := (hVmem a).mp ha g
      rw [hsmul] at h
      simpa using h
    have hone : ∀ g : G, g = 1 := fun g => hφ (by rw [htriv g, map_one])
    haveI : Subsingleton G := ⟨fun a b => by rw [hone a, hone b]⟩
    have hcardG : Nat.card G = 1 := Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
    rw [hcardG]
    exact le_of_lt hp.one_lt
  · -- The nontrivial case.
    obtain ⟨n, hn⟩ := hApg.exists_card_eq
    have hn_le : n ≤ 2 := by
      have h := hcard
      rw [hn] at h
      exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h
    -- `A` is nontrivial, since otherwise `V = ⊤`.
    have hAne : Nat.card A ≠ 1 := by
      intro h1
      apply hVtop
      rw [Subgroup.eq_top_iff']
      intro x
      haveI : Subsingleton A := (Nat.card_eq_one_iff_unique.mp h1).1
      rw [Subsingleton.elim x 1]
      exact V.one_mem
    have hpA : p ∣ Nat.card A := by
      rcases hApg.card_eq_or_dvd with h1 | hd
      · exact absurd h1 hAne
      · exact hd
    have hpV : p ∣ Nat.card V :=
      Nat.modEq_zero_iff_dvd.mp (hcongr.symm.trans hpA.modEq_zero_nat)
    have hpd : p ≤ Nat.card V := Nat.le_of_dvd Nat.card_pos hpV
    -- `V` is a proper subgroup of `A`.
    have hVltA : Nat.card V < Nat.card A := by
      have hne : (V : Set A) ≠ Set.univ := by
        intro h
        exact hVtop (Subgroup.ext (fun a => by simpa using Set.ext_iff.mp h a))
      have h := Set.ncard_lt_card hne
      rwa [← Nat.card_coe_set_eq (V : Set A)] at h
    -- Hence `n = 2`.
    have hn2 : n = 2 := by
      have hp_lt : p < p ^ n := by
        rw [hn] at hVltA
        exact lt_of_le_of_lt hpd hVltA
      have h1 : 1 < n := (Nat.pow_lt_pow_iff_right hp.one_lt).mp (by simpa [pow_one] using hp_lt)
      omega
    have hAd : Nat.card A = p ^ 2 := by rw [hn, hn2]
    -- A non-fixed element.
    obtain ⟨a₀, ha₀⟩ : ∃ a : A, a ∉ V := by
      by_contra h
      apply hVtop
      rw [Subgroup.eq_top_iff']
      intro x
      by_contra hx
      exact h ⟨x, hx⟩
    -- `A = ⟨a₀⟩ ⊔ V`.
    have hWtop : Subgroup.closure ({a₀} : Set A) ⊔ V = ⊤ := by
      set W : Subgroup A := Subgroup.closure ({a₀} : Set A) ⊔ V with hWdef
      have hmemW : a₀ ∈ W := by
        rw [hWdef]
        exact Subgroup.mem_sup_left (Subgroup.subset_closure (Set.mem_singleton a₀))
      have hWVne : W ≠ V := fun h => ha₀ (h ▸ hmemW)
      have hVW : V ≤ W := by
        intro v hv
        rw [hWdef]
        exact Subgroup.mem_sup_right hv
      have hVleW : Nat.card V ≤ Nat.card W :=
        Nat.card_le_card_of_injective (Subgroup.inclusion hVW) (Subgroup.inclusion_injective hVW)
      have hVltW : Nat.card V < Nat.card W := by
        rcases lt_or_eq_of_le hVleW with h | h
        · exact h
        · exact absurd (Subgroup.eq_of_le_of_card_ge hVW (le_of_eq h.symm)).symm hWVne
      obtain ⟨e, he⟩ := (hApg.to_subgroup W).exists_card_eq
      have he_gt : 1 < e := by
        have hpW : p < Nat.card W := lt_of_le_of_lt hpd hVltW
        rw [he] at hpW
        exact (Nat.pow_lt_pow_iff_right hp.one_lt).mp (by simpa [pow_one] using hpW)
      have he_le : e ≤ 2 := by
        have hdvd : p ^ e ∣ p ^ 2 := by
          rw [← he, ← hAd]
          exact Subgroup.card_subgroup_dvd_card W
        exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hdvd
      have he2 : e = 2 := by omega
      have hWcard : Nat.card W = Nat.card A := by rw [he, he2, ← hAd]
      exact Subgroup.eq_top_of_card_eq W hWcard
    -- The orbit map is injective into the complement of `V`.
    let f : G → {a : A // a ∉ V} := fun g => ⟨g • a₀, by
      intro hmem
      have hfix : g • a₀ = a₀ := by
        have h := (hVmem (g • a₀)).mp hmem g⁻¹
        rw [← mul_smul, inv_mul_cancel, one_smul] at h
        exact h.symm
      rw [hfix] at hmem
      exact ha₀ hmem⟩
    have hf_inj : Function.Injective f := by
      intro g h hgh
      have hgh' : g • a₀ = h • a₀ := by
        have := congrArg Subtype.val hgh
        simpa [f] using this
      -- `h⁻¹ * g` fixes all of `A`.
      have hfixA : ∀ a : A, (h⁻¹ * g) • a = a := by
        let K : Subgroup A :=
          { carrier := {a | (h⁻¹ * g) • a = a}
            one_mem' := by change (h⁻¹ * g) • (1 : A) = 1; rw [smul_one]
            mul_mem' := by
              intro a b ha hb
              change (h⁻¹ * g) • (a * b) = a * b
              rw [smul_mul', ha, hb]
            inv_mem' := by
              intro a ha
              change (h⁻¹ * g) • a⁻¹ = a⁻¹
              rw [smul_inv', ha] }
        have hKmem : ∀ a : A, a ∈ K ↔ (h⁻¹ * g) • a = a := fun a => Iff.rfl
        have hVK : V ≤ K := fun v hv => (hKmem v).mpr ((hVmem v).mp hv (h⁻¹ * g))
        have hclK : Subgroup.closure ({a₀} : Set A) ≤ K := by
          rw [Subgroup.closure_le]
          intro x hx
          rw [Set.mem_singleton_iff] at hx
          rw [hx]
          change (h⁻¹ * g) • a₀ = a₀
          rw [mul_smul, hgh', ← mul_smul, inv_mul_cancel, one_smul]
        have hKW : (⊤ : Subgroup A) ≤ K := by
          rw [← hWtop]
          exact sup_le hclK hVK
        intro a
        exact (hKmem a).mp (hKW (Subgroup.mem_top a))
      have hphi : φ (h⁻¹ * g) = 1 := by
        apply MulEquiv.ext
        intro a
        have h := hfixA a
        rw [hsmul] at h
        simpa using h
      have hkg : h⁻¹ * g = 1 := hφ (by rw [hphi, map_one])
      have : g = h := by
        have hh := congrArg (fun x => h * x) hkg
        simpa using hh
      exact this
    -- Bound `|G|`.
    obtain ⟨k, hk⟩ := hG.exists_card_eq
    have hle : Nat.card G ≤ Nat.card {a : A // a ∉ V} :=
      Nat.card_le_card_of_injective f hf_inj
    have hcompl_lt : Nat.card {a : A // a ∉ V} < p ^ 2 := by
      have hcompl : Nat.card {a : A // a ∉ V} = (Vᶜ : Set A).ncard :=
        Nat.card_coe_set_eq (Vᶜ : Set A)
      rw [hcompl]
      have hne : (Vᶜ : Set A) ≠ Set.univ := by
        intro h
        have hmem : (1 : A) ∈ (Vᶜ : Set A) := by rw [h]; exact Set.mem_univ 1
        rw [Set.mem_compl_iff] at hmem
        exact hmem V.one_mem
      calc (Vᶜ : Set A).ncard < Nat.card A := Set.ncard_lt_card hne
        _ = p ^ 2 := hAd
    have hpk_lt : p ^ k < p ^ 2 := by rw [← hk]; exact lt_of_le_of_lt hle hcompl_lt
    have hk2 : k < 2 := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hpk_lt
    have hk1 : k ≤ 1 := by omega
    rw [hk]
    calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hk1
      _ = p := pow_one p

end Work.SmallRank
