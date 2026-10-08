import Mathlib
import Submission.Work.ThmF.ChV12.irreducible_of_orderOf_prime
import Submission.Work.ThmF.ChV12.centralizer_irreducible_isCyclic
import Submission.Work.ThmF.ChV12.zpowers_eq_of_commute_of_orderOf_prime
import Submission.Work.ThmF.ChV12.odd_ppd_normalizes

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV12.even_card_closure_of_two_ppd`

Let `A` be a finite elementary abelian `2`-group (`x * x = 1`), `|A| = 2 ^ k`, and `q` a prime with
`orderOf (2 : ZMod q) = k` (a *primitive prime divisor* of `2 ^ k - 1`).  Then two automorphisms
`σ τ : MulAut A` of order `q` generating **distinct** cyclic subgroups generate a subgroup of
`⟨σ, τ⟩` of **even** order.

The proof is by contradiction.  Suppose `|G|` is odd, where `G = ⟨σ, τ⟩`.  Since `orderOf σ = q`
and `orderOf (2 : ZMod q) = k`, the element `σ` acts irreducibly on `A`
(`irreducible_of_orderOf_prime`), so `A` is a simple `𝔽₂[G]`-module.  By `odd_ppd_normalizes`, the
odd-order group `G` normalizes `⟨σ⟩`.

Then `G` normalizes `⟨σ⟩` and `τ ⟨σ⟩ τ⁻¹ = ⟨σ⟩`, so `τ` acts on the cyclic group `⟨σ⟩ ≅ C_q` by
conjugation; the induced automorphism `φ` of `⟨σ⟩` satisfies `φ ^ q = 1` (as `τ ^ q = 1`) and lives
in `MulAut ⟨σ⟩` of order `q - 1`; as `q` is prime, `gcd q (q - 1) = 1`, so `φ = 1`, i.e.
`τ σ τ⁻¹ = σ`.  Hence `σ` and `τ` commute, and by `zpowers_eq_of_commute_of_orderOf_prime` two
commuting elements of order `q` generate the same cyclic subgroup, contradicting `hne`.  ∎
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace Work.ThmF.ChV12
-- **(2026-10-07, area owner).**  Per the lead's ruling the odd-order theorem may be assumed,
-- so this node carries `(hFT : FeitThompsonProp)`; the FT-free route survives as the
-- `PpdClosureProp`/`TransitiveLinearSolvable` definitions (`ChV12/ppdClosureProp_holds.lean`).


/-- If `σ`, `τ` have prime order `q` and `τ σ τ⁻¹ = σ ^ i`, then `σ` and `τ` commute.

`τ` normalizes the cyclic group `⟨σ⟩ ≅ C_q`; the induced automorphism of `⟨σ⟩` has order dividing
both `q` (since `τ ^ q = 1`) and `q - 1 = |MulAut ⟨σ⟩|`, hence is trivial (as `gcd q (q - 1) = 1`),
so `τ σ τ⁻¹ = σ`. -/
lemma commute_of_conj_eq_zpow {M : Type*} [Group M] [Finite M] {q : ℕ} (hq : q.Prime)
    {σ τ : M} (hσ : orderOf σ = q) (hτ : orderOf τ = q) {i : ℤ}
    (hi : τ * σ * τ⁻¹ = σ ^ i) : σ * τ = τ * σ := by
  haveI : Fact q.Prime := ⟨hq⟩
  -- `τ` normalizes `⟨σ⟩`.
  have hτmap : Subgroup.map (MulAut.conj τ : M →* M) (Subgroup.zpowers σ) ≤ Subgroup.zpowers σ := by
    rintro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨i * n, ?_⟩
    have hcoe : ((MulAut.conj τ : M →* M)) σ = τ * σ * τ⁻¹ := by
      change (MulAut.conj τ) σ = τ * σ * τ⁻¹
      rw [MulAut.conj_apply]
    rw [map_zpow, hcoe, hi, ← zpow_mul]
  have heq : Subgroup.map (MulAut.conj τ : M →* M) (Subgroup.zpowers σ)
      = Subgroup.zpowers σ :=
    Subgroup.eq_of_le_of_card_ge hτmap
      (by rw [Subgroup.card_map_of_injective (MulAut.conj τ).injective])
  have hτN : τ ∈ Subgroup.normalizer ((Subgroup.zpowers σ : Subgroup M) : Set M) :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).mpr heq
  -- the induced automorphism `φ` of `⟨σ⟩`.
  have hφq : (Subgroup.normalizerMonoidHom (Subgroup.zpowers σ) ⟨τ, hτN⟩) ^ q = 1 := by
    have hord : orderOf (⟨τ, hτN⟩ :
        ↥(Subgroup.normalizer ((Subgroup.zpowers σ : Subgroup M) : Set M))) = q := by
      rw [← Subgroup.orderOf_coe (⟨τ, hτN⟩ :
        ↥(Subgroup.normalizer ((Subgroup.zpowers σ : Subgroup M) : Set M)))]
      exact hτ
    have h1 : (⟨τ, hτN⟩ :
        ↥(Subgroup.normalizer ((Subgroup.zpowers σ : Subgroup M) : Set M))) ^ q = 1 := by
      rw [← hord]; exact pow_orderOf_eq_one _
    rw [← map_pow, h1, map_one]
  have hdvd1 : orderOf (Subgroup.normalizerMonoidHom (Subgroup.zpowers σ) ⟨τ, hτN⟩) ∣ q :=
    orderOf_dvd_iff_pow_eq_one.mpr hφq
  have hdvd2 : orderOf (Subgroup.normalizerMonoidHom (Subgroup.zpowers σ) ⟨τ, hτN⟩) ∣ q - 1 := by
    have h2 := orderOf_dvd_natCard (Subgroup.normalizerMonoidHom (Subgroup.zpowers σ) ⟨τ, hτN⟩)
    rw [Subgroup.isCyclic_zpowers σ |>.card_mulAut,
      Nat.card_zpowers σ, hσ, Nat.totient_prime hq] at h2
    exact h2
  have hcop : Nat.Coprime (q - 1) q :=
    (Nat.coprime_self_sub_right (m := 1) hq.one_le).mpr (Nat.coprime_one_right q) |>.symm
  have hφ1 : Subgroup.normalizerMonoidHom (Subgroup.zpowers σ) ⟨τ, hτN⟩ = 1 := by
    have h3 : orderOf (Subgroup.normalizerMonoidHom (Subgroup.zpowers σ) ⟨τ, hτN⟩) = 1 := by
      have h4 : orderOf (Subgroup.normalizerMonoidHom (Subgroup.zpowers σ) ⟨τ, hτN⟩)
          ∣ Nat.gcd q (q - 1) := Nat.dvd_gcd hdvd1 hdvd2
      rw [show Nat.gcd q (q - 1) = 1 from hcop.symm] at h4
      exact Nat.dvd_one.mp h4
    exact orderOf_eq_one_iff.mp h3
  -- conclude `τ σ τ⁻¹ = σ`.
  have hconj : τ * σ * τ⁻¹ = σ := by
    have hh : (Subgroup.normalizerMonoidHom (Subgroup.zpowers σ) ⟨τ, hτN⟩)
        ⟨σ, Subgroup.mem_zpowers σ⟩ = ⟨σ, Subgroup.mem_zpowers σ⟩ := by
      rw [hφ1]; rfl
    have h2 := congrArg (Subtype.val) hh
    have hfac : ((Subgroup.normalizerMonoidHom (Subgroup.zpowers σ) ⟨τ, hτN⟩)
        ⟨σ, Subgroup.mem_zpowers σ⟩ : M) = τ * σ * τ⁻¹ := by
      simp only [Subgroup.normalizerMonoidHom, MulDistribMulAction.toMulAut_apply,
        MulDistribMulAction.toMulEquiv_apply]
      rfl
    rw [hfac] at h2
    simpa using h2
  calc σ * τ = (τ * σ * τ⁻¹) * τ := by rw [hconj]
    _ = τ * σ := by group

/-- **Main lemma.**  Two automorphisms of a finite elementary abelian `2`-group `A` of order
`2 ^ k` and of order `q` (where `q` is a primitive prime divisor of `2 ^ k - 1`) whose cyclic
subgroups are distinct generate a subgroup of even order. -/
theorem even_card_closure_of_two_ppd (hFT : Submission.Blueprint.FeitThompsonProp) {A : Type} [Group A] [Finite A]
    (hA2 : ∀ x : A, x * x = 1) (hAc : ∀ x y : A, x * y = y * x) {k q : ℕ}
    (hk1 : 1 ≤ k) (hk : Nat.card A = 2 ^ k) (hq : Nat.Prime q)
    (hord : orderOf (2 : ZMod q) = k)
    (σ τ : MulAut A) (hσ : orderOf σ = q) (hτ : orderOf τ = q)
    (hne : Subgroup.zpowers σ ≠ Subgroup.zpowers τ) :
    Even (Nat.card ↥(Subgroup.closure ({σ, τ} : Set (MulAut A)))) := by
  by_contra hev
  rw [Nat.not_even_iff_odd] at hev
  set G : Subgroup (MulAut A) := Subgroup.closure ({σ, τ} : Set (MulAut A)) with hG
  have hσG : σ ∈ G := Subgroup.subset_closure (by simp [hG])
  have hτG : τ ∈ G := Subgroup.subset_closure (by simp [hG])
  -- `G` normalizes `⟨σ⟩`
  have hnorm := odd_ppd_normalizes hFT hA2 hAc hk1 hk hq hord G hev σ hσG hσ
  obtain ⟨i, hi⟩ := hnorm τ hτG
  -- `τ σ τ⁻¹ = σ ^ i`, so `σ` and `τ` commute
  have hcomm : σ * τ = τ * σ := commute_of_conj_eq_zpow hq hσ hτ hi
  exact hne (zpowers_eq_of_commute_of_orderOf_prime hA2 hAc hk hq hord σ τ hσ hτ hcomm)

end Work.ThmF.ChV12
