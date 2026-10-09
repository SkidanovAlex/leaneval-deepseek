import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.place_basics
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Schmidt--Wingberg §4, the last two conjuncts of the constructed class `z`

This file isolates the *bookkeeping* half of the verification of Schmidt--Wingberg's construction of
the auxiliary class `z` (`Work.SSGRoute.sw_z_exists_odd_sketch`, the odd-`p`, `A = μ_p` case of
Theorem 13 of arXiv:math/9809211): once the sequence `z_1, z_2, …` has been produced (with the
local conditions (1), (2), (3) of the paper), the final class `z = z_i + z_N` has

* conjunct (5) — it is unramified at every place outside `cs(S)` which is not split in the level
  `N` (the paper: "`z_P` is unramified for `P ∉ T(K)` not split in `N`");
* conjunct (6) — at a place `B ∉ cs(S)` split in `N` at which `z` *is* ramified, `z` vanishes on
  the local groups of the `k`-conjugates of `B` that are not `G_K`-conjugates of `B`
  (the paper: "`z_P^σ = 0` for every `σ ∈ G(K|k) ∖ {1}`");

from exactly the three inputs which the construction supplies:

* `hz_conf` — `z` is unramified outside the `G_K`-conjugates of the two new primes `P_i`, `P_N`
  (this is the paper's condition (1): `z_i` is unramified at every place except `P_i`);
* `hPi_split`, `hPN_split` — the two new primes are split in `N`, which is the Chebotarev choice
  (`P_{n+1} ∉ T_n(K) ⊆ cs(N|k)`);
* `hz_conj_i`, `hz_conj_N` — the *one-sided* vanishing: `z` vanishes on the local groups of the
  `k`-conjugates of `P_i` (resp. `P_N`) that are not `G_K`-conjugates.  For `P_i` this is the
  paper's condition (3) (`(z_{n+1})_{σP_i} = -(z_i)_{σP_i}`, so that `z = z_i + z_N` vanishes);
  for `P_N` it is the final Hilbert-symbol computation of the paper (the only place where the
  product formula is used).

The proof is pure place bookkeeping: splitness in a normal extension is invariant under
`G_k`-conjugation (`SSGRoute.isSplitIn_conj`), so a place at which `z` is ramified and which is not
split in `N` cannot be a conjugate of the (split) new primes; and the "not `G_K`-conjugate"
condition for the pair `(B, Q)` transfers to the pair `(P_i, Q)` because `B` *is* a
`G_K`-conjugate of `P_i`.
-/

open scoped Pointwise

namespace Work.SSGRoute.ZSplit

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {p : ℕ} [Fact p.Prime]
variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

/-- **Conjuncts (5) and (6) of the §4 class `z`, from the construction's three inputs.** -/
theorem sw_conjuncts_five_six
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N]
    (S : Finset (ValuationSubring Ω))
    (Pi PN : ValuationSubring Ω) (hPi : SSGRoute.IsFinPlace k Pi) (hPN : SSGRoute.IsFinPlace k PN)
    (hPi_split : SSGRoute.IsSplitIn k N Pi) (hPN_split : SSGRoute.IsSplitIn k N PN)
    (z : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hz_conf : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (¬ ∃ τ ∈ K.fixingSubgroup, τ • Pi = B) → (¬ ∃ τ ∈ K.fixingSubgroup, τ • PN = B) →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0)
    (hz_conj_i : ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k Pi Q →
        (¬ ∃ τ ∈ K.fixingSubgroup, τ • Pi = Q) →
        ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup, z τ = 0)
    (hz_conj_N : ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k PN Q →
        (¬ ∃ τ ∈ K.fixingSubgroup, τ • PN = Q) →
        ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup, z τ = 0) :
    (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) ∧
    (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k N B →
        (∃ σ, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧ z σ ≠ 0) →
        ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k B Q →
          (¬ ∃ τ ∈ K.fixingSubgroup, τ • B = Q) →
          ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup, z τ = 0) := by
  have hnorm : (N.fixingSubgroup).Normal := IsGalois.fixingSubgroup_normal_of_isGalois N
  constructor
  · -- conjunct (5): the ramification of `z` sits on the `N`-split new primes
    intro B hB _ hns σ hσK hσI
    refine hz_conf B hB (fun h => ?_) (fun h => ?_) σ hσK hσI
    · obtain ⟨τP, _, hτPB⟩ := h
      exact hns (hτPB ▸ (SSGRoute.isSplitIn_conj N hnorm Pi τP).mpr hPi_split)
    · obtain ⟨τP, _, hτPB⟩ := h
      exact hns (hτPB ▸ (SSGRoute.isSplitIn_conj N hnorm PN τP).mpr hPN_split)
  · -- conjunct (6): the one-sided vanishing
    intro B hB _ _ hram Q hBQ hnotconj τ hτ
    obtain ⟨σI, hσII, hσIK, hσIne⟩ := hram
    -- `B` is a `G_K`-conjugate of one of the two new primes
    have hBc : (∃ ρ ∈ K.fixingSubgroup, ρ • Pi = B) ∨
        (∃ ρ ∈ K.fixingSubgroup, ρ • PN = B) := by
      by_contra h
      rw [not_or] at h
      exact hσIne (hz_conf B hB h.1 h.2 σI hσIK hσII)
    obtain ⟨σQ, hσQ⟩ := hBQ
    rcases hBc with ⟨τP, hτPK, hτPB⟩ | ⟨τP, hτPK, hτPB⟩
    · have hQpi : SSGRoute.IsConjPlace k Pi Q := ⟨σQ * τP, by rw [mul_smul, hτPB, hσQ]⟩
      have hQnp : ¬ ∃ ν ∈ K.fixingSubgroup, ν • Pi = Q := by
        rintro ⟨ν, hνK, hνQ⟩
        refine hnotconj ⟨ν * τP⁻¹,
          K.fixingSubgroup.mul_mem hνK (K.fixingSubgroup.inv_mem hτPK), ?_⟩
        rw [mul_smul, ← hτPB, inv_smul_smul]
        exact hνQ
      exact hz_conj_i Q hQpi hQnp τ hτ
    · have hQpn : SSGRoute.IsConjPlace k PN Q := ⟨σQ * τP, by rw [mul_smul, hτPB, hσQ]⟩
      have hQnp : ¬ ∃ ν ∈ K.fixingSubgroup, ν • PN = Q := by
        rintro ⟨ν, hνK, hνQ⟩
        refine hnotconj ⟨ν * τP⁻¹,
          K.fixingSubgroup.mul_mem hνK (K.fixingSubgroup.inv_mem hτPK), ?_⟩
        rw [mul_smul, ← hτPB, inv_smul_smul]
        exact hνQ
      exact hz_conj_N Q hQpn hQnp τ hτ

/-! ## Conjuncts (1)–(4): the sum of the two halves

The paper's construction sets `z = z_i + z_N` where each half satisfies `(z_i)_P = (1/2) y_P` at the
places of `T(K)`.  Here is the corresponding assembly: the sum is additive, locally constant, agrees
with `y` at the places of `cs(S)`, and vanishes on the involutions.  The hypothesis `p ≠ 2` is used
only here, through the invertibility of `2` in `ZMod p`. -/

/-- Cancellation of `2` in `ZMod p` for odd `p`. -/
theorem two_mul_eq_two_mul_zmod (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) {a b : ZMod p}
    (h : 2 * a = 2 * b) : a = b := by
  refine mul_left_cancel₀ (show (2 : ZMod p) ≠ 0 from ?_) h
  intro h0
  have hd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h0
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hd
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  exact hp (le_antisymm hle hp2)

/-- **Conjuncts (1)–(4) of the §4 class `z = z_i + z_N`.** -/
theorem sw_sum_conjuncts_one_four
    (hp : p ≠ 2)
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (S : Finset (ValuationSubring Ω))
    (y zi zN : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hzi : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, zi (g * h) = zi g + zi h)
    (hzN : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, zN (g * h) = zN g + zN h)
    (hzi_c : SSGRoute.IsLocConstOn K.fixingSubgroup zi)
    (hzN_c : SSGRoute.IsLocConstOn K.fixingSubgroup zN)
    (hzi_T : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → 2 * zi σ = y σ)
    (hzN_T : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → 2 * zN σ = y σ)
    (hzi_inv : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → zi c = 0)
    (hzN_inv : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → zN c = 0) :
    (∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup,
        (zi + zN) (g * h) = (zi + zN) g + (zi + zN) h) ∧
    SSGRoute.IsLocConstOn K.fixingSubgroup (zi + zN) ∧
    (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → (zi + zN) σ = y σ) ∧
    (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → (zi + zN) c = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g hg h hh
    simp only [Pi.add_apply, hzi g hg h hh, hzN g hg h hh]
    abel
  · obtain ⟨U, hUo, hU⟩ := hzi_c
    obtain ⟨V, hVo, hV⟩ := hzN_c
    refine ⟨U ⊓ V, hUo.inter hVo, ?_⟩
    intro g hg u hu huH
    rw [Subgroup.mem_inf] at hu
    simp only [Pi.add_apply, hU g hg u hu.1 huH, hV g hg u hu.2 huH]
  · intro B hB hconj σ hσK hσd
    simp only [Pi.add_apply]
    refine two_mul_eq_two_mul_zmod p hp ?_
    rw [mul_add, hzi_T B hB hconj σ hσK hσd, hzN_T B hB hconj σ hσK hσd, two_mul]
  · intro c hc hc2
    simp only [Pi.add_apply, hzi_inv c hc hc2, hzN_inv c hc hc2, add_zero]

/-! ## The §4 assembly: the six conjuncts from the two halves -/

/-- **The §4 odd-`p`, `A = μ_p` conclusion from the two halves `z_i`, `z_N`.**  This is the last
page of Schmidt--Wingberg's §4: the constructed class is `z = z_i + z_N`, and all six conjuncts of
the conclusion follow from the two halves' data — additivity, local constancy, the prescribed
values `(1/2) y` at the `cs(S)`-places, the vanishing on the involutions, the confinement of the
ramification to the two new primes `S_i`, `S_N` (which are split in `N`), and the one-sided
vanishing at the `k`-conjugates of the two new primes (condition (3) at `S_i`, the final
Hilbert-symbol computation at `S_N`). -/
theorem sw_z_exists_odd_of_two_classes
    (hp : p ≠ 2)
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N]
    (S : Finset (ValuationSubring Ω))
    (Si SN : ValuationSubring Ω) (hSi : SSGRoute.IsFinPlace k Si) (hSN : SSGRoute.IsFinPlace k SN)
    (hSi_split : SSGRoute.IsSplitIn k N Si) (hSN_split : SSGRoute.IsSplitIn k N SN)
    (y zi zN : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hzi : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, zi (g * h) = zi g + zi h)
    (hzN : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, zN (g * h) = zN g + zN h)
    (hzi_c : SSGRoute.IsLocConstOn K.fixingSubgroup zi)
    (hzN_c : SSGRoute.IsLocConstOn K.fixingSubgroup zN)
    (hzi_T : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → 2 * zi σ = y σ)
    (hzN_T : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → 2 * zN σ = y σ)
    (hzi_inv : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → zi c = 0)
    (hzN_inv : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → zN c = 0)
    (hzi_conf : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (¬ ∃ τ ∈ K.fixingSubgroup, τ • Si = B) →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → zi σ = 0)
    (hzN_conf : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (¬ ∃ τ ∈ K.fixingSubgroup, τ • SN = B) →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → zN σ = 0)
    (hzi_conj : ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k Si Q →
        (¬ ∃ τ ∈ K.fixingSubgroup, τ • Si = Q) →
        ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup, (zi + zN) τ = 0)
    (hzN_conj : ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k SN Q →
        (¬ ∃ τ ∈ K.fixingSubgroup, τ • SN = Q) →
        ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup, (zi + zN) τ = 0) :
    (∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup,
        (zi + zN) (g * h) = (zi + zN) g + (zi + zN) h) ∧
    SSGRoute.IsLocConstOn K.fixingSubgroup (zi + zN) ∧
    (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → (zi + zN) σ = y σ) ∧
    (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → (zi + zN) c = 0) ∧
    (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → (zi + zN) σ = 0) ∧
    (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k N B →
        (∃ σ, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧ (zi + zN) σ ≠ 0) →
        ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k B Q →
          (¬ ∃ τ ∈ K.fixingSubgroup, τ • B = Q) →
          ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup, (zi + zN) τ = 0) := by
  obtain ⟨h1, h2, h3, h4⟩ :=
    sw_sum_conjuncts_one_four (p := p) hp K S y zi zN hzi hzN hzi_c hzN_c hzi_T hzN_T hzi_inv hzN_inv
  have hconf : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (¬ ∃ τ ∈ K.fixingSubgroup, τ • Si = B) →
      (¬ ∃ τ ∈ K.fixingSubgroup, τ • SN = B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → (zi + zN) σ = 0 := by
    intro B hB h1 h2 σ hσK hσI
    rw [Pi.add_apply, hzi_conf B hB h1 σ hσK hσI, hzN_conf B hB h2 σ hσK hσI, add_zero]
  obtain ⟨h5, h6⟩ := sw_conjuncts_five_six K N S Si SN hSi hSN hSi_split hSN_split (zi + zN)
    hconf hzi_conj hzN_conj
  exact ⟨h1, h2, h3, h4, h5, h6⟩

end Work.SSGRoute.ZSplit
