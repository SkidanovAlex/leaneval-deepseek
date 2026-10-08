import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.SixThree
import Submission.Work.CORE4.Case2CountSetup

open scoped commutatorElement

set_option linter.style.haveILetI false

namespace Work.CORE4

/-- The "`U ⊓ M` versus `U ⊓ E`" transfer in Bender 1981, §4 (1)–(2) (p. 224).

Let `E ⊴ M` be subgroups of `G` (`(E.subgroupOf M).Normal`), `Q ≤ E` a `2`-subgroup,
`X ≤ M` of **odd** order with `Q ≤ N_G(X)`, `s ∈ Q` an involution, and assume the `E`-part of
Bender's (1) for `X ⊓ E`:

* `invSet (X ⊓ E) s = [Q, X ⊓ E]` **as sets**, and `[Q, X ⊓ E]` is cyclic.

Then `[Q, X] = [Q, X ⊓ E]`, `invSet X s = [Q, X]` (as sets), `[Q, X]` is cyclic,
`X ⊓ C_G(s) = X ⊓ C_G(Q)` and `X = [Q, X] ⊔ (X ⊓ C_G(s))`.

Route.  Since `s ∈ Q ≤ E` acts trivially on `M/E` and `X ⊓ E ⊴ X`,
* `[Q, X] ⊆ X ⊓ E`: for `q ∈ Q ≤ E`, `x ∈ X ≤ M`, `[q, x] = q · (x q⁻¹ x⁻¹) ∈ E`
  (normality of `E ⊴ M`) and `[q, x] ∈ X` (as `q` normalises `X`);
* `[Q, X] = [Q, [Q, X]]` by the coprimality axiom `I.toolkit.c11i` (`Q` is a `2`-group, `X` odd
  and `Q ≤ N_G(X)`); with `[Q, X] ≤ X ⊓ E` and `X ⊓ E ≤ X`, `Subgroup.commutator_mono` gives
  `[Q, X] ⊆ [Q, X ⊓ E]`, and `⊇` is trivial;
* `invSet X s = invSet (X ⊓ E) s`: `⊇` is trivial, and for `y ∈ X` with `y^s = y⁻¹` the image of
  `y` in `M/E` is fixed by `s` (as `s ∈ E`) and inverted by `s`, hence of order `≤ 2`; its order
  divides `orderOf y ∣ |X|`, which is odd, so that image is trivial, i.e. `y ∈ E`;
* `X = [Q, X] ⊔ (X ⊓ C_G(Q))` is `I.toolkit.c11i` again, and `[Q, X] ⊴ X` follows from
  `Subgroup.normalizer_commutator_ge_right` (or from `I.toolkit.c15` applied to `(X, s)`, which
  gives `(I.subgroupOf X).Normal` for `I = invSet X s = [Q, X]` since `s` has order `2`, `X` has
  odd order and `s ∈ Q ≤ N_G(X)`);
* hence (as `X` is odd and `[Q, X] = invSet X s`) every `x ∈ X ⊓ C_G(s)` can be written
  `x = k · c` with `k ∈ [Q, X] = invSet X s` and `c ∈ X ⊓ C_G(Q)`
  (`Work.CORE4.exists_mul_of_mem_of_normal_subgroupOf`); then `k⁻¹ c = x^s = x = k c` gives
  `k = k⁻¹`, so `k² = 1` and `k = 1` (`X` odd), whence `x = c ∈ C_G(Q)`; this is
  `X ⊓ C_G(s) = X ⊓ C_G(Q)`. -/
theorem TransferLayerInf (I : Work.GW2.C4Inputs) :
    ∀ {G : Type} [Group G] [Finite G], ∀ (E M Q X : Subgroup G) (s : G),
      E ≤ M → (E.subgroupOf M).Normal → Q ≤ E → X ≤ M →
      Q ≤ Subgroup.normalizer (X : Set G) →
      IsPGroup 2 Q → Odd (Nat.card X) → s ∈ Q → orderOf s = 2 →
      (((⁅Q, X ⊓ E⁆ : Subgroup G) : Set G) = Work.GW2.invSet (X ⊓ E) s) →
      IsCyclic (⁅Q, X ⊓ E⁆ : Subgroup G) →
      ((⁅Q, X⁆ : Subgroup G) = ⁅Q, X ⊓ E⁆) ∧
      (((⁅Q, X⁆ : Subgroup G) : Set G) = Work.GW2.invSet X s) ∧
      IsCyclic (⁅Q, X⁆ : Subgroup G) ∧
      (X ⊓ Subgroup.centralizer ({s} : Set G) =
        X ⊓ Subgroup.centralizer ((Q : Subgroup G) : Set G)) ∧
      X = ⁅Q, X⁆ ⊔ (X ⊓ Subgroup.centralizer ({s} : Set G)) := by
  intro G _ _ E M Q X s hEM hEnorm hQE hXM hNX hQP hXodd hsQ hs2 hI hcyc
  -- `2` is coprime to `|X|`
  have hcop : Nat.Coprime 2 (Nat.card X) := Nat.coprime_two_left.mpr hXodd
  -- coprimality axiom 1.1(i) for `(Q, X)`
  obtain ⟨h11i1, h11i2⟩ := I.toolkit.c11i G 2 Q X hQP hcop hNX
  -- `[Q, X] ≤ X`
  have hKX : (⁅Q, X⁆ : Subgroup G) ≤ X :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp hNX
  -- Step 1: `[Q, X] ≤ X ⊓ E`
  have hXinE : (⁅Q, X⁆ : Subgroup G) ≤ X ⊓ E := by
    rw [Subgroup.commutator_le]
    intro q hq x hx
    have hqE : q ∈ E := hQE hq
    have hconj : x * q⁻¹ * x⁻¹ ∈ E :=
      (Subgroup.normal_subgroupOf_iff hEM).mp hEnorm q⁻¹ x (E.inv_mem hqE) (hXM hx)
    refine Subgroup.mem_inf.mpr ⟨hKX (Subgroup.commutator_mem_commutator hq hx), ?_⟩
    have hrepr : (⁅q, x⁆ : G) = q * (x * q⁻¹ * x⁻¹) := by group
    rw [hrepr]
    exact E.mul_mem hqE hconj
  -- Step 2: `[Q, X] = [Q, X ⊓ E]`
  have hCommEq : (⁅Q, X⁆ : Subgroup G) = ⁅Q, X ⊓ E⁆ := by
    refine le_antisymm ?_ ?_
    · rw [← h11i1]
      exact Subgroup.commutator_mono le_rfl hXinE
    · exact Subgroup.commutator_mono le_rfl inf_le_left
  -- Step 3: `invSet X s = invSet (X ⊓ E) s`
  have hinvEq : Work.GW2.invSet X s = Work.GW2.invSet (X ⊓ E) s := by
    refine Set.Subset.antisymm ?_ ?_
    · intro y hy
      have hyX : y ∈ X := hy.1
      have hyinv : s * y * s⁻¹ = y⁻¹ := hy.2
      have hyM : y ∈ M := hXM hyX
      have hsE : s ∈ E := hQE hsQ
      have hsM : s ∈ M := hEM hsE
      haveI : (E.subgroupOf M).Normal := hEnorm
      set ŷ : ↥M := ⟨y, hyM⟩ with hŷ
      set ŝ : ↥M := ⟨s, hsM⟩ with hŝ
      -- `s` maps to `1` in `M/E`
      have hŝN : ŝ ∈ E.subgroupOf M := by
        rw [Subgroup.mem_subgroupOf, hŝ]
        exact hsE
      have hŝker : QuotientGroup.mk' (E.subgroupOf M) ŝ = 1 := by
        rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk' (E.subgroupOf M)]
        exact hŝN
      -- `ŝ * ŷ * ŝ⁻¹ = ŷ⁻¹` in `↥M`
      have hconj : ŝ * ŷ * ŝ⁻¹ = ŷ⁻¹ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hŷ, hŝ]
        simpa using hyinv
      -- hence `ŷ` maps to an element of order dividing `2`
      have hmap₁ : QuotientGroup.mk' (E.subgroupOf M) (ŝ * ŷ * ŝ⁻¹)
          = QuotientGroup.mk' (E.subgroupOf M) ŷ := by
        rw [map_mul, map_mul, map_inv, hŝker]
        simp
      have hpow : QuotientGroup.mk' (E.subgroupOf M) ŷ ^ 2 = 1 := by
        have h1 : QuotientGroup.mk' (E.subgroupOf M) ŷ
            = (QuotientGroup.mk' (E.subgroupOf M) ŷ)⁻¹ := by
          calc QuotientGroup.mk' (E.subgroupOf M) ŷ
              = QuotientGroup.mk' (E.subgroupOf M) (ŝ * ŷ * ŝ⁻¹) := hmap₁.symm
            _ = QuotientGroup.mk' (E.subgroupOf M) (ŷ⁻¹) := by rw [hconj]
            _ = (QuotientGroup.mk' (E.subgroupOf M) ŷ)⁻¹ := map_inv _ _
        have h2 : QuotientGroup.mk' (E.subgroupOf M) ŷ
            * QuotientGroup.mk' (E.subgroupOf M) ŷ = 1 := by
          have hh := congrArg
            (fun z => QuotientGroup.mk' (E.subgroupOf M) ŷ * z) h1
          rwa [mul_inv_cancel] at hh
        simpa [pow_two] using h2
      -- and its order also divides the odd number `|X|`
      have hdiv2 : orderOf (QuotientGroup.mk' (E.subgroupOf M) ŷ) ∣ 2 :=
        orderOf_dvd_iff_pow_eq_one.mpr hpow
      have hdivX : orderOf (QuotientGroup.mk' (E.subgroupOf M) ŷ) ∣ Nat.card X :=
        (orderOf_map_dvd (QuotientGroup.mk' (E.subgroupOf M)) ŷ).trans (by
          rw [hŷ, Subgroup.orderOf_mk]
          exact Subgroup.orderOf_dvd_natCard X hyX)
      have hord1 : orderOf (QuotientGroup.mk' (E.subgroupOf M) ŷ) = 1 := by
        have hdvd : orderOf (QuotientGroup.mk' (E.subgroupOf M) ŷ)
            ∣ (2).gcd (Nat.card X) := Nat.dvd_gcd hdiv2 hdivX
        rw [Nat.Coprime.gcd_eq_one hcop, Nat.dvd_one] at hdvd
        exact hdvd
      have hπ1 : QuotientGroup.mk' (E.subgroupOf M) ŷ = 1 := orderOf_eq_one_iff.mp hord1
      have hŷN : ŷ ∈ E.subgroupOf M := by
        rw [← QuotientGroup.ker_mk' (E.subgroupOf M)]
        exact MonoidHom.mem_ker.mpr hπ1
      have hyE : y ∈ E := by
        have := Subgroup.mem_subgroupOf.mp hŷN
        simpa [hŷ] using this
      exact ⟨Subgroup.mem_inf.mpr ⟨hyX, hyE⟩, hyinv⟩
    · intro y hy
      exact ⟨(Subgroup.mem_inf.mp hy.1).1, hy.2⟩
  -- `invSet X s = [Q, X]` as sets
  have hInvSetEq : ((⁅Q, X⁆ : Subgroup G) : Set G) = Work.GW2.invSet X s := by
    rw [hCommEq, hI, hinvEq]
  -- `[Q, X] ⊴ X` (from `I.toolkit.c15`)
  have hnormK : ((⁅Q, X⁆ : Subgroup G).subgroupOf X).Normal :=
    ((I.toolkit.c15 G I.toolkit.ft X s hs2 hXodd (hNX hsQ)).2.2 ⁅Q, X⁆ hInvSetEq).2.1
  -- Step 4: `X ⊓ C_G(s) = X ⊓ C_G(Q)`
  have hCentEq : X ⊓ Subgroup.centralizer ({s} : Set G) =
      X ⊓ Subgroup.centralizer ((Q : Subgroup G) : Set G) := by
    refine le_antisymm ?_ ?_
    · intro x hx
      obtain ⟨hxX, hxCs⟩ := Subgroup.mem_inf.mp hx
      -- write `x = k * c` with `k ∈ [Q, X]`, `c ∈ X ⊓ C_G(Q)`
      obtain ⟨k, hkK, c, hcB0, hkc⟩ :=
        exists_mul_of_mem_of_normal_subgroupOf (K := ⁅Q, X⁆)
          (B0 := X ⊓ Subgroup.centralizer ((Q : Subgroup G) : Set G))
          hKX inf_le_left hnormK h11i2 x hxX
      have hkX : k ∈ X := hKX hkK
      have hcCQ : c ∈ Subgroup.centralizer ((Q : Subgroup G) : Set G) :=
        (Subgroup.mem_inf.mp hcB0).2
      -- `s` inverts `k` and fixes `c`
      have hkinv : s * k * s⁻¹ = k⁻¹ := by
        have hkinv' : k ∈ Work.GW2.invSet X s := by
          rw [← hInvSetEq]; exact hkK
        exact hkinv'.2
      have hsc : s * c * s⁻¹ = c := by
        have hcomm : s * c = c * s := Subgroup.mem_centralizer_iff.mp hcCQ s hsQ
        rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
      -- `s` fixes `x` as well
      have hxfix : s * x * s⁻¹ = x := by
        have hcomm : x * s = s * x := Subgroup.mem_centralizer_singleton_iff.mp hxCs
        rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
      -- hence `k * c = k⁻¹ * c`
      have hx1 : k * c = k⁻¹ * c := by
        calc k * c = s * (k * c) * s⁻¹ := by rw [hkc, hxfix]
          _ = (s * k * s⁻¹) * (s * c * s⁻¹) := by group
          _ = k⁻¹ * c := by rw [hkinv, hsc]
      -- so `k = k⁻¹`
      have hkk : k = k⁻¹ := by
        calc k = k * c * c⁻¹ := by group
          _ = k⁻¹ * c * c⁻¹ := by rw [hx1]
          _ = k⁻¹ := by group
      -- and `k² = 1`, `k = 1` because `|X|` is odd
      have hk2 : k ^ 2 = 1 := by
        have h' : k * k = k * k⁻¹ := congrArg (fun z => k * z) hkk
        rw [mul_inv_cancel] at h'
        rwa [pow_two]
      have hk1 : k = 1 := by
        have hdvd2 : orderOf k ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hk2
        have hdvdX : orderOf k ∣ Nat.card X := Subgroup.orderOf_dvd_natCard X hkX
        have hdvd1 : orderOf k ∣ 1 := by
          have := Nat.dvd_gcd hdvd2 hdvdX
          rwa [Nat.Coprime.gcd_eq_one hcop] at this
        exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd1)
      have hxCQ : x ∈ Subgroup.centralizer ((Q : Subgroup G) : Set G) := by
        rw [← hkc, hk1, one_mul]
        exact hcCQ
      exact Subgroup.mem_inf.mpr ⟨hxX, hxCQ⟩
    · intro x hx
      obtain ⟨hxX, hxCQ⟩ := Subgroup.mem_inf.mp hx
      refine Subgroup.mem_inf.mpr ⟨hxX, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hxCQ s hsQ).symm
  refine ⟨hCommEq, hInvSetEq, ?_, hCentEq, ?_⟩
  · rw [hCommEq]; exact hcyc
  · have hsup : ⁅Q, X⁆ ⊔ (X ⊓ Subgroup.centralizer ((Q : Subgroup G) : Set G))
        = ⁅Q, X⁆ ⊔ (X ⊓ Subgroup.centralizer ({s} : Set G)) := by rw [hCentEq]
    exact h11i2.symm.trans hsup

end Work.CORE4
