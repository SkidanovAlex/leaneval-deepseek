/-
**The rank-one `(B, N)`-pair of `Sz(2^(2n+1))`: `N_G(T) = T ⋊ ⟨w⟩`.**

The Weyl element `w` inverts the maximal torus `T` (`szWg_conj_szTg`), so `T ⊔ ⟨w⟩ ≤ N_G(T)`.
Conversely, if `g` normalises `T` then the point `g • α` of the Bender action (where
`α = B ∈ Sz(q)/B`) is fixed by `T`.  Since `U` acts *regularly* on `Ω ∖ {α}` and `T` fixes the
second `T`-fixed point `β = w • α` (which exists because `B ⊓ Bʷ = T`), a `T`-fixed point
`x = u • β` with `u ∈ U` forces `t u t⁻¹ = u` for every `t ∈ T`.  The explicit commutation formula
`t(x)·u(a,b)·t(x)⁻¹ = u(x·a, x^(1+2^(n+1))·b)` shows that no non-trivial element of `U` is
centralised by `T` (using `gcd(2^(n+1)+1, 2^(2n+1)-1) = 1`), so `u = 1` and `x = β`.  Hence every
`T`-fixed point of `Ω` is `α` or `β`, and the usual argument gives `N_G(T) = T ⊔ ⟨w⟩`.

This is the last of the rank-one `(B,N)`-pair axioms for the Suzuki family.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Models.Port.Sz.Main
import Submission.Work.Models.Port.Sz.SuzukiCondition
import Submission.Work.Models.Port.Sz.Involutions
import Submission.Work.Models.Port.Sz.Borel
import Submission.Work.Models.Port.Sz.Bruhat
import Submission.Work.Models.Port.Sz.TwoTransitive
import Submission.Work.Models.Port.Commons.NumberTheory.Nat.coprime_two_pow_succ_add_one_two_pow_sub_one
import Submission.Work.Models.Port.PSU3.Bruhat

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

open Matrix LeanEval.GroupTheory.Defs
open scoped Pointwise

namespace Submission.Sz

/-- The torus element `t(x)` as an element of `SzModel n`. -/
noncomputable def szTgM (n : ℕ) (x : (SzField n)ˣ) : SzModel n :=
  ⟨szTgHom n x, szTg_mem_szModel n x⟩

@[simp] lemma szTgM_coe (n : ℕ) (x : (SzField n)ˣ) :
    ((szTgM n x : SzModel n) : GL (Fin 4) (SzField n)) = szTg n x := rfl

lemma szTgM_mem_szTS (n : ℕ) (x : (SzField n)ˣ) : szTgM n x ∈ szTS n :=
  Subgroup.mem_subgroupOf.mpr ⟨x, by simp [szTgM]⟩

lemma szTS_le_szBorelS (n : ℕ) : szTS n ≤ szBorelS n := by
  rw [szBorelS_eq_sup]; exact le_sup_right

lemma szWgM_notMem_szBorelS (n : ℕ) : szWgM n ∉ szBorelS n := fun h =>
  szWg_notMem_szBorel n (Subgroup.mem_subgroupOf.mp h)

/-- The Weyl element inverts the torus. -/
lemma szWgM_conj_szTgM (n : ℕ) (x : (SzField n)ˣ) :
    szWgM n * szTgM n x * (szWgM n)⁻¹ = szTgM n x⁻¹ := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, szTgM_coe, szWgM]
  rw [szWg_inv_eq n]
  exact szWg_conj_szTg n x

/-- The Weyl element normalises the torus. -/
lemma szWgM_mem_normalizer_szTS (n : ℕ) :
    szWgM n ∈ Subgroup.normalizer (szTS n : Set (SzModel n)) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_
    (le_of_eq (Subgroup.card_map_of_injective (MulEquiv.injective _)).symm)
  rintro y ⟨k, hk, rfl⟩
  have hk' : (k : GL (Fin 4) (SzField n)) ∈ (szTgHom n).range := Subgroup.mem_subgroupOf.mp hk
  obtain ⟨x, hx⟩ := hk'
  have hkx : szTgM n x = k := Subtype.ext (by simpa [szTgM] using hx)
  change szWgM n * k * (szWgM n)⁻¹ ∈ szTS n
  rw [← hkx, szWgM_conj_szTgM]
  exact szTgM_mem_szTS n x⁻¹

/-- **No non-trivial element of the Suzuki `2`-group is centralised by the torus.** -/
lemma eq_one_of_mem_szTwoGroupS_of_centralizes_szTS (n : ℕ) (hn : 1 ≤ n) {u : SzModel n}
    (hu : u ∈ szTwoGroupS n) (hcent : ∀ t ∈ szTS n, u * t = t * u) : u = 1 := by
  -- a non-identity torus element
  haveI : Fintype (SzField n)ˣ := Fintype.ofFinite _
  have hcard : 1 < Fintype.card (SzField n)ˣ := by
    rw [← Nat.card_eq_fintype_card, Nat.card_units (SzField n), card_szField]
    have h2 : 3 ≤ 2 ^ (2 * n + 1) := by
      calc 3 ≤ 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (2 * n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨x, hx⟩ := Fintype.exists_ne_of_one_lt_card hcard (1 : (SzField n)ˣ)
  have ht : szTgM n x ∈ szTS n := szTgM_mem_szTS n x
  have hcomm := hcent _ ht
  obtain ⟨a, b, huab⟩ := Subgroup.mem_subgroupOf.mp hu
  -- transport to `GL`
  have hcommGL : szUg n a b * szTg n x = szTg n x * szUg n a b := by
    have h := congrArg (fun z : SzModel n => (z : GL (Fin 4) (SzField n))) hcomm
    simp only [Subgroup.coe_mul, szTgM_coe] at h
    rw [huab] at h
    exact h
  have htut : szTg n x * szUg n a b * (szTg n x)⁻¹ = szUg n a b := by
    rw [← hcommGL, mul_assoc, mul_inv_cancel, mul_one]
  have hu' : szUg n ((x : SzField n) * a) ((x : SzField n) ^ (1 + 2 ^ (n + 1)) * b) =
      szUg n a b := (szTg_conj_szUg n x a b).symm.trans htut
  have hpair : ((x : SzField n) * a, (x : SzField n) ^ (1 + 2 ^ (n + 1)) * b) = (a, b) :=
    szUg_injective n hu'
  have h1 : (x : SzField n) * a = a := congrArg Prod.fst hpair
  have h2 : (x : SzField n) ^ (1 + 2 ^ (n + 1)) * b = b := congrArg Prod.snd hpair
  have hx1 : (x : SzField n) ≠ 1 := fun h => hx (Units.ext h)
  -- `x^k ≠ 1` where `k = 1 + 2^(n+1)`, because `k` is coprime to `|Fˣ| = 2^(2n+1) - 1`
  have hxk : (x : SzField n) ^ (1 + 2 ^ (n + 1)) ≠ 1 := by
    intro h
    have hdvd1 : orderOf x ∣ 1 + 2 ^ (n + 1) := by
      rw [orderOf_dvd_iff_pow_eq_one]
      exact Units.ext (by simpa using h)
    have hdvd2 : orderOf x ∣ 2 ^ (2 * n + 1) - 1 := by
      have := orderOf_dvd_natCard x
      rwa [Nat.card_units, card_szField] at this
    have hcop := Commons.NumberTheory.Nat.coprime_two_pow_succ_add_one_two_pow_sub_one n
    have hone : orderOf x = 1 := by
      have hg : orderOf x ∣ Nat.gcd (1 + 2 ^ (n + 1)) (2 ^ (2 * n + 1) - 1) :=
        Nat.dvd_gcd hdvd1 hdvd2
      rw [show Nat.gcd (1 + 2 ^ (n + 1)) (2 ^ (2 * n + 1) - 1) = 1 from by
        rw [Nat.add_comm]; exact hcop] at hg
      exact Nat.dvd_one.mp hg
    exact hx (orderOf_eq_one_iff.mp hone)
  have ha0 : a = 0 := by
    have hz : ((x : SzField n) - 1) * a = 0 := by
      rw [sub_mul, one_mul, h1, sub_self]
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hx1)
  have hb0 : b = 0 := by
    have hz : ((x : SzField n) ^ (1 + 2 ^ (n + 1)) - 1) * b = 0 := by
      rw [sub_mul, one_mul, h2, sub_self]
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hxk)
  refine Subtype.ext ?_
  rw [huab, ha0, hb0, szUg_zero]
  rfl

/-- The base point of the Bender action of `Sz(2^(2n+1))`. -/
noncomputable abbrev szPtBase (n : ℕ) : SzModel n ⧸ szBorelS n :=
  ((1 : SzModel n) : SzModel n ⧸ szBorelS n)

/-- The second `T`-fixed point `β = w • α` of the Bender action. -/
noncomputable abbrev szPtWeyl (n : ℕ) : SzModel n ⧸ szBorelS n := szWgM n • szPtBase n

/-- The second `T`-fixed point of the Bender action: `β = w • α`. -/
lemma szTS_fixes_szPtWeyl (n : ℕ) (t : SzModel n) (ht : t ∈ szTS n) :
    t • szPtWeyl n = szPtWeyl n := by
  have htBw : t ∈ (szBorelS n).map (MulAut.conj (szWgM n)).toMonoidHom := by
    have hmem : t ∈ szBorelS n ⊓ (szBorelS n).map (MulAut.conj (szWgM n)).toMonoidHom := by
      rw [szBorelS_inf_map_conj_eq n]; exact ht
    exact (Subgroup.mem_inf.mp hmem).2
  rw [← MulAction.mem_stabilizer_iff,
    MulAction.stabilizer_smul_eq_stabilizer_map_conj (szWgM n) (szPtBase n),
    MulAction.stabilizer_quotient]
  exact htBw

/-- The base point is fixed by `T`. -/
lemma szTS_fixes_szPtBase (n : ℕ) (t : SzModel n) (ht : t ∈ szTS n) :
    t • szPtBase n = szPtBase n := by
  rw [← MulAction.mem_stabilizer_iff, MulAction.stabilizer_quotient]
  exact szTS_le_szBorelS n ht

/-- **The `T`-fixed points of the Bender action are the base point and `β = w • α`.** -/
lemma eq_szPtBase_or_eq_szPtWeyl_of_forall_szTS_fixes (n : ℕ) (hn : 1 ≤ n)
    {x : SzModel n ⧸ szBorelS n} (hx : ∀ t ∈ szTS n, t • x = x) :
    x = szPtBase n ∨ x = szPtWeyl n := by
  by_cases hx0 : x = szPtBase n
  · exact Or.inl hx0
  · right
    have hβne : szPtWeyl n ≠ szPtBase n := by
      intro h
      refine szWgM_notMem_szBorelS n ?_
      rwa [← MulAction.mem_stabilizer_iff, MulAction.stabilizer_quotient] at h
    obtain ⟨u, hu⟩ := szTwoGroupS_exists_smul_eq_of_ne n hn (x := szPtWeyl n) (y := x) hβne hx0
    -- `U ∋ u' ↦ u' • β` is injective
    have hinj : ∀ u₁ u₂ : ↥(szTwoGroupS n),
        (u₁ : SzModel n) • szPtWeyl n = (u₂ : SzModel n) • szPtWeyl n → u₁ = u₂ := by
      intro u₁ u₂ h
      by_contra hne
      have hcoe : ((u₁⁻¹ * u₂ : ↥(szTwoGroupS n)) : SzModel n) =
          ((u₁ : SzModel n))⁻¹ * (u₂ : SzModel n) := by simp
      have h1 : ((u₁⁻¹ * u₂ : ↥(szTwoGroupS n)) : SzModel n) • szPtWeyl n = szPtWeyl n := by
        rw [hcoe, mul_smul, ← h, inv_smul_smul]
      refine hβne (szTwoGroupS_fixedPoint_eq_one n hn (u₁⁻¹ * u₂) ?_ h1)
      intro hc
      exact hne (inv_mul_eq_one.mp hc)
    have hcent : ∀ t ∈ szTS n, (u : SzModel n) * t = t * (u : SzModel n) := by
      intro t ht
      have hβT : t • szPtWeyl n = szPtWeyl n := szTS_fixes_szPtWeyl n t ht
      have hβinv : t⁻¹ • szPtWeyl n = szPtWeyl n := by
        calc t⁻¹ • szPtWeyl n = t⁻¹ • (t • szPtWeyl n) := by rw [hβT]
          _ = szPtWeyl n := inv_smul_smul t (szPtWeyl n)
      have hfix : t • ((u : SzModel n) • szPtWeyl n) = (u : SzModel n) • szPtWeyl n := by
        rw [hu]; exact hx t ht
      have hconj : (t * (u : SzModel n) * t⁻¹) • szPtWeyl n = (u : SzModel n) • szPtWeyl n := by
        calc (t * (u : SzModel n) * t⁻¹) • szPtWeyl n
            = (t * (u : SzModel n)) • (t⁻¹ • szPtWeyl n) := by rw [mul_smul, mul_smul]
          _ = (t * (u : SzModel n)) • szPtWeyl n := by rw [hβinv]
          _ = t • ((u : SzModel n) • szPtWeyl n) := by rw [mul_smul]
          _ = (u : SzModel n) • szPtWeyl n := hfix
      have hmemU : t * (u : SzModel n) * t⁻¹ ∈ szTwoGroupS n :=
        (Subgroup.le_normalizer_iff.mp (szTS_le_normalizer_szTwoGroupS n)) t ht
          (u : SzModel n) u.2
      have heq : (⟨t * (u : SzModel n) * t⁻¹, hmemU⟩ : ↥(szTwoGroupS n)) = u :=
        hinj ⟨t * (u : SzModel n) * t⁻¹, hmemU⟩ u hconj
      have htu : t * (u : SzModel n) * t⁻¹ = (u : SzModel n) := congrArg Subtype.val heq
      have h2 : t * (u : SzModel n) * t⁻¹ * t = (u : SzModel n) * t :=
        congrArg (fun z : SzModel n => z * t) htu
      rw [show t * (u : SzModel n) * t⁻¹ * t = t * (u : SzModel n) by group] at h2
      exact h2.symm
    have hu1 : (u : SzModel n) = 1 :=
      eq_one_of_mem_szTwoGroupS_of_centralizes_szTS n hn u.2 hcent
    rw [← hu, hu1, one_smul]

/-- **The rank-one `(B,N)`-pair relation `N_G(T) = T ⊔ ⟨w⟩`** for `Sz(2^(2n+1))`: the
normalizer of the maximal torus is generated by the torus and the Weyl element. -/
theorem normalizer_szTS_eq_sup_zpowers_szWgM (n : ℕ) (hn : 1 ≤ n) :
    Subgroup.normalizer (szTS n : Set (SzModel n)) =
      szTS n ⊔ Subgroup.zpowers (szWgM n) := by
  have hTfix : ∀ g ∈ Subgroup.normalizer (szTS n : Set (SzModel n)),
      ∀ t ∈ szTS n, t • (g • szPtBase n) = g • szPtBase n := by
    intro g hg t ht
    have ht' : t ∈ (szTS n).map (MulAut.conj g).toMonoidHom :=
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp hg).symm ▸ ht
    obtain ⟨t', ht'mem, ht'eq⟩ := Subgroup.mem_map.mp ht'
    rw [← ht'eq]
    change (g * t' * g⁻¹) • (g • szPtBase n) = g • szPtBase n
    rw [mul_smul, mul_smul, inv_smul_smul, szTS_fixes_szPtBase n t' ht'mem]
  -- `N(T) ∩ B = T`
  have hNB : ∀ g ∈ Subgroup.normalizer (szTS n : Set (SzModel n)),
      g ∈ szBorelS n → g ∈ szTS n := by
    intro g hg hgB
    have hgB' : g ∈ szTwoGroupS n ⊔ szTS n := by
      rw [szBorelS_eq_sup n] at hgB
      exact hgB
    obtain ⟨u, hu, t, ht, hut⟩ := Submission.PSU3.mem_sup_mul (szTwoGroupS n) (szTS n)
      (szTS_le_normalizer_szTwoGroupS n) hgB'
    have huN : u ∈ Subgroup.normalizer (szTS n : Set (SzModel n)) := by
      have h1 : g * t⁻¹ ∈ Subgroup.normalizer (szTS n : Set (SzModel n)) :=
        (Subgroup.normalizer _).mul_mem hg
          ((Subgroup.normalizer _).inv_mem (Subgroup.le_normalizer ht))
      rw [hut, mul_assoc, mul_inv_cancel, mul_one] at h1
      exact h1
    have hcent : ∀ t' ∈ szTS n, u * t' = t' * u := by
      intro t' ht'
      have h1 : u * t' * u⁻¹ ∈ szTS n :=
        (Subgroup.mem_normalizer_iff.mp huN t').mp ht'
      have h2 : t' * u⁻¹ * t'⁻¹ ∈ szTwoGroupS n :=
        (Subgroup.le_normalizer_iff.mp (szTS_le_normalizer_szTwoGroupS n)) t' ht' u⁻¹
          (Subgroup.inv_mem _ hu)
      have h3 : u * t' * u⁻¹ * t'⁻¹ ∈ szTwoGroupS n := by
        have hm := Subgroup.mul_mem (szTwoGroupS n) hu h2
        simpa only [mul_assoc] using hm
      have h4 : u * t' * u⁻¹ * t'⁻¹ ∈ szTS n :=
        Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ ht')
      have h5 : u * t' * u⁻¹ * t'⁻¹ = 1 := by
        have hmem : u * t' * u⁻¹ * t'⁻¹ ∈ szTwoGroupS n ⊓ szTS n :=
          Subgroup.mem_inf.mpr ⟨h3, h4⟩
        rwa [szTS_inf_szTwoGroupS n, Subgroup.mem_bot] at hmem
      have h6 : u * t' * u⁻¹ = t' := by
        calc u * t' * u⁻¹ = u * t' * u⁻¹ * t'⁻¹ * t' := by group
          _ = 1 * t' := by rw [h5]
          _ = t' := by group
      calc u * t' = (u * t' * u⁻¹) * u := by group
        _ = t' * u := by rw [h6]
    have hu1 : u = 1 := eq_one_of_mem_szTwoGroupS_of_centralizes_szTS n hn hu hcent
    rw [hut, hu1, one_mul]
    exact ht
  refine le_antisymm ?_ (sup_le Subgroup.le_normalizer
    ((Subgroup.zpowers_le).mpr (szWgM_mem_normalizer_szTS n)))
  intro g hg
  rcases eq_szPtBase_or_eq_szPtWeyl_of_forall_szTS_fixes n hn (hTfix g hg) with h | h
  · have hgB : g ∈ szBorelS n := by
      rwa [← MulAction.mem_stabilizer_iff, MulAction.stabilizer_quotient] at h
    exact Subgroup.mem_sup_left (hNB g hg hgB)
  · have hwginv : (szWgM n)⁻¹ * g ∈ Subgroup.normalizer (szTS n : Set (SzModel n)) :=
      (Subgroup.normalizer _).mul_mem
        ((Subgroup.normalizer _).inv_mem (szWgM_mem_normalizer_szTS n)) hg
    have hwgB : (szWgM n)⁻¹ * g ∈ szBorelS n := by
      have h1 : ((szWgM n)⁻¹ * g) • szPtBase n = szPtBase n := by
        rw [mul_smul, h]
        exact inv_smul_smul (szWgM n) (szPtBase n)
      rwa [← MulAction.mem_stabilizer_iff, MulAction.stabilizer_quotient] at h1
    have hmemT : (szWgM n)⁻¹ * g ∈ szTS n := hNB _ hwginv hwgB
    have hge : g = szWgM n * ((szWgM n)⁻¹ * g) := by group
    have hmem' : szWgM n * ((szWgM n)⁻¹ * g) ∈ Subgroup.zpowers (szWgM n) ⊔ szTS n :=
      Subgroup.mul_mem_sup (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩) hmemT
    rw [hge, sup_comm]
    exact hmem'

end Submission.Sz
