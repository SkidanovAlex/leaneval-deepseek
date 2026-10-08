/-
**Simplicity of the Suzuki group `Sz(2^(2n+1))`** for `n ≥ 1`.

This completes the Suzuki family of the Bender–Suzuki classification.  The main results are

* `isPerfect_SzModel (n) (hn : 1 ≤ n) : Group.IsPerfect ↥(SzModel n)`,
* `isSimpleGroup_SzModel (n) (hn : 1 ≤ n) : IsSimpleGroup (SzModel n)`.

The argument follows the same four steps as for `PSU(3,2^n)` (see `Submission/PSU3/Simple.lean`):

1.  `Sz(2^(2n+1))` acts faithfully and 2-transitively on the `q² + 1` cosets of its Borel
    subgroup `B = U ⋊ T` (the Suzuki `2`-group together with the maximal torus).  The
    faithfulness `core(B) = 1` is `szBorelS_normalCore_eq_bot`, and 2-transitivity is
    `szModel_isMultiplyPretransitive_two`.

2.  The Borel subgroup lies in the commutator subgroup.  Indeed `T` is abelian and normalises
    `U`, so `[B,B] ≤ U` (`commutator_szBorel_le_szTwoGroup`); every element of `U` is a
    commutator `[t(x), v]` with `v ∈ U` (`szTwoGroup_le_commutator`: for `x` a generator of
    `Fˣ` the commutator map `v ↦ t(x) v t(x)⁻¹ v⁻¹` is injective by
    `szTg_commutator_szUg`, hence bijective on the finite `2`-group `U`); finally `t(x)² ∈ G'`
    because `[w, t(x)] = t(x)⁻²` and `t(x)` has odd order, so `t(x) ∈ G'`
    (`szTorusS_le_commutator`).

3.  `G ≦ B ⊔ ⟨w⟩` by the Bruhat decomposition `G = B ∪ BwB`, so `G/G' = ⟨w̄⟩` with `w̄² = 1`
    because `B ≤ G'`.  Hence `[G:G'] ≤ 2` while `[G:G']` divides the odd number
    `[G:B] = q² + 1`; therefore `G = G'` (`commutator_SzModel_eq_top`).

4.  If `1 ≠ N ⊴ G` then 2-transitivity makes `N` transitive on `G ⧸ B`, so `N ⊔ B = G`; hence
    `G = G' ≤ N ⊔ [B,B] ≤ N ⊔ U`, so `G ⧸ N` is a perfect quotient of the `2`-group `U`, hence
    trivial: `N = G`.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Models.Port.Sz.Faithful
import Submission.Work.Models.Port.Sz.TwoTransitive
import Submission.Work.Models.Port.Sz.StronglyEmbedded
import Submission.Work.Models.Port.Commons.GroupTheory.Commutator.commutator_le_sup_commutator_of_sup_eq_top
import Submission.Work.Models.Port.Commons.GroupTheory.Commutator.commutator_le_of_eq_sup_of_le_normalizer_of_commutator_le
import Submission.Work.Models.Port.Commons.GroupTheory.Commutator.commutator_eq_top_of_sup_zpowers_eq_top_of_odd_index
import Submission.Work.Models.Port.Commons.GroupTheory.IsPGroup.subsingleton_of_isPerfect

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 3200000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open Matrix LeanEval.GroupTheory.Defs
open scoped MatrixGroups commutatorElement Pointwise

namespace Submission.Sz

/-! ## The Borel subgroup is contained in the commutator subgroup of `Sz(q)` -/

/-- The torus of `Sz(2^(2n+1))` is abelian. -/
lemma szTg_comm (n : ℕ) (x y : (SzField n)ˣ) :
    szTg n x * szTg n y = szTg n y * szTg n x := by
  rw [szTg_mul, szTg_mul]
  exact congrArg (szTg n) (mul_comm x y)

lemma commutator_szTorus_le_bot (n : ℕ) : ⁅(szTgHom n).range, (szTgHom n).range⁆ ≤ ⊥ := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  rw [Subgroup.mem_bot, commutatorElement_def]
  have h1 : szTgHom n a * szTgHom n b = szTgHom n b * szTgHom n a := by
    simp only [szTgHom_apply]
    exact szTg_comm n a b
  calc szTgHom n a * szTgHom n b * (szTgHom n a)⁻¹ * (szTgHom n b)⁻¹
      = szTgHom n b * szTgHom n a * (szTgHom n a)⁻¹ * (szTgHom n b)⁻¹ := by rw [h1]
    _ = 1 := by group

/-- Every commutator of two elements of the Borel subgroup lies in the Suzuki 2-group. -/
theorem commutator_szBorel_le_szTwoGroup (n : ℕ) : ⁅szBorel n, szBorel n⁆ ≤ szTwoGroup n := by
  refine Commons.GroupTheory.Commutator.commutator_le_of_eq_sup_of_le_normalizer_of_commutator_le
    (szTwoGroup n) ((szTgHom n).range) (szBorel n) rfl (szBorel_le_normalizer_szTwoGroup n) ?_
  exact (commutator_szTorus_le_bot n).trans bot_le

/-- Every commutator of two elements of the Borel subgroup of `SzModel n` lies in the Suzuki
2-group. -/
theorem commutator_szBorelS_le (n : ℕ) : ⁅szBorelS n, szBorelS n⁆ ≤ szTwoGroupS n := by
  rw [szBorelS, szTwoGroupS, Subgroup.commutator_le]
  intro x hx y hy
  rw [Subgroup.mem_subgroupOf]
  have hcomm : ⁅(x : GL (Fin 4) (SzField n)), (y : GL (Fin 4) (SzField n))⁆ ∈ szTwoGroup n :=
    commutator_szBorel_le_szTwoGroup n (Subgroup.commutator_mem_commutator hx hy)
  simpa only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] using hcomm

/-! ## The commutator of a torus element with a root element -/

lemma szUg_inj (n : ℕ) {a b a' b' : SzField n} (h : szUg n a b = szUg n a' b') :
    a = a' ∧ b = b' := by
  have h' : (fun p : SzField n × SzField n => szUg n p.1 p.2) (a, b) =
      (fun p : SzField n × SzField n => szUg n p.1 p.2) (a', b') := h
  exact Prod.ext_iff.mp (szUg_injective n h')

/-- **The commutator `[t(x), u(a,b)]` of a torus element with a root element.** -/
theorem szTg_commutator_szUg (n : ℕ) (x : (SzField n)ˣ) (a b : SzField n) :
    szTg n x * szUg n a b * (szTg n x)⁻¹ * (szUg n a b)⁻¹ =
      szUg n (((x : SzField n) + 1) * a)
        (((x : SzField n) ^ (1 + 2 ^ (n + 1)) + 1) * b +
          ((x : SzField n) + 1) * a ^ (1 + 2 ^ (n + 1))) := by
  rw [szTg_conj_szUg, ← szUg_inv, szUg_mul]
  congr 1
  · ring
  · have hx : ((x : SzField n) * a) * a ^ (2 ^ (n + 1)) =
        (x : SzField n) * a ^ (1 + 2 ^ (n + 1)) := by
      rw [pow_add, pow_one]
      ring
    rw [hx]
    ring

/-- The map `v ↦ [t(x), v]` on the Suzuki 2-group. -/
noncomputable def szTwoCommutatorMap (n : ℕ) (x : (SzField n)ˣ) (v : ↥(szTwoGroup n)) :
    ↥(szTwoGroup n) where
  val := szTg n x * (v : GL (Fin 4) (SzField n)) * (szTg n x)⁻¹ *
    (v : GL (Fin 4) (SzField n))⁻¹
  property := by
    have h1 : szTg n x * (v : GL (Fin 4) (SzField n)) * (szTg n x)⁻¹ ∈ szTwoGroup n :=
      (Subgroup.le_normalizer_iff.mp (szTgHom_range_le_normalizer n) (szTg n x)
        ⟨x, rfl⟩ (v : GL (Fin 4) (SzField n)) v.2)
    exact (szTwoGroup n).mul_mem h1 ((szTwoGroup n).inv_mem v.2)

lemma szTwoCommutatorMap_coe (n : ℕ) (x : (SzField n)ˣ) (v : ↥(szTwoGroup n)) :
    (szTwoCommutatorMap n x v : GL (Fin 4) (SzField n)) =
      szTg n x * (v : GL (Fin 4) (SzField n)) * (szTg n x)⁻¹ *
        (v : GL (Fin 4) (SzField n))⁻¹ :=
  rfl

lemma szTwoCommutatorMap_injective (n : ℕ) (x : (SzField n)ˣ)
    (hB : (x : SzField n) + 1 ≠ 0) (hC : (x : SzField n) ^ (1 + 2 ^ (n + 1)) + 1 ≠ 0) :
    Function.Injective (szTwoCommutatorMap n x) := by
  intro v v' h
  obtain ⟨a, b, hv⟩ := v.2
  obtain ⟨a', b', hv'⟩ := v'.2
  have hgl : szTg n x * szUg n a b * (szTg n x)⁻¹ * (szUg n a b)⁻¹ =
      szTg n x * szUg n a' b' * (szTg n x)⁻¹ * (szUg n a' b')⁻¹ := by
    have h1 := congrArg Subtype.val h
    rw [szTwoCommutatorMap_coe, szTwoCommutatorMap_coe, hv, hv'] at h1
    exact h1
  rw [szTg_commutator_szUg, szTg_commutator_szUg] at hgl
  obtain ⟨h1, h2⟩ := szUg_inj n hgl
  have ha : a = a' := mul_left_cancel₀ hB h1
  have hb : b = b' := by
    rw [ha] at h2
    exact mul_left_cancel₀ hC (add_right_cancel h2)
  apply Subtype.ext
  rw [hv, hv', ha, hb]

lemma szTwoCommutatorMap_surjective (n : ℕ) (x : (SzField n)ˣ)
    (hB : (x : SzField n) + 1 ≠ 0) (hC : (x : SzField n) ^ (1 + 2 ^ (n + 1)) + 1 ≠ 0) :
    Function.Surjective (szTwoCommutatorMap n x) :=
  Finite.surjective_of_injective (szTwoCommutatorMap_injective n x hB hC)

/-- **Every element of the Suzuki 2-group is a commutator `[t(x), v]`.** -/
theorem szTwoGroup_le_commutator (n : ℕ) (hn : 1 ≤ n) :
    szTwoGroupS n ≤ commutator ↥(SzModel n) := by
  obtain ⟨x₀, hx₀⟩ := IsCyclic.exists_generator (α := (SzField n)ˣ)
  have hcard : Nat.card (SzField n)ˣ = 2 ^ (2 * n + 1) - 1 := by
    rw [Nat.card_units, card_szField n]
  have horder : orderOf x₀ = 2 ^ (2 * n + 1) - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hx₀, hcard]
  have hbig : 4 ≤ 2 ^ (2 * n + 1) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hx_ne_one : x₀ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at horder
    omega
  have hq'pos : 0 < 2 ^ (n + 1) + 1 := by positivity
  have hq'lt : 2 ^ (n + 1) + 1 < 2 ^ (2 * n + 1) - 1 := by
    have h3 : 2 ^ (2 * n + 1) = 2 ^ (n + 1) * 2 ^ n := by
      rw [← pow_add]; congr 1; omega
    have h4 : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h5 : 2 ≤ 2 ^ (n + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h5' : 2 < 2 ^ (n + 1) :=
      calc 2 = 2 ^ 1 := by norm_num
        _ < 2 ^ (n + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have h6 : 2 ^ (n + 1) + 2 < 2 ^ (n + 1) * 2 := by
      rw [show 2 ^ (n + 1) * 2 = 2 ^ (n + 1) + 2 ^ (n + 1) by ring]
      exact Nat.add_lt_add_left h5' _
    have h8 : 2 ^ (n + 1) + 2 < 2 ^ (2 * n + 1) := by
      rw [h3]
      exact lt_of_lt_of_le h6 (Nat.mul_le_mul_left _ h4)
    exact Nat.lt_sub_iff_add_lt.mpr h8
  have hB : (x₀ : SzField n) + 1 ≠ 0 := by
    intro h
    apply hx_ne_one
    apply Units.ext
    have h' := add_eq_zero_iff_eq_neg.mp h
    simpa [CharTwo.neg_eq] using h'
  have hC : (x₀ : SzField n) ^ (1 + 2 ^ (n + 1)) + 1 ≠ 0 := by
    intro h
    have h1 : (x₀ : SzField n) ^ (1 + 2 ^ (n + 1)) = 1 := by
      have h' := add_eq_zero_iff_eq_neg.mp h
      simpa [CharTwo.neg_eq] using h'
    have h2 : x₀ ^ (1 + 2 ^ (n + 1)) = 1 := Units.ext h1
    have hdvd : orderOf x₀ ∣ (1 + 2 ^ (n + 1)) := orderOf_dvd_iff_pow_eq_one.mpr h2
    rw [horder] at hdvd
    have hpos : 0 < 1 + 2 ^ (n + 1) := by positivity
    have hlt : 1 + 2 ^ (n + 1) < 2 ^ (2 * n + 1) - 1 := by omega
    exact absurd (Nat.le_of_dvd hpos hdvd) (not_le.mpr hlt)
  intro u hu
  rw [szTwoGroupS, Subgroup.mem_subgroupOf] at hu
  obtain ⟨v, hv⟩ := szTwoCommutatorMap_surjective n x₀ hB hC ⟨u, hu⟩
  have hval : szTg n x₀ * (v : GL (Fin 4) (SzField n)) * (szTg n x₀)⁻¹ *
      (v : GL (Fin 4) (SzField n))⁻¹ = (u : GL (Fin 4) (SzField n)) := by
    have h1 := congrArg Subtype.val hv
    simpa only [szTwoCommutatorMap_coe] using h1
  have hcomm : ⁅(⟨szTg n x₀, szTg_mem_szModel n x₀⟩ : ↥(SzModel n)),
      (⟨(v : GL (Fin 4) (SzField n)), szTwoGroup_le_szModel n v.2⟩ : ↥(SzModel n))⁆ = u := by
    apply Subtype.ext
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hval
  rw [← hcomm]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-! ## The torus is contained in the commutator subgroup of `Sz(q)` -/

theorem szTorusS_le_commutator (n : ℕ) (hn : 1 ≤ n) :
    (szTgHom n).range.subgroupOf (SzModel n) ≤ commutator ↥(SzModel n) := by
  intro t ht
  rw [Subgroup.mem_subgroupOf] at ht
  obtain ⟨x, hx⟩ := ht
  -- `x ^ (q - 1) = 1`
  have hcard : Nat.card (SzField n)ˣ = 2 ^ (2 * n + 1) - 1 := by
    rw [Nat.card_units, card_szField n]
  have hxpow : x ^ (2 ^ (2 * n + 1) - 1) = 1 := by
    rw [← hcard]
    exact (orderOf_dvd_iff_pow_eq_one).mp (orderOf_dvd_natCard x)
  set t' : ↥(SzModel n) := ⟨szTg n x, szTg_mem_szModel n x⟩ with ht'
  have htq : t' ^ (2 ^ (2 * n + 1) - 1) = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    show (szTg n x) ^ (2 ^ (2 * n + 1) - 1) = (1 : GL (Fin 4) (SzField n))
    rw [← szTgHom_apply, ← map_pow, hxpow, map_one]
  have hwt : szWgM n * t' * (szWgM n)⁻¹ = t'⁻¹ := by
    apply Subtype.ext
    show szWg n * szTg n x * (szWg n)⁻¹ = (szTg n x)⁻¹
    rw [szWg_inv_eq, szWg_conj_szTg n x, szTg_inv]
  have hcomm : ⁅szWgM n, t'⁆ = t'⁻¹ * t'⁻¹ := by
    rw [commutatorElement_def, hwt]
  have hsq : t' ^ 2 = ⁅szWgM n, t'⁆⁻¹ := by
    rw [hcomm]
    group
  have h2 : t' ^ 2 ∈ commutator ↥(SzModel n) := by
    rw [hsq]
    exact (commutator ↥(SzModel n)).inv_mem
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
  have hteq : t' = t := Subtype.ext hx
  have hfin : t' = (t' ^ 2) ^ (2 ^ (2 * n)) := by
    have h1 : (t' ^ 2) ^ (2 ^ (2 * n)) = t' ^ (2 ^ (2 * n + 1)) := by
      rw [← pow_mul]
      congr 1
      rw [mul_comm, ← pow_succ]
    rw [h1]
    have h2 : 2 ^ (2 * n + 1) = 2 ^ (2 * n + 1) - 1 + 1 :=
      (Nat.sub_add_cancel (Nat.one_le_two_pow (n := 2 * n + 1))).symm
    rw [h2, pow_add, pow_one, htq, one_mul]
  have hthis : t' ∈ commutator ↥(SzModel n) := by
    rw [hfin]
    exact (commutator ↥(SzModel n)).pow_mem h2 (2 ^ (2 * n))
  exact hteq ▸ hthis


/-! ## `Sz(2^(2n+1))` is perfect -/

theorem commutator_SzModel_eq_top (n : ℕ) (hn : 1 ≤ n) : commutator ↥(SzModel n) = ⊤ := by
  set K := commutator ↥(SzModel n) with hK
  have hU : szTwoGroupS n ≤ K := szTwoGroup_le_commutator n hn
  have hT : (szTgHom n).range.subgroupOf (SzModel n) ≤ K := szTorusS_le_commutator n hn
  have hB : szBorelS n ≤ K := by
    rw [szBorelS, szBorel, Subgroup.subgroupOf_sup (szTwoGroup_le_szModel n)
      (szTgHom_range_le_szModel n)]
    exact sup_le hU hT
  have hw2 : szWgM n ^ 2 = 1 := by
    rw [pow_two]
    exact Subtype.ext (szWg_mul_self n)
  have hgen : szBorelS n ⊔ Subgroup.zpowers (szWgM n) = ⊤ := by
    apply le_antisymm le_top
    intro g _
    rcases sz_cover n g with hg | ⟨b₁, b₂, hg⟩
    · exact Subgroup.mem_sup_left hg
    · rw [hg]
      have h1 : (b₁ : SzModel n) * szWgM n ∈ szBorelS n ⊔ Subgroup.zpowers (szWgM n) :=
        Subgroup.mul_mem_sup b₁.2 (Subgroup.mem_zpowers (szWgM n))
      exact (szBorelS n ⊔ Subgroup.zpowers (szWgM n)).mul_mem h1 (Subgroup.mem_sup_left b₂.2)
  have hodd : Odd (szBorelS n).index := by
    rw [card_szBorelS_index n, card_szField n]
    have hsq : (2 ^ (2 * n + 1)) ^ 2 = 2 ^ (4 * n + 2) := by
      rw [← pow_mul]; congr 1; ring
    rw [hsq]
    exact odd_two_pow_add_one (4 * n + 1)
  exact Commons.GroupTheory.Commutator.commutator_eq_top_of_sup_zpowers_eq_top_of_odd_index
    (szBorelS n) (szWgM n) hw2 hgen hB hodd

/-- **`Sz(2^(2n+1))` is perfect** for `n ≥ 1`. -/
theorem isPerfect_SzModel (n : ℕ) (hn : 1 ≤ n) : Group.IsPerfect ↥(SzModel n) :=
  ⟨commutator_SzModel_eq_top n hn⟩

/-! ## Simplicity -/

theorem nontrivial_SzModel (n : ℕ) : Nontrivial (SzModel n) := by
  refine ⟨⟨szWgM n, 1, fun h => ?_⟩⟩
  exact szWgM_notMem n (h ▸ Subgroup.one_mem (szBorelS n))

/-- **`Sz(2^(2n+1))` is simple** for `n ≥ 1`. -/
theorem isSimpleGroup_SzModel (n : ℕ) (hn : 1 ≤ n) : IsSimpleGroup (SzModel n) := by
  haveI : Nontrivial (SzModel n) := nontrivial_SzModel n
  haveI hfaith : FaithfulSMul (SzModel n) ((SzModel n) ⧸ szBorelS n) := szBorelS_faithfulSMul n
  haveI h2 : MulAction.IsMultiplyPretransitive (SzModel n) ((SzModel n) ⧸ szBorelS n) 2 :=
    szModel_isMultiplyPretransitive_two n
  haveI hperf : Group.IsPerfect ↥(SzModel n) := isPerfect_SzModel n hn
  apply IsSimpleGroup.mk
  intro N hN
  by_cases hbot : N = ⊥
  · exact Or.inl hbot
  · refine Or.inr ?_
    haveI : N.Normal := hN
    have htrans := sz_normal_isPretransitive n N hN hbot
    have hsup : N ⊔ szBorelS n = ⊤ := by
      rw [eq_top_iff]
      intro g _
      obtain ⟨n', hn'⟩ := htrans (((g : SzModel n)) : SzModel n ⧸ szBorelS n)
        (((1 : SzModel n)) : SzModel n ⧸ szBorelS n)
      have hsm : ((n' : SzModel n) * g) • (((1 : SzModel n)) : SzModel n ⧸ szBorelS n)
          = (n' : SzModel n) • (((g : SzModel n)) : SzModel n ⧸ szBorelS n) := by
        rw [mul_smul, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
      have hmem : ((n' : SzModel n) * g) ∈ MulAction.stabilizer (SzModel n)
          (((1 : SzModel n)) : SzModel n ⧸ szBorelS n) := by
        rw [MulAction.mem_stabilizer_iff, hsm]
        exact hn'
      have h2' : ((n' : SzModel n) * g) ∈ szBorelS n := by
        rwa [MulAction.stabilizer_quotient] at hmem
      have h3 : g = (n' : SzModel n)⁻¹ * ((n' : SzModel n) * g) := by group
      rw [h3]
      exact Subgroup.mul_mem_sup (N.inv_mem n'.2) h2'
    have hcomm_le : commutator (SzModel n) ≤ N ⊔ szTwoGroupS n :=
      (Commons.GroupTheory.Commutator.commutator_le_sup_commutator_of_sup_eq_top N (szBorelS n)
        hsup).trans (sup_le_sup_left (commutator_szBorelS_le n) N)
    have htop : (⊤ : Subgroup (SzModel n)) ≤ N ⊔ szTwoGroupS n :=
      (le_of_eq hperf.commutator_eq_top.symm).trans hcomm_le
    have hsupU : N ⊔ szTwoGroupS n = ⊤ := top_le_iff.mp htop
    have hU2 : IsPGroup 2 ↥(szTwoGroupS n) := szTwoGroupS_isPGroup n
    have hQ2 : IsPGroup 2 (SzModel n ⧸ N) := by
      have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp (szTwoGroupS n).subtype) := by
        intro y
        obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N y
        have hg : g ∈ (↑(N ⊔ szTwoGroupS n) : Set (SzModel n)) := by rw [hsupU]; trivial
        rw [Subgroup.normal_mul N (szTwoGroupS n), Set.mem_mul] at hg
        obtain ⟨n'', hn'', u, hu, hnu⟩ := hg
        refine ⟨⟨u, hu⟩, ?_⟩
        have hn1' : (QuotientGroup.mk' N) n'' = 1 := (QuotientGroup.eq_one_iff n'').mpr hn''
        show (QuotientGroup.mk' N) u = (QuotientGroup.mk' N) g
        rw [← hnu, map_mul, hn1', one_mul]
      exact hU2.of_surjective _ hsurj
    haveI : Group.IsPerfect (SzModel n ⧸ N) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
    haveI : Finite (SzModel n ⧸ N) :=
      Finite.of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
    haveI hpr : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hsingle : Subsingleton (SzModel n ⧸ N) :=
      Commons.GroupTheory.IsPGroup.subsingleton_of_isPerfect hQ2 inferInstance
    rw [Subgroup.eq_top_iff']
    intro y
    exact (QuotientGroup.eq_one_iff y).mp
      (Subsingleton.elim ((y : SzModel n) : SzModel n ⧸ N) 1)

end Submission.Sz
