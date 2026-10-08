/-
The action of `Sz(2^(2n+1))` on the cosets of its Borel subgroup `B` is faithful: the normal
core of `B` is trivial.

Strategy: an element of `core_G(B)` lies in `B` and in every conjugate of `B`; since
`B ⊓ B^w` is a conjugate of the torus `T` (of odd order), the core has odd order.  On the other
hand the core centralises the Suzuki 2-group `U` (because `U ⊓ core ≤ U` is a `2`-group while
`core` has odd order), and any element of `B` centralising `U` already lies in `U` -- this is
the key computation: conjugation by an element of `U` preserves the first "root" coordinate
`u(a,b) ↦ u(a,*)`, whereas `t(x)` scales it by `x`, so only `t(x) = 1` can centralise.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Models.Port.Sz.TwoTransitive
import Submission.Work.Models.Port.Sz.StronglyEmbedded
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.centralizer_le_of_isPGroup_le
import Submission.Work.Models.Port.Commons.GroupTheory.GroupAction.isPretransitive_normalSubgroup_of_faithful_twoTransitive

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

open Matrix LeanEval.GroupTheory.Defs
open scoped Pointwise

namespace Submission.Sz

/-- An element of the Borel subgroup factors as `u * t` with `u` in the Suzuki 2-group and
`t` in the torus. -/
lemma szBorel_mem_decomp (n : ℕ) {b : GL (Fin 4) (SzField n)} (hb : b ∈ szBorel n) :
    ∃ u ∈ szTwoGroup n, ∃ t ∈ (szTgHom n).range, u * t = b := by
  have h := Subgroup.coe_mul_of_right_le_normalizer_left (szTwoGroup n) (szTgHom n).range
    (szTgHom_range_le_normalizer n)
  have hb' : b ∈ (szTwoGroup n ⊔ (szTgHom n).range : Subgroup (GL (Fin 4) (SzField n))) := by
    rw [szBorel] at hb; exact hb
  have hb'' : b ∈ ((szTwoGroup n : Set (GL (Fin 4) (SzField n))) *
      ((szTgHom n).range : Set (GL (Fin 4) (SzField n)))) := by
    rw [← h]; exact hb'
  exact Set.mem_mul.mp hb''

/-- Conjugation by an element of the Suzuki 2-group preserves the first root coordinate. -/
lemma szUg_conj_fst (n : ℕ) (a b c d : SzField n) :
    ∃ e : SzField n, szUg n a b * szUg n c d * (szUg n a b)⁻¹ = szUg n c e := by
  refine ⟨(b + d + a * c ^ (2 ^ (n + 1))) + (b + a ^ (1 + 2 ^ (n + 1))) +
    (a + c) * a ^ (2 ^ (n + 1)), ?_⟩
  have hcancel : (a + c) + a = c := by
    rw [add_assoc, add_comm c a, ← add_assoc, ← two_mul, szField_two_eq_zero n, zero_mul, zero_add]
  rw [szUg_mul n a b c d, ← szUg_inv n a b,
    szUg_mul n (a + c) (b + d + a * c ^ (2 ^ (n + 1))) a (b + a ^ (1 + 2 ^ (n + 1))),
    hcancel]

/-- An element of the Borel subgroup that centralises the Suzuki 2-group already lies in the
Suzuki 2-group. -/
theorem szBorel_centralizer_subset (n : ℕ) {b : GL (Fin 4) (SzField n)} (hb : b ∈ szBorel n)
    (hcent : ∀ u ∈ szTwoGroup n, b * u * b⁻¹ = u) : b ∈ szTwoGroup n := by
  obtain ⟨u, hu, t, ht, hut⟩ := szBorel_mem_decomp n hb
  obtain ⟨x, rfl⟩ := ht
  obtain ⟨a0, b0, rfl⟩ := hu
  -- From `u * t` centralising `U`, the torus part conjugates by the inverse of the `U` part.
  have htu : ∀ y ∈ szTwoGroup n, szTg n x * y * (szTg n x)⁻¹ =
      szUg n a0 (b0 + a0 ^ (1 + 2 ^ (n + 1))) * y *
        (szUg n a0 (b0 + a0 ^ (1 + 2 ^ (n + 1))))⁻¹ := by
    intro y hy
    have h1 := hcent y hy
    rw [← hut] at h1
    rw [_root_.mul_inv_rev] at h1
    have h2 : szUg n a0 b0 * (szTg n x * y * (szTg n x)⁻¹) * (szUg n a0 b0)⁻¹ = y := by
      simpa only [mul_assoc, szTgHom_apply] using h1
    have hb : szUg n a0 b0 = (szUg n a0 (b0 + a0 ^ (1 + 2 ^ (n + 1))))⁻¹ := by
      rw [szUg_inv n a0 b0, inv_inv]
    calc szTg n x * y * (szTg n x)⁻¹
        = (szUg n a0 b0)⁻¹ * (szUg n a0 b0 * (szTg n x * y * (szTg n x)⁻¹) *
            (szUg n a0 b0)⁻¹) * szUg n a0 b0 := by group
      _ = (szUg n a0 b0)⁻¹ * y * szUg n a0 b0 := by rw [h2]
      _ = szUg n a0 (b0 + a0 ^ (1 + 2 ^ (n + 1))) * y *
            (szUg n a0 (b0 + a0 ^ (1 + 2 ^ (n + 1))))⁻¹ := by
            rw [← szUg_inv n a0 b0, hb]
  -- Evaluate at `u(1,0)`.
  have hkey := htu (szUg n 1 0) (show szUg n 1 0 ∈ szTwoGroup n from ⟨1, 0, rfl⟩)
  rw [szTg_conj_szUg, mul_one, mul_zero] at hkey
  obtain ⟨e, he⟩ := szUg_conj_fst n a0 (b0 + a0 ^ (1 + 2 ^ (n + 1))) 1 0
  rw [he] at hkey
  have hx : (x : SzField n) = 1 := by
    have h := congrArg (fun g : GL (Fin 4) (SzField n) =>
      ((g : Matrix (Fin 4) (Fin 4) (SzField n))) 0 1) hkey
    simpa [szUg_coe, szU] using h
  have hx1 : x = 1 := Units.ext hx
  rw [hx1, map_one (szTgHom n), mul_one] at hut
  rw [← hut]
  exact ⟨a0, b0, rfl⟩

lemma szWgM_notMem (n : ℕ) : szWgM n ∉ szBorelS n := by
  intro h
  exact szWg_notMem_szBorel n (Subgroup.mem_subgroupOf.mp h)

/-- The action of `Sz(2^(2n+1))` on the cosets of its Borel subgroup is faithful: the normal
core of the Borel subgroup is trivial. -/
theorem szBorelS_normalCore_eq_bot (n : ℕ) :
    Subgroup.normalCore (szBorelS n) = ⊥ := by
  have hcoreB : Subgroup.normalCore (szBorelS n) ≤ szBorelS n := Subgroup.normalCore_le _
  -- the core is contained in the conjugate of `B` by `w`
  have hcoreBw : Subgroup.normalCore (szBorelS n) ≤
      (szBorelS n).map (MulAut.conj (szWgM n)).toMonoidHom := by
    rw [Subgroup.normalCore_eq_iInf_map_conj]
    exact iInf_le _ _
  -- hence the core has odd order
  have hodd : Odd (Nat.card ↥(Subgroup.normalCore (szBorelS n))) := by
    have hle : Subgroup.normalCore (szBorelS n) ≤ szBorelS n ⊓
        (szBorelS n).map (MulAut.conj (szWgM n)).toMonoidHom := le_inf hcoreB hcoreBw
    have hdvd := Subgroup.card_dvd_of_le hle
    have hcard : Nat.card ↥(szBorelS n ⊓
        (szBorelS n).map (MulAut.conj (szWgM n)).toMonoidHom) =
        Nat.card ↥(szTgHom n).range :=
      card_subgroupOf_inf_map_conj n (szWgM n) (szWgM_notMem n)
    rw [hcard] at hdvd
    obtain ⟨k, hk⟩ := hdvd
    have h := odd_card_torus n
    rw [hk] at h
    exact (Nat.odd_mul.mp h).1
  -- the core meets the Suzuki 2-group trivially (odd order meets a 2-group)
  have hcoreInf : Subgroup.normalCore (szBorelS n) ⊓ szTwoGroupS n = ⊥ := by
    refine Subgroup.card_eq_one.mp ?_
    have hodd' : Odd (Nat.card ↥(Subgroup.normalCore (szBorelS n) ⊓ szTwoGroupS n)) := by
      obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le (inf_le_left :
        Subgroup.normalCore (szBorelS n) ⊓ szTwoGroupS n ≤ Subgroup.normalCore (szBorelS n))
      have h := hodd
      rw [hk] at h
      exact (Nat.odd_mul.mp h).1
    have hpow : ∃ j ≤ 4 * n + 2,
        Nat.card ↥(Subgroup.normalCore (szBorelS n) ⊓ szTwoGroupS n) = 2 ^ j := by
      have h2 : Nat.card ↥(Subgroup.normalCore (szBorelS n) ⊓ szTwoGroupS n) ∣ 2 ^ (4 * n + 2) := by
        rw [← card_szTwoGroupS n]
        exact Subgroup.card_dvd_of_le inf_le_right
      exact (Nat.dvd_prime_pow Nat.prime_two).mp h2
    obtain ⟨j, -, hj⟩ := hpow
    rw [hj] at hodd' ⊢
    rcases j with _ | j'
    · rfl
    · exfalso
      exact (Nat.not_even_iff_odd.mpr hodd') ⟨2 ^ j', by rw [pow_succ]; ring⟩
  -- the core centralises the Suzuki 2-group
  have hcent : ∀ x ∈ Subgroup.normalCore (szBorelS n), ∀ y ∈ szTwoGroupS n,
      (x : SzModel n) * y * (x : SzModel n)⁻¹ = y := by
    intro x hx y hy
    have hxN : x ∈ Subgroup.normalizer ((szTwoGroupS n) : Set (SzModel n)) := by
      rw [normalizer_szTwoGroupS n]; exact hcoreB hx
    have hconj : (x : SzModel n) * y * (x : SzModel n)⁻¹ ∈ szTwoGroupS n :=
      ((Subgroup.mem_normalizer_iff.mp hxN) y).mp hy
    have hcomm : (x : SzModel n) * y * (x : SzModel n)⁻¹ * y⁻¹ ∈
        Subgroup.normalCore (szBorelS n) ⊓ szTwoGroupS n := by
      refine ⟨?_, ?_⟩
      · have h1 : y * (x : SzModel n)⁻¹ * y⁻¹ ∈ Subgroup.normalCore (szBorelS n) :=
          (Subgroup.normalCore_normal (szBorelS n)).conj_mem (x : SzModel n)⁻¹
            ((Subgroup.normalCore (szBorelS n)).inv_mem hx) y
        have h2 := (Subgroup.normalCore (szBorelS n)).mul_mem hx h1
        have heq : (x : SzModel n) * (y * (x : SzModel n)⁻¹ * y⁻¹) =
            (x : SzModel n) * y * (x : SzModel n)⁻¹ * y⁻¹ := by group
        rwa [heq] at h2
      · exact (szTwoGroupS n).mul_mem hconj ((szTwoGroupS n).inv_mem hy)
    rw [hcoreInf, Subgroup.mem_bot] at hcomm
    have hcomm' : (x : SzModel n) * y * (x : SzModel n)⁻¹ * y⁻¹ =
        y * y⁻¹ := by rw [hcomm, mul_inv_cancel]
    exact mul_right_cancel hcomm'
  -- hence the core lies in the Suzuki 2-group
  have hcore_le_U : Subgroup.normalCore (szBorelS n) ≤ szTwoGroupS n := by
    intro x hx
    rw [szTwoGroupS, Subgroup.mem_subgroupOf]
    refine szBorel_centralizer_subset n (Subgroup.mem_subgroupOf.mp (hcoreB hx)) ?_
    intro u hu
    have h := hcent x hx ⟨u, szTwoGroup_le_szModel n hu⟩ (by
      rw [szTwoGroupS, Subgroup.mem_subgroupOf]; exact hu)
    exact congrArg (fun w : SzModel n => ((w : SzModel n) : GL (Fin 4) (SzField n))) h
  have hsub : Subgroup.normalCore (szBorelS n) ≤ ⊥ := by
    rw [← hcoreInf]
    exact le_inf le_rfl hcore_le_U
  exact le_antisymm hsub bot_le

/-- The action of `Sz(2^(2n+1))` on the cosets of its Borel subgroup is faithful. -/
theorem szBorelS_faithfulSMul (n : ℕ) :
    FaithfulSMul (SzModel n) ((SzModel n) ⧸ szBorelS n) := by
  rw [faithfulSMul_iff]
  intro g hg
  have hmem : g⁻¹ ∈ Subgroup.normalCore (szBorelS n) := by
    rw [Subgroup.normalCore_eq_iInf_map_conj, Subgroup.mem_iInf]
    intro y
    have h := hg (QuotientGroup.mk y)
    rw [Commons.GroupTheory.GroupAction.coset_smul_mk, QuotientGroup.eq] at h
    refine Subgroup.mem_map.mpr ⟨y⁻¹ * g⁻¹ * y, ?_, ?_⟩
    · simpa [_root_.mul_inv_rev] using h
    · show MulAut.conj y (y⁻¹ * g⁻¹ * y) = g⁻¹
      rw [MulAut.conj_apply]; group
  rw [szBorelS_normalCore_eq_bot, Subgroup.mem_bot] at hmem
  exact inv_eq_one.mp hmem

/-- Every non-trivial normal subgroup of `Sz(2^(2n+1))` is transitive on the cosets of the
Borel subgroup.  (This is the standard first step in the simplicity proof: it reduces the
question to a statement about `2`-transitive groups.) -/
theorem sz_normal_isPretransitive (n : ℕ) (N : Subgroup (SzModel n)) (hN : N.Normal)
    (hNbot : N ≠ ⊥) :
    ∀ x y : (SzModel n) ⧸ szBorelS n, ∃ g : N, (g : SzModel n) • x = y := by
  haveI := szBorelS_faithfulSMul n
  haveI : MulAction.IsMultiplyPretransitive (SzModel n) ((SzModel n) ⧸ szBorelS n) 2 :=
    szModel_isMultiplyPretransitive_two n
  exact Commons.GroupTheory.GroupAction.isPretransitive_normalSubgroup_of_faithful_twoTransitive
    N hN hNbot

end Submission.Sz
