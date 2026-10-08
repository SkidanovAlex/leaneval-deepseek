/-
**The rank-one `(B, N)`-pair of `SU(3, 2^n)`: `N_G(T) = T ⋊ ⟨w⟩`.**

This completes the rank-one `(B,N)`-pair data for the third family of the Bender–Suzuki
classification, mirroring `Submission/Sz/Weyl.lean`.

The Weyl element `w = suSg n` inverts the maximal torus `T = suTS n`
(`suSg_mul_suTg_mul_suSg`), so `T ⊔ ⟨w⟩ ≤ N_G(T)`.  Conversely, if `g` normalises `T` then the
point `g • α` of the Bender action on `↥(SU3 n) ⧸ B` is fixed by `T`.  The unipotent radical `U`
acts *regularly* on `Ω ∖ {α}` (Suzuki condition `[G : B] = |U| + 1`, from the abstract rank-one
BN-pair theory, plus the fact that a non-trivial element of `U` fixes only the base point), and
`T` fixes the second `T`-fixed point `β = w • α`.  Writing a `T`-fixed point as `u • β` forces
`t u t⁻¹ = u` for every `t ∈ T`; the explicit commutation formula
`t(a)·u(b,c)·t(a)⁻¹ = u(a·b·(a^(q-1))⁻¹, a·c·a^q)` and the existence of `a ∈ F^×` with
`a^q = a`, `a ≠ 1` (namely `a = g^(q+1)` for `g` a generator of `F^×`) show that no non-trivial
element of `U` is centralised by `T`.  Hence every `T`-fixed point is `α` or `β`, and the usual
argument gives `N_G(T) = T ⊔ ⟨w⟩`.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Models.Port.PSU3.SuzukiCondition
import Submission.Work.Models.Port.PSU3.Centralizer
import Submission.Work.Models.Port.PSU3.StronglyEmbedded
import Submission.Work.Models.Port.PSU3.Bruhat
import Submission.Work.Models.Port.Commons.GroupTheory.Bender.isBenderAction_coset
import Submission.Work.Models.Port.Commons.GroupTheory.Bender.eq_of_smul_eq_self_of_mem_of_isPGroup_two
import Submission.Work.Models.Port.Commons.GroupTheory.GroupAction.exists_smul_eq_of_ne_of_card_eq_one_add
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.mem_sup_mul

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

namespace Submission.PSU3

/-! ## Strong embedding of the Borel subgroup `B` of `SU(3,2^n)` -/

/-- `B` is strongly embedded in `SU(3,2^n)`: this is inherited from the strong embedding of
`suB n` in `GL(3, 2^(2n))`, because `SU(3,2^n) ≤ GL(3,2^(2n))` is an intermediate subgroup. -/
theorem suBS_stronglyEmbedded (n : ℕ) (hn : 1 ≤ n) : IsStronglyEmbedded (suBS n) :=
  suB_stronglyEmbedded n hn

/-- A non-trivial element of `U ≤ SU(3,2^n)` fixes only the base point of the Bender action. -/
theorem suBS_fixedPoint_eq_one (n : ℕ) (hn : 1 ≤ n)
    (u : ↥(suUS n)) (hu : u ≠ 1)
    {x : ↥(SU3 n) ⧸ suBS n} (hx : (u : ↥(SU3 n)) • x = x) :
    x = ((1 : ↥(SU3 n)) : ↥(SU3 n) ⧸ suBS n) := by
  obtain ⟨hne, heven, hodd⟩ := suBS_stronglyEmbedded n hn
  obtain ⟨-, -, hEvenG, hinv⟩ :=
    Commons.GroupTheory.Bender.isBenderAction_coset (suBS n) hne heven hodd
  have hu' : (u : ↥(SU3 n)) ≠ 1 := fun h => hu (Subtype.ext h)
  refine Commons.GroupTheory.Bender.eq_of_smul_eq_self_of_mem_of_isPGroup_two
    (G := ↥(SU3 n)) hEvenG hinv (suUS_isPGroup n hn) ?_ u.2 hu' hx
  intro g
  rw [← MulAction.mem_stabilizer_iff, MulAction.stabilizer_quotient]
  exact suUS_le_suBS n g.2

/-! ## `U` acts regularly on the non-base points -/

/-- **`U` acts regularly on the non-base points of the Bender action**: the Suzuki condition
`[SU(3,2^n) : B] = |U| + 1` plus the freeness of the action of `U` away from the base point. -/
theorem suUS_exists_smul_eq_of_ne (n : ℕ) (hn : 1 ≤ n)
    {x y : ↥(SU3 n) ⧸ suBS n}
    (hx : x ≠ ((1 : ↥(SU3 n)) : ↥(SU3 n) ⧸ suBS n))
    (hy : y ≠ ((1 : ↥(SU3 n)) : ↥(SU3 n) ⧸ suBS n)) :
    ∃ u : ↥(suUS n), (u : ↥(SU3 n)) • x = y := by
  refine Commons.GroupTheory.GroupAction.exists_smul_eq_of_ne_of_card_eq_one_add
    (U := suUS n) (((1 : ↥(SU3 n)) : ↥(SU3 n) ⧸ suBS n)) ?_ ?_ ?_ hx hy
  · show (suBS n).index = Nat.card ↥(suUS n) + 1
    rw [suBS_index_eq_one_add n hn, Nat.add_comm]
  · intro u
    rw [← MulAction.mem_stabilizer_iff, MulAction.stabilizer_quotient]
    exact suUS_le_suBS n u.2
  · intro u hu x hx
    exact suBS_fixedPoint_eq_one n hn u hu hx

/-! ## The maximal torus and the Weyl element -/

@[simp] lemma suTgSU_val (n : ℕ) (a : (F n)ˣ) :
    ((suTgSU n a : ↥(SU3 n)) : GL (Fin 3) (F n)) = suTg n a := rfl

lemma suTgSU_mem_suTS (n : ℕ) (a : (F n)ˣ) : suTgSU n a ∈ suTS n :=
  Subgroup.mem_subgroupOf.mpr ⟨a, rfl⟩

lemma suTS_le_suBS (n : ℕ) : suTS n ≤ suBS n := by
  rw [suBS_eq_sup]
  exact le_sup_right

lemma suSgM_mul_self (n : ℕ) : suSgM n * suSgM n = 1 := by
  apply Subtype.ext
  show (suSg n : GL (Fin 3) (F n)) * suSg n = 1
  rw [suSg_mul_self]

lemma suSgM_inv (n : ℕ) : (suSgM n)⁻¹ = suSgM n :=
  inv_eq_of_mul_eq_one_right (suSgM_mul_self n)

/-- The Weyl element inverts the torus. -/
lemma suSgM_conj_suTgSU (n : ℕ) (a : (F n)ˣ) :
    suSgM n * suTgSU n a * (suSgM n)⁻¹ = suTgSU n ((a ^ (2 ^ n))⁻¹) := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, suTgSU_val, suSgM]
  rw [suSg_inv n]
  show suSg n * suTg n a * suSg n = suTg n ((a ^ (2 ^ n))⁻¹)
  exact suSg_mul_suTg_mul_suSg n a

/-- The Weyl element normalises the torus. -/
lemma suSgM_mem_normalizer_suTS (n : ℕ) :
    suSgM n ∈ Subgroup.normalizer (suTS n : Set (↥(SU3 n))) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_
    (le_of_eq (Subgroup.card_map_of_injective (MulEquiv.injective _)).symm)
  rintro y ⟨k, hk, rfl⟩
  have hk' : (k : GL (Fin 3) (F n)) ∈ suT n := Subgroup.mem_subgroupOf.mp hk
  obtain ⟨a, ha⟩ := hk'
  have hkx : suTgSU n a = k := Subtype.ext (by simpa [suTgSU] using ha.symm)
  change suSgM n * k * (suSgM n)⁻¹ ∈ suTS n
  rw [← hkx, suSgM_conj_suTgSU]
  exact suTgSU_mem_suTS n ((a ^ (2 ^ n))⁻¹)

/-! ## The fixed field element `a = g^(q+1)` of the torus -/

lemma gen_pow_succ_pow_fixed_unit (n : ℕ) (hn : 2 ≤ n) :
    (gen n ^ (2 ^ n + 1)) ^ (2 ^ n) = gen n ^ (2 ^ n + 1) := by
  have hpowU : gen n ^ (2 ^ (2 * n) - 1) = 1 := by
    rw [← orderOf_gen n (by omega)]
    exact pow_orderOf_eq_one (gen n)
  have hL : (2 ^ n + 1) * 2 ^ n = 2 ^ (2 * n) + 2 ^ n := by
    rw [add_mul, one_mul, ← sq_pow]
  have hR : 2 ^ (2 * n) + 2 ^ n = (2 ^ n + 1) + (2 ^ (2 * n) - 1) := by
    have h1 : 1 ≤ 2 ^ (2 * n) := Nat.one_le_two_pow
    omega
  rw [← pow_mul, hL, hR, pow_add, hpowU, mul_one]

lemma gen_pow_succ_pow_fixed (n : ℕ) (hn : 2 ≤ n) :
    ((gen n ^ (2 ^ n + 1) : (F n)ˣ) : F n) ^ (2 ^ n) =
      ((gen n ^ (2 ^ n + 1) : (F n)ˣ) : F n) := by
  have h := congrArg (fun u : (F n)ˣ => (u : F n)) (gen_pow_succ_pow_fixed_unit n hn)
  simpa using h

lemma gen_pow_succ_ne_one (n : ℕ) (hn : 2 ≤ n) :
    ((gen n ^ (2 ^ n + 1) : (F n)ˣ) : F n) ≠ 1 := by
  intro h
  have hunit : gen n ^ (2 ^ n + 1) = 1 := Units.ext h
  have hdvd : orderOf (gen n) ∣ 2 ^ n + 1 := by
    rw [orderOf_dvd_iff_pow_eq_one]
    exact hunit
  rw [orderOf_gen n (by omega)] at hdvd
  have h4 : 4 ≤ 2 ^ n := by
    calc (4:ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hbig : 2 ^ n + 3 ≤ 2 ^ (2 * n) := by
    rw [← sq_pow n]
    nlinarith
  have hle : 2 ^ (2 * n) - 1 ≤ 2 ^ n + 1 :=
    Nat.le_of_dvd (by omega : 0 < 2 ^ n + 1) hdvd
  omega

/-- **No non-trivial element of the unipotent radical is centralised by the torus.** -/
lemma eq_one_of_mem_suUS_of_centralizes_suTS (n : ℕ) (hn : 2 ≤ n) {u : ↥(SU3 n)}
    (hu : u ∈ suUS n) (hcent : ∀ t ∈ suTS n, u * t = t * u) : u = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set a : (F n)ˣ := gen n ^ (2 ^ n + 1) with ha
  have haq : (a : F n) ^ (2 ^ n) = (a : F n) := by rw [ha]; exact gen_pow_succ_pow_fixed n hn
  have ha1 : (a : F n) ≠ 1 := by rw [ha]; exact gen_pow_succ_ne_one n hn
  obtain ⟨b, c, hbc, hubc⟩ := Subgroup.mem_subgroupOf.mp hu
  have hcomm := hcent _ (suTgSU_mem_suTS n a)
  have hcommGL : suTg n a * suUg n b c * (suTg n a)⁻¹ = suUg n b c := by
    have h := congrArg (fun z : ↥(SU3 n) => (z : GL (Fin 3) (F n))) hcomm
    simp only [Subgroup.coe_mul, suTgSU_val] at h
    rw [hubc] at h
    rw [← h, mul_assoc, mul_inv_cancel, mul_one]
  have h1 : (fun p : F n × F n => suUg n p.1 p.2)
      ((a : F n) * b * ((a : F n) ^ (2 ^ n - 1))⁻¹, (a : F n) * c * (a : F n) ^ (2 ^ n)) =
      (fun p : F n × F n => suUg n p.1 p.2) (b, c) := by
    simpa using (suTg_conj_suUg n a b c).symm.trans hcommGL
  have hpair := suUg_injective n h1
  have hp1 : (a : F n) * b * ((a : F n) ^ (2 ^ n - 1))⁻¹ = b := congrArg Prod.fst hpair
  have hp2 : (a : F n) * c * (a : F n) ^ (2 ^ n) = c := congrArg Prod.snd hpair
  have hβ : (a : F n) ^ (2 ^ n - 1) = 1 := by
    have h1 : (a : F n) ^ (2 ^ n - 1) * (a : F n) = (a : F n) := by
      rw [← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow, haq]
    exact mul_right_cancel₀ (Units.ne_zero a) (by rw [h1, one_mul])
  have hb0 : b = 0 := by
    have h1 : (a : F n) * b = b := by
      rw [hβ, inv_one, mul_one] at hp1
      exact hp1
    have hz : ((a : F n) - 1) * b = 0 := by rw [sub_mul, one_mul, h1, sub_self]
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr ha1)
  have hc0 : c = 0 := by
    have h2 : (a : F n) * c * (a : F n) = c := by rw [haq] at hp2; exact hp2
    have hz : ((a : F n) ^ 2 - 1) * c = 0 := by
      rw [sub_mul, one_mul, pow_two,
        show (a : F n) * (a : F n) * c = (a : F n) * c * (a : F n) by ring, h2, sub_self]
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd (CharTwo.sq_inj.mp (by rw [one_pow]; exact sub_eq_zero.mp h)) ha1
    · exact h
  exact Subtype.ext (by rw [hubc, hb0, hc0, suUg_zero]; rfl)

/-! ## The `T`-fixed points of the Bender action -/

/-- The base point of the Bender action of `SU(3,2^n)`. -/
noncomputable abbrev suPtBase (n : ℕ) : ↥(SU3 n) ⧸ suBS n :=
  ((1 : ↥(SU3 n)) : ↥(SU3 n) ⧸ suBS n)

/-- The second `T`-fixed point `β = w • α` of the Bender action. -/
noncomputable abbrev suPtWeyl (n : ℕ) : ↥(SU3 n) ⧸ suBS n := suSgM n • suPtBase n

lemma suTS_fixes_suPtBase (n : ℕ) (t : ↥(SU3 n)) (ht : t ∈ suTS n) :
    t • suPtBase n = suPtBase n := by
  rw [← MulAction.mem_stabilizer_iff, MulAction.stabilizer_quotient]
  exact suTS_le_suBS n ht

lemma suTS_fixes_suPtWeyl (n : ℕ) (t : ↥(SU3 n)) (ht : t ∈ suTS n) :
    t • suPtWeyl n = suPtWeyl n := by
  have htBw : t ∈ (suBS n).map (MulAut.conj (suSgM n)).toMonoidHom := by
    have hmem : t ∈ suBS n ⊓ (suBS n).map (MulAut.conj (suSgM n)).toMonoidHom := by
      rw [suBS_inf_map_conj_eq n]; exact ht
    exact (Subgroup.mem_inf.mp hmem).2
  rw [← MulAction.mem_stabilizer_iff,
    MulAction.stabilizer_smul_eq_stabilizer_map_conj (suSgM n) (suPtBase n),
    MulAction.stabilizer_quotient]
  exact htBw

/-- **The `T`-fixed points of the Bender action are the base point and `β = w • α`.** -/
lemma eq_suPtBase_or_eq_suPtWeyl_of_forall_suTS_fixes (n : ℕ) (hn : 2 ≤ n)
    {x : ↥(SU3 n) ⧸ suBS n} (hx : ∀ t ∈ suTS n, t • x = x) :
    x = suPtBase n ∨ x = suPtWeyl n := by
  by_cases hx0 : x = suPtBase n
  · exact Or.inl hx0
  · right
    have hβne : suPtWeyl n ≠ suPtBase n := by
      intro h
      refine suSgM_notMem_suBS n ?_
      rwa [← MulAction.mem_stabilizer_iff, MulAction.stabilizer_quotient] at h
    obtain ⟨u, hu⟩ := suUS_exists_smul_eq_of_ne n (by omega) (x := suPtWeyl n) (y := x) hβne hx0
    have hinj : ∀ u₁ u₂ : ↥(suUS n),
        (u₁ : ↥(SU3 n)) • suPtWeyl n = (u₂ : ↥(SU3 n)) • suPtWeyl n → u₁ = u₂ := by
      intro u₁ u₂ h
      by_contra hne
      have hcoe : ((u₁⁻¹ * u₂ : ↥(suUS n)) : ↥(SU3 n)) =
          ((u₁ : ↥(SU3 n)))⁻¹ * (u₂ : ↥(SU3 n)) := by simp
      have h1 : ((u₁⁻¹ * u₂ : ↥(suUS n)) : ↥(SU3 n)) • suPtWeyl n = suPtWeyl n := by
        rw [hcoe, mul_smul, ← h, inv_smul_smul]
      refine hβne (suBS_fixedPoint_eq_one n (by omega) (u₁⁻¹ * u₂) ?_ h1)
      intro hc
      exact hne (inv_mul_eq_one.mp hc)
    have hcent : ∀ t ∈ suTS n, (u : ↥(SU3 n)) * t = t * (u : ↥(SU3 n)) := by
      intro t ht
      have hβT : t • suPtWeyl n = suPtWeyl n := suTS_fixes_suPtWeyl n t ht
      have hβinv : t⁻¹ • suPtWeyl n = suPtWeyl n := by
        calc t⁻¹ • suPtWeyl n = t⁻¹ • (t • suPtWeyl n) := by rw [hβT]
          _ = suPtWeyl n := inv_smul_smul t (suPtWeyl n)
      have hfix : t • ((u : ↥(SU3 n)) • suPtWeyl n) = (u : ↥(SU3 n)) • suPtWeyl n := by
        rw [hu]; exact hx t ht
      have hconj : (t * (u : ↥(SU3 n)) * t⁻¹) • suPtWeyl n = (u : ↥(SU3 n)) • suPtWeyl n := by
        calc (t * (u : ↥(SU3 n)) * t⁻¹) • suPtWeyl n
            = (t * (u : ↥(SU3 n))) • (t⁻¹ • suPtWeyl n) := by rw [mul_smul, mul_smul]
          _ = (t * (u : ↥(SU3 n))) • suPtWeyl n := by rw [hβinv]
          _ = t • ((u : ↥(SU3 n)) • suPtWeyl n) := by rw [mul_smul]
          _ = (u : ↥(SU3 n)) • suPtWeyl n := hfix
      have hmemU : t * (u : ↥(SU3 n)) * t⁻¹ ∈ suUS n :=
        (Subgroup.le_normalizer_iff.mp (suTS_le_normalizer_suUS n)) t ht (u : ↥(SU3 n)) u.2
      have heq : (⟨t * (u : ↥(SU3 n)) * t⁻¹, hmemU⟩ : ↥(suUS n)) = u :=
        hinj ⟨t * (u : ↥(SU3 n)) * t⁻¹, hmemU⟩ u hconj
      have htu : t * (u : ↥(SU3 n)) * t⁻¹ = (u : ↥(SU3 n)) := congrArg Subtype.val heq
      have h2 : t * (u : ↥(SU3 n)) * t⁻¹ * t = (u : ↥(SU3 n)) * t :=
        congrArg (fun z : ↥(SU3 n) => z * t) htu
      rw [show t * (u : ↥(SU3 n)) * t⁻¹ * t = t * (u : ↥(SU3 n)) by group] at h2
      exact h2.symm
    have hu1 : (u : ↥(SU3 n)) = 1 := eq_one_of_mem_suUS_of_centralizes_suTS n hn u.2 hcent
    rw [← hu, hu1, one_smul]

/-- **The rank-one `(B,N)`-pair relation `N_G(T) = T ⊔ ⟨w⟩`** for `SU(3,2^n)`: the normalizer of
the maximal torus is generated by the torus and the Weyl element. -/
theorem normalizer_suTS_eq_sup_zpowers_suSgM (n : ℕ) (hn : 2 ≤ n) :
    Subgroup.normalizer (suTS n : Set (↥(SU3 n))) =
      suTS n ⊔ Subgroup.zpowers (suSgM n) := by
  have hTfix : ∀ g ∈ Subgroup.normalizer (suTS n : Set (↥(SU3 n))),
      ∀ t ∈ suTS n, t • (g • suPtBase n) = g • suPtBase n := by
    intro g hg t ht
    have ht' : t ∈ (suTS n).map (MulAut.conj g).toMonoidHom :=
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp hg).symm ▸ ht
    obtain ⟨t', ht'mem, ht'eq⟩ := Subgroup.mem_map.mp ht'
    rw [← ht'eq]
    change (g * t' * g⁻¹) • (g • suPtBase n) = g • suPtBase n
    rw [mul_smul, mul_smul, inv_smul_smul, suTS_fixes_suPtBase n t' ht'mem]
  have hNB : ∀ g ∈ Subgroup.normalizer (suTS n : Set (↥(SU3 n))),
      g ∈ suBS n → g ∈ suTS n := by
    intro g hg hgB
    have hgB' : g ∈ suUS n ⊔ suTS n := by rw [suBS_eq_sup n] at hgB; exact hgB
    obtain ⟨u, hu, t, ht, hut⟩ := Commons.GroupTheory.Subgroup.mem_sup_mul (suUS n) (suTS n)
      (suTS_le_normalizer_suUS n) hgB'
    have huN : u ∈ Subgroup.normalizer (suTS n : Set (↥(SU3 n))) := by
      have h1 : g * t⁻¹ ∈ Subgroup.normalizer (suTS n : Set (↥(SU3 n))) :=
        (Subgroup.normalizer _).mul_mem hg
          ((Subgroup.normalizer _).inv_mem (Subgroup.le_normalizer ht))
      rw [hut, mul_assoc, mul_inv_cancel, mul_one] at h1
      exact h1
    have hcent : ∀ t' ∈ suTS n, u * t' = t' * u := by
      intro t' ht'
      have h1 : u * t' * u⁻¹ ∈ suTS n := (Subgroup.mem_normalizer_iff.mp huN t').mp ht'
      have h2 : t' * u⁻¹ * t'⁻¹ ∈ suUS n :=
        (Subgroup.le_normalizer_iff.mp (suTS_le_normalizer_suUS n)) t' ht' u⁻¹
          (Subgroup.inv_mem _ hu)
      have h3 : u * t' * u⁻¹ * t'⁻¹ ∈ suUS n := by
        have hm := Subgroup.mul_mem (suUS n) hu h2
        simpa only [mul_assoc] using hm
      have h4 : u * t' * u⁻¹ * t'⁻¹ ∈ suTS n :=
        Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ ht')
      have h5 : u * t' * u⁻¹ * t'⁻¹ = 1 := by
        have hmem : u * t' * u⁻¹ * t'⁻¹ ∈ suUS n ⊓ suTS n := Subgroup.mem_inf.mpr ⟨h3, h4⟩
        rwa [suTS_inf_suUS n, Subgroup.mem_bot] at hmem
      have h6 : u * t' * u⁻¹ = t' := by
        calc u * t' * u⁻¹ = u * t' * u⁻¹ * t'⁻¹ * t' := by group
          _ = 1 * t' := by rw [h5]
          _ = t' := by group
      calc u * t' = (u * t' * u⁻¹) * u := by group
        _ = t' * u := by rw [h6]
    have hu1 : u = 1 := eq_one_of_mem_suUS_of_centralizes_suTS n hn hu hcent
    rw [hut, hu1, one_mul]
    exact ht
  refine le_antisymm ?_ (sup_le Subgroup.le_normalizer
    ((Subgroup.zpowers_le).mpr (suSgM_mem_normalizer_suTS n)))
  intro g hg
  rcases eq_suPtBase_or_eq_suPtWeyl_of_forall_suTS_fixes n hn (hTfix g hg) with h | h
  · have hgB : g ∈ suBS n := by
      rwa [← MulAction.mem_stabilizer_iff, MulAction.stabilizer_quotient] at h
    exact Subgroup.mem_sup_left (hNB g hg hgB)
  · have hwginv : (suSgM n)⁻¹ * g ∈ Subgroup.normalizer (suTS n : Set (↥(SU3 n))) :=
      (Subgroup.normalizer _).mul_mem
        ((Subgroup.normalizer _).inv_mem (suSgM_mem_normalizer_suTS n)) hg
    have hwgB : (suSgM n)⁻¹ * g ∈ suBS n := by
      have h1 : ((suSgM n)⁻¹ * g) • suPtBase n = suPtBase n := by
        rw [mul_smul, h]
        exact inv_smul_smul (suSgM n) (suPtBase n)
      rwa [← MulAction.mem_stabilizer_iff, MulAction.stabilizer_quotient] at h1
    have hmemT : (suSgM n)⁻¹ * g ∈ suTS n := hNB _ hwginv hwgB
    have hge : g = suSgM n * ((suSgM n)⁻¹ * g) := by group
    have hmem' : suSgM n * ((suSgM n)⁻¹ * g) ∈ Subgroup.zpowers (suSgM n) ⊔ suTS n :=
      Subgroup.mul_mem_sup (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩) hmemT
    rw [hge, sup_comm]
    exact hmem'

end Submission.PSU3
