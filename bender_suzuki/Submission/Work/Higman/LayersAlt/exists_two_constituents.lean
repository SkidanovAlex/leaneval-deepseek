/-
Copyright (c) 2024. All rights reserved.

# The two constituents of `V` for a semiregular `σ` of order `2 ^ n - 1`

Let `V` be a finite `𝔽₂`-vector space of cardinality `2 ^ (2 * n)` and `σ` an endomorphism of `V`
of order `2 ^ n - 1` which is semiregular on `V ∖ {0}` (no non-trivial power of `σ` has a non-zero
fixed vector).  Then `V` is the direct sum of two `σ`-simple subspaces of dimension `n`.

Indeed every non-zero `σ`-invariant subspace `U` has `n ∣ dim U` and `2 ^ n ≤ |U|`, hence
`dim U ∈ {n, 2n}`; `V` itself is not simple (if it were, the minimal polynomial of `σ` would be an
irreducible polynomial of degree `2n` dividing `X ^ (2 ^ n - 1) - 1`, and
`Work.Higman.Q3.irred_natDegree_dvd_of_dvd_X_pow_sub_one` would force `2n ∣ n`), so a minimal
cyclic span is a simple subspace of dimension `n`; finally `σ` is semisimple (`minpoly σ` divides
the square-free `X ^ (2 ^ n - 1) - 1`), so that subspace has an invariant complement, which has
dimension `n` and is simple as well.
-/

import Mathlib
import Submission.Work.Higman.Layers.Defs
import Submission.Work.Higman.Layers.pow_le_card
import Submission.Work.Higman.Layers.dvd_finrank
import Submission.Work.Higman.Layers.exists_minpoly_vec
import Submission.Work.Higman.Q3.irred_natDegree_dvd_of_dvd_X_pow_sub_one
import Submission.Work.Higman.Q3.minpoly_natDegree_eq_finrank_of_irreducible
import Submission.Work.Higman.Q3.irreducible_minpoly_of_irreducible

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section

namespace Work.Higman.LayersAlt

open Work.Higman.Layers Polynomial

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem exists_two_constituents {σ : V →ₗ[ZMod 2] V} {n : ℕ} (hn : 1 ≤ n)
    (hcard : Nat.card V = 2 ^ (2 * n)) (horder : orderOf σ = 2 ^ n - 1)
    (hsr : Semiregular σ) :
    ∃ C₁ C₂ : Submodule (ZMod 2) V,
      IsSimpleMod σ C₁ ∧ IsSimpleMod σ C₂ ∧
      C₁ ⊓ C₂ = ⊥ ∧ C₁ ⊔ C₂ = ⊤ ∧
      Module.finrank (ZMod 2) C₁ = n ∧ Module.finrank (ZMod 2) C₂ = n := by
  classical
  haveI : Nontrivial V := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    have h1 : Nat.card V = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨0⟩⟩
    rw [hcard] at h1
    have h2 : 2 ≤ 2 ^ (2 * n) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hpow : σ ^ (2 ^ n - 1) = 1 := by
    rw [← horder]; exact pow_orderOf_eq_one σ
  have hcardV : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V), Nat.card_zmod]
  have hfinV : Module.finrank (ZMod 2) V = 2 * n := by
    have h : 2 ^ Module.finrank (ZMod 2) V = 2 ^ (2 * n) := by rw [← hcardV, hcard]
    exact Nat.pow_right_injective (by norm_num) h
  -- ## every non-zero invariant subspace has dimension at least `n`
  have hle_dim : ∀ U : Submodule (ZMod 2) V, IsInv σ U → U ≠ ⊥ →
      n ≤ Module.finrank (ZMod 2) U := by
    intro U hU hUne
    have h := pow_le_card horder hn hsr hU hUne
    have h2 : Nat.card U = 2 ^ Module.finrank (ZMod 2) U := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := U), Nat.card_zmod]
    rw [h2] at h
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h
  -- ## `V` is not simple
  have hnotsimple : ¬ (∀ U : Submodule (ZMod 2) V, IsInv σ U → U = ⊥ ∨ U = ⊤) := by
    intro hsimp
    have hirr : ∀ U : Submodule (ZMod 2) V, (∀ v ∈ U, σ v ∈ U) → U = ⊥ ∨ U = ⊤ := hsimp
    have hminirr : Irreducible (minpoly (ZMod 2) σ) :=
      Work.Higman.Q3.irreducible_minpoly_of_irreducible σ hirr
    have hdeg : (minpoly (ZMod 2) σ).natDegree = 2 * n := by
      rw [Work.Higman.Q3.minpoly_natDegree_eq_finrank_of_irreducible σ hirr, hfinV]
    have hdvd : minpoly (ZMod 2) σ ∣ Polynomial.X ^ (2 ^ n - 1) - 1 := by
      apply minpoly.dvd
      rw [map_sub, map_pow, aeval_X, map_one, hpow, sub_self]
    have h2 := Work.Higman.Q3.irred_natDegree_dvd_of_dvd_X_pow_sub_one _ hminirr hdvd
    rw [hdeg] at h2
    have : 2 * n ≤ n := Nat.le_of_dvd hn h2
    omega
  -- ## a minimal cyclic span
  have hex : ∃ d : ℕ, ∃ v : V, v ≠ 0 ∧ Module.finrank (ZMod 2) (cycSpan σ v) = d := by
    have hV2 : 2 ≤ Nat.card V := by
      rw [hcard]
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hne : ∃ v : V, v ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      have hsub : Subsingleton V := ⟨fun a b => by rw [hcon a, hcon b]⟩
      have h1 : Nat.card V = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨0⟩⟩
      omega
    obtain ⟨v, hv⟩ := hne
    exact ⟨_, v, hv, rfl⟩
  have hdmin : ∀ w : V, w ≠ 0 → Nat.find hex ≤ Module.finrank (ZMod 2) (cycSpan σ w) :=
    fun w hw => Nat.find_min' hex ⟨w, hw, rfl⟩
  obtain ⟨v, hv, hvd⟩ : ∃ v : V, v ≠ 0 ∧ Module.finrank (ZMod 2) (cycSpan σ v) = Nat.find hex :=
    Nat.find_spec hex
  -- ## the cyclic span of `v` is simple
  have hpow_mem : ∀ (U : Submodule (ZMod 2) V), IsInv σ U → ∀ k : ℕ, ∀ x ∈ U, (σ ^ k) x ∈ U := by
    intro U hU k
    induction k with
    | zero => intro x hx; simpa using hx
    | succ k ih =>
        intro x hx
        rw [pow_succ', Module.End.mul_apply]
        exact hU _ (ih x hx)
  have hSinv : IsInv σ (cycSpan σ v) := by
    have hmap : Submodule.map σ (cycSpan σ v) ≤ cycSpan σ v := by
      rw [cycSpan, Submodule.map_span]
      refine Submodule.span_le.mpr ?_
      rintro x ⟨y, ⟨k, rfl⟩, rfl⟩
      refine Submodule.subset_span ⟨k + 1, ?_⟩
      show (σ ^ (k + 1)) v = σ ((σ ^ k) v)
      rw [pow_succ', Module.End.mul_apply]
    intro x hx
    exact hmap (Submodule.mem_map_of_mem hx)
  have hSne : cycSpan σ v ≠ ⊥ := by
    intro h
    have hmem : v ∈ (⊥ : Submodule (ZMod 2) V) := by
      rw [← h]
      exact Submodule.subset_span ⟨0, by simp⟩
    exact hv (by simpa using hmem)
  have hSsimple : IsSimpleMod σ (cycSpan σ v) := by
    refine ⟨hSinv, hSne, ?_⟩
    intro U hUle hUinv
    by_cases hUbot : U = ⊥
    · exact Or.inl hUbot
    · right
      obtain ⟨w, hwU, hw0⟩ : ∃ w ∈ U, w ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hUbot ((Submodule.eq_bot_iff _).mpr fun x hx => hcon x hx)
      have hwcyc : cycSpan σ w ≤ U := by
        rw [cycSpan]
        refine Submodule.span_le.mpr ?_
        rintro x ⟨k, rfl⟩
        exact hpow_mem U hUinv k w hwU
      have hle1 : cycSpan σ w ≤ cycSpan σ v := hwcyc.trans hUle
      have heq : cycSpan σ w = cycSpan σ v :=
        Submodule.eq_of_le_of_finrank_eq hle1
          (by have h1 := hdmin w hw0
              have h2 : Module.finrank (ZMod 2) (cycSpan σ v) = Nat.find hex := hvd
              have h3 := Submodule.finrank_mono hle1
              omega)
      exact le_antisymm hUle (heq ▸ hwcyc)
  -- ## `dim` of the cyclic span is `n`
  have hSdim : Module.finrank (ZMod 2) (cycSpan σ v) = n := by
    have hdvd : n ∣ Module.finrank (ZMod 2) (cycSpan σ v) := dvd_finrank horder hn hsr hSinv hSne
    have hge : n ≤ Module.finrank (ZMod 2) (cycSpan σ v) := hle_dim _ hSinv hSne
    have hle : Module.finrank (ZMod 2) (cycSpan σ v) ≤ 2 * n := by
      rw [← hfinV]; exact Submodule.finrank_le _
    have hne : Module.finrank (ZMod 2) (cycSpan σ v) ≠ 2 * n := by
      intro heq
      have htop : cycSpan σ v = ⊤ :=
        Submodule.eq_of_le_of_finrank_eq le_top
          (by rw [Submodule.topEquiv.finrank_eq, hfinV, heq])
      refine hnotsimple fun U hU => ?_
      have hSsimple' : IsSimpleMod σ (⊤ : Submodule (ZMod 2) V) := by
        rw [← htop]; exact hSsimple
      exact hSsimple'.2.2 U le_top hU
    obtain ⟨k, hk⟩ := hdvd
    have hkge : 1 ≤ k := by
      have h1 : n ≤ n * k := hk ▸ hge
      have h2 : n * 1 ≤ n * k := by simpa using h1
      exact Nat.le_of_mul_le_mul_left h2 (by omega)
    have hkle : k ≤ 2 := by
      have h1 : n * k ≤ 2 * n := hk ▸ hle
      have h2 : n * k ≤ n * 2 := by simpa [mul_comm] using h1
      exact Nat.le_of_mul_le_mul_left h2 (by omega)
    have hk2 : k ≠ 2 := by
      rintro rfl
      exact hne (by rw [hk]; ring)
    have hk1 : k = 1 := by omega
    rw [hk, hk1, mul_one]
  -- ## `σ` is semisimple, so the cyclic span has an invariant complement
  have hsquarefree : Squarefree (Polynomial.X ^ (2 ^ n - 1) - 1 : Polynomial (ZMod 2)) := by
    have hne : ((2 ^ n - 1 : ℕ) : ZMod 2) ≠ 0 := by
      intro hzero
      rw [ZMod.natCast_eq_zero_iff] at hzero
      have hdvd : 2 ∣ 2 ^ n - 1 := hzero
      have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
      have h1 : 2 ∣ 1 := by
        have h3 : 2 ∣ 2 ^ n - (2 ^ n - 1) := Nat.dvd_sub h2 hdvd
        rwa [Nat.sub_sub_self (Nat.one_le_two_pow)] at h3
      omega
    have hsep := separable_X_pow_sub_C (1 : ZMod 2) hne (by norm_num : (1 : ZMod 2) ≠ 0)
    simpa using hsep.squarefree
  have hsemisimple : Module.End.IsSemisimple σ := by
    refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero (K := ZMod 2) hsquarefree ?_
    rw [map_sub, map_pow, aeval_X, map_one, hpow, sub_self]
  have hcompl_exists : ∀ U : Submodule (ZMod 2) V, IsInv σ U →
      ∃ C : Submodule (ZMod 2) V, IsInv σ C ∧ IsCompl U C := by
    intro U hU
    have hmem : U ∈ Module.End.invtSubmodule σ :=
      (Module.End.mem_invtSubmodule σ).mpr fun x hx => hU x hx
    obtain ⟨C, hC, hCC⟩ := (Module.End.isSemisimple_iff.mp hsemisimple) U hmem
    exact ⟨C, (Module.End.mem_invtSubmodule σ).mp hC, hCC⟩
  obtain ⟨C, hCinv, hCcompl⟩ := hcompl_exists (cycSpan σ v) hSinv
  -- ## the complement has dimension `n` and is simple
  have hCdim : Module.finrank (ZMod 2) C = n := by
    have h1 : Module.finrank (ZMod 2) ↥(cycSpan σ v ⊔ C)
        + Module.finrank (ZMod 2) ↥(cycSpan σ v ⊓ C)
        = Module.finrank (ZMod 2) (cycSpan σ v) + Module.finrank (ZMod 2) C :=
      Submodule.finrank_sup_add_finrank_inf_eq (cycSpan σ v) C
    rw [hCcompl.sup_eq_top, hCcompl.inf_eq_bot] at h1
    have htop : Module.finrank (ZMod 2) (⊤ : Submodule (ZMod 2) V) = 2 * n := by
      rw [Submodule.topEquiv.finrank_eq, hfinV]
    have hbot : Module.finrank (ZMod 2) (⊥ : Submodule (ZMod 2) V) = 0 := by simp
    rw [htop, hbot, hSdim] at h1
    omega
  have hCsimple : IsSimpleMod σ C := by
    refine ⟨hCinv, ?_, ?_⟩
    · intro hbot
      have htop : cycSpan σ v = ⊤ := by rw [← hCcompl.sup_eq_top, hbot, sup_bot_eq]
      have hcardS : Nat.card V = 2 ^ n := by
        have e : (⊤ : Submodule (ZMod 2) V) = cycSpan σ v := by
          rw [← hCcompl.sup_eq_top, hbot, sup_bot_eq]
        have h2 : Nat.card ↥(cycSpan σ v) = 2 ^ n := by
          have h3 : Nat.card ↥(cycSpan σ v)
              = Nat.card (ZMod 2) ^ Module.finrank (ZMod 2) ↥(cycSpan σ v) :=
            Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥(cycSpan σ v))
          rw [h3, Nat.card_zmod, hSdim]
        rw [← Nat.card_congr (Submodule.topEquiv (R := ZMod 2) (M := V)).toEquiv, e, h2]
      rw [hcard] at hcardS
      have h3 : 2 * n = n := Nat.pow_right_injective (by norm_num : 1 < 2) hcardS
      omega
    · intro U hUle hUinv
      by_cases hUbot : U = ⊥
      · exact Or.inl hUbot
      · right
        have h1 : n ≤ Module.finrank (ZMod 2) U := hle_dim U hUinv hUbot
        have h2 : Module.finrank (ZMod 2) U ≤ n := by
          rw [← hCdim]; exact Submodule.finrank_mono hUle
        exact Submodule.eq_of_le_of_finrank_eq hUle (by omega)
  exact ⟨cycSpan σ v, C, hSsimple, hCsimple, hCcompl.inf_eq_bot, hCcompl.sup_eq_top,
    hSdim, hCdim⟩

end Work.Higman.LayersAlt
