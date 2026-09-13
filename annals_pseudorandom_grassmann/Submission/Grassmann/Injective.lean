import Mathlib
import Submission.Grassmann.Spectrum
import Submission.Commons.Combinatorics.Finset.sum_ite_ite
import Submission.Commons.LinearAlgebra.Submodule.card_superspaces_finrank_eq_quotient
import Submission.Commons.LinearAlgebra.Submodule.card_submodule_finrank_strictMono

/-!
# Injectivity of the up operators `Ψ_i` (Layer 3, completing the spectral core)

For `Gr k ℓ` (the `ℓ`-dimensional subspaces of `𝔽₂ᵏ`) the operator
`(Ψ_i g)(L) = ∑_{W ≤ L, dim W = i} g W` is the *up operator* on level `i`.  In `Spectrum.lean`
its range `V_i = Vup i` was used to build the filtration `V_0 ≤ ⋯ ≤ V_ℓ = ⊤` with
`(A - θ_i) V_i ≤ V_{i-1}`.

This file proves the missing ingredient: **`Ψ_i` is injective** as soon as `i ≤ ℓ` and
`2(ℓ-1) < k` (in particular whenever `2ℓ ≤ k`).  Consequently `dim V_i = grCount k i`, the
filtration is strictly increasing and every Eberlein eigenvalue `θ_i` is attained with the
multiplicity `grCount k i - grCount k (i-1)`.

The key input is the *one-step* case `j → j+1`: if `ΨF` vanishes on all `(j+1)`-subspaces
then, double counting over the `(j+1)`-subspaces containing a fixed `j`-subspace `W`,

  `(2^(k-j) - 1) F W + ∑_{H ~ W} F H = 0`,

i.e. `F` is an eigenvector of the adjacency operator of `Gr k j` with eigenvalue
`-(2^(k-j) - 1)`.  That eigenvalue is *not* an Eberlein eigenvalue `θ_s` (`s ≤ j`) provided
`2j < k` (the smallest one is `θ_j = -(2^j - 1)` and `2^j < 2^(k-j)`), so `F = 0`.
The general case follows by the one-step factorisation
`Ψ_{i→ℓ} = c · Ψ_{i+1→ℓ} ∘ Ψ_{i→i+1}`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open PseudorandomGrassmann

local notation "𝔽₂" => ZMod 2

namespace Submission.Grassmann
namespace F2

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k j : ℕ}

/-! ## 1. Counting the superspaces of a fixed subspace -/

/-- The number of `n`-dimensional subspaces containing a fixed subspace `U`
(in `𝔽₂ᵏ`), when `dim U ≤ n`. -/
lemma natCard_superspaces (U : Submodule 𝔽₂ (Fin k → 𝔽₂)) (n : ℕ)
    (hU : Module.finrank 𝔽₂ U ≤ n) :
    Nat.card {C : Submodule 𝔽₂ (Fin k → 𝔽₂) // U ≤ C ∧ Module.finrank 𝔽₂ C = n} =
      grCount (k - Module.finrank 𝔽₂ U) (n - Module.finrank 𝔽₂ U) := by
  rw [Commons.LinearAlgebra.Submodule.card_superspaces_finrank_eq_quotient
    (K := 𝔽₂) (V := Fin k → 𝔽₂) U hU]
  rw [card_submodule_finrank_eq_grCount ((Fin k → 𝔽₂) ⧸ U) (n - Module.finrank 𝔽₂ U)]
  have hq : Module.finrank 𝔽₂ ((Fin k → 𝔽₂) ⧸ U) = k - Module.finrank 𝔽₂ U := by
    have h := Submodule.finrank_quotient_add_finrank (R := 𝔽₂) U
    rw [finrank_fin_fun] at h
    omega
  rw [hq]

/-- The number of `n`-dimensional subspaces containing a fixed subspace `U` is `0` when
`dim U > n`. -/
lemma natCard_superspaces_eq_zero (U : Submodule 𝔽₂ (Fin k → 𝔽₂)) (n : ℕ)
    (hU : n < Module.finrank 𝔽₂ U) :
    Nat.card {C : Submodule 𝔽₂ (Fin k → 𝔽₂) // U ≤ C ∧ Module.finrank 𝔽₂ C = n} = 0 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero_iff]
  exact ⟨fun C => absurd (by
    have h := Submodule.finrank_mono C.2.1
    omega) (by omega)⟩

/-- Version of `natCard_superspaces` phrased with `GrVertex`. -/
lemma natCard_superspaces_GrVertex (U : Submodule 𝔽₂ (Fin k → 𝔽₂)) (n : ℕ)
    (hU : Module.finrank 𝔽₂ U ≤ n) :
    Nat.card {C : GrVertex k n // U ≤ C.1} =
      grCount (k - Module.finrank 𝔽₂ U) (n - Module.finrank 𝔽₂ U) := by
  rw [Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
        (fun L : Submodule 𝔽₂ (Fin k → 𝔽₂) => Module.finrank 𝔽₂ L = n)
        (fun L : Submodule 𝔽₂ (Fin k → 𝔽₂) => U ≤ L)),
      Nat.card_congr (Equiv.subtypeEquivRight (fun L => and_comm))]
  exact natCard_superspaces U n hU

/-- Version of `natCard_superspaces_eq_zero` phrased with `GrVertex`. -/
lemma natCard_superspaces_GrVertex_eq_zero (U : Submodule 𝔽₂ (Fin k → 𝔽₂)) (n : ℕ)
    (hU : n < Module.finrank 𝔽₂ U) :
    Nat.card {C : GrVertex k n // U ≤ C.1} = 0 := by
  rw [Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
        (fun L : Submodule 𝔽₂ (Fin k → 𝔽₂) => Module.finrank 𝔽₂ L = n)
        (fun L : Submodule 𝔽₂ (Fin k → 𝔽₂) => U ≤ L)),
      Nat.card_congr (Equiv.subtypeEquivRight (fun L => and_comm))]
  exact natCard_superspaces_eq_zero U n hU

/-- **The key one-step counting identity.**  The number of `(j+1)`-subspaces containing both
`W` and `H` is `2^(k-j) - 1` for `H = W`, is `1` when `dim (W ⊓ H) = j - 1`, and is `0`
otherwise. -/
lemma natCard_superspaces_both (W H : GrVertex k j) :
    Nat.card {C : GrVertex k (j + 1) // W.1 ≤ C.1 ∧ H.1 ≤ C.1} =
      if H = W then 2 ^ (k - j) - 1
      else if Module.finrank 𝔽₂ ↥(W.1 ⊓ H.1) = j - 1 then 1 else 0 := by
  classical
  have hiff : ∀ C : GrVertex k (j + 1), (W.1 ≤ C.1 ∧ H.1 ≤ C.1) ↔ (W.1 ⊔ H.1 ≤ C.1) :=
    fun C => ⟨fun h => sup_le h.1 h.2, fun h => ⟨le_sup_left.trans h, le_sup_right.trans h⟩⟩
  rw [Nat.card_congr (Equiv.subtypeEquivRight hiff)]
  by_cases hHW : H = W
  · rw [hHW, if_pos rfl, sup_idem,
      natCard_superspaces_GrVertex W.1 (j + 1) (by rw [W.2]; omega), W.2,
      show j + 1 - j = 1 by omega, grCount_one]
  · rw [if_neg hHW]
    have hne : H.1 ≠ W.1 := fun h => hHW (Subtype.ext h)
    have hsup_ge : j + 1 ≤ Module.finrank 𝔽₂ ↥(W.1 ⊔ H.1) := by
      have h1 : j ≤ Module.finrank 𝔽₂ ↥(W.1 ⊔ H.1) := by
        have := Submodule.finrank_mono (le_sup_left : W.1 ≤ W.1 ⊔ H.1)
        rwa [W.2] at this
      rcases lt_or_eq_of_le h1 with hlt | heq
      · omega
      · exfalso
        have hweq : W.1 ⊔ H.1 = W.1 :=
          (Submodule.eq_of_le_of_finrank_eq (le_sup_left : W.1 ≤ W.1 ⊔ H.1) (by omega)).symm
        have hHWle : H.1 ≤ W.1 := le_sup_right.trans (le_of_eq hweq)
        exact hne (Submodule.eq_of_le_of_finrank_eq hHWle (by omega))
    have hiff2 : Module.finrank 𝔽₂ ↥(W.1 ⊔ H.1) = j + 1 ↔
        Module.finrank 𝔽₂ ↥(W.1 ⊓ H.1) = j - 1 := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq W.1 H.1
      rw [W.2, H.2] at h
      constructor
      · intro hs
        omega
      · intro hi
        omega
    by_cases hsup : Module.finrank 𝔽₂ ↥(W.1 ⊔ H.1) = j + 1
    · rw [if_pos (hiff2.mp hsup), natCard_superspaces_GrVertex (W.1 ⊔ H.1) (j + 1) (by omega),
        hsup, show j + 1 - (j + 1) = 0 by omega, grCount_zero]
    · rw [if_neg (fun h => hsup (hiff2.mpr h)),
        natCard_superspaces_GrVertex_eq_zero (W.1 ⊔ H.1) (j + 1) (by omega)]/-! ## 2. The one-step eigen-equation -/

/-- Adjacency in `Gr k j` in terms of the dimension of the intersection. -/
lemma adj_iff_inf (W H : GrVertex k j) :
    (Gr k j).Adj W H ↔ W ≠ H ∧ Module.finrank 𝔽₂ ↥(W.1 ⊓ H.1) = j - 1 := by
  unfold Gr
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, h⟩
    · exact ⟨hne, by rwa [inf_comm] at h⟩
  · rintro ⟨hne, h⟩
    exact ⟨hne, Or.inl h⟩

/-- Count form of `natCard_superspaces_both`, cast to `ℚ`. -/
lemma natCard_superspaces_both_cast (W H : GrVertex k j) :
    (Nat.card {C : GrVertex k (j + 1) // W.1 ≤ C.1 ∧ H.1 ≤ C.1} : ℚ) =
      (if H = W then (((2 ^ (k - j) - 1 : ℕ)) : ℚ)
        else if Module.finrank 𝔽₂ ↥(W.1 ⊓ H.1) = j - 1 then 1 else 0) := by
  rw [natCard_superspaces_both W H]
  by_cases h1 : H = W
  · rw [if_pos h1, if_pos h1]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : Module.finrank 𝔽₂ ↥(W.1 ⊓ H.1) = j - 1
    · rw [if_pos h2, if_pos h2]; norm_num
    · rw [if_neg h2, if_neg h2]; norm_num

/-- **The one-step eigen-equation.**  If `F` lies in the kernel of the one-step up operator
`Ψ_{j → j+1}` then `F` is an eigenvector of the adjacency operator of `Gr k j` with
eigenvalue `-(2^(k-j) - 1)`. -/
lemma upFun_step_eigen (F : GrVertex k j → ℚ)
    (hF : upFun (k := k) (ℓ := j + 1) j F = 0) (W : GrVertex k j) :
    adjOp F W = -(((2 ^ (k - j) - 1 : ℕ)) : ℚ) * F W := by
  classical
  have hsum : ∑ C : GrVertex k (j + 1),
      (if W.1 ≤ C.1 then upFun (k := k) (ℓ := j + 1) j F C else 0) = 0 := by
    refine Finset.sum_eq_zero (fun C _ => ?_)
    by_cases h : W.1 ≤ C.1
    · rw [if_pos h]; exact congrFun hF C
    · rw [if_neg h]
  have hunfold : ∑ C : GrVertex k (j + 1),
      (if W.1 ≤ C.1 then upFun (k := k) (ℓ := j + 1) j F C else 0)
      = ∑ C : GrVertex k (j + 1),
          (if W.1 ≤ C.1 then (∑ H : GrVertex k j, if H.1 ≤ C.1 then F H else 0)
            else 0) := by
    refine Finset.sum_congr rfl (fun C _ => ?_)
    by_cases h : W.1 ≤ C.1
    · rw [if_pos h, if_pos h, upFun]
    · rw [if_neg h, if_neg h]
  have hcollapse :
      (∑ C : GrVertex k (j + 1),
          (if W.1 ≤ C.1 then (∑ H : GrVertex k j, if H.1 ≤ C.1 then F H else 0)
            else 0))
      = ∑ H : GrVertex k j,
          F H * (if H = W then (((2 ^ (k - j) - 1 : ℕ)) : ℚ)
            else if Module.finrank 𝔽₂ ↥(W.1 ⊓ H.1) = j - 1 then 1 else 0) := by
    rw [Commons.Combinatorics.Finset.sum_ite_ite
      (fun C : GrVertex k (j + 1) => W.1 ≤ C.1) (fun C H => H.1 ≤ C.1) F]
    exact Finset.sum_congr rfl (fun H _ => by rw [natCard_superspaces_both_cast W H])
  have hterm : ∀ H : GrVertex k j,
      F H * (if H = W then (((2 ^ (k - j) - 1 : ℕ)) : ℚ)
          else if Module.finrank 𝔽₂ ↥(W.1 ⊓ H.1) = j - 1 then 1 else 0)
        = (if H = W then F H * (((2 ^ (k - j) - 1 : ℕ)) : ℚ) else 0)
          + (if H = W then 0
            else if Module.finrank 𝔽₂ ↥(W.1 ⊓ H.1) = j - 1 then F H else 0) := by
    intro H
    by_cases h1 : H = W
    · simp [h1]
    · rw [if_neg h1, if_neg h1, if_neg h1]
      by_cases h2 : Module.finrank 𝔽₂ ↥(W.1 ⊓ H.1) = j - 1
      · rw [if_pos h2, if_pos h2]; ring
      · rw [if_neg h2, if_neg h2]; ring
  have hadj : (∑ H : GrVertex k j,
      (if H = W then 0
        else if Module.finrank 𝔽₂ ↥(W.1 ⊓ H.1) = j - 1 then F H else 0)) = adjOp F W := by
    rw [adjOp, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun H _ => ?_)
    rw [adj_iff_inf]
    by_cases h1 : H = W
    · subst h1
      simp
    · have h2 : ¬ W = H := fun h => h1 h.symm
      by_cases h3 : Module.finrank 𝔽₂ ↥(W.1 ⊓ H.1) = j - 1 <;> simp [h2, h1, h3]
  have hmain : (0 : ℚ) = F W * (((2 ^ (k - j) - 1 : ℕ)) : ℚ) + adjOp F W := by
    rw [← hsum, hunfold, hcollapse, Finset.sum_congr rfl (fun H _ => hterm H),
      Finset.sum_add_distrib, hadj,
      Finset.sum_ite_eq' Finset.univ W (fun H => F H * (((2 ^ (k - j) - 1 : ℕ)) : ℚ)),
      if_pos (Finset.mem_univ W)]
  have : adjOp F W = -(F W * (((2 ^ (k - j) - 1 : ℕ)) : ℚ)) := by linarith
  rw [this]; ring

/-! ## 3. Injectivity of the up operators -/

/-- `θ_j = -(2^j - 1)` (the bottom of the Eberlein sequence). -/
lemma thetaQ_self (k j : ℕ) : thetaQ k j j = -(((2 ^ j - 1 : ℕ)) : ℚ) := by
  rw [thetaQ_eq]
  have h1 : aNum k j j = 0 := by simp [aNum]
  have h2 : bNum j j = 1 := by simp [bNum]
  rw [h1, h2]; norm_num

/-- The `j = 0` case of the step injectivity. -/
lemma upFun_step_injective_zero (hk : 0 < k) (F : GrVertex k 0 → ℚ)
    (hF : upFun (k := k) (ℓ := 1) 0 F = 0) : F = 0 := by
  classical
  have huniq : ∀ W : GrVertex k 0, W = ⟨⊥, finrank_bot_eq_zero k⟩ :=
    fun W => Subtype.ext (Submodule.finrank_eq_zero.mp W.2)
  have hstep := upFun_step_eigen F hF ⟨⊥, finrank_bot_eq_zero k⟩
  have hadj : adjOp F ⟨⊥, finrank_bot_eq_zero k⟩ = 0 := by
    rw [adjOp]
    refine Finset.sum_eq_zero (fun H hH => ?_)
    rw [Finset.mem_filter] at hH
    rw [adj_iff_inf] at hH
    exact absurd (huniq H).symm hH.2.1
  rw [hadj] at hstep
  have hc : (((2 ^ (k - 0) - 1 : ℕ)) : ℚ) ≠ 0 := by
    have h2 : (2 : ℕ) ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    have : 0 < 2 ^ (k - 0) - 1 := by
      rw [Nat.sub_zero]; omega
    exact_mod_cast (ne_of_gt this)
  have hzero : F ⟨⊥, finrank_bot_eq_zero k⟩ = 0 := by
    have hmul : (((2 ^ (k - 0) - 1 : ℕ)) : ℚ) * F ⟨⊥, finrank_bot_eq_zero k⟩ = 0 := by
      have := hstep
      rw [neg_mul] at this
      exact neg_eq_zero.mp this.symm
    rcases mul_eq_zero.mp hmul with h | h
    · exact absurd h hc
    · exact h
  funext W
  rw [huniq W, hzero]
  simp

/-- **One-step injectivity.**  For `2j < k` the one-step up operator `Ψ_{j → j+1}` is
injective. -/
lemma upFun_step_injective (hkj : 2 * j < k) (F : GrVertex k j → ℚ)
    (hF : upFun (k := k) (ℓ := j + 1) j F = 0) : F = 0 := by
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h
    exact upFun_step_injective_zero (by omega) F hF
  · by_contra hne
    have heig : adjOpLM (k := k) (ℓ := j) F = (-(((2 ^ (k - j) - 1 : ℕ)) : ℚ)) • F := by
      funext W
      rw [adjOpLM_apply, Pi.smul_apply, smul_eq_mul]
      exact upFun_step_eigen F hF W
    obtain ⟨s, hs, hseq⟩ := adjOpLM_eigenvalue_mem (k := k) (ℓ := j) h hne heig
    have hcodim : j ≤ k - j := by omega
    have hle : thetaQ k j j ≤ thetaQ k j s := thetaQ_le_of_le hs le_rfl hcodim
    have hpow : (((2 ^ j - 1 : ℕ)) : ℚ) < (((2 ^ (k - j) - 1 : ℕ)) : ℚ) := by
      have hp : 2 ^ j < 2 ^ (k - j) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      have h1 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
      exact_mod_cast (show 2 ^ j - 1 < 2 ^ (k - j) - 1 by omega)
    rw [hseq.symm, thetaQ_self] at hle
    linarith

/-- **Factorisation of the up operators:**
`Ψ_{i+1→ℓ} ∘ Ψ_{i→i+1} = (2^(ℓ-i) - 1) • Ψ_{i→ℓ}`. -/
lemma upFun_comp (i ℓ : ℕ) (hi : i + 1 ≤ ℓ) (F : GrVertex k i → ℚ) (L : GrVertex k ℓ) :
    upFun (k := k) (ℓ := ℓ) (i + 1) (upFun (k := k) (ℓ := i + 1) i F) L
      = (((2 ^ (ℓ - i) - 1 : ℕ)) : ℚ) * upFun (k := k) (ℓ := ℓ) i F L := by
  classical
  have h1 : upFun (k := k) (ℓ := ℓ) (i + 1) (upFun (k := k) (ℓ := i + 1) i F) L
      = ∑ C : GrVertex k (i + 1), ∑ W : GrVertex k i,
          if (C.1 ≤ L.1 ∧ W.1 ≤ C.1) then F W else 0 := by
    simp only [upFun]
    refine Finset.sum_congr rfl (fun C _ => ?_)
    rw [ite_sum_eq]
    refine Finset.sum_congr rfl (fun W _ => ?_)
    by_cases hC : C.1 ≤ L.1 <;> by_cases hW : W.1 ≤ C.1 <;> simp [hC, hW]
  rw [h1, Finset.sum_comm]
  have h2 : ∀ W : GrVertex k i,
      (∑ C : GrVertex k (i + 1), if (C.1 ≤ L.1 ∧ W.1 ≤ C.1) then F W else 0)
        = F W * (if W.1 ≤ L.1 then (((2 ^ (ℓ - i) - 1 : ℕ)) : ℚ) else 0) := by
    intro W
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hcnt : (Finset.univ.filter
          (fun C : GrVertex k (i + 1) => C.1 ≤ L.1 ∧ W.1 ≤ C.1)).card
        = Nat.card {C : GrVertex k (i + 1) // W.1 ≤ C.1 ∧ C.1 ≤ L.1} := by
      rw [← Fintype.card_subtype (fun C : GrVertex k (i + 1) => C.1 ≤ L.1 ∧ W.1 ≤ C.1),
        ← Nat.card_eq_fintype_card]
      exact Nat.card_congr (Equiv.subtypeEquivRight (fun C => and_comm))
    rw [hcnt, card_subspaces_between (i + 1) (by omega) W L, bNum]
    have hidx : ℓ + 1 - (i + 1) = ℓ - i := by omega
    rw [hidx]
    push_cast
    by_cases hWL : W.1 ≤ L.1 <;> simp [hWL, mul_comm]
  rw [Finset.sum_congr rfl (fun W _ => h2 W), upFun, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun W _ => ?_)
  by_cases hWL : W.1 ≤ L.1 <;> simp [hWL, mul_comm]

/-- Injectivity propagates one step down. -/
lemma upFun_injective_of_injective_succ (i ℓ : ℕ) (hi : i + 1 ≤ ℓ) (hki : 2 * i < k)
    (h : Function.Injective (upFun (k := k) (ℓ := ℓ) (i + 1))) :
    Function.Injective (upFun (k := k) (ℓ := ℓ) i) := by
  intro F₁ F₂ hF
  have hcomp : upFun (k := k) (ℓ := ℓ) (i + 1) (upFun (k := k) (ℓ := i + 1) i F₁)
      = upFun (k := k) (ℓ := ℓ) (i + 1) (upFun (k := k) (ℓ := i + 1) i F₂) := by
    funext L
    rw [upFun_comp i ℓ hi F₁ L, upFun_comp i ℓ hi F₂ L, hF]
  have hsub : upFun (k := k) (ℓ := i + 1) i F₁ = upFun (k := k) (ℓ := i + 1) i F₂ := h hcomp
  have hzero : upFun (k := k) (ℓ := i + 1) i (F₁ - F₂) = 0 := by
    have : (upLM (k := k) (ℓ := i + 1) i) (F₁ - F₂) = 0 := by
      rw [map_sub, upLM_apply, upLM_apply, hsub, sub_self]
    rwa [upLM_apply] at this
  have := upFun_step_injective hki (F₁ - F₂) hzero
  exact sub_eq_zero.mp this

/-- **Injectivity of the up operators.**  If `i ≤ ℓ` and `2(ℓ-1) < k` (in particular if
`2ℓ ≤ k`) then `Ψ_{i→ℓ}` is injective. -/
theorem upFun_injective (i ℓ : ℕ) (hiℓ : i ≤ ℓ) (hk : 2 * (ℓ - 1) < k) :
    Function.Injective (upFun (k := k) (ℓ := ℓ) i) := by
  suffices ∀ d i ℓ : ℕ, ℓ - i = d → i ≤ ℓ → 2 * (ℓ - 1) < k →
      Function.Injective (upFun (k := k) (ℓ := ℓ) i) by
    exact this (ℓ - i) i ℓ rfl hiℓ hk
  intro d
  induction d with
  | zero =>
      intro i ℓ hd hiℓ hk
      have hieq : i = ℓ := by omega
      subst hieq
      intro a b hab
      simpa [upFun_self] using hab
  | succ d ih =>
      intro i ℓ hd hiℓ hk
      have hsucc : ℓ - (i + 1) = d := by omega
      have hinj : Function.Injective (upFun (k := k) (ℓ := ℓ) (i + 1)) :=
        ih (i + 1) ℓ hsucc (by omega) hk
      exact upFun_injective_of_injective_succ i ℓ (by omega) (by omega) hinj

/-! ## 4. Consequences: the level spaces have the right dimensions -/

/-- The `ℚ`-linear map form of `upFun`. -/
lemma upLM_injective (i ℓ : ℕ) (hiℓ : i ≤ ℓ) (hk : 2 * (ℓ - 1) < k) :
    Function.Injective (upLM (k := k) (ℓ := ℓ) i) := by
  intro a b hab
  refine upFun_injective i ℓ hiℓ hk ?_
  simpa [upLM_apply] using hab

/-- **The dimension of the level-`i` space.**  For `i ≤ ℓ` with `2(ℓ-1) < k`,
`dim V_i = [k choose i]_2`. -/
theorem finrank_Vup (i ℓ : ℕ) (hiℓ : i ≤ ℓ) (hk : 2 * (ℓ - 1) < k) :
    Module.finrank ℚ (Vup (k := k) (ℓ := ℓ) i) = grCount k i := by
  have hker : LinearMap.ker (upLM (k := k) (ℓ := ℓ) i) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (upLM_injective i ℓ hiℓ hk)
  have hfr := LinearMap.finrank_range_add_finrank_ker (upLM (k := k) (ℓ := ℓ) i)
  rw [hker, finrank_bot, add_zero] at hfr
  show Module.finrank ℚ (LinearMap.range (upLM (k := k) (ℓ := ℓ) i)) = grCount k i
  rw [hfr, Module.finrank_fintype_fun_eq_card, card_GrVertex_eq_grCount]

/-! ## 5. Consequences: the Eberlein eigenvalues are all attained -/

/-- The Gaussian binomial is strictly increasing below half the dimension. -/
lemma grCount_lt_succ {i : ℕ} (h : 2 * i + 2 ≤ k) : grCount k i < grCount k (i + 1) :=
  Commons.LinearAlgebra.Submodule.card_submodule_finrank_strictMono (K := 𝔽₂)
    (V := Fin k → 𝔽₂) (m := i) (by rwa [finrank_fin_fun])

/-- The dimension of the level-`i` space, in the form `2ℓ ≤ k`. -/
lemma finrank_Vup_le (i ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hiℓ : i ≤ ℓ) (hk : 2 * ℓ ≤ k) :
    Module.finrank ℚ (Vup (k := k) (ℓ := ℓ) i) = grCount k i :=
  finrank_Vup i ℓ hiℓ (by omega)

/-- The level spaces `V_i` are strictly increasing (for `2ℓ ≤ k`). -/
lemma Vup_lt_succ (i ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hi : i + 1 ≤ ℓ) (hk : 2 * ℓ ≤ k) :
    Vup (k := k) (ℓ := ℓ) i < Vup (k := k) (ℓ := ℓ) (i + 1) := by
  refine lt_of_le_of_ne
    (Vup_pred_le (k := k) (ℓ := ℓ) (by omega) (i + 1) (by omega) hi) ?_
  intro heq
  have h1 : Module.finrank ℚ (Vup (k := k) (ℓ := ℓ) i) = grCount k i :=
    finrank_Vup_le i ℓ hℓ (by omega) hk
  have h2 : Module.finrank ℚ (Vup (k := k) (ℓ := ℓ) (i + 1)) = grCount k (i + 1) :=
    finrank_Vup_le (i + 1) ℓ hℓ hi hk
  have h3 : grCount k i < grCount k (i + 1) := grCount_lt_succ (k := k) (i := i) (by omega)
  have hfin : Module.finrank ℚ (Vup (k := k) (ℓ := ℓ) i)
      = Module.finrank ℚ (Vup (k := k) (ℓ := ℓ) (i + 1)) := by rw [heq]
  rw [h1, h2] at hfin
  omega

/-- `θ_0 = degree` is an eigenvalue (the constants). -/
lemma exists_eigenvector_theta_zero {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hk : ℓ ≤ k) :
    ∃ v : GrVertex k ℓ → ℚ, v ≠ 0 ∧ adjOpLM (k := k) (ℓ := ℓ) v = thetaQ k ℓ 0 • v := by
  classical
  obtain ⟨L⟩ := nonempty_GrVertex_of_le (k := k) (ℓ := ℓ) hk
  refine ⟨fun _ => 1, ?_, ?_⟩
  · intro h
    have hL := congrFun h L
    simp at hL
  · funext M
    rw [adjOpLM_apply, Pi.smul_apply, smul_eq_mul,
      adjOp_const' (k := k) (ℓ := ℓ) hℓ (1 : ℚ) M, thetaQ_zero_eq_degree (k := k) (ℓ := ℓ) hℓ]

/-- **Every Eberlein eigenvalue `θ_i` (`1 ≤ i ≤ ℓ`) is attained**, when `2ℓ ≤ k`. -/
theorem exists_eigenvector_theta {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (i : ℕ) (hi : 1 ≤ i) (hiℓ : i ≤ ℓ)
    (hk : 2 * ℓ ≤ k) :
    ∃ v : GrVertex k ℓ → ℚ, v ≠ 0 ∧ adjOpLM (k := k) (ℓ := ℓ) v = thetaQ k ℓ i • v := by
  classical
  set φ : (↥(Vup (k := k) (ℓ := ℓ) i)) →ₗ[ℚ] (GrVertex k ℓ → ℚ) :=
    (adjOpLM (k := k) (ℓ := ℓ) -
      (thetaQ k ℓ i) • (1 : (GrVertex k ℓ → ℚ) →ₗ[ℚ] (GrVertex k ℓ → ℚ))).comp
        (Vup (k := k) (ℓ := ℓ) i).subtype with hφ
  have hφapply : ∀ v : ↥(Vup (k := k) (ℓ := ℓ) i),
      φ v = adjOpLM (k := k) (ℓ := ℓ) v.1 - thetaQ k ℓ i • v.1 := fun v => rfl
  have hrange : LinearMap.range φ ≤ Vup (k := k) (ℓ := ℓ) (i - 1) := by
    rintro _ ⟨v, rfl⟩
    rw [hφapply v]
    exact adjOpLM_sub_mem_Vup_pred (k := k) (ℓ := ℓ) hℓ i hi hiℓ v.2
  have hlt : Module.finrank ℚ (↥(Vup (k := k) (ℓ := ℓ) (i - 1)))
      < Module.finrank ℚ (↥(Vup (k := k) (ℓ := ℓ) i)) := by
    have h := Vup_lt_succ (k := k) (ℓ := ℓ) (i - 1) hℓ (by omega) hk
    rw [show i - 1 + 1 = i by omega] at h
    exact Submodule.finrank_lt_finrank_of_lt h
  have hker : LinearMap.ker φ ≠ ⊥ := by
    intro hbot
    have hfr := LinearMap.finrank_range_add_finrank_ker φ
    rw [hbot, finrank_bot, add_zero] at hfr
    have := Submodule.finrank_mono hrange
    omega
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨w.1, ?_, ?_⟩
  · intro h
    exact hw0 (Subtype.ext h)
  · have h1 : φ w = 0 := hw
    rw [hφapply w] at h1
    exact sub_eq_zero.mp h1


end

end F2
end Submission.Grassmann
