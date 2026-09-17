import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_denom_mul_Kostant
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_weyl_denom_support
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_qZ_rho_sub_wact
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_wact_small_height_length
import Submission.Commons.Combinatorics.Finset.sum_powerset_erase
import Submission.Commons.Combinatorics.Finset.sum_powerset_erase_pair
import Submission.Commons.Algebra.BigOperators.Dcoef_erase_telescope_pair
import Submission.Commons.Algebra.BigOperators.Dcoef_erase_telescope

set_option maxHeartbeats 3200000

open scoped BigOperators

namespace Commons.LinearAlgebra.Matrix.Cartan

/-! ## The pairing `⟪β,β'⟫ = β ⬝ A⁻¹ β'` in the form used by the target statement -/

/-- The lattice pairing in the form of the target statement. -/
def bform (x y : Fin 8 → ℤ) : ℤ := ∑ i, x i * (E8NormTwo.E8inv.mulVec y) i

lemma bform_eq_bil (x y : Fin 8 → ℤ) : bform x y = bil x y := rfl

/-! ## The Weyl-denominator coefficient functional -/

/-- The coefficient of `e^{-ν}` in the Weyl denominator for a finset `L` of positive roots,
`∑_{T ⊆ L} (-1)^{|T|} [∑_{α∈T} α = ν]`. -/
noncomputable def Dcoef (L : Finset (Fin 8 → ℤ)) (ν : Fin 8 → ℤ) : ℤ :=
  ∑ T ∈ L.powerset, (if (∑ α ∈ T, α) = ν then (-1 : ℤ) ^ T.card else 0)

noncomputable def Dc (ν : Fin 8 → ℤ) : ℤ := Dcoef E8posRoots.P ν

/-! ## The two pieces of the target summation -/

noncomputable def gpair (N : ℕ) (ν : Fin 8 → ℤ) : ℤ :=
  ∑ β ∈ E8posRoots.P, ∑ β' ∈ E8posRoots.P,
    ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
      (if n • β + m • β' = ν then (if β = β' then 0 else bform β β') else 0)

noncomputable def gsing (N : ℕ) (ν : Fin 8 → ℤ) : ℤ :=
  ∑ β ∈ E8posRoots.P, ∑ n ∈ Finset.Icc 1 N,
    (if n • β = ν then (E8NormTwo.e8ht β - 1) else 0)

noncomputable def gc (N : ℕ) (ν : Fin 8 → ℤ) : ℤ := gpair N ν + 2 * gsing N ν

/-! ## Elementary height facts -/

lemma coords_add' (a b : Fin 8 → ℤ) : coords (a + b) = coords a + coords b := by
  simp only [coords, Matrix.mulVec_add]

lemma coords_nsmul (n : ℕ) (v : Fin 8 → ℤ) : coords (n • v) = n • coords v := by
  induction n with
  | zero => simp [coords]
  | succ n ih => rw [succ_nsmul, coords_add', ih, succ_nsmul]

lemma e8ht_neg (v : Fin 8 → ℤ) : E8NormTwo.e8ht (-v) = - E8NormTwo.e8ht v := by
  simp only [e8ht_eq_sum_coords, coords_neg', Pi.neg_apply, Finset.sum_neg_distrib]

lemma e8ht_nsmul (n : ℕ) (v : Fin 8 → ℤ) :
    E8NormTwo.e8ht (n • v) = n * E8NormTwo.e8ht v := by
  rw [e8ht_eq_sum_coords, coords_nsmul, e8ht_eq_sum_coords]
  simp only [Pi.smul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => nsmul_eq_mul n (coords v i))

lemma e8ht_zero : E8NormTwo.e8ht (0 : Fin 8 → ℤ) = 0 := by
  have h := e8ht_add (0 : Fin 8 → ℤ) 0
  simp only [add_zero] at h; omega

lemma e8ht_sum' (s : Finset (Fin 8 → ℤ)) :
    E8NormTwo.e8ht (∑ y ∈ s, y) = ∑ y ∈ s, E8NormTwo.e8ht y :=
  e8ht_sum s

lemma e8ht_mem_P_nonneg {y : Fin 8 → ℤ} (hy : y ∈ E8posRoots.P) :
    0 ≤ E8NormTwo.e8ht y := le_trans (by norm_num : (0:ℤ) ≤ 1) (one_le_e8ht_of_mem_P hy)


/-! ## The reflection recursion for the Weyl-denominator functional -/

lemma Dcoef_erase (L : Finset (Fin 8 → ℤ)) (β : Fin 8 → ℤ) (hβ : β ∈ L)
    (ν : Fin 8 → ℤ) :
    Dcoef L ν = Dcoef (L.erase β) ν - Dcoef (L.erase β) (ν - β) := by
  unfold Dcoef
  have hins : insert β (L.erase β) = L := Finset.insert_erase hβ
  have hnot : β ∉ L.erase β := Finset.notMem_erase β L
  conv_lhs => rw [← hins]
  rw [Finset.sum_powerset_insert hnot, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro T hT
  rw [Finset.mem_powerset] at hT
  have hnotT : β ∉ T := fun h => hnot (hT h)
  rw [Finset.sum_insert hnotT, Finset.card_insert_of_notMem hnotT]
  by_cases hc : (β + ∑ a ∈ T, a) = ν
  · rw [if_pos hc]
    have hc' : (∑ a ∈ T, a) = ν - β := by rw [← hc]; abel
    rw [if_pos hc', pow_succ]
    ring
  · rw [if_neg hc]
    have hc' : ¬ ((∑ a ∈ T, a) = ν - β) := by intro h; exact hc (by rw [h]; abel)
    rw [if_neg hc', neg_zero]

lemma Dcoef_eq_zero_of_ht_neg (L : Finset (Fin 8 → ℤ))
    (hL : ∀ a ∈ L, 0 ≤ E8NormTwo.e8ht a) (ν : Fin 8 → ℤ) (hν : E8NormTwo.e8ht ν < 0) :
    Dcoef L ν = 0 := by
  unfold Dcoef
  apply Finset.sum_eq_zero
  intro T hT
  rw [Finset.mem_powerset] at hT
  by_cases hc : (∑ a ∈ T, a) = ν
  · exfalso
    have h1 : E8NormTwo.e8ht (∑ a ∈ T, a) = ∑ a ∈ T, E8NormTwo.e8ht a := e8ht_sum T
    rw [hc] at h1
    have hnn : 0 ≤ ∑ a ∈ T, E8NormTwo.e8ht a :=
      Finset.sum_nonneg (fun a ha => hL a (hT ha))
    omega
  · rw [if_neg hc]

lemma mem_erase_ht_pos {L : Finset (Fin 8 → ℤ)} {β : Fin 8 → ℤ} (_hβ : β ∈ L)
    (hL : ∀ a ∈ L, 1 ≤ E8NormTwo.e8ht a) :
    ∀ a ∈ L.erase β, 0 ≤ E8NormTwo.e8ht a :=
  fun a ha => le_trans (by norm_num : (0:ℤ) ≤ 1) (hL a (Finset.mem_of_mem_erase ha))



/-! ## Swapping the Weyl-denominator sum inside the two target sums -/

lemma pair_summand (β β' : Fin 8 → ℤ) (n m : ℕ) (ν : Fin 8 → ℤ) :
    (∑ T ∈ E8posRoots.P.powerset,
        (-1:ℤ)^T.card *
          (if n • β + m • β' = ν - ∑ a ∈ T, a then
            (if β = β' then 0 else bform β β') else 0))
      = (if β = β' then 0 else bform β β') * Dc (ν - n • β - m • β') := by
  rw [Dc, Dcoef, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  by_cases h : (∑ a ∈ T, a) = ν - n • β - m • β'
  · have h' : n • β + m • β' = ν - ∑ a ∈ T, a := by rw [h]; abel
    rw [if_pos h', if_pos h]
    ring
  · have h' : ¬ (n • β + m • β' = ν - ∑ a ∈ T, a) := by
      intro hh
      apply h
      rw [show ν - n • β - m • β' = ν - (n • β + m • β') from by abel, hh]
      abel
    rw [if_neg h', if_neg h]
    ring

lemma sing_summand (β : Fin 8 → ℤ) (n : ℕ) (ν : Fin 8 → ℤ) :
    (∑ T ∈ E8posRoots.P.powerset,
        (-1:ℤ)^T.card * (if n • β = ν - ∑ a ∈ T, a then (E8NormTwo.e8ht β - 1) else 0))
      = (E8NormTwo.e8ht β - 1) * Dc (ν - n • β) := by
  rw [Dc, Dcoef, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  by_cases h : (∑ a ∈ T, a) = ν - n • β
  · have h' : n • β = ν - ∑ a ∈ T, a := by rw [h]; abel
    rw [if_pos h', if_pos h]
    ring
  · have h' : ¬ (n • β = ν - ∑ a ∈ T, a) := by
      intro hh
      apply h
      rw [show ν - n • β = ν - (n • β) from rfl, hh]
      abel
    rw [if_neg h', if_neg h]
    ring

lemma sum_powerset_gpair_swap (N : ℕ) (ν : Fin 8 → ℤ) :
    (∑ T ∈ E8posRoots.P.powerset, (-1:ℤ)^T.card * gpair N (ν - ∑ a ∈ T, a))
      = ∑ β ∈ E8posRoots.P, ∑ β' ∈ E8posRoots.P,
          ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
            (if β = β' then 0 else bform β β') * Dc (ν - n • β - m • β') := by
  have h1 : ∀ T ∈ E8posRoots.P.powerset,
      (-1:ℤ)^T.card * gpair N (ν - ∑ a ∈ T, a)
      = ∑ β ∈ E8posRoots.P, ∑ β' ∈ E8posRoots.P,
          ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
            (-1:ℤ)^T.card *
              (if n • β + m • β' = ν - ∑ a ∈ T, a then
                (if β = β' then 0 else bform β β') else 0) := by
    intro T hT
    rw [gpair]
    simp only [Finset.mul_sum]
  calc (∑ T ∈ E8posRoots.P.powerset, (-1:ℤ)^T.card * gpair N (ν - ∑ a ∈ T, a))
      = ∑ T ∈ E8posRoots.P.powerset, ∑ β ∈ E8posRoots.P, ∑ β' ∈ E8posRoots.P,
          ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
            (-1:ℤ)^T.card *
              (if n • β + m • β' = ν - ∑ a ∈ T, a then
                (if β = β' then 0 else bform β β') else 0) :=
          Finset.sum_congr rfl h1
    _ = ∑ β ∈ E8posRoots.P, ∑ β' ∈ E8posRoots.P,
          ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N, ∑ T ∈ E8posRoots.P.powerset,
            (-1:ℤ)^T.card *
              (if n • β + m • β' = ν - ∑ a ∈ T, a then
                (if β = β' then 0 else bform β β') else 0) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro β hβ
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro β' hβ'
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro n hn
          rw [Finset.sum_comm]
    _ = ∑ β ∈ E8posRoots.P, ∑ β' ∈ E8posRoots.P,
          ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
            (if β = β' then 0 else bform β β') * Dc (ν - n • β - m • β') := by
          apply Finset.sum_congr rfl; intro β hβ
          apply Finset.sum_congr rfl; intro β' hβ'
          apply Finset.sum_congr rfl; intro n hn
          apply Finset.sum_congr rfl; intro m hm
          exact pair_summand β β' n m ν

lemma sum_powerset_gsing_swap (N : ℕ) (ν : Fin 8 → ℤ) :
    (∑ T ∈ E8posRoots.P.powerset, (-1:ℤ)^T.card * gsing N (ν - ∑ a ∈ T, a))
      = ∑ β ∈ E8posRoots.P, ∑ n ∈ Finset.Icc 1 N,
          (E8NormTwo.e8ht β - 1) * Dc (ν - n • β) := by
  have h1 : ∀ T ∈ E8posRoots.P.powerset,
      (-1:ℤ)^T.card * gsing N (ν - ∑ a ∈ T, a)
      = ∑ β ∈ E8posRoots.P, ∑ n ∈ Finset.Icc 1 N,
            (-1:ℤ)^T.card *
              (if n • β = ν - ∑ a ∈ T, a then (E8NormTwo.e8ht β - 1) else 0) := by
    intro T hT
    rw [gsing]
    simp only [Finset.mul_sum]
  calc (∑ T ∈ E8posRoots.P.powerset, (-1:ℤ)^T.card * gsing N (ν - ∑ a ∈ T, a))
      = ∑ T ∈ E8posRoots.P.powerset, ∑ β ∈ E8posRoots.P, ∑ n ∈ Finset.Icc 1 N,
            (-1:ℤ)^T.card *
              (if n • β = ν - ∑ a ∈ T, a then (E8NormTwo.e8ht β - 1) else 0) :=
          Finset.sum_congr rfl h1
    _ = ∑ β ∈ E8posRoots.P, ∑ n ∈ Finset.Icc 1 N, ∑ T ∈ E8posRoots.P.powerset,
            (-1:ℤ)^T.card *
              (if n • β = ν - ∑ a ∈ T, a then (E8NormTwo.e8ht β - 1) else 0) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro β hβ
          rw [Finset.sum_comm]
    _ = ∑ β ∈ E8posRoots.P, ∑ n ∈ Finset.Icc 1 N,
          (E8NormTwo.e8ht β - 1) * Dc (ν - n • β) := by
          apply Finset.sum_congr rfl; intro β hβ
          apply Finset.sum_congr rfl; intro n hn
          exact sing_summand β n ν



/-! ## Subset bookkeeping -/

/-- The sum of the elements of a finset of weights. -/
abbrev Sig (T : Finset (Fin 8 → ℤ)) : Fin 8 → ℤ := ∑ a ∈ T, a

lemma Sig_erase {T : Finset (Fin 8 → ℤ)} {β : Fin 8 → ℤ} (hβ : β ∈ T) :
    Sig (T.erase β) = Sig T - β := by
  unfold Sig
  have h := Finset.sum_erase_add T (fun a => a) hβ
  rw [← h]; abel

lemma Sig_erase_erase {T : Finset (Fin 8 → ℤ)} {β β' : Fin 8 → ℤ}
    (hβ : β ∈ T) (hβ' : β' ∈ T.erase β) :
    Sig ((T.erase β).erase β') = Sig T - β - β' := by
  rw [Sig_erase hβ', Sig_erase hβ]

lemma card_erase_erase {T : Finset (Fin 8 → ℤ)} {β β' : Fin 8 → ℤ}
    (hβ : β ∈ T) (hβ' : β' ∈ T.erase β) :
    ((T.erase β).erase β').card = T.card - 2 := by
  rw [Finset.card_erase_of_mem hβ', Finset.card_erase_of_mem hβ, Nat.sub_sub]

lemma neg_one_pow_card_erase_erase {T : Finset (Fin 8 → ℤ)} {β β' : Fin 8 → ℤ}
    (hβ : β ∈ T) (hβ' : β' ∈ T.erase β) :
    (-1:ℤ)^((T.erase β).erase β').card = (-1:ℤ)^T.card := by
  rw [card_erase_erase hβ hβ']
  have h1 : 1 ≤ (T.erase β).card := Finset.card_pos.mpr ⟨β', hβ'⟩
  have h2 : 2 ≤ T.card := by
    have h3 : T.card = (T.erase β).card + 1 := by
      rw [Finset.card_erase_of_mem hβ, Nat.sub_add_cancel (Finset.card_pos.mpr ⟨β, hβ⟩)]
    omega
  have hc : T.card - 2 + 2 = T.card := Nat.sub_add_cancel h2
  conv_rhs => rw [← hc, pow_add]
  ring

lemma neg_one_pow_card_erase {T : Finset (Fin 8 → ℤ)} {β : Fin 8 → ℤ} (hβ : β ∈ T) :
    (-1:ℤ)^(T.erase β).card = - (-1:ℤ)^T.card := by
  rw [Finset.card_erase_of_mem hβ]
  have h1 : 1 ≤ T.card := Finset.card_pos.mpr ⟨β, hβ⟩
  have hc : T.card - 1 + 1 = T.card := Nat.sub_add_cancel h1
  conv_rhs => rw [← hc, pow_add]
  ring



/-! ## Reindexing the pair-sum and the height-sum into sums over subsets -/

lemma X1_eq (ν : Fin 8 → ℤ) :
    (∑ β ∈ E8posRoots.P, ∑ β' ∈ E8posRoots.P.erase β,
        bform β β' * Dcoef ((E8posRoots.P.erase β).erase β') (ν - β - β'))
    = ∑ T ∈ E8posRoots.P.powerset,
        (-1:ℤ)^T.card * (if Sig T = ν then (1:ℤ) else 0) *
          (∑ β ∈ T, ∑ β' ∈ T.erase β, bform β β') := by
  have hf : ∀ β β' : Fin 8 → ℤ,
      bform β β' * Dcoef ((E8posRoots.P.erase β).erase β') (ν - β - β')
      = ∑ S ∈ ((E8posRoots.P.erase β).erase β').powerset,
          bform β β' * ((-1:ℤ)^S.card *
            (if β + β' + Sig S = ν then (1:ℤ) else 0)) := by
    intro β β'
    unfold Dcoef
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S hS
    congr 1
    by_cases h : Sig S = ν - β - β'
    · have h' : β + β' + Sig S = ν := by rw [h]; abel
      rw [if_pos h, if_pos h', mul_one]
    · have h' : ¬ (β + β' + Sig S = ν) := by
        intro hh
        exact h (by rw [show ν - β - β' = ν - (β + β') from by abel, ← hh]; abel)
      rw [if_neg h, if_neg h', mul_zero]
  simp only [hf]
  rw [Commons.Combinatorics.Finset.sum_powerset_erase_pair]
  apply Finset.sum_congr rfl
  intro T hT
  rw [Finset.mem_powerset] at hT
  have hsimp : ∀ β ∈ T, ∀ β' ∈ T.erase β,
      bform β β' * ((-1:ℤ)^((T.erase β).erase β').card *
        (if β + β' + Sig ((T.erase β).erase β') = ν then (1:ℤ) else 0))
      = (-1:ℤ)^T.card * (if Sig T = ν then (1:ℤ) else 0) * bform β β' := by
    intro β hβT β' hβ'T
    rw [Sig_erase_erase hβT hβ'T, neg_one_pow_card_erase_erase hβT hβ'T]
    have hc : (β + β' + (Sig T - β - β') = ν) ↔ (Sig T = ν) := by
      constructor
      · intro h; rw [← h]; abel
      · intro h; rw [h]; abel
    rw [if_congr hc rfl rfl]
    ring
  rw [Finset.sum_congr rfl (fun β hβ =>
    Finset.sum_congr rfl (fun β' hβ' => hsimp β hβ β' hβ'))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro β hβ
  rw [Finset.mul_sum]

lemma X2_eq (ν : Fin 8 → ℤ) :
    (∑ β ∈ E8posRoots.P, (E8NormTwo.e8ht β - 1) * Dcoef (E8posRoots.P.erase β) (ν - β))
    = - ∑ T ∈ E8posRoots.P.powerset,
        (-1:ℤ)^T.card * (if Sig T = ν then (1:ℤ) else 0) *
          (∑ β ∈ T, (E8NormTwo.e8ht β - 1)) := by
  have hf : ∀ β : Fin 8 → ℤ,
      (E8NormTwo.e8ht β - 1) * Dcoef (E8posRoots.P.erase β) (ν - β)
      = ∑ S ∈ (E8posRoots.P.erase β).powerset,
          (E8NormTwo.e8ht β - 1) * ((-1:ℤ)^S.card *
            (if β + Sig S = ν then (1:ℤ) else 0)) := by
    intro β
    unfold Dcoef
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S hS
    congr 1
    by_cases h : Sig S = ν - β
    · have h' : β + Sig S = ν := by rw [h]; abel
      rw [if_pos h, if_pos h', mul_one]
    · have h' : ¬ (β + Sig S = ν) := by
        intro hh
        exact h (by rw [show ν - β = ν - (β + 0) from by abel, ← hh]; abel)
      rw [if_neg h, if_neg h', mul_zero]
  simp only [hf]
  rw [Commons.Combinatorics.Finset.sum_powerset_erase]
  have hsimp : ∀ T ∈ E8posRoots.P.powerset, ∀ β ∈ T,
      (E8NormTwo.e8ht β - 1) * ((-1:ℤ)^(T.erase β).card *
        (if β + Sig (T.erase β) = ν then (1:ℤ) else 0))
      = - ((-1:ℤ)^T.card * (if Sig T = ν then (1:ℤ) else 0) *
          (E8NormTwo.e8ht β - 1)) := by
    intro T hT β hβT
    rw [Sig_erase hβT, neg_one_pow_card_erase hβT]
    have hc : (β + (Sig T - β) = ν) ↔ (Sig T = ν) := by
      constructor
      · intro h; rw [← h]; abel
      · intro h; rw [h]; abel
    rw [if_congr hc rfl rfl]
    ring
  rw [Finset.sum_congr rfl (fun T hT =>
    Finset.sum_congr rfl (fun β hβ => hsimp T hT β hβ))]
  simp only [Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro T hT
  rw [Finset.mul_sum]



/-! ## The algebraic bracket `∑_{β≠β'∈T}⟪β,β'⟫ - 2∑_{β∈T}(ht β - 1) = ⟪ν,ν⟫ - 2 ht ν` -/

lemma bil_sum_left (s : Finset (Fin 8 → ℤ)) (v : Fin 8 → ℤ) :
    bil (∑ a ∈ s, a) v = ∑ a ∈ s, bil a v := by
  unfold bil
  rw [sum_dotProduct]

lemma coords_sum (s : Finset (Fin 8 → ℤ)) :
    coords (∑ a ∈ s, a) = ∑ a ∈ s, coords a := by
  change E8NormTwo.E8inv.mulVec (∑ a ∈ s, a) = ∑ a ∈ s, E8NormTwo.E8inv.mulVec a
  rw [Matrix.mulVec_sum]

lemma bil_sum_right (s : Finset (Fin 8 → ℤ)) (u : Fin 8 → ℤ) :
    bil u (∑ a ∈ s, a) = ∑ a ∈ s, bil u a := by
  unfold bil
  rw [coords_sum, dotProduct_sum]

lemma bracket_eq (T : Finset (Fin 8 → ℤ)) (hT : T ⊆ E8posRoots.P) (ν : Fin 8 → ℤ)
    (hν : Sig T = ν) :
    (∑ β ∈ T, ∑ β' ∈ T.erase β, bform β β') - 2 * (∑ β ∈ T, (E8NormTwo.e8ht β - 1))
      = E8NormTwo.qZ ν - 2 * E8NormTwo.e8ht ν := by
  have hA : (∑ β ∈ T, ∑ β' ∈ T.erase β, bform β β')
      = (∑ β ∈ T, ∑ β' ∈ T, bform β β') - ∑ β ∈ T, bform β β := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro β hβ
    have h := Finset.sum_erase_add T (fun β' => bform β β') hβ
    rw [← h]; abel
  have hB : (∑ β ∈ T, ∑ β' ∈ T, bform β β') = E8NormTwo.qZ ν := by
    have h2 : (∑ β ∈ T, ∑ β' ∈ T, bform β β') = bil (Sig T) (Sig T) := by
      rw [bil_sum_left]
      apply Finset.sum_congr rfl
      intro a ha
      exact (bil_sum_right T a).symm
    rw [h2, hν, qZ_eq_bil]
  have hC : (∑ β ∈ T, bform β β) = 2 * (T.card : ℤ) := by
    have h2 : ∀ β ∈ T, bform β β = (2:ℤ) := by
      intro β hβ
      rw [bform_eq_bil, (qZ_eq_bil β).symm]
      exact ((E8posRoots.memP β).mp (hT hβ)).1
    calc (∑ β ∈ T, bform β β) = ∑ β ∈ T, (2:ℤ) := Finset.sum_congr rfl h2
      _ = 2 * (T.card : ℤ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hD : (∑ β ∈ T, (E8NormTwo.e8ht β - 1)) = E8NormTwo.e8ht ν - (T.card : ℤ) := by
    have h2 : (∑ β ∈ T, (E8NormTwo.e8ht β - 1))
        = (∑ β ∈ T, E8NormTwo.e8ht β) - ∑ β ∈ T, (1:ℤ) := by
      rw [Finset.sum_sub_distrib]
    rw [h2, Finset.sum_const, ← e8ht_sum T]
    rw [show (∑ y ∈ T, y) = ν from hν]
    simp
  rw [hA, hB, hC, hD]; ring



/-! ## Monotonicity of the truncated sums in the truncation bound -/

lemma le_ht_of_comb {μ β β' : Fin 8 → ℤ} (hβ : β ∈ E8posRoots.P) (hβ' : β' ∈ E8posRoots.P)
    {n m : ℕ} (h : n • β + m • β' = μ) : (m : ℤ) ≤ E8NormTwo.e8ht μ := by
  rw [← h, e8ht_add, e8ht_nsmul, e8ht_nsmul]
  have h1 : 1 ≤ E8NormTwo.e8ht β := one_le_e8ht_of_mem_P hβ
  have h2 : 1 ≤ E8NormTwo.e8ht β' := one_le_e8ht_of_mem_P hβ'
  have hn : (0:ℤ) ≤ (n:ℤ) * E8NormTwo.e8ht β := by positivity
  nlinarith [hn, h2]

lemma le_ht_of_comb_left {μ β β' : Fin 8 → ℤ} (hβ : β ∈ E8posRoots.P)
    (hβ' : β' ∈ E8posRoots.P) {n m : ℕ} (h : n • β + m • β' = μ) :
    (n : ℤ) ≤ E8NormTwo.e8ht μ := by
  rw [← h, e8ht_add, e8ht_nsmul, e8ht_nsmul]
  have h1 : 1 ≤ E8NormTwo.e8ht β := one_le_e8ht_of_mem_P hβ
  have h2 : 1 ≤ E8NormTwo.e8ht β' := one_le_e8ht_of_mem_P hβ'
  have hm : (0:ℤ) ≤ (m:ℤ) * E8NormTwo.e8ht β' := by positivity
  nlinarith [hm, h1]

lemma le_ht_of_smul {μ β : Fin 8 → ℤ} (hβ : β ∈ E8posRoots.P) {n : ℕ}
    (h : n • β = μ) : (n : ℤ) ≤ E8NormTwo.e8ht μ := by
  rw [← h, e8ht_nsmul]
  have h1 : 1 ≤ E8NormTwo.e8ht β := one_le_e8ht_of_mem_P hβ
  have hn : (0:ℤ) ≤ (n:ℤ) * E8NormTwo.e8ht β := by positivity
  nlinarith [hn, h1]

lemma false_of_toNat_lt {a : ℤ} {m : ℕ} (h : (m:ℤ) ≤ a) (hM : a.toNat < m) : False := by
  by_cases ha : 0 ≤ a
  · have h1 : (a.toNat : ℤ) < (m:ℤ) := by exact_mod_cast hM
    rw [Int.toNat_of_nonneg ha] at h1
    omega
  · push Not at ha
    rw [Int.toNat_of_nonpos (le_of_lt ha)] at hM
    omega

lemma gsing_eq_of_le {N : ℕ} {μ : Fin 8 → ℤ} (hN : (E8NormTwo.e8ht μ).toNat ≤ N) :
    gsing N μ = gsing ((E8NormTwo.e8ht μ).toNat) μ := by
  unfold gsing
  apply Finset.sum_congr rfl
  intro β hβ
  refine (Finset.sum_subset ?_ ?_).symm
  · intro n hn
    rw [Finset.mem_Icc] at hn ⊢
    exact ⟨hn.1, le_trans hn.2 hN⟩
  · intro n hnN hnM
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hnN).1
    have hlt : (E8NormTwo.e8ht μ).toNat < n := by
      by_contra h
      exact hnM (Finset.mem_Icc.mpr ⟨hn1, not_lt.mp h⟩)
    rw [if_neg]
    intro hc
    exact false_of_toNat_lt (le_ht_of_smul hβ hc) hlt

lemma gpair_eq_of_le {N : ℕ} {μ : Fin 8 → ℤ} (hN : (E8NormTwo.e8ht μ).toNat ≤ N) :
    gpair N μ = gpair ((E8NormTwo.e8ht μ).toNat) μ := by
  unfold gpair
  apply Finset.sum_congr rfl
  intro β hβ
  apply Finset.sum_congr rfl
  intro β' hβ'
  have hinner : ∀ n : ℕ,
      (∑ m ∈ Finset.Icc 1 N,
          (if n • β + m • β' = μ then (if β = β' then 0 else bform β β') else 0))
        = ∑ m ∈ Finset.Icc 1 ((E8NormTwo.e8ht μ).toNat),
          (if n • β + m • β' = μ then (if β = β' then 0 else bform β β') else 0) := by
    intro n
    refine (Finset.sum_subset ?_ ?_).symm
    · intro m hm
      rw [Finset.mem_Icc] at hm ⊢
      exact ⟨hm.1, le_trans hm.2 hN⟩
    · intro m hmN hmM
      have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hmN).1
      have hlt : (E8NormTwo.e8ht μ).toNat < m := by
        by_contra h
        exact hmM (Finset.mem_Icc.mpr ⟨hm1, not_lt.mp h⟩)
      rw [if_neg]
      intro hc
      exact false_of_toNat_lt (le_ht_of_comb hβ hβ' hc) hlt
  simp only [hinner]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro n hn
    rw [Finset.mem_Icc] at hn ⊢
    exact ⟨hn.1, le_trans hn.2 hN⟩
  · intro n hnN hnM
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hnN).1
    have hlt : (E8NormTwo.e8ht μ).toNat < n := by
      by_contra h
      exact hnM (Finset.mem_Icc.mpr ⟨hn1, not_lt.mp h⟩)
    apply Finset.sum_eq_zero
    intro m hmN
    rw [if_neg]
    intro hc
    exact false_of_toNat_lt (le_ht_of_comb_left hβ hβ' hc) hlt

lemma gc_eq_of_le {N : ℕ} {μ : Fin 8 → ℤ} (hN : (E8NormTwo.e8ht μ).toNat ≤ N) :
    gc N μ = gc ((E8NormTwo.e8ht μ).toNat) μ := by
  rw [gc, gc, gpair_eq_of_le hN, gsing_eq_of_le hN]



/-! ## The two telescoping reductions -/

lemma gsing_telescope {N : ℕ} {ν : Fin 8 → ℤ} (hN : (E8NormTwo.e8ht ν).toNat ≤ N) :
    (∑ β ∈ E8posRoots.P, ∑ n ∈ Finset.Icc 1 N,
        (E8NormTwo.e8ht β - 1) * Dc (ν - n • β))
      = ∑ β ∈ E8posRoots.P,
          (E8NormTwo.e8ht β - 1) * Dcoef (E8posRoots.P.erase β) (ν - β) := by
  apply Finset.sum_congr rfl
  intro β hβ
  rw [← Finset.mul_sum]
  congr 1
  simpa only [Dc, Dcoef] using Commons.Algebra.BigOperators.Dcoef_erase_telescope e8htHom E8posRoots.P
    (fun a ha => one_le_e8ht_of_mem_P ha) β hβ N ν hN

lemma gpair_telescope {N : ℕ} {ν : Fin 8 → ℤ} (hN : (E8NormTwo.e8ht ν).toNat ≤ N) :
    (∑ β ∈ E8posRoots.P, ∑ β' ∈ E8posRoots.P,
        ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
          (if β = β' then 0 else bform β β') * Dc (ν - n • β - m • β'))
      = ∑ β ∈ E8posRoots.P, ∑ β' ∈ E8posRoots.P.erase β,
          bform β β' * Dcoef ((E8posRoots.P.erase β).erase β') (ν - β - β') := by
  apply Finset.sum_congr rfl
  intro β hβ
  have hsplit : ∀ β' : Fin 8 → ℤ,
      (∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
          (if β = β' then 0 else bform β β') * Dc (ν - n • β - m • β'))
      = (if β = β' then 0 else bform β β') *
          (∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N, Dc (ν - n • β - m • β')) := by
    intro β'
    simp only [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun β' _ => hsplit β')]
  have hzero : (if β = β then (0:ℤ) else bform β β) *
      (∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N, Dc (ν - n • β - m • β)) = 0 := by
    simp
  rw [← Finset.sum_erase_add _ _ hβ, hzero, add_zero]
  apply Finset.sum_congr rfl
  intro β' hβ'
  rw [if_neg (fun h => (Finset.ne_of_mem_erase hβ') h.symm)]
  have htel : (∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N, Dc (ν - n • β - m • β'))
      = Dcoef ((E8posRoots.P.erase β).erase β') (ν - β - β') := by
    simpa only [Dc, Dcoef] using Commons.Algebra.BigOperators.Dcoef_erase_telescope_pair e8htHom E8posRoots.P
      (fun a ha => one_le_e8ht_of_mem_P ha) β β' hβ hβ' N ν hN
  rw [htel]

/-! ## Assembling the main identity -/

lemma sum_add_two_neg {ι : Type*} [DecidableEq ι] (s : Finset ι) (f g : ι → ℤ) :
    (∑ i ∈ s, f i) + 2 * (- ∑ i ∈ s, g i) = ∑ i ∈ s, (f i - 2 * g i) := by
  rw [mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma combine (ν : Fin 8 → ℤ) :
    (∑ T ∈ E8posRoots.P.powerset, (-1:ℤ)^T.card * (if Sig T = ν then (1:ℤ) else 0) *
        (∑ β ∈ T, ∑ β' ∈ T.erase β, bform β β'))
      + 2 * (- ∑ T ∈ E8posRoots.P.powerset, (-1:ℤ)^T.card * (if Sig T = ν then (1:ℤ) else 0) *
        (∑ β ∈ T, (E8NormTwo.e8ht β - 1)))
      = (E8NormTwo.qZ ν - 2 * E8NormTwo.e8ht ν) * Dcoef E8posRoots.P ν := by
  rw [sum_add_two_neg]
  have hstep : (∑ T ∈ E8posRoots.P.powerset,
          ((-1:ℤ)^T.card * (if Sig T = ν then (1:ℤ) else 0) *
              (∑ β ∈ T, ∑ β' ∈ T.erase β, bform β β')
            - 2 * ((-1:ℤ)^T.card * (if Sig T = ν then (1:ℤ) else 0) *
              (∑ β ∈ T, (E8NormTwo.e8ht β - 1)))))
      = ∑ T ∈ E8posRoots.P.powerset,
          (-1:ℤ)^T.card * (if Sig T = ν then (1:ℤ) else 0) *
            (E8NormTwo.qZ ν - 2 * E8NormTwo.e8ht ν) := by
    apply Finset.sum_congr rfl
    intro T hT
    by_cases h : Sig T = ν
    · rw [if_pos h]
      have hb := bracket_eq T (Finset.mem_powerset.mp hT) ν h
      rw [← hb]; ring
    · rw [if_neg h]; ring
  rw [hstep]
  rw [Dcoef, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  by_cases h : Sig T = ν
  · rw [if_pos h, if_pos h]; ring
  · rw [if_neg h, if_neg h]; ring

lemma main_identity (ν : Fin 8 → ℤ) :
    (∑ T ∈ E8posRoots.P.powerset, (-1:ℤ)^T.card * gc ((E8NormTwo.e8ht ν).toNat) (ν - Sig T))
      = (E8NormTwo.qZ ν - 2 * E8NormTwo.e8ht ν) * Dcoef E8posRoots.P ν := by
  have hN : (E8NormTwo.e8ht ν).toNat ≤ (E8NormTwo.e8ht ν).toNat := le_refl _
  have hsplit : (∑ T ∈ E8posRoots.P.powerset,
        (-1:ℤ)^T.card * gc ((E8NormTwo.e8ht ν).toNat) (ν - Sig T))
      = (∑ T ∈ E8posRoots.P.powerset,
            (-1:ℤ)^T.card * gpair ((E8NormTwo.e8ht ν).toNat) (ν - Sig T))
        + 2 * (∑ T ∈ E8posRoots.P.powerset,
            (-1:ℤ)^T.card * gsing ((E8NormTwo.e8ht ν).toNat) (ν - Sig T)) := by
    rw [show (∑ T ∈ E8posRoots.P.powerset,
          (-1:ℤ)^T.card * gc ((E8NormTwo.e8ht ν).toNat) (ν - Sig T))
        = ∑ T ∈ E8posRoots.P.powerset,
            ((-1:ℤ)^T.card * gpair ((E8NormTwo.e8ht ν).toNat) (ν - Sig T)
              + 2 * ((-1:ℤ)^T.card * gsing ((E8NormTwo.e8ht ν).toNat) (ν - Sig T)))
        from Finset.sum_congr rfl (fun T _ => by rw [gc]; ring)]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hsplit]
  rw [sum_powerset_gpair_swap, sum_powerset_gsing_swap]
  rw [gpair_telescope hN, gsing_telescope hN]
  rw [X1_eq ν, X2_eq ν]
  exact combine ν



/-! ## The Weyl denominator coefficient vanishes against `⟪ν,ν⟫ - 2 ht ν` -/

lemma Dcoef_ne_zero_support (ν : Fin 8 → ℤ) (h : Dcoef E8posRoots.P ν ≠ 0) :
    ∃ L : List (Fin 8), wact L rhoZ = rhoZ - ν := by
  refine E8_weyl_denom_support E8posRoots.P ?_ ν ?_
  · intro v
    rw [E8posRoots.memP]
    exact ⟨fun h => ⟨h.2.1, h.1, h.2.2⟩, fun h => ⟨h.2.1, h.1, h.2.2⟩⟩
  · simpa only [Dcoef] using h

lemma Dcoef_mul_eq_zero (ν : Fin 8 → ℤ) :
    (E8NormTwo.qZ ν - 2 * E8NormTwo.e8ht ν) * Dcoef E8posRoots.P ν = 0 := by
  by_cases h : Dcoef E8posRoots.P ν = 0
  · rw [h, mul_zero]
  · obtain ⟨L, hL⟩ := Dcoef_ne_zero_support ν h
    have hsub : rhoZ - wact L rhoZ = ν := by rw [hL]; abel
    have hq := E8_qZ_rho_sub_wact L
    rw [hsub] at hq
    rw [hq]; ring

/-! ## Vanishing of the truncated sums by strong induction on the height -/

theorem gc_zero (ν : Fin 8 → ℤ) : gc ((E8NormTwo.e8ht ν).toNat) ν = 0 := by
  suffices H : ∀ n : ℕ, ∀ μ : Fin 8 → ℤ, (E8NormTwo.e8ht μ).toNat = n →
      gc ((E8NormTwo.e8ht μ).toNat) μ = 0 from H _ ν rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro μ hμ
    by_cases hn : n = 0
    · rw [hμ, hn]
      simp [gc, gpair, gsing]
    · have hpos : 1 ≤ n := Nat.pos_of_ne_zero hn
      have hμpos : 0 ≤ E8NormTwo.e8ht μ := by
        by_contra hneg
        push Not at hneg
        have h0 : (E8NormTwo.e8ht μ).toNat = 0 := Int.toNat_of_nonpos (le_of_lt hneg)
        omega
      have hμeq : E8NormTwo.e8ht μ = (n : ℤ) := by
        rw [← Int.toNat_of_nonneg hμpos, hμ]
      have hmain := main_identity μ
      rw [Dcoef_mul_eq_zero μ] at hmain
      have hmem : (∅ : Finset (Fin 8 → ℤ)) ∈ E8posRoots.P.powerset := by
        rw [Finset.mem_powerset]; exact Finset.empty_subset _
      have hsum := Finset.sum_erase_add E8posRoots.P.powerset
        (fun T => (-1:ℤ)^T.card * gc ((E8NormTwo.e8ht μ).toNat) (μ - Sig T)) hmem
      rw [hmain] at hsum
      have hzero : (∑ T ∈ E8posRoots.P.powerset.erase ∅,
          (-1:ℤ)^T.card * gc ((E8NormTwo.e8ht μ).toNat) (μ - Sig T)) = 0 := by
        apply Finset.sum_eq_zero
        intro T hT
        rw [Finset.mem_erase] at hT
        obtain ⟨hTne, hTmem⟩ := hT
        rw [Finset.mem_powerset] at hTmem
        have hne : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hTne
        have hSigpos : 1 ≤ E8NormTwo.e8ht (Sig T) := by
          rw [e8ht_sum]
          calc (1:ℤ) ≤ (T.card : ℤ) := by
                have := Finset.card_pos.mpr hne
                exact_mod_cast this
            _ = ∑ a ∈ T, (1:ℤ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
            _ ≤ ∑ a ∈ T, E8NormTwo.e8ht a :=
                  Finset.sum_le_sum (fun a ha => one_le_e8ht_of_mem_P (hTmem ha))
        have hsub' : (E8NormTwo.e8ht (μ - Sig T)).toNat ≤ n - 1 := by
          have h1 : E8NormTwo.e8ht (μ - Sig T) = (n:ℤ) - E8NormTwo.e8ht (Sig T) := by
            rw [e8ht_sub, hμeq]
          rw [h1]
          have hle : (n:ℤ) - E8NormTwo.e8ht (Sig T) ≤ (n:ℤ) - 1 := by omega
          calc ((n:ℤ) - E8NormTwo.e8ht (Sig T)).toNat
              ≤ ((n:ℤ) - 1).toNat := Int.toNat_le_toNat hle
            _ = n - 1 := by
                  have hc : (n:ℤ) - 1 = ((n - 1 : ℕ) : ℤ) := by omega
                  rw [hc, Int.toNat_natCast]
        have hlt : (E8NormTwo.e8ht (μ - Sig T)).toNat < n := by omega
        have hle : (E8NormTwo.e8ht (μ - Sig T)).toNat ≤ (E8NormTwo.e8ht μ).toNat := by
          rw [hμ]; omega
        rw [gc_eq_of_le hle, ih _ hlt (μ - Sig T) rfl]
        ring
      rw [hzero, zero_add] at hsum
      have hF0 : (-1:ℤ)^(∅ : Finset (Fin 8 → ℤ)).card *
          gc ((E8NormTwo.e8ht μ).toNat) (μ - Sig ∅) = gc ((E8NormTwo.e8ht μ).toNat) μ := by
        simp [Sig]
      rw [hF0] at hsum
      exact hsum

/-! ## The target theorem -/

/-- **Root-system identity (for the `E₈` Kostant/Freudenthal recursion).**

Writing `ht γ` for the height `E8NormTwo.e8ht γ = Σ i, coords γ i` and `⟪β,β'⟫ = Σ i, β i * (A⁻¹β') i`
for the lattice form, one has for every weight `δ`:

`Σ_{β ≠ β'} Σ_{n,m ≥ 1} [nβ + mβ' = δ] ⟪β,β'⟫ + 2 Σ_{β, n ≥ 1} [nβ = δ] (ht β - 1) = 0`. -/
theorem E8_root_pairing_summation (δ : Fin 8 → ℤ) :
    (∑ β ∈ E8posRoots.P, ∑ β' ∈ E8posRoots.P,
      ∑ n ∈ Finset.Icc 1 ((E8NormTwo.e8ht δ).toNat),
      ∑ m ∈ Finset.Icc 1 ((E8NormTwo.e8ht δ).toNat),
      (if n • β + m • β' = δ then
        (if β = β' then 0 else ∑ i, β i * (E8NormTwo.E8inv.mulVec β') i) else 0))
    + 2 * (∑ β ∈ E8posRoots.P, ∑ n ∈ Finset.Icc 1 ((E8NormTwo.e8ht δ).toNat),
      (if n • β = δ then (E8NormTwo.e8ht β - 1) else 0)) = 0 := by
  simpa only [gc, gpair, gsing, bform] using gc_zero δ

end Commons.LinearAlgebra.Matrix.Cartan

