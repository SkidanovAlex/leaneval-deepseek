import Submission.ZagierHoffmanProof.StepL27

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L28: prefix sums at length `j` of the (2.14) chain members

First true prefix-sum bounds: the type-1 / leading (`inl`) and type-2 (`inr (inl i)`)
members of the (2.14) chain have `j`-prefix sum equal to that of `s` (their first `j`
entries are `s_1,…,s_j`), while the type-3 (`inr (inr i)`) members have prefix sum
`psum s j + 1` (entry `s_j+1` at position `j−1`).  `psum_eq_of_pad0_eq` is the generic
bridge (equal `pad0` values below `m` ⇒ equal prefix sums); `Q_dep_inl/inr_inl/inr_inr`
supply the depth bounds `j ≤ Q.dep` that keep the prefix entries inside the tuples.
These are the seed inequalities for the per-type bounds (type-2's
`t'₁+…+t'ₖ ≤ s₁+…+s_j + 1 + (k−j−1)q < s₁+…+sₖ` extends this `j`-prefix sum with the
P2WpT-bound arithmetic; type-3's Init-comparison uses `s_j+1` at position `j−1`).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

lemma psum_eq_of_pad0_eq {d r : ℕ} (q : Fin d → ℕ+) (s : Fin r → ℕ+)
    (m : ℕ) (h : ∀ x : ℕ, x < m → pad0 q x = pad0 s x) :
    psum q m = psum s m := by
  classical
  change (∑ x ∈ Finset.range m, pad0 q x) = (∑ x ∈ Finset.range m, pad0 s x)
  apply Finset.sum_congr rfl
  intro x hx
  exact h x (Finset.mem_range.mp hx)

/-- Depth of the type-1 / leading members is at least `j`. -/
lemma Q_dep_inl (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i : D.ιA, j ≤ Q.dep (Sum.inl i) := by
  classical
  intro D Bs Q i
  have hlen : (sPrefix r s j (by omega) (by omega)).length = j - 1 :=
    sPrefix_length r s j (by omega) (by omega)
  have h1 : Q.dep (Sum.inl i) = Bs.dep (Sum.inl i) + (j - 1) := by
    have hd := FixedOver.prependList_dep F Bs (sPrefix r s j (by omega) (by omega)) (Sum.inl i)
    rw [hlen] at hd
    exact hd
  have h2 : Bs.dep (Sum.inl i) = D.depA i + 1 := by
    dsimp [Bs, ofBstarOver]
  rw [h1, h2]
  omega

/-- Depth of the type-2 members is at least `j`. -/
lemma Q_dep_inr_inl (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i : D.ιB, j ≤ Q.dep (Sum.inr (Sum.inl i)) := by
  classical
  intro D Bs Q i
  have hlen : (sPrefix r s j (by omega) (by omega)).length = j - 1 :=
    sPrefix_length r s j (by omega) (by omega)
  have h1 : Q.dep (Sum.inr (Sum.inl i)) = Bs.dep (Sum.inr (Sum.inl i)) + (j - 1) := by
    have hd := FixedOver.prependList_dep F Bs (sPrefix r s j (by omega) (by omega)) (Sum.inr (Sum.inl i))
    rw [hlen] at hd
    exact hd
  have h2 : Bs.dep (Sum.inr (Sum.inl i)) = D.depB i + 1 := by
    dsimp [Bs, ofBstarOver]
  rw [h1, h2]
  omega

/-- Depth of the type-3 members is at least `j`. -/
lemma Q_dep_inr_inr (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i : D.ιB, j ≤ Q.dep (Sum.inr (Sum.inr i)) := by
  classical
  intro D Bs Q i
  have hlen : (sPrefix r s j (by omega) (by omega)).length = j - 1 :=
    sPrefix_length r s j (by omega) (by omega)
  have h1 : Q.dep (Sum.inr (Sum.inr i)) = Bs.dep (Sum.inr (Sum.inr i)) + (j - 1) := by
    have hd := FixedOver.prependList_dep F Bs (sPrefix r s j (by omega) (by omega)) (Sum.inr (Sum.inr i))
    rw [hlen] at hd
    exact hd
  have h2 : Bs.dep (Sum.inr (Sum.inr i)) = D.depB i := by
    dsimp [Bs, ofBstarOver]
  have hpos : 0 < D.depB i := D.hdepB i
  rw [h1, h2]
  omega



/-- Type-2 members have `j`-prefix sum equal to that of `s`. -/
lemma type2_psum_j (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i : D.ιB, psum (Q.c (Sum.inr (Sum.inl i))) j = psum s j := by
  classical
  intro D Bs Q i
  have hdep : j ≤ Q.dep (Sum.inr (Sum.inl i)) := Q_dep_inr_inl F r s k j hk1 hkr hj1 hjk hsj R0 hbhd i
  have hjlr : j - 1 < r := by
    have : j - 1 ≤ r - 1 := by omega
    omega
  apply psum_eq_of_pad0_eq
  intro x hx
  have hxj : x < j := hx
  by_cases hxe : x = j - 1
  · subst x
    have hmQ : j - 1 < Q.dep (Sum.inr (Sum.inl i)) := by omega
    have hv := type2_sj_at_jm1 F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd i hmQ
    have hp1 : pad0 (Q.c (Sum.inr (Sum.inl i))) (j - 1) =
        ((Q.c (Sum.inr (Sum.inl i))) ⟨j - 1, hmQ⟩ : ℕ) :=
      pad0_of_lt (Q.c (Sum.inr (Sum.inl i))) hmQ
    have hp2 : pad0 s (j - 1) = (s ⟨j - 1, hjlr⟩ : ℕ) := pad0_of_lt s hjlr
    rw [hp1, hp2]
    exact hv
  · have hx1 : x < j - 1 := by omega
    have hmQ : x < Q.dep (Sum.inr (Sum.inl i)) := by omega
    have hv := member_prefix_pos F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd (Sum.inr (Sum.inl i)) x hx1 hmQ
    have hxr : x < r := by
      have : x < j - 1 := hx1
      omega
    have hp1 : pad0 (Q.c (Sum.inr (Sum.inl i))) x = ((Q.c (Sum.inr (Sum.inl i))) ⟨x, hmQ⟩ : ℕ) :=
      pad0_of_lt (Q.c (Sum.inr (Sum.inl i))) hmQ
    have hp2 : pad0 s x = (s ⟨x, hxr⟩ : ℕ) := pad0_of_lt s hxr
    rw [hp1, hp2]
    exact congrArg (fun t : ℕ+ => (t : ℕ)) hv


/-- Type-3 members have `j`-prefix sum equal to that of `s` plus one (their `j`-th
entry is `s_j+1`). -/
lemma type3_psum_j (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i : D.ιB, psum (Q.c (Sum.inr (Sum.inr i))) j = psum s j + 1 := by
  classical
  intro D Bs Q i
  have hdep : j ≤ Q.dep (Sum.inr (Sum.inr i)) := Q_dep_inr_inr F r s k j hk1 hkr hj1 hjk hsj R0 hbhd i
  have hjlr : j - 1 < r := by
    have : j - 1 ≤ r - 1 := by omega
    omega
  have hsplit : psum (Q.c (Sum.inr (Sum.inr i))) j =
      psum (Q.c (Sum.inr (Sum.inr i))) (j - 1) + pad0 (Q.c (Sum.inr (Sum.inr i))) (j - 1) := by
    have hj1' : (j - 1) + 1 = j := by omega
    have hsu := psum_succ (Q.c (Sum.inr (Sum.inr i))) (j - 1)
    rw [hj1'] at hsu
    exact hsu
  have hmid : psum (Q.c (Sum.inr (Sum.inr i))) (j - 1) = psum s (j - 1) := by
    apply psum_eq_of_pad0_eq (q := Q.c (Sum.inr (Sum.inr i))) (s := s) (m := j - 1)
    intro x hx
    have hx1 : x < j - 1 := hx
    have hmQ : x < Q.dep (Sum.inr (Sum.inr i)) := by omega
    have hv := member_prefix_pos F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd (Sum.inr (Sum.inr i)) x hx1 hmQ
    have hxr : x < r := by
      have : x < j - 1 := hx1
      omega
    rw [pad0_of_lt (Q.c (Sum.inr (Sum.inr i))) hmQ, pad0_of_lt s hxr]
    exact congrArg (fun t : ℕ+ => (t : ℕ)) hv
  have hlast : (pad0 (Q.c (Sum.inr (Sum.inr i))) (j - 1) : ℕ) = (s ⟨j - 1, hjlr⟩ : ℕ) + 1 := by
    have hmQ : j - 1 < Q.dep (Sum.inr (Sum.inr i)) := by omega
    have hv := type3_sjadd_one_at F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd i hmQ
    -- hv : ((Q.c…)⟨j−1,hmQ⟩:ℕ) = (s⟨j−1, by omega⟩:ℕ) + 1
    rw [pad0_of_lt (Q.c (Sum.inr (Sum.inr i))) hmQ]
    exact hv
  calc
    psum (Q.c (Sum.inr (Sum.inr i))) j
        = psum (Q.c (Sum.inr (Sum.inr i))) (j - 1) + pad0 (Q.c (Sum.inr (Sum.inr i))) (j - 1) := hsplit
    _ = psum s (j - 1) + ((s ⟨j - 1, hjlr⟩ : ℕ) + 1) := by rw [hmid, hlast]
    _ = psum s j + 1 := by
      have hj1' : (j - 1) + 1 = j := by omega
      have hsu := psum_succ s (j - 1)
      have hpj : psum s j = psum s (j - 1) + (s ⟨j - 1, hjlr⟩ : ℕ) := by
        rw [hj1'] at hsu
        rw [hsu]
        rw [pad0_of_lt s hjlr]
      omega

lemma a_side_psum_j (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i : D.ιA, psum (Q.c (Sum.inl i)) j = psum s j := by
  classical
  intro D Bs Q i
  have hdep : j ≤ Q.dep (Sum.inl i) := Q_dep_inl F r s k j hk1 hkr hj1 hjk hsj R0 hbhd i
  have hjlr : j - 1 < r := by
    have : j - 1 ≤ r - 1 := by omega
    omega
  apply psum_eq_of_pad0_eq
  intro x hx
  have hxj : x < j := hx
  by_cases hxe : x = j - 1
  · subst x
    have hmQ : j - 1 < Q.dep (Sum.inl i) := by omega
    have hv := type1_sj_at_jm1 F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd i hmQ
    have hp1 : pad0 (Q.c (Sum.inl i)) (j - 1) = ((Q.c (Sum.inl i)) ⟨j - 1, hmQ⟩ : ℕ) :=
      pad0_of_lt (Q.c (Sum.inl i)) hmQ
    have hp2 : pad0 s (j - 1) = (s ⟨j - 1, hjlr⟩ : ℕ) := pad0_of_lt s hjlr
    rw [hp1, hp2]
    exact hv
  · have hx1 : x < j - 1 := by omega
    have hmQ : x < Q.dep (Sum.inl i) := by omega
    have hv := member_prefix_pos F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd (Sum.inl i) x hx1 hmQ
    have hxr : x < r := by
      have : x < j - 1 := hx1
      omega
    have hp1 : pad0 (Q.c (Sum.inl i)) x = ((Q.c (Sum.inl i)) ⟨x, hmQ⟩ : ℕ) :=
      pad0_of_lt (Q.c (Sum.inl i)) hmQ
    have hp2 : pad0 s x = (s ⟨x, hxr⟩ : ℕ) := pad0_of_lt s hxr
    rw [hp1, hp2]
    exact congrArg (fun t : ℕ+ => (t : ℕ)) hv

end ZagierHoffmanPositiveChar
