import Submission.ZagierHoffmanProof.StepL26

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L27: common prefix values of the (2.14) chain members (first prefix bounds)

Every member of the (2.14) chain at the Prop-2.12 configuration shares its front
entries with `s`: at full-tuple positions `m < j−1` the value is `s_{m+1}`
(`member_prefix_pos` — the basis of every Init-comparison), and the type-1 /
leading (`inl`) and type-2 (`inr (inl i)`) members have value `s_j` at position
`j−1` (their tuples start `(s_1,…,s_j,…)`), while the type-3 members have `s_j+1`
there (StepL26).  These positional prefix facts are what the paper's per-type
prefix-sum analysis consumes (type-2: `t'₁+…+t'ₖ` starts `s₁+…+s_j+1+…`; type-3:
`u₁+…+u_ℓ ≤ s₁+…+s_ℓ` for `ℓ ≥ k`; Init-lex comparisons).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Every member of the (2.14) chain shares the front prefix values with `s`: at
full-tuple positions `m < j−1` the value is `s_{m+1}`. -/
lemma member_prefix_pos (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ p : D.ιA ⊕ (D.ιB ⊕ D.ιB),
      ∀ (m : ℕ) (hmf : m < j - 1) (hmQ : m < Q.dep p),
        (Q.c p) ⟨m, hmQ⟩ = s ⟨m, by omega⟩ := by
  classical
  intro D Bs Q p m hmf hmQ
  have hmfl : m < (sPrefix r s j (by omega) (by omega)).length := by
    have hlen : (sPrefix r s j (by omega) (by omega)).length = j - 1 :=
      sPrefix_length r s j (by omega) (by omega)
    simpa [hlen] using hmf
  have hval := prependList_c_front_value F Bs (sPrefix r s j (by omega) (by omega)) p m hmQ hmfl
  -- hval : Q.c p ⟨m,hmQ⟩ = (sPrefix…).reverse.get ⟨m, hmfl⟩
  calc
    (Q.c p) ⟨m, hmQ⟩ = (sPrefix r s j (by omega) (by omega)).reverse.get
        ⟨m, by simpa using hmfl⟩ := by
          -- hval's RHS index uses by-simpa from hmfl; write the same
          have hg := hval
          -- hval : … = (sPrefix…).reverse.get ⟨m, by simpa using hmfl⟩  (its own bound proof)
          exact hg
    _ = s ⟨m, by omega⟩ := by
          exact sPrefix_reverse_value r s j (by omega) (by omega) m hmfl

/-- The type-1 (and leading) members `inl i` have value `s_j` at full-tuple position
`j−1` (their tuples begin `(s_1,…,s_j,…)`). -/
lemma type1_sj_at_jm1 (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i : D.ιA, ∀ (hm : j - 1 < Q.dep (Sum.inl i)),
      ((Q.c (Sum.inl i)) ⟨j - 1, hm⟩ : ℕ) = (s ⟨j - 1, by omega⟩ : ℕ) := by
  classical
  intro D Bs Q i hm
  have hlen : (sPrefix r s j (by omega) (by omega)).length = j - 1 :=
    sPrefix_length r s j (by omega) (by omega)
  have hge : (sPrefix r s j (by omega) (by omega)).length ≤ j - 1 := by omega
  have hQdep : Q.dep (Sum.inl i) =
      Bs.dep (Sum.inl i) + (sPrefix r s j (by omega) (by omega)).length := by
    exact FixedOver.prependList_dep F Bs (sPrefix r s j (by omega) (by omega)) (Sum.inl i)
  have b' : (j - 1) - (sPrefix r s j (by omega) (by omega)).length < Bs.dep (Sum.inl i) := by
    have hm1 : j - 1 < Bs.dep (Sum.inl i) + (sPrefix r s j (by omega) (by omega)).length := by
      rw [← hQdep]
      exact hm
    omega
  have h1 : ((Q.c (Sum.inl i)) ⟨j - 1, hm⟩ : ℕ) =
      ((Bs.c (Sum.inl i)) ⟨(j - 1) - (sPrefix r s j (by omega) (by omega)).length, b'⟩ : ℕ) := by
    have hv := prependList_c_base_value F Bs (sPrefix r s j (by omega) (by omega))
      (Sum.inl i) (j - 1) hm hge
    apply congrArg (fun v : ℕ+ => (v : ℕ))
    calc
      (Q.c (Sum.inl i)) ⟨j - 1, hm⟩
          = (Bs.c (Sum.inl i)) ⟨(j - 1) - (sPrefix r s j (by omega) (by omega)).length,
              (by
                have hd := FixedOver.prependList_dep F Bs (sPrefix r s j (by omega) (by omega)) (Sum.inl i)
                rw [hd] at hm
                omega)⟩ := hv
      _ = (Bs.c (Sum.inl i)) ⟨(j - 1) - (sPrefix r s j (by omega) (by omega)).length, b'⟩ := by
            congr 1
  have hcBs : Bs.c (Sum.inl i) = consVec (s ⟨j - 1, by omega⟩) (D.cA i) := by
    dsimp [Bs, ofBstarOver, D]
  have h2 : ((Bs.c (Sum.inl i)) ⟨(j - 1) - (sPrefix r s j (by omega) (by omega)).length, b'⟩ : ℕ) =
      ((consVec (s ⟨j - 1, by omega⟩) (D.cA i))
        ⟨(j - 1) - (sPrefix r s j (by omega) (by omega)).length, b'⟩ : ℕ) := by
    apply congrArg (fun v : ℕ+ => (v : ℕ))
    exact congrFun hcBs ⟨(j - 1) - (sPrefix r s j (by omega) (by omega)).length, b'⟩
  -- the value at Bs-position (j−1)−len = 0 is the consVec head s_j
  have h3 : ((consVec (s ⟨j - 1, by omega⟩) (D.cA i))
        ⟨(j - 1) - (sPrefix r s j (by omega) (by omega)).length, b'⟩ : ℕ) =
      (s ⟨j - 1, by omega⟩ : ℕ) := by
    rw [show (⟨(j - 1) - (sPrefix r s j (by omega) (by omega)).length, b'⟩ :
            Fin (D.depA i + 1)) = ⟨0, by omega⟩ from (by
        apply Fin.ext
        simp
        omega)]
    have hhead := congrArg (fun t : ℕ+ => (t : ℕ)) (consVec_zero (s ⟨j - 1, by omega⟩) (D.cA i))
    simpa using hhead
  calc
    ((Q.c (Sum.inl i)) ⟨j - 1, hm⟩ : ℕ)
        = ((Bs.c (Sum.inl i)) ⟨(j - 1) - (sPrefix r s j (by omega) (by omega)).length, b'⟩ : ℕ) := h1
    _ = ((consVec (s ⟨j - 1, by omega⟩) (D.cA i))
          ⟨(j - 1) - (sPrefix r s j (by omega) (by omega)).length, b'⟩ : ℕ) := h2
    _ = (s ⟨j - 1, by omega⟩ : ℕ) := h3

lemma type2_sj_at_jm1 (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i : D.ιB, ∀ (hm : j - 1 < Q.dep (Sum.inr (Sum.inl i))),
      ((Q.c (Sum.inr (Sum.inl i))) ⟨j - 1, hm⟩ : ℕ) = (s ⟨j - 1, by omega⟩ : ℕ) := by
  classical
  intro D Bs Q i hm
  have hlen : (sPrefix r s j (by omega) (by omega)).length = j - 1 :=
    sPrefix_length r s j (by omega) (by omega)
  have hge : (sPrefix r s j (by omega) (by omega)).length ≤ j - 1 := by omega
  have hQdep : Q.dep (Sum.inr (Sum.inl i)) =
      Bs.dep (Sum.inr (Sum.inl i)) + (sPrefix r s j (by omega) (by omega)).length := by
    exact FixedOver.prependList_dep F Bs (sPrefix r s j (by omega) (by omega)) (Sum.inr (Sum.inl i))
  have b' : (j - 1) - (sPrefix r s j (by omega) (by omega)).length < Bs.dep (Sum.inr (Sum.inl i)) := by
    have hm1 : j - 1 < Bs.dep (Sum.inr (Sum.inl i)) + (sPrefix r s j (by omega) (by omega)).length := by
      rw [← hQdep]
      exact hm
    omega
  have h1 : ((Q.c (Sum.inr (Sum.inl i))) ⟨j - 1, hm⟩ : ℕ) =
      ((Bs.c (Sum.inr (Sum.inl i))) ⟨(j - 1) - (sPrefix r s j (by omega) (by omega)).length, b'⟩ : ℕ) := by
    have hv := prependList_c_base_value F Bs (sPrefix r s j (by omega) (by omega))
      (Sum.inr (Sum.inl i)) (j - 1) hm hge
    apply congrArg (fun v : ℕ+ => (v : ℕ))
    calc
      (Q.c (Sum.inr (Sum.inl i))) ⟨j - 1, hm⟩
          = (Bs.c (Sum.inr (Sum.inl i))) ⟨(j - 1) - (sPrefix r s j (by omega) (by omega)).length,
              (by
                have hd := FixedOver.prependList_dep F Bs (sPrefix r s j (by omega) (by omega)) (Sum.inr (Sum.inl i))
                rw [hd] at hm
                omega)⟩ := hv
      _ = (Bs.c (Sum.inr (Sum.inl i))) ⟨(j - 1) - (sPrefix r s j (by omega) (by omega)).length, b'⟩ := by
            congr 1
  have hcBs : Bs.c (Sum.inr (Sum.inl i)) = consVec (s ⟨j - 1, by omega⟩) (D.cB i) := by
    dsimp [Bs, ofBstarOver, D]
  have h2 : ((Bs.c (Sum.inr (Sum.inl i))) ⟨(j - 1) - (sPrefix r s j (by omega) (by omega)).length, b'⟩ : ℕ) =
      ((consVec (s ⟨j - 1, by omega⟩) (D.cB i))
        ⟨(j - 1) - (sPrefix r s j (by omega) (by omega)).length, b'⟩ : ℕ) := by
    apply congrArg (fun v : ℕ+ => (v : ℕ))
    exact congrFun hcBs ⟨(j - 1) - (sPrefix r s j (by omega) (by omega)).length, b'⟩
  have h3 : ((consVec (s ⟨j - 1, by omega⟩) (D.cB i))
        ⟨(j - 1) - (sPrefix r s j (by omega) (by omega)).length, b'⟩ : ℕ) =
      (s ⟨j - 1, by omega⟩ : ℕ) := by
    rw [show (⟨(j - 1) - (sPrefix r s j (by omega) (by omega)).length, b'⟩ :
            Fin (D.depB i + 1)) = ⟨0, by omega⟩ from (by
        apply Fin.ext
        simp
        omega)]
    have hhead := congrArg (fun t : ℕ+ => (t : ℕ)) (consVec_zero (s ⟨j - 1, by omega⟩) (D.cB i))
    simpa using hhead
  calc
    ((Q.c (Sum.inr (Sum.inl i))) ⟨j - 1, hm⟩ : ℕ)
        = ((Bs.c (Sum.inr (Sum.inl i))) ⟨(j - 1) - (sPrefix r s j (by omega) (by omega)).length, b'⟩ : ℕ) := h1
    _ = ((consVec (s ⟨j - 1, by omega⟩) (D.cB i))
          ⟨(j - 1) - (sPrefix r s j (by omega) (by omega)).length, b'⟩ : ℕ) := h2
    _ = (s ⟨j - 1, by omega⟩ : ℕ) := h3

end ZagierHoffmanPositiveChar
