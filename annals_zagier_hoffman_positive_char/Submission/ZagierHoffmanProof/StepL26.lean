import Submission.ZagierHoffmanProof.StepL25

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L26: per-type output values of the (2.14) chain (first bounds piece)

The (2.14) chain at the Prop-2.12 configuration classifies its outputs: the type-2
members (the `inr (inl i)` b-side of `B*_{s_j}`) have tuple `(s_1,…,s_j, 1, …)` —
value `1` at full-tuple position `j` — and the type-3 members (the merged `inr (inr i)`)
have tuple `(s_1,…,s_{j−1}, s_j+1, …)` — value `s_j+1` at position `j−1`.  These are
the structural seeds of the paper's type-2/type-3 bound analysis (prefix-sum bounds vs
`s` come next, on top of these entry values and the depth/weight arithmetic).  Also
here: `consVec_nat_value` (value of a prepended tuple at a Nat position) and
`headAdd_head` (the merged head `v + (t)₁`).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Value of `consVec x t` at a Nat position `ℓ`. -/
lemma consVec_nat_value (x : ℕ+) {m : ℕ} (t : Fin m → ℕ+) :
    ∀ (ℓ : ℕ) (hℓ : ℓ < m + 1),
      (consVec x t) ⟨ℓ, hℓ⟩ = if hz : ℓ = 0 then x else t ⟨ℓ - 1, by omega⟩ := by
  classical
  intro ℓ hℓ
  by_cases hz : ℓ = 0
  · subst ℓ
    change consVec x t ⟨0, hℓ⟩ = x
    have hidx : (⟨0, hℓ⟩ : Fin (m + 1)) = ⟨0, by omega⟩ := by
      apply Fin.ext
      rfl
    rw [hidx]
    rw [consVec_zero]
  · let i : Fin m := ⟨ℓ - 1, by
      have hlt : ℓ < m + 1 := hℓ
      omega⟩
    have hidx : (⟨ℓ, hℓ⟩ : Fin (m + 1)) = ⟨(i : ℕ) + 1, by omega⟩ := by
      apply Fin.ext
      simp [i]
      omega
    rw [hidx]
    rw [consVec_succ x t i]
    simp [i, hz]

/-- Head of `headAdd v t` is `v + (head of t)`. -/
lemma headAdd_head (v : ℕ+) {k : ℕ} (hr0 : 0 < k) (t : Fin k → ℕ+) :
    headAdd v hr0 t ⟨0, hr0⟩ = ⟨(v : ℕ) + (t ⟨0, hr0⟩ : ℕ),
      Nat.add_pos_left (PNat.pos v) (t ⟨0, hr0⟩ : ℕ)⟩ := by
  dsimp [headAdd]

/-- The type-2 member `inr (inl i)` of the (2.14) chain has value `1` at full-tuple
position `j` (its tuple is `(s_1,…,s_j, 1, …)`). -/
lemma type2_one_at_j (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i : D.ιB, ∀ (hmj : j < Q.dep (Sum.inr (Sum.inl i))),
      ((Q.c (Sum.inr (Sum.inl i))) ⟨j, hmj⟩ : ℕ) = 1 := by
  classical
  intro D Bs Q i hmj
  have hlen : (sPrefix r s j (by omega) (by omega)).length = j - 1 :=
    sPrefix_length r s j (by omega) (by omega)
  have hge : (sPrefix r s j (by omega) (by omega)).length ≤ j := by omega
  have hQdep : Q.dep (Sum.inr (Sum.inl i)) =
      Bs.dep (Sum.inr (Sum.inl i)) + (sPrefix r s j (by omega) (by omega)).length := by
    exact FixedOver.prependList_dep F Bs (sPrefix r s j (by omega) (by omega)) (Sum.inr (Sum.inl i))
  have b' : j - (sPrefix r s j (by omega) (by omega)).length < Bs.dep (Sum.inr (Sum.inl i)) := by
    have hm1 : j < Bs.dep (Sum.inr (Sum.inl i)) + (sPrefix r s j (by omega) (by omega)).length := by
      rw [← hQdep]
      exact hmj
    omega
  -- 1: peel the prefix
  have h1 : ((Q.c (Sum.inr (Sum.inl i))) ⟨j, hmj⟩ : ℕ) =
      ((Bs.c (Sum.inr (Sum.inl i))) ⟨j - (sPrefix r s j (by omega) (by omega)).length, b'⟩ : ℕ) := by
    have hv := prependList_c_base_value F Bs (sPrefix r s j (by omega) (by omega))
      (Sum.inr (Sum.inl i)) j hmj hge
    apply congrArg (fun v : ℕ+ => (v : ℕ))
    calc
      (Q.c (Sum.inr (Sum.inl i))) ⟨j, hmj⟩
          = (Bs.c (Sum.inr (Sum.inl i))) ⟨j - (sPrefix r s j (by omega) (by omega)).length,
              (by
                have hd := FixedOver.prependList_dep F Bs (sPrefix r s j (by omega) (by omega)) (Sum.inr (Sum.inl i))
                rw [hd] at hmj
                omega)⟩ := hv
      _ = (Bs.c (Sum.inr (Sum.inl i))) ⟨j - (sPrefix r s j (by omega) (by omega)).length, b'⟩ := by
            congr 1
  -- 2: Bs.c at the b-index is the consVec s_j (D.cB i)
  have hcBs : Bs.c (Sum.inr (Sum.inl i)) = consVec (s ⟨j - 1, by omega⟩) (D.cB i) := by
    dsimp [Bs, ofBstarOver, D]
  have h2 : ((Bs.c (Sum.inr (Sum.inl i))) ⟨j - (sPrefix r s j (by omega) (by omega)).length, b'⟩ : ℕ) =
      ((consVec (s ⟨j - 1, by omega⟩) (D.cB i)) ⟨j - (sPrefix r s j (by omega) (by omega)).length, b'⟩ : ℕ) := by
    apply congrArg (fun v : ℕ+ => (v : ℕ))
    exact congrFun hcBs ⟨j - (sPrefix r s j (by omega) (by omega)).length, b'⟩
  -- 3: consVec at position j−len = 1 gives the D.cB head
  have h3 : ((consVec (s ⟨j - 1, by omega⟩) (D.cB i))
        ⟨j - (sPrefix r s j (by omega) (by omega)).length, b'⟩ : ℕ) =
      ((D.cB i) ⟨0, (RelData.BCqIter F (k - j - 1) (toData F R0)).hdepB i⟩ : ℕ) := by
    have hcv := consVec_nat_value (s ⟨j - 1, by omega⟩) (D.cB i)
      (j - (sPrefix r s j (by omega) (by omega)).length) b'
    have hjj : j - (sPrefix r s j (by omega) (by omega)).length = 1 := by omega
    have hnz : j - (sPrefix r s j (by omega) (by omega)).length ≠ 0 := by omega
    have hpos : 0 < (RelData.BCqIter F (k - j - 1) (toData F R0)).depB i :=
      (RelData.BCqIter F (k - j - 1) (toData F R0)).hdepB i
    calc
      ((consVec (s ⟨j - 1, by omega⟩) (D.cB i))
            ⟨j - (sPrefix r s j (by omega) (by omega)).length, b'⟩ : ℕ)
          = ((D.cB i) ⟨(j - (sPrefix r s j (by omega) (by omega)).length) - 1,
              (by omega : (j - (sPrefix r s j (by omega) (by omega)).length) - 1 <
                  (RelData.BCqIter F (k - j - 1) (toData F R0)).depB i)⟩ : ℕ) := by
            apply congrArg (fun v : ℕ+ => (v : ℕ))
            rw [hcv]
            simp [hnz]
      _ = ((D.cB i) ⟨0, (RelData.BCqIter F (k - j - 1) (toData F R0)).hdepB i⟩ : ℕ) := by
            rw [show (⟨(j - (sPrefix r s j (by omega) (by omega)).length) - 1,
                (by omega : (j - (sPrefix r s j (by omega) (by omega)).length) - 1 <
                    (RelData.BCqIter F (k - j - 1) (toData F R0)).depB i)⟩ :
                    Fin ((RelData.BCqIter F (k - j - 1) (toData F R0)).depB i)) =
                ⟨0, (RelData.BCqIter F (k - j - 1) (toData F R0)).hdepB i⟩ from (by
              apply Fin.ext
              simp
              omega)]
  -- 4: D.cB heads are 1
  have h4 : ((D.cB i) ⟨0, (RelData.BCqIter F (k - j - 1) (toData F R0)).hdepB i⟩ : ℕ) = 1 := by
    have hh := RelData.BCqIter_head_one F (k - j - 1) R0 hbhd i
    have hh' := congrArg (fun t : ℕ+ => (t : ℕ)) hh
    simpa [oneExp, D] using hh'
  calc
    ((Q.c (Sum.inr (Sum.inl i))) ⟨j, hmj⟩ : ℕ)
        = ((Bs.c (Sum.inr (Sum.inl i))) ⟨j - (sPrefix r s j (by omega) (by omega)).length, b'⟩ : ℕ) := h1
    _ = ((consVec (s ⟨j - 1, by omega⟩) (D.cB i)) ⟨j - (sPrefix r s j (by omega) (by omega)).length, b'⟩ : ℕ) := h2
    _ = ((D.cB i) ⟨0, (RelData.BCqIter F (k - j - 1) (toData F R0)).hdepB i⟩ : ℕ) := h3
    _ = 1 := h4

/-- The type-3 member `inr (inr i)` of the (2.14) chain has value `s_j + 1` at
full-tuple position `j−1` (its tuple is `(s_1,…,s_{j−1}, s_j+1, …)`). -/
lemma type3_sjadd_one_at (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i : D.ιB, ∀ (hm : j - 1 < Q.dep (Sum.inr (Sum.inr i))),
      ((Q.c (Sum.inr (Sum.inr i))) ⟨j - 1, hm⟩ : ℕ) = (s ⟨j - 1, by omega⟩ : ℕ) + 1 := by
  classical
  intro D Bs Q i hm
  have hlen : (sPrefix r s j (by omega) (by omega)).length = j - 1 :=
    sPrefix_length r s j (by omega) (by omega)
  have hge : (sPrefix r s j (by omega) (by omega)).length ≤ j - 1 := by omega
  have hQdep : Q.dep (Sum.inr (Sum.inr i)) =
      Bs.dep (Sum.inr (Sum.inr i)) + (sPrefix r s j (by omega) (by omega)).length := by
    exact FixedOver.prependList_dep F Bs (sPrefix r s j (by omega) (by omega)) (Sum.inr (Sum.inr i))
  have b' : (j - 1) - (sPrefix r s j (by omega) (by omega)).length < Bs.dep (Sum.inr (Sum.inr i)) := by
    have hm1 : j - 1 < Bs.dep (Sum.inr (Sum.inr i)) + (sPrefix r s j (by omega) (by omega)).length := by
      rw [← hQdep]
      exact hm
    omega
  have h1 : ((Q.c (Sum.inr (Sum.inr i))) ⟨j - 1, hm⟩ : ℕ) =
      ((Bs.c (Sum.inr (Sum.inr i))) ⟨(j - 1) - (sPrefix r s j (by omega) (by omega)).length, b'⟩ : ℕ) := by
    have hv := prependList_c_base_value F Bs (sPrefix r s j (by omega) (by omega))
      (Sum.inr (Sum.inr i)) (j - 1) hm hge
    apply congrArg (fun v : ℕ+ => (v : ℕ))
    calc
      (Q.c (Sum.inr (Sum.inr i))) ⟨j - 1, hm⟩
          = (Bs.c (Sum.inr (Sum.inr i))) ⟨(j - 1) - (sPrefix r s j (by omega) (by omega)).length,
              (by
                have hd := FixedOver.prependList_dep F Bs (sPrefix r s j (by omega) (by omega)) (Sum.inr (Sum.inr i))
                rw [hd] at hm
                omega)⟩ := hv
      _ = (Bs.c (Sum.inr (Sum.inr i))) ⟨(j - 1) - (sPrefix r s j (by omega) (by omega)).length, b'⟩ := by
            congr 1
  have hcBs : Bs.c (Sum.inr (Sum.inr i)) =
      headAdd (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i) := by
    dsimp [Bs, ofBstarOver, D]
  have h2 : ((Bs.c (Sum.inr (Sum.inr i))) ⟨(j - 1) - (sPrefix r s j (by omega) (by omega)).length, b'⟩ : ℕ) =
      ((headAdd (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i))
        ⟨(j - 1) - (sPrefix r s j (by omega) (by omega)).length, b'⟩ : ℕ) := by
    apply congrArg (fun v : ℕ+ => (v : ℕ))
    exact congrFun hcBs ⟨(j - 1) - (sPrefix r s j (by omega) (by omega)).length, b'⟩
  have h3 : ((headAdd (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i))
        ⟨(j - 1) - (sPrefix r s j (by omega) (by omega)).length, b'⟩ : ℕ) =
      (s ⟨j - 1, by omega⟩ : ℕ) + 1 := by
    have hjj : (j - 1) - (sPrefix r s j (by omega) (by omega)).length = 0 := by omega
    rw [show (⟨(j - 1) - (sPrefix r s j (by omega) (by omega)).length, b'⟩ :
            Fin ((RelData.BCqIter F (k - j - 1) (toData F R0)).depB i)) =
          ⟨0, D.hdepB i⟩ from (by
        apply Fin.ext
        simp
        omega)]
    have hha := headAdd_head (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i)
    have hc := congrArg (fun t : ℕ+ => (t : ℕ)) hha
    rw [hc]
    have hbhead := RelData.BCqIter_head_one F (k - j - 1) R0 hbhd i
    have hbhead' : (((D.cB i) ⟨0, (RelData.BCqIter F (k - j - 1) (toData F R0)).hdepB i⟩ : ℕ) = 1) := by
      have hh' := congrArg (fun t : ℕ+ => (t : ℕ)) hbhead
      simpa [oneExp, D] using hh'
    rw [hbhead']
    rfl
  calc
    ((Q.c (Sum.inr (Sum.inr i))) ⟨j - 1, hm⟩ : ℕ)
        = ((Bs.c (Sum.inr (Sum.inr i))) ⟨(j - 1) - (sPrefix r s j (by omega) (by omega)).length, b'⟩ : ℕ) := h1
    _ = ((headAdd (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i))
          ⟨(j - 1) - (sPrefix r s j (by omega) (by omega)).length, b'⟩ : ℕ) := h2
    _ = (s ⟨j - 1, by omega⟩ : ℕ) + 1 := h3

end ZagierHoffmanPositiveChar
