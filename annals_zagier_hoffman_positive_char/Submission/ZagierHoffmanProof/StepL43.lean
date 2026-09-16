import Submission.ZagierHoffmanProof.StepL42

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L43: CASE-2 (R1) type-3 tail/psum/weight facts

Mirrors StepL32's type-3 family (`type3_tail_pad0`, `type3_psum_front`,
`type3_pad0_headAdd`, `type3_weight_decompose`, `type3_weight_eq`) and StepL35's
`type3_psum_k_le_X` at the R1 config: s : Fin k (depth k), `j` the last index with
`s_j < q`, positions `j..k−1` of `s` all `q` (`hqend`), R0 := r1Rel F.  The
`r1Rel` level-0 b-tail has weight `q−1` (`r1Rel_tail_weight`) and prefix bound
`≤ q−1` (`r1Rel_tail_psum`), so the block arithmetic is
`psum s k = psum s j + (k−j)·q` and a type-3 member's prefix-k is at most
`psum s j + 1 + (k−j−1)·q + (q−1) = psum s k`.
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Padded values of a type-3 member beyond the `s_j+1` at position `j−1`: at full
position `j+t` the value is the `t`-th padded entry of the b-fiber tail
`expTail (D.cB i)`. -/
lemma type3_tail_pad0_R1 (k : ℕ) (s : Fin k → ℕ+) (j : ℕ)
    (hk1 : 1 ≤ k) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F) :
    let D := RelData.BCqIter F (k - j - 1) (toData F (r1Rel F))
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) (r1Rel F) e)
        (RelData.iterate_merge_hv F (k - j - 1) (r1Rel F) (s ⟨j - 1, by omega⟩) (by omega) (r1Rel_hbhd F))
    let Q := FixedOver.prependList F Bs (sPrefix k s j (by omega) (by omega))
    ∀ i : D.ιB, ∀ (t : ℕ),
      pad0 (Q.c (Sum.inr (Sum.inr i))) (j + t) = pad0 (expTail (D.cB i)) t := by
  classical
  intro D Bs Q i t
  have hlen : (sPrefix k s j (by omega) (by omega)).length = j - 1 :=
    sPrefix_length k s j (by omega) (by omega)
  have hQdep : Q.dep (Sum.inr (Sum.inr i)) =
      Bs.dep (Sum.inr (Sum.inr i)) + (sPrefix k s j (by omega) (by omega)).length := by
    exact FixedOver.prependList_dep F Bs (sPrefix k s j (by omega) (by omega)) (Sum.inr (Sum.inr i))
  have hBsdep : Bs.dep (Sum.inr (Sum.inr i)) = D.depB i := by
    dsimp [Bs, ofBstarOver]
  by_cases hm : j + t < Q.dep (Sum.inr (Sum.inr i))
  · have hge : (sPrefix k s j (by omega) (by omega)).length ≤ j + t := by omega
    have b' : (j + t) - (sPrefix k s j (by omega) (by omega)).length < Bs.dep (Sum.inr (Sum.inr i)) := by
      rw [hBsdep]
      have hm0 : j + t < Q.dep (Sum.inr (Sum.inr i)) := hm
      rw [hQdep, hBsdep, hlen] at hm0
      omega
    have ht1b : t + 1 < D.depB i := by
      have hm0 : j + t < Q.dep (Sum.inr (Sum.inr i)) := hm
      rw [hQdep, hBsdep, hlen] at hm0
      omega
    have hval : ((Q.c (Sum.inr (Sum.inr i))) ⟨j + t, hm⟩ : ℕ) =
        ((D.cB i) ⟨t + 1, ht1b⟩ : ℕ) := by
      have h1 : ((Q.c (Sum.inr (Sum.inr i))) ⟨j + t, hm⟩ : ℕ) =
          ((Bs.c (Sum.inr (Sum.inr i))) ⟨(j + t) - (sPrefix k s j (by omega) (by omega)).length, b'⟩ : ℕ) := by
        have hv := prependList_c_base_value F Bs (sPrefix k s j (by omega) (by omega))
          (Sum.inr (Sum.inr i)) (j + t) hm hge
        apply congrArg (fun v : ℕ+ => (v : ℕ))
        calc
          (Q.c (Sum.inr (Sum.inr i))) ⟨j + t, hm⟩
              = (Bs.c (Sum.inr (Sum.inr i))) ⟨(j + t) - (sPrefix k s j (by omega) (by omega)).length,
                  (by
                    have hd := FixedOver.prependList_dep F Bs (sPrefix k s j (by omega) (by omega)) (Sum.inr (Sum.inr i))
                    rw [hd] at hm
                    omega)⟩ := hv
          _ = (Bs.c (Sum.inr (Sum.inr i))) ⟨(j + t) - (sPrefix k s j (by omega) (by omega)).length, b'⟩ := by
                congr 1
      have hcBs : Bs.c (Sum.inr (Sum.inr i)) = headAdd (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i) := by
        dsimp [Bs, ofBstarOver, D]
      have hbp : (j + t) - (sPrefix k s j (by omega) (by omega)).length = t + 1 := by omega
      have h2 : ((Bs.c (Sum.inr (Sum.inr i))) ⟨(j + t) - (sPrefix k s j (by omega) (by omega)).length, b'⟩ : ℕ) =
          ((headAdd (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i))
            ⟨(j + t) - (sPrefix k s j (by omega) (by omega)).length, b'⟩ : ℕ) := by
        apply congrArg (fun v : ℕ+ => (v : ℕ))
        exact congrFun hcBs ⟨(j + t) - (sPrefix k s j (by omega) (by omega)).length, b'⟩
      have h3 : ((headAdd (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i))
            ⟨(j + t) - (sPrefix k s j (by omega) (by omega)).length, b'⟩ : ℕ) =
          ((D.cB i) ⟨t + 1, ht1b⟩ : ℕ) := by
        -- headAdd at position t+1 ≥ 1 is the old tuple at t+1
        have hb2 : t + 1 < D.depB i := by
          have hb2' := b'
          simpa [hbp, hBsdep] using hb2'
        have hidx : (⟨(j + t) - (sPrefix k s j (by omega) (by omega)).length, b'⟩ : Fin (D.depB i)) =
            ⟨t + 1, hb2⟩ := by
          apply Fin.ext
          simp [hbp]
        have hhadd : (headAdd (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i)) ⟨t + 1, hb2⟩ =
            (D.cB i) ⟨t + 1, hb2⟩ := by
          have hnz : t + 1 ≠ 0 := by omega
          dsimp [headAdd]
        have h3' : (headAdd (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i))
                ⟨(j + t) - (sPrefix k s j (by omega) (by omega)).length, b'⟩ =
            (D.cB i) ⟨t + 1, ht1b⟩ := by
          calc
            (headAdd (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i))
                  ⟨(j + t) - (sPrefix k s j (by omega) (by omega)).length, b'⟩
                = (headAdd (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i)) ⟨t + 1, hb2⟩ := by
                  rw [hidx]
            _ = (D.cB i) ⟨t + 1, hb2⟩ := hhadd
            _ = (D.cB i) ⟨t + 1, ht1b⟩ := by
                  congr 1
        exact congrArg (fun v : ℕ+ => (v : ℕ)) h3'
      calc
        ((Q.c (Sum.inr (Sum.inr i))) ⟨j + t, hm⟩ : ℕ)
            = ((Bs.c (Sum.inr (Sum.inr i))) ⟨(j + t) - (sPrefix k s j (by omega) (by omega)).length, b'⟩ : ℕ) := h1
        _ = ((headAdd (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i))
              ⟨(j + t) - (sPrefix k s j (by omega) (by omega)).length, b'⟩ : ℕ) := h2
        _ = ((D.cB i) ⟨t + 1, ht1b⟩ : ℕ) := h3
    rw [pad0_of_lt (Q.c (Sum.inr (Sum.inr i))) hm]
    have hdep : t < (D.depB i) - 1 := by omega
    rw [pad0_of_lt (expTail (D.cB i)) hdep]
    have h4 : ((D.cB i) ⟨t + 1, ht1b⟩ : ℕ) = ((expTail (D.cB i)) ⟨t, hdep⟩ : ℕ) := by
      rw [expTail]
    exact hval.trans h4
  · have hgeQ : Q.dep (Sum.inr (Sum.inr i)) ≤ j + t := le_of_not_gt hm
    have hp1 : pad0 (Q.c (Sum.inr (Sum.inr i))) (j + t) = 0 := pad0_of_ge (Q.c (Sum.inr (Sum.inr i))) hgeQ
    rw [hp1]
    have hdep : (D.depB i) - 1 ≤ t := by
      have hge0 : Q.dep (Sum.inr (Sum.inr i)) ≤ j + t := hgeQ
      rw [hQdep, hBsdep, hlen] at hge0
      omega
    have hp2 : pad0 (expTail (D.cB i)) t = 0 := pad0_of_ge (expTail (D.cB i)) hdep
    rw [hp2]

/-- Type-3 front sum: the first `j−1` entries are `s₁..s_{j−1}`. -/
lemma type3_psum_front_R1 (k : ℕ) (s : Fin k → ℕ+) (j : ℕ)
    (hk1 : 1 ≤ k) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F) :
    let D := RelData.BCqIter F (k - j - 1) (toData F (r1Rel F))
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) (r1Rel F) e)
        (RelData.iterate_merge_hv F (k - j - 1) (r1Rel F) (s ⟨j - 1, by omega⟩) (by omega) (r1Rel_hbhd F))
    let Q := FixedOver.prependList F Bs (sPrefix k s j (by omega) (by omega))
    ∀ i : D.ιB, psum (Q.c (Sum.inr (Sum.inr i))) (j - 1) = psum s (j - 1) := by
  classical
  intro D Bs Q i
  have hQdep : Q.dep (Sum.inr (Sum.inr i)) =
      Bs.dep (Sum.inr (Sum.inr i)) + (sPrefix k s j (by omega) (by omega)).length := by
    exact FixedOver.prependList_dep F Bs (sPrefix k s j (by omega) (by omega)) (Sum.inr (Sum.inr i))
  have hBsdep : Bs.dep (Sum.inr (Sum.inr i)) = D.depB i := by
    dsimp [Bs, ofBstarOver]
  apply psum_eq_of_pad0_eq
  intro x hx
  have hx1 : x < j - 1 := hx
  have hxQ : x < Q.dep (Sum.inr (Sum.inr i)) := by
    have hQd : Q.dep (Sum.inr (Sum.inr i)) = (j - 1) + D.depB i := by
      have hlen : (sPrefix k s j (by omega) (by omega)).length = j - 1 :=
        sPrefix_length k s j (by omega) (by omega)
      rw [hQdep, hBsdep, hlen]
      omega
    rw [hQd]
    omega
  have hxr : x < k := by
    have : x < j - 1 := hx1
    omega
  have hv := member_prefix_pos_R1 F k s j hk1 hj1 hjk hsj (Sum.inr (Sum.inr i)) x hx1 hxQ
  rw [pad0_of_lt (Q.c (Sum.inr (Sum.inr i))) hxQ]
  rw [pad0_of_lt s hxr]
  exact congrArg (fun t : ℕ+ => (t : ℕ)) hv

/-- Type-3 member padded values at full positions `(j−1)+t` equal the `t`-th padded
entry of the merged tuple `headAdd s_j (D.cB i)` (its head `s_j+1`, then the fiber
tail). -/
lemma type3_pad0_headAdd_R1 (k : ℕ) (s : Fin k → ℕ+) (j : ℕ)
    (hk1 : 1 ≤ k) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F) :
    let D := RelData.BCqIter F (k - j - 1) (toData F (r1Rel F))
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) (r1Rel F) e)
        (RelData.iterate_merge_hv F (k - j - 1) (r1Rel F) (s ⟨j - 1, by omega⟩) (by omega) (r1Rel_hbhd F))
    let Q := FixedOver.prependList F Bs (sPrefix k s j (by omega) (by omega))
    ∀ i : D.ιB, ∀ (t : ℕ),
      pad0 (Q.c (Sum.inr (Sum.inr i))) ((j - 1) + t) =
        pad0 (headAdd (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i)) t := by
  classical
  intro D Bs Q i t
  have hlen : (sPrefix k s j (by omega) (by omega)).length = j - 1 :=
    sPrefix_length k s j (by omega) (by omega)
  have hQdep : Q.dep (Sum.inr (Sum.inr i)) = (j - 1) + D.depB i := by
    have h1 := FixedOver.prependList_dep F Bs (sPrefix k s j (by omega) (by omega)) (Sum.inr (Sum.inr i))
    have h2 : Bs.dep (Sum.inr (Sum.inr i)) = D.depB i := by
      dsimp [Bs, ofBstarOver]
    rw [h1, h2, hlen]
    omega
  have hBsdep : Bs.dep (Sum.inr (Sum.inr i)) = D.depB i := by
    dsimp [Bs, ofBstarOver]
  by_cases ht : t < D.depB i
  · cases t with
    | zero =>
        -- position j−1: the merged head s_j + 1 on both sides
        have hmj : j - 1 < Q.dep (Sum.inr (Sum.inr i)) := by
          rw [hQdep]
          omega
        have hsjadd := type3_sjadd_one_at_R1 F k s j hk1 hj1 hjk hsj i hmj
        rw [show (j - 1) + 0 = j - 1 by omega]
        rw [pad0_of_lt (Q.c (Sum.inr (Sum.inr i))) hmj]
        have hh := BCqIter_head_one_data F (k - j - 1) (r1Rel F) (r1Rel_hbhd F) i
        have hhadd := headAdd_head (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i)
        have hr : pad0 (headAdd (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i)) 0 =
            (s ⟨j - 1, by omega⟩ : ℕ) + 1 := by
          have hz : 0 < D.depB i := D.hdepB i
          rw [pad0_of_lt (headAdd (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i)) hz]
          have hidx : (⟨0, hz⟩ : Fin (D.depB i)) = ⟨0, D.hdepB i⟩ := by
            apply Fin.ext
            rfl
          rw [hidx]
          have hv := congrArg (fun u : ℕ+ => (u : ℕ)) hhadd
          have hh1 : ((D.cB i) ⟨0, D.hdepB i⟩ : ℕ) = 1 := hh
          rw [hv, hh1]
          rfl
        rw [hr]
        exact hsjadd
    | succ t' =>
        have hsh := type3_tail_pad0_R1 F k s j hk1 hj1 hjk hsj i t'
        have hdom : (j - 1) + (t' + 1) = j + t' := by omega
        rw [hdom]
        rw [hsh]
        have ht1 : t' + 1 < D.depB i := ht
        have hha : (headAdd (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i)) ⟨t' + 1, ht1⟩ =
            (D.cB i) ⟨t' + 1, ht1⟩ := by
          have hnz : t' + 1 ≠ 0 := by omega
          dsimp [headAdd]
        have hr : pad0 (headAdd (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i)) (t' + 1) =
            ((D.cB i) ⟨t' + 1, ht1⟩ : ℕ) := by
          rw [pad0_of_lt (headAdd (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i)) ht1]
          exact congrArg (fun u : ℕ+ => (u : ℕ)) hha
        have hdep' : t' < D.depB i - 1 := by omega
        have hl : pad0 (expTail (D.cB i)) t' = ((D.cB i) ⟨t' + 1, ht1⟩ : ℕ) := by
          rw [pad0_of_lt (expTail (D.cB i)) hdep']
          rfl
        rw [hr]
        rw [hl]
  · have htge : D.depB i ≤ t := le_of_not_gt ht
    have hgeQ : Q.dep (Sum.inr (Sum.inr i)) ≤ (j - 1) + t := by
      rw [hQdep]
      omega
    rw [pad0_of_ge (Q.c (Sum.inr (Sum.inr i))) hgeQ]
    rw [pad0_of_ge (headAdd (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i)) htge]


/-- Weight of a type-3 member: the `s₁..s_{j−1}` front plus the merged head `s_j+1`
plus the fiber tail. -/
lemma type3_weight_decompose_R1 (k : ℕ) (s : Fin k → ℕ+) (j : ℕ)
    (hk1 : 1 ≤ k) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F) :
    let D := RelData.BCqIter F (k - j - 1) (toData F (r1Rel F))
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) (r1Rel F) e)
        (RelData.iterate_merge_hv F (k - j - 1) (r1Rel F) (s ⟨j - 1, by omega⟩) (by omega) (r1Rel_hbhd F))
    let Q := FixedOver.prependList F Bs (sPrefix k s j (by omega) (by omega))
    ∀ i : D.ιB,
      weight (Q.dep (Sum.inr (Sum.inr i))) (Q.c (Sum.inr (Sum.inr i))) =
        psum s (j - 1) + ((s ⟨j - 1, by omega⟩ : ℕ) + 1 +
          weight (D.depB i - 1) (expTail (D.cB i))) := by
  classical
  intro D Bs Q i
  have hQdep : Q.dep (Sum.inr (Sum.inr i)) = (j - 1) + D.depB i := by
    have hlen : (sPrefix k s j (by omega) (by omega)).length = j - 1 :=
      sPrefix_length k s j (by omega) (by omega)
    have h1 := FixedOver.prependList_dep F Bs (sPrefix k s j (by omega) (by omega)) (Sum.inr (Sum.inr i))
    have h2 : Bs.dep (Sum.inr (Sum.inr i)) = D.depB i := by
      dsimp [Bs, ofBstarOver]
    rw [h1, h2, hlen]
    omega
  have hwpsum : weight (Q.dep (Sum.inr (Sum.inr i))) (Q.c (Sum.inr (Sum.inr i))) =
      psum (Q.c (Sum.inr (Sum.inr i))) (Q.dep (Sum.inr (Sum.inr i))) := by
    have hp := psum_ge_depth (Q.c (Sum.inr (Sum.inr i))) (m := Q.dep (Sum.inr (Sum.inr i))) (le_refl _)
    exact hp.symm
  have hsplit : psum (Q.c (Sum.inr (Sum.inr i))) ((j - 1) + D.depB i) =
      psum (Q.c (Sum.inr (Sum.inr i))) (j - 1) +
        (∑ t ∈ Finset.range (D.depB i), pad0 (Q.c (Sum.inr (Sum.inr i))) ((j - 1) + t)) := by
    change (∑ x ∈ Finset.range ((j - 1) + D.depB i), pad0 (Q.c (Sum.inr (Sum.inr i))) x) =
      (∑ x ∈ Finset.range (j - 1), pad0 (Q.c (Sum.inr (Sum.inr i))) x) +
        (∑ t ∈ Finset.range (D.depB i), pad0 (Q.c (Sum.inr (Sum.inr i))) ((j - 1) + t))
    rw [Finset.sum_range_add]
  have hh := BCqIter_head_one_data F (k - j - 1) (r1Rel F) (r1Rel_hbhd F) i
  have htail : (∑ t ∈ Finset.range (D.depB i), pad0 (Q.c (Sum.inr (Sum.inr i))) ((j - 1) + t)) =
      ((s ⟨j - 1, by omega⟩ : ℕ) + 1 + weight (D.depB i - 1) (expTail (D.cB i))) := by
    calc
      (∑ t ∈ Finset.range (D.depB i), pad0 (Q.c (Sum.inr (Sum.inr i))) ((j - 1) + t))
          = (∑ t ∈ Finset.range (D.depB i),
              pad0 (headAdd (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i)) t) := by
            apply Finset.sum_congr rfl
            intro t ht
            exact type3_pad0_headAdd_R1 F k s j hk1 hj1 hjk hsj i t
      _ = psum (headAdd (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i)) (D.depB i) := by rfl
      _ = weight (D.depB i) (headAdd (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i)) := by
            have hp' := psum_ge_depth (headAdd (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i))
              (m := D.depB i) (le_refl _)
            exact hp'
      _ = ((s ⟨j - 1, by omega⟩ : ℕ) + 1 + weight (D.depB i - 1) (expTail (D.cB i))) := by
            have hw := headAdd_weight (D.hdepB i) (s ⟨j - 1, by omega⟩) (D.cB i)
            rw [hw]
            have hh1 : ((D.cB i) ⟨0, D.hdepB i⟩ : ℕ) = 1 := hh
            rw [hh1]
  have hpfront : psum (Q.c (Sum.inr (Sum.inr i))) (j - 1) = psum s (j - 1) :=
    type3_psum_front_R1 F k s j hk1 hj1 hjk hsj i
  calc
    weight (Q.dep (Sum.inr (Sum.inr i))) (Q.c (Sum.inr (Sum.inr i)))
        = psum (Q.c (Sum.inr (Sum.inr i))) (Q.dep (Sum.inr (Sum.inr i))) := hwpsum
    _ = psum (Q.c (Sum.inr (Sum.inr i))) ((j - 1) + D.depB i) := by
          exact congrArg (psum (Q.c (Sum.inr (Sum.inr i)))) hQdep
    _ = psum (Q.c (Sum.inr (Sum.inr i))) (j - 1) +
          (∑ t ∈ Finset.range (D.depB i), pad0 (Q.c (Sum.inr (Sum.inr i))) ((j - 1) + t)) := hsplit
    _ = psum s (j - 1) + ((s ⟨j - 1, by omega⟩ : ℕ) + 1 +
          weight (D.depB i - 1) (expTail (D.cB i))) := by
          rw [hpfront, htail]


/-- ★ Type-3 weight preservation: a type-3 member has weight `w(s)` — the level-0
`b`-tail of `r1Rel` has weight `q−1`, so member weight =
`psum s (j−1) + (s_j + 1 + (k−j−1)·q + (q−1)) = psum s k = weight k s`. -/
lemma type3_weight_eq_R1 (k : ℕ) (s : Fin k → ℕ+) (j : ℕ)
    (hk1 : 1 ≤ k) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hqend : ∀ i : Fin k, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < k → (s i : ℕ) = Nat.card F) :
    let D := RelData.BCqIter F (k - j - 1) (toData F (r1Rel F))
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) (r1Rel F) e)
        (RelData.iterate_merge_hv F (k - j - 1) (r1Rel F) (s ⟨j - 1, by omega⟩) (by omega) (r1Rel_hbhd F))
    let Q := FixedOver.prependList F Bs (sPrefix k s j (by omega) (by omega))
    ∀ i : D.ιB,
      weight (Q.dep (Sum.inr (Sum.inr i))) (Q.c (Sum.inr (Sum.inr i))) = weight k s := by
  classical
  intro D Bs Q i
  have hdec := type3_weight_decompose_R1 F k s j hk1 hj1 hjk hsj i
  have hfib := BCq_fiber_weight_X F (k - j - 1) (r1Rel F) (r1Rel_hbhd F) (qMinusExp F : ℕ)
    (r1Rel_tail_weight F) i
  -- hfib : w(expTail (D.cB i)) = (k−j−1)·q + (q−1)
  have hsu := psum_succ s (j - 1)
  have hjj : (j - 1) + 1 = j := by omega
  have hpj : psum s j = psum s (j - 1) + (s ⟨j - 1, by omega⟩ : ℕ) := by
    rw [hjj] at hsu
    rw [hsu]
    rw [pad0_of_lt s (by omega : j - 1 < k)]
  -- block psum s k = psum s j + (k−j)·q
  have hp1 : psum s k = psum s j + (k - j) * Nat.card F := by
    apply psum_const_block (s := s) (j := j) (m := k) (q := Nat.card F)
    · omega
    · intro x hx1 hx2
      have hxr : x < k := hx2
      have hval : (s ⟨x, hxr⟩ : ℕ) = Nat.card F := hqend ⟨x, hxr⟩ hx1 hx2
      rw [pad0_of_lt s hxr]
      exact hval
  have hq1 : 1 ≤ Nat.card F := by
    have h2 : 2 ≤ Nat.card F := card_ge_two F
    omega
  calc
    weight (Q.dep (Sum.inr (Sum.inr i))) (Q.c (Sum.inr (Sum.inr i)))
        = psum s (j - 1) + ((s ⟨j - 1, by omega⟩ : ℕ) + 1 +
            weight (D.depB i - 1) (expTail (D.cB i))) := hdec
    _ = psum s (j - 1) + ((s ⟨j - 1, by omega⟩ : ℕ) + 1 +
            ((k - j - 1) * Nat.card F + (qMinusExp F : ℕ))) := by
          rw [hfib]
    _ = psum s (j - 1) + ((s ⟨j - 1, by omega⟩ : ℕ) + 1 +
            ((k - j - 1) * Nat.card F + (Nat.card F - 1))) := by
          have hqminus : (qMinusExp F : ℕ) = Nat.card F - 1 := by rfl
          rw [hqminus]
    _ = psum s (j - 1) + ((s ⟨j - 1, by omega⟩ : ℕ) +
            ((k - j - 1) * Nat.card F + Nat.card F)) := by omega
    _ = psum s (j - 1) + ((s ⟨j - 1, by omega⟩ : ℕ) + (k - j) * Nat.card F) := by
          have hn' : (k - j) * Nat.card F = (k - j - 1) * Nat.card F + Nat.card F := by
            have hk' : k - j = (k - j - 1) + 1 := by omega
            calc
              (k - j) * Nat.card F = ((k - j - 1) + 1) * Nat.card F := congrArg (fun m : ℕ => m * Nat.card F) hk'
              _ = (k - j - 1) * Nat.card F + 1 * Nat.card F := by rw [Nat.add_mul]
              _ = (k - j - 1) * Nat.card F + Nat.card F := by rw [one_mul]
          rw [hn']
    _ = psum s k := by
          rw [hp1, hpj]
          omega
    _ = weight k s := by exact psum_ge_depth s (le_refl k)


/-- ★ Type-3 prefix sum at `k` is at most that of `s`: member prefix-k =
`psum s j + 1 + psum(expTail (D.cB i))(k−j) ≤ psum s j + 1 + (k−j−1)·q + (q−1)
= psum s j + (k−j)·q = psum s k` (the `r1Rel` b-tail prefix bound `q−1`, block
positions `j..k−1` of `s` all `q`). -/
lemma type3_psum_k_le_R1 (k : ℕ) (s : Fin k → ℕ+) (j : ℕ)
    (hk1 : 1 ≤ k) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hqend : ∀ i : Fin k, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < k → (s i : ℕ) = Nat.card F) :
    let D := RelData.BCqIter F (k - j - 1) (toData F (r1Rel F))
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) (r1Rel F) e)
        (RelData.iterate_merge_hv F (k - j - 1) (r1Rel F) (s ⟨j - 1, by omega⟩) (by omega) (r1Rel_hbhd F))
    let Q := FixedOver.prependList F Bs (sPrefix k s j (by omega) (by omega))
    ∀ i : D.ιB, psum (Q.c (Sum.inr (Sum.inr i))) k ≤ psum s k := by
  classical
  intro D Bs Q i
  have hjk' : j ≤ k := by omega
  have hsplit : psum (Q.c (Sum.inr (Sum.inr i))) k =
      psum (Q.c (Sum.inr (Sum.inr i))) j +
        (∑ t ∈ Finset.range (k - j), pad0 (Q.c (Sum.inr (Sum.inr i))) (j + t)) := by
    change (∑ x ∈ Finset.range k, pad0 (Q.c (Sum.inr (Sum.inr i))) x) =
      (∑ x ∈ Finset.range j, pad0 (Q.c (Sum.inr (Sum.inr i))) x) +
        (∑ t ∈ Finset.range (k - j), pad0 (Q.c (Sum.inr (Sum.inr i))) (j + t))
    have hk : k = j + (k - j) := (Nat.add_sub_of_le hjk').symm
    rw [show Finset.range k = Finset.range (j + (k - j)) by exact congrArg Finset.range hk]
    rw [Finset.sum_range_add]
  have hpj : psum (Q.c (Sum.inr (Sum.inr i))) j = psum s j + 1 :=
    type3_psum_j_R1 F k s j hk1 hj1 hjk hsj i
  have htail : (∑ t ∈ Finset.range (k - j), pad0 (Q.c (Sum.inr (Sum.inr i))) (j + t)) =
      psum (expTail (D.cB i)) (k - j) := by
    change (∑ t ∈ Finset.range (k - j), pad0 (Q.c (Sum.inr (Sum.inr i))) (j + t)) =
      (∑ t ∈ Finset.range (k - j), pad0 (expTail (D.cB i)) t)
    apply Finset.sum_congr rfl
    intro t ht
    exact type3_tail_pad0_R1 F k s j hk1 hj1 hjk hsj i t
  have hfib := BCq_fiber_prefix_X F (k - j - 1) (r1Rel F) (r1Rel_hbhd F)
    (fun m : ℕ => (qMinusExp F : ℕ)) (fun j' => r1Rel_tail_psum F j') i (k - j)
  have hsub : (k - j) - (k - j - 1) = 1 := by omega
  have hfib' : psum (expTail (D.cB i)) (k - j) ≤ (k - j - 1) * Nat.card F + (qMinusExp F : ℕ) := by
    simpa [D, hsub] using hfib
  have hp1 : psum s k = psum s j + (k - j) * Nat.card F := by
    apply psum_const_block (s := s) (j := j) (m := k) (q := Nat.card F)
    · omega
    · intro x hx1 hx2
      have hxr : x < k := hx2
      have hval : (s ⟨x, hxr⟩ : ℕ) = Nat.card F := hqend ⟨x, hxr⟩ hx1 hx2
      rw [pad0_of_lt s hxr]
      exact hval
  calc
    psum (Q.c (Sum.inr (Sum.inr i))) k
        = psum (Q.c (Sum.inr (Sum.inr i))) j + psum (expTail (D.cB i)) (k - j) := by
          rw [hsplit, htail]
    _ = (psum s j + 1) + psum (expTail (D.cB i)) (k - j) := by rw [hpj]
    _ ≤ (psum s j + 1) + ((k - j - 1) * Nat.card F + (qMinusExp F : ℕ)) := by
          exact Nat.add_le_add_left hfib' (psum s j + 1)
    _ ≤ psum s j + (k - j) * Nat.card F := by
          have hqminus : (qMinusExp F : ℕ) = Nat.card F - 1 := by rfl
          have hn' : (k - j) * Nat.card F = (k - j - 1) * Nat.card F + Nat.card F := by
            have hk' : k - j = (k - j - 1) + 1 := by omega
            calc
              (k - j) * Nat.card F = ((k - j - 1) + 1) * Nat.card F := congrArg (fun m : ℕ => m * Nat.card F) hk'
              _ = (k - j - 1) * Nat.card F + 1 * Nat.card F := by rw [Nat.add_mul]
              _ = (k - j - 1) * Nat.card F + Nat.card F := by rw [one_mul]
          rw [hqminus]
          rw [hn']
          have hq1 : 1 ≤ Nat.card F := by
            have h2 : 2 ≤ Nat.card F := card_ge_two F
            omega
          omega
    _ = psum s k := by rw [← hp1]

end ZagierHoffmanPositiveChar
