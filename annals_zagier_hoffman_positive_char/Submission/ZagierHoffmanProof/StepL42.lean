import Submission.ZagierHoffmanProof.StepL41
import Submission.ZagierHoffmanProof.StepL32

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L42: CASE-2 (R1) type-2 per-member prefix facts

The CASE-2 (Prop 2.13) chain at the R1 config (s : Fin k, `j` the last index with
`s_j < q`, positions `j..k−1` all `q` — `hqend`) mirrors the CASE-1 type-2 family
lemmas of StepL26/27/28/30 with `r := k`, `R0 := r1Rel F`, and without the CASE-1
`hbig`/`hmid` hypotheses (impossible at `s_k = q`).  These are the front-value,
depth, `j`-prefix and tail-pad structural facts plus the final prefix-k STRICT bound
(the type-2 members' prefix-k < psum s k, feeding the Route-B recursion dispatch).

Reused verbatim (R0-parametric): BCq_fiber_prefix_qN, psum_const_block, psum_succ,
pad0_of_lt/ge, consVec_nat_value, weight_head_tail etc.  LEAN NOTES (inherited from
StepL30): the `by omega` merge-condition proofs need `hsj` in context; pads rewrite
with `pad0_of_lt`/`pad0_of_ge` on explicit bounds; `prependList_c_base_value` peel
followed by `congr 1` for the bound proofs; `congrArg (fun v : ℕ+ => (v : ℕ))` for
value-level statements.
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Every member of the CASE-2 chain shares the front prefix values with `s`: at
full-tuple positions `m < j−1` the value is `s_{m+1}`. -/
lemma member_prefix_pos_R1 (k : ℕ) (s : Fin k → ℕ+) (j : ℕ)
    (hk1 : 1 ≤ k) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F) :
    let D := RelData.BCqIter F (k - j - 1) (toData F (r1Rel F))
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) (r1Rel F) e)
        (RelData.iterate_merge_hv F (k - j - 1) (r1Rel F) (s ⟨j - 1, by omega⟩) (by omega) (r1Rel_hbhd F))
    let Q := FixedOver.prependList F Bs (sPrefix k s j (by omega) (by omega))
    ∀ p : D.ιA ⊕ (D.ιB ⊕ D.ιB),
      ∀ (m : ℕ) (hmf : m < j - 1) (hmQ : m < Q.dep p),
        (Q.c p) ⟨m, hmQ⟩ = s ⟨m, by omega⟩ := by
  classical
  intro D Bs Q p m hmf hmQ
  have hmfl : m < (sPrefix k s j (by omega) (by omega)).length := by
    have hlen : (sPrefix k s j (by omega) (by omega)).length = j - 1 :=
      sPrefix_length k s j (by omega) (by omega)
    simpa [hlen] using hmf
  have hval := prependList_c_front_value F Bs (sPrefix k s j (by omega) (by omega)) p m hmQ hmfl
  calc
    (Q.c p) ⟨m, hmQ⟩ = (sPrefix k s j (by omega) (by omega)).reverse.get
        ⟨m, by simpa using hmfl⟩ := by
          have hg := hval
          exact hg
    _ = s ⟨m, by omega⟩ := by
          exact sPrefix_reverse_value k s j (by omega) (by omega) m hmfl

/-- The type-2 members `inr (inl i)` have value `s_j` at full-tuple position `j−1`. -/
lemma type2_sj_at_jm1_R1 (k : ℕ) (s : Fin k → ℕ+) (j : ℕ)
    (hk1 : 1 ≤ k) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F) :
    let D := RelData.BCqIter F (k - j - 1) (toData F (r1Rel F))
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) (r1Rel F) e)
        (RelData.iterate_merge_hv F (k - j - 1) (r1Rel F) (s ⟨j - 1, by omega⟩) (by omega) (r1Rel_hbhd F))
    let Q := FixedOver.prependList F Bs (sPrefix k s j (by omega) (by omega))
    ∀ i : D.ιB, ∀ (hm : j - 1 < Q.dep (Sum.inr (Sum.inl i))),
      ((Q.c (Sum.inr (Sum.inl i))) ⟨j - 1, hm⟩ : ℕ) = (s ⟨j - 1, by omega⟩ : ℕ) := by
  classical
  intro D Bs Q i hm
  have hlen : (sPrefix k s j (by omega) (by omega)).length = j - 1 :=
    sPrefix_length k s j (by omega) (by omega)
  have hge : (sPrefix k s j (by omega) (by omega)).length ≤ j - 1 := by omega
  have hQdep : Q.dep (Sum.inr (Sum.inl i)) =
      Bs.dep (Sum.inr (Sum.inl i)) + (sPrefix k s j (by omega) (by omega)).length := by
    exact FixedOver.prependList_dep F Bs (sPrefix k s j (by omega) (by omega)) (Sum.inr (Sum.inl i))
  have b' : (j - 1) - (sPrefix k s j (by omega) (by omega)).length < Bs.dep (Sum.inr (Sum.inl i)) := by
    have hm1 : j - 1 < Bs.dep (Sum.inr (Sum.inl i)) + (sPrefix k s j (by omega) (by omega)).length := by
      rw [← hQdep]
      exact hm
    omega
  have h1 : ((Q.c (Sum.inr (Sum.inl i))) ⟨j - 1, hm⟩ : ℕ) =
      ((Bs.c (Sum.inr (Sum.inl i))) ⟨(j - 1) - (sPrefix k s j (by omega) (by omega)).length, b'⟩ : ℕ) := by
    have hv := prependList_c_base_value F Bs (sPrefix k s j (by omega) (by omega))
      (Sum.inr (Sum.inl i)) (j - 1) hm hge
    apply congrArg (fun v : ℕ+ => (v : ℕ))
    calc
      (Q.c (Sum.inr (Sum.inl i))) ⟨j - 1, hm⟩
          = (Bs.c (Sum.inr (Sum.inl i))) ⟨(j - 1) - (sPrefix k s j (by omega) (by omega)).length,
              (by
                have hd := FixedOver.prependList_dep F Bs (sPrefix k s j (by omega) (by omega)) (Sum.inr (Sum.inl i))
                rw [hd] at hm
                omega)⟩ := hv
      _ = (Bs.c (Sum.inr (Sum.inl i))) ⟨(j - 1) - (sPrefix k s j (by omega) (by omega)).length, b'⟩ := by
            congr 1
  have hcBs : Bs.c (Sum.inr (Sum.inl i)) = consVec (s ⟨j - 1, by omega⟩) (D.cB i) := by
    dsimp [Bs, ofBstarOver, D]
  have h2 : ((Bs.c (Sum.inr (Sum.inl i))) ⟨(j - 1) - (sPrefix k s j (by omega) (by omega)).length, b'⟩ : ℕ) =
      ((consVec (s ⟨j - 1, by omega⟩) (D.cB i))
        ⟨(j - 1) - (sPrefix k s j (by omega) (by omega)).length, b'⟩ : ℕ) := by
    apply congrArg (fun v : ℕ+ => (v : ℕ))
    exact congrFun hcBs ⟨(j - 1) - (sPrefix k s j (by omega) (by omega)).length, b'⟩
  have h3 : ((consVec (s ⟨j - 1, by omega⟩) (D.cB i))
        ⟨(j - 1) - (sPrefix k s j (by omega) (by omega)).length, b'⟩ : ℕ) =
      (s ⟨j - 1, by omega⟩ : ℕ) := by
    rw [show (⟨(j - 1) - (sPrefix k s j (by omega) (by omega)).length, b'⟩ :
            Fin (D.depB i + 1)) = ⟨0, by omega⟩ from (by
        apply Fin.ext
        simp
        omega)]
    have hhead := congrArg (fun t : ℕ+ => (t : ℕ)) (consVec_zero (s ⟨j - 1, by omega⟩) (D.cB i))
    simpa using hhead
  calc
    ((Q.c (Sum.inr (Sum.inl i))) ⟨j - 1, hm⟩ : ℕ)
        = ((Bs.c (Sum.inr (Sum.inl i))) ⟨(j - 1) - (sPrefix k s j (by omega) (by omega)).length, b'⟩ : ℕ) := h1
    _ = ((consVec (s ⟨j - 1, by omega⟩) (D.cB i))
          ⟨(j - 1) - (sPrefix k s j (by omega) (by omega)).length, b'⟩ : ℕ) := h2
    _ = (s ⟨j - 1, by omega⟩ : ℕ) := h3

/-- Depth of the type-2 members is at least `j`. -/
lemma Q_dep_inr_inl_R1 (k : ℕ) (s : Fin k → ℕ+) (j : ℕ)
    (hk1 : 1 ≤ k) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F) :
    let D := RelData.BCqIter F (k - j - 1) (toData F (r1Rel F))
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) (r1Rel F) e)
        (RelData.iterate_merge_hv F (k - j - 1) (r1Rel F) (s ⟨j - 1, by omega⟩) (by omega) (r1Rel_hbhd F))
    let Q := FixedOver.prependList F Bs (sPrefix k s j (by omega) (by omega))
    ∀ i : D.ιB, j ≤ Q.dep (Sum.inr (Sum.inl i)) := by
  classical
  intro D Bs Q i
  have hlen : (sPrefix k s j (by omega) (by omega)).length = j - 1 :=
    sPrefix_length k s j (by omega) (by omega)
  have h1 : Q.dep (Sum.inr (Sum.inl i)) = Bs.dep (Sum.inr (Sum.inl i)) + (j - 1) := by
    have hd := FixedOver.prependList_dep F Bs (sPrefix k s j (by omega) (by omega)) (Sum.inr (Sum.inl i))
    rw [hlen] at hd
    exact hd
  have h2 : Bs.dep (Sum.inr (Sum.inl i)) = D.depB i + 1 := by
    dsimp [Bs, ofBstarOver]
  rw [h1, h2]
  omega


/-- The type-2 members `inr (inl i)` have value `1` at full-tuple position `j`. -/
lemma type2_one_at_j_R1 (k : ℕ) (s : Fin k → ℕ+) (j : ℕ)
    (hk1 : 1 ≤ k) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F) :
    let D := RelData.BCqIter F (k - j - 1) (toData F (r1Rel F))
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) (r1Rel F) e)
        (RelData.iterate_merge_hv F (k - j - 1) (r1Rel F) (s ⟨j - 1, by omega⟩) (by omega) (r1Rel_hbhd F))
    let Q := FixedOver.prependList F Bs (sPrefix k s j (by omega) (by omega))
    ∀ i : D.ιB, ∀ (hmj : j < Q.dep (Sum.inr (Sum.inl i))),
      ((Q.c (Sum.inr (Sum.inl i))) ⟨j, hmj⟩ : ℕ) = 1 := by
  classical
  intro D Bs Q i hmj
  have hlen : (sPrefix k s j (by omega) (by omega)).length = j - 1 :=
    sPrefix_length k s j (by omega) (by omega)
  have hge : (sPrefix k s j (by omega) (by omega)).length ≤ j := by omega
  have hQdep : Q.dep (Sum.inr (Sum.inl i)) =
      Bs.dep (Sum.inr (Sum.inl i)) + (sPrefix k s j (by omega) (by omega)).length := by
    exact FixedOver.prependList_dep F Bs (sPrefix k s j (by omega) (by omega)) (Sum.inr (Sum.inl i))
  have b' : j - (sPrefix k s j (by omega) (by omega)).length < Bs.dep (Sum.inr (Sum.inl i)) := by
    have hm1 : j < Bs.dep (Sum.inr (Sum.inl i)) + (sPrefix k s j (by omega) (by omega)).length := by
      rw [← hQdep]
      exact hmj
    omega
  have h1 : ((Q.c (Sum.inr (Sum.inl i))) ⟨j, hmj⟩ : ℕ) =
      ((Bs.c (Sum.inr (Sum.inl i))) ⟨j - (sPrefix k s j (by omega) (by omega)).length, b'⟩ : ℕ) := by
    have hv := prependList_c_base_value F Bs (sPrefix k s j (by omega) (by omega))
      (Sum.inr (Sum.inl i)) j hmj hge
    apply congrArg (fun v : ℕ+ => (v : ℕ))
    calc
      (Q.c (Sum.inr (Sum.inl i))) ⟨j, hmj⟩
          = (Bs.c (Sum.inr (Sum.inl i))) ⟨j - (sPrefix k s j (by omega) (by omega)).length,
              (by
                have hd := FixedOver.prependList_dep F Bs (sPrefix k s j (by omega) (by omega)) (Sum.inr (Sum.inl i))
                rw [hd] at hmj
                omega)⟩ := hv
      _ = (Bs.c (Sum.inr (Sum.inl i))) ⟨j - (sPrefix k s j (by omega) (by omega)).length, b'⟩ := by
            congr 1
  have hcBs : Bs.c (Sum.inr (Sum.inl i)) = consVec (s ⟨j - 1, by omega⟩) (D.cB i) := by
    dsimp [Bs, ofBstarOver, D]
  have h2 : ((Bs.c (Sum.inr (Sum.inl i))) ⟨j - (sPrefix k s j (by omega) (by omega)).length, b'⟩ : ℕ) =
      ((consVec (s ⟨j - 1, by omega⟩) (D.cB i)) ⟨j - (sPrefix k s j (by omega) (by omega)).length, b'⟩ : ℕ) := by
    apply congrArg (fun v : ℕ+ => (v : ℕ))
    exact congrFun hcBs ⟨j - (sPrefix k s j (by omega) (by omega)).length, b'⟩
  have h3 : ((consVec (s ⟨j - 1, by omega⟩) (D.cB i))
        ⟨j - (sPrefix k s j (by omega) (by omega)).length, b'⟩ : ℕ) =
      ((D.cB i) ⟨0, D.hdepB i⟩ : ℕ) := by
    have hcv := consVec_nat_value (s ⟨j - 1, by omega⟩) (D.cB i)
      (j - (sPrefix k s j (by omega) (by omega)).length) b'
    have hpos : 0 < D.depB i := D.hdepB i
    have hjj : j - (sPrefix k s j (by omega) (by omega)).length = 1 := by
      have hlen' : (sPrefix k s j (by omega) (by omega)).length = j - 1 :=
        sPrefix_length k s j (by omega) (by omega)
      omega
    have hnz : j - (sPrefix k s j (by omega) (by omega)).length ≠ 0 := by omega
    calc
      ((consVec (s ⟨j - 1, by omega⟩) (D.cB i))
            ⟨j - (sPrefix k s j (by omega) (by omega)).length, b'⟩ : ℕ)
          = ((D.cB i) ⟨(j - (sPrefix k s j (by omega) (by omega)).length) - 1,
              (by omega : (j - (sPrefix k s j (by omega) (by omega)).length) - 1 < D.depB i)⟩ : ℕ) := by
            apply congrArg (fun v : ℕ+ => (v : ℕ))
            rw [hcv]
            simp [hnz]
      _ = ((D.cB i) ⟨0, D.hdepB i⟩ : ℕ) := by
            rw [show (⟨(j - (sPrefix k s j (by omega) (by omega)).length) - 1,
                (by omega : (j - (sPrefix k s j (by omega) (by omega)).length) - 1 < D.depB i)⟩ :
                    Fin (D.depB i)) = ⟨0, D.hdepB i⟩ from (by
              apply Fin.ext
              simp
              omega)]
  have h4 : ((D.cB i) ⟨0, D.hdepB i⟩ : ℕ) = 1 := by
    have hh := RelData.BCqIter_head_one F (k - j - 1) (r1Rel F) (r1Rel_hbhd F) i
    have hh' := congrArg (fun t : ℕ+ => (t : ℕ)) hh
    simpa [oneExp, D] using hh'
  calc
    ((Q.c (Sum.inr (Sum.inl i))) ⟨j, hmj⟩ : ℕ)
        = ((Bs.c (Sum.inr (Sum.inl i))) ⟨j - (sPrefix k s j (by omega) (by omega)).length, b'⟩ : ℕ) := h1
    _ = ((consVec (s ⟨j - 1, by omega⟩) (D.cB i)) ⟨j - (sPrefix k s j (by omega) (by omega)).length, b'⟩ : ℕ) := h2
    _ = ((D.cB i) ⟨0, D.hdepB i⟩ : ℕ) := h3
    _ = 1 := h4


/-- Type-2 members have `j`-prefix sum equal to that of `s`. -/
lemma type2_psum_j_R1 (k : ℕ) (s : Fin k → ℕ+) (j : ℕ)
    (hk1 : 1 ≤ k) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F) :
    let D := RelData.BCqIter F (k - j - 1) (toData F (r1Rel F))
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) (r1Rel F) e)
        (RelData.iterate_merge_hv F (k - j - 1) (r1Rel F) (s ⟨j - 1, by omega⟩) (by omega) (r1Rel_hbhd F))
    let Q := FixedOver.prependList F Bs (sPrefix k s j (by omega) (by omega))
    ∀ i : D.ιB, psum (Q.c (Sum.inr (Sum.inl i))) j = psum s j := by
  classical
  intro D Bs Q i
  have hdep : j ≤ Q.dep (Sum.inr (Sum.inl i)) := Q_dep_inr_inl_R1 F k s j hk1 hj1 hjk hsj i
  have hjlr : j - 1 < k := by omega
  apply psum_eq_of_pad0_eq
  intro x hx
  have hxj : x < j := hx
  by_cases hxe : x = j - 1
  · subst x
    have hmQ : j - 1 < Q.dep (Sum.inr (Sum.inl i)) := by omega
    have hv := type2_sj_at_jm1_R1 F k s j hk1 hj1 hjk hsj i hmQ
    have hp1 : pad0 (Q.c (Sum.inr (Sum.inl i))) (j - 1) =
        ((Q.c (Sum.inr (Sum.inl i))) ⟨j - 1, hmQ⟩ : ℕ) :=
      pad0_of_lt (Q.c (Sum.inr (Sum.inl i))) hmQ
    have hp2 : pad0 s (j - 1) = (s ⟨j - 1, hjlr⟩ : ℕ) := pad0_of_lt s hjlr
    rw [hp1, hp2]
    exact hv
  · have hx1 : x < j - 1 := by omega
    have hmQ : x < Q.dep (Sum.inr (Sum.inl i)) := by omega
    have hv := member_prefix_pos_R1 F k s j hk1 hj1 hjk hsj (Sum.inr (Sum.inl i)) x hx1 hmQ
    have hxr : x < k := by
      have : x < j - 1 := hx1
      omega
    have hp1 : pad0 (Q.c (Sum.inr (Sum.inl i))) x = ((Q.c (Sum.inr (Sum.inl i))) ⟨x, hmQ⟩ : ℕ) :=
      pad0_of_lt (Q.c (Sum.inr (Sum.inl i))) hmQ
    have hp2 : pad0 s x = (s ⟨x, hxr⟩ : ℕ) := pad0_of_lt s hxr
    rw [hp1, hp2]
    exact congrArg (fun t : ℕ+ => (t : ℕ)) hv


/-- Padded values of a type-2 member beyond the `1` at position `j`: at full
position `j+1+t` the value is the `t`-th padded entry of the b-fiber tail
`expTail (D.cB i)`. -/
lemma type2_tail_pad0_R1 (k : ℕ) (s : Fin k → ℕ+) (j : ℕ)
    (hk1 : 1 ≤ k) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F) :
    let D := RelData.BCqIter F (k - j - 1) (toData F (r1Rel F))
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) (r1Rel F) e)
        (RelData.iterate_merge_hv F (k - j - 1) (r1Rel F) (s ⟨j - 1, by omega⟩) (by omega) (r1Rel_hbhd F))
    let Q := FixedOver.prependList F Bs (sPrefix k s j (by omega) (by omega))
    ∀ i : D.ιB, ∀ (t : ℕ),
      pad0 (Q.c (Sum.inr (Sum.inl i))) (j + 1 + t) = pad0 (expTail (D.cB i)) t := by
  classical
  intro D Bs Q i t
  have hlen : (sPrefix k s j (by omega) (by omega)).length = j - 1 :=
    sPrefix_length k s j (by omega) (by omega)
  have hQdep : Q.dep (Sum.inr (Sum.inl i)) =
      Bs.dep (Sum.inr (Sum.inl i)) + (sPrefix k s j (by omega) (by omega)).length := by
    exact FixedOver.prependList_dep F Bs (sPrefix k s j (by omega) (by omega)) (Sum.inr (Sum.inl i))
  have hBsdep : Bs.dep (Sum.inr (Sum.inl i)) = D.depB i + 1 := by
    dsimp [Bs, ofBstarOver]
  by_cases hm : j + 1 + t < Q.dep (Sum.inr (Sum.inl i))
  · have hge : (sPrefix k s j (by omega) (by omega)).length ≤ j + 1 + t := by omega
    have ht1b : t + 1 < D.depB i := by
      have hm0 : j + 1 + t < Q.dep (Sum.inr (Sum.inl i)) := hm
      rw [hQdep, hBsdep, hlen] at hm0
      omega
    have b' : (j + 1 + t) - (sPrefix k s j (by omega) (by omega)).length < Bs.dep (Sum.inr (Sum.inl i)) := by
      rw [hBsdep]
      have hm0 : j + 1 + t < Q.dep (Sum.inr (Sum.inl i)) := hm
      rw [hQdep, hBsdep, hlen] at hm0
      omega
    have hval : ((Q.c (Sum.inr (Sum.inl i))) ⟨j + 1 + t, hm⟩ : ℕ) =
        ((D.cB i) ⟨t + 1, ht1b⟩ : ℕ) := by
      have h1 : ((Q.c (Sum.inr (Sum.inl i))) ⟨j + 1 + t, hm⟩ : ℕ) =
          ((Bs.c (Sum.inr (Sum.inl i))) ⟨(j + 1 + t) - (sPrefix k s j (by omega) (by omega)).length, b'⟩ : ℕ) := by
        have hv := prependList_c_base_value F Bs (sPrefix k s j (by omega) (by omega))
          (Sum.inr (Sum.inl i)) (j + 1 + t) hm hge
        apply congrArg (fun v : ℕ+ => (v : ℕ))
        calc
          (Q.c (Sum.inr (Sum.inl i))) ⟨j + 1 + t, hm⟩
              = (Bs.c (Sum.inr (Sum.inl i))) ⟨(j + 1 + t) - (sPrefix k s j (by omega) (by omega)).length,
                  (by
                    have hd := FixedOver.prependList_dep F Bs (sPrefix k s j (by omega) (by omega)) (Sum.inr (Sum.inl i))
                    rw [hd] at hm
                    omega)⟩ := hv
          _ = (Bs.c (Sum.inr (Sum.inl i))) ⟨(j + 1 + t) - (sPrefix k s j (by omega) (by omega)).length, b'⟩ := by
                congr 1
      have hcBs : Bs.c (Sum.inr (Sum.inl i)) = consVec (s ⟨j - 1, by omega⟩) (D.cB i) := by
        dsimp [Bs, ofBstarOver, D]
      have h2 : ((Bs.c (Sum.inr (Sum.inl i))) ⟨(j + 1 + t) - (sPrefix k s j (by omega) (by omega)).length, b'⟩ : ℕ) =
          ((consVec (s ⟨j - 1, by omega⟩) (D.cB i)) ⟨(j + 1 + t) - (sPrefix k s j (by omega) (by omega)).length, b'⟩ : ℕ) := by
        apply congrArg (fun v : ℕ+ => (v : ℕ))
        exact congrFun hcBs ⟨(j + 1 + t) - (sPrefix k s j (by omega) (by omega)).length, b'⟩
      have hbp0 : (j + 1 + t) - (sPrefix k s j (by omega) (by omega)).length = t + 2 := by
        rw [hlen]
        omega
      have h3 : ((consVec (s ⟨j - 1, by omega⟩) (D.cB i))
            ⟨(j + 1 + t) - (sPrefix k s j (by omega) (by omega)).length, b'⟩ : ℕ) =
          ((D.cB i) ⟨t + 1, ht1b⟩ : ℕ) := by
        have hcv := consVec_nat_value (s ⟨j - 1, by omega⟩) (D.cB i)
          ((j + 1 + t) - (sPrefix k s j (by omega) (by omega)).length) b'
        have hnz : (j + 1 + t) - (sPrefix k s j (by omega) (by omega)).length ≠ 0 := by omega
        calc
          ((consVec (s ⟨j - 1, by omega⟩) (D.cB i))
                ⟨(j + 1 + t) - (sPrefix k s j (by omega) (by omega)).length, b'⟩ : ℕ)
              = ((D.cB i) ⟨((j + 1 + t) - (sPrefix k s j (by omega) (by omega)).length) - 1,
                  (by omega : ((j + 1 + t) - (sPrefix k s j (by omega) (by omega)).length) - 1 < D.depB i)⟩ : ℕ) := by
                apply congrArg (fun v : ℕ+ => (v : ℕ))
                rw [hcv]
                simp [hnz]
          _ = ((D.cB i) ⟨t + 1, ht1b⟩ : ℕ) := by
                rw [show (⟨((j + 1 + t) - (sPrefix k s j (by omega) (by omega)).length) - 1,
                    (by omega : ((j + 1 + t) - (sPrefix k s j (by omega) (by omega)).length) - 1 < D.depB i)⟩ :
                        Fin (D.depB i)) = ⟨t + 1, ht1b⟩ from (by
                  apply Fin.ext
                  simp
                  omega)]
      calc
        ((Q.c (Sum.inr (Sum.inl i))) ⟨j + 1 + t, hm⟩ : ℕ)
            = ((Bs.c (Sum.inr (Sum.inl i))) ⟨(j + 1 + t) - (sPrefix k s j (by omega) (by omega)).length, b'⟩ : ℕ) := h1
        _ = ((consVec (s ⟨j - 1, by omega⟩) (D.cB i)) ⟨(j + 1 + t) - (sPrefix k s j (by omega) (by omega)).length, b'⟩ : ℕ) := h2
        _ = ((D.cB i) ⟨t + 1, ht1b⟩ : ℕ) := h3
    rw [pad0_of_lt (Q.c (Sum.inr (Sum.inl i))) hm]
    have hdep : t < (D.depB i) - 1 := by omega
    rw [pad0_of_lt (expTail (D.cB i)) hdep]
    exact hval
  · have hgeQ : Q.dep (Sum.inr (Sum.inl i)) ≤ j + 1 + t := le_of_not_gt hm
    have hp1 : pad0 (Q.c (Sum.inr (Sum.inl i))) (j + 1 + t) = 0 := pad0_of_ge (Q.c (Sum.inr (Sum.inl i))) hgeQ
    rw [hp1]
    have hdep : (D.depB i) - 1 ≤ t := by
      have hge0 : Q.dep (Sum.inr (Sum.inl i)) ≤ j + 1 + t := hgeQ
      rw [hQdep, hBsdep, hlen] at hge0
      omega
    have hp2 : pad0 (expTail (D.cB i)) t = 0 := pad0_of_ge (expTail (D.cB i)) hdep
    rw [hp2]


/-- Type-2 prefix sum after the `(s_1..s_j, 1)` front: the `(j+1+m)`-prefix is
`psum s j + 1 + (m-prefix of the b-fiber tail)`. -/
lemma type2_psum_after_R1 (k : ℕ) (s : Fin k → ℕ+) (j : ℕ)
    (hk1 : 1 ≤ k) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F) :
    let D := RelData.BCqIter F (k - j - 1) (toData F (r1Rel F))
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) (r1Rel F) e)
        (RelData.iterate_merge_hv F (k - j - 1) (r1Rel F) (s ⟨j - 1, by omega⟩) (by omega) (r1Rel_hbhd F))
    let Q := FixedOver.prependList F Bs (sPrefix k s j (by omega) (by omega))
    ∀ i : D.ιB, ∀ (m : ℕ),
      psum (Q.c (Sum.inr (Sum.inl i))) (j + 1 + m) =
        psum s j + 1 + psum (expTail (D.cB i)) m := by
  classical
  intro D Bs Q i m
  induction m with
  | zero =>
      have hpj : psum (Q.c (Sum.inr (Sum.inl i))) j = psum s j :=
        type2_psum_j_R1 F k s j hk1 hj1 hjk hsj i
      have hsu := psum_succ (Q.c (Sum.inr (Sum.inl i))) j
      have h1 : psum (Q.c (Sum.inr (Sum.inl i))) (j + 1) =
          psum s j + pad0 (Q.c (Sum.inr (Sum.inl i))) j := by
        rw [hsu, hpj]
      have hdep : j < Q.dep (Sum.inr (Sum.inl i)) := by
        have hb2 : 1 < D.depB i := D.hB2 i
        have hQd : Q.dep (Sum.inr (Sum.inl i)) = (D.depB i + 1) + (j - 1) := by
          have hlen : (sPrefix k s j (by omega) (by omega)).length = j - 1 :=
            sPrefix_length k s j (by omega) (by omega)
          have hQdep : Q.dep (Sum.inr (Sum.inl i)) =
              Bs.dep (Sum.inr (Sum.inl i)) + (sPrefix k s j (by omega) (by omega)).length :=
            FixedOver.prependList_dep F Bs (sPrefix k s j (by omega) (by omega)) (Sum.inr (Sum.inl i))
          have hBsdep : Bs.dep (Sum.inr (Sum.inl i)) = D.depB i + 1 := by
            dsimp [Bs, ofBstarOver]
          rw [hQdep, hBsdep, hlen]
        rw [hQd]
        omega
      have hp1 : (pad0 (Q.c (Sum.inr (Sum.inl i))) j : ℕ) = 1 := by
        have hv := type2_one_at_j_R1 F k s j hk1 hj1 hjk hsj i hdep
        rw [pad0_of_lt (Q.c (Sum.inr (Sum.inl i))) hdep]
        exact hv
      calc
        psum (Q.c (Sum.inr (Sum.inl i))) (j + 1)
            = psum s j + pad0 (Q.c (Sum.inr (Sum.inl i))) j := h1
        _ = psum s j + 1 := by rw [hp1]
        _ = psum s j + 1 + 0 := by omega
        _ = psum s j + 1 + psum (expTail (D.cB i)) 0 := by simp [psum_zero]
  | succ m ih =>
      have hsu := psum_succ (Q.c (Sum.inr (Sum.inl i))) (j + 1 + m)
      have ht := type2_tail_pad0_R1 F k s j hk1 hj1 hjk hsj i m
      have hsut := psum_succ (expTail (D.cB i)) m
      calc
        psum (Q.c (Sum.inr (Sum.inl i))) (j + 1 + (m + 1))
            = psum (Q.c (Sum.inr (Sum.inl i))) (j + 1 + m) + pad0 (Q.c (Sum.inr (Sum.inl i))) (j + 1 + m) := by
              have hjj : (j + 1 + m) + 1 = j + 1 + (m + 1) := by omega
              rw [← hjj]
              exact hsu
        _ = (psum s j + 1 + psum (expTail (D.cB i)) m) + pad0 (Q.c (Sum.inr (Sum.inl i))) (j + 1 + m) := by
              rw [ih]
        _ = psum s j + 1 + (psum (expTail (D.cB i)) m + pad0 (expTail (D.cB i)) m) := by
              rw [ht]
              dsimp [D]
              omega
        _ = psum s j + 1 + psum (expTail (D.cB i)) (m + 1) := by
              rw [← hsut]


/-- ★ Type-2 prefix sum at `k` is strictly smaller than that of `s`: the paper's
`t'₁+…+t'ₖ < s₁+…+sₖ` at the CASE-2 config (block positions `j..k−1` of `s` all `q`,
so `psum s k = psum s j + (k−j)·q` and the member's `k`-prefix is at most
`psum s j + 1 + (k−j−1)·q`, strict because `q ≥ 2`). -/
lemma type2_psum_lt_k_R1 (k : ℕ) (s : Fin k → ℕ+) (j : ℕ)
    (hk1 : 1 ≤ k) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hqend : ∀ i : Fin k, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < k → (s i : ℕ) = Nat.card F) :
    let D := RelData.BCqIter F (k - j - 1) (toData F (r1Rel F))
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) (r1Rel F) e)
        (RelData.iterate_merge_hv F (k - j - 1) (r1Rel F) (s ⟨j - 1, by omega⟩) (by omega) (r1Rel_hbhd F))
    let Q := FixedOver.prependList F Bs (sPrefix k s j (by omega) (by omega))
    ∀ i : D.ιB, psum (Q.c (Sum.inr (Sum.inl i))) k < psum s k := by
  classical
  intro D Bs Q i
  have hkdec : j + 1 + (k - j - 1) = k := by omega
  have hdec := type2_psum_after_R1 F k s j hk1 hj1 hjk hsj i (k - j - 1)
  have hqN := BCq_fiber_prefix_qN F (k - j - 1) (r1Rel F) (r1Rel_hbhd F) i
  have hc1 : psum (Q.c (Sum.inr (Sum.inl i))) k =
      psum (Q.c (Sum.inr (Sum.inl i))) (j + 1 + (k - j - 1)) := by
    exact congrArg (psum (Q.c (Sum.inr (Sum.inl i)))) (by omega : k = j + 1 + (k - j - 1))
  have hle1 : psum (Q.c (Sum.inr (Sum.inl i))) k ≤ psum s j + 1 + (k - j - 1) * Nat.card F := by
    rw [hc1]
    rw [hdec]
    have hqN' : psum (expTail (D.cB i)) (k - j - 1) ≤ (k - j - 1) * Nat.card F := hqN
    exact add_le_add_right hqN' (psum s j + 1)
  -- psum s k = psum s j + (k−j)·q: block positions j..k−1 all q
  have hp1 : psum s k = psum s j + (k - j) * Nat.card F := by
    apply psum_const_block (s := s) (j := j) (m := k) (q := Nat.card F)
    · omega
    · intro x hx1 hx2
      have hxr : x < k := hx2
      have hval : (s ⟨x, hxr⟩ : ℕ) = Nat.card F := hqend ⟨x, hxr⟩ hx1 hx2
      rw [pad0_of_lt s hxr]
      exact hval
  have hq2 : 2 ≤ Nat.card F := card_ge_two F
  have hn' : (k - j) * Nat.card F = (k - j - 1) * Nat.card F + Nat.card F := by
    have hk' : k - j = (k - j - 1) + 1 := by omega
    calc
      (k - j) * Nat.card F = ((k - j - 1) + 1) * Nat.card F := congrArg (fun m : ℕ => m * Nat.card F) hk'
      _ = (k - j - 1) * Nat.card F + 1 * Nat.card F := by rw [Nat.add_mul]
      _ = (k - j - 1) * Nat.card F + Nat.card F := by rw [one_mul]
  have hA : 1 + (k - j - 1) * Nat.card F < (k - j) * Nat.card F := by
    rw [hn']
    omega
  have hlt : psum s j + 1 + (k - j - 1) * Nat.card F < psum s j + (k - j) * Nat.card F := by omega
  calc
    psum (Q.c (Sum.inr (Sum.inl i))) k ≤ psum s j + 1 + (k - j - 1) * Nat.card F := hle1
    _ < psum s j + (k - j) * Nat.card F := hlt
    _ = psum s k := hp1.symm


/-- Type-2 member padded values at full positions `j + t` equal the `t`-th padded
entry of the level-`(k−j−1)` b-tuple (its head `1`, then the fiber tail). -/
lemma type2_pad0_shift_R1 (k : ℕ) (s : Fin k → ℕ+) (j : ℕ)
    (hk1 : 1 ≤ k) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F) :
    let D := RelData.BCqIter F (k - j - 1) (toData F (r1Rel F))
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) (r1Rel F) e)
        (RelData.iterate_merge_hv F (k - j - 1) (r1Rel F) (s ⟨j - 1, by omega⟩) (by omega) (r1Rel_hbhd F))
    let Q := FixedOver.prependList F Bs (sPrefix k s j (by omega) (by omega))
    ∀ i : D.ιB, ∀ (t : ℕ),
      pad0 (Q.c (Sum.inr (Sum.inl i))) (j + t) = pad0 (D.cB i) t := by
  classical
  intro D Bs Q i t
  have hQdep : Q.dep (Sum.inr (Sum.inl i)) = j + D.depB i := by
    have hlen : (sPrefix k s j (by omega) (by omega)).length = j - 1 :=
      sPrefix_length k s j (by omega) (by omega)
    have h1 := FixedOver.prependList_dep F Bs (sPrefix k s j (by omega) (by omega)) (Sum.inr (Sum.inl i))
    have h2 : Bs.dep (Sum.inr (Sum.inl i)) = D.depB i + 1 := by
      dsimp [Bs, ofBstarOver]
    rw [h1, h2, hlen]
    omega
  by_cases ht : t < D.depB i
  · cases t with
    | zero =>
        -- position j: value 1 = head of D.cB (padded, both in range)
        have hmj : j < Q.dep (Sum.inr (Sum.inl i)) := by
          rw [hQdep]
          omega
        have hh := BCqIter_head_one_data F (k - j - 1) (r1Rel F) (r1Rel_hbhd F) i
        have hh' : ((D.cB i) ⟨0, ht⟩ : ℕ) = 1 := by
          have hfin : (⟨0, ht⟩ : Fin (D.depB i)) = ⟨0, D.hdepB i⟩ := by
            apply Fin.ext
            rfl
          rw [hfin]
          exact hh
        rw [show j + 0 = j by omega]
        rw [pad0_of_lt (Q.c (Sum.inr (Sum.inl i))) hmj]
        rw [pad0_of_lt (D.cB i) ht]
        have hv := type2_one_at_j_R1 F k s j hk1 hj1 hjk hsj i hmj
        rw [hv, hh']
    | succ t' =>
        have hsh := type2_tail_pad0_R1 F k s j hk1 hj1 hjk hsj i t'
        -- hsh : pad0 (Q.c) (j+1+t') = pad0 (expTail (D.cB i)) t'
        have hpe := pad0_succ_expTail (D.cB i) t'
        have hdom : j + (t' + 1) = j + 1 + t' := by omega
        rw [hdom]
        rw [hsh]
        rw [hpe.symm]
  · have htge : D.depB i ≤ t := le_of_not_gt ht
    have hgeQ : Q.dep (Sum.inr (Sum.inl i)) ≤ j + t := by
      rw [hQdep]
      omega
    rw [pad0_of_ge (Q.c (Sum.inr (Sum.inl i))) hgeQ]
    rw [pad0_of_ge (D.cB i) htge]

/-- Weight of a type-2 member: the `s₁..s_j` front plus the level-`(k−j−1)` b-tuple. -/
lemma type2_weight_decompose_R1 (k : ℕ) (s : Fin k → ℕ+) (j : ℕ)
    (hk1 : 1 ≤ k) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F) :
    let D := RelData.BCqIter F (k - j - 1) (toData F (r1Rel F))
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) (r1Rel F) e)
        (RelData.iterate_merge_hv F (k - j - 1) (r1Rel F) (s ⟨j - 1, by omega⟩) (by omega) (r1Rel_hbhd F))
    let Q := FixedOver.prependList F Bs (sPrefix k s j (by omega) (by omega))
    ∀ i : D.ιB,
      weight (Q.dep (Sum.inr (Sum.inl i))) (Q.c (Sum.inr (Sum.inl i))) =
        psum s j + weight (D.depB i) (D.cB i) := by
  classical
  intro D Bs Q i
  have hQdep : Q.dep (Sum.inr (Sum.inl i)) = j + D.depB i := by
    have hlen : (sPrefix k s j (by omega) (by omega)).length = j - 1 :=
      sPrefix_length k s j (by omega) (by omega)
    have h1 := FixedOver.prependList_dep F Bs (sPrefix k s j (by omega) (by omega)) (Sum.inr (Sum.inl i))
    have h2 : Bs.dep (Sum.inr (Sum.inl i)) = D.depB i + 1 := by
      dsimp [Bs, ofBstarOver]
    rw [h1, h2, hlen]
    omega
  have hwpsum : weight (Q.dep (Sum.inr (Sum.inl i))) (Q.c (Sum.inr (Sum.inl i))) =
      psum (Q.c (Sum.inr (Sum.inl i))) (Q.dep (Sum.inr (Sum.inl i))) := by
    have hp := psum_ge_depth (Q.c (Sum.inr (Sum.inl i))) (m := Q.dep (Sum.inr (Sum.inl i))) (le_refl _)
    exact hp.symm
  have hsplit : psum (Q.c (Sum.inr (Sum.inl i))) (j + D.depB i) =
      psum (Q.c (Sum.inr (Sum.inl i))) j +
        (∑ t ∈ Finset.range (D.depB i), pad0 (Q.c (Sum.inr (Sum.inl i))) (j + t)) := by
    change (∑ x ∈ Finset.range (j + D.depB i), pad0 (Q.c (Sum.inr (Sum.inl i))) x) =
      (∑ x ∈ Finset.range j, pad0 (Q.c (Sum.inr (Sum.inl i))) x) +
        (∑ t ∈ Finset.range (D.depB i), pad0 (Q.c (Sum.inr (Sum.inl i))) (j + t))
    rw [Finset.sum_range_add]
  have htail : (∑ t ∈ Finset.range (D.depB i), pad0 (Q.c (Sum.inr (Sum.inl i))) (j + t)) =
      weight (D.depB i) (D.cB i) := by
    calc
      (∑ t ∈ Finset.range (D.depB i), pad0 (Q.c (Sum.inr (Sum.inl i))) (j + t))
          = (∑ t ∈ Finset.range (D.depB i), pad0 (D.cB i) t) := by
            apply Finset.sum_congr rfl
            intro t ht
            exact type2_pad0_shift_R1 F k s j hk1 hj1 hjk hsj i t
      _ = psum (D.cB i) (D.depB i) := by rfl
      _ = weight (D.depB i) (D.cB i) := by
            have hp' := psum_ge_depth (D.cB i) (m := D.depB i) (le_refl _)
            exact hp'
  have hpj : psum (Q.c (Sum.inr (Sum.inl i))) j = psum s j :=
    type2_psum_j_R1 F k s j hk1 hj1 hjk hsj i
  calc
    weight (Q.dep (Sum.inr (Sum.inl i))) (Q.c (Sum.inr (Sum.inl i)))
        = psum (Q.c (Sum.inr (Sum.inl i))) (Q.dep (Sum.inr (Sum.inl i))) := hwpsum
    _ = psum (Q.c (Sum.inr (Sum.inl i))) (j + D.depB i) := by
          exact congrArg (psum (Q.c (Sum.inr (Sum.inl i)))) hQdep
    _ = psum (Q.c (Sum.inr (Sum.inl i))) j +
          (∑ t ∈ Finset.range (D.depB i), pad0 (Q.c (Sum.inr (Sum.inl i))) (j + t)) := hsplit
    _ = psum s j + weight (D.depB i) (D.cB i) := by
          rw [hpj, htail]


/-- ★ Type-2 weight preservation: a type-2 member has weight `w(s)` — the level-0
`b`-tail of `r1Rel` has weight `q−1` (`r1Rel_tail_weight`), so the member weight is
`psum s j + 1 + (k−j−1)·q + (q−1) = psum s j + (k−j)·q = psum s k = weight k s`. -/
lemma type2_weight_eq_R1 (k : ℕ) (s : Fin k → ℕ+) (j : ℕ)
    (hk1 : 1 ≤ k) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hqend : ∀ i : Fin k, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < k → (s i : ℕ) = Nat.card F) :
    let D := RelData.BCqIter F (k - j - 1) (toData F (r1Rel F))
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) (r1Rel F) e)
        (RelData.iterate_merge_hv F (k - j - 1) (r1Rel F) (s ⟨j - 1, by omega⟩) (by omega) (r1Rel_hbhd F))
    let Q := FixedOver.prependList F Bs (sPrefix k s j (by omega) (by omega))
    ∀ i : D.ιB,
      weight (Q.dep (Sum.inr (Sum.inl i))) (Q.c (Sum.inr (Sum.inl i))) = weight k s := by
  classical
  intro D Bs Q i
  have hdec := type2_weight_decompose_R1 F k s j hk1 hj1 hjk hsj i
  have hwt := weight_head_tail (D.hdepB i) (D.cB i)
  have hh := BCqIter_head_one_data F (k - j - 1) (r1Rel F) (r1Rel_hbhd F) i
  have hfib := BCq_fiber_weight_X F (k - j - 1) (r1Rel F) (r1Rel_hbhd F) (qMinusExp F : ℕ)
    (r1Rel_tail_weight F) i
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
    weight (Q.dep (Sum.inr (Sum.inl i))) (Q.c (Sum.inr (Sum.inl i)))
        = psum s j + weight (D.depB i) (D.cB i) := hdec
    _ = psum s j + (1 + weight (D.depB i - 1) (expTail (D.cB i))) := by
          rw [hwt]
          rw [hh]
    _ = psum s j + (1 + ((k - j - 1) * Nat.card F + (qMinusExp F : ℕ))) := by
          rw [hfib]
    _ = psum s j + (1 + ((k - j - 1) * Nat.card F + (Nat.card F - 1))) := by
          have hqminus : (qMinusExp F : ℕ) = Nat.card F - 1 := by rfl
          rw [hqminus]
    _ = psum s j + ((k - j - 1) * Nat.card F + Nat.card F) := by omega
    _ = psum s j + (k - j) * Nat.card F := by
          have hn' : (k - j) * Nat.card F = (k - j - 1) * Nat.card F + Nat.card F := by
            have hk' : k - j = (k - j - 1) + 1 := by omega
            calc
              (k - j) * Nat.card F = ((k - j - 1) + 1) * Nat.card F := congrArg (fun m : ℕ => m * Nat.card F) hk'
              _ = (k - j - 1) * Nat.card F + 1 * Nat.card F := by rw [Nat.add_mul]
              _ = (k - j - 1) * Nat.card F + Nat.card F := by rw [one_mul]
          rw [hn']
    _ = psum s k := hp1.symm
    _ = weight k s := by exact psum_ge_depth s (le_refl k)


/-- Depth of the type-3 members is at least `j`. -/
lemma Q_dep_inr_inr_R1 (k : ℕ) (s : Fin k → ℕ+) (j : ℕ)
    (hk1 : 1 ≤ k) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F) :
    let D := RelData.BCqIter F (k - j - 1) (toData F (r1Rel F))
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) (r1Rel F) e)
        (RelData.iterate_merge_hv F (k - j - 1) (r1Rel F) (s ⟨j - 1, by omega⟩) (by omega) (r1Rel_hbhd F))
    let Q := FixedOver.prependList F Bs (sPrefix k s j (by omega) (by omega))
    ∀ i : D.ιB, j ≤ Q.dep (Sum.inr (Sum.inr i)) := by
  classical
  intro D Bs Q i
  have hlen : (sPrefix k s j (by omega) (by omega)).length = j - 1 :=
    sPrefix_length k s j (by omega) (by omega)
  have h1 : Q.dep (Sum.inr (Sum.inr i)) = Bs.dep (Sum.inr (Sum.inr i)) + (j - 1) := by
    have hd := FixedOver.prependList_dep F Bs (sPrefix k s j (by omega) (by omega)) (Sum.inr (Sum.inr i))
    rw [hlen] at hd
    exact hd
  have h2 : Bs.dep (Sum.inr (Sum.inr i)) = D.depB i := by
    dsimp [Bs, ofBstarOver]
  have hpos : 0 < D.depB i := D.hdepB i
  rw [h1, h2]
  omega

/-- The type-3 members `inr (inr i)` have value `s_j + 1` at full-tuple position
`j−1` (their tuples begin `(s_1,…,s_{j−1}, s_j+1, …)`). -/
lemma type3_sjadd_one_at_R1 (k : ℕ) (s : Fin k → ℕ+) (j : ℕ)
    (hk1 : 1 ≤ k) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F) :
    let D := RelData.BCqIter F (k - j - 1) (toData F (r1Rel F))
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) (r1Rel F) e)
        (RelData.iterate_merge_hv F (k - j - 1) (r1Rel F) (s ⟨j - 1, by omega⟩) (by omega) (r1Rel_hbhd F))
    let Q := FixedOver.prependList F Bs (sPrefix k s j (by omega) (by omega))
    ∀ i : D.ιB, ∀ (hm : j - 1 < Q.dep (Sum.inr (Sum.inr i))),
      ((Q.c (Sum.inr (Sum.inr i))) ⟨j - 1, hm⟩ : ℕ) = (s ⟨j - 1, by omega⟩ : ℕ) + 1 := by
  classical
  intro D Bs Q i hm
  have hlen : (sPrefix k s j (by omega) (by omega)).length = j - 1 :=
    sPrefix_length k s j (by omega) (by omega)
  have hge : (sPrefix k s j (by omega) (by omega)).length ≤ j - 1 := by omega
  have hQdep : Q.dep (Sum.inr (Sum.inr i)) =
      Bs.dep (Sum.inr (Sum.inr i)) + (sPrefix k s j (by omega) (by omega)).length := by
    exact FixedOver.prependList_dep F Bs (sPrefix k s j (by omega) (by omega)) (Sum.inr (Sum.inr i))
  have b' : (j - 1) - (sPrefix k s j (by omega) (by omega)).length < Bs.dep (Sum.inr (Sum.inr i)) := by
    have hm1 : j - 1 < Bs.dep (Sum.inr (Sum.inr i)) + (sPrefix k s j (by omega) (by omega)).length := by
      rw [← hQdep]
      exact hm
    omega
  have h1 : ((Q.c (Sum.inr (Sum.inr i))) ⟨j - 1, hm⟩ : ℕ) =
      ((Bs.c (Sum.inr (Sum.inr i))) ⟨(j - 1) - (sPrefix k s j (by omega) (by omega)).length, b'⟩ : ℕ) := by
    have hv := prependList_c_base_value F Bs (sPrefix k s j (by omega) (by omega))
      (Sum.inr (Sum.inr i)) (j - 1) hm hge
    apply congrArg (fun v : ℕ+ => (v : ℕ))
    calc
      (Q.c (Sum.inr (Sum.inr i))) ⟨j - 1, hm⟩
          = (Bs.c (Sum.inr (Sum.inr i))) ⟨(j - 1) - (sPrefix k s j (by omega) (by omega)).length,
              (by
                have hd := FixedOver.prependList_dep F Bs (sPrefix k s j (by omega) (by omega)) (Sum.inr (Sum.inr i))
                rw [hd] at hm
                omega)⟩ := hv
      _ = (Bs.c (Sum.inr (Sum.inr i))) ⟨(j - 1) - (sPrefix k s j (by omega) (by omega)).length, b'⟩ := by
            congr 1
  have hcBs : Bs.c (Sum.inr (Sum.inr i)) =
      headAdd (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i) := by
    dsimp [Bs, ofBstarOver, D]
  have h2 : ((Bs.c (Sum.inr (Sum.inr i))) ⟨(j - 1) - (sPrefix k s j (by omega) (by omega)).length, b'⟩ : ℕ) =
      ((headAdd (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i))
        ⟨(j - 1) - (sPrefix k s j (by omega) (by omega)).length, b'⟩ : ℕ) := by
    apply congrArg (fun v : ℕ+ => (v : ℕ))
    exact congrFun hcBs ⟨(j - 1) - (sPrefix k s j (by omega) (by omega)).length, b'⟩
  have h3 : ((headAdd (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i))
        ⟨(j - 1) - (sPrefix k s j (by omega) (by omega)).length, b'⟩ : ℕ) =
      (s ⟨j - 1, by omega⟩ : ℕ) + 1 := by
    have hjj : (j - 1) - (sPrefix k s j (by omega) (by omega)).length = 0 := by omega
    rw [show (⟨(j - 1) - (sPrefix k s j (by omega) (by omega)).length, b'⟩ :
            Fin (D.depB i)) = ⟨0, D.hdepB i⟩ from (by
        apply Fin.ext
        simp
        omega)]
    have hha := headAdd_head (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i)
    have hc := congrArg (fun t : ℕ+ => (t : ℕ)) hha
    rw [hc]
    have hbhead := RelData.BCqIter_head_one F (k - j - 1) (r1Rel F) (r1Rel_hbhd F) i
    have hbhead' : (((D.cB i) ⟨0, D.hdepB i⟩ : ℕ) = 1) := by
      have hh' := congrArg (fun t : ℕ+ => (t : ℕ)) hbhead
      simpa [oneExp, D] using hh'
    rw [hbhead']
    rfl
  calc
    ((Q.c (Sum.inr (Sum.inr i))) ⟨j - 1, hm⟩ : ℕ)
        = ((Bs.c (Sum.inr (Sum.inr i))) ⟨(j - 1) - (sPrefix k s j (by omega) (by omega)).length, b'⟩ : ℕ) := h1
    _ = ((headAdd (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i))
          ⟨(j - 1) - (sPrefix k s j (by omega) (by omega)).length, b'⟩ : ℕ) := h2
    _ = (s ⟨j - 1, by omega⟩ : ℕ) + 1 := h3

/-- Type-3 members have `j`-prefix sum equal to that of `s` plus one (their `j`-th
entry is `s_j+1`). -/
lemma type3_psum_j_R1 (k : ℕ) (s : Fin k → ℕ+) (j : ℕ)
    (hk1 : 1 ≤ k) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F) :
    let D := RelData.BCqIter F (k - j - 1) (toData F (r1Rel F))
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) (r1Rel F) e)
        (RelData.iterate_merge_hv F (k - j - 1) (r1Rel F) (s ⟨j - 1, by omega⟩) (by omega) (r1Rel_hbhd F))
    let Q := FixedOver.prependList F Bs (sPrefix k s j (by omega) (by omega))
    ∀ i : D.ιB, psum (Q.c (Sum.inr (Sum.inr i))) j = psum s j + 1 := by
  classical
  intro D Bs Q i
  have hdep : j ≤ Q.dep (Sum.inr (Sum.inr i)) := Q_dep_inr_inr_R1 F k s j hk1 hj1 hjk hsj i
  have hjlr : j - 1 < k := by omega
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
    have hv := member_prefix_pos_R1 F k s j hk1 hj1 hjk hsj (Sum.inr (Sum.inr i)) x hx1 hmQ
    have hxr : x < k := by
      have : x < j - 1 := hx1
      omega
    rw [pad0_of_lt (Q.c (Sum.inr (Sum.inr i))) hmQ, pad0_of_lt s hxr]
    exact congrArg (fun t : ℕ+ => (t : ℕ)) hv
  have hlast : (pad0 (Q.c (Sum.inr (Sum.inr i))) (j - 1) : ℕ) = (s ⟨j - 1, hjlr⟩ : ℕ) + 1 := by
    have hmQ : j - 1 < Q.dep (Sum.inr (Sum.inr i)) := by omega
    have hv := type3_sjadd_one_at_R1 F k s j hk1 hj1 hjk hsj i hmQ
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


/-- A type-3 member shares the `s`-front below position `j−1`. -/
lemma type3_front_eq_R1 (k : ℕ) (s : Fin k → ℕ+) (j : ℕ)
    (hk1 : 1 ≤ k) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F) :
    let D := RelData.BCqIter F (k - j - 1) (toData F (r1Rel F))
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) (r1Rel F) e)
        (RelData.iterate_merge_hv F (k - j - 1) (r1Rel F) (s ⟨j - 1, by omega⟩) (by omega) (r1Rel_hbhd F))
    let Q := FixedOver.prependList F Bs (sPrefix k s j (by omega) (by omega))
    ∀ i : D.ιB, ∀ x : ℕ, x < j - 1 →
      pad0 (Q.c (Sum.inr (Sum.inr i))) x = pad0 s x := by
  classical
  intro D Bs Q i x hx
  have hxr : x < k := by
    have : x < j - 1 := hx
    omega
  have hdepQ : j ≤ Q.dep (Sum.inr (Sum.inr i)) :=
    Q_dep_inr_inr_R1 F k s j hk1 hj1 hjk hsj i
  have hxQ : x < Q.dep (Sum.inr (Sum.inr i)) := by omega
  have hv := member_prefix_pos_R1 F k s j hk1 hj1 hjk hsj
    (Sum.inr (Sum.inr i)) x hx hxQ
  rw [pad0_of_lt (Q.c (Sum.inr (Sum.inr i))) hxQ]
  rw [pad0_of_lt s hxr]
  exact congrArg (fun t : ℕ+ => (t : ℕ)) hv

/-- A type-3 member's first `j` entries are `≤ q` (front `s`-entries via `hsleq`,
`s_j+1` via `hsj`). -/
lemma type3_front_le_R1 (k : ℕ) (s : Fin k → ℕ+) (j : ℕ)
    (hk1 : 1 ≤ k) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hsleq : ∀ x : ℕ, x < k - 1 → pad0 s x ≤ Nat.card F) :
    let D := RelData.BCqIter F (k - j - 1) (toData F (r1Rel F))
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) (r1Rel F) e)
        (RelData.iterate_merge_hv F (k - j - 1) (r1Rel F) (s ⟨j - 1, by omega⟩) (by omega) (r1Rel_hbhd F))
    let Q := FixedOver.prependList F Bs (sPrefix k s j (by omega) (by omega))
    ∀ i : D.ιB, ∀ x : ℕ, x < j → pad0 (Q.c (Sum.inr (Sum.inr i))) x ≤ Nat.card F := by
  classical
  intro D Bs Q i x hx
  have hdepQ : j ≤ Q.dep (Sum.inr (Sum.inr i)) :=
    Q_dep_inr_inr_R1 F k s j hk1 hj1 hjk hsj i
  by_cases hxj : x = j - 1
  · subst x
    have hxQ : j - 1 < Q.dep (Sum.inr (Sum.inr i)) := by omega
    have hv := type3_sjadd_one_at_R1 F k s j hk1 hj1 hjk hsj i hxQ
    have hp : pad0 (Q.c (Sum.inr (Sum.inr i))) (j - 1) =
        ((Q.c (Sum.inr (Sum.inr i))) ⟨j - 1, hxQ⟩ : ℕ) :=
      pad0_of_lt (Q.c (Sum.inr (Sum.inr i))) hxQ
    rw [hp]
    rw [hv]
    omega
  · have hx1 : x < j - 1 := by omega
    have hfront := type3_front_eq_R1 F k s j hk1 hj1 hjk hsj i x hx1
    rw [hfront]
    have hxk : x < k - 1 := by omega
    exact hsleq x hxk

/-- ★ The type-3 Init comparison: a type-3 member `u` of the CASE-2 chain has a
strictly lexicographically larger initial tuple than `s`, i.e.
`InitLt (Nat.card F) s u`, given the `(k−1)`-admissible front `s₁..s_{k−1} ≤ q`
(`hsleq`).  This is the termination engine of Prop 3.2 for kept type-3 members. -/
lemma type3_Init_gt_R1 (k : ℕ) (s : Fin k → ℕ+) (j : ℕ)
    (hk1 : 1 ≤ k) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hsleq : ∀ x : ℕ, x < k - 1 → pad0 s x ≤ Nat.card F) :
    let D := RelData.BCqIter F (k - j - 1) (toData F (r1Rel F))
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) (r1Rel F) e)
        (RelData.iterate_merge_hv F (k - j - 1) (r1Rel F) (s ⟨j - 1, by omega⟩) (by omega) (r1Rel_hbhd F))
    let Q := FixedOver.prependList F Bs (sPrefix k s j (by omega) (by omega))
    ∀ i : D.ιB, InitLt (Nat.card F) s (Q.c (Sum.inr (Sum.inr i))) := by
  classical
  intro D Bs Q i
  let p : D.ιA ⊕ (D.ιB ⊕ D.ιB) := Sum.inr (Sum.inr i)
  have hdepQ : j ≤ Q.dep p := by
    dsimp [p]
    exact Q_dep_inr_inr_R1 F k s j hk1 hj1 hjk hsj i
  have hjr : j ≤ k := by omega
  have huq : ∀ x : ℕ, x < j → pad0 (Q.c p) x ≤ Nat.card F := by
    dsimp [p]
    exact type3_front_le_R1 F k s j hk1 hj1 hjk hsj hsleq i
  have hvq : ∀ x : ℕ, x < j → pad0 s x ≤ Nat.card F := by
    intro x hx
    have hxk : x < k - 1 := by omega
    exact hsleq x hxk
  have heq : ∀ x : ℕ, x < j - 1 → pad0 (Q.c p) x = pad0 s x := by
    dsimp [p]
    exact type3_front_eq_R1 F k s j hk1 hj1 hjk hsj i
  have hxQ : j - 1 < Q.dep p := by omega
  have hxr : j - 1 < k := by omega
  have hv := type3_sjadd_one_at_R1 F k s j hk1 hj1 hjk hsj i hxQ
  have hgt : pad0 s (j - 1) < pad0 (Q.c p) (j - 1) := by
    dsimp [p]
    have hp1 : pad0 s (j - 1) = (s ⟨j - 1, hxr⟩ : ℕ) := pad0_of_lt s hxr
    have hp2 : pad0 (Q.c (Sum.inr (Sum.inr i))) (j - 1) =
        ((Q.c (Sum.inr (Sum.inr i))) ⟨j - 1, hxQ⟩ : ℕ) :=
      pad0_of_lt (Q.c (Sum.inr (Sum.inr i))) hxQ
    rw [hp1, hp2]
    rw [hv]
    omega
  simpa [p] using InitLt_of_head_gt (Nat.card F) (Q.c p) s j hj1 hdepQ hjr huq hvq heq hgt

end ZagierHoffmanPositiveChar
