import Submission.ZagierHoffmanProof.StepL125
import Submission.ZagierHoffmanProof.StepL116
set_option autoImplicit false
set_option maxHeartbeats 200000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L126: the mixed type-1 member-entry facts (SESSION 258s)

First half of `maink_mixed_type1_init_bound`: the entries 0..k−2 of a type-1
(i₀ ≠ u) member of the (k, j)-chain coincide with s's entries.  Three regions:
  • x < j−1 (front): `prependList_c_front_value` + `sPrefix_reverse_value`;
  • x = j−1 (base): `type1_sj_at_jm1` (head = v = s⟨j−1⟩);
  • j ≤ x ≤ k−2 (q-run): `type1_pad0_shift` + `BCqIter_cA_pad0_front` + `hmid`.
Also the pivot entry: pad0 member (k−1) = (R0.cA i₀)⟨0⟩ — via `type1_pad0_shift`
+ `RelData.BCqIter_cA_value` (first n entries are q, then the base tuple).
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★ The type-1 member's entries 0..k−2 equal s's entries. -/
theorem maink_type1_entry_eq (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hmid : ∀ i : Fin r, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < k - 1 → (s i : ℕ) = Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i₀ : R0.ιA, ∀ x : ℕ, x < k - 1 →
      pad0 (Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀))) x = pad0 s x := by
  classical
  intro D Bs Q i₀ x hx
  have hxr : x < r := by omega
  rw [pad0_of_lt s hxr]
  by_cases hxj : (j : ℕ) ≤ x
  · -- q-run region: member entry = q = s's entry (hmid)
    have hsh := type1_pad0_shift F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd
      (RelData.iterIdx F (k - j - 1) (toData F R0) i₀) x hxj
    have hsub : x - j < k - j - 1 := by omega
    have hf := BCqIter_cA_pad0_front F (k - j - 1) R0 i₀ (x - j) hsub
    rw [hsh, hf]
    exact (hmid ⟨x, hxr⟩ hxj hx).symm
  · have hxj' : x < j := by omega
    rcases Nat.lt_or_eq_of_le (show x ≤ j - 1 by omega) with hlt | heq
    · -- front region: member entry = s's entry via sPrefix
      have hlen : (sPrefix r s j (by omega) (by omega)).length = j - 1 :=
        sPrefix_length r s j (by omega) (by omega)
      have hmf : x < (sPrefix r s j (by omega) (by omega)).length := by rw [hlen]; omega
      have hmx : x < Q.dep (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀)) := by
        rw [FixedOver.prependList_dep]
        have hBs : Bs.dep (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀))
            = (RelData.BCqIter F (k - j - 1) (toData F R0)).depA
                (RelData.iterIdx F (k - j - 1) (toData F R0) i₀) + 1 := by
          dsimp [Bs, ofBstarOver, D]
        have hdepD : (RelData.BCqIter F (k - j - 1) (toData F R0)).depA
            (RelData.iterIdx F (k - j - 1) (toData F R0) i₀) = R0.depA i₀ + (k - j - 1) :=
          RelData.BCqIter_depA_at F (k - j - 1) (toData F R0) i₀
        have hlen : (sPrefix r s j (by omega) (by omega)).length = j - 1 :=
          sPrefix_length r s j (by omega) (by omega)
        rw [hBs, hdepD, hlen]
        have hpos : 0 < R0.depA i₀ := R0.hdepA i₀
        omega
      have hval := prependList_c_front_value F Bs (sPrefix r s j (by omega) (by omega))
        (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀)) x hmx hmf
      rw [pad0_of_lt (Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀))) hmx]
      rw [hval]
      have hrev := sPrefix_reverse_value r s j (by omega) (by omega) x (by simpa using hmf)
      rw [hrev]
    · -- base region: x = j−1, member entry = v = s⟨j−1⟩
      subst heq
      have hdep : j - 1 < Q.dep (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀)) := by
        rw [FixedOver.prependList_dep]
        have hBs : Bs.dep (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀))
            = (RelData.BCqIter F (k - j - 1) (toData F R0)).depA
                (RelData.iterIdx F (k - j - 1) (toData F R0) i₀) + 1 := by
          dsimp [Bs, ofBstarOver, D]
        have hdepD : (RelData.BCqIter F (k - j - 1) (toData F R0)).depA
            (RelData.iterIdx F (k - j - 1) (toData F R0) i₀) = R0.depA i₀ + (k - j - 1) :=
          RelData.BCqIter_depA_at F (k - j - 1) (toData F R0) i₀
        have hlen : (sPrefix r s j (by omega) (by omega)).length = j - 1 :=
          sPrefix_length r s j (by omega) (by omega)
        rw [hBs, hdepD, hlen]
        have hpos : 0 < R0.depA i₀ := R0.hdepA i₀
        omega
      rw [pad0_of_lt (Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀))) hdep]
      exact type1_sj_at_jm1 F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd
        (RelData.iterIdx F (k - j - 1) (toData F R0) i₀) hdep

/-- ★ The pivot entry of a type-1 member: at index `k−1` the member carries the
head `(R0.cA i₀)⟨0⟩` of the base a-tuple. -/
theorem maink_type1_pivot_eq (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i₀ : R0.ιA,
      pad0 (Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀))) (k - 1)
        = ((R0.cA i₀) ⟨0, R0.hdepA i₀⟩ : ℕ) := by
  classical
  intro D Bs Q i₀
  have hkj : j ≤ k - 1 := hjk
  have hk1' : j ≤ k - 1 := hjk
  have hsh := type1_pad0_shift F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd
    (RelData.iterIdx F (k - j - 1) (toData F R0) i₀) (k - 1) (by omega)
  have hsub : (k - 1) - j = k - j - 1 := by omega
  rw [hsh, hsub]
  -- the entry of the iterated cA at index n = k−j−1 is the base head
  have hdep_iter := RelData.BCqIter_depA_at F (k - j - 1) (toData F R0) i₀
  have hdepn : (k - j - 1) < (toData F R0).depA i₀ + (k - j - 1) := by
    have hpos : 0 < (toData F R0).depA i₀ := (toData F R0).hdepA i₀
    omega
  have hcv := RelData.BCqIter_cA_value F (k - j - 1) (toData F R0) i₀
    ⟨k - j - 1, hdepn⟩
  have hcv' : pad0 ((RelData.BCqIter F (k - j - 1) (toData F R0)).cA
        (RelData.iterIdx F (k - j - 1) (toData F R0) i₀)) (k - j - 1)
      = ((toData F R0).cA i₀) ⟨0, (toData F R0).hdepA i₀⟩ := by
    have h' : (k - j - 1) < (RelData.BCqIter F (k - j - 1) (toData F R0)).depA
        (RelData.iterIdx F (k - j - 1) (toData F R0) i₀) := by
      rw [hdep_iter]; exact hdepn
    rw [pad0_of_lt _ h']
    have hcast : (⟨k - j - 1, h'⟩ : Fin ((RelData.BCqIter F (k - j - 1) (toData F R0)).depA
          (RelData.iterIdx F (k - j - 1) (toData F R0) i₀)))
        = Fin.cast (hdep_iter).symm ⟨k - j - 1, hdepn⟩ := by
      apply Fin.ext
      simp
    rw [hcast]
    simpa using hcv
  rw [hcv']
  rfl

end ZagierHoffmanPositiveChar
