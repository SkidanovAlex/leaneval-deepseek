import Submission.ZagierHoffmanProof.StepL77
import Submission.ZagierHoffmanProof.StepL83
import Submission.ZagierHoffmanProof.StepL48
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L85: G5-3 (the level-3 j=0 (q,q)-front chain) — full chain facts

SESSIONS 239-241.  The in-domain (2-adm ∧ ¬3-adm) tuples with the all-q front
s₀ = q ∧ s₁ = q ∧ s₂ > q (CASE-1 j=0; prop212 has no instance there) expand at
level 3 via the empty-front chain D := BCqIter F 2 (toData F R0) on the
lemma_2_9_config_data relation R0 at k = 3 (D.cA u = s).

CONTENT: the depth/value bridges (g53c1_depth_eq, bstarBase3_values,
qprepend2_tail_values, g53c1_u_cA_values); the chain ζ-identity
(★ g53c1_zeta_core / g53c1_zeta); the a-side member facts (weight = w,
prefix-3 STRICT drop, 2-adm) and the a-side ℓ ≥ 3 prefix-≤ order
(★ g53c1_aSide_order, from the level-0 prefix bound hpref + lemma29_qExp_
telescope); the b-side member facts (weight = w, 2-adm, prefix-3 STRICT drop)
with the entry helpers b2_entry0 / b2_entry1_le_q / b1_entry1_le_q.  The b-side
ℓ ≥ 3 order and the g53_case1_step splice are the next items (see PLAN.md).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]


/-! ## SESSION 239 — G5-3 first stones: (q,q)-front chain value bridges + ζ-core.

The level-3 j=0 chain (mirror of StepL76/77): input s with 3 ≤ r, s₀=q, s₁=q,
q < s₂; R0 from lemma_2_9_config_data at k=3 (cA u ≃ bstarBase at 3 =
(s⟨2⟩, s⟨3⟩, ..)); D := BCqIter F 2 (toData F R0) so D.cA u = (q,q,R0.cA u) = s.
-/

/-- depth bridge for the k=3 chain. -/
lemma g53c1_depth_eq (r : ℕ) (hcase : 3 ≤ r) : (r - 3) + 1 + 2 = r := by omega

/-- bstarBase at k=3 value at m = s⟨m+2⟩ (shift by 2; independent of hs0/hs1). -/
lemma bstarBase3_values (r : ℕ) (s : Fin r → ℕ+) (hcase : 3 ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨2, by omega⟩ : ℕ)) :
    ∀ m : Fin ((r - 3) + 1),
      (bstarBase F r s 3 (by omega : 1 ≤ 3) hcase hbig) m = s ⟨(m : ℕ) + 2, by omega⟩ := by
  classical
  intro m
  by_cases hm0 : (m : ℕ) = 0
  · have hmm : m = ⟨0, by omega⟩ := Fin.ext (by simpa using hm0)
    rw [hmm]
    have hbh := bstarBase_head F r s 3 (by omega : 1 ≤ 3) hcase hbig
    change (bstarBase F r s 3 (by omega : 1 ≤ 3) hcase hbig) ⟨0, by omega⟩ =
      s ⟨0 + 2, by omega⟩
    rw [hbh]
  · let n : ℕ := (m : ℕ) - 1
    have hmn : (m : ℕ) = n + 1 := by omega
    have hmm : m = ⟨n + 1, by omega⟩ := Fin.ext (by simpa [hmn])
    rw [hmm]
    have hnl : n < r - 3 := by
      have hlt : n + 1 < (r - 3) + 1 := by
        have h1 : (m : ℕ) = n + 1 := hmn
        have h2 : (m : ℕ) < (r - 3) + 1 := m.isLt
        omega
      omega
    have hb := bstarBase_tail F r s 3 (by omega : 1 ≤ 3) hcase hbig ⟨n, hnl⟩
    change (bstarBase F r s 3 (by omega : 1 ≤ 3) hcase hbig) ⟨n + 1, by omega⟩ =
      s ⟨(n + 1) + 2, by omega⟩
    have hb' : (bstarBase F r s 3 (by omega : 1 ≤ 3) hcase hbig) ⟨n + 1, by omega⟩ =
        sTail r s 3 hcase ⟨n, hnl⟩ := by
      simpa using hb
    rw [hb']
    dsimp [sTail]
    have hidx : (⟨3 + n, by omega⟩ : Fin r) = ⟨(n + 1) + 2, by omega⟩ := by
      apply Fin.ext
      change (3 + n) = ((n : ℕ) + 1) + 2
      omega
    rw [hidx]

/-- the (q,q)-double-prepend of bstarBase-at-3 equals s (value bridge). -/
lemma qprepend2_tail_values (r : ℕ) (s : Fin r → ℕ+) (hcase : 3 ≤ r)
    (hs0 : (s ⟨0, by omega⟩ : ℕ) = Nat.card F)
    (hs1 : (s ⟨1, by omega⟩ : ℕ) = Nat.card F)
    (hbig : (Nat.card F : ℕ) < (s ⟨2, by omega⟩ : ℕ)) :
    ∀ i : Fin ((r - 3) + 1 + 2),
      (consVec (qExp F) (consVec (qExp F)
        (bstarBase F r s 3 (by omega : 1 ≤ 3) hcase hbig))) i =
        s ⟨(i : ℕ), by
          have h1 := g53c1_depth_eq r hcase
          simpa [h1] using i.isLt⟩ := by
  classical
  intro i
  by_cases hi0 : (i : ℕ) = 0
  · have hii : i = ⟨0, by omega⟩ := Fin.ext (by simpa using hi0)
    rw [hii]
    change (consVec (qExp F) (consVec (qExp F)
      (bstarBase F r s 3 (by omega : 1 ≤ 3) hcase hbig))) ⟨0, by omega⟩ = s ⟨0, by omega⟩
    rw [consVec_zero (qExp F) (consVec (qExp F)
      (bstarBase F r s 3 (by omega : 1 ≤ 3) hcase hbig))]
    apply Subtype.ext
    change Nat.card F = (s ⟨0, by omega⟩ : ℕ)
    exact hs0.symm
  · let n : ℕ := (i : ℕ) - 1
    have hin : (i : ℕ) = n + 1 := by omega
    by_cases hn0 : n = 0
    · have hii : i = ⟨1, by omega⟩ := Fin.ext (by simp [hin, hn0])
      rw [hii]
      change (consVec (qExp F) (consVec (qExp F)
        (bstarBase F r s 3 (by omega : 1 ≤ 3) hcase hbig))) ⟨1, by omega⟩ = s ⟨1, by omega⟩
      rw [consVec_succ (qExp F) (consVec (qExp F)
        (bstarBase F r s 3 (by omega : 1 ≤ 3) hcase hbig)) ⟨0, by omega⟩]
      rw [consVec_zero (qExp F) (bstarBase F r s 3 (by omega : 1 ≤ 3) hcase hbig)]
      apply Subtype.ext
      change Nat.card F = (s ⟨1, by omega⟩ : ℕ)
      exact hs1.symm
    · have hii : i = ⟨n + 1, by omega⟩ := Fin.ext (by simpa [hin])
      rw [hii]
      change (consVec (qExp F) (consVec (qExp F)
        (bstarBase F r s 3 (by omega : 1 ≤ 3) hcase hbig))) ⟨n + 1, by omega⟩ =
          s ⟨(n + 1), by omega⟩
      have hinner := consVec_succ (qExp F) (consVec (qExp F)
        (bstarBase F r s 3 (by omega : 1 ≤ 3) hcase hbig)) ⟨n, by omega⟩
      rw [hinner]
      -- inner consVec q (bstarBase) at position n (≥ 1): value = bstarBase at n−1
      let m : ℕ := n - 1
      have hnm : n = m + 1 := by omega
      have hmm' : (⟨n, by omega⟩ : Fin ((r - 3) + 1 + 1)) = ⟨m + 1, by omega⟩ := by
        apply Fin.ext
        omega
      rw [hmm']
      have hsucc := consVec_succ (qExp F) (bstarBase F r s 3 (by omega : 1 ≤ 3) hcase hbig)
        ⟨m, by omega⟩
      rw [hsucc]
      have hml : m < (r - 3) + 1 := by
        have hil : (i : ℕ) < (r - 3) + 1 + 2 := i.isLt
        omega
      have hb := bstarBase3_values F r s hcase hbig ⟨m, hml⟩
      rw [hb]
      have hidx : (⟨(n : ℕ) + 1, by omega⟩ : Fin r) = ⟨m + 2, by omega⟩ := by
        apply Fin.ext
        change ((n : ℕ) + 1) = (m + 2)
        omega
      rw [hidx]

/-- the iterate-2 u-member equals s value-wise (the ζ_A_eq_of_reindex input). -/
lemma g53c1_u_cA_values (r : ℕ) (s : Fin r → ℕ+) (hcase : 3 ≤ r)
    (hs0 : (s ⟨0, by omega⟩ : ℕ) = Nat.card F)
    (hs1 : (s ⟨1, by omega⟩ : ℕ) = Nat.card F)
    (hbig : (Nat.card F : ℕ) < (s ⟨2, by omega⟩ : ℕ))
    (R0 : BinaryRel F) (u : R0.ιA)
    (hdepu : R0.depA u = (r - 3) + 1)
    (hc0 : ∀ hd : R0.depA u = (r - 3) + 1,
      (fun x : Fin ((r - 3) + 1) => R0.cA u (Fin.cast hd.symm x)) =
        bstarBase F r s 3 (by omega : 1 ≤ 3) hcase hbig) :
    ∀ (m : ℕ) (hmQ : m < (RelData.BCqIter F 2 (toData F R0)).depA u) (hmr : m < r),
      (RelData.BCqIter F 2 (toData F R0)).cA u ⟨m, hmQ⟩ = s ⟨m, hmr⟩ := by
  classical
  intro m hmQ hmr
  by_cases hm0 : m = 0
  · subst m
    have hcA0 : (RelData.BCqIter F 2 (toData F R0)).cA u ⟨0, hmQ⟩ = qExp F := by rfl
    rw [hcA0]
    apply Subtype.ext
    change Nat.card F = (s ⟨0, by omega⟩ : ℕ)
    exact hs0.symm
  · have hmge1 : 1 ≤ m := by omega
    by_cases hm1 : m = 1
    · subst m
      have hcA1 : (RelData.BCqIter F 2 (toData F R0)).cA u ⟨1, hmQ⟩ = qExp F := by rfl
      rw [hcA1]
      apply Subtype.ext
      change Nat.card F = (s ⟨1, by omega⟩ : ℕ)
      exact hs1.symm
    · have hex : ∃ n : ℕ, m = n + 2 := ⟨m - 2, by omega⟩
      rcases hex with ⟨n, hmn⟩
      subst m
      have hndep : n < R0.depA u := by
        have hd : (RelData.BCqIter F 2 (toData F R0)).depA u = R0.depA u + 2 := by
          dsimp [RelData.BCqIter, RelData.BCq]
          rfl
        rw [hd] at hmQ
        omega
      have hcA : (RelData.BCqIter F 2 (toData F R0)).cA u ⟨n + 2, hmQ⟩ =
          (R0.cA u) ⟨n, hndep⟩ := by
        rfl
      rw [hcA]
      have hnlt0 : n < (r - 3) + 1 := by omega
      have hb := hc0 hdepu
      have hb' : (R0.cA u) (Fin.cast hdepu.symm ⟨n, hnlt0⟩) =
          bstarBase F r s 3 (by omega : 1 ≤ 3) hcase hbig ⟨n, hnlt0⟩ := by
        exact congrFun hb ⟨n, hnlt0⟩
      have hcast : Fin.cast hdepu.symm ⟨n, hnlt0⟩ = ⟨n, hndep⟩ := by
        apply Fin.ext
        rfl
      have hb'' : (R0.cA u) ⟨n, hndep⟩ =
          bstarBase F r s 3 (by omega : 1 ≤ 3) hcase hbig ⟨n, hnlt0⟩ := by
        rw [← hcast]
        exact hb'
      rw [hb'']
      have hbv := bstarBase3_values F r s hcase hbig ⟨n, hnlt0⟩
      -- hbv : bstarBase⟨n⟩ = s⟨n+2⟩; goal s⟨n+2, hmr⟩
      change bstarBase F r s 3 (by omega : 1 ≤ 3) hcase hbig ⟨n, hnlt0⟩ = s ⟨n + 2, hmr⟩
      rw [hbv]

/-- ★ the (q,q)-front (k=3 j=0) chain ζ-identity from the config conjuncts. -/
theorem g53c1_zeta_core (r : ℕ) (s : Fin r → ℕ+) (hcase : 3 ≤ r)
    (hs0 : (s ⟨0, by omega⟩ : ℕ) = Nat.card F)
    (hs1 : (s ⟨1, by omega⟩ : ℕ) = Nat.card F)
    (hbig : (Nat.card F : ℕ) < (s ⟨2, by omega⟩ : ℕ))
    (R0 : BinaryRel F) (u : R0.ιA)
    (hdepu : R0.depA u = (r - 3) + 1)
    (hau : R0.aA u = 1)
    (hc0 : ∀ hd : R0.depA u = (r - 3) + 1,
      (fun x : Fin ((r - 3) + 1) => R0.cA u (Fin.cast hd.symm x)) =
        bstarBase F r s 3 (by omega : 1 ≤ 3) hcase hbig) :
    let D := RelData.BCqIter F 2 (toData F R0)
    ζ_A F s +
      (∑ i : D.ιA, (if i = u then 0 else
        (((D.aA i : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (D.cA i)))) +
      (∑ p : D.ιB, (((D.aB p : RatFunc F) : RatFunc.CompletionAtInfty F) *
        ζ_A F (D.cB p))) = 0 := by
  classical
  intro D
  let f : D.ιA → RatFunc.CompletionAtInfty F := fun i =>
    (((D.aA i : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (D.cA i))
  let g : D.ιB → RatFunc.CompletionAtInfty F := fun p =>
    (((D.aB p : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (D.cB p))
  have hz0 : (∑ i : D.ιA, f i) + (∑ p : D.ιB, g p) = 0 := by
    have hz := BCqIter_zeta_zero F 2 R0
    rw [toBinaryRel_zeta_eq F (RelData.BCqIter F 2 (toData F R0)) (BCqIter_valid F 2 R0)] at hz
    simpa [f, g, D] using hz
  have hu_zeta : ζ_A F (D.cA u) = ζ_A F s := by
    refine ζ_A_eq_of_reindex F ?hd (D.cA u) s ?hp
    · have hd0 : D.depA u = R0.depA u + 2 := by
        dsimp [D, RelData.BCqIter, RelData.BCq]
        rfl
      omega
    · intro i
      have hilt : (i : ℕ) < D.depA u := i.isLt
      have hd0 : D.depA u = R0.depA u + 2 := by
        dsimp [D, RelData.BCqIter, RelData.BCq]
        rfl
      have hv := g53c1_u_cA_values F r s hcase hs0 hs1 hbig R0 u hdepu hc0 (i : ℕ) hilt (by omega)
      simpa using hv
  have hfu : f u = ζ_A F s := by
    have ha1 : (D.aA u : RatFunc F) = 1 := by dsimp [D]; exact hau
    dsimp [f]
    rw [ha1, hu_zeta]
    simp [completion_coe_one]
  have hgu : (∑ i : D.ιA, (if i = u then 0 else f i)) =
      (∑ i ∈ (Finset.univ : Finset D.ιA).erase u, f i) := by
    calc
      (∑ i : D.ιA, (if i = u then 0 else f i))
          = (∑ i ∈ (Finset.univ : Finset D.ιA), (if i = u then 0 else f i)) := by rfl
      _ = (∑ i ∈ (Finset.univ : Finset D.ιA).erase u, f i) := by
            have hs := Finset.sum_erase_add (s := (Finset.univ : Finset D.ιA))
              (f := fun i => if i = u then 0 else f i) (a := u) (Finset.mem_univ u)
            have hifu : (if u = u then 0 else f u) = 0 := by simp
            have herase : (∑ x ∈ (Finset.univ : Finset D.ιA).erase u, (if x = u then 0 else f x)) =
                (∑ x ∈ (Finset.univ : Finset D.ιA).erase u, f x) := by
              apply Finset.sum_congr rfl
              intro x hx
              have hxu : x ≠ u := (Finset.mem_erase.mp hx).1
              simp [hxu]
            calc
              (∑ i ∈ (Finset.univ : Finset D.ιA), (if i = u then 0 else f i))
                  = (∑ i ∈ (Finset.univ : Finset D.ιA).erase u, (if i = u then 0 else f i)) +
                      (if u = u then 0 else f u) := hs.symm
              _ = (∑ i ∈ (Finset.univ : Finset D.ιA).erase u, f i) := by
                    rw [herase, hifu]
                    simp
  have hspl : (∑ i : D.ιA, f i) = f u + (∑ i : D.ιA, (if i = u then 0 else f i)) := by
    have h1 : (∑ i : D.ιA, f i) = (∑ i ∈ (Finset.univ : Finset D.ιA).erase u, f i) + f u := by
      exact (Finset.sum_erase_add (s := (Finset.univ : Finset D.ιA)) (f := f) (a := u)
        (Finset.mem_univ u)).symm
    rw [h1, hgu]
    ring
  rw [hspl, hfu] at hz0
  simpa [add_assoc] using hz0

/-- the ∃ form (wrapper over the config rcases). -/
theorem g53c1_zeta (r : ℕ) (s : Fin r → ℕ+) (hcase : 3 ≤ r)
    (hs0 : (s ⟨0, by omega⟩ : ℕ) = Nat.card F)
    (hs1 : (s ⟨1, by omega⟩ : ℕ) = Nat.card F)
    (hbig : (Nat.card F : ℕ) < (s ⟨2, by omega⟩ : ℕ)) :
    ∃ (R0 : BinaryRel F) (u : R0.ιA),
      let D := RelData.BCqIter F 2 (toData F R0)
      ζ_A F s +
        (∑ i : D.ιA, (if i = u then 0 else
          (((D.aA i : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (D.cA i)))) +
        (∑ p : D.ιB, (((D.aB p : RatFunc F) : RatFunc.CompletionAtInfty F) *
          ζ_A F (D.cB p))) = 0 := by
  classical
  rcases lemma_2_9_config_data F r s 3 (by omega : 1 ≤ 3) hcase hbig with
    ⟨R0, u, hdepu, hau, hc0, hbhd, hwtA, hhead, hXw, hbndB⟩
  refine ⟨R0, u, ?_⟩
  intro D
  exact g53c1_zeta_core F r s hcase hs0 hs1 hbig R0 u hdepu hau hc0

/-- a-side (i ≠ u) members of the k=3 j=0 chain have weight w. -/
lemma g53c1_aSide_weight (r : ℕ) (s : Fin r → ℕ+) (hcase : 3 ≤ r)
    (hs0 : (s ⟨0, by omega⟩ : ℕ) = Nat.card F)
    (hs1 : (s ⟨1, by omega⟩ : ℕ) = Nat.card F)
    (hbig : (Nat.card F : ℕ) < (s ⟨2, by omega⟩ : ℕ))
    (R0 : BinaryRel F) (u : R0.ιA) (hau : R0.aA u = 1)
    (hwtA : ∀ i : R0.ιA, i ≠ u → weight (R0.depA i) (R0.cA i) = psum s r - psum s (3 - 1)) :
    let D := RelData.BCqIter F 2 (toData F R0)
    ∀ i : R0.ιA, i ≠ u → weight (D.depA i) (D.cA i) = weight r s := by
  classical
  intro D i hi
  have hdep : D.depA i = R0.depA i + 2 := by
    dsimp [D, RelData.BCqIter, RelData.BCq]
    rfl
  have hcA : D.cA i = consVec (qExp F) (consVec (qExp F) (R0.cA i)) := by
    dsimp [D, RelData.BCqIter, RelData.BCq]
    rfl
  rw [hcA]
  change weight (R0.depA i + 2) (consVec (qExp F) (consVec (qExp F) (R0.cA i))) = weight r s
  have hw1 : weight (R0.depA i + 2) (consVec (qExp F) (consVec (qExp F) (R0.cA i))) =
      (qExp F : ℕ) + weight (R0.depA i + 1) (consVec (qExp F) (R0.cA i)) := by
    exact weight_consVec (qExp F) (consVec (qExp F) (R0.cA i))
  have hw2 : weight (R0.depA i + 1) (consVec (qExp F) (R0.cA i)) =
      (qExp F : ℕ) + weight (R0.depA i) (R0.cA i) := by
    exact weight_consVec (qExp F) (R0.cA i)
  rw [hw1, hw2]
  have hwt := hwtA i hi
  rw [hwt]
  have hpsumr : psum s r = weight r s := psum_self s
  rw [← hpsumr]
  have hpsum2 : psum s (3 - 1) = 2 * (qExp F : ℕ) := by
    have hp : psum s 2 = pad0 s 0 + pad0 s 1 := by
      change (∑ j ∈ Finset.range 2, pad0 s j) = pad0 s 0 + pad0 s 1
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      simp
    rw [hp]
    have hp0 : pad0 s 0 = (s ⟨0, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 0 < r)
    have hp1 : pad0 s 1 = (s ⟨1, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 1 < r)
    rw [hp0, hp1]
    have hq : (qExp F : ℕ) = Nat.card F := by rfl
    rw [hs0, hs1]
    rw [hq]
    omega
  -- goal: (qExp) + ((qExp) + (psum s r - psum s 2)) = psum s r
  have hq : (qExp F : ℕ) = Nat.card F := by rfl
  rw [hq, hpsum2]
  have hle2 : psum s (3 - 1) ≤ psum s r := psum_mono s (by omega : 3 - 1 ≤ r)
  omega

/-- a-side (i ≠ u) prefix-3 is STRICTLY below psum s 3 (2q + head < 2q + s₂). -/
lemma g53c1_aSide_prefix_drop (r : ℕ) (s : Fin r → ℕ+) (hcase : 3 ≤ r)
    (hs0 : (s ⟨0, by omega⟩ : ℕ) = Nat.card F)
    (hs1 : (s ⟨1, by omega⟩ : ℕ) = Nat.card F)
    (hbig : (Nat.card F : ℕ) < (s ⟨2, by omega⟩ : ℕ))
    (R0 : BinaryRel F) (u : R0.ιA)
    (hhead : ∀ i : R0.ιA, i ≠ u →
      ((R0.cA i) ⟨0, R0.hdepA i⟩ : ℕ) < (s ⟨3 - 1, by omega⟩ : ℕ)) :
    let D := RelData.BCqIter F 2 (toData F R0)
    ∀ i : R0.ιA, i ≠ u → psum (D.cA i) 3 < psum s 3 := by
  classical
  intro D i hi
  have hcA : D.cA i = consVec (qExp F) (consVec (qExp F) (R0.cA i)) := by
    dsimp [D, RelData.BCqIter, RelData.BCq]
    rfl
  change psum (consVec (qExp F) (consVec (qExp F) (R0.cA i))) 3 < psum s 3
  -- psum 3 of the triple = q + q + head
  have hq : (qExp F : ℕ) = Nat.card F := by rfl
  have hp : psum (consVec (qExp F) (consVec (qExp F) (R0.cA i))) 3 =
      (qExp F : ℕ) + (qExp F : ℕ) + ((R0.cA i) ⟨0, R0.hdepA i⟩ : ℕ) := by
    have hd0 : 0 < R0.depA i + 2 := by omega
    have hd1 : 1 < R0.depA i + 2 := by omega
    have hd2 : 2 < R0.depA i + 2 := by
      have hda : 0 < R0.depA i := R0.hdepA i
      omega
    change (∑ j ∈ Finset.range 3, pad0 (consVec (qExp F) (consVec (qExp F) (R0.cA i))) j) =
      (qExp F : ℕ) + (qExp F : ℕ) + ((R0.cA i) ⟨0, R0.hdepA i⟩ : ℕ)
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    simp
    rw [pad0_of_lt (consVec (qExp F) (consVec (qExp F) (R0.cA i))) hd0]
    rw [pad0_of_lt (consVec (qExp F) (consVec (qExp F) (R0.cA i))) hd1]
    rw [pad0_of_lt (consVec (qExp F) (consVec (qExp F) (R0.cA i))) hd2]
    rfl
  rw [hp]
  -- psum s 3 = q + q + s₂
  have hp2 : psum s 3 = (qExp F : ℕ) + (qExp F : ℕ) + (s ⟨2, by omega⟩ : ℕ) := by
    change (∑ j ∈ Finset.range 3, pad0 s j) =
      (qExp F : ℕ) + (qExp F : ℕ) + (s ⟨2, by omega⟩ : ℕ)
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    simp
    rw [pad0_of_lt s (by omega : 0 < r)]
    rw [pad0_of_lt s (by omega : 1 < r)]
    rw [pad0_of_lt s (by omega : 2 < r)]
    rw [hs0, hs1]
    rw [hq]
  rw [hp2]
  have hh2 : ((R0.cA i) ⟨0, R0.hdepA i⟩ : ℕ) < (s ⟨2, by omega⟩ : ℕ) := by
    simpa using (hhead i hi)
  omega

/-- a-side (i ≠ u) members are 2-admissible. -/
lemma g53c1_aSide_twoAdm (r : ℕ) (s : Fin r → ℕ+) (hcase : 3 ≤ r)
    (hs0 : (s ⟨0, by omega⟩ : ℕ) = Nat.card F)
    (hs1 : (s ⟨1, by omega⟩ : ℕ) = Nat.card F)
    (hbig : (Nat.card F : ℕ) < (s ⟨2, by omega⟩ : ℕ))
    (R0 : BinaryRel F) (u : R0.ιA) :
    let D := RelData.BCqIter F 2 (toData F R0)
    ∀ i : R0.ιA, i ≠ u → kAdmissible (Nat.card F) (D.cA i) 2 := by
  classical
  intro D i hi
  have hcA : D.cA i = consVec (qExp F) (consVec (qExp F) (R0.cA i)) := by
    dsimp [D, RelData.BCqIter, RelData.BCq]
    rfl
  rw [hcA]
  refine twoAdm_of_pad0_le (Nat.card F) (consVec (qExp F) (consVec (qExp F) (R0.cA i))) ?_ ?_ ?_
  · change 3 ≤ R0.depA i + 2
    have hda : 0 < R0.depA i := R0.hdepA i
    omega
  · have hd0 : 0 < R0.depA i + 2 := by omega
    rw [pad0_of_lt (consVec (qExp F) (consVec (qExp F) (R0.cA i))) hd0]
    rfl
  · have hd1 : 1 < R0.depA i + 2 := by omega
    rw [pad0_of_lt (consVec (qExp F) (consVec (qExp F) (R0.cA i))) hd1]
    rfl


/-- b-side members of the k=3 j=0 chain have weight w (two p2WpT layers). -/
lemma g53c1_bSide_weight (r : ℕ) (s : Fin r → ℕ+) (hcase : 3 ≤ r)
    (hs0 : (s ⟨0, by omega⟩ : ℕ) = Nat.card F)
    (hs1 : (s ⟨1, by omega⟩ : ℕ) = Nat.card F)
    (hbig : (Nat.card F : ℕ) < (s ⟨2, by omega⟩ : ℕ))
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1)
    (hXw : ∀ j' : R0.ιB, weight (R0.depB j' - 1) (expTail (R0.cB j')) =
      psum s r - psum s (3 - 1) - 1) :
    let D := RelData.BCqIter F 2 (toData F R0)
    ∀ p : D.ιB, weight (D.depB p) (D.cB p) = weight r s := by
  classical
  intro D p
  let B := RelData.BCqIter F 1 (toData F R0)
  -- D = BCq B; p = (j₁, e₁) with j₁ : B.ιB
  have hcB : D.cB p = consVec oneExp ((p2WpT F (qMinusExp F) (B.hdepB p.1) (B.cB p.1)).c p.2) := by
    dsimp [D, B]
    rfl
  rw [hcB]
  change weight ((p2WpT F (qMinusExp F) (B.hdepB p.1) (B.cB p.1)).dep p.2 + 1)
      (consVec oneExp ((p2WpT F (qMinusExp F) (B.hdepB p.1) (B.cB p.1)).c p.2)) = weight r s
  have hw1 : weight ((p2WpT F (qMinusExp F) (B.hdepB p.1) (B.cB p.1)).dep p.2 + 1)
      (consVec oneExp ((p2WpT F (qMinusExp F) (B.hdepB p.1) (B.cB p.1)).c p.2)) =
      (oneExp : ℕ) + weight ((p2WpT F (qMinusExp F) (B.hdepB p.1) (B.cB p.1)).dep p.2)
        ((p2WpT F (qMinusExp F) (B.hdepB p.1) (B.cB p.1)).c p.2) := by
    exact weight_consVec oneExp ((p2WpT F (qMinusExp F) (B.hdepB p.1) (B.cB p.1)).c p.2)
  rw [hw1]
  have hwm1 : weight ((p2WpT F (qMinusExp F) (B.hdepB p.1) (B.cB p.1)).dep p.2)
        ((p2WpT F (qMinusExp F) (B.hdepB p.1) (B.cB p.1)).c p.2) =
      (qMinusExp F : ℕ) + weight (B.depB p.1) (B.cB p.1) := by
    have hwle := (p2WpT F (qMinusExp F) (B.hdepB p.1) (B.cB p.1)).hle p.2
    change weight ((p2WpT F (qMinusExp F) (B.hdepB p.1) (B.cB p.1)).dep p.2)
        ((p2WpT F (qMinusExp F) (B.hdepB p.1) (B.cB p.1)).c p.2) =
      weight 1 (single (qMinusExp F)) + weight (B.depB p.1) (B.cB p.1)
    rw [weight_single]
    exact hwle.1
  rw [hwm1]
  -- B.cB p.1 = iterate-1 b: expand its weight by the same two-step
  have hcB1 : B.cB p.1 = consVec oneExp ((p2WpT F (qMinusExp F)
      ((toData F R0).hdepB p.1.1) ((toData F R0).cB p.1.1)).c p.1.2) := by
    dsimp [B]
    rfl
  have hwB : weight (B.depB p.1) (B.cB p.1) = (oneExp : ℕ) + weight ((p2WpT F (qMinusExp F)
      ((toData F R0).hdepB p.1.1) ((toData F R0).cB p.1.1)).dep p.1.2)
        ((p2WpT F (qMinusExp F) ((toData F R0).hdepB p.1.1) ((toData F R0).cB p.1.1)).c p.1.2) := by
    rw [hcB1]
    change weight ((p2WpT F (qMinusExp F) ((toData F R0).hdepB p.1.1) ((toData F R0).cB p.1.1)).dep p.1.2 + 1)
        (consVec oneExp ((p2WpT F (qMinusExp F) ((toData F R0).hdepB p.1.1) ((toData F R0).cB p.1.1)).c p.1.2)) =
      (oneExp : ℕ) + weight ((p2WpT F (qMinusExp F) ((toData F R0).hdepB p.1.1) ((toData F R0).cB p.1.1)).dep p.1.2)
        ((p2WpT F (qMinusExp F) ((toData F R0).hdepB p.1.1) ((toData F R0).cB p.1.1)).c p.1.2)
    exact weight_consVec oneExp ((p2WpT F (qMinusExp F) ((toData F R0).hdepB p.1.1) ((toData F R0).cB p.1.1)).c p.1.2)
  rw [hwB]
  have hwm0 : weight ((p2WpT F (qMinusExp F) ((toData F R0).hdepB p.1.1) ((toData F R0).cB p.1.1)).dep p.1.2)
        ((p2WpT F (qMinusExp F) ((toData F R0).hdepB p.1.1) ((toData F R0).cB p.1.1)).c p.1.2) =
      (qMinusExp F : ℕ) + weight ((toData F R0).depB p.1.1) ((toData F R0).cB p.1.1) := by
    have hwle := (p2WpT F (qMinusExp F) ((toData F R0).hdepB p.1.1) ((toData F R0).cB p.1.1)).hle p.1.2
    change weight ((p2WpT F (qMinusExp F) ((toData F R0).hdepB p.1.1) ((toData F R0).cB p.1.1)).dep p.1.2)
        ((p2WpT F (qMinusExp F) ((toData F R0).hdepB p.1.1) ((toData F R0).cB p.1.1)).c p.1.2) =
      weight 1 (single (qMinusExp F)) + weight ((toData F R0).depB p.1.1) ((toData F R0).cB p.1.1)
    rw [weight_single]
    exact hwle.1
  rw [hwm0]
  -- weight (R0.cB j) = psum s r − psum s 2
  have hcbw : weight ((toData F R0).depB p.1.1) ((toData F R0).cB p.1.1) = psum s r - psum s 2 := by
    have hwt := weight_head_tail (R0.hdepB p.1.1) (R0.cB p.1.1)
    have hh : (((R0.cB p.1.1) ⟨0, (R0.hdepB p.1.1)⟩ : ℕ)) = 1 := by
      exact hbhd p.1.1
    rw [hh] at hwt
    have hX0 := hXw p.1.1
    change weight (R0.depB p.1.1 - 1) (expTail (R0.cB p.1.1)) = psum s r - psum s 2 - 1 at hX0
    rw [hX0] at hwt
    change weight (R0.depB p.1.1) (R0.cB p.1.1) = psum s r - psum s 2
    have hW : psum s 2 + 1 ≤ psum s r := by
      have hp3 := psum_mono s (by omega : 3 ≤ r)
      have hp2v : psum s 2 + 1 ≤ psum s 3 := by
        have hpl := psum_last r s 3 (by omega : 1 ≤ 3) hcase
        -- psum s 3 = psum s (3-1) + (s⟨2⟩:ℕ)
        have hp3' : psum s 3 = psum s 2 + (s ⟨2, by omega⟩ : ℕ) := by
          simpa using hpl
        rw [hp3']
        have hs2 : 1 ≤ (s ⟨2, by omega⟩ : ℕ) := (s ⟨2, by omega⟩).pos
        omega
      omega
    omega
  rw [hcbw]
  -- arithmetic: 1 + (q−1) + (1 + (q−1) + (psum r − psum 2)) = psum r, since psum s 2 = 2q
  have hpsr : psum s r = weight r s := psum_self s
  have hps2 : psum s 2 = 2 * (qExp F : ℕ) := by
    have hp : psum s 2 = pad0 s 0 + pad0 s 1 := by
      change (∑ j ∈ Finset.range 2, pad0 s j) = pad0 s 0 + pad0 s 1
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      simp
    rw [hp]
    have hp0 : pad0 s 0 = (s ⟨0, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 0 < r)
    have hp1 : pad0 s 1 = (s ⟨1, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 1 < r)
    rw [hp0, hp1]
    have hq : (qExp F : ℕ) = Nat.card F := by rfl
    rw [hs0, hs1]
    rw [hq]
    omega
  have hOne : (oneExp : ℕ) = 1 := by rfl
  have hqm : (qMinusExp F : ℕ) = Nat.card F - 1 := by rfl
  have hq : (qExp F : ℕ) = Nat.card F := by rfl
  rw [hOne, hqm, hps2]
  rw [← hpsr]
  change 1 + (Nat.card F - 1 + (1 + (Nat.card F - 1 + (psum s r - 2 * Nat.card F)))) = psum s r
  have hq0 : (qExp F : ℕ) = Nat.card F := by rfl
  have hle2 : 2 * Nat.card F ≤ psum s r := by
    calc
      2 * Nat.card F = psum s 2 := by rw [← hq0, ← hps2]
      _ ≤ psum s r := psum_mono s (by omega : 2 ≤ r)
  have hq2 : 2 ≤ Nat.card F := card_ge_two F
  omega

/-! ## SESSION 240 — b-side member facts of the level-3 j=0 chain (step probes). -/

/-- entry-0 of the iterate-2 b-member is the head 1. -/
lemma b2_entry0 (R0 : BinaryRel F) (u : R0.ιA) :
    let D := RelData.BCqIter F 2 (toData F R0)
    ∀ p : D.ιB, pad0 (D.cB p) 0 = 1 := by
  classical
  intro D p
  have hd0 : 0 < D.depB p := D.hdepB p
  rw [pad0_of_lt (D.cB p) hd0]
  have hcv : (D.cB p) ⟨0, hd0⟩ = oneExp := by rfl
  rw [hcv]
  rfl

/-- the head of the iterate-1 b-tuple (input to X₂) is 1. -/
lemma b1_head (R0 : BinaryRel F) :
    let B := RelData.BCqIter F 1 (toData F R0)
    ∀ p : B.ιB, ((B.cB p) ⟨0, B.hdepB p⟩ : ℕ) = 1 := by
  classical
  intro B p
  have hf : B.cB p = consVec oneExp ((p2WpT F (qMinusExp F)
      ((toData F R0).hdepB p.1) ((toData F R0).cB p.1)).c p.2) := by
    dsimp [B]
    rfl
  rw [hf]
  rfl


/-- entry-1 of the iterate-2 b-member (the X₂-fiber head) is ≤ q. -/
lemma b2_entry1_le_q (R0 : BinaryRel F) :
    let D := RelData.BCqIter F 2 (toData F R0)
    ∀ p : D.ιB, pad0 (D.cB p) 1 ≤ Nat.card F := by
  classical
  intro D p
  let B := RelData.BCqIter F 1 (toData F R0)
  let X₂ := p2WpT F (qMinusExp F) (B.hdepB p.1) (B.cB p.1)
  have hd1 : 1 < D.depB p := D.hB2 p
  rw [pad0_of_lt (D.cB p) hd1]
  have hv : (D.cB p) ⟨1, hd1⟩ = (X₂.c p.2) ⟨0, X₂.hdep p.2⟩ := by rfl
  rw [hv]
  have hle1 := (X₂.hle p.2).2 1
  have hsumL : psum (X₂.c p.2) 1 =
      ((X₂.c p.2) ⟨0, X₂.hdep p.2⟩ : ℕ) := by
    rw [psum_succ, psum_zero]
    simp
    rw [pad0_of_lt (X₂.c p.2) (X₂.hdep p.2)]
  have hsumR : psumSeq (tupPadSum (single (qMinusExp F)) (B.cB p.1)) 1 =
      (qMinusExp F : ℕ) + ((B.cB p.1) ⟨0, B.hdepB p.1⟩ : ℕ) := by
    dsimp [psumSeq, tupPadSum]
    change pad0 (single (qMinusExp F)) 0 + pad0 (B.cB p.1) 0 =
      (qMinusExp F : ℕ) + ((B.cB p.1) ⟨0, B.hdepB p.1⟩ : ℕ)
    rw [pad0_single_zero]
    rw [pad0_of_lt (B.cB p.1) (B.hdepB p.1)]
  have hBhead : ((B.cB p.1) ⟨0, B.hdepB p.1⟩ : ℕ) = 1 := by
    have hf : B.cB p.1 = consVec oneExp ((p2WpT F (qMinusExp F)
        ((toData F R0).hdepB p.1.1) ((toData F R0).cB p.1.1)).c p.1.2) := by
      rfl
    rw [hf]
    rfl
  calc
    ((X₂.c p.2) ⟨0, X₂.hdep p.2⟩ : ℕ) = psum (X₂.c p.2) 1 := hsumL.symm
    _ ≤ psumSeq (tupPadSum (single (qMinusExp F)) (B.cB p.1)) 1 := hle1
    _ = (qMinusExp F : ℕ) + ((B.cB p.1) ⟨0, B.hdepB p.1⟩ : ℕ) := hsumR
    _ = Nat.card F := by
          have hq : (qMinusExp F : ℕ) = Nat.card F - 1 := rfl
          rw [hq, hBhead]
          have h2 : 2 ≤ Nat.card F := card_ge_two F
          omega




/-- ★ b-side members of the k=3 j=0 chain are 2-admissible (entry-0 = 1, entry-1 ≤ q;
the depth-2 (·,q) form is killed by weight = w > 2q). -/
theorem g53c1_bSide_twoAdm (r : ℕ) (s : Fin r → ℕ+) (hcase : 3 ≤ r)
    (hs0 : (s ⟨0, by omega⟩ : ℕ) = Nat.card F)
    (hs1 : (s ⟨1, by omega⟩ : ℕ) = Nat.card F)
    (hbig : (Nat.card F : ℕ) < (s ⟨2, by omega⟩ : ℕ))
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1)
    (hXw : ∀ j' : R0.ιB, weight (R0.depB j' - 1) (expTail (R0.cB j')) =
      psum s r - psum s (3 - 1) - 1) :
    let D := RelData.BCqIter F 2 (toData F R0)
    ∀ p : D.ιB, kAdmissible (Nat.card F) (D.cB p) 2 := by
  classical
  intro D p
  constructor
  · intro x hx
    have hx01 : x = 0 ∨ x = 1 := by omega
    rcases hx01 with hx0 | hx1
    · subst x
      have hd0 : 0 < D.depB p := D.hdepB p
      rw [pad0_of_lt (D.cB p) hd0]
      have hv : (D.cB p) ⟨0, hd0⟩ = oneExp := by rfl
      rw [hv]
      have hq1 : 1 ≤ Nat.card F := by
        have h2 : 2 ≤ Nat.card F := card_ge_two F
        omega
      change (1 : ℕ) ≤ Nat.card F
      exact hq1
    · subst x
      exact b2_entry1_le_q F R0 p
  · intro hform
    rcases hform with ⟨hr1, hdep2, hall, hlast⟩
    -- weight ≤ q + 1 (witness depth ≤ 2, entries 1 and ≤ q)
    have hwtle : weight (D.depB p) (D.cB p) ≤ Nat.card F + 1 := by
      have hd0 : 0 < D.depB p := D.hdepB p
      have hp0 : pad0 (D.cB p) 0 = 1 := by
        rw [pad0_of_lt (D.cB p) hd0]
        have hv : (D.cB p) ⟨0, hd0⟩ = oneExp := by rfl
        rw [hv]
        rfl
      have he1 : pad0 (D.cB p) 1 ≤ Nat.card F := by
        simpa using (b2_entry1_le_q F R0 p)
      calc
        weight (D.depB p) (D.cB p) = psum (D.cB p) (D.depB p) := (psum_self (D.cB p)).symm
        _ ≤ psum (D.cB p) 2 := psum_mono (D.cB p) hdep2
        _ = pad0 (D.cB p) 0 + pad0 (D.cB p) 1 := by
              change (∑ j ∈ Finset.range 2, pad0 (D.cB p) j) = pad0 (D.cB p) 0 + pad0 (D.cB p) 1
              rw [Finset.sum_range_succ]
              rw [Finset.sum_range_succ]
              simp
        _ ≤ Nat.card F + 1 := by
              rw [hp0]
              omega
    have hwt := g53c1_bSide_weight F r s hcase hs0 hs1 hbig R0 hbhd hXw p
    -- weight = w > 2q ≥ q + 2 : contradiction with weight ≤ q + 1
    have hwbig : 2 * Nat.card F + 1 ≤ weight r s := by
      have hmono : psum s 3 ≤ psum s r := psum_mono s hcase
      have hq0 : (qExp F : ℕ) = Nat.card F := by rfl
      have hps3v : psum s 3 = (qExp F : ℕ) + (qExp F : ℕ) + (s ⟨2, by omega⟩ : ℕ) := by
        change (∑ j ∈ Finset.range 3, pad0 s j) =
          (qExp F : ℕ) + (qExp F : ℕ) + (s ⟨2, by omega⟩ : ℕ)
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
        simp
        rw [pad0_of_lt s (by omega : 0 < r)]
        rw [pad0_of_lt s (by omega : 1 < r)]
        rw [pad0_of_lt s (by omega : 2 < r)]
        rw [hs0, hs1]
        rw [hq0]
      have hp3 : 2 * Nat.card F + 1 ≤ psum s 3 := by
        rw [hps3v]
        rw [hq0]
        have hbig' : Nat.card F < (s ⟨2, by omega⟩ : ℕ) := hbig
        omega
      have hpsr : psum s r = weight r s := psum_self s
      omega
    have hw' : weight (D.depB p) (D.cB p) = weight r s := hwt
    have hq2 : 2 ≤ Nat.card F := card_ge_two F
    omega

/-- entry-1 of the iterate-1 b-member (the X₁-fiber head) is ≤ q (needs hbhd). -/
lemma b1_entry1_le_q (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let B := RelData.BCqIter F 1 (toData F R0)
    ∀ p : B.ιB, pad0 (B.cB p) 1 ≤ Nat.card F := by
  classical
  intro B p
  let X₁ := p2WpT F (qMinusExp F) ((toData F R0).hdepB p.1) ((toData F R0).cB p.1)
  have hd1 : 1 < B.depB p := B.hB2 p
  rw [pad0_of_lt (B.cB p) hd1]
  have hv : (B.cB p) ⟨1, hd1⟩ = (X₁.c p.2) ⟨0, X₁.hdep p.2⟩ := by rfl
  rw [hv]
  have hle1 := (X₁.hle p.2).2 1
  have hsumL : psum (X₁.c p.2) 1 =
      ((X₁.c p.2) ⟨0, X₁.hdep p.2⟩ : ℕ) := by
    rw [psum_succ, psum_zero]
    simp
    rw [pad0_of_lt (X₁.c p.2) (X₁.hdep p.2)]
  have hsumR : psumSeq (tupPadSum (single (qMinusExp F)) ((toData F R0).cB p.1)) 1 =
      (qMinusExp F : ℕ) + (((toData F R0).cB p.1) ⟨0, (toData F R0).hdepB p.1⟩ : ℕ) := by
    dsimp [psumSeq, tupPadSum]
    change pad0 (single (qMinusExp F)) 0 + pad0 ((toData F R0).cB p.1) 0 =
      (qMinusExp F : ℕ) + (((toData F R0).cB p.1) ⟨0, (toData F R0).hdepB p.1⟩ : ℕ)
    rw [pad0_single_zero]
    rw [pad0_of_lt ((toData F R0).cB p.1) ((toData F R0).hdepB p.1)]
  have hR0head : (((toData F R0).cB p.1) ⟨0, (toData F R0).hdepB p.1⟩ : ℕ) = 1 := by
    change (((R0.cB p.1) ⟨0, R0.hdepB p.1⟩ : ℕ)) = 1
    exact hbhd p.1
  calc
    ((X₁.c p.2) ⟨0, X₁.hdep p.2⟩ : ℕ) = psum (X₁.c p.2) 1 := hsumL.symm
    _ ≤ psumSeq (tupPadSum (single (qMinusExp F)) ((toData F R0).cB p.1)) 1 := hle1
    _ = (qMinusExp F : ℕ) + (((toData F R0).cB p.1) ⟨0, (toData F R0).hdepB p.1⟩ : ℕ) := hsumR
    _ = Nat.card F := by
          have hq : (qMinusExp F : ℕ) = Nat.card F - 1 := rfl
          rw [hq, hR0head]
          have h2 : 2 ≤ Nat.card F := card_ge_two F
          omega

/-- ★ b-side members of the k=3 j=0 chain have STRICT prefix-3 drop:
psum (D.cB p) 3 < psum s 3. -/
theorem g53c1_bSide_prefix_drop (r : ℕ) (s : Fin r → ℕ+) (hcase : 3 ≤ r)
    (hs0 : (s ⟨0, by omega⟩ : ℕ) = Nat.card F)
    (hs1 : (s ⟨1, by omega⟩ : ℕ) = Nat.card F)
    (hbig : (Nat.card F : ℕ) < (s ⟨2, by omega⟩ : ℕ))
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F 2 (toData F R0)
    ∀ p : D.ιB, psum (D.cB p) 3 < psum s 3 := by
  classical
  intro D p
  let B := RelData.BCqIter F 1 (toData F R0)
  let X₂ := p2WpT F (qMinusExp F) (B.hdepB p.1) (B.cB p.1)
  -- psum (D.cB p) 3 = 1 + psum (X₂.c p.2) 2
  have hsplit : psum (D.cB p) 3 = (1 : ℕ) + psum (X₂.c p.2) 2 := by
    have hc : psum (D.cB p) 3 = psum (consVec oneExp (X₂.c p.2)) 3 := by rfl
    rw [hc]
    have hpc := psum_consVec oneExp (X₂.c p.2) 2
    -- hpc : psum (consVec oneExp (X₂.c p.2)) (2+1) = 1 + psum (X₂.c p.2) 2
    have h23 : 2 + 1 = 3 := by omega
    rw [h23] at hpc
    rw [hpc]
    change (1 : ℕ) + psum (X₂.c p.2) 2 = (1 : ℕ) + psum (X₂.c p.2) 2
    rfl
  -- psum (X₂.c p.2) 2 ≤ (q−1) + psum (B.cB p.1) 2  (X₂.hle at m=2)
  have hXle : psum (X₂.c p.2) 2 ≤ (qMinusExp F : ℕ) + psum (B.cB p.1) 2 := by
    have hle := (X₂.hle p.2).2 2
    have hsplit' : psumSeq (tupPadSum (single (qMinusExp F)) (B.cB p.1)) 2 =
        (qMinusExp F : ℕ) + psum (B.cB p.1) 2 := by
      rw [psumSeq_tupPadSum_split (single (qMinusExp F)) (B.cB p.1) 2]
      -- psum (single qMinus) 2 = qMinus
      have hsa : psum (single (qMinusExp F)) 2 = (qMinusExp F : ℕ) := by
        change (∑ j ∈ Finset.range 2, pad0 (single (qMinusExp F)) j) = (qMinusExp F : ℕ)
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        simp
        rw [pad0_single_zero]
        have hp1 : pad0 (single (qMinusExp F)) 1 = 0 := pad0_of_ge (single (qMinusExp F)) (by omega : 1 ≤ 1)
        rw [hp1]
        simp
      rw [hsa]
    rw [hsplit'] at hle
    exact hle
  -- psum (B.cB p.1) 2 ≤ 1 + q  (entry-0 = 1, entry-1 ≤ q)
  have hBle : psum (B.cB p.1) 2 ≤ (1 : ℕ) + Nat.card F := by
    have hB0 : pad0 (B.cB p.1) 0 = 1 := by
      have hd0 : 0 < B.depB p.1 := B.hdepB p.1
      rw [pad0_of_lt (B.cB p.1) hd0]
      have hv : (B.cB p.1) ⟨0, hd0⟩ = oneExp := by rfl
      rw [hv]
      rfl
    have hB1 : pad0 (B.cB p.1) 1 ≤ Nat.card F := b1_entry1_le_q F R0 hbhd p.1
    have hps2 : psum (B.cB p.1) 2 = pad0 (B.cB p.1) 0 + pad0 (B.cB p.1) 1 := by
      change (∑ j ∈ Finset.range 2, pad0 (B.cB p.1) j) = pad0 (B.cB p.1) 0 + pad0 (B.cB p.1) 1
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      simp
    rw [hps2]
    rw [hB0]
    omega
  -- assemble: psum (D.cB p) 3 ≤ 1 + (q−1) + (1 + q) = 2q + 1
  have hps3 : psum (D.cB p) 3 ≤ Nat.card F + (Nat.card F + 1) := by
    rw [hsplit]
    have hq : (qMinusExp F : ℕ) = Nat.card F - 1 := rfl
    have hq2 : 2 ≤ Nat.card F := card_ge_two F
    omega
  -- psum s 3 = 2q + s₂ ≥ 3q + 1 > 2q + 1
  have hps3s : Nat.card F + (Nat.card F + 1) < psum s 3 := by
    have hq0 : (qExp F : ℕ) = Nat.card F := by rfl
    have hps3v : psum s 3 = (qExp F : ℕ) + (qExp F : ℕ) + (s ⟨2, by omega⟩ : ℕ) := by
      change (∑ j ∈ Finset.range 3, pad0 s j) =
        (qExp F : ℕ) + (qExp F : ℕ) + (s ⟨2, by omega⟩ : ℕ)
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
      simp
      rw [pad0_of_lt s (by omega : 0 < r)]
      rw [pad0_of_lt s (by omega : 1 < r)]
      rw [pad0_of_lt s (by omega : 2 < r)]
      rw [hs0, hs1]
      rw [hq0]
    rw [hps3v]
    rw [hq0]
    have hbig' : Nat.card F < (s ⟨2, by omega⟩ : ℕ) := hbig
    have hq1 : 1 ≤ Nat.card F := by
      have h2 : 2 ≤ Nat.card F := card_ge_two F
      omega
    omega
  omega

/-! ## SESSION 241 — the g53 member ℓ ≥ 3 orders (the flagged order item).

a-side order: D.cA i = (q,q,R0.cA i) so psum ℓ = 2q + psum(R0.cA i)(ℓ−2); the
level-0 prefix bound hpref (from the config's hleA over the concrete w1Of/sTail
reference) + lemma29_qExp_telescope at k=3 give psum(R0.cA)(ℓ−2) ≤ s⟨2⟩ + psum s ℓ
− psum s 3; with psum s 3 = 2q + s⟨2⟩ the member prefix ≤ psum s ℓ. -/

/-- psum (consVec x t) ℓ = x + psum t (ℓ−1) (from StepL50). -/
lemma psum_consVec_sub_one' (x : ℕ+) {m : ℕ} (t : Fin m → ℕ+) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    psum (consVec x t) ℓ = (x : ℕ) + psum t (ℓ - 1) := by
  exact psum_consVec_sub_one x t ℓ hℓ

/-- a-side members (i ≠ u) of the k=3 j=0 chain: psum ℓ ≤ psum s ℓ for ℓ ≥ 3. -/
theorem g53c1_aSide_order (r : ℕ) (s : Fin r → ℕ+) (hcase3 : 3 ≤ r)
    (hs0v : (s ⟨0, by omega⟩ : ℕ) = Nat.card F)
    (hs1v : (s ⟨1, by omega⟩ : ℕ) = Nat.card F)
    (hbigv : (Nat.card F : ℕ) < (s ⟨2, by omega⟩ : ℕ))
    (R0 : BinaryRel F) (u : R0.ιA)
    (hpref : ∀ i : R0.ιA, i ≠ u → ∀ m : ℕ,
      psum (R0.cA i) m ≤ psumSeq (tupPadSum (single (qExp F))
        (consVec (w1Of F r s 3 (by omega : 1 ≤ 3) hcase3 hbigv) (sTail r s 3 hcase3))) m) :
    let D := RelData.BCqIter F 2 (toData F R0)
    ∀ i : R0.ιA, i ≠ u → ∀ ℓ : ℕ, 3 ≤ ℓ → psum (D.cA i) ℓ ≤ psum s ℓ := by
  classical
  intro D i hi ℓ hℓ3
  have hcA : D.cA i = consVec (qExp F) (consVec (qExp F) (R0.cA i)) := by
    dsimp [D, RelData.BCqIter, RelData.BCq]
    rfl
  -- psum (D.cA i) ℓ = 2q + psum (R0.cA i) (ℓ − 2)
  have hsplit : psum (D.cA i) ℓ = (qExp F : ℕ) + ((qExp F : ℕ) + psum (R0.cA i) (ℓ - 2)) := by
    change psum (consVec (qExp F) (consVec (qExp F) (R0.cA i))) ℓ =
      (qExp F : ℕ) + ((qExp F : ℕ) + psum (R0.cA i) (ℓ - 2))
    have hℓ1 : ℓ = (ℓ - 1) + 1 := by omega
    rw [hℓ1]
    rw [psum_consVec (qExp F) (consVec (qExp F) (R0.cA i)) (ℓ - 1)]
    have hℓ2 : ℓ - 1 = (ℓ - 2) + 1 := by omega
    rw [hℓ2]
    rw [psum_consVec (qExp F) (R0.cA i) (ℓ - 2)]
    rfl
  -- the reference bound
  have hpre := hpref i hi (ℓ - 2)
  have htel := lemma29_qExp_telescope F r s 3 (by omega : 1 ≤ 3) hcase3 hbigv (ℓ - 2) (by omega : 1 ≤ ℓ - 2)
  -- htel : psumSeq (tupPadSum (single qExp)(consVec (w1Of) (sTail))) (ℓ−2) = s⟨2⟩ + (psum s (3+(ℓ−2)−1) − psum s 3)
  have htel' : psumSeq (tupPadSum (single (qExp F))
        (consVec (w1Of F r s 3 (by omega : 1 ≤ 3) hcase3 hbigv) (sTail r s 3 hcase3))) (ℓ - 2) =
      (s ⟨2, by omega⟩ : ℕ) + (psum s ℓ - psum s 3) := by
    rw [htel]
    congr 1
    have hidx : 3 + (ℓ - 2) - 1 = ℓ := by omega
    rw [hidx]
  have hb : psum (R0.cA i) (ℓ - 2) ≤ (s ⟨2, by omega⟩ : ℕ) + (psum s ℓ - psum s 3) := by
    rw [← htel']
    exact hpre
  -- psum s 3 = 2q + s⟨2⟩
  have hp3 : psum s 3 = (qExp F : ℕ) + (qExp F : ℕ) + (s ⟨2, by omega⟩ : ℕ) := by
    change (∑ j ∈ Finset.range 3, pad0 s j) =
      (qExp F : ℕ) + (qExp F : ℕ) + (s ⟨2, by omega⟩ : ℕ)
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    simp
    rw [pad0_of_lt s (by omega : 0 < r)]
    rw [pad0_of_lt s (by omega : 1 < r)]
    rw [pad0_of_lt s (by omega : 2 < r)]
    rw [hs0v, hs1v]
    rw [← show (qExp F : ℕ) = Nat.card F by rfl]
  rw [hsplit]
  have hq : (qExp F : ℕ) = Nat.card F := by rfl
  have hmono : psum s 3 ≤ psum s ℓ := psum_mono s (by omega : 3 ≤ ℓ)
  omega


theorem g53c1_bSide_order (r : ℕ) (s : Fin r → ℕ+) (hcase3 : 3 ≤ r)
    (hs0v : (s ⟨0, by omega⟩ : ℕ) = Nat.card F)
    (hs1v : (s ⟨1, by omega⟩ : ℕ) = Nat.card F)
    (hbigv : (Nat.card F : ℕ) < (s ⟨2, by omega⟩ : ℕ))
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1)
    (hbndB : ∀ j' : R0.ιB, ∀ m : ℕ,
      psum (expTail (R0.cB j')) m ≤ psumSeq (tupPadSum (single (qMinusExp F))
        (consVec (w1Of F r s 3 (by omega : 1 ≤ 3) hcase3 hbigv) (sTail r s 3 hcase3))) m) :
    let D := RelData.BCqIter F 2 (toData F R0)
    ∀ p : D.ιB, ∀ ℓ : ℕ, 3 ≤ ℓ → psum (D.cB p) ℓ ≤ psum s ℓ := by
  classical
  intro D p ℓ hℓ3
  by_cases hℓ3e : ℓ = 3
  · subst ℓ
    have hdrop' : psum (D.cB p) 3 < psum s 3 := by
      simpa using (g53c1_bSide_prefix_drop F r s hcase3 hs0v hs1v hbigv R0 hbhd p)
    omega
  · -- ℓ ≥ 4
    have hℓ4 : 4 ≤ ℓ := by omega
    let B := RelData.BCqIter F 1 (toData F R0)
    let X₂ := p2WpT F (qMinusExp F) (B.hdepB p.1) (B.cB p.1)
    -- layer X₂: psum(D.cB)ℓ = 1 + psum(X₂.c)(ℓ−1)
    have hL2 : psum (D.cB p) ℓ = (1 : ℕ) + psum (X₂.c p.2) (ℓ - 1) := by
      change psum (consVec oneExp (X₂.c p.2)) ℓ = (1 : ℕ) + psum (X₂.c p.2) (ℓ - 1)
      have hℓ1 : ℓ = (ℓ - 1) + 1 := by omega
      rw [hℓ1]
      rw [psum_consVec oneExp (X₂.c p.2) (ℓ - 1)]
      rfl
    have hL2le : psum (X₂.c p.2) (ℓ - 1) ≤
        psumSeq (tupPadSum (single (qMinusExp F)) (B.cB p.1)) (ℓ - 1) := by
      exact (X₂.hle p.2).2 (ℓ - 1)
    -- psumSeq (tupPadSum (single qMinus) (B.cB p.1)) (ℓ−1) = (q−1) + psum (B.cB p.1) (ℓ−1)
    have hsplit2 : psumSeq (tupPadSum (single (qMinusExp F)) (B.cB p.1)) (ℓ - 1) =
        (qMinusExp F : ℕ) + psum (B.cB p.1) (ℓ - 1) := by
      rw [psumSeq_tupPadSum_split (single (qMinusExp F)) (B.cB p.1) (ℓ - 1)]
      have hsa : psum (single (qMinusExp F)) (ℓ - 1) = (qMinusExp F : ℕ) := by
        exact psum_single_of_pos (qMinusExp F) (by omega : 0 < ℓ - 1)
      rw [hsa]
    -- layer X₁: psum(B.cB p.1)(ℓ−1) = 1 + psum(X₁.c)(ℓ−2)
    let X₁ := p2WpT F (qMinusExp F) ((toData F R0).hdepB p.1.1) ((toData F R0).cB p.1.1)
    have hBcB : B.cB p.1 = consVec oneExp (X₁.c p.1.2) := by
      dsimp [B, X₁]
      rfl
    have hL1 : psum (B.cB p.1) (ℓ - 1) = (1 : ℕ) + psum (X₁.c p.1.2) (ℓ - 2) := by
      change psum (consVec oneExp (X₁.c p.1.2)) (ℓ - 1) =
        (1 : ℕ) + psum (X₁.c p.1.2) (ℓ - 2)
      have hℓ2 : ℓ - 1 = (ℓ - 2) + 1 := by omega
      rw [hℓ2]
      rw [psum_consVec oneExp (X₁.c p.1.2) (ℓ - 2)]
      rfl
    have hL1le : psum (X₁.c p.1.2) (ℓ - 2) ≤
        psumSeq (tupPadSum (single (qMinusExp F)) ((toData F R0).cB p.1.1)) (ℓ - 2) := by
      exact (X₁.hle p.1.2).2 (ℓ - 2)
    have hsplit1 : psumSeq (tupPadSum (single (qMinusExp F)) ((toData F R0).cB p.1.1)) (ℓ - 2) =
        (qMinusExp F : ℕ) + psum ((toData F R0).cB p.1.1) (ℓ - 2) := by
      rw [psumSeq_tupPadSum_split (single (qMinusExp F)) ((toData F R0).cB p.1.1) (ℓ - 2)]
      have hsa : psum (single (qMinusExp F)) (ℓ - 2) = (qMinusExp F : ℕ) := by
        exact psum_single_of_pos (qMinusExp F) (by omega : 0 < ℓ - 2)
      rw [hsa]
    -- psum(R0.cB)(ℓ−2) = 1 + psum(expTail)(ℓ−3)
    have hR0 : psum ((toData F R0).cB p.1.1) (ℓ - 2) =
        (1 : ℕ) + psum (expTail (R0.cB p.1.1)) (ℓ - 3) := by
      have hh := psum_head_expTail ((toData F R0).hdepB p.1.1) ((toData F R0).cB p.1.1) (ℓ - 3)
      -- hh : psum t ((ℓ−3)+1) = head + psum (expTail t)(ℓ−3)
      have hℓ3' : (ℓ - 3) + 1 = ℓ - 2 := by omega
      rw [hℓ3'] at hh
      have hhead : (((toData F R0).cB p.1.1) ⟨0, (toData F R0).hdepB p.1.1⟩ : ℕ) = 1 := by
        change (((R0.cB p.1.1) ⟨0, R0.hdepB p.1.1⟩ : ℕ)) = 1
        exact hbhd p.1.1
      rw [hh, hhead]
      congr 1
    -- expTail bound via hbndB + X-telescope
    have hbnd := hbndB p.1.1 (ℓ - 3)
    have htel := lemma29_X_telescope F r s 3 (by omega : 1 ≤ 3) hcase3 hbigv (ℓ - 3) (by omega : 1 ≤ ℓ - 3)
    have htel' : psumSeq (tupPadSum (single (qMinusExp F))
          (consVec (w1Of F r s 3 (by omega : 1 ≤ 3) hcase3 hbigv) (sTail r s 3 hcase3))) (ℓ - 3) =
        ((s ⟨2, by omega⟩ : ℕ) - 1) + (psum s (ℓ - 1) - psum s 3) := by
      rw [htel]
      congr 1
      have hidx : 3 + (ℓ - 3) - 1 = ℓ - 1 := by omega
      rw [hidx]
    have hEt : psum (expTail ((toData F R0).cB p.1.1)) (ℓ - 3) ≤
        ((s ⟨2, by omega⟩ : ℕ) - 1) + (psum s (ℓ - 1) - psum s 3) := by
      rw [← htel']
      exact hbnd
    -- psum s 3 = 2q + s⟨2⟩
    have hp3 : psum s 3 = (qExp F : ℕ) + (qExp F : ℕ) + (s ⟨2, by omega⟩ : ℕ) := by
      change (∑ j ∈ Finset.range 3, pad0 s j) =
        (qExp F : ℕ) + (qExp F : ℕ) + (s ⟨2, by omega⟩ : ℕ)
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
      simp
      rw [pad0_of_lt s (by omega : 0 < r)]
      rw [pad0_of_lt s (by omega : 1 < r)]
      rw [pad0_of_lt s (by omega : 2 < r)]
      rw [hs0v, hs1v]
      rw [← show (qExp F : ℕ) = Nat.card F by rfl]
    -- assemble: psum (D.cB p) ℓ ≤ psum s ℓ via the layered chain
    -- psum(B.cB p.1)(ℓ−1) ≤ 1 + (q−1) + 1 + expTail(ℓ−3)   [B-head 1, X₁, R0-head 1]
    have hB1 : psum (B.cB p.1) (ℓ - 1) ≤
        (1 : ℕ) + (qMinusExp F : ℕ) + (1 : ℕ) + psum (expTail (R0.cB p.1.1)) (ℓ - 3) := by
      calc
        psum (B.cB p.1) (ℓ - 1) = (1 : ℕ) + psum (X₁.c p.1.2) (ℓ - 2) := hL1
        _ ≤ (1 : ℕ) + psumSeq (tupPadSum (single (qMinusExp F)) ((toData F R0).cB p.1.1)) (ℓ - 2) := by
              exact Nat.add_le_add_left hL1le (1 : ℕ)
        _ = (1 : ℕ) + ((qMinusExp F : ℕ) + psum ((toData F R0).cB p.1.1) (ℓ - 2)) := by rw [hsplit1]
        _ = (1 : ℕ) + ((qMinusExp F : ℕ) + ((1 : ℕ) + psum (expTail (R0.cB p.1.1)) (ℓ - 3))) := by rw [hR0]
        _ = (1 : ℕ) + (qMinusExp F : ℕ) + (1 : ℕ) + psum (expTail (R0.cB p.1.1)) (ℓ - 3) := by omega
    -- psum(D.cB p)ℓ ≤ 1 + (q−1) + [hB1-bound] ≤ 1 + (q−1) + 1 + (q−1) + 1 + ((s⟨2⟩−1) + P)
    have hmain : psum (D.cB p) ℓ ≤ psum s (ℓ - 1) := by
      calc
        psum (D.cB p) ℓ = (1 : ℕ) + psum (X₂.c p.2) (ℓ - 1) := hL2
        _ ≤ (1 : ℕ) + psumSeq (tupPadSum (single (qMinusExp F)) (B.cB p.1)) (ℓ - 1) := by
              exact Nat.add_le_add_left hL2le (1 : ℕ)
        _ = (1 : ℕ) + ((qMinusExp F : ℕ) + psum (B.cB p.1) (ℓ - 1)) := by rw [hsplit2]
        _ ≤ (1 : ℕ) + ((qMinusExp F : ℕ) + ((1 : ℕ) + (qMinusExp F : ℕ) + (1 : ℕ) +
              psum (expTail (R0.cB p.1.1)) (ℓ - 3))) := by
              have hle := Nat.add_le_add_left hB1 ((1 : ℕ) + (qMinusExp F : ℕ))
              omega
        _ ≤ (1 : ℕ) + ((qMinusExp F : ℕ) + ((1 : ℕ) + (qMinusExp F : ℕ) + (1 : ℕ) +
              (((s ⟨2, by omega⟩ : ℕ) - 1) + (psum s (ℓ - 1) - psum s 3)))) := by
              have hle := Nat.add_le_add_left (Nat.add_le_add_left hEt ((1 : ℕ) + (qMinusExp F : ℕ))) ((1 : ℕ) + (qMinusExp F : ℕ))
              omega
        _ ≤ psum s (ℓ - 1) := by
              have hq : (qMinusExp F : ℕ) = Nat.card F - 1 := rfl
              have hq0 : (qExp F : ℕ) = Nat.card F := rfl
              have hq2 : 2 ≤ Nat.card F := card_ge_two F
              have hmono2 : psum s 3 ≤ psum s (ℓ - 1) := psum_mono s (by omega : 3 ≤ ℓ - 1)
              have hAbs : (1 : ℕ) + (Nat.card F - 1) + ((1 : ℕ) + (Nat.card F - 1)) + (1 : ℕ) +
                  ((s ⟨2, by omega⟩ : ℕ) - 1) ≤ psum s 3 := by
                rw [hp3]
                rw [hq0]
                omega
              omega
    have hmono' : psum s (ℓ - 1) ≤ psum s ℓ := psum_mono s (by omega : ℓ - 1 ≤ ℓ)
    omega
end ZagierHoffmanPositiveChar
