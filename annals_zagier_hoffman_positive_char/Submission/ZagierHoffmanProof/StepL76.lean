import Submission.ZagierHoffmanProof.StepL75
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators
namespace ZagierHoffmanPositiveChar
/-!
# Step L76: the CASE-1 j=0 depth/value bridge (SESSION 226 item (i))

The (q,s₂>q,…,s_r) empty-front chain's u-member is the q-prepend of the tail-from-2
tuple `bstarBase F r s 2` (length (r−2)+1): comparing it to s (length r) hits the
non-defeq depth arithmetic ((r−2)+1+1 vs r).  The transport bridge:
  ★ g5c1_depth_eq : (r−2)+1+1 = r  (2 ≤ r) — the depth equality;
  ★ qprepend_tail_values : ∀ i : Fin ((r−2)+1+1), (consVec qExp (bstarBase …)) i =
      s ⟨(i : ℕ), ·⟩ — the VALUE equality at every position (head = q via hs0;
      tail = sTail⟨m⟩ = s⟨2+m⟩ via bstarBase's consVec structure + sTail's +2 shift;
      `Nat.add_comm 2 m` for the 2+m/m+2 index alignment — omega cannot close the
      Fin-ext without it, and the `Fin.ext`-val goal needs the explicit comm theorem);
  ★ qprepend_tail_zeta : ζ_A(consVec qExp (bstarBase …)) = ζ_A s — the
      u-identification, via ζ_A_eq_of_reindex (Counting.lean) + the value bridge.
The library's `ζ_A_eq_of_reindex` is the existing depth-transport for ζ_A — no new
zeta-transport theory was needed; this module supplies its input (value bridge) for
the CASE-1 j=0 instance.  NEXT: the CASE-1 chain ζ-identity (g5c1_zeta: rcases
lemma_2_9_config_data, D := BCqIter 1 (toData R0), level-sum + a-sum u-split with
this bridge identifying the u-term), then member facts, then the g5 recursion.
-/

attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- arithmetic bridge: the depth of the (q)-prepended tail equals r. -/
lemma g5c1_depth_eq (r : ℕ) (hcase : 2 ≤ r) : (r - 2) + 1 + 1 = r := by omega

/-- ★ the CASE-1 j=0 value bridge: at every position, the (q)-prepend of the
tail-from-2 tuple (bstarBase at k=2) equals s — the `ζ_A_eq_of_reindex` input for
ζ_A(consVec q bstarBase) = ζ_A s (used in the u-identification of the empty-front
chain; Fin-cast-free value form avoids the depth-type mismatch). -/
lemma qprepend_tail_values (r : ℕ) (s : Fin r → ℕ+) (hcase : 2 ≤ r)
    (hs0 : (s ⟨0, by omega⟩ : ℕ) = Nat.card F)
    (hbig : (Nat.card F : ℕ) < (s ⟨1, by omega⟩ : ℕ)) :
    ∀ i : Fin ((r - 2) + 1 + 1),
      (consVec (qExp F) (bstarBase F r s 2 (by omega : 1 ≤ 2) hcase hbig)) i =
        s ⟨(i : ℕ), by
          have h1 := g5c1_depth_eq r hcase
          simpa [h1] using i.isLt⟩ := by
  classical
  intro i
  by_cases hi0 : (i : ℕ) = 0
  · have hii : i = ⟨0, by omega⟩ := Fin.ext (by simpa using hi0)
    rw [hii]
    change (consVec (qExp F) (bstarBase F r s 2 (by omega : 1 ≤ 2) hcase hbig))
        ⟨0, by omega⟩ = s ⟨0, by omega⟩
    rw [consVec_zero (qExp F) (bstarBase F r s 2 (by omega : 1 ≤ 2) hcase hbig)]
    apply Subtype.ext
    change Nat.card F = (s ⟨0, by omega⟩ : ℕ)
    exact hs0.symm
  · let n : ℕ := (i : ℕ) - 1
    have hin : (i : ℕ) = n + 1 := by omega
    have hii : i = ⟨n + 1, by omega⟩ := Fin.ext (by simpa [hin])
    rw [hii]
    change (consVec (qExp F) (bstarBase F r s 2 (by omega : 1 ≤ 2) hcase hbig))
        ⟨n + 1, by omega⟩ = s ⟨n + 1, by omega⟩
    rw [consVec_succ (qExp F) (bstarBase F r s 2 (by omega : 1 ≤ 2) hcase hbig) ⟨n, by omega⟩]
    -- (bstarBase)⟨n⟩ with n < (r-2)+1
    have hnlt : n < (r - 2) + 1 := by
      have hil : n + 1 < (r - 2) + 1 + 1 := by omega
      omega
    by_cases hn0 : n = 0
    · have hnn : (⟨n, hnlt⟩ : Fin ((r - 2) + 1)) = ⟨0, by omega⟩ := by
        apply Fin.ext
        simp [hn0]
      rw [hnn]
      -- (bstarBase)⟨0⟩ = q + w1 = s₂ = s⟨1⟩
      have hbh := bstarBase_head F r s 2 (by omega : 1 ≤ 2) hcase hbig
      -- hbh : (bstarBase)⟨0, 0<r-2+1⟩ = s⟨1, by omega⟩
      simpa [hn0, hin] using hbh
    · -- n ≥ 1: (bstarBase)⟨n⟩ = sTail⟨n-1⟩ = s⟨n+1⟩
      let m : ℕ := n - 1
      have hnm : n = m + 1 := by omega
      have hmlt : m < r - 2 := by
        have : n < (r - 2) + 1 := hnlt
        omega
      have hmm : (⟨n, hnlt⟩ : Fin ((r - 2) + 1)) = ⟨m + 1, by omega⟩ := by
        apply Fin.ext
        simp [hnm]
      rw [hmm]
      -- bstarBase = consVec ⟨q+w1⟩ (sTail) : value at m+1 = sTail⟨m⟩
      have hb : (bstarBase F r s 2 (by omega : 1 ≤ 2) hcase hbig) ⟨m + 1, by omega⟩ =
          (sTail r s 2 hcase) ⟨m, hmlt⟩ := by
        dsimp [bstarBase]
        rw [consVec_succ ⟨(qExp F : ℕ) + (w1Of F r s 2 (by omega : 1 ≤ 2) hcase hbig : ℕ),
          Nat.add_pos_left (PNat.pos (qExp F)) (w1Of F r s 2 (by omega : 1 ≤ 2) hcase hbig : ℕ)⟩
          (sTail r s 2 hcase) ⟨m, by omega⟩]
      rw [hb]
      have hst0 : (sTail r s 2 hcase) ⟨m, hmlt⟩ = s ⟨2 + m, by omega⟩ := by
        dsimp [sTail]
      have hidx : (⟨2 + m, by omega⟩ : Fin r) = ⟨m + 2, by omega⟩ := by
        exact Fin.ext (Nat.add_comm 2 m)
      have hsm : s ⟨2 + m, by omega⟩ = s ⟨m + 2, by omega⟩ := by
        rw [hidx]
      have hst : (sTail r s 2 hcase) ⟨m, hmlt⟩ = s ⟨m + 2, by omega⟩ := by
        rw [hst0, hidx]
      simpa [hnm] using hst

/-- ★ the reindex corollary: ζ_A of the (q)-prepended tail-from-2 equals ζ_A(s) —
the u-identification bridge of the CASE-1 j=0 chain (feeds ζ_A_eq_of_reindex). -/
lemma qprepend_tail_zeta (r : ℕ) (s : Fin r → ℕ+) (hcase : 2 ≤ r)
    (hs0 : (s ⟨0, by omega⟩ : ℕ) = Nat.card F)
    (hbig : (Nat.card F : ℕ) < (s ⟨1, by omega⟩ : ℕ)) :
    ζ_A F (consVec (qExp F) (bstarBase F r s 2 (by omega : 1 ≤ 2) hcase hbig)) = ζ_A F s := by
  classical
  exact ζ_A_eq_of_reindex F (g5c1_depth_eq r hcase)
    (consVec (qExp F) (bstarBase F r s 2 (by omega : 1 ≤ 2) hcase hbig)) s
    (qprepend_tail_values F r s hcase hs0 hbig)

end ZagierHoffmanPositiveChar
