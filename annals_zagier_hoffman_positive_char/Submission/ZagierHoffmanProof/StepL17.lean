import Submission.ZagierHoffmanProof.StepL16

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L17: Prop-2.12 configuration arithmetic

`w1Of r s k …` is the head `s_k − q` of Prop 2.12's `W = (s_k − q, s_{k+1}, …, s_r)`
(positive because `s_k > q`).  `w1Of_add` / `w1Of_add_pnat` record the head
arithmetic `q + (s_k − q) = s_k` — the identity that makes Lemma 2.9's merged head
`(q+w1) :: B` equal the tail `(s_k, …, s_r)` of `s`, and hence (after the whole
BC_q/B*/prefix chain) the leading tuple equal to `s` itself.
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The head `s_k − q` of Prop 2.12's `W`, as a positive natural. -/
noncomputable def w1Of (r : ℕ) (s : Fin r → ℕ+) (k : ℕ) (hk1 : 1 ≤ k) (hkr : k ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ)) : ℕ+ :=
  ⟨(s ⟨k - 1, by omega⟩ : ℕ) - Nat.card F, by
    have hbig' : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ) := hbig
    omega⟩

/-- Head arithmetic: `q + (s_k − q) = s_k` (the merged head value). -/
lemma w1Of_add (r : ℕ) (s : Fin r → ℕ+) (k : ℕ) (hk1 : 1 ≤ k) (hkr : k ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ)) :
    (qExp F : ℕ) + (w1Of F r s k hk1 hkr hbig : ℕ) = (s ⟨k - 1, by omega⟩ : ℕ) := by
  have hq : (qExp F : ℕ) = Nat.card F := by rfl
  have hv : (w1Of F r s k hk1 hkr hbig : ℕ) = (s ⟨k - 1, by omega⟩ : ℕ) - Nat.card F := by rfl
  rw [hq, hv]
  omega

/-- Head arithmetic, PNat form (the merged head tuple entry). -/
lemma w1Of_add_pnat (r : ℕ) (s : Fin r → ℕ+) (k : ℕ) (hk1 : 1 ≤ k) (hkr : k ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ)) :
    (⟨(qExp F : ℕ) + (w1Of F r s k hk1 hkr hbig : ℕ),
        Nat.add_pos_left (PNat.pos (qExp F)) (w1Of F r s k hk1 hkr hbig : ℕ)⟩ : ℕ+) =
      s ⟨k - 1, by omega⟩ := by
  apply Subtype.ext
  exact w1Of_add F r s k hk1 hkr hbig

end ZagierHoffmanPositiveChar
