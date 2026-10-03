import Mathlib
import Submission.Work.Peluse.ladderA_defs

namespace Work.Peluse.LadderA

open Work.Peluse

/-- One step of the peel: the product `x ↦ G (x + a) * conj (G (x + b))` is supported in
`[-(M+B), M+B]` whenever `G` is supported in `[-M, M]` and `|a| ≤ B`.  (Only the shift `a` of the
left factor is needed; the right factor is conjugated, so `b` does not matter for the support.) -/
lemma supportIn_iterDeltaStep {M B : ℕ} {G : ℤ → ℂ} (hG : Work.Peluse.SupportIn G M)
    (a b : ℤ) (ha : a.natAbs ≤ B) :
    Work.Peluse.SupportIn (fun x : ℤ => G (x + a) * star (G (x + b))) (M + B) := by
  intro x hx
  -- `|x| ≤ |x + a| + |a|`, so `|x| > M + B ≥ M + |a|` forces `|x + a| > M`.
  have h1 : x.natAbs ≤ (x + a).natAbs + a.natAbs := by
    have h := Int.natAbs_add_le (x + a) (-a)
    rw [add_neg_cancel_right, Int.natAbs_neg] at h
    exact h
  have hsub : M < (x + a).natAbs := by omega
  simp [hG (x + a) hsub]

/-- The support of the `k`-fold iterated difference stays inside `[-N - kB, N + kB]` once the `k`
shifts have both coordinates bounded by `B`. -/
lemma supportIn_iterDelta_aux (k : ℕ) :
    ∀ (sh : Fin k → ℤ × ℤ) {N B : ℕ} {f : ℤ → ℂ},
      Work.Peluse.SupportIn f N →
      (∀ i : Fin k, (sh i).1.natAbs ≤ B ∧ (sh i).2.natAbs ≤ B) →
      Work.Peluse.SupportIn (Work.Peluse.Ulower.iterDelta k sh f) (N + k * B) := by
  induction k with
  | zero =>
      intro sh N B f hf hB
      simpa [Work.Peluse.Ulower.iterDelta_zero] using hf
  | succ k ih =>
      intro sh N B f hf hB
      have hB' : ∀ i : Fin k, (sh i.succ).1.natAbs ≤ B ∧ (sh i.succ).2.natAbs ≤ B :=
        fun i => hB i.succ
      have hih : Work.Peluse.SupportIn
          (Work.Peluse.Ulower.iterDelta k (fun i : Fin k => sh i.succ) f) (N + k * B) :=
        ih (fun i : Fin k => sh i.succ) hf hB'
      have hstep := supportIn_iterDeltaStep hih (sh 0).1 (sh 0).2 (hB 0).1
      have hcongr : (N + k * B) + B = N + (k + 1) * B := by
        rw [Nat.succ_mul, add_assoc]
      rw [hcongr] at hstep
      rwa [Work.Peluse.Ulower.iterDelta_succ]

theorem supportIn_iterDelta {k : ℕ} (sh : Fin k → ℤ × ℤ) {N B : ℕ} {f : ℤ → ℂ}
    (hf : Work.Peluse.SupportIn f N) (hB : ∀ i : Fin k, (sh i).1.natAbs ≤ B ∧ (sh i).2.natAbs ≤ B) :
    Work.Peluse.SupportIn (Work.Peluse.Ulower.iterDelta k sh f) (N + k * B) :=
  supportIn_iterDelta_aux k sh hf hB

end Work.Peluse.LadderA
