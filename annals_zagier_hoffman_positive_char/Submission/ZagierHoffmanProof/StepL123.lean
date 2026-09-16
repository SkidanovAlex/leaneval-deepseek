import Submission.ZagierHoffmanProof.StepL122
set_option autoImplicit false
set_option maxHeartbeats 200000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L123: the mixed-type-1 output-level prefix (item (ii), first piece)

At the (k₁,j)-chain of an in-domain-at-k₁ input (its own first-bad index
k₁ ≤ k, output level k ≥ k₁), the type-1 members (i₀ ≠ u) satisfy the
OUTPUT-level prefix bound
    psum (member₁ i₀) ℓ ≤ psum s ℓ      for all k₁ ≤ ℓ ≤ r,
proved by the type1_psum_decompose_ge decomposition (type1_psum_decompose_ge:
psum member ℓ = psum s (k₁−1) + psum (R0.cA i₀) (ℓ−k₁+1)) + the restricted
config hpref (i₀ ≠ u) + the qExp-telescope — with the full-∀-hpref replaced by
the config's i₀ ≠ u version (the only place hpref is used is at the member's
own i₀).  At ℓ = k₁ this is in fact STRICT (type1_psum_lt_k); the ≤ at ℓ > k₁
is what the mixed MainkStep assembly consumes (strictness at the output level
k > k₁ is NOT automatic — the equality case there is item (iii)).

NOTE (SESSION 258m): this is the verbatim port of `type1_psum_ge_k_le`'s body
(StepL48) with (a) the hypothesis `hsj : (s⟨j−1⟩:ℕ) < Nat.card F` added
explicitly (type1_psum_decompose_ge REQUIRES it — it is NOT derivable from the
other config hypotheses), and (b) the FULL-∀-hpref replaced by the (k₁)-
config's restricted i₀ ≠ u version (the only place hpref is used is at the
member's own i₀, where hi₀ supplies the inequality).
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★ The mixed-type-1 output-level prefix: type-1 members (i₀ ≠ u) of the
(k₁,j)-chain satisfy psum (member) ℓ ≤ psum s ℓ for every k₁ ≤ ℓ ≤ r, from the
(k₁)-config's restricted hpref. -/
theorem maink_mixed_type1_le (k₁ r j : ℕ) (s : Fin r → ℕ+) (hk1 : 1 ≤ k₁) (hkr : k₁ ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨k₁ - 1, by omega⟩ : ℕ))
    (hj1 : 1 ≤ j) (hjk : j ≤ k₁ - 1)
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hmid : ∀ i : Fin r, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < k₁ - 1 → (s i : ℕ) = Nat.card F)
    (R0 : BinaryRel F) (u : R0.ιA)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1)
    (hpref : ∀ i₀ : R0.ιA, i₀ ≠ u → ∀ m : ℕ,
      psum (R0.cA i₀) m ≤ psumSeq (tupPadSum (single (qExp F))
        (consVec (w1Of F r s k₁ hk1 hkr hbig) (sTail r s k₁ hkr))) m) :
    let D := RelData.BCqIter F (k₁ - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k₁ - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k₁ - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i₀ : R0.ιA, i₀ ≠ u → ∀ (ℓ : ℕ), k₁ ≤ ℓ → ℓ ≤ r →
      psum (Q.c (Sum.inl (RelData.iterIdx F (k₁ - j - 1) (toData F R0) i₀))) ℓ ≤ psum s ℓ := by
  classical
  intro D Bs Q i₀ hi₀ ℓ hkℓ hℓr
  have hdec := type1_psum_decompose_ge F r s k₁ j hk1 hkr hj1 hjk hbig hsj hmid R0 hbhd i₀ ℓ hkℓ
  have hpref' : psum (R0.cA i₀) (ℓ - k₁ + 1) ≤ psumSeq (tupPadSum (single (qExp F))
      (consVec (w1Of F r s k₁ hk1 hkr hbig) (sTail r s k₁ hkr))) (ℓ - k₁ + 1) :=
    hpref i₀ hi₀ (ℓ - k₁ + 1)
  have htel := lemma29_qExp_telescope F r s k₁ hk1 hkr hbig (ℓ - k₁ + 1) (by omega)
  have hk1' : k₁ + (ℓ - k₁ + 1) - 1 = ℓ := by omega
  have htel' : psumSeq (tupPadSum (single (qExp F))
        (consVec (w1Of F r s k₁ hk1 hkr hbig) (sTail r s k₁ hkr))) (ℓ - k₁ + 1) =
      (s ⟨k₁ - 1, by omega⟩ : ℕ) + (psum s ℓ - psum s k₁) := by
    rw [htel, hk1']
  have hkm1 : k₁ - 1 < r := by omega
  have hsu := psum_succ s (k₁ - 1)
  have hkk : (k₁ - 1) + 1 = k₁ := by omega
  have hpks : psum s k₁ = psum s (k₁ - 1) + (s ⟨k₁ - 1, hkm1⟩ : ℕ) := by
    rw [hkk] at hsu
    rw [hsu]
    rw [pad0_of_lt s hkm1]
  have hkleq : psum s k₁ ≤ psum s ℓ := psum_mono s hkℓ
  calc
    psum (Q.c (Sum.inl (RelData.iterIdx F (k₁ - j - 1) (toData F R0) i₀))) ℓ
        = psum s (k₁ - 1) + psum (R0.cA i₀) (ℓ - k₁ + 1) := hdec
    _ ≤ psum s (k₁ - 1) + psumSeq (tupPadSum (single (qExp F))
          (consVec (w1Of F r s k₁ hk1 hkr hbig) (sTail r s k₁ hkr))) (ℓ - k₁ + 1) := by
          exact Nat.add_le_add_left hpref' (psum s (k₁ - 1))
    _ = psum s (k₁ - 1) + ((s ⟨k₁ - 1, by omega⟩ : ℕ) + (psum s ℓ - psum s k₁)) := by
          rw [htel']
    _ ≤ psum s ℓ := by
          rw [hpks]
          omega

end ZagierHoffmanPositiveChar
