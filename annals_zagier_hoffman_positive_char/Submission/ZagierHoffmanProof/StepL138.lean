import Submission.ZagierHoffmanProof.StepL137
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L138: ★★ `maink_g5_zeta_core` — the G5 (j = 0) ζ-identity at symbolic k
(SESSION 259h) — this closes (a)

The count-(k−1) transcription of `g5c1_zeta_core` (StepL77, level 2), with
  step 1: `BCqIter_zeta_zero F (k−1) R0` + `toBinaryRel_zeta_eq` + `simpa`;
  step 2: `hu_zeta` via `ζ_A_eq_of_reindex` + `maink_g5_depA_u_eq` +
          `maink_g5_u_cA_values` (StepL137);
  step 3: `hfu` via `hau` + `completion_coe_one`;
  step 4: the guard/erase bookkeeping (`hgu`/`hspl`) and the final rewrite.
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★★ The G5 (j = 0) ζ-identity at symbolic k, from the config conjuncts. -/
theorem maink_g5_zeta_core (r : ℕ) (s : Fin r → ℕ+) (k : ℕ) (hk1 : 1 ≤ k) (hkr : k ≤ r)
    (hallq : ∀ x : ℕ, x < k - 1 → pad0 s x = Nat.card F)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (R0 : BinaryRel F) (u : R0.ιA)
    (hdepu : R0.depA u = (r - k) + 1)
    (hau : R0.aA u = 1)
    (hc0 : ∀ hd : R0.depA u = (r - k) + 1,
      (fun x : Fin ((r - k) + 1) => R0.cA u (Fin.cast hd.symm x)) =
        bstarBase F r s k hk1 hkr hbig) :
    let D := RelData.BCqIter F (k - 1) (toData F R0)
    ζ_A F s +
      (∑ i : D.ιA, (if i = RelData.iterIdx F (k - 1) (toData F R0) u then 0 else
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
    have hz := BCqIter_zeta_zero F (k - 1) R0
    rw [toBinaryRel_zeta_eq F (RelData.BCqIter F (k - 1) (toData F R0))
      (BCqIter_valid F (k - 1) R0)] at hz
    simpa [f, g, D] using hz
  let u' := RelData.iterIdx F (k - 1) (toData F R0) u
  have hu_zeta : ζ_A F (D.cA u') = ζ_A F s := by
    refine ζ_A_eq_of_reindex F (maink_g5_depA_u_eq F r s k hk1 hkr R0 u hdepu)
      (D.cA u') s ?_
    intro i
    exact maink_g5_u_cA_values F r s k hk1 hkr hallq hbig R0 u hdepu hc0 i.1 i.isLt (by
      have hd := maink_g5_depA_u_eq F r s k hk1 hkr R0 u hdepu
      omega)
  have hfu : f u' = ζ_A F s := by
    have ha1 : (D.aA u' : RatFunc F) = 1 := by
      dsimp [u']
      rw [RelData.BCqIter_aA_at F (k - 1) (toData F R0) u]
      exact hau
    dsimp [f]
    rw [ha1, hu_zeta]
    simp [completion_coe_one]
  have hgu : (∑ i : D.ιA, (if i = u' then 0 else f i)) =
      (∑ i ∈ (Finset.univ : Finset D.ιA).erase u', f i) := by
    calc
      (∑ i : D.ιA, (if i = u' then 0 else f i))
          = (∑ i ∈ (Finset.univ : Finset D.ιA), (if i = u' then 0 else f i)) := by rfl
      _ = (∑ i ∈ (Finset.univ : Finset D.ιA).erase u', f i) := by
            have hs := Finset.sum_erase_add (s := (Finset.univ : Finset D.ιA))
              (f := fun i => if i = u' then 0 else f i) (a := u') (Finset.mem_univ u')
            have hifu : (if u' = u' then 0 else f u') = 0 := by simp
            have herase : (∑ x ∈ (Finset.univ : Finset D.ιA).erase u',
                (if x = u' then 0 else f x)) =
                (∑ x ∈ (Finset.univ : Finset D.ιA).erase u', f x) := by
              apply Finset.sum_congr rfl
              intro x hx
              have hxu : x ≠ u' := (Finset.mem_erase.mp hx).1
              simp [hxu]
            calc
              (∑ i ∈ (Finset.univ : Finset D.ιA), (if i = u' then 0 else f i))
                  = (∑ i ∈ (Finset.univ : Finset D.ιA).erase u', (if i = u' then 0 else f i)) +
                      (if u' = u' then 0 else f u') := hs.symm
              _ = (∑ i ∈ (Finset.univ : Finset D.ιA).erase u', f i) := by
                    rw [herase, hifu]
                    simp
  have hspl : (∑ i : D.ιA, f i) = f u' + (∑ i : D.ιA, (if i = u' then 0 else f i)) := by
    have h1 : (∑ i : D.ιA, f i) = (∑ i ∈ (Finset.univ : Finset D.ιA).erase u', f i) + f u' := by
      exact (Finset.sum_erase_add (s := (Finset.univ : Finset D.ιA)) (f := f) (a := u')
        (Finset.mem_univ u')).symm
    rw [h1, hgu]
    ring
  rw [hspl, hfu] at hz0
  simpa [add_assoc] using hz0

end ZagierHoffmanPositiveChar
