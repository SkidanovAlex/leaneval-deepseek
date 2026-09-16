import Submission.ZagierHoffmanProof.StepL38

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L39: R1-chain value facts for the CASE-2 (Prop 2.13) leading member

★ `r1_iter_cA_all_q`: after `n` `BC_q`-steps of the R1 relation, the (single)
`a`-tuple has value `q` at every position.
★ `Bs_leading_pos_R1`: the B*-leading tuple of the CASE-2 chain has the values of
`s` at its base positions — `(s_j, q, …, q)` matching `s_{j+1}..s_k = q` — i.e.
`Bs.c (inl u') ⟨ℓ⟩ = s ⟨(j−1)+ℓ⟩` for base positions `ℓ` (head `s_j` at ℓ = 0, then
all-`q` from `r1_iter_cA_all_q` at ℓ ≥ 1 with `hqend`: positions `j..k−1` of `s`
are `q`).  Together with the R0-independent prefix-front facts these give the
CASE-2 leading member = `s`, the value content of the zeta_213 leading-ζ lemma
(PLAN 183j).

LEAN NOTES: rewrite under the PNat→ℕ coercion fails mysteriously — compose
equalities (`hval1.trans …`, `hvq.trans hs.symm`) instead of `rw`; `change` the
goal to the literal consVec-index form before `rw [hcBs]`-style index rewrites
(domain proofs are defeq through `ofBstarOver`); `congr 1` can close Fin-index
goals by itself (no trailing `Fin.ext`).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]
/-- After `n` `BC_q`-steps the (single) `a`-tuple of the R1 relation is all `q`:
every entry equals `q`. -/
lemma r1_iter_cA_all_q (n : ℕ) :
    ∀ x : Fin ((r1Rel F).depA PUnit.unit + n),
      (((RelData.BCqIter F n (toData F (r1Rel F))).cA
          (RelData.iterIdx F n (toData F (r1Rel F)) PUnit.unit))
        (Fin.cast (RelData.BCqIter_depA_at F n (toData F (r1Rel F)) PUnit.unit).symm x) : ℕ) = Nat.card F := by
  classical
  intro x
  have hv := RelData.BCqIter_cA_value F n (toData F (r1Rel F)) PUnit.unit x
  rw [hv]
  split_ifs <;> rfl

/-- ★ The B*-leading tuple of the CASE-2 (R1) chain has the values of `s` at its base
positions: `(s_j, q, …, q)` matching `s_{j+1}..s_k = q`. -/
lemma Bs_leading_pos_R1 (k j : ℕ) (s : Fin k → ℕ+)
    (hk1 : 1 ≤ k) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hqend : ∀ i : Fin k, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < k → (s i : ℕ) = Nat.card F) :
    let D := RelData.BCqIter F (k - j - 1) (toData F (r1Rel F))
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩)
        (fun e => BCqIter_valid F (k - j - 1) (r1Rel F) e)
        (RelData.iterate_merge_hv F (k - j - 1) (r1Rel F) (s ⟨j - 1, by omega⟩)
          (by omega) (r1Rel_hbhd F))
    ∀ (ℓ : ℕ) (hℓ : ℓ < Bs.dep (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F (r1Rel F)) PUnit.unit)))
      (hbd : (j - 1) + ℓ < k),
      Bs.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F (r1Rel F)) PUnit.unit)) ⟨ℓ, hℓ⟩ =
        s ⟨(j - 1) + ℓ, hbd⟩ := by
  classical
  intro D Bs ℓ hℓ hbd
  let u' := RelData.iterIdx F (k - j - 1) (toData F (r1Rel F)) PUnit.unit
  let n := k - j - 1
  let v := s ⟨j - 1, by omega⟩
  have hdepBs : Bs.dep (Sum.inl u') = (RelData.BCqIter F n (toData F (r1Rel F))).depA u' + 1 := by
    dsimp [Bs, ofBstarOver, D, n]
  have hcBs : Bs.c (Sum.inl u') = consVec v ((RelData.BCqIter F n (toData F (r1Rel F))).cA u') := by
    dsimp [Bs, ofBstarOver, v, n]
  rw [hcBs]
  change consVec v ((RelData.BCqIter F n (toData F (r1Rel F))).cA u') ⟨ℓ, hℓ⟩ =
      s ⟨(j - 1) + ℓ, hbd⟩
  by_cases hz : ℓ = 0
  · subst ℓ
    have hidx0 : (⟨0, hℓ⟩ : Fin ((RelData.BCqIter F n (toData F (r1Rel F))).depA u' + 1)) =
        ⟨0, by omega⟩ := by
      apply Fin.ext
      rfl
    rw [hidx0]
    rw [consVec_zero]
    congr 1
  · have hℓnz : ℓ ≠ 0 := hz
    have hbv : ℓ - 1 < (RelData.BCqIter F n (toData F (r1Rel F))).depA u' := by
      have hℓ' : ℓ < Bs.dep (Sum.inl u') := hℓ
      rw [hdepBs] at hℓ'
      have hpos : 0 < ℓ := Nat.pos_of_ne_zero hℓnz
      omega
    let i : Fin ((RelData.BCqIter F n (toData F (r1Rel F))).depA u') := ⟨ℓ - 1, hbv⟩
    have hℓi : (⟨ℓ, hℓ⟩ : Fin ((RelData.BCqIter F n (toData F (r1Rel F))).depA u' + 1)) =
        ⟨(i : ℕ) + 1, by omega⟩ := by
      apply Fin.ext
      simp [i]
      omega
    rw [hℓi]
    rw [consVec_succ v ((RelData.BCqIter F n (toData F (r1Rel F))).cA u') i]
    change (RelData.BCqIter F n (toData F (r1Rel F))).cA u' ⟨ℓ - 1, hbv⟩ =
      s ⟨(j - 1) + ℓ, hbd⟩
    -- value of the iterate-cA at ℓ−1 is q
    have hvq : (((RelData.BCqIter F n (toData F (r1Rel F))).cA u') ⟨ℓ - 1, hbv⟩ : ℕ) = Nat.card F := by
      -- use r1_iter_cA_all_q with the cast-transport
      have hdepD : (RelData.BCqIter F n (toData F (r1Rel F))).depA u' =
          (r1Rel F).depA PUnit.unit + n := by
        dsimp [u']
        exact RelData.BCqIter_depA_at F n (toData F (r1Rel F)) PUnit.unit
      have hbv' : ℓ - 1 < (r1Rel F).depA PUnit.unit + n := by
        simpa [hdepD] using hbv
      have hx : (⟨ℓ - 1, hbv⟩ : Fin ((RelData.BCqIter F n (toData F (r1Rel F))).depA u')) =
          Fin.cast (RelData.BCqIter_depA_at F n (toData F (r1Rel F)) PUnit.unit).symm ⟨ℓ - 1, hbv'⟩ := by
        apply Fin.ext
        simp
      have hval1 : (((RelData.BCqIter F n (toData F (r1Rel F))).cA u') ⟨ℓ - 1, hbv⟩ : ℕ) =
          (((RelData.BCqIter F n (toData F (r1Rel F))).cA u')
            (Fin.cast (RelData.BCqIter_depA_at F n (toData F (r1Rel F)) PUnit.unit).symm ⟨ℓ - 1, hbv'⟩) : ℕ) := by
        exact congrArg (fun e : Fin ((RelData.BCqIter F n (toData F (r1Rel F))).depA u') =>
          (((RelData.BCqIter F n (toData F (r1Rel F))).cA u') e : ℕ)) hx
      exact hval1.trans (r1_iter_cA_all_q F n ⟨ℓ - 1, hbv'⟩)
    -- s-value at (j−1)+ℓ is q
    have hs : (s ⟨(j - 1) + ℓ, hbd⟩ : ℕ) = Nat.card F := by
      have hge : (j : ℕ) ≤ (j - 1) + ℓ := by omega
      exact hqend ⟨(j - 1) + ℓ, hbd⟩ hge hbd
    apply Subtype.ext
    exact hvq.trans hs.symm




end ZagierHoffmanPositiveChar
