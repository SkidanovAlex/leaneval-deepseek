import Submission.ZagierHoffmanProof.StepL40
import Submission.ZagierHoffmanProof.StepL25

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L41: the ζ_A-level CASE-2 decomposition (Prop 2.13) — `zeta_213`

`zeta_213` is the ζ_A-level content of Prop 2.13: for a CASE-2 input `s : Fin k`
(depth `k`, `s₁..s_{k−1} ≤ q`, `s_k = q`) with `j` the last index with `s_j < q`
(so positions `j..k−1` of `s` are all `q`, hypothesis `hqend`), the R1 chain
(`R0 := r1Rel F`, `u := PUnit.unit`, `n := k−j−1` `BC_q`-steps, `B*_{s_j}`, prefix
`s₁..s_{j−1}`) is valid at every level (`chain_valid_of` — CASE-1's
`chain_valid_sjk_data` needs `hbig`, absent here), and its leading member is `s`
(`leading_zeta_R1`); assembling with `zeta_fixed_bridge` and `triple_sum_split`
gives
  ζ_A(s) + (guarded type-1 sum over D.ιA) + (type-2 sum) + (type-3 sum) = 0.
For the R1 relation `D.ιA` is `PUnit`-based so the guarded type-1 sum is `0` in
practice (a `prop213` assembly erases it); we keep the guarded form exactly as in
`zeta_214` so the proof is a verbatim copy with the R1 config.
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The ζ_A-level (2.13): ζ_A(s) plus the guarded type-1, the type-2 and the type-3
members sums to zero at the R1 (CASE-2) configuration. -/
theorem zeta_213 (k : ℕ) (s : Fin k → ℕ+) (j : ℕ)
    (hk1 : 1 ≤ k) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hqend : ∀ i : Fin k, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < k → (s i : ℕ) = Nat.card F) :
    let D := RelData.BCqIter F (k - j - 1) (toData F (r1Rel F))
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) (r1Rel F) e)
        (RelData.iterate_merge_hv F (k - j - 1) (r1Rel F) (s ⟨j - 1, by omega⟩) (by omega) (r1Rel_hbhd F))
    let Q := FixedOver.prependList F Bs (sPrefix k s j (by omega) (by omega))
    let u' := RelData.iterIdx F (k - j - 1) (toData F (r1Rel F)) PUnit.unit
    ζ_A F s +
      (∑ i : D.ιA, (if i = u' then 0 else (Q.a (Sum.inl i) : RatFunc.CompletionAtInfty F) *
        ζ_A F (Q.c (Sum.inl i)))) +
      (∑ i : D.ιB, (Q.a (Sum.inr (Sum.inl i)) : RatFunc.CompletionAtInfty F) *
        ζ_A F (Q.c (Sum.inr (Sum.inl i)))) +
      (∑ i : D.ιB, (Q.a (Sum.inr (Sum.inr i)) : RatFunc.CompletionAtInfty F) *
        ζ_A F (Q.c (Sum.inr (Sum.inr i)))) = 0 := by
  classical
  intro D Bs Q u'
  let f : D.ιA ⊕ (D.ιB ⊕ D.ιB) → RatFunc.CompletionAtInfty F := fun p =>
    (Q.a p : RatFunc.CompletionAtInfty F) * ζ_A F (Q.c p)
  have hvalid : ∀ d : ℕ, FixedOver.level F Q d = 0 := by
    intro d
    dsimp [Q, Bs, D]
    exact chain_valid_of F (r1Rel F) (r1Rel_hbhd F) PUnit.unit (r1Rel_aA_unit F)
      (k - j - 1) (s ⟨j - 1, by omega⟩)
      (by omega : (s ⟨j - 1, by omega⟩ : ℕ) + 1 ≤ Nat.card F)
      (sPrefix k s j (by omega) (by omega)) d
  have hzeta : (∑ p : D.ιA ⊕ (D.ιB ⊕ D.ιB), f p) = 0 := by
    have hz := zeta_fixed_bridge F Q.dep Q.hdep Q.c Q.a (fun d => by
      simpa [FixedOver.level] using hvalid d)
    dsimp [f]
    exact hz
  have hsplit := triple_sum_split F f
  rw [hsplit] at hzeta
  let F1 : D.ιA → RatFunc.CompletionAtInfty F := fun i => f (Sum.inl i)
  -- the leading member keeps coefficient 1 and value ζ_A s
  have hcoeff : Q.a (Sum.inl u') = (1 : RatFunc F) := by
    have hc := leading_member_coeff F (k - j - 1) (r1Rel F) PUnit.unit (s ⟨j - 1, by omega⟩)
      (fun e => BCqIter_valid F (k - j - 1) (r1Rel F) e)
      (RelData.iterate_merge_hv F (k - j - 1) (r1Rel F) (s ⟨j - 1, by omega⟩) (by omega) (r1Rel_hbhd F))
      (sPrefix k s j (by omega) (by omega))
    rw [r1Rel_aA_unit F] at hc
    simpa [Q, Bs, u'] using hc
  have hzetaLead : ζ_A F s = ζ_A F (Q.c (Sum.inl u')) := by
    dsimp [Q, Bs, u']
    exact leading_zeta_R1 F k s j hk1 hj1 hjk hsj hqend
  have hfu : f (Sum.inl u') = ζ_A F s := by
    dsimp [f]
    rw [hcoeff]
    simp [completion_coe_one, hzetaLead]
  -- split the type-1 sum at u'
  have hsplit1 : (∑ i : D.ιA, F1 i) = F1 u' + (∑ i : D.ιA, (if i = u' then 0 else F1 i)) := by
    have hmem : u' ∈ (Finset.univ : Finset (D.ιA)) := Finset.mem_univ u'
    have herase : (∑ i : D.ιA, F1 i) = (∑ i ∈ (Finset.univ : Finset (D.ιA)).erase u', F1 i) + F1 u' := by
      rw [← Finset.sum_erase_add (s := (Finset.univ : Finset (D.ιA))) (f := F1) (a := u') hmem]
    have hif : (∑ i ∈ (Finset.univ : Finset (D.ιA)).erase u', F1 i) =
        (∑ i : D.ιA, (if i = u' then 0 else F1 i)) := by
      calc
        (∑ i ∈ (Finset.univ : Finset (D.ιA)).erase u', F1 i)
            = (∑ i ∈ (Finset.univ : Finset (D.ιA)).erase u', (if i = u' then 0 else F1 i)) := by
              apply Finset.sum_congr rfl
              intro i hi
              have hiu : i ≠ u' := (Finset.mem_erase.mp hi).1
              simp [hiu]
        _ = (∑ i : D.ιA, (if i = u' then 0 else F1 i)) := by
              rw [← Finset.sum_erase_add (s := (Finset.univ : Finset (D.ιA)))
                (f := fun i : D.ιA => (if i = u' then 0 else F1 i)) (a := u') hmem]
              simp
    calc
      (∑ i : D.ιA, F1 i) = (∑ i ∈ (Finset.univ : Finset (D.ιA)).erase u', F1 i) + F1 u' := herase
      _ = (∑ i : D.ιA, (if i = u' then 0 else F1 i)) + F1 u' := by rw [hif]
      _ = F1 u' + (∑ i : D.ιA, (if i = u' then 0 else F1 i)) := by rw [add_comm]
  -- rewrite hzeta
  have hzeta' : F1 u' + (∑ i : D.ιA, (if i = u' then 0 else F1 i)) +
      (∑ i : D.ιB, f (Sum.inr (Sum.inl i))) + (∑ i : D.ιB, f (Sum.inr (Sum.inr i))) = 0 := by
    simpa [hsplit1, F1] using hzeta
  have hzeta'' : (f (Sum.inl u') + (∑ i : D.ιA, (if i = u' then 0 else f (Sum.inl i)))) +
      (∑ i : D.ιB, f (Sum.inr (Sum.inl i))) + (∑ i : D.ιB, f (Sum.inr (Sum.inr i))) = 0 := by
    simpa [F1] using hzeta'
  rw [hfu] at hzeta''
  simpa [f] using hzeta''

end ZagierHoffmanPositiveChar
