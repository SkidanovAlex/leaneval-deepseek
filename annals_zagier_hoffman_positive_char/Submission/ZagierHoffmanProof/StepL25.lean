import Submission.ZagierHoffmanProof.StepL24

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L25: the ζ_A-level (2.14) at the Prop-2.12 configuration

`zeta_214` is the ζ_A-level content of paper (2.14): summing the valid fixed
relation `Q` (the B*_{s_j}-output of the BC_q-iterate of the Lemma-2.9 relation at
`s/k/j`, prefixed by `(s_{j-1},…,s_1)`) over levels with `zeta_fixed_bridge` gives
Σ p : ι₀, a_p·ζ_A(c_p) = 0; splitting off the distinguished type-1 member
`inl u'` (coefficient 1 by `leading_member_coeff`, value `ζ_A(s)` by
`leading_zeta`) yields
  ζ_A(s) + Σ_{iA ≠ u'} … + Σ_{type 2} … + Σ_{type 3} … = 0
with the type-1 sum in an `if`-erased form (the assembly splits the `if` when it
needs the actual non-leading type-1 family).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The ζ_A-level (2.14) at the Prop-2.12 configuration: ζ_A(s) plus the non-leading
type-1 members, the type-2 and the type-3 members sums to zero. -/
theorem zeta_214 (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hmid : ∀ i : Fin r, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < k - 1 → (s i : ℕ) = Nat.card F)
    (R0 : BinaryRel F) (u : R0.ιA)
    (ha : R0.aA u = 1)
    (hdep0 : R0.depA u = (r - k) + 1)
    (hc0 : ∀ hd : R0.depA u = (r - k) + 1,
        (fun x : Fin ((r - k) + 1) => R0.cA u (Fin.cast hd.symm x)) =
          bstarBase F r s k hk1 hkr hbig)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    let u' := RelData.iterIdx F (k - j - 1) (toData F R0) u
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
    exact chain_valid_sjk_data F r s k j hk1 hkr hj1 hjk hbig hsj R0 u ha hbhd d
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
    have hc := leading_member_coeff F (k - j - 1) R0 u (s ⟨j - 1, by omega⟩)
      (fun e => BCqIter_valid F (k - j - 1) R0 e)
      (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
      (sPrefix r s j (by omega) (by omega))
    rw [ha] at hc
    simpa [Q, Bs, u'] using hc
  have hzetaLead : ζ_A F s = ζ_A F (Q.c (Sum.inl u')) := by
    dsimp [Q, Bs, u']
    exact leading_zeta F r s k j hk1 hkr hj1 hjk hbig hsj hmid R0 u hdep0 hc0 hbhd
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
