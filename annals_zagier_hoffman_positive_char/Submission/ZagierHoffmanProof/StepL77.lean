import Submission.ZagierHoffmanProof.StepL76
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators
namespace ZagierHoffmanPositiveChar
/-!
# Step L77: the CASE-1 j=0 empty-front chain ζ-identity (SESSION 226/227)

★ g5c1_zeta (r s hcase hs0 hbig) : ∃ R0 u, ζ_A s + Σ_{i≠u} (aA i)·ζ_A(cA i) +
Σ_p (aB p)·ζ_A(cB p) = 0 — for the in-domain head-q input s = (q, s₂>q, …, s_r)
the CASE-1 j=0 chain (BCqIter F 1 over the tail relation R0 from
lemma_2_9_config_data at k = 2) gives the level-sum of its validity with the
u-member identified with ζ_A(s):
  • g5c1_u_cA_values — the value equality of the chain's u-member with s at every
    position (natural-index form with explicit bounds, mirroring StepL24's
    leading_tuple_value): head q via hs0; tail via hc0's bstarBase identification +
    qprepend_tail_values (StepL76);
  • hu_zeta — ζ_A(D.cA u) = ζ_A s via ζ_A_eq_of_reindex (Counting.lean) + the value
    lemma (the u-depth is D.depA u = (r−2)+1+1 = r by omega);
  • hz0 — the level-sum Σ_a (D.aA)·ζ(D.cA) + Σ_b (D.aB)·ζ(D.cB) = 0 via
    BCqIter_zeta_zero F 1 R0 + toBinaryRel_zeta_eq (the rfl bridge: toBinaryRel
    copies the RelData fields, so BinaryRel.zeta of the iterate is the plain sum);
  • hgu/hspl — the a-sum u-split (Finset.sum_erase_add): Σ_a = (u-term) + guarded;
    the u-term collapses to ζ_A s (aA u = 1 via hau).
LEAN NOTES: BCqIter_zeta_zero's BinaryRel.zeta over the toBinaryRel-iterate needs
toBinaryRel_zeta_eq (rfl) — direct simpa fails on the defeq-but-semireducible
Fintype instances; simpa [f, g, D] closes the hz0 target after the rw.  The member
facts (weight w for i ≠ u via hwtA + q-prepend, head q, second entry < s₂ via
hhead, b-members 2-adm via StepL75's kAdm2_cons_one/p2WpT_front_le) and the g5
recursion assembly are NEXT.  Named gates unchanged.
-/

attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- value equality of the CASE-1 j=0 chain's u-member with s (natural-index, bounds
over the chain depth; tuple values reduce at the kernel). -/
lemma g5c1_u_cA_values (r : ℕ) (s : Fin r → ℕ+) (hcase : 2 ≤ r)
    (hs0 : (s ⟨0, by omega⟩ : ℕ) = Nat.card F)
    (hbig : (Nat.card F : ℕ) < (s ⟨1, by omega⟩ : ℕ))
    (R0 : BinaryRel F) (u : R0.ιA)
    (hdepu : R0.depA u = (r - 2) + 1)
    (hc0 : ∀ hd : R0.depA u = (r - 2) + 1,
      (fun x : Fin ((r - 2) + 1) => R0.cA u (Fin.cast hd.symm x)) =
        bstarBase F r s 2 (by omega : 1 ≤ 2) hcase hbig) :
    ∀ (m : ℕ) (hmQ : m < (RelData.BCqIter F 1 (toData F R0)).depA u) (hmr : m < r),
      (RelData.BCqIter F 1 (toData F R0)).cA u ⟨m, hmQ⟩ = s ⟨m, hmr⟩ := by
  classical
  intro m hmQ hmr
  by_cases hm0 : m = 0
  · subst m
    have hcA0 : (RelData.BCqIter F 1 (toData F R0)).cA u ⟨0, hmQ⟩ = qExp F := by rfl
    rw [hcA0]
    apply Subtype.ext
    change Nat.card F = (s ⟨0, by omega⟩ : ℕ)
    exact hs0.symm
  · have hex : ∃ n : ℕ, m = n + 1 := ⟨m - 1, by omega⟩
    rcases hex with ⟨n, hmn⟩
    subst m
    have hndep : n < R0.depA u := by
      have hd : (RelData.BCqIter F 1 (toData F R0)).depA u = R0.depA u + 1 := by
        dsimp [RelData.BCqIter, RelData.BCq]
        rfl
      rw [hd] at hmQ
      omega
    have hcA : (RelData.BCqIter F 1 (toData F R0)).cA u ⟨n + 1, hmQ⟩ =
        (R0.cA u) ⟨n, hndep⟩ := by rfl
    rw [hcA]
    have hnlt0 : n < (r - 2) + 1 := by omega
    have hb := hc0 hdepu
    have hb' : (R0.cA u) (Fin.cast hdepu.symm ⟨n, hnlt0⟩) =
        bstarBase F r s 2 (by omega : 1 ≤ 2) hcase hbig ⟨n, hnlt0⟩ := by
      exact congrFun hb ⟨n, hnlt0⟩
    have hcast : Fin.cast hdepu.symm ⟨n, hnlt0⟩ = ⟨n, hndep⟩ := by
      apply Fin.ext
      rfl
    have hb'' : (R0.cA u) ⟨n, hndep⟩ =
        bstarBase F r s 2 (by omega : 1 ≤ 2) hcase hbig ⟨n, hnlt0⟩ := by
      rw [← hcast]
      exact hb'
    rw [hb'']
    have hmp : n + 1 < (r - 2) + 1 + 1 := by omega
    have hqtv' := qprepend_tail_values F r s hcase hs0 hbig ⟨n + 1, hmp⟩
    have hcv : (consVec (qExp F) (bstarBase F r s 2 (by omega : 1 ≤ 2) hcase hbig))
        ⟨n + 1, hmp⟩ = (bstarBase F r s 2 (by omega : 1 ≤ 2) hcase hbig) ⟨n, hnlt0⟩ := by
      rw [consVec_succ (qExp F) (bstarBase F r s 2 (by omega : 1 ≤ 2) hcase hbig) ⟨n, hnlt0⟩]
    have hbstar_s : (bstarBase F r s 2 (by omega : 1 ≤ 2) hcase hbig) ⟨n, hnlt0⟩ =
        s ⟨n + 1, hmr⟩ := by
      rw [← hcv]
      exact hqtv'
    rw [hbstar_s]

/-- toBinaryRel copies the fields: its BinaryRel.zeta is the plain data sum (rfl). -/
lemma toBinaryRel_zeta_eq (X : RelData F) (hv : ∀ e : ℕ, RelData.level F X e = 0) :
    BinaryRel.zeta F (RelData.toBinaryRel F X hv) =
      (∑ i : X.ιA, (((X.aA i : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (X.cA i))) +
      (∑ p : X.ιB, (((X.aB p : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (X.cB p))) := by
  rfl

/-- ★ CASE-1 j=0 ζ-identity from the config conjuncts (no rcases inside — the
assembly module rcases lemma_2_9_config_data ONCE for the member data and reuses
this identity; separate rcases produce non-defeq witnesses). -/
theorem g5c1_zeta_core (r : ℕ) (s : Fin r → ℕ+) (hcase : 2 ≤ r)
    (hs0 : (s ⟨0, by omega⟩ : ℕ) = Nat.card F)
    (hbig : (Nat.card F : ℕ) < (s ⟨1, by omega⟩ : ℕ))
    (R0 : BinaryRel F) (u : R0.ιA)
    (hdepu : R0.depA u = (r - 2) + 1)
    (hau : R0.aA u = 1)
    (hc0 : ∀ hd : R0.depA u = (r - 2) + 1,
      (fun x : Fin ((r - 2) + 1) => R0.cA u (Fin.cast hd.symm x)) =
        bstarBase F r s 2 (by omega : 1 ≤ 2) hcase hbig) :
    let D := RelData.BCqIter F 1 (toData F R0)
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
    have hz := BCqIter_zeta_zero F 1 R0
    rw [toBinaryRel_zeta_eq F (RelData.BCqIter F 1 (toData F R0)) (BCqIter_valid F 1 R0)] at hz
    simpa [f, g, D] using hz
  have hu_zeta : ζ_A F (D.cA u) = ζ_A F s := by
    refine ζ_A_eq_of_reindex F ?hd (D.cA u) s ?hp
    · have hd0 : D.depA u = R0.depA u + 1 := by
        dsimp [D, RelData.BCqIter, RelData.BCq]
        rfl
      omega
    · intro i
      have hilt : (i : ℕ) < D.depA u := i.isLt
      have hd0 : D.depA u = R0.depA u + 1 := by
        dsimp [D, RelData.BCqIter, RelData.BCq]
        rfl
      have hv := g5c1_u_cA_values F r s hcase hs0 hbig R0 u hdepu hc0 (i : ℕ) hilt (by omega)
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


/-- ★ CASE-1 j=0 ζ-identity (∃ form): ∃ R0 u with the identity — wrapper over the
config rcases + g5c1_zeta_core. -/
theorem g5c1_zeta (r : ℕ) (s : Fin r → ℕ+) (hcase : 2 ≤ r)
    (hs0 : (s ⟨0, by omega⟩ : ℕ) = Nat.card F)
    (hbig : (Nat.card F : ℕ) < (s ⟨1, by omega⟩ : ℕ)) :
    ∃ (R0 : BinaryRel F) (u : R0.ιA),
      let D := RelData.BCqIter F 1 (toData F R0)
      ζ_A F s +
        (∑ i : D.ιA, (if i = u then 0 else
          (((D.aA i : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (D.cA i)))) +
        (∑ p : D.ιB, (((D.aB p : RatFunc F) : RatFunc.CompletionAtInfty F) *
          ζ_A F (D.cB p))) = 0 := by
  classical
  have hk1 : 1 ≤ 2 := by omega
  rcases lemma_2_9_config_data F r s 2 hk1 hcase hbig with ⟨R0, u, hdepu, hau, hc0, hbhd, hwtA, hhead, hXw, hbndB⟩
  refine ⟨R0, u, ?_⟩
  intro D
  exact g5c1_zeta_core F r s hcase hs0 hbig R0 u hdepu hau hc0

end ZagierHoffmanPositiveChar
