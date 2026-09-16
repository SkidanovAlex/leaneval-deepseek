import Submission.ZagierHoffmanProof.StepL31

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L32: Prop-2.12 assembly — the type-1 reindexing (chunk 1)

zeta_214 gives the (2.14) ζ_A-level relation with its type-1 sum over the iterate
`a`-indices `D.ιA` (excluding the leading member `u'`).  The per-member prefix-k
bounds (`type1_psum_decompose` / `type1_psum_lt_k`, StepL31) and the `hleA`-head
facts are stated over the BASE `a`-indices `R0.ιA` (via `iterIdx`).  This module
records the bridge: `RelData.BCqIter_ιA_equiv` (the base↔iterate index equivalence,
`iterIdx` with the `BCqIter_ιA`-transport inverse), `sum_reindex_iterIdx` (sums over
`D.ιA` reindex to sums over `R0.ιA`), `RelData.iterIdx_injective`, and
★ `type1_guard_reindex`: zeta_214's type-1 sum (with the `i = u'` guard, `u'` the
leading member) reindexes to `R0.ιA` with the `i₀ = u` guard — so each type-1
member is indexed by its base index and the StepL31 bounds apply per member.
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The `a`-index reindexing equivalence: base `a`-indices ↔ iterate `a`-indices
(`iterIdx` with the `BCqIter_ιA` equality as the inverse). -/
noncomputable def RelData.BCqIter_ιA_equiv (n : ℕ) (D : RelData F) :
    D.ιA ≃ (RelData.BCqIter F n D).ιA where
  toFun := RelData.iterIdx F n D
  invFun := fun i => Eq.mpr (RelData.BCqIter_ιA F n D).symm i
  left_inv := by
    intro x
    exact eq_mpr_symm_id (RelData.BCqIter_ιA F n D).symm x
  right_inv := by
    intro i
    unfold RelData.iterIdx
    exact eq_mpr_symm_id (RelData.BCqIter_ιA F n D) i

/-- Sums over the iterate `a`-indices reindex to sums over the base `a`-indices via
`iterIdx` (the Prop-2.12 type-1 reindexing). -/
lemma sum_reindex_iterIdx (n : ℕ) (R0 : BinaryRel F) {M : Type*} [AddCommMonoid M]
    (fam : (RelData.BCqIter F n (toData F R0)).ιA → M) :
    (∑ i : (RelData.BCqIter F n (toData F R0)).ιA, fam i) =
      (∑ i₀ : R0.ιA, fam (RelData.iterIdx F n (toData F R0) i₀)) := by
  let e : R0.ιA ≃ (RelData.BCqIter F n (toData F R0)).ιA :=
    RelData.BCqIter_ιA_equiv F n (toData F R0)
  have hsum := Fintype.sum_equiv e (f := fun i₀ : R0.ιA => fam (RelData.iterIdx F n (toData F R0) i₀))
    (g := fun i => fam i)
    (by intro x; rfl)
  -- hsum : ∑ i₀, fam (iterIdx i₀) = ∑ i : D.ιA, fam i
  exact hsum.symm


/-- iterIdx is injective (it is the transport of the BCqIter_ιA type equality). -/
lemma RelData.iterIdx_injective (n : ℕ) (R0 : BinaryRel F) :
    Function.Injective (RelData.iterIdx F n (toData F R0)) := by
  intro a b h
  have he := RelData.BCqIter_ιA_equiv F n (toData F R0)
  have hinj : Function.Injective (RelData.BCqIter_ιA_equiv F n (toData F R0)).toFun :=
    (RelData.BCqIter_ιA_equiv F n (toData F R0)).injective
  exact hinj h

/-- ★ The type-1 guard reindex: zeta_214's type-1 sum (over the iterate `a`-indices
`D.ιA`, excluding the leading member `u'`) reindexes to the base `a`-indices
`R0.ιA`, excluding `u` — the Prop-2.12 assembly step that makes `type1_psum_lt_k`
(an `R0.ιA`-statement) applicable per member. -/
lemma type1_guard_reindex (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1)
    (u : R0.ιA) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    let u' := RelData.iterIdx F (k - j - 1) (toData F R0) u
    (∑ i : D.ιA, (if i = u' then 0 else
        (((Q.a (Sum.inl i) : RatFunc F) : RatFunc.CompletionAtInfty F) *
          ζ_A F (Q.c (Sum.inl i))))) =
    (∑ i₀ : R0.ιA, (if i₀ = u then 0 else
        (((Q.a (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀)) : RatFunc F) :
            RatFunc.CompletionAtInfty F) *
          ζ_A F (Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀)))))) := by
  classical
  intro D Bs Q u'
  have hsum := sum_reindex_iterIdx F (k - j - 1) R0
    (fam := fun i : D.ιA => if i = u' then 0 else
      (((Q.a (Sum.inl i) : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (Q.c (Sum.inl i))))
  -- hsum : Σ i : D.ιA fam i = Σ i₀ fam (iterIdx i₀)
  -- goal : LHS = RHS: rw [hsum]; then per-i₀ congr:
  rw [hsum]
  apply Fintype.sum_congr
  intro i₀
  by_cases hi : i₀ = u
  · subst i₀
    have hiu : RelData.iterIdx F (k - j - 1) (toData F R0) u = u' := by
      dsimp [u']
    simp [hiu]
  · -- i₀ ≠ u: both ifs reduce to the coeff·ζ term
    have hniu : RelData.iterIdx F (k - j - 1) (toData F R0) i₀ ≠ u' := by
      intro hbad
      have hEq : i₀ = u := by
        have hinj := RelData.iterIdx_injective F (k - j - 1) R0
        exact hinj hbad
      exact hi hEq
    simp [hi, hniu]


/-- The `a`-coefficient of a reindexed type-1 member is the base coefficient:
`Q.a (inl (iterIdx i₀)) = R0.aA i₀`. -/
lemma type1_coeff (n : ℕ) (R0 : BinaryRel F) (v : ℕ+)
    (hvalid : ∀ e : ℕ, RelData.level F (RelData.BCqIter F n (toData F R0)) e = 0)
    (hv : ∀ p : (RelData.BCqIter F n (toData F R0)).ιB,
      (v : ℕ) + (((RelData.BCqIter F n (toData F R0)).cB p)
        ⟨0, (RelData.BCqIter F n (toData F R0)).hdepB p⟩ : ℕ) ≤ Nat.card F)
    (xs : List ℕ+) (i₀ : R0.ιA) :
    ((FixedOver.prependList F (ofBstarOver F (RelData.BCqIter F n (toData F R0)) v hvalid hv) xs).a
        (Sum.inl (RelData.iterIdx F n (toData F R0) i₀)) : RatFunc F) = R0.aA i₀ := by
  classical
  calc
    ((FixedOver.prependList F (ofBstarOver F (RelData.BCqIter F n (toData F R0)) v hvalid hv) xs).a
        (Sum.inl (RelData.iterIdx F n (toData F R0) i₀)) : RatFunc F)
        = (ofBstarOver F (RelData.BCqIter F n (toData F R0)) v hvalid hv).a
            (Sum.inl (RelData.iterIdx F n (toData F R0) i₀)) := by
          exact FixedOver.prependList_a F (ofBstarOver F (RelData.BCqIter F n (toData F R0)) v hvalid hv)
            xs (Sum.inl (RelData.iterIdx F n (toData F R0) i₀))
    _ = (RelData.BCqIter F n (toData F R0)).aA (RelData.iterIdx F n (toData F R0) i₀) := by rfl
    _ = (toData F R0).aA i₀ := by
          have hcast := RelData.BCqIter_aA_cast F n (toData F R0) (RelData.iterIdx F n (toData F R0) i₀)
          have hrt : Eq.mpr (RelData.BCqIter_ιA F n (toData F R0)).symm
              (RelData.iterIdx F n (toData F R0) i₀) = i₀ := by
            unfold RelData.iterIdx
            exact eq_mpr_symm_id (RelData.BCqIter_ιA F n (toData F R0)).symm i₀
          rw [hrt] at hcast
          exact hcast
    _ = R0.aA i₀ := by rfl


/-- zeta_214 with the type-1 sum reindexed to the base `a`-indices (each type-1 member
indexed by `i₀ : R0.ιA`, `i₀ ≠ u`). -/
theorem zeta_214_reindexed (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
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
    ζ_A F s +
      (∑ i₀ : R0.ιA, (if i₀ = u then 0 else (Q.a (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀)) : RatFunc.CompletionAtInfty F) *
        ζ_A F (Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀))))) +
      (∑ i : D.ιB, (Q.a (Sum.inr (Sum.inl i)) : RatFunc.CompletionAtInfty F) *
        ζ_A F (Q.c (Sum.inr (Sum.inl i)))) +
      (∑ i : D.ιB, (Q.a (Sum.inr (Sum.inr i)) : RatFunc.CompletionAtInfty F) *
        ζ_A F (Q.c (Sum.inr (Sum.inr i)))) = 0 := by
  classical
  intro D Bs Q
  have hz := zeta_214 F r s k j hk1 hkr hj1 hjk hbig hsj hmid R0 u ha hdep0 hc0 hbhd
  -- hz's conclusion has the lets D Bs Q and the D.ιA-type-1 sum
  simpa [type1_guard_reindex F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd u] using hz


/-- The `n`-fold `BC_q` iterate of an `a`-tuple has weight `n·q` plus the base
weight: the `n` leading `q`'s account for the extra. -/
lemma BCqIter_cA_weight (n : ℕ) (D : RelData F) (i : D.ιA) :
    weight ((RelData.BCqIter F n D).depA (RelData.iterIdx F n D i))
        ((RelData.BCqIter F n D).cA (RelData.iterIdx F n D i)) =
      n * Nat.card F + weight (D.depA i) (D.cA i) := by
  revert D i
  induction n with
  | zero =>
      intro D i
      change weight (D.depA i) (D.cA i) = 0 * Nat.card F + weight (D.depA i) (D.cA i)
      omega
  | succ n ih =>
      intro D i
      have hrec : RelData.BCqIter F (n + 1) D = RelData.BCqIter F n (RelData.BCq F D) := by rfl
      change weight ((RelData.BCqIter F n (RelData.BCq F D)).depA (RelData.iterIdx F n (RelData.BCq F D) i))
          ((RelData.BCqIter F n (RelData.BCq F D)).cA (RelData.iterIdx F n (RelData.BCq F D) i)) =
        (n + 1) * Nat.card F + weight (D.depA i) (D.cA i)
      have hih := ih (RelData.BCq F D) i
      -- hih : weight (depA(iterIdx n (BCq D) i)) (cA …) = nq + weight ((BCq D).depA i) ((BCq D).cA i)
      have hstep : weight ((RelData.BCq F D).depA i) ((RelData.BCq F D).cA i) =
          Nat.card F + weight (D.depA i) (D.cA i) := by
        change weight (D.depA i + 1) (consVec (qExp F) (D.cA i)) =
          Nat.card F + weight (D.depA i) (D.cA i)
        have hw := weight_consVec (qExp F) (D.cA i)
        rw [hw]
        rw [show (qExp F : ℕ) = Nat.card F by rfl]
      calc
        weight ((RelData.BCqIter F n (RelData.BCq F D)).depA (RelData.iterIdx F n (RelData.BCq F D) i))
            ((RelData.BCqIter F n (RelData.BCq F D)).cA (RelData.iterIdx F n (RelData.BCq F D) i))
            = n * Nat.card F + weight ((RelData.BCq F D).depA i) ((RelData.BCq F D).cA i) := hih
        _ = n * Nat.card F + (Nat.card F + weight (D.depA i) (D.cA i)) := by rw [hstep]
        _ = (n + 1) * Nat.card F + weight (D.depA i) (D.cA i) := by ring


/-- Weight of a type-1 member: the `s₁..s_j` front plus the iterate `a`-tuple. -/
lemma type1_weight_decompose (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i₀ : R0.ιA,
      weight (Q.dep (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀)))
          (Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀))) =
        psum s j + weight ((RelData.BCqIter F (k - j - 1) (toData F R0)).depA
            (RelData.iterIdx F (k - j - 1) (toData F R0) i₀))
          ((RelData.BCqIter F (k - j - 1) (toData F R0)).cA
            (RelData.iterIdx F (k - j - 1) (toData F R0) i₀)) := by
  classical
  intro D Bs Q i₀
  let i : D.ιA := RelData.iterIdx F (k - j - 1) (toData F R0) i₀
  let depD : ℕ := D.depA i
  have hQdep : Q.dep (Sum.inl i) = j + D.depA i := by
    have hlen : (sPrefix r s j (by omega) (by omega)).length = j - 1 :=
      sPrefix_length r s j (by omega) (by omega)
    have h1 := FixedOver.prependList_dep F Bs (sPrefix r s j (by omega) (by omega)) (Sum.inl i)
    -- h1 : Q.dep (inl i) = Bs.dep (inl i) + len
    have h2 : Bs.dep (Sum.inl i) = D.depA i + 1 := by
      dsimp [Bs, ofBstarOver]
    rw [h1, h2, hlen]
    omega
  -- weight = psum at full depth
  have hwpsum : weight (Q.dep (Sum.inl i)) (Q.c (Sum.inl i)) = psum (Q.c (Sum.inl i)) (Q.dep (Sum.inl i)) := by
    have hp := psum_ge_depth (Q.c (Sum.inl i)) (m := Q.dep (Sum.inl i)) (le_refl _)
    exact hp.symm
  -- psum split at j + depD
  have hsplit : psum (Q.c (Sum.inl i)) (j + D.depA i) =
      psum (Q.c (Sum.inl i)) j + (∑ t ∈ Finset.range (D.depA i), pad0 (Q.c (Sum.inl i)) (j + t)) := by
    change (∑ x ∈ Finset.range (j + D.depA i), pad0 (Q.c (Sum.inl i)) x) =
      (∑ x ∈ Finset.range j, pad0 (Q.c (Sum.inl i)) x) +
        (∑ t ∈ Finset.range (D.depA i), pad0 (Q.c (Sum.inl i)) (j + t))
    rw [Finset.sum_range_add]
  have htail : (∑ t ∈ Finset.range (D.depA i), pad0 (Q.c (Sum.inl i)) (j + t)) =
      psum (D.cA i) (D.depA i) := by
    apply Finset.sum_congr rfl
    intro t ht
    have hx : j ≤ j + t := by omega
    have hsh := type1_pad0_shift F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd i (j + t) hx
    -- hsh : pad0 (Q.c i) (j+t) = pad0 (D.cA i) (j+t−j)
    have hsub : (j + t) - j = t := by omega
    rw [hsh]
    rw [hsub]
  have hwD : psum (D.cA i) (D.depA i) = weight (D.depA i) (D.cA i) := by
    have hp := psum_ge_depth (D.cA i) (m := D.depA i) (le_refl _)
    exact hp
  have hpj : psum (Q.c (Sum.inl i)) j = psum s j :=
    a_side_psum_j F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd i
  calc
    weight (Q.dep (Sum.inl i)) (Q.c (Sum.inl i))
        = psum (Q.c (Sum.inl i)) (Q.dep (Sum.inl i)) := hwpsum
    _ = psum (Q.c (Sum.inl i)) (j + D.depA i) := by
          exact congrArg (psum (Q.c (Sum.inl i))) hQdep
    _ = psum (Q.c (Sum.inl i)) j + (∑ t ∈ Finset.range (D.depA i), pad0 (Q.c (Sum.inl i)) (j + t)) := hsplit
    _ = psum s j + psum (D.cA i) (D.depA i) := by
          rw [hpj, htail]
    _ = psum s j + weight (D.depA i) (D.cA i) := by rw [hwD]



/-- ★ Type-1 weight preservation: a type-1 member has weight `w(s)` (given the base
`a`-member weights are `s_k + … + s_r` — the `hleA`-weight content). -/
lemma type1_weight_eq (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hmid : ∀ i : Fin r, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < k - 1 → (s i : ℕ) = Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i₀ : R0.ιA,
      (weight (R0.depA i₀) (R0.cA i₀) = psum s r - psum s (k - 1)) →
        weight (Q.dep (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀)))
            (Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀))) =
          weight r s := by
  classical
  intro D Bs Q i₀ hwtA
  let i : D.ιA := RelData.iterIdx F (k - j - 1) (toData F R0) i₀
  have hdec := type1_weight_decompose F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd i₀
  -- hdec : weight (Q.c i) = psum s j + weight (D.cA i)  [Q.dep-domain version]
  have hiter := BCqIter_cA_weight F (k - j - 1) (toData F R0) i₀
  -- hiter : weight (depA(iterIdx)) (cA(iterIdx)) = nq + weight ((toData R0).depA i₀) ((toData R0).cA i₀)
  have hn : (k - 1 - j) = k - j - 1 := by omega
  have hpkm1 : psum s (k - 1) = psum s j + (k - 1 - j) * Nat.card F := by
    apply psum_const_block (s := s) (j := j) (m := k - 1) (q := Nat.card F)
    · omega
    · intro x hxj hxkm1
      have hxr : x < r := by omega
      have hm := hmid ⟨x, hxr⟩ hxj hxkm1
      rw [pad0_of_lt s hxr]
      exact hm
  have hmono : psum s (k - 1) ≤ psum s r := psum_mono s (by omega)
  calc
    weight (Q.dep (Sum.inl i)) (Q.c (Sum.inl i))
        = psum s j + weight (D.depA i) (D.cA i) := hdec
    _ = psum s j + ((k - j - 1) * Nat.card F + weight ((toData F R0).depA i₀) ((toData F R0).cA i₀)) := by
          rw [hiter]
    _ = psum s j + (k - j - 1) * Nat.card F + (psum s r - psum s (k - 1)) := by
          have hw0 : weight ((toData F R0).depA i₀) ((toData F R0).cA i₀) = weight (R0.depA i₀) (R0.cA i₀) := by rfl
          rw [hw0, hwtA]
          omega
    _ = weight r s := by
          rw [← psum_ge_depth s (le_refl r)]
          have hn' : (k - j - 1) = (k - 1 - j) := by omega
          rw [hn']
          rw [← hpkm1]
          omega


/-- One `BC_q` b-step fiber: weight of the p2WpT-fiber is `(q−1)` plus the weight of
the old b-tuple (the P2Data LePad weight-equality). -/
lemma fiber_weight_step (D : RelData F) (j : D.ιB)
    (e : (p2WpT F (qMinusExp F) (D.hdepB j) (D.cB j)).ι) :
    weight ((p2WpT F (qMinusExp F) (D.hdepB j) (D.cB j)).dep e)
        ((p2WpT F (qMinusExp F) (D.hdepB j) (D.cB j)).c e) =
      (Nat.card F - 1) + weight (D.depB j) (D.cB j) := by
  classical
  have hle := (p2WpT F (qMinusExp F) (D.hdepB j) (D.cB j)).hle e
  have hw := hle.1
  have hs : weight 1 (single (qMinusExp F)) = (Nat.card F - 1 : ℕ) := by
    have h := weight_single (qMinusExp F)
    simpa [qMinusExp] using h
  rw [hw, hs]

/-- Weight of a tuple splits into its head and its tail (expTail). -/
lemma weight_head_tail {d : ℕ} (hdpos : 0 < d) (t : Fin d → ℕ+) :
    weight d t = (t ⟨0, hdpos⟩ : ℕ) + weight (d - 1) (expTail t) := by
  classical
  have hp := psum_head_expTail hdpos t (d - 1)
  -- hp : psum t ((d−1)+1) = (t⟨0,hdpos⟩:ℕ) + psum (expTail t)(d−1)
  have hd : (d - 1) + 1 = d := by omega
  have hw1 : weight d t = psum t d := (psum_ge_depth t (le_refl d)).symm
  have hw2 : weight (d - 1) (expTail t) = psum (expTail t) (d - 1) := by
    have hp' := psum_ge_depth (expTail t) (m := d - 1) (le_refl _)
    exact hp'.symm
  calc
    weight d t = psum t d := hw1
    _ = psum t ((d - 1) + 1) := by
          exact congrArg (psum t) hd.symm
    _ = (t ⟨0, hdpos⟩ : ℕ) + psum (expTail t) (d - 1) := by
          simpa [hd] using hp
    _ = (t ⟨0, hdpos⟩ : ℕ) + weight (d - 1) (expTail t) := by rw [hw2]

/-- ★ The `BC_q`-iterate b-fiber weight: an `n`-level fiber (expTail of the level-`n`
b-tuple) has weight `n·q` plus the level-0 tail weight `Xw`. -/
lemma BCq_fiber_weight_X (n : ℕ) (R0 : BinaryRel F)
    (hbhd : ∀ j : R0.ιB, ((R0.cB j) ⟨0, R0.hdepB j⟩ : ℕ) = 1)
    (Xw : ℕ)
    (hXw : ∀ j : R0.ιB,
      weight (R0.depB j - 1) (expTail (R0.cB j)) = Xw) :
    ∀ i : (RelData.BCqIter F n (toData F R0)).ιB,
      weight ((RelData.BCqIter F n (toData F R0)).depB i - 1)
          (expTail ((RelData.BCqIter F n (toData F R0)).cB i)) =
        n * Nat.card F + Xw := by
  classical
  induction n with
  | zero =>
      intro i
      change weight (R0.depB i - 1) (expTail (R0.cB i)) = 0 * Nat.card F + Xw
      rw [hXw i]
      simp
  | succ n ih =>
      rw [BCqIter_append]
      intro i
      change RelData.BCqIdx F (RelData.BCqIter F n (toData F R0)) at i
      rcases i with ⟨j, e⟩
      let Dn : RelData F := RelData.BCqIter F n (toData F R0)
      let fib : P2Data F 1 (Dn.depB j) (by omega : 0 < 1) (Dn.hdepB j)
          (single (qMinusExp F)) (Dn.cB j) := p2WpT F (qMinusExp F) (Dn.hdepB j) (Dn.cB j)
      have hcB : (RelData.BCq F Dn).cB ⟨j, e⟩ = consVec oneExp (fib.c e) := by
        dsimp [RelData.BCq, Dn, fib]
      have htail : expTail ((RelData.BCq F Dn).cB ⟨j, e⟩) = fib.c e := by
        rw [hcB]
        rfl
      have hdep : (RelData.BCq F Dn).depB ⟨j, e⟩ - 1 = fib.dep e := by
        have hd : (RelData.BCq F Dn).depB ⟨j, e⟩ = fib.dep e + 1 := by
          dsimp [RelData.BCq, Dn, fib]
        rw [hd]
        omega
      have hfw := fiber_weight_step F Dn j e
      have hih := ih j
      have hsplit : weight (Dn.depB j) (Dn.cB j) = 1 + weight (Dn.depB j - 1) (expTail (Dn.cB j)) := by
        have hh := BCqIter_head_one_data F n R0 hbhd j
        have hwht := weight_head_tail (Dn.hdepB j) (Dn.cB j)
        rw [hwht]
        have hh1 : ((Dn.cB j) ⟨0, Dn.hdepB j⟩ : ℕ) = 1 := hh
        rw [hh1]
      calc
        weight ((RelData.BCq F Dn).depB ⟨j, e⟩ - 1)
            (expTail ((RelData.BCq F Dn).cB ⟨j, e⟩))
            = weight (fib.dep e) (fib.c e) := by
              rw [htail]
              rfl
        _ = (Nat.card F - 1) + weight (Dn.depB j) (Dn.cB j) := hfw
        _ = (Nat.card F - 1) + (1 + weight (Dn.depB j - 1) (expTail (Dn.cB j))) := by rw [hsplit]
        _ = (Nat.card F - 1) + (1 + (n * Nat.card F + Xw)) := by
              rw [hih]
        _ = (Nat.card F) + (n * Nat.card F + Xw) := by
              have hq2 : 1 ≤ Nat.card F := by
                have h2 : 2 ≤ Nat.card F := card_ge_two F
                omega
              omega
        _ = (n + 1) * Nat.card F + Xw := by ring


/-- Padded values shift: the entry at `a+1` of a tuple is the entry at `a` of its tail. -/
lemma pad0_succ_expTail {d : ℕ} (t : Fin d → ℕ+) (a : ℕ) :
    pad0 t (a + 1) = pad0 (expTail t) a := by
  classical
  by_cases h : a + 1 < d
  · have ha : a < d - 1 := by omega
    have hp1 : pad0 t (a + 1) = (t ⟨a + 1, h⟩ : ℕ) := pad0_of_lt t h
    have hp2 : pad0 (expTail t) a = ((expTail t) ⟨a, ha⟩ : ℕ) := pad0_of_lt (expTail t) ha
    rw [hp1, hp2]
    rfl
  · have hge : d ≤ a + 1 := le_of_not_gt h
    have hp1 : pad0 t (a + 1) = 0 := pad0_of_ge t hge
    have hge2 : d - 1 ≤ a := by omega
    have hp2 : pad0 (expTail t) a = 0 := pad0_of_ge (expTail t) hge2
    rw [hp1, hp2]

/-- Type-2 member padded values at full positions `j + t` equal the `t`-th padded
entry of the level-`(k−j−1)` b-tuple (its head `1`, then the fiber tail). -/
lemma type2_pad0_shift (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i : D.ιB, ∀ (t : ℕ),
      pad0 (Q.c (Sum.inr (Sum.inl i))) (j + t) = pad0 (D.cB i) t := by
  classical
  intro D Bs Q i t
  have hQdep : Q.dep (Sum.inr (Sum.inl i)) = j + D.depB i := by
    have hlen : (sPrefix r s j (by omega) (by omega)).length = j - 1 :=
      sPrefix_length r s j (by omega) (by omega)
    have h1 := FixedOver.prependList_dep F Bs (sPrefix r s j (by omega) (by omega)) (Sum.inr (Sum.inl i))
    have h2 : Bs.dep (Sum.inr (Sum.inl i)) = D.depB i + 1 := by
      dsimp [Bs, ofBstarOver]
    rw [h1, h2, hlen]
    omega
  by_cases ht : t < D.depB i
  · cases t with
    | zero =>
        -- position j: value 1 = head of D.cB (padded, both in range)
        have hmj : j < Q.dep (Sum.inr (Sum.inl i)) := by
          rw [hQdep]
          omega
        have hh := BCqIter_head_one_data F (k - j - 1) R0 hbhd i
        have hh' : ((D.cB i) ⟨0, ht⟩ : ℕ) = 1 := by
          have hfin : (⟨0, ht⟩ : Fin (D.depB i)) = ⟨0, D.hdepB i⟩ := by
            apply Fin.ext
            rfl
          rw [hfin]
          exact hh
        rw [show j + 0 = j by omega]
        rw [pad0_of_lt (Q.c (Sum.inr (Sum.inl i))) hmj]
        rw [pad0_of_lt (D.cB i) ht]
        have hv := type2_one_at_j F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd i hmj
        rw [hv, hh']
    | succ t' =>
        have hsh := type2_tail_pad0 F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd i t'
        -- hsh : pad0 (Q.c) (j+1+t') = pad0 (expTail (D.cB i)) t'
        have hpe := pad0_succ_expTail (D.cB i) t'
        have hdom : j + (t' + 1) = j + 1 + t' := by omega
        rw [hdom]
        rw [hsh]
        rw [hpe.symm]
  · have htge : D.depB i ≤ t := le_of_not_gt ht
    have hgeQ : Q.dep (Sum.inr (Sum.inl i)) ≤ j + t := by
      rw [hQdep]
      omega
    rw [pad0_of_ge (Q.c (Sum.inr (Sum.inl i))) hgeQ]
    rw [pad0_of_ge (D.cB i) htge]

/-- ★ Weight of a type-2 member: the `s₁..s_j` front plus the level-`(k−j−1)` b-tuple. -/
lemma type2_weight_decompose (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i : D.ιB,
      weight (Q.dep (Sum.inr (Sum.inl i))) (Q.c (Sum.inr (Sum.inl i))) =
        psum s j + weight (D.depB i) (D.cB i) := by
  classical
  intro D Bs Q i
  have hQdep : Q.dep (Sum.inr (Sum.inl i)) = j + D.depB i := by
    have hlen : (sPrefix r s j (by omega) (by omega)).length = j - 1 :=
      sPrefix_length r s j (by omega) (by omega)
    have h1 := FixedOver.prependList_dep F Bs (sPrefix r s j (by omega) (by omega)) (Sum.inr (Sum.inl i))
    have h2 : Bs.dep (Sum.inr (Sum.inl i)) = D.depB i + 1 := by
      dsimp [Bs, ofBstarOver]
    rw [h1, h2, hlen]
    omega
  have hwpsum : weight (Q.dep (Sum.inr (Sum.inl i))) (Q.c (Sum.inr (Sum.inl i))) =
      psum (Q.c (Sum.inr (Sum.inl i))) (Q.dep (Sum.inr (Sum.inl i))) := by
    have hp := psum_ge_depth (Q.c (Sum.inr (Sum.inl i))) (m := Q.dep (Sum.inr (Sum.inl i))) (le_refl _)
    exact hp.symm
  have hsplit : psum (Q.c (Sum.inr (Sum.inl i))) (j + D.depB i) =
      psum (Q.c (Sum.inr (Sum.inl i))) j +
        (∑ t ∈ Finset.range (D.depB i), pad0 (Q.c (Sum.inr (Sum.inl i))) (j + t)) := by
    change (∑ x ∈ Finset.range (j + D.depB i), pad0 (Q.c (Sum.inr (Sum.inl i))) x) =
      (∑ x ∈ Finset.range j, pad0 (Q.c (Sum.inr (Sum.inl i))) x) +
        (∑ t ∈ Finset.range (D.depB i), pad0 (Q.c (Sum.inr (Sum.inl i))) (j + t))
    rw [Finset.sum_range_add]
  have htail : (∑ t ∈ Finset.range (D.depB i), pad0 (Q.c (Sum.inr (Sum.inl i))) (j + t)) =
      weight (D.depB i) (D.cB i) := by
    calc
      (∑ t ∈ Finset.range (D.depB i), pad0 (Q.c (Sum.inr (Sum.inl i))) (j + t))
          = (∑ t ∈ Finset.range (D.depB i), pad0 (D.cB i) t) := by
            apply Finset.sum_congr rfl
            intro t ht
            exact type2_pad0_shift F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd i t
      _ = psum (D.cB i) (D.depB i) := by rfl
      _ = weight (D.depB i) (D.cB i) := by
            have hp' := psum_ge_depth (D.cB i) (m := D.depB i) (le_refl _)
            exact hp'
  have hpj : psum (Q.c (Sum.inr (Sum.inl i))) j = psum s j :=
    type2_psum_j F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd i
  calc
    weight (Q.dep (Sum.inr (Sum.inl i))) (Q.c (Sum.inr (Sum.inl i)))
        = psum (Q.c (Sum.inr (Sum.inl i))) (Q.dep (Sum.inr (Sum.inl i))) := hwpsum
    _ = psum (Q.c (Sum.inr (Sum.inl i))) (j + D.depB i) := by
          exact congrArg (psum (Q.c (Sum.inr (Sum.inl i)))) hQdep
    _ = psum (Q.c (Sum.inr (Sum.inl i))) j +
          (∑ t ∈ Finset.range (D.depB i), pad0 (Q.c (Sum.inr (Sum.inl i))) (j + t)) := hsplit
    _ = psum s j + weight (D.depB i) (D.cB i) := by
          rw [hpj, htail]


/-- ★ Type-2 weight preservation: a type-2 member has weight `w(s)` (given every
level-0 b-tail has weight `s_k − 1 + s_{k+1} + … + s_r` — the `hleB`-weight content). -/
lemma type2_weight_eq (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hmid : ∀ i : Fin r, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < k - 1 → (s i : ℕ) = Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i : D.ιB,
      (∀ j' : R0.ιB,
        weight (R0.depB j' - 1) (expTail (R0.cB j')) =
          psum s r - psum s (k - 1) - 1) →
        weight (Q.dep (Sum.inr (Sum.inl i))) (Q.c (Sum.inr (Sum.inl i))) = weight r s := by
  classical
  intro D Bs Q i hXw
  let Xw : ℕ := psum s r - psum s (k - 1) - 1
  have hdec := type2_weight_decompose F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd i
  -- hdec : w(Q.c) = psum s j + w(D.cB i)
  have hwt := weight_head_tail (D.hdepB i) (D.cB i)
  have hh := BCqIter_head_one_data F (k - j - 1) R0 hbhd i
  have hfib := BCq_fiber_weight_X F (k - j - 1) R0 hbhd Xw (fun j' => by
    simpa [Xw] using hXw j') i
  -- hfib : w(expTail (D.cB i)) = (k−j−1)·q + Xw
  have hpkm1 : psum s (k - 1) = psum s j + (k - 1 - j) * Nat.card F := by
    apply psum_const_block (s := s) (j := j) (m := k - 1) (q := Nat.card F)
    · omega
    · intro x hxj hxkm1
      have hxr : x < r := by omega
      have hm := hmid ⟨x, hxr⟩ hxj hxkm1
      rw [pad0_of_lt s hxr]
      exact hm
  have ha1 : 1 ≤ psum s r - psum s (k - 1) := by
    -- psum s r ≥ psum s (k−1) + s_{k−1} ≥ psum s (k−1) + 1
    have hkm1 : k - 1 < r := by omega
    have hsu := psum_succ s (k - 1)
    have hkk : (k - 1) + 1 = k := by omega
    have hpk : psum s k = psum s (k - 1) + (s ⟨k - 1, hkm1⟩ : ℕ) := by
      rw [hkk] at hsu
      rw [hsu]
      rw [pad0_of_lt s hkm1]
    have hmono : psum s k ≤ psum s r := psum_mono s (by omega)
    have hsk : 1 ≤ (s ⟨k - 1, hkm1⟩ : ℕ) := (s ⟨k - 1, hkm1⟩).pos
    omega
  have h1x : 1 + Xw = psum s r - psum s (k - 1) := by
    dsimp [Xw]
    omega
  calc
    weight (Q.dep (Sum.inr (Sum.inl i))) (Q.c (Sum.inr (Sum.inl i)))
        = psum s j + weight (D.depB i) (D.cB i) := hdec
    _ = psum s j + (1 + weight (D.depB i - 1) (expTail (D.cB i))) := by
          rw [hwt]
          rw [hh]
    _ = psum s j + (1 + ((k - j - 1) * Nat.card F + Xw)) := by
          rw [hfib]
    _ = psum s j + ((k - j - 1) * Nat.card F + (1 + Xw)) := by omega
    _ = psum s j + (k - j - 1) * Nat.card F + (psum s r - psum s (k - 1)) := by
          rw [h1x]
          omega
    _ = weight r s := by
          rw [← psum_ge_depth s (le_refl r)]
          have hn' : (k - j - 1) = (k - 1 - j) := by omega
          rw [hn']
          rw [← hpkm1]
          omega


/-- Type-3 member padded values at full positions `j + t` equal the `t`-th padded
entry of the b-tuple tail (the type-3 member has head `s_j+1` at `j−1`, then the
same fiber as type-2). -/
lemma type3_tail_pad0 (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i : D.ιB, ∀ (t : ℕ),
      pad0 (Q.c (Sum.inr (Sum.inr i))) (j + t) = pad0 (expTail (D.cB i)) t := by
  classical
  intro D Bs Q i t
  have hlen : (sPrefix r s j (by omega) (by omega)).length = j - 1 :=
    sPrefix_length r s j (by omega) (by omega)
  have hQdep : Q.dep (Sum.inr (Sum.inr i)) =
      Bs.dep (Sum.inr (Sum.inr i)) + (sPrefix r s j (by omega) (by omega)).length := by
    exact FixedOver.prependList_dep F Bs (sPrefix r s j (by omega) (by omega)) (Sum.inr (Sum.inr i))
  have hBsdep : Bs.dep (Sum.inr (Sum.inr i)) = D.depB i := by
    dsimp [Bs, ofBstarOver]
  by_cases hm : j + t < Q.dep (Sum.inr (Sum.inr i))
  · have hge : (sPrefix r s j (by omega) (by omega)).length ≤ j + t := by omega
    have b' : (j + t) - (sPrefix r s j (by omega) (by omega)).length < Bs.dep (Sum.inr (Sum.inr i)) := by
      rw [hBsdep]
      have hm0 : j + t < Q.dep (Sum.inr (Sum.inr i)) := hm
      rw [hQdep, hBsdep, hlen] at hm0
      omega
    have ht1b : t + 1 < D.depB i := by
      have hm0 : j + t < Q.dep (Sum.inr (Sum.inr i)) := hm
      rw [hQdep, hBsdep, hlen] at hm0
      omega
    have hval : ((Q.c (Sum.inr (Sum.inr i))) ⟨j + t, hm⟩ : ℕ) =
        ((D.cB i) ⟨t + 1, ht1b⟩ : ℕ) := by
      have h1 : ((Q.c (Sum.inr (Sum.inr i))) ⟨j + t, hm⟩ : ℕ) =
          ((Bs.c (Sum.inr (Sum.inr i))) ⟨(j + t) - (sPrefix r s j (by omega) (by omega)).length, b'⟩ : ℕ) := by
        have hv := prependList_c_base_value F Bs (sPrefix r s j (by omega) (by omega))
          (Sum.inr (Sum.inr i)) (j + t) hm hge
        apply congrArg (fun v : ℕ+ => (v : ℕ))
        calc
          (Q.c (Sum.inr (Sum.inr i))) ⟨j + t, hm⟩
              = (Bs.c (Sum.inr (Sum.inr i))) ⟨(j + t) - (sPrefix r s j (by omega) (by omega)).length,
                  (by
                    have hd := FixedOver.prependList_dep F Bs (sPrefix r s j (by omega) (by omega)) (Sum.inr (Sum.inr i))
                    rw [hd] at hm
                    omega)⟩ := hv
          _ = (Bs.c (Sum.inr (Sum.inr i))) ⟨(j + t) - (sPrefix r s j (by omega) (by omega)).length, b'⟩ := by
                congr 1
      have hcBs : Bs.c (Sum.inr (Sum.inr i)) = headAdd (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i) := by
        dsimp [Bs, ofBstarOver, D]
      have hbp : (j + t) - (sPrefix r s j (by omega) (by omega)).length = t + 1 := by omega
      have h2 : ((Bs.c (Sum.inr (Sum.inr i))) ⟨(j + t) - (sPrefix r s j (by omega) (by omega)).length, b'⟩ : ℕ) =
          ((headAdd (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i))
            ⟨(j + t) - (sPrefix r s j (by omega) (by omega)).length, b'⟩ : ℕ) := by
        apply congrArg (fun v : ℕ+ => (v : ℕ))
        exact congrFun hcBs ⟨(j + t) - (sPrefix r s j (by omega) (by omega)).length, b'⟩
      have h3 : ((headAdd (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i))
            ⟨(j + t) - (sPrefix r s j (by omega) (by omega)).length, b'⟩ : ℕ) =
          ((D.cB i) ⟨t + 1, ht1b⟩ : ℕ) := by
        -- headAdd at position t+1 ≥ 1 is the old tuple at t+1
        have hb2 : t + 1 < D.depB i := by
          have hb2' := b'
          simpa [hbp, hBsdep] using hb2'
        have hidx : (⟨(j + t) - (sPrefix r s j (by omega) (by omega)).length, b'⟩ : Fin (D.depB i)) =
            ⟨t + 1, hb2⟩ := by
          apply Fin.ext
          simp [hbp]
        have hhadd : (headAdd (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i)) ⟨t + 1, hb2⟩ =
            (D.cB i) ⟨t + 1, hb2⟩ := by
          have hnz : t + 1 ≠ 0 := by omega
          dsimp [headAdd]
        have h3' : (headAdd (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i))
                ⟨(j + t) - (sPrefix r s j (by omega) (by omega)).length, b'⟩ =
            (D.cB i) ⟨t + 1, ht1b⟩ := by
          calc
            (headAdd (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i))
                  ⟨(j + t) - (sPrefix r s j (by omega) (by omega)).length, b'⟩
                = (headAdd (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i)) ⟨t + 1, hb2⟩ := by
                  rw [hidx]
            _ = (D.cB i) ⟨t + 1, hb2⟩ := hhadd
            _ = (D.cB i) ⟨t + 1, ht1b⟩ := by
                  congr 1
        exact congrArg (fun v : ℕ+ => (v : ℕ)) h3'
      calc
        ((Q.c (Sum.inr (Sum.inr i))) ⟨j + t, hm⟩ : ℕ)
            = ((Bs.c (Sum.inr (Sum.inr i))) ⟨(j + t) - (sPrefix r s j (by omega) (by omega)).length, b'⟩ : ℕ) := h1
        _ = ((headAdd (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i))
              ⟨(j + t) - (sPrefix r s j (by omega) (by omega)).length, b'⟩ : ℕ) := h2
        _ = ((D.cB i) ⟨t + 1, ht1b⟩ : ℕ) := h3
    rw [pad0_of_lt (Q.c (Sum.inr (Sum.inr i))) hm]
    have hdep : t < (D.depB i) - 1 := by omega
    rw [pad0_of_lt (expTail (D.cB i)) hdep]
    -- ((D.cB i)⟨t+1⟩ : ℕ) = ((expTail (D.cB i))⟨t⟩ : ℕ):
    have h4 : ((D.cB i) ⟨t + 1, ht1b⟩ : ℕ) = ((expTail (D.cB i)) ⟨t, hdep⟩ : ℕ) := by
      rw [expTail]
    exact hval.trans h4
  · have hgeQ : Q.dep (Sum.inr (Sum.inr i)) ≤ j + t := le_of_not_gt hm
    have hp1 : pad0 (Q.c (Sum.inr (Sum.inr i))) (j + t) = 0 := pad0_of_ge (Q.c (Sum.inr (Sum.inr i))) hgeQ
    rw [hp1]
    have hdep : (D.depB i) - 1 ≤ t := by
      have hge0 : Q.dep (Sum.inr (Sum.inr i)) ≤ j + t := hgeQ
      rw [hQdep, hBsdep, hlen] at hge0
      omega
    have hp2 : pad0 (expTail (D.cB i)) t = 0 := pad0_of_ge (expTail (D.cB i)) hdep
    rw [hp2]


/-- Type-3 front sum: the first `j−1` entries are `s₁..s_{j−1}`. -/
lemma type3_psum_front (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i : D.ιB, psum (Q.c (Sum.inr (Sum.inr i))) (j - 1) = psum s (j - 1) := by
  classical
  intro D Bs Q i
  have hQdep : Q.dep (Sum.inr (Sum.inr i)) =
      Bs.dep (Sum.inr (Sum.inr i)) + (sPrefix r s j (by omega) (by omega)).length := by
    exact FixedOver.prependList_dep F Bs (sPrefix r s j (by omega) (by omega)) (Sum.inr (Sum.inr i))
  have hBsdep : Bs.dep (Sum.inr (Sum.inr i)) = D.depB i := by
    dsimp [Bs, ofBstarOver]
  apply psum_eq_of_pad0_eq
  intro x hx
  have hx1 : x < j - 1 := hx
  have hxQ : x < Q.dep (Sum.inr (Sum.inr i)) := by
    have hQd : Q.dep (Sum.inr (Sum.inr i)) = (j - 1) + D.depB i := by
      have hlen : (sPrefix r s j (by omega) (by omega)).length = j - 1 :=
        sPrefix_length r s j (by omega) (by omega)
      rw [hQdep, hBsdep, hlen]
      omega
    rw [hQd]
    omega
  have hxr : x < r := by
    have : x < j - 1 := hx1
    omega
  have hv := member_prefix_pos F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd (Sum.inr (Sum.inr i)) x hx1 hxQ
  rw [pad0_of_lt (Q.c (Sum.inr (Sum.inr i))) hxQ]
  rw [pad0_of_lt s hxr]
  exact congrArg (fun t : ℕ+ => (t : ℕ)) hv


/-- ★ The headAdd shift: type-3 member padded values at full positions `(j−1)+t`
equal the `t`-th padded entry of the merged tuple `headAdd s_j (D.cB i)` (its head
`s_j+1`, then the fiber tail). -/
lemma type3_pad0_headAdd (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i : D.ιB, ∀ (t : ℕ),
      pad0 (Q.c (Sum.inr (Sum.inr i))) ((j - 1) + t) =
        pad0 (headAdd (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i)) t := by
  classical
  intro D Bs Q i t
  have hlen : (sPrefix r s j (by omega) (by omega)).length = j - 1 :=
    sPrefix_length r s j (by omega) (by omega)
  have hQdep : Q.dep (Sum.inr (Sum.inr i)) = (j - 1) + D.depB i := by
    have h1 := FixedOver.prependList_dep F Bs (sPrefix r s j (by omega) (by omega)) (Sum.inr (Sum.inr i))
    have h2 : Bs.dep (Sum.inr (Sum.inr i)) = D.depB i := by
      dsimp [Bs, ofBstarOver]
    rw [h1, h2, hlen]
    omega
  have hBsdep : Bs.dep (Sum.inr (Sum.inr i)) = D.depB i := by
    dsimp [Bs, ofBstarOver]
  by_cases ht : t < D.depB i
  · cases t with
    | zero =>
        -- position j−1: the merged head s_j + 1 on both sides
        have hmj : j - 1 < Q.dep (Sum.inr (Sum.inr i)) := by
          rw [hQdep]
          omega
        have hsjadd := type3_sjadd_one_at F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd i hmj
        -- hsjadd : ((Q.c…)⟨j−1, hmj⟩ : ℕ) = (s⟨j−1⟩ : ℕ) + 1
        rw [show (j - 1) + 0 = j - 1 by omega]
        rw [pad0_of_lt (Q.c (Sum.inr (Sum.inr i))) hmj]
        -- right side: headAdd-head value = s_j + D.cB-head = s_j + 1
        have hh := BCqIter_head_one_data F (k - j - 1) R0 hbhd i
        have hhadd := headAdd_head (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i)
        -- hhadd : headAdd s_j (D.hdepB i)(D.cB i)⟨0, D.hdepB i⟩ = ⟨s_j + head⟩
        have hr : pad0 (headAdd (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i)) 0 =
            (s ⟨j - 1, by omega⟩ : ℕ) + 1 := by
          have hz : 0 < D.depB i := D.hdepB i
          rw [pad0_of_lt (headAdd (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i)) hz]
          -- value = headAdd⟨0⟩: use the head-value:
          have hidx : (⟨0, hz⟩ : Fin (D.depB i)) = ⟨0, D.hdepB i⟩ := by
            apply Fin.ext
            rfl
          rw [hidx]
          have hv := congrArg (fun u : ℕ+ => (u : ℕ)) hhadd
          -- hv : ((headAdd…)⟨0, D.hdepB i⟩ : ℕ) = (s⟨j−1⟩ : ℕ) + ((D.cB i)⟨0, D.hdepB i⟩ : ℕ)
          have hh1 : ((D.cB i) ⟨0, D.hdepB i⟩ : ℕ) = 1 := hh
          rw [hv, hh1]
          rfl
        rw [hr]
        exact hsjadd
    | succ t' =>
        -- position j+t': the D.cB tail entry t' = t'+1-st entry; headAdd keeps it
        have hsh := type3_tail_pad0 F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd i t'
        have hdom : (j - 1) + (t' + 1) = j + t' := by omega
        rw [hdom]
        rw [hsh]
        -- right side: pad0 (headAdd) (t'+1) = headAdd⟨t'+1⟩ = D.cB⟨t'+1⟩ = expTail⟨t'⟩
        have ht1 : t' + 1 < D.depB i := ht
        have hha : (headAdd (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i)) ⟨t' + 1, ht1⟩ =
            (D.cB i) ⟨t' + 1, ht1⟩ := by
          have hnz : t' + 1 ≠ 0 := by omega
          dsimp [headAdd]
        have hr : pad0 (headAdd (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i)) (t' + 1) =
            ((D.cB i) ⟨t' + 1, ht1⟩ : ℕ) := by
          rw [pad0_of_lt (headAdd (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i)) ht1]
          exact congrArg (fun u : ℕ+ => (u : ℕ)) hha
        have hdep' : t' < D.depB i - 1 := by omega
        have hl : pad0 (expTail (D.cB i)) t' = ((D.cB i) ⟨t' + 1, ht1⟩ : ℕ) := by
          rw [pad0_of_lt (expTail (D.cB i)) hdep']
          rfl
        rw [hr]
        rw [hl]
  · have htge : D.depB i ≤ t := le_of_not_gt ht
    have hgeQ : Q.dep (Sum.inr (Sum.inr i)) ≤ (j - 1) + t := by
      rw [hQdep]
      omega
    rw [pad0_of_ge (Q.c (Sum.inr (Sum.inr i))) hgeQ]
    rw [pad0_of_ge (headAdd (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i)) htge]


/-- The tail of a `headAdd`-merged tuple is the tail of the original. -/
lemma expTail_headAdd {d : ℕ} (hdpos : 0 < d) (v : ℕ+) (t : Fin d → ℕ+) :
    expTail (headAdd v hdpos t) = expTail t := by
  classical
  funext a
  rfl

/-- Weight of the `headAdd`-merged tuple: the head `v + t₁` plus the tail. -/
lemma headAdd_weight {d : ℕ} (hdpos : 0 < d) (v : ℕ+) (t : Fin d → ℕ+) :
    weight d (headAdd v hdpos t) = (v : ℕ) + (t ⟨0, hdpos⟩ : ℕ) + weight (d - 1) (expTail t) := by
  classical
  have hh := headAdd_head v hdpos t
  have ht := expTail_headAdd hdpos v t
  have hwt := weight_head_tail hdpos (headAdd v hdpos t)
  -- hwt : weight d (headAdd) = (headAdd⟨0⟩ : ℕ) + weight (d−1)(expTail (headAdd))
  have hv := congrArg (fun u : ℕ+ => (u : ℕ)) hh
  calc
    weight d (headAdd v hdpos t) = ((headAdd v hdpos t) ⟨0, hdpos⟩ : ℕ) + weight (d - 1) (expTail (headAdd v hdpos t)) := hwt
    _ = ((v : ℕ) + (t ⟨0, hdpos⟩ : ℕ)) + weight (d - 1) (expTail t) := by
          rw [hv]
          rw [ht]
          rfl


/-- ★ Weight of a type-3 member: the `s₁..s_{j−1}` front, the merged head `s_j+1`, and
the b-fiber tail. -/
lemma type3_weight_decompose (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i : D.ιB,
      weight (Q.dep (Sum.inr (Sum.inr i))) (Q.c (Sum.inr (Sum.inr i))) =
        psum s (j - 1) + ((s ⟨j - 1, by omega⟩ : ℕ) + 1 +
          weight (D.depB i - 1) (expTail (D.cB i))) := by
  classical
  intro D Bs Q i
  have hQdep : Q.dep (Sum.inr (Sum.inr i)) = (j - 1) + D.depB i := by
    have hlen : (sPrefix r s j (by omega) (by omega)).length = j - 1 :=
      sPrefix_length r s j (by omega) (by omega)
    have h1 := FixedOver.prependList_dep F Bs (sPrefix r s j (by omega) (by omega)) (Sum.inr (Sum.inr i))
    have h2 : Bs.dep (Sum.inr (Sum.inr i)) = D.depB i := by
      dsimp [Bs, ofBstarOver]
    rw [h1, h2, hlen]
    omega
  have hwpsum : weight (Q.dep (Sum.inr (Sum.inr i))) (Q.c (Sum.inr (Sum.inr i))) =
      psum (Q.c (Sum.inr (Sum.inr i))) (Q.dep (Sum.inr (Sum.inr i))) := by
    have hp := psum_ge_depth (Q.c (Sum.inr (Sum.inr i))) (m := Q.dep (Sum.inr (Sum.inr i))) (le_refl _)
    exact hp.symm
  have hsplit : psum (Q.c (Sum.inr (Sum.inr i))) ((j - 1) + D.depB i) =
      psum (Q.c (Sum.inr (Sum.inr i))) (j - 1) +
        (∑ t ∈ Finset.range (D.depB i), pad0 (Q.c (Sum.inr (Sum.inr i))) ((j - 1) + t)) := by
    change (∑ x ∈ Finset.range ((j - 1) + D.depB i), pad0 (Q.c (Sum.inr (Sum.inr i))) x) =
      (∑ x ∈ Finset.range (j - 1), pad0 (Q.c (Sum.inr (Sum.inr i))) x) +
        (∑ t ∈ Finset.range (D.depB i), pad0 (Q.c (Sum.inr (Sum.inr i))) ((j - 1) + t))
    rw [Finset.sum_range_add]
  have hh := BCqIter_head_one_data F (k - j - 1) R0 hbhd i
  have htail : (∑ t ∈ Finset.range (D.depB i), pad0 (Q.c (Sum.inr (Sum.inr i))) ((j - 1) + t)) =
      ((s ⟨j - 1, by omega⟩ : ℕ) + 1 + weight (D.depB i - 1) (expTail (D.cB i))) := by
    calc
      (∑ t ∈ Finset.range (D.depB i), pad0 (Q.c (Sum.inr (Sum.inr i))) ((j - 1) + t))
          = (∑ t ∈ Finset.range (D.depB i),
              pad0 (headAdd (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i)) t) := by
            apply Finset.sum_congr rfl
            intro t ht
            exact type3_pad0_headAdd F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd i t
      _ = psum (headAdd (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i)) (D.depB i) := by rfl
      _ = weight (D.depB i) (headAdd (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i)) := by
            have hp' := psum_ge_depth (headAdd (s ⟨j - 1, by omega⟩) (D.hdepB i) (D.cB i))
              (m := D.depB i) (le_refl _)
            exact hp'
      _ = ((s ⟨j - 1, by omega⟩ : ℕ) + 1 + weight (D.depB i - 1) (expTail (D.cB i))) := by
            have hw := headAdd_weight (D.hdepB i) (s ⟨j - 1, by omega⟩) (D.cB i)
            -- hw : weight (depB) (headAdd s_j (D.hdepB i)(D.cB i)) =
            --      (s_j:ℕ) + ((D.cB i)⟨0, hdepB i⟩:ℕ) + weight(depB−1)(expTail (D.cB i))
            rw [hw]
            have hh1 : ((D.cB i) ⟨0, D.hdepB i⟩ : ℕ) = 1 := hh
            rw [hh1]
  have hpfront : psum (Q.c (Sum.inr (Sum.inr i))) (j - 1) = psum s (j - 1) :=
    type3_psum_front F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd i
  calc
    weight (Q.dep (Sum.inr (Sum.inr i))) (Q.c (Sum.inr (Sum.inr i)))
        = psum (Q.c (Sum.inr (Sum.inr i))) (Q.dep (Sum.inr (Sum.inr i))) := hwpsum
    _ = psum (Q.c (Sum.inr (Sum.inr i))) ((j - 1) + D.depB i) := by
          exact congrArg (psum (Q.c (Sum.inr (Sum.inr i)))) hQdep
    _ = psum (Q.c (Sum.inr (Sum.inr i))) (j - 1) +
          (∑ t ∈ Finset.range (D.depB i), pad0 (Q.c (Sum.inr (Sum.inr i))) ((j - 1) + t)) := hsplit
    _ = psum s (j - 1) + ((s ⟨j - 1, by omega⟩ : ℕ) + 1 +
          weight (D.depB i - 1) (expTail (D.cB i))) := by
          rw [hpfront, htail]


/-- ★ Type-3 weight preservation: a type-3 member has weight `w(s)` (given every
level-0 b-tail has weight `s_k − 1 + s_{k+1} + … + s_r` — the `hleB`-weight content). -/
lemma type3_weight_eq (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hmid : ∀ i : Fin r, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < k - 1 → (s i : ℕ) = Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i : D.ιB,
      (∀ j' : R0.ιB,
        weight (R0.depB j' - 1) (expTail (R0.cB j')) =
          psum s r - psum s (k - 1) - 1) →
        weight (Q.dep (Sum.inr (Sum.inr i))) (Q.c (Sum.inr (Sum.inr i))) = weight r s := by
  classical
  intro D Bs Q i hXw
  let Xw : ℕ := psum s r - psum s (k - 1) - 1
  have hdec := type3_weight_decompose F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd i
  -- hdec : w(Q.c) = psum s (j−1) + (s_j + 1 + w(expTail))
  have hfib := BCq_fiber_weight_X F (k - j - 1) R0 hbhd Xw (fun j' => by
    simpa [Xw] using hXw j') i
  -- hfib : w(expTail (D.cB i)) = (k−j−1)·q + Xw
  have hpkm1 : psum s (k - 1) = psum s j + (k - 1 - j) * Nat.card F := by
    apply psum_const_block (s := s) (j := j) (m := k - 1) (q := Nat.card F)
    · omega
    · intro x hxj hxkm1
      have hxr : x < r := by omega
      have hm := hmid ⟨x, hxr⟩ hxj hxkm1
      rw [pad0_of_lt s hxr]
      exact hm
  have hsu := psum_succ s (j - 1)
  have hjj : (j - 1) + 1 = j := by omega
  have hpj : psum s j = psum s (j - 1) + (s ⟨j - 1, by omega⟩ : ℕ) := by
    rw [hjj] at hsu
    rw [hsu]
    rw [pad0_of_lt s (by omega : j - 1 < r)]
  have hpkm1' : psum s (k - 1) = psum s (j - 1) + (s ⟨j - 1, by omega⟩ : ℕ) +
      (k - 1 - j) * Nat.card F := by
    rw [hpkm1, hpj]
  have ha1 : 1 ≤ psum s r - psum s (k - 1) := by
    have hkm1 : k - 1 < r := by omega
    have hsu2 := psum_succ s (k - 1)
    have hkk : (k - 1) + 1 = k := by omega
    have hpk : psum s k = psum s (k - 1) + (s ⟨k - 1, hkm1⟩ : ℕ) := by
      rw [hkk] at hsu2
      rw [hsu2]
      rw [pad0_of_lt s hkm1]
    have hmono : psum s k ≤ psum s r := psum_mono s (by omega)
    have hsk : 1 ≤ (s ⟨k - 1, hkm1⟩ : ℕ) := (s ⟨k - 1, hkm1⟩).pos
    omega
  have h1x : 1 + Xw = psum s r - psum s (k - 1) := by
    dsimp [Xw]
    omega
  calc
    weight (Q.dep (Sum.inr (Sum.inr i))) (Q.c (Sum.inr (Sum.inr i)))
        = psum s (j - 1) + ((s ⟨j - 1, by omega⟩ : ℕ) + 1 +
            weight (D.depB i - 1) (expTail (D.cB i))) := hdec
    _ = psum s (j - 1) + ((s ⟨j - 1, by omega⟩ : ℕ) + 1 +
            ((k - j - 1) * Nat.card F + Xw)) := by
          rw [hfib]
    _ = psum s (j - 1) + (s ⟨j - 1, by omega⟩ : ℕ) +
          ((k - j - 1) * Nat.card F + (1 + Xw)) := by omega
    _ = psum s (j - 1) + (s ⟨j - 1, by omega⟩ : ℕ) +
          ((k - j - 1) * Nat.card F + (psum s r - psum s (k - 1))) := by
          rw [h1x]
    _ = psum s (j - 1) + (s ⟨j - 1, by omega⟩ : ℕ) +
          (k - 1 - j) * Nat.card F + (psum s r - psum s (k - 1)) := by
          have hn' : (k - j - 1) = (k - 1 - j) := by omega
          rw [hn']
          omega
    _ = weight r s := by
          rw [← psum_ge_depth s (le_refl r)]
          rw [← hpkm1']
          omega


end ZagierHoffmanPositiveChar
