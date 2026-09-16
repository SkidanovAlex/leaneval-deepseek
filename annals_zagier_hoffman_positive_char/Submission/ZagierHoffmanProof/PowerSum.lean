import ChallengeDeps
import Submission.ZagierHoffmanProof.Block
import Submission.Commons.Data.Fin.prod_split_head
import Submission.Commons.FieldTheory.Polynomial.card_monic_degree

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Polynomial RatFunc
open scoped WithZero Topology BigOperators
open WithZero

/-!
# Power sums (`§2.1` of the paper)

For a tuple of exponents `𝔰 : Fin r → ℕ+` and an integer `d`, the *power sum*
`S_d(𝔰)` (defined in `Block.lean` as the sum of the zeta summands over the degree-`d`
block) and its "strictly-less" sibling `S_<d(𝔰)` (sum over tuples whose leading degree
is `< d`) are the atoms of the paper's algebraic calculus.

Key recursion (paper (2.3)-style, 0-indexed): for depth `r ≥ 2`,
`S_d(s₀,s₁,…,s_{r-1}) = P_d(s₀) · S_<d(s₁,…,s_{r-1})`, where `P_d(n)` is the depth-one
power sum over monic polynomials of degree `d`.  The proof factors the degree-`d` block
of length-`r` tuples as (leading monic polynomial of degree `d`) × (length-`(r-1)` tuple
with all degrees `< d`).
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Tuples of length `r ≥ 1` whose leading polynomial has degree `< d`. -/
def blockSetLT (r : ℕ) (hr : 0 < r) (d : ℕ) : Set (monicStrictAntiNatDegree F r) :=
  {a | (a.val ⟨0, hr⟩).natDegree < d}

/-- The degree-`< d` block is finite (any entry is then monic of degree `< d`). -/
theorem finite_blockLT {r : ℕ} (hr : 0 < r) (d : ℕ) :
    Set.Finite (blockSetLT F r hr d) := by
  classical
  simpa [blockSetLT] using finite_deg_lt F hr d

/-- `S_<d(𝔰)`: sum of the zeta summands over tuples whose leading degree is `< d`. -/
noncomputable def S_lt (r : ℕ) (hr : 0 < r) (𝔰 : Fin r → ℕ+) (d : ℕ) :
    RatFunc.CompletionAtInfty F :=
  ∑' a : {a : monicStrictAntiNatDegree F r // a ∈ blockSetLT F r hr d},
    zetaTerm F 𝔰 a.1

/-- Monic polynomials of degree exactly `d`. -/
def MonicDeg (d : ℕ) : Set F[X] := {p : F[X] | p.Monic ∧ p.natDegree = d}

/-- The monic polynomials of degree `d` form a finite set. -/
theorem finite_MonicDeg (d : ℕ) : Set.Finite (MonicDeg F d) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have hle : Set.Finite {p : F[X] | p.Monic ∧ p.natDegree ≤ d} := by
    change Finite {p : F[X] // p.Monic ∧ p.natDegree ≤ d}
    exact Commons.FieldTheory.Polynomial.finite_monic_le F d
  exact Set.Finite.subset hle (by
    intro p hp
    exact ⟨hp.1, le_of_eq hp.2⟩)

/-- Depth-one power sum `P_d(n) = ∑_{a monic, deg a = d} a^{-n}` (a finite sum). -/
noncomputable def P (d : ℕ) (n : ℕ+) : RatFunc.CompletionAtInfty F :=
  ∑' a : {p : F[X] // p ∈ MonicDeg F d},
    (((a.1 : RatFunc F) : RatFunc.CompletionAtInfty F) ^ (n : ℕ))⁻¹



/-- The tail of a length-`r` tuple: entries at indices `1,…,r-1`, viewed as a tuple of
length `r - 1`. -/
noncomputable def tailTuple {r : ℕ} (hr : 1 < r) (a : monicStrictAntiNatDegree F r) :
    monicStrictAntiNatDegree F (r - 1) :=
  ⟨fun j : Fin (r - 1) => a.val ⟨j.1 + 1, by omega⟩,
    ⟨by
      intro j k hjk
      have hk : (j.1 : ℕ) < k.1 := Fin.lt_def.mp hjk
      have hlt : (⟨j.1 + 1, by omega⟩ : Fin r) < ⟨k.1 + 1, by omega⟩ :=
        (Fin.mk_lt_mk).2 (by omega)
      simpa using a.2.1 hlt,
      by
        intro j
        exact a.2.2 ⟨j.1 + 1, by omega⟩⟩⟩

/-- The tail of a degree-`d` tuple has leading degree `< d`. -/
lemma tailTuple_leading_lt {r : ℕ} (hr : 1 < r) (hr0 : 0 < r) (hrT : 0 < r - 1)
    (d : ℕ) (a : monicStrictAntiNatDegree F r) (ha : (a.val ⟨0, hr0⟩).natDegree = d) :
    ((tailTuple F hr a).val ⟨0, hrT⟩).natDegree < d := by
  have hlt : (a.val ⟨1, by omega⟩).natDegree < (a.val ⟨0, hr0⟩).natDegree := by
    have h01 : (⟨0, hr0⟩ : Fin r) < ⟨1, by omega⟩ := (Fin.mk_lt_mk).2 (by omega)
    simpa using a.2.1 h01
  simpa [tailTuple, ha] using hlt



/-- The zeta summand of a tuple factorizes as the leading term times the summand of its
tail. -/
lemma zetaTerm_fact {r : ℕ} (hr : 1 < r) (hr0 : 0 < r) (𝔰 : Fin r → ℕ+)
    (a : monicStrictAntiNatDegree F r) :
    zetaTerm F 𝔰 a =
      ((((a.val ⟨0, hr0⟩ : RatFunc F) : RatFunc.CompletionAtInfty F) ^ (𝔰 ⟨0, hr0⟩ : ℕ))⁻¹) *
      zetaTerm F (fun j : Fin (r - 1) => 𝔰 ⟨j.1 + 1, by omega⟩) (tailTuple F hr a) := by
  let c : Fin r → RatFunc.CompletionAtInfty F := fun i =>
    ((a.val i : RatFunc F) : RatFunc.CompletionAtInfty F)
  let e : Fin (r - 1) → RatFunc.CompletionAtInfty F := fun j =>
    ((a.val ⟨j.1 + 1, by omega⟩ : RatFunc F) : RatFunc.CompletionAtInfty F)
  have hsplit : (∏ i : Fin r, c i ^ (𝔰 i : ℕ)) =
      c ⟨0, hr0⟩ ^ (𝔰 ⟨0, hr0⟩ : ℕ) *
        ∏ j : Fin (r - 1), e j ^ (𝔰 ⟨j.1 + 1, by omega⟩ : ℕ) := by
    have hs := Commons.Data.Fin.prod_split_head (M := RatFunc.CompletionAtInfty F)
      (r := r) hr0 (g := fun i : Fin r => c i ^ (𝔰 i : ℕ))
    simpa [c, e] using hs
  unfold zetaTerm tailTuple
  rw [hsplit]
  rw [mul_inv_rev]
  rw [mul_comm]

/-- Head (index-0 entry) of a length-`r` function. -/
noncomputable def headOf (r : ℕ) (hr : 0 < r) (a : Fin r → F[X]) : F[X] :=
  a ⟨0, hr⟩

/-- Tail of a length-`r` function: entries at indices `1,…,r-1`. -/
noncomputable def tailOf (r : ℕ) (hr : 1 < r) (a : Fin r → F[X]) : Fin (r - 1) → F[X] :=
  fun j => a ⟨j.1 + 1, by omega⟩

/-- Build a length-`r` function from a head polynomial and a tail function. -/
noncomputable def consTuple (r : ℕ) (hr : 1 < r) (p : F[X]) (b : Fin (r - 1) → F[X]) :
    Fin r → F[X] :=
  fun i => if h : (i : ℕ) = 0 then p else b ⟨i.1 - 1, by omega⟩

/-- Recombining head and tail recovers the original function. -/
lemma consTuple_head_tail (r : ℕ) (hr : 1 < r) (hr0 : 0 < r) (a : Fin r → F[X]) :
    consTuple F r hr (headOf F r hr0 a) (tailOf F r hr a) = a := by
  funext i
  by_cases hi : (i : ℕ) = 0
  · have hi0 : i = (⟨0, hr0⟩ : Fin r) := Fin.ext (by simpa using hi)
    unfold consTuple headOf
    rw [dif_pos hi]
    rw [hi0]
  · unfold consTuple tailOf
    rw [dif_neg hi]
    apply congrArg a
    apply Fin.ext
    simp
    omega

/-- Taking head and tail of a concatenation recovers the parts. -/
lemma head_tail_consTuple (r : ℕ) (hr : 1 < r) (p : F[X]) (b : Fin (r - 1) → F[X]) :
    headOf F r (by omega) (consTuple F r hr p b) = p ∧
    tailOf F r hr (consTuple F r hr p b) = b := by
  constructor
  · unfold headOf consTuple
    rw [dif_pos (by simp : ((⟨0, by omega⟩ : Fin r) : ℕ) = 0)]
  · unfold tailOf consTuple
    funext j
    have hne : ¬ ((⟨j.1 + 1, by omega⟩ : Fin r) : ℕ) = 0 := by
      simp
    rw [dif_neg hne]
    apply congrArg b
    apply Fin.ext
    simp

/-- The function-level tail of `a.val` is definitionally the value of `tailTuple` (glue
item 1 of the recursion). -/
lemma tailTuple_val_eq_tailOf {r : ℕ} (hr : 1 < r) (a : monicStrictAntiNatDegree F r) :
    (tailTuple F hr a).val = tailOf F r hr a.val := by
  rfl




/-- The pointwise value function underlying `consTuple`. -/
noncomputable def consVal (r : ℕ) (hr : 1 < r) (p : F[X]) (b : Fin (r - 1) → F[X]) (i : Fin r) : F[X] :=
  if h : (i : ℕ) = 0 then p else b ⟨i.1 - 1, by omega⟩

lemma consTuple_eq_consVal (r : ℕ) (hr : 1 < r) (p : F[X]) (b : Fin (r - 1) → F[X]) :
    consTuple F r hr p b = consVal F r hr p b := by
  rfl

lemma consVal_zero (r : ℕ) (hr : 1 < r) (p : F[X]) (b : Fin (r - 1) → F[X]) :
    consVal F r hr p b ⟨0, by omega⟩ = p := by
  unfold consVal
  rw [dif_pos (by simp : ((⟨0, by omega⟩ : Fin r) : ℕ) = 0)]

lemma consVal_succ (r : ℕ) (hr : 1 < r) (p : F[X]) (b : Fin (r - 1) → F[X])
    (k : ℕ) (hk : k + 1 < r) :
    consVal F r hr p b ⟨k + 1, hk⟩ = b ⟨k, by omega⟩ := by
  unfold consVal
  have hne : ¬ ((⟨k + 1, hk⟩ : Fin r) : ℕ) = 0 := by
    simp
  rw [dif_neg hne]
  congr 1

/-- In a strictly-decreasing tuple, entry `t` has degree at most the leading degree. -/
lemma monic_tuple_deg_le_zero {m : ℕ} (hrm : 0 < m) (b : monicStrictAntiNatDegree F m) (t : Fin m) :
    (b.val t).natDegree ≤ (b.val ⟨0, hrm⟩).natDegree := by
  by_cases ht : (t : ℕ) = 0
  · have ht0 : t = ⟨0, hrm⟩ := Fin.ext (by simpa using ht)
    rw [ht0]
  · have h0t : (⟨0, hrm⟩ : Fin m) < t := (Fin.mk_lt_mk).2 (Nat.pos_of_ne_zero ht)
    exact le_of_lt (by simpa using b.2.1 h0t)

/-- consTuple of a monic degree-`d` polynomial and a `< d`-bounded tail is strictly
degree-decreasing. -/
lemma consTuple_strictAnti (r : ℕ) (hr : 1 < r) (hrT : 0 < r - 1) (d : ℕ) (p : F[X])
    (b : monicStrictAntiNatDegree F (r - 1))
    (hpdeg : p.natDegree = d) (hb : (b.val ⟨0, hrT⟩).natDegree < d) :
    StrictAnti (natDegree ∘ consTuple F r hr p b.val) := by
  intro i j hij
  change natDegree (consVal F r hr p b.val j) < natDegree (consVal F r hr p b.val i)
  by_cases hi0 : (i : ℕ) = 0
  · have hjgt : 0 < (j : ℕ) := by
      have hij' : (i : ℕ) < (j : ℕ) := Fin.lt_def.mp hij
      omega
    unfold consVal
    rw [dif_pos hi0]
    have hjne : ¬ ((j : ℕ) = 0) := by omega
    rw [dif_neg hjne]
    rw [hpdeg]
    exact lt_of_le_of_lt
      (monic_tuple_deg_le_zero F hrT b ⟨j.1 - 1, by omega⟩) hb
  · unfold consVal
    rw [dif_neg hi0]
    have hjne : ¬ ((j : ℕ) = 0) := by
      have hij' : (i : ℕ) < (j : ℕ) := Fin.lt_def.mp hij
      omega
    rw [dif_neg hjne]
    have hlt : (⟨i.1 - 1, by omega⟩ : Fin (r - 1)) < ⟨j.1 - 1, by omega⟩ := by
      apply Fin.mk_lt_mk.2
      have hij' : (i : ℕ) < (j : ℕ) := Fin.lt_def.mp hij
      omega
    simpa using b.2.1 hlt

/-- consTuple of a monic head and a monic tail is monic. -/
lemma consTuple_monic (r : ℕ) (hr : 1 < r) (p : F[X])
    (b : monicStrictAntiNatDegree F (r - 1))
    (hp : p.Monic) : ∀ i : Fin r, ((consTuple F r hr p b.val) i).Monic := by
  intro i
  by_cases hi : (i : ℕ) = 0
  · have hi0 : i = ⟨0, by omega⟩ := Fin.ext (by simpa using hi)
    rw [consTuple_eq_consVal, hi0, consVal_zero]
    exact hp
  · rw [consTuple_eq_consVal]
    unfold consVal
    rw [dif_neg hi]
    exact b.2.2 ⟨i.1 - 1, by omega⟩




abbrev BlockD (r : ℕ) (hr0 : 0 < r) (d : ℕ) :=
  {a : monicStrictAntiNatDegree F r // a ∈ blockSet F r hr0 d}

abbrev HeadD (d : ℕ) := {p : F[X] // p ∈ MonicDeg F d}

abbrev TailLT (r : ℕ) (hrT : 0 < r) (d : ℕ) :=
  {b : monicStrictAntiNatDegree F r // b ∈ blockSetLT F r hrT d}

noncomputable def blockForward (r : ℕ) (hr : 1 < r) (hr0 : 0 < r) (hrT : 0 < r - 1)
    (d : ℕ) (a : BlockD F r hr0 d) : HeadD F d × TailLT F (r - 1) hrT d :=
  (⟨a.1.val ⟨0, hr0⟩, by
      constructor
      · exact a.1.2.2 ⟨0, hr0⟩
      · change (a.1.val ⟨0, hr0⟩).natDegree = d
        simpa [blockSet] using a.2⟩,
   ⟨tailTuple F hr a.1, by
      change ((tailTuple F hr a.1).val ⟨0, hrT⟩).natDegree < d
      exact @tailTuple_leading_lt F _ _ _ r hr hr0 hrT d a.1 (by simpa [blockSet] using a.2)⟩)

noncomputable def blockInverse (r : ℕ) (hr : 1 < r) (hr0 : 0 < r) (hrT : 0 < r - 1)
    (d : ℕ) (x : HeadD F d × TailLT F (r - 1) hrT d) : BlockD F r hr0 d :=
  ⟨⟨consTuple F r hr x.1.1 x.2.1.val,
     ⟨@consTuple_strictAnti F _ _ _ r hr hrT d x.1.1 x.2.1 (by exact x.1.2.2)
        (by simpa [blockSetLT] using x.2.2),
      @consTuple_monic F _ _ _ r hr x.1.1 x.2.1 (by exact x.1.2.1)⟩⟩,
   by
     change (consTuple F r hr x.1.1 x.2.1.val ⟨0, hr0⟩).natDegree = d
     rw [consTuple_eq_consVal]
     rw [consVal_zero]
     exact x.1.2.2⟩


/-- consVal at index 0 (explicit proof) is the head. -/
lemma consVal_zero' (r : ℕ) (hr : 1 < r) (hr0 : 0 < r) (p : F[X])
    (b : Fin (r - 1) → F[X]) :
    consVal F r hr p b ⟨0, hr0⟩ = p := by
  unfold consVal
  rw [dif_pos (by simp : ((⟨0, hr0⟩ : Fin r) : ℕ) = 0)]

-- roundtrip: inverse(forward a) = a
lemma blockForwardInverse (r : ℕ) (hr : 1 < r) (hr0 : 0 < r) (hrT : 0 < r - 1)
    (d : ℕ) (a : BlockD F r hr0 d) :
    blockInverse F r hr hr0 hrT d (blockForward F r hr hr0 hrT d a) = a := by
  unfold blockInverse blockForward
  apply Subtype.ext
  apply Subtype.ext
  change consTuple F r hr (a.1.val ⟨0, hr0⟩) (tailTuple F hr a.1).val = a.1.val
  have ht : (tailTuple F hr a.1).val = tailOf F r hr a.1.val := tailTuple_val_eq_tailOf F hr a.1
  rw [ht]
  have hct := consTuple_head_tail F r hr hr0 a.1.val
  simpa [headOf] using hct

-- roundtrip: forward(inverse x) = x
lemma blockInverseForward (r : ℕ) (hr : 1 < r) (hr0 : 0 < r) (hrT : 0 < r - 1)
    (d : ℕ) (x : HeadD F d × TailLT F (r - 1) hrT d) :
    blockForward F r hr hr0 hrT d (blockInverse F r hr hr0 hrT d x) = x := by
  cases x with
  | mk p b =>
    unfold blockForward blockInverse
    apply Prod.ext
    · apply Subtype.ext
      change (consTuple F r hr p.1 b.1.val) ⟨0, hr0⟩ = p.1
      rw [consTuple_eq_consVal]
      exact consVal_zero' F r hr hr0 p.1 b.1.val
    · apply Subtype.ext
      apply Subtype.ext
      change (tailTuple F hr (⟨consTuple F r hr p.1 b.1.val,
        ⟨consTuple_strictAnti F r hr hrT d p.1 b.1 (by exact p.2.2) (by simpa [blockSetLT] using b.2),
         consTuple_monic F r hr p.1 b.1 (by exact p.2.1)⟩⟩)).val = b.1.val
      have ht : (tailTuple F hr (⟨consTuple F r hr p.1 b.1.val,
        ⟨consTuple_strictAnti F r hr hrT d p.1 b.1 (by exact p.2.2) (by simpa [blockSetLT] using b.2),
         consTuple_monic F r hr p.1 b.1 (by exact p.2.1)⟩⟩)).val =
          tailOf F r hr (consTuple F r hr p.1 b.1.val) := by
        rfl
      rw [ht]
      exact (head_tail_consTuple F r hr p.1 b.1.val).2


/-- The degree-`d` block of length `r` is in bijection with (monic degree-`d` polynomials)
× (length-`(r-1)` tuples with leading degree `< d`). -/
noncomputable def blockEquiv (r : ℕ) (hr : 1 < r) (hr0 : 0 < r) (hrT : 0 < r - 1)
    (d : ℕ) : BlockD F r hr0 d ≃ (HeadD F d × TailLT F (r - 1) hrT d) where
  toFun := blockForward F r hr hr0 hrT d
  invFun := blockInverse F r hr hr0 hrT d
  left_inv := blockForwardInverse F r hr hr0 hrT d
  right_inv := blockInverseForward F r hr hr0 hrT d


/-- Step 1 of the recursion: the degree-`d` block sum equals the sum over the product
(head × tail) of the zeta summand of the reconstructed tuple. -/
lemma S_eq_tsum_over_product (r : ℕ) (hr : 1 < r) (hr0 : 0 < r) (hrT : 0 < r - 1)
    (𝔰 : Fin r → ℕ+) (d : ℕ) :
    S F r hr0 𝔰 d =
      ∑' x : HeadD F d × TailLT F (r - 1) hrT d,
        zetaTerm F 𝔰 ((blockEquiv F r hr hr0 hrT d).symm x).1 := by
  let e := blockEquiv F r hr hr0 hrT d
  rw [S]
  calc
    (∑' a : BlockD F r hr0 d, zetaTerm F 𝔰 a.1)
        = ∑' a : BlockD F r hr0 d, zetaTerm F 𝔰 (e.symm (e a)).1 := by
          apply tsum_congr
          intro a
          rw [Equiv.symm_apply_apply e a]
    _ = ∑' x : HeadD F d × TailLT F (r - 1) hrT d, zetaTerm F 𝔰 (e.symm x).1 := by
          exact Equiv.tsum_eq e (fun x : HeadD F d × TailLT F (r - 1) hrT d =>
            zetaTerm F 𝔰 (e.symm x).1)




/-- The summand over the reconstructed tuple factorizes into head-term × tail-term. -/
lemma zetaTerm_blockInverse (r : ℕ) (hr : 1 < r) (hr0 : 0 < r) (hrT : 0 < r - 1)
    (𝔰 : Fin r → ℕ+) (d : ℕ)
    (x : HeadD F d × TailLT F (r - 1) hrT d) :
    zetaTerm F 𝔰 ((blockEquiv F r hr hr0 hrT d).symm x).1 =
      ((((x.1.1 : RatFunc F) : RatFunc.CompletionAtInfty F) ^ (𝔰 ⟨0, hr0⟩ : ℕ))⁻¹) *
      zetaTerm F (fun j : Fin (r - 1) => 𝔰 ⟨j.1 + 1, by omega⟩) x.2.1 := by
  let e := blockEquiv F r hr hr0 hrT d
  have hs : e.symm x = blockInverse F r hr hr0 hrT d x := by rfl
  rw [hs]
  have hz := zetaTerm_fact F hr hr0 𝔰 (blockInverse F r hr hr0 hrT d x).1
  rw [hz]
  have hheadval : (blockInverse F r hr hr0 hrT d x).1.val ⟨0, hr0⟩ = x.1.1 := by
    change (consTuple F r hr x.1.1 x.2.1.val) ⟨0, hr0⟩ = x.1.1
    rw [consTuple_eq_consVal]
    exact consVal_zero' F r hr hr0 x.1.1 x.2.1.val
  have htail : tailTuple F hr (blockInverse F r hr hr0 hrT d x).1 = x.2.1 := by
    apply Subtype.ext
    change (tailTuple F hr (blockInverse F r hr hr0 hrT d x).1).val = x.2.1.val
    have htv := tailTuple_val_eq_tailOf F hr (blockInverse F r hr hr0 hrT d x).1
    rw [htv]
    change tailOf F r hr (consTuple F r hr x.1.1 x.2.1.val) = x.2.1.val
    exact (head_tail_consTuple F r hr x.1.1 x.2.1.val).2
  rw [hheadval]
  rw [htail]

/-- The degree-`d` block sum `S_d(𝔰)` equals `P_d(𝔰₀) · S_<d(𝔰₁,…,𝔰_{r-1})`. -/
lemma S_d_recursion (r : ℕ) (hr : 1 < r) (hr0 : 0 < r) (hrT : 0 < r - 1)
    (𝔰 : Fin r → ℕ+) (d : ℕ) :
    S F r hr0 𝔰 d =
      P F d (𝔰 ⟨0, hr0⟩) *
      S_lt F (r - 1) hrT (fun j : Fin (r - 1) => 𝔰 ⟨j.1 + 1, by omega⟩) d := by
  classical
  have h1 := S_eq_tsum_over_product F r hr hr0 hrT 𝔰 d
  rw [h1]
  rw [tsum_congr (fun x : HeadD F d × TailLT F (r - 1) hrT d =>
    zetaTerm_blockInverse F r hr hr0 hrT 𝔰 d x)]
  let f : HeadD F d → RatFunc.CompletionAtInfty F := fun p =>
    (((p.1 : RatFunc F) : RatFunc.CompletionAtInfty F) ^ (𝔰 ⟨0, hr0⟩ : ℕ))⁻¹
  let g : TailLT F (r - 1) hrT d → RatFunc.CompletionAtInfty F := fun b =>
    zetaTerm F (fun j : Fin (r - 1) => 𝔰 ⟨j.1 + 1, by omega⟩) b.1
  haveI : Finite (HeadD F d) := by
    change Finite {p : F[X] // p ∈ MonicDeg F d}
    exact finite_MonicDeg F d
  haveI : Finite (TailLT F (r - 1) hrT d) := by
    change Finite {b : monicStrictAntiNatDegree F (r - 1) // b ∈ blockSetLT F (r - 1) hrT d}
    exact finite_blockLT F hrT d
  have hf : Summable f := Summable.of_finite (f := f)
  have hg : Summable g := Summable.of_finite (f := g)
  have hmul := tsum_mul_tsum_of_nonarchimedean (R := RatFunc.CompletionAtInfty F)
    (f := f) (g := g) hf hg
  rw [← hmul]
  have hfid : (∑' p : HeadD F d, f p) = P F d (𝔰 ⟨0, hr0⟩) := by rfl
  have hgid : (∑' b : TailLT F (r - 1) hrT d, g b) =
      S_lt F (r - 1) hrT (fun j : Fin (r - 1) => 𝔰 ⟨j.1 + 1, by omega⟩) d := by rfl
  rw [hfid, hgid]


/-- Chen's coefficients Δ^i_{a,b} (paper (2.1)) as integers: `(-1)^(a-1) C(i-1,a-1) +
`(-1)^(b-1) C(i-1,b-1)` when `(q-1) | i`, and `0` otherwise.  Casting into the
completion (a field of characteristic `p`) gives the coefficients in `𝔽_p`. -/
noncomputable def ChenDeltaZ (a b i : ℕ) : ℤ :=
  if (Nat.card F - 1) ∣ i then
    (if Even (a - 1) then 1 else -1) * (Nat.choose (i - 1) (a - 1) : ℤ) +
      (if Even (b - 1) then 1 else -1) * (Nat.choose (i - 1) (b - 1) : ℤ)
  else 0



/-- The monic degree-`d` polynomials form a finite type, via the explicit coefficient
bijection `monicDegreeEquiv`. -/
noncomputable def fintypeMonicDeg (d : ℕ) : Fintype (HeadD F d) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  haveI : DecidableEq F := Classical.decEq F
  change Fintype {p : F[X] // p.Monic ∧ p.natDegree = d}
  exact Fintype.ofEquiv (Fin d → F) (Commons.FieldTheory.Polynomial.monicDegreeEquiv F d).symm

noncomputable instance instFintypeHeadD (d : ℕ) : Fintype (HeadD F d) := fintypeMonicDeg F d

/-- `P_d(n)` is the finite sum over monic degree-`d` polynomials. -/
lemma P_eq_sum (d : ℕ) (n : ℕ+) :
    P F d n = ∑ p : HeadD F d,
      (((p.1 : RatFunc F) : RatFunc.CompletionAtInfty F) ^ (n : ℕ))⁻¹ := by
  rw [P]
  rw [tsum_fintype]




/-- `P_a · P_b` is the double sum over pairs of monic degree-`d` polynomials. -/
lemma P_mul_eq_double_sum (d : ℕ) (a b : ℕ+) :
    P F d a * P F d b =
      ∑ p : HeadD F d, ∑ q : HeadD F d,
        ((((p.1 : RatFunc F) : RatFunc.CompletionAtInfty F) ^ (a : ℕ))⁻¹) *
        ((((q.1 : RatFunc F) : RatFunc.CompletionAtInfty F) ^ (b : ℕ))⁻¹) := by
  rw [P_eq_sum F d a, P_eq_sum F d b]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mul_sum]




lemma inv_mul_pow (x : RatFunc.CompletionAtInfty F) (a b : ℕ) :
    (x ^ a)⁻¹ * (x ^ b)⁻¹ = (x ^ (a + b))⁻¹ := by
  rw [pow_add, mul_inv_rev, mul_comm]

lemma diag_eq_P_add (d : ℕ) (a b : ℕ+) :
    (∑ p : HeadD F d,
      ((((p.1 : RatFunc F) : RatFunc.CompletionAtInfty F) ^ (a : ℕ))⁻¹) *
      ((((p.1 : RatFunc F) : RatFunc.CompletionAtInfty F) ^ (b : ℕ))⁻¹)) =
      P F d ⟨(a : ℕ) + (b : ℕ), Nat.add_pos_left (PNat.pos a) (b : ℕ)⟩ := by
  let n : ℕ+ := ⟨(a : ℕ) + (b : ℕ), Nat.add_pos_left (PNat.pos a) (b : ℕ)⟩
  rw [P_eq_sum F d n]
  apply Finset.sum_congr rfl
  intro p hp
  exact inv_mul_pow F (((p.1 : RatFunc F) : RatFunc.CompletionAtInfty F)) (a : ℕ) (b : ℕ)




/-! ### Step B1 : the off-diagonal parametrisation (Thakur's partition) -/

def MonicDegLt (d : ℕ) : Set F[X] := {p : F[X] | p.Monic ∧ p.natDegree < d}

/-- Monic degree-`< d` polynomials as a type. -/
abbrev MonicLt (d : ℕ) := {m : F[X] // m ∈ MonicDegLt F d}

/-- The monic polynomials of degree `< d` form a finite set. -/
theorem finite_MonicDegLt (d : ℕ) : Set.Finite (MonicDegLt F d) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have hle : Set.Finite {p : F[X] | p.Monic ∧ p.natDegree ≤ d} := by
    change Finite {p : F[X] // p.Monic ∧ p.natDegree ≤ d}
    exact Commons.FieldTheory.Polynomial.finite_monic_le F d
  exact Set.Finite.subset hle (by
    intro p hp
    exact ⟨hp.1, le_of_lt hp.2⟩)

noncomputable instance instFintypeMonicLt (d : ℕ) : Fintype (MonicLt F d) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  change Fintype {p : F[X] // p ∈ MonicDegLt F d}
  exact Set.Finite.fintype (finite_MonicDegLt F d)

/-- The difference of two distinct monic polynomials of the same natural degree has
degree strictly below that degree. -/
lemma natDegree_sub_lt_of_monic (p q : F[X]) (hp : p.Monic) (hq : q.Monic)
    (hdeg : p.natDegree = q.natDegree) (hne : p ≠ q) :
    (q - p).natDegree < p.natDegree := by
  have hne0 : q - p ≠ 0 := by
    intro h0
    apply hne
    exact (eq_of_sub_eq_zero h0).symm
  have hle : (q - p).natDegree ≤ p.natDegree := by
    have h1 := natDegree_sub_le q p
    rw [← hdeg] at h1
    simpa using h1
  -- natDegree(q-p) ≠ p.natDegree
  have hnede : (q - p).natDegree ≠ p.natDegree := by
    intro hn
    have hc : (q - p).coeff ((q - p).natDegree) = 0 := by
      rw [Polynomial.coeff_sub]
      have hc1 : q.coeff (q - p).natDegree = 1 := by
        have : (q - p).natDegree = q.natDegree := by omega
        rw [this]
        exact hq.coeff_natDegree
      have hc2 : p.coeff (q - p).natDegree = 1 := by
        rw [hn]
        exact hp.coeff_natDegree
      rw [hc1, hc2]
      simp
    have hcne : (q - p).coeff ((q - p).natDegree) ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact (Polynomial.leadingCoeff_eq_zero.not.mpr hne0)
    exact hcne hc
  omega

/-- `p + δ·m` is monic of degree `d` for `p` monic of degree `d`, `m` monic of degree `< d`. -/
lemma shift_monic (d : ℕ) (hd : 1 ≤ d) (p : HeadD F d) (m : MonicLt F d) (δ : F) :
    ((p.1 + Polynomial.C δ * m.1).Monic) ∧ (p.1 + Polynomial.C δ * m.1).natDegree = d := by
  have hpd : p.1.natDegree = d := p.2.2
  by_cases hδ : δ = 0
  · have h0 : (Polynomial.C 0 * m.1 : F[X]) = 0 := by simp
    rw [hδ, h0, add_zero]
    exact ⟨p.2.1, hpd⟩
  · have hdegm : (Polynomial.C δ * m.1).natDegree < d := by
      rw [Polynomial.natDegree_C_mul (a := δ) (p := m.1) (a0 := hδ)]
      exact m.2.2
    have hdegsum : (p.1 + Polynomial.C δ * m.1).natDegree = p.1.natDegree := by
      exact Polynomial.natDegree_add_eq_left_of_natDegree_lt (by omega : (Polynomial.C δ * m.1).natDegree < p.1.natDegree)
    have hm : (p.1 + Polynomial.C δ * m.1).Monic := by
      rw [Polynomial.Monic.def]
      change (p.1 + Polynomial.C δ * m.1).coeff ((p.1 + Polynomial.C δ * m.1).natDegree) = 1
      rw [show (p.1 + Polynomial.C δ * m.1).natDegree = d by rw [hdegsum, hpd]]
      rw [Polynomial.coeff_add]
      have hc1 : p.1.coeff d = 1 := by
        have hcp := p.2.1.coeff_natDegree
        rw [hpd] at hcp
        exact hcp
      have hc2 : (Polynomial.C δ * m.1).coeff d = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [hc1, hc2]
      simp
    exact ⟨hm, by rw [hdegsum, hpd]⟩

/-- For `δ ≠ 0`, `p + δ·m ≠ p`. -/
lemma shift_ne_self (d : ℕ) (hd : 1 ≤ d) (p : HeadD F d) (m : MonicLt F d) (δ : F) (hδ : δ ≠ 0) :
    p.1 + Polynomial.C δ * m.1 ≠ p.1 := by
  intro h
  have ht0 : Polynomial.C δ * m.1 = 0 := by
    have h' : p.1 + Polynomial.C δ * m.1 = p.1 + 0 := by simpa using h
    exact add_left_cancel h'
  have hmne : m.1 ≠ 0 := m.2.1.ne_zero
  have hδ0 : δ = 0 := by
    have hc : Polynomial.C δ = 0 ∨ m.1 = 0 := (mul_eq_zero.mp ht0)
    rcases hc with hc | hc
    · exact (Polynomial.C_eq_zero.mp hc)
    · exact False.elim (hmne hc)
  exact hδ hδ0



/-- The difference of two distinct level-`d` heads has degree `< d`. -/
lemma diff_natDegree_lt (d : ℕ) (hd : 1 ≤ d) (p q : HeadD F d) (hne : q ≠ p) :
    (q.1 - p.1).natDegree < d := by
  have hlt := natDegree_sub_lt_of_monic F p.1 q.1 p.2.1 q.2.1
    (by rw [p.2.2, q.2.2]) (by intro hpq; apply hne; apply Subtype.ext; exact hpq.symm)
  rwa [p.2.2] at hlt

/-- Forward direction of the level-`d` shift bijection: `q ≠ p` is recorded by the
monic-normalised difference `m` together with the scalar `δ = lc(q-p)`. -/
noncomputable def shiftForward (d : ℕ) (hd : 1 ≤ d) (p : HeadD F d)
    (x : {q : HeadD F d // q ≠ p}) : {y : MonicLt F d × F // y.2 ≠ 0} := by
  let r : F[X] := x.1.1 - p.1
  let δ : F := r.leadingCoeff
  have hne0 : r ≠ 0 := by
    dsimp [r]
    intro h0
    apply x.2
    apply Subtype.ext
    exact eq_of_sub_eq_zero h0
  have hδ : δ ≠ 0 := by
    dsimp [δ]
    exact (Polynomial.leadingCoeff_eq_zero.not.mpr hne0)
  have hmon : (Polynomial.C δ⁻¹ * r).Monic := by
    rw [Polynomial.Monic.def]
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
    dsimp [δ]
    rw [inv_mul_cancel₀ hδ]
  have hdegm : (Polynomial.C δ⁻¹ * r).natDegree < d := by
    rw [Polynomial.natDegree_C_mul (a := δ⁻¹) (p := r) (a0 := inv_ne_zero hδ)]
    exact diff_natDegree_lt F d hd p x.1 x.2
  refine ⟨(⟨(Polynomial.C δ⁻¹ * r), ?_⟩, δ), hδ⟩
  change (Polynomial.C δ⁻¹ * r).Monic ∧ (Polynomial.C δ⁻¹ * r).natDegree < d
  exact ⟨hmon, hdegm⟩

/-- Inverse of the level-`d` shift bijection: rebuild `q = p + δ·m`. -/
noncomputable def shiftInverse (d : ℕ) (hd : 1 ≤ d) (p : HeadD F d)
    (y : {z : MonicLt F d × F // z.2 ≠ 0}) : {q : HeadD F d // q ≠ p} := by
  let m : MonicLt F d := y.1.1
  let δ : F := y.1.2
  have hmem : p.1 + Polynomial.C δ * m.1 ∈ MonicDeg F d := by
    change (p.1 + Polynomial.C δ * m.1).Monic ∧ (p.1 + Polynomial.C δ * m.1).natDegree = d
    exact shift_monic F d hd p m δ
  let q : HeadD F d := ⟨p.1 + Polynomial.C δ * m.1, hmem⟩
  refine ⟨q, ?_⟩
  intro h
  have hq : p.1 + Polynomial.C δ * m.1 = p.1 := by
    have hq' : q.1 = p.1 := congrArg (fun z : HeadD F d => z.1) h
    simpa [q] using hq'
  have hδne : δ ≠ 0 := by
    dsimp [δ]
    exact y.2
  exact (shift_ne_self F d hd p m δ hδne) hq

/-- `C a * (C a⁻¹ * r) = r` for `a ≠ 0`. -/
lemma C_inv_mul_left (a : F) (ha : a ≠ 0) (r : F[X]) :
    Polynomial.C a * (Polynomial.C (a⁻¹) * r) = r := by
  calc
    Polynomial.C a * (Polynomial.C (a⁻¹) * r) = (Polynomial.C a * Polynomial.C (a⁻¹)) * r := by
      rw [mul_assoc]
    _ = Polynomial.C (a * a⁻¹) * r := by rw [← Polynomial.C_mul]
    _ = Polynomial.C 1 * r := by rw [mul_inv_cancel₀ ha]
    _ = r := by simp

/-- `C (a⁻¹) * (C a * r) = r` for `a ≠ 0`. -/
lemma C_inv_mul_right (a : F) (ha : a ≠ 0) (r : F[X]) :
    Polynomial.C (a⁻¹) * (Polynomial.C a * r) = r := by
  calc
    Polynomial.C (a⁻¹) * (Polynomial.C a * r) = (Polynomial.C (a⁻¹) * Polynomial.C a) * r := by
      rw [mul_assoc]
    _ = Polynomial.C (a⁻¹ * a) * r := by rw [← Polynomial.C_mul]
    _ = Polynomial.C 1 * r := by rw [inv_mul_cancel₀ ha]
    _ = r := by simp

/-- First-component roundtrip of `headShiftEquiv`. -/
lemma shift_roundtrip_fst (d : ℕ) (hd : 1 ≤ d) (p : HeadD F d) (m : MonicLt F d) (δ : F)
    (hy : (m, δ).2 ≠ 0) :
    (shiftForward F d hd p (shiftInverse F d hd p ⟨(m, δ), hy⟩)).1.1 = m.1 := by
  dsimp [shiftInverse, shiftForward]
  have hs : p.1 + Polynomial.C δ * m.1 - p.1 = Polynomial.C δ * m.1 := by ring
  have hlc : (p.1 + Polynomial.C δ * m.1 - p.1).leadingCoeff = δ := by
    rw [hs, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
    rw [m.2.1.leadingCoeff]
    simp
  have hδ : δ ≠ 0 := by simpa using hy
  rw [hlc]
  rw [hs]
  exact C_inv_mul_right F δ hδ m.1

/-- Second-component roundtrip of `headShiftEquiv`. -/
lemma shift_roundtrip_snd (d : ℕ) (hd : 1 ≤ d) (p : HeadD F d) (m : MonicLt F d) (δ : F)
    (hy : (m, δ).2 ≠ 0) :
    (shiftForward F d hd p (shiftInverse F d hd p ⟨(m, δ), hy⟩)).1.2 = δ := by
  dsimp [shiftInverse, shiftForward]
  have hs : p.1 + Polynomial.C δ * m.1 - p.1 = Polynomial.C δ * m.1 := by ring
  rw [hs, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
  rw [m.2.1.leadingCoeff]
  simp

noncomputable def headShiftEquiv (d : ℕ) (hd : 1 ≤ d) (p : HeadD F d) :
    {q : HeadD F d // q ≠ p} ≃ {y : MonicLt F d × F // y.2 ≠ 0} where
  toFun := shiftForward F d hd p
  invFun := shiftInverse F d hd p
  left_inv := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    have hr : x.1.1 - p.1 ≠ 0 := by
      intro h0
      apply x.2
      apply Subtype.ext
      exact eq_of_sub_eq_zero h0
    have hδ : (x.1.1 - p.1).leadingCoeff ≠ 0 := by
      exact (Polynomial.leadingCoeff_eq_zero.not.mpr hr)
    calc
      p.1 + Polynomial.C (x.1.1 - p.1).leadingCoeff *
          (Polynomial.C ((x.1.1 - p.1).leadingCoeff)⁻¹ * (x.1.1 - p.1))
          = p.1 + (x.1.1 - p.1) := by
            rw [C_inv_mul_left F (x.1.1 - p.1).leadingCoeff hδ (x.1.1 - p.1)]
      _ = x.1.1 := by ring
  right_inv := by
    intro y
    apply Subtype.ext
    rcases y with ⟨y0, hy⟩
    rcases y0 with ⟨m, δ⟩
    apply Prod.ext
    · apply Subtype.ext
      exact shift_roundtrip_fst F d hd p m δ hy
    · exact shift_roundtrip_snd F d hd p m δ hy
end ZagierHoffmanPositiveChar
