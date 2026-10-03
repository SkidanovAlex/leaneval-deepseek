/-
# HNN extensions: finite-order elements are conjugate into the base group

This file sets up the normal-form ("length") vocabulary used to prove that in an HNN extension
`HNNExtension G A B φ`, every element of finite order is conjugate into the image of `G`.

The proof follows Britton's lemma: an element `x` is written in the normal form
`of h * t ^ (u₁ : ℤ) * of g₁ * ⋯ * t ^ (uₙ : ℤ) * of gₙ`, and the number of `t`-letters is the
`length` `rlen φ x`.  Conjugating a reducible word shortens it, so a length-minimal conjugate
of a torsion element is cyclically reduced; powers of a cyclically reduced word of length `n ≥ 1`
have length `k * n ≥ 1`, so they are not `1`.  Hence the minimal conjugate has length `0`, i.e.
lies in the image of `G`.

This file collects the definitions and the elementary list algebra; the main theorem is in
`Submission.Work.ORLocInd.HNN.finiteOrder_conj_mem_of`.
-/
import Mathlib
import Submission.Work.ORLocInd.Basic

set_option autoImplicit false

namespace Work.ORLocInd.HNN

open HNNExtension

variable {G : Type*} [Group G] {A B : Subgroup G}

/-- A fixed choice of transversal pair for the subgroups `A` and `B`, used to put elements of an
HNN extension into normal form. -/
noncomputable def stdTransversal (G : Type*) [Group G] (A B : Subgroup G) :
    NormalWord.TransversalPair G A B :=
  Classical.choice (NormalWord.TransversalPair.nonempty G A B)

/-- The product of the letters `t ^ (u : ℤ) * of g` attached to a list `l : List (ℤˣ × G)`. -/
noncomputable def lprod (φ : A ≃* B) (l : List (ℤˣ × G)) : HNNExtension G A B φ :=
  (l.map (fun p => t ^ (p.1 : ℤ) * of p.2)).prod

/-- The element of the HNN extension represented by a head `h : G` and a list of letters `l`. -/
noncomputable def wProd (φ : A ≃* B) (h : G) (l : List (ℤˣ × G)) : HNNExtension G A B φ :=
  of h * lprod φ l

/-- The number of `t`-letters in the normal form of `x`; equivalently the length of any reduced
word for `x` (see `rlen_prod`). -/
noncomputable def rlen (φ : A ≃* B) (x : HNNExtension G A B φ) : ℕ :=
  ((NormalWord.equiv φ (stdTransversal G A B)) x).toList.length

/-- The reducedness relation between consecutive letters of a reduced word. -/
def rel (A B : Subgroup G) (a b : ℤˣ × G) : Prop := a.2 ∈ toSubgroup A B a.1 → a.1 = b.1

/-- Multiply the group part of the *last* letter of `l` by `k`; this is the effect of right
multiplication by `of k` on the letter list of a reduced word. -/
def lmove : List (ℤˣ × G) → G → List (ℤˣ × G)
  | [], _ => []
  | [p], k => [(p.1, p.2 * k)]
  | p :: q :: rest, k => p :: lmove (q :: rest) k

/-- `k` copies of the letter list `l`, concatenated. -/
def lpow (l : List (ℤˣ × G)) : ℕ → List (ℤˣ × G)
  | 0 => []
  | k + 1 => l ++ lpow l k

/-- Absorb `of k` on the right of `wProd φ h l`: either into the last letter, or into the head
if `l` is empty. -/
noncomputable def absorbR (h k : G) (l : List (ℤˣ × G)) : G × List (ℤˣ × G) :=
  if l = [] then (h * k, []) else (h, lmove l k)

/-- A `ReducedWord` from a head and a letter list carrying the chain condition. -/
def mkRW (h : G) (l : List (ℤˣ × G)) (hc : l.IsChain (rel A B)) : NormalWord.ReducedWord G A B :=
  ⟨h, l, hc⟩

/-! ### Elementary list algebra -/

@[simp] theorem lprod_nil (φ : A ≃* B) : lprod φ ([] : List (ℤˣ × G)) = 1 := rfl

theorem lprod_cons (φ : A ≃* B) (p : ℤˣ × G) (l : List (ℤˣ × G)) :
    lprod φ (p :: l) = (t ^ (p.1 : ℤ) * of p.2) * lprod φ l := by
  simp only [lprod, List.map_cons, List.prod_cons]

theorem lprod_singleton (φ : A ≃* B) (p : ℤˣ × G) :
    lprod φ [p] = t ^ (p.1 : ℤ) * of p.2 := by
  rw [lprod_cons, lprod_nil, mul_one]

theorem lprod_append (φ : A ≃* B) (l₁ l₂ : List (ℤˣ × G)) :
    lprod φ (l₁ ++ l₂) = lprod φ l₁ * lprod φ l₂ := by
  simp only [lprod, List.map_append, List.prod_append]

theorem prod_eq_wProd (φ : A ≃* B) (w : NormalWord.ReducedWord G A B) :
    NormalWord.ReducedWord.prod φ w = wProd φ w.head w.toList := rfl

theorem mkRW_prod (φ : A ≃* B) (h : G) (l : List (ℤˣ × G)) (hc : l.IsChain (rel A B)) :
    NormalWord.ReducedWord.prod φ (mkRW (A:=A) (B:=B) h l hc) = wProd φ h l :=
  prod_eq_wProd φ _

/-! ### The letter list `lmove` -/

theorem lmove_append_singleton (l : List (ℤˣ × G)) (p : ℤˣ × G) (k : G) :
    lmove (l ++ [p]) k = l ++ [(p.1, p.2 * k)] := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      cases l with
      | nil => rfl
      | cons b l' =>
          simp only [List.cons_append, lmove]
          rw [List.cons_append] at ih
          rw [ih, List.cons_append]

theorem lmove_length : ∀ (l : List (ℤˣ × G)) (k : G), (lmove l k).length = l.length
  | [], k => rfl
  | [p], k => rfl
  | p :: q :: rest, k => by
      rw [show lmove (p :: q :: rest) k = p :: lmove (q :: rest) k from rfl]
      rw [List.length_cons, List.length_cons, lmove_length (q :: rest) k]

theorem forall_mem_some_rel (x a : ℤˣ × G) :
    (∀ y ∈ (some a : Option (ℤˣ × G)), rel A B x y) ↔ rel A B x a := by simp

theorem lmove_rel_head_iff (x : ℤˣ × G) : ∀ (l : List (ℤˣ × G)) (k : G),
    (∀ y ∈ (lmove l k).head?, rel A B x y) ↔ (∀ y ∈ l.head?, rel A B x y)
  | [], k => by simp [lmove]
  | [p], k => by
      simp only [lmove, List.head?_cons]
      rw [forall_mem_some_rel (a := (p.1, p.2 * k)), forall_mem_some_rel (a := p)]
      simp only [rel]
  | p :: q :: rest, k => by
      simp only [lmove, List.head?_cons]

theorem isChain_lmove_iff : ∀ (l : List (ℤˣ × G)) (k : G),
    (lmove l k).IsChain (rel A B) ↔ l.IsChain (rel A B)
  | [], k => by simp [lmove]
  | [p], k => by simp [lmove]
  | p :: q :: rest, k => by
      rw [show lmove (p :: q :: rest) k = p :: lmove (q :: rest) k from rfl,
        List.isChain_cons, List.isChain_cons,
        lmove_rel_head_iff (A:=A) (B:=B) p (q :: rest) k,
        isChain_lmove_iff (q :: rest) k]

/-- Right multiplication by `of k` only changes the last letter (or the head). -/
theorem lprod_lmove (φ : A ≃* B) : ∀ (l : List (ℤˣ × G)) (k : G), l ≠ [] →
    lprod φ (lmove l k) = lprod φ l * of k
  | [], k, h => (h rfl).elim
  | [p], k, h => by
      rw [show lmove [p] k = [(p.1, p.2 * k)] from rfl, lprod_singleton, lprod_singleton, map_mul]
      group
  | p :: q :: rest, k, h => by
      rw [show lmove (p :: q :: rest) k = p :: lmove (q :: rest) k from rfl]
      conv_lhs => rw [lprod_cons]
      conv_rhs => rw [lprod_cons]
      rw [lprod_lmove φ (q :: rest) k (by simp)]
      group

/-! ### `rlen` and reduced words -/

theorem normalWord_prod (φ : A ≃* B) (x : HNNExtension G A B φ) :
    NormalWord.ReducedWord.prod φ (NormalWord.equiv φ (stdTransversal G A B) x).toReducedWord = x :=
  (NormalWord.equiv φ (stdTransversal G A B)).symm_apply_apply x

/-- The length `rlen` of an element is the length of any reduced word representing it. -/
theorem rlen_prod (φ : A ≃* B) (w : NormalWord.ReducedWord G A B) :
    rlen φ (NormalWord.ReducedWord.prod φ w) = w.toList.length := by
  obtain ⟨w', hw1, hw2, _⟩ :=
    ReducedWord.exists_normalWord_prod_eq φ (stdTransversal G A B) w
  have h1 : NormalWord.equiv φ (stdTransversal G A B) (NormalWord.ReducedWord.prod φ w) = w' := by
    apply NormalWord.prod_injective φ (stdTransversal G A B)
    change NormalWord.ReducedWord.prod φ
        ((NormalWord.equiv φ (stdTransversal G A B) (NormalWord.ReducedWord.prod φ w)).toReducedWord)
      = NormalWord.ReducedWord.prod φ w'.toReducedWord
    rw [normalWord_prod, hw1]
  rw [rlen, h1]
  have := congrArg List.length hw2
  simpa using this

/-- An element of length `0` lies in the image of the base group. -/
theorem exists_of_rlen_eq_zero (φ : A ≃* B) {x : HNNExtension G A B φ} (hx : rlen φ x = 0) :
    ∃ g : G, x = of g := by
  refine ⟨(NormalWord.equiv φ (stdTransversal G A B) x).head, ?_⟩
  have hnil : (NormalWord.equiv φ (stdTransversal G A B) x).toList = [] := by
    have : (NormalWord.equiv φ (stdTransversal G A B) x).toList.length = 0 := hx
    exact List.eq_nil_of_length_eq_zero this
  conv_lhs => rw [← normalWord_prod (φ:=φ) x]
  rw [prod_eq_wProd]
  simp [wProd, lprod, hnil]

theorem rlen_wProd (φ : A ≃* B) (h : G) (l : List (ℤˣ × G)) (hc : l.IsChain (rel A B)) :
    rlen φ (wProd φ h l) = l.length := by
  rw [← mkRW_prod (A:=A) (B:=B) φ h l hc, rlen_prod]
  rfl

/-! ### `absorbR` and the `phiHat` conjugation -/

theorem absorbR_length (h k : G) (l : List (ℤˣ × G)) : (absorbR h k l).2.length = l.length := by
  unfold absorbR
  split_ifs with hl
  · simp [hl]
  · exact lmove_length l k

theorem absorbR_chain (h k : G) {l : List (ℤˣ × G)} (hc : l.IsChain (rel A B)) :
    (absorbR h k l).2.IsChain (rel A B) := by
  unfold absorbR
  split_ifs with hl
  · simp
  · exact (isChain_lmove_iff l k).2 hc

theorem wProd_absorbR (φ : A ≃* B) (h k : G) (l : List (ℤˣ × G)) :
    wProd φ (absorbR h k l).1 (absorbR h k l).2 = wProd φ h l * of k := by
  unfold absorbR
  split_ifs with hl
  · simp [wProd, hl, map_mul]
  · simp only [wProd]
    rw [lprod_lmove φ l k hl]
    group

/-- The conjugate of `of w` by `t ^ u`, for `w` in the appropriate subgroup. -/
noncomputable def phiHat (φ : A ≃* B) (u : ℤˣ) (w : G) (hw : w ∈ toSubgroup A B u) : G :=
  ((toSubgroupEquiv φ u ⟨w, hw⟩ : toSubgroup A B (-u)) : G)

theorem t_zpow_conj (φ : A ≃* B) (u : ℤˣ) (w : G) (hw : w ∈ toSubgroup A B u) :
    (t : HNNExtension G A B φ) ^ (u : ℤ) * of w
        * ((t : HNNExtension G A B φ) ^ (u : ℤ))⁻¹
      = of (phiHat φ u w hw) := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · rw [phiHat]
    simp only [Units.val_one, zpow_one, toSubgroupEquiv_one]
    exact (equiv_eq_conj (φ := φ) ⟨w, hw⟩).symm
  · rw [phiHat]
    simp only [Units.val_neg, Units.val_one, toSubgroupEquiv_neg_one, toSubgroup_neg_one]
    rw [zpow_neg, zpow_one]
    exact (equiv_symm_eq_conj (φ := φ) ⟨w, hw⟩).symm

/-! ### The cyclic reduction step -/

/-- The algebraic identity behind cyclic reduction. -/
theorem reduce_core (φ : A ≃* B) (p q : ℤˣ × G) (mid : List (ℤˣ × G))
    (hpq : p.1 = -q.1) (hmem : q.2 ∈ toSubgroup A B q.1) :
    (t : HNNExtension G A B φ) ^ (q.1 : ℤ) * lprod φ (p :: (mid ++ [q]))
        * ((t : HNNExtension G A B φ) ^ (q.1 : ℤ))⁻¹
      = of p.2 * lprod φ mid * of (phiHat φ q.1 q.2 hmem) := by
  rw [lprod_cons, lprod_append, lprod_singleton]
  have hpinv : (t : HNNExtension G A B φ) ^ (p.1 : ℤ) = ((t : HNNExtension G A B φ) ^ (q.1 : ℤ))⁻¹ := by
    rw [hpq, Units.val_neg, zpow_neg]
  calc (t : HNNExtension G A B φ) ^ (q.1 : ℤ)
          * ((t ^ (p.1 : ℤ) * of p.2) * (lprod φ mid * (t ^ (q.1 : ℤ) * of q.2)))
          * (t ^ (q.1 : ℤ))⁻¹
      = of p.2 * lprod φ mid * (t ^ (q.1 : ℤ) * of q.2 * (t ^ (q.1 : ℤ))⁻¹) := by
        rw [hpinv]; group
    _ = of p.2 * lprod φ mid * of (phiHat φ q.1 q.2 hmem) := by
        rw [t_zpow_conj]

/-- If a word with head `p`, last letter `q` and middle `mid` is not cyclically reduced, then a
conjugate of its product has length at most `mid.length`. -/
theorem reduce_not_cyclic (φ : A ≃* B) (p q : ℤˣ × G) (mid : List (ℤˣ × G))
    (hmid : mid.IsChain (rel A B)) (hnot : ¬ rel A B q p) :
    rlen φ ((t : HNNExtension G A B φ) ^ (q.1 : ℤ) * lprod φ (p :: (mid ++ [q]))
      * ((t : HNNExtension G A B φ) ^ (q.1 : ℤ))⁻¹) ≤ mid.length := by
  have hmem : q.2 ∈ toSubgroup A B q.1 := by
    by_contra hc
    exact hnot (fun h => absurd h hc)
  have hne1 : q.1 ≠ p.1 := fun heq => hnot (fun _ => heq)
  have hpq : p.1 = -q.1 := by
    rcases Int.units_eq_one_or p.1 with h1 | h1 <;>
      rcases Int.units_eq_one_or q.1 with h2 | h2 <;>
      rw [h1, h2] at hne1 ⊢ <;>
      simp_all
  rw [reduce_core φ p q mid hpq hmem]
  rw [show of p.2 * lprod φ mid * of (phiHat φ q.1 q.2 hmem)
      = wProd φ p.2 mid * of (phiHat φ q.1 q.2 hmem) from by rw [wProd]]
  rw [← wProd_absorbR φ p.2 (phiHat φ q.1 q.2 hmem) mid]
  rw [rlen_wProd φ (absorbR p.2 (phiHat φ q.1 q.2 hmem) mid).1
        (absorbR p.2 (phiHat φ q.1 q.2 hmem) mid).2
        (absorbR_chain p.2 (phiHat φ q.1 q.2 hmem) hmid)]
  rw [absorbR_length]

/-! ### Powers of a cyclically reduced word -/

theorem lprod_lpow (φ : A ≃* B) (l : List (ℤˣ × G)) (k : ℕ) :
    lprod φ (lpow l k) = (lprod φ l) ^ k := by
  induction k with
  | zero => simp [lpow]
  | succ k ih =>
      rw [show lpow l (k+1) = l ++ lpow l k from rfl, lprod_append, ih, pow_succ']

theorem lpow_length (l : List (ℤˣ × G)) (k : ℕ) : (lpow l k).length = k * l.length := by
  induction k with
  | zero => simp [lpow]
  | succ k ih =>
      rw [show lpow l (k+1) = l ++ lpow l k from rfl, List.length_append, ih, Nat.succ_mul,
        Nat.add_comm]

theorem head?_lpow_succ (l : List (ℤˣ × G)) (k : ℕ) : (lpow l (k+1)).head? = l.head? := by
  induction k with
  | zero => rw [show lpow l 1 = l from by simp [lpow]]
  | succ k ih =>
      rw [show lpow l (k+2) = l ++ lpow l (k+1) from rfl, List.head?_append, ih]
      cases l.head? <;> rfl

theorem isChain_lpow (l : List (ℤˣ × G)) (k : ℕ) (hc : l.IsChain (rel A B))
    (hcyc : ∀ x ∈ l.getLast?, ∀ y ∈ l.head?, rel A B x y) :
    (lpow l k).IsChain (rel A B) := by
  induction k with
  | zero => simp [lpow]
  | succ k ih =>
      rw [show lpow l (k+1) = l ++ lpow l k from rfl]
      refine hc.append ih ?_
      intro x hx y hy
      cases k with
      | zero => simp [lpow] at hy
      | succ j =>
          rw [head?_lpow_succ l j] at hy
          exact hcyc x hx y hy

/-- The `k`-th power of a cyclically reduced word has length `k * n`. -/
theorem rlen_lpow (φ : A ≃* B) (l : List (ℤˣ × G)) (k : ℕ) (hc : l.IsChain (rel A B))
    (hcyc : ∀ x ∈ l.getLast?, ∀ y ∈ l.head?, rel A B x y) :
    rlen φ ((lprod φ l) ^ k) = k * l.length := by
  rw [← lprod_lpow φ l k]
  rw [show lprod φ (lpow l k) = wProd φ 1 (lpow l k) from by simp [wProd]]
  rw [rlen_wProd φ 1 (lpow l k) (isChain_lpow l k hc hcyc), lpow_length]

/-! ### The decomposition of a list of length at least two -/

theorem exists_decomp : ∀ (l : List (ℤˣ × G)), 2 ≤ l.length →
    ∃ (p q : ℤˣ × G) (mid : List (ℤˣ × G)),
      l = p :: (mid ++ [q]) ∧ l.head? = some p ∧ l.getLast? = some q ∧
        mid.length = l.length - 2 ∧ (l.IsChain (rel A B) → mid.IsChain (rel A B))
  | [], h => absurd h (by simp)
  | [_], h => absurd h (by simp)
  | p :: q :: rest, h => by
      by_cases hrest : rest = []
      · subst hrest
        exact ⟨p, q, [], rfl, rfl, rfl, rfl, fun _ => List.isChain_nil⟩
      · have h2 : 2 ≤ (q :: rest).length := by
          rw [List.length_cons]
          have := List.length_pos_iff.mpr hrest
          omega
        obtain ⟨p', q', mid', hd, hh, hl, hlen, hch⟩ := exists_decomp (q :: rest) h2
        refine ⟨p, q', p' :: mid', ?_, rfl, ?_, ?_, ?_⟩
        · rw [hd, List.cons_append]
        · rw [List.getLast?_cons_cons, hl]
        · rw [List.length_cons, List.length_cons]
          omega
        · intro hc
          have hpre : p' :: mid' <+: q :: rest := by
            rw [hd]
            exact ⟨[q'], List.cons_append ..⟩
          exact hc.tail.prefix hpre

theorem rlen_one (φ : A ≃* B) : rlen φ (1 : HNNExtension G A B φ) = 0 := by
  have h : (NormalWord.equiv φ (stdTransversal G A B)) (1 : HNNExtension G A B φ)
      = (NormalWord.empty : NormalWord (stdTransversal G A B)) := by
    simp [NormalWord.equiv]
  rw [rlen, h]
  rfl

theorem normalWord_chain (φ : A ≃* B) (x : HNNExtension G A B φ) :
    (NormalWord.equiv φ (stdTransversal G A B) x).toList.IsChain (rel A B) :=
  (NormalWord.equiv φ (stdTransversal G A B) x).toReducedWord.chain

theorem hcyc_of_length_le_one {l : List (ℤˣ × G)} (h : l.length ≤ 1) :
    ∀ x ∈ l.getLast?, ∀ y ∈ l.head?, rel A B x y := by
  match l with
  | [] => intro x hx; exact absurd hx (by simp)
  | [a] =>
      intro x hx y hy
      have hx' : a = x := by
        rw [show ([a] : List (ℤˣ × G)).getLast? = some a from rfl] at hx
        simpa using hx
      have hy' : a = y := by
        rw [show ([a] : List (ℤˣ × G)).head? = some a from rfl] at hy
        simpa using hy
      rw [← hx', ← hy']
      exact fun _ => rfl
  | _ :: _ :: _ => exact absurd h (by simp)

end Work.ORLocInd.HNN
