import Submission.ZagierHoffmanProof.StepB4

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Polynomial RatFunc
open scoped BigOperators

/-!
# Step B5: depth-general power-sum products (paper §2.1 finish / §2.2 anchor)

Cor 2.7 of the paper: when the singleton `v` merges into the first slot of a tuple
`t` with `v + t₁ ≤ q`, the product is *pure*: `S_d(v)·S_d(t) = S_d(v+t₁, t₂, …)`.
At the level of the block sums this is the "singleton × depth-`k`" shuffle; it is the
anchor that all of §2.2's `B*_v`-algebra rests on.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Length-one blocks of degree exactly `d` are monic degree-`d` polynomials. -/
noncomputable def monicTuple1HeadEquiv (d : ℕ) (hr0 : 0 < 1) :
    HeadD F d ≃ BlockD F 1 hr0 d where
  toFun p := by
    refine ⟨⟨fun _ : Fin 1 => p.1, ?_, ?_⟩, ?_⟩
    · intro i j hij
      exfalso
      have hi : (i : ℕ) < 1 := i.2
      have hj : (j : ℕ) < 1 := j.2
      have hij' : (i : ℕ) < (j : ℕ) := hij
      omega
    · intro i
      exact p.2.1
    · change (p.1).natDegree = d
      exact p.2.2
  invFun b := ⟨b.1.1 ⟨0, hr0⟩, by
      change (b.1.1 ⟨0, hr0⟩).Monic ∧ (b.1.1 ⟨0, hr0⟩).natDegree = d
      exact ⟨b.1.2.2 ⟨0, hr0⟩, by simpa [blockSet] using b.2⟩⟩
  left_inv := by
    intro p
    apply Subtype.ext
    rfl
  right_inv := by
    intro b
    apply Subtype.ext
    apply Subtype.ext
    funext i
    fin_cases i
    rfl

/-- At depth one, `S_d(s) = P_d(s)`. -/
lemma S_one_eq_P (d : ℕ) (hr0 : 0 < 1) (𝔰 : Fin 1 → ℕ+) :
    S F 1 hr0 𝔰 d = P F d (𝔰 ⟨0, hr0⟩) := by
  classical
  let e : HeadD F d ≃ BlockD F 1 hr0 d := monicTuple1HeadEquiv F d hr0
  letI : Fintype (BlockD F 1 hr0 d) := Fintype.ofEquiv (HeadD F d) e
  calc
    S F 1 hr0 𝔰 d = ∑' b : BlockD F 1 hr0 d, zetaTerm F 𝔰 b.1 := by rfl
    _ = ∑ b : BlockD F 1 hr0 d, zetaTerm F 𝔰 b.1 := by rw [tsum_fintype]
    _ = ∑ p : HeadD F d, zetaTerm F 𝔰 (e p).1 := by
          exact (Equiv.sum_comp (e := e) (g := fun b : BlockD F 1 hr0 d => zetaTerm F 𝔰 b.1)).symm
    _ = ∑ p : HeadD F d, ((((p.1 : RatFunc F) : RatFunc.CompletionAtInfty F) ^ (𝔰 ⟨0, hr0⟩ : ℕ))⁻¹) := by
          apply Finset.sum_congr rfl
          intro p hp
          dsimp [e, zetaTerm, monicTuple1HeadEquiv]
          rw [Fin.prod_univ_one]
    _ = P F d (𝔰 ⟨0, hr0⟩) := by
          rw [P_eq_sum F d (𝔰 ⟨0, hr0⟩)]

/-- Prefixing a singleton exponent into the first slot of a depth-`k` exponent vector. -/
noncomputable def headAdd (v : ℕ+) {k : ℕ} (hr0 : 0 < k) (𝔱 : Fin k → ℕ+) : Fin k → ℕ+ :=
  fun j : Fin k => if (j : ℕ) = 0 then
    ⟨(v : ℕ) + (𝔱 ⟨0, hr0⟩ : ℕ), Nat.add_pos_left (PNat.pos v) (𝔱 ⟨0, hr0⟩ : ℕ)⟩
  else 𝔱 j

/-- Paper Corollary 2.7 (pure case): for `(v) + t₁ ≤ q`, multiplying the depth-`k`
power sum `S_d(t₁,…,t_k)` by the singleton `S_d(v)` merges `v` into the first slot. -/
lemma S_mul_P_pure (v : ℕ+) {k : ℕ} (hr0 : 0 < k) (𝔱 : Fin k → ℕ+) (d : ℕ) (hd : 1 ≤ d)
    (hv : (v : ℕ) + (𝔱 ⟨0, hr0⟩ : ℕ) ≤ Nat.card F) :
    P F d v * S F k hr0 𝔱 d = S F k hr0 (headAdd v hr0 𝔱) d := by
  classical
  by_cases hk : 1 < k
  · have hrec := S_d_recursion F k hk hr0 (by omega : 0 < k - 1) 𝔱 d
    have hrec' := S_d_recursion F k hk hr0 (by omega : 0 < k - 1) (headAdd v hr0 𝔱) d
    have htail : (fun j : Fin (k - 1) => (headAdd v hr0 𝔱) ⟨j.1 + 1, by omega⟩) =
        (fun j : Fin (k - 1) => 𝔱 ⟨j.1 + 1, by omega⟩) := by
      funext j
      dsimp [headAdd]
    have hhead : (headAdd v hr0 𝔱) ⟨0, hr0⟩ = ⟨(v : ℕ) + (𝔱 ⟨0, hr0⟩ : ℕ),
        Nat.add_pos_left (PNat.pos v) (𝔱 ⟨0, hr0⟩ : ℕ)⟩ := by
      dsimp [headAdd]
    calc
      P F d v * S F k hr0 𝔱 d
          = P F d v * (P F d (𝔱 ⟨0, hr0⟩) * S_lt F (k - 1) (by omega : 0 < k - 1)
              (fun j : Fin (k - 1) => 𝔱 ⟨j.1 + 1, by omega⟩) d) := by
            rw [hrec]
      _ = (P F d v * P F d (𝔱 ⟨0, hr0⟩)) * S_lt F (k - 1) (by omega : 0 < k - 1)
              (fun j : Fin (k - 1) => 𝔱 ⟨j.1 + 1, by omega⟩) d := by ring
      _ = P F d ⟨(v : ℕ) + (𝔱 ⟨0, hr0⟩ : ℕ), Nat.add_pos_left (PNat.pos v) (𝔱 ⟨0, hr0⟩ : ℕ)⟩ *
          S_lt F (k - 1) (by omega : 0 < k - 1)
            (fun j : Fin (k - 1) => 𝔱 ⟨j.1 + 1, by omega⟩) d := by
          rw [P_pure F d hd v (𝔱 ⟨0, hr0⟩) hv]
      _ = P F d ((headAdd v hr0 𝔱) ⟨0, hr0⟩) *
          S_lt F (k - 1) (by omega : 0 < k - 1)
            (fun j : Fin (k - 1) => (headAdd v hr0 𝔱) ⟨j.1 + 1, by omega⟩) d := by
          rw [hhead]
          congr 2
      _ = S F k hr0 (headAdd v hr0 𝔱) d := by
          exact (hrec').symm
  · have hk1 : k = 1 := by omega
    subst k
    have h1 := S_one_eq_P F d hr0 𝔱
    have h1' := S_one_eq_P F d hr0 (headAdd v hr0 𝔱)
    calc
      P F d v * S F 1 hr0 𝔱 d
          = P F d v * P F d (𝔱 ⟨0, hr0⟩) := by rw [h1]
      _ = P F d ⟨(v : ℕ) + (𝔱 ⟨0, hr0⟩ : ℕ), Nat.add_pos_left (PNat.pos v) (𝔱 ⟨0, hr0⟩ : ℕ)⟩ := by
            rw [P_pure F d hd v (𝔱 ⟨0, hr0⟩) hv]
      _ = P F d ((headAdd v hr0 𝔱) ⟨0, hr0⟩) := by
            congr 1
      _ = S F 1 hr0 (headAdd v hr0 𝔱) d := by
            rw [← h1']


/-- Equality of sets gives an equivalence of the corresponding subtypes. -/
noncomputable def subtype_equiv_of_set_eq {α : Type*} {s t : Set α} (h : s = t) :
    {x : α // x ∈ s} ≃ {x : α // x ∈ t} where
  toFun x := ⟨x.1, by
      change x.1 ∈ t
      rw [← h]
      exact x.2⟩
  invFun x := ⟨x.1, by
      change x.1 ∈ s
      rw [h]
      exact x.2⟩
  left_inv := by intro x; apply Subtype.ext; rfl
  right_inv := by intro x; apply Subtype.ext; rfl

/-- The `< d+1` blocks split as the disjoint union of the `< d` blocks and the
degree-`d` blocks.  Forward map: keep the block on the `< d` side iff its leading
degree is `< d`. -/
noncomputable def blockSetLT_toFun (r : ℕ) (hr : 0 < r) (d : ℕ)
    (x : {a : monicStrictAntiNatDegree F r // a ∈ blockSetLT F r hr (d + 1)}) :
    ({a : monicStrictAntiNatDegree F r // a ∈ blockSetLT F r hr d} ⊕
     {a : monicStrictAntiNatDegree F r // a ∈ blockSet F r hr d}) := by
  classical
  by_cases h : (x.1.1 ⟨0, hr⟩).natDegree < d
  · exact Sum.inl ⟨x.1, by simpa [blockSetLT] using h⟩
  · exact Sum.inr ⟨x.1, by
      have hd1 : (x.1.1 ⟨0, hr⟩).natDegree < d + 1 := by simpa [blockSetLT] using x.2
      have heq : (x.1.1 ⟨0, hr⟩).natDegree = d := by omega
      simpa [blockSet] using heq⟩

/-- Backward map of `blockSetLT_toFun`. -/
noncomputable def blockSetLT_invFun (r : ℕ) (hr : 0 < r) (d : ℕ)
    (y : ({a : monicStrictAntiNatDegree F r // a ∈ blockSetLT F r hr d} ⊕
          {a : monicStrictAntiNatDegree F r // a ∈ blockSet F r hr d})) :
    {a : monicStrictAntiNatDegree F r // a ∈ blockSetLT F r hr (d + 1)} := by
  classical
  cases y with
  | inl l =>
    exact ⟨l.1, by
      have h : (l.1.1 ⟨0, hr⟩).natDegree < d := by simpa [blockSetLT] using l.2
      change (l.1.1 ⟨0, hr⟩).natDegree < d + 1
      exact Nat.lt.step h⟩
  | inr t0 =>
    exact ⟨t0.1, by
      have h : (t0.1.1 ⟨0, hr⟩).natDegree = d := by simpa [blockSet] using t0.2
      change (t0.1.1 ⟨0, hr⟩).natDegree < d + 1
      rw [h]
      exact Nat.lt_succ_self d⟩

lemma blockSetLT_left_inv (r : ℕ) (hr : 0 < r) (d : ℕ)
    (x : {a : monicStrictAntiNatDegree F r // a ∈ blockSetLT F r hr (d + 1)}) :
    blockSetLT_invFun F r hr d (blockSetLT_toFun F r hr d x) = x := by
  classical
  by_cases h : (x.1.1 ⟨0, hr⟩).natDegree < d
  · dsimp [blockSetLT_toFun, blockSetLT_invFun]
    rw [dif_pos h]
  · dsimp [blockSetLT_toFun, blockSetLT_invFun]
    rw [dif_neg h]

lemma blockSetLT_right_inv (r : ℕ) (hr : 0 < r) (d : ℕ)
    (y : ({a : monicStrictAntiNatDegree F r // a ∈ blockSetLT F r hr d} ⊕
          {a : monicStrictAntiNatDegree F r // a ∈ blockSet F r hr d})) :
    blockSetLT_toFun F r hr d (blockSetLT_invFun F r hr d y) = y := by
  classical
  cases y with
  | inl l =>
    dsimp [blockSetLT_toFun, blockSetLT_invFun]
    have hl : (l.1.1 ⟨0, hr⟩).natDegree < d := by simpa [blockSetLT] using l.2
    rw [dif_pos hl]
  | inr t0 =>
    dsimp [blockSetLT_toFun, blockSetLT_invFun]
    have ht : (t0.1.1 ⟨0, hr⟩).natDegree = d := by simpa [blockSet] using t0.2
    rw [dif_neg (by omega : ¬ (t0.1.1 ⟨0, hr⟩).natDegree < d)]

/-- The `< d+1` blocks split as the disjoint union of the `< d` blocks and the
degree-`d` blocks. -/
noncomputable def blockSetLT_succ (r : ℕ) (hr : 0 < r) (d : ℕ) :
    {a : monicStrictAntiNatDegree F r // a ∈ blockSetLT F r hr (d + 1)} ≃
      ({a : monicStrictAntiNatDegree F r // a ∈ blockSetLT F r hr d} ⊕
       {a : monicStrictAntiNatDegree F r // a ∈ blockSet F r hr d}) where
  toFun := blockSetLT_toFun F r hr d
  invFun := blockSetLT_invFun F r hr d
  left_inv := by
    intro x
    exact blockSetLT_left_inv F r hr d x
  right_inv := by
    intro y
    exact blockSetLT_right_inv F r hr d y


/-- The level decomposition: the `< d` block sum is the sum of the level-`i` block sums
for `i < d`. -/
lemma S_lt_succ (r : ℕ) (hr : 0 < r) (𝔰 : Fin r → ℕ+) (d : ℕ) :
    S_lt F r hr 𝔰 (d + 1) = S_lt F r hr 𝔰 d + S F r hr 𝔰 d := by
  classical
  let A := {a : monicStrictAntiNatDegree F r // a ∈ blockSetLT F r hr (d + 1)}
  let A0 := {a : monicStrictAntiNatDegree F r // a ∈ blockSetLT F r hr d}
  let A1 := {a : monicStrictAntiNatDegree F r // a ∈ blockSet F r hr d}
  haveI : Finite A := by
    dsimp [A]
    exact finite_blockLT F hr (d + 1)
  haveI : Finite A0 := by
    dsimp [A0]
    exact finite_blockLT F hr d
  haveI : Finite A1 := by
    dsimp [A1]
    exact finite_block F hr d
  letI : Fintype A := Fintype.ofFinite (α := A)
  letI : Fintype A0 := Fintype.ofFinite (α := A0)
  letI : Fintype A1 := Fintype.ofFinite (α := A1)
  let e : A ≃ (A0 ⊕ A1) := by
    change {a : monicStrictAntiNatDegree F r // a ∈ blockSetLT F r hr (d + 1)} ≃
      ({a : monicStrictAntiNatDegree F r // a ∈ blockSetLT F r hr d} ⊕
       {a : monicStrictAntiNatDegree F r // a ∈ blockSet F r hr d})
    exact blockSetLT_succ F r hr d
  let underlying : A0 ⊕ A1 → monicStrictAntiNatDegree F r :=
    Sum.elim (fun a : A0 => a.1) (fun a : A1 => a.1)
  have hper (a : A) : zetaTerm F 𝔰 a.1 = zetaTerm F 𝔰 (underlying (e a)) := by
    dsimp [e, underlying, blockSetLT_succ]
    by_cases h : (a.1.1 ⟨0, hr⟩).natDegree < d
    · have hto : blockSetLT_toFun F r hr d a = Sum.inl (⟨a.1, by simpa [blockSetLT] using h⟩ : A0) := by
        dsimp [blockSetLT_toFun]
        rw [dif_pos h]
      rw [hto]
      rfl
    · have hto : blockSetLT_toFun F r hr d a = Sum.inr (⟨a.1, by
          have hd1 : (a.1.1 ⟨0, hr⟩).natDegree < d + 1 := by simpa [blockSetLT] using a.2
          have heq : (a.1.1 ⟨0, hr⟩).natDegree = d := by omega
          simpa [blockSet] using heq⟩ : A1) := by
        dsimp [blockSetLT_toFun]
        rw [dif_neg h]
      rw [hto]
      rfl
  calc
    S_lt F r hr 𝔰 (d + 1)
        = ∑' a : A, zetaTerm F 𝔰 a.1 := by rfl
    _ = ∑ a : A, zetaTerm F 𝔰 a.1 := by rw [tsum_fintype]
    _ = ∑ a : A, zetaTerm F 𝔰 (underlying (e a)) := by
          apply Finset.sum_congr rfl
          intro a ha
          exact hper a
    _ = ∑ y : A0 ⊕ A1, zetaTerm F 𝔰 (underlying y) := by
          exact Equiv.sum_comp (e := e) (g := fun y : A0 ⊕ A1 => zetaTerm F 𝔰 (underlying y))
    _ = (∑ a₀ : A0, zetaTerm F 𝔰 a₀.1) + ∑ a₁ : A1, zetaTerm F 𝔰 a₁.1 := by
          exact Fintype.sum_sum_type (fun y : A0 ⊕ A1 =>
            zetaTerm F 𝔰 (Sum.elim (fun a₀ : A0 => a₀.1) (fun a₁ : A1 => a₁.1) y))
    _ = S_lt F r hr 𝔰 d + S F r hr 𝔰 d := by
          rw [show S_lt F r hr 𝔰 d = ∑ a₀ : A0, zetaTerm F 𝔰 a₀.1 by
            change (∑' a₀ : A0, zetaTerm F 𝔰 a₀.1) = ∑ a₀ : A0, zetaTerm F 𝔰 a₀.1
            rw [tsum_fintype]]
          rw [show S F r hr 𝔰 d = ∑ a₁ : A1, zetaTerm F 𝔰 a₁.1 by
            change (∑' a₁ : A1, zetaTerm F 𝔰 a₁.1) = ∑ a₁ : A1, zetaTerm F 𝔰 a₁.1
            rw [tsum_fintype]]

/-- The level decomposition: `S_<d(s)` is the sum of the level-`i` power sums for
`i < d`. -/
lemma S_lt_eq_sum_levels (r : ℕ) (hr : 0 < r) (𝔰 : Fin r → ℕ+) (d : ℕ) :
    S_lt F r hr 𝔰 d = ∑ i ∈ Finset.range d, S F r hr 𝔰 i := by
  classical
  induction d with
  | zero =>
    let E := {a : monicStrictAntiNatDegree F r // a ∈ blockSetLT F r hr 0}
    haveI : Finite E := by
      dsimp [E]
      exact finite_blockLT F hr 0
    haveI : Fintype E := Fintype.ofFinite (α := E)
    have hE : S_lt F r hr 𝔰 0 = 0 := by
      change (∑' a : E, zetaTerm F 𝔰 a.1) = 0
      rw [tsum_fintype]
      apply Finset.sum_eq_zero
      intro a ha
      have hmem : (a.1.1 ⟨0, hr⟩).natDegree < 0 := by simpa [blockSetLT] using a.2
      omega
    rw [hE]
    simp
  | succ d ih =>
    rw [S_lt_succ F r hr 𝔰 d]
    rw [ih]
    rw [Finset.sum_range_succ]

end ZagierHoffmanPositiveChar
