/-
Area DSCOH (curric-46) — the values of a Čech `1`-cocycle on pairs of charts.

Let `c` be a `0`-cochain of the chart Čech complex of the standard cover of `ℙⁿ`, i.e. a family
of degree-zero sections `c {k} ∈ (M[1/X_k])₀` indexed by the singletons, and suppose that `c` is a
cocycle: `cechDiff c = 0`.  The `{i,j}`-component of `cechDiff c` is the alternating sum

  `(-1)^{#{k ∈ {i,j} : k < i}} • res_{j → {i,j}} c {j} + (-1)^{#{k ∈ {i,j} : k < j}} • res_{i → {i,j}} c {i}`

and `c` being a cocycle forces this sum to vanish; since at least one of the two signs is `-1`
and the other `+1` (exactly one of `i < j`, `j < i` holds), the two terms are equal.  That is the
statement proved here: **the two restrictions of the `1`-cocycle `c` to the chart `{i,j}` agree**.

The mathematical content is bookkeeping: the transition maps `resAt` of the chart localizations
and the components of `cechDiff` are indexed by *finsets*, and `{i,j} \ {i} = {j}` holds only
propositionally, not definitionally.  The auxiliary lemmas below (`resAt_heq_apply` and
`cechDiff_pair_eq`) are the tools that reconcile the two descriptions.
-/
import Mathlib
import Submission.Work.DSCOH.Basic
import Submission.Work.DSCOH.Cech
import Submission.Work.DSCOH.Shift
import Submission.Work.DSCOH.cechDiff_apply_coe
import Submission.Work.DSCOH.negOne_pow_card_filter_erase

namespace Work.DSCOH

/-- `resAt` only depends on the proof of the inclusion of charts (which is a proposition). -/
private theorem resAt_proof_irrel {A : Type*} [CommRing A] {n : ℕ}
    {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M]
    [IsScalarTower A (Poly A n) M]
    {S T : Finset (Fin n)} (h₁ h₂ : S ⊆ T) (x : locAt (A := A) (M := M) S) :
    resAt (A := A) (M := M) h₁ x = resAt (A := A) (M := M) h₂ x :=
  congrArg (fun h : S ⊆ T => resAt (A := A) (M := M) h x) (Subsingleton.elim h₁ h₂)

/-- Heterogeneous equality of the values of a dependent function at equal arguments. -/
private lemma heq_apply_of_eq_aux {α : Type*} {β : α → Type*} {a b : α} (h : a = b)
    (f : (i : α) → β i) : HEq (f a) (f b) := by
  subst h
  rfl

/-- Restriction maps out of charts that are *equal* (as finsets) but whose inclusions into `T` are
different proofs agree on heterogeneous-equal elements.  This is what allows the comparison of the
`{i,j} \ {i}`-component of a Čech cochain with its `{j}`-component. -/
private theorem resAt_heq_apply {A : Type*} [CommRing A] {n : ℕ}
    {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M]
    [IsScalarTower A (Poly A n) M]
    {S S' T : Finset (Fin n)} (hS : S = S') (h : S ⊆ T) (h' : S' ⊆ T)
    {x : locAt (A := A) (M := M) S} {x' : locAt (A := A) (M := M) S'} (hx : HEq x x') :
    resAt (A := A) (M := M) h x = resAt (A := A) (M := M) h' x' := by
  subst hS
  rw [eq_of_heq hx]

/-- **The Čech differential at a two-element chart.**  The `{i,j}`-component of `cechDiff 0 c` is
the alternating sum of the two restrictions of `c` from the singletons `{j}` and `{i}`.  The
sources `{i,j} \ {i}` and `{i,j} \ {j}` of the restrictions coming out of `cechDiff` are
identified with `{j}` and `{i}` in the statement of this lemma. -/
private theorem cechDiff_pair_eq {A : Type*} [CommRing A] {n : ℕ} (d : ℕ)
    [SetLike.GradedSMul (homSub A n) (shift (A := A) (n := n) d)]
    {i j : Fin n} (hij : i ≠ j)
    (hcard : ({i, j} : Finset (Fin n)).card = 0 + 1 + 1)
    (c : CechTerm (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d) 0) :
    (((cechDiff (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d) 0 c)
        ⟨{i, j}, hcard⟩ : locAt (A := A) (M := Poly A n) ({i, j} : Finset (Fin n)))) =
      (-1 : ℤ) ^ ((({i, j} : Finset (Fin n)).filter (fun x => x < i)).card) •
        (resAt (A := A) (M := Poly A n) (S := {j}) (T := {i, j}) (by simp)
          (c ⟨{j}, Finset.card_singleton j⟩ : locAt (A := A) (M := Poly A n) {j}))
      + (-1 : ℤ) ^ ((({i, j} : Finset (Fin n)).filter (fun x => x < j)).card) •
        (resAt (A := A) (M := Poly A n) (S := {i}) (T := {i, j}) (by simp)
          (c ⟨{i}, Finset.card_singleton i⟩ : locAt (A := A) (M := Poly A n) {i})) := by
  rw [cechDiff_apply_coe (A := A) (n := n) (M := Poly A n)
        (shift (A := A) (n := n) d) 0 c ⟨{i, j}, hcard⟩]
  -- the sum over `{i,j}.attach` has exactly the two terms at `i` and `j`
  have hattach : ({i, j} : Finset (Fin n)).attach = {⟨i, by simp⟩, ⟨j, by simp⟩} := by
    apply Finset.ext
    intro x
    constructor
    · intro _
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases Finset.mem_insert.mp x.2 with h | h
      · exact Or.inl (Subtype.ext h : x = ⟨i, by simp⟩)
      · exact Or.inr (Subtype.ext (Finset.mem_singleton.mp h) : x = ⟨j, by simp⟩)
    · intro _
      exact Finset.mem_attach _ _
  rw [hattach]
  have hne : (⟨i, by simp⟩ : {x // x ∈ ({i, j} : Finset (Fin n))}) ≠ ⟨j, by simp⟩ := by
    intro h; exact hij (Subtype.ext_iff.mp h)
  rw [Finset.sum_pair hne]
  have hErase_i : ({i, j} : Finset (Fin n)).erase i = {j} := by
    rw [Finset.erase_insert (by simpa using hij)]
  have hErase_j : ({i, j} : Finset (Fin n)).erase j = {i} := by
    rw [Finset.erase_insert_of_ne hij]; simp
  -- compare the two summands with the two restrictions at the singletons
  congr 1
  · congr 1
    refine resAt_heq_apply (A := A) (n := n) (M := Poly A n) (hS := hErase_i) _ _ ?_
    refine heq_apply_of_eq_aux ?_
      (fun S : {S : Finset (Fin n) // S.card = 0 + 1} =>
        (c S : locAt (A := A) (M := Poly A n) S.1))
    exact Subtype.ext hErase_i
  · congr 1
    refine resAt_heq_apply (A := A) (n := n) (M := Poly A n) (hS := hErase_j) _ _ ?_
    refine heq_apply_of_eq_aux ?_
      (fun S : {S : Finset (Fin n) // S.card = 0 + 1} =>
        (c S : locAt (A := A) (M := Poly A n) S.1))
    exact Subtype.ext hErase_j

/-- `(-1)^a` is its own inverse in `ℤ`. -/
private theorem negOne_pow_mul_self (a : ℕ) : (-1 : ℤ) ^ a * (-1 : ℤ) ^ a = 1 := by
  rw [← pow_add, show a + a = 2 * a from by ring, pow_mul]
  norm_num

/-- The sign arithmetic at the end of the proof: if `s` and `t` are the two (opposite) signs and
`s • X + t • Y = 0`, then `X = Y`. -/
private theorem eq_of_smul_add_smul_eq_zero {M : Type*} [AddCommGroup M] {s t : ℤ} {X Y : M}
    (hsq : s * s = 1) (hst : s * t = -1) (h : s • X + t • Y = 0) : X = Y := by
  have h1 := congrArg (fun z => s • z) h
  rw [smul_add, smul_smul, smul_smul, smul_zero, hsq, hst, one_smul, neg_smul, one_smul] at h1
  have h2 : X - Y = 0 := by simpa [sub_eq_add_neg] using h1
  exact sub_eq_zero.mp h2

theorem resAt_eq_of_cechDiff_zero {A : Type*} [CommRing A] {n : ℕ} (d : ℕ)
    [SetLike.GradedSMul (homSub A n) (shift (A := A) (n := n) d)]
    {i j : Fin n} (hij : i ≠ j)
    (c : CechTerm (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d) 0)
    (hc : cechDiff (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d) 0 c = 0) :
    resAt (A := A) (M := Poly A n) (S := {j}) (T := {i, j}) (by simp)
        (c ⟨{j}, Finset.card_singleton j⟩)
      = resAt (A := A) (M := Poly A n) (S := {i}) (T := {i, j}) (by simp)
        (c ⟨{i}, Finset.card_singleton i⟩) := by
  have hcard : ({i, j} : Finset (Fin n)).card = 0 + 1 + 1 := by
    rw [Finset.card_pair hij]
  -- the `{i,j}`-component of the cocycle condition
  have hzero : (((cechDiff (A := A) (n := n) (M := Poly A n)
        (shift (A := A) (n := n) d) 0 c) ⟨{i, j}, hcard⟩ :
          locAt (A := A) (M := Poly A n) ({i, j} : Finset (Fin n)))) = 0 := by
    rw [hc]; rfl
  have hErase_i : ({i, j} : Finset (Fin n)).erase i = {j} := by
    rw [Finset.erase_insert (by simpa using hij)]
  have hErase_j : ({i, j} : Finset (Fin n)).erase j = {i} := by
    rw [Finset.erase_insert_of_ne hij]; simp
  -- the two remaining filter cardinalities vanish
  have hfilter_j : (((({i, j} : Finset (Fin n)).erase i).filter (fun k => k < j))).card = 0 := by
    rw [hErase_i]; simp
  have hfilter_i : (((({i, j} : Finset (Fin n)).erase j).filter (fun k => k < i))).card = 0 := by
    rw [hErase_j]; simp
  -- the two signs add up to zero, hence are opposite
  have hsign : (-1 : ℤ) ^ ((({i, j} : Finset (Fin n)).filter (fun x => x < i)).card)
      + (-1 : ℤ) ^ ((({i, j} : Finset (Fin n)).filter (fun x => x < j)).card) = 0 := by
    have h := negOne_pow_card_filter_erase ({i, j} : Finset (Fin n))
      (by simp : i ∈ ({i, j} : Finset (Fin n))) (by simp : j ∈ ({i, j} : Finset (Fin n))) hij
    rw [hfilter_j, hfilter_i] at h
    simpa using h
  have hst : (-1 : ℤ) ^ ((({i, j} : Finset (Fin n)).filter (fun x => x < i)).card)
      * (-1 : ℤ) ^ ((({i, j} : Finset (Fin n)).filter (fun x => x < j)).card) = -1 := by
    have ht : (-1 : ℤ) ^ ((({i, j} : Finset (Fin n)).filter (fun x => x < j)).card)
        = -(-1 : ℤ) ^ ((({i, j} : Finset (Fin n)).filter (fun x => x < i)).card) := by
      linarith [hsign]
    rw [ht, mul_neg, negOne_pow_mul_self]
  -- the cocycle condition in the two-term form of `cechDiff_pair_eq`
  have hkey : (-1 : ℤ) ^ ((({i, j} : Finset (Fin n)).filter (fun x => x < i)).card) •
        (resAt (A := A) (M := Poly A n) (S := {j}) (T := {i, j}) (by simp)
          (c ⟨{j}, Finset.card_singleton j⟩ : locAt (A := A) (M := Poly A n) {j}))
      + (-1 : ℤ) ^ ((({i, j} : Finset (Fin n)).filter (fun x => x < j)).card) •
        (resAt (A := A) (M := Poly A n) (S := {i}) (T := {i, j}) (by simp)
          (c ⟨{i}, Finset.card_singleton i⟩ : locAt (A := A) (M := Poly A n) {i})) = 0 := by
    convert (cechDiff_pair_eq (A := A) (n := n) d hij hcard c).symm.trans hzero using 1
  exact eq_of_smul_add_smul_eq_zero (negOne_pow_mul_self _) hst hkey

end Work.DSCOH
