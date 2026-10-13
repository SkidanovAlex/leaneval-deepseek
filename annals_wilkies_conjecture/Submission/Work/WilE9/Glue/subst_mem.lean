import Mathlib
import Submission.Work.WilE9.Defs
import Submission.Work.WilG0.Defs
import Submission.Work.WilG0.diagSet_eq
import Submission.Work.WilG0.diagPoly_totalDegree_le
import Submission.Work.WilG4a.subst_lift_eq

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilE9.Glue

open WilkiesDesign WilkiesDesign.E

/-
  Pullback of a `Gen`-set along a coordinate map `ι : Fin m → Fin N`.

  IMPORTANT: do NOT prove this by instantiating the generic `SOMin` version
  (`Work.WilG4a.subst_mem`) at `WilkiesDesign.E.genSOMin`: the `comps` field of `genSOMin` is
  the `sorry`ed `E8_comps`, so such a proof would depend on `sorryAx` and is rejected. The
  proof has to be a native transcription of the WilG4a chain with `S.Ω` replaced by `Gen`
  (i.e. re-prove `liftNM_mem`, `diagSet_mem` for `Gen` — the files
  `Submission/Work/WilG0/liftNM_mem.lean`, `Submission/Work/WilG0/diagSet_mem.lean`,
  `Submission/Work/WilG4a/subst_mem.lean`, `Submission/Work/WilG4a/subst_lift_eq.lean` are
  readable and their proofs transplant verbatim). The set identity to use is
  `Work.WilG4a.subst_lift_eq` (it mentions no `SOMin`, so it is directly usable).

  Below, the three ingredients of the `SOMin` chain of `Work.WilG4a.subst_mem` are
  re-proved for the inductive `Gen` (they are `gen_liftNM_mem`, `gen_diagSet_mem`,
  `gen_projLastIter_mem`), using only the constructors `Gen.prod_left`, `Gen.hyp`,
  `Gen.proj` and the monotonicities `Gen.monoF`/`Gen.monoD`/`Gen.inter₂`.  No `SOMin`
  (and hence no `genSOMin`/`E8_comps`) is mentioned anywhere.
-/

/-! ## Transport along an equality of dimensions -/

/-- Membership in the transport of a set along an equality of dimensions: the two ambient
index types are identified by `Fin.cast`, which preserves the underlying value. -/
private theorem cast_mem_iff {a b : ℕ} (h : a = b) {X : Set (Fin a → ℝ)} (z : Fin b → ℝ) :
    z ∈ (h ▸ X) ↔ (fun i : Fin a => z (Fin.cast h i)) ∈ X := by
  subst h
  rfl

/-- `Fin.cast` of `Fin.addNat` is `Fin.natAdd`: the two ways of shifting an index agree. -/
private theorem cast_addNat_eq_natAdd (n m : ℕ) (j : Fin m) :
    Fin.cast (Nat.add_comm m n) (Fin.addNat j n) = Fin.natAdd n j := by
  ext
  simp only [Fin.val_cast, Fin.val_addNat, Fin.val_natAdd]
  exact Nat.add_comm _ _

/-- Transport of a `Gen`-set along an equality of dimensions. -/
theorem gen_cast_mem {a b F D : ℕ} (h : a = b) {X : Set (Fin a → ℝ)}
    (hX : Gen F D a X) : Gen F D b (h ▸ X) := by
  subst h
  exact hX

/-! ## `liftNM`: prepending `n` free coordinates -/

/-- Iterating `Gen.prod_left` `n` times prepends `n` free coordinates to `A`, producing a set
in dimension `m + n` (the `D`-block sits in the last `m` coordinates of `Fin (m + n)`). -/
private theorem liftMN_mem_aux {m F D : ℕ} {A : Set (Fin m → ℝ)}
    (hA : Gen F D m A) (n : ℕ) : Gen (F + n) D (m + n) (Work.WilG0.liftMN n m A) := by
  induction n with
  | zero =>
    have h0 : Work.WilG0.liftMN 0 m A = A := by ext z; simp [Work.WilG0.liftMN]
    rw [h0]
    simpa using hA
  | succ n ih =>
    -- `liftMN (n+1) m A` is the `Fin.tail`-preimage of `liftMN n m A`
    have hz : Work.WilG0.liftMN (n+1) m A
        = {z : Fin (m+(n+1)) → ℝ | Fin.tail z ∈ Work.WilG0.liftMN n m A} := by
      apply Set.ext
      intro z
      have hfun : (fun j : Fin m => (Fin.tail z) (Fin.addNat j n))
          = (fun j : Fin m => z (Fin.addNat j (n+1))) := by
        funext j; rfl
      show ((fun j : Fin m => z (Fin.addNat j (n+1))) ∈ A) ↔
           ((fun j : Fin m => (Fin.tail z) (Fin.addNat j n)) ∈ A)
      rw [hfun]
    rw [hz]
    exact Gen.prod_left ih

/-- `liftNM n m A` is `liftMN n m A` transported along `Nat.add_comm m n`. -/
private theorem liftNM_eq_liftMN_cast (n m : ℕ) (A : Set (Fin m → ℝ)) :
    Work.WilG0.liftNM n m A = (Nat.add_comm m n) ▸ Work.WilG0.liftMN n m A := by
  apply Set.ext
  intro z
  rw [cast_mem_iff]
  simp only [Work.WilG0.liftNM, Work.WilG0.liftMN, Set.mem_ofPred_eq]
  have hfun : (fun j : Fin m => z (Fin.cast (Nat.add_comm m n) (Fin.addNat j n)))
      = (fun j : Fin m => z (Fin.natAdd n j)) := by
    funext j
    rw [cast_addNat_eq_natAdd]
  rw [hfun]

/-- `liftNM n m A` — `A` placed on the last `m` coordinates of `ℝ^{n+m}` — is a `Gen`-set of
format `F + n` (one `prod_left` per free coordinate) and unchanged degree. -/
theorem gen_liftNM_mem {n m F D : ℕ} {A : Set (Fin m → ℝ)} (h : Gen F D m A) :
    Gen (F + n) D (n + m) (Work.WilG0.liftNM n m A) := by
  have h1 : Gen (F + n) D (m + n) (Work.WilG0.liftMN n m A) := liftMN_mem_aux h n
  have h2 : Gen (F + n) D (n + m)
      ((Nat.add_comm m n) ▸ Work.WilG0.liftMN n m A) :=
    gen_cast_mem (Nat.add_comm m n) h1
  rwa [← liftNM_eq_liftMN_cast n m A] at h2

/-! ## The diagonal set -/

/-- The graph `diagSet n m ι` of the coordinate substitution `x ↦ x ∘ ι` is a `Gen`-set of
format `n + m` and degree `2` (the `hyp` axiom applied to the sum of squares `diagPoly`). -/
theorem gen_diagSet_mem (n m : ℕ) (ι : Fin m → Fin n) :
    Gen (n + m) 2 (n + m) (Work.WilG0.diagSet n m ι) := by
  have hmem : Gen (n + m) (Work.WilG0.diagPoly n m ι).totalDegree (n + m)
      (Work.WilG0.diagSet n m ι) := by
    rw [Work.WilG0.diagSet_eq n m ι]
    exact Gen.hyp (n + m) (Work.WilG0.diagPoly n m ι)
  exact Gen.monoD (Work.WilG0.diagPoly_totalDegree_le n m ι) hmem

/-! ## Iterated projection -/

/-- Iterating `Gen.proj` `m` times eliminates the last `m` coordinates: dimension `n + m → n`,
format `F → F + m`, degree unchanged. -/
theorem gen_projLastIter_mem {n m F D : ℕ} {X : Set (Fin (n + m) → ℝ)}
    (h : Gen F D (n + m) X) : Gen (F + m) D n (Work.WilG0.projLastIter n m X) := by
  have key : ∀ m (F D : ℕ) (X : Set (Fin (n + m) → ℝ)),
      Gen F D (n + m) X → Gen (F + m) D n (Work.WilG0.projLastIter n m X) := by
    intro m
    induction m with
    | zero =>
      intro F D X hX
      simpa [Work.WilG0.projLastIter] using hX
    | succ m ih =>
      intro F D X hX
      have hX' : Gen (F + 1) D (n + m) (projLast X) := Gen.proj hX
      have hres : Gen ((F + 1) + m) D n (Work.WilG0.projLastIter n m (projLast X)) :=
        ih (F + 1) D (projLast X) hX'
      have heq : (F + 1) + m = F + (m + 1) := by omega
      exact heq ▸ hres
  exact key m F D X h

/-! ## The substitution atom -/

/-- **Substitution.** Pulling back a `Gen F D m`-set along a coordinate map `ι : Fin m → Fin N`
yields a `Gen`-set of dimension `N`, format at most `F + 2 * (N + m) + 1` and degree at most
`D + 2`.

The pulled-back set is the projection of `liftNM N m A ∩ diagSet N m ι` (the set identity
`Work.WilG4a.subst_lift_eq`): the lift costs `N` in the format, the intersection one more
format and `2` in the degree, and the `m` projections cost `m` more; finally
`max (F + N) (N + m) + 1 + m ≤ F + 2 * (N + m) + 1`. -/
theorem subst_mem {N m F D : ℕ} {A : Set (Fin m → ℝ)} (ι : Fin m → Fin N)
    (hA : WilkiesDesign.E.Gen F D m A) :
    WilkiesDesign.E.Gen (F + 2 * (N + m) + 1) (D + 2) N {x : Fin N → ℝ | (fun j => x (ι j)) ∈ A} := by
  have hlift : Gen (F + N) D (N + m) (Work.WilG0.liftNM N m A) := gen_liftNM_mem hA
  have hdiag : Gen (N + m) 2 (N + m) (Work.WilG0.diagSet N m ι) := gen_diagSet_mem N m ι
  have h3 : Gen (max (F + N) (N + m) + 1) (D + 2) (N + m)
      (Work.WilG0.liftNM N m A ∩ Work.WilG0.diagSet N m ι) :=
    Gen.inter₂ hlift hdiag
  have h4 : Gen (max (F + N) (N + m) + 1 + m) (D + 2) N
      (Work.WilG0.projLastIter N m
        (Work.WilG0.liftNM N m A ∩ Work.WilG0.diagSet N m ι)) :=
    gen_projLastIter_mem h3
  have h5 : Gen (F + 2 * (N + m) + 1) (D + 2) N
      (Work.WilG0.projLastIter N m
        (Work.WilG0.liftNM N m A ∩ Work.WilG0.diagSet N m ι)) :=
    Gen.monoF (by omega) h4
  have hset : {x : Fin N → ℝ | (fun j => x (ι j)) ∈ A} =
      Work.WilG0.projLastIter N m
        (Work.WilG0.liftNM N m A ∩ Work.WilG0.diagSet N m ι) :=
    Work.WilG4a.subst_lift_eq ι A
  rw [hset]
  exact h5

end Work.WilE9.Glue
