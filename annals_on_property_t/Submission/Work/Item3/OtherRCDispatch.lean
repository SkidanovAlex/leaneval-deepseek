import Submission.Work.Item3.OtherRCStrict

open Submission.Nielsen
open Submission.FreeGroupAut
open Commons.GroupTheory.FreeGroup
open FreeGroup
set_option autoImplicit false

/-!
# OtherRCDispatch: the seven OTHER-rc shapes, dispatched and split

This module turns the seven state-level shape lemmas (`OtherRCStrict.lean`)
into the case-split skeleton of U1b (`otherRC_forces_strict`,
`UnchangedLow.lean`).

* `ShapePair α a b` — the seven-disjunct predicate on a *pair* of distinct
  coordinates (S1..S7 with the strictness bounds);
* `HasShapePair α` — some pair satisfies a shape;
* `hasShapePair_strict` — **PROVED**: any shape pair yields
  `∃ γ ∈ AutClosure n, N (α·γ) < N α`, by the seven state-level lemmas;
* `HasShapePairAt α w` — coordinate `w` participates in a shape (either
  role) — the branch predicate;
* `hasShapePairAt_imp` — **PROVED**: participation implies `HasShapePair`
  (branch (A) of the completeness case split: the low word's own coordinate
  participating feeds straight into `HasShapePair`);
* `OtherRCConfig` — the OTHER-rc configuration;
* `branchPartition` (open) — every OTHER-rc configuration is in branch (A)
  (`q` participates) or branch (B) (an rc-coverer participates); machine:
  0 counterexamples, and never `c` alone, never neither (`FallTwoRunNotes.md`);
* `otherRC_complete` (open) — the completeness statement;
  `otherRC_complete_of_partition` (**PROVED**) — the partition plus the
  branch mappings give completeness, hence U1b by
  `otherRC_strict_of_complete`.

All lemmas kernel-checked; axioms `[propext, Classical.choice,
Quot.sound]`.
-/

namespace Submission.Nielsen

/-- **A shape pair**: two distinct coordinates satisfy one of the seven
OTHER-rc overlap identities with its strictness bound (S1..S7). -/
def ShapePair {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (a b : Fin n) : Prop :=
  a ≠ b ∧
  ((∃ z : Fin n × Bool,
      (α (FreeGroup.of a)).toWord = [z] ++ FreeGroup.invRev ((α (FreeGroup.of b)).toWord) ∧
      2 ≤ FreeGroup.norm (α (FreeGroup.of a)))
  ∨ (∃ z : Fin n × Bool,
      (α (FreeGroup.of a)).toWord = [z] ++ (α (FreeGroup.of b)).toWord ∧
      2 ≤ FreeGroup.norm (α (FreeGroup.of a)))
  ∨ (∃ S : List (Fin n × Bool),
      (α (FreeGroup.of b)).toWord = FreeGroup.invRev ((α (FreeGroup.of a)).toWord) ++ S ∧
      S.length < FreeGroup.norm (α (FreeGroup.of a)))
  ∨ (∃ S : List (Fin n × Bool),
      (α (FreeGroup.of a)).toWord = (α (FreeGroup.of b)).toWord ++ S ∧
      S.length < FreeGroup.norm (α (FreeGroup.of a)))
  ∨ (∃ S : List (Fin n × Bool),
      (α (FreeGroup.of b)).toWord = (α (FreeGroup.of a)).toWord ++ S ∧
      S.length < FreeGroup.norm (α (FreeGroup.of a)))
  ∨ (∃ (P S : List (Fin n × Bool)) (y : Fin n × Bool),
      (α (FreeGroup.of a)).toWord = P ++ [y] ∧
      (α (FreeGroup.of b)).toWord = P ++ S ++ [y] ∧
      S.length + 2 < FreeGroup.norm (α (FreeGroup.of a)))
  ∨ (∃ (Xa Xb Z : List (Fin n × Bool)),
      (α (FreeGroup.of a)).toWord = Xa ++ Z ∧
      (α (FreeGroup.of b)).toWord = FreeGroup.invRev Z ++ Xb ∧
      (α (FreeGroup.of b)).toWord.length < 2 * Z.length))

/-- **The shape pair predicate.**  Some pair of distinct coordinates satisfies
one of the seven OTHER-rc shapes. -/
def HasShapePair {n : ℕ} (α : MulAut (FreeGroup (Fin n))) : Prop :=
  ∃ a b : Fin n, ShapePair α a b

/-- **Coordinate participation.**  The coordinate `w` participates in a
shape (in either role) — the branch predicate of the completeness case
split. -/
def HasShapePairAt {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (w : Fin n) : Prop :=
  (∃ b : Fin n, ShapePair α w b) ∨ (∃ b : Fin n, ShapePair α b w)

/-- **Branch (A) mapping (PROVED).**  A coordinate participating in a shape
yields `HasShapePair` — so branch (A) of the completeness split (the low
word's coordinate `q` participating) feeds straight into the predicate the
dispatch consumes. -/
theorem hasShapePairAt_imp {n : ℕ} (α : MulAut (FreeGroup (Fin n))) {w : Fin n}
    (h : HasShapePairAt α w) : HasShapePair α := by
  rcases h with ⟨b, hb⟩ | ⟨b, hb⟩
  · exact ⟨w, b, hb⟩
  · exact ⟨b, w, hb⟩

/-- **Dispatch.**  Any shape pair yields a strict closure move, by the seven
state-level shape lemmas. -/
theorem hasShapePair_strict {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (h : HasShapePair α) :
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧ N (α * γ) < N α := by
  rcases h with ⟨a, b, hab, h⟩
  rcases h with ⟨z, hu, hlen⟩ | ⟨z, hu, hlen⟩ | ⟨S, hv, hshort⟩ | ⟨S, hu, hshort⟩ |
    ⟨S, hv, hshort⟩ | ⟨P, S, y, hu, hv, hshort⟩ | ⟨Xa, Xb, Z, hu, hv, hshort⟩
  · exact begTelescopeRight_strict α a b hab z hu hlen
  · exact begTelescopeInvRight_strict α a b hab z hu hlen
  · exact prefixOverlap_strict α a b hab S hv hshort
  · exact covererExtendsPartner_strict α a b hab S hu hshort
  · exact partnerExtendsCoverer_strict α a b hab S hv hshort
  · exact covererPairOverlap_strict α a b hab P S y hu hv hshort
  · exact boundaryZipper_strict α a b hab Xa Xb Z hu hv hshort

/-- **The OTHER-rc configuration.**  Some row-`< p` even coordinate `q` has
an inhabited right covering class whose second half is not `invRev A` (i.e.
is not of the `endInv` form). -/
def OtherRCConfig {n : ℕ} (S : RebalanceState n) (p : Fin n)
    (A B : List (Fin n × Bool)) (α' : MulAut (FreeGroup (Fin n))) : Prop :=
  ∃ q : Fin n, (S.row.symm q).val < p.val ∧
    (coordWord α' q).length % 2 = 0 ∧
    RightCoverClass α' q (secondHalf (coordWord α' q)) ∧
    ¬ EndsWithWord (coordWord α' q) (FreeGroup.invRev A)

/-- **Branch partition container (open).**  Every OTHER-rc configuration of a
genuine-run post-pass state lies in branch (A) (the low coordinate `q`
participates in a shape) or branch (B) (an rc-coverer of `q` participates in
a shape).  Machine: 0 counterexamples (52 shape witnesses at n = 4: q-
participation S1 4 / S4 2 / S5 2, coverer-participation S1 6 / S2 10 /
S3 7 / S4 7 / S5 7; never `c` alone, never neither). -/
def branchPartition {n : ℕ} (S : RebalanceState n) (p : Fin n)
    (A B : List (Fin n × Bool)) (α' : MulAut (FreeGroup (Fin n))) : Prop :=
  GenuineRunTo S p A B α' → OtherRCConfig S p A B α' →
    (∃ q : Fin n, (S.row.symm q).val < p.val ∧ HasShapePairAt α' q ∧
        RightCoverClass α' q (secondHalf (coordWord α' q)))
    ∨ (∃ q u : Fin n, (S.row.symm q).val < p.val ∧
        RightCoverClass α' q (secondHalf (coordWord α' q)) ∧ u ≠ q ∧
        (EndsWithWord (coordWord α' u) (secondHalf (coordWord α' q)) ∨
          BeginsWithWord (coordWord α' u) (FreeGroup.invRev (secondHalf (coordWord α' q)))) ∧
        HasShapePairAt α' u)

/-- **Completeness container (open).**  Every OTHER-rc configuration of a
genuine-run post-pass state admits one of the seven shapes. -/
def otherRC_complete {n : ℕ} (S : RebalanceState n) (p : Fin n)
    (A B : List (Fin n × Bool)) (α' : MulAut (FreeGroup (Fin n))) : Prop :=
  GenuineRunTo S p A B α' → OtherRCConfig S p A B α' → HasShapePair α'

/-- **Assembly (PROVED).**  The branch partition (open) plus the branch
mappings give completeness: in branch (A) the low coordinate participates,
in branch (B) an rc-coverer participates, and either participation yields
`HasShapePair` by `hasShapePairAt_imp`. -/
theorem otherRC_complete_of_partition {n : ℕ} (S : RebalanceState n) (p : Fin n)
    (A B : List (Fin n × Bool)) (α' : MulAut (FreeGroup (Fin n)))
    (hpart : branchPartition S p A B α') : otherRC_complete S p A B α' := by
  intro hrun hcfg
  rcases hpart hrun hcfg with ⟨q, _hq, hshape, _hrc⟩ | ⟨q, u, _hq, _hrc, _hu, _hcov, hshape⟩
  · exact hasShapePairAt_imp α' hshape
  · exact hasShapePairAt_imp α' hshape

/-- **Assembly of the OTHER-rc branch.**  Completeness plus the proven
dispatch give the strict closure move from an OTHER-rc configuration of a
genuine run — the conclusion of U1b (`otherRC_forces_strict`). -/
theorem otherRC_strict_of_complete {n : ℕ} (S : RebalanceState n) (p : Fin n)
    (A B : List (Fin n × Bool)) (α' : MulAut (FreeGroup (Fin n)))
    (hcomplete : otherRC_complete S p A B α') (hrun : GenuineRunTo S p A B α')
    (hcfg : OtherRCConfig S p A B α') :
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧ N (α' * γ) < N α' :=
  hasShapePair_strict α' (hcomplete hrun hcfg)

/-- **Compensation container (open; the refined target).**  For every rc-coverer
`u` of the low coordinate `q` (either disjunct: `u` ends with the second half
of `q`'s word, or begins with its inverse-reversal), either the *coverer* `u`
participates in a shape, or the *low coordinate* `q` does.  Machine: 14/14
(ends-`y`) and 19/19 (begins-`y⁻¹`) at n = 4, 0 counterexamples.  This is the
valid form of the `ends y` / `begins y⁻¹` case analysis: the per-coverer
statement is FALSE (12/13, 10/11 — non-participating coverers exist), and the
pair `(u, q)` never forms a shape (0/34); the non-participating coverers are
exactly compensated by `q` participating. -/
def branchCompensation {n : ℕ} (S : RebalanceState n) (p : Fin n)
    (A B : List (Fin n × Bool)) (α' : MulAut (FreeGroup (Fin n))) : Prop :=
  GenuineRunTo S p A B α' → OtherRCConfig S p A B α' →
    ∀ q : Fin n, (S.row.symm q).val < p.val →
      (coordWord α' q).length % 2 = 0 →
      RightCoverClass α' q (secondHalf (coordWord α' q)) →
      ¬ EndsWithWord (coordWord α' q) (FreeGroup.invRev A) →
      ∀ u : Fin n, u ≠ q →
        (EndsWithWord (coordWord α' u) (secondHalf (coordWord α' q)) ∨
          BeginsWithWord (coordWord α' u) (FreeGroup.invRev (secondHalf (coordWord α' q)))) →
        HasShapePairAt α' u ∨ HasShapePairAt α' q

/-- **Reduction (PROVED).**  The compensation container implies the branch
partition: given the OTHER-rc witness `q` (whose right covering class is
inhabited by some `u`), compensation at `u` yields either `q` participating
(branch (A)) or `u` participating (branch (B)). -/
theorem branchPartition_of_compensation {n : ℕ} (S : RebalanceState n) (p : Fin n)
    (A B : List (Fin n × Bool)) (α' : MulAut (FreeGroup (Fin n)))
    (h : branchCompensation S p A B α') : branchPartition S p A B α' := by
  intro hrun hcfg
  obtain ⟨q, hq, heven, hrc, hend⟩ := hcfg
  obtain ⟨u, huq, hcov⟩ := hrc
  rcases h hrun ⟨q, hq, heven, ⟨u, huq, hcov⟩, hend⟩ q hq heven
      ⟨u, huq, hcov⟩ hend u huq hcov with hup | hqp
  · exact Or.inr ⟨q, u, hq, ⟨u, huq, hcov⟩, huq, hcov, hup⟩
  · exact Or.inl ⟨q, hq, hqp, ⟨u, huq, hcov⟩⟩

/-! ### Bridge: a single strict elementary move contradicts residualness

The `∃ γ ∈ AutClosure` form of the shape lemmas' conclusion does not by itself
contradict `NoEndCancel` (a macro could drop `N` without any single move from
the *initial* state doing so).  What the U1 assembly needs is the single-move
form: one of `rho`/`rhoNeg`/`lam`/`lamNeg` strictly dropping `N` contradicts
`NoEndCancel` by `noEndCancel_iff_local_min`.  These four bridges make the
seven shape lemmas (each of whose proofs internally *does* produce a single
move) usable for that contradiction. -/

/-- A strict `rho` move contradicts residualness. -/
theorem not_noEndCancel_of_rho {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (i j : Fin n) (hij : i ≠ j) (h : N (α * rho i j hij) < N α) :
    ¬ NoEndCancel n α := by
  intro hres
  have hle := (noEndCancel_iff_local_min n α).mp hres
  have := hle.1 i j hij
  omega

/-- A strict `rhoNeg` move contradicts residualness. -/
theorem not_noEndCancel_of_rhoNeg {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (i j : Fin n) (hij : i ≠ j) (h : N (α * rhoNeg i j hij) < N α) :
    ¬ NoEndCancel n α := by
  intro hres
  have hle := (noEndCancel_iff_local_min n α).mp hres
  have := hle.2.1 i j hij
  omega

/-- A strict `lam` move contradicts residualness. -/
theorem not_noEndCancel_of_lam {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (i j : Fin n) (hij : i ≠ j) (h : N (α * lam i j hij) < N α) :
    ¬ NoEndCancel n α := by
  intro hres
  have hle := (noEndCancel_iff_local_min n α).mp hres
  have := hle.2.2.1 i j hij
  omega

/-- A strict `lamNeg` move contradicts residualness. -/
theorem not_noEndCancel_of_lamNeg {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (i j : Fin n) (hij : i ≠ j) (h : N (α * lamNeg i j hij) < N α) :
    ¬ NoEndCancel n α := by
  intro hres
  have hle := (noEndCancel_iff_local_min n α).mp hres
  have := hle.2.2.2 i j hij
  omega

end Submission.Nielsen
