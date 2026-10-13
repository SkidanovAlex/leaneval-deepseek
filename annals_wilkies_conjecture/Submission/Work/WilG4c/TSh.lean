/-
  WilG4c / `TSh` — a small "Ω-formula calculus" with *declared* polynomial degrees.

  ## Why not reuse `Work.WilG0.OShape`?

  `Work.WilG0.realize_mem_Omega` already gives that every `OShape` realises in
  `S.Ω (oFmt F s) (s.deg d)`, where `s.deg d` sums the *actual* `totalDegree`s of the
  polynomial atoms.  For the encoding below we need the resulting degree to be bounded by a
  polynomial `b.eval D` in the *degree parameter* `D` alone; with `OShape` that means
  bounding `totalDegree P` for each of the (many, nested) concrete polynomials appearing in
  the data, which requires traversing the whole nested data term.

  Here the degree is instead *declared*: a polynomial atom is `TSh.poly n P h` with
  `h : P.totalDegree ≤ 8`, so its degree contribution is the literal `8` and the bound
  `s.deg d ≤ tAtoms s * (D + 2 + 8)` follows from `TSh.MemLe` (every `mem` atom declares a
  degree `≤ D`) by a short induction.  The price is local: each atom of the encoding carries a
  `totalDegree ≤ 8` side condition, discharged once and for all when the atom is built.

  The construction is carried out in the structure `PKS S F D n` which bundles the shape, its
  data, `TSh.Good` (so that `TSh.realize_mem_Omega` applies) and `TSh.MemLe` (so that the
  degree is bounded): the combinators preserve both fields, so no nested unfolding is ever
  needed.

  `exb` is the *block* existential: `exb n k s` quantifies the last `k` coordinates at once
  and realises as `Work.WilG5.projN k`.  It is what makes the construction below parametric in
  the number `M` of cube coordinates.

  Everything here is `sorry`-free.
-/
import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilG5.Basic
import Submission.Work.WilG5.Reindex3
import Submission.Work.WilG0.Subst

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-! ## 1. The calculus -/

/-- Shapes of first-order formulas whose atoms are a polynomial equation of total degree
`≤ 8`, or membership of a coordinate substitution `x ∘ ι` in an `Ω`-set.  `ex` quantifies the
last variable, `exb k` the last `k` of them. -/
inductive TSh : ℕ → Type where
  | poly (n : ℕ) (P : MvPolynomial (Fin n) ℝ) (h : P.totalDegree ≤ 8) : TSh n
  | mem (n m : ℕ) (ι : Fin m → Fin n) : TSh n
  | neg {n : ℕ} (s : TSh n) : TSh n
  | and {n : ℕ} (s t : TSh n) : TSh n
  | ex {n : ℕ} (s : TSh (n + 1)) : TSh n
  | exb (n k : ℕ) (s : TSh (n + k)) : TSh n

/-- Atom data: a `mem` atom carries its set and its declared degree. -/
def TSh.Data : {n : ℕ} → TSh n → Type
  | _, .poly .. => PUnit
  | _, .mem _ m _ => Set (Fin m → ℝ) × ℕ
  | _, .neg s => s.Data
  | _, .and s t => s.Data × t.Data
  | _, .ex s => s.Data
  | _, .exb _ _ s => s.Data

/-- The set realised by a shape and its data. -/
def TSh.realize : {n : ℕ} → (s : TSh n) → s.Data → Set (Fin n → ℝ)
  | _, .poly _ P _, _ => {x | MvPolynomial.eval x P = 0}
  | _, .mem _ _ ι, d => {x | x ∘ ι ∈ d.1}
  | _, .neg s, d => (TSh.realize s d)ᶜ
  | _, .and s t, d => TSh.realize s d.1 ∩ TSh.realize t d.2
  | _, .ex s, d => projLast (TSh.realize s d)
  | _, .exb _ k s, d => Work.WilG5.projN k (TSh.realize s d)

/-- The declared degree of a shape. -/
def TSh.deg : {n : ℕ} → (s : TSh n) → s.Data → ℕ
  | _, .poly .., _ => 8
  | _, .mem _ _ _, d => d.2 + 2
  | _, .neg s, d => TSh.deg s d
  | _, .and s t, d => TSh.deg s d.1 + TSh.deg t d.2
  | _, .ex s, d => TSh.deg s d
  | _, .exb _ _ s, d => TSh.deg s d

/-- The goodness condition of the atoms: the `mem` sets lie in `S.Ω F (declared degree)`. -/
def TSh.Good (S : SOMin) (F : ℕ) : {n : ℕ} → (s : TSh n) → s.Data → Prop
  | _, .poly .., _ => True
  | _, .mem _ m _, d => d.1 ∈ S.Ω F d.2 m
  | _, .neg s, d => TSh.Good S F s d
  | _, .and s t, d => TSh.Good S F s d.1 ∧ TSh.Good S F t d.2
  | _, .ex s, d => TSh.Good S F s d
  | _, .exb _ _ s, d => TSh.Good S F s d

/-- Every `mem` atom declares a degree at most `D`. -/
def TSh.MemLe : {n : ℕ} → (s : TSh n) → s.Data → ℕ → Prop
  | _, .poly .., _, _ => True
  | _, .mem _ _ _, d, D => d.2 ≤ D
  | _, .neg s, d, D => TSh.MemLe s d D
  | _, .and s t, d, D => TSh.MemLe s d.1 D ∧ TSh.MemLe t d.2 D
  | _, .ex s, d, D => TSh.MemLe s d D
  | _, .exb _ _ s, d, D => TSh.MemLe s d D

/-- An explicit format bound: it depends only on the shape and on `F`. -/
def tFmt (F : ℕ) : {n : ℕ} → TSh n → ℕ
  | _, .poly n _ _ => n
  | _, .mem n m _ => max (F + n) (n + m) + 1 + m + n
  | _, .neg s => tFmt F s + 1
  | _, .and s t => max (tFmt F s) (tFmt F t) + 1
  | _, .ex s => tFmt F s + 1
  | _, .exb _ k s => tFmt F s + k

/-- The number of atoms of a shape. -/
def tAtoms : {n : ℕ} → TSh n → ℕ
  | _, .poly .. => 1
  | _, .mem .. => 1
  | _, .neg s => tAtoms s
  | _, .and s t => tAtoms s + tAtoms t
  | _, .ex s => tAtoms s
  | _, .exb _ _ s => tAtoms s

/-! ## 2. The two structural theorems -/

theorem TSh.realize_mem_Omega (S : SOMin) {n : ℕ} (s : TSh n) :
    ∀ (F : ℕ) (d : s.Data), s.Good S F d →
      s.realize d ∈ S.Ω (tFmt F s) (s.deg d) n := by
  induction s with
  | poly n P hP =>
      intro F d _
      exact Work.WilG0.Omega_mono_F le_rfl (Work.WilG0.Omega_mono_D hP (S.hyp n P))
  | mem n m ι =>
      intro F d hd
      exact Work.WilG0.substSet_mem hd n ι
  | neg s ih =>
      intro F d hd
      exact S.compl (ih F d hd)
  | and s t ihs iht =>
      intro F d hd
      obtain ⟨hd1, hd2⟩ := hd
      have h1 := Work.WilG0.Omega_mono_F (S := S) (F := tFmt F s)
        (F' := max (tFmt F s) (tFmt F t)) (le_max_left _ _) (ihs F d.1 hd1)
      have h2 := Work.WilG0.Omega_mono_F (S := S) (F := tFmt F t)
        (F' := max (tFmt F s) (tFmt F t)) (le_max_right _ _) (iht F d.2 hd2)
      exact Work.WilG0.Omega_inter2 h1 h2
  | ex s ih =>
      intro F d hd
      exact S.proj (ih F d hd)
  | exb n k s ih =>
      intro F d hd
      exact Work.WilG5.projN_mem (S := S) (n := n) k (tFmt F s) (s.deg d) (ih F d hd)

theorem TSh.deg_le {n : ℕ} (s : TSh n) :
    ∀ (d : s.Data) (D : ℕ), s.MemLe d D → s.deg d ≤ tAtoms s * (D + 2 + 8) := by
  induction s with
  | poly n P hP =>
      intro d D _
      simp only [TSh.deg, tAtoms]
      omega
  | mem n m ι =>
      intro d D hd
      simp only [TSh.deg, tAtoms, TSh.MemLe] at hd ⊢
      omega
  | neg s ih =>
      intro d D hd
      exact ih d D hd
  | and s t ihs iht =>
      intro d D hd
      obtain ⟨hd1, hd2⟩ := hd
      have h1 := ihs d.1 D hd1
      have h2 := iht d.2 D hd2
      simp only [TSh.deg, tAtoms]
      rw [Nat.add_mul]
      omega
  | ex s ih =>
      intro d D hd
      exact ih d D hd
  | exb n k s ih =>
      intro d D hd
      exact ih d D hd

/-! ## 3. Shapes carrying their invariants -/

/-- A shape, its data, and the two facts the construction needs downstream. -/
structure PKS (S : SOMin) (F D : ℕ) (n : ℕ) where
  sh : TSh n
  dat : sh.Data
  good : TSh.Good S F sh dat
  mle : TSh.MemLe sh dat D

namespace PKS

variable {S : SOMin} {F D : ℕ} {n : ℕ}

/-- The realised set. -/
def Real (s : PKS S F D n) : Set (Fin n → ℝ) := s.sh.realize s.dat

/-- The declared degree. -/
def Deg (s : PKS S F D n) : ℕ := s.sh.deg s.dat

/-- The format bound. -/
def Fmt (s : PKS S F D n) : ℕ := tFmt F s.sh

/-- The number of atoms. -/
def Atoms (s : PKS S F D n) : ℕ := tAtoms s.sh

/-! ### Constructors -/

/-- A polynomial atom `P = 0` (with declared degree `8`). -/
def poly (P : MvPolynomial (Fin n) ℝ) (h : P.totalDegree ≤ 8) : PKS S F D n :=
  ⟨TSh.poly n P h, PUnit.unit, trivial, trivial⟩

/-- A substitution atom `x ∘ ι ∈ A`. -/
def mem {m : ℕ} (A : Set (Fin m → ℝ)) (hA : A ∈ S.Ω F D m) (ι : Fin m → Fin n) :
    PKS S F D n :=
  ⟨TSh.mem n m ι, (A, D), hA, le_rfl⟩

/-- Negation. -/
def neg (s : PKS S F D n) : PKS S F D n :=
  ⟨TSh.neg s.sh, s.dat, s.good, s.mle⟩

/-- Conjunction. -/
def conj (s t : PKS S F D n) : PKS S F D n :=
  ⟨TSh.and s.sh t.sh, (s.dat, t.dat), ⟨s.good, t.good⟩, ⟨s.mle, t.mle⟩⟩

/-- Existential quantification of the last variable. -/
def exi (s : PKS S F D (n + 1)) : PKS S F D n :=
  ⟨TSh.ex s.sh, s.dat, s.good, s.mle⟩

/-- Existential quantification of the last `k` variables. -/
def exb {k : ℕ} (s : PKS S F D (n + k)) : PKS S F D n :=
  ⟨TSh.exb n k s.sh, s.dat, s.good, s.mle⟩

/-- Implication `s → t` (coded as `¬(s ∧ ¬t)`). -/
def imp (s t : PKS S F D n) : PKS S F D n := neg (conj s (neg t))

/-- Universal quantification of the last `k` variables. -/
def allb {k : ℕ} (s : PKS S F D (n + k)) : PKS S F D n := neg (exb (neg s))

/-! ### Realisation of the connectives -/

@[simp] theorem Real_poly {P : MvPolynomial (Fin n) ℝ} (h : P.totalDegree ≤ 8) :
    (poly P h : PKS S F D n).Real = {x : Fin n → ℝ | MvPolynomial.eval x P = 0} := rfl

@[simp] theorem Real_mem {m : ℕ} (A : Set (Fin m → ℝ)) (hA : A ∈ S.Ω F D m)
    (ι : Fin m → Fin n) : (mem A hA ι : PKS S F D n).Real = {x : Fin n → ℝ | x ∘ ι ∈ A} := rfl

@[simp] theorem Real_neg (s : PKS S F D n) : (neg s).Real = (s.Real)ᶜ := rfl

@[simp] theorem Real_conj (s t : PKS S F D n) : (conj s t).Real = s.Real ∩ t.Real := rfl

@[simp] theorem Real_exi (s : PKS S F D (n + 1)) : (exi s).Real = projLast s.Real := rfl

theorem Real_exb {k : ℕ} (s : PKS S F D (n + k)) :
    (exb s).Real = Work.WilG5.projN k s.Real := rfl

theorem Real_allb {k : ℕ} (s : PKS S F D (n + k)) :
    (allb s).Real = {x : Fin n → ℝ | ∀ y : Fin k → ℝ, Fin.append x y ∈ s.Real} := by
  ext x
  simp only [allb, Real_neg, Real_exb, Work.WilG5.projN, Set.mem_compl_iff, Set.mem_setOf_eq,
    not_exists, not_not]

theorem Real_imp (s t : PKS S F D n) : (imp s t).Real = s.Realᶜ ∪ t.Real := by
  ext x
  simp only [imp, Real_neg, Real_conj, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_union]
  tauto

/-! ### The size bookkeeping -/

@[simp] theorem Deg_neg (s : PKS S F D n) : (neg s).Deg = s.Deg := rfl

@[simp] theorem Deg_conj (s t : PKS S F D n) : (conj s t).Deg = s.Deg + t.Deg := rfl

@[simp] theorem Deg_exi (s : PKS S F D (n + 1)) : (exi s).Deg = s.Deg := rfl

@[simp] theorem Deg_exb {k : ℕ} (s : PKS S F D (n + k)) : (exb s).Deg = s.Deg := rfl

@[simp] theorem Fmt_neg (s : PKS S F D n) : (neg s).Fmt = s.Fmt + 1 := rfl

@[simp] theorem Fmt_conj (s t : PKS S F D n) : (conj s t).Fmt = max s.Fmt t.Fmt + 1 := rfl

@[simp] theorem Fmt_exi (s : PKS S F D (n + 1)) : (exi s).Fmt = s.Fmt + 1 := rfl

@[simp] theorem Fmt_exb {k : ℕ} (s : PKS S F D (n + k)) : (exb s).Fmt = s.Fmt + k := rfl

@[simp] theorem Atoms_neg (s : PKS S F D n) : (neg s).Atoms = s.Atoms := rfl

@[simp] theorem Atoms_conj (s t : PKS S F D n) : (conj s t).Atoms = s.Atoms + t.Atoms := rfl

@[simp] theorem Atoms_exi (s : PKS S F D (n + 1)) : (exi s).Atoms = s.Atoms := rfl

@[simp] theorem Atoms_exb {k : ℕ} (s : PKS S F D (n + k)) : (exb s).Atoms = s.Atoms := rfl

/-! ### The two conclusions -/

theorem Real_mem_Omega (s : PKS S F D n) : s.Real ∈ S.Ω s.Fmt s.Deg n :=
  TSh.realize_mem_Omega S s.sh F s.dat s.good

theorem Deg_le (s : PKS S F D n) : s.Deg ≤ s.Atoms * (D + 2 + 8) :=
  TSh.deg_le s.sh s.dat D s.mle

end PKS

/-! ## 4. The atoms -/

/-- `∑ j, (X (a j) - X (b j))²`. -/
def sqSum {M K : ℕ} (a b : Fin M → Fin K) : MvPolynomial (Fin K) ℝ :=
  ∑ j : Fin M, (MvPolynomial.X (a j) - MvPolynomial.X (b j)) ^ 2

theorem sqSum_td {M K : ℕ} (a b : Fin M → Fin K) : (sqSum a b).totalDegree ≤ 2 := by
  refine MvPolynomial.totalDegree_finsetSum_le fun j _ => ?_
  refine (MvPolynomial.totalDegree_pow _ 2).trans ?_
  have h2 : (MvPolynomial.X (a j) - MvPolynomial.X (b j) : MvPolynomial (Fin K) ℝ).totalDegree
      ≤ 1 := by
    refine (MvPolynomial.totalDegree_sub _ _).trans ?_
    rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X]
    omega
  omega

/-- The lift of a polynomial along `Fin.castSucc`. -/
def liftP {K : ℕ} (A : MvPolynomial (Fin K) ℝ) : MvPolynomial (Fin (K + 1)) ℝ :=
  MvPolynomial.rename Fin.castSucc A

theorem liftP_td {K : ℕ} {A : MvPolynomial (Fin K) ℝ} (hA : A.totalDegree ≤ 4) :
    (liftP A).totalDegree ≤ 4 :=
  (MvPolynomial.totalDegree_rename_le _ _).trans hA

/-- `X i ^ 2` has degree at most `4`. -/
theorem td_X_sq {K : ℕ} (i : Fin K) :
    ((MvPolynomial.X i) ^ 2 : MvPolynomial (Fin K) ℝ).totalDegree ≤ 4 := by
  rw [MvPolynomial.totalDegree_X_pow]
  omega

/-- **The strict-inequality atom** `A < B` (for `A`, `B` of total degree `≤ 4`), realised by
`∃ t, t² = B - A ∧ t ≠ 0`. -/
def ltS (S : SOMin) (F D : ℕ) {K : ℕ} (A B : MvPolynomial (Fin K) ℝ)
    (hA : A.totalDegree ≤ 4) (hB : B.totalDegree ≤ 4) : PKS S F D K :=
  PKS.exi (PKS.conj
    (PKS.poly (MvPolynomial.X (Fin.last K) ^ 2 - (liftP B - liftP A)) (by
      have h1 : (liftP B - liftP A : MvPolynomial (Fin (K + 1)) ℝ).totalDegree ≤ 4 :=
        (MvPolynomial.totalDegree_sub _ _).trans (max_le (liftP_td hB) (liftP_td hA))
      have h2 : ((MvPolynomial.X (Fin.last K)) ^ 2 : MvPolynomial (Fin (K + 1)) ℝ).totalDegree
          ≤ 4 := td_X_sq _
      exact (MvPolynomial.totalDegree_sub _ _).trans ((max_le h2 h1).trans (by norm_num))))
    (PKS.neg (PKS.poly (MvPolynomial.X (Fin.last K)) (by
      rw [MvPolynomial.totalDegree_X]; norm_num))))

theorem lt_of_sq_sub {a b t : ℝ} (h : t ^ 2 - (b - a) = 0) (ht : t ≠ 0) : a < b := by
  have h1 : t ^ 2 = b - a := by linarith
  have hpos : 0 < t ^ 2 := sq_pos_of_ne_zero ht
  linarith

theorem exists_sq_sub_of_lt {a b : ℝ} (h : a < b) :
    ∃ t : ℝ, t ^ 2 - (b - a) = 0 ∧ t ≠ 0 := by
  refine ⟨Real.sqrt (b - a), ?_, ?_⟩
  · rw [Real.sq_sqrt (by linarith)]; ring
  · exact ne_of_gt (Real.sqrt_pos.mpr (by linarith))

theorem ltS_Real {S : SOMin} {F D K : ℕ} (A B : MvPolynomial (Fin K) ℝ)
    (hA : A.totalDegree ≤ 4) (hB : B.totalDegree ≤ 4) :
    (ltS S F D A B hA hB).Real =
      {z : Fin K → ℝ | MvPolynomial.eval z A < MvPolynomial.eval z B} := by
  have hZ : ∀ (z : Fin K → ℝ) (t : ℝ),
      MvPolynomial.eval (Fin.snoc z t)
        (MvPolynomial.X (Fin.last K) : MvPolynomial (Fin (K+1)) ℝ) = t := by
    intro z t
    rw [MvPolynomial.eval_X, Fin.snoc_last]
  have hL : ∀ (z : Fin K → ℝ) (t : ℝ) (C : MvPolynomial (Fin K) ℝ),
      MvPolynomial.eval (Fin.snoc z t) (liftP C) = MvPolynomial.eval z C := by
    intro z t C
    rw [liftP, MvPolynomial.eval_rename]
    have hcomp : (Fin.snoc z t) ∘ Fin.castSucc = z := by
      funext i
      exact Fin.snoc_castSucc (α := fun _ => ℝ) t z i
    rw [hcomp]
  have key : (ltS S F D A B hA hB).Real =
      {z : Fin K → ℝ |
        ∃ t : ℝ, t ^ 2 - (MvPolynomial.eval z B - MvPolynomial.eval z A) = 0 ∧ t ≠ 0} := by
    ext z
    simp only [ltS, PKS.Real_exi, PKS.Real_conj, PKS.Real_neg, PKS.Real_poly, projLast,
      Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff]
    constructor
    · rintro ⟨t, h1, h2⟩
      simp only [MvPolynomial.eval_sub, MvPolynomial.eval_pow, hZ z t, hL z t] at h1 h2
      exact ⟨t, h1, h2⟩
    · rintro ⟨t, h1, h2⟩
      refine ⟨t, ?_, ?_⟩
      · simp only [MvPolynomial.eval_sub, MvPolynomial.eval_pow, hZ z t, hL z t]
        exact h1
      · simp only [hZ z t]
        exact h2
  rw [key]
  ext z
  constructor
  · rintro ⟨t, h1, h2⟩
    exact lt_of_sq_sub h1 h2
  · intro h
    exact exists_sq_sub_of_lt h

/-- **The positivity atom** `0 < z i`. -/
def posS (S : SOMin) (F D : ℕ) {K : ℕ} (i : Fin K) : PKS S F D K :=
  ltS S F D 0 (MvPolynomial.X i) (by simp) (by rw [MvPolynomial.totalDegree_X]; omega)

theorem posS_Real {S : SOMin} {F D K : ℕ} (i : Fin K) :
    (posS S F D i).Real = {z : Fin K → ℝ | 0 < z i} := by
  rw [posS, ltS_Real]
  ext z
  simp

/-- **The `ℓ²`-ball atom** `∑ j, (z (a j) - z (b j))² < (z d)²`. -/
def ballS (S : SOMin) (F D : ℕ) {M K : ℕ} (a b : Fin M → Fin K) (d : Fin K) :
    PKS S F D K :=
  ltS S F D (sqSum a b) ((MvPolynomial.X d) ^ 2) ((sqSum_td a b).trans (by omega)) (td_X_sq d)

theorem ballS_Real {S : SOMin} {F D M K : ℕ} (a b : Fin M → Fin K) (d : Fin K) :
    (ballS S F D a b d).Real =
      {z : Fin K → ℝ | (∑ j : Fin M, (z (a j) - z (b j)) ^ 2) < (z d) ^ 2} := by
  rw [ballS, ltS_Real]
  ext z
  have hev : MvPolynomial.eval z (sqSum a b) =
      ∑ j : Fin M, (z (a j) - z (b j)) ^ 2 := by
    simp only [sqSum, MvPolynomial.eval_sum, MvPolynomial.eval_pow, MvPolynomial.eval_sub,
      MvPolynomial.eval_X]
  simp only [Set.mem_setOf_eq, hev, MvPolynomial.eval_pow, MvPolynomial.eval_X]

/-- **The inequality atom** `A ≤ B` (the negation of `B < A`). -/
def leS (S : SOMin) (F D : ℕ) {K : ℕ} (A B : MvPolynomial (Fin K) ℝ)
    (hA : A.totalDegree ≤ 4) (hB : B.totalDegree ≤ 4) : PKS S F D K :=
  PKS.neg (ltS S F D B A hB hA)

theorem leS_Real {S : SOMin} {F D K : ℕ} (A B : MvPolynomial (Fin K) ℝ)
    (hA : A.totalDegree ≤ 4) (hB : B.totalDegree ≤ 4) :
    (leS S F D A B hA hB).Real =
      {z : Fin K → ℝ | MvPolynomial.eval z A ≤ MvPolynomial.eval z B} := by
  rw [leS, PKS.Real_neg, ltS_Real]
  ext z
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]

end Work.WilG4c
