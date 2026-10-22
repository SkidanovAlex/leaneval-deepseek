/-
AREA RESOL — the vocabulary of the telescopic description of a complex as a retract.

This file contains *only* the definitions (and the elementary component lemmas on which they
depend) used to exhibit a bounded-above complex as a retract of the telescope of its
truncations; the proofs of the telescope identities live in `RESOL/B5Tower.lean`.

Given a complex `K`, put `U m := trunc (L m) K` where `trunc` is the brutal truncation
(`RESOL/B5Setup.lean`) and `L m = -m`, and let `Uinc m : U m ⟶ U (m+1)` be the canonical
inclusion (`truncIncl`).  With

* `A K := ∐_m U m`, `s K := telescopeShift (U K) (Uinc K)` (the "shift" of the telescope),
* `sc K := 𝟙 (A K) - s K`, `T K := cone (sc K) = telescope (U K) (Uinc K)`,
* `σ K : A K ⟶ K` the fold map (the sum of the inclusions `U m ⊆ K`),
* `u m n : K.X n ⟶ (A K).X n` the inclusion of `K.X n` as the `m`-th summand,
* `Xsum K n` a telescoping sum of such inclusions and `α K n`, `β K n` the two components of
  the coherent section `ψ K : K ⟶ T K` (built in `RESOL/B5Tower.lean`).
-/
import Mathlib
import Submission.Work.RESOL.Basic
import Submission.Work.RESOL.B5Setup
import Submission.Work.RESOL.B5Telescope
import Submission.Work.RESOL.solidCofibrant_trunc

open CategoryTheory Limits LightCondensed
open HomologicalComplex

noncomputable section

namespace Work.RESOL

/-! ## The canonical inclusion `trunc j K ⟶ K` -/

/-- The canonical inclusion `trunc j K ⟶ K` (the identity in degrees `≥ j`, zero below). -/
def incl (K : Cpx) (j : ℤ) : trunc j K ⟶ K where
  f n := if h : j ≤ n then eqToHom (trunc_X_of_le K j h) else 0
  comm' i n hin := by
    rw [ComplexShape.up_Rel] at hin
    obtain rfl : n = i + 1 := by omega
    by_cases h : j ≤ i
    · have h' : j ≤ i + 1 := by omega
      rw [dif_pos h, dif_pos h', trunc_d_eq K rfl h h']
      simp only [Category.assoc, eqToHom_comp_eqToHom_self, Category.comp_id]
    · rw [dif_neg h, zero_comp, trunc_d_eq_zero K rfl h, zero_comp]

lemma incl_f_of_le (K : Cpx) {j n : ℤ} (h : j ≤ n) :
    (incl K j).f n = eqToHom (trunc_X_of_le K j h) := by
  simp only [incl, dif_pos h]

lemma incl_f_of_not_le (K : Cpx) {j n : ℤ} (h : ¬ j ≤ n) : (incl K j).f n = 0 := by
  simp only [incl, dif_neg h]

/-- The relation of the cochain complex shape `up ℤ`, with an explicit canonical proof (so that
all occurrences of this proof in a term are syntactically identical). -/
lemma rel_up (i : ℤ) : (ComplexShape.up ℤ).Rel i (i + 1) := rfl

/-- `eqToHom` does not depend on the proof of the equation. -/
lemma eqToHom_proof_irrel {C : Type*} [Category C] {X Y : C} (p q : X = Y) :
    eqToHom p = eqToHom q := by
  rw [Subsingleton.elim p q]

/-! ## The tower of truncations -/

/-- The truncation levels of the tower: `L m = -m`.  Defined by recursion so that
`L (m+1) = L m - 1` holds definitionally. -/
def L : ℕ → ℤ
  | 0 => 0
  | (m + 1) => L m - 1

lemma L_zero : L 0 = 0 := rfl

lemma L_succ (m : ℕ) : L (m + 1) = L m - 1 := rfl

lemma L_eq (m : ℕ) : L m = -(m : ℤ) := by
  induction m with
  | zero => simp [L]
  | succ m ih => rw [L_succ, ih]; push_cast; ring

lemma L_anti : Antitone L := by
  intro a b hab
  simp only [L_eq]
  omega

/-- The `m`-th truncation of the tower: `U m = σ^{≥ -m}K`. -/
abbrev U (K : Cpx) (m : ℕ) : Cpx := trunc (L m) K

/-- The canonical proof of `L (m+1) ≤ n` from `L m ≤ n`. -/
lemma L_succ_le {m : ℕ} {n : ℤ} (h : L m ≤ n) : L (m + 1) ≤ n := by
  rw [L_succ]; omega

/-- The canonical proof of `L m ≤ n+1` from `L m ≤ n`. -/
lemma L_le_succ {m : ℕ} {n : ℤ} (h : L m ≤ n) : L m ≤ n + 1 := by omega

/-- The inclusion `U m ⟶ U (m+1)` of the tower.  It is defined with *canonical* proofs of the
statements `L m ≤ n` and `L (m+1) ≤ n` so that all its components are syntactically determined
by these lemmas (this avoids any need for `eqToHom` to be proof-irrelevant in the middle of a
composition). -/
abbrev Uinc (K : Cpx) (m : ℕ) : U K m ⟶ U K (m + 1) where
  f n := if h : L m ≤ n then
      eqToHom (trunc_X_of_le K (L m) h) ≫
        eqToHom (trunc_X_of_le K (L (m + 1)) (L_succ_le h)).symm
    else 0
  comm' i n hin := by
    rw [ComplexShape.up_Rel] at hin
    obtain rfl : n = i + 1 := by omega
    by_cases h : L m ≤ i
    · have h2 : L (m + 1) ≤ i := L_succ_le h
      have h3 : L m ≤ i + 1 := L_le_succ h
      rw [dif_pos h, dif_pos h3, trunc_d_eq K rfl h2 (L_succ_le h3), trunc_d_eq K rfl h h3]
      simp only [Category.assoc, eqToHom_comp_eqToHom_self_sandwich]
    · rw [dif_neg h, zero_comp, trunc_d_eq_zero K rfl h, zero_comp]

lemma Uinc_f_of_le (K : Cpx) {m : ℕ} {n : ℤ} (h : L m ≤ n) :
    (Uinc K m).f n = eqToHom (trunc_X_of_le K (L m) h) ≫
      eqToHom (trunc_X_of_le K (L (m + 1)) (L_succ_le h)).symm := by
  simp only [Uinc, dif_pos h]

lemma Uinc_f_of_not_le (K : Cpx) {m : ℕ} {n : ℤ} (h : ¬ L m ≤ n) :
    (Uinc K m).f n = 0 := by
  simp only [Uinc, dif_neg h]

/-- The coproduct of the tower. -/
abbrev A (K : Cpx) [HasCoproduct (U K)] : Cpx := ∐ (U K)

/-- The "shift" morphism of the telescope: the summand `U m` is mapped into the summand
`U (m+1)` by the inclusion of the tower. -/
abbrev s (K : Cpx) [HasCoproduct (U K)] : A K ⟶ A K := telescopeShift (U K) (Uinc K)

/-- The fold map: the sum of the inclusions `U m ⊆ K`. -/
abbrev σ (K : Cpx) [HasCoproduct (U K)] : A K ⟶ K := Sigma.desc (fun m => incl K (L m))

/-- The differential `1 - s` of the telescope, as a morphism of complexes. -/
abbrev sc (K : Cpx) [HasCoproduct (U K)] : A K ⟶ A K := 𝟙 (A K) - s K

/-- The telescope of the tower. -/
abbrev T (K : Cpx) [HasCoproduct (U K)] : Cpx := homotopyCofiber (sc K)

/-! ## The index bound `M` -/

/-- The smallest level whose truncation sees degree `n`: `M n = max 0 (-n)`. -/
def M (n : ℤ) : ℕ := (-n).toNat

lemma L_M (n : ℤ) : L (M n) ≤ n := by
  rw [L_eq, M]
  have h : (-n : ℤ) ≤ (((-n).toNat : ℕ) : ℤ) := Int.self_le_toNat (-n)
  omega

lemma M_succ_le (n : ℤ) : M (n + 1) ≤ M n :=
  Int.toNat_le_toNat (by omega)

/-- The terms of the telescoping sum at level `n+1` are visible from degree `n+1`. -/
lemma L_add_M (n : ℤ) (k : ℕ) : L (M (n + 1) + k) ≤ n + 1 :=
  le_trans (L_anti (Nat.le_add_right _ _)) (L_M (n + 1))

/-! ## The coherent section `ψ` -/

/-- The inclusion of `K.X n` into `(A K).X n` as the `m`-th summand (zero if `m` is too small
for the truncation `U m` to see degree `n`). -/
abbrev u (K : Cpx) [HasCoproduct (U K)] (m : ℕ) (n : ℤ) : K.X n ⟶ (A K).X n :=
  dite (L m ≤ n)
    (fun h => eqToHom (trunc_X_of_le K (L m) h).symm ≫ (Sigma.ι (U K) m).f n)
    (fun _ => 0)

lemma u_of_le (K : Cpx) [HasCoproduct (U K)] {m : ℕ} {n : ℤ} (h : L m ≤ n) :
    u K m n = eqToHom (trunc_X_of_le K (L m) h).symm ≫ (Sigma.ι (U K) m).f n :=
  dite_eq_left h

lemma u_of_not_le (K : Cpx) [HasCoproduct (U K)] {m : ℕ} {n : ℤ} (h : ¬ L m ≤ n) :
    u K m n = 0 :=
  dite_eq_right h

/-- The telescoping sum of inclusions appearing in the first component of `ψ`. -/
abbrev Ysum (K : Cpx) [HasCoproduct (U K)] (n m : ℤ) : K.X m ⟶ (A K).X m :=
  ∑ k ∈ Finset.range (M n - M (n + 1)), u K (M (n + 1) + k) m

/-- The telescoping sum in degree `n+1`. -/
abbrev Xsum (K : Cpx) [HasCoproduct (U K)] (n : ℤ) : K.X (n + 1) ⟶ (A K).X (n + 1) :=
  Ysum K n (n + 1)

/-- The first component of `ψ`: `d_K` followed by the telescoping sum. -/
abbrev α (K : Cpx) [HasCoproduct (U K)] (n : ℤ) : K.X n ⟶ (A K).X (n + 1) :=
  K.d n (n + 1) ≫ Xsum K n

/-- The second component of `ψ`: the inclusion of degree `n` into the level-`M n` summand. -/
abbrev β (K : Cpx) [HasCoproduct (U K)] (n : ℤ) : K.X n ⟶ (A K).X n := u K (M n) n

/-- The "coherent section" `K ⟶ T K` of the fold map, as a family of morphisms. -/
abbrev ψf (K : Cpx) [HasCoproduct (U K)] (n : ℤ) : K.X n ⟶ (T K).X n :=
  α K n ≫ homotopyCofiber.inlX (sc K) (n + 1) n (rel_up n) +
    β K n ≫ homotopyCofiber.inrX (sc K) n

end Work.RESOL
