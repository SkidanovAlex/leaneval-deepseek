/-
  Area E7 / WilE7: the *strict* (open) cylindrical lift of a semi-Pfaffian set.

  Given a semi-Pfaffian set `X` in `ℝ^{n+m}`, `bandExt X` is the semi-Pfaffian set in
  `ℝ^{n+1+m}` obtained by extending the data of `X` along the coordinate insertion
  `Work.WilE8.skipInj n m` (which inserts a new coordinate at position `n`, i.e. as the last of
  the first `n+1` coordinates) and cutting by the two *strict* inequalities `-1 < x_new < 1`.

  This is the strict companion of `Work.WilE8.SemiPf.extend (skipInj n m) X`, whose point set is
  the closed cylinder: the new coordinate of the latter is only constrained by the closed cube.
  The point set of `bandExt X` is `bandRel X.set ∩ cubeC (n+1+m)`, i.e. the open band over
  `X.set` cut by the cube.

  The extra inequalities are added with `Work.WilE7.SemiPf.addConds`, which first replaces the DNF
  list by `redBasics`.  That is what keeps the degree bound honest: `redBasics X` has at most
  `max 1 X.deg` branches (`redBasics_length_le`), so `bandExt` never multiplies the degree by the
  (a priori unbounded) number of branches of `X`.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.Defs
import Submission.Work.WilE7.ProdDefs
import Submission.Work.WilE7.BandAux.BandDefs
import Submission.Work.WilE8.Basic
import Submission.Work.WilE8.Extend
import Submission.Work.WilE8.Extend.semipf_set_extend
import Submission.Work.WilE8.Extend.semipf_deg_extend
import Submission.Work.WilE8.Star.LiftDef
import Submission.Work.WilE8.Star.projFirst_cyl

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7

open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-- The coordinate inserted by `Work.WilE8.skipInj n m`, i.e. the last of the first `n+1`
coordinates of `Fin (n+1+m)`. -/
def newIdx (n m : ℕ) : Fin (n + 1 + m) := Fin.castAdd m (Fin.last n)

@[simp] theorem newIdx_val (n m : ℕ) : ((newIdx n m : Fin (n + 1 + m)) : ℕ) = n :=
  Fin.val_castAdd ..

/-- The open cylinder over `K ⊆ ℝ^{n+m}` in `ℝ^{n+1+m}`: the new coordinate (inserted at
position `n`, the last of the first `n+1`) is required to lie in the open interval `(-1,1)`. -/
def bandRel {n m : ℕ} (K : Set (Fin (n + m) → ℝ)) : Set (Fin (n + 1 + m) → ℝ) :=
  {z | (fun i => z (Work.WilE8.skipInj n m i)) ∈ K ∧ -1 < z (newIdx n m) ∧ z (newIdx n m) < 1}

theorem mem_bandRel {n m : ℕ} {K : Set (Fin (n + m) → ℝ)} {z : Fin (n + 1 + m) → ℝ} :
    z ∈ bandRel K ↔ (fun i => z (Work.WilE8.skipInj n m i)) ∈ K ∧
      -1 < z (newIdx n m) ∧ z (newIdx n m) < 1 := Iff.rfl

/-! ## The two band atoms -/

/-- The atom `-1 < x_new`, i.e. `x_new + 1`. -/
def bandPos1 (n m r : ℕ) : EAPoly (n + 1 + m) r :=
  MvPolynomial.X (Sum.inl (newIdx n m)) + MvPolynomial.C 1

/-- The atom `x_new < 1`, i.e. `1 - x_new`. -/
def bandPos2 (n m r : ℕ) : EAPoly (n + 1 + m) r :=
  MvPolynomial.C 1 - MvPolynomial.X (Sum.inl (newIdx n m))

theorem eaEval_bandPos1 {n m r : ℕ} (c : EAChain (n + 1 + m) r) (z : Fin (n + 1 + m) → ℝ) :
    eaEval c (bandPos1 n m r) z = z (newIdx n m) + 1 := by
  rw [bandPos1, eaEval, MvPolynomial.eval_add, MvPolynomial.eval_X, MvPolynomial.eval_C,
    Sum.elim_inl]

theorem eaEval_bandPos2 {n m r : ℕ} (c : EAChain (n + 1 + m) r) (z : Fin (n + 1 + m) → ℝ) :
    eaEval c (bandPos2 n m r) z = 1 - z (newIdx n m) := by
  rw [bandPos2, eaEval, MvPolynomial.eval_sub, MvPolynomial.eval_X, MvPolynomial.eval_C,
    Sum.elim_inl]

theorem atomDeg_bandPos1_le {n m r : ℕ} : atomDeg (bandPos1 n m r) ≤ 2 := by
  have h := MvPolynomial.totalDegree_add
    (MvPolynomial.X (Sum.inl (newIdx n m)) : EAPoly (n + 1 + m) r) (MvPolynomial.C 1)
  rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C] at h
  have h1 : (MvPolynomial.X (Sum.inl (newIdx n m)) + MvPolynomial.C 1 :
      EAPoly (n + 1 + m) r).totalDegree ≤ 1 := by
    refine h.trans ?_
    rw [Nat.max_le]
    exact ⟨le_refl 1, Nat.zero_le 1⟩
  simp only [bandPos1, atomDeg]
  omega

theorem atomDeg_bandPos2_le {n m r : ℕ} : atomDeg (bandPos2 n m r) ≤ 2 := by
  have h := MvPolynomial.totalDegree_sub
    (MvPolynomial.C 1) (MvPolynomial.X (Sum.inl (newIdx n m)) : EAPoly (n + 1 + m) r)
  rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C] at h
  have h1 : (MvPolynomial.C 1 - MvPolynomial.X (Sum.inl (newIdx n m)) :
      EAPoly (n + 1 + m) r).totalDegree ≤ 1 := by
    refine h.trans ?_
    rw [Nat.max_le]
    exact ⟨Nat.zero_le 1, le_refl 1⟩
  simp only [bandPos2, atomDeg]
  omega

/-! ## The strict band lift -/

/-- The strict band lift of a semi-Pfaffian set: extend along `skipInj n m` and cut by the two
strict inequalities `-1 < x_new`, `x_new < 1`. -/
def bandExt {n m : ℕ} (X : SemiPf (n + m)) : SemiPf (n + 1 + m) :=
  SemiPf.addConds (Work.WilE8.SemiPf.extend (Work.WilE8.skipInj n m) X) []
    [bandPos1 n m (Work.WilE8.SemiPf.extend (Work.WilE8.skipInj n m) X).r,
     bandPos2 n m (Work.WilE8.SemiPf.extend (Work.WilE8.skipInj n m) X).r]

theorem bandExt_set {n m : ℕ} (X : SemiPf (n + m)) :
    (bandExt X).set = bandRel X.set ∩ cubeC (n + 1 + m) := by
  ext z
  constructor
  · intro hz
    rw [bandExt, SemiPf.addConds_set] at hz
    obtain ⟨⟨hzY, -⟩, hP⟩ := hz
    rw [Work.WilE8.Extend.semipf_set_extend (Work.WilE8.Star.skipInj_injective n m) X] at hzY
    obtain ⟨hzcube, hzX⟩ := hzY
    refine ⟨⟨hzX, ?_, ?_⟩, hzcube⟩
    · have h1 := hP (bandPos1 n m (Work.WilE8.SemiPf.extend
          (Work.WilE8.skipInj n m) X).r) (by simp)
      rw [eaEval_bandPos1] at h1
      linarith
    · have h2 := hP (bandPos2 n m (Work.WilE8.SemiPf.extend
          (Work.WilE8.skipInj n m) X).r) (by simp)
      rw [eaEval_bandPos2] at h2
      linarith
  · intro hz
    obtain ⟨⟨hzX, h1, h2⟩, hzcube⟩ := hz
    rw [bandExt, SemiPf.addConds_set]
    rw [Work.WilE8.Extend.semipf_set_extend (Work.WilE8.Star.skipInj_injective n m) X]
    refine ⟨⟨⟨hzcube, hzX⟩, fun f hf => by simp at hf⟩, fun g hg => ?_⟩
    rcases List.mem_cons.mp hg with rfl | hg'
    · rw [eaEval_bandPos1]; linarith
    · rw [List.mem_singleton.mp hg', eaEval_bandPos2]; linarith

theorem bandExt_mem {n m : ℕ} {X : SemiPf (n + m)} {z : Fin (n + 1 + m) → ℝ} :
    z ∈ (bandExt X).set ↔ (fun i => z (Work.WilE8.skipInj n m i)) ∈ X.set ∧
      -1 < z (newIdx n m) ∧ z (newIdx n m) < 1 ∧ z ∈ cubeC (n + 1 + m) := by
  rw [bandExt_set, Set.mem_inter_iff, mem_bandRel]
  tauto

theorem bandExt_fmt {n m : ℕ} (X : SemiPf (n + m)) : (bandExt X).fmt = X.fmt + 1 := by
  rw [bandExt, SemiPf.addConds_fmt]
  show (n + 1 + m) + X.r = (n + m) + X.r + 1
  omega

theorem bandExt_atoms_le {n m : ℕ} (X : SemiPf (n + m)) :
    ((List.map atomDeg ([] : List (EAPoly (n + 1 + m)
        (Work.WilE8.SemiPf.extend (Work.WilE8.skipInj n m) X).r))).sum +
      (List.map atomDeg
        [bandPos1 n m (Work.WilE8.SemiPf.extend (Work.WilE8.skipInj n m) X).r,
         bandPos2 n m (Work.WilE8.SemiPf.extend (Work.WilE8.skipInj n m) X).r]).sum) ≤ 4 := by
  simp only [List.map_nil, List.sum_nil, zero_add, List.map_cons, List.sum_cons,
    List.map_nil, List.sum_nil, add_zero]
  have h1 := atomDeg_bandPos1_le (n := n) (m := m)
    (r := (Work.WilE8.SemiPf.extend (Work.WilE8.skipInj n m) X).r)
  have h2 := atomDeg_bandPos2_le (n := n) (m := m)
    (r := (Work.WilE8.SemiPf.extend (Work.WilE8.skipInj n m) X).r)
  omega

theorem bandExt_deg_le {n m : ℕ} (X : SemiPf (n + m)) : (bandExt X).deg ≤ 4 + 5 * X.deg := by
  have h := SemiPf.addConds_deg_le (Work.WilE8.SemiPf.extend (Work.WilE8.skipInj n m) X) []
    [bandPos1 n m (Work.WilE8.SemiPf.extend (Work.WilE8.skipInj n m) X).r,
     bandPos2 n m (Work.WilE8.SemiPf.extend (Work.WilE8.skipInj n m) X).r]
  rw [bandExt]
  have hYdeg : (Work.WilE8.SemiPf.extend (Work.WilE8.skipInj n m) X).deg = X.deg :=
    Work.WilE8.Extend.semipf_deg_extend (Work.WilE8.Star.skipInj_injective n m) X
  have hS := bandExt_atoms_le X
  have hmax : max 1 (Work.WilE8.SemiPf.extend (Work.WilE8.skipInj n m) X).deg
      ≤ 1 + X.deg := by
    rw [hYdeg]
    exact max_le (by omega) (by omega)
  have hmul : max 1 (Work.WilE8.SemiPf.extend (Work.WilE8.skipInj n m) X).deg *
      ((List.map atomDeg ([] : List (EAPoly (n + 1 + m)
        (Work.WilE8.SemiPf.extend (Work.WilE8.skipInj n m) X).r))).sum +
        (List.map atomDeg
          [bandPos1 n m (Work.WilE8.SemiPf.extend (Work.WilE8.skipInj n m) X).r,
           bandPos2 n m (Work.WilE8.SemiPf.extend (Work.WilE8.skipInj n m) X).r]).sum)
      ≤ (1 + X.deg) * 4 := Nat.mul_le_mul hmax hS
  have h1 : (bandExt X).deg ≤ (Work.WilE8.SemiPf.extend (Work.WilE8.skipInj n m) X).deg +
      max 1 (Work.WilE8.SemiPf.extend (Work.WilE8.skipInj n m) X).deg *
      ((List.map atomDeg ([] : List (EAPoly (n + 1 + m)
        (Work.WilE8.SemiPf.extend (Work.WilE8.skipInj n m) X).r))).sum +
        (List.map atomDeg
          [bandPos1 n m (Work.WilE8.SemiPf.extend (Work.WilE8.skipInj n m) X).r,
           bandPos2 n m (Work.WilE8.SemiPf.extend (Work.WilE8.skipInj n m) X).r]).sum) := h
  rw [hYdeg] at h1
  omega

end Work.WilE7
