import Mathlib
import Submission.Work.ANALYTIC.RealCond

/-!
# Vocabulary for the parametrised null sequence of REFS/03 §3

This file fixes the objects and maps used by `Work.ANALYTIC.exists_realNullSeq`.

* `Point = ∗` is the one point light profinite set;
* `lam r n = r * (1/2)^(Nat.log2 (n+1))` is the null sequence of REFS/03 §3, and `lamC r` is its
  extension to `ℕ∪{∞}` by `0` at `∞` (a continuous function);
* `ptZero`, `ptOne : ∗ ⟶ ℕ∪{∞}` are the points `0` and `1`;
* `phiA`, `phiB : ℕ∪{∞} ⟶ ℕ∪{∞}` are the continuous maps `n ↦ 2n+1` and `n ↦ 2n+2` (fixing `∞`).

The identities `ptZero ≫ shift = ptOne`, `ptZero ≫ phiA = ptOne`, `phiA ≫ shift = phiB` and
`phiB ≫ shift = shift ≫ phiA` are recorded here; they are the "bookkeeping" that turns the
null-sequence identities on generators into identities of morphisms.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed OnePoint
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

namespace Work.ANALYTIC

/-- The point, as a light profinite set. -/
abbrev NSPoint : LightProfinite.{0} := LightProfinite.of PUnit.{1}

/-! ## The null sequence `n ↦ r * (1/2)^(log2 (n+1))` -/

/-- The null sequence of REFS/03 §3 (parametrised by its value `r` at `e₀`). -/
def lam (r : ℝ) (n : ℕ) : ℝ := r * (1 / 2) ^ (Nat.log2 (n + 1))

theorem nat_log2_tendsto_atTop : Filter.Tendsto (fun n : ℕ => Nat.log2 (n + 1)) Filter.atTop
    Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  exact ⟨2 ^ b, fun n hn => by rw [Nat.le_log2 (by omega)]; omega⟩

theorem tendsto_lam (r : ℝ) : Filter.Tendsto (fun n : ℕ => lam r n) Filter.atTop (nhds 0) := by
  have h2 : Filter.Tendsto (fun k : ℕ => r * (1 / 2) ^ k) Filter.atTop (nhds 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) < 1 by norm_num)).const_mul r
    simpa using h
  exact h2.comp nat_log2_tendsto_atTop

/-- The null sequence `lam r`, extended by `0` at `∞`: a continuous function `ℕ∪{∞} → ℝ`. -/
def lamC (r : ℝ) : C(ℕ∪{∞}, ℝ) :=
  ⟨fun x => x.elim 0 (lam r),
    (OnePoint.continuous_iff_from_nat fun x : OnePoint ℕ => x.elim 0 (lam r)).mpr
      (by simpa using tendsto_lam r)⟩

@[simp]
theorem lamC_infty (r : ℝ) : lamC r ∞ = 0 := by
  simp [lamC]

@[simp]
theorem lamC_some (r : ℝ) (n : ℕ) : lamC r (OnePoint.some n) = lam r n := by
  simp [lamC]

theorem lamC_zero (r : ℝ) : lamC r (OnePoint.some 0) = r := by
  simp [lamC, lam]

/-! ## The points `0` and `1` of `ℕ∪{∞}` -/

/-- The point `0 : ℕ∪{∞}`, as a morphism from the one point light profinite set. -/
def ptZero : NSPoint ⟶ ℕ∪{∞} :=
  ConcreteCategory.ofHom ⟨fun _ => OnePoint.some 0, continuous_const⟩

/-- The point `1 : ℕ∪{∞}`, as a morphism from the one point light profinite set. -/
def ptOne : NSPoint ⟶ ℕ∪{∞} :=
  ConcreteCategory.ofHom ⟨fun _ => OnePoint.some 1, continuous_const⟩

theorem ptZero_apply (x : ↥(NSPoint).toTop) : ptZero x = OnePoint.some 0 := rfl

theorem ptOne_apply (x : ↥(NSPoint).toTop) : ptOne x = OnePoint.some 1 := rfl

/-! ## The maps `n ↦ 2n+1` and `n ↦ 2n+2` -/

theorem continuous_map_nat (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop) :
    Continuous (fun x : OnePoint ℕ => OnePoint.map f x) := by
  rw [OnePoint.continuous_iff_from_nat]
  have hsome : Filter.Tendsto (fun n : ℕ => (OnePoint.some n : OnePoint ℕ)) Filter.atTop
      (nhds ∞) :=
    (OnePoint.continuous_iff_from_nat (id : OnePoint ℕ → OnePoint ℕ)).mp continuous_id
  have hmap : ∀ n : ℕ, OnePoint.map f (OnePoint.some n) = OnePoint.some (f n) := fun n => rfl
  have hmapinfty : OnePoint.map f (∞ : OnePoint ℕ) = ∞ := rfl
  simpa only [hmap, hmapinfty, Function.comp_def] using hsome.comp hf

theorem tendsto_two_mul_add (c : ℕ) : Filter.Tendsto (fun n : ℕ => 2 * n + c) Filter.atTop
    Filter.atTop := by
  have h := Filter.tendsto_atTop_mono (f := id) (g := fun n : ℕ => 2 * n + c)
    (fun n => by simp; omega) Filter.tendsto_id
  simpa using h

/-- The map `ℕ∪{∞} → ℕ∪{∞}`, `n ↦ 2n+1`, `∞ ↦ ∞`. -/
def phiA : ℕ∪{∞} ⟶ ℕ∪{∞} :=
  ConcreteCategory.ofHom ⟨fun x : OnePoint ℕ => OnePoint.map (fun n => 2 * n + 1) x,
    continuous_map_nat _ (tendsto_two_mul_add 1)⟩

/-- The map `ℕ∪{∞} → ℕ∪{∞}`, `n ↦ 2n+2`, `∞ ↦ ∞`. -/
def phiB : ℕ∪{∞} ⟶ ℕ∪{∞} :=
  ConcreteCategory.ofHom ⟨fun x : OnePoint ℕ => OnePoint.map (fun n => 2 * n + 2) x,
    continuous_map_nat _ (tendsto_two_mul_add 2)⟩

theorem phiA_apply_some (n : ℕ) : phiA (OnePoint.some n) = OnePoint.some (2 * n + 1) := rfl

theorem phiB_apply_some (n : ℕ) : phiB (OnePoint.some n) = OnePoint.some (2 * n + 2) := rfl

theorem phiA_apply_infty : phiA (∞ : ℕ∪{∞}) = ∞ := rfl

theorem phiB_apply_infty : phiB (∞ : ℕ∪{∞}) = ∞ := rfl

theorem shift_apply_some (n : ℕ) :
    LightProfinite.shift (OnePoint.some n) = OnePoint.some (n + 1) := rfl

theorem shift_apply_infty : LightProfinite.shift (∞ : ℕ∪{∞}) = ∞ := rfl

/-! ## The bookkeeping identities -/

theorem ptZero_shift : ptZero ≫ LightProfinite.shift = ptOne := by
  apply ConcreteCategory.hom_ext
  intro x
  rfl

theorem ptZero_phiA : ptZero ≫ phiA = ptOne := by
  apply ConcreteCategory.hom_ext
  intro x
  rfl

theorem phiA_shift : phiA ≫ LightProfinite.shift = phiB := by
  apply ConcreteCategory.hom_ext
  intro x
  cases x with
  | none => rfl
  | some n => rfl

theorem phiB_shift : phiB ≫ LightProfinite.shift = LightProfinite.shift ≫ phiA := by
  apply ConcreteCategory.hom_ext
  intro x
  cases x with
  | none => rfl
  | some n => rfl

end Work.ANALYTIC
