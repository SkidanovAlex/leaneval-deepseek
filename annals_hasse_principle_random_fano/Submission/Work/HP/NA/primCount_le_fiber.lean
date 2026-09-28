import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.NA.Setup
import Submission.Work.HP.primCount_residue_le
import Submission.Work.HP.NA.card_residue_class_le

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `primCount_le_fiber`

Counts of primitive coefficient vectors of height `≤ A` that satisfy a property `P` which is
detected modulo `W` are at most the number of residue classes involved times the largest
residue-class fibre.

The map `a ↦ (fun m => (a m : ZMod W))` sends the primitive height ball into `(ZMod W)^{N}`
(`N = NN d n`).  If `P a` implies `Bad (ā)` for the reduction `ā` of `a`, then the set counted by
`primCount` is covered by the `Nat.card {c // Bad c}` fibres of that map.  Each fibre of a fixed
residue class `c` is a residue-class ball, bounded by `(2A/W + 1)^N` (this is
`card_residue_class_le`, Mathlib-free), and the union of the fibres is bounded by the sum of the
fibre counts (`Set.ncard_iUnion_le_of_fintype`).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open Finset

namespace Work.HP.NA

/-- Every coordinate of an integer vector is bounded by its Euclidean norm. -/
private lemma abs_coord_le_eNorm'' {d n : ℕ} (a : Mon d n → ℤ) (m : Mon d n) :
    |(a m : ℝ)| ≤ eNorm a := by
  have h1 : ((a m : ℝ)) ^ 2 ≤ ∑ i, ((a i : ℝ)) ^ 2 :=
    Finset.single_le_sum (fun i _ => sq_nonneg ((a i : ℝ))) (Finset.mem_univ m)
  calc |(a m : ℝ)| = Real.sqrt (((a m : ℝ)) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (∑ i, ((a i : ℝ)) ^ 2) := Real.sqrt_le_sqrt h1
    _ = eNorm a := rfl

/-- The height ball `{a | ‖a‖ ≤ A}` is finite: it is contained in a product of intervals. -/
private lemma ball_finite'' {d n : ℕ} (A : ℝ) : {a : Mon d n → ℤ | eNorm a ≤ A}.Finite := by
  classical
  refine (Finset.finite_toSet (Fintype.piFinset
    (fun _ : Mon d n => Finset.Icc (-(⌈A⌉₊ : ℤ)) (⌈A⌉₊ : ℤ)))).subset ?_
  intro a ha
  rw [Finset.mem_coe, Fintype.mem_piFinset]
  intro m
  rw [Finset.mem_Icc]
  have h1 : |(a m : ℝ)| ≤ A := le_trans (abs_coord_le_eNorm'' a m) ha
  have h2 : ((|a m| : ℤ) : ℝ) ≤ (⌈A⌉₊ : ℝ) := by
    rw [Int.cast_abs]
    exact le_trans h1 (Nat.le_ceil A)
  exact abs_le.mp (by exact_mod_cast h2)

theorem primCount_le_fiber (d n : ℕ) (W : ℕ) (hW : 0 < W) (A : ℝ) (hA : 0 ≤ A)
    (P : (Work.HP.Mon d n → ℤ) → Prop) (Bad : (Work.HP.Mon d n → ZMod W) → Prop)
    (hP : ∀ a, P a → Bad (fun m => (a m : ZMod W))) :
    Work.HP.primCount d n A P
      ≤ (2 * A / W + 1) ^ (Work.HP.NN d n) * (Nat.card {c : Work.HP.Mon d n → ZMod W // Bad c} : ℝ) := by
  classical
  haveI : NeZero W := ⟨by omega⟩
  let Φ : {c : Mon d n → ZMod W // Bad c} → Set (Mon d n → ℤ) :=
    fun c => {a | IsPrim a ∧ eNorm a ≤ A ∧ P a ∧ ∀ m, (a m : ZMod W) = c.1 m}
  have hcover : primSet d n A P = ⋃ c, Φ c := by
    ext a
    constructor
    · intro ha
      change IsPrim a ∧ eNorm a ≤ A ∧ P a at ha
      refine Set.mem_iUnion.mpr ⟨⟨fun m => (a m : ZMod W), hP a ha.2.2⟩,
        ha.1, ha.2.1, ha.2.2, fun m => rfl⟩
    · intro ha
      rw [Set.mem_iUnion] at ha
      obtain ⟨c, hc⟩ := ha
      change IsPrim a ∧ eNorm a ≤ A ∧ P a
      exact ⟨hc.1, hc.2.1, hc.2.2.1⟩
  have hle1 : (primSet d n A P).ncard
      ≤ ∑ c : {c : Mon d n → ZMod W // Bad c}, (Φ c).ncard := by
    rw [hcover]
    exact Set.ncard_iUnion_le_of_fintype Φ
  have hbound : ∀ c : {c : Mon d n → ZMod W // Bad c},
      ((Φ c).ncard : ℝ) ≤ (2 * A / W + 1) ^ (NN d n) := by
    intro c
    have hfin : ({a : Mon d n → ℤ | eNorm a ≤ A ∧ ∀ m, (a m : ZMod W) = c.1 m} : Set _).Finite :=
      (ball_finite'' (d := d) (n := n) A).subset (fun a ha => ha.1)
    have hle : (Φ c).ncard
        ≤ ({a : Mon d n → ℤ | eNorm a ≤ A ∧ ∀ m, (a m : ZMod W) = c.1 m} : Set _).ncard :=
      Set.ncard_le_ncard (fun a ha => ⟨ha.2.1, ha.2.2.2⟩) hfin
    calc ((Φ c).ncard : ℝ)
        ≤ (({a : Mon d n → ℤ | eNorm a ≤ A ∧ ∀ m, (a m : ZMod W) = c.1 m} : Set _).ncard : ℝ) := by
          exact_mod_cast hle
      _ = (Nat.card ↑({a : Mon d n → ℤ | eNorm a ≤ A ∧ ∀ m, (a m : ZMod W) = c.1 m} : Set _) : ℝ) := by
          rw [Nat.card_coe_set_eq]
      _ ≤ (2 * A / W + 1) ^ (NN d n) := card_residue_class_le d n W hW A hA c.1
  calc primCount d n A P
      = ((primSet d n A P).ncard : ℝ) := rfl
    _ ≤ ((∑ c : {c : Mon d n → ZMod W // Bad c}, (Φ c).ncard : ℕ) : ℝ) := by
        exact_mod_cast hle1
    _ = ∑ c : {c : Mon d n → ZMod W // Bad c}, ((Φ c).ncard : ℝ) := by
        rw [Nat.cast_sum]
    _ ≤ ∑ _c : {c : Mon d n → ZMod W // Bad c}, ((2 * A / W + 1) ^ (NN d n)) :=
        Finset.sum_le_sum (fun c _ => hbound c)
    _ = (2 * A / W + 1) ^ (NN d n) * (Nat.card {c : Mon d n → ZMod W // Bad c} : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
        ring

end Work.HP.NA
