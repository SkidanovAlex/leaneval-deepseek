/-
# FI §15: auxiliary vocabulary for the `e`-stratum bound `S15pDng_e_bound`

The stratum sum of FI (15.1)–(15.2) is indexed by the pairs `(z₁,z₂)` of the coefficient box
with `(d, Re z₁) = e`, `4d ∣ |Δ|`.  Writing `z = e·ρ + i·s = scalePt e (ρ + i s)`, the stratum
becomes a pair sum in the variables `w = ρ + i·s` at modulus `4d/e`.  This module collects the
coordinate vocabulary of that change of variables (`scalePt`, `unscalePt`, `clsIdx`) together
with the elementary membership/arithmetic lemmas about it.
-/
import Mathlib
import Submission.Work.FIArea4.S15stratumDefs
import Submission.Work.FIArea4.S15expSumDefs
import Submission.Work.FIArea4.S15prim_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## The scaled point `e·ρ + i·s` -/

/-- The point `e·Re w + i·Im w` (the pair variable `z = eρ + is` of FI (15.2)). -/
def scalePt (e : ℕ) (w : GaussianInt) : GaussianInt := ⟨(e : ℤ) * w.re, w.im⟩

/-- The inverse change of variables `z = eρ + is ↦ ρ + is`. -/
def unscalePt (e : ℕ) (z : GaussianInt) : GaussianInt := ⟨z.re / (e : ℤ), z.im⟩

@[simp] lemma scalePt_re (e : ℕ) (w : GaussianInt) : (scalePt e w).re = (e : ℤ) * w.re := rfl
@[simp] lemma scalePt_im (e : ℕ) (w : GaussianInt) : (scalePt e w).im = w.im := rfl
@[simp] lemma unscalePt_re (e : ℕ) (z : GaussianInt) : (unscalePt e z).re = z.re / (e : ℤ) := rfl
@[simp] lemma unscalePt_im (e : ℕ) (z : GaussianInt) : (unscalePt e z).im = z.im := rfl

lemma scalePt_injective (e : ℕ) (he : 1 ≤ e) : Function.Injective (scalePt e) := by
  intro a b h
  have hez : (e : ℤ) ≠ 0 := by omega
  refine Zsqrtd.ext ?_ (by simpa using congrArg Zsqrtd.im h)
  have h1 : (e : ℤ) * a.re = (e : ℤ) * b.re := by simpa using congrArg Zsqrtd.re h
  exact mul_left_cancel₀ hez h1

lemma scalePt_unscalePt (e : ℕ) (_he : 1 ≤ e) {z : GaussianInt} (h : (e : ℤ) ∣ z.re) :
    scalePt e (unscalePt e z) = z := by
  have h' : (e : ℤ) * (z.re / (e : ℤ)) = z.re := Int.mul_ediv_cancel' h
  exact Zsqrtd.ext (by simpa using h') (by simp)

lemma unscalePt_scalePt (e : ℕ) (he : 1 ≤ e) (w : GaussianInt) :
    unscalePt e (scalePt e w) = w := by
  have hez : (e : ℤ) ≠ 0 := by omega
  have h' : (e : ℤ) * w.re / (e : ℤ) = w.re := Int.mul_ediv_cancel_left w.re hez
  exact Zsqrtd.ext (by simpa using h') (by simp)

lemma scalePt_re_natAbs (e : ℕ) (w : GaussianInt) :
    (scalePt e w).re.natAbs = e * w.re.natAbs := by
  simp only [scalePt_re, Int.natAbs_mul, Int.natAbs_natCast]

/-! ## The box `boxN Pa = gBox (radN Pa)` -/

lemma mem_gBox_iff {R : ℤ} {z : GaussianInt} :
    z ∈ Work.FIPlan.gBox R ↔ z.re ∈ Finset.Icc (-R) R ∧ z.im ∈ Finset.Icc (-R) R := by
  rw [Work.FIPlan.gBox, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨(Finset.mem_product.mp hp).1, (Finset.mem_product.mp hp).2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(z.re, z.im), Finset.mem_product.mpr ⟨h1, h2⟩, by cases z; rfl⟩

lemma mem_gBox_of {R : ℤ} {z : GaussianInt} (h1 : z.re ∈ Finset.Icc (-R) R)
    (h2 : z.im ∈ Finset.Icc (-R) R) : z ∈ Work.FIPlan.gBox R := mem_gBox_iff.mpr ⟨h1, h2⟩

lemma mem_boxN_iff {Pa : Work.FITop.Params} {z : GaussianInt} :
    z ∈ Work.FITop.boxN Pa ↔
      z.re ∈ Finset.Icc (-(Work.FITop.radN Pa)) (Work.FITop.radN Pa) ∧
      z.im ∈ Finset.Icc (-(Work.FITop.radN Pa)) (Work.FITop.radN Pa) :=
  mem_gBox_iff

@[simp] lemma mem_boxN {Pa : Work.FITop.Params} {z : GaussianInt} :
    z ∈ Work.FITop.boxN Pa ↔
      z.re ∈ Finset.Icc (-(Work.FITop.radN Pa)) (Work.FITop.radN Pa) ∧
      z.im ∈ Finset.Icc (-(Work.FITop.radN Pa)) (Work.FITop.radN Pa) :=
  mem_boxN_iff

/-! ## The class index modulo `m` -/

/-- The class of `w` modulo `m`: the residue `Im w · (Re w)⁻¹` read in `[0,m)`. -/
def clsIdx (m : ℕ) (w : GaussianInt) : ℕ :=
  (((w.im : ZMod m) * ((w.re : ZMod m))⁻¹)).val

/-- An integer coprime to `m` is a unit modulo `m`. -/
lemma isUnit_intCast_zmod' (m : ℕ) (z : ℤ) (h : Nat.Coprime z.natAbs m) :
    IsUnit (((z : ℤ)) : ZMod m) := by
  have h2 : IsUnit (((z.natAbs : ℕ) : ZMod m)) := (ZMod.isUnit_iff_coprime z.natAbs m).mpr h
  rcases Int.natAbs_eq z with hz | hz
  · rw [hz]; simpa using h2
  · rw [hz]; simpa using h2.neg

/-- If `w` lies in the class of index `a` and its real part is coprime to `m`, then the class
index function returns `a`. -/
lemma clsIdx_eq_of_mem {m a : ℕ} (ha : a < m) {w : GaussianInt}
    (hc : Nat.Coprime w.re.natAbs m)
    (h : (w.im : ZMod m) = (a : ZMod m) * (w.re : ZMod m)) : clsIdx m w = a := by
  have hu : IsUnit ((w.re : ZMod m)) := isUnit_intCast_zmod' m w.re hc
  have hval : ((w.im : ZMod m) * ((w.re : ZMod m))⁻¹) = (a : ZMod m) := by
    rw [h, mul_assoc, ZMod.mul_inv_of_unit _ hu, mul_one]
  unfold clsIdx
  rw [hval, ZMod.val_natCast, Nat.mod_eq_of_lt ha]

/-- `EvarG` is insensitive to the values of the array off the points with `(Re z, m) = 1`. -/
lemma EvarG_restrict (R : ℤ) (m : ℕ) (u : GaussianInt → ℂ) :
    EvarG R m (fun z => if Nat.Coprime z.re.natAbs m then u z else 0) = EvarG R m u := by
  have h : ∀ a : ℕ, clsSumG R m (fun z => if Nat.Coprime z.re.natAbs m then u z else 0) a
      = clsSumG R m u a := by
    intro a
    unfold clsSumG
    refine Finset.sum_congr rfl (fun z hz => ?_)
    have hz1 : Nat.Coprime z.re.natAbs m := (Finset.mem_filter.mp hz).2.1
    dsimp only
    by_cases hc : Nat.Coprime z.re.natAbs m
    · rw [if_pos hc]
    · exact absurd hz1 hc
  unfold EvarG
  simp only [h]

end

end Work.FIArea4
