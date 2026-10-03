import Mathlib
import Submission.Work.Peluse.Basic

/-!
# Translating all the direction sets of a box sum

The `2^t`-th power `Work.Peluse.boxSumPow t Q S f` of Peluse's Gowers box norm is the average over
pairs of shift tuples `h, h' : ∏_i Q_i` of the unconditional `x`-sum of the cube term
`∏_{ω : Fin t → Bool} C^{|ω|} f (x + ω·h + (1-ω)·h')`.

Replacing *every* direction set `Q i` by its translate `Q i + s` (i.e. shifting every direction by
the same amount `s`) does not change the box sum: a shift tuple `h ≡ a + s` corresponds to the
tuple `a ∈ ∏_i Q_i`, and the corner shift picks up exactly the constant `t·s`
(`cornerShift_add_const`), which is then absorbed by the change of variables `x ↦ x + t·s` in the
`tsum` over `ℤ` (`tsum_add_shift_int`).  Nothing needs summability of `f`: Mathlib's `tsum` over
`ℤ` is invariant under any bijection of the index type, summable or not.

This is the `t`-fold generalisation of `boxNormPow_two_shift` (the case `t = 2`, for `boxNormPow`,
in `Submission/Work/Peluse/Ulower/dense_le_apBoxNorm.lean`), in the same style as `boxSumPow_neg`
(reflection of the direction sets).  It exists because the upper-lowering argument needs to apply
Peluse's inverse theorem to a *translated* polynomial `P(X) - s` (equivalently, with all directions
shifted by `s`), and the resulting box norms must be compared.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.Ulower

noncomputable section

/-! ## Reindexing tools -/

/-- The translation `q ↦ q + s` of a finite set of integers is a bijection onto its image; this is
its inverse map `z ↦ z - s`, packaged as an equivalence of subtypes. -/
def shiftE (Q : Finset ℤ) (s : ℤ) :
    {x : ℤ // x ∈ Q.image (fun q => q + s)} ≃ {x : ℤ // x ∈ Q} where
  toFun z := ⟨z.1 - s, by
    obtain ⟨q, hq, hqz⟩ := Finset.mem_image.mp z.2
    have : z.1 - s = q := by omega
    rwa [this]⟩
  invFun z := ⟨z.1 + s, Finset.mem_image.mpr ⟨z.1, z.2, rfl⟩⟩
  left_inv z := by ext; simp
  right_inv z := by ext; simp

/-- The componentwise version of `shiftE`, for the shift *tuples* `∏_i Q_i` of the box norm. -/
abbrev piShiftE (t : ℕ) (Q : Fin t → Finset ℤ) (s : ℤ) :
    ((i : Fin t) → {x : ℤ // x ∈ (Q i).image (fun q => q + s)}) ≃
      ((i : Fin t) → {x : ℤ // x ∈ Q i}) where
  toFun h := fun i => shiftE (Q i) s (h i)
  invFun h := fun i => (shiftE (Q i) s).symm (h i)
  left_inv h := by funext i; simp [shiftE]
  right_inv h := by funext i; simp [shiftE]

/-- Translating both corners of a cube by `s` translates the corner by `t · s`. -/
lemma cornerShift_add_const {t : ℕ} (h h' : Fin t → ℤ) (s : ℤ) (ω : Fin t → Bool) :
    Work.Peluse.cornerShift (fun i => h i + s) (fun i => h' i + s) ω
      = Work.Peluse.cornerShift h h' ω + (t : ℤ) * s := by
  have hterm : ∀ i : Fin t,
      (if ω i then h i + s else h' i + s) = (if ω i then h i else h' i) + s := by
    intro i; by_cases hi : ω i <;> simp [hi]
  simp only [Work.Peluse.cornerShift]
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin]
  simp

/-- Change of variables for an unconditional sum over `ℤ`: translation of the argument by `p` is a
bijection of `ℤ`, so `∑' x, G (x + p) = ∑' x, G x`.  No summability hypothesis is needed. -/
lemma tsum_add_shift_int (G : ℤ → ℂ) (p : ℤ) :
    (∑' x : ℤ, G (x + p)) = ∑' x : ℤ, G x :=
  Equiv.tsum_eq (Equiv.addRight p) G

/-! ## The general statement for `prodCubeSum` -/

/-- **Translation of the direction sets** (general `2^t` functions).  Replacing every direction set
`Q i` by its translate `Q i + s` leaves the cube average `Work.Peluse.prodCubeSum` unchanged. -/
theorem prodCubeSum_image_shift (t : ℕ) (Q : Fin t → Finset ℤ) (S : Finset ℤ)
    (F : (Fin t → Bool) → ℤ → ℂ) (s : ℤ) :
    Work.Peluse.prodCubeSum t (fun i => (Q i).image (fun q => q + s)) S F
      = Work.Peluse.prodCubeSum t Q S F := by
  have hcard : ∀ i : Fin t, ((Q i).image (fun q => q + s)).card = (Q i).card := fun i =>
    Finset.card_image_of_injective _ (fun a b h => by simpa using add_right_cancel h)
  simp only [Work.Peluse.prodCubeSum, hcard]
  congr 1
  let E := piShiftE t Q s
  -- The inner `x`-sum over a pair of *unshifted* shift tuples.
  have key : ∀ (u u' : (i : Fin t) → {x : ℤ // x ∈ Q i}),
      (∑' x : ℤ, ∏ ω : Fin t → Bool,
        (star^[Work.Peluse.weight ω]) (F ω (x + Work.Peluse.cornerShift
          (fun i => ((E.symm u) i).1) (fun i => ((E.symm u') i).1) ω)))
      = ∑' x : ℤ, ∏ ω : Fin t → Bool,
        (star^[Work.Peluse.weight ω]) (F ω (x + Work.Peluse.cornerShift
          (fun i => (u i).1) (fun i => (u' i).1) ω)) := by
    intro u u'
    -- The shifted corners are the unshifted ones plus the constant `t · s`.
    have hcs : ∀ ω : Fin t → Bool,
        Work.Peluse.cornerShift (fun i => ((E.symm u) i).1) (fun i => ((E.symm u') i).1) ω
          = Work.Peluse.cornerShift (fun i => (u i).1) (fun i => (u' i).1) ω + (t : ℤ) * s := by
      intro ω
      have h1 : (fun i : Fin t => ((E.symm u) i).1) = (fun i => (u i).1 + s) := by
        funext i; rfl
      have h2 : (fun i : Fin t => ((E.symm u') i).1) = (fun i => (u' i).1 + s) := by
        funext i; rfl
      rw [h1, h2, cornerShift_add_const]
    have hpt : ∀ x : ℤ,
        (∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
          (F ω (x + Work.Peluse.cornerShift (fun i => ((E.symm u) i).1)
            (fun i => ((E.symm u') i).1) ω)))
        = ∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
          (F ω ((x + (t : ℤ) * s) + Work.Peluse.cornerShift (fun i => (u i).1)
            (fun i => (u' i).1) ω)) := by
      intro x
      refine Finset.prod_congr rfl (fun ω _ => ?_)
      rw [hcs ω, show x + (Work.Peluse.cornerShift (fun i => (u i).1) (fun i => (u' i).1) ω
            + (t : ℤ) * s)
          = (x + (t : ℤ) * s) + Work.Peluse.cornerShift (fun i => (u i).1)
              (fun i => (u' i).1) ω from by ring]
    -- Absorb the constant `t · s` into the change of variables `x ↦ x + t · s`.
    rw [tsum_congr hpt]
    exact tsum_add_shift_int (fun y : ℤ => ∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
      (F ω (y + Work.Peluse.cornerShift (fun i => (u i).1) (fun i => (u' i).1) ω)))
      ((t : ℤ) * s)
  -- Reindex the two shift-tuple sums along the componentwise translation.
  rw [← Equiv.sum_comp E.symm (g :=
    fun h : (i : Fin t) → {x : ℤ // x ∈ (Q i).image (fun q => q + s)} =>
      ∑ h' : (i : Fin t) → {x : ℤ // x ∈ (Q i).image (fun q => q + s)},
        ∑' x : ℤ, ∏ ω : Fin t → Bool,
          (star^[Work.Peluse.weight ω]) (F ω (x + Work.Peluse.cornerShift
            (fun i => (h i).1) (fun i => (h' i).1) ω)))]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [← Equiv.sum_comp E.symm (g :=
    fun h' : (i : Fin t) → {x : ℤ // x ∈ (Q i).image (fun q => q + s)} =>
      ∑' x : ℤ, ∏ ω : Fin t → Bool,
        (star^[Work.Peluse.weight ω]) (F ω (x + Work.Peluse.cornerShift
          (fun i => ((E.symm h) i).1) (fun i => (h' i).1) ω)))]
  exact Finset.sum_congr rfl (fun h' _ => key h h')

/-! ## The target statement -/

/-- **Shifting all direction sets of the box-sum power.**  Replacing every direction set `Q` by the
translate `Q.image (· + s)` (the case in which all `t` directions are shifted by the same amount
`s`) leaves `Work.Peluse.boxSumPow` unchanged. -/
theorem boxSumPow_shift_directions (t : ℕ) (Q S : Finset ℤ) (f : ℤ → ℂ) (s : ℤ) :
    Work.Peluse.boxSumPow t (fun _ : Fin t => Q.image (fun q : ℤ => q + s)) S f
      = Work.Peluse.boxSumPow t (fun _ : Fin t => Q) S f := by
  have hcard : (Q.image (fun q : ℤ => q + s)).card = Q.card :=
    Finset.card_image_of_injective _ (fun a b h => by simpa using add_right_cancel h)
  simp only [Work.Peluse.boxSumPow, Work.Peluse.prodCubeSum, hcard]
  congr 1
  let E := piShiftE t (fun _ : Fin t => Q) s
  -- The inner `x`-sum over a pair of *unshifted* shift tuples.
  have key : ∀ (u u' : (i : Fin t) → {x : ℤ // x ∈ Q}),
      (∑' x : ℤ, ∏ ω : Fin t → Bool,
        (star^[Work.Peluse.weight ω]) (f (x + Work.Peluse.cornerShift
          (fun i => ((E.symm u) i).1) (fun i => ((E.symm u') i).1) ω)))
      = ∑' x : ℤ, ∏ ω : Fin t → Bool,
        (star^[Work.Peluse.weight ω]) (f (x + Work.Peluse.cornerShift
          (fun i => (u i).1) (fun i => (u' i).1) ω)) := by
    intro u u'
    have hcs : ∀ ω : Fin t → Bool,
        Work.Peluse.cornerShift (fun i => ((E.symm u) i).1) (fun i => ((E.symm u') i).1) ω
          = Work.Peluse.cornerShift (fun i => (u i).1) (fun i => (u' i).1) ω + (t : ℤ) * s := by
      intro ω
      have h1 : (fun i : Fin t => ((E.symm u) i).1) = (fun i => (u i).1 + s) := by
        funext i; rfl
      have h2 : (fun i : Fin t => ((E.symm u') i).1) = (fun i => (u' i).1 + s) := by
        funext i; rfl
      rw [h1, h2, cornerShift_add_const]
    have hpt : ∀ x : ℤ,
        (∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
          (f (x + Work.Peluse.cornerShift (fun i => ((E.symm u) i).1)
            (fun i => ((E.symm u') i).1) ω)))
        = ∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
          (f ((x + (t : ℤ) * s) + Work.Peluse.cornerShift (fun i => (u i).1)
            (fun i => (u' i).1) ω)) := by
      intro x
      refine Finset.prod_congr rfl (fun ω _ => ?_)
      rw [hcs ω, show x + (Work.Peluse.cornerShift (fun i => (u i).1) (fun i => (u' i).1) ω
            + (t : ℤ) * s)
          = (x + (t : ℤ) * s) + Work.Peluse.cornerShift (fun i => (u i).1)
              (fun i => (u' i).1) ω from by ring]
    rw [tsum_congr hpt]
    exact tsum_add_shift_int (fun y : ℤ => ∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
      (f (y + Work.Peluse.cornerShift (fun i => (u i).1) (fun i => (u' i).1) ω)))
      ((t : ℤ) * s)
  rw [← Equiv.sum_comp E.symm (g :=
    fun h : (i : Fin t) → {x : ℤ // x ∈ Q.image (fun q => q + s)} =>
      ∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q.image (fun q => q + s)},
        ∑' x : ℤ, ∏ ω : Fin t → Bool,
          (star^[Work.Peluse.weight ω]) (f (x + Work.Peluse.cornerShift
            (fun i => (h i).1) (fun i => (h' i).1) ω)))]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [← Equiv.sum_comp E.symm (g :=
    fun h' : (i : Fin t) → {x : ℤ // x ∈ Q.image (fun q => q + s)} =>
      ∑' x : ℤ, ∏ ω : Fin t → Bool,
        (star^[Work.Peluse.weight ω]) (f (x + Work.Peluse.cornerShift
          (fun i => ((E.symm h) i).1) (fun i => (h' i).1) ω)))]
  exact Finset.sum_congr rfl (fun h' _ => key h h')

end

end Work.Peluse.Ulower
