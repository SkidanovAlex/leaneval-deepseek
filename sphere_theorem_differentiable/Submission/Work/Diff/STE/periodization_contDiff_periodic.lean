import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The periodization of a smooth function supported in the open unit cube

For a smooth `f : (ι → ℝ) → ℂ` whose support is contained in the open cube `(-1/2, 1/2)^ι`, the
periodization

`P x = ∑' m : ι → ℤ, f (x + m)`

is smooth, is `1`-periodic in every coordinate, and agrees with `f` on the fundamental cube
`(-1/2, 1/2)^ι`.

The proof is the standard local-finiteness argument: near a point `x` only the finitely many
multi-indices `m` with `|m i| ≤ ⌊|x i|⌋ + 1` (for all `i`) can contribute to the sum, so on an open
neighbourhood of `x` the periodization coincides with a finite sum of translates of `f`, hence is
smooth there.  The periodicity is a reindexing of the sum (`Equiv.addLeft`), and the identification
on the fundamental cube follows because `f (x + m) ≠ 0` with `|x i| < 1/2` forces `m = 0`.
-/

noncomputable section

namespace Work.Diff.STE

open Function

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The integer vector `m : ι → ℤ` regarded as a real vector. -/
def iVec (m : ι → ℤ) : ι → ℝ := fun i => (m i : ℝ)

@[simp] lemma iVec_apply (m : ι → ℤ) (i : ι) : iVec m i = (m i : ℝ) := rfl

@[simp] lemma iVec_zero : iVec (0 : ι → ℤ) = 0 := funext fun i => by simp

/-- If `f` is supported in the open unit cube and `y` is within `1/2` of `x` in every coordinate,
then every multi-index `m` contributing to `∑' m, f (y + m)` satisfies `|m i| < ⌊|x i|⌋ + 2`. -/
lemma abs_lt_floor_add_two_of_support {f : (ι → ℝ) → ℂ}
    (hsupp : support f ⊆ Set.pi Set.univ (fun _ : ι => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)))
    {x y : ι → ℝ} (hy : ∀ i, |y i - x i| < 1 / 2) {m : ι → ℤ}
    (hm : f (y + iVec m) ≠ 0) (i : ι) :
    |m i| < ⌊|x i|⌋ + 2 := by
  have hmem : y + iVec m ∈ support f := hm
  have hcoord : y i + (m i : ℝ) ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
    have := Set.mem_pi.mp (hsupp hmem) i (Set.mem_univ i)
    simpa using this
  have ha : |y i + (m i : ℝ)| < 1 / 2 := by
    rw [Set.mem_Ioo] at hcoord
    exact abs_lt.mpr ⟨hcoord.1, hcoord.2⟩
  have hb : |y i - x i| < 1 / 2 := hy i
  have hyx : |y i| < 1 / 2 + |x i| := by
    calc |y i| = |(y i - x i) + x i| := by rw [sub_add_cancel]
      _ ≤ |y i - x i| + |x i| := abs_add_le _ _
      _ < 1 / 2 + |x i| := by linarith
  have hm1 : |(m i : ℝ)| < 1 + |x i| := by
    have h02 : |(m i : ℝ)| = |(y i + (m i : ℝ)) - y i| := by rw [add_sub_cancel_left]
    rw [h02]
    calc |(y i + (m i : ℝ)) - y i| = |(y i + (m i : ℝ)) + (-y i)| := by rw [sub_eq_add_neg]
      _ ≤ |y i + (m i : ℝ)| + |-y i| := abs_add_le _ _
      _ = |y i + (m i : ℝ)| + |y i| := by rw [abs_neg]
      _ < 1 + |x i| := by linarith
  have hm2 : (1 : ℝ) + |x i| < ((⌊|x i|⌋ + 2 : ℤ) : ℝ) := by
    have := Int.lt_floor_add_one (|x i|)
    push_cast
    linarith
  have hm3 : ((|m i| : ℤ) : ℝ) < ((⌊|x i|⌋ + 2 : ℤ) : ℝ) := by
    rw [Int.cast_abs]
    exact lt_trans hm1 hm2
  exact_mod_cast hm3

/-- The periodization of a smooth function supported in the open unit cube is smooth at every
point.  Near a point `x` the sum is a finite sum: the box `S` of multi-indices with
`|m i| ≤ ⌊|x i|⌋ + 1` is finite and carries the whole sum on a neighbourhood of `x`. -/
lemma contDiffAt_periodization {f : (ι → ℝ) → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hsupp : support f ⊆ Set.pi Set.univ (fun _ : ι => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)))
    (x : ι → ℝ) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ι → ℝ => ∑' m : ι → ℤ, f (y + iVec m)) x := by
  classical
  set N : ι → ℤ := fun i => ⌊|x i|⌋ + 2 with hNdef
  set S : Finset (ι → ℤ) := Fintype.piFinset (fun i => Finset.Icc (-(N i)) (N i)) with hSdef
  have hfin : ContDiff ℝ (⊤ : ℕ∞) (fun y : ι → ℝ => ∑ m ∈ S, f (y + iVec m)) := by
    apply ContDiff.sum
    intro m _
    have hshift : ContDiff ℝ (⊤ : ℕ∞) (fun y : ι → ℝ => y + iVec m) := by
      simpa using (contDiff_id.add (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ι → ℝ => iVec m)))
    exact hf.comp hshift
  have hBopen : IsOpen (Set.pi Set.univ (fun i : ι => Set.Ioo (x i - 1 / 2) (x i + 1 / 2))) :=
    isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
  have hxB : x ∈ Set.pi Set.univ (fun i : ι => Set.Ioo (x i - 1 / 2) (x i + 1 / 2)) := by
    rw [Set.mem_pi]
    intro i _
    rw [Set.mem_Ioo]
    constructor <;> linarith
  have hEq : (fun y : ι → ℝ => ∑ m ∈ S, f (y + iVec m)) =ᶠ[nhds x]
      (fun y : ι → ℝ => ∑' m : ι → ℤ, f (y + iVec m)) := by
    refine Filter.eventually_of_mem (hBopen.mem_nhds hxB) ?_
    intro y hy
    refine (tsum_eq_sum (s := S) ?_).symm
    intro m hm
    by_contra hc
    have hyabs : ∀ i, |y i - x i| < 1 / 2 := by
      intro i
      have := Set.mem_pi.mp hy i (Set.mem_univ i)
      rw [Set.mem_Ioo] at this
      rw [abs_lt]
      exact ⟨by linarith [this.1], by linarith [this.2]⟩
    have hbound : ∀ i, m i ∈ Finset.Icc (-(N i)) (N i) := by
      intro i
      have h1 : |m i| < N i := by
        have := abs_lt_floor_add_two_of_support hsupp hyabs hc i
        simpa [hNdef] using this
      rw [Finset.mem_Icc]
      have h2 := abs_lt.mp h1
      exact ⟨by linarith [h2.1], by linarith [h2.2]⟩
    exact hm (by rw [hSdef, Fintype.mem_piFinset]; exact hbound)
  exact hfin.contDiffAt.congr_of_eventuallyEq hEq.symm

/-- The periodization `x ↦ ∑' m, f (x + m)` is `1`-periodic in every coordinate; this is a
reindexing of the sum by the translation `m ↦ eᵢ + m` on `ι → ℤ`. -/
lemma periodization_periodic (f : (ι → ℝ) → ℂ) :
    Periodic1 (fun x : ι → ℝ => ∑' m : ι → ℤ, f (x + iVec m)) := by
  intro i x
  change ∑' m : ι → ℤ, f ((x + Pi.single i 1) + iVec m) = ∑' m : ι → ℤ, f (x + iVec m)
  have h : ∀ m : ι → ℤ,
      f ((x + Pi.single i 1) + iVec m) = f (x + iVec (Pi.single i (1 : ℤ) + m)) := by
    intro m
    congr 1
    funext j
    by_cases hji : j = i
    · subst hji; simp [Pi.single_eq_same]; ring
    · simp [Pi.single_eq_of_ne hji]
  rw [tsum_congr h]
  exact (Equiv.addLeft (Pi.single i (1 : ℤ))).tsum_eq (fun n : ι → ℤ => f (x + iVec n))

/-- On the fundamental cube `(-1/2, 1/2)^ι` the periodization equals `f`: if `|x i| < 1/2` for all
`i`, then `f (x + m) ≠ 0` forces `m i = 0` in every coordinate. -/
lemma periodization_eq_self {f : (ι → ℝ) → ℂ}
    (hsupp : support f ⊆ Set.pi Set.univ (fun _ : ι => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)))
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) :
    (∑' m : ι → ℤ, f (x + iVec m)) = f x := by
  have h : ∀ m : ι → ℤ, m ≠ 0 → f (x + iVec m) = 0 := by
    intro m hm
    by_contra hc
    have hmi : ∀ i, m i = 0 := by
      intro i
      have hmem : x + iVec m ∈ support f := hc
      have hcoord : x i + (m i : ℝ) ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
        have := Set.mem_pi.mp (hsupp hmem) i (Set.mem_univ i)
        simpa using this
      have hxa : |x i| < 1 / 2 := by
        have hh := hx i
        rw [Set.mem_Ioo] at hh
        exact abs_lt.mpr ⟨hh.1, hh.2⟩
      rw [Set.mem_Ioo] at hcoord
      have h1 : |x i + (m i : ℝ)| < 1 / 2 := abs_lt.mpr ⟨hcoord.1, hcoord.2⟩
      have hmm : |((m i : ℤ) : ℝ)| < 1 := by
        have h02 : (m i : ℝ) = (x i + (m i : ℝ)) - x i := by ring
        rw [h02]
        calc |(x i + (m i : ℝ)) - x i| = |(x i + (m i : ℝ)) + (-x i)| := by rw [sub_eq_add_neg]
          _ ≤ |x i + (m i : ℝ)| + |-x i| := abs_add_le _ _
          _ = |x i + (m i : ℝ)| + |x i| := by rw [abs_neg]
          _ < 1 := by linarith
      have h2 : |m i| < (1 : ℤ) := by
        rw [← Int.cast_abs] at hmm
        exact_mod_cast hmm
      have h3 := abs_lt.mp h2
      omega
    exact hm (funext hmi)
  rw [tsum_eq_single (0 : ι → ℤ) h]
  rw [iVec_zero, add_zero]

theorem periodization_contDiff_periodic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℝ) → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hsupp : Function.support f ⊆ Set.pi Set.univ
      (fun _ : ι => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2))) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : ι → ℝ => ∑' m : ι → ℤ, f (x + fun i => (m i : ℝ))) ∧
      Work.Diff.STE.Periodic1 (fun x : ι → ℝ => ∑' m : ι → ℤ, f (x + fun i => (m i : ℝ))) ∧
      ∀ x : ι → ℝ, (∀ i, x i ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) →
        (∑' m : ι → ℤ, f (x + fun i => (m i : ℝ))) = f x := by
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun x : ι → ℝ => ∑' m : ι → ℤ, f (x + iVec m)) :=
    contDiff_iff_contDiffAt.mpr (fun x => contDiffAt_periodization hf hsupp x)
  have hper : Periodic1 (fun x : ι → ℝ => ∑' m : ι → ℤ, f (x + iVec m)) :=
    periodization_periodic f
  have hself : ∀ x : ι → ℝ, (∀ i, x i ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) →
      (∑' m : ι → ℤ, f (x + iVec m)) = f x := fun x hx => periodization_eq_self hsupp hx
  exact ⟨hcd, hper, hself⟩

end Work.Diff.STE
