import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Submission.Work.BoseBoxFock.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

/-! ## Helper: finite-combination absolute bounds for a linear functional

The two lemmas below are the abstract content of `exists_abs_bound_double`: a *linear*
functional `L` of a finite scalar combination of vectors is bounded by the corresponding
weighted combination of the absolute values, provided each vector is already bounded. -/

/-- A single finite sum: if `|L (X i)| ≤ B i` for `i ∈ s` then the scalar combination obeys
the weighted bound. -/
private lemma abs_sum_smul_le {ι M : Type*} [AddCommGroup M] [Module ℝ M]
    (L : M →ₗ[ℝ] ℝ) {s : Finset ι} {c B : ι → ℝ} {X : ι → M}
    (h : ∀ i ∈ s, |L (X i)| ≤ B i) :
    |L (∑ i ∈ s, c i • X i)| ≤ ∑ i ∈ s, |c i| * B i := by
  rw [map_sum]
  refine le_trans (Finset.abs_sum_le_sum_abs (fun i => L (c i • X i)) s) ?_
  refine Finset.sum_le_sum fun i hi => ?_
  rw [map_smul, smul_eq_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (h i hi) (abs_nonneg _)

/-- The double-sum form of `abs_sum_smul_le`. -/
private lemma abs_sum_sum_smul_le {ι κ M : Type*} [AddCommGroup M] [Module ℝ M]
    (L : M →ₗ[ℝ] ℝ) {s : Finset ι} {t : Finset κ} {c B : ι → κ → ℝ} {X : ι → κ → M}
    (h : ∀ i ∈ s, ∀ j ∈ t, |L (X i j)| ≤ B i j) :
    |L (∑ i ∈ s, ∑ j ∈ t, c i j • X i j)| ≤ ∑ i ∈ s, ∑ j ∈ t, |c i j| * B i j := by
  rw [map_sum]
  refine le_trans (Finset.abs_sum_le_sum_abs (fun i => L (∑ j ∈ t, c i j • X i j)) s) ?_
  exact Finset.sum_le_sum fun i hi => abs_sum_smul_le L fun j hj => h i hi j hj

/-- **A finite scalar combination of window-bounded operators is window-bounded.**  If each
`X a b` satisfies `|⟨g, X a b g⟩| ≤ C_{ab} ‖g‖²` on the window `NWindow M`, then so does any
finite scalar combination `∑_{a ∈ s} ∑_{b ∈ t} c a b • X a b`, the constant being
`∑_{a ∈ s} ∑_{b ∈ t} |c a b| · C_{ab}` (with the `C_{ab}` the chosen nonnegative bound). -/
theorem exists_abs_bound_double {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F) (M : ℝ)
    {α β : Type*} (s : Finset α) (t : Finset β) (c : α → β → ℝ) (X : α → β → F.H →ₗ[ℝ] F.H)
    (hX : ∀ a ∈ s, ∀ b ∈ t, ∃ C : ℝ, ∀ g : F.H, T.NWindow M g →
      |F.qw g (X a b)| ≤ C * F.normSq g) :
    ∃ D : ℝ, ∀ g : F.H, T.NWindow M g →
      |F.qw g (∑ a ∈ s, ∑ b ∈ t, c a b • X a b)| ≤ D * F.normSq g := by
  classical
  -- Choose one bound per pair `(a,b)`, made nonnegative by taking absolute values.
  let Cb : α → β → ℝ := fun a b =>
    if h : a ∈ s ∧ b ∈ t then |Classical.choose (hX a h.1 b h.2)| else 0
  have hCb : ∀ a ∈ s, ∀ b ∈ t, ∀ g : F.H, T.NWindow M g →
      |F.qw g (X a b)| ≤ Cb a b * F.normSq g := by
    intro a ha b hb g hg
    have hiff : a ∈ s ∧ b ∈ t := ⟨ha, hb⟩
    have hspec : ∀ g : F.H, T.NWindow M g →
        |F.qw g (X a b)| ≤ Classical.choose (hX a hiff.1 b hiff.2) * F.normSq g :=
      Classical.choose_spec (hX a hiff.1 b hiff.2)
    show |F.qw g (X a b)| ≤
      (if h : a ∈ s ∧ b ∈ t then |Classical.choose (hX a h.1 b h.2)| else 0) * F.normSq g
    rw [dif_pos hiff]
    calc |F.qw g (X a b)| ≤ Classical.choose (hX a hiff.1 b hiff.2) * F.normSq g := hspec g hg
      _ ≤ |Classical.choose (hX a hiff.1 b hiff.2)| * F.normSq g :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (F.bp_nonneg g)
  refine ⟨∑ a ∈ s, ∑ b ∈ t, |c a b| * Cb a b, ?_⟩
  intro g hg
  -- `qw g ·` is linear in the operator argument.
  let L : (F.H →ₗ[ℝ] F.H) →ₗ[ℝ] ℝ :=
    { toFun := fun Z => F.qw g Z
      map_add' := by
        intro Y Z
        simp only [Work.BoseB7.FockData.qw, LinearMap.add_apply, map_add]
      map_smul' := by
        intro r Y
        simp [Work.BoseB7.FockData.qw, smul_eq_mul] }
  have hL : ∀ Z : F.H →ₗ[ℝ] F.H, L Z = F.qw g Z := fun Z => rfl
  have key := abs_sum_sum_smul_le L (s := s) (t := t) (c := c)
    (B := fun a b => Cb a b * F.normSq g) (X := X)
    (fun a ha b hb => by rw [hL]; exact hCb a ha b hb g hg)
  rw [hL] at key
  calc |F.qw g (∑ a ∈ s, ∑ b ∈ t, c a b • X a b)|
      ≤ ∑ a ∈ s, ∑ b ∈ t, |c a b| * (Cb a b * F.normSq g) := key
    _ = (∑ a ∈ s, ∑ b ∈ t, |c a b| * Cb a b) * F.normSq g := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun b _ => ?_
          ring

end Work.BoseBoxFock
