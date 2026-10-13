import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongEps.LocUnif.iUnion_subbox
import Submission.Work.FTS.StrongEps.LocUnif.volume_box_sdiff_openBox

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif

open MeasureTheory

/-- The closed sub-boxes of the rectangle `[a,b] × [c,d]`, obtained by shrinking each side by
the margin `(b-a)/(k+2)` respectively `(d-c)/(k+2)`.  They increase with `k` and exhaust the
open rectangle `(a,b) × (c,d)`. -/
private def subbox (a b c d : ℝ) (k : ℕ) : Set (ℝ × ℝ) :=
  Set.Icc (a + (b - a) / ((k : ℝ) + 2)) (b - (b - a) / ((k : ℝ) + 2)) ×ˢ
    Set.Icc (c + (d - c) / ((k : ℝ) + 2)) (d - (d - c) / ((k : ℝ) + 2))

/-- The sub-boxes `subbox a b c d k` are increasing in `k`. -/
private lemma subbox_mono {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    Monotone (subbox a b c d) := by
  apply monotone_nat_of_le_succ
  intro k
  have hb : (0 : ℝ) < b - a := sub_pos.mpr hab
  have hd : (0 : ℝ) < d - c := sub_pos.mpr hcd
  have hδb : (b - a) / (((k + 1 : ℕ) : ℝ) + 2) ≤ (b - a) / ((k : ℝ) + 2) := by
    apply div_le_div_of_nonneg_left (le_of_lt hb) (by positivity)
    push_cast
    linarith
  have hδd : (d - c) / (((k + 1 : ℕ) : ℝ) + 2) ≤ (d - c) / ((k : ℝ) + 2) := by
    apply div_le_div_of_nonneg_left (le_of_lt hd) (by positivity)
    push_cast
    linarith
  intro p hp
  simp only [subbox, Set.mem_prod, Set.mem_Icc] at hp ⊢
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hp
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

-- The hypothesis `hg` of the target statement is not needed for the argument: the identity
-- holds for an arbitrary `g : ℝ × ℝ → ENNReal`.  Silence the unused-variable linter rather
-- than change the statement of the lemma.
set_option linter.unusedVariables false

/-- The Lebesgue integral of a nonnegative function over the closed rectangle `[a,b] × [c,d]`
is the supremum of its integrals over the increasing family of closed sub-boxes obtained by
cutting off the margin `(b-a)/(k+2)` (resp. `(d-c)/(k+2)`) from each side.

This is monotone convergence along an exhaustion of the rectangle, modulo the null set
consisting of its boundary. -/
theorem lintegral_subbox_eq_iSup {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    {g : ℝ × ℝ → ENNReal}
    (hg : AEMeasurable g (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d))) :
    ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d, g p =
      ⨆ k : ℕ, ∫⁻ p in (Set.Icc (a + (b - a) / ((k : ℝ) + 2)) (b - (b - a) / ((k : ℝ) + 2)) ×ˢ
          Set.Icc (c + (d - c) / ((k : ℝ) + 2)) (d - (d - c) / ((k : ℝ) + 2))), g p := by
  -- the sub-boxes increase with `k`, hence form a directed family
  have hdir : Directed (fun x1 x2 : Set (ℝ × ℝ) => x1 ⊆ x2) (subbox a b c d) :=
    (subbox_mono hab hcd).directed_le
  -- they exhaust the open rectangle, which differs from the closed one by a null boundary
  have hUnion : (⋃ k, subbox a b c d k) = Set.Ioo a b ×ˢ Set.Ioo c d := by
    simpa only [subbox] using iUnion_subbox hab hcd
  have hnull : volume (Set.Icc a b ×ˢ Set.Icc c d \ Set.Ioo a b ×ˢ Set.Ioo c d : Set (ℝ × ℝ)) = 0 :=
    volume_box_sdiff_openBox a b c d
  have hae : (Set.Icc a b ×ˢ Set.Icc c d : Set (ℝ × ℝ)) =ᵐ[volume]
      (Set.Ioo a b ×ˢ Set.Ioo c d) := by
    rw [ae_eq_set]
    refine ⟨hnull, ?_⟩
    rw [Set.sdiff_eq_empty.mpr (Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self)]
    simp
  rw [Measure.restrict_congr_set hae]
  rw [← hUnion]
  rw [setLIntegral_iUnion_of_directed g hdir]
  rfl

end Work.FTS.StrongEps.LocUnif
