import Mathlib
import Submission.Work.Diff.EXT.ConnCov.RicTr.ShiftDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The selection-sum bound

`Work.Diff.EXT.ConnCov.RicTr.Hom j m` is the type of *strictly monotone* maps `Fin j → Fin m`, i.e.
of the `j`-element *selections* of direction slots out of `m`.  The tower recursion produces, at
each order `j`, a sum over all such selections; bounding the tower therefore requires bounding

  `∑_j (-1)^{m+j} (m-j)! · ∑_{f : Hom j m} F j f`

by the `m`-th order quantity times `∏_i (1 + b_i)`, where `b_i` are the (nonnegative) weights of
the individual slots.  The elementary input is

  `∑_{f : Hom j m} ∏_l b (f l) ≤ ∏_i (1 + b_i)`,

proved below as `sum_hom_prod_le`: each strictly monotone `f` contributes the monomial on its image
(an injection into the `j`-element subsets), and `∏ (1 + b_i)` expands over *all* subsets
(`Finset.prod_one_add`), so the binomial series dominates term by term.  Multiplying by
`(m-j)! ≤ m!` gives the factorial-weighted bound.
-/

set_option maxHeartbeats 400000

namespace Work.Diff.EXT.ConnCov.RicTrNT

open Finset

/-- **Elementary symmetric bound.**  For nonnegative weights `b : Fin m → ℝ`, the sum of the
products `∏_{l} b (f l)` over all strictly monotone `f : Fin j → Fin m` is at most
`∏_{i} (1 + b i)`.  Each `f` contributes the monomial carried by its image, a `j`-element subset,
and the full product expands over all subsets. -/
theorem sum_hom_prod_le (m : ℕ) (b : Fin m → ℝ) (hb : ∀ i, 0 ≤ b i) (j : ℕ) :
    (∑ f : Work.Diff.EXT.ConnCov.RicTr.Hom j m, ∏ l : Fin j, b (f.val l))
      ≤ ∏ i : Fin m, (1 + b i) := by
  classical
  -- Reindex the sum over strictly monotone maps by the images, i.e. by `j`-element subsets.
  have hmain : (∑ f : Work.Diff.EXT.ConnCov.RicTr.Hom j m, ∏ l : Fin j, b (f.val l))
      = ∑ S ∈ (Finset.univ : Finset (Fin m)).powersetCard j, ∏ i ∈ S, b i := by
    refine Finset.sum_bij (fun (a : Work.Diff.EXT.ConnCov.RicTr.Hom j m)
        (_ : a ∈ Finset.univ) => (Finset.univ.image a.val : Finset (Fin m))) ?_ ?_ ?_ ?_
    · intro a _
      exact Finset.mem_powersetCard.mpr ⟨fun x _ => Finset.mem_univ x, by
        rw [Finset.card_image_of_injective Finset.univ a.property.injective, Finset.card_univ,
            Fintype.card_fin]⟩
    · -- the image determines a strictly monotone map: it is the increasing enumeration
      intro a₁ _ a₂ _ h
      have hcard₁ : (Finset.univ.image a₁.val).card = j := by
        rw [Finset.card_image_of_injective Finset.univ a₁.property.injective, Finset.card_univ,
            Fintype.card_fin]
      have h₁ : a₁.val = (Finset.univ.image a₁.val).orderEmbOfFin hcard₁ :=
        Finset.orderEmbOfFin_unique hcard₁
          (fun x => Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩) a₁.property
      have h₂ : a₂.val = (Finset.univ.image a₁.val).orderEmbOfFin hcard₁ := by
        refine Finset.orderEmbOfFin_unique hcard₁ (fun x => ?_) a₂.property
        rw [h]
        exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
      exact Subtype.ext (h₁.trans h₂.symm)
    · -- every `j`-element subset is the image of its increasing enumeration
      intro S hS
      obtain ⟨-, hcard⟩ := Finset.mem_powersetCard.mp hS
      refine ⟨⟨S.orderEmbOfFin hcard, (S.orderEmbOfFin hcard).strictMono⟩, Finset.mem_univ _, ?_⟩
      exact Finset.image_orderEmbOfFin_univ S hcard
    · -- on the image, `∏_l b (f l) = ∏_{i ∈ image f} b i`
      intro a _
      exact (Finset.prod_image (f := b) (s := (Finset.univ : Finset (Fin j))) (g := a.val)
        (fun x _ y _ hxy => a.property.injective hxy)).symm
  rw [hmain]
  calc ∑ S ∈ (Finset.univ : Finset (Fin m)).powersetCard j, ∏ i ∈ S, b i
      ≤ ∑ S ∈ (Finset.univ : Finset (Fin m)).powerset, ∏ i ∈ S, b i := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro S hS
          exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hS).1
        · intro S _ _
          exact Finset.prod_nonneg (fun i _ => hb i)
    _ = ∏ i : Fin m, (1 + b i) := (Finset.prod_one_add (Finset.univ : Finset (Fin m))).symm

theorem SelSumBound (m : ℕ) (b : Fin m → ℝ) (hb : ∀ i, 0 ≤ b i)
    (R : ℕ → ℝ) (hR : ∀ j, 0 ≤ R j) (Q : ℝ) (hQ : 0 ≤ Q)
    (F : (j : ℕ) → (Fin j → Fin m) → ℝ)
    (hF : ∀ j, j ≤ m → ∀ f : Work.Diff.EXT.ConnCov.RicTr.Hom j m,
      |F j f.val| ≤ R j * (Finset.univ.prod (fun l : Fin j => b (f.val l))) * Q) :
    |∑ j ∈ Finset.range (m + 1),
        ((-1 : ℝ) ^ (m + j) * ((m - j).factorial : ℝ)) *
          ∑ f : Work.Diff.EXT.ConnCov.RicTr.Hom j m, F j f.val|
      ≤ ((m.factorial : ℝ) * (∑ j ∈ Finset.range (m + 1), R j))
          * (Finset.univ.prod (fun i : Fin m => (1 + b i))) * Q := by
  classical
  set P : ℝ := ∏ i : Fin m, (1 + b i) with hPdef
  have hP : 0 ≤ P := by
    rw [hPdef]
    exact Finset.prod_nonneg (fun i _ => by linarith [hb i])
  -- per-order bound on the inner selection sum
  have hinner : ∀ j, j ≤ m → |∑ f : Work.Diff.EXT.ConnCov.RicTr.Hom j m, F j f.val|
      ≤ R j * P * Q := by
    intro j hj
    calc |∑ f : Work.Diff.EXT.ConnCov.RicTr.Hom j m, F j f.val|
        ≤ ∑ f : Work.Diff.EXT.ConnCov.RicTr.Hom j m, |F j f.val| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ f : Work.Diff.EXT.ConnCov.RicTr.Hom j m,
            R j * (∏ l : Fin j, b (f.val l)) * Q :=
          Finset.sum_le_sum (fun f _ => hF j hj f)
      _ = R j * Q * (∑ f : Work.Diff.EXT.ConnCov.RicTr.Hom j m, ∏ l : Fin j, b (f.val l)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun f _ => by ring)
      _ ≤ R j * Q * P :=
          mul_le_mul_of_nonneg_left (by rw [hPdef]; exact sum_hom_prod_le m b hb j)
            (mul_nonneg (hR j) hQ)
      _ = R j * P * Q := by ring
  -- bound each summand of the outer alternating sum
  have hstep : ∀ j ∈ Finset.range (m + 1),
      |((-1 : ℝ) ^ (m + j) * ((m - j).factorial : ℝ)) *
          ∑ f : Work.Diff.EXT.ConnCov.RicTr.Hom j m, F j f.val|
        ≤ ((m - j).factorial : ℝ) * (R j * P * Q) := by
    intro j hj
    have hjle : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have habs : |((-1 : ℝ) ^ (m + j) * ((m - j).factorial : ℝ))| = ((m - j).factorial : ℝ) := by
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
          abs_of_nonneg (Nat.cast_nonneg _)]
    rw [abs_mul, habs]
    exact mul_le_mul_of_nonneg_left (hinner j hjle) (Nat.cast_nonneg _)
  have hsum1 : |∑ j ∈ Finset.range (m + 1),
        ((-1 : ℝ) ^ (m + j) * ((m - j).factorial : ℝ)) *
          ∑ f : Work.Diff.EXT.ConnCov.RicTr.Hom j m, F j f.val|
      ≤ ∑ j ∈ Finset.range (m + 1), ((m - j).factorial : ℝ) * (R j * P * Q) :=
    le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum hstep)
  have hsum2 : ∑ j ∈ Finset.range (m + 1), ((m - j).factorial : ℝ) * (R j * P * Q)
      = P * Q * (∑ j ∈ Finset.range (m + 1), ((m - j).factorial : ℝ) * R j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hsum3 : ∑ j ∈ Finset.range (m + 1), ((m - j).factorial : ℝ) * R j
      ≤ (m.factorial : ℝ) * (∑ j ∈ Finset.range (m + 1), R j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun j hj => ?_)
    have hfac : ((m - j).factorial : ℝ) ≤ (m.factorial : ℝ) :=
      Nat.cast_le.mpr (Nat.factorial_le (Nat.sub_le m j))
    exact mul_le_mul_of_nonneg_right hfac (hR j)
  have hmain : |∑ j ∈ Finset.range (m + 1),
        ((-1 : ℝ) ^ (m + j) * ((m - j).factorial : ℝ)) *
          ∑ f : Work.Diff.EXT.ConnCov.RicTr.Hom j m, F j f.val|
      ≤ P * Q * ((m.factorial : ℝ) * (∑ j ∈ Finset.range (m + 1), R j)) :=
    le_trans hsum1 (le_trans (le_of_eq hsum2)
      (mul_le_mul_of_nonneg_left hsum3 (mul_nonneg hP hQ)))
  have hswap : P * Q * ((m.factorial : ℝ) * (∑ j ∈ Finset.range (m + 1), R j))
      = ((m.factorial : ℝ) * (∑ j ∈ Finset.range (m + 1), R j)) * P * Q := by ring
  rw [hswap] at hmain
  simpa only [hPdef] using hmain

end Work.Diff.EXT.ConnCov.RicTrNT
