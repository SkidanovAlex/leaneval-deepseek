import Mathlib
import Submission.Work.TMC16Core.Core.uni_nonres3_support
import Submission.Work.TMC16Core.Core.uni_nonres3_blkle

namespace Work.TMC16Core.Core

/-- The upper bound on the sum of `log |sin|` over the non-resonant window `Dnr`. -/
theorem pdw_sum_up {α ξ : ℝ} {q : ℕ → ℕ} {n s a' b' : ℕ} {y k : ℤ}
    (hL : 1 ≤ q (n - 1)) (hs : 1 ≤ s) (hab : a' + b' = s)
    (hy : Work.TMC16Core.Core.Tnr q n s ≤ y)
    (hk : k ∈ Work.TMC16Core.Core.Dnr q n s a' b' y)
    (hblk : ∀ (p : ℤ) (ξ : ℝ) (k₀ : ℤ),
      k₀ ∈ Finset.Icc p (p + (q (n - 1) : ℤ) - 1) →
      (∀ k ∈ Finset.Icc p (p + (q (n - 1) : ℤ) - 1),
        |Real.sin (Real.pi * (ξ + (k : ℝ) * α))| ≥
          |Real.sin (Real.pi * (ξ + (k₀ : ℝ) * α))|) →
      |∑ k ∈ (Finset.Icc p (p + (q (n - 1) : ℤ) - 1)).erase k₀,
          Real.log |Real.sin (Real.pi * (ξ + (k : ℝ) * α))|
        + ((q (n - 1) : ℝ) - 1) * Real.log 2| ≤ 32 * Real.log (q (n - 1) : ℝ))
    (hnz : ∀ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase k,
      Real.sin (Real.pi * (ξ + (i : ℝ) * α)) ≠ 0) :
    ∑ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase k,
        Real.log |Real.sin (Real.pi * (ξ + (i : ℝ) * α))|
      ≤ -((2 * (s : ℝ) * (q (n - 1) : ℝ) - 2 * (s : ℝ)) * Real.log 2)
        + 64 * (s : ℝ) * Real.log ((q (n - 1) : ℝ)) := by
  classical
  have habR : (a' : ℝ) + (b' : ℝ) = (s : ℝ) := by exact_mod_cast hab
  have habZ : (a' : ℤ) + (b' : ℤ) = (s : ℤ) := by exact_mod_cast hab
  have hsy : (s : ℤ) * (q (n - 1) : ℤ) ≤ y := by simpa only [Tnr] using hy
  have hdisj : ((a' : ℤ) + (b' : ℤ)) * (q (n - 1) : ℤ) ≤ y := by
    rw [habZ]; exact hsy
  have hdisjS :
      Disjoint (Finset.Icc (-((a' : ℤ) * (q (n - 1) : ℤ)))
          ((a' : ℤ) * (q (n - 1) : ℤ) - 1))
        (Finset.Icc (y - (b' : ℤ) * (q (n - 1) : ℤ))
          (y + (b' : ℤ) * (q (n - 1) : ℤ) - 1)) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_Icc] at hx1 hx2
    obtain ⟨h1a, h1b⟩ := hx1
    obtain ⟨h2a, h2b⟩ := hx2
    nlinarith [hdisj]
  have hdisjE : Disjoint
      ((Finset.Icc (-((a' : ℤ) * (q (n - 1) : ℤ)))
          ((a' : ℤ) * (q (n - 1) : ℤ) - 1)).erase k)
      ((Finset.Icc (y - (b' : ℤ) * (q (n - 1) : ℤ))
          (y + (b' : ℤ) * (q (n - 1) : ℤ) - 1)).erase k) := by
    rw [Finset.disjoint_left]
    intro x hxa hxb
    rw [Finset.mem_erase] at hxa hxb
    exact (Finset.disjoint_left.mp hdisjS) hxa.2 hxb.2
  have hsplit : (Dnr q n s a' b' y).erase k
      = (Finset.Icc (-((a' : ℤ) * (q (n - 1) : ℤ)))
            ((a' : ℤ) * (q (n - 1) : ℤ) - 1)).erase k
        ∪ (Finset.Icc (y - (b' : ℤ) * (q (n - 1) : ℤ))
            (y + (b' : ℤ) * (q (n - 1) : ℤ) - 1)).erase k := by
    simp only [Dnr, erase_union]
  have hAeq : Finset.Icc (-((a' : ℤ) * (q (n - 1) : ℤ)))
        (-((a' : ℤ) * (q (n - 1) : ℤ)) + ((2 * a' : ℕ) : ℤ) * (q (n - 1) : ℤ) - 1)
      = Finset.Icc (-((a' : ℤ) * (q (n - 1) : ℤ)))
        ((a' : ℤ) * (q (n - 1) : ℤ) - 1) := by
    congr 1
    push_cast
    ring
  have hBeq : Finset.Icc (y - (b' : ℤ) * (q (n - 1) : ℤ))
        (y - (b' : ℤ) * (q (n - 1) : ℤ) + ((2 * b' : ℕ) : ℤ) * (q (n - 1) : ℤ) - 1)
      = Finset.Icc (y - (b' : ℤ) * (q (n - 1) : ℤ))
        (y + (b' : ℤ) * (q (n - 1) : ℤ) - 1) := by
    congr 1
    push_cast
    ring
  have hnzL : ∀ i ∈ Finset.Icc (-((a' : ℤ) * (q (n - 1) : ℤ)))
        (-((a' : ℤ) * (q (n - 1) : ℤ)) + ((2 * a' : ℕ) : ℤ) * (q (n - 1) : ℤ) - 1),
      i ≠ k → Real.sin (Real.pi * (ξ + (i : ℝ) * α)) ≠ 0 := by
    intro i hi hik
    rw [hAeq] at hi
    refine hnz i (Finset.mem_erase.mpr ⟨hik, ?_⟩)
    show i ∈ Finset.Icc (-((a' : ℤ) * (q (n - 1) : ℤ)))
          ((a' : ℤ) * (q (n - 1) : ℤ) - 1) ∪
        Finset.Icc (y - (b' : ℤ) * (q (n - 1) : ℤ))
          (y + (b' : ℤ) * (q (n - 1) : ℤ) - 1)
    exact Finset.mem_union.mpr (Or.inl hi)
  have hnzR : ∀ i ∈ Finset.Icc (y - (b' : ℤ) * (q (n - 1) : ℤ))
        (y - (b' : ℤ) * (q (n - 1) : ℤ) + ((2 * b' : ℕ) : ℤ) * (q (n - 1) : ℤ) - 1),
      i ≠ k → Real.sin (Real.pi * (ξ + (i : ℝ) * α)) ≠ 0 := by
    intro i hi hik
    rw [hBeq] at hi
    refine hnz i (Finset.mem_erase.mpr ⟨hik, ?_⟩)
    show i ∈ Finset.Icc (-((a' : ℤ) * (q (n - 1) : ℤ)))
          ((a' : ℤ) * (q (n - 1) : ℤ) - 1) ∪
        Finset.Icc (y - (b' : ℤ) * (q (n - 1) : ℤ))
          (y + (b' : ℤ) * (q (n - 1) : ℤ) - 1)
    exact Finset.mem_union.mpr (Or.inr hi)
  have hboundL :
      ∑ i ∈ (Finset.Icc (-((a' : ℤ) * (q (n - 1) : ℤ)))
            ((a' : ℤ) * (q (n - 1) : ℤ) - 1)).erase k,
          Real.log |Real.sin (Real.pi * (ξ + (i : ℝ) * α))|
        ≤ (2 * (a' : ℝ)) *
            (-(((q (n - 1) : ℝ) - 1) * Real.log 2) + 32 * Real.log (q (n - 1) : ℝ)) := by
    have h := uni_nonres3_blkle (L := q (n - 1)) (α := α) (ξ := ξ) hL
        (fun p k₀ hk₀ hmin => hblk p ξ k₀ hk₀ hmin)
        (-((a' : ℤ) * (q (n - 1) : ℤ))) (2 * a') k hnzL
    rw [hAeq] at h
    calc ∑ i ∈ (Finset.Icc (-((a' : ℤ) * (q (n - 1) : ℤ)))
              ((a' : ℤ) * (q (n - 1) : ℤ) - 1)).erase k,
            Real.log |Real.sin (Real.pi * (ξ + (i : ℝ) * α))|
          ≤ ((2 * a' : ℕ) : ℝ) *
              (-(((q (n - 1) : ℝ) - 1) * Real.log 2) + 32 * Real.log (q (n - 1) : ℝ)) := h
      _ = (2 * (a' : ℝ)) *
            (-(((q (n - 1) : ℝ) - 1) * Real.log 2) + 32 * Real.log (q (n - 1) : ℝ)) := by
          push_cast; ring
  have hboundR :
      ∑ i ∈ (Finset.Icc (y - (b' : ℤ) * (q (n - 1) : ℤ))
            (y + (b' : ℤ) * (q (n - 1) : ℤ) - 1)).erase k,
          Real.log |Real.sin (Real.pi * (ξ + (i : ℝ) * α))|
        ≤ (2 * (b' : ℝ)) *
            (-(((q (n - 1) : ℝ) - 1) * Real.log 2) + 32 * Real.log (q (n - 1) : ℝ)) := by
    have h := uni_nonres3_blkle (L := q (n - 1)) (α := α) (ξ := ξ) hL
        (fun p k₀ hk₀ hmin => hblk p ξ k₀ hk₀ hmin)
        (y - (b' : ℤ) * (q (n - 1) : ℤ)) (2 * b') k hnzR
    rw [hBeq] at h
    calc ∑ i ∈ (Finset.Icc (y - (b' : ℤ) * (q (n - 1) : ℤ))
              (y + (b' : ℤ) * (q (n - 1) : ℤ) - 1)).erase k,
            Real.log |Real.sin (Real.pi * (ξ + (i : ℝ) * α))|
          ≤ ((2 * b' : ℕ) : ℝ) *
              (-(((q (n - 1) : ℝ) - 1) * Real.log 2) + 32 * Real.log (q (n - 1) : ℝ)) := h
      _ = (2 * (b' : ℝ)) *
            (-(((q (n - 1) : ℝ) - 1) * Real.log 2) + 32 * Real.log (q (n - 1) : ℝ)) := by
          push_cast; ring
  rw [hsplit, Finset.sum_union hdisjE]
  calc
    (∑ i ∈ (Finset.Icc (-((a' : ℤ) * (q (n - 1) : ℤ)))
          ((a' : ℤ) * (q (n - 1) : ℤ) - 1)).erase k,
        Real.log |Real.sin (Real.pi * (ξ + (i : ℝ) * α))|)
      + (∑ i ∈ (Finset.Icc (y - (b' : ℤ) * (q (n - 1) : ℤ))
          (y + (b' : ℤ) * (q (n - 1) : ℤ) - 1)).erase k,
        Real.log |Real.sin (Real.pi * (ξ + (i : ℝ) * α))|)
      ≤ (2 * (a' : ℝ)) *
            (-(((q (n - 1) : ℝ) - 1) * Real.log 2) + 32 * Real.log (q (n - 1) : ℝ))
        + (2 * (b' : ℝ)) *
            (-(((q (n - 1) : ℝ) - 1) * Real.log 2) + 32 * Real.log (q (n - 1) : ℝ)) :=
        add_le_add hboundL hboundR
    _ = -((2 * (s : ℝ) * (q (n - 1) : ℝ) - 2 * (s : ℝ)) * Real.log 2)
        + 64 * (s : ℝ) * Real.log ((q (n - 1) : ℝ)) := by
        rw [← habR]; ring

end Work.TMC16Core.Core
