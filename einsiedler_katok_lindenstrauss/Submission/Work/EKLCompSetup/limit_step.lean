import Mathlib
import Submission.Work.EKLComp.C8Defs
import Submission.Work.EKLC8Core.All

namespace Work.EKLCompSetup

theorem limit_step
    {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    [PolishSpace Work.EKLContract.X3]
    (D : Work.EKLComp.C8Setup μ) {ρ B : ℝ} (hρ : 0 < ρ)
    {ys ys' : ℕ → Work.EKLContract.X3} {H : ℕ → Work.EKLContract.SL3} {c : ℕ → ℝ}
    (hys : ∀ n, ys n ∈ D.X₁) (hys' : ∀ n, ys' n ∈ D.X₁)
    (heq : ∀ n, D.ν (ys n) = D.ν (ys' n))
    (hsmul : ∀ n, ys' n = H n • ys n)
    (hc : Filter.Tendsto c Filter.atTop (nhds 0)) (hc0 : ∀ n, 0 ≤ c n)
    (hB : ∀ n i j, |(((H n : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)) i j| ≤ B)
    (h00 : ∀ n, |(((H n : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)) 0 0 - 1| ≤ c n)
    (h11 : ∀ n, |(((H n : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)) 1 1 - 1| ≤ c n)
    (h22 : ∀ n, |(((H n : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)) 2 2 - 1| ≤ c n)
    (h10 : ∀ n, |(((H n : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)) 1 0| ≤ c n)
    (h12 : ∀ n, |(((H n : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)) 1 2| ≤ c n)
    (h20 : ∀ n, |(((H n : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)) 2 0| ≤ c n)
    (hlow : ∀ n, ρ ^ 2 / 2 ≤
      Work.EKLC8Core.u12max (((H n : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ))) :
    ∃ (y y' : Work.EKLContract.X3) (h : Work.EKLContract.SL3),
      y ∈ D.X₁ ∧ y' ∈ D.X₁ ∧
      h ∈ (Work.EKLContract.Upar Work.EKLComp.h01 Work.EKLComp.h02 Work.EKLComp.h21 :
        Set Work.EKLContract.SL3) ∧
      h ≠ 1 ∧ y' = h • y ∧ D.ν y = D.ν y' := by
  -- Step 11 of `ROUTE_LEAD` §5: extract a convergent subsequence of `(ys, H)`, pass to the
  -- limit, and read off the shape of `h` from `EKLC8Core.limit_shape`.
  obtain ⟨y, hy_mem, φ₁, hφ₁, hys₁⟩ :=
    D.X₁_compact.tendsto_subseq (fun n => hys n)
  obtain ⟨h, φ₂, hφ₂, hH_t⟩ :=
    Work.EKLC8Core.exists_subseq_tendsto_of_entry_bound
      (g := fun n => H (φ₁ n)) (B := B) (fun n i j => hB (φ₁ n) i j)
  have hφ₂t : Filter.Tendsto φ₂ Filter.atTop Filter.atTop := hφ₂.tendsto_atTop
  have hys_t := hys₁.comp hφ₂t
  have hφ₁t : Filter.Tendsto φ₁ Filter.atTop Filter.atTop := hφ₁.tendsto_atTop
  have hc_t := (hc.comp hφ₁t).comp hφ₂t
  obtain ⟨_, _, _, _, _, _, _, hmem, hne⟩ :=
    Work.EKLC8Core.limit_shape (H := fun n => H (φ₁ (φ₂ n)))
      (HInf := h) (c := fun n => c (φ₁ (φ₂ n))) hρ hc_t (fun n => hc0 _) hH_t
      (fun n => h00 _) (fun n => h11 _) (fun n => h22 _)
      (fun n => h10 _) (fun n => h12 _) (fun n => h20 _) (fun n => hlow _)
  have hys'_t : Filter.Tendsto (fun n => ys' (φ₁ (φ₂ n))) Filter.atTop (nhds (h • y)) := by
    have h1 : (fun n => ys' (φ₁ (φ₂ n)))
        = fun n => H (φ₁ (φ₂ n)) • ys (φ₁ (φ₂ n)) := by
      funext n; exact hsmul _
    rw [h1]
    exact hH_t.smul hys_t
  have hy'_mem : h • y ∈ D.X₁ :=
    D.X₁_compact.isClosed.mem_of_tendsto hys'_t (Filter.Eventually.of_forall fun n => hys' _)
  have hν : D.ν y = D.ν (h • y) :=
    D.X₁_limit y (h • y) (fun n => ys (φ₁ (φ₂ n))) (fun n => ys' (φ₁ (φ₂ n)))
      (fun n => hys _) (fun n => hys' _) hys_t hys'_t (fun n => heq _)
  exact ⟨y, h • y, h, hy_mem, hy'_mem, hmem, hne, rfl, hν⟩

end Work.EKLCompSetup
