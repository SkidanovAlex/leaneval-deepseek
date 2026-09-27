import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLComp.Misiurewicz.Defs
import Submission.Work.EKLComp.Core

/-!
# Reindexing a window join over a grid

`Hfam μ (winJoin T P k N)` is a sum over the index set `Fin N → Fin P.n`.  Splitting the time
window `[k, k + m * n)` into the `m` consecutive blocks `[k + i * n, k + (i+1) * n)` and
reindexing the first index set as `Fin m → Fin n → Fin P.n` gives the same sum, because the
atoms of `winJoin T P k (m * n)` are exactly the intersections of the atoms of the block joins
`winJoin T P (k + i * n) n`.
-/

namespace Work.Misiurewicz

open MeasureTheory

/-! ## A reindexing lemma for `Hfam` -/

/-- `Hfam` is invariant under an equivalence of the index types. -/
theorem Hfam_congr_equiv {X : Type*} [MeasurableSpace X] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : MeasureTheory.Measure X) (e : ι ≃ κ) (σ : κ → Set X) :
    Work.EKLContract.Hfam μ (fun i => σ (e i)) = Work.EKLContract.Hfam μ σ := by
  unfold Work.EKLContract.Hfam
  exact Fintype.sum_equiv e _ _ fun _ => rfl

/-! ## The combinatorial reindexing of `Fin (m * n)` -/

/-- The bijection between `Fin (m * n) → α` and `Fin m → Fin n → α` obtained by viewing
`Fin (m * n)` as the product `Fin m × Fin n` (row-major order). -/
def gridEquiv (m n : ℕ) (α : Type*) :
    (Fin (m*n) → α) ≃ (Fin m → Fin n → α) :=
  (Equiv.arrowCongr (finProdFinEquiv (m := m) (n := n)).symm (Equiv.refl α)).trans
    (Equiv.curry (Fin m) (Fin n) α)

theorem gridEquiv_apply (m n : ℕ) (α : Type*) (w : Fin (m*n) → α) (i : Fin m) (j : Fin n) :
    gridEquiv m n α w i j = w (finProdFinEquiv (i, j)) := rfl

/-- The row-major value of the pair `(i, j)` is `i * n + j`, hence
`finProdFinEquiv p + k = p.2 + (k + p.1 * n)` as the exponents appearing in the two joins. -/
theorem val_finProdFinEquiv_add {m n : ℕ} (k : ℕ) (p : Fin m × Fin n) :
    ((finProdFinEquiv p : Fin (m*n)) : ℕ) + k = (p.2 : ℕ) + (k + (p.1 : ℕ) * n) := by
  have h : ((finProdFinEquiv p : Fin (m*n)) : ℕ) = (p.2 : ℕ) + n * (p.1 : ℕ) := rfl
  rw [h, Nat.mul_comm n ((p.1 : ℕ))]
  omega

/-- A double `iInter` over `Fin m` and `Fin n` is an `iInter` over the product `Fin m × Fin n`. -/
theorem iInter_prod_eq {m n : ℕ} {α : Type*} (f : Fin m × Fin n → Set α) :
    (⋂ p : Fin m × Fin n, f p) = ⋂ i : Fin m, ⋂ j : Fin n, f (i, j) := by
  ext x
  simp only [Set.mem_iInter]
  exact ⟨fun h i j => h (i, j), fun h p => h p.1 p.2⟩

/-! ## The identity of atoms -/

theorem winJoin_grid_pointwise (T : Work.EKLContract.X3 → Work.EKLContract.X3)
    (P : Work.EKLContract.FinPart Work.EKLContract.X3) (k m n : ℕ)
    (w : Fin (m*n) → Fin P.n) :
    Work.EKLComp.winJoin T P k (m*n) w =
      ⋂ i : Fin m, Work.EKLComp.winJoin T P (k + (i : ℕ) * n) n
        (gridEquiv m n (Fin P.n) w i) := by
  have step1 : Work.EKLComp.winJoin T P k (m*n) w =
      ⋂ p : Fin m × Fin n,
        T^[((finProdFinEquiv p : Fin (m*n)) : ℕ) + k] ⁻¹' P.parts (w (finProdFinEquiv p)) :=
    Set.iInter_congr_of_surjective
      (f := fun t : Fin (m*n) => T^[(t : ℕ) + k] ⁻¹' P.parts (w t))
      (g := fun p : Fin m × Fin n =>
        T^[((finProdFinEquiv p : Fin (m*n)) : ℕ) + k] ⁻¹' P.parts (w (finProdFinEquiv p)))
      finProdFinEquiv.symm finProdFinEquiv.symm.surjective
      (fun t => by simp only [Equiv.apply_symm_apply])
  have step2 : (⋂ p : Fin m × Fin n,
        T^[((finProdFinEquiv p : Fin (m*n)) : ℕ) + k] ⁻¹' P.parts (w (finProdFinEquiv p))) =
      ⋂ p : Fin m × Fin n,
        T^[(p.2 : ℕ) + (k + (p.1 : ℕ) * n)] ⁻¹' P.parts (w (finProdFinEquiv p)) :=
    Set.iInter_congr fun p => by rw [val_finProdFinEquiv_add]
  have step3 : (⋂ p : Fin m × Fin n,
        T^[(p.2 : ℕ) + (k + (p.1 : ℕ) * n)] ⁻¹' P.parts (w (finProdFinEquiv p))) =
      ⋂ i : Fin m, Work.EKLComp.winJoin T P (k + (i : ℕ) * n) n
        (gridEquiv m n (Fin P.n) w i) := by
    rw [iInter_prod_eq]
    exact Set.iInter_congr fun i => rfl
  exact step1.trans (step2.trans step3)

/-! ## The target -/

theorem Hfam_winJoin_grid_reindex (μ : MeasureTheory.Measure Work.EKLContract.X3)
    [MeasureTheory.IsProbabilityMeasure μ]
    (T : Work.EKLContract.X3 → Work.EKLContract.X3)
    (P : Work.EKLContract.FinPart Work.EKLContract.X3) (k m n : ℕ) :
    Work.EKLContract.Hfam μ (Work.EKLComp.winJoin T P k (m * n)) =
      Work.EKLContract.Hfam μ (fun V : Fin m → Fin n → Fin P.n =>
        ⋂ i : Fin m, Work.EKLComp.winJoin T P (k + (i : ℕ) * n) n (V i)) := by
  have hpt : Work.EKLComp.winJoin T P k (m * n) = fun w : Fin (m * n) → Fin P.n =>
      ⋂ i : Fin m, Work.EKLComp.winJoin T P (k + (i : ℕ) * n) n
        (gridEquiv m n (Fin P.n) w i) :=
    funext fun w => winJoin_grid_pointwise T P k m n w
  rw [hpt]
  exact Hfam_congr_equiv μ (gridEquiv m n (Fin P.n))
    (fun V : Fin m → Fin n → Fin P.n =>
      ⋂ i : Fin m, Work.EKLComp.winJoin T P (k + (i : ℕ) * n) n (V i))

end Work.Misiurewicz
