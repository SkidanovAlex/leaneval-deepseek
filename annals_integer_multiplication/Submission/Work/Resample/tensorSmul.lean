import Mathlib
import Submission.Work.Resample.defs

namespace Work.Resample

/-- Pulling a constant scalar out of a product of a mapped list. -/
theorem prod_map_mul_const_apply {α : Type*} (l : List α) (d : ℂ) (g : α → ℂ) :
    (l.map (fun x => d * g x)).prod = d ^ l.length * (l.map g).prod := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.prod_cons, List.length_cons, ih, pow_succ]; ring

/-- The individual tensor entry witnesses the scalar by one factor per tensor leg. -/
theorem digitProd_smul (a c : List ℕ) (d : ℂ) (f : ℕ → ℕ → ℕ → ℂ) (J K : ℕ) :
    digitProd a c (fun i j k => d * f i j k) J K = d ^ a.length * digitProd a c f J K := by
  simp only [digitProd]
  rw [prod_map_mul_const_apply]
  simp

theorem tensorSmul (a c : List ℕ) (d : ℂ) (f : ℕ → ℕ → ℕ → ℂ) (u : Fin a.prod → ℂ) :
    Work.Resample.tensorLin a c (fun i j k => d * f i j k) u = d ^ a.length • Work.Resample.tensorLin a c f u := by
  funext J
  simp only [tensorLin_apply, tensorFun, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro K _
  rw [digitProd_smul]
  ring

end Work.Resample
