import Mathlib
import Submission.Work.NN.Seeley.Setup
import Submission.Work.NN.Final.dilation_expansion

noncomputable section

namespace Work.NN.Seeley

open scoped BigOperators

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The multilinear coefficient: `Φ` evaluated on the family which is `(0, (v j).2)` on the
indices in `t` and `((v j).1, 0)` off `t`. -/
def seeleyCoef {k : ℕ} (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => X × ℝ) ℂ)
    (v : Fin k → X × ℝ) (t : Finset (Fin k)) : ℂ :=
  Φ (t.piecewise (fun j => (0, (v j).2)) (fun j => ((v j).1, 0)))

/-- From the real summability hypothesis `∑' |a m| * (b m)^j` we get the summable family
`m ↦ a m * (-(b m))^j`. -/
lemma summable_moment {a b : ℕ → ℝ} {j : ℕ}
    (h : Summable fun m => |a m| * (b m) ^ j) :
    Summable fun m => a m * (-(b m)) ^ j := by
  have h1 : Summable fun m => ‖(|a m| * (b m) ^ j : ℝ)‖ :=
    (summable_norm_iff (f := fun m => |a m| * (b m) ^ j)).mpr h
  have h2 : Summable fun m => ‖(a m * (-(b m)) ^ j : ℝ)‖ := by
    simpa [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg] using h1
  exact Summable.of_norm h2

/-- Multilinear expansion of the function `s ↦ Φ (fun j => ((v j).1, s * (v j).2))` as a
polynomial in `s` with coefficients `seeleyCoef Φ v t`. -/
lemma phi_expansion {k : ℕ} (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => X × ℝ) ℂ)
    (v : Fin k → X × ℝ) (s : ℝ) :
    Φ (fun j => ((v j).1, s * (v j).2))
      = ∑ t : Finset (Fin k), s ^ t.card • seeleyCoef Φ v t := by
  have h := Work.NN.Final.dilation_expansion Φ
    (fun j : Fin k => ((v j).1, (0 : ℝ)))
    (fun j : Fin k => ((0 : X), (v j).2))
    (fun _ : Fin k => s)
  rw [show (fun j : Fin k => ((v j).1, (0 : ℝ)) + s • ((0 : X), (v j).2))
      = (fun j : Fin k => ((v j).1, s * (v j).2)) from by funext j; simp] at h
  simpa only [seeleyCoef, Finset.prod_const] using h

/-- The multilinear moment identity underlying the jet matching of the Seeley extension. -/
theorem seeley_moment_tensor {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {a b : ℕ → ℝ} (ha : ∀ j : ℕ, ∑' m, a m * (-(b m)) ^ j = 1)
    (hsum : ∀ j : ℕ, Summable fun m => |a m| * (b m) ^ j)
    (k : ℕ) (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => X × ℝ) ℂ)
    (v : Fin k → X × ℝ) :
    (∑' m, (a m) • Φ (fun j => ((v j).1, -(b m) * (v j).2))) = Φ v := by
  classical
  have hexp : ∀ s : ℝ, Φ (fun j => ((v j).1, s * (v j).2))
      = ∑ t : Finset (Fin k), s ^ t.card • seeleyCoef Φ v t :=
    fun s => phi_expansion Φ v s
  have hv : Φ v = ∑ t : Finset (Fin k), seeleyCoef Φ v t := by
    have h := hexp 1
    rw [show (fun j : Fin k => ((v j).1, (1 : ℝ) * (v j).2)) = v from by funext j; simp] at h
    simpa using h
  have hterm : ∀ m : ℕ, (a m) • Φ (fun j => ((v j).1, -(b m) * (v j).2))
      = ∑ t : Finset (Fin k), (a m * (-(b m)) ^ t.card) • seeleyCoef Φ v t := by
    intro m
    rw [hexp (-(b m)), Finset.smul_sum]
    exact Finset.sum_congr rfl fun t _ => by rw [smul_smul]
  have hsumble : ∀ t : Finset (Fin k),
      Summable (fun m => (a m * (-(b m)) ^ t.card) • seeleyCoef Φ v t) := by
    intro t
    have hm : Summable (fun m => a m * (-(b m)) ^ t.card) := summable_moment (hsum t.card)
    have h1 : HasSum (fun m => a m * (-(b m)) ^ t.card) 1 := by
      have hh := hm.hasSum
      rwa [ha t.card] at hh
    exact (h1.smul_const (seeleyCoef Φ v t)).summable
  have hval : ∀ t : Finset (Fin k),
      (∑' m, (a m * (-(b m)) ^ t.card) • seeleyCoef Φ v t) = seeleyCoef Φ v t := by
    intro t
    have hm : Summable (fun m => a m * (-(b m)) ^ t.card) := summable_moment (hsum t.card)
    have h1 : HasSum (fun m => a m * (-(b m)) ^ t.card) 1 := by
      have hh := hm.hasSum
      rwa [ha t.card] at hh
    simpa using (h1.smul_const (seeleyCoef Φ v t)).tsum_eq
  calc (∑' m, (a m) • Φ (fun j => ((v j).1, -(b m) * (v j).2)))
      = ∑' m, ∑ t : Finset (Fin k), (a m * (-(b m)) ^ t.card) • seeleyCoef Φ v t := by
        refine tsum_congr fun m => ?_
        exact hterm m
    _ = ∑ t : Finset (Fin k), ∑' m, (a m * (-(b m)) ^ t.card) • seeleyCoef Φ v t :=
        Summable.tsum_finsetSum
          (f := fun t m => (a m * (-(b m)) ^ t.card) • seeleyCoef Φ v t)
          (s := Finset.univ) (fun t _ => hsumble t)
    _ = ∑ t : Finset (Fin k), seeleyCoef Φ v t :=
        Finset.sum_congr rfl fun t _ => hval t
    _ = Φ v := hv.symm

end Work.NN.Seeley
