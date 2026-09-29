import Mathlib
import Submission.Work.TMComp.PerfectDefs
import Submission.Work.TMComp.Perfect.KernelDefs

/-!
# Component C2 (`P_Perfect`): the eigenspaces of an almost Mathieu operator are a line

An `ℓ²` solution of the eigenvalue equation `H u = E u` of a Jacobi operator
`(H u) n = u (n+1) + u (n-1) + v n · u n` is determined, through the second order recursion
`u (n+1) = (E - v n) · u n - u (n-1)`, by its two initial values `u m`, `u (m+1)`.  The
Wronskian `wronsk u v` of two `ℓ²` solutions is constant (it is unchanged by the recursion),
and it tends to `0` because both solutions are `ℓ²`; hence it vanishes identically, and a
nonzero solution determines the second one from its two data at a point where it is nonzero.

This gives `kernel_dim_le_one`: any two `ℓ²` eigenvectors of an almost Mathieu operator at the
same real energy are linearly dependent.
-/

open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMComp.Perfect

open Filter Topology
open Work.TMContract

/-! ## 1. `ℓ²` sequences decay -/

/-- The coordinates of an `ℓ²(ℤ)` sequence tend to `0` along `+∞`. -/
theorem kernel_decay_atTop (f : EllTwo) :
    Tendsto (fun k : ℕ => (f (k : ℤ) : ℂ)) atTop (nhds 0) := by
  have hmem : Memℓp (f : ℤ → ℂ) 2 := lp.memℓp f
  have hsum : Summable (fun n : ℤ => ‖f n‖ ^ (2 : ℕ)) := by
    simpa [Real.rpow_two] using hmem.summable (p := 2) (by norm_num)
  have hsumN : Summable (fun k : ℕ => ‖f (k : ℤ)‖ ^ (2 : ℕ)) :=
    hsum.comp_injective Nat.cast_injective
  have h1 : Tendsto (fun k : ℕ => ‖f (k : ℤ)‖ ^ (2 : ℕ)) atTop (nhds 0) :=
    hsumN.tendsto_atTop_zero
  have h2 : Tendsto (fun k : ℕ => (‖f (k : ℤ)‖ : ℝ)) atTop (nhds 0) := by
    have h1' : Tendsto (fun k : ℕ => Real.sqrt (‖f (k : ℤ)‖ ^ (2:ℕ))) atTop (nhds 0) := by
      have := Real.continuous_sqrt.continuousAt.tendsto.comp h1
      rwa [Real.sqrt_zero] at this
    have heq : (fun k : ℕ => Real.sqrt (‖f (k : ℤ)‖ ^ (2:ℕ)))
        = (fun k : ℕ => (‖f (k : ℤ)‖ : ℝ)) :=
      funext fun k => Real.sqrt_sq (norm_nonneg _)
    rwa [heq] at h1'
  exact tendsto_zero_iff_norm_tendsto_zero.mpr h2

/-- The coordinates shifted by one also tend to `0` along `+∞`. -/
theorem kernel_decay_shift (f : EllTwo) :
    Tendsto (fun k : ℕ => (f (((k:ℤ)+1)) : ℂ)) atTop (nhds 0) := by
  have h := (kernel_decay_atTop f).comp (tendsto_add_atTop_nat (1 : ℕ))
  simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using h

/-! ## 2. Wronskian constancy -/

/-- One step of the Wronskian constancy. -/
theorem kernel_wronsk_step {c x y : ℤ → ℂ} (hx : IsRecSol c x) (hy : IsRecSol c y) (n : ℤ) :
    wronsk x y (n + 1) = wronsk x y n := by
  have hu : x (n + 2) = c (n + 1) * x (n + 1) - x n := by
    have h := hx (n + 1)
    rw [show n + 1 + 1 = n + 2 by ring, show n + 1 - 1 = n by ring] at h
    exact h
  have hv : y (n + 2) = c (n + 1) * y (n + 1) - y n := by
    have h := hy (n + 1)
    rw [show n + 1 + 1 = n + 2 by ring, show n + 1 - 1 = n by ring] at h
    exact h
  simp only [wronsk]
  rw [show n + 1 + 1 = n + 2 by ring]
  linear_combination (x (n + 1)) * hv - (y (n + 1)) * hu

/-- The Wronskian of two solutions of the same second order recursion is constant. -/
theorem kernel_wronsk_const {c x y : ℤ → ℂ} (hx : IsRecSol c x) (hy : IsRecSol c y) (n m : ℤ) :
    wronsk x y n = wronsk x y m := by
  have hstep : ∀ k : ℤ, wronsk x y (k + 1) = wronsk x y k := fun k => kernel_wronsk_step hx hy k
  have hpos : ∀ k : ℤ, 0 ≤ k → wronsk x y k = wronsk x y 0 :=
    Int.leInduction (m := 0) (motive := fun k _ => wronsk x y k = wronsk x y 0) rfl
      (fun k _ ih => (hstep k).trans ih)
  have hneg : ∀ k : ℤ, k ≤ 0 → wronsk x y k = wronsk x y 0 :=
    Int.leInductionDown (m := 0) (motive := fun k _ => wronsk x y k = wronsk x y 0) rfl
      (fun k _ ih => by
        have h := hstep (k - 1)
        rw [show k - 1 + 1 = k by ring] at h
        exact h.symm.trans ih)
  have hn' : wronsk x y n = wronsk x y 0 := by
    rcases le_total 0 n with hn | hn
    · exact hpos n hn
    · exact hneg n hn
  have hm' : wronsk x y m = wronsk x y 0 := by
    rcases le_total 0 m with hm | hm
    · exact hpos m hm
    · exact hneg m hm
  rw [hn', hm']

/-! ## 3. Two solutions agreeing in two consecutive coordinates agree everywhere -/

/-- Two solutions of the same second order recursion which agree in two consecutive
coordinates (up to a common factor `a`) are equal everywhere. -/
theorem kernel_eq_of_two_data {c x y : ℤ → ℂ} (hx : IsRecSol c x) (hy : IsRecSol c y) {m : ℤ}
    {a : ℂ} (hm : x m = a * y m) (hm1 : x (m + 1) = a * y (m + 1)) : ∀ n : ℤ, x n = a * y n := by
  have hz : ∀ k : ℤ, (x (k + 1) - a * y (k + 1)) =
      c k * (x k - a * y k) - (x (k - 1) - a * y (k - 1)) := by
    intro k
    have h1 := hx k
    have h2 := hy k
    rw [h1, h2]; ring
  have hb : ∀ k : ℤ, (x (k - 1) - a * y (k - 1)) =
      c k * (x k - a * y k) - (x (k + 1) - a * y (k + 1)) := by
    intro k
    rw [hz k]; ring
  have hup : ∀ k : ℤ, m ≤ k → (x k - a * y k = 0) ∧ (x (k + 1) - a * y (k + 1) = 0) :=
    Int.leInduction (m := m)
      (motive := fun k _ => (x k - a * y k = 0) ∧ (x (k + 1) - a * y (k + 1) = 0))
      ⟨by rw [hm]; ring, by rw [hm1]; ring⟩
      (fun k _ ih => by
        refine ⟨ih.2, ?_⟩
        have h := hz (k + 1)
        rw [show k + 1 + 1 = k + 2 by ring, show k + 1 - 1 = k by ring] at h
        rw [show k + 1 + 1 = k + 2 by ring, h, ih.2, ih.1]; ring)
  have hdown : ∀ k : ℤ, k ≤ m → (x k - a * y k = 0) ∧ (x (k - 1) - a * y (k - 1) = 0) :=
    Int.leInductionDown (m := m)
      (motive := fun k _ => (x k - a * y k = 0) ∧ (x (k - 1) - a * y (k - 1) = 0))
      ⟨by rw [hm]; ring, by rw [hb m, hm, hm1]; ring⟩
      (fun k _ ih => by
        refine ⟨ih.2, ?_⟩
        have h := hb (k - 1)
        rw [show k - 1 + 1 = k by ring] at h
        rw [h, ih.2, ih.1]; ring)
  intro n
  rcases le_total m n with hmn | hmn
  · exact sub_eq_zero.mp (hup n hmn).1
  · exact sub_eq_zero.mp (hdown n hmn).1

/-! ## 4. The eigenvalue recursion -/

/-- An eigenvector of an almost Mathieu operator satisfies the second order recursion
`u (n+1) = (E - v n) · u n - u (n-1)` with `v n = 2λ cos 2π(θ + nα)`. -/
theorem kernel_eigen_rec (α lam θ E : ℝ) {H : EllTwo →L[ℂ] EllTwo}
    (hH : IsAlmostMathieuOperator α lam θ H) {u : EllTwo} (hu : H u = (E:ℂ) • u) :
    IsRecSol (fun n : ℤ => (E:ℂ) - ((amoPot α lam θ n : ℝ):ℂ)) (u : ℤ → ℂ) := by
  intro n
  have h1 : H u n = u (n+1) + u (n-1) + ((amoPot α lam θ n : ℝ):ℂ) * u n := by
    rw [hH u n]; simp [amoPot]
  have h2 : (H u) n = ((E:ℂ) • u) n := by rw [hu]
  rw [h2] at h1
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] at h1
  linear_combination -h1

/-! ## 5. The main statement -/

/-- Any two `ℓ²` eigenvectors of an almost Mathieu operator at the same real energy are linearly
dependent. -/
theorem kernel_dim_le_one (α lam θ E : ℝ)
    (H : LeanEval.Analysis.TenMartini.EllTwo →L[ℂ] LeanEval.Analysis.TenMartini.EllTwo)
    (hH : LeanEval.Analysis.TenMartini.IsAlmostMathieuOperator α lam θ H)
    {u v : LeanEval.Analysis.TenMartini.EllTwo}
    (hu : H u = (E : ℂ) • u) (hv : H v = (E : ℂ) • v) :
    ∃ c : ℂ, v = c • u ∨ u = c • v := by
  have hcu : IsRecSol (fun n : ℤ => (E:ℂ) - ((amoPot α lam θ n : ℝ):ℂ)) (u : ℤ → ℂ) :=
    kernel_eigen_rec α lam θ E hH hu
  have hcv : IsRecSol (fun n : ℤ => (E:ℂ) - ((amoPot α lam θ n : ℝ):ℂ)) (v : ℤ → ℂ) :=
    kernel_eigen_rec α lam θ E hH hv
  -- the Wronskian is constant, and vanishes because the solutions are `ℓ²`
  have hWc : ∀ n : ℤ, wronsk (u:ℤ→ℂ) (v:ℤ→ℂ) n = wronsk (u:ℤ→ℂ) (v:ℤ→ℂ) 0 :=
    fun n => kernel_wronsk_const hcu hcv n 0
  have hWlim : Tendsto (fun k : ℕ => wronsk (u:ℤ→ℂ) (v:ℤ→ℂ) (k:ℤ)) atTop (nhds 0) := by
    have h := ((kernel_decay_atTop u).mul (kernel_decay_shift v)).sub
      ((kernel_decay_shift u).mul (kernel_decay_atTop v))
    simpa [wronsk, sub_eq_add_neg, mul_comm] using h
  have hW0 : wronsk (u:ℤ→ℂ) (v:ℤ→ℂ) 0 = 0 := by
    have hconst : (fun k : ℕ => wronsk (u:ℤ→ℂ) (v:ℤ→ℂ) (k:ℤ))
        = fun _ : ℕ => wronsk (u:ℤ→ℂ) (v:ℤ→ℂ) 0 := funext fun k => hWc (k:ℤ)
    rw [hconst] at hWlim
    exact tendsto_nhds_unique (f := fun _ : ℕ => wronsk (u:ℤ→ℂ) (v:ℤ→ℂ) 0)
      tendsto_const_nhds hWlim
  have hWzero : ∀ n : ℤ, wronsk (u:ℤ→ℂ) (v:ℤ→ℂ) n = 0 := fun n => by rw [hWc n, hW0]
  -- two independent `ℓ²` solutions would have a nonzero Wronskian
  by_cases hvz : v = 0
  · exact ⟨0, Or.inl (by rw [hvz]; simp)⟩
  · have hne : ∃ m : ℤ, (v : ℤ → ℂ) m ≠ 0 := by
      by_contra h
      simp only [not_exists, ne_eq, not_not] at h
      exact hvz (ellTwo_ext fun n => by simpa using h n)
    obtain ⟨m, hm⟩ := hne
    have hm' : (v:ℤ→ℂ) m ≠ 0 := hm
    refine ⟨(u:ℤ→ℂ) m / (v:ℤ→ℂ) m, Or.inr ?_⟩
    have hm_eq : (u:ℤ→ℂ) m = ((u:ℤ→ℂ) m / (v:ℤ→ℂ) m) * (v:ℤ→ℂ) m := by
      field_simp
    have hWm : (u:ℤ→ℂ) m * (v:ℤ→ℂ) (m+1) = (u:ℤ→ℂ) (m+1) * (v:ℤ→ℂ) m := by
      have h := hWzero m
      simp only [wronsk] at h
      exact sub_eq_zero.mp h
    have hm1_eq : (u:ℤ→ℂ) (m+1) = ((u:ℤ→ℂ) m / (v:ℤ→ℂ) m) * (v:ℤ→ℂ) (m+1) := by
      rw [div_mul_eq_mul_div, eq_div_iff hm']
      exact hWm.symm
    have hcoord := kernel_eq_of_two_data hcu hcv hm_eq hm1_eq
    apply ellTwo_ext
    intro n
    have h := hcoord n
    simpa [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] using h


end Work.TMComp.Perfect

end
