import Mathlib
import Submission.Work.TMC16Core.Defs

namespace Work.TMC16Core.Basic

/-!
## The Poisson formula for formal solutions of the almost Mathieu equation

Avila–Jitomirskaya, *The Ten Martini Problem*, equation (poi): for a formal solution
`Ψ` of `H Ψ = E Ψ` on all of `ℤ` and an interval `I = [x₁,x₂]`, the values of `Ψ`
inside `I` are determined by the two boundary values through the Dirichlet Green's
function `G_I`:

`Ψ(y) = - G_I(y,x₁) Ψ(x₁-1) - G_I(y,x₂) Ψ(x₂+1)`   for `x₁ ≤ y ≤ x₂`.

Here `dirMat` is (the matrix of) `H - E` restricted to `[x₁,x₂]` with zero boundary
conditions, so it is the symmetric tridiagonal matrix with diagonal `v_n - E` and
off-diagonal entries `1`.  The proof is the standard one: the vector
`w i = u (x₁+i)` satisfies `dirMat · w = -u(x₁-1) e₀ - u(x₂+1) e_last`, whence
`w = dirMat⁻¹ · (…)` and the claim is read off entrywise.
-/

open Matrix

/-! ### Elementary auxiliary lemmas -/

/-- Shifting the phase by `x α` shifts the site index by `x`. -/
private lemma amoPot_shift (α lam θ : ℝ) (x : ℤ) (i : ℤ) :
    Work.TMC16Core.amoPot α lam (θ + (x : ℝ) * α) i = Work.TMC16Core.amoPot α lam θ (x + i) := by
  unfold Work.TMC16Core.amoPot
  push_cast
  ring_nf

/-- Left cancellation for `Matrix.mulVec` with an invertible matrix: if `A *ᵥ v = b` then
`v = A⁻¹ *ᵥ b`. -/
lemma mulVec_eq_inv_mulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.det ≠ 0)
    (v b : Fin n → ℂ) (h : A.mulVec v = b) : v = A⁻¹.mulVec b := by
  have h' := congrArg (fun z => A⁻¹.mulVec z) h
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA),
    Matrix.one_mulVec] at h'
  exact h'

/-- Applying `A⁻¹` to a two-point source: the entries of the resulting vector. -/
lemma inv_mulVec_single_add_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n)
    (a b : ℂ) (i : Fin n) :
    (A⁻¹.mulVec (Pi.single p a + Pi.single q b)) i = A⁻¹ i p * a + A⁻¹ i q * b := by
  rw [Matrix.mulVec_add, Matrix.mulVec_single, Matrix.mulVec_single]
  simp [Matrix.col]
  ring

/-- The Kronecker sum `∑ j, (if i = j then c else 0) * w j = c * w i`. -/
lemma sum_ite_fin_eq {n : ℕ} (i : Fin n) (c : ℂ) (w : Fin n → ℂ) :
    (∑ j : Fin n, (if i = j then c else 0) * w j) = c * w i := by
  rw [show (∑ j : Fin n, (if i = j then c else 0) * w j)
      = ∑ j : Fin n, (if j = i then c * w j else 0) from
    Finset.sum_congr rfl (fun j _ => by
      by_cases h : i = j
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (fun hh : j = i => h hh.symm), zero_mul])]
  rw [Finset.sum_ite_eq']
  rw [if_pos (Finset.mem_univ i)]

/-- The sum selecting the index `m+1`. -/
lemma sum_ite_ofNat_eq {n : ℕ} (m : ℕ) (w : Fin n → ℂ) :
    (∑ j : Fin n, (if ((m:ℤ) + 1 = ((j:ℕ):ℤ)) then (1:ℂ) else 0) * w j)
      = (if h : m + 1 < n then w ⟨m + 1, h⟩ else 0) := by
  by_cases h : m + 1 < n
  · rw [dif_pos h]
    rw [show (∑ j : Fin n, (if ((m:ℤ) + 1 = ((j:ℕ):ℤ)) then (1:ℂ) else 0) * w j)
        = ∑ j : Fin n, (if j = (⟨m+1, h⟩ : Fin n) then w j else 0) from
      Finset.sum_congr rfl (fun j _ => by
        by_cases hj : j = (⟨m+1, h⟩ : Fin n)
        · subst hj; simp
        · rw [if_neg hj]
          have hne : ¬ (((m:ℤ) + 1) = ((j:ℕ):ℤ)) := by
            intro hh
            exact hj (by apply Fin.ext; change (j:ℕ) = m + 1; omega)
          rw [if_neg hne, zero_mul])]
    rw [Finset.sum_ite_eq']
    rw [if_pos (Finset.mem_univ _)]
  · rw [dif_neg h]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hne : ¬ (((m:ℤ) + 1) = ((j:ℕ):ℤ)) := by
      intro hh
      exact h (by omega)
    rw [if_neg hne, zero_mul]

/-- The sum selecting the index `m-1` (empty when `m = 0`). -/
lemma sum_ite_eq_ofNat {n : ℕ} (m : ℕ) (hm : m < n) (w : Fin n → ℂ) :
    (∑ j : Fin n, (if (((j:ℕ):ℤ) + 1 = ((m:ℤ))) then (1:ℂ) else 0) * w j)
      = (if h : 0 < m then w ⟨m - 1, by omega⟩ else 0) := by
  by_cases h : 0 < m
  · rw [dif_pos h]
    rw [show (∑ j : Fin n, (if (((j:ℕ):ℤ) + 1 = ((m:ℤ))) then (1:ℂ) else 0) * w j)
        = ∑ j : Fin n, (if j = (⟨m-1, by omega⟩ : Fin n) then w j else 0) from
      Finset.sum_congr rfl (fun j _ => by
        by_cases hj : j = (⟨m-1, by omega⟩ : Fin n)
        · subst hj
          simp [Int.natCast_pred_of_pos h]
        · rw [if_neg hj]
          have hne : ¬ ((((j:ℕ):ℤ) + 1) = ((m:ℤ))) := by
            intro hh
            exact hj (by apply Fin.ext; change (j:ℕ) = m - 1; omega)
          rw [if_neg hne, zero_mul])]
    rw [Finset.sum_ite_eq']
    rw [if_pos (Finset.mem_univ _)]
  · rw [dif_neg h]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hne : ¬ ((((j:ℕ):ℤ) + 1) = ((m:ℤ))) := by
      intro hh
      exact h (by omega)
    rw [if_neg hne, zero_mul]

/-- The matrix-vector product of the Dirichlet (symmetric tridiagonal) matrix: the
three-term difference formula with zero boundary conditions. -/
lemma dirMat_mulVec_aux (α lam : ℝ) (θ : ℝ) (E : ℂ) (n : ℕ) (w : Fin n → ℂ) (i : Fin n) :
    ((Work.TMC16Core.dirMat α lam θ E n).mulVec w) i =
      (((Work.TMC16Core.amoPot α lam θ ((i : ℕ) : ℤ) : ℝ) : ℂ) - E) * w i
        + (if h : (i : ℕ) + 1 < n then w ⟨(i : ℕ) + 1, h⟩ else 0)
        + (if h : 0 < (i : ℕ) then w ⟨(i : ℕ) - 1, by omega⟩ else 0) := by
  rw [Matrix.mulVec, dotProduct]
  simp only [Work.TMC16Core.dirMat]
  rw [Finset.sum_congr rfl (fun j _ => by rw [add_mul, add_mul])]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [sum_ite_fin_eq i _ w, sum_ite_ofNat_eq (i:ℕ) w, sum_ite_eq_ofNat (i:ℕ) i.isLt w]

/-! ### The Poisson formula -/

theorem poisson (α lam : ℝ) (θ : ℝ) (E : ℂ) (x₁ x₂ y : ℤ) (u : ℤ → ℂ)
    (hsol : Work.TMC16Core.IsFormalSol α lam θ E u)
    (hdet : (Work.TMC16Core.dirMat α lam (θ + (x₁ : ℝ) * α) E ((x₂ - x₁ + 1).toNat)).det ≠ 0)
    (h1 : x₁ ≤ y) (h2 : y ≤ x₂) :
    u y = -(Work.TMC16Core.G α lam θ E x₁ x₂ y x₁) * u (x₁ - 1) -
          (Work.TMC16Core.G α lam θ E x₁ x₂ y x₂) * u (x₂ + 1) := by
  have hd0 : (0:ℤ) ≤ x₂ - x₁ := by omega
  have hy0 : (0:ℤ) ≤ y - x₁ := by omega
  have hxd : (((x₂ - x₁).toNat : ℕ) : ℤ) = x₂ - x₁ := Int.toNat_of_nonneg hd0
  have hyx : (((y - x₁).toNat : ℕ) : ℤ) = y - x₁ := Int.toNat_of_nonneg hy0
  have hxy : x₁ + (((y - x₁).toNat : ℕ) : ℤ) = y := by
    rw [hyx]; ring
  have hNval0 : (x₂ - x₁ + 1).toNat = (x₂ - x₁).toNat + 1 := by
    have h := Int.toNat_of_nonneg (show (0:ℤ) ≤ x₂ - x₁ + 1 by omega)
    have : (((x₂ - x₁ + 1).toNat : ℕ) : ℤ) = ((((x₂ - x₁).toNat + 1 : ℕ)) : ℤ) := by
      push_cast; omega
    exact Int.ofNat_inj.mp this
  have hNpos0 : 0 < (x₂ - x₁ + 1).toNat := by omega
  set N : ℕ := (x₂ - x₁ + 1).toNat with hNdef
  have hNval : N = (x₂ - x₁).toNat + 1 := by rw [hNdef]; exact hNval0
  have hNpos : 0 < N := by rw [hNdef]; exact hNpos0
  have hdet' : (Work.TMC16Core.dirMat α lam (θ + (x₁ : ℝ) * α) E N).det ≠ 0 := by
    rw [hNdef]; exact hdet
  have hyN : (y - x₁).toNat < N := by omega
  have hlast : (x₂ - x₁).toNat = N - 1 := by omega
  have hlastlt : N - 1 < N := by omega
  set A : Matrix (Fin N) (Fin N) ℂ := Work.TMC16Core.dirMat α lam (θ + (x₁:ℝ)*α) E N with hAdef
  set p : Fin N := ⟨0, hNpos⟩ with hpdef
  set q : Fin N := ⟨N - 1, hlastlt⟩ with hqdef
  set i0 : Fin N := ⟨(y - x₁).toNat, hyN⟩ with hi0def
  have hA : A.det ≠ 0 := hdet'
  let w : Fin N → ℂ := fun i => u (x₁ + ((i:ℕ):ℤ))
  let b : Fin N → ℂ := Pi.single p (-u (x₁ - 1)) + Pi.single q (-u (x₂ + 1))
  -- the vector of values of `u` on the interval solves the Dirichlet problem
  have hAw : A.mulVec w = b := by
    funext i
    show (Work.TMC16Core.dirMat α lam (θ + (x₁:ℝ)*α) E N).mulVec w i = b i
    rw [dirMat_mulVec_aux α lam (θ + (x₁:ℝ)*α) E N w i]
    rw [show ((Work.TMC16Core.amoPot α lam (θ + (x₁:ℝ)*α) ((i:ℕ):ℤ) : ℝ) : ℂ)
        = ((Work.TMC16Core.amoPot α lam θ (x₁ + ((i:ℕ):ℤ)) : ℝ) : ℂ) from by
      congr 1
      exact amoPot_shift α lam θ x₁ ((i:ℕ):ℤ)]
    dsimp only [w, b]
    rw [Pi.add_apply, Pi.single_apply, Pi.single_apply]
    have hsol_i : (((Work.TMC16Core.amoPot α lam θ (x₁ + ((i:ℕ):ℤ)) : ℝ) : ℂ) - E) * u (x₁ + ((i:ℕ):ℤ))
        = -u (x₁ + ((i:ℕ):ℤ) + 1) - u (x₁ + ((i:ℕ):ℤ) - 1) := by
      have h := hsol (x₁ + ((i:ℕ):ℤ))
      simp only [Work.TMC16Core.amoAct] at h
      linear_combination h
    rw [hsol_i]
    have harg1 : ∀ h : (i:ℕ)+1 < N,
        u (x₁ + ((((i:ℕ)+1 : ℕ)) : ℤ)) = u ((x₁ + ((i:ℕ):ℤ)) + 1) := by
      intro h
      congr 1
      push_cast
      ring
    have harg2 : ∀ h : 0 < (i:ℕ),
        u (x₁ + ((((i:ℕ)-1 : ℕ)) : ℤ)) = u ((x₁ + ((i:ℕ):ℤ)) - 1) := by
      intro h
      congr 1
      rw [Int.natCast_pred_of_pos h]
      ring
    by_cases h0 : (i:ℕ) = 0
    · by_cases hN1 : N = 1
      · -- the interval has a single site and `y` is that site
        have hx2 : x₂ = x₁ := by omega
        have hn : x₁ + ((i:ℕ):ℤ) = x₁ := by omega
        have hip : i = p := by
          apply Fin.ext; rw [hpdef]; exact h0
        have hiq : i = q := by
          apply Fin.ext; rw [hqdef]; change (i:ℕ) = N - 1; omega
        rw [dif_neg (by omega : ¬ ((i:ℕ)+1 < N)), dif_neg (by omega : ¬ (0 < (i:ℕ))),
            if_pos hip, if_pos hiq, hn, hx2]
        try ring
      · -- `y` is the left endpoint of an interval with at least two sites
        have hn : x₁ + ((i:ℕ):ℤ) = x₁ := by omega
        have hip : i = p := by
          apply Fin.ext; rw [hpdef]; exact h0
        have hiq : ¬ (i = q) := by
          intro hh
          have : (i:ℕ) = N - 1 := by rw [hqdef] at hh; exact congrArg Fin.val hh
          omega
        rw [dif_pos (by omega : (i:ℕ)+1 < N), harg1 (by omega : (i:ℕ)+1 < N),
            dif_neg (by omega : ¬ (0 < (i:ℕ))), if_pos hip, if_neg hiq, hn]
        try ring
    · by_cases h1 : (i:ℕ) + 1 < N
      · -- interior site
        have hip : ¬ (i = p) := by
          intro hh
          have : (i:ℕ) = 0 := by rw [hpdef] at hh; exact congrArg Fin.val hh
          exact h0 this
        have hiq : ¬ (i = q) := by
          intro hh
          have : (i:ℕ) = N - 1 := by rw [hqdef] at hh; exact congrArg Fin.val hh
          omega
        rw [dif_pos h1, harg1 h1, dif_pos (by omega : 0 < (i:ℕ)), harg2 (by omega : 0 < (i:ℕ)),
            if_neg hip, if_neg hiq]
        try ring
      · -- `y` is the right endpoint of an interval with at least two sites
        have hn : x₁ + ((i:ℕ):ℤ) = x₂ := by omega
        have hip : ¬ (i = p) := by
          intro hh
          have : (i:ℕ) = 0 := by rw [hpdef] at hh; exact congrArg Fin.val hh
          exact h0 this
        have hiq : i = q := by
          apply Fin.ext; rw [hqdef]; change (i:ℕ) = N - 1; omega
        rw [dif_neg h1, dif_pos (by omega : 0 < (i:ℕ)), harg2 (by omega : 0 < (i:ℕ)),
            if_neg hip, if_pos hiq, hn]
        try ring
  -- invert the Dirichlet matrix and read off the `y`-th entry
  have hw : w = A⁻¹.mulVec b := mulVec_eq_inv_mulVec A hA w b hAw
  have hval : w i0 = A⁻¹ i0 p * (-u (x₁ - 1)) + A⁻¹ i0 q * (-u (x₂ + 1)) := by
    have h1 := congrFun hw i0
    dsimp only [b] at h1
    rwa [inv_mulVec_single_add_apply A p q] at h1
  have hwy : w i0 = u y := by
    have hwiy : ((i0:ℕ):ℤ) = ((y - x₁).toNat : ℤ) := by simp only [hi0def]
    show u (x₁ + ((i0:ℕ):ℤ)) = u y
    rw [hwiy, hxy]
  -- identify the two relevant entries with the values of `G`
  have hG1 : Work.TMC16Core.G α lam θ E x₁ x₂ y x₁ = A⁻¹ i0 p := by
    have hc : (y - x₁).toNat < N ∧ (x₁ - x₁).toNat < N := by
      have hh : (x₁ - x₁).toNat = 0 := by simp
      exact ⟨hyN, by omega⟩
    have e1 : (⟨(y - x₁).toNat, hc.1⟩ : Fin N) = i0 := by
      rw [hi0def]
    have e2 : (⟨(x₁ - x₁).toNat, hc.2⟩ : Fin N) = p := by
      apply Fin.ext; rw [hpdef]; change (x₁ - x₁).toNat = 0; simp
    unfold Work.TMC16Core.G Work.TMC16Core.greenEntry
    rw [← hNdef, dif_pos hc, ← hAdef, e1, e2]
  have hG2 : Work.TMC16Core.G α lam θ E x₁ x₂ y x₂ = A⁻¹ i0 q := by
    have hc : (y - x₁).toNat < N ∧ (x₂ - x₁).toNat < N := ⟨hyN, by omega⟩
    have e1 : (⟨(y - x₁).toNat, hc.1⟩ : Fin N) = i0 := by
      rw [hi0def]
    have e2 : (⟨(x₂ - x₁).toNat, hc.2⟩ : Fin N) = q := by
      apply Fin.ext; rw [hqdef]; change (x₂ - x₁).toNat = N - 1; omega
    unfold Work.TMC16Core.G Work.TMC16Core.greenEntry
    rw [← hNdef, dif_pos hc, ← hAdef, e1, e2]
  rw [← hG1, ← hG2] at hval
  rw [hwy] at hval
  rw [hval]
  ring

end Work.TMC16Core.Basic
