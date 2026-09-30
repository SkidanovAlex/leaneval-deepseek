/-
# Injectivity of the fold charts on the Klein ball

The chart map of the fold class `i : Fin 98` and the sign index `r` is

  `foldTheta i r y = coordPerm i (mobiusKlein (N_F · D_r) y)`

(`FoldPiece.lean`): the coordinate permutation `coordPerm i` reindexes the model coordinates of
the Möbius image of the Klein point `y` under the developing matrix `N_F · D_r`.

This file proves that this map is **injective on the open unit ball** — the `hcross` field of the
blueprint's FOLD area in its pointwise form.  The argument is a chain of three injectivities:

* `coordPerm i` is injective, because it reindexes coordinates by the *bijective* permutation
  `foldTau i` (`foldTau_bijective`);
* for any `IsLorentzMat A` the Klein action `mobiusKlein A` is injective on the ball: two points of
  the ball with the same image have the same image under the *upper sheet lift* `hypOfKlein` after
  applying `A` (since `uhsOfHyp` retracts onto the upper sheet by `hypOfKUHS`), and `A` is
  left-invertible by `J · Aᵀ · J` because `Aᵀ J A = J`;
* `N_F · D_r` is a Lorentz matrix.  `N_F` is one by the certificate `foldN2_lorentz`, and the
  developing matrix is reached from the fold identity `N_F D_r k_r = R_{ε_r} N_F`
  (`foldNr_mul_D_mul_K`): since `k_r` and `R_{ε_r}` are Lorentz diagonal matrices with entries
  `±1`, so is their product expression for `N_F D_r`.
-/
import Mathlib
import Submission.Work.FoldInst.CertFlip
import Submission.Work.FoldInst.Voronoi

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Matrix
open scoped Matrix

namespace Work.FoldInst

/-! ### Diagonal Lorentz matrices with `±1` entries -/

/-- A diagonal matrix whose entries are all `±1` and whose last entry is positive is a Lorentz
matrix preserving the upper sheet. -/
theorem foldInst_diag_lorentz {d : Fin 5 → ℝ} (hd : ∀ i, d i * d i = 1) (hd4 : 0 < d 4) :
    HypModel.IsLorentzMat (Matrix.diagonal d) := by
  constructor
  · have ht : (Matrix.diagonal d)ᵀ = Matrix.diagonal d := by
      ext a b
      by_cases hab : a = b
      · subst hab; simp
      · simp [hab, Ne.symm hab]
    calc (Matrix.diagonal d)ᵀ * HypModel.J * Matrix.diagonal d
        = Matrix.diagonal d * Matrix.diagonal (fun i => if i = 4 then (-1:ℝ) else 1)
            * Matrix.diagonal d := by
          rw [ht, HypModel.J]
      _ = Matrix.diagonal (fun i => d i * (if i = 4 then (-1:ℝ) else 1)) * Matrix.diagonal d := by
          rw [Matrix.diagonal_mul_diagonal]
      _ = Matrix.diagonal (fun i => (d i * (if i = 4 then (-1:ℝ) else 1)) * d i) := by
          rw [Matrix.diagonal_mul_diagonal]
      _ = Matrix.diagonal (fun i => if i = 4 then (-1:ℝ) else 1) := by
          congr 1; ext i
          have h : d i ^ 2 = 1 := by rw [sq, hd i]
          ring_nf
          rw [h, one_mul]
      _ = HypModel.J := by rw [HypModel.J]
  · show (0:ℝ) < Matrix.diagonal d 4 4
    rw [Matrix.diagonal_apply_eq]
    exact hd4

/-- A diagonal matrix whose entries are all `±1` is its own inverse. -/
theorem foldInst_diagonal_self_mul {d : Fin 5 → ℝ} (hd : ∀ i, d i * d i = 1) :
    Matrix.diagonal d * Matrix.diagonal d = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  have : (fun i : Fin 5 => d i * d i) = (fun _ => 1) := by funext i; exact hd i
  rw [this, Matrix.diagonal_one]

/-! ### The Klein diagonal `k_r` of the representative

`foldKrR i r = diag(k₀,k₁,k₂,k₃,1)` with `k_t = ±1` (`foldRepK_pm`). -/

theorem foldInst_foldKrR_eq_diagonal (i : Fin 98) (r : Fin (foldCodim i) → Bool) :
    foldKrR i r = Matrix.diagonal (fun j : Fin 5 =>
      if h : (j : ℕ) < 4 then (foldKr i r ⟨j, h⟩ : ℝ) else 1) := by
  ext a b
  simp only [foldKrR, diagK, Matrix.map_apply, Matrix.diagonal_apply, Int.coe_castRingHom]
  by_cases hab : a = b
  · subst hab; by_cases h4 : (a : ℕ) < 4 <;> simp [h4]
  · simp [hab]

theorem foldInst_foldKrR_entry_self (i : Fin 98) (r : Fin (foldCodim i) → Bool) :
    ∀ j : Fin 5, (if h : (j : ℕ) < 4 then (foldKr i r ⟨j, h⟩ : ℝ) else 1)
      * (if h : (j : ℕ) < 4 then (foldKr i r ⟨j, h⟩ : ℝ) else 1) = 1 := by
  intro j
  by_cases h4 : (j : ℕ) < 4
  · rw [dite_eq_left h4]
    simp only [foldKr]
    rcases foldRepK_pm i (foldRepOf i r) ⟨j, h4⟩ with h | h <;> rw [h] <;> norm_num
  · rw [dite_eq_right h4]; norm_num

theorem foldInst_foldKrR_isLorentz (i : Fin 98) (r : Fin (foldCodim i) → Bool) :
    HypModel.IsLorentzMat (foldKrR i r) := by
  rw [foldInst_foldKrR_eq_diagonal]
  refine foldInst_diag_lorentz (foldInst_foldKrR_entry_self i r) ?_
  rw [dite_eq_right (by norm_num : ¬ ((4:Fin 5):ℕ) < 4)]; norm_num

theorem foldInst_foldKrR_mul_self (i : Fin 98) (r : Fin (foldCodim i) → Bool) :
    foldKrR i r * foldKrR i r = 1 := by
  rw [foldInst_foldKrR_eq_diagonal]
  exact foldInst_diagonal_self_mul (foldInst_foldKrR_entry_self i r)

/-! ### The reflection matrix `R_{ε_r}`

`reflEr e = diag(e₀,e₁,e₂,1,1)` with `e_t = ±1` (`foldRepEps_pm`). -/

theorem foldInst_reflEr_eq_diagonal (e : Fin 3 → ℤ) :
    reflEr e = Matrix.diagonal (fun i : Fin 5 =>
      if h : (i : ℕ) < 3 then (e ⟨i, h⟩ : ℝ) else 1) := by
  ext a b
  simp only [reflEr, reflE, Matrix.map_apply, Matrix.diagonal_apply, Int.coe_castRingHom]
  by_cases hab : a = b
  · subst hab; by_cases h3 : (a : ℕ) < 3 <;> simp [h3]
  · simp [hab]

theorem foldInst_foldEr_pm (i : Fin 98) (r : Fin (foldCodim i) → Bool) :
    ∀ j : Fin 3, foldEr i r j = 1 ∨ foldEr i r j = -1 := by
  intro j
  simpa [foldEr] using foldRepEps_pm i (foldRepOf i r) j

theorem foldInst_reflEr_isLorentz (e : Fin 3 → ℤ) (he : ∀ j, e j = 1 ∨ e j = -1) :
    HypModel.IsLorentzMat (reflEr e) := by
  rw [foldInst_reflEr_eq_diagonal]
  refine foldInst_diag_lorentz (fun j => ?_) ?_
  · by_cases h3 : (j : ℕ) < 3
    · rw [dite_eq_left h3]
      rcases he ⟨j, h3⟩ with h | h <;> simp [h]
    · rw [dite_eq_right h3]; norm_num
  · rw [dite_eq_right (by norm_num : ¬ ((4:Fin 5):ℕ) < 3)]; norm_num

/-! ### The developing matrix `N_F · D_r` is Lorentz -/

/-- **`N_F · D_r` is a Lorentz matrix.**  The fold identity `N_F D_r k_r = R_{ε_r} N_F`
(`foldNr_mul_D_mul_K`) rewrites it, using `k_r² = 1`, as the product
`R_{ε_r} · N_F · k_r` of Lorentz matrices. -/
theorem foldInst_foldNr_mul_foldDrR_isLorentz (i : Fin 98) (r : Fin (foldCodim i) → Bool) :
    HypModel.IsLorentzMat (foldNr i * foldDrR i r) := by
  have h1 := foldNr_mul_D_mul_K i r
  have h4 : foldNr i * foldDrR i r = foldNr i * foldDrR i r * foldKrR i r * foldKrR i r := by
    rw [mul_assoc, foldInst_foldKrR_mul_self i r, mul_one]
  have h3 : foldNr i * foldDrR i r * foldKrR i r * foldKrR i r
      = reflEr (foldEr i r) * foldNr i * foldKrR i r :=
    congrArg (fun M => M * foldKrR i r) h1
  rw [h4, h3]
  exact HypModel.IsLorentzMat.mul
    (HypModel.IsLorentzMat.mul (foldInst_reflEr_isLorentz _ (foldInst_foldEr_pm i r))
      (FoldThetaOrthantAux.foldNr_isLorentz i))
    (foldInst_foldKrR_isLorentz i r)

/-! ### Injectivity of the coordinate permutation -/

/-- `coordPerm i` reindexes the model coordinates by the permutation `foldTau i`, which is
bijective, so it is injective. -/
theorem foldInst_coordPerm_injective (i : Fin 98) : Function.Injective (coordPerm i) := by
  intro y y' h
  ext k
  have hσ : Function.invFun (foldTau i) (foldTau i k) = k :=
    Function.leftInverse_invFun (foldTau_bijective i).1 k
  have h2 : (coordPerm i y).ofLp (foldTau i k) = (coordPerm i y').ofLp (foldTau i k) :=
    congrFun (congrArg WithLp.ofLp h) (foldTau i k)
  rw [coordPerm_apply, coordPerm_apply, hσ] at h2
  simpa using h2

/-! ### The Klein action of a Lorentz matrix is injective on the ball -/

theorem foldInst_J_self_mul : HypModel.J * HypModel.J = 1 := by
  rw [HypModel.J, Matrix.diagonal_mul_diagonal]
  have h : (fun i : Fin 5 => (if i = 4 then (-1:ℝ) else 1) * (if i = 4 then (-1:ℝ) else 1))
      = (fun _ => 1) := by
    funext i; by_cases h : i = 4 <;> simp [h]
  rw [h, Matrix.diagonal_one]

/-- **A matrix with `Aᵀ J A = J` is injective as a linear map.**  Its left inverse is
`J Aᵀ J`, because `(J Aᵀ J) A = J (Aᵀ J A) = J² = 1`. -/
theorem foldInst_mulVec_injective_of_isometry {A : Matrix (Fin 5) (Fin 5) ℝ}
    (hA : Aᵀ * HypModel.J * A = HypModel.J) : Function.Injective A.mulVec := by
  have hBA : (HypModel.J * Aᵀ * HypModel.J) * A = 1 := by
    calc (HypModel.J * Aᵀ * HypModel.J) * A
        = HypModel.J * (Aᵀ * HypModel.J * A) := by noncomm_ring
      _ = HypModel.J * HypModel.J := by rw [hA]
      _ = 1 := foldInst_J_self_mul
  intro w w' hw
  have h' := congrArg (fun x => (HypModel.J * Aᵀ * HypModel.J).mulVec x) hw
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec, Matrix.one_mulVec] at h'
  exact h'

/-- **The Klein action `mobiusKlein A` of a Lorentz matrix is injective on the ball.**

If `mobiusKlein A y = mobiusKlein A z`, then applying the upper half space inverse `hypOfUHS` to
both sides (legitimate because `A` preserves the upper sheet, so both `A·hypOfKlein y` and
`A·hypOfKlein z` lie there) gives `A·hypOfKlein y = A·hypOfKlein z`.  The linear map `A` is
injective (`foldInst_mulVec_injective_of_isometry`), and `hypOfKlein` is injective on the ball. -/
theorem foldInst_mobiusKlein_injOn_ball {A : Matrix (Fin 5) (Fin 5) ℝ}
    (hA : HypModel.IsLorentzMat A) :
    Set.InjOn (HypModel.mobiusKlein A) HypModel.ball := by
  have hc := foldInst_mulVec_injective_of_isometry hA.1
  intro y hy z hz h
  have hAy := HypModel.isLorentzMat_mem_upperSheet hA (HypModel.hypOfKlein_mem_upperSheet hy)
  have hAz := HypModel.isLorentzMat_mem_upperSheet hA (HypModel.hypOfKlein_mem_upperSheet hz)
  have hPQ : A.mulVec (HypModel.hypOfKlein y) = A.mulVec (HypModel.hypOfKlein z) := by
    have h1 : HypModel.hypOfUHS (HypModel.uhsOfHyp (A.mulVec (HypModel.hypOfKlein y)))
        = HypModel.hypOfUHS (HypModel.uhsOfHyp (A.mulVec (HypModel.hypOfKlein z))) := by
      have h2 := congrArg HypModel.hypOfUHS h
      simpa [HypModel.mobiusKlein] using h2
    rwa [HypModel.hypOfUHS_uhsOfHyp hAy, HypModel.hypOfUHS_uhsOfHyp hAz] at h1
  exact HypModel.hypOfKlein_injOn hy hz (hc hPQ)

/-! ### The target -/

/-- **The fold chart of the class `i` and the sign index `r` is injective on the Klein ball.**
`foldTheta i r = coordPerm i ∘ mobiusKlein (N_F D_r)` is a composite of injective maps: the
coordinate permutation (`foldInst_coordPerm_injective`), the Klein action of the Lorentz matrix
`N_F D_r` (`foldInst_mobiusKlein_injOn_ball`, `foldInst_foldNr_mul_foldDrR_isLorentz`). -/
theorem foldTheta_injOn (i : Fin 98) (r : Fin (foldCodim i) → Bool) :
    Set.InjOn (foldTheta i r) HypModel.ball := by
  have hc := foldInst_coordPerm_injective i
  have hmob := foldInst_mobiusKlein_injOn_ball (foldInst_foldNr_mul_foldDrR_isLorentz i r)
  intro y hy z hz h
  exact hmob hy hz (hc (by simpa [foldTheta] using h))

end Work.FoldInst
