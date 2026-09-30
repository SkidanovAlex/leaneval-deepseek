/-
# The flip identity of the fold charts

The fold chart of a fold class `i : Fin 98` and a sign index `r : Fin (foldCodim i) → Bool` is

  `foldTheta i r = coordPerm i ∘ mobiusKlein (N_F D_r)`,

where `N_F` is the normalisation of the class, `D_r` the developing matrix and `coordPerm i` the
coordinate permutation that moves the wall coordinates to the front.

The identifications of `M̄` act on the chart by flipping the sign index: for a set `Δ` of walls, the
group element `wallSum i Δ` (the sum of the wall types) carries the piece `Dvor i r` onto the piece
`Dvor i (flipSet r Δ)` (`actX_image_Dvor`), and on the chart the flip is a reflection of the
coordinates of the walls in `Δ`.  This file proves that identity:

  `foldTheta i (flipSet r Δ) (act (wallSum i Δ).1 y) = reflCoords Δ (foldTheta i r y)`.

The proof is pure linear algebra, valid for *every* `y : E4` (the statement carries no hypothesis on
`y`).  In matrix form the identity is

  `N_F D_{flipSet r Δ} · diag(signVec (wallSum i Δ).1) = R_{ε_{flipSet r Δ}} R_{ε_r} · N_F D_r`,

which follows from the fold identity `N_F D_s k_s = R_{ε_s} N_F` of the certificate together with
the flip step `fold_state_flipSet`: `k_{flipSet r Δ} = diag(signVec (wallSum i Δ).1) · k_r` and
`ε_{flipSet r Δ} ε_r = -1` exactly at the wall positions in `Δ`.  Mapping through the Klein lift
(`hypOfKlein` is equivariant under sign changes) and through `uhsOfHyp` (a diagonal reflection of
the first three coordinates reflects the corresponding coordinates of the chart point) reduces the
identity to the combinatorial statement about `coordPerm i` and `reflCoords Δ`.
-/
import Mathlib
import Submission.Work.FoldInst.CertFlip
import Submission.Work.FoldInst.Voronoi
import Submission.Work.FoldInst.fold_state_flipSet

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

/-! ### The Klein diagonal of a `±1` vector, over `ℝ` -/

/-- The Klein diagonal `diagK k` of a `±1` vector, over `ℝ` (the real form of the representative
matrices `foldKrR`). -/
def diagKR (k : Fin 4 → ℤ) : Matrix (Fin 5) (Fin 5) ℝ := (diagK k).map (Int.castRingHom ℝ)

theorem diagKR_eq_diagonal (k : Fin 4 → ℤ) :
    diagKR k = Matrix.diagonal
      (fun i : Fin 5 => if h : (i : ℕ) < 4 then (k ⟨i, h⟩ : ℝ) else 1) := by
  ext i j
  rw [diagKR, diagK, Matrix.map_apply, Matrix.diagonal_apply, Matrix.diagonal_apply,
    Int.coe_castRingHom]
  by_cases hij : i = j
  · subst hij
    by_cases h : (i : ℕ) < 4 <;> simp [h]
  · simp [hij]

theorem diagKR_mulVec (k : Fin 4 → ℤ) (P : HypModel.V5) (i : Fin 5) :
    (diagKR k *ᵥ P) i = (if h : (i : ℕ) < 4 then (k ⟨i, h⟩ : ℝ) else 1) * P i := by
  rw [diagKR_eq_diagonal, Matrix.mulVec_diagonal]

theorem diagKR_mul (k k' : Fin 4 → ℤ) : diagKR k * diagKR k' = diagKR (k * k') := by
  rw [diagKR_eq_diagonal, diagKR_eq_diagonal, diagKR_eq_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases h : (i : ℕ) < 4 <;> simp [h, Pi.mul_apply]

theorem diagKR_one : diagKR (fun _ : Fin 4 => (1 : ℤ)) = 1 := by
  rw [diagKR_eq_diagonal]
  ext i j
  rw [Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    by_cases h : (i : ℕ) < 4 <;> simp [h]
  · simp [hij]

/-- The square of the Klein diagonal of a `±1` vector is the identity. -/
theorem diagKR_self (k : Fin 4 → ℤ) (h : ∀ i, k i = 1 ∨ k i = -1) :
    diagKR k * diagKR k = 1 := by
  rw [diagKR_mul]
  have hkk : (k * k) = fun _ : Fin 4 => (1 : ℤ) := by
    funext i
    rcases h i with hi | hi <;> simp [Pi.mul_apply, hi]
  rw [hkk, diagKR_one]

theorem diagKR_comm (k k' : Fin 4 → ℤ) : diagKR k * diagKR k' = diagKR k' * diagKR k := by
  rw [diagKR_mul, diagKR_mul]
  congr 1
  funext i
  exact mul_comm _ _

/-- A `±1` vector is recovered from the group element it encodes. -/
theorem signVec_toG {k : Fin 4 → ℤ} (h : ∀ i, k i = 1 ∨ k i = -1) : signVec (toG k) = k := by
  funext i
  rcases h i with hi | hi <;> simp [signVec, toG, hi]

/-! ### The sign reflection `R_ε` of a sign pattern -/

theorem reflEr_mul (e e' : Fin 3 → ℤ) : reflEr e * reflEr e' = reflEr (e * e') := by
  rw [reflEr, reflEr, reflEr, ← Matrix.map_mul]
  congr 1
  rw [reflE, reflE, reflE, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases h : (i : ℕ) < 3 <;> simp [h, Pi.mul_apply]

theorem reflEr_one : reflEr (fun _ : Fin 3 => (1 : ℤ)) = 1 := by
  rw [reflEr]
  simp only [reflE, Int.coe_castRingHom]
  ext i j
  rw [Matrix.map_apply, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    by_cases h3 : (i : ℕ) < 3 <;> simp [h3]
  · simp [hij]

theorem reflEr_self (e : Fin 3 → ℤ) (h : ∀ i, e i = 1 ∨ e i = -1) :
    reflEr e * reflEr e = 1 := by
  rw [reflEr_mul]
  have hee : (e * e) = fun _ : Fin 3 => (1 : ℤ) := by
    funext i
    rcases h i with hi | hi <;> simp [Pi.mul_apply, hi]
  rw [hee, reflEr_one]

/-! ### The wall positions of a representative -/

theorem f3to4_injective : Function.Injective f3to4 := by
  intro t t' h
  have h2 := congrArg Fin.val h
  have h3 : t.val = t'.val := by simpa [f3to4] using h2
  exact Fin.ext h3

lemma foldWallPosAt_eq (i : Fin 98) (t : Fin (foldCodim i)) :
    foldWallPosAt i t = foldWallPos i ⟨t.val, lt_of_lt_of_le t.isLt (foldCodim_le i)⟩ := rfl

/-- The positions of the walls of a representative are distinct. -/
theorem foldWallPosAt_injective (i : Fin 98) : Function.Injective (foldWallPosAt i) := by
  intro t t' h
  have h' : foldWallPos i ⟨t.val, lt_of_lt_of_le t.isLt (foldCodim_le i)⟩ =
      foldWallPos i ⟨t'.val, lt_of_lt_of_le t'.isLt (foldCodim_le i)⟩ := h
  have h2 := foldWallPos_injective i
    ⟨t.val, lt_of_lt_of_le t.isLt (foldCodim_le i)⟩
    ⟨t'.val, lt_of_lt_of_le t'.isLt (foldCodim_le i)⟩ t.isLt t'.isLt h'
  have h3 := congrArg Fin.val h2
  exact Fin.ext h3

/-- **The sign pattern of the flipped representative.**  The product of the sign patterns of
`flipSet r Δ` and of `r` is `-1` exactly at the wall positions of the walls in `Δ`. -/
theorem wallPat_eq (i : Fin 98) (r : Fin (foldCodim i) → Bool)
    (Δ : Finset (Fin (foldCodim i))) (j : Fin 3) :
    (foldEr i (flipSet r Δ) * foldEr i r) j =
      (if ∃ t ∈ Δ, foldWallPosAt i t = j then -1 else 1) := by
  by_cases h : ∃ t ∈ Δ, foldWallPosAt i t = j
  · rw [ite_eq_left h]
    obtain ⟨t, htΔ, htj⟩ := h
    show foldEr i (flipSet r Δ) j * foldEr i r j = -1
    rw [← htj, foldEr_flipSet_wall i r Δ t, ite_eq_left htΔ]
  · rw [ite_eq_right h]
    by_cases h2 : ∃ t : Fin (foldCodim i), foldWallPosAt i t = j
    · obtain ⟨t, ht⟩ := h2
      rw [Pi.mul_apply, ← ht, foldEr_flipSet_wall i r Δ t,
        ite_eq_right (fun htΔ => h ⟨t, htΔ, ht⟩)]
    · push Not at h2
      rw [Pi.mul_apply]
      exact foldEr_flipSet_off i r Δ j h2

/-- The set of the wall positions of the walls in `Δ`, as a subset of `Fin 4`. -/
def wallPosSet (i : Fin 98) (Δ : Finset (Fin (foldCodim i))) : Finset (Fin 4) :=
  Δ.image fun t => f3to4 (foldWallPosAt i t)

theorem mem_wallPosSet (i : Fin 98) (Δ : Finset (Fin (foldCodim i))) (j : Fin 3) :
    f3to4 j ∈ wallPosSet i Δ ↔ ∃ t ∈ Δ, foldWallPosAt i t = j := by
  rw [wallPosSet, Finset.mem_image]
  constructor
  · rintro ⟨t, ht, ht'⟩
    exact ⟨t, ht, f3to4_injective ht'⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, rfl⟩

/-- The membership in `wallPosSet` in terms of the permutation `foldTau` of the class: the inverse
`foldTau`-image of `j` lies in the wall position set exactly when `j` is in `Δ`. -/
theorem mem_wallPosSet_invFun (i : Fin 98) (Δ : Finset (Fin (foldCodim i))) {j : Fin 4}
    (hj : (j : ℕ) < foldCodim i) :
    Function.invFun (foldTau i) j ∈ wallPosSet i Δ ↔ (⟨j, hj⟩ : Fin (foldCodim i)) ∈ Δ := by
  have h3 : (j : ℕ) < 3 := by have := foldCodim_le i; omega
  have h1 : Function.invFun (foldTau i) j = f3to4 (foldWallPosAt i ⟨j, hj⟩) := by
    have h := coordPerm_invFun_wall i (⟨j.val, h3⟩ : Fin 3) hj
    have hj' : f3to4 (⟨j.val, h3⟩ : Fin 3) = j := Fin.ext rfl
    rw [hj'] at h
    rw [h]
    rfl
  rw [h1, mem_wallPosSet]
  constructor
  · rintro ⟨t, htΔ, ht⟩
    rw [foldWallPosAt_injective i ht] at htΔ
    exact htΔ
  · intro hjΔ
    exact ⟨⟨j, hj⟩, hjΔ, rfl⟩

/-! ### The Klein lift is equivariant under the sign change -/

/-- **The Klein lift under a sign change.**  For every `g : Fin 4 → ZMod 2` and every `y : E4`,
`hypOfKlein (act g y) = diag(signVec g) · hypOfKlein y`.  No hypothesis on `y` is needed: both
sides are the same linear rescaling of the same ray. -/
theorem hypOfKlein_act (g : Fin 4 → ZMod 2) (y : E4) :
    HypModel.hypOfKlein (act g y) = diagKR (signVec g) *ᵥ HypModel.hypOfKlein y := by
  ext j
  fin_cases j <;>
    simp [diagKR_mulVec, HypModel.hypOfKlein, HypModel.ray, act_apply_apply,
      one_sub_norm_sq_act g y] <;> ring

/-! ### A diagonal reflection of the first three coordinates in the upper half space model -/

/-- **A sign reflection of the first three coordinates of the hyperboloid vector reflects the
corresponding coordinates of the upper half space point.**  The last two coordinates of the vector
are untouched, so the height `P₄ − P₃` does not change. -/
theorem uhsOfHyp_reflEr (e : Fin 3 → ℤ) (Q : HypModel.V5) :
    HypModel.uhsOfHyp (reflEr e *ᵥ Q) =
      Work.Fold.e4Of (fun j => (if h : (j : ℕ) < 3 then (e ⟨j, h⟩ : ℝ) else 1)
        * HypModel.uhsOfHyp Q j) := by
  refine Work.Fold.e4_ext fun j => ?_
  rw [Work.Fold.e4Of_apply]
  by_cases hj : (j : ℕ) < 3
  · rw [dite_eq_left hj, uhsOfHyp_coord _ _ hj, uhsOfHyp_coord _ _ hj, reflEr_mulVec_apply,
      reflEr_mulVec_four, reflEr_mulVec_three, dite_eq_left hj]
    ring
  · rw [dite_eq_right hj]
    have hj3 : j = 3 := Fin.ext (by omega)
    rw [hj3, HypModel.uhsOfHyp_apply_three, HypModel.uhsOfHyp_apply_three,
      reflEr_mulVec_four, reflEr_mulVec_three]
    simp

/-- The wall form of `uhsOfHyp_reflEr`: for the sign pattern attached to `Δ`, the reflected
coordinates are exactly the coordinates in `wallPosSet i Δ`. -/
theorem uhsOfHyp_reflEr_wall (i : Fin 98) (r : Fin (foldCodim i) → Bool)
    (Δ : Finset (Fin (foldCodim i))) (Q : HypModel.V5) :
    HypModel.uhsOfHyp (reflEr (foldEr i (flipSet r Δ) * foldEr i r) *ᵥ Q) =
      Work.Fold.e4Of (fun j => (if j ∈ wallPosSet i Δ then (-1 : ℝ) else 1)
        * HypModel.uhsOfHyp Q j) := by
  rw [uhsOfHyp_reflEr]
  congr 1
  funext j
  by_cases hj : (j : ℕ) < 3
  · rw [dite_eq_left hj]
    by_cases hc : j ∈ wallPosSet i Δ
    · rw [ite_eq_left hc]
      rw [wallPat_eq i r Δ ⟨j, hj⟩,
        ite_eq_left ((mem_wallPosSet i Δ ⟨j, hj⟩).mp hc)]
      norm_num
    · rw [ite_eq_right hc]
      rw [wallPat_eq i r Δ ⟨j, hj⟩,
        ite_eq_right (fun h => hc ((mem_wallPosSet i Δ ⟨j, hj⟩).mpr h))]
      norm_num
  · rw [dite_eq_right hj]
    have hmem : j ∉ wallPosSet i Δ := by
      intro hmem
      rw [wallPosSet, Finset.mem_image] at hmem
      obtain ⟨t, -, ht⟩ := hmem
      have hval := congrArg Fin.val ht
      simp [f3to4] at hval
      omega
    rw [ite_eq_right hmem, one_mul]

/-! ### The coordinate permutation and the reflection `reflCoords` -/

/-- `reflCoords Δ` on `coordPerm i z` reflects the coordinates of `z` at the wall positions of the
walls in `Δ`. -/
theorem reflCoords_coordPerm (i : Fin 98) (Δ : Finset (Fin (foldCodim i))) (z : E4) :
    reflCoords Δ (coordPerm i z) = coordPerm i (Work.Fold.e4Of (fun j =>
      (if j ∈ wallPosSet i Δ then (-1 : ℝ) else 1) * z j)) := by
  refine Work.Fold.e4_ext fun j => ?_
  rw [reflCoords_apply, coordPerm_apply, coordPerm_apply, Work.Fold.e4Of_apply]
  by_cases hj : (j : ℕ) < foldCodim i
  · rw [dite_eq_left hj]
    by_cases hc : (⟨j, hj⟩ : Fin (foldCodim i)) ∈ Δ
    · rw [ite_eq_left hc, ite_eq_left ((mem_wallPosSet_invFun i Δ hj).mpr hc)]
    · rw [ite_eq_right hc, ite_eq_right (fun h => hc ((mem_wallPosSet_invFun i Δ hj).mp h))]
  · rw [dite_eq_right hj]
    have hnot : Function.invFun (foldTau i) j ∉ wallPosSet i Δ := by
      intro hmem
      rw [wallPosSet, Finset.mem_image] at hmem
      obtain ⟨t, -, ht⟩ := hmem
      have h2 : foldTau i (f3to4 (foldWallPosAt i t)) =
          foldTau i (Function.invFun (foldTau i) j) := by rw [ht]
      rw [foldWallPosAt_eq,
        foldTau_wall i ⟨t.val, lt_of_lt_of_le t.isLt (foldCodim_le i)⟩ t.isLt,
        Function.rightInverse_invFun (foldTau_bijective i).2] at h2
      have hval := congrArg Fin.val h2
      simp [f3to4] at hval
      omega
    rw [ite_eq_right hnot]
    simp

/-! ### The matrix identity of the flip -/

/-- **The flip step, in matrix form.**  Reading the flip step `fold_state_flipSet` through the fold
identity `N_F D_s k_s = R_{ε_s} N_F`, the normalisation of the flipped representative differs from
that of `r` by the sign reflection of the walls in `Δ`:

  `N_F D_{flipSet r Δ} · diag(signVec (wallSum i Δ).1) = R_{ε_{flipSet r Δ} ε_r} · N_F D_r`. -/
theorem foldNr_mul_D_flip_mul (i : Fin 98) (r : Fin (foldCodim i) → Bool)
    (Δ : Finset (Fin (foldCodim i))) :
    foldNr i * foldDrR i (flipSet r Δ) * diagKR (signVec (wallSum i Δ).1) =
      reflEr (foldEr i (flipSet r Δ) * foldEr i r) * (foldNr i * foldDrR i r) := by
  have hKss : foldKrR i (flipSet r Δ) * foldKrR i (flipSet r Δ) = 1 :=
    diagKR_self (foldKr i (flipSet r Δ)) (fun j => foldRepK_pm i (foldRepOf i (flipSet r Δ)) j)
  have hKrr : foldKrR i r * foldKrR i r = 1 :=
    diagKR_self (foldKr i r) (fun j => foldRepK_pm i (foldRepOf i r) j)
  have hDg : diagKR (signVec (wallSum i Δ).1) * diagKR (signVec (wallSum i Δ).1) = 1 := by
    refine diagKR_self _ (fun j => ?_)
    by_cases h : (wallSum i Δ).1 j = 0 <;> simp [signVec, h]
  have hRrr : reflEr (foldEr i r) * reflEr (foldEr i r) = 1 :=
    reflEr_self _ (fun j => foldRepEps_pm i (foldRepOf i r) j)
  have hNDs : foldNr i * foldDrR i (flipSet r Δ) =
      reflEr (foldEr i (flipSet r Δ)) * (foldNr i * foldKrR i (flipSet r Δ)) := by
    have h := congrArg (fun M => M * foldKrR i (flipSet r Δ))
      (foldNr_mul_D_mul_K i (flipSet r Δ))
    simp only [Matrix.mul_assoc, hKss, Matrix.mul_one] at h
    exact h
  have hNDr : foldNr i * foldDrR i r = reflEr (foldEr i r) * (foldNr i * foldKrR i r) := by
    have h := congrArg (fun M => M * foldKrR i r) (foldNr_mul_D_mul_K i r)
    simp only [Matrix.mul_assoc, hKrr, Matrix.mul_one] at h
    exact h
  have hKr : foldKrR i (flipSet r Δ) =
      diagKR (signVec (wallSum i Δ).1) * foldKrR i r := by
    have hgen : foldKr i (flipSet r Δ) = signVec (wallSum i Δ).1 * foldKr i r := by
      have h1 : signVec (toG (foldKr i (flipSet r Δ))) = foldKr i (flipSet r Δ) :=
        signVec_toG (fun j => foldRepK_pm i (foldRepOf i (flipSet r Δ)) j)
      have h2 : signVec (toG (foldKr i r)) = foldKr i r :=
        signVec_toG (fun j => foldRepK_pm i (foldRepOf i r) j)
      have h3 : toG (foldKr i (flipSet r Δ)) = (wallSum i Δ).1 + toG (foldKr i r) := by
        simpa using congrArg Prod.fst (fold_state_flipSet i r Δ)
      calc foldKr i (flipSet r Δ) = signVec (toG (foldKr i (flipSet r Δ))) := h1.symm
        _ = signVec ((wallSum i Δ).1 + toG (foldKr i r)) := by rw [h3]
        _ = signVec (wallSum i Δ).1 * signVec (toG (foldKr i r)) := signVec_add _ _
        _ = signVec (wallSum i Δ).1 * foldKr i r := by rw [h2]
    show diagKR (foldKr i (flipSet r Δ)) =
      diagKR (signVec (wallSum i Δ).1) * diagKR (foldKr i r)
    rw [hgen, diagKR_mul]
  have hKD : foldKrR i (flipSet r Δ) * diagKR (signVec (wallSum i Δ).1) = foldKrR i r := by
    rw [hKr]
    calc (diagKR (signVec (wallSum i Δ).1) * foldKrR i r) * diagKR (signVec (wallSum i Δ).1)
        = diagKR (signVec (wallSum i Δ).1) *
            (foldKrR i r * diagKR (signVec (wallSum i Δ).1)) := Matrix.mul_assoc _ _ _
      _ = diagKR (signVec (wallSum i Δ).1) *
            (diagKR (signVec (wallSum i Δ).1) * foldKrR i r) := by
          rw [show foldKrR i r * diagKR (signVec (wallSum i Δ).1) =
              diagKR (signVec (wallSum i Δ).1) * foldKrR i r from diagKR_comm (foldKr i r) _]
      _ = (diagKR (signVec (wallSum i Δ).1) * diagKR (signVec (wallSum i Δ).1)) *
            foldKrR i r := (Matrix.mul_assoc _ _ _).symm
      _ = foldKrR i r := by rw [hDg, one_mul]
  have hL : foldNr i * foldDrR i (flipSet r Δ) * diagKR (signVec (wallSum i Δ).1)
      = reflEr (foldEr i (flipSet r Δ)) * (foldNr i * foldKrR i r) := by
    rw [hNDs]
    simp only [Matrix.mul_assoc]
    rw [hKD]
  have hR : reflEr (foldEr i (flipSet r Δ) * foldEr i r) * (foldNr i * foldDrR i r)
      = reflEr (foldEr i (flipSet r Δ)) * (foldNr i * foldKrR i r) := by
    rw [← reflEr_mul, hNDr]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (reflEr (foldEr i r)) (reflEr (foldEr i r))
      (foldNr i * foldKrR i r), hRrr, one_mul]
  exact hL.trans hR.symm

/-! ### The flip identity of the chart -/

theorem foldTheta_flip (i : Fin 98) (r : Fin (foldCodim i) → Bool)
    (Δ : Finset (Fin (foldCodim i))) (y : E4) :
    foldTheta i (flipSet r Δ) (act (wallSum i Δ).1 y) = reflCoords Δ (foldTheta i r y) := by
  have hvec : (foldNr i * foldDrR i (flipSet r Δ)) *ᵥ
        HypModel.hypOfKlein (act (wallSum i Δ).1 y)
      = reflEr (foldEr i (flipSet r Δ) * foldEr i r)
          *ᵥ ((foldNr i * foldDrR i r) *ᵥ HypModel.hypOfKlein y) := by
    rw [hypOfKlein_act (wallSum i Δ).1 y, Matrix.mulVec_mulVec, foldNr_mul_D_flip_mul,
      Matrix.mulVec_mulVec]
  calc foldTheta i (flipSet r Δ) (act (wallSum i Δ).1 y)
      = coordPerm i (HypModel.uhsOfHyp (reflEr (foldEr i (flipSet r Δ) * foldEr i r)
          *ᵥ ((foldNr i * foldDrR i r) *ᵥ HypModel.hypOfKlein y))) := by
        rw [foldTheta, HypModel.mobiusKlein, hvec]
    _ = coordPerm i (Work.Fold.e4Of fun j => (if j ∈ wallPosSet i Δ then (-1 : ℝ) else 1)
          * HypModel.uhsOfHyp ((foldNr i * foldDrR i r) *ᵥ HypModel.hypOfKlein y) j) := by
        rw [uhsOfHyp_reflEr_wall]
    _ = reflCoords Δ (coordPerm i (HypModel.uhsOfHyp
          ((foldNr i * foldDrR i r) *ᵥ HypModel.hypOfKlein y))) :=
        (reflCoords_coordPerm i Δ _).symm
    _ = reflCoords Δ (foldTheta i r y) := rfl

end Work.FoldInst
