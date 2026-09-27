import Mathlib
import Submission.Work.Mostow.euclidBlockDefs
import Submission.Work.Mostow.ellipticDefs
import Submission.Work.Mostow.vblk_add_smul
import Submission.Work.Mostow.blkMap_linBlk

/-!
# `Work.Mostow.strataAdaptFold`

The linear block map `linBlk k m R` on `E (k + m)` keeps the first `k` coordinates and applies `R`
to the last `m`.  The statement proved here is the compatibility of the *folded* description with
the *adapted* (value split) description: if the same map is written with the split at `k + d`
(keeping the first `k + d` coordinates and applying `T` to the last `m - d`), then it agrees with
`linBlk k m Tb` on `E (k + m)` **iff** the block `Tb` is the value-split block
`vblk d hd T` on `E m`.

The proof is a coordinate computation.  A vector of `E (k + m)` is determined by its tangential
part `tanC k m` and its normal part `nrmC k m` (`Work.Mostow.eq_of_tanC_nrmC'`), and the
`tanC`/`nrmC` of the block maps are computed in `Work.Mostow.linBlk_tanC`,
`Work.Mostow.linBlk_nrmC` and the lemmas `vblkD_tanC`/`vblkD_nrmC` below.
-/

namespace Work.Mostow

open Submission.Mostow

noncomputable section

/-! ### Coordinates of a transported vector -/

private lemma cast_ofLp {m n : ℕ} (e : m = n) (x : E m) (i : Fin n) :
    (e ▸ x : E n).ofLp i = x.ofLp (Fin.cast e.symm i) := by
  cases e; rfl

private lemma linBlk_ofLp_castAdd (k m : ℕ) (R : E m ≃ₗᵢ[ℝ] E m) (u : E (k + m))
    (i : Fin k) : (linBlk k m R u).ofLp (Fin.castAdd m i) = u.ofLp (Fin.castAdd m i) := by
  simp [linBlk, Fin.append_left]

private lemma linBlk_ofLp_natAdd (k m : ℕ) (R : E m ≃ₗᵢ[ℝ] E m) (u : E (k + m))
    (i : Fin m) : (linBlk k m R u).ofLp (Fin.natAdd k i) = (R (nrmC k m u)).ofLp i := by
  simp [linBlk, nrmC, Fin.append_right]

private lemma linBlk_ofLp_of_lt (k m : ℕ) (R : E m ≃ₗᵢ[ℝ] E m) (u : E (k + m))
    (i : Fin (k + m)) (h : (i : ℕ) < k) : (linBlk k m R u).ofLp i = u.ofLp i := by
  have h1 := linBlk_ofLp_castAdd k m R u ⟨i.val, h⟩
  have hidx : Fin.castAdd m ⟨i.val, h⟩ = i := Fin.ext rfl
  rwa [hidx] at h1

private lemma linBlk_ofLp_of_ge (k m : ℕ) (R : E m ≃ₗᵢ[ℝ] E m) (u : E (k + m))
    (i : Fin (k + m)) (h : ¬ (i : ℕ) < k) :
    (linBlk k m R u).ofLp i = (R (nrmC k m u)).ofLp ⟨i.val - k, by have := i.isLt; omega⟩ := by
  have hk : k ≤ i.val := Nat.le_of_not_lt h
  have h1 := linBlk_ofLp_natAdd k m R u ⟨i.val - k, by omega⟩
  have hidx : Fin.natAdd k ⟨i.val - k, by omega⟩ = i :=
    Fin.ext (by simp only [Fin.val_natAdd]; omega)
  rwa [hidx] at h1

/-! ### Coordinates of `tanC` and `nrmC` -/

private lemma tanC_ofLp (k m : ℕ) (u : E (k + m)) (i : Fin k) :
    (tanC k m u).ofLp i = u.ofLp (Fin.castAdd m i) := rfl

private lemma nrmC_ofLp (k m : ℕ) (u : E (k + m)) (j : Fin m) :
    (nrmC k m u).ofLp j = u.ofLp (Fin.natAdd k j) := rfl

/-! ### The value-split block map with the split at `k + d` -/

/-- The tail of `u : E (k + m)` from coordinate `k + d` on, as an element of `E (m - d)`. -/
private def tailD (k d m : ℕ) (u : E (k + m)) : E (m - d) :=
  WithLp.toLp 2 (fun j : Fin (m - d) => u ⟨k + d + j.val, by have := j.isLt; omega⟩)

/-- Keep the first `k + d` coordinates of `u : E (k + m)` and apply `T` to the last `m - d`. -/
private def vblkD (k d m : ℕ) (_hd : d ≤ m) (T : E (m - d) ≃ₗᵢ[ℝ] E (m - d))
    (u : E (k + m)) : E (k + m) :=
  WithLp.toLp 2 (fun i : Fin (k + m) =>
    if h : (i : ℕ) < k + d then u i
    else (T (tailD k d m u)) ⟨i.val - (k + d), by have := i.isLt; omega⟩)

private lemma tailD_ofLp (k d m : ℕ) (u : E (k + m)) (j : Fin (m - d)) :
    (tailD k d m u).ofLp j = u.ofLp ⟨k + d + j.val, by have := j.isLt; omega⟩ := rfl

private lemma vblkD_apply_lt (k d m : ℕ) (hd : d ≤ m) (T : E (m - d) ≃ₗᵢ[ℝ] E (m - d))
    (u : E (k + m)) (i : Fin (k + m)) (h : (i : ℕ) < k + d) :
    (vblkD k d m hd T u).ofLp i = u.ofLp i := by
  simp [vblkD, h]

private lemma vblkD_apply_ge (k d m : ℕ) (hd : d ≤ m) (T : E (m - d) ≃ₗᵢ[ℝ] E (m - d))
    (u : E (k + m)) (i : Fin (k + m)) (h : ¬ (i : ℕ) < k + d) :
    (vblkD k d m hd T u).ofLp i
      = (T (tailD k d m u)).ofLp ⟨i.val - (k + d), by have := i.isLt; omega⟩ := by
  simp [vblkD, h]

private lemma vblkD_tanC (k d m : ℕ) (hd : d ≤ m) (T : E (m - d) ≃ₗᵢ[ℝ] E (m - d))
    (u : E (k + m)) : tanC k m (vblkD k d m hd T u) = tanC k m u := by
  ext i
  rw [tanC_ofLp, tanC_ofLp,
    vblkD_apply_lt k d m hd T u (Fin.castAdd m i) (by rw [Fin.val_castAdd]; omega)]

private lemma tailD_eq_tailOf (k d m : ℕ) (u : E (k + m)) :
    tailD k d m u = tailOf d (nrmC k m u) := by
  apply WithLp.ofLp_injective
  funext j
  rw [tailD_ofLp, tailOf_ofLp, nrmC_ofLp]
  exact congrArg u.ofLp (Fin.ext (by simp only [Fin.val_natAdd]; omega))

private lemma vblkD_nrmC (k d m : ℕ) (hd : d ≤ m) (T : E (m - d) ≃ₗᵢ[ℝ] E (m - d))
    (u : E (k + m)) : nrmC k m (vblkD k d m hd T u) = vblk d hd T (nrmC k m u) := by
  apply WithLp.ofLp_injective
  funext j
  rw [nrmC_ofLp]
  by_cases hj : (j : ℕ) < d
  · rw [vblkD_apply_lt k d m hd T u (Fin.natAdd k j) (by rw [Fin.val_natAdd]; omega),
      vblk_ofLp_of_lt d hd T (nrmC k m u) j hj, nrmC_ofLp]
  · rw [vblkD_apply_ge k d m hd T u (Fin.natAdd k j) (by rw [Fin.val_natAdd]; omega),
      vblk_ofLp_of_ge d hd T (nrmC k m u) j hj, tailD_eq_tailOf]
    exact congrArg (fun idx : Fin (m - d) => (T (tailOf d (nrmC k m u))).ofLp idx)
      (Fin.ext (by simp only [Fin.val_natAdd]; omega))

/-! ### Removing the cast -/

private lemma nrmC_tailD_cast (k d m : ℕ) (e : (k + d) + (m - d) = k + m) (u : E (k + m)) :
    nrmC (k + d) (m - d) (e.symm ▸ u) = tailD k d m u := by
  apply WithLp.ofLp_injective
  funext j
  rw [nrmC_ofLp]
  show (e.symm ▸ u).ofLp (Fin.natAdd (k + d) j) = (tailD k d m u).ofLp j
  rw [cast_ofLp, tailD_ofLp]
  exact congrArg u.ofLp (Fin.ext (by simp only [Fin.val_cast, Fin.val_natAdd]))

private lemma cast_linBlk_eq_vblkD (k d m : ℕ) (hd : d ≤ m) (e : (k + d) + (m - d) = k + m)
    (T : E (m - d) ≃ₗᵢ[ℝ] E (m - d)) (u : E (k + m)) :
    (e ▸ linBlk (k + d) (m - d) T (e.symm ▸ u) : E (k + m)) = vblkD k d m hd T u := by
  apply WithLp.ofLp_injective
  funext i
  rw [cast_ofLp]
  by_cases hi : (i : ℕ) < k + d
  · rw [linBlk_ofLp_of_lt (k + d) (m - d) T (e.symm ▸ u) (Fin.cast e.symm i)
      (by rw [Fin.val_cast]; exact hi), cast_ofLp,
      vblkD_apply_lt k d m hd T u i hi]
    exact congrArg u.ofLp (Fin.ext rfl)
  · rw [linBlk_ofLp_of_ge (k + d) (m - d) T (e.symm ▸ u) (Fin.cast e.symm i)
      (by rw [Fin.val_cast]; exact hi), vblkD_apply_ge k d m hd T u i hi,
      nrmC_tailD_cast k d m e u]
    exact congrArg (fun idx : Fin (m - d) => (T (tailD k d m u)).ofLp idx)
      (Fin.ext (by simp only [Fin.val_cast]))

/-! ### The normal embedding -/

private def normalEmb (k m : ℕ) (y : E m) : E (k + m) :=
  WithLp.toLp 2 (Fin.append (fun _ : Fin k => (0 : ℝ)) y)

private lemma nrmC_normalEmb (k m : ℕ) (y : E m) : nrmC k m (normalEmb k m y) = y := by
  apply WithLp.ofLp_injective
  funext j
  rw [nrmC_ofLp]
  show (normalEmb k m y).ofLp (Fin.natAdd k j) = y.ofLp j
  rw [show (normalEmb k m y).ofLp (Fin.natAdd k j)
      = (normalEmb k m y) (Fin.natAdd k j) from rfl]
  simp [normalEmb, Fin.append_right]

theorem strataAdaptFold (k d m : ℕ) (hd : d ≤ m) (e : (k + d) + (m - d) = k + m)
    (T : Submission.Mostow.E (m - d) ≃ₗᵢ[ℝ] Submission.Mostow.E (m - d))
    (Tb : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m) :
    (∀ x : Submission.Mostow.E (k + m),
        (e ▸ (Work.Mostow.linBlk (k + d) (m - d) T (e.symm ▸ x)) : Submission.Mostow.E (k + m))
          = Work.Mostow.linBlk k m Tb x)
      ↔ (∀ y : Submission.Mostow.E m, Tb y = Work.Mostow.vblk d hd T y) := by
  have key : ∀ x : E (k + m),
      (e ▸ (linBlk (k + d) (m - d) T (e.symm ▸ x)) : E (k + m)) = vblkD k d m hd T x :=
    fun x => cast_linBlk_eq_vblkD k d m hd e T x
  constructor
  · intro h y
    have hx : vblkD k d m hd T (normalEmb k m y) = linBlk k m Tb (normalEmb k m y) := by
      rw [← key (normalEmb k m y)]
      exact h (normalEmb k m y)
    have h2 := congrArg (fun v => nrmC k m v) hx
    rw [linBlk_nrmC, vblkD_nrmC, nrmC_normalEmb] at h2
    exact h2.symm
  · intro hTb x
    rw [key x]
    refine eq_of_tanC_nrmC' ?_ ?_
    · rw [vblkD_tanC, linBlk_tanC]
    · rw [vblkD_nrmC, linBlk_nrmC]
      exact (hTb (nrmC k m x)).symm

end

end Work.Mostow
