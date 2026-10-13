/-
  WilG4c / `FibreLimitPiBasic` — index evaluations and the pullback identity for the
  general-`n` fibre-limit construction of `FibreLimitPiDefs`.
-/
import Mathlib
import Submission.Work.WilG4c.FibreLimitPiDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign
open Work.WilG0

variable {p n : ℕ}

/-! ## 1  Evaluations of the generic points -/

theorem XgenP_e (w : Fin (Wp p n) → ℝ) (ε : ℝ) : XgenP p n w ε (eIdx1 p n) = ε := by
  rw [show eIdx1 p n = Fin.last (Wp p n) from Fin.ext rfl, XgenP, Fin.snoc_last]

theorem XgenP_par (w : Fin (Wp p n) → ℝ) (ε : ℝ) (i : Fin p) :
    XgenP p n w ε (parIdx1 p n i) = w (parIdxW p n i) := by
  rw [show parIdx1 p n i = Fin.castSucc (parIdxW p n i) from Fin.ext rfl, XgenP,
    Fin.snoc_castSucc]

theorem XgenP_y0 (w : Fin (Wp p n) → ℝ) (ε : ℝ) (j : Fin (n+1)) :
    XgenP p n w ε (y0Idx1 p n j) = w (y0IdxW p n j) := by
  rw [show y0Idx1 p n j = Fin.castSucc (y0IdxW p n j) from Fin.ext rfl, XgenP,
    Fin.snoc_castSucc]

theorem XgenP_v0 (w : Fin (Wp p n) → ℝ) (ε : ℝ) :
    XgenP p n w ε (v0Idx1 p n) = w (v0IdxW p n) := by
  rw [show v0Idx1 p n = Fin.castSucc (v0IdxW p n) from Fin.ext rfl, XgenP,
    Fin.snoc_castSucc]

theorem YgenP_r (ξ : Fin (W1 p n) → ℝ) (ρ : ℝ) : YgenP p n ξ ρ (rIdx2 p n) = ρ := by
  rw [show rIdx2 p n = Fin.last (W1 p n) from Fin.ext rfl, YgenP, Fin.snoc_last]

theorem YgenP_e (ξ : Fin (W1 p n) → ℝ) (ρ : ℝ) :
    YgenP p n ξ ρ (eIdx2 p n) = ξ (eIdx1 p n) := by
  rw [show eIdx2 p n = Fin.castSucc (eIdx1 p n) from Fin.ext rfl, YgenP, Fin.snoc_castSucc]

theorem YgenP_par (ξ : Fin (W1 p n) → ℝ) (ρ : ℝ) (i : Fin p) :
    YgenP p n ξ ρ (parIdx2 p n i) = ξ (parIdx1 p n i) := by
  rw [show parIdx2 p n i = Fin.castSucc (parIdx1 p n i) from Fin.ext rfl, YgenP,
    Fin.snoc_castSucc]

theorem YgenP_y0 (ξ : Fin (W1 p n) → ℝ) (ρ : ℝ) (j : Fin (n+1)) :
    YgenP p n ξ ρ (y0Idx2 p n j) = ξ (y0Idx1 p n j) := by
  rw [show y0Idx2 p n j = Fin.castSucc (y0Idx1 p n j) from Fin.ext rfl, YgenP,
    Fin.snoc_castSucc]

theorem YgenP_v0 (ξ : Fin (W1 p n) → ℝ) (ρ : ℝ) :
    YgenP p n ξ ρ (v0Idx2 p n) = ξ (v0Idx1 p n) := by
  rw [show v0Idx2 p n = Fin.castSucc (v0Idx1 p n) from Fin.ext rfl, YgenP,
    Fin.snoc_castSucc]

/-! ## 2  Evaluations of `ZgenP` -/

theorem ZgenP_e (ξ : Fin (W2 p n) → ℝ) (x : Fin (n+1) → ℝ) (v : ℝ) :
    ZgenP p n ξ x v (eIdxP p n) = ξ (eIdx2 p n) := by
  rw [show eIdxP p n = Fin.castSucc (Fin.castAdd (n+1) (eIdx2 p n)) from Fin.ext rfl, ZgenP,
    Fin.snoc_castSucc, Fin.append_left]

theorem ZgenP_r (ξ : Fin (W2 p n) → ℝ) (x : Fin (n+1) → ℝ) (v : ℝ) :
    ZgenP p n ξ x v (rIdxP p n) = ξ (rIdx2 p n) := by
  rw [show rIdxP p n = Fin.castSucc (Fin.castAdd (n+1) (rIdx2 p n)) from Fin.ext rfl, ZgenP,
    Fin.snoc_castSucc, Fin.append_left]

theorem ZgenP_par (ξ : Fin (W2 p n) → ℝ) (x : Fin (n+1) → ℝ) (v : ℝ) (i : Fin p) :
    ZgenP p n ξ x v (parIdxP p n i) = ξ (parIdx2 p n i) := by
  rw [show parIdxP p n i = Fin.castSucc (Fin.castAdd (n+1) (parIdx2 p n i)) from Fin.ext rfl,
    ZgenP, Fin.snoc_castSucc, Fin.append_left]

theorem ZgenP_y0 (ξ : Fin (W2 p n) → ℝ) (x : Fin (n+1) → ℝ) (v : ℝ) (j : Fin (n+1)) :
    ZgenP p n ξ x v (y0IdxP p n j) = ξ (y0Idx2 p n j) := by
  rw [show y0IdxP p n j = Fin.castSucc (Fin.castAdd (n+1) (y0Idx2 p n j)) from Fin.ext rfl,
    ZgenP, Fin.snoc_castSucc, Fin.append_left]

theorem ZgenP_v0 (ξ : Fin (W2 p n) → ℝ) (x : Fin (n+1) → ℝ) (v : ℝ) :
    ZgenP p n ξ x v (v0IdxP p n) = ξ (v0Idx2 p n) := by
  rw [show v0IdxP p n = Fin.castSucc (Fin.castAdd (n+1) (v0Idx2 p n)) from Fin.ext rfl,
    ZgenP, Fin.snoc_castSucc, Fin.append_left]

theorem ZgenP_y (ξ : Fin (W2 p n) → ℝ) (x : Fin (n+1) → ℝ) (v : ℝ) (j : Fin (n+1)) :
    ZgenP p n ξ x v (yIdxP p n j) = x j := by
  rw [show yIdxP p n j = Fin.castSucc (Fin.natAdd (W2 p n) j) from Fin.ext rfl, ZgenP,
    Fin.snoc_castSucc, Fin.append_right]

theorem ZgenP_v (ξ : Fin (W2 p n) → ℝ) (x : Fin (n+1) → ℝ) (v : ℝ) :
    ZgenP p n ξ x v (vIdxP p n) = v := by
  rw [show vIdxP p n = Fin.last (W2 p n + (n+1)) from Fin.ext rfl, ZgenP, Fin.snoc_last]

/-! ## 3  The substitution map -/

theorem iotaP_par (i : Fin p) :
    iotaP p n (Fin.castSucc (Fin.castAdd (n+1) i)) = parIdxP p n i := by
  have h1 : (↑(Fin.castSucc (Fin.castAdd (n+1) i)) : ℕ) < p := by
    simp only [Fin.val_castSucc, Fin.val_castAdd]; exact i.isLt
  unfold iotaP
  rw [if_pos h1]
  apply Fin.ext
  simp only [parIdxP, Fin.val_mk, Fin.val_castSucc, Fin.val_castAdd]

theorem iotaP_y (i : Fin (n+1)) :
    iotaP p n (Fin.castSucc (Fin.natAdd p i)) = yIdxP p n i := by
  have h1 : ¬ (↑(Fin.castSucc (Fin.natAdd p i)) : ℕ) < p := by
    simp only [Fin.val_castSucc, Fin.val_natAdd]; omega
  have h2 : (↑(Fin.castSucc (Fin.natAdd p i)) : ℕ) < p + (n+1) := by
    simp only [Fin.val_castSucc, Fin.val_natAdd]; omega
  unfold iotaP
  rw [if_neg h1, if_pos h2]
  apply Fin.ext
  simp only [yIdxP, Fin.val_mk, Fin.val_castSucc, Fin.val_natAdd]
  omega

theorem iotaP_v : iotaP p n (Fin.last (p + (n+1))) = vIdxP p n := by
  have h1 : ¬ ((Fin.last (p + (n+1)) : Fin (Wp p n)) : ℕ) < p := by
    rw [Fin.val_last]; omega
  have h2 : ¬ ((Fin.last (p + (n+1)) : Fin (Wp p n)) : ℕ) < p + (n+1) := by
    rw [Fin.val_last]; omega
  unfold iotaP
  rw [if_neg h1, if_neg h2]
  rfl

/-! ## 4  The pullback identity -/

theorem pullbackP (z : Fin (NB p n) → ℝ) :
    (fun j : Fin (Wp p n) => z (iotaP p n j)) =
      Fin.snoc (Fin.append (fun i : Fin p => z (parIdxP p n i))
        (fun i : Fin (n+1) => z (yIdxP p n i))) (z (vIdxP p n)) := by
  funext j
  refine Fin.lastCases ?_ ?_ j
  · rw [Fin.snoc_last, iotaP_v]
  · intro j'
    rw [Fin.snoc_castSucc]
    refine Fin.addCases ?_ ?_ j'
    · intro i
      rw [Fin.append_left, iotaP_par]
    · intro i
      rw [Fin.append_right, iotaP_y]

/-! ## 5  `snocIt` versus `Fin.append` -/

/-- `snocIt` is the concatenation of two tuples. -/
theorem snocIt_append (m k : ℕ) (x : Fin m → ℝ) (w : Fin k → ℝ) :
    snocIt m k x w = Fin.append x w := by
  induction k with
  | zero =>
    have hw : w = Fin.elim0 := funext (fun j => j.elim0)
    rw [hw, Fin.append_elim0]
    rfl
  | succ k ih =>
    rw [show snocIt m (k+1) x w
        = Fin.snoc (snocIt m k x (Fin.init w)) (w (Fin.last k)) from rfl, ih,
      ← Fin.append_snoc x (Fin.init w) (w (Fin.last k)), Fin.snoc_init_self]

/-! ## 6  The base point `w` versus `parPt` / `cubePt` -/

theorem parIdxW_eq (i : Fin p) : parIdxW p n i = Fin.castSucc (Fin.castAdd (n+1) i) :=
  Fin.ext rfl

theorem y0IdxW_eq (j : Fin (n+1)) : y0IdxW p n j = Fin.castSucc (Fin.natAdd p j) :=
  Fin.ext rfl

theorem v0IdxW_eq : v0IdxW p n = Fin.last (p + (n+1)) := Fin.ext rfl

theorem cubePt_y0IdxW (w : Fin (Wp p n) → ℝ) (j : Fin (n+1)) :
    Work.WilkG4c.cubePt (Fin.init w) j = w (y0IdxW p n j) := by
  rw [y0IdxW_eq]; rfl

theorem parPt_parIdxW (w : Fin (Wp p n) → ℝ) (i : Fin p) :
    Work.WilkG4c.parPt (Fin.init w) i = w (parIdxW p n i) := by
  rw [parIdxW_eq]; rfl

/-! ## 7  The evaluation of `ZgenP` over a full base point -/

theorem ZgenP_pullbackP (w : Fin (Wp p n) → ℝ) (ε ρ : ℝ) (x : Fin (n+1) → ℝ) (v : ℝ) :
    (fun j : Fin (Wp p n) =>
        ZgenP p n (YgenP p n (XgenP p n w ε) ρ) x v (iotaP p n j))
      = Fin.snoc (Fin.append (Work.WilkG4c.parPt (Fin.init w)) x) v := by
  rw [pullbackP]
  congr 1
  · congr 1
    · funext i
      rw [ZgenP_par, YgenP_par, XgenP_par, parIdxW_eq]
      rfl
    · funext j
      rw [ZgenP_y]
  · rw [ZgenP_v]

attribute [simp] XgenP_e XgenP_par XgenP_y0 XgenP_v0 YgenP_r YgenP_e YgenP_par YgenP_y0
  YgenP_v0 ZgenP_e ZgenP_r ZgenP_par ZgenP_y0 ZgenP_v0 ZgenP_y ZgenP_v

end Work.WilG4c
