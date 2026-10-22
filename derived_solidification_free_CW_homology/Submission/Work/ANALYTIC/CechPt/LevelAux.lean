import Mathlib
import Submission.Work.ANALYTIC.CechPt.LevelDefs

/-!
# Auxiliary combinatorics of the level-`n` dyadic nerve

This file collects the definitions and elementary lemmas used in the proof of
`Work.ANALYTIC.CechPt.level_acyclic` (the acyclicity of the cochain complex of the level-`n`
dyadic nerve of the interval, `Submission/Work/ANALYTIC/CechPt/LevelDefs.lean`).

The main tool is the explicit simplicial retraction `rhoV` of the `N`-vertex interval onto its
`(N-1)`-vertex sub-interval (collapse the top vertex `N-1` onto `N-2`): it acts on simplices
coordinatewise (`rhoS`), and the *prism* of the resulting simplicial homotopy (`W`, `midH`)
provides explicit homotopy operators (`H`) which will be used to transfer exactness from the
`(N-1)`-vertex level to the `N`-vertex level.
-/

namespace Work.ANALYTIC.CechPt.Level

/-! ## The collapse of the top vertex -/

/-- The collapse of the top vertex of `Fin N`: `i ↦ min i (N-2)`. -/
def rhoV (N : ℕ) (i : Fin N) : Fin N := ⟨min (i : ℕ) (N - 2), by omega⟩

theorem rhoV_val (N : ℕ) (i : Fin N) : ((rhoV N i : Fin N) : ℕ) = min (i : ℕ) (N - 2) := rfl

theorem rhoV_le (N : ℕ) (i : Fin N) : ((rhoV N i : Fin N) : ℕ) ≤ (i : ℕ) := by
  simp only [rhoV]; omega

theorem rhoV_le_top (N : ℕ) (i : Fin N) : ((rhoV N i : Fin N) : ℕ) ≤ N - 2 := by
  simp only [rhoV]; omega

theorem rhoV_self (N : ℕ) (i : Fin N) (h : (i : ℕ) ≤ N - 2) : rhoV N i = i := by
  ext; simp only [rhoV]; omega

theorem rhoV_idem (N : ℕ) (i : Fin N) : rhoV N (rhoV N i) = rhoV N i := by
  ext; simp only [rhoV, Nat.min_def]; split_ifs <;> omega

theorem le_rhoV_add_one {N : ℕ} {a b : Fin N} (h : (a : ℕ) ≤ (b : ℕ) + 1) :
    (a : ℕ) ≤ ((rhoV N b : Fin N) : ℕ) + 1 := by simp only [rhoV]; omega

theorem rhoV_le_add_one {N : ℕ} {a b : Fin N} (h : (a : ℕ) ≤ (b : ℕ) + 1) :
    ((rhoV N a : Fin N) : ℕ) ≤ (b : ℕ) + 1 := by simp only [rhoV]; omega

theorem rhoV_le_rhoV_add_one {N : ℕ} {a b : Fin N} (h : (a : ℕ) ≤ (b : ℕ) + 1) :
    ((rhoV N a : Fin N) : ℕ) ≤ ((rhoV N b : Fin N) : ℕ) + 1 := by simp only [rhoV]; omega

/-- The top vertex `N-1` is collapsed onto `N-2`, i.e. it does not lie in the image of `rhoV`. -/
theorem rhoV_ne_top {N : ℕ} {i : Fin N} (hi : (i : ℕ) = N - 1) : ((rhoV N i : Fin N) : ℕ) = N - 2 := by
  simp only [rhoV]; omega

/-! ## Building simplices from value functions -/

/-- Build an element of `lev M p` from a value function on `Fin (p+1)`. -/
def mkLev {M p : ℕ} (g : Fin (p + 1) → ℕ) (h1 : ∀ i j, g i ≤ g j + 1)
    (h2 : ∀ i, g i < M) : lev M p :=
  ⟨fun i => ⟨g i, h2 i⟩, fun i j => h1 i j⟩

@[simp] theorem mkLev_val {M p : ℕ} {g : Fin (p + 1) → ℕ} (h1 : ∀ i j, g i ≤ g j + 1)
    (h2 : ∀ i, g i < M) (i : Fin (p + 1)) : ((mkLev g h1 h2).1 i : ℕ) = g i := rfl

/-- The collapse of the top vertex, coordinatewise on simplices. -/
def rhoS {M p : ℕ} (x : lev M p) : lev M p :=
  mkLev (fun i => ((rhoV M (x.1 i) : Fin M) : ℕ))
    (fun i j => rhoV_le_rhoV_add_one (x.2 i j))
    (fun i => by simp only [rhoV]; have := (x.1 i).isLt; omega)

@[simp] theorem rhoS_val {M p : ℕ} (x : lev M p) (i : Fin (p + 1)) :
    ((rhoS x).1 i : ℕ) = ((rhoV M (x.1 i) : Fin M) : ℕ) := rfl

/-! ## The prism insertion `W` -/

/-- Value function of the `j`-th prism insertion. -/
def wVal {M p : ℕ} (j : Fin (p + 1)) (y : lev M p) (i : Fin (p + 2)) : ℕ :=
  if h : (i : ℕ) ≤ (j : ℕ) then ((y.1 ⟨(i : ℕ), by omega⟩ : Fin M) : ℕ)
  else ((rhoV M (y.1 ⟨(i : ℕ) - 1, by omega⟩) : Fin M) : ℕ)

theorem wVal_of_le {M p : ℕ} {j : Fin (p + 1)} {y : lev M p} {i : Fin (p + 2)}
    (h : (i : ℕ) ≤ (j : ℕ)) :
    wVal j y i = ((y.1 ⟨(i : ℕ), by omega⟩ : Fin M) : ℕ) := dif_pos h

theorem wVal_of_gt {M p : ℕ} {j : Fin (p + 1)} {y : lev M p} {i : Fin (p + 2)}
    (h : ¬ (i : ℕ) ≤ (j : ℕ)) :
    wVal j y i = ((rhoV M (y.1 ⟨(i : ℕ) - 1, by omega⟩) : Fin M) : ℕ) := dif_neg h

theorem wVal_le {M p : ℕ} (j : Fin (p + 1)) (y : lev M p) (i i' : Fin (p + 2)) :
    wVal j y i ≤ wVal j y i' + 1 := by
  by_cases h1 : (i : ℕ) ≤ (j : ℕ) <;> by_cases h2 : (i' : ℕ) ≤ (j : ℕ)
  · rw [wVal_of_le h1, wVal_of_le h2]; exact y.2 _ _
  · rw [wVal_of_le h1, wVal_of_gt h2]; exact le_rhoV_add_one (y.2 _ _)
  · rw [wVal_of_gt h1, wVal_of_le h2]; exact rhoV_le_add_one (y.2 _ _)
  · rw [wVal_of_gt h1, wVal_of_gt h2]; exact rhoV_le_rhoV_add_one (y.2 _ _)

theorem wVal_lt {M p : ℕ} (j : Fin (p + 1)) (y : lev M p) (i : Fin (p + 2)) : wVal j y i < M := by
  by_cases h1 : (i : ℕ) ≤ (j : ℕ)
  · rw [wVal_of_le h1]; exact (y.1 ⟨(i : ℕ), by omega⟩).isLt
  · rw [wVal_of_gt h1]; simp only [rhoV]
    have := (y.1 ⟨(i : ℕ) - 1, by omega⟩).isLt; omega

/-- The `j`-th prism insertion: `(y_0, …, y_j, ρ y_j, ρ y_{j+1}, …, ρ y_p)`. -/
def W {M p : ℕ} (j : Fin (p + 1)) (y : lev M p) : lev M (p + 1) :=
  mkLev (wVal j y) (wVal_le j y) (wVal_lt j y)

@[simp] theorem W_val {M p : ℕ} (j : Fin (p + 1)) (y : lev M p) (i : Fin (p + 2)) :
    ((W j y).1 i : ℕ) = wVal j y i := rfl

theorem W_le_val {M p : ℕ} (j : Fin (p + 1)) (y : lev M p) (i : Fin (p + 2))
    (h : (i : ℕ) ≤ (j : ℕ)) :
    ((W j y).1 i : ℕ) = ((y.1 ⟨(i : ℕ), by omega⟩ : Fin M) : ℕ) := by
  rw [W_val, wVal_of_le h]

theorem W_gt_val {M p : ℕ} (j : Fin (p + 1)) (y : lev M p) (i : Fin (p + 2))
    (h : ¬ (i : ℕ) ≤ (j : ℕ)) :
    ((W j y).1 i : ℕ) = ((rhoV M (y.1 ⟨(i : ℕ) - 1, by omega⟩) : Fin M) : ℕ) := by
  rw [W_val, wVal_of_gt h]

/-- The cut maps `midH t y = (y_0, …, y_{t-1}, ρ y_t, …, ρ y_p)`. -/
def mVal {M p : ℕ} (t : Fin (p + 2)) (y : lev M p) (i : Fin (p + 1)) : ℕ :=
  if h : (i : ℕ) < (t : ℕ) then ((y.1 i : Fin M) : ℕ) else ((rhoV M (y.1 i) : Fin M) : ℕ)

theorem mVal_of_lt {M p : ℕ} {t : Fin (p + 2)} {y : lev M p} {i : Fin (p + 1)}
    (h : (i : ℕ) < (t : ℕ)) : mVal t y i = ((y.1 i : Fin M) : ℕ) := dif_pos h

theorem mVal_of_ge {M p : ℕ} {t : Fin (p + 2)} {y : lev M p} {i : Fin (p + 1)}
    (h : ¬ (i : ℕ) < (t : ℕ)) : mVal t y i = ((rhoV M (y.1 i) : Fin M) : ℕ) := dif_neg h

theorem mVal_le {M p : ℕ} (t : Fin (p + 2)) (y : lev M p) (i i' : Fin (p + 1)) :
    mVal t y i ≤ mVal t y i' + 1 := by
  by_cases h1 : (i : ℕ) < (t : ℕ) <;> by_cases h2 : (i' : ℕ) < (t : ℕ)
  · rw [mVal_of_lt h1, mVal_of_lt h2]; exact y.2 _ _
  · rw [mVal_of_lt h1, mVal_of_ge h2]; exact le_rhoV_add_one (y.2 _ _)
  · rw [mVal_of_ge h1, mVal_of_lt h2]; exact rhoV_le_add_one (y.2 _ _)
  · rw [mVal_of_ge h1, mVal_of_ge h2]; exact rhoV_le_rhoV_add_one (y.2 _ _)

theorem mVal_lt {M p : ℕ} (t : Fin (p + 2)) (y : lev M p) (i : Fin (p + 1)) : mVal t y i < M := by
  by_cases h1 : (i : ℕ) < (t : ℕ)
  · rw [mVal_of_lt h1]; exact (y.1 i).isLt
  · rw [mVal_of_ge h1]; simp only [rhoV]; have := (y.1 i).isLt; omega

def midH {M p : ℕ} (t : Fin (p + 2)) (y : lev M p) : lev M p :=
  mkLev (mVal t y) (mVal_le t y) (mVal_lt t y)

@[simp] theorem midH_val {M p : ℕ} (t : Fin (p + 2)) (y : lev M p) (i : Fin (p + 1)) :
    ((midH t y).1 i : ℕ) = mVal t y i := rfl

theorem midH_lt_val {M p : ℕ} (t : Fin (p + 2)) (y : lev M p) (i : Fin (p + 1))
    (h : (i : ℕ) < (t : ℕ)) :
    ((midH t y).1 i : ℕ) = ((y.1 i : Fin M) : ℕ) := by
  rw [midH_val, mVal_of_lt h]

theorem midH_ge_val {M p : ℕ} (t : Fin (p + 2)) (y : lev M p) (i : Fin (p + 1))
    (h : ¬ (i : ℕ) < (t : ℕ)) :
    ((midH t y).1 i : ℕ) = ((rhoV M (y.1 i) : Fin M) : ℕ) := by
  rw [midH_val, mVal_of_ge h]

/-- `midH 0` is the collapse `rhoS`. -/
theorem midH_zero {M p : ℕ} (y : lev M p) : midH (0 : Fin (p + 2)) y = rhoS y := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  rw [midH_ge_val, rhoS_val]
  simp only [Fin.val_zero]; omega

/-- `midH (last)` is the identity. -/
theorem midH_last {M p : ℕ} (y : lev M p) : midH (Fin.last (p + 1)) y = y := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  rw [midH_lt_val]
  simp only [Fin.val_last]; omega


theorem succAbove_eq_mk_lt {n : ℕ} (i : Fin (n+1)) (m : Fin n) (hm : (m:ℕ) < (i:ℕ)) :
    Fin.succAbove i m = (⟨(m:ℕ), by omega⟩ : Fin (n+1)) := by
  rw [Fin.succAbove_of_castSucc_lt _ _ (by simp only [Fin.castSucc, Fin.lt_def]; exact hm)]
  exact Fin.ext rfl

theorem succAbove_eq_mk_ge {n : ℕ} (i : Fin (n+1)) (m : Fin n) (hm : (i:ℕ) ≤ (m:ℕ)) :
    Fin.succAbove i m = (⟨(m:ℕ)+1, by omega⟩ : Fin (n+1)) := by
  rw [Fin.succAbove_of_le_castSucc _ _ (by simp only [Fin.le_def, Fin.val_castSucc]; omega)]
  exact Fin.ext rfl

-- (F1)
theorem face_W_lt {M p : ℕ} (j : Fin (p+1)) (y : lev M (p+1)) (i : Fin (p+2))
    (h : (i:ℕ) ≤ (j:ℕ)) :
    face ⟨(i:ℕ), by omega⟩ (W (Fin.succ j) y) = W j (face ⟨(i:ℕ), by omega⟩ y) := by
  apply Subtype.ext
  funext k
  apply Fin.ext
  change ((W (Fin.succ j) y).1 (Fin.succAbove ⟨(i:ℕ), by omega⟩ k) : ℕ)
      = ((W j (face ⟨(i:ℕ), by omega⟩ y)).1 k : ℕ)
  by_cases hk : (k:ℕ) < (i:ℕ)
  · rw [succAbove_eq_mk_lt (⟨(i:ℕ), by omega⟩ : Fin (p+3)) k hk]
    have hcond : ((⟨(k:ℕ), by omega⟩ : Fin (p+3)) : ℕ) ≤ ((Fin.succ j : Fin (p+2)) : ℕ) := by
      simp only [Fin.val_succ]; omega
    have hkj : (k:ℕ) ≤ (j:ℕ) := by omega
    rw [W_le_val _ _ _ hcond, W_le_val _ _ _ hkj]
    have hface : ((face ⟨(i:ℕ), by omega⟩ y).1 ⟨(k:ℕ), by omega⟩ : Fin M)
        = y.1 (Fin.succAbove ⟨(i:ℕ), by omega⟩ ⟨(k:ℕ), by omega⟩) := rfl
    rw [hface]
    have hidx : Fin.succAbove ⟨(i:ℕ), by omega⟩ ⟨(k:ℕ), by omega⟩
        = (⟨(k:ℕ), by omega⟩ : Fin (p+2)) :=
      succAbove_eq_mk_lt (⟨(i:ℕ), by omega⟩ : Fin (p+2)) ⟨(k:ℕ), by omega⟩ hk
    rw [hidx]
  · rw [succAbove_eq_mk_ge (⟨(i:ℕ), by omega⟩ : Fin (p+3)) k (by show (i:ℕ) ≤ (k:ℕ); omega)]
    by_cases hkj : (k:ℕ) ≤ (j:ℕ)
    · have hcond : ((⟨(k:ℕ)+1, by omega⟩ : Fin (p+3)) : ℕ) ≤ ((Fin.succ j : Fin (p+2)) : ℕ) := by
        simp only [Fin.val_succ]; omega
      rw [W_le_val _ _ _ hcond, W_le_val _ _ _ hkj]
      have hface : ((face ⟨(i:ℕ), by omega⟩ y).1 ⟨(k:ℕ), by omega⟩ : Fin M)
          = y.1 (Fin.succAbove ⟨(i:ℕ), by omega⟩ ⟨(k:ℕ), by omega⟩) := rfl
      rw [hface]
      have hidx : Fin.succAbove ⟨(i:ℕ), by omega⟩ ⟨(k:ℕ), by omega⟩
          = (⟨(k:ℕ)+1, by omega⟩ : Fin (p+2)) :=
        succAbove_eq_mk_ge (⟨(i:ℕ), by omega⟩ : Fin (p+2)) ⟨(k:ℕ), by omega⟩ (by show (i:ℕ) ≤ (k:ℕ); omega)
      rw [hidx]
    · have hcond : ¬ ((⟨(k:ℕ)+1, by omega⟩ : Fin (p+3)) : ℕ) ≤ ((Fin.succ j : Fin (p+2)) : ℕ) := by
        simp only [Fin.val_succ]; omega
      rw [W_gt_val _ _ _ hcond, W_gt_val _ _ _ hkj]
      have hface : ((face ⟨(i:ℕ), by omega⟩ y).1 ⟨(k:ℕ)-1, by omega⟩ : Fin M)
          = y.1 (Fin.succAbove ⟨(i:ℕ), by omega⟩ ⟨(k:ℕ)-1, by omega⟩) := rfl
      rw [hface]
      have hidx : Fin.succAbove ⟨(i:ℕ), by omega⟩ ⟨(k:ℕ)-1, by omega⟩
          = (⟨(k:ℕ), by omega⟩ : Fin (p+2)) := by
        rw [succAbove_eq_mk_ge (⟨(i:ℕ), by omega⟩ : Fin (p+2)) ⟨(k:ℕ)-1, by omega⟩
          (by show (i:ℕ) ≤ (k:ℕ)-1; omega)]
        exact Fin.ext (by simp only; omega)
      rw [hidx]
      exact congrArg (fun t => ((rhoV M (y.1 t) : Fin M) : ℕ)) (Fin.ext (by simp only; omega))




-- (F4)
theorem face_W_gt {M p : ℕ} (j : Fin (p+1)) (y : lev M (p+1)) (i : Fin (p+2))
    (h : (j:ℕ)+1 ≤ (i:ℕ)) :
    face ⟨(i:ℕ)+1, by omega⟩ (W (Fin.castSucc j) y) = W j (face ⟨(i:ℕ), by omega⟩ y) := by
  apply Subtype.ext
  funext k
  apply Fin.ext
  change ((W (Fin.castSucc j) y).1 (Fin.succAbove ⟨(i:ℕ)+1, by omega⟩ k) : ℕ)
      = ((W j (face ⟨(i:ℕ), by omega⟩ y)).1 k : ℕ)
  have hcv : ((Fin.castSucc j : Fin (p+2)) : ℕ) = (j:ℕ) := Fin.val_castSucc j
  by_cases hk : (k:ℕ) < (i:ℕ)+1
  · rw [succAbove_eq_mk_lt (⟨(i:ℕ)+1, by omega⟩ : Fin (p+3)) k hk]
    by_cases hkj : (k:ℕ) ≤ (j:ℕ)
    · have hcond : ((⟨(k:ℕ), by omega⟩ : Fin (p+3)) : ℕ) ≤ ((Fin.castSucc j : Fin (p+2)) : ℕ) := by
        rw [hcv]; omega
      rw [W_le_val _ _ _ hcond, W_le_val _ _ _ hkj]
      have hface : ((face ⟨(i:ℕ), by omega⟩ y).1 ⟨(k:ℕ), by omega⟩ : Fin M)
          = y.1 (Fin.succAbove ⟨(i:ℕ), by omega⟩ ⟨(k:ℕ), by omega⟩) := rfl
      rw [hface]
      have hidx : Fin.succAbove ⟨(i:ℕ), by omega⟩ ⟨(k:ℕ), by omega⟩
          = (⟨(k:ℕ), by omega⟩ : Fin (p+2)) :=
        succAbove_eq_mk_lt (⟨(i:ℕ), by omega⟩ : Fin (p+2)) ⟨(k:ℕ), by omega⟩
          (by show (k:ℕ) < (i:ℕ); omega)
      rw [hidx]
    · have hcond : ¬ ((⟨(k:ℕ), by omega⟩ : Fin (p+3)) : ℕ) ≤ ((Fin.castSucc j : Fin (p+2)) : ℕ) := by
        rw [hcv]; omega
      rw [W_gt_val _ _ _ hcond, W_gt_val _ _ _ hkj]
      have hface : ((face ⟨(i:ℕ), by omega⟩ y).1 ⟨(k:ℕ)-1, by omega⟩ : Fin M)
          = y.1 (Fin.succAbove ⟨(i:ℕ), by omega⟩ ⟨(k:ℕ)-1, by omega⟩) := rfl
      rw [hface]
      have hidx : Fin.succAbove ⟨(i:ℕ), by omega⟩ ⟨(k:ℕ)-1, by omega⟩
          = (⟨(k:ℕ)-1, by omega⟩ : Fin (p+2)) :=
        succAbove_eq_mk_lt (⟨(i:ℕ), by omega⟩ : Fin (p+2)) ⟨(k:ℕ)-1, by omega⟩
          (by show (k:ℕ)-1 < (i:ℕ); omega)
      rw [hidx]
  · rw [succAbove_eq_mk_ge (⟨(i:ℕ)+1, by omega⟩ : Fin (p+3)) k (by show (i:ℕ)+1 ≤ (k:ℕ); omega)]
    by_cases hkj : (k:ℕ)+1 ≤ (j:ℕ)
    · have hcond : ((⟨(k:ℕ)+1, by omega⟩ : Fin (p+3)) : ℕ) ≤ ((Fin.castSucc j : Fin (p+2)) : ℕ) := by
        rw [hcv]; omega
      have hkj' : (k:ℕ) ≤ (j:ℕ) := by omega
      rw [W_le_val _ _ _ hcond, W_le_val _ _ _ hkj']
      have hface : ((face ⟨(i:ℕ), by omega⟩ y).1 ⟨(k:ℕ), by omega⟩ : Fin M)
          = y.1 (Fin.succAbove ⟨(i:ℕ), by omega⟩ ⟨(k:ℕ), by omega⟩) := rfl
      rw [hface]
      have hidx : Fin.succAbove ⟨(i:ℕ), by omega⟩ ⟨(k:ℕ), by omega⟩
          = (⟨(k:ℕ)+1, by omega⟩ : Fin (p+2)) :=
        succAbove_eq_mk_ge (⟨(i:ℕ), by omega⟩ : Fin (p+2)) ⟨(k:ℕ), by omega⟩
          (by show (i:ℕ) ≤ (k:ℕ); omega)
      rw [hidx]
    · have hcond : ¬ ((⟨(k:ℕ)+1, by omega⟩ : Fin (p+3)) : ℕ) ≤ ((Fin.castSucc j : Fin (p+2)) : ℕ) := by
        rw [hcv]; omega
      rw [W_gt_val _ _ _ hcond]
      by_cases hkj' : (k:ℕ) ≤ (j:ℕ)
      · exfalso; omega
      · rw [W_gt_val _ _ _ hkj']
        have hface : ((face ⟨(i:ℕ), by omega⟩ y).1 ⟨(k:ℕ)-1, by omega⟩ : Fin M)
            = y.1 (Fin.succAbove ⟨(i:ℕ), by omega⟩ ⟨(k:ℕ)-1, by omega⟩) := rfl
        rw [hface]
        have hidx : Fin.succAbove ⟨(i:ℕ), by omega⟩ ⟨(k:ℕ)-1, by omega⟩
            = (⟨(k:ℕ), by omega⟩ : Fin (p+2)) := by
          rw [succAbove_eq_mk_ge (⟨(i:ℕ), by omega⟩ : Fin (p+2)) ⟨(k:ℕ)-1, by omega⟩
            (by show (i:ℕ) ≤ (k:ℕ)-1; omega)]
          exact Fin.ext (by simp only; omega)
        rw [hidx]
        exact congrArg (fun t => ((rhoV M (y.1 t) : Fin M) : ℕ)) (Fin.ext (by simp only; omega))




/-! ## The homotopy operator `H` and its prism identity -/

/-- The face deleting the `j`-th coordinate of the prism insertion is the cut at `j`. -/
theorem face_W_eq {M p : ℕ} (j : Fin (p+2)) (y : lev M (p+1)) :
    face ⟨(j:ℕ), by omega⟩ (W j y) = midH ⟨(j:ℕ), by omega⟩ y := by
  apply Subtype.ext
  funext k
  apply Fin.ext
  change ((W j y).1 (Fin.succAbove ⟨(j:ℕ), by omega⟩ k) : ℕ)
      = ((midH ⟨(j:ℕ), by omega⟩ y).1 k : ℕ)
  by_cases h : (k:ℕ) < (j:ℕ)
  · have hsucc : Fin.succAbove ⟨(j:ℕ), by omega⟩ k = Fin.castSucc k := by
      rw [Fin.succAbove_of_castSucc_lt]
      simp only [Fin.castSucc, Fin.lt_def]; exact h
    have h1 : ((Fin.castSucc k : Fin (p+3)) : ℕ) ≤ (j:ℕ) := by
      simp only [Fin.val_castSucc]; omega
    rw [hsucc, W_le_val _ _ _ h1, midH_lt_val _ _ _ h]
    exact congrArg (fun t => ((y.1 t : Fin M) : ℕ)) (Fin.ext (by simp))
  · have hsucc : Fin.succAbove ⟨(j:ℕ), by omega⟩ k = Fin.succ k := by
      rw [Fin.succAbove_of_le_castSucc]
      simp only [Fin.le_def, Fin.val_castSucc]; omega
    have h1 : ¬ ((Fin.succ k : Fin (p+3)) : ℕ) ≤ (j:ℕ) := by
      simp only [Fin.val_succ]; omega
    rw [hsucc, W_gt_val _ _ _ h1, midH_ge_val _ _ _ h]
    exact congrArg (fun t => ((rhoV M (y.1 t) : Fin M) : ℕ))
      (Fin.ext (by simp only [Fin.val_succ]; omega))

/-- The face deleting the `(j+1)`-st coordinate of the prism insertion is the cut at `j+1`. -/
theorem face_W_succ {M p : ℕ} (j : Fin (p+2)) (y : lev M (p+1)) :
    face ⟨(j:ℕ)+1, by omega⟩ (W j y) = midH ⟨(j:ℕ)+1, by omega⟩ y := by
  apply Subtype.ext
  funext k
  apply Fin.ext
  change ((W j y).1 (Fin.succAbove ⟨(j:ℕ)+1, by omega⟩ k) : ℕ)
      = ((midH ⟨(j:ℕ)+1, by omega⟩ y).1 k : ℕ)
  by_cases h : (k:ℕ) < (j:ℕ)+1
  · have hsucc : Fin.succAbove ⟨(j:ℕ)+1, by omega⟩ k = Fin.castSucc k := by
      rw [Fin.succAbove_of_castSucc_lt]
      simp only [Fin.castSucc, Fin.lt_def]; exact h
    have h1 : ((Fin.castSucc k : Fin (p+3)) : ℕ) ≤ (j:ℕ) := by
      simp only [Fin.val_castSucc]; omega
    rw [hsucc, W_le_val _ _ _ h1, midH_lt_val _ _ _ h]
    exact congrArg (fun t => ((y.1 t : Fin M) : ℕ)) (Fin.ext (by simp only [Fin.val_castSucc]))
  · have hsucc : Fin.succAbove ⟨(j:ℕ)+1, by omega⟩ k = Fin.succ k := by
      rw [Fin.succAbove_of_le_castSucc]
      simp only [Fin.le_def, Fin.val_castSucc]; omega
    have h1 : ¬ ((Fin.succ k : Fin (p+3)) : ℕ) ≤ (j:ℕ) := by
      simp only [Fin.val_succ]; omega
    rw [hsucc, W_gt_val _ _ _ h1, midH_ge_val _ _ _ h]
    exact congrArg (fun t => ((rhoV M (y.1 t) : Fin M) : ℕ))
      (Fin.ext (by simp only [Fin.val_succ]; omega))

/-- The homotopy operator on cochains: `(H q G) z = ∑_j (-1)^j G (W_j z)`. -/
def H {M : ℕ} (q : ℕ) (G : lev M (q + 1) → ℤ) : lev M q → ℤ :=
  fun z => ∑ j : Fin (q + 1), (-1 : ℤ) ^ (j : ℕ) * G (W j z)

/-! ## The inclusion and the retraction between consecutive levels -/

/-- The inclusion of the `(M+1)`-vertex level into the `(M+2)`-vertex level. -/
def inclS {M p : ℕ} (x : lev (M + 1) p) : lev (M + 2) p :=
  mkLev (fun i => ((x.1 i : Fin (M + 1)) : ℕ))
    (fun i j => x.2 i j)
    (fun i => by have := (x.1 i).isLt; omega)

@[simp] theorem inclS_val {M p : ℕ} (x : lev (M + 1) p) (i : Fin (p + 1)) :
    ((inclS x).1 i : ℕ) = ((x.1 i : Fin (M + 1)) : ℕ) := rfl

/-- The collapse of the top vertex, from the `(M+2)`-vertex level onto the `(M+1)`-vertex level. -/
def retrS {M p : ℕ} (x : lev (M + 2) p) : lev (M + 1) p :=
  mkLev (fun i => min ((x.1 i : Fin (M + 2)) : ℕ) M)
    (fun i j => by
      have h := x.2 i j
      simp only [Nat.min_def] at *
      split_ifs <;> omega)
    (fun i => by
      have := (x.1 i).isLt
      simp only [Nat.min_def]
      split_ifs <;> omega)

@[simp] theorem retrS_val {M p : ℕ} (x : lev (M + 2) p) (i : Fin (p + 1)) :
    ((retrS x).1 i : ℕ) = min ((x.1 i : Fin (M + 2)) : ℕ) M := rfl

end Work.ANALYTIC.CechPt.Level
