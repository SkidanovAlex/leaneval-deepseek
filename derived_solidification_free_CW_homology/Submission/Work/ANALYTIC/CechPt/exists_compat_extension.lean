import Mathlib
import Submission.Work.ANALYTIC.CechPt.CechLevels
import Submission.Work.ANALYTIC.CechPt.LevelAux
import Submission.Work.ANALYTIC.CechPt.levDiv_exists
import Submission.Work.ANALYTIC.CechPt.upLevDiv
import Submission.Work.ANALYTIC.CechPt.upLevLt

/-!
# Compatible extensions of simplices of the level nerves

Let `y` be a `p`-simplex of the level-`n` dyadic nerve `Level.lev (2^(n+1)) p`, i.e. a `(p+1)`-tuple
of vertices of `{0, …, 2^(n+1)-1}` of diameter at most one.  This module constructs a whole family

`Y m ∈ Level.lev (2^(m+1)) p   (m : ℕ)`

with `Y n = y` and `((Y (m+1)).1 i : ℕ) / 2 = ((Y m).1 i : ℕ)` for all `m` and `i`, i.e. the
level-`m` simplex is the coordinatewise halving of the level-`(m+1)` simplex.

The family is built from two formulas:

* below (and at) level `n` the coordinates are the halvings `(y_i) / 2^(n-m)`
  (`Level.levDiv_exists`, imported from `levDiv_exists.lean`);
* above level `n` the coordinates are the additive shift `y_i + (2^(m-n)-1) * maxC y`, where
  `maxC y` is the largest coordinate of `y`.  Since the coordinates of a simplex of the level
  nerve have diameter at most one, `maxC y - y_i ∈ {0,1}`; adding a constant preserves the
  diameter condition, and the shift is exactly what makes the level-`(m+1)` coordinates the
  doublings of the level-`m` ones.

-/

namespace Work.ANALYTIC.CechPt

open Level

noncomputable section

/-! ## The largest coordinate of a simplex -/

/-- The largest coordinate of a simplex of the level-`M` dyadic nerve. -/
private def maxC {M p : ℕ} (y : Level.lev M p) : ℕ :=
  Finset.univ.sup (fun i : Fin (p + 1) => (y.1 i : ℕ))

private theorem le_maxC {M p : ℕ} (y : Level.lev M p) (i : Fin (p + 1)) :
    (y.1 i : ℕ) ≤ maxC y := by
  show (y.1 i : ℕ) ≤ Finset.univ.sup (fun j : Fin (p + 1) => (y.1 j : ℕ))
  exact Finset.le_sup (s := Finset.univ) (f := fun j : Fin (p + 1) => (y.1 j : ℕ))
    (b := i) (Finset.mem_univ i)

/-- Every coordinate is within one of the largest coordinate; this is the diameter condition. -/
private theorem maxC_le {M p : ℕ} (y : Level.lev M p) (i : Fin (p + 1)) :
    maxC y ≤ (y.1 i : ℕ) + 1 := by
  show Finset.univ.sup (fun j : Fin (p + 1) => (y.1 j : ℕ)) ≤ (y.1 i : ℕ) + 1
  exact Finset.sup_le (fun j _ => y.2 j i)

private theorem maxC_lt {M p : ℕ} (y : Level.lev M p) : maxC y < M := by
  have hM : 0 < M := lt_of_le_of_lt (Nat.zero_le _) (y.1 ⟨0, Nat.succ_pos p⟩).isLt
  show Finset.univ.sup (fun j : Fin (p + 1) => (y.1 j : ℕ)) < M
  rw [Finset.sup_lt_iff hM]
  intro b _
  exact (y.1 b).isLt

/-! ## The shift above level `n` -/

/-- Coordinates of the level-`m` extension of `y` above level `n`: an additive shift by
`(2^(m-n)-1) * maxC y`. -/
private def upVal (p n : ℕ) (y : Level.lev (2 ^ (n + 1)) p) (m : ℕ) (i : Fin (p + 1)) : ℕ :=
  (y.1 i : ℕ) + (2 ^ (m - n) - 1) * maxC y

/-- The shift is a constant, so it preserves the diameter condition. -/
private theorem upVal_diam (p n m : ℕ) (y : Level.lev (2 ^ (n + 1)) p) (i j : Fin (p + 1)) :
    upVal p n y m i ≤ upVal p n y m j + 1 := by
  have h := y.2 i j
  simp only [upVal]
  omega

/-- The shifted coordinates stay below `2^(m+1)` for `m ≥ n`. -/
private theorem upVal_lt (p n m : ℕ) (y : Level.lev (2 ^ (n + 1)) p) (h : n ≤ m)
    (i : Fin (p + 1)) : upVal p n y m i < 2 ^ (m + 1) :=
  upLevLt (y.1 i : ℕ) (maxC y) n m (le_maxC y i) (maxC_lt y) h

/-- The level-`m` extension of `y`, for `m ≥ n`. -/
private def upLev (p n : ℕ) (y : Level.lev (2 ^ (n + 1)) p) (m : ℕ) (h : n ≤ m) :
    Level.lev (2 ^ (m + 1)) p :=
  Level.mkLev (upVal p n y m) (upVal_diam p n m y) (upVal_lt p n m y h)

/-- Halving the shifted level-`(m+1)` coordinates gives the level-`m` ones. -/
private theorem upVal_div (p n m : ℕ) (y : Level.lev (2 ^ (n + 1)) p) (h : n ≤ m)
    (i : Fin (p + 1)) : upVal p n y (m + 1) i / 2 = upVal p n y m i :=
  upLevDiv (y.1 i : ℕ) (maxC y) n m (le_maxC y i) (maxC_le y i) h

/-- The base case `m = n` of `upVal_div`. -/
private theorem upVal_div_self (p n : ℕ) (y : Level.lev (2 ^ (n + 1)) p) (i : Fin (p + 1)) :
    upVal p n y (n + 1) i / 2 = (y.1 i : ℕ) := by
  have h1 : (y.1 i : ℕ) ≤ maxC y := le_maxC y i
  have h2 : maxC y ≤ (y.1 i : ℕ) + 1 := maxC_le y i
  have hn : n + 1 - n = 1 := by omega
  have hgoal : upVal p n y (n + 1) i = (y.1 i : ℕ) + maxC y := by
    simp only [upVal, hn]
    norm_num
  rw [hgoal]
  omega

/-! ## The compatible family -/

/-- The downward truncation `Level.levDiv_exists`, chosen once and for all. -/
private def levTr (p : ℕ) :
    ∀ (n m : ℕ), m ≤ n → Level.lev (2 ^ (n + 1)) p → Level.lev (2 ^ (m + 1)) p :=
  Classical.choose (levDiv_exists p)

private theorem levTr_val (p n m : ℕ) (h : m ≤ n) (y : Level.lev (2 ^ (n + 1)) p)
    (i : Fin (p + 1)) :
    ((levTr p n m h y).1 i : ℕ) = (y.1 i : ℕ) / 2 ^ (n - m) :=
  (Classical.choose_spec (levDiv_exists p)).1 n m h y i

private theorem levTr_self (p n : ℕ) (y : Level.lev (2 ^ (n + 1)) p) :
    levTr p n n le_rfl y = y :=
  (Classical.choose_spec (levDiv_exists p)).2.1 n y

/-- The compatible family: truncation below level `n`, shift above it. -/
private def Yfam (p n : ℕ) (y : Level.lev (2 ^ (n + 1)) p) (m : ℕ) :
    Level.lev (2 ^ (m + 1)) p :=
  if h : m ≤ n then levTr p n m h y else upLev p n y m (by omega)

private theorem Yfam_val_le (p n : ℕ) (y : Level.lev (2 ^ (n + 1)) p) (m : ℕ) (hm : m ≤ n)
    (i : Fin (p + 1)) :
    ((Yfam p n y m).1 i : ℕ) = (y.1 i : ℕ) / 2 ^ (n - m) := by
  rw [Yfam, dif_pos hm]
  exact levTr_val p n m hm y i

private theorem Yfam_val_gt (p n : ℕ) (y : Level.lev (2 ^ (n + 1)) p) (m : ℕ) (hm : ¬ m ≤ n)
    (i : Fin (p + 1)) :
    ((Yfam p n y m).1 i : ℕ) = (y.1 i : ℕ) + (2 ^ (m - n) - 1) * maxC y := by
  rw [Yfam, dif_neg hm]
  rfl

private theorem Yfam_self (p n : ℕ) (y : Level.lev (2 ^ (n + 1)) p) : Yfam p n y n = y := by
  rw [Yfam, dif_pos (le_refl n)]
  exact levTr_self p n y

/-- **Compatible extension of a level-`n` simplex.**  Every simplex of the level-`n` dyadic nerve
of the interval extends to a family of simplices of all levels whose consecutive members are
related by coordinatewise halving. -/
theorem exists_compat_extension (p n : ℕ) (y : Work.ANALYTIC.CechPt.Level.lev (2 ^ (n + 1)) p) :
    ∃ Y : ∀ m : ℕ, Work.ANALYTIC.CechPt.Level.lev (2 ^ (m + 1)) p,
      Y n = y ∧ ∀ (m : ℕ) (i : Fin (p + 1)), ((Y (m + 1)).1 i : ℕ) / 2 = ((Y m).1 i : ℕ) := by
  refine ⟨Yfam p n y, Yfam_self p n y, ?_⟩
  intro m i
  by_cases h1 : m + 1 ≤ n
  · rw [Yfam_val_le p n y (m + 1) h1 i, Yfam_val_le p n y m (by omega) i,
      Nat.div_div_eq_div_mul]
    congr 1
    rw [← pow_succ]
    congr 1
    omega
  · by_cases h2 : m ≤ n
    · have hmn : m = n := by omega
      rw [hmn]
      rw [Yfam_val_gt p n y (n + 1) (by omega) i, Yfam_self]
      exact upVal_div_self p n y i
    · rw [Yfam_val_gt p n y (m + 1) (by omega) i, Yfam_val_gt p n y m h2 i]
      exact upVal_div p n m y (by omega) i

end

end Work.ANALYTIC.CechPt
