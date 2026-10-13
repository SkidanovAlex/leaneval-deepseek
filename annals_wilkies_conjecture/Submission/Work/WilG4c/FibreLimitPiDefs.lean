/-
  WilG4c / `FibreLimitPiDefs` — the vocabulary for the general-`n` fibre-limit lemma
  `Work.WilG4c.fibreLimitEqMem_pi`.

  This is the `n + 1`-cube-variable generalisation of `Work.WilG4a.CD.fibreLimitEqMem`
  (one cube variable, `n = 0`).  Given `A ⊆ ℝ^{p+(n+1)+1}` (coordinates `(u, x, y)`: `p`
  parameters, `n+1` cube coordinates, one value), we build the set of

    `w : Fin (p+(n+1)+1) → ℝ`

  such that the `A`-values along the *punctured cube* `x ↦ (u, x, v)`, `x ≠ u`, tend to
  `w (last)` as `x → u`.

  The `∀ε>0 ∃δ>0 …` condition (the "limit" condition) is the complement of the
  `∃ε>0 ∀ρ≠0 ∃x∃v …` condition ("bad"): over `ℝ` the two are exchanged by
  `¬∀ = ∃¬`, and the punctured `δ`-cube `{x | x ≠ u, ∀j |x_j - u_j| < δ}` is replaced by
  `{x | x ≠ u, ∀j (x_j - u_j)^2 ≤ ρ^2}`.

  ## The layout

  The big space is `ℝ^{NB}` with coordinates

  * `0 … Wp-1` : `w` (the base point),
  * `Wp`       : `ε`
  * `Wp+1`     : `ρ`
  * `W2 … W2+n`: the punctured-cube variable `x` (`n+1` coordinates),
  * `W2+n+1`   : `v` (the value),

  where `Wp = p + (n+1) + 1`, `W1 = Wp + 1`, `W2 = Wp + 2 = W1 + 1`,
  `NB = W2 + (n+1) + 1`.  All the `∃`/`∀` are then eliminated by projections and
  complements: `G1` drops `v` and the `n+1` cube coordinates, `Kset` adds `ρ ≠ 0`,
  `P1` drops `ρ`, `P2` adds `¬P1` and `ε > 0`, `Bc` drops `ε`, and `Bset = Bcᶜ`.
-/
import Mathlib
import Submission.Work.WilG4c.SlicedDerivDefs
import Submission.Work.WilG4a.subst_mem
import Submission.Work.WilG0.API
import Submission.Work.WilG0.projLastIter_eq
import Submission.Work.WilkiesH.Omega.omega_poly_le
import Submission.Work.WilkiesH.Omega.omega_poly_lt
import Submission.Work.WilkiesH.Omega.omega_poly_ne
import Submission.Work.WilG1.Basic

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign

open Work.WilG0

/-! ## 1  Dimensions and index layout -/

/-- `Wp p n = p + (n+1) + 1`: the dimension of the base point `w`. -/
abbrev Wp (p n : ℕ) : ℕ := p + (n + 1) + 1
/-- `(w, ε)`: dimension `Wp + 1`. -/
abbrev W1 (p n : ℕ) : ℕ := Wp p n + 1
/-- `(w, ε, ρ)`: dimension `Wp + 2`. -/
abbrev W2 (p n : ℕ) : ℕ := W1 p n + 1
/-- The big space `(w, ε, ρ, x, v)`: dimension `W2 + (n+1) + 1`. -/
abbrev NB (p n : ℕ) : ℕ := W2 p n + (n + 1) + 1

@[simp] theorem NB_eq_snoc (p n : ℕ) : NB p n = W2 p n + (n + 1) + 1 := rfl

/-- The `w`-coordinate blocks seen inside the big space, and the extra slots. -/
def parIdxP (p n : ℕ) (i : Fin p) : Fin (NB p n) :=
  ⟨i, by simp only [NB, W2, W1, Wp]; omega⟩
def y0IdxP (p n : ℕ) (i : Fin (n+1)) : Fin (NB p n) :=
  ⟨p + i, by simp only [NB, W2, W1, Wp]; omega⟩
def v0IdxP (p n : ℕ) : Fin (NB p n) :=
  ⟨p + (n+1), by simp only [NB, W2, W1, Wp]; omega⟩
def eIdxP (p n : ℕ) : Fin (NB p n) :=
  ⟨Wp p n, by simp only [NB, W2, W1, Wp]; omega⟩
def rIdxP (p n : ℕ) : Fin (NB p n) :=
  ⟨W1 p n, by simp only [NB, W2, W1, Wp]; omega⟩
def yIdxP (p n : ℕ) (i : Fin (n+1)) : Fin (NB p n) :=
  ⟨W2 p n + i, by simp only [NB, W2, W1, Wp]; omega⟩
def vIdxP (p n : ℕ) : Fin (NB p n) :=
  ⟨W2 p n + (n+1), by simp only [NB, W2, W1, Wp]; omega⟩

/-- The corresponding indices inside the smaller spaces `ℝ^{W2}`, `ℝ^{W1}`, `ℝ^{Wp}`. -/
def parIdxW (p n : ℕ) (i : Fin p) : Fin (Wp p n) :=
  ⟨i, by simp only [Wp]; omega⟩
def y0IdxW (p n : ℕ) (i : Fin (n+1)) : Fin (Wp p n) :=
  ⟨p + i, by simp only [Wp]; omega⟩
def v0IdxW (p n : ℕ) : Fin (Wp p n) :=
  ⟨p + (n+1), by simp only [Wp]; omega⟩
def parIdx1 (p n : ℕ) (i : Fin p) : Fin (W1 p n) :=
  ⟨i, by simp only [W1, Wp]; omega⟩
def y0Idx1 (p n : ℕ) (i : Fin (n+1)) : Fin (W1 p n) :=
  ⟨p + i, by simp only [W1, Wp]; omega⟩
def v0Idx1 (p n : ℕ) : Fin (W1 p n) :=
  ⟨p + (n+1), by simp only [W1, Wp]; omega⟩
def parIdx2 (p n : ℕ) (i : Fin p) : Fin (W2 p n) :=
  ⟨i, by simp only [W2, W1, Wp]; omega⟩
def y0Idx2 (p n : ℕ) (i : Fin (n+1)) : Fin (W2 p n) :=
  ⟨p + i, by simp only [W2, W1, Wp]; omega⟩
def v0Idx2 (p n : ℕ) : Fin (W2 p n) :=
  ⟨p + (n+1), by simp only [W2, W1, Wp]; omega⟩
def eIdx2 (p n : ℕ) : Fin (W2 p n) :=
  ⟨Wp p n, by simp only [W2, W1, Wp]; omega⟩
def rIdx2 (p n : ℕ) : Fin (W2 p n) :=
  ⟨W1 p n, by simp only [W2, W1, Wp]; omega⟩
def eIdx1 (p n : ℕ) : Fin (W1 p n) :=
  ⟨Wp p n, by simp only [W1, Wp]; omega⟩

/-- The substitution map from the `A`-coordinates `Fin (Wp)` into the big space: parameter
coordinates stay, the cube coordinates go to the cube block, the value coordinate to `v`. -/
def iotaP (p n : ℕ) (j : Fin (Wp p n)) : Fin (NB p n) :=
  if (j : ℕ) < p then ⟨j, by have := j.isLt; simp only [NB, W2, W1, Wp] at *; omega⟩
  else if (j : ℕ) < p + (n+1) then
    ⟨W2 p n + ((j:ℕ) - p), by have := j.isLt; simp only [NB, W2, W1, Wp] at *; omega⟩
  else ⟨W2 p n + (n+1), by have := j.isLt; simp only [NB, W2, W1, Wp] at *; omega⟩

/-! ## 2  The generic points -/

/-- `(w, ε)` as a point of `ℝ^{W1}`. -/
def XgenP (p n : ℕ) (w : Fin (Wp p n) → ℝ) (ε : ℝ) : Fin (W1 p n) → ℝ := Fin.snoc w ε
/-- `(w, ε, ρ)` as a point of `ℝ^{W2}`. -/
def YgenP (p n : ℕ) (ξ : Fin (W1 p n) → ℝ) (ρ : ℝ) : Fin (W2 p n) → ℝ := Fin.snoc ξ ρ
/-- `(w, ε, ρ, x, v)` as a point of the big space. -/
def ZgenP (p n : ℕ) (ξ : Fin (W2 p n) → ℝ) (x : Fin (n+1) → ℝ) (v : ℝ) :
    Fin (NB p n) → ℝ := Fin.snoc (Fin.append ξ x) v

/-! ## 3  The pieces of the big set -/

/-- The pullback of `A` along `iotaP`. -/
def pPullP (p n : ℕ) (A : Set (Fin (Wp p n) → ℝ)) : Set (Fin (NB p n) → ℝ) :=
  {z | (fun j : Fin (Wp p n) => z (iotaP p n j)) ∈ A}

/-- `ε > 0`. -/
def pPosEP (p n : ℕ) : Set (Fin (NB p n) → ℝ) := {z | 0 < z (eIdxP p n)}
/-- `ρ ≠ 0`. -/
def pRneP (p n : ℕ) : Set (Fin (NB p n) → ℝ) := {z | z (rIdxP p n) ≠ 0}
/-- `(x j - u j)^2 ≤ ρ^2`. -/
def pSqP (p n : ℕ) (j : Fin (n+1)) : Set (Fin (NB p n) → ℝ) :=
  {z | (z (yIdxP p n j) - z (y0IdxP p n j)) ^ 2 ≤ (z (rIdxP p n)) ^ 2}
/-- `∀ j, (x j - u j)^2 ≤ ρ^2`. -/
def pSqAllP (p n : ℕ) : Set (Fin (NB p n) → ℝ) := ⋂ j : Fin (n+1), pSqP p n j
/-- `x j ≠ u j`. -/
def pYneqP (p n : ℕ) (j : Fin (n+1)) : Set (Fin (NB p n) → ℝ) :=
  {z | z (yIdxP p n j) ≠ z (y0IdxP p n j)}
/-- `x ≠ u`. -/
def pYneP (p n : ℕ) : Set (Fin (NB p n) → ℝ) := ⋃ j : Fin (n+1), pYneqP p n j
/-- `ε^2 < (v - w_last)^2`. -/
def pEpsP (p n : ℕ) : Set (Fin (NB p n) → ℝ) :=
  {z | (z (eIdxP p n)) ^ 2 < (z (vIdxP p n) - z (v0IdxP p n)) ^ 2}

/-- The big set. -/
def BigSetP (p n : ℕ) (A : Set (Fin (Wp p n) → ℝ)) : Set (Fin (NB p n) → ℝ) :=
  ((((pPullP p n A ∩ pPosEP p n) ∩ pRneP p n) ∩ pSqAllP p n) ∩ pYneP p n) ∩ pEpsP p n

/-! ## 4  The other pieces -/

/-- Forget `v` and the `n+1` cube coordinates. -/
def G1P (p n : ℕ) (A : Set (Fin (Wp p n) → ℝ)) : Set (Fin (W2 p n) → ℝ) :=
  projLastIter (W2 p n) (n+2) (BigSetP p n A)

/-- `ρ ≠ 0` and not in `G1`. -/
def KsetP (p n : ℕ) (A : Set (Fin (Wp p n) → ℝ)) : Set (Fin (W2 p n) → ℝ) :=
  {ξ : Fin (W2 p n) → ℝ | ξ (rIdx2 p n) ≠ 0} ∩ (G1P p n A)ᶜ

/-- Forget `ρ`. -/
def P1P (p n : ℕ) (A : Set (Fin (Wp p n) → ℝ)) : Set (Fin (W1 p n) → ℝ) :=
  projLast (KsetP p n A)

/-- Not in `P1` and `ε > 0`. -/
def P2P (p n : ℕ) (A : Set (Fin (Wp p n) → ℝ)) : Set (Fin (W1 p n) → ℝ) :=
  (P1P p n A)ᶜ ∩ {ξ : Fin (W1 p n) → ℝ | 0 < ξ (eIdx1 p n)}

/-- Forget `ε`. -/
def BcP (p n : ℕ) (A : Set (Fin (Wp p n) → ℝ)) : Set (Fin (Wp p n) → ℝ) :=
  projLast (P2P p n A)

/-- The complement of `Bc`: the fibre-limit set. -/
def BsetP (p n : ℕ) (A : Set (Fin (Wp p n) → ℝ)) : Set (Fin (Wp p n) → ℝ) := (BcP p n A)ᶜ

/-! ## 5  The two semantic descriptions -/

/-- The `∃ε>0 ∀ρ≠0 ∃x∃v` description (the complement of the fibre-limit set). -/
def CoreP (p n : ℕ) (A : Set (Fin (Wp p n) → ℝ)) : Set (Fin (Wp p n) → ℝ) :=
  {w | ∃ ε : ℝ, 0 < ε ∧ ∀ ρ : ℝ, ρ ≠ 0 →
    ∃ (x : Fin (n+1) → ℝ) (v : ℝ),
      Fin.snoc (Fin.append (Work.WilkG4c.parPt (Fin.init w)) x) v ∈ A ∧
      (∀ j, (x j - Work.WilkG4c.cubePt (Fin.init w) j) ^ 2 ≤ ρ ^ 2) ∧
      x ≠ Work.WilkG4c.cubePt (Fin.init w) ∧
      ε ^ 2 < (v - w (Fin.last (p + (n+1)))) ^ 2}

/-- The fibre-limit set of the statement. -/
def LimeqP (p n : ℕ) (A : Set (Fin (Wp p n) → ℝ)) : Set (Fin (Wp p n) → ℝ) :=
  {w | ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ x : Fin (n+1) → ℝ, x ≠ Work.WilkG4c.cubePt (Fin.init w) →
      (∀ j, |x j - Work.WilkG4c.cubePt (Fin.init w) j| < δ) →
      ∀ v : ℝ, Fin.snoc (Fin.append (Work.WilkG4c.parPt (Fin.init w)) x) v ∈ A →
        |v - w (Fin.last (p + (n+1)))| ≤ ε}

end Work.WilG4c
