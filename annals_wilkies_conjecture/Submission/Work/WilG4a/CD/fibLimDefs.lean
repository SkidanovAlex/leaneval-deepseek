import Mathlib
import Submission.Work.WilG4a.Defs
import Submission.Work.WilG4a.subst_mem
import Submission.Work.WilG4a.liftNM_mem
import Submission.Work.WilG1.Calc.pos_mem
import Submission.Work.WilkiesH.Omega.omega_poly_le
import Submission.Work.WilkiesH.Omega.omega_poly_lt
import Submission.Work.WilkiesH.Omega.omega_poly_ne

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Classical

namespace Work.WilG4a.CD

open WilkiesDesign

/-!
# `fibreLimitEqMem` : the fibre_y-limit set is `Ω`-definable

For `A ⊆ ℝ^{p+2}` (coordinates `(u, x, y)` of a parametrised family) we build the set of
`w : Fin (p+2) → ℝ` such that the `A`-values `v` along the fibre_y `t ↦ (u, t, v)` tend to
`w (Fin.last (p+1))` as `t → w ⟨p⟩`.

The `∀ε>0 ∃δ>0 ∀t …` condition is rewritten, over `ℝ`, as `∃ε>0 ∀ρ≠0 ∃t∃v, …`; the `∃`/`∀`
quantifiers are then eliminated by projections and complements in the big space with
coordinates `(w | ε | ρ | t | v)`, and the atomic conditions `ε>0`, `ρ≠0`, `(t-y₀)² ≤ ρ²`,
`t ≠ y₀`, `ε² < (v-v₀)²`, `(u,t,v) ∈ A` are supplied by the `Ω`-calculus.

## The layout

The big space is `ℝ^{p+6}` with coordinates

* `0 … p+1` : `w`
* `p+2`     : `ε`
* `p+3`     : `ρ`
* `p+4`     : `t`
* `p+5`     : `v`

and the substitution map `iota p : Fin (p+2) → Fin (p+6)` sends the first `p` coordinates of
`A` to the first `p` coordinates of the big space, the `x`-coordinate (index `p`) to `t`, and
the `y`-coordinate (index `p+1`) to `v`.
-/

/-! ## §1  The index layout -/

/-- Substitution map of the big space. -/
def iota (p : ℕ) (j : Fin (p+2)) : Fin (p+6) :=
  if h : (j : ℕ) < p then ⟨(j : ℕ), by omega⟩ else ⟨(j : ℕ) + 4, by omega⟩

/-- The `ε`-slot (big space). -/
def eIdx (p : ℕ) : Fin (p+6) := ⟨p+2, by omega⟩
/-- The `ρ`-slot (big space). -/
def rIdx (p : ℕ) : Fin (p+6) := ⟨p+3, by omega⟩
/-- The `t`-slot (big space). -/
def tIdx (p : ℕ) : Fin (p+6) := ⟨p+4, by omega⟩
/-- The `v`-slot (big space). -/
def vIdx_y (p : ℕ) : Fin (p+6) := ⟨p+5, by omega⟩
/-- The `y₀`-slot (big space). -/
def yIdx_y (p : ℕ) : Fin (p+6) := ⟨p, by omega⟩
/-- The `v₀`-slot (big space). -/
def v0Idx (p : ℕ) : Fin (p+6) := ⟨p+1, by omega⟩

/-- The `ε`-slot in `ℝ^{p+4}`. -/
def eIdx4 (p : ℕ) : Fin (p+4) := ⟨p+2, by omega⟩
/-- The `ρ`-slot in `ℝ^{p+4}`. -/
def rIdx4 (p : ℕ) : Fin (p+4) := ⟨p+3, by omega⟩
/-- The `y₀`-slot in `ℝ^{p+4}`. -/
def yIdx4 (p : ℕ) : Fin (p+4) := ⟨p, by omega⟩
/-- The `v₀`-slot in `ℝ^{p+4}`. -/
def v0Idx4 (p : ℕ) : Fin (p+4) := ⟨p+1, by omega⟩

/-- The `ε`-slot in `ℝ^{p+3}`. -/
def eIdx3 (p : ℕ) : Fin (p+3) := ⟨p+2, by omega⟩
/-- The `y₀`-slot in `ℝ^{p+3}`. -/
def yIdx3 (p : ℕ) : Fin (p+3) := ⟨p, by omega⟩
/-- The `v₀`-slot in `ℝ^{p+3}`. -/
def v0Idx3 (p : ℕ) : Fin (p+3) := ⟨p+1, by omega⟩

/-- The `y₀`-slot in `ℝ^{p+2}`. -/
def yIdx2 (p : ℕ) : Fin (p+2) := ⟨p, by omega⟩
/-- The `v₀`-slot in `ℝ^{p+2}`. -/
def v0Idx2 (p : ℕ) : Fin (p+2) := ⟨p+1, by omega⟩

/-! ## §2  Coordinate projections and the fibre_y -/

/-- The first `p` coordinates of a point of `ℝ^{p+2}`. -/
def pre2 (p : ℕ) (w : Fin (p+2) → ℝ) : Fin p → ℝ :=
  fun i => w (Fin.castSucc (Fin.castSucc i))

/-- The first `p` coordinates of a point of `ℝ^{p+3}`. -/
def pre3 (p : ℕ) (ξ : Fin (p+3) → ℝ) : Fin p → ℝ :=
  fun i => ξ (Fin.castSucc (Fin.castSucc (Fin.castSucc i)))

/-- The first `p` coordinates of a point of `ℝ^{p+4}`. -/
def pre4 (p : ℕ) (ζ : Fin (p+4) → ℝ) : Fin p → ℝ :=
  fun i => ζ (Fin.castSucc (Fin.castSucc (Fin.castSucc (Fin.castSucc i))))

/-- The first `p` coordinates of a point of `ℝ^{p+6}`. -/
def pre6 (p : ℕ) (z : Fin (p+6) → ℝ) : Fin p → ℝ :=
  fun i => z (Fin.castSucc (Fin.castSucc (Fin.castSucc (Fin.castSucc (Fin.castSucc
    (Fin.castSucc i))))))

/-- The fibre_y point of the family `A` at `(w, t, v)`. -/
def fibre_y (p : ℕ) (w : Fin (p+2) → ℝ) (t v : ℝ) : Fin (p+2) → ℝ :=
  Fin.snoc (Fin.snoc (Fin.init (Fin.init w)) t) v

/-- The generic point of the big space with data `(ζ, t, v)`. -/
def Zgen (p : ℕ) (ζ : Fin (p+4) → ℝ) (t v : ℝ) : Fin (p+6) → ℝ :=
  Fin.snoc (Fin.snoc ζ t) v

/-- The generic point of `ℝ^{p+4}` with data `(ξ, ρ)`. -/
def Ygen (p : ℕ) (ξ : Fin (p+3) → ℝ) (r : ℝ) : Fin (p+4) → ℝ := Fin.snoc ξ r

/-- The generic point of `ℝ^{p+3}` with data `(w, ε)`. -/
def Xgen (p : ℕ) (w : Fin (p+2) → ℝ) (ε : ℝ) : Fin (p+3) → ℝ := Fin.snoc w ε

/-! ## §3  Index evaluation lemmas -/

lemma iota_lt {p : ℕ} {j : Fin (p+2)} (h : (j : ℕ) < p) :
    iota p j = (⟨(j : ℕ), by omega⟩ : Fin (p+6)) := by
  simp only [iota]; rw [dif_pos h]

lemma iota_p (p : ℕ) : iota p ⟨p, by omega⟩ = tIdx p := by
  simp only [iota, tIdx]; rw [dif_neg (show ¬ (p < p) by omega)]

lemma iota_p1 (p : ℕ) : iota p ⟨p+1, by omega⟩ = vIdx_y p := by
  simp only [iota, vIdx_y]; rw [dif_neg (show ¬ (p+1 < p) by omega)]

lemma Zgen_v (p : ℕ) (ζ : Fin (p+4) → ℝ) (t v : ℝ) : Zgen p ζ t v (vIdx_y p) = v := by
  rw [show vIdx_y p = Fin.last (p+5) from Fin.ext rfl, Zgen, Fin.snoc_last]

lemma Zgen_t (p : ℕ) (ζ : Fin (p+4) → ℝ) (t v : ℝ) : Zgen p ζ t v (tIdx p) = t := by
  rw [show tIdx p = Fin.castSucc (Fin.last (p+4)) from Fin.ext rfl, Zgen,
    Fin.snoc_castSucc, Fin.snoc_last]

lemma Zgen_e (p : ℕ) (ζ : Fin (p+4) → ℝ) (t v : ℝ) :
    Zgen p ζ t v (eIdx p) = ζ (eIdx4 p) := by
  rw [show eIdx p = Fin.castSucc (Fin.castSucc (eIdx4 p)) from Fin.ext rfl, Zgen,
    Fin.snoc_castSucc, Fin.snoc_castSucc]

lemma Zgen_r (p : ℕ) (ζ : Fin (p+4) → ℝ) (t v : ℝ) :
    Zgen p ζ t v (rIdx p) = ζ (rIdx4 p) := by
  rw [show rIdx p = Fin.castSucc (Fin.castSucc (rIdx4 p)) from Fin.ext rfl, Zgen,
    Fin.snoc_castSucc, Fin.snoc_castSucc]

lemma Zgen_y (p : ℕ) (ζ : Fin (p+4) → ℝ) (t v : ℝ) :
    Zgen p ζ t v (yIdx_y p) = ζ (yIdx4 p) := by
  rw [show yIdx_y p = Fin.castSucc (Fin.castSucc (yIdx4 p)) from Fin.ext rfl, Zgen,
    Fin.snoc_castSucc, Fin.snoc_castSucc]

lemma Zgen_v0 (p : ℕ) (ζ : Fin (p+4) → ℝ) (t v : ℝ) :
    Zgen p ζ t v (v0Idx p) = ζ (v0Idx4 p) := by
  rw [show v0Idx p = Fin.castSucc (Fin.castSucc (v0Idx4 p)) from Fin.ext rfl, Zgen,
    Fin.snoc_castSucc, Fin.snoc_castSucc]

lemma Ygen_r (p : ℕ) (ξ : Fin (p+3) → ℝ) (r : ℝ) : Ygen p ξ r (rIdx4 p) = r := by
  rw [show rIdx4 p = Fin.last (p+3) from Fin.ext rfl, Ygen, Fin.snoc_last]

lemma Ygen_e (p : ℕ) (ξ : Fin (p+3) → ℝ) (r : ℝ) : Ygen p ξ r (eIdx4 p) = ξ (eIdx3 p) := by
  rw [show eIdx4 p = Fin.castSucc (eIdx3 p) from Fin.ext rfl, Ygen, Fin.snoc_castSucc]

lemma Ygen_y (p : ℕ) (ξ : Fin (p+3) → ℝ) (r : ℝ) : Ygen p ξ r (yIdx4 p) = ξ (yIdx3 p) := by
  rw [show yIdx4 p = Fin.castSucc (yIdx3 p) from Fin.ext rfl, Ygen, Fin.snoc_castSucc]

lemma Ygen_v0 (p : ℕ) (ξ : Fin (p+3) → ℝ) (r : ℝ) :
    Ygen p ξ r (v0Idx4 p) = ξ (v0Idx3 p) := by
  rw [show v0Idx4 p = Fin.castSucc (v0Idx3 p) from Fin.ext rfl, Ygen, Fin.snoc_castSucc]

lemma Xgen_e (p : ℕ) (w : Fin (p+2) → ℝ) (ε : ℝ) : Xgen p w ε (eIdx3 p) = ε := by
  rw [show eIdx3 p = Fin.last (p+2) from Fin.ext rfl, Xgen, Fin.snoc_last]

lemma Xgen_y (p : ℕ) (w : Fin (p+2) → ℝ) (ε : ℝ) : Xgen p w ε (yIdx3 p) = w (yIdx2 p) := by
  rw [show yIdx3 p = Fin.castSucc (yIdx2 p) from Fin.ext rfl, Xgen, Fin.snoc_castSucc]

lemma Xgen_v0 (p : ℕ) (w : Fin (p+2) → ℝ) (ε : ℝ) :
    Xgen p w ε (v0Idx3 p) = w (v0Idx2 p) := by
  rw [show v0Idx3 p = Fin.castSucc (v0Idx2 p) from Fin.ext rfl, Xgen, Fin.snoc_castSucc]

lemma pre4_Ygen (p : ℕ) (ξ : Fin (p+3) → ℝ) (r : ℝ) : pre4 p (Ygen p ξ r) = pre3 p ξ := by
  funext i
  simp only [pre4, pre3, Ygen, Fin.snoc_castSucc]

lemma pre3_Xgen (p : ℕ) (w : Fin (p+2) → ℝ) (ε : ℝ) : pre3 p (Xgen p w ε) = pre2 p w := by
  funext i
  simp only [pre3, pre2, Xgen, Fin.snoc_castSucc]

lemma pre6_Zgen (p : ℕ) (ζ : Fin (p+4) → ℝ) (t v : ℝ) :
    pre6 p (Zgen p ζ t v) = pre4 p ζ := by
  funext i
  simp only [pre6, pre4, Zgen, Fin.snoc_castSucc]

lemma init_init (p : ℕ) (w : Fin (p+2) → ℝ) : Fin.init (Fin.init w) = pre2 p w := rfl

lemma fibre_eq (p : ℕ) (w : Fin (p+2) → ℝ) (t v : ℝ) :
    fibre_y p w t v = Fin.snoc (Fin.snoc (pre2 p w) t) v := by
  rw [fibre_y, init_init]

lemma init_last (p : ℕ) (w : Fin (p+2) → ℝ) :
    (Fin.init w) (Fin.last p) = w (yIdx2 p) :=
  congrArg w (show Fin.castSucc (Fin.last p) = yIdx2 p from Fin.ext rfl)

lemma last_eq (p : ℕ) (w : Fin (p+2) → ℝ) : w (Fin.last (p+1)) = w (v0Idx2 p) :=
  congrArg w (show Fin.last (p+1) = v0Idx2 p from Fin.ext rfl)

/-- Evaluation of the pullback of `z` along `iota p` as a nested `Fin.snoc`. -/
lemma pullback_eq (p : ℕ) (z : Fin (p+6) → ℝ) :
    (fun j : Fin (p+2) => z (iota p j)) =
      Fin.snoc (Fin.snoc (pre6 p z) (z (tIdx p))) (z (vIdx_y p)) := by
  funext j
  refine Fin.lastCases ?_ ?_ j
  · rw [Fin.snoc_last]
    rw [show (Fin.last (p+1) : Fin (p+2)) = ⟨p+1, by omega⟩ from Fin.ext rfl]
    rw [iota_p1]
  · intro i
    rw [Fin.snoc_castSucc]
    refine Fin.lastCases ?_ ?_ i
    · rw [Fin.snoc_last]
      rw [show (Fin.castSucc (Fin.last p) : Fin (p+2)) = ⟨p, by omega⟩ from Fin.ext rfl]
      rw [iota_p]
    · intro i'
      rw [Fin.snoc_castSucc]
      rw [show (Fin.castSucc (Fin.castSucc i') : Fin (p+2)) = ⟨(i' : ℕ), by omega⟩
        from Fin.ext rfl]
      have hlt : ((⟨(i' : ℕ), by omega⟩ : Fin (p+2)) : ℕ) < p := i'.isLt
      rw [iota_lt hlt]
      rw [show (⟨(i' : ℕ), by omega⟩ : Fin (p+6)) = Fin.castSucc (Fin.castSucc (Fin.castSucc
        (Fin.castSucc (Fin.castSucc (Fin.castSucc i'))))) from Fin.ext rfl]
      rfl

/-! ## §4  The six pieces of the big set -/

/-- The pullback of `A` along `iota p`. -/
def pPull (p : ℕ) (A : Set (Fin (p+2) → ℝ)) : Set (Fin (p+6) → ℝ) :=
  {z | (fun j : Fin (p+2) => z (iota p j)) ∈ A}

/-- `ε > 0`. -/
def pPosE (p : ℕ) : Set (Fin (p+6) → ℝ) := {z | 0 < z (eIdx p)}

/-- `ρ ≠ 0`. -/
def pRne (p : ℕ) : Set (Fin (p+6) → ℝ) := {z | z (rIdx p) ≠ 0}

/-- `(t - y₀)² ≤ ρ²`. -/
def pSq (p : ℕ) : Set (Fin (p+6) → ℝ) :=
  {z | (z (tIdx p) - z (yIdx_y p)) ^ 2 ≤ (z (rIdx p)) ^ 2}

/-- `t ≠ y₀`. -/
def pTne (p : ℕ) : Set (Fin (p+6) → ℝ) := {z | z (tIdx p) ≠ z (yIdx_y p)}

/-- `ε² < (v - v₀)²`. -/
def pEps (p : ℕ) : Set (Fin (p+6) → ℝ) :=
  {z | (z (eIdx p)) ^ 2 < (z (vIdx_y p) - z (v0Idx p)) ^ 2}

/-- The big set. -/
def BigSet (p : ℕ) (A : Set (Fin (p+2) → ℝ)) : Set (Fin (p+6) → ℝ) :=
  ((pPull p A ∩ pPosE p) ∩ pRne p ∩ pSq p ∩ pTne p) ∩ pEps p

/-! ## §5  Degree bookkeeping -/

lemma td_negX_le {N : ℕ} (i : Fin N) :
    (-MvPolynomial.X i : MvPolynomial (Fin N) ℝ).totalDegree ≤ 1 := by
  rw [MvPolynomial.totalDegree_neg]
  exact le_of_eq (MvPolynomial.totalDegree_X i)

lemma td_sub_le {N : ℕ} (i j : Fin N) :
    (MvPolynomial.X i - MvPolynomial.X j : MvPolynomial (Fin N) ℝ).totalDegree ≤ 1 := by
  refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
  rw [max_le_iff]
  exact ⟨le_of_eq (MvPolynomial.totalDegree_X i), le_of_eq (MvPolynomial.totalDegree_X j)⟩

lemma td_sq_le {σ : Type*} {R : Type*} [CommSemiring R]
    {A : MvPolynomial σ R} (hA : A.totalDegree ≤ 1) : (A ^ 2).totalDegree ≤ 2 := by
  refine le_trans (MvPolynomial.totalDegree_pow A 2) ?_
  calc 2 * A.totalDegree ≤ 2 * 1 := Nat.mul_le_mul_left 2 hA
    _ = 2 := rfl

/-! ## §6  `Ω`-membership of the six pieces -/

theorem pPull_mem {S : SOMin} {p F D : ℕ} {A : Set (Fin (p+2) → ℝ)}
    (hA : A ∈ S.Ω F D (p+2)) :
    pPull p A ∈ S.Ω (F + 2 * ((p+6) + (p+2)) + 1) (D + 2) (p+6) := by
  have h := Work.WilG4a.subst_mem S (iota p) hA
  rwa [show pPull p A = {x : Fin (p+6) → ℝ | x ∘ (iota p) ∈ A} from rfl]

theorem pPosE_mem (S : SOMin) (p : ℕ) : pPosE p ∈ S.Ω (p+9) 3 (p+6) := by
  have h := Work.WilkiesH.Omega.omega_poly_lt S (p+6)
    (-MvPolynomial.X (eIdx p) : MvPolynomial (Fin (p+6)) ℝ)
  rw [show {x : Fin (p+6) → ℝ |
        MvPolynomial.eval x (-MvPolynomial.X (eIdx p) : MvPolynomial (Fin (p+6)) ℝ) < 0}
      = pPosE p from by
    ext z
    simp only [pPosE, Set.mem_ofPred_eq, MvPolynomial.eval_neg, MvPolynomial.eval_X]
    exact neg_lt_zero] at h
  refine Work.WilG1.Omega.mono h (by omega) ?_
  have := td_negX_le (eIdx p); omega

theorem pRne_mem (S : SOMin) (p : ℕ) : pRne p ∈ S.Ω (p+7) 1 (p+6) := by
  have h := Work.WilkiesH.Omega.omega_poly_ne S (p+6)
    (MvPolynomial.X (rIdx p) : MvPolynomial (Fin (p+6)) ℝ)
  rw [show {x : Fin (p+6) → ℝ |
        MvPolynomial.eval x (MvPolynomial.X (rIdx p) : MvPolynomial (Fin (p+6)) ℝ) ≠ 0}
      = pRne p from by
    ext z
    simp only [pRne, Set.mem_ofPred_eq, MvPolynomial.eval_X]] at h
  refine Work.WilG1.Omega.mono h (by omega) ?_
  exact le_of_eq (MvPolynomial.totalDegree_X (rIdx p))

theorem pSq_mem (S : SOMin) (p : ℕ) : pSq p ∈ S.Ω (p+8) 4 (p+6) := by
  have h := Work.WilkiesH.Omega.omega_poly_le S (p+6)
    ((MvPolynomial.X (tIdx p) - MvPolynomial.X (yIdx_y p)) ^ 2 -
      (MvPolynomial.X (rIdx p)) ^ 2 : MvPolynomial (Fin (p+6)) ℝ)
  rw [show {x : Fin (p+6) → ℝ |
        MvPolynomial.eval x ((MvPolynomial.X (tIdx p) - MvPolynomial.X (yIdx_y p)) ^ 2 -
          (MvPolynomial.X (rIdx p)) ^ 2 : MvPolynomial (Fin (p+6)) ℝ) ≤ 0}
      = pSq p from by
    ext z
    simp only [pSq, Set.mem_ofPred_eq, MvPolynomial.eval_sub, MvPolynomial.eval_pow,
      MvPolynomial.eval_X]
    constructor <;> intro hh <;> linarith] at h
  refine Work.WilG1.Omega.mono h (by omega) ?_
  have hA : ((MvPolynomial.X (tIdx p) - MvPolynomial.X (yIdx_y p) :
      MvPolynomial (Fin (p+6)) ℝ) ^ 2).totalDegree ≤ 2 := td_sq_le (td_sub_le _ _)
  have hB : ((MvPolynomial.X (rIdx p) : MvPolynomial (Fin (p+6)) ℝ) ^ 2).totalDegree ≤ 2 :=
    td_sq_le (le_of_eq (MvPolynomial.totalDegree_X _))
  have htd : ((MvPolynomial.X (tIdx p) - MvPolynomial.X (yIdx_y p)) ^ 2 -
      (MvPolynomial.X (rIdx p)) ^ 2 : MvPolynomial (Fin (p+6)) ℝ).totalDegree ≤ 2 :=
    le_trans (MvPolynomial.totalDegree_sub _ _) (max_le hA hB)
  omega

theorem pTne_mem (S : SOMin) (p : ℕ) : pTne p ∈ S.Ω (p+7) 1 (p+6) := by
  have h := Work.WilkiesH.Omega.omega_poly_ne S (p+6)
    (MvPolynomial.X (tIdx p) - MvPolynomial.X (yIdx_y p) : MvPolynomial (Fin (p+6)) ℝ)
  rw [show {x : Fin (p+6) → ℝ |
        MvPolynomial.eval x (MvPolynomial.X (tIdx p) - MvPolynomial.X (yIdx_y p) :
          MvPolynomial (Fin (p+6)) ℝ) ≠ 0}
      = pTne p from by
    ext z
    simp only [pTne, Set.mem_ofPred_eq, MvPolynomial.eval_sub, MvPolynomial.eval_X]
    constructor
    · intro hh hc; exact hh (by rw [hc]; ring)
    · intro hh hc; exact hh (by linarith)] at h
  refine Work.WilG1.Omega.mono h (by omega) ?_
  exact td_sub_le (tIdx p) (yIdx_y p)

theorem pEps_mem (S : SOMin) (p : ℕ) : pEps p ∈ S.Ω (p+9) 4 (p+6) := by
  have h := Work.WilkiesH.Omega.omega_poly_lt S (p+6)
    ((MvPolynomial.X (eIdx p)) ^ 2 -
      (MvPolynomial.X (vIdx_y p) - MvPolynomial.X (v0Idx p)) ^ 2 :
        MvPolynomial (Fin (p+6)) ℝ)
  rw [show {x : Fin (p+6) → ℝ |
        MvPolynomial.eval x ((MvPolynomial.X (eIdx p)) ^ 2 -
          (MvPolynomial.X (vIdx_y p) - MvPolynomial.X (v0Idx p)) ^ 2 :
            MvPolynomial (Fin (p+6)) ℝ) < 0}
      = pEps p from by
    ext z
    simp only [pEps, Set.mem_ofPred_eq, MvPolynomial.eval_sub, MvPolynomial.eval_pow,
      MvPolynomial.eval_X]
    constructor <;> intro hh <;> linarith] at h
  refine Work.WilG1.Omega.mono h (by omega) ?_
  have hA : ((MvPolynomial.X (eIdx p) : MvPolynomial (Fin (p+6)) ℝ) ^ 2).totalDegree ≤ 2 :=
    td_sq_le (le_of_eq (MvPolynomial.totalDegree_X _))
  have hB : ((MvPolynomial.X (vIdx_y p) - MvPolynomial.X (v0Idx p) :
      MvPolynomial (Fin (p+6)) ℝ) ^ 2).totalDegree ≤ 2 := td_sq_le (td_sub_le _ _)
  have htd : ((MvPolynomial.X (eIdx p)) ^ 2 -
      (MvPolynomial.X (vIdx_y p) - MvPolynomial.X (v0Idx p)) ^ 2 :
        MvPolynomial (Fin (p+6)) ℝ).totalDegree ≤ 2 :=
    le_trans (MvPolynomial.totalDegree_sub _ _) (max_le hA hB)
  omega

/-! ## §7  `Ω`-membership of the big set -/

/-- Binary intersection at a common format. -/
theorem inter2_same {S : SOMin} {n F D₁ D₂ : ℕ} {X Y : Set (Fin n → ℝ)}
    (hX : X ∈ S.Ω F D₁ n) (hY : Y ∈ S.Ω F D₂ n) :
    X ∩ Y ∈ S.Ω (F + 1) (D₁ + D₂) n := by
  have h := S.inter (F := F) (n := n) (k := 2)
    (fun i : Fin 2 => if i = 0 then D₁ else D₂)
    (fun i : Fin 2 => if i = 0 then X else Y)
    (by intro i
        fin_cases i
        · simpa using hX
        · simpa using hY)
  have hsum : (∑ i : Fin 2, (if i = 0 then D₁ else D₂)) = D₁ + D₂ := by
    rw [Fin.sum_univ_two]; simp
  rw [hsum] at h
  rwa [Work.WilG1.Omega.iInter_fin_two] at h

theorem BigSet_mem {S : SOMin} {p F D : ℕ} {A : Set (Fin (p+2) → ℝ)}
    (hA : A ∈ S.Ω F D (p+2)) :
    BigSet p A ∈ S.Ω (F + 4 * p + 22) (D + 15) (p + 6) := by
  have h1 : pPull p A ∈ S.Ω (F + 4 * p + 17) (D + 2) (p + 6) :=
    Work.WilG1.Omega.mono (pPull_mem (S := S) (p := p) hA) (by omega) le_rfl
  have h2 : pPosE p ∈ S.Ω (F + 4 * p + 17) 3 (p + 6) :=
    Work.WilG1.Omega.mono (pPosE_mem S p) (by omega) le_rfl
  have h3 : pRne p ∈ S.Ω (F + 4 * p + 17) 1 (p + 6) :=
    Work.WilG1.Omega.mono (pRne_mem S p) (by omega) le_rfl
  have h4 : pSq p ∈ S.Ω (F + 4 * p + 17) 4 (p + 6) :=
    Work.WilG1.Omega.mono (pSq_mem S p) (by omega) le_rfl
  have h5 : pTne p ∈ S.Ω (F + 4 * p + 17) 1 (p + 6) :=
    Work.WilG1.Omega.mono (pTne_mem S p) (by omega) le_rfl
  have h6 : pEps p ∈ S.Ω (F + 4 * p + 17) 4 (p + 6) :=
    Work.WilG1.Omega.mono (pEps_mem S p) (by omega) le_rfl
  have s1 : pPull p A ∩ pPosE p ∈ S.Ω ((F + 4 * p + 17) + 1) ((D + 2) + 3) (p + 6) :=
    inter2_same (S := S) h1 h2
  have h3' : pRne p ∈ S.Ω ((F + 4 * p + 17) + 1) 1 (p + 6) :=
    Work.WilG1.Omega.mono h3 (by omega) le_rfl
  have s2 : (pPull p A ∩ pPosE p) ∩ pRne p ∈
      S.Ω (((F + 4 * p + 17) + 1) + 1) (((D + 2) + 3) + 1) (p + 6) :=
    inter2_same (S := S) s1 h3'
  have h4' : pSq p ∈ S.Ω (((F + 4 * p + 17) + 1) + 1) 4 (p + 6) :=
    Work.WilG1.Omega.mono h4 (by omega) le_rfl
  have s3 : ((pPull p A ∩ pPosE p) ∩ pRne p) ∩ pSq p ∈
      S.Ω ((((F + 4 * p + 17) + 1) + 1) + 1) ((((D + 2) + 3) + 1) + 4) (p + 6) :=
    inter2_same (S := S) s2 h4'
  have h5' : pTne p ∈ S.Ω ((((F + 4 * p + 17) + 1) + 1) + 1) 1 (p + 6) :=
    Work.WilG1.Omega.mono h5 (by omega) le_rfl
  have s4 : (((pPull p A ∩ pPosE p) ∩ pRne p) ∩ pSq p) ∩ pTne p ∈
      S.Ω (((((F + 4 * p + 17) + 1) + 1) + 1) + 1) (((((D + 2) + 3) + 1) + 4) + 1) (p + 6) :=
    inter2_same (S := S) s3 h5'
  have h6' : pEps p ∈ S.Ω (((((F + 4 * p + 17) + 1) + 1) + 1) + 1) 4 (p + 6) :=
    Work.WilG1.Omega.mono h6 (by omega) le_rfl
  have s5 : ((((pPull p A ∩ pPosE p) ∩ pRne p) ∩ pSq p) ∩ pTne p) ∩ pEps p ∈
      S.Ω ((((((F + 4 * p + 17) + 1) + 1) + 1) + 1) + 1)
        ((((((D + 2) + 3) + 1) + 4) + 1) + 4) (p + 6) :=
    inter2_same (S := S) s4 h6'
  exact Work.WilG1.Omega.mono s5 (by omega) (by omega)

/-! ## §8  The intermediate sets -/

/-- Forget the last two (`t`, `v`) coordinates of the big set. -/
def G1 (p : ℕ) (A : Set (Fin (p+2) → ℝ)) : Set (Fin (p+4) → ℝ) :=
  projLast (projLast (BigSet p A))

/-- `ρ ≠ 0` and not in `G1`. -/
def Kset (p : ℕ) (A : Set (Fin (p+2) → ℝ)) : Set (Fin (p+4) → ℝ) :=
  {ζ | ζ (rIdx4 p) ≠ 0} ∩ (G1 p A)ᶜ

/-- Forget the `ρ`-coordinate. -/
def P1 (p : ℕ) (A : Set (Fin (p+2) → ℝ)) : Set (Fin (p+3) → ℝ) := projLast (Kset p A)

/-- Not in `P1` and `ε > 0`. -/
def P2 (p : ℕ) (A : Set (Fin (p+2) → ℝ)) : Set (Fin (p+3) → ℝ) :=
  (P1 p A)ᶜ ∩ {ξ | 0 < ξ (eIdx3 p)}

/-- Forget the `ε`-coordinate. -/
def Bc (p : ℕ) (A : Set (Fin (p+2) → ℝ)) : Set (Fin (p+2) → ℝ) := projLast (P2 p A)

/-- The complement of `Bc`: the fibre_y-limit set. -/
def Bset (p : ℕ) (A : Set (Fin (p+2) → ℝ)) : Set (Fin (p+2) → ℝ) := (Bc p A)ᶜ

/-! ## §9  Membership characterisations -/

lemma BigSet_mem_iff (p : ℕ) (A : Set (Fin (p+2) → ℝ)) (z : Fin (p+6) → ℝ) :
    z ∈ BigSet p A ↔ (fun j : Fin (p+2) => z (iota p j)) ∈ A ∧ 0 < z (eIdx p) ∧
      z (rIdx p) ≠ 0 ∧ (z (tIdx p) - z (yIdx_y p)) ^ 2 ≤ (z (rIdx p)) ^ 2 ∧
      z (tIdx p) ≠ z (yIdx_y p) ∧ (z (eIdx p)) ^ 2 < (z (vIdx_y p) - z (v0Idx p)) ^ 2 := by
  simp only [BigSet, pPull, pPosE, pRne, pSq, pTne, pEps, Set.mem_inter_iff,
    Set.mem_ofPred_eq]
  tauto

lemma G1_mem_iff (p : ℕ) (A : Set (Fin (p+2) → ℝ)) (ζ : Fin (p+4) → ℝ) :
    ζ ∈ G1 p A ↔ ∃ t v : ℝ, Fin.snoc (Fin.snoc (pre4 p ζ) t) v ∈ A ∧
      0 < ζ (eIdx4 p) ∧ ζ (rIdx4 p) ≠ 0 ∧ (t - ζ (yIdx4 p)) ^ 2 ≤ (ζ (rIdx4 p)) ^ 2 ∧
      t ≠ ζ (yIdx4 p) ∧ (ζ (eIdx4 p)) ^ 2 < (v - ζ (v0Idx4 p)) ^ 2 := by
  simp only [G1, projLast]
  constructor
  · rintro ⟨t, v, hZ⟩
    have h := (BigSet_mem_iff p A (Zgen p ζ t v)).mp hZ
    rw [pullback_eq, pre6_Zgen, Zgen_e, Zgen_r, Zgen_t, Zgen_y, Zgen_v, Zgen_v0] at h
    exact ⟨t, v, h⟩
  · rintro ⟨t, v, hA, h1, h2, h3, h4, h5⟩
    refine ⟨t, v, (BigSet_mem_iff p A (Zgen p ζ t v)).mpr ?_⟩
    rw [pullback_eq, pre6_Zgen, Zgen_e, Zgen_r, Zgen_t, Zgen_y, Zgen_v, Zgen_v0]
    exact ⟨hA, h1, h2, h3, h4, h5⟩

lemma Kset_mem_iff (p : ℕ) (A : Set (Fin (p+2) → ℝ)) (z : Fin (p+4) → ℝ) :
    z ∈ Kset p A ↔ z (rIdx4 p) ≠ 0 ∧ z ∉ G1 p A := by
  simp only [Kset, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_compl_iff]

lemma P1_mem_iff (p : ℕ) (A : Set (Fin (p+2) → ℝ)) (ξ : Fin (p+3) → ℝ) :
    ξ ∈ P1 p A ↔ ∃ r : ℝ, Ygen p ξ r ∈ Kset p A := Iff.rfl

lemma P2_mem_iff (p : ℕ) (A : Set (Fin (p+2) → ℝ)) (ξ : Fin (p+3) → ℝ) :
    ξ ∈ P2 p A ↔ ξ ∉ P1 p A ∧ 0 < ξ (eIdx3 p) := by
  simp only [P2, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_ofPred_eq]

lemma Bc_mem_iff (p : ℕ) (A : Set (Fin (p+2) → ℝ)) (w : Fin (p+2) → ℝ) :
    w ∈ Bc p A ↔ ∃ ε : ℝ, Xgen p w ε ∈ P2 p A := Iff.rfl

