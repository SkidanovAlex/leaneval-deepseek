/-
# `BridgeSquare/pieceDefs.lean` — the vocabulary of the per-piece identity `piece_eq_psi`

The per-piece identity relates, for each cusp `v` and each unit edge `i` of the `κ_{v,3}`-corner
line, the chart chain `c1 v (Xv v i) (Xv v (i+1))` with (the boundary correction of) `Ψ_M` of the
cellular edge `edgeCell v 1 k`.  Everything is expressed through the *cusp* coordinates

  `Yv v k t = cornerPt (edgeCube v 1 k) + t • eVec (fibreDir v 1) − cuspH`

of the corner edge of the cube `edgeCube v 1 k` (parameter `t ∈ [0,1]`).

The edge and the cell match up under the *reversal* permutation `τ = Fin.rev`:
the interior of the `i`-th unit edge of the corner line lies in the cube `edgeCube v 1 (τ i)`.
-/
import Mathlib
import Submission.Work.BridgeSquare.fibreSteps

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option maxHeartbeats 1000000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped Topology Simplicial
open Convexity

namespace Work.BridgeSquare

noncomputable section

/-- The unit coordinate vector of the cusp coordinate space `E3`. -/
def eVec (j : Fin 3) : cE3 := WithLp.toLp 2 (fun i : Fin 3 => if i = j then (1 : ℝ) else 0)

/-- The lower corner of the cube `a`, as a point of the cusp coordinate space `E3`. -/
def cornerPt (a : Fin 48) : cE3 :=
  WithLp.toLp 2 (fun j : Fin 3 => (Work.Cusp.cubeCorner a j : ℝ))

/-- The point of the corner edge of the cube `edgeCube v 1 k` at parameter `t`, in cusp
coordinates. -/
def Yv (v : Fin 5) (k : Fin 4) (t : ℝ) : cE3 :=
  cornerPt (edgeCube v 1 k) + t • eVec (fibreDir v 1) - Work.RTOwed.cuspH

/-- The reversal permutation of the unit edges of the corner line. -/
def tauV (v : Fin 5) : Fin (fibreLen v 1) ≃ Fin (fibreLen v 1) := Fin.revPerm

/-- The global sign of the `v`-th cusp: `+1` for `v ≤ 3`, `−1` for `v = 4`. -/
def sgnB (v : Fin 5) : ℤ := if (v : ℕ) = 4 then -1 else 1

/-- The per-cusp sign `c_v = (−1)^{v+1}` of the per-piece identity `piece_eq_psi`. -/
def cpsi (v : Fin 5) : ℤ := if (v : ℕ) % 2 = 0 then -1 else 1

theorem cpsi_spec (v : Fin 5) : cpsi v = 1 ∨ cpsi v = -1 := by
  unfold cpsi; split <;> simp

/-- The lattice vector `λ_v` translating the `i`-th chart segment to the corner edge
`Yv v (τ i) ·`. -/
def lamY (v : Fin 5) (i : Fin (fibreLen v 1)) : cE3 :=
  cornerPt (edgeCube v 1 (Fin.castLE (fibreLen_le_four v) (Fin.rev i)))
    + (((i : ℕ) : ℝ) + 1) • eVec (fibreDir v 1)

@[simp] theorem eVec_ofLp (j : Fin 3) (i : Fin 3) :
    (eVec j).ofLp i = if i = j then (1 : ℝ) else 0 := rfl

@[simp] theorem cornerPt_ofLp (a : Fin 48) (j : Fin 3) :
    (cornerPt a).ofLp j = (Work.Cusp.cubeCorner a j : ℝ) := rfl

@[simp] theorem Yv_apply (v : Fin 5) (k : Fin 4) (t : ℝ) (j : Fin 3) :
    (Yv v k t).ofLp j
      = (Work.Cusp.cubeCorner (edgeCube v 1 k) j : ℝ)
          + t * (if j = fibreDir v 1 then 1 else 0) - 1 / 2 := by
  simp only [Yv, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, eVec_ofLp,
    cornerPt_ofLp, Work.RTOwed.cuspH, Fin.isValue]

/-- **The unit step of the `κ_{v,3}` direction is minus the coordinate unit vector.** -/
theorem unitStep_eq_neg_eVec (v : Fin 5) :
    Work.BridgeSquare.unitStep v = - eVec (fibreDir v 1) := by
  apply PiLp.ext
  intro i
  simp only [Work.BridgeSquare.unitStep, Work.Cusp.ofInt3_apply, PiLp.neg_apply, eVec_ofLp]
  fin_cases v <;> fin_cases i <;>
    simp only [Work.BridgeSquare.fibreDir, Work.BridgeSquare.dirKappa, Work.Cusp.kappa,
      Fin.isValue, Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- **`Xv` is the point `−h − i·e_d` of the cusp coordinates.** -/
theorem Xv_eq (v : Fin 5) (i : ℕ) :
    Xv v i = -(((i : ℝ)) • eVec (fibreDir v 1)) - Work.RTOwed.cuspH := by
  rw [Xv, unitStep_eq_neg_eVec, smul_neg]

/-- **The chart segment and the corner edge differ by the lattice vector `lamY`.** -/
theorem cPt_edge_sub (v : Fin 5) (i : Fin (fibreLen v 1))
    (z : StdSimplex ℝ (Fin 2)) :
    cPt (![Xv v (i : ℕ), Xv v ((i : ℕ) + 1)] : Fin 2 → cE3) z
      - cPt (![Yv v (Fin.castLE (fibreLen_le_four v) (Fin.rev i)) 1,
              Yv v (Fin.castLE (fibreLen_le_four v) (Fin.rev i)) 0] : Fin 2 → cE3) z
      = - lamY v i := by
  rw [cPt_eq_sum, cPt_eq_sum, Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hsum : z.weights 0 + z.weights 1 = 1 := by
    have := MbarHomology.Mbar.sum_weights z
    simpa using this
  rw [show z.weights 1 = 1 - z.weights 0 from by linarith]
  rw [Xv_eq, Xv_eq]
  simp only [Yv, lamY]
  module


/-! ## The lattice vector and the chart identification -/

/-- The cube carrying the interior of the `i`-th unit edge is `edgeCube v 1 (τ i)`. -/
theorem cubeOfMod_edgeCube_j1 (v : Fin 5) (i : Fin (fibreLen v 1)) :
    Work.Cusp.cubeOfMod v (fun j : Fin 3 =>
        if j = fibreDir v 1 then (-((i : ℕ) : ℤ) - 1) else 0)
      = edgeCube v 1 (Fin.castLE (fibreLen_le_four v) (Fin.rev i)) := by
  revert v i
  decide

/-- **`lamY` is a cusp lattice vector.** -/
theorem lamY_mem_lattice (v : Fin 5) (i : Fin (fibreLen v 1)) :
    lamY v i ∈ Work.Cusp.lattice v := by
  refine Work.RTOwed.mem_of_latVec Work.RTOwed.cuspCertificates v ?_
  intro j
  have hdvd := Work.RTOwed.cuspCert.cubeOfMod_corner_dvd v
      (fun t : Fin 3 => if t = fibreDir v 1 then (-((i : ℕ) : ℤ) - 1) else 0) j
  rw [cubeOfMod_edgeCube_j1 v i] at hdvd
  obtain ⟨m, hm⟩ := hdvd
  refine ⟨-m, ?_⟩
  have key : (Work.Cusp.cubeCorner
        (edgeCube v 1 (Fin.castLE (fibreLen_le_four v) (Fin.rev i))) j : ℝ)
      + (((i : ℕ) : ℝ) + 1) * (if j = fibreDir v 1 then 1 else 0)
      = - ((if j = fibreDir v 1 then (-((i : ℕ) : ℤ) - 1) else 0)
            - Work.Cusp.cubeCorner
                (edgeCube v 1 (Fin.castLE (fibreLen_le_four v) (Fin.rev i))) j) := by
    by_cases hj : j = fibreDir v 1 <;> simp [hj] <;> ring
  simp only [lamY, cornerPt, eVec, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Fin.isValue]
  rw [key, ← Int.cast_sub, hm]
  push_cast
  ring

/-- **The `i`-th chart segment is the corner edge of the cube `edgeCube v 1 (τ i)`.** -/
theorem chart_eq_Yv (v : Fin 5) (i : Fin (fibreLen v 1)) :
    c1 v (Xv v (i : ℕ)) (Xv v ((i : ℕ) + 1))
      = c1 v (Yv v (Fin.castLE (fibreLen_le_four v) (Fin.rev i)) 1)
             (Yv v (Fin.castLE (fibreLen_le_four v) (Fin.rev i)) 0) := by
  unfold c1 cChain
  congr 1
  apply ContinuousMap.ext
  intro z
  simp only [cSimp_apply]
  exact Work.RTOwed.mbarPtC_periodic v (by
    rw [cPt_edge_sub v i z]
    exact AddSubgroup.neg_mem _ (lamY_mem_lattice v i))


/-- The sign of a genuine unit edge is `±1`. -/
theorem edgeSign_pm (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 1) :
    edgeSign v 1 k = 1 ∨ edgeSign v 1 k = -1 := by
  revert v k hk; decide

/-- The reversal index `eIdx v (Fin.rev i)` is a genuine edge index. -/
theorem eIdx_rev_lt (v : Fin 5) (i : Fin (fibreLen v 1)) :
    (eIdx v (Fin.revPerm i) : ℕ) < fibreLen v 1 := by
  show (Fin.rev i : ℕ) < fibreLen v 1
  exact (Fin.rev i).isLt

end

end Work.BridgeSquare
