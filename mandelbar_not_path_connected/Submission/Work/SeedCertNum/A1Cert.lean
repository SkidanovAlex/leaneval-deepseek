/-
Copyright: subproject `Submission/Work/SeedCertNum/` of `mandelbar_not_path_connected`.

# The A1 Krawczyk certificate: data, Boolean check, soundness statement

Item **A1** of the `SeedCertNum` contract (`NOTES_LEAD_mandelbar_noncusp.md` §2.2).  `KrawData`
collects the *dyadic* inputs of the certificate for the unique zero `(z₁, c_b)` of

  `Φ(x,y,t) = (Re (g z - z), Im (g z - z), ∏_{k<5} (2‖T^k z‖)² - 1)`,  `z = x+iy`, `c = x₀+it`,

and `KrawData.ok` is the whole numerical check as a single `Bool`:

* `0 < r` (`r` the radius of the box);
* for every `(i,j)` the interval `Jint (i,j)` (the enclosure of the Jacobian of `Φ` over the
  box `Xz × Xt` computed by `Submission/Work/SeedCertNum/A1Defs.lean`) is contained in
  `[Ac i j - Δ i j, Ac i j + Δ i j]`;
* `etaBound ≤ eta`, where `etaBound = β · ‖Φ u₀‖` is the *computable* bound on `‖M Φ u₀‖`;
* the ball condition `(α + β·ε)·r + η < r` with `α = Σ_{ij} |(M A - 1)_{ij}|`,
  `β = Σ_{ij}|M_{ij}|`, `ε = Σ_{ij} Δ_{ij}`.

The soundness theorem `kraw_sound` (delegated) turns `ok = true` into
`∃! u ∈ closedBall u₀ r, Φ u = 0`, by feeding the four numeric hypotheses to
`Work.SeedCertNum.krawczyk_numeric`.

The residual bound `etaBound` is computed on the *degenerate* boxes `Xzp × Xtp` at the centre
`u₀`, where every box operation is exact, so `residBound = ‖Φ u₀‖` exactly; the interval
arithmetic then only has to bound `‖M v‖ ≤ β ‖v‖`.
-/
import Mathlib
import Submission.Work.SeedCertNum.Mat3
import Submission.Work.SeedCertNum.Jet2

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCert

open LeanEval.ComplexAnalysis (Tantibar)

noncomputable section

/-- The dyadic literal `n / 2^e`. -/
def dy (n : ℤ) (e : ℕ) : Dya := ⟨n, e⟩

/-- A `3×3` dyadic matrix. -/
def m3 (a00 a01 a02 a10 a11 a12 a20 a21 a22 : Dya) : Fin 3 → Fin 3 → Dya :=
  ![![a00, a01, a02], ![a10, a11, a12], ![a20, a21, a22]]

/-- The sum of all nine entries (right-nested). -/
def matSumDya (a : Fin 3 → Fin 3 → Dya) : Dya :=
  Dya.add (a 0 0) (Dya.add (a 0 1) (Dya.add (a 0 2) (Dya.add (a 1 0) (Dya.add (a 1 1)
    (Dya.add (a 1 2) (Dya.add (a 2 0) (Dya.add (a 2 1) (a 2 2))))))))

/-- Entrywise absolute value. -/
def matAbsDya (a : Fin 3 → Fin 3 → Dya) : Fin 3 → Fin 3 → Dya := fun i j => Dya.abs (a i j)

/-- Entrywise difference. -/
def matSubDya (a b : Fin 3 → Fin 3 → Dya) : Fin 3 → Fin 3 → Dya := fun i j => Dya.sub (a i j) (b i j)

/-- Matrix product over the dyadics. -/
def matMulDya (a b : Fin 3 → Fin 3 → Dya) : Fin 3 → Fin 3 → Dya :=
  fun i j => Dya.add (Dya.mul (a i 0) (b 0 j)) (Dya.add (Dya.mul (a i 1) (b 1 j)) (Dya.mul (a i 2) (b 2 j)))

/-- The identity matrix over the dyadics. -/
def matIdDya : Fin 3 → Fin 3 → Dya := fun i j => if i = j then Dya.one else Dya.zero

/-- The dyadic data of an A1 Krawczyk certificate. -/
structure KrawData where
  /-- `Re c`, kept at a fixed rational value. -/
  x₀ : Dya
  /-- `Re` of the centre of the box for `z`. -/
  ux : Dya
  /-- `Im` of the centre of the box for `z`. -/
  uy : Dya
  /-- `Im c` at the centre. -/
  ut : Dya
  /-- The radius of the box (the same in all three coordinates). -/
  r : Dya
  /-- The dyadic matrix `A ≈ JΦ(u₀)`. -/
  Ac : Fin 3 → Fin 3 → Dya
  /-- The dyadic matrix `M ≈ A⁻¹`. -/
  Mb : Fin 3 → Fin 3 → Dya
  /-- Entrywise half-widths: `Jint (i,j) ⊆ [Ac i j - Δ i j, Ac i j + Δ i j]`. -/
  Δ : Fin 3 → Fin 3 → Dya
  /-- An upper bound for `‖M Φ u₀‖`. -/
  eta : Dya
deriving DecidableEq, Repr

namespace KrawData

/-- The centre `u₀ ∈ ℝ³`. -/
def u₀ (D : KrawData) : E3 := (D.ux.toReal, D.uy.toReal, D.ut.toReal)

/-- The radius. -/
def rad (D : KrawData) : ℝ := D.r.toReal

/-- The box for `z`, centred at `(ux,uy)`. -/
def Xz (D : KrawData) : CBox :=
  ⟨Dya.sub D.ux D.r, Dya.add D.ux D.r, Dya.sub D.uy D.r, Dya.add D.uy D.r⟩

/-- The interval for `t = Im c`, centred at `ut`. -/
def Xt (D : KrawData) : IV := ⟨Dya.sub D.ut D.r, Dya.add D.ut D.r⟩

/-- The parameter box `c ∈ x₀ + i·Xt`. -/
def Ctyp (D : KrawData) : CBox := pbox D.x₀ D.Xt

/-- The degenerate box at the centre `z₀`. -/
def Xzp (D : KrawData) : CBox := ⟨D.ux, D.ux, D.uy, D.uy⟩

/-- The degenerate interval at `ut`. -/
def Xtp (D : KrawData) : IV := ⟨D.ut, D.ut⟩

/-- The degenerate parameter box at the centre. -/
def Ctypp (D : KrawData) : CBox := pbox D.x₀ D.Xtp

/-- `Ac` as reals. -/
def Acr (D : KrawData) : Fin 3 → Fin 3 → ℝ := fun i j => (D.Ac i j).toReal

/-- `Mb` as reals. -/
def Mbr (D : KrawData) : Fin 3 → Fin 3 → ℝ := fun i j => (D.Mb i j).toReal

/-- `Δ` as reals. -/
def Δr (D : KrawData) : Fin 3 → Fin 3 → ℝ := fun i j => (D.Δ i j).toReal

/-- `α = Σ_{ij} |(M A - 1)_{ij}|`. -/
def alpha (D : KrawData) : Dya :=
  matSumDya (matAbsDya (matSubDya (matMulDya D.Mb D.Ac) matIdDya))

/-- `β = Σ_{ij} |M_{ij}|`. -/
def beta (D : KrawData) : Dya := matSumDya (matAbsDya D.Mb)

/-- `ε = Σ_{ij} Δ_{ij}`. -/
def eps (D : KrawData) : Dya := matSumDya (matAbsDya D.Δ)

/-- The enclosure of `Φ u₀`, computed on the degenerate boxes at the centre. -/
def residBox (D : KrawData) : IV × IV × IV :=
  let Z := D.Xzp
  let C := D.Ctypp
  let V := boxV C Z 5
  ((V.sub Z).re, (V.sub Z).im, IV.sub (boxPi C Z) ⟨Dya.one, Dya.one⟩)

/-- A dyadic upper bound for `‖Φ u₀‖` (exact, since the boxes are degenerate). -/
def residBound (D : KrawData) : Dya :=
  Dya.max (Dya.max (Dya.maxAbs D.residBox.1.lo D.residBox.1.hi)
      (Dya.maxAbs D.residBox.2.1.lo D.residBox.2.1.hi))
    (Dya.maxAbs D.residBox.2.2.lo D.residBox.2.2.hi)

/-- A dyadic upper bound for `‖M (Φ u₀)‖`. -/
def etaBound (D : KrawData) : Dya := Dya.mul D.beta D.residBound

/-- The entrywise checks `Jint (i,j) ⊆ [Ac i j - Δ i j, Ac i j + Δ i j]`. -/
def allJint (D : KrawData) : Bool :=
  (List.finRange 3).all fun i => (List.finRange 3).all fun j =>
    Dya.le (Dya.sub (D.Ac i j) (D.Δ i j)) (Jint D.Ctyp D.Xz i j).lo &&
    Dya.le (Jint D.Ctyp D.Xz i j).hi (Dya.add (D.Ac i j) (D.Δ i j))

/-- The whole numerical check of the certificate. -/
def ok (D : KrawData) : Bool :=
  Dya.pos D.r && D.allJint && Dya.le D.etaBound D.eta &&
    Dya.lt (Dya.add (Dya.mul (Dya.add D.alpha (Dya.mul D.beta D.eps)) D.r) D.eta) D.r

end KrawData

end

end Work.SeedCert
