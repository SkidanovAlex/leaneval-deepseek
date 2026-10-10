import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.MotK.KleinData
import Submission.Work.MotK.KleinPScale
import Submission.Work.MotC2.Relations
import Submission.Work.MotC2.TranslationDefs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# TDG (`Work.MotTDG`): `T_diag` is a theorem about every Klein datum

This is the definition layer of the area `Submission/Work/MotTDG` (namespace `Work.MotTDG`),
which implements node **TDG** of `MOTIVIC_KDATA_LEAD.md` §3: for *every* Klein datum the field
`T_diag` of `Work.MotV.KleinData.Good` follows from the other good fields `klein_eq` and `spans`
(and `ab ≠ 0`).  No curve is chosen, no chord--tangent certificate is needed.

## The mathematics

Write `F = L(E)` for the function field of `E = D.E.baseChange L` over a field `L ⊇ 𝕜`, and

* `kleinBas D L = (1, x, y, x², x·y)` — `basE E` below, the basis of `L(5·O)`;
* `kleinCoord D L i = ∑_m cL i m · kleinBas m` — the Klein linear forms, `cL = cL D L`;
* `spans` gives the inverse matrix `eL` (`eL * cL = 1`), so the `κ_i` are again an `L`-basis.

The ten monomials `goodMon (basE E) = (1, x, y, x², xy, x³, x²y, x⁴, x³y, x²y²)` of `L(10·O)`
are `L`-linearly independent (`tenMon_linearIndependent`, node **TDG-a**): in the `L[x]`-basis
`1, y` they are unitriangular, using the Weierstrass relation `x²y² = x⁵ + …`.

The key observation is that the Weierstrass relations among `v = (v₀,…,v₄)` are *quadrics*
(`vwQuad`, node **TDG-c**), because `x³ = x·x²`.  Expanding a Pfaffian along a matrix
(`kleinP_mulVec_expand`, node **TDG-b**) and reducing modulo the Veronese--Weierstrass quadrics
gives the exact polynomial identity

  `p_k (C v) = ∑_j muVW … j * vwQuad … v j + ∑_t rhoVW … t * goodMon v t`

whose remainder vanishes at `v = bas` by `klein_eq`, hence identically (`rhoVW_eq_zero`,
node **TDG-d**).  The multiplier matrix `muMat` of the five `vwQuad` is invertible
(`muMat_det_ne_zero`, node **TDG-e**).

Consequently, for any invertible projectivity `M` of `ℙ⁴` preserving the Pfaffian net
(`PfaffStable`), the vector `v' = eL · κ'` with `κ' = Mκ/ℓ(Mκ)` satisfies
`vwQuad v' = 0` and `v'₀ = 1`; so `(v'₁, v'₂)` is a point of `E` over `F` and, being nonconstant,
induces an `L`-algebra endomorphism `x ↦ v'₁`, `y ↦ v'₂` of `F` (`exists_algHom_of_point`,
node **TDG-f**), which is an automorphism because the same construction for the inverse of `M`
inverts it (`projAut_of_kleinEq_spans`, node **TDG-M**).  Specialising `M = diag(ζ^i)` gives
`T_diag` (`T_diag_of_kleinEq_spans`, node **TDG-T**).

## Conventions

* All generic polynomial identities are stated for `{R : Type*} [CommRing R]`, so they specialise
  to every `𝕜`-algebra; the curve-level ones for a Weierstrass curve `E` over a field `L`.
* `basE E` is `(1, x, y, x², x·y)` with `x = genX E`, `y = genY E`; `Work.MotV.kleinBas D L`
  is definitionally `basE (D.E.baseChange L)`.
* `cL D L i m` is the `(i,m)` entry of the Klein matrix over `L`; `eL D e L m i` the `(m,i)` entry
  of a `spans` matrix `e`.  Entry order matters: `kleinCoord i = ∑ m cL i m * basE m`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.MotTDG
noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine

/-! ## §0 The generic quadratic data -/

section Generic

variable {R : Type*} [CommRing R]

/-- The five **Veronese--Weierstrass quadrics** in the coordinates `v = (v₀,…,v₄)`: the three
trivial Veronese syzygies `v₀v₃ − v₁²`, `v₀v₄ − v₁v₂`, `v₁v₄ − v₂v₃`, the Weierstrass equation
(non-homogeneous in `v`, valid at `v₀ = 1`) and its `y`-multiple.  At `v = (1, x, y, x², xy)` all
five vanish (`vwQuad_basE`), the last two because of the Weierstrass relation and its `x`-multiple.
This is the `vwQuad` of `MOTIVIC_KDATA_LEAD.md` §3. -/
def vwQuad (a₁ a₂ a₃ a₄ a₆ : R) (v : Fin 5 → R) : Fin 5 → R :=
  ![v 0 * v 3 - v 1 ^ 2,
    v 0 * v 4 - v 1 * v 2,
    v 1 * v 4 - v 2 * v 3,
    v 2 ^ 2 + a₁ * v 1 * v 2 + a₃ * v 0 * v 2 - v 1 * v 3 - a₂ * v 0 * v 3 - a₄ * v 0 * v 1
      - a₆ * v 0 ^ 2,
    v 2 * v 4 - v 3 ^ 2 - a₂ * v 1 * v 3 - a₄ * v 0 * v 3 - a₆ * v 0 * v 1 + a₁ * v 1 * v 4
      + a₃ * v 0 * v 4]

/-- The ten **good monomials** in `v = (v₀,…,v₄)`; at `v = (1, x, y, x², xy)` these are
`1, x, y, x², xy, x³, x²y, x⁴, x³y, x²y²` — the ten monomials of `L(10·O)`. -/
def goodMon (v : Fin 5 → R) : Fin 10 → R :=
  ![v 0 ^ 2, v 0 * v 1, v 0 * v 2, v 0 * v 3, v 0 * v 4, v 1 * v 3, v 1 * v 4, v 3 ^ 2,
    v 3 * v 4, v 4 ^ 2]

/-- **The reverse direction**: `vwQuad a₁ … a₆ v = 0` together with `v₀ = 1` gives the Weierstrass
relation for the pair `(v₁, v₂)`: the first component forces `v₃ = v₁²`, and the fourth component
is then exactly the relation. -/
theorem relation_of_vwQuad_eq_zero {a₁ a₂ a₃ a₄ a₆ : R} {v : Fin 5 → R} (h0 : v 0 = 1)
    (h : vwQuad a₁ a₂ a₃ a₄ a₆ v = 0) :
    v 2 ^ 2 + a₁ * v 1 * v 2 + a₃ * v 2 = v 1 ^ 3 + a₂ * v 1 ^ 2 + a₄ * v 1 + a₆ := by
  have h3 : v 2 ^ 2 + a₁ * v 1 * v 2 + a₃ * v 0 * v 2 - v 1 * v 3 - a₂ * v 0 * v 3
      - a₄ * v 0 * v 1 - a₆ * v 0 ^ 2 = 0 := by
    have := congrFun h 3
    simpa only [vwQuad, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
      Matrix.cons_val, Pi.zero_apply] using this
  have h1 : v 0 * v 3 - v 1 ^ 2 = 0 := by
    have := congrFun h 0
    simpa only [vwQuad, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
      Matrix.cons_val, Pi.zero_apply] using this
  rw [h0] at h1 h3
  have hv3 : v 3 = v 1 ^ 2 := by linear_combination h1
  rw [hv3] at h3
  linear_combination (norm := first | refl_ring1 | ring1) h3

/-- The generic quadratic form `∑_m P_m v_m² + ∑_{m<n} B_{mn} v_m v_n`. -/
def quadForm (P : Fin 5 → R) (B : Fin 5 → Fin 5 → R) (v : Fin 5 → R) : R :=
  ∑ m, P m * v m ^ 2 + ∑ m, ∑ n, (if m < n then B m n * v m * v n else 0)

/-- Polar form of the Pfaffian `p_k`. -/
def kleinPolar (a b : R) (k : Fin 5) (x y : Fin 5 → R) : R :=
  Work.MotK.kleinP a b (x + y) k - Work.MotK.kleinP a b x k - Work.MotK.kleinP a b y k

/-- `colP k m = p_k (col_m c)`: the diagonal coefficient of the quadratic form `v ↦ p_k (c·v)`. -/
def colP (a b : R) (c : Fin 5 → Fin 5 → R) (k m : Fin 5) : R :=
  Work.MotK.kleinP a b (fun i => c i m) k

/-- `colB k m n = polar_k (col_m c, col_n c)`: the off-diagonal coefficient of `v ↦ p_k (c·v)`. -/
def colB (a b : R) (c : Fin 5 → Fin 5 → R) (k m n : Fin 5) : R :=
  kleinPolar a b k (fun i => c i m) (fun i => c i n)

/-- The coefficient vector `μ` of the `vwQuad` part of the reduction identity (**TDG-c**). -/
def muVW (a₁ : R) (P : Fin 5 → R) (B : Fin 5 → Fin 5 → R) : Fin 5 → R :=
  ![-P 1, -B 1 2 + a₁ * P 2, -B 2 3, P 2, B 2 4]

/-- The coefficient vector `ρ` of the `goodMon` part of the reduction identity (**TDG-c**). -/
def rhoVW (a₁ a₂ a₃ a₄ a₆ : R) (P : Fin 5 → R) (B : Fin 5 → Fin 5 → R) : Fin 10 → R :=
  ![P 0 + a₆ * P 2,
    B 0 1 + a₆ * B 2 4 + a₄ * P 2,
    B 0 2 - a₃ * P 2,
    B 0 3 + a₄ * B 2 4 + P 1 + a₂ * P 2,
    B 0 4 + B 1 2 - a₃ * B 2 4 - a₁ * P 2,
    B 1 3 + a₂ * B 2 4 + P 2,
    B 1 4 + B 2 3 - a₁ * B 2 4,
    B 2 4 + P 3,
    B 3 4,
    P 4]

end Generic

/-! ## §1 The ten monomials of `L(10·O)` -/

section Curve

variable {L : Type*} [Field L]

/-- The basis `1, x, y, x², x·y` of `L(5·O)` in the function field of `E` (the Klein basis of the
Weierstrass model). -/
def basE (E : WeierstrassCurve L) : Fin 5 → FunctionField E :=
  ![1, Work.MotV.genX E, Work.MotV.genY E, Work.MotV.genX E ^ 2,
    Work.MotV.genX E * Work.MotV.genY E]

/-- The ten monomials `1, x, y, x², xy, x³, x²y, x⁴, x³y, x²y²` of `L(10·O)`, as functions of
`basE E`.  Node **TDG-a** proves they are `L`-linearly independent. -/
def tenMon (E : WeierstrassCurve L) : Fin 10 → FunctionField E :=
  goodMon (basE E)

@[simp] theorem basE_zero (E : WeierstrassCurve L) : basE E 0 = 1 := rfl
@[simp] theorem basE_one (E : WeierstrassCurve L) : basE E 1 = Work.MotV.genX E := rfl
@[simp] theorem basE_two (E : WeierstrassCurve L) : basE E 2 = Work.MotV.genY E := rfl
@[simp] theorem basE_three (E : WeierstrassCurve L) : basE E 3 = Work.MotV.genX E ^ 2 := rfl
@[simp] theorem basE_four (E : WeierstrassCurve L) :
    basE E 4 = Work.MotV.genX E * Work.MotV.genY E := rfl

@[simp] theorem tenMon_zero (E : WeierstrassCurve L) : tenMon E 0 = 1 := by
  simp [tenMon, goodMon, basE]
@[simp] theorem tenMon_one (E : WeierstrassCurve L) : tenMon E 1 = Work.MotV.genX E := by
  simp [tenMon, goodMon, basE]
@[simp] theorem tenMon_two (E : WeierstrassCurve L) : tenMon E 2 = Work.MotV.genY E := by
  simp [tenMon, goodMon, basE]
@[simp] theorem tenMon_three (E : WeierstrassCurve L) : tenMon E 3 = Work.MotV.genX E ^ 2 := by
  simp [tenMon, goodMon, basE]
@[simp] theorem tenMon_four (E : WeierstrassCurve L) :
    tenMon E 4 = Work.MotV.genX E * Work.MotV.genY E := by
  simp [tenMon, goodMon, basE]
@[simp] theorem tenMon_five (E : WeierstrassCurve L) : tenMon E 5 = Work.MotV.genX E ^ 3 := by
  simp [tenMon, goodMon, basE]
  first | refl_ring1 | ring
@[simp] theorem tenMon_six (E : WeierstrassCurve L) :
    tenMon E 6 = Work.MotV.genX E ^ 2 * Work.MotV.genY E := by
  simp [tenMon, goodMon, basE]
  first | refl_ring1 | ring
@[simp] theorem tenMon_seven (E : WeierstrassCurve L) : tenMon E 7 = Work.MotV.genX E ^ 4 := by
  simp [tenMon, goodMon, basE]
  first | refl_ring1 | ring
@[simp] theorem tenMon_eight (E : WeierstrassCurve L) :
    tenMon E 8 = Work.MotV.genX E ^ 3 * Work.MotV.genY E := by
  simp [tenMon, goodMon, basE]
  first | refl_ring1 | ring
@[simp] theorem tenMon_nine (E : WeierstrassCurve L) :
    tenMon E 9 = Work.MotV.genX E ^ 2 * Work.MotV.genY E ^ 2 := by
  simp [tenMon, goodMon, basE]
  first | refl_ring1 | ring

/-- `Work.MotV.genX` is `Work.MotC2.genX` (both are the class of `X`). -/
theorem genX_eq (E : WeierstrassCurve L) : Work.MotV.genX E = Work.MotC2.genX E := by
  rw [Work.MotV.genX, Work.MotC2.genX, Work.MotC2.coordX_eq_mk]

/-- `Work.MotV.genY` is `Work.MotC2.genY` (both are the class of `Y`). -/
theorem genY_eq (E : WeierstrassCurve L) : Work.MotV.genY E = Work.MotC2.genY E := by
  rw [Work.MotV.genY, Work.MotC2.genY, Work.MotC2.coordY_eq_mk]

/-- The Weierstrass relation in the function field, in the `Work.MotV` coordinates. -/
theorem genXY_relation (E : WeierstrassCurve L) :
    Work.MotV.genY E ^ 2 + algebraMap L (FunctionField E) E.a₁ * Work.MotV.genX E
        * Work.MotV.genY E + algebraMap L (FunctionField E) E.a₃ * Work.MotV.genY E =
      Work.MotV.genX E ^ 3 + algebraMap L (FunctionField E) E.a₂ * Work.MotV.genX E ^ 2
        + algebraMap L (FunctionField E) E.a₄ * Work.MotV.genX E
        + algebraMap L (FunctionField E) E.a₆ := by
  rw [genX_eq E, genY_eq E]
  exact Work.MotC2.genX_genY_relation E

/-- **All five Veronese--Weierstrass quadrics vanish at the Weierstrass basis**: if
`y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` then `vwQuad a₁ … a₆ ![1, x, y, x², xy] = 0`.

The first three components are the trivial Veronese syzygies, the fourth is the Weierstrass
relation itself (with `x³ = x·x²`) and the fifth is `x` times it. -/
theorem vwQuad_eq_zero_of_relation {R : Type*} [CommRing R] (a₁ a₂ a₃ a₄ a₆ x y : R)
    (h : y ^ 2 + a₁ * x * y + a₃ * y = x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆) :
    vwQuad a₁ a₂ a₃ a₄ a₆ ![1, x, y, x ^ 2, x * y] = 0 := by
  funext k
  fin_cases k
  · show 1 * (x ^ 2) - x ^ 2 = 0
    first | refl_ring1 | ring
  · show 1 * (x * y) - x * y = 0
    first | refl_ring1 | ring
  · show x * (x * y) - y * (x ^ 2) = 0
    first | refl_ring1 | ring
  · show y ^ 2 + a₁ * x * y + a₃ * 1 * y - x * (x ^ 2) - a₂ * 1 * (x ^ 2) - a₄ * 1 * x
        - a₆ * 1 ^ 2 = 0
    linear_combination (norm := first | refl_ring1 | ring1) h
  · show y * (x * y) - (x ^ 2) ^ 2 - a₂ * x * (x ^ 2) - a₄ * 1 * (x ^ 2) - a₆ * 1 * x
        + a₁ * x * (x * y) + a₃ * 1 * (x * y) = 0
    linear_combination (norm := first | refl_ring1 | ring1) (x : R) * h

/-- The generic point of `E` satisfies its Weierstrass equation (`MotC2` form). -/
theorem basE_vwQuad_eq_zero (E : WeierstrassCurve L) :
    vwQuad (algebraMap L (FunctionField E) E.a₁) (algebraMap L (FunctionField E) E.a₂)
      (algebraMap L (FunctionField E) E.a₃) (algebraMap L (FunctionField E) E.a₄)
      (algebraMap L (FunctionField E) E.a₆) (basE E) = 0 :=
  vwQuad_eq_zero_of_relation _ _ _ _ _ _ _ (genXY_relation E)

end Curve

/-! ## §2 Klein data over `𝕜`, pushed to an `L`-algebra -/

section Klein

variable {𝕜 : Type*} [Field 𝕜]

/-- The Klein matrix `cL D L i m = D.coord i m`, pushed to `L`.  (Its type is `Matrix` rather
than the definitionally equal `Fin 5 → Fin 5 → L` so that the matrix multiplication instances
apply.) -/
def cL (D : Work.MotV.KleinData 𝕜) (L : Type*) [Field L] [Algebra 𝕜 L] :
    Matrix (Fin 5) (Fin 5) L :=
  fun i m => algebraMap 𝕜 L (D.coord i m)

/-- The matrix `eL D L e m i = e m i` of a `spans` witness `e`, pushed to `L`. -/
def eL (D : Work.MotV.KleinData 𝕜) (L : Type*) [Field L] [Algebra 𝕜 L]
    (e : Fin 5 → Fin 5 → 𝕜) : Matrix (Fin 5) (Fin 5) L := fun m i => algebraMap 𝕜 L (e m i)

/-- The Klein coordinates `κ = kleinCoord D L` are `cL` applied to `basE`. -/
theorem kleinCoord_eq_cL (D : Work.MotV.KleinData 𝕜) (L : Type*) [Field L] [Algebra 𝕜 L]
    (i : Fin 5) :
    Work.MotV.kleinCoord D L i =
    ∑ m, algebraMap L (FunctionField (D.E.baseChange L)) (cL D L i m) * basE (D.E.baseChange L) m := by
  rw [Work.MotV.kleinCoord_eq_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [cL, Work.MotV.kleinBas, basE]

/-- The `spans` witness says `basE = eL · κ` (with the `(m,i)` convention). -/
theorem basE_eq_eL_kleinCoord (D : Work.MotV.KleinData 𝕜) (L : Type*) [Field L] [Algebra 𝕜 L]
    (e : Fin 5 → Fin 5 → 𝕜)
    (he : ∀ m, Work.MotV.kleinBas D L m =
      ∑ i, algebraMap L _ (algebraMap 𝕜 L (e m i)) * Work.MotV.kleinCoord D L i)
    (m : Fin 5) :
    basE (D.E.baseChange L) m =
      ∑ i, algebraMap L (FunctionField (D.E.baseChange L)) (eL D L e m i)
        * Work.MotV.kleinCoord D L i := by
  have h : basE (D.E.baseChange L) m = Work.MotV.kleinBas D L m := rfl
  rw [h, he m]
  rfl

/-- The `M`-image of the Klein coordinates: `κ ↦ Mκ` (`(Mκ) i = ∑ j M i j κ j`). -/
def kvec (D : Work.MotV.KleinData 𝕜) (L : Type*) [Field L] [Algebra 𝕜 L]
    (M : Matrix (Fin 5) (Fin 5) L) (i : Fin 5) : FunctionField (D.E.baseChange L) :=
  ∑ j, algebraMap L (FunctionField (D.E.baseChange L)) (M i j) * Work.MotV.kleinCoord D L j

/-- The linear form `ℓ(z) = ∑_i eL 0 i z_i` of a `spans` witness; `ℓ (kleinCoord D L) = 1`. -/
def ell (D : Work.MotV.KleinData 𝕜) (L : Type*) [Field L] [Algebra 𝕜 L]
    (e : Fin 5 → Fin 5 → 𝕜) (z : Fin 5 → FunctionField (D.E.baseChange L)) :
    FunctionField (D.E.baseChange L) :=
  ∑ i, algebraMap L (FunctionField (D.E.baseChange L)) (eL D L e 0 i) * z i

/-- The normalised `M`-image of the Klein coordinates: `κ' = Mκ / ℓ(Mκ)`. -/
def kappaShift (D : Work.MotV.KleinData 𝕜) (L : Type*) [Field L] [Algebra 𝕜 L]
    (e : Fin 5 → Fin 5 → 𝕜) (M : Matrix (Fin 5) (Fin 5) L) (i : Fin 5) :
    FunctionField (D.E.baseChange L) :=
  kvec D L M i / ell D L e (kvec D L M)

/-- The Weierstrass vector of the shifted coordinates: `v' = eL · κ'`. -/
def wvec (D : Work.MotV.KleinData 𝕜) (L : Type*) [Field L] [Algebra 𝕜 L]
    (e : Fin 5 → Fin 5 → 𝕜) (M : Matrix (Fin 5) (Fin 5) L) (m : Fin 5) :
    FunctionField (D.E.baseChange L) :=
  ∑ i, algebraMap L (FunctionField (D.E.baseChange L)) (eL D L e m i) * kappaShift D L e M i

/-- The multiplier matrix `μ` of the identity `p_k (C v) = ∑_j μ_{k j} vwQuad_j (v)`. -/
def muMat (D : Work.MotV.KleinData 𝕜) (L : Type*) [Field L] [Algebra 𝕜 L] :
    Matrix (Fin 5) (Fin 5) L :=
  Matrix.of fun k j => muVW (D.E.baseChange L).a₁
    (colP (algebraMap 𝕜 L D.a) (algebraMap 𝕜 L D.b) (cL D L) k)
    (colB (algebraMap 𝕜 L D.a) (algebraMap 𝕜 L D.b) (cL D L) k) j

/-- `M` **preserves the Pfaffian net**: `p_k (M z) = ∑_j N_{k j} p_j (z)` for all `z` in every
`L`-algebra.  Written this way it is stable under base change, so it can be used at
`R = FunctionField (D.E.baseChange L)`. -/
def PfaffStable (D : Work.MotV.KleinData 𝕜) (L : Type*) [Field L] [Algebra 𝕜 L]
    (M : Matrix (Fin 5) (Fin 5) L) : Prop :=
  ∃ N : Matrix (Fin 5) (Fin 5) L, ∀ (R : Type*) [CommRing R] [Algebra L R] (z : Fin 5 → R)
    (k : Fin 5),
    Work.MotK.kleinP (algebraMap L R (algebraMap 𝕜 L D.a)) (algebraMap L R (algebraMap 𝕜 L D.b))
        (fun i => ∑ j, algebraMap L R (M i j) * z j) k =
      ∑ j, algebraMap L R (N k j) *
        Work.MotK.kleinP (algebraMap L R (algebraMap 𝕜 L D.a))
          (algebraMap L R (algebraMap 𝕜 L D.b)) z j

/-- The `T_diag` field of `Work.MotV.KleinData.Good`, as a standalone proposition about a datum
(node **TDG-T** proves it from `klein_eq` and `spans`). -/
def TDiagProp (D : Work.MotV.KleinData 𝕜) : Prop :=
  ∀ (L : Type) [Field L] [Algebra 𝕜 L] (ζ : L), IsPrimitiveRoot ζ 5 →
    ∃ σ : FunctionField (D.E.baseChange L) ≃ₐ[L] FunctionField (D.E.baseChange L),
      ∀ i, σ (Work.MotV.kleinCoord D L i / Work.MotV.kleinCoord D L 0) =
        algebraMap L _ ζ ^ (i : ℕ) * (Work.MotV.kleinCoord D L i / Work.MotV.kleinCoord D L 0)

end Klein

end

end Work.MotTDG
