/-
# The minimal `Δ`-complex structure on the torus `T²`, and its chain-level certificate

This module supplies the *data* used by `Work.PieceHomology.exists_torus2DeltaCx`: the finite
`Δ`-complex `torus2DeltaCx` with `1, 3, 2` simplices (one vertex, three edges, two triangles),
the finite free chain complex `torus2Cx` whose boundary operators are the matrices of the
`Δ`-chain complex, and the strong-deformation-retract certificate `torus2SDR` for it.

## The combinatorial model

`T²` is the quotient of a square with opposite sides identified.  Cutting the square along a
diagonal gives two triangles all of whose vertices and edges are identified: the resulting
`Δ`-complex has

* one `0`-simplex (the single vertex),
* three `1`-simplices `a, b, c` (all of them loops at the vertex, since both endpoints coincide),
* two `2`-simplices `T₀ = [b, c, a]` and `T₁ = [a, c, b]` (the list is the cyclic order of the
  edges: the `i`-th entry is the face *opposite* the `i`-th vertex).

With this gluing both triangles have boundary `a + b - c`, so the `Δ`-chain complex is

`ℤ --0--> ℤ³ --M--> ℤ²`,  `M = [a + b - c, a + b - c]`,

whose homology is `H₀ = ℤ`, `H₁ = ℤ³/⟨a+b-c⟩ = ℤ²`, `H₂ = ker M = ℤ·(T₀ - T₁)`, and `0` above:
the homology of `T²`, of ranks `rankT2 = (1, 2, 1)` (`Work.HomologyIso.rankT2`).

## What is here, and what is not

* `torus2DeltaCx` — the `Δ`-complex (`card 0 = 1`, `card 1 = 3`, `card 2 = 2`);
* `torus2Cx` — the finite free complex `ℤ --0--> ℤ³ --M--> ℤ²` with the same boundary matrices as
  `torus2DeltaCx.chain`, with the `SDR` certificate `torus2SDR` (Betti numbers `torus2B = (1,2,1)`)
  verified by `torus2SDR_check`;
* the concrete face/boundary computations `torus2DeltaCx_chainD_zero`, `torus2Bd_one_matrix`,
  `torus2Cx_d` used to compare the two complexes;
* `torus2B_eq_rankT2` — the computed ranks are the model ranks.

The comparison of `torus2Cx.toChainComplex` with `torus2DeltaCx.chain` is *not* here: the two
complexes live in different presentations (copowers of `ℤ` versus `Fin n → ℤ`), and the
isomorphism between them is the coproduct-to-product identification in every degree,

`(∐_{i : Fin n} ℤ) ≅ (Fin n → ℤ)`,  `Sigma.ι i 1 ↦ Pi.single i 1`,

together with the degreewise comparison of the differentials (checked on the basis simplices).

## How to compare the two complexes (plan)

Let `e k : torus2DeltaCx.chainX k ≅ torus2Cx.toChainComplex.X k` be the coproduct-to-product
identification above, in degree `k` (both sides have `torus2Card k` free generators:
`torus2DeltaCx.chainX k = ∐_{i : Fin (torus2Card k)} ℤ` and
`torus2Cx.toChainComplex.X k = ℤ^{(Fin (torus2Card k) → ℤ)}`).  Then
`HomologicalComplex.Hom.isoOfComponents (fun k => e k)` gives the chain isomorphism, provided
the differentials match:

* in degree `0` (i.e. `d 1 0`): the matrix is `0` (`torus2Bd_zero_matrix`) and
  `torus2DeltaCx.chainD 0 = 0` (`torus2DeltaCx_chainD_zero`);
* in degree `1` (i.e. `d 2 1`): the boundary of both triangles is `a + b - c`, so under `e` the
  `Δ`-differential is the matrix `!![1,1; 1,1; -1,-1]` (`torus2Bd_one_matrix`); the check is
  finite — rewrite `chainι 2 σ ≫ chainD 1` by `DeltaHomology.DeltaCx.ι_chainD`, push `≫ e 1`
  inside the sum, evaluate both sides at the generator `1 : ℤ` (`LinearMap.ext_ring`,
  `ModuleCat.hom_ext`) and decide the resulting identity in `Fin 3 → ℤ` (whose entries are
  `0/±1`, comparing with the face values `torus2DeltaCx_face_tri`);
* in degrees `≥ 2`: both sides are morphisms out of a zero object
  (`DeltaHomology.isZero_chainX_of_dim_lt`, or the `Fin 0` indexing), so they agree by
  `CategoryTheory.Limits.IsZero.eq_of_src`.

Everything that remains is thus a *finite* computation plus the coproduct-to-product
identification, which is provided by the module `Submission.Work.PieceHomology.torus2CoprodPi`.
-/
import Mathlib
import Submission.Work.PieceHomology.Basic
import Submission.Work.HomologyIso.Algebra
import Submission.Work.Certificates.SDR.sound

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits

namespace Work.PieceHomology

open Work.Certificates

noncomputable section

/-! ## §1  The `Δ`-complex -/

/-- The number of `k`-simplices: `1, 3, 2` in degrees `0, 1, 2`, and none above. -/
def torus2Card : ℕ → ℕ
  | 0 => 1
  | 1 => 3
  | 2 => 2
  | _ => 0

/-- The `Δ`-complex has no simplices above its dimension. -/
theorem torus2Card_eq_zero (k : ℕ) (hk : 2 < k) : torus2Card k = 0 := by
  match k with
  | 0 => omega
  | 1 => omega
  | 2 => omega
  | k + 3 => rfl

@[simp] theorem torus2Card_zero : torus2Card 0 = 1 := rfl
@[simp] theorem torus2Card_one : torus2Card 1 = 3 := rfl
@[simp] theorem torus2Card_two : torus2Card 2 = 2 := rfl

/-- The faces of the two triangles, labelled by the edge they are opposite to:
`T₀ = [b, c, a]` and `T₁ = [a, c, b]`, where `a = 0`, `b = 1`, `c = 2`. -/
def torus2TriFace (σ : Fin 2) (i : Fin 3) : Fin 3 :=
  match σ, i with
  | 0, 0 => 1 | 0, 1 => 2 | 0, 2 => 0
  | 1, 0 => 0 | 1, 1 => 2 | 1, 2 => 1

/-- The face maps of the `Δ`-complex: the edges are loops at the single vertex (both faces are
the vertex), the triangles have the faces above, and there is nothing above dimension `2`. -/
def torus2Face : ∀ {k : ℕ}, Fin (torus2Card (k+1)) → Fin (k+2) → Fin (torus2Card k)
  | 0, _, _ => (0 : Fin 1)
  | 1, σ, i => torus2TriFace σ i
  | (_+2), σ, _ => Fin.elim0 σ

/-- The semi-simplicial identities: vacuous above degree `0`, and in degree `0` both sides lie in
`Fin 1`. -/
theorem torus2Face_face : ∀ {k : ℕ} (σ : Fin (torus2Card (k+2))) (i j : Fin (k+2)), i ≤ j →
    torus2Face (torus2Face σ (Fin.succ j)) i
      = torus2Face (torus2Face σ (Fin.castSucc i)) j := by
  rintro (_ | _ | k) σ i j hij
  · rfl
  · exact Fin.elim0 σ
  · exact Fin.elim0 σ

/-- **The `Δ`-complex of the torus**: one vertex, three edges and two triangles. -/
def torus2DeltaCx : DeltaHomology.DeltaCx where
  dim := 2
  card := torus2Card
  face := torus2Face
  face_face := torus2Face_face
  card_eq_zero := fun k hk => torus2Card_eq_zero k (by omega)

@[simp] theorem torus2DeltaCx_card (k : ℕ) : torus2DeltaCx.card k = torus2Card k := rfl

/-! ### Naming the simplices

The simplices of `torus2DeltaCx` are the elements of `Fin (torus2Card k)`; since `torus2Card k`
is *definitionally* a numeral only for the literal degrees, it is convenient to have named
elements (and the face computations on them) available with literal index types. -/

/-- The three edges, as `1`-simplices. -/
def torus2Edge (i : Fin 3) : Fin (torus2Card 1) := i

/-- The two triangles, as `2`-simplices. -/
def torus2Tri (σ : Fin 2) : Fin (torus2Card 2) := σ

/-- The single vertex, as a `0`-simplex. -/
def torus2Vertex : Fin (torus2Card 0) := (0 : Fin 1)

/-- Both endpoints of every edge are the single vertex. -/
theorem torus2Face_edge (σ : Fin (torus2Card 1)) (i : Fin 2) :
    torus2Face σ i = torus2Vertex := rfl

/-- The same, for the face map of the `Δ`-complex. -/
theorem torus2DeltaCx_face_edge (σ : Fin (torus2Card 1)) (i : Fin 2) :
    torus2DeltaCx.face (k := 0) σ i = torus2Vertex := torus2Face_edge σ i

/-- The faces of the two triangles, in the named form. -/
theorem torus2DeltaCx_face_tri (σ : Fin 2) (j : Fin 3) :
    torus2DeltaCx.face (k := 1) (torus2Tri σ) j = torus2Edge (torus2TriFace σ j) := rfl

/-- Both endpoints of every edge are the single vertex, so the boundary `∂₁ = d₀ - d₁` of the
`Δ`-chain complex vanishes. -/
theorem torus2DeltaCx_chainD_zero : torus2DeltaCx.chainD 0 = 0 := by
  apply DeltaHomology.DeltaCx.chainX_hom_ext
  intro σ
  have h : torus2DeltaCx.chainι 1 σ ≫ torus2DeltaCx.chainD 0 = 0 := by
    rw [DeltaHomology.DeltaCx.ι_chainD, Fin.sum_univ_two]
    rw [torus2DeltaCx_face_edge σ 0, torus2DeltaCx_face_edge σ 1]
    simp
  simpa using h

/-! ## §2  The finite free chain complex and its certificate -/

/-- `∂₁ = 0`: the three edges are loops. -/
def torus2BdZero : SOp 1 3 := SOp.zero 1 3

/-- `∂₂ = [a+b-c, a+b-c]`, the matrix with both columns `(1,1,-1)`. -/
def torus2BdOne : SOp 3 2 :=
  SOp.ofList [[(0,1),(1,1),(2,-1)], [(0,1),(1,1),(2,-1)]]

/-- The boundary operators of the finite complex, in the indexing of `FinChainCx`
(`torus2Bd k = ∂_{k+1} : C_{k+1} → C_k`). -/
def torus2Bd : ∀ k, SOp (torus2Card k) (torus2Card (k+1))
  | 0 => torus2BdZero
  | 1 => torus2BdOne
  | _ => SOp.zero _ _

theorem torus2Bd_zero_matrix : (torus2Bd 0).toMatrix = 0 :=
  SOp.toMatrix_zero _ _

theorem torus2Bd_one_matrix : (torus2Bd 1).toMatrix = !![1,1;1,1;-1,-1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- `∂ ∘ ∂ = 0`. -/
theorem torus2Bd_comp : ∀ k, (torus2Bd k).toMatrix * (torus2Bd (k+1)).toMatrix = 0 := by
  intro k
  match k with
  | 0 => rw [show torus2Bd 0 = SOp.zero (torus2Card 0) (torus2Card 1) from rfl,
      SOp.toMatrix_zero, Matrix.zero_mul]
  | 1 => rw [show torus2Bd 2 = SOp.zero (torus2Card 2) (torus2Card 3) from rfl,
      SOp.toMatrix_zero, Matrix.mul_zero]
  | k + 2 => rw [show torus2Bd (k+2) = SOp.zero (torus2Card (k+2)) (torus2Card (k+3)) from rfl,
      SOp.toMatrix_zero, Matrix.zero_mul]

/-- **The finite free chain complex** `ℤ --0--> ℤ³ --M--> ℤ²` of the torus. -/
def torus2Cx : FinChainCx where
  dim := torus2Card
  bd := torus2Bd
  bd_comp := torus2Bd_comp

@[simp] theorem torus2Cx_dim (k : ℕ) : torus2Cx.dim k = torus2Card k := rfl

/-- The differential of `torus2Cx.toChainComplex` is the matrix of `torus2Bd`. -/
theorem torus2Cx_d (k : ℕ) :
    (torus2Cx.toChainComplex).d (k+1) k
      = ModuleCat.ofHom (Matrix.toLin' ((torus2Bd k).toMatrix)) :=
  ChainComplex.of_d (fun k : ℕ => ModuleCat.of ℤ (Fin (torus2Card k) → ℤ))
    (fun k : ℕ => ModuleCat.ofHom (Matrix.toLin' ((torus2Bd k).toMatrix))) k

/-- The ranks of the homology: `(1, 2, 1)`. -/
def torus2B : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 1
  | _ => 0

theorem torus2B_eq_zero (k : ℕ) (hk : 2 < k) : torus2B k = 0 := by
  match k with
  | 0 => omega
  | 1 => omega
  | 2 => omega
  | k + 3 => rfl

@[simp] theorem torus2B_zero : torus2B 0 = 1 := rfl
@[simp] theorem torus2B_one : torus2B 1 = 2 := rfl
@[simp] theorem torus2B_two : torus2B 2 = 1 := rfl

/-- The computed ranks are the model ranks `rankT2 = (1,2,1)` of `H_*(T²)`. -/
theorem torus2B_eq_rankT2 (k : ℕ) : torus2B k = Work.HomologyIso.rankT2 (k : ℤ) := by
  match k with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | k + 3 =>
      rw [torus2B_eq_zero (k+3) (by omega),
        Work.HomologyIso.rankT2_eq_zero _ (by omega) (by omega) (by omega)]

/-! ## §3  The strong deformation retract -/

/-- `Z₀ : ℤ → C₀`. -/
def torus2Zzero : SOp 1 1 := SOp.ofList [[(0,1)]]

/-- `Z₁ : ℤ² → C₁`, the two surviving loops. -/
def torus2Zone : SOp 3 2 := SOp.ofList [[(0,1)],[(1,1)]]

/-- `Z₂ : ℤ → C₂`, the generator maps to the cycle `T₀ - T₁`. -/
def torus2Ztwo : SOp 2 1 := SOp.ofList [[(0,1),(1,-1)]]

def torus2Z : ∀ k, SOp (torus2Card k) (torus2B k)
  | 0 => torus2Zzero
  | 1 => torus2Zone
  | 2 => torus2Ztwo
  | _ => SOp.zero _ _

/-- `ρ₀`. -/
def torus2Rhozero : SOp 1 1 := SOp.ofList [[(0,1)]]

/-- `ρ₁ : C₁ → ℤ²`, `x ↦ (1,0)`, `y ↦ (0,1)`, `z ↦ (1,1)`; it kills `a + b - c`. -/
def torus2Rhoone : SOp 2 3 := SOp.ofList [[(0,1)],[(1,1)],[(0,1),(1,1)]]

/-- `ρ₂ : C₂ → ℤ`, `T₀ ↦ 1`, `T₁ ↦ 0`. -/
def torus2Rhotwo : SOp 1 2 := SOp.ofList [[(0,1)], []]

def torus2Rho : ∀ k, SOp (torus2B k) (torus2Card k)
  | 0 => torus2Rhozero
  | 1 => torus2Rhoone
  | 2 => torus2Rhotwo
  | _ => SOp.zero _ _

/-- `h₀ : C₀ → C₁`. -/
def torus2Hzero : SOp 3 1 := SOp.ofList [[]]

/-- `h₁ : C₁ → C₂`, `z ↦ -T₁`. -/
def torus2Hone : SOp 2 3 := SOp.ofList [[], [], [(1,-1)]]

/-- `h₂ : C₂ → C₃ = 0`. -/
def torus2Htwo : SOp 0 2 := SOp.ofList [[], []]

def torus2H : ∀ k, SOp (torus2Card (k+1)) (torus2Card k)
  | 0 => torus2Hzero
  | 1 => torus2Hone
  | 2 => torus2Htwo
  | _ => SOp.zero _ _

/-- **The strong deformation retract certificate** of the torus complex, with Betti numbers
`(1, 2, 1)`. -/
def torus2SDR : SDR torus2Cx where
  N := 3
  b := torus2B
  Z := torus2Z
  ρ := torus2Rho
  h := torus2H
  dim_zero := fun k hk => torus2Card_eq_zero k (by omega)
  b_zero := fun k hk => torus2B_eq_zero k (by omega)

/-- The certificate passes: `∂Z = 0`, `ρ∂ = 0`, `ρZ = 1` and `1 - Zρ = ∂h + h∂`. -/
theorem torus2SDR_check : torus2SDR.check = true := by decide

/-- **The homology of the certified complex is `ℤ^{torus2B k}`** — for the finite complex
itself; it is transported to `torus2DeltaCx.chain` by the comparison isomorphism. -/
theorem torus2Cx_homology (k : ℕ) :
    Nonempty (torus2Cx.homology k ≅ ModuleCat.of ℤ (Fin (torus2B k) → ℤ)) :=
  SDR.sound torus2SDR torus2SDR_check k

end

end Work.PieceHomology
