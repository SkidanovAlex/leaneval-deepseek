import Mathlib
import Submission.Work.MotTDG.Defs
import Submission.Work.MotTDG.Ring
import Submission.Work.MotTDG.TenMonLI

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotTDG

/-!
**TDG-d**: all remainders `rhoVW` of the reduction identity `quad_reduce` vanish.

For a Klein datum `D` over `𝕜` whose Klein coordinates satisfy the five Pfaffian equations
(`klein_eq`, hypothesis `hkl`), each of the ten remainder coefficients `rhoVW t` — the coefficient
of the good monomial `goodMon t` in the reduction of `quadForm (colP k) (colB k)` modulo the five
Veronese--Weierstrass quadrics — is zero.  This is the step that upgrades the *identity* of node
TDG-c (`quad_reduce`, the pure `ring` result in `Submission/Work/MotTDG/Ring.lean`) to the
statement `p_k (C v) = ∑_j μ_{k j} vwQuad_j (v)` used afterwards.

PROOF ROUTE.  Put `E = D.E.baseChange L`, `κ i = Work.MotV.kleinCoord D L i`, `bas = basE E`,
`c = cL D L`, `a b` for the pushed-forward Klein parameters and `a₁ … a₆` for the coefficients of
`E` (all in `L`).

* `Work.MotTDG.kleinCoord_eq_cL` rewrites `κ i = ∑ m, algebraMap L _ (c i m) * bas m`.
* Applying `Work.MotTDG.kleinP_mulVec_expand` (node TDG-b) with `c` and `v := bas` turns
  `Work.MotK.kleinP a b κ k` into `∑ m, colP a b c k m * bas m ^ 2 + ∑ m ∑ n, (if m < n then
  colB a b c k m n * bas m * bas n else 0)`, which is `quadForm (colP a b c k) (colB a b c k) bas`.
* `Work.MotTDG.quad_reduce` (node TDG-c) rewrites that as
  `∑ j, muVW a₁ (colP …) (colB …) j * vwQuad a₁ … a₆ bas j +
     ∑ t, rhoVW a₁ … a₆ (colP …) (colB …) t * goodMon bas t`.
* Every `vwQuad a₁ … a₆ bas j = 0` (`Work.MotTDG.basE_vwQuad_eq_zero`), and
  `goodMon bas = tenMon E` by definition (`Work.MotTDG.tenMon`).
* Hence `hkl L k` says `∑ t, algebraMap L (FunctionField E) (rhoVW … t) • tenMon E t = 0` in
  `FunctionField E`, and `Work.MotTDG.TenMonLI` (node TDG-a, a restatement of
  `Work.MotTDG.tenMon_linearIndependent`; import `Submission.Work.MotTDG.TenMonLI`)
  plus `Fintype.linearIndependent_iff` gives `rhoVW … t = 0`.

The conclusion `rhoVW (…) t = 0` is exactly the shape needed by the consumer
`Work.MotTDG.muMat_det_ne_zero` (node TDG-e).

FUNCTORIALITY LEMMAS.  The five lemmas `map_kleinP`, `map_kleinPolar`, `map_colP`, `map_colB`,
`map_rhoVW` below record that the polynomial expressions `kleinP`, `colP`, `colB`, `rhoVW` commute
with an arbitrary ring homomorphism (they are polynomial in their arguments with integer
coefficients); they are what transports the `L`-level identity to the function field of
`E = D.E.baseChange L`.
-/

/-! ## §1 Functoriality of the polynomial data under a ring homomorphism -/

theorem map_kleinP {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (a b : R) (x : Fin 5 → R) (k : Fin 5) :
    f (Work.MotK.kleinP a b x k) = Work.MotK.kleinP (f a) (f b) (fun i => f (x i)) k := by
  fin_cases k <;>
    simp [Work.MotK.kleinP, Work.MotK.kleinP0, Work.MotK.kleinP1, Work.MotK.kleinP2,
      Work.MotK.kleinP3, Work.MotK.kleinP4]

theorem map_kleinPolar {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (a b : R) (k : Fin 5) (x y : Fin 5 → R) :
    f (kleinPolar a b k x y) = kleinPolar (f a) (f b) k (fun i => f (x i)) (fun i => f (y i)) := by
  fin_cases k <;>
    simp [kleinPolar, Work.MotK.kleinP, Work.MotK.kleinP0, Work.MotK.kleinP1, Work.MotK.kleinP2,
      Work.MotK.kleinP3, Work.MotK.kleinP4]

theorem map_colP {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (a b : R) (c : Fin 5 → Fin 5 → R) (k m : Fin 5) :
    f (colP a b c k m) = colP (f a) (f b) (fun i m => f (c i m)) k m :=
  map_kleinP f a b (fun i => c i m) k

theorem map_colB {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (a b : R) (c : Fin 5 → Fin 5 → R) (k m n : Fin 5) :
    f (colB a b c k m n) = colB (f a) (f b) (fun i m => f (c i m)) k m n :=
  map_kleinPolar f a b k (fun i => c i m) (fun i => c i n)

theorem map_rhoVW {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (a₁ a₂ a₃ a₄ a₆ : R) (P : Fin 5 → R) (B : Fin 5 → Fin 5 → R) (t : Fin 10) :
    f (rhoVW a₁ a₂ a₃ a₄ a₆ P B t) =
      rhoVW (f a₁) (f a₂) (f a₃) (f a₄) (f a₆) (fun i => f (P i)) (fun i j => f (B i j)) t := by
  fin_cases t <;> simp [rhoVW]

/-! ## §2 The vanishing of the remainders -/

theorem rhoVW_eq_zero {𝕜 : Type} [Field 𝕜] (D : Work.MotV.KleinData 𝕜)
    (hkl : ∀ (L : Type) [Field L] [Algebra 𝕜 L] (k : Fin 5),
      Work.MotK.kleinP (algebraMap 𝕜 _ D.a) (algebraMap 𝕜 _ D.b) (Work.MotV.kleinCoord D L) k = 0)
    (L : Type) [Field L] [Algebra 𝕜 L] (k : Fin 5) (t : Fin 10) :
    rhoVW (D.E.baseChange L).a₁ (D.E.baseChange L).a₂ (D.E.baseChange L).a₃
      (D.E.baseChange L).a₄ (D.E.baseChange L).a₆
      (colP (algebraMap 𝕜 L D.a) (algebraMap 𝕜 L D.b) (cL D L) k)
      (colB (algebraMap 𝕜 L D.a) (algebraMap 𝕜 L D.b) (cL D L) k) t = 0 := by
  let E : WeierstrassCurve L := D.E.baseChange L
  let F := WeierstrassCurve.Affine.FunctionField E
  let c : Fin 5 → Fin 5 → L := cL D L
  let P : Fin 5 → L := colP (algebraMap 𝕜 L D.a) (algebraMap 𝕜 L D.b) c k
  let B : Fin 5 → Fin 5 → L := colB (algebraMap 𝕜 L D.a) (algebraMap 𝕜 L D.b) c k
  let cc : Fin 5 → Fin 5 → F := fun i m => algebraMap L F (c i m)
  let P' : Fin 5 → F :=
    colP (algebraMap L F (algebraMap 𝕜 L D.a)) (algebraMap L F (algebraMap 𝕜 L D.b)) cc k
  let B' : Fin 5 → Fin 5 → F :=
    colB (algebraMap L F (algebraMap 𝕜 L D.a)) (algebraMap L F (algebraMap 𝕜 L D.b)) cc k
  -- `hkl` at the function field of `E`, with the two scalars pushed into `L`
  have h0 : Work.MotK.kleinP (algebraMap L F (algebraMap 𝕜 L D.a))
      (algebraMap L F (algebraMap 𝕜 L D.b)) (Work.MotV.kleinCoord D L) k = 0 := by
    rw [← IsScalarTower.algebraMap_apply 𝕜 L F D.a,
      ← IsScalarTower.algebraMap_apply 𝕜 L F D.b]
    exact hkl L k
  -- the Klein coordinates in the matrix-times-basis form
  have hκ : Work.MotV.kleinCoord D L = fun i => ∑ m, cc i m * basE E m := by
    funext i
    exact kleinCoord_eq_cL D L i
  have h1 : Work.MotK.kleinP (algebraMap L F (algebraMap 𝕜 L D.a))
      (algebraMap L F (algebraMap 𝕜 L D.b)) (fun i => ∑ m, cc i m * basE E m) k = 0 := by
    rw [← hκ]; exact h0
  -- expand the Pfaffian along the matrix `c`
  have h2 := kleinP_mulVec_expand (algebraMap L F (algebraMap 𝕜 L D.a))
      (algebraMap L F (algebraMap 𝕜 L D.b)) cc (basE E) k
  have h3 : quadForm P' B' (basE E) = 0 := by
    rw [quadForm, ← h2]; exact h1
  -- reduce modulo the five Veronese--Weierstrass quadrics
  have h4 := quad_reduce (algebraMap L F E.a₁) (algebraMap L F E.a₂) (algebraMap L F E.a₃)
    (algebraMap L F E.a₄) (algebraMap L F E.a₆) P' B' (basE E)
  have h5 : ∀ j : Fin 5, vwQuad (algebraMap L F E.a₁) (algebraMap L F E.a₂) (algebraMap L F E.a₃)
      (algebraMap L F E.a₄) (algebraMap L F E.a₆) (basE E) j = 0 :=
    fun j => congrFun (basE_vwQuad_eq_zero E) j
  have h6 : ∑ t, rhoVW (algebraMap L F E.a₁) (algebraMap L F E.a₂) (algebraMap L F E.a₃)
      (algebraMap L F E.a₄) (algebraMap L F E.a₆) P' B' t * tenMon E t = 0 := by
    have h := h4
    rw [h3] at h
    have hz : (∑ j, muVW (algebraMap L F E.a₁) P' B' j *
        vwQuad (algebraMap L F E.a₁) (algebraMap L F E.a₂) (algebraMap L F E.a₃)
          (algebraMap L F E.a₄) (algebraMap L F E.a₆) (basE E) j) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [h5 j, mul_zero]
    rw [hz, zero_add] at h
    simpa only [tenMon] using h.symm
  -- the coefficients are the images of the `L`-level coefficients
  have hP : (fun m => algebraMap L F (P m)) = P' := by
    funext m
    exact map_colP (algebraMap L F) (algebraMap 𝕜 L D.a) (algebraMap 𝕜 L D.b) c k m
  have hB : (fun i j => algebraMap L F (B i j)) = B' := by
    funext i j
    exact map_colB (algebraMap L F) (algebraMap 𝕜 L D.a) (algebraMap 𝕜 L D.b) c k i j
  have h7 : ∀ t, algebraMap L F (rhoVW E.a₁ E.a₂ E.a₃ E.a₄ E.a₆ P B t) =
      rhoVW (algebraMap L F E.a₁) (algebraMap L F E.a₂) (algebraMap L F E.a₃)
        (algebraMap L F E.a₄) (algebraMap L F E.a₆) P' B' t := by
    intro t
    rw [map_rhoVW (algebraMap L F) E.a₁ E.a₂ E.a₃ E.a₄ E.a₆ P B t]
    rw [hP, hB]
  have h8 : ∑ t, (algebraMap L F (rhoVW E.a₁ E.a₂ E.a₃ E.a₄ E.a₆ P B t)) * tenMon E t = 0 := by
    simpa only [h7] using h6
  have h9 : ∑ t, (rhoVW E.a₁ E.a₂ E.a₃ E.a₄ E.a₆ P B t) • tenMon E t = 0 := by
    simpa only [Algebra.smul_def] using h8
  -- the ten monomials of `L(10·O)` are `L`-independent (node TDG-a)
  exact (Fintype.linearIndependent_iff.mp (TenMonLI E))
    (fun t => rhoVW E.a₁ E.a₂ E.a₃ E.a₄ E.a₆ P B t) h9 t

end Work.MotTDG
