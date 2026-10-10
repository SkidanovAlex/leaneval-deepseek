import Mathlib
import Submission.Work.MotTDG.Defs
import Submission.Work.MotTDG.Ring
import Submission.Work.MotTDG.rhoVW_eq_zero

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# TDG: the reduction of a Pfaffian to the Veronese--Weierstrass quadrics over an algebra

`Work.MotTDG.reduce_alg` is the `R`-algebra level form of the reduction identity of node **TDG-c**
(`Work.MotTDG.quad_reduce`) *modulo the five quadrics*: for a Klein datum `D` whose Klein
coordinates satisfy the Pfaffian equations over every `𝕜`-algebra (`hkl`, the `klein_eq` field of
`KleinData.Good`), the Pfaffian of the (`L`-linearly recombined) vector `v` equals the sum of the
`muMat`-multiples of the five Veronese--Weierstrass quadrics `vwQuad`:

  `p_k (C v) = ∑_j μ_kj · vwQuad_j (v)`

with *no* remainder.  The remainders `rhoVW` vanish in `L` by node **TDG-d**
(`Work.MotTDG.rhoVW_eq_zero`), and the identity then transports along `algebraMap L R` because
`quad_reduce` is a polynomial identity with integer coefficients (the functoriality lemmas
`map_muVW`, `map_rhoVW` and `map_colP`/`map_colB` record this).

The two closure lemmas `kleinP_eq_quadForm` and `quadForm_eq_sum_muVW` split the proof into the
two halves of the reduction (TDG-b plus the vanishing of the remainders).

The version of TDG-d needed here is *universe polymorphic in the base field* `𝕜`
(`rhoVW_eq_zero'` below), because the target quantifies `𝕜 : Type*`.
-/

namespace Work.MotTDG
noncomputable section

/-! ## Functoriality of the reduction data under a ring homomorphism -/

/-- `muVW` is a polynomial expression with integer coefficients, hence commutes with any ring
homomorphism. -/
theorem map_muVW {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a₁ : R)
    (P : Fin 5 → R) (B : Fin 5 → Fin 5 → R) (j : Fin 5) :
    f (muVW a₁ P B j) = muVW (f a₁) (fun i => f (P i)) (fun i j => f (B i j)) j := by
  fin_cases j <;> simp [muVW]

/-- The entries of the multiplier matrix `muMat` are the `muVW` coefficients. -/
theorem muMat_apply {𝕜 : Type*} [Field 𝕜] (D : Work.MotV.KleinData 𝕜)
    (L : Type*) [Field L] [Algebra 𝕜 L] (k j : Fin 5) :
    muMat D L k j =
      muVW (D.E.baseChange L).a₁
        (colP (algebraMap 𝕜 L D.a) (algebraMap 𝕜 L D.b) (cL D L) k)
        (colB (algebraMap 𝕜 L D.a) (algebraMap 𝕜 L D.b) (cL D L) k) j :=
  rfl

/-! ## TDG-d, universe polymorphic in the base field -/

/-- **TDG-d** (`Work.MotTDG.rhoVW_eq_zero`, restated with `𝕜 : Type*`): all remainder coefficients
`rhoVW` of the reduction identity vanish for a Klein datum satisfying the Pfaffian equations.

The proof is that of `Work.MotTDG.rhoVW_eq_zero`, which is stated for `{𝕜 : Type}`; every ingredient
(`kleinCoord_eq_cL`, `kleinP_mulVec_expand`, `quad_reduce`, `basE_vwQuad_eq_zero`, `map_rhoVW`,
`map_colP`, `map_colB`, `TenMonLI`) is already universe polymorphic. -/
theorem rhoVW_eq_zero' {𝕜 : Type*} [Field 𝕜] (D : Work.MotV.KleinData 𝕜)
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
  have h0 : Work.MotK.kleinP (algebraMap L F (algebraMap 𝕜 L D.a))
      (algebraMap L F (algebraMap 𝕜 L D.b)) (Work.MotV.kleinCoord D L) k = 0 := by
    rw [← IsScalarTower.algebraMap_apply 𝕜 L F D.a,
      ← IsScalarTower.algebraMap_apply 𝕜 L F D.b]
    exact hkl L k
  have hκ : Work.MotV.kleinCoord D L = fun i => ∑ m, cc i m * basE E m := by
    funext i
    exact kleinCoord_eq_cL D L i
  have h1 : Work.MotK.kleinP (algebraMap L F (algebraMap 𝕜 L D.a))
      (algebraMap L F (algebraMap 𝕜 L D.b)) (fun i => ∑ m, cc i m * basE E m) k = 0 := by
    rw [← hκ]; exact h0
  have h2 := kleinP_mulVec_expand (algebraMap L F (algebraMap 𝕜 L D.a))
      (algebraMap L F (algebraMap 𝕜 L D.b)) cc (basE E) k
  have h3 : quadForm P' B' (basE E) = 0 := by
    rw [quadForm, ← h2]; exact h1
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
  exact (Fintype.linearIndependent_iff.mp (TenMonLI E))
    (fun t => rhoVW E.a₁ E.a₂ E.a₃ E.a₄ E.a₆ P B t) h9 t

/-! ## The two halves of the reduction -/

/-- **TDG-b**: expanding the Pfaffian of `c · v` gives the quadratic form with diagonal
coefficients `colP` and polar coefficients `colB`. -/
theorem kleinP_eq_quadForm {R : Type*} [CommRing R] (a b : R) (c : Fin 5 → Fin 5 → R)
    (v : Fin 5 → R) (k : Fin 5) :
    Work.MotK.kleinP a b (fun i => ∑ m, c i m * v m) k =
      quadForm (colP a b c k) (colB a b c k) v := by
  rw [kleinP_mulVec_expand a b c v k]
  rfl

/-- **TDG-c + TDG-d**: if the remainders `rhoVW` of the reduction identity vanish, the quadratic
form collapses onto the five Veronese--Weierstrass quadrics with multiplier matrix `muVW`. -/
theorem quadForm_eq_sum_muVW {R : Type*} [CommRing R] (a₁ a₂ a₃ a₄ a₆ : R)
    (P : Fin 5 → R) (B : Fin 5 → Fin 5 → R) (v : Fin 5 → R)
    (h : ∀ t, rhoVW a₁ a₂ a₃ a₄ a₆ P B t = 0) :
    quadForm P B v = ∑ j, muVW a₁ P B j * vwQuad a₁ a₂ a₃ a₄ a₆ v j := by
  have hq := quad_reduce a₁ a₂ a₃ a₄ a₆ P B v
  have h2 : (∑ t, rhoVW a₁ a₂ a₃ a₄ a₆ P B t * goodMon v t) = 0 :=
    Finset.sum_eq_zero (fun t _ => by rw [h t, zero_mul])
  rw [hq, h2, add_zero]

/-! ## The target -/

theorem reduce_alg {𝕜 : Type*} [Field 𝕜] (D : Work.MotV.KleinData 𝕜)
    (hkl : ∀ (L' : Type) [Field L'] [Algebra 𝕜 L'] (k : Fin 5),
      Work.MotK.kleinP (algebraMap 𝕜 _ D.a) (algebraMap 𝕜 _ D.b)
        (Work.MotV.kleinCoord D L') k = 0)
    (L : Type) [Field L] [Algebra 𝕜 L] (R : Type*) [CommRing R] [Algebra L R]
    (v : Fin 5 → R) (k : Fin 5) :
    Work.MotK.kleinP (algebraMap L R (algebraMap 𝕜 L D.a)) (algebraMap L R (algebraMap 𝕜 L D.b))
        (fun i => ∑ m, algebraMap L R (Work.MotTDG.cL D L i m) * v m) k
      = ∑ j, algebraMap L R (Work.MotTDG.muMat D L k j) *
          Work.MotTDG.vwQuad (algebraMap L R (D.E.baseChange L).a₁)
            (algebraMap L R (D.E.baseChange L).a₂) (algebraMap L R (D.E.baseChange L).a₃)
            (algebraMap L R (D.E.baseChange L).a₄) (algebraMap L R (D.E.baseChange L).a₆) v j := by
  let c : Fin 5 → Fin 5 → L := cL D L
  let P : Fin 5 → L := colP (algebraMap 𝕜 L D.a) (algebraMap 𝕜 L D.b) c k
  let B : Fin 5 → Fin 5 → L := colB (algebraMap 𝕜 L D.a) (algebraMap 𝕜 L D.b) c k
  let cR : Fin 5 → Fin 5 → R := fun i m => algebraMap L R (c i m)
  have hP : (fun m => algebraMap L R (P m)) =
      colP (algebraMap L R (algebraMap 𝕜 L D.a)) (algebraMap L R (algebraMap 𝕜 L D.b)) cR k := by
    funext m
    exact map_colP (algebraMap L R) (algebraMap 𝕜 L D.a) (algebraMap 𝕜 L D.b) c k m
  have hB : (fun m n => algebraMap L R (B m n)) =
      colB (algebraMap L R (algebraMap 𝕜 L D.a)) (algebraMap L R (algebraMap 𝕜 L D.b)) cR k := by
    funext m n
    exact map_colB (algebraMap L R) (algebraMap 𝕜 L D.a) (algebraMap 𝕜 L D.b) c k m n
  have hrem : ∀ t, rhoVW (algebraMap L R (D.E.baseChange L).a₁)
      (algebraMap L R (D.E.baseChange L).a₂) (algebraMap L R (D.E.baseChange L).a₃)
      (algebraMap L R (D.E.baseChange L).a₄) (algebraMap L R (D.E.baseChange L).a₆)
      (fun m => algebraMap L R (P m)) (fun m n => algebraMap L R (B m n)) t = 0 := by
    intro t
    rw [← map_rhoVW (algebraMap L R) (D.E.baseChange L).a₁ (D.E.baseChange L).a₂
        (D.E.baseChange L).a₃ (D.E.baseChange L).a₄ (D.E.baseChange L).a₆ P B t,
      rhoVW_eq_zero' D hkl L k t, map_zero]
  have h1 : Work.MotK.kleinP (algebraMap L R (algebraMap 𝕜 L D.a))
        (algebraMap L R (algebraMap 𝕜 L D.b))
        (fun i => ∑ m, algebraMap L R (cL D L i m) * v m) k =
      quadForm (colP (algebraMap L R (algebraMap 𝕜 L D.a))
          (algebraMap L R (algebraMap 𝕜 L D.b)) cR k)
        (colB (algebraMap L R (algebraMap 𝕜 L D.a))
          (algebraMap L R (algebraMap 𝕜 L D.b)) cR k) v :=
    kleinP_eq_quadForm _ _ cR v k
  have h2 : quadForm (colP (algebraMap L R (algebraMap 𝕜 L D.a))
          (algebraMap L R (algebraMap 𝕜 L D.b)) cR k)
        (colB (algebraMap L R (algebraMap 𝕜 L D.a))
          (algebraMap L R (algebraMap 𝕜 L D.b)) cR k) v =
      quadForm (fun m => algebraMap L R (P m)) (fun m n => algebraMap L R (B m n)) v := by
    rw [← hP, ← hB]
  have h3 : quadForm (fun m => algebraMap L R (P m)) (fun m n => algebraMap L R (B m n)) v =
      ∑ j, muVW (algebraMap L R (D.E.baseChange L).a₁) (fun m => algebraMap L R (P m))
            (fun m n => algebraMap L R (B m n)) j *
            vwQuad (algebraMap L R (D.E.baseChange L).a₁) (algebraMap L R (D.E.baseChange L).a₂)
              (algebraMap L R (D.E.baseChange L).a₃) (algebraMap L R (D.E.baseChange L).a₄)
              (algebraMap L R (D.E.baseChange L).a₆) v j :=
    quadForm_eq_sum_muVW (algebraMap L R (D.E.baseChange L).a₁)
      (algebraMap L R (D.E.baseChange L).a₂) (algebraMap L R (D.E.baseChange L).a₃)
      (algebraMap L R (D.E.baseChange L).a₄) (algebraMap L R (D.E.baseChange L).a₆)
      (fun m => algebraMap L R (P m)) (fun m n => algebraMap L R (B m n)) v hrem
  have h4 : (∑ j, muVW (algebraMap L R (D.E.baseChange L).a₁) (fun m => algebraMap L R (P m))
            (fun m n => algebraMap L R (B m n)) j *
            vwQuad (algebraMap L R (D.E.baseChange L).a₁) (algebraMap L R (D.E.baseChange L).a₂)
              (algebraMap L R (D.E.baseChange L).a₃) (algebraMap L R (D.E.baseChange L).a₄)
              (algebraMap L R (D.E.baseChange L).a₆) v j) =
      ∑ j, algebraMap L R (muMat D L k j) *
            vwQuad (algebraMap L R (D.E.baseChange L).a₁) (algebraMap L R (D.E.baseChange L).a₂)
              (algebraMap L R (D.E.baseChange L).a₃) (algebraMap L R (D.E.baseChange L).a₄)
              (algebraMap L R (D.E.baseChange L).a₆) v j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show algebraMap L R ((muMat D L) k j)
          = algebraMap L R (muVW (D.E.baseChange L).a₁ P B j) from rfl, map_muVW]
  exact h1.trans (h2.trans (h3.trans h4))

end
end Work.MotTDG
