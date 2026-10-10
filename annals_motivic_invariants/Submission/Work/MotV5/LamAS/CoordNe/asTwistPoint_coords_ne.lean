import Mathlib
import Submission.Work.MotV5.Defs
import Submission.Work.MotV5.ASTwistData
import Submission.Work.MotC2.Translation
import Submission.Work.MotC2.Negation
import Submission.Work.MotV5.LamAS.lamExtraction
import Submission.Work.MotV5.LamAS.root_eq_asRoot_add
import Submission.Work.MotT.TwistPointKDefs
import Submission.Work.MotT.evalAtLoc_transAlgEquiv
import Submission.Work.MotV5.LamAS.asShiftCross
import Submission.Work.MotV.Defs

set_option linter.unusedVariables false -- v435-speed

/-!
# The Klein-point extraction, non-degenerate case (self-contained)

This file is a **self-contained copy** of `Submission/Work/MotV5/LamAS/asTwistPoint_coords.lean`
(same proof, helper lemmas relocated to the namespace `Work.MotV5.LamAS.CoordNe`) with the extra
hypothesis `R ≠ 0`.  The point of the copy is that the degenerate branch `R = O` -- the only place
where the original file invokes `Work.MotV5.LamAS.asTwistPoint_zero` -- is vacuous here and is
discharged by `absurd rfl hRne`.  The module therefore avoids the dependency
`asTwistPoint_zero → Work.MotV5.Nodes.lam_AS`.

The mathematical content is identical to the original:

Let `K = RatFunc 𝕜`, `Kb 𝕜 = AlgebraicClosure K`, `L ⊆ Kb 𝕜` a finite Galois intermediate field
containing `W = asRoot g` (`g : RatFunc 𝕜`), and let `R`, `Q` be points of the Klein model
`E_{↥L}`.  Suppose

* `Q` acts on the Klein coordinates by the projective shift `τ_Q κᵢ = λ κ_{i+1}` (`λ ≠ 0`);
* `γ W = W + d γ` for every `γ : ↥L ≃ₐ[K] ↥L`, with `d γ ∈ Fin 5` the Artin–Schreier cocycle;
* `γ R = R + (d γ) • Q` for every `γ`.

Then the twisted Klein curve `C^AS_g` has a `K`-rational point: there is a nonzero
`y : Fin 5 → RatFunc 𝕜` whose AS Galois coordinates `asCoord (asRoot g) (algebraMap y)` satisfy the
Klein equations.
-/

namespace Work.MotV5.LamAS.CoordNe

open WeierstrassCurve WeierstrassCurve.Affine

set_option maxHeartbeats 1000000

noncomputable section

section Helpers

variable {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5]

/-! ## §1 The Klein coordinates lifted to the affine coordinate ring

The coordinate step evaluates the Klein coordinates `κᵢ = kleinCoord D ↥L i` at the point `R`.  For
that we lift them to the affine coordinate ring `Coord (E⁄L)`, where the evaluation homomorphism
`Work.MotT.plugHomAt` is available. -/

/-- The basis `1, x, y, x², xy` in the affine coordinate ring of the base-changed curve. -/
def asKleinBas (D : Work.MotV.KleinData 𝕜) (M : Type) [Field M] [Algebra 𝕜 M] :
    Fin 5 → Work.MotC2.Coord (D.E.baseChange M) :=
  ![1, Work.MotC2.coordX (D.E.baseChange M), Work.MotC2.coordY (D.E.baseChange M),
    (Work.MotC2.coordX (D.E.baseChange M)) ^ 2,
    Work.MotC2.coordX (D.E.baseChange M) * Work.MotC2.coordY (D.E.baseChange M)]

/-- The lift of the Klein coordinates `κᵢ` to the affine coordinate ring. -/
def asKlein (D : Work.MotV.KleinData 𝕜) (M : Type) [Field M] [Algebra 𝕜 M] (i : Fin 5) :
    Work.MotC2.Coord (D.E.baseChange M) :=
  ∑ m, algebraMap 𝕜 (Work.MotC2.Coord (D.E.baseChange M)) (D.coord i m) * asKleinBas D M m

lemma asGenX_eq (M : Type) [Field M] (E : WeierstrassCurve M) :
    Work.MotV.genX E = Work.MotC2.genX E := by
  simp [Work.MotV.genX, Work.MotC2.genX, Work.MotC2.coordX_eq_mk]

lemma asGenY_eq (M : Type) [Field M] (E : WeierstrassCurve M) :
    Work.MotV.genY E = Work.MotC2.genY E := by
  simp [Work.MotV.genY, Work.MotC2.genY, Work.MotC2.coordY_eq_mk]

lemma asKleinBas_map (D : Work.MotV.KleinData 𝕜) (M : Type) [Field M] [Algebra 𝕜 M] (m : Fin 5) :
    algebraMap (Work.MotC2.Coord (D.E.baseChange M)) (Work.MotC2.Func (D.E.baseChange M))
        (asKleinBas D M m) = Work.MotV.kleinBas D M m := by
  have hb : Work.MotV.kleinBas D M = ![1, Work.MotC2.genX (D.E.baseChange M),
      Work.MotC2.genY (D.E.baseChange M), (Work.MotC2.genX (D.E.baseChange M)) ^ 2,
      Work.MotC2.genX (D.E.baseChange M) * Work.MotC2.genY (D.E.baseChange M)] := by
    simp only [Work.MotV.kleinBas]
    rw [asGenX_eq M (D.E.baseChange M), asGenY_eq M (D.E.baseChange M)]
  rw [hb]
  fin_cases m <;> simp [asKleinBas, Work.MotC2.genX, Work.MotC2.genY]

lemma asKlein_map (D : Work.MotV.KleinData 𝕜) (M : Type) [Field M] [Algebra 𝕜 M] (i : Fin 5) :
    algebraMap (Work.MotC2.Coord (D.E.baseChange M)) (Work.MotC2.Func (D.E.baseChange M))
        (asKlein D M i) = Work.MotV.kleinCoord D M i := by
  rw [Work.MotV.kleinCoord_eq_sum, asKlein, map_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [map_mul, asKleinBas_map,
    ← IsScalarTower.algebraMap_apply 𝕜 M (Work.MotC2.Func (D.E.baseChange M)) (D.coord i m),
    ← IsScalarTower.algebraMap_apply 𝕜 (Work.MotC2.Coord (D.E.baseChange M))
      (Work.MotC2.Func (D.E.baseChange M)) (D.coord i m)]

/-- The Klein coordinates lie in the local ring of **every** affine point: they are polynomials in
the coordinates. -/
lemma kleinCoord_mem_affPlaceAt (D : Work.MotV.KleinData 𝕜) (M : Type) [Field M] [Algebra 𝕜 M]
    (a b : M) (i : Fin 5) :
    Work.MotV.kleinCoord D M i ∈ Work.MotC2.affPlaceAt (D.E.baseChange M) a b := by
  rw [← asKlein_map D M i]
  exact Algebra.subset_adjoin (Set.mem_union_left _ ⟨asKlein D M i, rfl⟩)

/-- The Klein Pfaffians vanish on the lifted Klein coordinates. -/
lemma kleinP_asKlein (D : Work.MotV.KleinData 𝕜) (hD : D.Good) (M : Type) [Field M] [Algebra 𝕜 M]
    (k : Fin 5) :
    Work.MotK.kleinP (algebraMap 𝕜 (Work.MotC2.Coord (D.E.baseChange M)) D.a)
        (algebraMap 𝕜 (Work.MotC2.Coord (D.E.baseChange M)) D.b) (asKlein D M) k = 0 := by
  refine IsFractionRing.injective (Work.MotC2.Coord (D.E.baseChange M))
    (Work.MotC2.Func (D.E.baseChange M)) ?_
  rw [map_zero, kleinP_map']
  have h1 : (fun i => algebraMap (Work.MotC2.Coord (D.E.baseChange M))
      (Work.MotC2.Func (D.E.baseChange M)) (asKlein D M i)) = Work.MotV.kleinCoord D M := by
    funext i; exact asKlein_map D M i
  rw [h1]
  rw [← IsScalarTower.algebraMap_apply 𝕜 (Work.MotC2.Coord (D.E.baseChange M))
      (Work.MotC2.Func (D.E.baseChange M)) D.a,
    ← IsScalarTower.algebraMap_apply 𝕜 (Work.MotC2.Coord (D.E.baseChange M))
      (Work.MotC2.Func (D.E.baseChange M)) D.b]
  exact hD.klein_eq M k

/-- The `spans` identity of `D.Good`, lifted to the coordinate ring. -/
lemma asKleinBas_span (D : Work.MotV.KleinData 𝕜) (M : Type) [Field M] [Algebra 𝕜 M]
    (e : Fin 5 → Fin 5 → 𝕜)
    (he : ∀ (M' : Type) [Field M'] [Algebra 𝕜 M'] (m : Fin 5), Work.MotV.kleinBas D M' m =
      ∑ i, algebraMap M' _ (algebraMap 𝕜 M' (e m i)) * Work.MotV.kleinCoord D M' i)
    (m : Fin 5) :
    asKleinBas D M m = ∑ i, algebraMap 𝕜 (Work.MotC2.Coord (D.E.baseChange M)) (e m i) *
      asKlein D M i := by
  refine IsFractionRing.injective (Work.MotC2.Coord (D.E.baseChange M))
    (Work.MotC2.Func (D.E.baseChange M)) ?_
  rw [asKleinBas_map, map_sum, he M m]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_mul, asKlein_map,
    ← IsScalarTower.algebraMap_apply 𝕜 (Work.MotC2.Coord (D.E.baseChange M))
      (Work.MotC2.Func (D.E.baseChange M)) (e m i),
    ← IsScalarTower.algebraMap_apply 𝕜 M (Work.MotC2.Func (D.E.baseChange M)) (e m i)]

/-! ## §2b A ring-homomorphism form of the evaluation of constants -/

lemma plugHomAt_toRingHom_algebraMap {M : Type} [Field M] (E : WeierstrassCurve M) (a b : M)
    (h : Nonsingular E a b) {K : Type} [Field K] [Algebra K M] (c : K) :
    (Work.MotT.plugHomAt E a b h).toRingHom (algebraMap K (Work.MotC2.Coord E) c) =
      algebraMap K M c :=
  Work.MotT.plugHomAt_algebraMap_K E a b h c

/-! ## §2 Galois covariance of the evaluation at a point -/

/-- **Galois covariance of the evaluation of the Klein coordinates.**  For an automorphism `σ` of
the coefficient field `M` over `K` (with `𝕜 ⊆ K ⊆ M`), the value at the conjugate point
`(σ a, σ b)` is the conjugate of the value at `(a, b)`: the Klein coordinates are `𝕜`-linear
combinations of `1, x, y, x², xy`, and `σ` fixes the coefficients and acts on the coordinates. -/
lemma plugHomAt_asKlein_galois {M : Type} [Field M] [Algebra 𝕜 M] {K : Type} [Field K]
    [Algebra 𝕜 K] [Algebra K M] [IsScalarTower 𝕜 K M]
    (D : Work.MotV.KleinData 𝕜) (σ : M ≃ₐ[K] M) {a b : M}
    (h : Nonsingular (D.E.baseChange M) a b)
    (h' : Nonsingular (D.E.baseChange M) (σ a) (σ b)) (i : Fin 5) :
    Work.MotT.plugHomAt (D.E.baseChange M) (σ a) (σ b) h' (asKlein D M i) =
      σ (Work.MotT.plugHomAt (D.E.baseChange M) a b h (asKlein D M i)) := by
  have hcoe : ∀ m : Fin 5,
      Work.MotT.plugHomAt (D.E.baseChange M) (σ a) (σ b) h' (asKleinBas D M m) =
        σ (Work.MotT.plugHomAt (D.E.baseChange M) a b h (asKleinBas D M m)) := by
    intro m
    fin_cases m <;>
      simp [asKleinBas, Work.MotT.plugHomAt_coordX, Work.MotT.plugHomAt_coordY]
  have hbase : ∀ m : Fin 5, σ (algebraMap 𝕜 M (D.coord i m)) = algebraMap 𝕜 M (D.coord i m) := by
    intro m
    rw [IsScalarTower.algebraMap_apply 𝕜 K M]
    exact σ.commutes (algebraMap 𝕜 K (D.coord i m))
  calc Work.MotT.plugHomAt (D.E.baseChange M) (σ a) (σ b) h' (asKlein D M i)
      = ∑ m, algebraMap 𝕜 M (D.coord i m) *
          Work.MotT.plugHomAt (D.E.baseChange M) (σ a) (σ b) h' (asKleinBas D M m) := by
        rw [asKlein, map_sum]
        exact Finset.sum_congr rfl (fun m _ => by
          rw [map_mul, Work.MotT.plugHomAt_algebraMap_K])
    _ = ∑ m, algebraMap 𝕜 M (D.coord i m) *
          σ (Work.MotT.plugHomAt (D.E.baseChange M) a b h (asKleinBas D M m)) :=
        Finset.sum_congr rfl (fun m _ => by rw [hcoe m])
    _ = σ (∑ m, algebraMap 𝕜 M (D.coord i m) *
          Work.MotT.plugHomAt (D.E.baseChange M) a b h (asKleinBas D M m)) := by
        rw [map_sum]
        exact (Finset.sum_congr rfl (fun m _ => by rw [map_mul, hbase m])).symm
    _ = σ (Work.MotT.plugHomAt (D.E.baseChange M) a b h (asKlein D M i)) := by
        congr 1
        rw [asKlein, map_sum]
        exact Finset.sum_congr rfl (fun m _ => by
          rw [map_mul, Work.MotT.plugHomAt_algebraMap_K])

/-! ## §3 Powers of the translation -/

/-- The `n`-fold iterate of the translation by `Q` is the translation by `n • Q`. -/
lemma asTransAlgEquiv_pow {M : Type} [Field M] [DecidableEq M] (E : WeierstrassCurve M)
    [E.IsElliptic] (Q : E.toAffine.Point) :
    ∀ n : ℕ, (Work.MotC2.transAlgEquiv E Q) ^ n = Work.MotC2.transAlgEquiv E (n • Q) := by
  intro n
  induction n with
  | zero => simp [Work.MotC2.transAlgEquiv_zero]
  | succ n ih => rw [pow_succ, ih, succ_nsmul, Work.MotC2.transAlgEquiv_add]

end Helpers

/-! ## §4 The AS extraction -/

/-- **The Klein-point extraction, non-degenerate case.**  This is
`Work.MotV5.LamAS.asTwistPoint_coords` (in `Submission/Work/MotV5/LamAS/asTwistPoint_coords.lean`,
which is PROVED) with the extra hypothesis `R ≠ 0`, so that the degenerate branch
`R = O` -- the only place where that file uses `asTwistPoint_zero` -- is vacuous and can be
discharged by `exact absurd rfl hRne`.  Copy the proof from `asTwistPoint_coords.lean` (the whole
file, including its helper lemmas `asGenX_eq`, `asKleinBas_map`, `asKlein_map`,
`kleinCoord_mem_affPlaceAt`, `kleinP_asKlein`, `asKleinBas_span`, `plugHomAt_toRingHom_algebraMap`,
`plugHomAt_asKlein_galois`, `asTransAlgEquiv_pow`) but do NOT import
`Submission.Work.MotV5.LamAS.asTwistPoint_zero` (it imports `Nodes.lam_AS` and would create an
import cycle). -/
theorem asTwistPoint_coords_ne {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (g : RatFunc 𝕜)
    (L : IntermediateField (RatFunc 𝕜) (Work.MotV.Kb 𝕜))
    [IsGalois (RatFunc 𝕜) ↥L] [FiniteDimensional (RatFunc 𝕜) ↥L]
    [instDec : DecidableEq ↥L] [instEll : (D.E.baseChange ↥L).IsElliptic]
    (hW : Work.MotV5.asRoot g ∈ L)
    (Q R : (D.E.baseChange ↥L).toAffine.Point) (hRne : R ≠ 0)
    (hQshift : ∃ lam : Work.MotC2.Func (D.E.baseChange ↥L), lam ≠ 0 ∧
      ∀ i : Fin 5, Work.MotC2.transAlgEquiv (D.E.baseChange ↥L) Q
          (Work.MotV.kleinCoord D ↥L i) = lam * Work.MotV.kleinCoord D ↥L (i + 1))
    (d : (↥L ≃ₐ[RatFunc 𝕜] ↥L) → Fin 5)
    (hd : ∀ γ : ↥L ≃ₐ[RatFunc 𝕜] ↥L, γ ⟨Work.MotV5.asRoot g, hW⟩
        = ⟨Work.MotV5.asRoot g, hW⟩ + algebraMap ℤ ↥L ((d γ : Fin 5) : ℤ))
    (hR : ∀ γ : ↥L ≃ₐ[RatFunc 𝕜] ↥L,
      WeierstrassCurve.Affine.Point.map (W' := D.E) (S := RatFunc 𝕜)
        (F := ↥L) (K := ↥L) γ.toAlgHom R = R + ((d γ : ℕ) • Q)) :
    ∃ y : Fin 5 → RatFunc 𝕜, y ≠ 0 ∧
      ∀ k, Work.MotK.kleinP (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a)
        (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b)
        (Work.MotV.asCoord (Work.MotV5.asRoot g)
          (fun j => algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (y j))) k = 0 := by
  classical
  rcases R with _ | ⟨r₁, r₂, hr⟩
  · -- ### The degenerate case `R = O`, excluded by `hRne`
    exact absurd rfl hRne
  · -- ### The affine case `R = (r₁, r₂)`
    haveI hnsR : Work.MotC2.IsNonsingularPoint (D.E.baseChange ↥L) r₁ r₂ := ⟨hr⟩
    obtain ⟨lam, hlam0, hshift⟩ := hQshift
    -- the Klein coordinates of `R`
    let kval : Fin 5 → ↥L :=
      fun i => Work.MotT.plugHomAt (D.E.baseChange ↥L) r₁ r₂ hr (asKlein D ↥L i)
    -- `R` lies on the Klein cone
    have hkleinP : ∀ k, Work.MotK.kleinP (algebraMap 𝕜 ↥L D.a) (algebraMap 𝕜 ↥L D.b)
        kval k = 0 := by
      intro k
      have h := congrArg
        (fun x => (Work.MotT.plugHomAt (D.E.baseChange ↥L) r₁ r₂ hr).toRingHom x)
        (kleinP_asKlein D hD.1 ↥L k)
      rw [map_zero, kleinP_map'] at h
      rw [plugHomAt_toRingHom_algebraMap, plugHomAt_toRingHom_algebraMap] at h
      exact h
    -- some Klein coordinate of `R` does not vanish
    have hkval_ne : kval ≠ 0 := by
      intro h0
      have h0' : ∀ i : Fin 5, kval i = 0 := fun i => by simpa using congrFun h0 i
      obtain ⟨e, he⟩ := hD.1.spans
      have hone : Work.MotT.plugHomAt (D.E.baseChange ↥L) r₁ r₂ hr (asKleinBas D ↥L 0) = 1 := by
        simp [asKleinBas]
      have hspan := asKleinBas_span D ↥L e he 0
      have hsum : (1 : ↥L) = ∑ i : Fin 5, algebraMap 𝕜 ↥L (e 0 i) * kval i := by
        have h := congrArg (Work.MotT.plugHomAt (D.E.baseChange ↥L) r₁ r₂ hr) hspan
        rw [hone, map_sum] at h
        rw [h]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [map_mul, Work.MotT.plugHomAt_algebraMap_K]
      have hzero : (∑ i : Fin 5, algebraMap 𝕜 ↥L (e 0 i) * kval i) = 0 := by
        refine Finset.sum_eq_zero (fun i _ => ?_)
        rw [h0' i, mul_zero]
      rw [hzero] at hsum
      exact one_ne_zero hsum
    -- the Galois conjugates of `R`
    have hdata : ∀ γ : ↥L ≃ₐ[RatFunc 𝕜] ↥L,
        ∃ (hσ : WeierstrassCurve.Affine.Nonsingular (D.E.baseChange ↥L) (γ r₁) (γ r₂)),
          WeierstrassCurve.Affine.Point.some r₁ r₂ hr + ((d γ : ℕ) • Q)
            = WeierstrassCurve.Affine.Point.some (γ r₁) (γ r₂) hσ := by
      intro γ
      refine ⟨(WeierstrassCurve.Affine.baseChange_nonsingular D.E (f := γ.toAlgHom)
        (AlgEquiv.injective γ) r₁ r₂).mpr hr, ?_⟩
      exact (hR γ).symm
    -- the twisted Galois law for the values `κᵢ(R)`
    have hcross_val : ∀ γ : ↥L ≃ₐ[RatFunc 𝕜] ↥L, ∀ i j : Fin 5,
        γ (kval i) * kval (j + d γ) = γ (kval j) * kval (i + d γ) := by
      intro γ i j
      obtain ⟨hσ, hσeq⟩ := hdata γ
      haveI hnsσ : Work.MotC2.IsNonsingularPoint (D.E.baseChange ↥L) (γ r₁) (γ r₂) := ⟨hσ⟩
      -- the shifted Klein coordinates are regular at `R`
      have hmemτ : ∀ l : Fin 5,
          (Work.MotC2.transAlgEquiv (D.E.baseChange ↥L) ((d γ : ℕ) • Q))
            (Work.MotV.kleinCoord D ↥L l) ∈ Work.MotC2.affPlaceAt (D.E.baseChange ↥L) r₁ r₂ := by
        intro l
        rw [← Work.MotT.map_transAlgEquiv_affPlaceAt (D.E.baseChange ↥L) hr hσ
          ((d γ : ℕ) • Q) hσeq]
        exact Subalgebra.mem_map.mpr ⟨Work.MotV.kleinCoord D ↥L l,
          kleinCoord_mem_affPlaceAt D ↥L (γ r₁) (γ r₂) l, rfl⟩
      let Z : Fin 5 → ↥(Work.MotC2.affPlaceAt (D.E.baseChange ↥L) r₁ r₂) :=
        fun l => algebraMap (Work.MotC2.Coord (D.E.baseChange ↥L))
          ↥(Work.MotC2.affPlaceAt (D.E.baseChange ↥L) r₁ r₂) (asKlein D ↥L l)
      let Zτ : Fin 5 → ↥(Work.MotC2.affPlaceAt (D.E.baseChange ↥L) r₁ r₂) :=
        fun l => ⟨(Work.MotC2.transAlgEquiv (D.E.baseChange ↥L) ((d γ : ℕ) • Q))
          (Work.MotV.kleinCoord D ↥L l), hmemτ l⟩
      have hvalτ : ∀ l : Fin 5,
          Work.MotT.evalAtLoc (D.E.baseChange ↥L) r₁ r₂ (Zτ l) = γ (kval l) := by
        intro l
        obtain ⟨hf, hfeq⟩ := Work.MotT.evalAtLoc_transAlgEquiv (D.E.baseChange ↥L)
          ((d γ : ℕ) • Q) hσeq
          (algebraMap (Work.MotC2.Coord (D.E.baseChange ↥L))
            ↥(Work.MotC2.affPlaceAt (D.E.baseChange ↥L) (γ r₁) (γ r₂)) (asKlein D ↥L l))
        rw [Work.MotT.evalAtLoc_algebraMap] at hfeq
        rw [show Zτ l = (⟨(Work.MotC2.transAlgEquiv (D.E.baseChange ↥L) ((d γ : ℕ) • Q))
              (algebraMap (Work.MotC2.Coord (D.E.baseChange ↥L))
                (Work.MotC2.Func (D.E.baseChange ↥L)) (asKlein D ↥L l)), hf⟩ :
              ↥(Work.MotC2.affPlaceAt (D.E.baseChange ↥L) r₁ r₂))
            from Subtype.ext (congrArg
              (Work.MotC2.transAlgEquiv (D.E.baseChange ↥L) ((d γ : ℕ) • Q))
              (asKlein_map D ↥L l)).symm]
        exact hfeq.trans (plugHomAt_asKlein_galois D γ hr hσ l)
      have hvalκ : ∀ l : Fin 5,
          Work.MotT.evalAtLoc (D.E.baseChange ↥L) r₁ r₂ (Z l) = kval l := by
        intro l
        rw [Work.MotT.evalAtLoc_algebraMap]
      -- the function-level cross relation, evaluated at `R`
      have hf : (Work.MotC2.transAlgEquiv (D.E.baseChange ↥L) ((d γ : ℕ) • Q))
            (Work.MotV.kleinCoord D ↥L i) * Work.MotV.kleinCoord D ↥L (j + d γ)
          = (Work.MotC2.transAlgEquiv (D.E.baseChange ↥L) ((d γ : ℕ) • Q))
            (Work.MotV.kleinCoord D ↥L j) * Work.MotV.kleinCoord D ↥L (i + d γ) := by
        rw [← asTransAlgEquiv_pow (D.E.baseChange ↥L) Q (d γ : ℕ)]
        exact asShiftCross D ↥L (Work.MotC2.transAlgEquiv (D.E.baseChange ↥L) Q) lam hlam0
          hshift (d γ) i j
      have hsub : Zτ i * Z (j + d γ) = Zτ j * Z (i + d γ) := by
        refine Subtype.ext ?_
        show (Work.MotC2.transAlgEquiv (D.E.baseChange ↥L) ((d γ : ℕ) • Q))
              (Work.MotV.kleinCoord D ↥L i) *
            (algebraMap (Work.MotC2.Coord (D.E.baseChange ↥L))
              (Work.MotC2.Func (D.E.baseChange ↥L)) (asKlein D ↥L (j + d γ))) =
          (Work.MotC2.transAlgEquiv (D.E.baseChange ↥L) ((d γ : ℕ) • Q))
              (Work.MotV.kleinCoord D ↥L j) *
            (algebraMap (Work.MotC2.Coord (D.E.baseChange ↥L))
              (Work.MotC2.Func (D.E.baseChange ↥L)) (asKlein D ↥L (i + d γ)))
        rw [asKlein_map, asKlein_map]
        exact hf
      have hprod := congrArg (Work.MotT.evalAtLoc (D.E.baseChange ↥L) r₁ r₂) hsub
      rw [map_mul, map_mul] at hprod
      rw [hvalτ i, hvalκ (j + d γ), hvalτ j, hvalκ (i + d γ)] at hprod
      exact hprod
    -- the extraction
    obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hkval_ne
    simp only [Pi.zero_apply] at hi₀
    have hkne : ∀ γ : ↥L ≃ₐ[RatFunc 𝕜] ↥L, kval (i₀ + d γ) ≠ 0 := by
      intro γ
      have hstep := hcross_val γ (i₀ - d γ) i₀
      rw [sub_add_cancel] at hstep
      intro h0
      rw [h0, mul_zero] at hstep
      rcases mul_eq_zero.mp hstep.symm with h3 | h3
      · exact hi₀ (γ.injective (by rw [h3, map_zero]))
      · exact hi₀ h3
    refine lamExtraction 𝕜 D hD g L hW kval hkval_ne ?_ d hd
      (fun γ => γ (kval i₀) / kval (i₀ + d γ)) (fun γ => ?_) (fun γ i => ?_)
    · intro k
      rw [← IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) ↥L D.a,
        ← IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) ↥L D.b]
      exact hkleinP k
    · exact div_ne_zero (fun h => hi₀ (γ.injective (by rw [h, map_zero]))) (hkne γ)
    · rw [div_mul_eq_mul_div, eq_div_iff (hkne γ)]
      exact hcross_val γ i i₀

end

end Work.MotV5.LamAS.CoordNe
