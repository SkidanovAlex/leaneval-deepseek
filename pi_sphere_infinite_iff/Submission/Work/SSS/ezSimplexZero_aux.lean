import Mathlib
import Submission.Work.SSS.serreE1EZ
import Submission.Work.SSS.iotaF_chainMap
import Submission.Work.SSS.ezGen_snd_sum_zero

/-!
# Auxiliary lemmas for the `0`-face cycle computation

Small general-purpose lemmas used in `Submission/Work/SSS/ezSimplexZero_chain_cycle.lean`:

* `Work.SSS.down_next_eq` : the predecessor of the homology complex shape;
* `Work.SSS.mem_boundary_of_lt_degree` : a simplex of `Δ[P]` in degree `< P` lies in `∂Δ[P]`;
* `Work.SSS.sCCMap_pieceπOf_genP_bdry` : a generator `genP x y` with `x ∈ ∂Δ[P]` is killed by the
  projection to the σ-piece;
* `Work.SSS.cokernel_sCCMap_d` : the differential of the quotient `C(T_σ)/C(∂T_σ)` commutes with the
  projection and with `sCCMap` (in the abstract form for a subcomplex), and
  `Work.SSS.pieceAlong_d_pieceπOf_sCCMap` : the same statement for the σ-piece itself;
* `Work.SSS.ezGen_snd_sum_zero_next` : `Work.SSS.ezGen_snd_sum_zero` with the cycle hypothesis
  indexed by `(ComplexShape.down ℕ).next`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology

noncomputable section

/-- The predecessor in the chain-complex shape `… → 2 → 1 → 0`. -/
lemma down_next_eq (n : ℕ) : (ComplexShape.down ℕ).next n = n - 1 := by
  rcases n with _ | k
  · rw [ComplexShape.next_eq_self' _ 0 (fun k hk => Nat.succ_ne_zero k hk)]
  · rw [ComplexShape.next_eq' _ (ComplexShape.down_mk (k + 1) k rfl)]
    omega

/-- A `k`-simplex of `Δ[P]` with `k < P` lies in the boundary `∂Δ[P]`: its underlying monotone map
`Fin (k+1) → Fin (P+1)` cannot be surjective. -/
theorem mem_boundary_of_lt_degree {P k : ℕ} (h : k < P)
    (x : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) _⦋k⦌) :
    x ∈ (SSet.boundary P).obj (op ⦋k⦌) := by
  rw [SSet.mem_boundary_iff_notMem_range]
  by_contra hc
  push Not at hc
  have hsurj : Function.Surjective (fun i : Fin (k + 1) => (⇑x : Fin (k + 1) → Fin (P + 1)) i) :=
    fun j => hc j
  have hle := Fintype.card_le_of_surjective _ hsurj
  simp only [Fintype.card_fin] at hle
  omega

/-- **The projection to the σ-piece kills the generators carried by `∂Δ[P]`.**  For a simplex
`x` of `Δ[P]` lying in the boundary and any simplex `y` of `F` in the same degree, the image of the
generator `genP x y` of `C(Δ[P] ⊗ F)` in the σ-piece `C(T_σ)/C(∂T_σ)` is zero. -/
theorem sCCMap_pieceπOf_genP_bdry {Xf Yf F : SSet.{0}} (f : Xf ⟶ Yf) (P : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Yf)
    (ez : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⊗ F ⟶ pullAlong f σ)
    (hez : ez ≫ pullback.fst σ f = SemiCartesianMonoidalCategory.fst _ _)
    {k : ℕ} (x : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) _⦋k⦌)
    (hx : x ∈ (SSet.boundary P).obj (op ⦋k⦌)) (y : F _⦋k⦌) :
    (ModuleCat.Hom.hom ((pieceπOf f σ).f k))
      ((ModuleCat.Hom.hom ((sCCMap ez).f k)) (Work.KunnethEZ.genP x y)) = 0 := by
  refine Work.SSS.IotaAux.sCCMap_piecepiOf_elt_eq_zero f σ ez (x, y) ?_
  change (pullback.fst σ f).app (op ⦋k⦌) (ez.app (op ⦋k⦌) (x, y))
    ∈ (SSet.boundary P).obj (op ⦋k⦌)
  have hc : (ez ≫ pullback.fst σ f).app (op ⦋k⦌) (x, y)
      = (SemiCartesianMonoidalCategory.fst
          (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) F).app (op ⦋k⦌) (x, y) :=
    congrArg (fun (φ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⊗ F
        ⟶ (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0})) =>
      φ.app (op ⦋k⦌) (x, y)) hez
  have hgoal : (pullback.fst σ f).app (op ⦋k⦌) (ez.app (op ⦋k⦌) (x, y)) = x := hc.trans rfl
  rw [hgoal]
  exact hx

/-- **The differential of the quotient commutes with `sCCMap`.**  For a subcomplex `K ⊆ B` and a
simplicial map `w : A ⟶ B`, the differential of the cokernel complex `C(B)/C(K)` sends the class of
`sCCMap w z` to the class of `sCCMap w (∂ z)`. -/
theorem cokernel_sCCMap_d {A B : SSet.{0}} (K : B.Subcomplex) (w : A ⟶ B) {i j : ℕ}
    (z : (sCC A).X i) :
    (cokernel (sCCMap K.ι)).d i j
        ((cokernel.π (sCCMap K.ι)).f i ((sCCMap w).f i z))
      = (cokernel.π (sCCMap K.ι)).f j ((sCCMap w).f j (((sCC A).d i j) z)) := by
  have hπ := HomologicalComplex.Hom.comm (cokernel.π (sCCMap K.ι)) i j
  have hw := HomologicalComplex.Hom.comm (sCCMap w) i j
  have e1 := congrArg (fun (g : (sCC B).X i ⟶ (cokernel (sCCMap K.ι)).X j) =>
      g.hom ((sCCMap w).f i z)) hπ
  have e2 := congrArg (fun (g : (sCC A).X i ⟶ (sCC B).X j) => g.hom z) hw
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e1 e2
  rw [e1, e2]

/-- The differential of the σ-piece commutes with the projection `pieceπOf` and with `sCCMap`. -/
theorem pieceAlong_d_pieceπOf_sCCMap {Xf Yf F : SSet.{0}} (f : Xf ⟶ Yf) {P : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Yf)
    (ez : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⊗ F ⟶ pullAlong f σ)
    {i j : ℕ} (z : (sCC ((SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⊗ F)).X i) :
    (pieceAlong f σ).d i j ((pieceπOf f σ).f i ((sCCMap ez).f i z))
      = (pieceπOf f σ).f j
          ((sCCMap ez).f j (((sCC ((SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⊗ F)).d i j) z)) :=
  cokernel_sCCMap_d (bdryAlong f σ) ez z

/-- `Work.SSS.ezGen_snd_sum_zero` with the cycle hypothesis indexed by
`(ComplexShape.down ℕ).next`. -/
theorem ezGen_snd_sum_zero_next (X Y : SSet.{0}) (n q : ℕ) (σ : X _⦋n⦌)
    (τ : Y _⦋q+1⦌)
    (hτ : (ModuleCat.Hom.hom ((sCC Y).d (q + 1) ((ComplexShape.down ℕ).next (q + 1))))
        (((Y).ιChainComplex (R := ModuleCat.of ℤ ℤ) τ).hom 1) = 0) :
    (∑ j : Fin (q + 2), ((-1 : ℤ) ^ (j : ℕ)) •
      Work.Cohomology.Crux33.ezGen n q X Y σ (Y.δ j τ)) = 0 := by
  rw [down_next_eq (q + 1)] at hτ
  exact Work.SSS.ezGen_snd_sum_zero X Y n q σ τ hτ

/-! ## The cycle property of the shuffle chain in the σ-piece

The master lemma: for an arbitrary lift `ez : Δ[P] ⊗ F ⟶ T_σ` lying over `pr₁ ≫ σ` and a cycle
`τ` of `F` in degree `q`, the shuffle chain `ezGen P q Δ[P] F [id_P] τ`, pushed into `T_σ` by `ez`
and projected to the σ-piece `C(T_σ)/C(∂T_σ)`, is a cycle. -/

/-- **The shuffle chain `ezGen P q [id_P] τ`, pushed into the σ-piece, is a cycle.** -/
theorem sCCMap_ezGen_chain_cycle {Xf Yf F : SSet.{0}} (f : Xf ⟶ Yf) (P q : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Yf)
    (ez : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⊗ F ⟶ pullAlong f σ)
    (hez : ez ≫ pullback.fst σ f = SemiCartesianMonoidalCategory.fst _ _)
    (τ : F _⦋q⦌)
    (hτ : (ModuleCat.Hom.hom ((sCC F).d q ((ComplexShape.down ℕ).next q)))
        (((F).ιChainComplex (R := ModuleCat.of ℤ ℤ) τ).hom 1) = 0) :
    (ModuleCat.Hom.hom ((pieceAlong f σ).d (P+q) ((ComplexShape.down ℕ).next (P+q))))
      ((ModuleCat.Hom.hom ((pieceπOf f σ).f (P+q)))
        ((ModuleCat.Hom.hom ((sCCMap ez).f (P+q)))
          (Work.Cohomology.Crux33.ezGen P q
            (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) F (stdIdSimplex P) τ))) = 0 := by
  rcases Nat.eq_zero_or_pos q with hq0 | hqpos
  · -- ## `q = 0`
    subst hq0
    rcases Nat.eq_zero_or_pos P with hP0 | hPpos
    · -- `P = q = 0`: the differential `d 0 0` vanishes
      subst hP0
      have hz : ((pieceAlong f σ).d (0+0) ((ComplexShape.down ℕ).next (0+0))) = 0 := by
        rw [show (ComplexShape.down ℕ).next (0+0) = 0 from ChainComplex.next_nat_zero]
        exact HomologicalComplex.shape _ 0 0 (by rw [ComplexShape.down_Rel]; omega)
      rw [hz]
      simp
    · -- `P = P'+1`, `q = 0`
      obtain ⟨P', rfl⟩ : ∃ P', P = P' + 1 := ⟨P - 1, by omega⟩
      rw [show (ComplexShape.down ℕ).next (P' + 1 + 0) = P' from
        ChainComplex.next_nat_succ P']
      rw [pieceAlong_d_pieceπOf_sCCMap]
      -- the shuffle chain `ezGen (P'+1) 0 [id] τ` is the single generator `genP x y`
      rw [Work.KunnethEZ.ezGen_zero_single_right]
      -- its boundary is `Σ_j (-1)^j genP ((Δ[P'+1]).δ_j x) (F.δ_j y)`
      rw [Work.KunnethEZ.d_genP (n := P')]
      simp only [map_sum, map_zsmul]
      -- every `Δ[P'+1]`-component of the boundary is a `P'`-simplex, hence lies in `∂Δ[P'+1]`
      have hgen : ∀ (x : (SSet.stdSimplex.obj (SimplexCategory.mk (P'+1)) : SSet.{0}) _⦋P'⦌)
          (y : F _⦋P'⦌),
          (ModuleCat.Hom.hom ((pieceπOf f σ).f P'))
            ((ModuleCat.Hom.hom ((sCCMap ez).f P')) (Work.KunnethEZ.genP x y)) = 0 :=
        fun x y => Work.SSS.sCCMap_pieceπOf_genP_bdry f (P'+1) σ ez hez x
          (Work.SSS.mem_boundary_of_lt_degree (by omega) x) y
      refine Finset.sum_eq_zero (fun j _ => ?_)
      rw [hgen]
      exact zsmul_zero _
  · -- ## `q = q'+1`
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    have hτ' : (ModuleCat.Hom.hom ((sCC F).d (q'+1) q'))
        (((F).ιChainComplex (R := ModuleCat.of ℤ ℤ) τ).hom 1) = 0 := by
      rw [ChainComplex.next_nat_succ q'] at hτ
      exact hτ
    rcases Nat.eq_zero_or_pos P with hP0 | hPpos
    · -- `P = 0`, `q = q'+1`: only the `Y`-boundary part survives, and it is `ι(∂τ) = 0`
      subst hP0
      rw [show (ComplexShape.down ℕ).next (0 + (q'+1)) = 0 + q' from
        ChainComplex.next_nat_succ (0 + q')]
      rw [pieceAlong_d_pieceπOf_sCCMap]
      have hb : ((sCC ((SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⊗ F)).d
            (0 + (q'+1)) (0 + q'))
          (Work.Cohomology.Crux33.ezGen 0 (q'+1)
            (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) F (stdIdSimplex 0) τ)
          = ∑ j : Fin (q'+2), ((-1 : ℤ) ^ (j : ℕ)) •
              Work.Cohomology.Crux33.ezGen 0 q'
                (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) F (stdIdSimplex 0)
                (F.δ j τ) :=
        Work.SSS.ezGen_boundary_zero q' (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})
          F (stdIdSimplex 0) τ
      rw [hb]
      rw [Work.SSS.ezGen_snd_sum_zero (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) F 0 q'
        (stdIdSimplex 0) τ hτ']
      simp
    · -- `P = P'+1`, `q = q'+1`: the `X`-boundary part dies in the piece, the `Y`-part is `ι(∂τ)`
      obtain ⟨P', rfl⟩ : ∃ P', P = P' + 1 := ⟨P - 1, by omega⟩
      rw [show (ComplexShape.down ℕ).next ((P'+1) + (q'+1)) = (P'+1) + q' from
        ChainComplex.next_nat_succ ((P'+1) + q')]
      rw [pieceAlong_d_pieceπOf_sCCMap]
      have hb : ((sCC ((SSet.stdSimplex.obj (SimplexCategory.mk (P'+1)) : SSet.{0}) ⊗ F)).d
            ((P'+1) + (q'+1)) ((P'+1) + q'))
          (Work.Cohomology.Crux33.ezGen (P'+1) (q'+1)
            (SSet.stdSimplex.obj (SimplexCategory.mk (P'+1)) : SSet.{0}) F (stdIdSimplex (P'+1)) τ)
          = xChain P' q' (SSet.stdSimplex.obj (SimplexCategory.mk (P'+1)) : SSet.{0}) F
              (stdIdSimplex (P'+1)) τ
            + ((-1 : ℤ) ^ (P'+1)) •
              yChain (P'+1) q' (SSet.stdSimplex.obj (SimplexCategory.mk (P'+1)) : SSet.{0}) F
                (stdIdSimplex (P'+1)) τ :=
        Work.SSS.ezGen_boundary_succ P' q'
          (SSet.stdSimplex.obj (SimplexCategory.mk (P'+1)) : SSet.{0}) F (stdIdSimplex (P'+1)) τ
      rw [hb]
      have hy : yChain (P'+1) q' (SSet.stdSimplex.obj (SimplexCategory.mk (P'+1)) : SSet.{0}) F
          (stdIdSimplex (P'+1)) τ = 0 := by
        rw [Work.SSS.yChain_eq_ezGen]
        exact Work.SSS.ezGen_snd_sum_zero
          (SSet.stdSimplex.obj (SimplexCategory.mk (P'+1)) : SSet.{0}) F (P'+1) q'
          (stdIdSimplex (P'+1)) τ hτ'
      have hz : ((-1 : ℤ) ^ (P'+1)) •
          yChain (P'+1) q' (SSet.stdSimplex.obj (SimplexCategory.mk (P'+1)) : SSet.{0}) F
            (stdIdSimplex (P'+1)) τ = 0 := by
        rw [hy]
        exact zsmul_zero _
      rw [hz, add_zero]
      exact Work.SSS.IotaAux.xChain_piecePi_eq_zero f P' q' σ ez hez τ

end

end Work.SSS
