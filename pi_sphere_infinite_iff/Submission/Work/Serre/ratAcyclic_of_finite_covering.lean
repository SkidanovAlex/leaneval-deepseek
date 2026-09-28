import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Serre.Models
import Submission.Work.Serre.serreRangeEMVanAll

/-!
# A finite covering of a rationally acyclic space is rationally acyclic

If `p : E → X` is a finite (`m`-sheeted) covering map and `E` is rationally acyclic, then so is `X`.
The mathematical content is the **transfer**: the sum of the `m` lifts of a singular simplex is a
chain map `τ : C_*(X;ℚ) → C_*(E;ℚ)` with `τ ≫ p_# = m • id`, and `m` is invertible in `ℚ`.

The only geometric input is that a covering is trivial over a simplex: `Δⁿ` is simply connected and
locally path connected, so a lifting of a simplex is determined by its value at one point
(`IsCoveringMap.existsUnique_continuousMap_lifts`).  Hence two lifts that agree at one point are
equal, and there are exactly `m` lifts of every simplex, enumerated by the value at the first vertex.
For a face of a simplex, the `m` face-lifts are `m` distinct lifts of the face — of which there are
exactly `m` — so they exhaust them; the sums over `Fin m` are therefore equal with no transport
between index types, which is what makes the chain map property formal.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial Topology
open Simplicial

namespace Work.Serre

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.defProp false

namespace FiniteCover

variable {E X : Type} [TopologicalSpace E] [TopologicalSpace X]

variable {E X : Type} [TopologicalSpace E] [TopologicalSpace X]

abbrev coFace (n : ℕ) (i : Fin (n + 2)) :
    C(stdSimplex ℝ (Fin (n + 1)), stdSimplex ℝ (Fin (n + 2))) :=
  ⟨stdSimplex.map (Fin.succAbove i), stdSimplex.continuous_map _⟩

abbrev sing (Y : Type) [TopologicalSpace Y] : SSet := TopCat.toSSet.obj (TopCat.of Y)
abbrev simpOf (Y : Type) [TopologicalSpace Y] (n : ℕ) (τ : C(stdSimplex ℝ (Fin (n+1)), Y)) :
    sing Y _⦋n⦌ := ((TopCat.of Y).toSSetObjEquivT (Opposite.op ⦋n⦌)).symm τ
abbrev simOf (Y : Type) [TopologicalSpace Y] (n : ℕ) (a : sing Y _⦋n⦌) :
    C(stdSimplex ℝ (Fin (n+1)), Y) := ((TopCat.of Y).toSSetObjEquivT (Opposite.op ⦋n⦌)) a

theorem simOf_simpOf (Y : Type) [TopologicalSpace Y] (n : ℕ)
    (τ : C(stdSimplex ℝ (Fin (n+1)), Y)) : simOf Y n (simpOf Y n τ) = τ :=
  Equiv.apply_symm_apply _ _

theorem simpOf_simOf (Y : Type) [TopologicalSpace Y] (n : ℕ) (a : sing Y _⦋n⦌) :
    simpOf Y n (simOf Y n a) = a :=
  Equiv.symm_apply_apply _ _

theorem delta_simpOf (Y : Type) [TopologicalSpace Y] (n : ℕ) (i : Fin (n + 2))
    (τ : C(stdSimplex ℝ (Fin (n+2)), Y)) :
    (sing Y).δ i (simpOf Y (n+1) τ) = simpOf Y n (τ.comp (coFace n i)) := by
  rw [show (sing Y).δ i = (TopCat.toSSet.obj (TopCat.of Y)).map (SimplexCategory.δ i).op from rfl]
  have h := TopCat.toSSetObjEquivT_symm_naturality (X := TopCat.of Y) (SimplexCategory.δ i) τ
  rw [h]
  simp only [simpOf]
  congr 1

theorem toSSetMap_simpOf {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    (g : C(E, X)) (n : ℕ) (τ : C(stdSimplex ℝ (Fin (n+1)), E)) :
    (TopCat.toSSet.map (TopCat.ofHom g)).app (Opposite.op ⦋n⦌) (simpOf E n τ) =
      simpOf X n (g.comp τ) := by
  apply ((TopCat.of X).toSSetObjEquivT (Opposite.op ⦋n⦌)).injective
  ext z
  simp only [simpOf, Equiv.apply_symm_apply, ContinuousMap.comp_apply]
  rfl

theorem simOf_delta (Y : Type) [TopologicalSpace Y] (n : ℕ) (i : Fin (n + 2))
    (a : sing Y _⦋n+1⦌) :
    simOf Y n ((sing Y).δ i a) = (simOf Y (n+1) a).comp (coFace n i) := by
  conv_lhs => rw [← simpOf_simOf Y (n+1) a]
  rw [delta_simpOf Y n i (simOf Y (n+1) a), simOf_simpOf]

abbrev sVert (n : ℕ) : stdSimplex ℝ (Fin (n + 1)) := stdSimplex.vertex (0 : Fin (n + 1))

instance instSimplyConnected (n : ℕ) : SimplyConnectedSpace (stdSimplex ℝ (Fin (n + 1))) := by
  haveI : ContractibleSpace (stdSimplex ℝ (Fin (n + 1))) :=
    (convex_stdSimplex ℝ (Fin (n + 1))).contractibleSpace
      ⟨_, (stdSimplex.vertex (0 : Fin (n + 1))).2⟩
  infer_instance

instance instLocallyPathConnected (n : ℕ) :
    LocallyPathConnectedSpace (stdSimplex ℝ (Fin (n + 1))) :=
  (convex_stdSimplex ℝ (Fin (n + 1))).locallyPathConnectedSpace

theorem existsUnique_lift (p : C(E, X)) (hp : IsCoveringMap p) (n : ℕ)
    (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) (e : E) (he : p e = σ (sVert n)) :
    ∃! F : C(stdSimplex ℝ (Fin (n + 1)), E), F (sVert n) = e ∧ p.comp F = σ := by
  have h := hp.existsUnique_continuousMap_lifts σ (sVert n) e he
  refine ⟨h.choose, ⟨h.choose_spec.1.1, ?_⟩, fun G hG => ?_⟩
  · ext z; exact congr_fun h.choose_spec.1.2 z
  · exact h.choose_spec.2 G ⟨hG.1, by ext z; exact congr_fun (congrArg DFunLike.coe hG.2) z⟩

theorem lift_eq_of_lifts_eq {p : C(E, X)} (hp : IsCoveringMap p) {n : ℕ}
    {σ : C(stdSimplex ℝ (Fin (n + 1)), X)} {ρ ρ' : C(stdSimplex ℝ (Fin (n + 1)), E)}
    (hρ : p.comp ρ = σ) (hρ' : p.comp ρ' = σ) (z : stdSimplex ℝ (Fin (n + 1)))
    (hz : ρ z = ρ' z) : ρ = ρ' := by
  have hfun : ⇑ρ = ⇑ρ' := by
    refine hp.eq_of_comp_eq ρ.2 ρ'.2 ?_ z hz
    ext w
    exact (congr_fun (congrArg DFunLike.coe hρ) w).trans
      (congr_fun (congrArg DFunLike.coe hρ').symm w)
  exact ContinuousMap.ext fun w => congr_fun hfun w

/-- The data of a finite covering. -/
structure CoverData (E X : Type) [TopologicalSpace E] [TopologicalSpace X] where
  p : C(E, X)
  hp : IsCoveringMap p
  m : ℕ
  hm : 0 < m
  hcard : ∀ x : X, Nat.card ↥(p ⁻¹' {x}) = m

variable (D : CoverData E X)

theorem fibre_finite (x : X) : Finite ↥(D.p ⁻¹' {x}) := by
  refine Finite.of_not_infinite fun hinf => ?_
  have h0 : Nat.card ↥(D.p ⁻¹' {x}) = 0 := Nat.card_eq_zero.mpr (Or.inr hinf)
  have h1 : Nat.card ↥(D.p ⁻¹' {x}) = D.m := D.hcard x
  rw [h0] at h1
  exact (Nat.lt_irrefl 0 (h1 ▸ D.hm)).elim

theorem fibre_equiv_fin (x : X) : Nonempty (↥(D.p ⁻¹' {x}) ≃ Fin D.m) := by
  have hf := fibre_finite D x
  haveI : Fintype ↥(D.p ⁻¹' {x}) := Fintype.ofFinite _
  have h : Fintype.card ↥(D.p ⁻¹' {x}) = D.m := by
    rw [← Nat.card_eq_fintype_card]
    exact D.hcard x
  exact ⟨Fintype.equivFinOfCardEq h⟩

noncomputable def fibEquiv (x : X) : ↥(D.p ⁻¹' {x}) ≃ Fin D.m :=
  Classical.choice (fibre_equiv_fin D x)

noncomputable def liftSpec (n : ℕ) (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) (k : Fin D.m) :
    ∃! F : C(stdSimplex ℝ (Fin (n + 1)), E),
      F (sVert n) = ((fibEquiv D (σ (sVert n))).symm k).1 ∧ D.p.comp F = σ :=
  existsUnique_lift D.p D.hp n σ _ (by
    have h := ((fibEquiv D (σ (sVert n))).symm k).2
    rwa [Set.mem_preimage, Set.mem_singleton_iff] at h)

noncomputable def liftK (n : ℕ) (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) (k : Fin D.m) :
    C(stdSimplex ℝ (Fin (n + 1)), E) :=
  Classical.choose (liftSpec D n σ k)

theorem liftK_val (n : ℕ) (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) (k : Fin D.m) :
    liftK D n σ k (sVert n) = ((fibEquiv D (σ (sVert n))).symm k).1 :=
  (Classical.choose_spec (liftSpec D n σ k)).1.1

theorem liftK_lifts (n : ℕ) (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) (k : Fin D.m) :
    D.p.comp (liftK D n σ k) = σ :=
  (Classical.choose_spec (liftSpec D n σ k)).1.2

theorem liftK_eq_iff (n : ℕ) (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) (k : Fin D.m)
    {F : C(stdSimplex ℝ (Fin (n + 1)), E)} :
    F = liftK D n σ k ↔
      F (sVert n) = ((fibEquiv D (σ (sVert n))).symm k).1 ∧ D.p.comp F = σ :=
  ⟨fun h => h ▸ ⟨liftK_val D n σ k, liftK_lifts D n σ k⟩,
    fun h => (Classical.choose_spec (liftSpec D n σ k)).2 F h⟩

theorem liftK_injective (n : ℕ) (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    Function.Injective (liftK D n σ) := by
  intro k k' h
  have h1 : ((fibEquiv D (σ (sVert n))).symm k).1 =
      ((fibEquiv D (σ (sVert n))).symm k').1 := by
    rw [← liftK_val D n σ k, ← liftK_val D n σ k', h]
  have h2 : (fibEquiv D (σ (sVert n))).symm k = (fibEquiv D (σ (sVert n))).symm k' :=
    Subtype.ext h1
  exact (fibEquiv D (σ (sVert n))).symm.injective h2

theorem liftK_surjective (n : ℕ) (σ : C(stdSimplex ℝ (Fin (n + 1)), X))
    {ρ : C(stdSimplex ℝ (Fin (n + 1)), E)} (hρ : D.p.comp ρ = σ) :
    ∃ k : Fin D.m, ρ = liftK D n σ k := by
  refine ⟨fibEquiv D (σ (sVert n)) ⟨ρ (sVert n), ?_⟩, ?_⟩
  · rw [Set.mem_preimage, Set.mem_singleton_iff]
    exact congr_fun (congrArg DFunLike.coe hρ) (sVert n)
  · rw [liftK_eq_iff]
    refine ⟨?_, hρ⟩
    simp

theorem liftK_face_injective (n : ℕ) (σ : C(stdSimplex ℝ (Fin (n + 2)), X)) (i : Fin (n + 2)) :
    Function.Injective fun k : Fin D.m =>
      (liftK D (n + 1) σ k).comp (coFace n i) := by
  intro k k' h
  refine liftK_injective D (n + 1) σ ?_
  refine lift_eq_of_lifts_eq D.hp (liftK_lifts D (n + 1) σ k) (liftK_lifts D (n + 1) σ k')
    ((coFace n i) (sVert n)) ?_
  exact congr_fun (congrArg DFunLike.coe h) (sVert n)

theorem liftK_face (n : ℕ) (σ : C(stdSimplex ℝ (Fin (n + 2)), X)) (i : Fin (n + 2)) :
    ∃ φ : Fin D.m → Fin D.m, Function.Bijective φ ∧ ∀ k : Fin D.m,
      (liftK D (n + 1) σ k).comp (coFace n i) =
        liftK D n (σ.comp (coFace n i)) (φ k) := by
  have h : ∀ k : Fin D.m, ∃ k' : Fin D.m,
      (liftK D (n + 1) σ k).comp (coFace n i) =
        liftK D n (σ.comp (coFace n i)) k' := fun k =>
    liftK_surjective D n (σ.comp (coFace n i))
      (by rw [← ContinuousMap.comp_assoc, liftK_lifts])
  refine ⟨fun k => Classical.choose (h k), ?_, fun k => Classical.choose_spec (h k)⟩
  refine (Function.Injective.bijective_of_finite ?_)
  intro k k' hk
  dsimp only at hk
  refine liftK_face_injective D n σ i ?_
  show (liftK D (n + 1) σ k).comp (coFace n i) = (liftK D (n + 1) σ k').comp (coFace n i)
  rw [Classical.choose_spec (h k), Classical.choose_spec (h k'), hk]

abbrev qC : ModuleCat ℚ := ModuleCat.of ℚ ℚ

noncomputable def transfer (n : ℕ) :
    ((sing X).chainComplex qC).X n ⟶ ((sing E).chainComplex qC).X n :=
  Cofan.IsColimit.desc (A := ((sing E).chainComplex qC).X n)
    ((sing X).isColimitChainComplexXCofan qC n)
    (fun a => ∑ k : Fin D.m, (sing E).ιChainComplex (R := qC)
      (simpOf E n (liftK D n (simOf X n a) k)))

theorem transfer_ι (n : ℕ) (a : sing X _⦋n⦌) :
    (sing X).ιChainComplex (R := qC) a ≫ transfer D n =
      ∑ k : Fin D.m, (sing E).ιChainComplex (R := qC)
        (simpOf E n (liftK D n (simOf X n a) k)) :=
  Cofan.IsColimit.fac (A := ((sing E).chainComplex qC).X n)
    ((sing X).isColimitChainComplexXCofan qC n)
    (fun a => ∑ k : Fin D.m, (sing E).ιChainComplex (R := qC)
      (simpOf E n (liftK D n (simOf X n a) k))) a

theorem sum_liftK_face (n : ℕ) (σ : C(stdSimplex ℝ (Fin (n + 2)), X)) (i : Fin (n + 2)) :
    (∑ k : Fin D.m, (sing E).ιChainComplex (R := qC)
        (simpOf E n ((liftK D (n + 1) σ k).comp (coFace n i)))) =
      ∑ k : Fin D.m, (sing E).ιChainComplex (R := qC)
        (simpOf E n (liftK D n (σ.comp (coFace n i)) k)) := by
  obtain ⟨φ, hφ, hφk⟩ := liftK_face D n σ i
  refine Fintype.sum_bijective φ hφ (fun k => (sing E).ιChainComplex (R := qC)
      (simpOf E n ((liftK D (n + 1) σ k).comp (coFace n i))))
    (fun k => (sing E).ιChainComplex (R := qC)
      (simpOf E n (liftK D n (σ.comp (coFace n i)) k))) ?_
  intro k
  rw [hφk k]

abbrev pChainMap :
    (sing E).chainComplex qC ⟶ (sing X).chainComplex qC :=
  SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom D.p)) qC

theorem transfer_comp_chainMap (n : ℕ) :
    transfer D n ≫ (pChainMap D).f n =
      (D.m : ℚ) • 𝟙 (((sing X).chainComplex qC).X n) := by
  apply SSet.chainComplex_hom_ext
  intro a
  have h1 : (sing X).ιChainComplex (R := qC) a ≫
      (transfer D n ≫ (pChainMap D).f n)
      = D.m • (sing X).ιChainComplex (R := qC) a := by
    rw [← Category.assoc, transfer_ι, Preadditive.sum_comp]
    simp only [SSet.ι_chainComplexMap_f, toSSetMap_simpOf, liftK_lifts, simpOf_simOf]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have h2 : (sing X).ιChainComplex (R := qC) a ≫
      ((D.m : ℚ) • 𝟙 (((sing X).chainComplex qC).X n))
      = D.m • (sing X).ιChainComplex (R := qC) a := by
    rw [Linear.comp_smul, Category.comp_id, Nat.cast_smul_eq_nsmul]
  exact h1.trans h2.symm

theorem transfer_d (n : ℕ) :
    transfer D (n + 1) ≫ ((sing E).chainComplex qC).d (n + 1) n =
      ((sing X).chainComplex qC).d (n + 1) n ≫ transfer D n := by
  apply SSet.chainComplex_hom_ext
  intro a
  have hL : (sing X).ιChainComplex (R := qC) a ≫
      (transfer D (n + 1) ≫ ((sing E).chainComplex qC).d (n + 1) n) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        ∑ k : Fin D.m, (sing E).ιChainComplex (R := qC)
          (simpOf E n (liftK D n ((simOf X (n + 1) a).comp (coFace n i)) k)) := by
    rw [← Category.assoc, transfer_ι, Preadditive.sum_comp]
    simp only [SSet.ιChainComplex_d]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.smul_sum]
    simp only [delta_simpOf]
    exact congrArg (fun x => (-1 : ℤ) ^ (i : ℕ) • x)
      (sum_liftK_face D n (simOf X (n + 1) a) i)
  have hR : (sing X).ιChainComplex (R := qC) a ≫
      (((sing X).chainComplex qC).d (n + 1) n ≫ transfer D n) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        ∑ k : Fin D.m, (sing E).ιChainComplex (R := qC)
          (simpOf E n (liftK D n ((simOf X (n + 1) a).comp (coFace n i)) k)) := by
    rw [← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp]
    simp only [Preadditive.zsmul_comp, transfer_ι, simOf_delta]
  rw [hL, hR]


theorem homologyMap_smul_id (c : ℚ) (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :
    HomologicalComplex.homologyMap (c • 𝟙 K) n = c • 𝟙 (K.homology n) := by
  rw [← HomologicalComplex.homologyFunctor_map (ModuleCat ℚ) (ComplexShape.down ℕ) n (c • 𝟙 K),
    Functor.map_smul, HomologicalComplex.homologyFunctor_map, HomologicalComplex.homologyMap_id]
  rfl

noncomputable def transferChain :
    Work.Serre.ratChains (TopCat.of X) ⟶ Work.Serre.ratChains (TopCat.of E) :=
  ChainComplex.ofHom (fun n => transfer D n) (fun n => transfer_d D n)

theorem transferChain_comp_chainMap :
    transferChain D ≫ Work.Cohomology.chainMap ℚ (TopCat.of E) (TopCat.of X) (TopCat.ofHom D.p) =
      (D.m : ℚ) • 𝟙 (Work.Serre.ratChains (TopCat.of X)) := by
  apply HomologicalComplex.hom_ext
  intro n
  exact transfer_comp_chainMap D n


end FiniteCover

theorem ratAcyclic_of_finite_covering {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    (p : C(E, X)) (hp : IsCoveringMap p) [PathConnectedSpace X] (m : ℕ) (hm : 0 < m)
    (hcard : ∀ x : X, Nat.card ↥(p ⁻¹' {x}) = m)
    (hE : Work.Serre.RatAcyclic E) : Work.Serre.RatAcyclic X := by
  let D : FiniteCover.CoverData E X := ⟨p, hp, m, hm, hcard⟩
  have hvan : ∀ n : ℕ, 0 < n → IsZero (ratH (TopCat.of X) n) := by
    intro n hn
    have hhom := congrArg (fun (f : ratChains (TopCat.of X) ⟶ ratChains (TopCat.of X)) =>
        HomologicalComplex.homologyMap f n) (FiniteCover.transferChain_comp_chainMap D)
    rw [HomologicalComplex.homologyMap_comp] at hhom
    rw [FiniteCover.homologyMap_smul_id] at hhom
    have hpz : HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℚ (TopCat.of E) (TopCat.of X) (TopCat.ofHom D.p)) n = 0 :=
      IsZero.eq_zero_of_src (hE.isZero_ratH hn) _
    rw [hpz, comp_zero] at hhom
    have hmm : (D.m : ℚ) • 𝟙 (ratH (TopCat.of X) n) = 0 := hhom.symm
    have hid : 𝟙 (ratH (TopCat.of X) n) = 0 := by
      have hmq : (D.m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp D.hm)
      calc 𝟙 (ratH (TopCat.of X) n)
          = (D.m : ℚ)⁻¹ • ((D.m : ℚ) • 𝟙 (ratH (TopCat.of X) n)) := by
            rw [smul_smul, inv_mul_cancel₀ hmq, one_smul]
        _ = 0 := by rw [hmm, smul_zero]
    exact (IsZero.iff_id_eq_zero _).mpr hid
  intro n
  rcases Nat.eq_zero_or_pos n with h | hn
  · subst h
    exact isIso_ratHomologyMap_toPoint_zero_of_subsingleton_pi0 X (Classical.arbitrary X)
      (subsingleton_pi0_of_pathConnectedSpace X _)
  · exact IsZero.isIso (hvan n hn)
      (Work.Cohomology.homologyContractible_ring ℚ (X := TopCat.of PUnit) n hn) _

end

end Work.Serre
