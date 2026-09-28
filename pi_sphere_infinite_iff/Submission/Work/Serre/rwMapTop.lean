import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Serre.Engine
import Submission.Work.Serre.C1Cyl
import Submission.Work.Serre.C1CylExplicit
import Submission.Work.Serre.RangeOne.Comparison
import Submission.Work.Serre.RangeOne.rangeWhitehead
import Submission.Work.Serre.RangeOne.subsingletonRelPiRange
import Submission.Work.Serre.serreAttachKillPi
import Submission.Work.Serre.serrePostnikovTower
import Submission.Work.Serre.cylRelPi
import Submission.Work.Serre.cylJoinedIncl
import Submission.Work.Serre.attachIncl_pi0_bijective
import Submission.Work.Serre.attachIncl_piMap_bijective_of_compress
import Submission.Work.RatHurewicz.compression_of_relPiVanishing
import Submission.Work.RatHurewicz.compressRel_attachCells_range
import Submission.Work.RatHurewicz.CompressRelToRelPi
import Submission.Work.Serre.rwCompressRelKillCellsA
import Submission.Work.Cohomology.good_empty
import Submission.Work.Cohomology.isZero_dualComplex_empty

namespace Work.Serre

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Topology Topology.Homotopy unitInterval Simplicial

namespace RwTop

/-! ## Homology of the empty space -/

theorem isZero_ratH_of_isEmpty (X : Type) [TopologicalSpace X] [IsEmpty X] (m : ℕ) :
    IsZero (ratH (TopCat.of X) m) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  refine ShortComplex.exact_of_isZero_X₂ _ ?_
  have h : IsEmpty ((TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op ⦋m⦌)) := by
    refine ⟨fun x => ?_⟩
    have hx := (TopCat.toSSetObjEquivT (TopCat.of X) (Opposite.op ⦋m⦌)) x
    haveI : Nonempty (↑(stdSimplex ℝ (Fin ((Opposite.unop (Opposite.op ⦋m⦌)).len + 1)))) :=
      inferInstance
    exact isEmptyElim (hx (Classical.arbitrary _))
  haveI := h
  exact Work.Cohomology.isZero_coproduct_of_isEmpty
    (fun _ : ((TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op ⦋m⦌)) => ModuleCat.of ℚ ℚ)

/-! ## The inclusion of an attachment is a homology isomorphism below the cell dimension -/

theorem isIso_ratHomologyMap_attachIncl (m : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere m, Y)) (t : ℕ) (ht : t ≤ m) :
    IsIso (ratHomologyMap (Work.RatHurewicz.attachIncl m Y ι f) t) := by
  have hcomp : ∀ d, d ≤ m + 1 → Work.RatHurewicz.CompressRel
      (Work.RatHurewicz.attachCells m Y ι f)
      (Set.range (Work.RatHurewicz.attachIncl m Y ι f)) d :=
    Work.RatHurewicz.compressRel_attachCells_range m Y ι f
  have hiso : IsIso (ratHomologyMap
      (Work.RatHurewicz.setIncl (Set.range (Work.RatHurewicz.attachIncl m Y ι f))) t) :=
    isIso_ratHomologyMap_setIncl_of_compressRel hcomp t (by omega)
  let e := Work.RatHurewicz.rangeHomeo m Y ι f
  let eC : C(Y, ↥(Set.range (Work.RatHurewicz.attachIncl m Y ι f))) := ⟨⇑e, e.continuous⟩
  have hfact : (Work.RatHurewicz.setIncl
        (Set.range (Work.RatHurewicz.attachIncl m Y ι f))).comp eC
      = Work.RatHurewicz.attachIncl m Y ι f := by
    ext y
    rfl
  have hsplit : ratHomologyMap (Work.RatHurewicz.attachIncl m Y ι f) t
      = ratHomologyMap eC t ≫ ratHomologyMap (Work.RatHurewicz.setIncl
          (Set.range (Work.RatHurewicz.attachIncl m Y ι f))) t := by
    rw [← ratHomologyMap_comp eC
      (Work.RatHurewicz.setIncl (Set.range (Work.RatHurewicz.attachIncl m Y ι f))) t, hfact]
  rw [hsplit]
  have hE : IsIso (ratHomologyMap eC t) :=
    IsRatHomologyIso.of_homotopyEquiv e.toHomotopyEquiv t
  have := hiso
  have := hE
  infer_instance

/-! ## The top degree for a subspace inclusion -/

/-- **Range-Whitehead in the top degree, subspace form.**

If `A ⊆ W` meets every path component of `W` and the inclusion is a bijection on `π_q` at every
base point of `A` for `q ≤ n + 1`, then `H_{n+1}(A;ℚ) → H_{n+1}(W;ℚ)` is an isomorphism.

The proof kills `π_{n+2}` of the ambient space: `W' := KillCells (n+1) W` is `W` with an `(n+3)`-cell
attached along every map `S^{n+2} → W`, so `π_q(W) → π_q(W')` is an isomorphism for `q ≤ n + 1` and
`π_{n+2}(W') = 0`.  For `A' := killIncl '' A ⊆ W'` one gets, one degree beyond the range where the
inclusion of `A'` is a `π`-bijection, the vanishing of the relative groups of the pair `(W', A')` in
dimensions `≤ n + 2`, hence the compression property in dimensions `≤ n + 2`
(`Work.Serre.rwCompressRelKillCellsA`).  The relative cone construction then gives the isomorphism
for the killed pair, and it is transported back along the two homology isomorphisms
`H_*(A;ℚ) ≅ H_*(A';ℚ)` (a homeomorphism) and `H_*(W;ℚ) ≅ H_*(W';ℚ)`
(`Work.Serre.isIso_ratHomologyMap_attachIncl`). -/
theorem isIso_ratHomologyMap_setIncl_top (n : ℕ) {W : Type} [TopologicalSpace W] (A : Set W)
    (hconn0 : ∀ w : W, ∃ a : ↥A, Nonempty (Path w a))
    (hpi : ∀ q : ℕ, q ≤ n + 1 → ∀ a : ↥A,
      Function.Bijective (piMapN (RatHurewicz.setIncl A) q a)) :
    IsIso (ratHomologyMap (RatHurewicz.setIncl A) (n + 1)) := by
  classical
  let A' : Set (KillCells (n + 1) W) := {z | ∃ a : ↥A, killIncl (n + 1) W (a : W) = z}
  have hcomp : ∀ d, d ≤ n + 2 → RatHurewicz.CompressRel (KillCells (n + 1) W) A' d :=
    rwCompressRelKillCellsA n A hconn0 hpi
  have hiso : IsIso (ratHomologyMap (RatHurewicz.setIncl A') (n + 1)) :=
    isIso_ratHomologyMap_setIncl_of_compressRel hcomp (n + 1) (by omega)
  have hkill : IsIso (ratHomologyMap (killIncl (n + 1) W) (n + 1)) :=
    RwTop.isIso_ratHomologyMap_attachIncl (n + 1) W (KillIdx (n + 1) W) (fun g => g) (n + 1) le_rfl
  have hind : Topology.IsInducing (fun a : ↥A => killIncl (n + 1) W (a : W)) :=
    Topology.IsInducing.comp
      (RatHurewicz.isInducing_attachIncl (n + 1) W (KillIdx (n + 1) W) (fun g => g))
      Topology.IsInducing.subtypeVal
  have hinj : Function.Injective (fun a : ↥A => killIncl (n + 1) W (a : W)) :=
    fun _ _ h => Subtype.ext
      (RatHurewicz.AttachRange.attachIncl_injective (n + 1) W (KillIdx (n + 1) W)
        (fun g => g) h)
  let hf : Topology.IsEmbedding (fun a : ↥A => killIncl (n + 1) W (a : W)) :=
    Topology.IsEmbedding.mk hind hinj
  let e := hf.toHomeomorph
  let eC : C(↥A, ↥A') := ⟨⇑e, e.continuous⟩
  have hfact : (killIncl (n + 1) W).comp (RatHurewicz.setIncl A)
      = (RatHurewicz.setIncl A').comp eC := by
    ext a
    exact (Topology.IsEmbedding.toHomeomorph_apply_coe hf a).symm
  have heC : IsIso (ratHomologyMap eC (n + 1)) :=
    IsRatHomologyIso.of_homotopyEquiv e.toHomotopyEquiv (n + 1)
  have hbig : IsIso (ratHomologyMap ((killIncl (n + 1) W).comp
      (RatHurewicz.setIncl A)) (n + 1)) := by
    rw [hfact, ratHomologyMap_comp eC (RatHurewicz.setIncl A') (n + 1)]
    haveI := hiso
    haveI := heC
    infer_instance
  rw [ratHomologyMap_comp (RatHurewicz.setIncl A) (killIncl (n + 1) W) (n + 1)] at hbig
  haveI := hbig
  haveI := hkill
  exact IsIso.of_isIso_comp_right (ratHomologyMap (RatHurewicz.setIncl A) (n + 1))
    (ratHomologyMap (killIncl (n + 1) W) (n + 1))

end RwTop

/-! ## The main theorem: range-Whitehead in the top degree -/

/-- **Range-Whitehead in the top degree.**

If `i : A → W` is a bijection on `π_q` at every base point for `q ≤ n + 1` and every point of `W`
is joined by a path to a point of `i(A)`, then `H_{n+1}(A;ℚ) → H_{n+1}(W;ℚ)` is an isomorphism.

The proof replaces `i` by the inclusion of `A` into its mapping cylinder (`cylIncl i`, an
embedding, the retraction `cylRetract i` being a homotopy equivalence), and applies the subspace
form `Work.Serre.isIso_ratHomologyMap_setIncl_top` to the pair
`(cyl i, Set.range (cylIncl i))`:  every point of the cylinder is joined to the bottom copy
(`Work.Serre.cylJoinedIncl`), the relative homotopy groups of the pair vanish in degrees `≤ n`
(`Work.Serre.cylRelPi` transported to the range by
`Work.Serre.RangeOne.subsingleton_relPi_range_cylIncl`), and the inclusion is a `π_q`-bijection for
`q ≤ n + 1` because it is `cylIncl i` up to the homeomorphism of `A` with its image and
`π_q(cylIncl i) ≅ π_q(i)` (`Work.Serre.bijective_piMapN_cylIncl`; the degree `q = 0` is handled by
the compression property of the pair in dimensions `0` and `1`,
`Work.Serre.bijective_zmkMap_setIncl_of_compressRel`). -/
theorem rwMapTop (n : ℕ) {A W : Type} [TopologicalSpace A] [TopologicalSpace W] (i : C(A, W))
    (hconn0 : ∀ w : W, ∃ a : A, Nonempty (Path w (i a)))
    (hpi : ∀ (q : ℕ), q ≤ n + 1 → ∀ a : A,
      Function.Bijective (Work.Serre.piMapN i q a)) :
    CategoryTheory.IsIso (Work.Serre.ratHomologyMap i (n + 1)) := by
  classical
  by_cases hA : Nonempty A
  · haveI : Nonempty A := hA
    let f : C(A, cyl i) := cylIncl i
    let A' : Set (cyl i) := Set.range (f : A → cyl i)
    have hconn' : ∀ w : cyl i, ∃ a : ↥A', Nonempty (Path w (a : cyl i)) := by
      intro w
      obtain ⟨x, hx⟩ := cylJoinedIncl i (fun x => (hpi 0 (by omega) x).2) w
      exact ⟨⟨f x, x, rfl⟩, hx⟩
    have hrel : ∀ a : ↥A', ∀ k : ℕ, k ≤ n →
        Subsingleton (RatHurewicz.RelHomotopyGroup (RatHurewicz.setIncl A') a k) := by
      intro a k hk
      obtain ⟨x, hx⟩ := a.2
      have hEq : (⟨f x, x, rfl⟩ : ↥A') = a := Subtype.ext hx
      exact hEq ▸ RangeOne.subsingleton_relPi_range_cylIncl i x k
        ((cylRelPi i x n (fun m hm y => hpi m (by omega) y)).1 k (by omega))
    have hcomp : ∀ d, d ≤ n + 1 → RatHurewicz.CompressRel (cyl i) A' d :=
      RatHurewicz.compression_of_relPiVanishing n hconn' hrel
    have hpi' : ∀ q : ℕ, q ≤ n + 1 → ∀ a : ↥A',
        Function.Bijective (piMapN (RatHurewicz.setIncl A') q a) := by
      intro q hq a
      rcases Nat.eq_zero_or_pos q with hq0 | hqpos
      · subst hq0
        have hbijA : Function.Bijective (zmkMap (RatHurewicz.setIncl A')) :=
          bijective_zmkMap_setIncl_of_compressRel (hcomp 0 (by omega)) (hcomp 1 (by omega))
        have hfun : piMapN (RatHurewicz.setIncl A') 0 a
            = HomotopyGroup.map (N := Fin 0) (RatHurewicz.setIncl A') (x := a) := by
          funext t
          rfl
        rw [hfun]
        have hnat : ∀ t : HomotopyGroup (Fin 0) (↥A') a,
            HomotopyGroup.pi0EquivZerothHomotopy
              (HomotopyGroup.map (N := Fin 0) (RatHurewicz.setIncl A') (x := a) t)
            = zmkMap (RatHurewicz.setIncl A')
                (HomotopyGroup.pi0EquivZerothHomotopy t) :=
          fun t => pi0EquivZerothHomotopy_map _ _ t
        have hfun2 : HomotopyGroup.map (N := Fin 0) (RatHurewicz.setIncl A') (x := a)
            = fun t => (HomotopyGroup.pi0EquivZerothHomotopy
                  (x := RatHurewicz.setIncl A' a)).symm
                (zmkMap (RatHurewicz.setIncl A')
                  (HomotopyGroup.pi0EquivZerothHomotopy (x := a) t)) := by
          funext t
          rw [← hnat t]
          exact (Equiv.symm_apply_apply _ _).symm
        rw [hfun2]
        exact (Equiv.bijective _).comp (hbijA.comp (Equiv.bijective _))
      · obtain ⟨q', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
        let hC : C(A, ↥A') := ⟨⇑(RangeOne.cylRangeHomeo i), (RangeOne.cylRangeHomeo i).continuous⟩
        let hI : C(↥A', A) := ⟨⇑(RangeOne.cylRangeHomeo i).symm,
          (RangeOne.cylRangeHomeo i).symm.continuous⟩
        have hh1 : hI.comp hC = ContinuousMap.id A := by
          ext x
          simp [hC, hI]
        have hh2 : hC.comp hI = ContinuousMap.id ↥A' := by
          ext x
          simp [hC, hI]
        have hCeq : (RatHurewicz.setIncl A').comp hC = f := by
          ext x
          exact RangeOne.cylRangeHomeo_coe i x
        have hx : hC (hI a) = a := by
          show (RangeOne.cylRangeHomeo i) ((RangeOne.cylRangeHomeo i).symm a) = a
          exact Homeomorph.apply_symm_apply _ _
        rw [← hx]
        have hbijL : Function.Bijective
            (piMapN ((RatHurewicz.setIncl A').comp hC) (q' + 1) (hI a)) := by
          rw [hCeq]
          exact bijective_piMapN_cylIncl i (q' + 1) (by omega) (hI a) (hpi (q' + 1) hq (hI a))
        have hbijE : Function.Bijective (piMapN hC (q' + 1) (hI a)) :=
          bijective_πmap_of_comp_eq_id_gen hC hI hh1 hh2 q' (hI a)
        have hcomp_apply : piMapN ((RatHurewicz.setIncl A').comp hC) (q' + 1) (hI a)
            = (piMapN (RatHurewicz.setIncl A') (q' + 1) (hC (hI a)))
              ∘ (piMapN hC (q' + 1) (hI a)) := by
          funext t
          exact piMapN_comp hC (RatHurewicz.setIncl A') (q' + 1) (hI a) t
        have hbij : Function.Bijective ((piMapN (RatHurewicz.setIncl A') (q' + 1) (hC (hI a)))
            ∘ (piMapN hC (q' + 1) (hI a))) := by
          rw [← hcomp_apply]
          exact hbijL
        refine ⟨fun u v huv => ?_, fun y => ?_⟩
        · obtain ⟨u', rfl⟩ := hbijE.2 u
          obtain ⟨v', rfl⟩ := hbijE.2 v
          rw [hbij.1 huv]
        · obtain ⟨z, hz⟩ := hbij.2 y
          exact ⟨piMapN hC (q' + 1) (hI a) z, hz⟩
    have hsub : IsIso (ratHomologyMap (RatHurewicz.setIncl A') (n + 1)) :=
      RwTop.isIso_ratHomologyMap_setIncl_top n A' hconn' hpi'
    have hcylincl : IsIso (ratHomologyMap (cylIncl i) (n + 1)) := by
      let ecm : C(A, ↥A') := ⟨⇑(RangeOne.cylRangeHomeo i), (RangeOne.cylRangeHomeo i).continuous⟩
      have hfact : (RatHurewicz.setIncl A').comp ecm = cylIncl i := by
        ext x
        exact RangeOne.cylRangeHomeo_coe i x
      have hsplit : ratHomologyMap (cylIncl i) (n + 1)
          = ratHomologyMap ecm (n + 1) ≫ ratHomologyMap (RatHurewicz.setIncl A') (n + 1) := by
        rw [← ratHomologyMap_comp ecm (RatHurewicz.setIncl A') (n + 1), hfact]
      rw [hsplit]
      have hecm : IsIso (ratHomologyMap ecm (n + 1)) :=
        IsRatHomologyIso.of_homotopyEquiv (RangeOne.cylRangeHomeo i).toHomotopyEquiv (n + 1)
      haveI := hsub
      haveI := hecm
      infer_instance
    have hret : IsIso (ratHomologyMap (cylRetract i) (n + 1)) := by
      obtain ⟨E, hE⟩ := cylHomotopyEquivExplicit i
      have h1 : IsIso (ratHomologyMap E.toFun (n + 1)) :=
        IsRatHomologyIso.of_homotopyEquiv E (n + 1)
      rwa [hE] at h1
    have hfc : ratHomologyMap i (n + 1)
        = ratHomologyMap (cylIncl i) (n + 1) ≫ ratHomologyMap (cylRetract i) (n + 1) := by
      rw [← ratHomologyMap_comp (cylIncl i) (cylRetract i) (n + 1), cylRetract_cylIncl i]
    rw [hfc]
    haveI := hcylincl
    haveI := hret
    infer_instance
  · haveI : IsEmpty A := not_nonempty_iff.mp hA
    haveI : IsEmpty W := ⟨fun w => by obtain ⟨a, -⟩ := hconn0 w; exact hA ⟨a⟩⟩
    exact IsZero.isIso (RwTop.isZero_ratH_of_isEmpty A (n + 1)) (RwTop.isZero_ratH_of_isEmpty W (n + 1)) _


end

end Work.Serre
