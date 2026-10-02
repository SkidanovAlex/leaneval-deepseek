import Mathlib
import Submission.Work.RatHurewicz.LensSpace.EM
import Submission.Work.Stems.fin_prod_ratH_vanishing
import Submission.Work.Serre.serreE0Range
import Submission.Work.RatHurewicz.coverRangeTransfer
import Submission.Work.RatHurewicz.isEMSpaceUpTo_pi_fin
import Submission.Work.RatHurewicz.SimplyConnectedBridge

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# A rationally acyclic range model of `K(A,1)` for a finite abelian `A`

The target: for every finite abelian group `A` and every `N` there is a space `L` with a base point
`l₀` such that `L` is a model of `K(A,1)` up to degree `N` (`Work.Serre.IsEMSpaceUpTo A 1 _ N L l₀`)
and `H_t(L;ℚ) = 0` for `0 < t ≤ N`.

## The construction

`A` is a finite product of finite cyclic groups (the structure theorem,
`AddCommGroup.equiv_directSum_zmod_of_finite'`): `A ≃+ ∏_{i : ι} ZMod (n i)`.  Let

* `E := ∏_{i : ι} S^{2N+3}` — a product of spheres (each `S^{2N+3}` is `(2N+2)`-connected, so `E`
  is `(2N+2)`-connected and hence rationally acyclic in degrees `≤ 2N+2` by the Hurewicz theorem in
  range `Work.Serre.serreE0Range`), carrying the free action
* `G := ∏_{i : ι} μ_{n i}` by scalar multiplication of the `n_i`-th roots of unity on the `i`-th
  factor (the lens-space action `Work.RatHurewicz.lensAct`), with quotient
* `L := E/G`.

The quotient map `E → L` is a covering with `|G| = ∏ n i = |A|` sheets
(`IsQuotientCoveringMap`, Mathlib), so the transfer for a finite covering
(`Work.RatHurewicz.isZero_ratH_of_finite_covering_range`) gives `H_t(L;ℚ) = 0` for
`0 < t ≤ 2N+2 ⊇ {1,…,N}`.  Moreover `π_1(L) ≅ G` (the covering is simply connected:
Mathlib's `IsQuotientCoveringMap.fundamentalGroupEquiv`), and `π_i(L) = 0` for `2 ≤ i ≤ 2N+2` (the
long exact sequence of the covering), so `L` is a range model of `K(A,1)` through degree `N`.
-/

namespace Work.RatHurewicz

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-! ## The structure theorem for finite abelian groups, in the shape used below -/

/-- Every finite abelian group is a finite product of finite cyclic groups. -/
theorem finiteAbelianProdZmod (A : Type) [AddCommGroup A] [Fintype A] :
    ∃ (ι : Type) (_ : Fintype ι) (n : ι → ℕ),
      (∀ i, n i ≠ 0) ∧ Nonempty (A ≃+ ((i : ι) → ZMod (n i))) := by
  obtain ⟨ι, hι, n, hn, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' A
  letI := hι
  exact ⟨ι, hι, n, fun i => by have := hn i; omega,
    ⟨e.trans (DirectSum.addEquivProd fun i : ι => ZMod (n i))⟩⟩

/-! ## The model space -/

/-- The total space: a product of spheres `S^{2N+3}`. -/
abbrev famTotal (ι : Type) (N : ℕ) : Type := (i : ι) → lensTotal N

/-- The group acting on it, `∏ᵢ μ_{nᵢ}`. -/
abbrev famGroup (ι : Type) (n : ι → ℕ) : Type := (i : ι) → Multiplicative (ZMod (n i))

/-- The quotient `L = E/G`. -/
abbrev famSpace (ι : Type) [Fintype ι] (n : ι → ℕ) (N : ℕ) [∀ i, NeZero (n i)] : Type :=
  Quotient (MulAction.orbitRel (famGroup ι n) (famTotal ι N))

/-- A base point of `S^{2N+3}`. -/
def lensBase (N : ℕ) : lensTotal N :=
  ⟨EuclideanSpace.single 0 (1 : ℝ), by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, EuclideanSpace.norm_single]
    norm_num⟩

/-- A base point of `E`. -/
def famBase (ι : Type) (N : ℕ) : famTotal ι N := fun _ => lensBase N

/-- The quotient map, as a continuous map. -/
def famProjCM (ι : Type) [Fintype ι] (n : ι → ℕ) (N : ℕ) [∀ i, NeZero (n i)] :
    C(famTotal ι N, famSpace ι n N) :=
  ⟨Quotient.mk _, continuous_quot_mk⟩

variable {ι : Type} [Fintype ι] {n : ι → ℕ} {N : ℕ} [∀ i, NeZero (n i)]

instance famFiniteGroup : Finite (famGroup ι n) := by classical exact Finite.of_fintype _

instance famContinuousConstSMul : ContinuousConstSMul (famGroup ι n) (famTotal ι N) where
  continuous_const_smul g := continuous_pi fun i =>
    ((continuous_const_smul (g i)).comp (continuous_apply i))

instance famIsCancelSMul : IsCancelSMul (famGroup ι n) (famTotal ι N) where
  left_cancel' g x y h := by
    funext i
    exact IsCancelSMul.left_cancel (g i) (x i) (y i) (congrFun h i)
  right_cancel' g g' x h := by
    funext i
    exact IsCancelSMul.right_cancel (g i) (g' i) (x i) (congrFun h i)

/-- The quotient map is a quotient covering map with group `G`. -/
theorem famIsQuotientCoveringMap :
    IsQuotientCoveringMap (⇑(famProjCM ι n N)) (famGroup ι n) :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

/-- In particular it is a covering map. -/
theorem famIsCoveringMap : IsCoveringMap (⇑(famProjCM ι n N)) :=
  IsQuotientCoveringMap.isCoveringMap _ _ (famIsQuotientCoveringMap (N := N))

/-! ## Connectivity of the total space

`S^{2N+3}` is `(2N+2)`-connected, hence so is the product `E`. -/

theorem lensConn : Work.Serre.Conn (lensTotal N) (lensBase N) (2 * N + 3) :=
  fun i hi => Work.Stems.sphereConnectivity (2 * N + 3) i hi (lensBase N)

/-- **A product of `(K-1)`-connected spheres is `(K-1)`-connected.** -/
theorem conn_pi_fin {S : Type} [TopologicalSpace S] (s₀ : S) (K : ℕ)
    (h : Work.Serre.Conn S s₀ K) : Work.Serre.Conn (ι → S) (fun _ => s₀) K := by
  classical
  have hfin : Work.Serre.Conn (Fin (Fintype.card ι) → S) (fun _ => s₀) K :=
    Work.Stems.conn_fin_prod K (Fintype.card ι) s₀ h
  intro i hi
  have hm : (Homeomorph.piCongrLeft (Y := fun _ : ι => S)
      (Fintype.equivFin ι).symm).symm (fun _ => s₀) = (fun _ => s₀) := by
    rw [Homeomorph.piCongrLeft_symm_apply]
  exact Work.Stems.subsingleton_homotopyGroup_fin_of_homeomorph
    (Homeomorph.piCongrLeft (Y := fun _ : ι => S) (Fintype.equivFin ι).symm).symm hm i
    (hfin i hi)

/-- **The total space `E` is `(2N+2)`-connected.** -/
theorem famConn : Work.Serre.Conn (famTotal ι N) (famBase ι N) (2 * N + 3) :=
  conn_pi_fin (ι := ι) (lensBase N) (2 * N + 3) lensConn

/-- The total space is simply connected (needed for the computation of `π₁` of the quotient). -/
theorem famSimplyConnected : SimplyConnectedSpace (famTotal ι N) :=
  simplyConnectedSpace_of_subsingleton (famBase ι N)
    (famConn (ι := ι) (N := N) 0 (by omega))
    (famConn (ι := ι) (N := N) 1 (by omega))

/-! ## The homotopy groups of `L` -/

/-- **`π_i(L) = 0` for `2 ≤ i ≤ 2N+2`**, by the long exact homotopy sequence of the covering. -/
theorem famSubsingletonPi {i : ℕ} (hi : 2 ≤ i) (hiN : i ≤ 2 * N + 2) :
    Subsingleton (HomotopyGroup (Fin i) (famSpace ι n N)
      (famProjCM ι n N (famBase ι N))) := by
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 2 := ⟨i - 2, by omega⟩
  haveI hdisc : DiscreteTopology
      (Work.StemsB.fibre (famProjCM ι n N) (famProjCM ι n N (famBase ι N))) :=
    (famIsCoveringMap (ι := ι) (n := n) (N := N) _).discreteTopology_fiber
  refine subsingleton_homotopyGroup_base_of_isCoveringMap (famProjCM ι n N)
    (famIsCoveringMap (ι := ι) (n := n) (N := N)) (famBase ι N) m ?_ ?_
  · exact famConn (ι := ι) (N := N) (m + 2) (by omega)
  · exact Work.Serre.subsingleton_homotopyGroup_of_discrete (m + 1) (by omega) _ _

/-- **`π₁(L) ≅ G`**: the covering is simply connected, so the fundamental group of the quotient is
the group of the covering. -/
theorem famPiOne :
    Nonempty (HomotopyGroup (Fin 1) (famSpace ι n N) (famProjCM ι n N (famBase ι N)) ≃*
      Multiplicative ((i : ι) → ZMod (n i))) := by
  haveI := famSimplyConnected (ι := ι) (N := N)
  refine ⟨(HomotopyGroup.pi1MulEquivFundamentalGroup).trans
    (((famIsQuotientCoveringMap (ι := ι) (n := n) (N := N)).fundamentalGroupEquiv
        ⟨famBase ι N, rfl⟩).trans ?_)⟩
  exact (mulOppositeCommMulEquiv (famGroup ι n)).trans
    (MulEquiv.piMultiplicative fun i : ι => ZMod (n i)).symm

/-- `L` is path connected. -/
theorem famPathConnected : PathConnectedSpace (famSpace ι n N) := by
  have h : IsPathConnected (Set.univ : Set (famSpace ι n N)) := by
    have h1 : IsPathConnected (Set.univ : Set (famTotal ι N)) := by
      haveI := famSimplyConnected (ι := ι) (N := N)
      rw [← pathConnectedSpace_iff_univ]; infer_instance
    have h2 := h1.image (famProjCM ι n N).continuous
    rwa [Set.image_univ, Set.range_eq_univ.mpr
      (famIsQuotientCoveringMap (ι := ι) (n := n) (N := N)).surjective] at h2
  rw [pathConnectedSpace_iff_univ]; exact h

/-- `π₀(L) = 0`. -/
theorem famSubsingletonPiZero (l₀ : famSpace ι n N) :
    Subsingleton (HomotopyGroup (Fin 0) (famSpace ι n N) l₀) := by
  haveI := famPathConnected (ι := ι) (n := n) (N := N)
  have hZ : Subsingleton (ZerothHomotopy (famSpace ι n N)) :=
    (pathConnectedSpace_iff_zerothHomotopy.mp inferInstance).2
  exact ⟨fun a b => (HomotopyGroup.pi0EquivZerothHomotopy
    (X := famSpace ι n N) (x := l₀)).injective (Subsingleton.elim _ _)⟩

/-! ## The fibre cardinality and the transfer -/

/-- Every fibre of the quotient map has `∏ᵢ nᵢ` elements (`= |A|`). -/
theorem famCardFibre (x : famSpace ι n N) :
    Nat.card ↥((⇑(famProjCM ι n N)) ⁻¹' {x}) = ∏ i, n i := by
  classical
  obtain ⟨y, rfl⟩ := (famIsQuotientCoveringMap (ι := ι) (n := n) (N := N)).surjective x
  refine (Nat.card_congr ((famIsQuotientCoveringMap (ι := ι) (n := n) (N := N)).fiberEquivGroup
    ⟨y, rfl⟩)).trans ?_
  rw [Nat.card_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  show Nat.card (Multiplicative (ZMod (n i))) = n i
  rw [Nat.card_congr (Multiplicative.toAdd), Nat.card_zmod]

/-- **`H_t(L;ℚ) = 0` for `0 < t ≤ 2N+2`**, by the transfer of the finite covering `E → L`. -/
theorem famIsZeroRatH :
    ∀ t : ℕ, 0 < t → t ≤ 2 * N + 2 →
      IsZero (Work.Serre.ratH (TopCat.of (famSpace ι n N)) t) := by
  refine isZero_ratH_of_finite_covering_range (famProjCM ι n N)
    (famIsCoveringMap (ι := ι) (n := n) (N := N))
    (∏ i, n i) (Finset.prod_pos fun i _ => Nat.pos_of_ne_zero (NeZero.ne (n i)))
    (fun x => famCardFibre (ι := ι) (n := n) (N := N) x) (2 * N + 2) ?_
  intro t ht htM
  have hc : ∀ i : ℕ, i ≤ 2 * N + 2 →
      Subsingleton (HomotopyGroup (Fin i) (famTotal ι N) (famBase ι N)) :=
    fun i hi => famConn (ι := ι) (N := N) i (by omega)
  exact (Work.Serre.serreE0Range (famTotal ι N) (famBase ι N) (2 * N + 2) hc) t ht (by omega)

/-! ## The range model -/

/-- `L` is a range model of `K(∏ᵢ ZMod (nᵢ), 1)` through degree `N`. -/
theorem famIsEMSpaceUpTo :
    Work.Serre.IsEMSpaceUpTo ((i : ι) → ZMod (n i)) 1 (by norm_num : 0 < 1) N
      (famSpace ι n N) (famProjCM ι n N (famBase ι N)) := by
  constructor
  · obtain ⟨iso⟩ := famPiOne (ι := ι) (n := n) (N := N)
    exact ⟨iso⟩
  · intro i hi hc
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      exact famSubsingletonPiZero (famProjCM ι n N (famBase ι N))
    · exact famSubsingletonPi (ι := ι) (n := n) (N := N) (by omega) (by omega)

/-! ## The target -/

theorem exists_finiteAbelian_rangeModel (A : Type) [AddCommGroup A] [Fintype A] (N : ℕ) :
    ∃ (L : Type) (_ : TopologicalSpace L) (l₀ : L),
      Work.Serre.IsEMSpaceUpTo A 1 (by norm_num : 0 < 1) N L l₀ ∧
      (∀ t : ℕ, 0 < t → t ≤ N →
        CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of L) t)) := by
  obtain ⟨ι, hι, n, hn, ⟨e⟩⟩ := finiteAbelianProdZmod A
  letI := hι
  haveI hne : ∀ i, NeZero (n i) := fun i => ⟨hn i⟩
  refine ⟨famSpace ι n N, inferInstance, famProjCM ι n N (famBase ι N), ?_, ?_⟩
  · exact isEMSpaceUpTo_of_addEquiv (k := 1) (N := N) (by norm_num)
      (famProjCM ι n N (famBase ι N))
      (famIsEMSpaceUpTo (ι := ι) (n := n) (N := N)) e.symm
  · intro t ht htN
    exact famIsZeroRatH (ι := ι) (n := n) (N := N) t ht (by omega)

end

end Work.RatHurewicz
