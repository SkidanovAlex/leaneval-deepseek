import Mathlib
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.cuspZ2Defs
import Submission.Work.Mostow.cuspThinRegionDefs
import Submission.Work.Mostow.cuspParDispDefs
import Submission.Work.Mostow.cuspThinRegion_eq_parDisp
import Submission.Work.Mostow.paraUniqueFixed
import Submission.Work.Mostow.margulisCusp
import Submission.Work.Mostow.hptOf_level
import Submission.Work.Mostow.hptOf_yc
import Submission.Work.Mostow.levYcFormula
import Submission.Work.Mostow.geomFiniteMultThick
import Submission.Work.Mostow.cuspShimizuHoroballAux
import Submission.Work.Mostow.cuspCocompactAtLevel
import Submission.Work.Mostow.cuspCocompactAllLevels
import Submission.Work.Mostow.cuspCocompactDefs
import Submission.Work.Mostow.frontierShortBoundCusp
import Submission.Work.Mostow.frontierCocompactOfLattice
import Submission.Work.Mostow.hptOfLevelYc
import Submission.Work.Mostow.cuspHoroballEmbedding
import Submission.Work.Mostow.flatEllipticGap
import Submission.Work.Mostow.stabFlatDefs
import Submission.Work.Mostow.StabLift
import Submission.Work.Mostow.stabFlatActionCanon

/-!
# A flat (horospherical) translation in the stabiliser of a parabolic fixed point

For a lattice `Γ ≤ PO(n,1)` (`n ≥ 2`) with a parabolic fixed point `ξ` whose stabiliser we know
preserves the horospherical levels (`hvan`), there is `δ ∈ Γ` fixing `ξ` and acting on the
horospheres of `ξ` as a flat translation `y ↦ y + v` with `v ≠ 0`, `v ⊥ ξ`.

The proof goes through the workspace's Bieberbach-based flat-translation machine
(`Work.Mostow.csha_flatTransOfCocompact`): it is enough to know that `Γ_ξ` acts *cocompactly* on
the level-one horosphere of `ξ`.  That is obtained from

* the Margulis thin region `cuspThinRegion Γ ξ ε`, whose translates at distinct cusps are disjoint
  (from the Margulis lemma, `Work.Mostow.margulisCusp`); and
* the "thin horoball" fact `∃ t, horoball ξ t ⊆ cuspThinRegion Γ ξ ε`,

which together say that a deep horoball at `ξ` is precisely invariant (Shimizu's lemma); the
packing argument `Work.Mostow.cuspCocompactAtLevel` plus the horocyclic flow
(`Work.Mostow.cuspCocompactAllLevels`) then give cocompactness at level one.

## Case `n = 2`

Handled directly by `Work.Mostow.flatTrans_of_lattice_two` (which is axiom-clean): the flat linear
part of the parabolic `q ∈ Γ_ξ` given by `hξ` is an element of `O(1) = {±1}`, and `-1` is excluded
because then the flat action has a fixed point, making `q` elliptic rather than parabolic.

## Case `n ≥ 3`

Here `∃ t, horoball ξ t ⊆ cuspThinRegion Γ ξ ε` is proved in `cuspThinRegion_horoball_of_gap`
from the elliptic gap `θ > 0` of the cusp stabiliser, using the workspace's axiom-clean frontier
machinery `Work.Mostow.frontierShortBoundCusp` and `Work.Mostow.frontierCocompactOfLattice`: the
frontier points whose flat coordinates are the thresholds `cEps ε / parDisp Γ ξ y` are
`Γ_ξ`-cocompact, so the level of a frontier point is bounded below by `lev ξ` on a fixed compact
set, which bounds `parDisp Γ ξ` above.

The elliptic gap is `Work.Mostow.flatEllipticGap` (proved via the Zassenhaus argument: the
`θ₀`-small elliptics of `Γ_ξ` generate a finitely generated nilpotent torsion group, hence a finite
group with a common fixed point, and discreteness bounds those).
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity
open scoped Pointwise

noncomputable section

variable {n : ℕ}

/-! ## Basic bookkeeping -/

/-- An element of `PO n 1` fixing `ξ` with vanishing Busemann cocycle at `ξ` preserves every
horosphere of `ξ`. -/
lemma lev_smul_of_bCocy_zero_of_bd (hA : POActionProp n) (hI : HypIsometryProp n)
    {ξ : E n} (hξ : ξ ∈ Sph n) {δ : PO n 1} (hbd : bd δ ξ = ξ) (hc : bCocy δ ξ = 0) :
    ∀ u : E n, lev ξ (δ • u) = lev ξ u := by
  have hvd : HypIsoData n := HypIsoData.ofProp hI
  have hpb : POBasic n := POBasic.ofProp hA
  intro u
  rw [lev_smul_self hvd hpb ξ hξ δ u hbd]
  have h0 : lev ξ (δ • (0 : E n)) = 1 := by
    rw [lev_eq_exp hξ]
    have hb : busemann ξ (δ • (0 : E n)) = bCocy δ ξ := by rw [bCocy, hbd]
    rw [hb, hc, Real.exp_zero]
  rw [h0, mul_one]

/-- The Margulis region at `ξ` is equivariant: translating it by `γ ∈ Γ` moves the cusp to
`bd γ ξ`. -/
lemma smul_cuspThinRegion (hA : POActionProp n) (hI : HypIsometryProp n)
    (Γ : Subgroup (PO n 1)) (γ : Γ) (ξ : E n) (hξ : ξ ∈ Sph n) (ε : ℝ) :
    (γ : PO n 1) • (cuspThinRegion Γ ξ ε) = cuspThinRegion Γ (bd (γ : PO n 1) ξ) ε := by
  have hpb : POBasic n := POBasic.ofProp hA
  have hvd : HypIsoData n := HypIsoData.ofProp hI
  ext w
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨q, hq, hqfix, hd⟩ := hu
    refine ⟨⟨(γ : PO n 1) * (q : PO n 1) * (γ : PO n 1)⁻¹,
      mul_mem (mul_mem γ.2 q.2) (inv_mem γ.2)⟩, ?_, ?_, ?_⟩
    · exact isParabolic_conj hA hI (γ : PO n 1) (q : PO n 1) hq
    · show bd ((γ : PO n 1) * (q : PO n 1) * (γ : PO n 1)⁻¹) (bd (γ : PO n 1) ξ) = bd (γ : PO n 1) ξ
      have hξγ : bd (γ : PO n 1) ξ ∈ Sph n := hpb.bd_mem _ _ hξ
      have h1 : bd (γ : PO n 1)⁻¹ (bd (γ : PO n 1) ξ) = ξ := by
        rw [← hpb.bd_mul (γ : PO n 1)⁻¹ (γ : PO n 1) ξ hξ, inv_mul_cancel, hpb.bd_one ξ hξ]
      rw [hpb.bd_mul ((γ : PO n 1) * (q : PO n 1)) ((γ : PO n 1)⁻¹) (bd (γ : PO n 1) ξ) hξγ,
        h1, hpb.bd_mul (γ : PO n 1) (q : PO n 1) ξ hξ, hqfix]
    · show hdist ((γ : PO n 1) • u)
        (((γ : PO n 1) * (q : PO n 1) * (γ : PO n 1)⁻¹) • ((γ : PO n 1) • u)) < ε
      have h2 : (γ : PO n 1)⁻¹ • ((γ : PO n 1) • u) = u := by
        rw [← hpb.mul_smul, inv_mul_cancel, hpb.one_smul]
      rw [hpb.mul_smul, hpb.mul_smul, h2,
        hvd.isom_smul (γ : PO n 1) u ((q : PO n 1) • u)]
      exact hd
  · rintro ⟨p, hp, hpfix, hd⟩
    refine ⟨(γ : PO n 1)⁻¹ • w, ?_, ?_⟩
    · refine ⟨⟨(γ : PO n 1)⁻¹ * (p : PO n 1) * (γ : PO n 1),
        mul_mem (mul_mem (inv_mem γ.2) p.2) γ.2⟩, ?_, ?_, ?_⟩
      · simpa only [inv_inv] using isParabolic_conj hA hI (γ : PO n 1)⁻¹ (p : PO n 1) hp
      · show bd ((γ : PO n 1)⁻¹ * (p : PO n 1) * (γ : PO n 1)) ξ = ξ
        have hξγ : bd (γ : PO n 1) ξ ∈ Sph n := hpb.bd_mem _ _ hξ
        rw [hpb.bd_mul ((γ : PO n 1)⁻¹ * (p : PO n 1)) (γ : PO n 1) ξ hξ,
          hpb.bd_mul ((γ : PO n 1)⁻¹) (p : PO n 1) (bd (γ : PO n 1) ξ) hξγ]
        rw [hpfix]
        rw [← hpb.bd_mul (γ : PO n 1)⁻¹ (γ : PO n 1) ξ hξ, inv_mul_cancel, hpb.bd_one ξ hξ]
      · show hdist ((γ : PO n 1)⁻¹ • w)
          (((γ : PO n 1)⁻¹ * (p : PO n 1) * (γ : PO n 1)) • ((γ : PO n 1)⁻¹ • w)) < ε
        have h2 : (γ : PO n 1) • ((γ : PO n 1)⁻¹ • w) = w := by
          rw [← hpb.mul_smul, mul_inv_cancel, hpb.one_smul]
        have h3 : ((γ : PO n 1)⁻¹ * (p : PO n 1) * (γ : PO n 1)) • ((γ : PO n 1)⁻¹ • w)
            = (γ : PO n 1)⁻¹ • ((p : PO n 1) • w) := by
          rw [hpb.mul_smul, hpb.mul_smul, h2]
        rw [h3, hvd.isom_smul (γ : PO n 1)⁻¹ w ((p : PO n 1) • w)]
        exact hd
    · show (γ : PO n 1) • ((γ : PO n 1)⁻¹ • w) = w
      rw [← hpb.mul_smul, mul_inv_cancel, hpb.one_smul]

/-- The Margulis regions at two distinct parabolic fixed points are disjoint, for `ε` below a
Margulis threshold.  (Margulis: an element short at a point of the region of `ξ` and of the region
of `η` must fix both, hence `ξ = η`.) -/
theorem cuspThinRegion_separation_lattice (n : ℕ) (hn : 2 ≤ n)
    (hA : Submission.Mostow.POActionProp n) (hI : Submission.Mostow.HypIsometryProp n)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1))
    (hdisc : IsDiscrete (SetLike.coe Γ)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ ξ ∈ parFixed Γ, ∀ η ∈ parFixed Γ,
      ξ ≠ η → Disjoint (cuspThinRegion Γ ξ ε) (cuspThinRegion Γ η ε) := by
  obtain ⟨εM, hεMpos, hεM⟩ := margulisCusp n hn hA hI 1
  refine ⟨min εM 1, lt_min hεMpos one_pos, ?_⟩
  intro ε hε hεle ξ hξ η hη hne
  rw [Set.disjoint_left]
  intro u hu hu'
  obtain ⟨q, hq, hqfix, hqu⟩ := hu
  obtain ⟨p, hp, hpfix, hpu⟩ := hu'
  have hqu' : hdist u ((q : PO n 1) • u) < εM :=
    lt_of_lt_of_le hqu (le_trans hεle (min_le_left _ _))
  have hpu' : hdist u ((p : PO n 1) • u) ≤ 1 :=
    le_of_lt (lt_of_lt_of_le hpu (le_trans hεle (min_le_right _ _)))
  have hfix : bd (p : PO n 1) ξ = ξ :=
    hεM Γ hdisc u ξ q p hq hξ.1 hqfix hqu' hpu'
  exact hne (paraUniqueFixed (POBasic.ofProp hA) (HypIsoData.ofProp hI) hp hξ.1 hfix hη.1 hpfix).symm

/-- **Shimizu's lemma (horoball form).**  If a horoball at `ξ` is contained in the Margulis
region of `ξ`, then it is precisely invariant modulo `Γ`. -/
lemma horoball_embedded_of_subset (n : ℕ) (hn : 2 ≤ n)
    (hA : Submission.Mostow.POActionProp n) (hI : Submission.Mostow.HypIsometryProp n)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1))
    {ξ : E n} (hξ : ξ ∈ parFixed Γ) {ε : ℝ} (hε : 0 < ε)
    (hsep : ∀ ξ' ∈ parFixed Γ, ∀ η ∈ parFixed Γ, ξ' ≠ η →
      Disjoint (cuspThinRegion Γ ξ' ε) (cuspThinRegion Γ η ε))
    {t : ℝ} (hthin : horoball ξ t ⊆ cuspThinRegion Γ ξ ε) :
    ∀ γ : Γ, bd (γ : PO n 1) ξ ≠ ξ →
      Disjoint (horoball ξ t)
        (horoball (bd (γ : PO n 1) ξ) (t + bCocy (γ : PO n 1) ξ)) := by
  have hpb : POBasic n := POBasic.ofProp hA
  have hvd : HypIsoData n := HypIsoData.ofProp hI
  have hξS : ξ ∈ Sph n := hξ.1
  intro γ hγ
  rw [Set.disjoint_left]
  intro u hu1 hu2
  -- `u ∈ horoball ξ t` and `γ u ∈ horoball (bd γ ξ) (t + bCocy γ ξ)`; by the Busemann cocycle
  -- the second says exactly `γ⁻¹ u ∈ horoball ξ t`.
  have hbus : busemann (bd (γ : PO n 1) ξ) u
      = busemann ξ ((γ : PO n 1)⁻¹ • u) + bCocy (γ : PO n 1) ξ := by
    have h := hvd.busemann_cocycle (γ : PO n 1) ξ ((γ : PO n 1)⁻¹ • u) hξS
    have h1 : (γ : PO n 1) • ((γ : PO n 1)⁻¹ • u) = u := by
      rw [← hpb.mul_smul, mul_inv_cancel, hpb.one_smul]
    rw [h1] at h
    exact h
  have hu2' : (γ : PO n 1)⁻¹ • u ∈ horoball ξ t := by
    simp only [horoball, Set.mem_ofPred_eq] at hu1 hu2 ⊢
    rw [hbus] at hu2
    linarith
  have h1 : u ∈ cuspThinRegion Γ ξ ε := hthin hu1
  have h2 : (γ : PO n 1)⁻¹ • u ∈ cuspThinRegion Γ ξ ε := hthin hu2'
  have h3 : (γ : PO n 1)⁻¹ • u
      ∈ cuspThinRegion Γ (bd (γ : PO n 1)⁻¹ ξ) ε := by
    have h := smul_cuspThinRegion hA hI Γ (γ⁻¹) ξ hξS ε
    rw [show ((γ⁻¹ : Γ) : PO n 1) = (γ : PO n 1)⁻¹ from rfl] at h
    rw [← h]
    exact ⟨u, h1, rfl⟩
  have hmem : bd (γ : PO n 1)⁻¹ ξ ∈ parFixed Γ :=
    parFixed_invariant hA hI Γ γ⁻¹ hξ
  have hne : ξ ≠ bd (γ : PO n 1)⁻¹ ξ := by
    intro h
    apply hγ
    have h2 : bd (γ : PO n 1) (bd (γ : PO n 1)⁻¹ ξ) = bd (γ : PO n 1) ξ :=
      congrArg (bd (γ : PO n 1)) h.symm
    rw [← h2, ← hpb.bd_mul (γ : PO n 1) ((γ : PO n 1)⁻¹) ξ hξS, mul_inv_cancel]
    exact hpb.bd_one ξ hξS
  exact Set.disjoint_left.mp (hsep ξ hξ (bd (γ : PO n 1)⁻¹ ξ) hmem hne) h2 h3

/-- Cocompactness of the stabiliser of `ξ` on the level-one horosphere, from the "thin horoball"
fact at `ξ`. -/
theorem cocompact_level_one_of_thinHoroball (n : ℕ) (hn : 2 ≤ n)
    (hA : Submission.Mostow.POActionProp n) (hI : Submission.Mostow.HypIsometryProp n)
    (hBb : ∀ m, Submission.Mostow.BieberbachProp m)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)) (hΓ : Submission.Mostow.HypLattice Γ)
    (hvan : ∀ (γ : Γ) ξ, ξ ∈ Work.Mostow.parFixed Γ →
      Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      Work.Mostow.bCocy (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = 0)
    (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Work.Mostow.parFixed Γ)
    (hthin : ∀ ε : ℝ, 0 < ε → ∃ t : ℝ,
      Submission.Mostow.horoball ξ t ⊆ Work.Mostow.cuspThinRegion Γ ξ ε) :
    ∃ K : Set (Submission.Mostow.E n), IsCompact K ∧ ∀ u : Submission.Mostow.E n,
      Work.Mostow.lev ξ u = 1 → ∃ γ : Γ,
        Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ ∧
        (γ : LeanEval.Geometry.MostowRigidity.PO n 1) • u ∈ K := by
  have hξS : ξ ∈ Submission.Mostow.Sph n := hξ.1
  obtain ⟨ε₀, hε₀pos, hsep⟩ :=
    cuspThinRegion_separation_lattice n hn hA hI Γ hΓ.1
  have hε : 0 < ε₀ / 2 := by linarith
  have hεle : ε₀ / 2 ≤ ε₀ := by linarith
  obtain ⟨t, hthin'⟩ := hthin (ε₀ / 2) hε
  have hsep' : ∀ ξ' ∈ Work.Mostow.parFixed Γ, ∀ η ∈ Work.Mostow.parFixed Γ, ξ' ≠ η →
      Disjoint (Work.Mostow.cuspThinRegion Γ ξ' (ε₀ / 2))
        (Work.Mostow.cuspThinRegion Γ η (ε₀ / 2)) :=
    fun ξ' hξ' η hη hne => hsep (ε₀ / 2) hε hεle ξ' hξ' η hη hne
  have hemb := horoball_embedded_of_subset n hn hA hI Γ hξ hε hsep' hthin'
  have hstab : ∀ (γ : Γ), Submission.Mostow.bd
      (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      Work.Mostow.bCocy (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = 0 :=
    fun γ hγ => hvan γ ξ hξ hγ
  obtain ⟨K, hKc, hK⟩ :=
    cuspCocompactAtLevel n hn hA hI hBb Γ hΓ ξ hξ hstab t hemb
  have hC : Work.Mostow.CuspCocompact Γ ξ :=
    cuspCocompactAllLevels n hA hI Γ ξ hξS hstab t ⟨K, hKc, hK⟩
  obtain ⟨K', hK'c, hK'⟩ := hC 0
  refine ⟨K', hK'c, fun u hu => ?_⟩
  have hbu : Submission.Mostow.busemann ξ u = 0 := by
    have h := Work.Mostow.lev_eq_exp hξS u
    rw [hu] at h
    have h2 : Real.exp (Submission.Mostow.busemann ξ u) = Real.exp 0 := by
      rw [← h, Real.exp_zero]
    exact Real.exp_injective h2
  exact hK' u hbu

/-- **The crux, conditional on the elliptic gap.**  For `n ≥ 3`, the elliptic gap of the cusp
stabiliser (`hgap`) gives that every Margulis region at `ξ` contains a horoball at `ξ`. -/
theorem cuspThinRegion_horoball_of_gap (n : ℕ) (hn : 3 ≤ n)
    (hA : Submission.Mostow.POActionProp n) (hI : Submission.Mostow.HypIsometryProp n)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)) (hΓ : Submission.Mostow.HypLattice Γ)
    (hvan : ∀ (γ : Γ) ξ, ξ ∈ Work.Mostow.parFixed Γ →
      Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      Work.Mostow.bCocy (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = 0)
    (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Work.Mostow.parFixed Γ)
    (hgap : ∃ θ : ℝ, 0 < θ ∧ ∀ (γ : Γ) (A : Submission.Mostow.E n →ₗ[ℝ] Submission.Mostow.E n)
      (v : Submission.Mostow.E n),
      (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ≠ 1 →
      Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      (∃ p : Submission.Mostow.E n, (γ : LeanEval.Geometry.MostowRigidity.PO n 1) • p = p) →
      (∀ y : Submission.Mostow.E n, inner ℝ y ξ = 0 → inner ℝ (A y) ξ = 0) →
      (∀ y : Submission.Mostow.E n, inner ℝ y ξ = 0 → ‖A y‖ = ‖y‖) →
      (∀ (y : Submission.Mostow.E n) (D : ℝ), inner ℝ y ξ = 0 → 0 < D →
        Work.Mostow.lev ξ ((γ : LeanEval.Geometry.MostowRigidity.PO n 1) • Work.Mostow.hptOf ξ y D) = D ∧
        Work.Mostow.yc ξ ((γ : LeanEval.Geometry.MostowRigidity.PO n 1) • Work.Mostow.hptOf ξ y D) = A y + v) →
      ∃ y : Submission.Mostow.E n, inner ℝ y ξ = 0 ∧ ‖y‖ = 1 ∧ θ ≤ ‖A y - y‖) :
    ∀ ε' : ℝ, 0 < ε' → ∃ t : ℝ,
      Submission.Mostow.horoball ξ t ⊆ Work.Mostow.cuspThinRegion Γ ξ ε' := by
  obtain ⟨θ, hθ, hgap'⟩ := hgap
  have hξS : ξ ∈ Submission.Mostow.Sph n := hξ.1
  have hn2 : 2 ≤ n := by omega
  -- Step 1: the uniform bound on the short elements at the frontier points.
  obtain ⟨ε, hε, N, hN⟩ :=
    Work.Mostow.frontierShortBoundCusp n hn hA hI Γ hΓ hvan ξ hξ θ hθ hgap'
  -- Step 2: the frontier is `Γ_ξ`-cocompact.
  obtain ⟨K, hKc, hK⟩ :=
    Work.Mostow.frontierCocompactOfLattice n hn hA hI Γ hΓ hvan ξ hξ ε hε N hN
  have hKne : K.Nonempty := by
    obtain ⟨σ, -, hσK⟩ := hK 0 (by simp)
    exact ⟨_, hσK⟩
  -- Step 3: `lev ξ` is bounded below on `K`, hence `parDisp` is bounded above.
  have hcontlev : Continuous (fun z : Submission.Mostow.E n => Work.Mostow.lev ξ z) := by
    have htpart : Continuous (fun u : Submission.Mostow.E n => Submission.Mostow.tpart u) := by
      simp only [Submission.Mostow.tpart]; fun_prop
    simp only [Work.Mostow.lev]
    exact htpart.sub (by fun_prop)
  obtain ⟨z₀, hz₀K, hz₀min⟩ := hKc.exists_isMinOn hKne hcontlev.continuousOn
  have hz₀pos : 0 < Work.Mostow.lev ξ z₀ := Work.Mostow.lev_pos ξ hξS z₀
  have hstab : ∀ (γ : Γ), Submission.Mostow.bd
      (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      Work.Mostow.bCocy (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = 0 :=
    fun γ hγ => hvan γ ξ hξ hγ
  have hparDispPos : ∀ y : Submission.Mostow.E n, inner ℝ y ξ = 0 →
      0 < Work.Mostow.parDisp Γ ξ y :=
    fun y hy => Work.Mostow.parDisp_pos_of_discrete n hA hI Γ hΓ.1 hξS hstab hξ.2 hy
  -- `parDisp ≤ M` with `M := cEps ε / lev ξ z₀`
  have hbound : ∀ y : Submission.Mostow.E n, inner ℝ y ξ = 0 →
      Work.Mostow.parDisp Γ ξ y ≤ Work.Mostow.cEps ε / Work.Mostow.lev ξ z₀ := by
    intro y hy
    have hpos : 0 < Work.Mostow.cEps ε / Work.Mostow.parDisp Γ ξ y :=
      div_pos (Work.Mostow.fsbc_cEps_pos hε) (hparDispPos y hy)
    obtain ⟨σ, hσbd, hσK⟩ := hK y hy
    have hlev : ∀ u : Submission.Mostow.E n,
        Work.Mostow.lev ξ ((σ : LeanEval.Geometry.MostowRigidity.PO n 1) • u)
          = Work.Mostow.lev ξ u :=
      lev_smul_of_bCocy_zero_of_bd hA hI hξS hσbd (hvan σ ξ hξ hσbd)
    have h1 : Work.Mostow.lev ξ z₀ ≤ Work.Mostow.cEps ε / Work.Mostow.parDisp Γ ξ y := by
      calc Work.Mostow.lev ξ z₀
          ≤ Work.Mostow.lev ξ ((σ : LeanEval.Geometry.MostowRigidity.PO n 1) •
              Work.Mostow.frontierPt Γ ξ ε y) := hz₀min hσK
        _ = Work.Mostow.lev ξ (Work.Mostow.frontierPt Γ ξ ε y) := hlev _
        _ = Work.Mostow.cEps ε / Work.Mostow.parDisp Γ ξ y :=
            Work.Mostow.lev_frontierPt hξS hy hpos
    have hpd : 0 < Work.Mostow.parDisp Γ ξ y := hparDispPos y hy
    calc Work.Mostow.parDisp Γ ξ y
        = Work.Mostow.cEps ε / (Work.Mostow.cEps ε / Work.Mostow.parDisp Γ ξ y) := by
          rw [eq_div_iff (ne_of_gt (div_pos (Work.Mostow.fsbc_cEps_pos hε) hpd))]
          field_simp
      _ ≤ Work.Mostow.cEps ε / Work.Mostow.lev ξ z₀ :=
          div_le_div_of_nonneg_left (le_of_lt (Work.Mostow.fsbc_cEps_pos hε)) hz₀pos h1
  -- Step 4: conclude.
  intro ε' hε'
  have hMpos : 0 < Work.Mostow.cEps ε / Work.Mostow.lev ξ z₀ :=
    div_pos (Work.Mostow.fsbc_cEps_pos hε) hz₀pos
  refine ⟨Real.log (Work.Mostow.cEps ε' / (Work.Mostow.cEps ε / Work.Mostow.lev ξ z₀)), ?_⟩
  intro u hu
  have hthin := (Work.Mostow.cuspThinRegion_eq_parDisp n hA hI Γ hΓ.1 hvan hξ).2 ε' hε' u
  rw [hthin]
  have hlevu : Work.Mostow.lev ξ u = Real.exp (Submission.Mostow.busemann ξ u) :=
    Work.Mostow.lev_eq_exp hξS u
  have hlt : Work.Mostow.lev ξ u < Work.Mostow.cEps ε' / (Work.Mostow.cEps ε / Work.Mostow.lev ξ z₀) := by
    rw [hlevu, ← Real.exp_log (div_pos (Work.Mostow.fsbc_cEps_pos hε') hMpos)]
    exact Real.exp_lt_exp.mpr hu
  have hyc : inner ℝ (Work.Mostow.yc ξ u) ξ = 0 := Work.Mostow.inner_yc hξS u
  have hle := hbound (Work.Mostow.yc ξ u) hyc
  have hpd := hparDispPos (Work.Mostow.yc ξ u) hyc
  have h0 : 0 ≤ Work.Mostow.cEps ε' / (Work.Mostow.cEps ε / Work.Mostow.lev ξ z₀) :=
    le_of_lt (div_pos (Work.Mostow.fsbc_cEps_pos hε') hMpos)
  calc Work.Mostow.lev ξ u * Work.Mostow.parDisp Γ ξ (Work.Mostow.yc ξ u)
      < (Work.Mostow.cEps ε' / (Work.Mostow.cEps ε / Work.Mostow.lev ξ z₀))
          * Work.Mostow.parDisp Γ ξ (Work.Mostow.yc ξ u) :=
        mul_lt_mul_of_pos_right hlt hpd
    _ ≤ (Work.Mostow.cEps ε' / (Work.Mostow.cEps ε / Work.Mostow.lev ξ z₀))
          * (Work.Mostow.cEps ε / Work.Mostow.lev ξ z₀) :=
        mul_le_mul_of_nonneg_left hle h0
    _ = Work.Mostow.cEps ε' := by
        rw [div_mul_cancel₀]
        exact ne_of_gt hMpos

/-- **The elliptic gap of a cusp stabiliser**, in the abstract `(A, v)` form used by
`Work.Mostow.frontierShortBoundCusp`.  This is `Work.Mostow.stabEllipticGapLattice`. -/
theorem ellipticGapCusp (n : ℕ) (hn : 3 ≤ n)
    (hA : Submission.Mostow.POActionProp n) (hI : Submission.Mostow.HypIsometryProp n)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)) (hΓ : Submission.Mostow.HypLattice Γ)
    (hvan : ∀ (γ : Γ) ξ, ξ ∈ Work.Mostow.parFixed Γ →
      Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      Work.Mostow.bCocy (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = 0)
    (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Work.Mostow.parFixed Γ) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ (γ : Γ) (A : Submission.Mostow.E n →ₗ[ℝ] Submission.Mostow.E n)
      (v : Submission.Mostow.E n),
      (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ≠ 1 →
      Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      (∃ p : Submission.Mostow.E n, (γ : LeanEval.Geometry.MostowRigidity.PO n 1) • p = p) →
      (∀ y : Submission.Mostow.E n, inner ℝ y ξ = 0 → inner ℝ (A y) ξ = 0) →
      (∀ y : Submission.Mostow.E n, inner ℝ y ξ = 0 → ‖A y‖ = ‖y‖) →
      (∀ (y : Submission.Mostow.E n) (D : ℝ), inner ℝ y ξ = 0 → 0 < D →
        Work.Mostow.lev ξ ((γ : LeanEval.Geometry.MostowRigidity.PO n 1) • Work.Mostow.hptOf ξ y D) = D ∧
        Work.Mostow.yc ξ ((γ : LeanEval.Geometry.MostowRigidity.PO n 1) • Work.Mostow.hptOf ξ y D) = A y + v) →
      ∃ y : Submission.Mostow.E n, inner ℝ y ξ = 0 ∧ ‖y‖ = 1 ∧ θ ≤ ‖A y - y‖ :=
  Work.Mostow.flatEllipticGap n hn hA hI Γ hΓ ξ hξ

/-- **A flat translation in the cusp stabiliser of a lattice.**

For a lattice `Γ ≤ PO(n,1)` (`n ≥ 2`), a parabolic fixed point `ξ ∈ parFixed Γ` whose stabiliser
preserves the horospherical levels (`hvan`), there is `δ ∈ Γ` fixing `ξ` acting on the horospheres
of `ξ` as the flat translation by a nonzero vector `v ⊥ ξ`, preserving the levels. -/
theorem flatTranslationCusp (n : ℕ) (hn : 2 ≤ n)
    (hA : Submission.Mostow.POActionProp n) (hI : Submission.Mostow.HypIsometryProp n)
    (hBb : ∀ m, Submission.Mostow.BieberbachProp m)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)) (hΓ : Submission.Mostow.HypLattice Γ)
    (hvan : ∀ (γ : Γ) ξ, ξ ∈ Work.Mostow.parFixed Γ →
      Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      Work.Mostow.bCocy (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = 0)
    (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Work.Mostow.parFixed Γ) :
    ∃ (δ : Γ) (v : Submission.Mostow.E n), v ≠ 0 ∧ inner ℝ v ξ = 0 ∧
      Submission.Mostow.bd (δ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ ∧
      (∀ u : Submission.Mostow.E n,
        Work.Mostow.yc ξ ((δ : LeanEval.Geometry.MostowRigidity.PO n 1) • u)
          = Work.Mostow.yc ξ u + v) ∧
      (∀ u : Submission.Mostow.E n,
        Work.Mostow.lev ξ ((δ : LeanEval.Geometry.MostowRigidity.PO n 1) • u)
          = Work.Mostow.lev ξ u) := by
  by_cases h2 : n = 2
  · subst h2
    obtain ⟨δ, _hpar, hbd, hc, v, hv, hyc⟩ :=
      Work.Mostow.flatTrans_of_lattice_two hA hI Γ hvan ξ hξ
    have hvξ : inner ℝ v ξ = 0 := by
      have h := congrArg (fun z => inner ℝ z ξ) (hyc 0)
      rw [inner_add_left] at h
      have h1 : inner ℝ (Work.Mostow.yc ξ ((δ : PO 2 1) • (0 : E 2))) ξ = 0 :=
        Work.Mostow.inner_yc hξ.1 _
      have h2' : inner ℝ (Work.Mostow.yc ξ (0 : E 2)) ξ = 0 := Work.Mostow.inner_yc hξ.1 _
      rw [h1, h2', zero_add] at h
      exact h.symm
    exact ⟨δ, v, hv, hvξ, hbd, hyc, lev_smul_of_bCocy_zero_of_bd hA hI hξ.1 hbd hc⟩
  · have hn3 : 3 ≤ n := by omega
    obtain ⟨K, hKc, hK⟩ :=
      cocompact_level_one_of_thinHoroball n hn hA hI hBb Γ hΓ hvan ξ hξ
        (cuspThinRegion_horoball_of_gap n hn3 hA hI Γ hΓ hvan ξ hξ
          (ellipticGapCusp n hn3 hA hI Γ hΓ hvan ξ hξ))
    obtain ⟨δ, _hpar, hbd, hc, v, hv, hvξ, hyc⟩ :=
      csha_flatTransOfCocompact n hn hA hI hBb Γ hΓ hvan ξ hξ ⟨K, hKc, hK⟩
    exact ⟨δ, v, hv, hvξ, hbd, hyc, lev_smul_of_bCocy_zero_of_bd hA hI hξ.1 hbd hc⟩

end

end Work.Mostow
