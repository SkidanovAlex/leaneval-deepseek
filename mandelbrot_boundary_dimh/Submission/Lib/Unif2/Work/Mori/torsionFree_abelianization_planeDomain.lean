import Mathlib
import Submission.Lib.Unif2.Work.Mori.torsionFree_abelianization_riemannSurface
import Submission.Lib.Unif2.Work.Spine.Plane.Dyadic
import Submission.Lib.Unif2.Work.Spine.Plane.pi1_spine_isFreeGroup

/-!
# The abelianization of the fundamental group of a plane domain is torsion-free

The target of this file is `Work.Mori.torsionFree_abelianization_planeDomain`: for a connected open
`U ⊆ ℂ`, the abelianization `π₁(U,z)^{ab}` is a torsion-free abelian group.

This is the "abelian half" of the planar spine theorem, and it is **strictly weaker** than freeness
of `π₁(U)`: a torsion-free abelianization rules out torsion quotients, not non-free ones.

## Route (spine-free)

Unlike `Work.Mori.torsionFree_abelianization_riemannSurface` (whose proof routes through freeness of
`π₁` of an open surface, i.e. through the spine theorem), the present statement is proved *without*
the spine theorem, using the explicit polyomino exhaustion of a plane domain:

* `Work.Spine.Plane.polyK U hU n` is a finite union of level-`n` dyadic squares, increasing in `n`,
  contained in `U`, and every compact subset of `U` lies in some term
  (`Work.Spine.Plane.exists_polyK_superset_of_compact`, `..._of_path`, `..._of_homotopy`);
* each `Work.Spine.Plane.polyK U hU n` **strongly deformation retracts onto a one-dimensional CW
  spine** (`Commons.Topology.Plane.dyadicPolyomino_deformationRetract`, packaged as
  `Work.Spine.Plane.spine_deformationRetract`), so `π₁(polyK U hU n)` is *free*
  (`isFreeGroup_fundamentalGroup_polyK` below);
* freeness ⟹ the abelianization is free abelian ⟹ torsion-free;
* torsion-freeness passes to the filtered colimit of the `π₁(polyK U hU n)`
  (`Work.Mori.isMulTorsionFree_abelianization_of_directedColimit`), and the colimit is `π₁(U)` by
  the cofinality of the exhaustion.

The two-step structure (free at each level, torsion-free in the limit) is exactly why the abelian
statement is cheaper than the spine theorem: the limit of the free groups need not be free, but it
is always torsion-free.
-/

/-!
## Status of this file (this session)

Proved here, **without** the spine theorem:

* `Work.Mori.isFreeGroup_fundamentalGroup_polyK`: `π₁` of a level-`n` dyadic polyomino is free.
  The polyomino fold `Work.Spine.Plane.spine_deformationRetract` is a *strong deformation
  retraction* of the polyomino onto a retract `G` carrying a CW structure with no cells of
  dimension `≥ 2`; `G` is the equaliser of the continuous map `H (·, 1)` with the identity, hence
  closed, so its CW structure transports to the subtype and freeness of `π₁` of a one-dimensional
  CW complex applies; the retraction is a homotopy equivalence, transported along
  `Commons.AlgebraicTopology.FundamentalGroup.pi1_equiv_of_homotopyEquiv`.
* `Work.Mori.isMulTorsionFree_abelianization_polyK`: the abelianisation of the polyomino's `π₁` is
  torsion-free (a free group's abelianisation is free abelian).

**Still to do** for the target `torsionFree_abelianization_planeDomain`: pass to the filtered
colimit `π₁(U) = colim_n π₁(polyK U hU n)` using
`Work.Mori.isMulTorsionFree_abelianization_of_directedColimit` (proved in
`torsionFree_abelianization_riemannSurface.lean`, pure group theory), the cofinality lemmas
`Work.Spine.Plane.exists_polyK_superset_of_path` / `..._of_homotopy`, and the base-point bookkeeping
`FundamentalGroup.mapOfEq` / `Work.Mori.fundamentalGroupSubtypeMapOfSubset`.  The only missing
ingredient is that bookkeeping; the mathematics is complete (see the file header).
-/

set_option maxHeartbeats 800000

open scoped unitInterval

namespace Work.Mori

noncomputable section

open Set

variable {U : Set ℂ}

/-- **The fundamental group of a polyomino is free.**

`Work.Spine.Plane.polyK U hU n` is a finite union of dyadic squares; the polyomino fold of
`Commons.Topology.Plane.dyadicPolyomino_deformationRetract` (packaged as
`Work.Spine.Plane.spine_deformationRetract`) is a *strong deformation retraction* of the polyomino
onto a subspace `G` carrying a CW structure with no cells of dimension `≥ 2`.  The retract `G` is
the equaliser of the continuous map `H (·, 1)` with the identity, hence closed, so its CW structure
transports to the subtype `↥G` and freeness of `π₁` of a one-dimensional CW complex applies. -/
theorem isFreeGroup_fundamentalGroup_polyK (hU : IsOpen U) (n : ℕ)
    (v : ↥(Work.Spine.Plane.polyK U hU n)) :
    IsFreeGroup (FundamentalGroup ↥(Work.Spine.Plane.polyK U hU n) v) := by
  obtain ⟨G, hC, H, hdim, hHc, hH0, hH1, hHfix⟩ :=
    Work.Spine.Plane.spine_deformationRetract U hU n
  -- the retract is the equaliser of `H (·,1)` with the identity, hence closed
  have hGeq : G = {x : ↥(Work.Spine.Plane.polyK U hU n) | H (x, (1 : unitInterval)) = x} := by
    ext x
    constructor
    · intro hx
      exact hHfix x hx 1
    · intro hx
      rw [← hx]
      exact hH1 x
  have hGclosed : IsClosed G := by
    rw [hGeq]
    exact isClosed_eq (hHc.comp (by fun_prop)) continuous_id
  obtain ⟨hC', hcell'⟩ :=
    Commons.Topology.CWComplex.exists_cwComplex_univ_of_isClosed_subspace hGclosed hC
  -- π₁ of the retract is free
  have hfree : ∀ w : ↥G, IsFreeGroup (FundamentalGroup ↥G w) := fun w =>
    Work.Spine.Plane.isFreeGroup_fundamentalGroup_of_oneDimCWComplex_point hC'
      (fun m hm => hcell' m (hdim m hm)) w
  -- the strong deformation retraction is a homotopy equivalence, transported to `π₁`
  obtain ⟨he⟩ :=
    Commons.Topology.Homotopy.homotopyEquiv_of_deformationRetract G H hHc hH0 hH1 hHfix
  obtain ⟨e⟩ := Commons.AlgebraicTopology.FundamentalGroup.pi1_equiv_of_homotopyEquiv he v
  exact IsFreeGroup.ofMulEquiv e.symm

/-- **The abelianisation of `π₁` of a polyomino is torsion-free.** -/
theorem isMulTorsionFree_abelianization_polyK (hU : IsOpen U) (n : ℕ)
    (v : ↥(Work.Spine.Plane.polyK U hU n)) :
    IsMulTorsionFree (Abelianization (FundamentalGroup ↥(Work.Spine.Plane.polyK U hU n) v)) := by
  haveI : IsFreeGroup (FundamentalGroup ↥(Work.Spine.Plane.polyK U hU n) v) :=
    isFreeGroup_fundamentalGroup_polyK hU n v
  exact isMulTorsionFree_abelianization_of_isFreeGroup

/-! ## The base-point bookkeeping for the colimit

`FundamentalGroup.mapOfEq` is the only place where the base points of the pieces of an exhaustion
enter.  The two lemmas below are all that is needed to make the directed system of
`Work.Mori.isMulTorsionFree_abelianization_of_directedColimit` functorial. -/

/-- `FundamentalGroup.mapOfEq` is insensitive to the choice of the endpoint proof. -/
theorem mapOfEq_congr' {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {y : Y} (h₁ h₂ : f x = y) :
    FundamentalGroup.mapOfEq f h₁ = FundamentalGroup.mapOfEq f h₂ := by
  ext γ
  simp only [FundamentalGroup.mapOfEq_apply]

/-- `FundamentalGroup.mapOfEq` only depends on the continuous map. -/
theorem mapOfEq_congr_map {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f₁ f₂ : C(X, Y)} (hf : f₁ = f₂) {x : X} {y : Y} (h₁ : f₁ x = y) (h₂ : f₂ x = y) :
    FundamentalGroup.mapOfEq f₁ h₁ = FundamentalGroup.mapOfEq f₂ h₂ := by
  subst hf
  exact mapOfEq_congr' _ _ _

/-- **Composition of `FundamentalGroup.mapOfEq`.** -/
theorem mapOfEq_comp' {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : C(X, Y)) (g : C(Y, Z)) {x : X} {y : Y} {z : Z}
    (hf : f x = y) (hg : g y = z) (hgf : (g.comp f) x = z) :
    (FundamentalGroup.mapOfEq g hg).comp (FundamentalGroup.mapOfEq f hf)
      = FundamentalGroup.mapOfEq (g.comp f) hgf := by
  ext γ
  simp only [MonoidHom.comp_apply, FundamentalGroup.mapOfEq_apply]
  rw [Path.Homotopic.Quotient.map_cast, Path.Homotopic.Quotient.cast_cast,
    Path.Homotopic.Quotient.map_comp]

/-! ## Comparing a lifted loop with the loop it lifts

The two lemmas below are the path-level input of the cofinality of the polyomino exhaustion: a loop
of the ambient space with image in a level, lifted to that level, represents the same class as the
original loop. -/

/-- The class of a lifted loop under the inclusion of the level is the class of the loop. -/
theorem mapOfEq_mk_lift {X : Type*} [TopologicalSpace X] {K V : Set X} (hKV : K ⊆ V)
    {x z : X} (hx : x = z) (hxK : x ∈ K) (hV : z ∈ V)
    (γ : Path (⟨x, hxK⟩ : ↥K) ⟨x, hxK⟩) (γ₀ : Path (⟨z, hV⟩ : ↥V) ⟨z, hV⟩)
    (hγ : ∀ t, ((γ t : ↥K) : X) = ((γ₀ t : ↥V) : X)) :
    FundamentalGroup.mapOfEq
        (⟨fun y => ⟨y.1, hKV y.2⟩, Continuous.subtype_mk continuous_subtype_val _⟩ : C(↥K, ↥V))
        (Subtype.ext hx) (Path.Homotopic.Quotient.mk γ) = Path.Homotopic.Quotient.mk γ₀ := by
  rw [FundamentalGroup.mapOfEq_apply, ← Path.Homotopic.Quotient.mk_map,
    ← Path.Homotopic.Quotient.mk_cast]
  congr 1
  exact Path.ext (funext fun t => Subtype.ext (hγ t))

/-- The class-level computation of `mapOfEq` on a loop class. -/
theorem mapOfEq_mk_eq {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}
    (f : C(X, Y)) (h : f x = y) (γ : Path x x) :
    FundamentalGroup.mapOfEq f h (Path.Homotopic.Quotient.mk γ)
      = (Path.Homotopic.Quotient.mk (γ.map (f := fun z => f z) f.continuous)).cast h.symm h.symm := by
  rw [FundamentalGroup.mapOfEq_apply, ← Path.Homotopic.Quotient.mk_map]

/-- `mapOfEq` with the trivial endpoint equality is `FundamentalGroup.map`. -/
theorem mapOfEq_rfl {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (x : X) :
    FundamentalGroup.mapOfEq f (rfl : f x = f x) = FundamentalGroup.map f x := by
  ext p
  rw [FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.cast_rfl_rfl]
  rfl

/-- **`mapOfEq` has the same kernel as `FundamentalGroup.map`** (it differs from it by conjugation
along the endpoint identification). -/
theorem mapOfEq_eq_one_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X}
    {y : Y} (f : C(X, Y)) (h : f x = y) (p : FundamentalGroup X x) :
    FundamentalGroup.mapOfEq f h p = 1 ↔ FundamentalGroup.map f x p = 1 := by
  cases h
  rw [mapOfEq_rfl]

/-- A loop of the ambient space whose image lies in a level, regarded as a loop of that level. -/
def liftLoop {X : Type*} [TopologicalSpace X] {K : Set X} {z : X} (hzK : z ∈ K)
    (γ : Path (⟨z, hzK⟩ : ↥K) ⟨z, hzK⟩) : Path (⟨z, hzK⟩ : ↥K) ⟨z, hzK⟩ := γ


/-! ## The directed colimit with an element-wise cofinality hypothesis

The exhaustion of a plane domain by polyominoes does *not* satisfy the uniform "eventually killed
kernel" hypothesis (a loop of a level that is null-homotopic in the domain has its homotopy at its
own level, with no uniform bound in general), but it satisfies the element-wise form: every
*individual* element killed in the colimit is killed at some later level.  The two lemmas below are
`Work.Mori.abelianization_eventual_kernel` / `Work.Mori.isMulTorsionFree_abelianization_of_directedColimit`
with that weaker hypothesis; the proofs are unchanged except at the single place where the kernel
hypothesis is applied. -/

theorem abelianization_eventual_kernel' {G : Type*} [Group G] {H : ℕ → Type*} [∀ n, Group (H n)]
    (psi : (n m : ℕ) → n ≤ m → H n →* H m)
    (phi : (n : ℕ) → H n →* G)
    (hphipsi : ∀ {n m : ℕ} (hnm : n ≤ m), (phi m).comp (psi n m hnm) = phi n)
    (hpsi : ∀ {n m k : ℕ} (hnm : n ≤ m) (hmk : m ≤ k),
      (psi m k hmk).comp (psi n m hnm) = psi n k (hnm.trans hmk))
    (hsurj : ∀ g : G, ∃ n, ∃ x : H n, phi n x = g)
    (hker : ∀ (n : ℕ) (x : H n), phi n x = 1 → ∃ m, ∃ hnm : n ≤ m, psi n m hnm x = 1)
    (n : ℕ) (y : Abelianization (H n))
    (hy : Abelianization.map (phi n) y = 1) :
    ∃ m, ∃ hnm : n ≤ m, Abelianization.map (psi n m hnm) y = 1 := by
  -- write y as the class of an element of H n
  obtain ⟨z, hz⟩ : ∃ z : H n, Abelianization.of z = y := by
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨z, rfl⟩
  -- phi n z ∈ commutator G
  have hc : phi n z ∈ commutator G := by
    rw [mem_commutator_iff]
    rw [← hy, ← hz, abelianization_map_of]
  -- it comes from the commutator subgroup of some stage
  have hmem := commutator_le_iSup_map (G := G) psi phi hphipsi hsurj hc
  have hdir : Directed (· ≤ ·) (fun k => (commutator (H k)).map (phi k)) :=
    fun i j => ⟨max i j, map_commutator_mono psi phi hphipsi (le_max_left _ _),
      map_commutator_mono psi phi hphipsi (le_max_right _ _)⟩
  rw [Subgroup.mem_iSup_of_directed hdir] at hmem
  obtain ⟨k, hk⟩ := hmem
  obtain ⟨c, hc_mem, hck⟩ := hk
  -- choose M ≥ n, k
  obtain ⟨M, hMn, hMk⟩ : ∃ M : ℕ, n ≤ M ∧ k ≤ M := ⟨max n k, le_max_left _ _, le_max_right _ _⟩
  have h1 : phi M (psi k M hMk c) = phi n z := by
    have := congrArg (fun f : H k →* G => f c) (hphipsi hMk)
    exact this.trans hck
  have h2 : phi M (psi n M hMn z) = phi n z := by
    have := congrArg (fun f : H n →* G => f z) (hphipsi hMn)
    exact this
  -- so the element psi k M c * (psi n M z)⁻¹ is killed by phi M
  have h3 : phi M (psi k M hMk c * (psi n M hMn z)⁻¹) = 1 := by
    rw [map_mul, map_inv, h1, h2, mul_inv_cancel]
  -- extract a further stage M' at which it is killed in H M'
  obtain ⟨M', hMM', hkill⟩ := hker M (psi k M hMk c * (psi n M hMn z)⁻¹) h3
  refine ⟨M', hMn.trans hMM', ?_⟩
  -- hkill : psi M M' (psi k M c * (psi n M z)⁻¹) = 1
  have hkill' : (psi M M' hMM').comp (psi k M hMk) c = (psi M M' hMM').comp (psi n M hMn) z := by
    have h := hkill
    rw [map_mul, map_inv, mul_inv_eq_one] at h
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
    exact h
  -- rewrite psi n M' z using compatibility
  have hcomp : (psi M M' hMM').comp (psi n M hMn) z = psi n M' (hMn.trans hMM') z := by
    have := congrArg (fun f : H n →* H M' => f z) (hpsi hMn hMM')
    exact this
  have hmem' : (psi M M' hMM').comp (psi k M hMk) c ∈ commutator (H M') :=
    map_commutator_le ((psi M M' hMM').comp (psi k M hMk))
      (Subgroup.mem_map_of_mem _ hc_mem)
  have hfin : Abelianization.of (((psi M M' hMM').comp (psi k M hMk)) c) = 1 :=
    (mem_commutator_iff _).mp hmem'
  rw [← hz, abelianization_map_of, ← hcomp, ← hkill']
  exact hfin

theorem isMulTorsionFree_abelianization_of_directedColimit'
    {G : Type*} [Group G] {H : ℕ → Type*} [∀ n, Group (H n)]
    (psi : (n m : ℕ) → n ≤ m → H n →* H m)
    (phi : (n : ℕ) → H n →* G)
    (hphipsi : ∀ {n m : ℕ} (hnm : n ≤ m), (phi m).comp (psi n m hnm) = phi n)
    (hpsi : ∀ {n m k : ℕ} (hnm : n ≤ m) (hmk : m ≤ k),
      (psi m k hmk).comp (psi n m hnm) = psi n k (hnm.trans hmk))
    (hsurj : ∀ g : G, ∃ n, ∃ x : H n, phi n x = g)
    (hker : ∀ (n : ℕ) (x : H n), phi n x = 1 → ∃ m, ∃ hnm : n ≤ m, psi n m hnm x = 1)
    (htf : ∀ n, IsMulTorsionFree (Abelianization (H n))) :
    IsMulTorsionFree (Abelianization G) := by
  have main : ∀ (N : ℕ), N ≠ 0 → ∀ a : Abelianization G, a ^ N = 1 → a = 1 := by
    intro N hN a ha
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (s := commutator G) a
    have hg' : Abelianization.of g = a := hg
    subst hg'
    obtain ⟨n, x, hx⟩ := hsurj g
    subst hx
    have hbmap : Abelianization.map (phi n) (Abelianization.of x) = Abelianization.of ((phi n) x) :=
      abelianization_map_of (phi n) x
    have hbN : Abelianization.map (phi n) ((Abelianization.of x) ^ N) = 1 := by
      rw [map_pow, hbmap]
      exact ha
    obtain ⟨m, hnm, hm⟩ :=
      abelianization_eventual_kernel' psi phi hphipsi hpsi hsurj hker n _ hbN
    have htors : Abelianization.map (psi n m hnm) (Abelianization.of x) = 1 := by
      refine IsMulTorsionFree.pow_left_injective (M := Abelianization (H m)) hN ?_
      show (Abelianization.map (psi n m hnm) (Abelianization.of x)) ^ N
        = (1 : Abelianization (H m)) ^ N
      rw [one_pow, ← map_pow]
      exact hm
    rw [show (phi n) x = (phi m) ((psi n m hnm) x) from
      (congrArg (fun f : H n →* G => f x) (hphipsi hnm)).symm]
    rw [← abelianization_map_of]
    rw [show Abelianization.of ((psi n m hnm) x)
      = Abelianization.map (psi n m hnm) (Abelianization.of x) from
        (abelianization_map_of (psi n m hnm) x).symm]
    rw [htors, map_one]
  refine ⟨fun N hN a b hab => ?_⟩
  have hab' : a ^ N = b ^ N := hab
  have h1 : (a * b⁻¹) ^ N = 1 := by
    rw [mul_pow, hab', inv_pow, mul_inv_cancel]
  have h2 := main N hN (a * b⁻¹) h1
  rwa [mul_inv_eq_one] at h2

/-! ## The polyomino colimit

`π₁(U)` is the filtered colimit of the `π₁(polyK U hU n)` (cofinality: every loop, and every
homotopy of loops, lands in a level), and torsion-freeness passes to filtered colimits of groups by
`Work.Mori.isMulTorsionFree_abelianization_of_directedColimit'` (the element-wise kernel form, since
the polyomino exhaustion does *not* satisfy the uniform form).  The resulting theorem,
`Work.Mori.torsionFree_abelianization_planeDomain` — that `π₁(U)^{ab}` is torsion-free for a
connected open `U ⊆ ℂ` — is proved in the module
`Submission.Work.Mori.torsionFree_abelianization_planeDomain_colimit`, on top of the *general*
exhaustion lemma `Work.Mori.isMulTorsionFree_abelianization_of_exhaustion`
(`Submission/Work/Mori/torsionFree_abelianization_of_exhaustion.lean`), which performs the colimit
passage once and for all; this keeps the file free of the heavy elaboration of the concrete
polyomino system.

The bricks used below are the `FundamentalGroup.mapOfEq` calculus (`mapOfEq_congr'`,
`mapOfEq_congr_map`, `mapOfEq_comp'`, `mapOfEq_mk_lift`, `mapOfEq_mk_eq`, `mapOfEq_rfl`,
`mapOfEq_eq_one_iff`), the polyomino freeness `isFreeGroup_fundamentalGroup_polyK` and
`isMulTorsionFree_abelianization_polyK`, and the element-wise colimit lemma
`isMulTorsionFree_abelianization_of_directedColimit'`. -/

end

end Work.Mori
