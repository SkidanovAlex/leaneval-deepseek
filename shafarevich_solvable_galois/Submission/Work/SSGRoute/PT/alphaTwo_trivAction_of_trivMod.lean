import Mathlib
import Submission.Work.SSGRoute.PT.AlphaTwoTrivModSurj
import Submission.Work.SSGRoute.PT.alphaTwo_naturality
import Submission.Work.AbsoluteKummer.H2Pi.nonempty_h2_pi_equiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The trivial-action base case of `α²` in full generality

If `α²` is bijective for the trivial module `ℤ/p`, then it is bijective for *every* finite module
of exponent `p` with trivial `G`-action.  Such a module is an `𝔽_p`-vector space `(ℤ/p)^n`, and
`α²` is compatible both with the product decomposition `Hom_ℤ(∏ᵢ Nᵢ, C) ≅ ∏ᵢ Hom_ℤ(Nᵢ, C)` and
with the product decomposition of `H²` (`Work.AbsoluteKummer.H2Pi.nonempty_h2_pi_equiv`); the
transfer along an additive equivalence `(ℤ/p)^n ≅ N` uses the naturality of `α²` in `N`
(`Work.SSGRoute.PT.alphaTwo_naturality`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open Classical

namespace Work.SSGRoute.PT

noncomputable section

/-! ## Functoriality of `mapH2` -/

/-- `mapH2` of the identity coefficient map is the identity. -/
theorem mapH2_id_coeff {G : Type} [TopologicalSpace G] [Group G] {M : Type} [AddCommGroup M]
    [DistribMulAction G M] :
    Work.AbsoluteKummer.mapH2 (AddMonoidHom.id M)
      (Work.GroupCohomology.isEquivariant_id (G := G) (A := M))
      = AddMonoidHom.id (Work.AbsoluteKummer.H2 G M) := by
  refine AddMonoidHom.ext (fun x => ?_)
  exact Work.AbsoluteKummer.SES.H2_induction_on (M := M) x
    (C := fun z => (Work.AbsoluteKummer.mapH2 (AddMonoidHom.id M)
      (Work.GroupCohomology.isEquivariant_id (G := G) (A := M))) z = z)
    (fun c => Work.AbsoluteKummer.mapH2_id_H2π c)

/-- `mapH2` depends only on the coefficient map (the equivariance witness is a proposition). -/
theorem mapH2_congr_map {G : Type} [TopologicalSpace G] [Group G] {M : Type} {N : Type}
    [AddCommGroup M] [AddCommGroup N] [DistribMulAction G M] [DistribMulAction G N]
    {φ ψ : M →+ N} (h : φ = ψ) (hφ : Work.GroupCohomology.IsEquivariant G φ)
    (hψ : Work.GroupCohomology.IsEquivariant G ψ) :
    Work.AbsoluteKummer.mapH2 φ hφ = Work.AbsoluteKummer.mapH2 ψ hψ := by
  subst h
  exact congrArg (fun hh => Work.AbsoluteKummer.mapH2 φ hh) (Subsingleton.elim hφ hψ)

/-- An equivariant additive equivalence induces mutually inverse maps on `H²`: the composite
`mapH2 e ∘ mapH2 e.symm` is the identity. -/
theorem mapH2_comp_symm_eq_id {G : Type} [TopologicalSpace G] [Group G] {M : Type} {N : Type}
    [AddCommGroup M] [AddCommGroup N] [DistribMulAction G M] [DistribMulAction G N]
    (e : M ≃+ N) (he : Work.GroupCohomology.IsEquivariant G (e : M →+ N))
    (he' : Work.GroupCohomology.IsEquivariant G (e.symm : N →+ M)) :
    (Work.AbsoluteKummer.mapH2 (e : M →+ N) he).comp
        (Work.AbsoluteKummer.mapH2 (e.symm : N →+ M) he')
      = AddMonoidHom.id (Work.AbsoluteKummer.H2 G N) := by
  refine AddMonoidHom.ext (fun y => ?_)
  exact Work.AbsoluteKummer.SES.H2_induction_on (M := N) y
    (C := fun z => (Work.AbsoluteKummer.mapH2 (e : M →+ N) he)
      ((Work.AbsoluteKummer.mapH2 (e.symm : N →+ M) he') z) = z) (fun c => by
    rw [Work.AbsoluteKummer.mapH2_H2π, Work.AbsoluteKummer.mapH2_H2π]
    congr 1
    refine Subtype.ext (funext fun p => ?_)
    simp only [Work.AbsoluteKummer.mapZ2_apply]
    exact e.apply_symm_apply ((c : G × G → N) p))

/-- The mirror image of `mapH2_comp_symm_eq_id`: the composite `mapH2 e.symm ∘ mapH2 e` is the
identity. -/
theorem mapH2_symm_comp_eq_id {G : Type} [TopologicalSpace G] [Group G] {M : Type} {N : Type}
    [AddCommGroup M] [AddCommGroup N] [DistribMulAction G M] [DistribMulAction G N]
    (e : M ≃+ N) (he : Work.GroupCohomology.IsEquivariant G (e : M →+ N))
    (he' : Work.GroupCohomology.IsEquivariant G (e.symm : N →+ M)) :
    (Work.AbsoluteKummer.mapH2 (e.symm : N →+ M) he').comp
        (Work.AbsoluteKummer.mapH2 (e : M →+ N) he)
      = AddMonoidHom.id (Work.AbsoluteKummer.H2 G M) := by
  refine AddMonoidHom.ext (fun x => ?_)
  exact Work.AbsoluteKummer.SES.H2_induction_on (M := M) x
    (C := fun z => (Work.AbsoluteKummer.mapH2 (e.symm : N →+ M) he')
      ((Work.AbsoluteKummer.mapH2 (e : M →+ N) he) z) = z) (fun c => by
    rw [Work.AbsoluteKummer.mapH2_H2π, Work.AbsoluteKummer.mapH2_H2π]
    congr 1
    refine Subtype.ext (funext fun p => ?_)
    simp only [Work.AbsoluteKummer.mapZ2_apply]
    exact e.symm_apply_apply ((c : G × G → M) p))

/-! ## Products: the universal property of the product -/

/-- The inclusion of the `i`-th factor into a product of additive groups. -/
def piIncl {ι : Type} [DecidableEq ι] (N : ι → Type) [∀ i, AddZeroClass (N i)] (i : ι) :
    N i →+ (∀ j, N j) where
  toFun a := Pi.single i a
  map_zero' := Pi.single_zero i
  map_add' a b := Pi.single_add i a b

@[simp] theorem piIncl_apply {ι : Type} [DecidableEq ι] (N : ι → Type) [∀ i, AddZeroClass (N i)]
    (i : ι) (a : N i) : piIncl N i a = Pi.single i a := rfl

theorem piIncl_equivariant {G : Type} [Group G] {ι : Type} [DecidableEq ι] {N : ι → Type}
    [∀ i, AddCommGroup (N i)] [∀ i, DistribMulAction G (N i)] (i : ι) :
    Work.GroupCohomology.IsEquivariant G (piIncl N i) := by
  intro g a
  funext j
  by_cases h : j = i
  · subst h
    simp [piIncl, Pi.single_eq_same]
  · simp [piIncl, Pi.single_eq_of_ne h]

theorem evalAddMonoidHom_equivariant {G : Type} [Group G] {ι : Type} {N : ι → Type}
    [∀ i, AddCommGroup (N i)] [∀ i, DistribMulAction G (N i)] (i : ι) :
    Work.GroupCohomology.IsEquivariant G (Pi.evalAddMonoidHom N i) := by
  intro g a
  simp [Pi.evalAddMonoidHom, Pi.smul_apply]

/-- The `i`-th coordinate of an invariant element of a product is invariant. -/
theorem coord_mem_invariants {G : Type} [Group G] {ι : Type} {N : ι → Type}
    [∀ i, AddCommGroup (N i)] [∀ i, DistribMulAction G (N i)] {x : ∀ i, N i}
    (hx : x ∈ Work.GroupCohomology.invariants G (∀ i, N i)) (i : ι) :
    x i ∈ Work.GroupCohomology.invariants G (N i) := by
  intro g
  have h := congrFun (hx g) i
  simpa [Pi.smul_apply] using h

/-- An invariant element of a product is the sum of the inclusions of its coordinates. -/
theorem invariants_pi_eq_sum {G : Type} [Group G] {ι : Type} [Fintype ι] [DecidableEq ι]
    {N : ι → Type} [∀ i, AddCommGroup (N i)] [∀ i, DistribMulAction G (N i)]
    (h : ∀ i, Work.GroupCohomology.IsEquivariant G (piIncl N i))
    (n : ↥(Work.GroupCohomology.invariants G (∀ i, N i))) :
    n = ∑ i, invariantsHom (piIncl N i) (h i)
      ⟨(n : ∀ i, N i) i, coord_mem_invariants (N := N) n.2 i⟩ := by
  have hcoe : (AddSubgroup.subtype (Work.GroupCohomology.invariants G (∀ i, N i)))
      (∑ i, invariantsHom (piIncl N i) (h i)
        ⟨(n : ∀ i, N i) i, coord_mem_invariants (N := N) n.2 i⟩)
      = ∑ i, (Pi.single i ((n : ∀ i, N i) i) : ∀ i, N i) := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun i _ => rfl)
  refine Subtype.ext ?_
  show (AddSubgroup.subtype (Work.GroupCohomology.invariants G (∀ i, N i))) n
      = (AddSubgroup.subtype (Work.GroupCohomology.invariants G (∀ i, N i)))
          (∑ i, invariantsHom (piIncl N i) (h i)
            ⟨(n : ∀ i, N i) i, coord_mem_invariants (N := N) n.2 i⟩)
  rw [hcoe, Finset.univ_sum_single (f := (n : ∀ i, N i))]
  rfl

/-! ## `Hom_ℤ(∏ᵢ Nᵢ, C) ≅ ∏ᵢ Hom_ℤ(Nᵢ, C)` -/

/-- Assembly of a tuple of coefficient homs into a hom out of the product. -/
def conjHomPiAssemble {ι : Type} [Fintype ι] {N : ι → Type}
    [∀ i, AddCommGroup (N i)] {C : Type} [AddCommGroup C] (F : ∀ i, ConjHom (N i) C) :
    (∀ i, N i) →+ C where
  toFun x := ∑ i, F i (x i)
  map_zero' := by simp
  map_add' x y := by simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]

/-- `Hom_ℤ(∏ᵢ Nᵢ, C) ≅ ∏ᵢ Hom_ℤ(Nᵢ, C)` for the conjugation action: a hom out of the product is
its tuple of restrictions to the factors. -/
def conjHomPiEquiv {ι : Type} [Fintype ι] [DecidableEq ι]
    (N : ι → Type) [∀ i, AddCommGroup (N i)]
    (C : Type) [AddCommGroup C] :
    ConjHom (∀ i, N i) C ≃+ (∀ i, ConjHom (N i) C) where
  toFun f := fun i => ConjHom.precomp (piIncl N i) f
  invFun F := ⟨conjHomPiAssemble F⟩
  left_inv f := by
    refine ConjHom.ext_apply (fun x => ?_)
    show (∑ i, (ConjHom.precomp (piIncl N i)) f (x i)) = f x
    simp only [ConjHom.precomp_apply, piIncl_apply]
    rw [← map_sum, Finset.univ_sum_single]
  right_inv F := by
    funext i
    refine ConjHom.ext_apply (fun a => ?_)
    show (∑ j, F j ((piIncl N i a) j)) = F i a
    rw [Fintype.sum_eq_single i (fun j hj => by
      rw [piIncl_apply, Pi.single_eq_of_ne hj, map_zero])]
    rw [piIncl_apply, Pi.single_eq_same]
  map_add' f f' := by
    funext i
    exact map_add (ConjHom.precomp (piIncl N i)) f f'

@[simp] theorem conjHomPiEquiv_apply {ι : Type} [Fintype ι] [DecidableEq ι]
    {N : ι → Type} [∀ i, AddCommGroup (N i)] {C : Type} [AddCommGroup C]
    (f : ConjHom (∀ i, N i) C) (i : ι) :
    conjHomPiEquiv N C f i = ConjHom.precomp (piIncl N i) f := rfl

@[simp] theorem conjHomPiEquiv_apply_apply {ι : Type} [Fintype ι] [DecidableEq ι]
    {N : ι → Type} [∀ i, AddCommGroup (N i)] {C : Type} [AddCommGroup C]
    (f : ConjHom (∀ i, N i) C) (i : ι) (a : N i) :
    conjHomPiEquiv N C f i a = f (Pi.single i a) := by
  rw [conjHomPiEquiv_apply, ConjHom.precomp_apply, piIncl_apply]

@[simp] theorem conjHomPiEquiv_symm_apply {ι : Type} [Fintype ι] [DecidableEq ι]
    {N : ι → Type} [∀ i, AddCommGroup (N i)] {C : Type} [AddCommGroup C]
    (F : ∀ i, ConjHom (N i) C) (x : ∀ i, N i) :
    (conjHomPiEquiv N C).symm F x = ∑ i, F i (x i) := rfl

theorem conjHomPiEquiv_equivariant {G : Type} [Group G] {ι : Type} [Fintype ι] [DecidableEq ι]
    {N : ι → Type} [∀ i, AddCommGroup (N i)] [∀ i, DistribMulAction G (N i)] {C : Type}
    [AddCommGroup C] [DistribMulAction G C] :
    Work.GroupCohomology.IsEquivariant G
      (conjHomPiEquiv N C : ConjHom (∀ i, N i) C →+ (∀ i, ConjHom (N i) C)) := by
  intro g f
  funext i
  refine ConjHom.ext_apply (fun a => ?_)
  show (g • f) (Pi.single i a) = (g • (conjHomPiEquiv N C f)) i a
  rw [ConjHom.smul_apply, Pi.smul_apply, ConjHom.smul_apply, conjHomPiEquiv_apply_apply]
  exact congrArg (fun c : ∀ j, N j => g • f c)
    (piIncl_equivariant (N := N) i g⁻¹ a).symm

theorem conjHomPiEquiv_symm_equivariant {G : Type} [Group G] {ι : Type} [Fintype ι]
    [DecidableEq ι] {N : ι → Type} [∀ i, AddCommGroup (N i)] [∀ i, DistribMulAction G (N i)]
    {C : Type} [AddCommGroup C] [DistribMulAction G C] :
    Work.GroupCohomology.IsEquivariant G
      ((conjHomPiEquiv N C).symm : (∀ i, ConjHom (N i) C) →+ ConjHom (∀ i, N i) C) := by
  intro g F
  refine (conjHomPiEquiv N C).injective ?_
  have h1 : (conjHomPiEquiv N C) ((conjHomPiEquiv N C).symm (g • F)) = g • F :=
    (conjHomPiEquiv N C).apply_symm_apply (g • F)
  have h2 : (conjHomPiEquiv N C) (g • (conjHomPiEquiv N C).symm F) = g • F :=
    (conjHomPiEquiv_equivariant (N := N) (C := C) g
      ((conjHomPiEquiv N C).symm F)).trans
      (congrArg (fun y => g • y) ((conjHomPiEquiv N C).apply_symm_apply F))
  exact h1.trans h2.symm

/-! ## `H²` of a product of coefficient modules -/

/-- The coordinate map `H²(G, ∏ᵢ Mᵢ) → ∏ᵢ H²(G, Mᵢ)`. -/
def h2PiCoordMap {G : Type} [TopologicalSpace G] [Group G] {ι : Type} [Fintype ι]
    (M : ι → Type) [∀ i, AddCommGroup (M i)] [∀ i, DistribMulAction G (M i)] :
    Work.AbsoluteKummer.H2 G (∀ i, M i) →+ (∀ i, Work.AbsoluteKummer.H2 G (M i)) :=
  AddMonoidHom.pi (fun i => Work.AbsoluteKummer.mapH2 (Pi.evalAddMonoidHom M i)
    (evalAddMonoidHom_equivariant (N := M) i))

/-- A `2`-cocycle with values in a product of modules whose coordinates are all coboundaries is a
coboundary. -/
theorem h2Pi_mem_B2_of_coords {G : Type} [TopologicalSpace G] [Group G] {ι : Type} [Fintype ι]
    {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, DistribMulAction G (M i)]
    {c : G × G → (∀ i, M i)} (h : ∀ i, (fun p => c p i) ∈ Work.AbsoluteKummer.B2 G (M i)) :
    c ∈ Work.AbsoluteKummer.B2 G (∀ i, M i) := by
  choose b hb hbeq using fun i => (Work.AbsoluteKummer.mem_B2_iff (fun p => c p i)).mp (h i)
  refine (Work.AbsoluteKummer.mem_B2_iff c).mpr ⟨fun g i => b i g, ?_, ?_⟩
  · rw [Work.AbsoluteKummer.mem_C1c_iff]
    intro g₀
    choose U hU hg₀U hconst using
      fun i => (Work.AbsoluteKummer.mem_C1c_iff (b i)).mp (hb i) g₀
    refine ⟨⋂ i, U i, isOpen_iInter_of_finite hU, Set.mem_iInter.mpr hg₀U, fun g hg => ?_⟩
    funext i
    exact hconst i g (Set.mem_iInter.mp hg i)
  · funext p i
    obtain ⟨g, k⟩ := p
    have h2 := congrFun (hbeq i) (g, k)
    rw [← h2]
    simp only [Work.GroupCohomology.d1_apply, Pi.sub_apply, Pi.add_apply, Pi.smul_apply]

/-- The coordinate map is injective. -/
theorem h2PiCoordMap_injective {G : Type} [TopologicalSpace G] [Group G] {ι : Type} [Fintype ι]
    (M : ι → Type) [∀ i, AddCommGroup (M i)] [∀ i, DistribMulAction G (M i)] :
    Function.Injective (h2PiCoordMap (G := G) M) := by
  have hker : (h2PiCoordMap (G := G) M).ker = ⊥ := by
    rw [AddSubgroup.eq_bot_iff_forall]
    intro x hx
    rw [AddMonoidHom.mem_ker] at hx
    obtain ⟨c, hc⟩ := QuotientAddGroup.mk'_surjective
      ((Work.AbsoluteKummer.B2 G (∀ i, M i)).comap
        (Work.AbsoluteKummer.Z2 G (∀ i, M i)).subtype) x
    rw [← hc] at hx ⊢
    change Work.AbsoluteKummer.H2π G (∀ i, M i) c = 0
    rw [Work.AbsoluteKummer.H2π_eq_zero_iff]
    refine h2Pi_mem_B2_of_coords (fun i => ?_)
    have h1 : Work.AbsoluteKummer.H2π G (M i)
        (Work.AbsoluteKummer.mapZ2 (Pi.evalAddMonoidHom M i)
          (evalAddMonoidHom_equivariant (N := M) i) c) = 0 := by
      have h2 : (h2PiCoordMap (G := G) M) (Work.AbsoluteKummer.H2π G (∀ i, M i) c) i = 0 := by
        simpa only [Work.AbsoluteKummer.H2π, Pi.zero_apply] using congrFun hx i
      rw [show (h2PiCoordMap (G := G) M) (Work.AbsoluteKummer.H2π G (∀ i, M i) c) i
            = Work.AbsoluteKummer.mapH2 (Pi.evalAddMonoidHom M i)
                (evalAddMonoidHom_equivariant (N := M) i)
                (Work.AbsoluteKummer.H2π G (∀ i, M i) c) from rfl] at h2
      rw [Work.AbsoluteKummer.mapH2_H2π] at h2
      exact h2
    rw [Work.AbsoluteKummer.H2π_eq_zero_iff] at h1
    rw [show (fun p : G × G => (c : G × G → (∀ i, M i)) p i) =
        (↑(Work.AbsoluteKummer.mapZ2 (Pi.evalAddMonoidHom M i)
          (evalAddMonoidHom_equivariant (N := M) i) c) : G × G → M i) from rfl]
    exact h1
  intro x y hxy
  have h0 : x - y = 0 := by
    rw [← AddSubgroup.mem_bot, ← hker]
    rw [AddMonoidHom.mem_ker, map_sub, hxy, sub_self]
  exact sub_eq_zero.mp h0

/-- The coordinate map is surjective, a preimage being the "gluing" of the coordinates. -/
theorem h2PiCoordMap_surjective {G : Type} [TopologicalSpace G] [Group G] {ι : Type} [Fintype ι]
    (M : ι → Type) [∀ i, AddCommGroup (M i)] [∀ i, DistribMulAction G (M i)] :
    Function.Surjective (h2PiCoordMap (G := G) M) := by
  intro y
  choose c hc using fun i => QuotientAddGroup.mk'_surjective
    ((Work.AbsoluteKummer.B2 G (M i)).comap (Work.AbsoluteKummer.Z2 G (M i)).subtype) (y i)
  have hZ : (fun p : G × G => fun i => (c i : G × G → M i) p)
      ∈ Work.AbsoluteKummer.Z2 G (∀ i, M i) := by
    rw [Work.AbsoluteKummer.mem_Z2_iff]
    constructor
    · intro g h k
      funext i
      exact ((Work.AbsoluteKummer.mem_Z2_iff (c i : G × G → M i)).mp (c i).2).1 g h k
    · intro p₀
      choose U hU hp₀ hconst using fun i =>
        ((Work.AbsoluteKummer.mem_Z2_iff (c i : G × G → M i)).mp (c i).2).2 p₀
      exact ⟨⋂ i, U i, isOpen_iInter_of_finite hU, Set.mem_iInter.mpr hp₀,
        fun p hp => funext fun i => hconst i p (Set.mem_iInter.mp hp i)⟩
  refine ⟨Work.AbsoluteKummer.H2π G (∀ i, M i) ⟨_, hZ⟩, ?_⟩
  funext i
  show (h2PiCoordMap (G := G) M) (Work.AbsoluteKummer.H2π G (∀ i, M i) ⟨_, hZ⟩) i = y i
  rw [show (h2PiCoordMap (G := G) M) (Work.AbsoluteKummer.H2π G (∀ i, M i) ⟨_, hZ⟩) i
        = Work.AbsoluteKummer.mapH2 (Pi.evalAddMonoidHom M i)
            (evalAddMonoidHom_equivariant (N := M) i)
            (Work.AbsoluteKummer.H2π G (∀ i, M i) ⟨_, hZ⟩) from rfl]
  rw [Work.AbsoluteKummer.mapH2_H2π, ← hc i]
  congr 1

/-- **`H²` of a product of coefficients is the product of the `H²`'s.** -/
def h2PiEquiv {G : Type} [TopologicalSpace G] [Group G] {ι : Type} [Fintype ι]
    (M : ι → Type) [∀ i, AddCommGroup (M i)] [∀ i, DistribMulAction G (M i)] :
    Work.AbsoluteKummer.H2 G (∀ i, M i) ≃+ (∀ i, Work.AbsoluteKummer.H2 G (M i)) :=
  AddEquiv.ofBijective (h2PiCoordMap (G := G) M)
    ⟨h2PiCoordMap_injective M, h2PiCoordMap_surjective M⟩

/-- The coordinate rule for the product decomposition of `H²`. -/
theorem h2PiEquiv_apply {G : Type} [TopologicalSpace G] [Group G] {ι : Type} [Fintype ι]
    {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, DistribMulAction G (M i)]
    (x : Work.AbsoluteKummer.H2 G (∀ i, M i)) (i : ι) :
    h2PiEquiv (G := G) M x i
      = Work.AbsoluteKummer.mapH2 (Pi.evalAddMonoidHom M i)
          (evalAddMonoidHom_equivariant (N := M) i) x := rfl

/-! ## The product reduction for `α²` -/

/-- The coefficient map `Hom_ℤ(∏ᵢ Nᵢ, C) → Hom_ℤ(Nᵢ, C)` is the `i`-th component of the product
identification. -/
theorem evalHom_comp_conjHomPiEquiv {ι : Type} [Fintype ι] [DecidableEq ι]
    {N : ι → Type} [∀ i, AddCommGroup (N i)] {C : Type}
    [AddCommGroup C] (i : ι) :
    (Pi.evalAddMonoidHom (fun i => ConjHom (N i) C) i).comp
        (conjHomPiEquiv N C : ConjHom (∀ i, N i) C →+ (∀ i, ConjHom (N i) C))
      = ConjHom.precomp (piIncl N i) := by
  refine AddMonoidHom.ext (fun f => ?_)
  refine ConjHom.ext_apply (fun a => ?_)
  show conjHomPiEquiv N C f i a = (ConjHom.precomp (piIncl N i)) f a
  rw [conjHomPiEquiv_apply_apply, ConjHom.precomp_apply, piIncl_apply]

/-- The composite `(eval i) ∘ conjHomPiEquiv` is equivariant. -/
theorem eval_comp_conjHomPiEquiv_equivariant {G : Type} [Group G] {ι : Type} [Fintype ι]
    [DecidableEq ι] {N : ι → Type} [∀ i, AddCommGroup (N i)] [∀ i, DistribMulAction G (N i)]
    {C : Type} [AddCommGroup C] [DistribMulAction G C] (i : ι) :
    Work.GroupCohomology.IsEquivariant G
      ((Pi.evalAddMonoidHom (fun i => ConjHom (N i) C) i).comp
        (conjHomPiEquiv N C : ConjHom (∀ i, N i) C →+ (∀ i, ConjHom (N i) C))) := by
  intro g F
  rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
    conjHomPiEquiv_equivariant (N := N) (C := C) g F]
  exact evalAddMonoidHom_equivariant (N := fun i => ConjHom (N i) C) i g
    (conjHomPiEquiv N C F)

/-- **The product reduction**: if `α²` is bijective for each `Nᵢ` then it is bijective for the
product `∏ᵢ Nᵢ`. -/
theorem alphaTwo_pi_bijective {G : Type} [TopologicalSpace G] [Group G] {ι : Type} [Fintype ι]
    [DecidableEq ι] {N : ι → Type} [∀ i, AddCommGroup (N i)] [∀ i, DistribMulAction G (N i)]
    {C : Type} [AddCommGroup C] [DistribMulAction G C]
    (h : ∀ i, Function.Bijective (alphaTwo (G := G) (N := N i) (C := C))) :
    Function.Bijective (alphaTwo (G := G) (N := ∀ i, N i) (C := C)) := by
  have hE : Work.GroupCohomology.IsEquivariant G
      (conjHomPiEquiv N C : ConjHom (∀ i, N i) C →+ (∀ i, ConjHom (N i) C)) :=
    conjHomPiEquiv_equivariant (N := N) (C := C)
  have hE' : Work.GroupCohomology.IsEquivariant G
      ((conjHomPiEquiv N C).symm : (∀ i, ConjHom (N i) C) →+ ConjHom (∀ i, N i) C) :=
    conjHomPiEquiv_symm_equivariant (N := N) (C := C)
  have hpre : ∀ i : ι,
      Work.GroupCohomology.IsEquivariant G (ConjHom.precomp (piIncl N i)) :=
    fun i => precomp_smul (C := C) (piIncl N i) (piIncl_equivariant (N := N) i)
  set Ψ : Work.AbsoluteKummer.H2 G (ConjHom (∀ i, N i) C) →+
      Work.AbsoluteKummer.H2 G (∀ i, ConjHom (N i) C) :=
    Work.AbsoluteKummer.mapH2 (conjHomPiEquiv N C : ConjHom (∀ i, N i) C →+
      (∀ i, ConjHom (N i) C)) hE with hΨ
  set Ψ' : Work.AbsoluteKummer.H2 G (∀ i, ConjHom (N i) C) →+
      Work.AbsoluteKummer.H2 G (ConjHom (∀ i, N i) C) :=
    Work.AbsoluteKummer.mapH2 ((conjHomPiEquiv N C).symm : (∀ i, ConjHom (N i) C) →+
      ConjHom (∀ i, N i) C) hE' with hΨ'
  have hΨr : Ψ.comp Ψ' = AddMonoidHom.id _ := by
    rw [hΨ, hΨ']
    exact mapH2_comp_symm_eq_id (conjHomPiEquiv N C) hE hE'
  have hΨl : Ψ'.comp Ψ = AddMonoidHom.id _ := by
    rw [hΨ, hΨ']
    exact mapH2_symm_comp_eq_id (conjHomPiEquiv N C) hE hE'
  have hΨ_inj : Function.Injective Ψ := by
    intro a b hab
    have h1 := congrArg (fun (φ : Work.AbsoluteKummer.H2 G (ConjHom (∀ i, N i) C) →+
        Work.AbsoluteKummer.H2 G (ConjHom (∀ i, N i) C)) => φ a) hΨl
    have h2 := congrArg (fun (φ : Work.AbsoluteKummer.H2 G (ConjHom (∀ i, N i) C) →+
        Work.AbsoluteKummer.H2 G (ConjHom (∀ i, N i) C)) => φ b) hΨl
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply] at h1 h2
    rw [hab] at h1
    rw [h1] at h2
    exact h2
  have hΨ_surj : Function.Surjective Ψ := by
    intro y
    refine ⟨Ψ' y, ?_⟩
    have h1 := congrArg (fun (φ : Work.AbsoluteKummer.H2 G (∀ i, ConjHom (N i) C) →+
        Work.AbsoluteKummer.H2 G (∀ i, ConjHom (N i) C)) => φ y) hΨr
    simpa only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply] using h1
  set Θ : Work.AbsoluteKummer.H2 G (∀ i, ConjHom (N i) C) ≃+
      (∀ i, Work.AbsoluteKummer.H2 G (ConjHom (N i) C)) :=
    h2PiEquiv (G := G) (fun i => ConjHom (N i) C) with hΘ
  have hΘ_inj : Function.Injective Θ.toAddMonoidHom := Θ.injective
  have hΘ_surj : Function.Surjective Θ.toAddMonoidHom := Θ.surjective
  set Φ : Work.AbsoluteKummer.H2 G (ConjHom (∀ i, N i) C) →+
      (∀ i, Work.AbsoluteKummer.H2 G (ConjHom (N i) C)) :=
    AddMonoidHom.pi (fun i => Work.AbsoluteKummer.mapH2 (ConjHom.precomp (piIncl N i))
      (hpre i)) with hΦ
  have hΦ_apply : ∀ (x : Work.AbsoluteKummer.H2 G (ConjHom (∀ i, N i) C)) (i : ι),
      Φ x i = Work.AbsoluteKummer.mapH2 (ConjHom.precomp (piIncl N i)) (hpre i) x :=
    fun _ _ => rfl
  have hΦ_fact : Φ = Θ.toAddMonoidHom.comp Ψ := by
    refine AddMonoidHom.ext (fun x => funext fun i => ?_)
    rw [hΦ_apply x i, AddMonoidHom.comp_apply, hΘ,
      show (h2PiEquiv (G := G) (fun i => ConjHom (N i) C)).toAddMonoidHom (Ψ x) i
        = (h2PiEquiv (G := G) (fun i => ConjHom (N i) C)) (Ψ x) i from rfl,
      h2PiEquiv_apply, hΨ]
    rw [← mapH2_comp (φ := (conjHomPiEquiv N C : ConjHom (∀ i, N i) C →+
        (∀ i, ConjHom (N i) C)))
      (ψ := Pi.evalAddMonoidHom (fun i => ConjHom (N i) C) i)
      (hφ := hE) (hψ := evalAddMonoidHom_equivariant (N := fun i => ConjHom (N i) C) i)
      (hc := eval_comp_conjHomPiEquiv_equivariant (N := N) (C := C) i) x]
    exact congrArg (fun (η : Work.AbsoluteKummer.H2 G (ConjHom (∀ i, N i) C) →+
        Work.AbsoluteKummer.H2 G (ConjHom (N i) C)) => η x)
      (mapH2_congr_map (G := G) (M := ConjHom (∀ i, N i) C) (N := ConjHom (N i) C)
        (evalHom_comp_conjHomPiEquiv (N := N) (C := C) i).symm
        (hpre i) (eval_comp_conjHomPiEquiv_equivariant (N := N) (C := C) i))
  have hΦ_inj : Function.Injective Φ := by
    rw [hΦ_fact]
    intro a b hab
    exact hΨ_inj (hΘ_inj hab)
  have hΦ_surj : Function.Surjective Φ := by
    rw [hΦ_fact]
    intro y
    obtain ⟨u, hu⟩ := hΘ_surj y
    obtain ⟨v, hv⟩ := hΨ_surj u
    refine ⟨v, ?_⟩
    exact (congrArg Θ.toAddMonoidHom hv).trans hu
  constructor
  · intro x y hxy
    refine hΦ_inj (funext fun i => ?_)
    refine (h i).1 ?_
    ext n
    rw [hΦ_apply x i, hΦ_apply y i]
    rw [alphaTwo_naturality (piIncl N i) (piIncl_equivariant (N := N) i) (hpre i) x n]
    rw [alphaTwo_naturality (piIncl N i) (piIncl_equivariant (N := N) i) (hpre i) y n]
    exact congrArg (fun (φ : ↥(Work.GroupCohomology.invariants G (∀ i, N i)) →+
        Work.AbsoluteKummer.H2 G C) =>
      φ (invariantsHom (piIncl N i) (piIncl_equivariant (N := N) i) n)) hxy
  · intro g
    have hg : ∀ i, ∃ x : Work.AbsoluteKummer.H2 G (ConjHom (N i) C),
        alphaTwo (G := G) (N := N i) (C := C) x
          = g.comp (invariantsHom (piIncl N i) (piIncl_equivariant (N := N) i)) :=
      fun i => (h i).2 _
    choose x hx using hg
    obtain ⟨z, hz⟩ := hΦ_surj (fun i => x i)
    refine ⟨z, ?_⟩
    ext n
    rw [invariants_pi_eq_sum (N := N) (piIncl_equivariant (N := N)) n, map_sum, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← alphaTwo_naturality (piIncl N i) (piIncl_equivariant (N := N) i) (hpre i) z
      ⟨(n : ∀ i, N i) i, coord_mem_invariants (N := N) n.2 i⟩]
    rw [← hΦ_apply z i, congrFun hz i, hx i]
    rfl

/-! ## Transfer of bijectivity along an additive equivalence -/

/-- If `e : N ≃+ N'` is an equivariant additive equivalence and `α²` is bijective for `N'`, then
it is bijective for `N`. -/
theorem alphaTwo_addEquiv_transfer {G : Type} [TopologicalSpace G] [Group G] {C : Type}
    [AddCommGroup C] [DistribMulAction G C] {N : Type} [AddCommGroup N] [DistribMulAction G N]
    {N' : Type} [AddCommGroup N'] [DistribMulAction G N']
    (e : N ≃+ N') (he : Work.GroupCohomology.IsEquivariant G (e : N →+ N'))
    (h : Function.Bijective (alphaTwo (G := G) (N := N') (C := C))) :
    Function.Bijective (alphaTwo (G := G) (N := N) (C := C)) := by
  have he' : Work.GroupCohomology.IsEquivariant G (e.symm : N' →+ N) := by
    intro g m
    have h1 : e ((e.symm : N' →+ N) (g • m)) = g • m := e.apply_symm_apply (g • m)
    have h2 : e (g • (e.symm : N' →+ N) m) = g • m := by
      have hstep : e (g • (e.symm : N' →+ N) m)
          = g • e ((e.symm : N' →+ N) m) := he g ((e.symm : N' →+ N) m)
      exact hstep.trans (congrArg (fun y => g • y) (e.apply_symm_apply m))
    exact e.injective (h1.trans h2.symm)
  have hpre : Work.GroupCohomology.IsEquivariant G (ConjHom.precomp (e : N →+ N')) :=
    precomp_smul (C := C) (e : N →+ N') he
  have hpre' : Work.GroupCohomology.IsEquivariant G (ConjHom.precomp (e.symm : N' →+ N)) :=
    precomp_smul (C := C) (e.symm : N' →+ N) he'
  have hsec : (Work.AbsoluteKummer.mapH2 (ConjHom.precomp (e : N →+ N')) hpre).comp
      (Work.AbsoluteKummer.mapH2 (ConjHom.precomp (e.symm : N' →+ N)) hpre')
      = AddMonoidHom.id (Work.AbsoluteKummer.H2 G (ConjHom N C)) := by
    refine AddMonoidHom.ext (fun y => ?_)
    exact Work.AbsoluteKummer.SES.H2_induction_on (M := ConjHom N C) y
      (C := fun z => (Work.AbsoluteKummer.mapH2 (ConjHom.precomp (e : N →+ N')) hpre)
        ((Work.AbsoluteKummer.mapH2 (ConjHom.precomp (e.symm : N' →+ N)) hpre') z) = z)
      (fun c => by
      rw [Work.AbsoluteKummer.mapH2_H2π, Work.AbsoluteKummer.mapH2_H2π]
      congr 1
      refine Subtype.ext (funext fun p => ?_)
      refine ConjHom.ext_apply (fun n => ?_)
      simp only [Work.AbsoluteKummer.mapZ2_apply, ConjHom.precomp_apply]
      exact congrArg (fun y : N => (c : G × G → ConjHom N C) p y) (e.symm_apply_apply n))
  have hinv_surj : Function.Surjective (invariantsHom (e : N →+ N') he) := by
    intro m
    refine ⟨⟨e.symm (m : N'), ?_⟩, Subtype.ext ?_⟩
    · intro g
      exact (he' g (m : N')).symm.trans
        (congrArg (fun y => (e.symm : N' →+ N) y) (m.2 g))
    · exact e.apply_symm_apply (m : N')
  have hinv_comp : ∀ n : ↥(Work.GroupCohomology.invariants G N),
      invariantsHom (e.symm : N' →+ N) he' (invariantsHom (e : N →+ N') he n) = n := by
    intro n
    exact Subtype.ext (e.symm_apply_apply (n : N))
  refine ⟨?_, ?_⟩
  · intro y₁ y₂ hy
    have hy₁ : Work.AbsoluteKummer.mapH2 (ConjHom.precomp (e : N →+ N')) hpre
        (Work.AbsoluteKummer.mapH2 (ConjHom.precomp (e.symm : N' →+ N)) hpre' y₁) = y₁ := by
      have h1 := congrArg (fun (φ : Work.AbsoluteKummer.H2 G (ConjHom N C) →+
          Work.AbsoluteKummer.H2 G (ConjHom N C)) => φ y₁) hsec
      simpa only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply] using h1
    have hy₂ : Work.AbsoluteKummer.mapH2 (ConjHom.precomp (e : N →+ N')) hpre
        (Work.AbsoluteKummer.mapH2 (ConjHom.precomp (e.symm : N' →+ N)) hpre' y₂) = y₂ := by
      have h1 := congrArg (fun (φ : Work.AbsoluteKummer.H2 G (ConjHom N C) →+
          Work.AbsoluteKummer.H2 G (ConjHom N C)) => φ y₂) hsec
      simpa only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply] using h1
    have key : ∀ n : ↥(Work.GroupCohomology.invariants G N),
        alphaTwo (G := G) (N := N') (C := C)
            (Work.AbsoluteKummer.mapH2 (ConjHom.precomp (e.symm : N' →+ N)) hpre' y₁)
            (invariantsHom (e : N →+ N') he n)
          = alphaTwo (G := G) (N := N') (C := C)
            (Work.AbsoluteKummer.mapH2 (ConjHom.precomp (e.symm : N' →+ N)) hpre' y₂)
            (invariantsHom (e : N →+ N') he n) := by
      intro n
      rw [← alphaTwo_naturality (e : N →+ N') he hpre
          (Work.AbsoluteKummer.mapH2 (ConjHom.precomp (e.symm : N' →+ N)) hpre' y₁) n,
        ← alphaTwo_naturality (e : N →+ N') he hpre
          (Work.AbsoluteKummer.mapH2 (ConjHom.precomp (e.symm : N' →+ N)) hpre' y₂) n,
        hy₁, hy₂]
      exact congrArg (fun (φ : ↥(Work.GroupCohomology.invariants G N) →+
        Work.AbsoluteKummer.H2 G C) => φ n) hy
    have hcleq : Work.AbsoluteKummer.mapH2 (ConjHom.precomp (e.symm : N' →+ N)) hpre' y₁
        = Work.AbsoluteKummer.mapH2 (ConjHom.precomp (e.symm : N' →+ N)) hpre' y₂ := by
      have : alphaTwo (G := G) (N := N') (C := C)
          (Work.AbsoluteKummer.mapH2 (ConjHom.precomp (e.symm : N' →+ N)) hpre' y₁)
          = alphaTwo (G := G) (N := N') (C := C)
            (Work.AbsoluteKummer.mapH2 (ConjHom.precomp (e.symm : N' →+ N)) hpre' y₂) := by
        ext m
        obtain ⟨n, hn⟩ := hinv_surj m
        rw [← hn]
        exact key n
      exact h.1 this
    rw [← hy₁, ← hy₂, hcleq]
  · intro g
    obtain ⟨x, hx⟩ := h.2 (g.comp (invariantsHom (e.symm : N' →+ N) he'))
    refine ⟨Work.AbsoluteKummer.mapH2 (ConjHom.precomp (e : N →+ N')) hpre x, ?_⟩
    ext n
    rw [alphaTwo_naturality (e : N →+ N') he hpre x n, hx]
    refine congrArg g (Subtype.ext ?_)
    exact e.symm_apply_apply (n : N)

/-! ## The linear-algebra reduction to a power of `ℤ/p` -/

/-- A finite module over `ℤ/p` is additively a power of the trivial module `ℤ/p`. -/
theorem exists_addEquiv_fin_trivMod {G : Type} [Group G] (p : ℕ) [Fact p.Prime] (N : Type)
    [AddCommGroup N] [Module (ZMod p) N] [Finite N] :
    ∃ n : ℕ, Nonempty (N ≃+ (Fin n → TrivMod G p)) :=
  ⟨Module.finrank (ZMod p) N, ⟨(Module.finBasis (ZMod p) N).equivFun.toAddEquiv⟩⟩

/-- The `G`-action on a power of `TrivMod G p` is trivial. -/
theorem smul_fin_trivMod_eq {G : Type} [Group G] (n p : ℕ) (g : G)
    (y : Fin n → TrivMod G p) : g • y = y := by
  funext i
  exact TrivMod.smul_eq G p g (y i)

/-! ## The trivial-action base case in full generality -/

/-- **The trivial-action base case of `α²` in full generality.**  If `α²` is bijective for the
trivial module `ℤ/p` (the Kummer computation of `AlphaTwoTrivModSurj`), then it is bijective for
*every* finite `G`-module of exponent `p` on which `G` acts trivially (such a module is an
`𝔽_p`-vector space `(ℤ/p)^n`, and `α²` is compatible with the corresponding direct-sum
decomposition; the product decomposition of `H²` is
`Work.AbsoluteKummer.H2Pi.nonempty_h2_pi_equiv`). -/
theorem alphaTwo_trivAction_of_trivMod {G : Type} [TopologicalSpace G] [Group G] (p : ℕ)
    [Fact p.Prime] {C : Type} [AddCommGroup C] [DistribMulAction G C]
    {N : Type} [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction G N]
    (htriv : ∀ (g : G) (n : N), g • n = n) [Finite N]
    (h : Function.Bijective
      (Work.SSGRoute.PT.alphaTwo (G := G) (N := Work.SSGRoute.PT.TrivMod G p) (C := C))) :
    Function.Bijective (Work.SSGRoute.PT.alphaTwo (G := G) (N := N) (C := C)) := by
  obtain ⟨n, ⟨e⟩⟩ := exists_addEquiv_fin_trivMod (G := G) p N
  have hpi : Function.Bijective
      (alphaTwo (G := G) (N := Fin n → TrivMod G p) (C := C)) :=
    alphaTwo_pi_bijective (G := G) (C := C) (N := fun _ : Fin n => TrivMod G p) (fun _ => h)
  refine alphaTwo_addEquiv_transfer (e := e) ?_ hpi
  intro g x
  show e (g • x) = g • e x
  rw [htriv g x]
  exact (smul_fin_trivMod_eq n p g (e x)).symm

end

end Work.SSGRoute.PT
