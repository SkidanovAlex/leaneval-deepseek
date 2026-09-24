import Mathlib
import Submission.Work.Spine.Main

/-!
# Torsion-freeness of the abelianization of `π₁` of an open Riemann surface

The target of this file is

`Work.Mori.torsionFree_abelianization_riemannSurface`:

the abelianization `H₁(X;ℤ) = π₁(X,x)^{ab}` of the fundamental group of a connected,
second countable, **non-compact** complex one-manifold (a non-compact Riemann surface) is
**torsion-free**.

## Mathematical content and architecture

The classical proof is the abelian half of the theorem of Johansson/Stallings that the fundamental
group of an open surface is *free*: `π₁` of a connected non-compact surface is a free group, and the
abelianization of a free group is a free abelian group, hence torsion-free.

Two routes to the target are set up in this file.

**Route 1 (freeness, wired).**  `isMulTorsionFree_abelianization_of_isFreeGroup` proves, in full
generality, that the abelianization of a *free* group is torsion-free (transported from the
torsion-freeness of `FreeAbelianGroup α ≃+ (α →₀ ℤ)`).  Consequently the target follows immediately
from freeness of `π₁` of the open surface, i.e. from
`Work.Spine.isFreeGroup_fundamentalGroup_of_noncompact` (the topological step of Hubbard's
Theorem 1.1.2, `Submission/Work/Spine/DESIGN.md`) — this is the dependency of the target as proved
below.

**Route 2 (colimits, machinery ready).**  Much less than freeness suffices for torsion-freeness,
namely: the target is a *filtered colimit* of the abelianizations at the members of a compact
exhaustion, and torsion-freeness passes to filtered colimits.  The two ingredients are proved here
in full generality:

* `exists_forall_mem_of_exhaustion` (+ the path and homotopy forms): in a compact exhaustion whose
  *interiors* cover the space, every continuous map from a compact space (`C(I,X)`,`C(I²,X)`) lands
  in a single member — the *cofinality* that makes `π₁(X,x)` the filtered colimit of the
  `π₁(K n,x)`;
* `isMulTorsionFree_abelianization_of_directedColimit`: **torsion-freeness of the abelianization
  passes to directed colimits of groups** — if a group `G` is the directed colimit of groups `H n`
  (surjectivity and "eventually killed kernel") and each `Abelianization (H n)` is torsion-free,
  then so is `Abelianization G`.  Its heart is the classical fact
  (`commutator_le_iSup_map` + `abelianization_eventual_kernel`) that the commutator subgroup of the
  colimit is the union of the images of the commutator subgroups, so that a relation valid in the
  colimit is already valid at some finite stage.

This second route reduces the target to the *local* statement that the abelianization of `π₁` of
*each* member of a compact exhaustion is torsion-free - a statement still weaker than freeness, and
the natural "compact bordered surface" input of the spine programme
(`Submission/Work/Spine/CompactBordered/NOTES_plan_crux.md`).  In particular
`isMulTorsionFree_abelianization_of_directedColimit` bypasses the *hard* final step ("the limit of a
nested sequence of free groups is free") of the design notes in `Submission/Work/Spine/DESIGN.md`:
for torsion-freeness no compatible-basis argument is needed.

## What remains for Route 2

To instantiate `isMulTorsionFree_abelianization_of_directedColimit` one needs, for `X` as in the
target:

* an exhaustion `K : ℕ → Set X` (`x ∈ K 0`, monotone, interiors covering — `CompactExhaustion`
  provides one) whose members `K n` are *compact bordered subsurfaces* of `X` — for instance finite
  unions of discs of the disc tiling `Commons.Topology.Surface.exists_locallyFinite_disk_tiling`;
* the *local* freeness/torsion-freeness input for each member, i.e. the "compact bordered surface"
  theorem of `Submission/Work/Spine/CompactBordered/` (for such a member the abelianization of `π₁`
  is free abelian, being the abelianization of a free group);
* the base point bookkeeping (`FundamentalGroup.map` of the inclusions, at the various base points
  `⟨x, _⟩`), for which the functoriality lemmas `pathQuotient_map_map` and
  `fundamentalGroup_map_comp` above are the algebraic input; the `hker` hypothesis of the colimit
  lemma is then exactly the statement that a loop of `K n` that is null-homotopic in `X` is
  null-homotopic in `K m` for some `m`, which follows from `exists_forall_mem_of_homotopy`.

The reduction (Route 1) is unconditional and is the dependency used below; Route 2 is the strict
weakening of it that the torsion-freeness statement really needs.
-/

namespace Work.Mori

open Subgroup
open scoped commutatorElement

/-- `(α →₀ ℤ)` is torsion-free as an additive monoid: an integer linear combination of a finitely
supported function that vanishes must be the zero function. -/
theorem isAddTorsionFree_finsupp_int (α : Type*) : IsAddTorsionFree (α →₀ ℤ) := by
  refine ⟨fun n hn => ?_⟩
  intro f g hfg
  ext a
  have h : (n • (f a) : ℤ) = n • (g a) := by
    have h2 := congr_fun (congrArg DFunLike.coe hfg) a
    simpa using h2
  exact IsAddTorsionFree.nsmul_right_injective hn h

/-- The free abelian group on `α` — Mathlib's `Additive (Abelianization (FreeGroup α))` — is
torsion-free, transported from `α →₀ ℤ` along `FreeAbelianGroup.equivFinsupp`. -/
theorem isAddTorsionFree_freeAbelianGroup (α : Type*) : IsAddTorsionFree (FreeAbelianGroup α) := by
  have hfin : IsAddTorsionFree (α →₀ ℤ) := isAddTorsionFree_finsupp_int α
  refine ⟨fun n hn => ?_⟩
  intro x y hxy
  have hxy' : n • x = n • y := hxy
  have h' : (FreeAbelianGroup.equivFinsupp α) x = (FreeAbelianGroup.equivFinsupp α) y := by
    refine IsAddTorsionFree.nsmul_right_injective (M := α →₀ ℤ) hn ?_
    have h3 : (FreeAbelianGroup.equivFinsupp α) (n • x) =
        (FreeAbelianGroup.equivFinsupp α) (n • y) := by rw [hxy']
    rw [map_nsmul, map_nsmul] at h3
    exact h3
  exact (FreeAbelianGroup.equivFinsupp α).injective h'

/-- **The abelianization of a free group is torsion-free.** -/
theorem isMulTorsionFree_abelianization_freeGroup (α : Type*) :
    IsMulTorsionFree (Abelianization (FreeGroup α)) := by
  have hFAG : IsAddTorsionFree (FreeAbelianGroup α) := isAddTorsionFree_freeAbelianGroup α
  have hFAG' : IsAddTorsionFree (Additive (Abelianization (FreeGroup α))) := hFAG
  refine ⟨fun n hn => ?_⟩
  intro a b hab
  have hab' : a ^ n = b ^ n := hab
  have h1 : (n • Additive.ofMul a : Additive (Abelianization (FreeGroup α))) =
      n • Additive.ofMul b := by
    show Additive.ofMul (a ^ n) = Additive.ofMul (b ^ n)
    rw [hab']
  exact Additive.ofMul.injective
    (IsAddTorsionFree.nsmul_right_injective hn
      (M := Additive (Abelianization (FreeGroup α))) h1)

/-- **The abelianization of a free group is torsion-free**: if `G` is a free group then
`Abelianization G` has no non-trivial elements of finite order. -/
theorem isMulTorsionFree_abelianization_of_isFreeGroup {G : Type*} [Group G] [IsFreeGroup G] :
    IsMulTorsionFree (Abelianization G) := by
  have hfree : IsMulTorsionFree (Abelianization (FreeGroup (IsFreeGroup.Generators G))) :=
    isMulTorsionFree_abelianization_freeGroup (IsFreeGroup.Generators G)
  have e : Abelianization G ≃* Abelianization (FreeGroup (IsFreeGroup.Generators G)) :=
    (IsFreeGroup.toFreeGroup G).abelianizationCongr
  exact Function.Injective.isMulTorsionFree e.toMonoidHom e.injective

/-! ## The commutator subgroup of a directed colimit

The classical "the commutator subgroup of a filtered colimit of groups is the union of the images of
the commutator subgroups" is the key algebraic step in deducing torsion-freeness of `π₁^{ab}` of a
union from torsion-freeness of the `π₁^{ab}` of the pieces: a relation valid in the colimit is
already valid in some finite stage.  We prove the inclusion (the direction that is used); the reverse
inclusion is trivial. -/

/-- **The commutator subgroup of a directed colimit of groups is contained in the union of the
images of the commutator subgroups.**  If every element of `G` is the image of an element of some
`H n` (under a compatible cocone `φ` of a directed system `ψ`), then `commutator G` is contained in
`⨆ n, (commutator (H n)).map (φ n)`. -/
theorem abelianization_map_of {G H : Type*} [Group G] [Group H] (f : G →* H) (x : G) :
    Abelianization.map f (Abelianization.of x) = Abelianization.of (f x) := rfl

theorem mem_commutator_iff {G : Type*} [Group G] (x : G) :
    x ∈ commutator G ↔ Abelianization.of x = 1 := by
  rw [← Abelianization.ker_of G, MonoidHom.mem_ker]

theorem map_commutator_le {G H : Type*} [Group G] [Group H] (f : G →* H) :
    (commutator G).map f ≤ commutator H := by
  rw [commutator_eq_closure, commutator_eq_closure, Subgroup.map_le_iff_le_comap]
  rw [Subgroup.closure_le]
  rintro _ ⟨x, y, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_comap, map_commutatorElement]
  exact Subgroup.subset_closure ⟨f x, f y, rfl⟩

theorem map_commutator_mono {G : Type*} [Group G] {H : ℕ → Type*} [∀ n, Group (H n)]
    (psi : (n m : ℕ) → n ≤ m → H n →* H m)
    (phi : (n : ℕ) → H n →* G)
    (hphipsi : ∀ {n m : ℕ} (hnm : n ≤ m), (phi m).comp (psi n m hnm) = phi n)
    {n m : ℕ} (hnm : n ≤ m) :
    (commutator (H n)).map (phi n) ≤ (commutator (H m)).map (phi m) := by
  calc (commutator (H n)).map (phi n)
      = (commutator (H n)).map ((phi m).comp (psi n m hnm)) := by rw [hphipsi hnm]
    _ = ((commutator (H n)).map (psi n m hnm)).map (phi m) := by rw [Subgroup.map_map]
    _ ≤ (commutator (H m)).map (phi m) := Subgroup.map_mono (map_commutator_le (psi n m hnm))

theorem commutator_le_iSup_map {G : Type*} [Group G] {H : ℕ → Type*} [∀ n, Group (H n)]
    (psi : (n m : ℕ) → n ≤ m → H n →* H m)
    (phi : (n : ℕ) → H n →* G)
    (hphipsi : ∀ {n m : ℕ} (hnm : n ≤ m), (phi m).comp (psi n m hnm) = phi n)
    (hsurj : ∀ g : G, ∃ n, ∃ x : H n, phi n x = g) :
    commutator G ≤ ⨆ n, (commutator (H n)).map (phi n) := by
  rw [commutator_eq_closure, Subgroup.closure_le]
  rintro _ ⟨x, y, rfl⟩
  obtain ⟨n, x', hx⟩ := hsurj x
  obtain ⟨m, y', hy⟩ := hsurj y
  obtain ⟨k, hnk, hmk⟩ : ∃ k, n ≤ k ∧ m ≤ k := ⟨max n m, le_max_left _ _, le_max_right _ _⟩
  have hx' : phi k (psi n k hnk x') = x := by
    rw [← hx, ← hphipsi hnk]; rfl
  have hy' : phi k (psi m k hmk y') = y := by
    rw [← hy, ← hphipsi hmk]; rfl
  have hcomm : ⁅psi n k hnk x', psi m k hmk y'⁆ ∈ commutator (H k) := by
    rw [commutator_eq_closure]
    exact Subgroup.subset_closure ⟨_, _, rfl⟩
  refine Subgroup.mem_iSup_of_mem k ?_
  have h2 := Subgroup.mem_map_of_mem (phi k) hcomm
  rwa [map_commutatorElement, hx', hy'] at h2

/-- **Cofinality of the abelianization: an element of a stage that dies in the colimit dies at a
later stage.** -/
theorem abelianization_eventual_kernel {G : Type*} [Group G] {H : ℕ → Type*} [∀ n, Group (H n)]
    (psi : (n m : ℕ) → n ≤ m → H n →* H m)
    (phi : (n : ℕ) → H n →* G)
    (hphipsi : ∀ {n m : ℕ} (hnm : n ≤ m), (phi m).comp (psi n m hnm) = phi n)
    (hpsi : ∀ {n m k : ℕ} (hnm : n ≤ m) (hmk : m ≤ k),
      (psi m k hmk).comp (psi n m hnm) = psi n k (hnm.trans hmk))
    (hsurj : ∀ g : G, ∃ n, ∃ x : H n, phi n x = g)
    (hker : ∀ n, ∃ m, ∃ hnm : n ≤ m, ∀ x : H n, phi n x = 1 → psi n m hnm x = 1)
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
  obtain ⟨M', hMM', hkM'⟩ := hker M
  have hkill := hkM' (psi k M hMk c * (psi n M hMn z)⁻¹) h3
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

end Work.Mori

namespace Work.Mori

theorem isMulTorsionFree_abelianization_of_directedColimit
    {G : Type*} [Group G] {H : ℕ → Type*} [∀ n, Group (H n)]
    (psi : (n m : ℕ) → n ≤ m → H n →* H m)
    (phi : (n : ℕ) → H n →* G)
    (hphipsi : ∀ {n m : ℕ} (hnm : n ≤ m), (phi m).comp (psi n m hnm) = phi n)
    (hpsi : ∀ {n m k : ℕ} (hnm : n ≤ m) (hmk : m ≤ k),
      (psi m k hmk).comp (psi n m hnm) = psi n k (hnm.trans hmk))
    (hsurj : ∀ g : G, ∃ n, ∃ x : H n, phi n x = g)
    (hker : ∀ n, ∃ m, ∃ hnm : n ≤ m, ∀ x : H n, phi n x = 1 → psi n m hnm x = 1)
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
      abelianization_eventual_kernel psi phi hphipsi hpsi hsurj hker n _ hbN
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


/-! ## Two functoriality lemmas for the path/homotopy API

The statements below are the functoriality of `Path.Homotopic.Quotient.map` and of
`FundamentalGroup.map`; they are the bookkeeping needed to compare the fundamental groups of the
members of an exhaustion with that of the union (and are not in Mathlib in this form). -/

/-- Functoriality of `Path.Homotopic.Quotient.map`. -/
theorem pathQuotient_map_map {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {x₀ x₁ : X} (P : Path.Homotopic.Quotient x₀ x₁)
    (f : C(X, Y)) (g : C(Y, Z)) :
    (P.map f).map g = P.map (g.comp f) := by
  induction P using Quotient.inductionOn with
  | _ p =>
    simp only [Path.Homotopic.Quotient.map, Quotient.map_mk, Path.map_map]
    congr 2

/-- Functoriality of `FundamentalGroup.map`. -/
theorem fundamentalGroup_map_comp {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : C(X, Y)) (g : C(Y, Z)) (x : X) :
    FundamentalGroup.map (g.comp f) x
      = (FundamentalGroup.map g (f x)).comp (FundamentalGroup.map f x) := by
  ext a
  simp only [MonoidHom.comp_apply, FundamentalGroup.map_apply]
  rw [pathQuotient_map_map]

/-- Equal base points give canonically isomorphic fundamental groups. -/
noncomputable def fundamentalGroupCongr {X : Type*} [TopologicalSpace X] {x y : X} (h : x = y) :
    FundamentalGroup X x ≃* FundamentalGroup X y := by
  subst h
  exact MulEquiv.refl _

/-- The inclusion-induced map `π₁(K, x) →* π₁(X, x)` for a subspace `K ⊆ X` and `x ∈ K`. -/
noncomputable def fundamentalGroupSubtypeMap {X : Type*} [TopologicalSpace X] (K : Set X)
    (x : X) (hx : x ∈ K) :
    FundamentalGroup ↥K ⟨x, hx⟩ →* FundamentalGroup X x :=
  (fundamentalGroupCongr rfl).toMonoidHom.comp
    (FundamentalGroup.map (⟨Subtype.val, continuous_subtype_val⟩ : C(↥K, X)) ⟨x, hx⟩)

/-- The inclusion-induced map `π₁(K, x) →* π₁(L, x)` for subspaces `K ⊆ L` of `X` and `x ∈ K`. -/
noncomputable def fundamentalGroupSubtypeMapOfSubset {X : Type*} [TopologicalSpace X] {K L : Set X}
    (hKL : K ⊆ L) (x : X) (hx : x ∈ K) :
    FundamentalGroup ↥K ⟨x, hx⟩ →* FundamentalGroup ↥L ⟨x, hKL hx⟩ :=
  (fundamentalGroupCongr (Subtype.ext rfl)).toMonoidHom.comp
    (FundamentalGroup.map (⟨fun y => ⟨y.1, hKL y.2⟩,
      Continuous.subtype_mk continuous_subtype_val _⟩ : C(↥K, ↥L)) ⟨x, hx⟩)

/-! ## Cofinality of a compact exhaustion

The two lemmas below are the *general* form of the cofinality statements that the planar case
(`Work.Spine.Plane.exists_polyK_superset_of_path`, `..._of_homotopy`) proves for the dyadic
polyomino exhaustion: in any compact exhaustion `(K n)` whose *interiors* cover the space, every
continuous map from a compact space — in particular every path and every path homotopy — lands in a
single member `K n`.  They are the input of every "`π₁` is the filtered colimit of the `π₁(K n)`"
argument for an open surface. -/

/-- **Cofinality of a compact exhaustion.** If `(K n)` is an increasing sequence of closed sets whose
interiors cover `X`, then every continuous map from a compact space into `X` lands in some `K n`.

(For `CompactExhaustion K` one has `K n ⊆ interior (K (n+1))`, so the hypothesis is automatic.) -/
theorem exists_forall_mem_of_exhaustion {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace Y] (K : ℕ → Set X) (hmono : Monotone K)
    (hint : ⋃ n, interior (K n) = Set.univ) (f : C(Y, X)) : ∃ n, ∀ y, f y ∈ K n := by
  have hcover : (Set.univ : Set Y) ⊆ ⋃ n, f ⁻¹' (interior (K n)) := by
    intro y _
    have hy : f y ∈ ⋃ n, interior (K n) := by rw [hint]; exact Set.mem_univ _
    simpa using hy
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun n => f ⁻¹' interior (K n))
    (fun n => isOpen_interior.preimage f.continuous) hcover
  refine ⟨t.sup id, fun y => ?_⟩
  have hy := ht (Set.mem_univ y)
  simp only [Set.mem_iUnion, Set.mem_preimage] at hy ⊢
  obtain ⟨n, hnt, hny⟩ := hy
  exact hmono (Finset.le_sup (f := id) hnt) (interior_subset hny)

/-- **Every path lies in a single member of a compact exhaustion.** -/
theorem exists_forall_mem_of_path {X : Type*} [TopologicalSpace X] (K : ℕ → Set X)
    (hmono : Monotone K) (hint : ⋃ n, interior (K n) = Set.univ) (γ : C(Set.Icc (0:ℝ) 1, X)) :
    ∃ n, ∀ t, γ t ∈ K n :=
  exists_forall_mem_of_exhaustion K hmono hint γ

/-- **Every path homotopy lies in a single member of a compact exhaustion.**  This is the
cofinality statement that turns `π₁` of the union into the filtered colimit of the `π₁ (K n)`. -/
theorem exists_forall_mem_of_homotopy {X : Type*} [TopologicalSpace X] (K : ℕ → Set X)
    (hmono : Monotone K) (hint : ⋃ n, interior (K n) = Set.univ)
    (F : C(Set.Icc (0:ℝ) 1 × Set.Icc (0:ℝ) 1, X)) : ∃ n, ∀ q, F q ∈ K n :=
  exists_forall_mem_of_exhaustion K hmono hint F

/-- **The abelianization of the fundamental group of a non-compact Riemann surface is
torsion-free.**

This is the abelian half of Johansson/Stallings: `π₁(X,x)` is free for `X` a connected second
countable non-compact surface, and the abelianization of a free group is free abelian, hence
torsion-free.

SUPPLY NOTE.  The remaining input is `IsFreeGroup (FundamentalGroup X x)`, i.e. the topological
step of Hubbard's Theorem 1.1.2 (`Work.Spine.isFreeGroup_fundamentalGroup_of_noncompact`, whose
subproject is the one described in `Submission/Work/Spine/DESIGN.md`).  With that instance in
scope the proof is the two-line `isMulTorsionFree_abelianization_of_isFreeGroup` followed by
`IsMulTorsionFree.pow_left_injective`. -/
theorem torsionFree_abelianization_riemannSurface
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hX : ¬ CompactSpace X) (x : X) (a : Abelianization (FundamentalGroup X x)) (n : ℕ) (hn : n ≠ 0) :
    a ^ n = 1 → a = 1 := by
  -- The topological step of Hubbard, Theorem 1.1.2 (Johansson/Stallings): `π₁` of a connected
  -- second countable non-compact surface is free.  This is the deliverable of the subproject
  -- `Submission/Work/Spine/` (see `Submission/Work/Spine/DESIGN.md`); the present file is the
  -- "abelian half" of that step, and closes as soon as the freeness theorem is unconditional.
  haveI hspine : IsFreeGroup (FundamentalGroup X x) :=
    Work.Spine.isFreeGroup_fundamentalGroup_of_noncompact hX x
  haveI : IsMulTorsionFree (Abelianization (FundamentalGroup X x)) :=
    isMulTorsionFree_abelianization_of_isFreeGroup
  intro h
  exact IsMulTorsionFree.pow_left_injective hn (by simpa using h)

end Work.Mori
