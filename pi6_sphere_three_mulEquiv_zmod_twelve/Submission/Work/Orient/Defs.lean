import Mathlib
import Submission.Work.Cohomology.localHomology
import Submission.Work.Cohomology.pd_plumbing
import Submission.Work.Cohomology.relChains_empty_homology_iso
import Submission.Work.Cohomology.local_generator_ball
import Submission.Work.ThomBordism.localGenDefs

set_option synthInstance.maxHeartbeats 400000

/-!
# ORIENT: the vocabulary of fundamental classes of compact manifolds

This file fixes the **vocabulary of the ORIENT chapter**: local homology groups, local classes,
fundamental classes (a global class whose localisations generate at every point), orientations
(a locally consistent family of local generators), and the relative version for a compact manifold
with boundary.

Everything is phrased in the workspace's singular (co)homology (`Submission/Work/Cohomology/`) and
in the excluded-set convention of `Work.ThomBordism.RelH`:

* `RelH M n A = (relChains M Aᶜ).homology n = H_n(M, M ∖ A)` (`A` is the *excluded* set),
* `LocH M n x = H_n(M, M ∖ {x})` — the local homology group at the point `x`,
* `relClass M n c K` — the image of a global class `c` in `H_n(M, M∖K)`,
* `locClass M n c x` — the image of `c` in the local group at `x`.

Main notions:

* `Work.Orient.IsFundClass M n c` — `c` is a **fundamental class**: its local class at every point
  generates the local group.  For the closed `8`-manifolds of area THOM this is *literally* the
  field `Work.ThomBordism.Man8.c_fund` (see `Submission/Work/Orient/Bridge.lean`).
* `Work.Orient.GenAt M n c K` — the same condition at a set `K`.
* `Work.Orient.Orientable n M` — `∃ c, IsFundClass M n c`.
* `Work.Orient.IsOrientFamily n M γ` — an **orientation** of `M` as a locally consistent family of
  local generators: every `γ x` generates `H_n(M, M∖{x})`, and over every coordinate ball `K` the
  classes `γ x`, `x ∈ K`, are the specialisations of one class of `H_n(M, M∖K)`.
* `Work.Orient.IsRelFundClass W n B w` — the relative version: `w ∈ H_n(W,B)` restricts to a local
  generator at every point *outside* `B` (in the applications `B = ∂W`, so at every interior point).

The existence and uniqueness theorems live in `Submission/Work/Orient/Closed.lean` (compact
manifolds without boundary) and `Submission/Work/Orient/Boundary.lean` (compact manifolds with
boundary); the bridge to the notions of area THOM (`Man8`, `NullBordismFamily`) is
`Submission/Work/Orient/Bridge.lean`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Orient

noncomputable section

variable {n : ℕ}

/-! ## Local homology and local classes -/

/-- **The relative homology `H_n(M, M∖A)` of the pair with excluded set `A`** (the ORIENT name for
`Work.ThomBordism.RelH`). -/
abbrev RelH (M : TopCat) (n : ℕ) (A : Set M) : ModuleCat ℤ :=
  (Work.Cohomology.relChains M Aᶜ).homology n

/-- **The local homology group** `H_n(M, M ∖ {x})` of a space `M` at the point `x`. -/
abbrev LocH (M : TopCat) (n : ℕ) (x : M) : ModuleCat ℤ :=
  (Work.Cohomology.relChains M {y : M | y ≠ x}).homology n

/-- **The restriction `H_n(M, M∖B) → H_n(M, M∖A)`** for `A ⊆ B` (enlarging the excluded set). -/
abbrev resRelH (M : TopCat) (n : ℕ) {A B : Set M} (h : A ⊆ B) : RelH M n B →ₗ[ℤ] RelH M n A :=
  Work.ThomBordism.RelHmap M n h

/-- **A coordinate closed ball of `M`** (the chart image of a closed ball): the pieces of the cover
of `Work.ThomBordism.convexCover`. -/
abbrev IsCoordBall (n : ℕ) (M : TopCat) [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (K : Set M) : Prop :=
  Work.ThomBordism.IsCoordBall n M K

/-- **The class of `c` at the excluded set `K`**: the image of `c ∈ H_n(M)` in `H_n(M, M∖K)`. -/
def relClass (M : TopCat) (n : ℕ) (c : (Work.Cohomology.singularChains ℤ M).homology n)
    (K : Set M) : Work.ThomBordism.RelH M n K :=
  Work.Cohomology.relLocClass M n c K

/-- **The local class** at `x` of a global class `c ∈ H_n(M)`. -/
def locClass (M : TopCat) (n : ℕ) (c : (Work.Cohomology.singularChains ℤ M).homology n)
    (x : M) : LocH M n x :=
  relClass M n c {x}

/-- `LocH M n x` is `RelH M n {x}`, definitionally. -/
theorem LocH_eq_RelH (M : TopCat) (n : ℕ) (x : M) : LocH M n x = Work.ThomBordism.RelH M n {x} := rfl

/-- `locClass` is the local class at `{x}`, definitionally. -/
theorem locClass_eq_relClass (M : TopCat) (n : ℕ)
    (c : (Work.Cohomology.singularChains ℤ M).homology n) (x : M) :
    locClass M n c x = relClass M n c {x} := rfl

/-- **`c` is a fundamental class** (`c` is an orientation class): its local class at every point of
`M` generates the local group `H_n(M, M∖{x})`.

For a closed `8`-manifold `V` of area THOM this is exactly the field `Man8.c_fund`. -/
def IsFundClass (M : TopCat) (n : ℕ) (c : (Work.Cohomology.singularChains ℤ M).homology n) : Prop :=
  ∀ x : M, Submodule.span ℤ {locClass M n c x} = ⊤

/-- **`c` generates at the set `K`**: its image in `H_n(M, M∖K)` generates. -/
def GenAt (M : TopCat) (n : ℕ) (c : (Work.Cohomology.singularChains ℤ M).homology n)
    (K : Set M) : Prop :=
  Submodule.span ℤ {relClass M n c K} = ⊤

/-- **Orientability** (of an `n`-manifold, in the form used in this chapter): `H_n(M; ℤ)` contains a
fundamental class.  By `Work.Orient.exists_fundClass_of_isOrientFamily`
(`Submission/Work/Orient/Closed.lean`) this is what an orientation (an oriented atlas) supplies, and
by `Work.Orient.eq_of_locClass_eq` it is unique for a connected `M`. -/
def Orientable (n : ℕ) (M : TopCat) : Prop :=
  ∃ c : (Work.Cohomology.singularChains ℤ M).homology n, IsFundClass M n c

/-! ## Relative fundamental classes (manifolds with boundary) -/

/-- The inclusion of relative chain complexes `C_*(X,A) ⟶ C_*(X,B)` for `A ⊆ B`.  (This is the
ORIENT copy of `Work.ThomBordism.relChainsIncl`, with the *same* body, so that `relPunct` below is
definitionally the map appearing in the field `Work.ThomBordism.NullBordismFamily.w_fund`.) -/
def relChainsIncl (X : TopCat) {A B : Set X} (h : A ⊆ B) :
    Work.Cohomology.relChains X A ⟶ Work.Cohomology.relChains X B :=
  Work.Cohomology.relChainsMapOf X X A B (𝟙 X) (TopCat.ofHom ⟨fun a => ⟨a.1, h a.2⟩,
    Continuous.subtype_mk continuous_subtype_val (fun a => h a.2)⟩) (by ext a; rfl)

/-- The restriction `H_n(W,B) → H_n(W, W∖{x})` for `x ∉ B`, i.e. the map of relative chain
complexes `C_*(W,B) ⟶ C_*(W, W∖{x})`.  (This is the map appearing in the field
`Work.ThomBordism.NullBordismFamily.w_fund`; `Work.Orient.relPunct_eq_relChainsInclPunct` in
`Submission/Work/Orient/Bridge.lean` shows that the two are the same map.) -/
def relPunct (W : TopCat) (B : Set W) (x : W) (hx : x ∉ B) :
    Work.Cohomology.relChains W B ⟶ Work.Cohomology.relChains W {y : W | y ≠ x} :=
  relChainsIncl W (A := B) (B := {y : W | y ≠ x}) (fun y hy hyx => hx (hyx ▸ hy))

/-- **The relative fundamental class property**: `w ∈ H_n(W,B)` restricts to a local generator of
`H_n(W, W∖{x})` at every point `x` outside `B`.  For `B = ∂W` this says that `w` is a local
generator at every interior point (there are no conditions at the boundary points, where the local
group `H_n(W, W∖{x})` vanishes — see `Work.Orient.Boundary.localHomology_corner`). -/
def IsRelFundClass (W : TopCat) (n : ℕ) (B : Set W)
    (w : (Work.Cohomology.relChains W B).homology n) : Prop :=
  ∀ (x : W) (hx : x ∉ B),
    Submodule.span ℤ {(HomologicalComplex.homologyMap (relPunct W B x hx) n).hom w} = ⊤

/-- **Orientation reversal** preserves the property of being a relative fundamental class. -/
theorem IsRelFundClass.neg {W : TopCat} {n : ℕ} {B : Set W}
    {w : (Work.Cohomology.relChains W B).homology n} (h : IsRelFundClass W n B w) :
    IsRelFundClass W n B (-w) := by
  intro x hx
  have hmap : (HomologicalComplex.homologyMap (relPunct W B x hx) n).hom (-w)
      = -((HomologicalComplex.homologyMap (relPunct W B x hx) n).hom w) := map_neg _ _
  rw [hmap]
  have hs : ({-((HomologicalComplex.homologyMap (relPunct W B x hx) n).hom w)} :
      Set (LocH W n x)) =
      -({((HomologicalComplex.homologyMap (relPunct W B x hx) n).hom w)} :
        Set (LocH W n x)) := by
    ext y; simp
  rw [hs, Submodule.span_neg]
  exact h x hx

/-! ## Orientations as locally consistent families of local generators -/

/-- **An orientation of `M`, as a locally consistent family of local generators.**

`γ x ∈ H_n(M, M∖{x})` is a generator for every `x`, and over every coordinate ball `K`
(`Work.ThomBordism.IsCoordBall n M K`, the chart image of a closed ball) the classes `γ x`,
`x ∈ K`, are all specialisations of one class of `H_n(M, M∖K)`.

This is the representation of an orientation that a smooth oriented manifold supplies (the local
generator induced by an oriented chart, the transition functions preserving it) and that the
preimage-orientation construction produces (`Submission/Work/Orient/Preimage.lean`). -/
def IsOrientFamily (n : ℕ) (M : TopCat) [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (γ : (x : M) → LocH M n x) : Prop :=
  (∀ x : M, Submodule.span ℤ {γ x} = ⊤) ∧
    ∀ K : Set M, Work.ThomBordism.IsCoordBall n M K →
      ∃ a : Work.ThomBordism.RelH M n K, ∀ x (hx : x ∈ K),
        Work.ThomBordism.RelHmap M n (Set.singleton_subset_iff.mpr hx) a = γ x

/-- **The family of local classes of a fundamental class is an orientation family.**  (The
converse, that every orientation family comes from a fundamental class, is
`Work.Orient.exists_fundClass_of_isOrientFamily` in `Closed.lean`.) -/
theorem isOrientFamily_locClass (n : ℕ) (M : TopCat)
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (c : (Work.Cohomology.singularChains ℤ M).homology n) (hc : IsFundClass M n c) :
    IsOrientFamily n M (fun x => locClass M n c x) := by
  refine ⟨hc, fun K _ => ⟨relClass M n c K, fun x hx => ?_⟩⟩
  show Work.ThomBordism.RelHmap M n (Set.singleton_subset_iff.mpr hx) (relClass M n c K)
      = locClass M n c x
  rw [locClass_eq_relClass]
  exact Work.Cohomology.relLocClass_restrict M n c (Set.singleton_subset_iff.mpr hx)

/-! ## API of the local classes -/

/-- The local class map is additive in the global class. -/
theorem locClass_add (M : TopCat) (n : ℕ)
    (c c' : (Work.Cohomology.singularChains ℤ M).homology n) (x : M) :
    locClass M n (c + c') x = locClass M n c x + locClass M n c' x :=
  map_add _ _ _

/-- The local class map is subtractive in the global class. -/
theorem locClass_sub (M : TopCat) (n : ℕ)
    (c c' : (Work.Cohomology.singularChains ℤ M).homology n) (x : M) :
    locClass M n (c - c') x = locClass M n c x - locClass M n c' x :=
  map_sub _ _ _

/-- The local class map is `ℤ`-linear in the global class. -/
theorem locClass_zsmul (M : TopCat) (n : ℕ)
    (c : (Work.Cohomology.singularChains ℤ M).homology n) (k : ℤ) (x : M) :
    locClass M n (k • c) x = k • locClass M n c x :=
  map_zsmul _ _ _

/-- The local class of `0` is `0`. -/
@[simp] theorem locClass_zero (M : TopCat) (n : ℕ) (x : M) :
    locClass M n 0 x = 0 :=
  map_zero _

/-- **Orientation reversal**: the local class of `-c` is the negative of the local class of `c`. -/
theorem locClass_neg (M : TopCat) (n : ℕ)
    (c : (Work.Cohomology.singularChains ℤ M).homology n) (x : M) :
    locClass M n (-c) x = - locClass M n c x :=
  map_neg _ _

/-- The class of `c` at `K` restricts to the local class at `x ∈ K`. -/
theorem relClass_restrict (M : TopCat) (n : ℕ)
    (c : (Work.Cohomology.singularChains ℤ M).homology n) {K : Set M} {x : M} (hx : x ∈ K) :
    Work.ThomBordism.RelHmap M n (Set.singleton_subset_iff.mpr hx) (relClass M n c K)
      = locClass M n c x := by
  rw [locClass_eq_relClass]
  exact Work.Cohomology.relLocClass_restrict M n c (Set.singleton_subset_iff.mpr hx)

/-- **A fundamental class generates over every coordinate ball.** -/
theorem genAt_of_isFundClass {M : TopCat} [CompactSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (hn : 1 ≤ n)
    {c : (Work.Cohomology.singularChains ℤ M).homology n} (hc : IsFundClass M n c)
    {K : Set M} (hK : Work.ThomBordism.IsCoordBall n M K) : GenAt M n c K := by
  obtain ⟨z, r, hr, hball, rfl⟩ := hK
  exact Work.Cohomology.local_generator_ball n hn M c (fun x => hc x) z r hr hball

/-! ## Orientation reversal -/

/-- **Orientation reversal of an orientation family.** -/
theorem IsOrientFamily.neg {M : TopCat} [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {γ : (x : M) → LocH M n x} (h : IsOrientFamily n M γ) :
    IsOrientFamily n M (fun x => - γ x) := by
  refine ⟨fun x => ?_, fun K hK => ?_⟩
  · have hs : ({-γ x} : Set (LocH M n x)) = -({γ x} : Set (LocH M n x)) := by ext y; simp
    rw [hs, Submodule.span_neg]
    exact h.1 x
  · obtain ⟨a, ha⟩ := h.2 K hK
    refine ⟨-a, fun x hx => ?_⟩
    have h1 : (Work.ThomBordism.RelHmap M n (Set.singleton_subset_iff.mpr hx)) (-a)
        = -((Work.ThomBordism.RelHmap M n (Set.singleton_subset_iff.mpr hx)) a) :=
      map_neg _ _
    rw [h1, ha x hx]

/-- **Orientation reversal** preserves the property of being a fundamental class. -/
theorem IsFundClass.neg {M : TopCat}
    {c : (Work.Cohomology.singularChains ℤ M).homology n} (h : IsFundClass M n c) :
    IsFundClass M n (-c) := by
  intro x
  have hs : ({-locClass M n c x} : Set (LocH M n x)) = -({locClass M n c x} : Set (LocH M n x)) := by
    ext y; simp
  rw [locClass_neg, hs, Submodule.span_neg]
  exact h x

/-- **Orientation reversal** preserves orientability. -/
theorem Orientable.neg {M : TopCat} {n : ℕ} (h : Orientable n M) : Orientable n M := by
  obtain ⟨c, hc⟩ := h
  refine ⟨-c, fun x => ?_⟩
  have hs : ({-locClass M n c x} : Set (LocH M n x)) = -({locClass M n c x} : Set (LocH M n x)) := by
    ext y; simp
  rw [locClass_neg, hs, Submodule.span_neg]
  exact hc x

end

end Work.Orient
