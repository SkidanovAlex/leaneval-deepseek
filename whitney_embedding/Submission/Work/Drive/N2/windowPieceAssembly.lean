import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.Drive.N2.GoodDrawingFamily
import Submission.Work.Drive.N2.goodDrawingOn_of_modelPullback

/-!
# The window piece of the compact `n = 2` movie: the assembly of the two halves (H8 lane)

The lead's window design (`Submission/Work/Drive/N2Lead/NOTES_LEAD_window.md`, 01:10) draws the
window of a critical value `c` as a *two-piece* map

    `x ↦ if x ∈ K then W (Ξ x) else Park x`

where

* `K := connectedComponentIn (f ⁻¹' Ioo (c - η) (c + η)) p` is the critical component of the slab
  (open, and with open complement inside the slab);
* `W ∘ Ξ` is the *near* piece: `W = S ∘ Φ_i` is the model pulled back by the window diffeo `Φ_i`,
  and `Ξ z = Φ* (ζ (f z) - f z, z)` is the frozen-time transport which makes the piece agree with the
  collars (`ζ ≡ c ∓ η/2` on the collars);
* `Park` is the *far* piece: the parked band picture transported by the single flow `Φ*`, drawn on
  the rest of the slab.

The two halves live in the two half-spaces `x₀ < 0` (models) and `x₀ > 0` (parking spots), which is
what separates them on the level sets.

This file contains the *purely logical* half of the construction, in the exact shape the assembly
`Work.Drive.N2.levelSeparatingMap_of_windowHybrids` consumes:

* `Work.Drive.N2.GoodDrawingOnK` — the rows of a drawing of the *preimage of `K`*;
* `Work.Drive.N2.goodDrawingOnK_of_modelPullback` — the near rows from a model embedding `S` and the
  window map `Ψ` (`goodDrawingOn_of_modelPullback` restricted to `K`);
* `Work.Drive.N2.windowPiece_goodDrawing` — **the gluing**: the two-piece map is a `GoodDrawingOn`
  as soon as the near piece satisfies `GoodDrawingOnK`, the far piece is a `GoodDrawingOn` on the
  value set, and the two pieces are separated by the sign of the coordinate `0`.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set Function Filter

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M]

/-- **The rows of a drawing of a *part* of `M`.**  This is `GoodDrawingOn` with the smoothness and
separation rows required only at the points of the open set `K`: the map `g` is smooth on
`K ∩ f ⁻¹' A`, its differential is injective on `ker (df)` there, and it separates the points of
the `f`-levels inside `K ∩ f ⁻¹' A`. -/
def GoodDrawingOnK (f : M → ℝ) (K : Set M) (A : Set ℝ)
    (g : M → EuclideanSpace ℝ (Fin 3)) : Prop :=
  (∀ x : M, x ∈ K → f x ∈ A → ContMDiffAt (𝓡 2) (𝓡 3) ∞ g x) ∧
  (∀ x : M, x ∈ K → f x ∈ A → ∀ v : TangentSpace (𝓡 2) x,
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 → mfderiv (𝓡 2) (𝓡 3) g x v = 0 → v = 0) ∧
  (∀ x y : M, x ∈ K → y ∈ K → f x ∈ A → f y ∈ A → f x = f y → g x = g y → x = y)

/-- `GoodDrawingOn` is the special case `K = univ` of `GoodDrawingOnK`. -/
lemma goodDrawingOnK_univ {f : M → ℝ} {A : Set ℝ} {g : M → EuclideanSpace ℝ (Fin 3)}
    (h : GoodDrawingOn f A g) : GoodDrawingOnK f univ A g :=
  ⟨fun x _ hx => h.1 x hx, fun x _ hx => h.2.1 x hx, fun x y _ _ hx hy => h.2.2 x y hx hy⟩

/-- `GoodDrawingOnK` from the unlocalised rows. -/
lemma goodDrawingOnK_of_rows {f : M → ℝ} {A : Set ℝ} {K : Set M}
    {g : M → EuclideanSpace ℝ (Fin 3)}
    (hsm : ∀ x : M, f x ∈ A → ContMDiffAt (𝓡 2) (𝓡 3) ∞ g x)
    (himm : ∀ x : M, f x ∈ A → ∀ v : TangentSpace (𝓡 2) x,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 → mfderiv (𝓡 2) (𝓡 3) g x v = 0 → v = 0)
    (hinj : ∀ x y : M, f x ∈ A → f y ∈ A → f x = f y → g x = g y → x = y) :
    GoodDrawingOnK f K A g :=
  ⟨fun x _ hx => hsm x hx, fun x _ hx => himm x hx, fun x y _ _ hx hy => hinj x y hx hy⟩

/-- **The near rows of the window, from the model.**  If `S : N → ℝ³` is an injective immersion of
the model surface and `Ψ : M → N` is the window map (the composite of the window diffeo `Φ_i` with
the freeze transport `Ξ`), then `S ∘ Ψ` satisfies the rows of a drawing of the part `K` as soon as
`Ψ` is injective on the `f`-levels of `A` inside `K` and immersive on `ker (df)` there.  This is
`Work.Drive.N2.goodDrawingOn_of_modelPullback` with every row restricted to `K`. -/
theorem goodDrawingOnK_of_modelPullback {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) N] [IsManifold (𝓡 2) ∞ N]
    {f : M → ℝ} {K : Set M} {A : Set ℝ} (S : N → EuclideanSpace ℝ (Fin 3)) (Psi : M → N)
    (hSsm : ContMDiff (𝓡 2) (𝓡 3) ∞ S) (hSinj : Function.Injective S)
    (hSimm : ∀ y : N, Function.Injective (mfderiv (𝓡 2) (𝓡 3) S y))
    (hPsm : ∀ x : M, x ∈ K → f x ∈ A → ContMDiffAt (𝓡 2) (𝓡 2) ∞ Psi x)
    (hPinj : ∀ x y : M, x ∈ K → y ∈ K → f x ∈ A → f y ∈ A → f x = f y → Psi x = Psi y → x = y)
    (hPimm : ∀ x : M, x ∈ K → f x ∈ A → ∀ v : TangentSpace (𝓡 2) x,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 → mfderiv (𝓡 2) (𝓡 2) Psi x v = 0 → v = 0) :
    GoodDrawingOnK f K A (fun x => S (Psi x)) := by
  have hn : ((∞ : WithTop ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  refine ⟨?_, ?_, ?_⟩
  · intro x hxK hxA
    exact (hSsm.contMDiffAt).comp x (hPsm x hxK hxA)
  · intro x hxK hxA v hv hvS
    have hmd : MDifferentiableAt (𝓡 2) (𝓡 2) Psi x := (hPsm x hxK hxA).mdifferentiableAt hn
    have hms : MDifferentiableAt (𝓡 2) (𝓡 3) S (Psi x) := hSsm.contMDiffAt.mdifferentiableAt hn
    have hcomp := mfderiv_comp_apply (I := 𝓡 2) (I' := 𝓡 2) (I'' := 𝓡 3)
      (f := Psi) (g := S) x hms hmd v
    have hzero : mfderiv (𝓡 2) (𝓡 3) S (Psi x) (mfderiv (𝓡 2) (𝓡 2) Psi x v) = 0 := by
      rw [← hcomp]; exact hvS
    exact hPimm x hxK hxA v hv ((hSimm (Psi x)) (hzero.trans (map_zero _).symm))
  · intro x y hxK hyK hxA hyA hfxy hSeq
    exact hPinj x y hxK hyK hxA hyA hfxy (hSinj hSeq)

open Classical in
/-- **The gluing of the two halves of the window piece.**

Let `A` be the value set of the window, `K` the (open) part of `M` drawn by the *near* piece `g`, and
`Park` the (globally defined) *far* piece, whose rows on the value set `A` are `GoodDrawingOn f A
Park`.  Suppose

* `K` is open, and `K` is open in the value set in the sense that every point outside `K` with
  `f x ∈ A` has a neighbourhood contained in `Kᶜ` (for `K` a connected component of the slab this is
  `IsOpen (slab \ K)`, since `slab` is open);
* the near piece satisfies the rows of `GoodDrawingOnK f K A g`;
* the two pieces are separated by the sign of the coordinate `0`: `(g x) 0 < 0` for `x ∈ K ∩ f ⁻¹' A`
  and `0 < (Park x) 0` for `x ∉ K` with `f x ∈ A`.

Then `x ↦ if x ∈ K then g x else Park x` is a `GoodDrawingOn f A`.

The proof is a case split on membership in `K`; the only cross case is the sign separation. -/
theorem windowPiece_goodDrawing {f : M → ℝ} {A : Set ℝ} {K : Set M}
    (hKopen : IsOpen K)
    (hKout : ∀ x : M, x ∉ K → f x ∈ A → ∀ᶠ y in 𝓝 x, y ∉ K)
    {g Park : M → EuclideanSpace ℝ (Fin 3)}
    (hg : GoodDrawingOnK f K A g) (hPark : GoodDrawingOn f A Park)
    (hsigng : ∀ x : M, x ∈ K → f x ∈ A → (g x) 0 < 0)
    (hsignPark : ∀ x : M, x ∉ K → f x ∈ A → 0 < (Park x) 0) :
    GoodDrawingOn f A (fun x => if x ∈ K then g x else Park x) := by
  have hpiece_eq : ∀ x : M, x ∈ K → (fun y : M => if y ∈ K then g y else Park y) =ᶠ[𝓝 x] g := by
    intro x hx
    filter_upwards [hKopen.mem_nhds hx] with y hy
    simp only [hy, if_pos]
  have hpiece_eq' : ∀ x : M, x ∉ K → f x ∈ A →
      (fun y : M => if y ∈ K then g y else Park y) =ᶠ[𝓝 x] Park := by
    intro x hx hxA
    filter_upwards [hKout x hx hxA] with y hy
    rw [if_neg hy]
  refine ⟨?_, ?_, ?_⟩
  · intro x hxA
    by_cases hx : x ∈ K
    · exact ((hg.1 x hx hxA).congr_of_eventuallyEq (hpiece_eq x hx))
    · exact ((hPark.1 x hxA).congr_of_eventuallyEq (hpiece_eq' x hx hxA))
  · intro x hxA v hv hvpiece
    by_cases hx : x ∈ K
    · have h : mfderiv (𝓡 2) (𝓡 3) (fun y : M => if y ∈ K then g y else Park y) x
          = mfderiv (𝓡 2) (𝓡 3) g x := (hpiece_eq x hx).mfderiv_eq
      rw [h] at hvpiece
      exact hg.2.1 x hx hxA v hv hvpiece
    · have h : mfderiv (𝓡 2) (𝓡 3) (fun y : M => if y ∈ K then g y else Park y) x
          = mfderiv (𝓡 2) (𝓡 3) Park x := (hpiece_eq' x hx hxA).mfderiv_eq
      rw [h] at hvpiece
      exact hPark.2.1 x hxA v hv hvpiece
  · intro x y hxA hyA hfxy hpiece
    have hx0 : (fun z : M => if z ∈ K then g z else Park z) x
        = if x ∈ K then g x else Park x := rfl
    have hy0 : (fun z : M => if z ∈ K then g z else Park z) y
        = if y ∈ K then g y else Park y := rfl
    rw [hx0, hy0] at hpiece
    by_cases hx : x ∈ K
    · rw [if_pos hx] at hpiece
      by_cases hy : y ∈ K
      · rw [if_pos hy] at hpiece
        exact hg.2.2 x y hx hy hxA hyA hfxy hpiece
      · rw [if_neg hy] at hpiece
        have h1 := hsigng x hx hxA
        have h2 := hsignPark y hy hyA
        rw [hpiece] at h1
        linarith
    · rw [if_neg hx] at hpiece
      by_cases hy : y ∈ K
      · rw [if_pos hy] at hpiece
        have h1 := hsignPark x hx hxA
        have h2 := hsigng y hy hyA
        rw [hpiece] at h1
        linarith
      · rw [if_neg hy] at hpiece
        exact hPark.2.2 x y hxA hyA hfxy hpiece

end Work.Drive.N2

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set Function Filter

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M]

/-! ## The frozen-time transport `Ξ` of the window piece

The window design draws the near piece as `W ∘ Ξ`, where `W` is the model boundary picture of the
component `K` and

    `Ξ z = Φ* (ζ (f z) - f z, z)`

is the transport of `z` along the single flow `Φ*` for the *frozen time* `ζ (f z) - f z`.  The rows
below are the ones the near piece consumes:

* `contMDiff_xiMap` — `Ξ` is smooth;
* `mfderiv_xiMap_ker` — on `ker (df)` the differential of `Ξ` is the frozen-time transport
  `d (Φ* (ζ (f x) - f x, ·))`: the time component of the graph derivative vanishes along `ker df`;
* `injective_mfderiv_timeShift` — the frozen-time transport has injective differential (it is a
  diffeomorphism);
* `xiMap_injOn_level` — at a fixed level of `f`, `Ξ` is injective.

Consequently `S ∘ Φ_i ∘ Ξ` inherits the rows of `goodDrawingOnK_of_modelPullback` from the model
embedding `S`, the window diffeo `Φ_i` and these three rows (see
`Submission/Work/Drive/N2/NOTES_windowPiece_ASSEMBLY_H8.md`). -/

/-- The **frozen-time transport** of the window piece: flow `z` for the time which would bring its
value to the frozen value `ζ (f z)`. -/
noncomputable def xiMap (Φ : ℝ × M → M) (ζ : ℝ → ℝ) (f : M → ℝ) : M → M :=
  fun z => Φ (ζ (f z) - f z, z)

lemma xiMap_apply (Φ : ℝ × M → M) (ζ : ℝ → ℝ) (f : M → ℝ) (z : M) :
    xiMap Φ ζ f z = Φ (ζ (f z) - f z, z) := rfl

/-- `Ξ` fixes the points of the frozen band `|f - c| ≤ η/4`, on which `ζ` is the identity. -/
lemma xiMap_eq_self (Φ : ℝ × M → M) (ζ : ℝ → ℝ) (f : M → ℝ) (hΦ0 : ∀ x : M, Φ (0, x) = x)
    {c η : ℝ} (hζ : ∀ t : ℝ, |t - c| ≤ η / 4 → ζ t = t)
    {z : M} (hz : |f z - c| ≤ η / 4) : xiMap Φ ζ f z = z := by
  rw [xiMap_apply, hζ (f z) hz, sub_self]
  exact hΦ0 z

/-- **`Ξ` is smooth.** -/
lemma contMDiff_xiMap {f : M → ℝ} {Φ : ℝ × M → M} {ζ : ℝ → ℝ}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (hΦ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞ Φ)
    (hζ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ ζ) :
    ContMDiff (𝓡 2) (𝓡 2) ∞ (xiMap Φ ζ f) := by
  have hgraph : ContMDiff (𝓡 2) ((𝓘(ℝ, ℝ)).prod (𝓡 2)) ∞
      (fun z : M => (ζ (f z) - f z, z)) :=
    ((hζ.comp hf).sub hf).prodMk contMDiff_id
  exact hΦ.comp hgraph

/-! ### The graph of a time function -/

set_option backward.isDefEq.respectTransparency false in
/-- The *time* component of the derivative of the graph map `z ↦ (τ z, z)`. -/
lemma mfderiv_prodGraph_fst {τ : M → ℝ} (hτ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ τ)
    (x : M) (v : TangentSpace (𝓡 2) x) :
    (mfderiv (𝓡 2) ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (fun z : M => (τ z, z)) x v).1
      = mfderiv (𝓡 2) 𝓘(ℝ, ℝ) τ x v := by
  have hn : ((∞ : WithTop ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hmd := (hτ.prodMk contMDiff_id).mdifferentiableAt (x := x) hn
  have hc := mfderiv_comp_apply (I := 𝓡 2) (I' := (𝓘(ℝ, ℝ)).prod (𝓡 2)) (I'' := 𝓘(ℝ, ℝ))
    (f := fun z : M => (τ z, z)) (g := Prod.fst) (x := x) mdifferentiableAt_fst hmd v
  have h1 : (Prod.fst ∘ fun z : M => (τ z, z)) = τ := rfl
  rw [h1] at hc
  have h2 : mfderiv ((𝓘(ℝ, ℝ)).prod (𝓡 2)) 𝓘(ℝ, ℝ) Prod.fst (τ x, x)
      = ContinuousLinearMap.fst ℝ (TangentSpace 𝓘(ℝ, ℝ) (τ x)) (TangentSpace (𝓡 2) x) :=
    mfderiv_fst
  rw [h2] at hc
  exact (rfl : (mfderiv (𝓡 2) ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (fun z : M => (τ z, z)) x v).1
      = (ContinuousLinearMap.fst ℝ (TangentSpace 𝓘(ℝ, ℝ) (τ x)) (TangentSpace (𝓡 2) x))
          (mfderiv (𝓡 2) ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (fun z : M => (τ z, z)) x v)).trans hc.symm

set_option backward.isDefEq.respectTransparency false in
/-- The *space* component of the derivative of the graph map `z ↦ (τ z, z)`. -/
lemma mfderiv_prodGraph_snd {τ : M → ℝ} (hτ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ τ)
    (x : M) (v : TangentSpace (𝓡 2) x) :
    (mfderiv (𝓡 2) ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (fun z : M => (τ z, z)) x v).2 = v := by
  have hn : ((∞ : WithTop ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hmd := (hτ.prodMk contMDiff_id).mdifferentiableAt (x := x) hn
  have hc := mfderiv_comp_apply (I := 𝓡 2) (I' := (𝓘(ℝ, ℝ)).prod (𝓡 2)) (I'' := 𝓡 2)
    (f := fun z : M => (τ z, z)) (g := Prod.snd) (x := x) mdifferentiableAt_snd hmd v
  have h1 : (Prod.snd ∘ fun z : M => (τ z, z)) = (fun z : M => z) := rfl
  rw [h1] at hc
  have h2 : mfderiv ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 2) Prod.snd (τ x, x)
      = ContinuousLinearMap.snd ℝ (TangentSpace 𝓘(ℝ, ℝ) (τ x)) (TangentSpace (𝓡 2) x) :=
    mfderiv_snd
  rw [h2] at hc
  have hid : mfderiv (𝓡 2) (𝓡 2) (fun z : M => z) x v = v := by
    change mfderiv (𝓡 2) (𝓡 2) id x v = v
    rw [mfderiv_id]
    rfl
  rw [hid] at hc
  exact (rfl : (mfderiv (𝓡 2) ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (fun z : M => (τ z, z)) x v).2
      = (ContinuousLinearMap.snd ℝ (TangentSpace 𝓘(ℝ, ℝ) (τ x)) (TangentSpace (𝓡 2) x))
          (mfderiv (𝓡 2) ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (fun z : M => (τ z, z)) x v)).trans hc.symm

set_option backward.isDefEq.respectTransparency false in
/-- **The frozen-time differential.**  For a smooth time function `τ` whose differential kills `v`,
the transport `z ↦ Φ (τ z, z)` has at `x` the same differential as its *frozen slice*
`z ↦ Φ (τ x, z)`: the time component of the graph derivative vanishes on `v`, so only the space
component survives. -/
lemma mfderiv_frozenTime {τ : M → ℝ} {Φ : ℝ × M → M}
    (hΦ : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 2) ∞ Φ) (hτ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ τ)
    (x : M) (v : TangentSpace (𝓡 2) x)
    (hτv : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) τ x v = 0) :
    mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (τ z, z)) x v
      = mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (τ x, z)) x v := by
  have hn : ((∞ : WithTop ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hG : ContMDiff (𝓡 2) ((𝓘(ℝ, ℝ)).prod (𝓡 2)) ∞ (fun z : M => (τ z, z)) :=
    hτ.prodMk contMDiff_id
  have hmdΦ : MDifferentiableAt ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 2) Φ (τ x, x) :=
    hΦ.contMDiffAt.mdifferentiableAt hn
  have hchain := mfderiv_comp_apply (I := 𝓡 2) (I' := (𝓘(ℝ, ℝ)).prod (𝓡 2)) (I'' := 𝓡 2)
    (f := fun z : M => (τ z, z)) (g := Φ) (x := x) hmdΦ
    (hG.contMDiffAt.mdifferentiableAt hn) v
  simp only [Function.comp_def] at hchain
  rw [hchain]
  have hsplit := mfderiv_prod_eq_add_apply (f := Φ) (p := (τ x, x))
    (v := mfderiv (𝓡 2) ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (fun z : M => (τ z, z)) x v) hmdΦ
  rw [hsplit]
  have hw1 : (mfderiv (𝓡 2) ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (fun z : M => (τ z, z)) x v).1 = 0 := by
    rw [mfderiv_prodGraph_fst hτ x v, hτv]
  have hw2 : (mfderiv (𝓡 2) ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (fun z : M => (τ z, z)) x v).2 = v :=
    mfderiv_prodGraph_snd hτ x v
  rw [hw1, hw2]
  rw [map_zero, zero_add]

set_option backward.isDefEq.respectTransparency false in
/-- **The frozen slice of a flow is a diffeomorphism in the space variable**, hence has injective
differential. -/
lemma injective_mfderiv_timeShift {Φ : ℝ × M → M}
    (hΦ : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 2) ∞ Φ)
    (hΦ0 : ∀ x : M, Φ (0, x) = x)
    (hΦcomp : ∀ (s t : ℝ) (x : M), Φ (s, Φ (t, x)) = Φ (s + t, x)) (t : ℝ) (x : M) :
    Function.Injective (mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (t, z)) x) := by
  have hn : ((∞ : WithTop ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hmd1 : MDifferentiableAt (𝓡 2) (𝓡 2) (fun z : M => Φ (t, z)) x :=
    (hΦ.comp (contMDiff_const.prodMk contMDiff_id)).contMDiffAt.mdifferentiableAt hn
  have hmd2 : MDifferentiableAt (𝓡 2) (𝓡 2) (fun z : M => Φ (-t, z)) (Φ (t, x)) :=
    (hΦ.comp (contMDiff_const.prodMk contMDiff_id)).contMDiffAt.mdifferentiableAt hn
  have hgen : ∀ a : TangentSpace (𝓡 2) x,
      mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (-t, z)) (Φ (t, x))
        (mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (t, z)) x a) = a := by
    intro a
    have hcomp := mfderiv_comp_apply (I := 𝓡 2) (I' := 𝓡 2) (I'' := 𝓡 2)
      (f := fun z : M => Φ (t, z)) (g := fun z : M => Φ (-t, z)) (x := x) hmd2 hmd1 a
    simp only [Function.comp_def] at hcomp
    have hleft : mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (-t, Φ (t, z))) x a = a := by
      have hid : (fun z : M => Φ (-t, Φ (t, z))) = id := by
        funext z
        rw [hΦcomp, neg_add_cancel]
        exact hΦ0 z
      rw [hid, mfderiv_id]
      rfl
    exact hcomp.symm.trans hleft
  intro u w huw
  rw [← hgen u, ← hgen w, huw]

set_option backward.isDefEq.respectTransparency false in
/-- **The differential of `Ξ` on the level directions is the frozen-time transport.**

This is `Work.Drive.N2.mfderiv_transport_self` with an arbitrary smooth *frozen time function* `ζ`
in place of the level shift `f x - f ·`: for `v ∈ ker (df)` the derivative of the time component
`ζ (f ·) - f ·` vanishes, so the only contribution of the graph map `z ↦ (ζ (f z) - f z, z)` to the
derivative of `Ξ` is the space component (this is `mfderiv_frozenTime`). -/
lemma mfderiv_xiMap_ker {f : M → ℝ} {Φ : ℝ × M → M} {ζ : ℝ → ℝ}
    (hΦ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞ Φ)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (hζ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ ζ)
    (x : M) (v : TangentSpace (𝓡 2) x)
    (hv : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0) :
    mfderiv (𝓡 2) (𝓡 2) (xiMap Φ ζ f) x v
      = mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (ζ (f x) - f x, z)) x v := by
  have hn : ((∞ : WithTop ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hτ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun z : M => ζ (f z) - f z) := (hζ.comp hf).sub hf
  have hτv : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun z : M => ζ (f z) - f z) x v = 0 := by
    have hζsub : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ => ζ t - t) := hζ.sub contMDiff_id
    have hcomp : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun z : M => ζ (f z) - f z) x v
        = mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => ζ t - t) (f x)
            (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v) := by
      have h := mfderiv_comp_apply (I := 𝓡 2) (I' := 𝓘(ℝ, ℝ)) (I'' := 𝓘(ℝ, ℝ))
        (f := f) (g := fun t : ℝ => ζ t - t) (x := x)
        (hζsub.contMDiffAt.mdifferentiableAt hn) (hf.contMDiffAt.mdifferentiableAt hn) v
      simpa only [Function.comp_def] using h
    rw [hcomp, hv, map_zero]
  exact mfderiv_frozenTime hΦ hτ x v hτv

/-- **`Ξ` is injective on the level sets of `f`**: two points of the same level whose frozen-time
transports coincide are equal (the transport is the time `ζ (f x) - f x` of the flow applied to
both, and the flow is a bijection in the space variable). -/
lemma xiMap_injOn_level {Φ : ℝ × M → M} {ζ : ℝ → ℝ} {f : M → ℝ}
    (hΦ0 : ∀ x : M, Φ (0, x) = x)
    (hΦcomp : ∀ (s t : ℝ) (x : M), Φ (s, Φ (t, x)) = Φ (s + t, x))
    {x y : M} (hf : f x = f y) (h : xiMap Φ ζ f x = xiMap Φ ζ f y) : x = y := by
  have ht : ζ (f x) - f x = ζ (f y) - f y := by rw [hf]
  have h' : Φ (ζ (f x) - f x, x) = Φ (ζ (f x) - f x, y) := by
    have h1 : Φ (ζ (f x) - f x, x) = Φ (ζ (f y) - f y, y) := h
    rwa [← ht] at h1
  calc x = Φ (-(ζ (f x) - f x), Φ (ζ (f x) - f x, x)) := by
        rw [hΦcomp, neg_add_cancel, hΦ0]
    _ = Φ (-(ζ (f x) - f x), Φ (ζ (f x) - f x, y)) := by rw [h']
    _ = y := by rw [hΦcomp, neg_add_cancel, hΦ0]

end Work.Drive.N2

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set Function Filter

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M]

/-! ## The near piece `S ∘ Φ_i ∘ Ξ`

The near piece of the window is `x ↦ S (Φ_i (Ξ x))`, where

* `S : N → ℝ³` is the embedding of the model surface;
* `Φ_i : M → N` is the window diffeo (`windowDiffeo`), required here only through its smoothness
  and the **injectivity of its differential** (it is a diffeo onto its image);
* `Ξ = xiMap Φ ζ f` is the freeze transport.

The rows of that composite are the following, and *no value row* (`f (Ξ x) = ζ (f x)`, i.e. the
legality of the journey to the frozen level) is needed: the level separation is paid for by
`S` (injective), `Φ_i` (injective differential) and `Ξ` (injective on the levels of `f`). -/
theorem goodDrawingOnK_of_windowTransport {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) N] [IsManifold (𝓡 2) ∞ N]
    {f : M → ℝ} {K : Set M} {A : Set ℝ}
    (S : N → EuclideanSpace ℝ (Fin 3)) (Phi : M → N)
    (hSsm : ContMDiff (𝓡 2) (𝓡 3) ∞ S) (hSinj : Function.Injective S)
    (hSimm : ∀ y : N, Function.Injective (mfderiv (𝓡 2) (𝓡 3) S y))
    {Φ : ℝ × M → M} {ζ : ℝ → ℝ}
    (hPsm : ContMDiff (𝓡 2) (𝓡 2) ∞ Phi)
    (hPinj : ∀ x y : M, Phi (xiMap Φ ζ f x) = Phi (xiMap Φ ζ f y) →
      xiMap Φ ζ f x = xiMap Φ ζ f y)
    (hPimm : ∀ x : M, Function.Injective (mfderiv (𝓡 2) (𝓡 2) Phi (xiMap Φ ζ f x)))
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f) (hζ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ ζ)
    (hΦ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞ Φ)
    (hΦ0 : ∀ x : M, Φ (0, x) = x)
    (hΦcomp : ∀ (s t : ℝ) (x : M), Φ (s, Φ (t, x)) = Φ (s + t, x)) :
    GoodDrawingOnK f K A (fun x => S (Phi (xiMap Φ ζ f x))) := by
  have hn : ((∞ : WithTop ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hΞsm : ContMDiff (𝓡 2) (𝓡 2) ∞ (xiMap Φ ζ f) := contMDiff_xiMap hf hΦ hζ
  refine ⟨?_, ?_, ?_⟩
  · intro x _ _
    exact (hSsm.comp hPsm).contMDiffAt.comp x hΞsm.contMDiffAt
  · intro x _ _ v hv hvS
    have hmdΞ : MDifferentiableAt (𝓡 2) (𝓡 2) (xiMap Φ ζ f) x :=
      hΞsm.contMDiffAt.mdifferentiableAt hn
    have hmdP : MDifferentiableAt (𝓡 2) (𝓡 2) Phi (xiMap Φ ζ f x) :=
      hPsm.contMDiffAt.mdifferentiableAt hn
    have hmdS : MDifferentiableAt (𝓡 2) (𝓡 3) S (Phi (xiMap Φ ζ f x)) :=
      hSsm.contMDiffAt.mdifferentiableAt hn
    have hcomp1 := mfderiv_comp_apply (I := 𝓡 2) (I' := 𝓡 2) (I'' := 𝓡 2)
      (f := xiMap Φ ζ f) (g := Phi) (x := x) hmdP hmdΞ v
    have hcomp2 := mfderiv_comp_apply (I := 𝓡 2) (I' := 𝓡 2) (I'' := 𝓡 3)
      (f := fun y : M => Phi (xiMap Φ ζ f y)) (g := S) (x := x) hmdS
      ((hPsm.comp hΞsm).contMDiffAt.mdifferentiableAt hn) v
    simp only [Function.comp_def] at hcomp1 hcomp2
    have h1 : mfderiv (𝓡 2) (𝓡 2) (fun y : M => Phi (xiMap Φ ζ f y)) x v
        = mfderiv (𝓡 2) (𝓡 2) Phi (xiMap Φ ζ f x)
            (mfderiv (𝓡 2) (𝓡 2) (xiMap Φ ζ f) x v) := hcomp1
    have h2 : mfderiv (𝓡 2) (𝓡 3) (fun y : M => S (Phi (xiMap Φ ζ f y))) x v
        = mfderiv (𝓡 2) (𝓡 3) S (Phi (xiMap Φ ζ f x))
            (mfderiv (𝓡 2) (𝓡 2) (fun y : M => Phi (xiMap Φ ζ f y)) x v) := hcomp2
    have hzero : mfderiv (𝓡 2) (𝓡 3) S (Phi (xiMap Φ ζ f x))
        (mfderiv (𝓡 2) (𝓡 2) Phi (xiMap Φ ζ f x)
          (mfderiv (𝓡 2) (𝓡 2) (xiMap Φ ζ f) x v)) = 0 := by
      rw [← h1, ← h2]; exact hvS
    have hPzero : mfderiv (𝓡 2) (𝓡 2) Phi (xiMap Φ ζ f x)
        (mfderiv (𝓡 2) (𝓡 2) (xiMap Φ ζ f) x v) = 0 :=
      hSimm _ (hzero.trans (map_zero _).symm)
    have hΞzero : mfderiv (𝓡 2) (𝓡 2) (xiMap Φ ζ f) x v = 0 :=
      hPimm x (hPzero.trans (map_zero _).symm)
    have hslice := mfderiv_xiMap_ker hΦ hf hζ x v hv
    rw [hslice] at hΞzero
    exact injective_mfderiv_timeShift hΦ hΦ0 hΦcomp (ζ (f x) - f x) x
      (hΞzero.trans (map_zero _).symm)
  · intro x y _ _ _ _ hfxy hSeq
    have h1 : Phi (xiMap Φ ζ f x) = Phi (xiMap Φ ζ f y) := hSinj hSeq
    have h2 : xiMap Φ ζ f x = xiMap Φ ζ f y := hPinj x y h1
    exact xiMap_injOn_level hΦ0 hΦcomp hfxy h2

end Work.Drive.N2

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set Function Filter

/-! ## The openness rows of the critical component

`windowPiece_goodDrawing` consumes two openness rows: `IsOpen K` and the fact that outside `K` (at
the window values) the complement is a neighbourhood.  For `K` a connected component of the (open)
slab `f ⁻¹' Ioo (c - η) (c + η)` of a locally connected space, both are automatic. -/

/-- **The complement of a connected component of an open set is open** in a locally connected
space: every other point lies in its own component, which is open. -/
theorem isOpen_sdiff_connectedComponentIn {α : Type*} [TopologicalSpace α]
    [LocallyConnectedSpace α] {s : Set α} (hs : IsOpen s) (p : α) :
    IsOpen (s \ connectedComponentIn s p) := by
  have hset : s \ connectedComponentIn s p
      = ⋃ y ∈ (s \ connectedComponentIn s p), connectedComponentIn s y := by
    ext z
    constructor
    · intro hz
      exact mem_iUnion.2 ⟨z, mem_iUnion.2 ⟨hz, mem_connectedComponentIn hz.1⟩⟩
    · intro hz
      rw [mem_iUnion] at hz
      obtain ⟨y, hy⟩ := hz
      rw [mem_iUnion] at hy
      obtain ⟨hyS, hzy⟩ := hy
      refine ⟨connectedComponentIn_subset s y hzy, ?_⟩
      intro hzK
      have h1 : connectedComponentIn s y = connectedComponentIn s z := connectedComponentIn_eq hzy
      have h2 : connectedComponentIn s p = connectedComponentIn s z := connectedComponentIn_eq hzK
      have hyz : y ∈ connectedComponentIn s z := by
        rw [← h1]; exact mem_connectedComponentIn hyS.1
      exact hyS.2 (h2 ▸ hyz)
  rw [hset]
  exact isOpen_iUnion fun y => isOpen_iUnion fun _ => hs.connectedComponentIn

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M]

/-- **The critical component of the slab is open.** -/
theorem windowAssembly_component_open {f : M → ℝ} (hf : Continuous f) (c η : ℝ) (p : M) :
    IsOpen (connectedComponentIn (f ⁻¹' Set.Ioo (c - η) (c + η)) p) := by
  haveI : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 2)) M
  exact (isOpen_Ioo.preimage hf).connectedComponentIn

/-- **The complement of the critical component inside the slab is open.** -/
theorem windowAssembly_component_compl_open {f : M → ℝ} (hf : Continuous f) (c η : ℝ) (p : M) :
    IsOpen ((f ⁻¹' Set.Ioo (c - η) (c + η))
      \ connectedComponentIn (f ⁻¹' Set.Ioo (c - η) (c + η)) p) := by
  haveI : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 2)) M
  exact isOpen_sdiff_connectedComponentIn (isOpen_Ioo.preimage hf) p

/-- **The `hKout` row of `windowPiece_goodDrawing`** for the critical component: a point outside `K`
whose value lies in the window has a neighbourhood on which `K` is avoided (the complement of `K` in
the slab is open, and contains the point). -/
theorem windowAssembly_component_eventually_notMem {f : M → ℝ} (hf : Continuous f) (c η : ℝ)
    (p : M) {A : Set ℝ} (hA : A ⊆ Set.Ioo (c - η) (c + η)) :
    ∀ x : M, x ∉ connectedComponentIn (f ⁻¹' Set.Ioo (c - η) (c + η)) p → f x ∈ A →
      ∀ᶠ y in 𝓝 x, y ∉ connectedComponentIn (f ⁻¹' Set.Ioo (c - η) (c + η)) p := by
  intro x hx hxA
  refine Filter.mem_of_superset
    ((windowAssembly_component_compl_open hf c η p).mem_nhds ⟨hA hxA, hx⟩) ?_
  intro y hy
  exact hy.2

end Work.Drive.N2

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set Function Filter

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M]

open Classical in
/-- **The window piece of a critical value, assembled.**  This is the single call site the endgame
(`Work.Drive.N2.levelSeparatingMap_of_windowHybrids`'s `hwin`) needs: with

* `K` the critical component of the slab and the two openness rows
  (`windowAssembly_component_open`, `windowAssembly_component_eventually_notMem`),
* `ζ` the freeze, `Φ*` the single model-adapted flow and `Ξ = xiMap Φ* ζ f`,
* `S` the embedding of the model surface and `Φ_i` the window diffeo (its rows),
* `P` the parked picture and `footMap Φ* f anchor` the transport to the anchor level (its rows,
  including the landing row of the journey to the anchor level),

the two-piece map is a `GoodDrawingOn` on the value set `A`, provided the two pieces are separated by
the sign of the coordinate `0`. -/
theorem windowDrawing_of_data {f : M → ℝ} {A : Set ℝ} {K : Set M} {c η anchor : ℝ}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (hKopen : IsOpen K)
    (hKout : ∀ x : M, x ∉ K → f x ∈ A → ∀ᶠ y in 𝓝 x, y ∉ K)
    {Φ : ℝ × M → M} (hΦ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞ Φ)
    (hΦ0 : ∀ x : M, Φ (0, x) = x)
    (hΦcomp : ∀ (s t : ℝ) (x : M), Φ (s, Φ (t, x)) = Φ (s + t, x))
    {ζ : ℝ → ℝ} (hζ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ ζ)
    {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) N]
    [IsManifold (𝓡 2) ∞ N]
    (S : N → EuclideanSpace ℝ (Fin 3)) (Phi : M → N)
    (hSsm : ContMDiff (𝓡 2) (𝓡 3) ∞ S) (hSinj : Function.Injective S)
    (hSimm : ∀ y : N, Function.Injective (mfderiv (𝓡 2) (𝓡 3) S y))
    (hPsm : ContMDiff (𝓡 2) (𝓡 2) ∞ Phi)
    (hPinj : ∀ x y : M, Phi (xiMap Φ ζ f x) = Phi (xiMap Φ ζ f y) →
      xiMap Φ ζ f x = xiMap Φ ζ f y)
    (hPimm : ∀ x : M, Function.Injective (mfderiv (𝓡 2) (𝓡 2) Phi (xiMap Φ ζ f x)))
    {P : M → EuclideanSpace ℝ (Fin 3)} (hLanding : ∀ x : M, f x ∈ A →
      f (Φ (anchor - f x, x)) = anchor)
    (hPark : GoodDrawingOn f A (fun x => P (Φ (anchor - f x, x))))
    (hsigng : ∀ x : M, x ∈ K → f x ∈ A → (S (Phi (xiMap Φ ζ f x))) 0 < 0)
    (hsignPark : ∀ x : M, x ∉ K → f x ∈ A → 0 < (P (Φ (anchor - f x, x))) 0) :
    GoodDrawingOn f A
      (fun x => if x ∈ K then S (Phi (xiMap Φ ζ f x)) else P (Φ (anchor - f x, x))) :=
  windowPiece_goodDrawing hKopen hKout
    (goodDrawingOnK_of_windowTransport S Phi hSsm hSinj hSimm hPsm hPinj hPimm hf hζ hΦ hΦ0 hΦcomp)
    hPark hsigng hsignPark

end Work.Drive.N2
