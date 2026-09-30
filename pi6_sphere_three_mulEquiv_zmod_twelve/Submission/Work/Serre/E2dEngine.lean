import Mathlib
import Submission.Work.Serre.E2dSets
import Submission.Work.Serre.serreE2a
import Submission.Work.Serre.serreE2b

/-!
# The engine of the E2(d) computation

The E2(d) statement (`Work.Serre.SerreE2d`) computes `H_{k+n}(τ^*E, τ^*E|_{∂Iⁿ}) ≅ H_k(F)` for a
Serre fibration `p : E → B`, a map `τ : Iⁿ → B` and the fibre `F = p⁻¹(τ d₀)`.

The engine of the proof is the following consequence of the *relative* cube homotopy lifting
property (`Work.Serre.SerreE2a`) and of the compression theorem (`Work.Serre.SerreE2b`):

**If `W₀ ⊆ W ⊆ Z` and the pair `(W, W₀)` has the compression property at the level of the base
(every map of pairs `(Iᵈ,∂Iᵈ) → (W,W₀)` compresses into `W₀` relative to the boundary), then for
every Serre fibration `q : X → Z` the pair `(q⁻¹W, q⁻¹W₀)` has vanishing homology in every
degree.**

Indeed, a map `(Iᵈ, ∂Iᵈ) → (q⁻¹W, q⁻¹W₀)` can be compressed into `q⁻¹W₀` relative to `∂Iᵈ`: its
base map is pushed into `W₀` by the compression property of the base pair, and this homotopy of
the base is lifted, relative to the hat `Iᵈ × {0} ∪ ∂Iᵈ × I`, by the relative cube HLP
`Work.Serre.serreE2a`.

This is the form in which *both* outputs of the E2(d) induction are obtained:

* `Work.Serre.serreE2c` — the fibre over a point (`W = Iⁿ`, `W₀ = {d₀}`);
* the acyclicity of the slab pairs of the Mayer–Vietoris cover of the cube.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

/-- The compression hypothesis for the pair of preimages `(q⁻¹W, q⁻¹W₀)`, obtained by lifting the
compression homotopy of the base pair `(W, W₀)` by the relative cube HLP. -/
theorem compress_hyp_of_base_compress {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
    (q : C(X, Z)) (hq : Work.StemsB.IsSerreFibration q) (W₀ W : Set Z) (hW : W₀ ⊆ W)
    (hb : ∀ d, Work.RatHurewicz.CompressRel ↥W {x : ↥W | (x : Z) ∈ W₀} d)
    (n : ℕ) :
    ∀ f : C(Work.Stems.Cubical.IC n, ↥(q ⁻¹' W)),
      (∀ t, t ∈ Cube.boundary (Fin n) → f t ∈ {x : ↥(q ⁻¹' W) | (x : X) ∈ q ⁻¹' W₀}) →
      ∃ g : C(Work.Stems.Cubical.IC n, ↥(q ⁻¹' W)),
        (∀ t, g t ∈ {x : ↥(q ⁻¹' W) | (x : X) ∈ q ⁻¹' W₀}) ∧
        ContinuousMap.HomotopicRel f g (Cube.boundary (Fin n)) := by
  intro f hf
  -- the underlying point of `f x` lies over `W`
  have h1 : ∀ x : Work.Stems.Cubical.IC n, q (((f x : ↥(q ⁻¹' W)) : X)) ∈ W := fun x => (f x).2
  -- the base map of `f`
  let b : C(Work.Stems.Cubical.IC n, ↥W) :=
    ⟨fun x => ⟨q (((f x : ↥(q ⁻¹' W)) : X)), h1 x⟩,
      (q.continuous.comp (continuous_subtype_val.comp f.continuous)).subtype_mk (fun x => h1 x)⟩
  have hb' : ∀ x : Work.Stems.Cubical.IC n, (b x : Z) = q (((f x : ↥(q ⁻¹' W)) : X)) := fun _ => rfl
  have hbf : ∀ t, t ∈ Cube.boundary (Fin n) → b t ∈ {x : ↥W | (x : Z) ∈ W₀} :=
    fun t ht => hf t ht
  -- the base-level compression
  obtain ⟨K, hK0, hKrel, hK1⟩ := hb n b hbf
  -- the base homotopy, as a map into `Z`
  let H : C(Work.Stems.Cubical.IC n × unitInterval, Z) :=
    ⟨fun z => (K z : ↥W), continuous_subtype_val.comp K.continuous⟩
  have hH : ∀ z : Work.Stems.Cubical.IC n × unitInterval, H z = (K z : ↥W) := fun _ => rfl
  -- the prescribed lift on the hat: the first coordinate of the point of the cube
  let g : C(↥(hatSet n), X) :=
    ⟨fun z => ((f z.1.1 : ↥(q ⁻¹' W)) : X), by fun_prop⟩
  have hg : ∀ z : ↥(hatSet n), g z = ((f z.1.1 : ↥(q ⁻¹' W)) : X) := fun _ => rfl
  have hcomp : q.comp g = H.comp (hatIncl n) := by
    ext z
    obtain ⟨⟨x, t⟩, hx⟩ := z
    show q (((f x : ↥(q ⁻¹' W)) : X)) = (K (x, t) : ↥W)
    rcases hx with hx | hx
    · -- the bottom face: the compression homotopy starts at the base map
      have ht : t = 0 := hx
      rw [ht, hK0]
      exact (hb' x).symm
    · -- the lateral face: the compression homotopy is constant there
      rw [hKrel x hx t]
      exact (hb' x).symm
  obtain ⟨G, hG, hGhat⟩ := serreE2a X Z q n hq H g hcomp
  have hGv : ∀ (x : Work.Stems.Cubical.IC n) (t : unitInterval),
      q (G (x, t)) = (K (x, t) : ↥W) := by
    intro x t
    have h : q (G (x, t)) = H (x, t) := congrFun (congrArg DFunLike.coe hG) (x, t)
    rw [h, hH]
  -- the lifted homotopy, as a map into `q ⁻¹' W`
  have hGmem : ∀ z : Work.Stems.Cubical.IC n × unitInterval, q (G z) ∈ W := fun z => by
    rw [hGv z.1 z.2]
    exact (K z).2
  let G' : C(Work.Stems.Cubical.IC n × unitInterval, ↥(q ⁻¹' W)) :=
    ⟨fun z => ⟨G z, hGmem z⟩, G.continuous.subtype_mk hGmem⟩
  have hBase : ∀ x : Work.Stems.Cubical.IC n, G' (x, 0) = f x := fun x => by
    refine Subtype.ext ?_
    show G (x, 0) = ((f x : ↥(q ⁻¹' W)) : X)
    exact (hGhat ⟨(x, 0), Or.inl rfl⟩).trans (hg _)
  have hFix : ∀ (x : Work.Stems.Cubical.IC n) (hx : x ∈ Cube.boundary (Fin n))
      (t : unitInterval), G' (x, t) = f x := fun x hx t => by
    refine Subtype.ext ?_
    show G (x, t) = ((f x : ↥(q ⁻¹' W)) : X)
    exact (hGhat ⟨(x, t), Or.inr hx⟩).trans (hg _)
  refine ⟨⟨fun x => G' (x, 1), G'.continuous.comp (continuous_id.prodMk continuous_const)⟩, ?_, ?_⟩
  · -- the endpoint lies over `W₀`
    intro x
    show q (G (x, 1)) ∈ W₀
    rw [hGv x 1]
    exact hK1 x
  · -- the homotopy is relative to the boundary
    refine ⟨ContinuousMap.HomotopyWith.mk
      { toContinuousMap :=
          ⟨fun z => G' (z.2, z.1), G'.continuous.comp (continuous_snd.prodMk continuous_fst)⟩
        map_zero_left := fun x => hBase x
        map_one_left := fun x => rfl }
      (fun t => ?_)⟩
    intro x hx
    exact hFix x hx t

/-- **The base-compression vanishing lemma.**  If the base pair `(W, W₀)` has the compression
property (in all dimensions), then for every Serre fibration `q : X → Z` the relative homology of
the pair `(q⁻¹W, q⁻¹W₀)` vanishes in every degree. -/
theorem isZero_relChains_preimage_of_base_compress {X Z : Type} [TopologicalSpace X]
    [TopologicalSpace Z] (q : C(X, Z)) (hq : Work.StemsB.IsSerreFibration q) (W₀ W : Set Z)
    (hW : W₀ ⊆ W) (hb : ∀ d, Work.RatHurewicz.CompressRel ↥W {x : ↥W | (x : Z) ∈ W₀} d)
    (m : ℕ) :
    IsZero ((Work.Cohomology.relChains (TopCat.of ↥(q ⁻¹' W))
      {x : ↥(q ⁻¹' W) | (x : X) ∈ q ⁻¹' W₀}).homology m) :=
  serreE2b ↥(q ⁻¹' W) {x : ↥(q ⁻¹' W) | (x : X) ∈ q ⁻¹' W₀} m
    (fun n _ => compress_hyp_of_base_compress q hq W₀ W hW hb n) m le_rfl

/-! ## Base-level compression properties

The engine above takes the compression property of the base pair `(W, W₀)` as a hypothesis.  Here
we record the two ways in which it is produced in the E2(d) induction:

* a *deformation retraction* of the ambient space into `W₀` fixing `W₀` pointwise
  (`compressRel_of_deformation`), which covers the middle-slab and fibre-over-a-point cases;
* the general `Work.RatHurewicz.compression_of_relPiVanishing`, used for the slab pairs.
-/

/-- A deformation retraction of `Y` into `A` fixing `A` pointwise gives the compression property of
the pair `(Y, A)` in every dimension. -/
theorem compressRel_of_deformation {Y : Type} [TopologicalSpace Y] {A : Set Y}
    (c : C(Y × unitInterval, Y)) (hc0 : ∀ y, c (y, 0) = y) (hc1 : ∀ y, c (y, 1) ∈ A)
    (hcA : ∀ y ∈ A, ∀ t, c (y, t) = y) (d : ℕ) : Work.RatHurewicz.CompressRel Y A d := by
  intro f hf
  refine ⟨⟨fun z => c (f z.1, z.2),
      c.continuous.comp ((f.continuous.comp continuous_fst).prodMk continuous_snd)⟩, ?_, ?_, ?_⟩
  · intro x
    exact hc0 (f x)
  · intro x hx t
    exact hcA (f x) (hf x hx) t
  · intro x
    exact hc1 (f x)

/-- The compression property of the pair `(Y, {y₀})` for a contraction of `Y` onto `y₀` fixing
`y₀`. -/
theorem compressRel_singleton_of_contraction {Y : Type} [TopologicalSpace Y] (y₀ : Y)
    (c : C(Y × unitInterval, Y)) (hc0 : ∀ y, c (y, 0) = y) (hc1 : ∀ y, c (y, 1) = y₀)
    (hcy : ∀ t, c (y₀, t) = y₀) (d : ℕ) : Work.RatHurewicz.CompressRel Y {y₀} d :=
  compressRel_of_deformation c hc0 (fun y => by rw [hc1]; rfl)
    (fun y hy t => by rw [Set.mem_singleton_iff.mp hy, hcy]) d

/-- **The pair of the total space with the fibre over a point has vanishing relative homology**,
given a contraction of the base onto that point fixing it. -/
theorem isZero_relChains_preimage_singleton {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
    (q : C(X, Z)) (hq : Work.StemsB.IsSerreFibration q) (z₀ : Z)
    (c : C(Z × unitInterval, Z)) (hc0 : ∀ z, c (z, 0) = z) (hc1 : ∀ z, c (z, 1) = z₀)
    (hcz : ∀ t, c (z₀, t) = z₀) (m : ℕ) :
    IsZero ((Work.Cohomology.relChains (TopCat.of ↥(q ⁻¹' (Set.univ : Set Z)))
      {x : ↥(q ⁻¹' (Set.univ : Set Z)) | (x : X) ∈ q ⁻¹' ({z₀} : Set Z)}).homology m) := by
  have hsub : ({z₀} : Set Z) ⊆ (Set.univ : Set Z) := Set.subset_univ _
  -- the induced contraction on the subtype `↥univ`
  let c' : C(↥(Set.univ : Set Z) × unitInterval, ↥(Set.univ : Set Z)) :=
    ⟨fun w => ⟨c (w.1.1, w.2), trivial⟩, by
      refine Continuous.subtype_mk ?_ (fun w => trivial)
      exact c.continuous.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)⟩
  have hc0' : ∀ w : ↥(Set.univ : Set Z), c' (w, 0) = w := by
    intro w
    refine Subtype.ext ?_
    show c (w.1, 0) = w.1
    rw [hc0]
  have hc1' : ∀ w : ↥(Set.univ : Set Z), c' (w, 1) = ⟨z₀, trivial⟩ := by
    intro w
    refine Subtype.ext ?_
    show c (w.1, 1) = z₀
    rw [hc1]
  have hc1'' : ∀ w : ↥(Set.univ : Set Z), c' (w, 1) ∈
      {x : ↥(Set.univ : Set Z) | (x : Z) ∈ ({z₀} : Set Z)} := by
    intro w
    rw [hc1' w]
    rfl
  have hcy' : ∀ t : unitInterval, c' (⟨z₀, trivial⟩, t) = ⟨z₀, trivial⟩ := by
    intro t
    refine Subtype.ext ?_
    show c (z₀, t) = z₀
    rw [hcz]
  exact isZero_relChains_preimage_of_base_compress q hq ({z₀} : Set Z) Set.univ hsub
    (fun d => compressRel_of_deformation c' hc0' hc1'' (fun w hw t => by
      have hw' : (w : Z) = z₀ := hw
      have hw'' : w = ⟨z₀, trivial⟩ := Subtype.ext hw'
      rw [hw'']
      exact hcy' t) d) m

end

end Work.Serre
