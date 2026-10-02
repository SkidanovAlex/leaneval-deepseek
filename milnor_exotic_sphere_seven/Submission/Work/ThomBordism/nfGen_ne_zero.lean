import Mathlib
import Submission.Work.ThomBordism.nfGenBasic
import Submission.Work.ThomBordism.stdThomGen_span
import Submission.Work.Thom.relCohomology_euclidean_punctured

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-!
# The oriented fibre generator of the normal bundle is nonzero

`Work.ThomBordism.nfGen hk E ND x ∈ H^k(ν_x, ν_x ∖ 0; ℤ)` is the *oriented fibre generator* of the
normal bundle of the embedding `E : V ↪ ℝ^{8+k}` at the point `x`: the pullback, along the coordinate
reading

`nfRead E ND x : (ν_x, ν_x ∖ 0) ⟶ (ℝ^k, ℝ^k ∖ 0)`

of the fibre in the σ-corrected orthonormal frame `Work.ThomBordism.Gauss.gframe`, of the standard
generator `Work.ThomBordism.stdThomGen` of `H^k(ℝ^k, ℝ^k ∖ 0; ℤ)` (see
`Submission/Work/ThomBordism/orientedFibreGen.lean` and `.../nfGenBasic.lean`, whose `nfGen_eq`
shows that this is the *unconditional* description, the `if` of the definition never taking its
`else` branch thanks to `Work.ThomBordism.nfRead_ne_zero`).

This module proves that this fibre generator is **nonzero**, i.e. that the fibre model of the Thom
class of the normal bundle really carries the generator of `H^k(ν_x, ν_x∖0; ℤ) ≅ ℤ`.  The argument:

* `readFrame_sum_smul` — the reading map of an orthonormal frame inverts the assembly of a vector
  from its coordinates: `readFrame f (∑ j, v j • f j) = v`;
* the vectors of the corrected frame `gframe` are normal and it is orthonormal
  (`Gauss.orthonormal_gframe`, `Gauss.gframe_apply`, `Work.Tubular.orthFrame_mem`), so
  `v ↦ (x, ∑ j, v j • gframe j)` is a **continuous section** of the pair map `nfRead E ND x`
  (`sum_smul_gframe_mem` plus the two `have`s `hs_read`, `hs_mem` of the main proof);
* a continuous section of a map of pairs makes the pullback on relative cohomology **injective**
  (`eq_zero_of_relCohMap_eq_zero_of_section`), so `nfGen hk E ND x = 0` would force
  `stdThomGen k hk = 0` — impossible, since `stdThomGen` generates
  `H^k(ℝ^k, ℝ^k∖0; ℤ) ≅ ℤ` (`stdThomGen_span` and
  `Work.Thom.relCohomology_euclidean_punctured`), which is `stdThomGen_ne_zero` below.
-/

open CategoryTheory Limits
open scoped Topology

namespace Work.ThomBordism

/-! ## Reading a linear combination in an orthonormal frame -/

/-- **The reading map of an orthonormal frame inverts the coordinate combination.**  If `f` is an
orthonormal family in `ℝ^N`, then reading the vector `∑ j, v j • f j` in the frame `f`
(`Work.ThomBordism.readFrame`, i.e. `x ↦ (⟨f j, x⟩)_j`) returns the coordinates `v`. -/
theorem readFrame_sum_smul {N k : ℕ} (f : Fin k → EuclideanSpace ℝ (Fin N))
    (hf : Orthonormal ℝ f) (v : EuclideanSpace ℝ (Fin k)) :
    readFrame f (∑ j, v j • f j) = v := by
  rw [readFrame_apply]
  have h : (fun j : Fin k => inner ℝ (f j) (∑ i, v i • f i)) = fun j : Fin k => v j := by
    funext j
    exact hf.inner_right_fintype (fun i => v i) j
  rw [h, show (fun j : Fin k => v j) = PontryaginThom.eucToFun k v from rfl]
  exact PontryaginThom.funToEuc_eucToFun k v

/-! ## The section -/

/-- **The coordinate combination of the corrected frame is a normal vector.**  For `x` in the chart
`i` of the cover of the normal data, the combination `∑ j, v j • gframe_j` of the σ-corrected
orthonormal frame lies in the normal space `ν_x` (each `gframe_j` is `± orthFrame_j` and the
Gram–Schmidt frame spans `ν_x`). -/
theorem sum_smul_gframe_mem {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : PontryaginThom.EmbeddingData V (8 + k)) (ND : PontryaginThom.NormalData V k E.e)
    (i : PontryaginThom.CoverIdx V k) (x : V.pt) (hx : x ∈ ND.D.baseSet i)
    (v : EuclideanSpace ℝ (Fin k)) :
    (∑ j, v j • Gauss.gframe E ND i x j) ∈ Work.Tubular.normalSpace E x := by
  refine Submodule.sum_mem _ fun j _ => ?_
  have hg : Gauss.gframe E ND i x j ∈ Work.Tubular.normalSpace E x := by
    rw [Gauss.gframe_apply]
    exact Submodule.smul_mem _ _ (Work.Tubular.orthFrame_mem E ND i hx j)
  exact Submodule.smul_mem _ _ hg

/-! ## Nonvanishing of the standard generator -/

/-- **The standard generator of `(ℝ^k, ℝ^k∖0)` is nonzero.**  `Work.ThomBordism.stdThomGen k hk`
generates `H^k(ℝ^k, ℝ^k∖0; ℤ)` (`stdThomGen_span`), and that group is `ℤ` by
`Work.Thom.relCohomology_euclidean_punctured`; a generator of a nonzero module is nonzero. -/
theorem stdThomGen_ne_zero (k : ℕ) (hk : 1 ≤ k) : stdThomGen k hk ≠ 0 := by
  intro h0
  haveI hsub : Subsingleton (Work.Thom.RelCoh ℤ k (EuclideanSpace ℝ (Fin k)) ({0}ᶜ)) := by
    refine ⟨fun a b => ?_⟩
    have htop : (⊤ : Submodule ℤ (Work.Thom.RelCoh ℤ k (EuclideanSpace ℝ (Fin k))
        ({0}ᶜ))) = ⊥ := by
      rw [← stdThomGen_span k hk, h0]
      simp
    have ha : a = 0 := (Submodule.eq_bot_iff _).mp htop a (Submodule.mem_top)
    have hb : b = 0 := (Submodule.eq_bot_iff _).mp htop b (Submodule.mem_top)
    rw [ha, hb]
  have hset : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k)))
      = {v : EuclideanSpace ℝ (Fin k) | v ≠ 0} := by
    ext v; simp
  haveI hsub' : Subsingleton (Work.Thom.RelCoh ℤ k (EuclideanSpace ℝ (Fin k))
      {v : EuclideanSpace ℝ (Fin k) | v ≠ 0}) := hset ▸ hsub
  obtain ⟨e⟩ := Work.Thom.relCohomology_euclidean_punctured k hk k
  have hinv : (ModuleCat.Hom.hom e.hom).comp (ModuleCat.Hom.hom e.inv) = LinearMap.id := by
    have h := congrArg ModuleCat.Hom.hom e.inv_hom_id
    rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h
    exact h
  have hsurj : Function.Surjective (ModuleCat.Hom.hom e.hom) :=
    fun y => ⟨(ModuleCat.Hom.hom e.inv) y, LinearMap.congr_fun hinv y⟩
  have hsub'' : Subsingleton (Fin (if k = k then 1 else 0) → ℤ) :=
    ⟨fun a b => by
      obtain ⟨x, rfl⟩ := hsurj a
      obtain ⟨y, rfl⟩ := hsurj b
      rw [Subsingleton.elim x y]⟩
  rw [if_pos rfl] at hsub''
  haveI := hsub''
  have h1 : (1 : ℤ) = 0 := by
    have hsingle : (fun _ : Fin 1 => (1 : ℤ)) = 0 := Subsingleton.elim _ _
    exact congrFun hsingle 0
  exact one_ne_zero h1

/-! ## A section of a map of pairs makes the pullback injective -/

/-- **A continuous section of a map of pairs makes the pullback on relative cohomology
injective.**  If `f : (X,A) → (ℝ^k, ℝ^k∖0)` admits a continuous section `s` (i.e. `f (s v) = v` for
all `v`, and `s` maps the punctured set into `A`), then pullback along `f` kills only `0`. -/
theorem eq_zero_of_relCohMap_eq_zero_of_section {X : Type} [TopologicalSpace X] {k : ℕ}
    (f : C(X, EuclideanSpace ℝ (Fin k))) (A : Set X)
    (hf : ∀ x ∈ A, f x ∈ ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k))))
    (s : C(EuclideanSpace ℝ (Fin k), X))
    (hsA : ∀ v ∈ ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k))), s v ∈ A)
    (hs : ∀ v, f (s v) = v) (y : Work.Thom.RelCoh ℤ k (EuclideanSpace ℝ (Fin k)) ({0}ᶜ))
    (hy : (ModuleCat.Hom.hom (Work.Thom.relCohMap f A ({0}ᶜ) hf ℤ k)) y = 0) : y = 0 := by
  have hcomp_fun : f.comp s = ContinuousMap.id (EuclideanSpace ℝ (Fin k)) :=
    ContinuousMap.ext hs
  have hcomp : Work.Thom.relCohMap f A ({0}ᶜ) hf ℤ k
      ≫ Work.Thom.relCohMap s ({0}ᶜ) A hsA ℤ k
      = 𝟙 (Work.Thom.RelCoh ℤ k (EuclideanSpace ℝ (Fin k)) ({0}ᶜ)) := by
    rw [Work.Thom.relCohMap_compA ({0}ᶜ) A ({0}ᶜ) s f hsA hf
      (fun v hv => by rw [hs v]; exact hv) ℤ k]
    exact (Work.Thom.relCohMap_congrA ({0}ᶜ) ({0}ᶜ) hcomp_fun
      (fun v hv => by rw [ContinuousMap.comp_apply, hs v]; exact hv)
      (fun v hv => hv) ℤ k).trans (Work.Thom.relCohMap_idA ({0}ᶜ) ℤ k)
  have key : (ModuleCat.Hom.hom (Work.Thom.relCohMap s ({0}ᶜ) A hsA ℤ k))
      ((ModuleCat.Hom.hom (Work.Thom.relCohMap f A ({0}ᶜ) hf ℤ k)) y) = y := by
    have h := congrArg ModuleCat.Hom.hom hcomp
    rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h
    exact LinearMap.congr_fun h y
  rw [hy, map_zero] at key
  exact key.symm

/-! ## The fibre generator -/

/-- **The oriented fibre generator of the normal bundle is nonzero**: the common frame reading
`nfRead E ND x` of the fibre `ν_x` is split by the coordinate combination in the σ-corrected
orthonormal frame `gframe`, so the pullback of `stdThomGen` — which is `nfGen` — is nonzero. -/
theorem nfGen_ne_zero {V : Work.ThomBordism.Man8} {k : ℕ} (hk : 1 ≤ k)
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e) (x : V.pt) :
    nfGen hk E ND x ≠ 0 := by
  classical
  have hx : x ∈ ND.D.baseSet (ND.D.indexAt x) := ND.D.mem_baseSet_at x
  have hf : Orthonormal ℝ (Gauss.gframe E ND (ND.D.indexAt x) x) :=
    Gauss.orthonormal_gframe E ND (ND.D.indexAt x) hx
  have hmem : ∀ v : EuclideanSpace ℝ (Fin k),
      (∑ j, v j • Gauss.gframe E ND (ND.D.indexAt x) x j) ∈ Work.Tubular.normalSpace E x :=
    fun v => sum_smul_gframe_mem E ND (ND.D.indexAt x) x hx v
  have hcont : Continuous fun v : EuclideanSpace ℝ (Fin k) =>
      (⟨⟨(x, ∑ j, v j • Gauss.gframe E ND (ND.D.indexAt x) x j), hmem v⟩, rfl⟩ :
        ↥(nfSet E x)) := by
    refine Continuous.subtype_mk ?_ ?_
    · refine Continuous.subtype_mk ?_ ?_
      · exact continuous_const.prodMk (show Continuous fun v : EuclideanSpace ℝ (Fin k) =>
          ∑ j, v j • Gauss.gframe E ND (ND.D.indexAt x) x j from
          continuous_finsetSum _ fun j _ =>
            (EuclideanSpace.proj j).continuous.smul continuous_const)
  let s : C(EuclideanSpace ℝ (Fin k), ↥(nfSet E x)) :=
    ⟨fun v => ⟨⟨(x, ∑ j, v j • Gauss.gframe E ND (ND.D.indexAt x) x j), hmem v⟩, rfl⟩, hcont⟩
  have hs_read : ∀ v : EuclideanSpace ℝ (Fin k), nfRead E ND x (s v) = v := by
    intro v
    have hv : Work.Tubular.NormalTotal.vec (s v).1
        = ∑ j, v j • Gauss.gframe E ND (ND.D.indexAt x) x j := rfl
    show readFrame (Gauss.gframe E ND (ND.D.indexAt x) x)
      (Work.Tubular.NormalTotal.vec (s v).1) = v
    rw [hv]
    exact readFrame_sum_smul _ hf v
  have hs_mem : ∀ v ∈ ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k))), s v ∈ nfPunct E x := by
    intro v hv hzero
    have h1 := hs_read v
    rw [show nfRead E ND x (s v)
      = readFrame (Gauss.gframe E ND (ND.D.indexAt x) x)
        (Work.Tubular.NormalTotal.vec (s v).1) from rfl, hzero, map_zero] at h1
    exact hv h1.symm
  intro hgen
  have hy : (ModuleCat.Hom.hom (Work.Thom.relCohMap (nfRead E ND x) (nfPunct E x)
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k)))
      (fun p hp => nfRead_ne_zero hk E ND x p hp) ℤ k)) (stdThomGen k hk) = 0 := by
    rw [← nfGen_eq hk E ND x]
    exact hgen
  exact stdThomGen_ne_zero k hk
    (eq_zero_of_relCohMap_eq_zero_of_section (f := nfRead E ND x) (A := nfPunct E x)
      (fun p hp => nfRead_ne_zero hk E ND x p hp) s hs_mem hs_read (stdThomGen k hk) hy)

end Work.ThomBordism
