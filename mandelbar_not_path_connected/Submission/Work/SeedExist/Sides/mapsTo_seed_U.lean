/-
# `Work.SeedExist.Sides.mapsTo_seed_U`

**The characteristic component of the critical value is invariant under the second return.**
From the simple parabolic flower of `z₁` alone (no Böttcher data, no Jordan curve theorem) the
connected component `U c` of the critical value `c = T_c 0` in the interior of the filled Julia
set is carried into itself by `(T_c)^[5]`, and by `(T_c)^[4]` into the component `U₀ c` of the
critical point `0`.

## The argument

Write `T = T_c`, `V = interior (K c)` (the Fatou set of the polynomial-like map `T`),
`g = T^[5]`, `F = T^[10] = g ∘ g`, `U c = connectedComponentIn V c` and
`U₀ c = connectedComponentIn V 0`.  Everything rests on three elementary facts:

* **`V` is forward invariant.**  `K c` is forward invariant (`K` is the set of bounded orbits,
  `Work.SeedExist.Fatou.mapsTo_tantibar_K`), so `T '' V` is an open subset of `K c`, hence
  contained in `V` (`mapsTo_interior_K`).
* **the image of a component is contained in a component** — `f '' connectedComponentIn V z ⊆
  connectedComponentIn V (f z)` when `f` is continuous and maps `V` into itself
  (`image_connectedComponentIn_subset`): the image is preconnected and contained in `V`.
* **`0 ∈ V` and `c = T 0 ∈ V`** (`Work.SeedExist.Fatou.interior_of_fatou`, i.e. Fatou's theorem
  `hfat`).

The heart of the proof is the invariance `g '' U₀ c ⊆ U₀ c`.  Fatou's theorem `hfat` produces a
point `x` of the petal `fl.Pg` and an index `i < 5` with `T^[i] x ∈ U₀ c`.  Let `W` be the
component of `x`.  Since the petal `fl.Pa` is open, preconnected and contained in `K c`, one has
`fl.Pa ⊆ W`; since `fl.Pg` is `g`-invariant, `g x ∈ fl.Pg ⊆ W`.  Hence the image `T^[i] '' W` is
preconnected, contained in `V` and meets `U₀ c`, so `T^[i] '' W ⊆ U₀ c`; consequently `g '' U₀ c`
is preconnected, contained in `V` and meets `U₀ c` at
`T^[5] (T^[i] x) = T^[i] (T^[5] x) ∈ T^[i] '' W ⊆ U₀ c`.  Therefore `g '' U₀ c ⊆ U₀ c`, and in
particular `T^[5] 0 ∈ U₀ c`.

The two conclusions are then immediate:

* `T '' U₀ c ⊆ U c` (preconnected, in `V`, contains `T 0 = c`), so
  `T^[4] '' U c ⊆ connectedComponentIn V (T^[4] c) = connectedComponentIn V (T^[5] 0) = U₀ c`;
* `T^[5] c = T (T^[5] 0) ∈ T '' U₀ c ⊆ U c`, so
  `T^[5] '' U c ⊆ connectedComponentIn V (T^[5] c) = U c`.

Only the *first* conjunct of `FatouCritInBasin` is used (the critical point lies in the
immediate parabolic basin); the second is not needed.
-/
import Mathlib
import Submission.Work.SeedExist.Setup
import Submission.Work.ELRig.Pa_subset_K
import Submission.Work.ELPull.tantibar_openMap
import Submission.Work.SeedExist.Fatou.interior_of_fatou

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Function Set
open scoped Topology

noncomputable section

namespace Work.SeedExist.Sides

open LeanEval.ComplexAnalysis (Tantibar)

/-! ## Elementary invariance of the Fatou set -/

/-- **The interior of the filled Julia set is forward invariant under `T_c`.**  `T_c` is open, so
the image of the open set `interior (K c)` is open; and `K c` is forward invariant, so that image
is contained in `K c`.  Hence it is contained in `interior (K c)`. -/
theorem mapsTo_interior_K (c : ℂ) :
    Set.MapsTo (Tantibar c) (interior (Work.EL.K c)) (interior (Work.EL.K c)) := by
  have himg : Tantibar c '' interior (Work.EL.K c) ⊆ Work.EL.K c := by
    rintro w ⟨z, hz, rfl⟩
    exact Work.SeedExist.Fatou.mapsTo_tantibar_K c (interior_subset hz)
  have hsub : Tantibar c '' interior (Work.EL.K c) ⊆ interior (Work.EL.K c) :=
    (Work.ELPull.isOpenMap_Tantibar c _ isOpen_interior).subset_interior_iff.mpr himg
  intro z hz
  exact hsub ⟨z, hz, rfl⟩

/-- **The image of a component lies in the component of the image.**  If `f` is continuous and
maps `V` into itself, then for `z ∈ V` the image of the component of `z` is a preconnected subset
of `V` containing `f z`, hence is contained in the component of `f z`. -/
theorem image_connectedComponentIn_subset {V : Set ℂ} {f : ℂ → ℂ} (hf : Continuous f)
    (hmap : Set.MapsTo f V V) {z : ℂ} (hz : z ∈ V) :
    f '' connectedComponentIn V z ⊆ connectedComponentIn V (f z) := by
  have hsub : f '' connectedComponentIn V z ⊆ V := by
    rintro w ⟨y, hy, rfl⟩
    exact hmap (connectedComponentIn_subset V z hy)
  exact (isPreconnected_connectedComponentIn.image f hf.continuousOn).subset_connectedComponentIn
    ⟨z, mem_connectedComponentIn hz, rfl⟩ hsub

/-! ## Elementary iterate arithmetic of `T_c` -/

/-- `T_c 0 = c`. -/
theorem tantibar_zero (c : ℂ) : Tantibar c 0 = c := by
  simp [LeanEval.ComplexAnalysis.Tantibar]

/-- The iterate of `T_c` at a one-step-old point: `T^[n] (T x) = T (T^[n] x)`. -/
theorem iterate_apply_tantibar (c : ℂ) (n : ℕ) (x : ℂ) :
    ((Tantibar c)^[n]) (Tantibar c x) = Tantibar c (((Tantibar c)^[n]) x) := by
  rw [← Function.iterate_succ_apply (Tantibar c) n x,
    ← Function.iterate_succ_apply' (Tantibar c) n x]

/-- Iterates of `T_c` commute: `T^[m] (T^[n] x) = T^[n] (T^[m] x)`. -/
theorem iterate_comm_tantibar (c : ℂ) (m n : ℕ) (x : ℂ) :
    ((Tantibar c)^[m]) (((Tantibar c)^[n]) x) = ((Tantibar c)^[n]) (((Tantibar c)^[m]) x) := by
  rw [← Function.iterate_add_apply, ← Function.iterate_add_apply, Nat.add_comm]

/-- The fourth iterate of the critical value is the fifth iterate of the critical point:
`T^[4] c = T^[5] 0`. -/
theorem iterate_four_tantibar_zero (c : ℂ) :
    ((Tantibar c)^[4]) c = ((Tantibar c)^[5]) 0 := by
  have h1 : ((Tantibar c)^[4]) c = ((Tantibar c)^[4]) (Tantibar c 0) := by
    rw [tantibar_zero c]
  rw [h1, ← Function.iterate_succ_apply (Tantibar c) 4 0]

/-- The fifth iterate of the critical value is the sixth iterate of the critical point, i.e.
`T (T^[5] 0)`. -/
theorem iterate_five_tantibar (c : ℂ) :
    ((Tantibar c)^[5]) c = Tantibar c (((Tantibar c)^[5]) 0) := by
  have h1 : ((Tantibar c)^[5]) c = ((Tantibar c)^[5]) (Tantibar c 0) := by
    rw [tantibar_zero c]
  rw [h1, iterate_apply_tantibar c 5 0]

/-! ## The main theorem -/

theorem mapsTo_seed_U {c z₁ : ℂ}
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.FSeed.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) z₁)
    (hfat : Work.SeedExist.FatouCritInBasin c z₁ fl.Pg) :
    Set.MapsTo ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) (Work.SeedExist.U c) (Work.SeedExist.U c) ∧
      Set.MapsTo ((LeanEval.ComplexAnalysis.Tantibar c)^[4]) (Work.SeedExist.U c) (Work.SeedExist.U₀ c) := by
  have hTV : Set.MapsTo (Tantibar c) (interior (Work.EL.K c)) (interior (Work.EL.K c)) :=
    mapsTo_interior_K c
  have hTVn : ∀ n : ℕ,
      Set.MapsTo ((Tantibar c)^[n]) (interior (Work.EL.K c)) (interior (Work.EL.K c)) :=
    fun n => hTV.iterate n
  have hcont : ∀ n : ℕ, Continuous ((Tantibar c)^[n]) :=
    fun n => (Work.Landing.Family.tantibar_continuous c).iterate n
  have hVc : c ∈ interior (Work.EL.K c) := (Work.SeedExist.Fatou.interior_of_fatou fl hfat).1
  have hV0 : (0 : ℂ) ∈ interior (Work.EL.K c) := (Work.SeedExist.Fatou.interior_of_fatou fl hfat).2
  -- the petal point of Fatou's theorem, and its component `W`
  obtain ⟨i, _hi5, x, hxPg, hxiU0⟩ := hfat.1
  have hPaK : fl.Pa ⊆ Work.EL.K c := Work.ELRig.Pa_subset_K fl.toParabolicFlower
  have hPaV : fl.Pa ⊆ interior (Work.EL.K c) := fl.isOpen_Pa.subset_interior_iff.mpr hPaK
  have hxPa : x ∈ fl.Pa := fl.Pg_sub hxPg
  have hxV : x ∈ interior (Work.EL.K c) := hPaV hxPa
  have hPaW : fl.Pa ⊆ connectedComponentIn (interior (Work.EL.K c)) x :=
    fl.isPreconnected_Pa.subset_connectedComponentIn hxPa hPaV
  have hTxW : (Tantibar c)^[5] x ∈ connectedComponentIn (interior (Work.EL.K c)) x :=
    hPaW (fl.Pg_sub (fl.mapsTo_g_Pg hxPg))
  -- the `i`-th image of `W` lies in `U₀`
  have hWiU : (Tantibar c)^[i] '' connectedComponentIn (interior (Work.EL.K c)) x ⊆
      Work.SeedExist.U₀ c := by
    have hinc := image_connectedComponentIn_subset (V := interior (Work.EL.K c))
      (f := (Tantibar c)^[i]) (hcont i) (hTVn i) hxV
    intro w hw
    have h1 := hinc hw
    rw [← connectedComponentIn_eq hxiU0] at h1
    exact h1
  have hmemU0 : (Tantibar c)^[i] ((Tantibar c)^[5] x) ∈ Work.SeedExist.U₀ c :=
    hWiU ⟨(Tantibar c)^[5] x, hTxW, rfl⟩
  -- `U₀` is invariant under the second return `T^[5]`
  have hgU0 : Set.MapsTo ((Tantibar c)^[5]) (Work.SeedExist.U₀ c) (Work.SeedExist.U₀ c) := by
    have hpre : IsPreconnected ((Tantibar c)^[5] '' Work.SeedExist.U₀ c) :=
      isPreconnected_connectedComponentIn.image _ (hcont 5).continuousOn
    have hsub : (Tantibar c)^[5] '' Work.SeedExist.U₀ c ⊆ interior (Work.EL.K c) := by
      rintro w ⟨y, hy, rfl⟩
      exact hTVn 5 (connectedComponentIn_subset (interior (Work.EL.K c)) 0 hy)
    have hpt : (Tantibar c)^[i] ((Tantibar c)^[5] x) ∈ (Tantibar c)^[5] '' Work.SeedExist.U₀ c :=
      ⟨(Tantibar c)^[i] x, hxiU0, iterate_comm_tantibar c 5 i x⟩
    have hinc := hpre.subset_connectedComponentIn hpt hsub
    intro y hy
    have h1 := hinc ⟨y, hy, rfl⟩
    rw [← connectedComponentIn_eq hmemU0] at h1
    exact h1
  have hT5_0 : (Tantibar c)^[5] 0 ∈ Work.SeedExist.U₀ c :=
    hgU0 (mem_connectedComponentIn hV0)
  -- `T '' U₀ ⊆ U c`
  have hTU0U : Tantibar c '' Work.SeedExist.U₀ c ⊆ Work.SeedExist.U c := by
    have hinc := image_connectedComponentIn_subset (V := interior (Work.EL.K c))
      (f := Tantibar c) (Work.Landing.Family.tantibar_continuous c) hTV hV0
    rw [tantibar_zero c] at hinc
    intro w hw
    exact hinc hw
  refine ⟨?_, ?_⟩
  · intro y hy
    have hinc := image_connectedComponentIn_subset (V := interior (Work.EL.K c))
      (f := (Tantibar c)^[5]) (hcont 5) (hTVn 5) hVc
    have hmemT5c : (Tantibar c)^[5] c ∈ Work.SeedExist.U c := by
      rw [iterate_five_tantibar c]
      exact hTU0U ⟨(Tantibar c)^[5] 0, hT5_0, rfl⟩
    have h1 := hinc ⟨y, hy, rfl⟩
    rw [← connectedComponentIn_eq hmemT5c] at h1
    exact h1
  · intro y hy
    have hinc := image_connectedComponentIn_subset (V := interior (Work.EL.K c))
      (f := (Tantibar c)^[4]) (hcont 4) (hTVn 4) hVc
    have hmemT4c : (Tantibar c)^[4] c ∈ Work.SeedExist.U₀ c := by
      rw [iterate_four_tantibar_zero c]
      exact hT5_0
    have h1 := hinc ⟨y, hy, rfl⟩
    rw [← connectedComponentIn_eq hmemT4c] at h1
    exact h1

end Work.SeedExist.Sides
