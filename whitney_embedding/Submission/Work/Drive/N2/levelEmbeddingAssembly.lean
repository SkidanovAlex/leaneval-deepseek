import Mathlib
import Submission.Work.Drive.N2.LevelData
import Submission.Work.Whitney.isEmbedding_of_injective_of_compactSpace

/-!
# From level embedding data to an embedding in `ℝ⁴` (compact surfaces) — local copy

**This is a mechanically renamed copy of `Submission/Work/Drive/N2/embedding_of_level_embedding.lean`**
(only `incl3/incl4/proj3/proj4` are renamed to `incl3X4/incl4X4/proj3X4/proj4X4` and the main theorem
to `levelEmbeddingAssembly`).  The copy exists because the original file's `Work.Drive.N2.proj3`
clashes with the *different* `Work.Drive.N2.proj3` of `Submission/Work/Drive/N2/anchorPictureAux.lean`
(the `z`-coordinate of `ℝ³`), which enters the cone of `Work.Drive.N2.levelSeparatingMap`: no module
importing both can be built, and the target `Work.Drive.N2.embedding_of_morse_movie` imports both.
A one-line rename in either of the two files removes the need for this copy.

Let `M` be a compact `C^∞` surface, `f : M → ℝ` a smooth function and
`D : HasLevelEmbedding f` level-embedding data for `f`: a smooth map `g : M → ℝ³` which separates
the points of every level set of `f` and whose differential is injective on `ker (df)`.

This file proves the elementary consequence `levelEmbeddingAssembly`: the map

`e x = (g x, f x) : M → ℝ³ × ℝ = ℝ⁴`

is a smooth embedding whose differential is injective at every point.

Since `M` is compact and Hausdorff, the topological part is immediate from
`Work.Whitney.isEmbedding_of_injective_of_compactSpace` once we know that `e` is injective, and
injectivity is exactly the condition that `g` separates the points of every level set of `f`.
For the differential: writing `incl3X4` and `incl4X4` for the inclusions of `ℝ³` and `ℝ` as the first
three, resp. the last, coordinates of `ℝ⁴`, we have
`e = incl3X4 ∘ g + incl4X4 ∘ f`, hence `mfderiv e x = incl3X4 ∘ mfderiv g x + incl4X4 ∘ mfderiv f x`.
If this vanishes on `v`, applying the coordinate projections `proj3X4` and `proj4X4` shows that
`mfderiv g x v = 0` and `mfderiv f x v = 0`, so `v = 0` by the immersion property in `D`.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff

noncomputable section

/-! ### The four coordinate maps on `ℝ⁴ = ℝ³ × ℝ` -/

/-- The inclusion of `ℝ³` into `ℝ⁴` as the first three coordinates. -/
def incl3X4 : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
  LinearMap.toContinuousLinearMap
    ((WithLp.linearEquiv 2 ℝ (Fin 4 → ℝ)).symm.toLinearMap.comp
      (LinearMap.pi (fun i : Fin 4 =>
        if h : (i : ℕ) < 3 then
          (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) (⟨i, h⟩ : Fin 3)).comp
            (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).toLinearMap
        else 0)))

/-- The inclusion of `ℝ` into `ℝ⁴` as the last coordinate. -/
def incl4X4 : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
  LinearMap.toContinuousLinearMap
    ((WithLp.linearEquiv 2 ℝ (Fin 4 → ℝ)).symm.toLinearMap.comp
      (LinearMap.pi (fun i : Fin 4 =>
        if (i : ℕ) < 3 then 0 else LinearMap.id)))

/-- The projection of `ℝ⁴` onto its first three coordinates. -/
def proj3X4 : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm :
        (Fin 3 → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 3))).comp
    (ContinuousLinearMap.pi (fun j : Fin 3 =>
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ)
        (Fin.castSucc j : Fin 4)).comp
        ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)) :
          EuclideanSpace ℝ (Fin 4) →L[ℝ] (Fin 4 → ℝ))))

/-- The projection of `ℝ⁴` onto its last coordinate. -/
def proj4X4 : EuclideanSpace ℝ (Fin 4) →L[ℝ] ℝ :=
  ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) (Fin.last 3 : Fin 4)) :
      (Fin 4 → ℝ) →L[ℝ] ℝ).comp
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)) :
      EuclideanSpace ℝ (Fin 4) →L[ℝ] (Fin 4 → ℝ))

lemma proj3X4_incl3X4 (u : EuclideanSpace ℝ (Fin 3)) : proj3X4 (incl3X4 u) = u := by
  ext j; simp [proj3X4, incl3X4, Fin.castSucc]

lemma proj3X4_incl4X4 (t : ℝ) : proj3X4 (incl4X4 t) = 0 := by
  ext j; simp [proj3X4, incl4X4, Fin.castSucc]

lemma proj4X4_incl3X4 (u : EuclideanSpace ℝ (Fin 3)) : proj4X4 (incl3X4 u) = 0 := by
  simp [proj4X4, incl3X4]

lemma proj4X4_incl4X4 (t : ℝ) : proj4X4 (incl4X4 t) = t := by
  simp [proj4X4, incl4X4]

/-- Recovering the `ℝ³`-component of `incl3X4 u + incl4X4 t`. -/
lemma proj3X4_sum (u : EuclideanSpace ℝ (Fin 3)) (t : ℝ) :
    proj3X4 (incl3X4 u + incl4X4 t) = u := by
  rw [map_add, proj3X4_incl3X4, proj3X4_incl4X4, add_zero]

/-- Recovering the `ℝ`-component of `incl3X4 u + incl4X4 t`. -/
lemma proj4X4_sum (u : EuclideanSpace ℝ (Fin 3)) (t : ℝ) :
    proj4X4 (incl3X4 u + incl4X4 t) = t := by
  rw [map_add, proj4X4_incl3X4, proj4X4_incl4X4, zero_add]

/-- The first three coordinates of `incl3X4 a` are those of `a`. -/
lemma incl3X4_castSucc (a : EuclideanSpace ℝ (Fin 3)) (j : Fin 3) :
    incl3X4 a (Fin.castSucc j) = a j := by simp [incl3X4, Fin.castSucc]

/-- The last coordinate of `incl3X4 a` vanishes. -/
lemma incl3X4_last (a : EuclideanSpace ℝ (Fin 3)) : incl3X4 a (Fin.last 3) = 0 := by simp [incl3X4]

/-- The last coordinate of `incl4X4 t` is `t`. -/
lemma incl4X4_last (t : ℝ) : incl4X4 t (Fin.last 3) = t := by simp [incl4X4]

/-- The first three coordinates of `incl4X4 t` vanish. -/
lemma incl4X4_castSucc (t : ℝ) (j : Fin 3) : incl4X4 t (Fin.castSucc j) = 0 :=
  by simp [incl4X4, Fin.castSucc]

/-! ### The main statement -/

theorem levelEmbeddingAssembly {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (f : M → ℝ)
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (D : HasLevelEmbedding f) :
    ∃ e : M → EuclideanSpace ℝ (Fin 4),
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) e ∧
      Topology.IsEmbedding e ∧
      ∀ x : M, Function.Injective
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) e x) := by
  have he : ContMDiff (𝓡 2) (𝓡 4) ∞ (fun x : M => incl3X4 (D.g x) + incl4X4 (f x)) :=
    ContMDiff.add (incl3X4.contMDiff.comp D.smooth_g) (incl4X4.contMDiff.comp hf)
  refine ⟨fun x => incl3X4 (D.g x) + incl4X4 (f x), he, ?_, ?_⟩
  · -- the topological part: `e` is injective, `M` is compact and `ℝ⁴` Hausdorff
    refine Work.Whitney.isEmbedding_of_injective_of_compactSpace _ he ?_
    intro x y hxy
    have hg : D.g x = D.g y := by
      ext j
      have h := congrArg (fun v : EuclideanSpace ℝ (Fin 4) => v (Fin.castSucc j)) hxy
      have h3 : (incl3X4 (D.g x) + incl4X4 (f x)) (Fin.castSucc j)
          = (incl3X4 (D.g y) + incl4X4 (f y)) (Fin.castSucc j) := h
      simpa only [PiLp.add_apply, incl3X4_castSucc, incl4X4_castSucc, add_zero] using h3
    have hfxy : f x = f y := by
      have h := congrArg (fun v : EuclideanSpace ℝ (Fin 4) => v (Fin.last 3)) hxy
      have h3 : (incl3X4 (D.g x) + incl4X4 (f x)) (Fin.last 3)
          = (incl3X4 (D.g y) + incl4X4 (f y)) (Fin.last 3) := h
      simpa only [PiLp.add_apply, incl3X4_last, incl4X4_last, zero_add] using h3
    exact D.injOn_level x y hfxy hg
  · -- the differential of `e = incl3X4 ∘ g + incl4X4 ∘ f`
    intro x
    have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
    have hgd : MDifferentiableAt (𝓡 2) (𝓡 3) D.g x := D.smooth_g.mdifferentiableAt hne
    have hfd : MDifferentiableAt (𝓡 2) 𝓘(ℝ,ℝ) f x := hf.mdifferentiableAt hne
    have h1 : HasMFDerivAt (𝓡 2) (𝓡 4) (fun x : M => incl3X4 (D.g x)) x
        (incl3X4.comp (mfderiv (𝓡 2) (𝓡 3) D.g x)) :=
      HasMFDerivAt.comp x (incl3X4.hasFDerivAt.hasMFDerivAt) hgd.hasMFDerivAt
    have h2 : HasMFDerivAt (𝓡 2) (𝓡 4) (fun x : M => incl4X4 (f x)) x
        (incl4X4.comp (mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f x)) :=
      HasMFDerivAt.comp x (incl4X4.hasFDerivAt.hasMFDerivAt) hfd.hasMFDerivAt
    have hL := (h1.add h2).mfderiv
    change Function.Injective (mfderiv (𝓡 2) (𝓡 4)
      ((fun x : M => incl3X4 (D.g x)) + (fun x => incl4X4 (f x))) x)
    rw [hL]
    rintro v w hvw
    have h0 : (incl3X4.comp (mfderiv (𝓡 2) (𝓡 3) D.g x)
        + incl4X4.comp (mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f x)) (v - w) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr hvw
    have h0' : incl3X4 (mfderiv (𝓡 2) (𝓡 3) D.g x (v - w))
        + incl4X4 (mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f x (v - w)) = 0 := h0
    have hAv : mfderiv (𝓡 2) (𝓡 3) D.g x (v - w) = 0 := by
      have h2 := congrArg proj3X4 h0'
      exact (proj3X4_sum (mfderiv (𝓡 2) (𝓡 3) D.g x (v - w))
        (mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f x (v - w))).symm.trans (h2.trans (map_zero proj3X4))
    have hBv : mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f x (v - w) = 0 := by
      have h2 := congrArg proj4X4 h0'
      exact (proj4X4_sum (mfderiv (𝓡 2) (𝓡 3) D.g x (v - w))
        (mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f x (v - w))).symm.trans (h2.trans (map_zero proj4X4))
    exact sub_eq_zero.mp (D.imm x (v - w) hAv hBv)

end

end Work.Drive.N2
