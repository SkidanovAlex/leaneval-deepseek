import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.Drive.N2.GoodDrawingFamily
import Submission.Work.Drive.N2.collarDrawing_local
import Submission.Work.Compat.MFDerivCongrV433

/-!
# The **wide** collar drawing, and the pasting of good drawings by value sets

`Work.Drive.N2.collarDrawing_local` produces the rows of the collar drawing
`z ↦ e (τ (f z)) (Φ (b - f z, z))` on the value band `Ioo a b` **whose upper end is the anchor level
`b`**.  The gap engine needs the same rows on a band `Ioo lo hi` with the anchor `b` in its
*interior* (its two certificates sit at levels `u₁ < b < u₂`), so this file records the widening:
the same proof, with the value condition `f x ∈ Icc a b` replaced by `f x ∈ Icc lo hi` and the
anchor membership `b ∈ Icc lo hi` supplied by `lo < b < hi`.

The second brick is the trivial pasting: the three rows of `GoodDrawingOn` are each local in the
*value* `f x`, so two good drawings of the *same* function on two value sets give one on the union.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set Filter

set_option maxHeartbeats 1000000

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

/-- **The union of two value sets carrying the same drawing.**  All three rows of
`GoodDrawingOn f A g` depend on `f x` only through `f x ∈ A`, so they paste over a union: in the
injectivity row, `f x = f y` puts both points in the *same* one of the two sets. -/
theorem goodDrawingOn_union {f : M → ℝ} {A₁ A₂ : Set ℝ} {g : M → EuclideanSpace ℝ (Fin 3)}
    (h₁ : GoodDrawingOn f A₁ g) (h₂ : GoodDrawingOn f A₂ g) :
    GoodDrawingOn f (A₁ ∪ A₂) g := by
  refine ⟨fun x hx => ?_, fun x hx v h1 h2 => ?_, fun x y hx hy hfxy hgxy => ?_⟩
  · rcases hx with hx | hx
    · exact h₁.1 x hx
    · exact h₂.1 x hx
  · rcases hx with hx | hx
    · exact h₁.2.1 x hx v h1 h2
    · exact h₂.2.1 x hx v h1 h2
  · rcases hx with hx | hx
    · exact h₁.2.2 x y hx (by rwa [← hfxy]) hfxy hgxy
    · exact h₂.2.2 x y hx (by rwa [← hfxy]) hfxy hgxy

/-- **The wide collar drawing.**  `collarDrawing_local` with the value band `Ioo lo hi` and the
anchor level `b` in its interior: for `x` with `f x` anywhere in `Icc lo hi` the transported point
`Φ (b - f x, x)` is on the anchor level, so the three rows transfer. -/
theorem collarDrawing_wide {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    (f : M → ℝ) (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    {lo b hi : ℝ} (hlob : lo < b) (hbhi : b < hi) {Φ : ℝ × M → M}
    (hΦsm : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞ Φ) (hΦ0 : ∀ x : M, Φ (0, x) = x)
    (hΦf : ∀ x : M, ∀ t : ℝ, f x ∈ Set.Icc lo hi → f x + t ∈ Set.Icc lo hi →
      f (Φ (t, x)) = f x + t)
    (hΦcomp : ∀ x : M, ∀ s t : ℝ, f x ∈ Set.Icc lo hi → f x + t ∈ Set.Icc lo hi →
      f x + t + s ∈ Set.Icc lo hi → Φ (s, Φ (t, x)) = Φ (s + t, x))
    (e : ℝ → M → EuclideanSpace ℝ (Fin 3))
    (hesm : ∀ (z : M), f z ∈ Set.Icc lo hi → ∀ (s : ℝ),
      ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 3) ∞
        (fun p : ℝ × M => e p.1 p.2) (s, Φ (b - f z, z)))
    (heinj : ∀ s : ℝ, ∀ x y : M, f x = b → f y = b → e s x = e s y → x = y)
    (heimm : ∀ s : ℝ, ∀ y : M, f y = b → ∀ v : TangentSpace (𝓡 2) y,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f y v = 0 → mfderiv (𝓡 2) (𝓡 3) (fun z => e s z) y v = 0 → v = 0)
    (τ : ℝ → ℝ) (hτsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) τ) :
    Work.Drive.N2.GoodDrawingOn f (Set.Ioo lo hi) (fun z => e (τ (f z)) (Φ (b - f z, z))) := by
  classical
  have hb : b ∈ Set.Icc lo hi := ⟨le_of_lt hlob, le_of_lt hbhi⟩
  have hτcm : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ τ := hτsm.contMDiff
  have hτf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun z : M => τ (f z)) := by
    simpa only [Function.comp_def] using hτsm.comp_contMDiff hf
  have hTsm : ContMDiff (𝓡 2) (𝓡 2) ∞ (fun z : M => Φ (b - f z, z)) :=
    hΦsm.comp (bandGraph_contMDiff f hf b)
  have hGsm : ContMDiff (𝓡 2) ((𝓘(ℝ, ℝ)).prod (𝓡 2)) ∞
      (fun z : M => (τ (f z), Φ (b - f z, z))) := hτf.prodMk hTsm
  have hgsm : ∀ z : M, f z ∈ Set.Icc lo hi → ContMDiffAt (𝓡 2) (𝓡 3) ∞
      (fun z : M => e (τ (f z)) (Φ (b - f z, z))) z :=
    fun z hz => (hesm z hz (τ (f z))).comp z (hGsm z)
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact hgsm x (Set.Ioo_subset_Icc_self hx)
  · intro x hx v hfv hgv
    have hxI : f x ∈ Set.Icc lo hi := Set.Ioo_subset_Icc_self hx
    have hlohi : lo < hi := lt_trans hlob hbhi
    have hTx : f (Φ (b - f x, x)) = b := bandGraph_eq_of_mem f (le_of_lt hlohi) hΦf hb hxI
    have hreg : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x ≠ 0 :=
      mfderiv_ne_zero_of_flow f hlohi hf hΦsm hΦ0 hΦf hxI
    have hfτ : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun z : M => f (Φ (b - f z, z))) x = 0 := by
      have hnb : ∀ᶠ z in 𝓝 x, f z ∈ Set.Ioo lo hi :=
        hf.continuous.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds hx)
      have hev : (fun z : M => f (Φ (b - f z, z))) =ᶠ[𝓝 x] (fun _ : M => b) := by
        filter_upwards [hnb] with z hz
        exact bandGraph_eq_of_mem f (le_of_lt hlohi) hΦf hb ⟨hz.1.le, hz.2.le⟩
      exact hev.mfderiv_eq_v433.trans mfderiv_const
    have hτfv : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun z : M => τ (f z)) x v = 0 := by
      have hc := mfderiv_comp_apply (I := 𝓡 2) (I' := 𝓘(ℝ, ℝ)) (I'' := 𝓘(ℝ, ℝ))
        (f := f) (g := τ) (x := x) (hτcm.mdifferentiableAt (by simp))
        (hf.mdifferentiableAt (by simp)) v
      have hc' : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun z : M => τ (f z)) x v
          = mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) τ (f x) (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v) := by
        simpa only [Function.comp_def] using hc
      rw [hc', hfv, map_zero]
    have hGv : mfderiv (𝓡 2) ((𝓘(ℝ, ℝ)).prod (𝓡 2))
          (fun z : M => (τ (f z), Φ (b - f z, z))) x v
        = ((0 : ℝ), mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (b - f z, z)) x v) := by
      rw [mfderiv_prodMk (I := 𝓡 2) (I' := 𝓘(ℝ, ℝ)) (I'' := 𝓡 2)
        (f := fun z : M => τ (f z)) (g := fun z : M => Φ (b - f z, z))
        (hτf.mdifferentiableAt (by simp)) (hTsm.mdifferentiableAt (by simp))]
      change (((mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun z : M => τ (f z)) x).prod
        (mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (b - f z, z)) x)) v) = _
      rw [ContinuousLinearMap.prod_apply, hτfv]
      rfl
    have hchain : mfderiv (𝓡 2) (𝓡 3) (fun z : M => e (τ (f z)) (Φ (b - f z, z))) x v
        = mfderiv ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 3) (fun p : ℝ × M => e p.1 p.2)
            (τ (f x), Φ (b - f x, x))
            (mfderiv (𝓡 2) ((𝓘(ℝ, ℝ)).prod (𝓡 2))
              (fun z : M => (τ (f z), Φ (b - f z, z))) x v) := by
      have h := mfderiv_comp_apply (I := 𝓡 2) (I' := (𝓘(ℝ, ℝ)).prod (𝓡 2)) (I'' := 𝓡 3)
        (f := fun z : M => (τ (f z), Φ (b - f z, z)))
        (g := fun p : ℝ × M => e p.1 p.2) (x := x)
        ((hesm x hxI (τ (f x))).mdifferentiableAt (by simp))
        (hGsm.mdifferentiableAt (by simp)) v
      simpa only [Function.comp_def] using h
    have hslice : mfderiv ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 3) (fun p : ℝ × M => e p.1 p.2)
          (τ (f x), Φ (b - f x, x))
          ((0 : ℝ), mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (b - f z, z)) x v)
        = mfderiv (𝓡 2) (𝓡 3) (fun z : M => e (τ (f x)) z) (Φ (b - f x, x))
            (mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (b - f z, z)) x v) := by
      let w : TangentSpace ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (τ (f x), Φ (b - f x, x)) :=
        ((0 : TangentSpace (𝓘(ℝ, ℝ)) (τ (f x))),
          mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (b - f z, z)) x v)
      have h := mfderiv_prod_eq_add_apply (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 2) (I'' := 𝓡 3)
        (f := fun p : ℝ × M => e p.1 p.2) (p := (τ (f x), Φ (b - f x, x))) (v := w)
        ((hesm x hxI (τ (f x))).mdifferentiableAt (by simp))
      change mfderiv ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 3) (fun p : ℝ × M => e p.1 p.2)
          (τ (f x), Φ (b - f x, x)) w
        = mfderiv (𝓡 2) (𝓡 3) (fun z : M => e (τ (f x)) z) (Φ (b - f x, x))
            (mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (b - f z, z)) x v)
      rw [h]
      rw [show w = ((0 : TangentSpace (𝓘(ℝ, ℝ)) (τ (f x))),
          mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (b - f z, z)) x v) from rfl]
      rw [map_zero, zero_add]
    have hdgv : mfderiv (𝓡 2) (𝓡 3) (fun z : M => e (τ (f x)) z) (Φ (b - f x, x))
          (mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (b - f z, z)) x v) = 0 := by
      have h2 : mfderiv ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 3) (fun p : ℝ × M => e p.1 p.2)
            (τ (f x), Φ (b - f x, x))
            (mfderiv (𝓡 2) ((𝓘(ℝ, ℝ)).prod (𝓡 2))
              (fun z : M => (τ (f z), Φ (b - f z, z))) x v)
          = mfderiv ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 3) (fun p : ℝ × M => e p.1 p.2)
            (τ (f x), Φ (b - f x, x))
            ((0 : ℝ), mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (b - f z, z)) x v) :=
        congrArg (fun w => mfderiv ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 3) (fun p : ℝ × M => e p.1 p.2)
          (τ (f x), Φ (b - f x, x)) w) hGv
      exact hslice.symm.trans (h2.symm.trans (hchain.symm.trans hgv))
    have hdfT : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f (Φ (b - f x, x))
          (mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (b - f z, z)) x v) = 0 := by
      have hc := mfderiv_comp_apply (I := 𝓡 2) (I' := 𝓡 2) (I'' := 𝓘(ℝ, ℝ))
        (f := fun z : M => Φ (b - f z, z)) (g := f) (x := x)
        (hf.mdifferentiableAt (by simp)) (hTsm.mdifferentiableAt (by simp)) v
      have hc' : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun z : M => f (Φ (b - f z, z))) x v
          = mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f (Φ (b - f x, x))
              (mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (b - f z, z)) x v) := by
        simpa only [Function.comp_def] using hc
      have hz : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun z : M => f (Φ (b - f z, z))) x v = 0 := by
        rw [hfτ]; rfl
      rw [← hc', hz]
    have hdTv : mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (b - f z, z)) x v = 0 :=
      heimm (τ (f x)) (Φ (b - f x, x)) hTx
        (mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (b - f z, z)) x v) hdfT hdgv
    have hσsm : ContMDiff (𝓡 2) (𝓡 2) ∞ (fun z : M => Φ (f x - f z, z)) :=
      hΦsm.comp (bandGraph_contMDiff f hf (f x))
    have hEq : mfderiv (𝓡 2) (𝓡 2)
          (fun z : M => Φ (f x - f (Φ (b - f z, z)), Φ (b - f z, z))) x
        = mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (f x - f z, z)) x := by
      refine mfderiv_eq_of_eqOn_band f hlohi hf _ _ (hσsm.comp hTsm) hσsm hxI hreg ?_
      intro z hz
      rw [bandGraph_eq_of_mem f (le_of_lt hlohi) hΦf hb hz]
      have h := hΦcomp z (f x - b) (b - f z) hz (by simpa using hb)
        (by rw [show f z + (b - f z) + (f x - b) = f x by ring]; exact hxI)
      simpa [show (f x - b) + (b - f z) = f x - f z by ring] using h
    have hchainσ : mfderiv (𝓡 2) (𝓡 2)
          (fun z : M => Φ (f x - f (Φ (b - f z, z)), Φ (b - f z, z))) x v
        = mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (f x - f z, z)) (Φ (b - f x, x))
            (mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (b - f z, z)) x v) :=
      mfderiv_comp_apply (I := 𝓡 2) (I' := 𝓡 2) (I'' := 𝓡 2)
        (f := fun z : M => Φ (b - f z, z)) (g := fun w : M => Φ (f x - f w, w)) (x := x)
        (hσsm.mdifferentiableAt (by simp)) (hTsm.mdifferentiableAt (by simp)) v
    have hσzero : mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (f x - f z, z)) x v = 0 := by
      have h1 : mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (f x - f z, z)) x v
          = mfderiv (𝓡 2) (𝓡 2)
              (fun z : M => Φ (f x - f (Φ (b - f z, z)), Φ (b - f z, z))) x v :=
        (congrArg (fun (L : TangentSpace (𝓡 2) x →L[ℝ] TangentSpace (𝓡 2) x) => L v)
          hEq).symm
      have h3 : mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (f x - f z, z)) (Φ (b - f x, x))
            (mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (b - f z, z)) x v) = 0 := by
        rw [hdTv]
        exact map_zero _
      exact h1.trans (hchainσ.trans h3)
    have hσv : mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (f x - f z, z)) x v = v :=
      mfderiv_bandShift_apply f hf hΦsm hΦ0 rfl v hfv
    exact hσv.symm.trans hσzero
  · intro x y hx hy hfxy hgxy
    have hlohi : lo < hi := lt_trans hlob hbhi
    have hxI : f x ∈ Set.Icc lo hi := Set.Ioo_subset_Icc_self hx
    have hyI : f y ∈ Set.Icc lo hi := Set.Ioo_subset_Icc_self hy
    have hTx : f (Φ (b - f x, x)) = b := bandGraph_eq_of_mem f (le_of_lt hlohi) hΦf hb hxI
    have hTy : f (Φ (b - f y, y)) = b := bandGraph_eq_of_mem f (le_of_lt hlohi) hΦf hb hyI
    have hτeq : τ (f y) = τ (f x) := by rw [hfxy]
    have hEq1 : e (τ (f x)) (Φ (b - f x, x)) = e (τ (f x)) (Φ (b - f y, y)) := by
      have h : e (τ (f x)) (Φ (b - f x, x)) = e (τ (f y)) (Φ (b - f y, y)) := hgxy
      rw [hτeq] at h
      exact h
    have hτ : Φ (b - f x, x) = Φ (b - f y, y) := heinj (τ (f x)) _ _ hTx hTy hEq1
    have hback : ∀ z : M, f z ∈ Set.Icc lo hi → f z = f x →
        Φ (f z - b, Φ (b - f z, z)) = z := by
      intro z hz _
      have h := hΦcomp z (f z - b) (b - f z) hz (by simpa using hb)
        (by rw [show f z + (b - f z) + (f z - b) = f z by ring]; exact hz)
      rw [show (f z - b) + (b - f z) = 0 by ring, hΦ0 z] at h
      exact h
    have h1 := hback x hxI rfl
    have h2 := hback y hyI hfxy.symm
    rw [hτ] at h1
    have hfx_eq : f x - b = f y - b := by rw [hfxy]
    rw [← hfx_eq] at h2
    exact h1.symm.trans h2



end Work.Drive.N2
