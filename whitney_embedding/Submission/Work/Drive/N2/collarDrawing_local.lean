import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.Drive.N2.GoodDrawingFamily
import Submission.Work.Drive.N2.collarDrawing

/-!
# The **localised** collar drawing

`Work.Drive.N2.collarDrawing` asks the isotopy of pictures `e` to be *jointly* smooth on all of
`ℝ × M`.  The collar family of the global assembly produces `e` only on (and near) the level
`f ⁻¹' {b}`, and the chain rule of `collarDrawing` only ever evaluates `e` at the points
`(τ (f z), Φ (b - f z, z))` — whose second coordinate is *on* that level.  This file records that
weakening: the joint smoothness is required only on `{s} × (the transported level)`.  The proof is
the proof of `collarDrawing` with the hypothesis `hesm` read pointwise.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology in
/-- **The collar drawing (item (1) of the lead's plan), $\\texttt{collarDrawing}$.**

`Φ` is a level flow over the critical-value-free interval `[a,b]` and `e : ℝ → M → ℝ³` is a smooth
*isotopy of pictures*: for every time `s`, `e s` is an embedding of the top level `f ⁻¹' {b}` (injective
there, and immersive on `ker df` there).  Running that isotopy with a time map `τ` of the value `f`
produces a good drawing on the collar `f ⁻¹' (a,b)`:

  `z ↦ e (τ (f z)) (Φ (b - f z, z))`.

This is a strict generalisation of the proved `Work.Drive.N2.goodDrawingOn_band` (which is the case of a
constant isotopy `e s = A`).  The `τ`-dependence is harmless: on `ker df` the derivative of `τ ∘ f`
vanishes, so the chain rule reduces both the immersion and the injectivity clauses to the corresponding
statements for a single picture `e s`.

Note (for the caller): this does *not* assert agreement of the drawing with the constant pictures
`e 0`, `e 1` on the parts of the collar where `τ` is locally constant; that is a separate obligation of
the assembly (the equality is with the *transported* pictures `z ↦ e s (Φ (b - f z, z))`). -/
theorem collarDrawing_local {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    (f : M → ℝ) (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    {a b : ℝ} (hab : a ≤ b) {Φ : ℝ × M → M}
    (hΦsm : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞ Φ) (hΦ0 : ∀ x : M, Φ (0, x) = x)
    (hΦf : ∀ x : M, ∀ t : ℝ, f x ∈ Set.Icc a b → f x + t ∈ Set.Icc a b →
      f (Φ (t, x)) = f x + t)
    (hΦcomp : ∀ x : M, ∀ s t : ℝ, f x ∈ Set.Icc a b → f x + t ∈ Set.Icc a b →
      f x + t + s ∈ Set.Icc a b → Φ (s, Φ (t, x)) = Φ (s + t, x))
    (e : ℝ → M → EuclideanSpace ℝ (Fin 3))
    (hesm : ∀ (z : M), f z ∈ Set.Icc a b → ∀ (s : ℝ),
      ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 3) ∞
        (fun p : ℝ × M => e p.1 p.2) (s, Φ (b - f z, z)))
    (heinj : ∀ s : ℝ, ∀ x y : M, f x = b → f y = b → e s x = e s y → x = y)
    (heimm : ∀ s : ℝ, ∀ y : M, f y = b → ∀ v : TangentSpace (𝓡 2) y,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f y v = 0 → mfderiv (𝓡 2) (𝓡 3) (fun z => e s z) y v = 0 → v = 0)
    (τ : ℝ → ℝ) (hτsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) τ) :
    Work.Drive.N2.GoodDrawingOn f (Set.Ioo a b) (fun z => e (τ (f z)) (Φ (b - f z, z))) := by
  classical
  have hb : b ∈ Set.Icc a b := ⟨hab, le_refl b⟩
  have hτcm : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ τ := hτsm.contMDiff
  have hτf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun z : M => τ (f z)) := by
    simpa only [Function.comp_def] using hτsm.comp_contMDiff hf
  have hTsm : ContMDiff (𝓡 2) (𝓡 2) ∞ (fun z : M => Φ (b - f z, z)) :=
    hΦsm.comp (bandGraph_contMDiff f hf b)
  have hGsm : ContMDiff (𝓡 2) ((𝓘(ℝ, ℝ)).prod (𝓡 2)) ∞
      (fun z : M => (τ (f z), Φ (b - f z, z))) := hτf.prodMk hTsm
  have hgsm : ∀ z : M, f z ∈ Set.Icc a b → ContMDiffAt (𝓡 2) (𝓡 3) ∞
      (fun z : M => e (τ (f z)) (Φ (b - f z, z))) z :=
    fun z hz => (hesm z hz (τ (f z))).comp z (hGsm z)
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact hgsm x (Set.Ioo_subset_Icc_self hx)
  · intro x hx v hfv hgv
    have hxI : f x ∈ Set.Icc a b := Set.Ioo_subset_Icc_self hx
    rcases eq_or_lt_of_le hab with hab_eq | hab_lt
    · exfalso
      rw [hab_eq, Set.Ioo_self] at hx
      exact hx
    · have hTx : f (Φ (b - f x, x)) = b := bandGraph_eq_of_mem f hab hΦf hb hxI
      have hreg : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x ≠ 0 :=
        mfderiv_ne_zero_of_flow f hab_lt hf hΦsm hΦ0 hΦf hxI
      have hfτ : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun z : M => f (Φ (b - f z, z))) x = 0 :=
        mfderiv_tau_f_eq_zero f hab_lt hf hΦsm hΦf hxI hreg
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
        refine mfderiv_eq_of_eqOn_band f hab_lt hf _ _ (hσsm.comp hTsm) hσsm hxI hreg ?_
        intro z hz
        rw [bandGraph_eq_of_mem f hab hΦf hb hz]
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
    have hxI : f x ∈ Set.Icc a b := Set.Ioo_subset_Icc_self hx
    have hyI : f y ∈ Set.Icc a b := Set.Ioo_subset_Icc_self hy
    have hTx : f (Φ (b - f x, x)) = b := bandGraph_eq_of_mem f hab hΦf hb hxI
    have hTy : f (Φ (b - f y, y)) = b := bandGraph_eq_of_mem f hab hΦf hb hyI
    have hτeq : τ (f y) = τ (f x) := by rw [hfxy]
    have hEq1 : e (τ (f x)) (Φ (b - f x, x)) = e (τ (f x)) (Φ (b - f y, y)) := by
      have h : e (τ (f x)) (Φ (b - f x, x)) = e (τ (f y)) (Φ (b - f y, y)) := hgxy
      rw [hτeq] at h
      exact h
    have hτ : Φ (b - f x, x) = Φ (b - f y, y) := heinj (τ (f x)) _ _ hTx hTy hEq1
    have hback : ∀ z : M, f z ∈ Set.Icc a b → f z = f x →
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
