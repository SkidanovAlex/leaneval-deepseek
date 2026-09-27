import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.Drive.N2C.defs
import Submission.Work.Drive.N2.GoodDrawingFamily
import Submission.Work.Drive.N2.roundConfigDefs
import Submission.Work.Drive.N2Lead.levelCurvesReparamCinf
import Submission.Work.Drive.N2Lead.roundImageReparamCinf

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology

open scoped Manifold ContDiff Topology in
/-- **The identification row of the certified-window design** (Tier `D2e` of
`Submission/Work/Drive/N2Lead/NOTES_LEAD_coherentWindows.md` §4).  A picture `e 1` of a regular level
`f = u` whose image is a disjoint union of round circles — each component drawn onto its own circle of
positive radius `r i` about `c i`, the circles pairwise separated by `hsep` — is *certified*: it is
level-isotopic, through pictures of the same level, to a disjoint round configuration read through a
parametrisation of the level.  The isotopy is the given one (`IsLevelIsotopy f u e`); the
parametrisation of the level is the only thing that changes at the end (choose the level curves so
that the round parameter advances like the argument of `e 1` along them).  Read the design note §4
(Tier D) first; the intended proof is: a smooth argument lift of `x ↦ e 1 (L.γ i x)` along the circle
of centre `c i` and radius `r i` (Brick: a smooth curve in `S¹` whose image lies in `S¹` admits a
smooth real lift), then reparametrise `L` by the inverse of the normalised lift and take the round
configuration of centres `c` and radii `r`.  The result goes in namespace `Work.Drive.N2Lead`. -/
theorem isCertifiedAt_of_roundImage {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f) {u : ℝ}
    (hreg : ∀ x : M, f x = u → ¬ Work.Drive.Morse.IsCritical f x)
    {g : M → EuclideanSpace ℝ (Fin 3)} {e : ℝ → M → EuclideanSpace ℝ (Fin 3)}
    (he : Work.Drive.N2C.IsLevelIsotopy f u e) (h0 : ∀ y : M, f y = u → e 0 y = g y)
    {n : ℕ} (L : Work.Drive.N2C.LevelCurves f u n) (c : Fin n → EuclideanSpace ℝ (Fin 3))
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (hround : ∀ (i : Fin n) (x : ℝ), ∃ t : ℝ,
      e 1 (L.γ i x) = c i + r i • Work.Drive.N2.roundPic t)
    (hsep : ∀ i j, i ≠ j → ∀ t t' : ℝ,
      c i + r i • Work.Drive.N2.roundPic t ≠ c j + r j • Work.Drive.N2.roundPic t') :
    Work.Drive.N2C.IsCertifiedAt f u g := by
  classical
  have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  -- the time-`1` slice of the level isotopy is smooth at the points of the level
  have hslice : ∀ y : M, f y = u →
      ContMDiffAt (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : M => e 1 z) y := by
    intro y hy
    exact (he.1 1 y hy).comp y (contMDiffAt_const.prodMk contMDiffAt_id)
  have hslice_md : ∀ y : M, f y = u → MDifferentiableAt (𝓡 2) (𝓡 3) (fun z : M => e 1 z) y :=
    fun y hy => (hslice y hy).mdifferentiableAt hn
  -- the curve `t ↦ e 1 (γ i t)` is smooth
  have hEsm : ∀ i : Fin n,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => e 1 (L.γ i t)) := by
    intro i
    rw [contDiff_iff_contDiffAt]
    intro t
    rw [← contMDiffAt_iff_contDiffAt]
    have hfe : (fun t : ℝ => e 1 (L.γ i t)) = ((fun z : M => e 1 z) ∘ L.γ i) := rfl
    rw [hfe]
    exact ContMDiffAt.comp (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) t
      (hslice (L.γ i t) (L.val i t)) ((L.sm i).contMDiffAt)
  -- it is periodic
  have hEper : ∀ i : Fin n, ∀ x : ℝ, e 1 (L.γ i (x + 1)) = e 1 (L.γ i x) := by
    intro i x
    rw [L.per i x]
  -- it is injective modulo the period
  have hEinj : ∀ i : Fin n, ∀ x y : ℝ, e 1 (L.γ i x) = e 1 (L.γ i y) → ∃ k : ℤ, y = x + k := by
    intro i x y hxy
    have h1 : L.γ i x = L.γ i y := he.2.1 1 (L.γ i x) (L.γ i y) (L.val i x) (L.val i y) hxy
    obtain ⟨k, hk⟩ := L.modOne i x y h1
    exact ⟨-k, by push_cast; linarith⟩
  -- it is immersive
  have hEimm : ∀ i : Fin n, ∀ x : ℝ, fderiv ℝ (fun t : ℝ => e 1 (L.γ i t)) x ≠ 0 := by
    intro i x
    -- the tangent vector `mfderiv γ x 1` does not vanish
    have hTne : (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (L.γ i) x) ≠ 0 := by
      intro hT0
      have hbot : (mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (L.γ i x)).ker = ⊥ := by
        have h1 : (mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (L.γ i x)).ker
            ≤ (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (L.γ i) x).range := by
          intro w hw
          obtain ⟨s, hs⟩ := L.ker i x w hw
          exact ⟨s, hs⟩
        have hrange : (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (L.γ i) x).range = ⊥ := by
          rw [hT0]; simp
        rw [hrange] at h1
        exact le_bot_iff.mp h1
      have hinj : Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (L.γ i x)) :=
        LinearMap.ker_eq_bot.mp hbot
      have e2 : TangentSpace (𝓡 2) (L.γ i x) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 2) :=
        { toFun := id, invFun := id, left_inv := fun _ => rfl, right_inv := fun _ => rfl,
          map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
      haveI : Module.Finite ℝ (TangentSpace (𝓡 2) (L.γ i x)) := Module.Finite.equiv e2.symm
      haveI : Module.Finite ℝ (TangentSpace 𝓘(ℝ,ℝ) (f (L.γ i x))) :=
        (inferInstance : Module.Finite ℝ ℝ)
      have h2 : Module.finrank ℝ (TangentSpace (𝓡 2) (L.γ i x)) = 2 := by
        rw [e2.finrank_eq, finrank_euclideanSpace_fin]
      have e1 : TangentSpace 𝓘(ℝ,ℝ) (f (L.γ i x)) ≃ₗ[ℝ] ℝ :=
        { toFun := id, invFun := id, left_inv := fun _ => rfl, right_inv := fun _ => rfl,
          map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
      have h1 : Module.finrank ℝ (TangentSpace 𝓘(ℝ,ℝ) (f (L.γ i x))) = 1 := by
        rw [e1.finrank_eq, Module.finrank_self]
      have hle := LinearMap.finrank_le_finrank_of_injective
        (f := (mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (L.γ i x)).toLinearMap) hinj
      rw [h2, h1] at hle
      omega
    intro hzero
    obtain ⟨t, ht⟩ : ∃ t : TangentSpace 𝓘(ℝ,ℝ) x,
        (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (L.γ i) x) t ≠ 0 := by
      by_contra h
      push_neg at h
      refine hTne (ContinuousLinearMap.ext ?_)
      intro s
      simpa using h s
    -- the tangent vector lies in the kernel of `df`
    have hvker : mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (L.γ i x)
        ((mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (L.γ i) x) t) = 0 := by
      have hfun : (f ∘ L.γ i) = fun _ : ℝ => u := funext (fun s => L.val i s)
      have hcomp := mfderiv_comp_apply (I := 𝓘(ℝ,ℝ)) (I' := 𝓡 2) (I'' := 𝓘(ℝ,ℝ)) x
        (f := L.γ i) (g := f) (hf.mdifferentiableAt hn) ((L.sm i).mdifferentiableAt hn) t
      have h0 : (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (f ∘ L.γ i) x) t = 0 := by
        rw [hfun, mfderiv_const]; exact zero_apply t
      exact hcomp ▸ h0
    -- its image under `d (e 1)` vanishes as well, because `fderiv (e 1 ∘ γ) = 0`
    have hz : mfderiv 𝓘(ℝ,ℝ) (𝓡 3) ((fun y : M => e 1 y) ∘ L.γ i) x = 0 := by
      have h1 : (fun s : ℝ => e 1 (L.γ i s)) = ((fun y : M => e 1 y) ∘ L.γ i) := rfl
      rw [← h1, mfderiv_eq_fderiv, hzero]
      rfl
    have hchain2 := mfderiv_comp_apply (I := 𝓘(ℝ,ℝ)) (I' := 𝓡 2) (I'' := 𝓡 3) x
      (f := L.γ i) (g := fun y : M => e 1 y) (hslice_md (L.γ i x) (L.val i x))
      ((L.sm i).mdifferentiableAt hn) t
    have hde : (mfderiv (𝓡 2) (𝓡 3) (fun y : M => e 1 y) (L.γ i x))
        ((mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (L.γ i) x) t) = 0 := by
      have h0 : (mfderiv 𝓘(ℝ,ℝ) (𝓡 3) ((fun y : M => e 1 y) ∘ L.γ i) x) t = 0 := by
        rw [hz]; rfl
      rw [hchain2] at h0
      exact h0
    exact ht (he.2.2 1 (L.γ i x) (L.val i x) ((mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (L.γ i) x) t) hvker hde)
  -- reparametrise each component so that `e 1` becomes the round picture at unit speed
  have hdata : ∀ i : Fin n, ∃ (h : ℝ → ℝ) (δ : ℝ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h ∧
      (∀ x, e 1 (L.γ i (h x)) = c i + r i • Work.Drive.N2.roundPic (2 * Real.pi * x)) ∧
      Function.Injective h ∧ Function.Surjective h ∧ (∀ x, deriv h x ≠ 0) ∧
      (δ = 1 ∨ δ = -1) ∧ ∀ x, h (x + 1) = h x + δ := by
    intro i
    obtain ⟨h, hsm, himg, hinj, hsurj, hder, ⟨δ, hδ, hper⟩⟩ :=
      roundImageReparamCinf (E := fun t : ℝ => e 1 (L.γ i t)) (c := c i) (r := r i)
        (hr i) (hEsm i) (hround i) (hEper i) (hEinj i) (hEimm i)
    exact ⟨h, δ, hsm, himg, hinj, hsurj, hder, hδ, hper⟩
  choose h δ hsm himg hinj hsurj hder hδ hper using hdata
  -- the reparametrised level curves
  obtain ⟨L', hL'⟩ := levelCurvesReparamCinf (L := L) hδ hsm hinj hsurj hder hper
  refine ⟨n, L', ⟨c, r, hr, fun _ => 0⟩, e, ?_, he, h0, ?_⟩
  · intro i j hij t t'
    simpa [Work.Drive.N2.RoundConfig.circle] using hsep i j hij (2 * Real.pi * t) (2 * Real.pi * t')
  · intro i x
    rw [hL' i x]
    simpa [Work.Drive.N2.RoundConfig.circle] using himg i x

end Work.Drive.N2Lead
