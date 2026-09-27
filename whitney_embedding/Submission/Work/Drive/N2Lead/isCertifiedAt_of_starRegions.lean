import Mathlib
import Submission.Work.Drive.N2C.defs
import Submission.Work.Drive.N2Lead.twistDefs
import Submission.Work.Drive.N2Lead.starShapedRadial
import Submission.Work.Drive.N2Lead.starShapedComponents
import Submission.Work.Drive.N2Lead.isCertifiedAt_of_roundImage
import Submission.Work.Drive.N2Lead.isLevelIsotopy_squash
import Submission.Work.Drive.N2Lead.isLevelIsotopy_ambient_local
import Submission.Work.Drive.N2Lead.smoothArgLiftCinf
import Submission.Work.Drive.N2Lead.smoothArgLiftComplex
import Submission.Work.Drive.N2Lead.radFlatKernel
import Submission.Work.Drive.N2Lead.starRegionsCore
import Submission.Work.Drive.N2Lead.starRegionsComponents
import Submission.Work.Drive.N2Lead.starRegionsPush
import Submission.Work.Drive.N2.exists_levelComponentCurves
import Submission.Work.Drive.N2C.levelCurves_ofComponentCurves

set_option maxHeartbeats 2000000

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Function Filter

noncomputable section

/-- The norm of the planar projection of the round picture is `1`. -/
lemma norm_proj2_roundPic (t : ℝ) : ‖proj2 (Work.Drive.N2.roundPic t)‖ = 1 := by
  have h1 : Complex.normSq (proj2 (Work.Drive.N2.roundPic t)) = 1 := by
    rw [proj2_roundPic, Complex.normSq_apply]
    simp only [Complex.ofReal_re, Complex.ofReal_im]
    nlinarith [Real.cos_sq_add_sin_sq t]
  have h2 : ‖proj2 (Work.Drive.N2.roundPic t)‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq, h1]
  nlinarith [norm_nonneg (proj2 (Work.Drive.N2.roundPic t)), h2]

/-- The unit vector in the direction of a non-zero complex number, as the cosine and sine of its
argument. -/
lemma inv_norm_smul_eq_arg (z : ℂ) (hz : z ≠ 0) :
    (‖z‖⁻¹ : ℝ) • z = (⟨Real.cos (Complex.arg z), Real.sin (Complex.arg z)⟩ : ℂ) := by
  apply Complex.ext
  · rw [Complex.smul_re, smul_eq_mul, Complex.cos_arg hz, div_eq_mul_inv]
    ring
  · rw [Complex.smul_im, smul_eq_mul, Complex.sin_arg, div_eq_mul_inv]
    ring

/-- The planar inclusion of the point `⟨cos t, sin t⟩` is the round picture. -/
lemma pl_cos_sin (t : ℝ) :
    pl (⟨Real.cos t, Real.sin t⟩ : ℂ) = Work.Drive.N2.roundPic t := rfl

/-- The squash at time `0` is the identity. -/
lemma sq_zero' (v : E3) : sq 0 v = v := by
  ext i
  fin_cases i <;> simp [sq]

open scoped Manifold ContDiff in
/-- **The star-regions certificate interface** (`NOTES_LEAD_saddlePacket.md` §4.1, with `hrate` in the equivalent *real-multiple* form, which avoids the `ℂ`-scalar-multiplication instance on `TangentSpace 𝓘(ℝ,ℂ) ·`): the picture `g` of the regular level `u` is split by finitely many pairwise disjoint convex open regions `Ω k`, each containing the closed ball of radius `ρ k > 0` about its centre `o k`; on `Ω k` the planar picture never meets `o k`, the angular rate of `proj2 (g ·)` about `o k` along `ker df` never vanishes, and one ray of `Ω k` is hit at most once on the level.  Then `g` is certified at `u`. -/
theorem isCertifiedAt_of_starRegions {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f) {u : ℝ}
    (hreg : ∀ x : M, f x = u → ¬ Work.Drive.Morse.IsCritical f x)
    {g : M → Work.Drive.N2Lead.E3}
    (hg : Work.Drive.N2C.IsLevelIsotopy f u (fun _ : ℝ => g))
    {K : ℕ} (Ω : Fin K → Set ℂ) (o : Fin K → ℂ) (ρ : Fin K → ℝ)
    (hΩ : ∀ k : Fin K, IsOpen (Ω k) ∧ Convex ℝ (Ω k)) (hρ : ∀ k : Fin K, 0 < ρ k)
    (hball : ∀ k : Fin K, Metric.closedBall (o k) (ρ k) ⊆ Ω k)
    (hdisj : Pairwise fun k l : Fin K => Disjoint (Ω k) (Ω l))
    (hin : ∀ y : M, f y = u → ∃ k : Fin K, Work.Drive.N2Lead.proj2 (g y) ∈ Ω k)
    (hrate : ∀ (y : M) (k : Fin K), f y = u → Work.Drive.N2Lead.proj2 (g y) ∈ Ω k →
      Work.Drive.N2Lead.proj2 (g y) ≠ o k ∧
      ∀ v : TangentSpace (𝓡 2) y, mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f y v = 0 → v ≠ 0 →
      ¬ (∃ t : ℝ, mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun z : M => Work.Drive.N2Lead.proj2 (g z)) y v
          = t • (Work.Drive.N2Lead.proj2 (g y) - o k)))
    (hhit : ∀ k : Fin K, ∃ e : ℂ, e ≠ 0 ∧ ∀ x y : M, f x = u → f y = u →
      (∃ s : ℝ, 0 < s ∧ Work.Drive.N2Lead.proj2 (g x) = o k + s • e) →
      (∃ s : ℝ, 0 < s ∧ Work.Drive.N2Lead.proj2 (g y) = o k + s • e) → x = y) :
    Work.Drive.N2C.IsCertifiedAt f u g := by
  classical
  by_cases hlev : ∃ x : M, f x = u
  · obtain ⟨n, γ, hγsm, hγper, hγinjIco, hγval, hγimm, hγker, hγcover, hγdisj, hγcl, hγmod⟩ :=
      Work.Drive.N2.exists_levelComponentCurves f hf u hreg hlev
    -- smoothness of the picture at the points of the level
    have hsmg : ∀ y : M, f y = u → ContMDiffAt (𝓡 2) (𝓡 3) tpC g y :=
      fun y hy => (hg.1 0 y hy).comp y (contMDiffAt_const.prodMk contMDiffAt_id)
    have hcover' : ∀ x : M, f x = u → ∃ (i : Fin n) (t : ℝ), x = γ i t := by
      intro x hx
      have hmem : x ∈ ⋃ i, Set.range (γ i) := by rw [hγcover]; exact hx
      obtain ⟨i, t, ht⟩ := Set.mem_iUnion.mp hmem
      exact ⟨i, t, ht.symm⟩
    -- each component lies in one region
    have hregion : ∀ i : Fin n, ∃ k : Fin K, ∀ t : ℝ, proj2 (g (γ i t)) ∈ Ω k := by
      intro i
      refine pathRegionConst (fun k => (hΩ k).1) hdisj ?_ fun t => hin _ (hγval i t)
      rw [continuous_iff_continuousAt]
      intro t
      exact proj2CLM.continuous.continuousAt.comp
        (((hsmg (γ i t) (hγval i t)).continuousAt).comp
          ((hγsm i).continuous.continuousAt))
    choose kk hkk using hregion
    -- the radial-graph rows of every component
    have hgraph : ∀ i : Fin n, IsRadialGraph (fun t => proj2 (g (γ i t))) (o (kk i)) :=
      fun i => isRadialGraph_of_starRegion hf hsmg hrate hhit (hγsm i) (hγper i) (hγinjIco i)
        (fun t h0 => hγimm i t (ContinuousLinearMap.ext_ring h0)) (hγval i) (hkk i)
    -- distinct components occupy distinct regions
    have hkk_inj : Function.Injective kk := by
      intro i j hij
      by_contra hne
      obtain ⟨e, hene, hhe⟩ := hhit (kk i)
      obtain ⟨t, a, ha, ht⟩ := (hgraph i).2.2 e hene
      obtain ⟨t', a', ha', ht'⟩ := (hgraph j).2.2 e hene
      rw [← hij] at ht'
      have hx : proj2 (g (γ i t)) = o (kk i) + a • e := by
        rw [← ht]; abel
      have hy : proj2 (g (γ j t')) = o (kk i) + a' • e := by
        rw [← ht']; abel
      have heq := hhe (γ i t) (γ j t') (hγval i t) (hγval j t') ⟨a, ha, hx⟩ ⟨a', ha', hy⟩
      exact (Set.disjoint_left.mp (hγdisj i j hne) (Set.mem_range_self t)) ⟨t', heq.symm⟩
    -- the planar projection of the picture is injective on the level
    have hinj_proj : ∀ x y : M, f x = u → f y = u → proj2 (g x) = proj2 (g y) → x = y := by
      intro x y hx hy hxy
      obtain ⟨i, s, hs⟩ := hcover' x hx
      obtain ⟨j, t, ht⟩ := hcover' y hy
      subst hs
      subst ht
      have hk_eq : kk i = kk j := by
        by_contra hne
        have h1 : proj2 (g (γ i s)) ∈ Ω (kk i) := hkk i s
        have h2 : proj2 (g (γ j t)) ∈ Ω (kk j) := hkk j t
        exact (Set.disjoint_left.mp (hdisj hne) h1) (by rw [hxy]; exact h2)
      have hij : i = j := hkk_inj hk_eq
      subst hij
      have hray : ∃ c : ℝ, 0 < c ∧ proj2 (g (γ i s)) - o (kk i) = c • (proj2 (g (γ i t)) - o (kk i)) :=
        ⟨1, one_pos, by rw [one_smul, hxy]⟩
      obtain ⟨m, hm⟩ := (hgraph i).2.1 s t hray
      have hp : Function.Periodic (γ i) 1 := hγper i
      have hshift : γ i s = γ i t := by
        rw [hm]
        simpa using hp.int_mul m t
      rw [hshift] at hxy ⊢
    -- the squashed picture is a level isotopy
    have himm_proj : ∀ y : M, f y = u → ∀ v : TangentSpace (𝓡 2) y,
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f y v = 0 →
        mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun z : M => proj2 (g z)) y v = 0 → v = 0 := by
      intro y hy v hv hv'
      obtain ⟨i, t, rfl⟩ := hcover' y hy
      by_contra hv0
      exact (hrate (γ i t) (kk i) (hγval i t) (hkk i t)).2 v hv hv0 ⟨0, by rw [zero_smul]; exact hv'⟩
    have he₁ : Work.Drive.N2C.IsLevelIsotopy f u (fun s y => sq s (g y)) :=
      isLevelIsotopy_squash hsmg hinj_proj himm_proj
    -- the push rows
    have hW : ∀ (s : ℝ) (y : M), f y = u → (fun s y => sq s (g y)) s y ∈ PushDomain Ω o := by
      intro s y hy
      obtain ⟨i, t, rfl⟩ := hcover' y hy
      exact ⟨kk i, by simpa using hkk i t, by simpa using (hrate (γ i t) (kk i) (hγval i t) (hkk i t)).1⟩
    have hF : ∀ (s : ℝ) (v : E3), v ∈ PushDomain Ω o →
        ContMDiffAt ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E3)) 𝓘(ℝ, E3) tpC
          (Function.uncurry (pushMap Ω o ρ)) (s, v) :=
      fun s v hv => contMDiffAt_uncurry_pushMap (fun k => (hΩ k).1) hdisj hv
    have hinj_push : ∀ (s : ℝ) (x y : M), f x = u → f y = u →
        pushMap Ω o ρ s (sq s (g x)) = pushMap Ω o ρ s (sq s (g y)) → x = y := by
      intro s x y hx hy hxy
      obtain ⟨i, s₁, rfl⟩ := hcover' x hx
      obtain ⟨j, t₁, rfl⟩ := hcover' y hy
      have h1 : proj2 (sq s (g (γ i s₁))) ∈ Ω (kk i) := by simpa using hkk i s₁
      have h1' : proj2 (sq s (g (γ i s₁))) ≠ o (kk i) := by
        simpa using (hrate (γ i s₁) (kk i) (hγval i s₁) (hkk i s₁)).1
      have h2 : proj2 (sq s (g (γ j t₁))) ∈ Ω (kk j) := by simpa using hkk j t₁
      have h2' : proj2 (sq s (g (γ j t₁))) ≠ o (kk j) := by
        simpa using (hrate (γ j t₁) (kk j) (hγval j t₁) (hkk j t₁)).1
      obtain ⟨hkk_eq, c, hc, hray⟩ :=
        pushMap_eq_imp hdisj hρ (fun k => (hΩ k).2) hball h1 h1' h2 h2' hxy
      have hij : i = j := hkk_inj hkk_eq
      subst hij
      have hray' : ∃ c : ℝ, 0 < c ∧
          proj2 (g (γ i t₁)) - o (kk i) = c • (proj2 (g (γ i s₁)) - o (kk i)) :=
        ⟨c, hc, by simpa using hray⟩
      obtain ⟨m, hm⟩ := (hgraph i).2.1 t₁ s₁ hray'
      have hp : Function.Periodic (γ i) 1 := hγper i
      have hshift : γ i t₁ = γ i s₁ := by
        rw [hm]
        simpa using hp.int_mul m s₁
      rw [hshift]
    have himm_push : ∀ (s : ℝ) (y : M), f y = u → ∀ v : TangentSpace (𝓡 2) y,
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f y v = 0 →
        fderiv ℝ (pushMap Ω o ρ s) ((fun s y => sq s (g y)) s y)
          (mfderiv (𝓡 2) (𝓡 3) (fun y : M => sq s (g y)) y v) = 0 → v = 0 := by
      intro s y hy v hv hder
      obtain ⟨i, t, rfl⟩ := hcover' y hy
      have hk1 : proj2 (sq s (g (γ i t))) ∈ Ω (kk i) := by simpa using hkk i t
      have hk2 : proj2 (sq s (g (γ i t))) ≠ o (kk i) := by
        simpa using (hrate (γ i t) (kk i) (hγval i t) (hkk i t)).1
      obtain ⟨c, hc⟩ := pushMap_fderiv_eq_zero (fun k => (hΩ k).1) hdisj hρ hk1 hk2 hder
      -- the planar projection of the tangent vector, through the chain rule
      have hw : (mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun z : M => proj2 (g z)) (γ i t) v : ℂ)
          = proj2 (mfderiv (𝓡 2) (𝓡 3) (fun y : M => sq s (g y)) (γ i t) v) := by
        have hFm : MDifferentiableAt (𝓡 2) (𝓡 3) (fun y : M => sq s (g y)) (γ i t) :=
          ((he₁.1 s (γ i t) (hγval i t)).comp (γ i t)
            (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by simp)
        have hpj : MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℂ) proj2 (sq s (g (γ i t))) := by
          rw [show (proj2 : E3 → ℂ) = ⇑proj2CLM from rfl]
          exact proj2CLM.mdifferentiableAt
        have hchain := mfderiv_comp_apply (I := 𝓡 2) (I' := 𝓡 3) (I'' := 𝓘(ℝ, ℂ)) (γ i t)
          (f := fun y : M => sq s (g y)) (g := proj2) hpj hFm v
        rw [show (proj2 ∘ fun y : M => sq s (g y)) = (fun z : M => proj2 (sq s (g z)))
          from rfl] at hchain
        have h1 : mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun z : M => proj2 (sq s (g z))) (γ i t) v
            = proj2 (mfderiv (𝓡 2) (𝓡 3) (fun y : M => sq s (g y)) (γ i t) v) := by
          rw [hchain, mfderiv_proj2_apply_tangent]
        have h2 : (fun z : M => proj2 (sq s (g z))) = (fun z : M => proj2 (g z)) :=
          funext fun z => proj2_sq s (g z)
        rw [h2] at h1
        exact h1
      by_contra hv0
      refine (hrate (γ i t) (kk i) (hγval i t) (hkk i t)).2 v hv hv0 ⟨c, ?_⟩
      rw [hw]
      exact hc
    have he : Work.Drive.N2C.IsLevelIsotopy f u (fun s y => pushMap Ω o ρ s (sq s (g y))) :=
      isLevelIsotopy_ambient_local he₁ hW hF hinj_push himm_push
    have he0 : ∀ y : M, f y = u → (fun s y => pushMap Ω o ρ s (sq s (g y))) 0 y = g y := by
      intro y hy
      simp only [pushMap_zero, sq_zero']
    -- the level curves and the round configuration
    let L : Work.Drive.N2C.LevelCurves f u n :=
      { γ := γ, sm := hγsm, val := hγval, per := hγper, injIco := hγinjIco, modOne := hγmod,
        cover := hcover', disj := hγdisj, ker := hγker }
    have hL : ∀ (i : Fin n) (x : ℝ), L.γ i x = γ i x := fun i x => rfl
    refine isCertifiedAt_of_roundImage hf hreg he he0 L (fun i => pl (o (kk i)))
      (fun i => ρ (kk i)) (fun i => hρ (kk i)) ?_ ?_
    · -- the pushed picture is drawn on the round circle
      intro i x
      rw [hL i x]
      have hk1 : proj2 (sq 1 (g (γ i x))) ∈ Ω (kk i) := by simpa using hkk i x
      have hk2 : proj2 (sq 1 (g (γ i x))) ≠ o (kk i) := by
        simpa using (hrate (γ i x) (kk i) (hγval i x) (hkk i x)).1
      rw [pushMap_of_mem hdisj (1 : ℝ) (sq 1 (g (γ i x))) (kk i) hk1 hk2, radFlat_one]
      set z : ℂ := proj2 (g (γ i x)) - o (kk i) with hz
      have hzne : z ≠ 0 := sub_ne_zero.mpr (hrate (γ i x) (kk i) (hγval i x) (hkk i x)).1
      have hnorm : (‖z‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hzne
      have h1 : proj2 (sq 1 (g (γ i x)) - pl (o (kk i))) = z := by
        rw [proj2_sub, proj2_sq, proj2_pl]
      rw [h1]
      refine ⟨Complex.arg z, ?_⟩
      have harg : (‖z‖⁻¹ : ℝ) • pl z = Work.Drive.N2.roundPic (Complex.arg z) := by
        rw [show (‖z‖⁻¹ : ℝ) • pl z = pl ((‖z‖⁻¹ : ℝ) • z) from (map_smul plCLM _ _).symm,
          inv_norm_smul_eq_arg z hzne, pl_cos_sin]
      have hρ' : (ρ (kk i) / ‖z‖) • pl z = ρ (kk i) • Work.Drive.N2.roundPic (Complex.arg z) := by
        rw [div_eq_mul_inv, mul_smul, harg]
      rw [hρ']
    · -- the round circles are pairwise disjoint
      intro i j hij t t' hcon
      have hne : kk i ≠ kk j := fun h => hij (hkk_inj h)
      have h1 : proj2 (pl (o (kk i)) + ρ (kk i) • Work.Drive.N2.roundPic t) ∈ Ω (kk i) := by
        refine hball (kk i) ?_
        rw [Metric.mem_closedBall, dist_eq_norm]
        have hsub : proj2 (pl (o (kk i)) + ρ (kk i) • Work.Drive.N2.roundPic t) - o (kk i)
            = ρ (kk i) • proj2 (Work.Drive.N2.roundPic t) := by
          rw [proj2_add, proj2_smul, proj2_pl]
          abel
        rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos (hρ (kk i)), norm_proj2_roundPic, mul_one]
      have h2 : proj2 (pl (o (kk j)) + ρ (kk j) • Work.Drive.N2.roundPic t') ∈ Ω (kk j) := by
        refine hball (kk j) ?_
        rw [Metric.mem_closedBall, dist_eq_norm]
        have hsub : proj2 (pl (o (kk j)) + ρ (kk j) • Work.Drive.N2.roundPic t') - o (kk j)
            = ρ (kk j) • proj2 (Work.Drive.N2.roundPic t') := by
          rw [proj2_add, proj2_smul, proj2_pl]
          abel
        rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos (hρ (kk j)), norm_proj2_roundPic, mul_one]
      exact (Set.disjoint_left.mp (hdisj hne) h1) (hcon ▸ h2)
  · exact Work.Drive.N2C.isCertifiedAt_of_empty fun y hy => hlev ⟨y, hy⟩

end

end Work.Drive.N2Lead
