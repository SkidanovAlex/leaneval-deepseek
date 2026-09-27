import Mathlib
import Submission.Work.Drive.PushDisc.straightFlatTubeTwoPlane

namespace Work.Drive.PushDisc

open scoped Manifold ContDiff Topology
open Set Metric Filter

set_option maxHeartbeats 1000000

/-!
# The straight flat tube with the two-plane framing and the straightened arc

`Work.Drive.PushDisc.straightFlatTubeTwoPlane` merges the straightened arc row of
`Work.Drive.PushDisc.exists_straightFlatTube` with the two-plane framing.  The arc row
itself is proved inside `Work.Drive.PushDisc.exists_straightFlatTube` (`harcΦ`) but is not
exposed there; the two lemmas below replay that proof with the arc row exposed, so that the
shear of the two-plane step can be applied on top of it (the shear fixes `sheetA` pointwise,
hence fixes every point `(2 t - 1, 0, 0, 0)` of the straightened arc).
-/

theorem straightFlatTubeOfFlatTubeArc {n : ℕ} (hn : 3 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y : M, Function.Injective (mfderiv
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y))
    (W : Set M) (p₁ p₂ q₁ q₂ : M)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨ (y = q₂ ∧ z = q₁))
    (γ₁ : ℝ → M) (hγ₁0 : γ₁ 0 = p₁) (hγ₁1 : γ₁ 1 = q₁)
    (hne : f q₁ ≠ f p₁)
    (A Ainv : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n)))
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hAinv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ainv)
    (hAl : Function.LeftInverse Ainv A) (hAr : Function.RightInverse Ainv A)
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin (2 * n)))) (hK : Module.finrank ℝ K = n)
    (U : Set M) (hUo : IsOpen U) (hUW : U ⊆ W) (hUarc : γ₁ '' Set.Icc (0 : ℝ) 1 ⊆ U)
    (hp₂U : p₂ ∉ U) (hq₂U : q₂ ∉ U)
    (hflat : ∀ x : M, x ∈ U → A (f x) ∈ K)
    (harc : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      A (f (γ₁ t)) = A (f p₁) + t • (A (f q₁) - A (f p₁))) :
    ∃ (k : ℕ) (hk : n = k + 1) (Φ : EuclideanSpace ℝ (Fin (2 * n)) → Work.Drive.Whitney.Mdl k)
      (Θ : Work.Drive.Whitney.Mdl k → EuclideanSpace ℝ (Fin (2 * n))) (U₁ : Set M) (δ₀ : ℝ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ ∧
      (∀ y : EuclideanSpace ℝ (Fin (2 * n)), Θ (Φ y) = y) ∧
      (∀ ξ : Work.Drive.Whitney.Mdl k, Φ (Θ ξ) = ξ) ∧
      IsOpen U₁ ∧ U₁ ⊆ W ∧ γ₁ '' Set.Icc (0 : ℝ) 1 ⊆ U₁ ∧ p₂ ∉ U₁ ∧ q₂ ∉ U₁ ∧
      (∀ x : M, x ∈ U₁ → Φ (f x) ∈ Work.Drive.Whitney.sheetA) ∧
      0 < δ₀ ∧ (∀ x : ℝ, |x| ≤ 1 + δ₀ → ∃ z : M, z ∈ U₁ ∧ Φ (f z) = (x, 0, 0, 0)) ∧
      Φ (f p₁) = ((-1 : ℝ), 0, 0, 0) ∧ Φ (f q₁) = ((1 : ℝ), 0, 0, 0) ∧
      (∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → Φ (f (γ₁ t)) = (2 * t - 1, 0, 0, 0)) := by
  classical
  -- ## the two endpoints of the arc lie in the tube, so their images lie in `K`
  have hp₁U : p₁ ∈ U := hUarc ⟨0, ⟨le_refl 0, zero_le_one⟩, hγ₁0⟩
  have hq₁U : q₁ ∈ U := hUarc ⟨1, ⟨zero_le_one, le_refl 1⟩, hγ₁1⟩
  have hfpK : A (f p₁) ∈ K := hflat p₁ hp₁U
  have hfqK : A (f q₁) ∈ K := hflat q₁ hq₁U
  -- ## `f` is injective on the tube, so `A (f q₁) ≠ A (f p₁)`
  have hUinj : Set.InjOn f U := by
    intro y hy z hz hyz
    rcases hclean y z (hUW hy) (hUW hz) hyz with h | h | h | h | h
    · exact h
    · exact absurd (h.2 ▸ hz) hp₂U
    · exact absurd (h.1 ▸ hy) hp₂U
    · exact absurd (h.2 ▸ hz) hq₂U
    · exact absurd (h.1 ▸ hy) hq₂U
  have hd0 : A (f q₁) - A (f p₁) ≠ 0 := by
    intro h
    exact hne (hAl.injective (sub_eq_zero.mp h))
  have hdK : A (f q₁) - A (f p₁) ∈ K := K.sub_mem hfqK hfpK
  -- ## the linear algebra: an isomorphism of `ℝ^{2n}` onto the model, pinned on `K`
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨L, e, hLval, hed⟩ :=
    exists_linearEquiv_sheetA hk K hK (A (f q₁) - A (f p₁)) hdK hd0
  set q₁c : Work.Drive.Whitney.Mdl k := ((-1 : ℝ), 0, 0, 0) with hq₁c
  have hq₁cmem : q₁c ∈ sheetASub k := ⟨rfl, rfl⟩
  set w : EuclideanSpace ℝ (Fin (2 * n)) :=
    ((e.symm ⟨q₁c, hq₁cmem⟩ : ↥K) : EuclideanSpace ℝ (Fin (2 * n))) - A (f p₁) with hw
  have hwK : w ∈ K := by
    rw [hw]
    exact K.sub_mem (e.symm ⟨q₁c, hq₁cmem⟩).2 hfpK
  set Φ : EuclideanSpace ℝ (Fin (2 * n)) → Work.Drive.Whitney.Mdl k :=
    fun y => L (A y + w) with hΦ
  set Θ : Work.Drive.Whitney.Mdl k → EuclideanSpace ℝ (Fin (2 * n)) :=
    fun ξ => Ainv (L.symm ξ - w) with hΘ
  have hΦsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ := by
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : EuclideanSpace ℝ (Fin (2 * n)) => L (z + w)) :=
      ((L.toContinuousLinearEquiv :
          EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ] Work.Drive.Whitney.Mdl k)).contDiff.comp
        (contDiff_id.add contDiff_const)
    exact h1.comp hA
  have hΘsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ := by
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun ξ : Work.Drive.Whitney.Mdl k => L.symm ξ - w) :=
      ((L.symm.toContinuousLinearEquiv :
          Work.Drive.Whitney.Mdl k →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)))).contDiff.sub
        contDiff_const
    exact hAinv.comp h2
  have hΘΦ : ∀ y : EuclideanSpace ℝ (Fin (2 * n)), Θ (Φ y) = y := by
    intro y
    show Ainv (L.symm (L (A y + w)) - w) = y
    rw [LinearEquiv.symm_apply_apply, add_sub_cancel_right]
    exact hAl y
  have hΦΘ : ∀ ξ : Work.Drive.Whitney.Mdl k, Φ (Θ ξ) = ξ := by
    intro ξ
    show L (A (Ainv (L.symm ξ - w)) + w) = ξ
    rw [hAr (L.symm ξ - w), sub_add_cancel, LinearEquiv.apply_symm_apply]
  have hsheet : ∀ x : M, x ∈ U → Φ (f x) ∈ Work.Drive.Whitney.sheetA := by
    intro x hx
    have h1 : A (f x) ∈ K := hflat x hx
    have h2 : A (f x) + w ∈ K := K.add_mem h1 hwK
    show L (A (f x) + w) ∈ Work.Drive.Whitney.sheetA
    rw [show L (A (f x) + w)
        = (e ⟨A (f x) + w, h2⟩ : Work.Drive.Whitney.Mdl k) from hLval ⟨A (f x) + w, h2⟩]
    exact (e ⟨A (f x) + w, h2⟩).2
  have hend₁ : Φ (f p₁) = ((-1 : ℝ), 0, 0, 0) := by
    have hval : A (f p₁) + w
        = ((e.symm ⟨q₁c, hq₁cmem⟩ : ↥K) : EuclideanSpace ℝ (Fin (2 * n))) := by
      rw [hw]; abel
    show L (A (f p₁) + w) = ((-1 : ℝ), 0, 0, 0)
    rw [hval]
    rw [show L ((e.symm ⟨q₁c, hq₁cmem⟩ : ↥K) : EuclideanSpace ℝ (Fin (2 * n)))
        = (e (e.symm ⟨q₁c, hq₁cmem⟩) : Work.Drive.Whitney.Mdl k) from
      hLval (e.symm ⟨q₁c, hq₁cmem⟩)]
    rw [LinearEquiv.apply_symm_apply]
  have hend₂ : Φ (f q₁) = ((1 : ℝ), 0, 0, 0) := by
    have hval : A (f q₁) + w
        = ((e.symm ⟨q₁c, hq₁cmem⟩ : ↥K) : EuclideanSpace ℝ (Fin (2 * n)))
          + (A (f q₁) - A (f p₁)) := by
      rw [hw]; abel
    show L (A (f q₁) + w) = ((1 : ℝ), 0, 0, 0)
    rw [hval]
    rw [show L (((e.symm ⟨q₁c, hq₁cmem⟩ : ↥K) : EuclideanSpace ℝ (Fin (2 * n)))
          + (A (f q₁) - A (f p₁)))
        = (e (e.symm ⟨q₁c, hq₁cmem⟩ + ⟨A (f q₁) - A (f p₁), hdK⟩) :
            Work.Drive.Whitney.Mdl k) from
      hLval (e.symm ⟨q₁c, hq₁cmem⟩ + ⟨A (f q₁) - A (f p₁), hdK⟩)]
    rw [map_add, LinearEquiv.apply_symm_apply, hed]
    show ((-1 : ℝ), 0, 0, 0) + ((2 : ℝ), 0, 0, 0) = ((1 : ℝ), 0, 0, 0)
    refine mdl_ext ?_ ?_ ?_ ?_ <;> simp <;> norm_num
  -- ## the arc row in the model
  have hLd : L (A (f q₁) - A (f p₁)) = ((2 : ℝ), 0, 0, 0) := by
    rw [show L (A (f q₁) - A (f p₁))
        = (e ⟨A (f q₁) - A (f p₁), hdK⟩ : Work.Drive.Whitney.Mdl k) from
      hLval ⟨A (f q₁) - A (f p₁), hdK⟩, hed]
  have harcΦ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      Φ (f (γ₁ t)) = ((2 * t - 1 : ℝ), 0, 0, 0) := by
    intro t ht
    have h1 : A (f (γ₁ t)) = A (f p₁) + t • (A (f q₁) - A (f p₁)) := harc t ht
    show L (A (f (γ₁ t)) + w) = ((2 * t - 1 : ℝ), 0, 0, 0)
    have hsplit : A (f p₁) + t • (A (f q₁) - A (f p₁)) + w
        = (A (f p₁) + w) + t • (A (f q₁) - A (f p₁)) := by abel
    rw [h1, hsplit, map_add, map_smul, hLd]
    have hLw : L (A (f p₁) + w) = ((-1 : ℝ), 0, 0, 0) := hend₁
    rw [hLw]
    refine mdl_ext ?_ ?_ ?_ ?_ <;> simp <;> ring
  -- ## the `(x,u)`-chart of the flat tube and the straight arc row
  have hUne : U.Nonempty := ⟨p₁, hp₁U⟩
  obtain ⟨c, hcsrc, hceq⟩ :=
    sheetChartOfFlatTube hk f hf himm U hUo hUne hUinj Φ hΦsm Θ hΘsm hΘΦ hsheet
  have harcRow : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      c (γ₁ t) = Work.Drive.PushDisc.splitE k ((2 * t - 1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))) := by
    intro t ht
    rw [hceq (γ₁ t) (hUarc ⟨t, ht, rfl⟩), harcΦ t ht]
  -- ## the extension of the arc row past its ends
  obtain ⟨δ₀, hδ₀, hseg⟩ := segmentRowOfArcRow (n := n) (k := k) U hUo c hcsrc γ₁ hUarc harcRow
  refine ⟨k, hk, Φ, Θ, U, δ₀, hΦsm, hΘsm, hΘΦ, hΦΘ, hUo, hUW, hUarc, hp₂U, hq₂U, hsheet,
    hδ₀, ?_, hend₁, hend₂, harcΦ⟩
  intro x hx
  obtain ⟨z, hzU, hzc⟩ := hseg x hx
  refine ⟨z, hzU, ?_⟩
  rw [hceq z hzU] at hzc
  have h2 := (splitE k).injective hzc
  have hx1 : (Φ (f z)).1 = x := congrArg Prod.fst h2
  have hu1 : (Φ (f z)).2.2.1 = (0 : EuclideanSpace ℝ (Fin k)) := congrArg Prod.snd h2
  obtain ⟨hy0, hv0⟩ := hsheet z hzU
  exact mdl_ext hx1 hy0 hu1 hv0

theorem exists_straightFlatTubeArc {n : ℕ} (hn : 3 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y : M, Function.Injective (mfderiv
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y))
    (W : Set M) (hWopen : IsOpen W) (hWcpt : IsCompact (closure W))
    (p₁ p₂ q₁ q₂ : M) (hW₁ : p₁ ∈ W) (hW₃ : q₁ ∈ W) (hp₁p₂ : p₁ ≠ p₂)
    (hfp : f p₁ = f p₂)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨ (y = q₂ ∧ z = q₁))
    (hsep : ∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z)
    (γ₁ : ℝ → M) (hγ₁ : Continuous γ₁) (hγ₁0 : γ₁ 0 = p₁) (hγ₁1 : γ₁ 1 = q₁)
    (hγW₁ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t ∈ W)
    (hγ₁inj : Set.InjOn γ₁ (Set.Icc (0 : ℝ) 1))
    (hγ₁smooth : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ₁)
    (hγ₁imm : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → Function.Injective (mfderiv
      (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) γ₁ t))
    (hp₂arc : p₂ ∉ γ₁ '' Set.Icc (0 : ℝ) 1) (hq₂arc : q₂ ∉ γ₁ '' Set.Icc (0 : ℝ) 1) :
    ∃ (k : ℕ) (hk : n = k + 1)
      (Φ : EuclideanSpace ℝ (Fin (2 * n)) → Work.Drive.Whitney.Mdl k)
      (Θ : Work.Drive.Whitney.Mdl k → EuclideanSpace ℝ (Fin (2 * n)))
      (U₁ : Set M) (δ₀ : ℝ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ ∧
      (∀ y : EuclideanSpace ℝ (Fin (2 * n)), Θ (Φ y) = y) ∧
      (∀ ξ : Work.Drive.Whitney.Mdl k, Φ (Θ ξ) = ξ) ∧
      IsOpen U₁ ∧ U₁ ⊆ W ∧ γ₁ '' Set.Icc (0 : ℝ) 1 ⊆ U₁ ∧ p₂ ∉ U₁ ∧ q₂ ∉ U₁ ∧
      (∀ x : M, x ∈ U₁ → Φ (f x) ∈ Work.Drive.Whitney.sheetA) ∧
      0 < δ₀ ∧ (∀ x : ℝ, |x| ≤ 1 + δ₀ → ∃ z : M, z ∈ U₁ ∧ Φ (f z) = (x, 0, 0, 0)) ∧
      Φ (f p₁) = ((-1 : ℝ), 0, 0, 0) ∧ Φ (f q₁) = ((1 : ℝ), 0, 0, 0) ∧
      (∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → Φ (f (γ₁ t)) = (2 * t - 1, 0, 0, 0)) := by
  obtain ⟨A, Ainv, K, U, hA, hAinv, hAl, hAr, hK, hUo, hUclW, hUarc, hp₂U, hq₂U, hflat, harc⟩ :=
    Work.Drive.PushDisc.flatTubeStraightSpine hn f hf himm W hWopen hWcpt p₁ p₂ q₁ q₂ hW₁ hW₃
      hp₁p₂ hfp hclean hsep γ₁ hγ₁ hγ₁0 hγ₁1 hγW₁ hγ₁inj hγ₁smooth hγ₁imm hp₂arc hq₂arc
  have hfne : f p₁ ≠ f q₁ := by
    intro h
    rcases hclean p₁ q₁ hW₁ hW₃ h with h1 | h1 | h1 | h1 | h1
    · have h10 : (0 : ℝ) = 1 := hγ₁inj (by norm_num) (by norm_num) (by rw [hγ₁0, hγ₁1, h1])
      norm_num at h10
    · exact hp₂arc ⟨1, ⟨zero_le_one, le_refl 1⟩, hγ₁1.trans h1.2⟩
    · exact absurd h1.1 hp₁p₂
    · have h10 : (0 : ℝ) = 1 := hγ₁inj (by norm_num) (by norm_num) (by rw [hγ₁0, hγ₁1, h1.1])
      norm_num at h10
    · exact hq₂arc ⟨0, ⟨le_refl 0, zero_le_one⟩, hγ₁0.trans h1.1⟩
  exact straightFlatTubeOfFlatTubeArc hn f hf himm W p₁ p₂ q₁ q₂ hclean γ₁ hγ₁0 hγ₁1
    (fun h => hfne h.symm) A Ainv hA hAinv hAl hAr K hK U hUo
    (Subset.trans subset_closure hUclW) hUarc hp₂U hq₂U hflat harc



/-- **The straight flat tube with the two-plane framing AND the straightened arc.**  This is
`Work.Drive.PushDisc.straightFlatTubeTwoPlane` with the extra conclusion that the *chart* carries the
first bigon arc onto the standard segment `(2 t - 1, 0, 0, 0)`.

Proof route (reviewer-verified): the arc row is *already proved inside*
`Submission/Work/Drive/PushDisc/exists_straightFlatTube.lean` (`harcΦ : ∀ t ∈ Icc 0 1,
Φ (f (γ₁ t)) = (2*t-1,0,0,0)`, used there for `segmentRowOfArcRow`) — it is only not exposed in the
statement.  So: replay the composition `exists_straightFlatTube` +
`exists_shear_twoPlanes_of_flatChart` (as `straightFlatTubeTwoPlane` does) and add the conjunct; the
shear `shear k c` fixes `sheetA` pointwise, so it fixes every arc point (they all have `y = 0`). -/
theorem straightFlatTubeArc {n : ℕ} (hn : 3 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y : M, Function.Injective (mfderiv
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y))
    (W : Set M) (hWopen : IsOpen W) (hWcpt : IsCompact (closure W))
    (p₁ p₂ q₁ q₂ : M) (hW₁ : p₁ ∈ W) (hW₃ : q₁ ∈ W) (hp₁p₂ : p₁ ≠ p₂)
    (hfp : f p₁ = f p₂) (hfq : f q₁ = f q₂)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨
        (y = q₂ ∧ z = q₁))
    (hsep : ∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z)
    (htransP : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₁).range ⊔
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₂).range = ⊤)
    (htransQ : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f q₁).range ⊔
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f q₂).range = ⊤)
    (γ₁ : ℝ → M) (hγ₁ : Continuous γ₁) (hγ₁0 : γ₁ 0 = p₁) (hγ₁1 : γ₁ 1 = q₁)
    (hγW₁ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t ∈ W)
    (hγ₁inj : Set.InjOn γ₁ (Set.Icc (0 : ℝ) 1))
    (hγ₁smooth : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ₁)
    (hγ₁imm : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → Function.Injective (mfderiv
      (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) γ₁ t))
    (hp₂arc : p₂ ∉ γ₁ '' Set.Icc (0 : ℝ) 1) (hq₂arc : q₂ ∉ γ₁ '' Set.Icc (0 : ℝ) 1) :
    ∃ (k : ℕ) (hk : n = k + 1)
      (Φ : EuclideanSpace ℝ (Fin (2 * n)) → Work.Drive.Whitney.Mdl k)
      (Θ : Work.Drive.Whitney.Mdl k → EuclideanSpace ℝ (Fin (2 * n))) (U₁ : Set M) (δ₀ : ℝ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ ∧
      (∀ y : EuclideanSpace ℝ (Fin (2 * n)), Θ (Φ y) = y) ∧
      (∀ ξ : Work.Drive.Whitney.Mdl k, Φ (Θ ξ) = ξ) ∧
      IsOpen U₁ ∧ U₁ ⊆ W ∧ γ₁ '' Set.Icc (0 : ℝ) 1 ⊆ U₁ ∧ p₂ ∉ U₁ ∧ q₂ ∉ U₁ ∧
      (∀ x : M, x ∈ U₁ → Φ (f x) ∈ Work.Drive.Whitney.sheetA) ∧
      0 < δ₀ ∧ (∀ x : ℝ, |x| ≤ 1 + δ₀ → ∃ z : M, z ∈ U₁ ∧ Φ (f z) = (x, 0, 0, 0)) ∧
      Φ (f p₁) = ((-1 : ℝ), 0, 0, 0) ∧ Φ (f q₁) = ((1 : ℝ), 0, 0, 0) ∧
      (∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → Φ (f (γ₁ t)) = (2 * t - 1, 0, 0, 0)) ∧
      (Submodule.map (fderiv ℝ Φ (f p₁)).toLinearMap
        (LinearMap.range (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₂).toLinearMap) ⊓
        Work.Drive.PushDisc.kerXV k = ⊥) ∧
      (Submodule.map (fderiv ℝ Φ (f q₁)).toLinearMap
        (LinearMap.range (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f q₂).toLinearMap) ⊓
        Work.Drive.PushDisc.kerXV k = ⊥) := by
  classical
  obtain ⟨k, hk, Φ₀, Θ₀, U₁, δ₀, hΦ₀sm, hΘ₀sm, hΘΦ, hΦΘ, hUo, hUW, hUarc, hp₂U, hq₂U,
    hsheet, hδ₀, hseg, hpin₁, hpin₂, harc₀⟩ :=
    exists_straightFlatTubeArc hn f hf himm W hWopen hWcpt p₁ p₂ q₁ q₂ hW₁ hW₃ hp₁p₂ hfp hclean
      hsep γ₁ hγ₁ hγ₁0 hγ₁1 hγW₁ hγ₁inj hγ₁smooth hγ₁imm hp₂arc hq₂arc
  have hp₁U : p₁ ∈ U₁ := hUarc ⟨0, ⟨le_refl 0, zero_le_one⟩, hγ₁0⟩
  have hq₁U : q₁ ∈ U₁ := hUarc ⟨1, ⟨zero_le_one, le_refl 1⟩, hγ₁1⟩
  obtain ⟨c, hc₁, hc₂⟩ := exists_shear_twoPlanes_of_flatChart hk f hf himm p₁ p₂ q₁ q₂ htransP
    htransQ Φ₀ Θ₀ hΦ₀sm hΘ₀sm hΘΦ hΦΘ U₁ hUo hp₁U hq₁U hsheet
  refine ⟨k, hk, (fun y : EuclideanSpace ℝ (Fin (2 * n)) => shear k c (Φ₀ y)),
    (fun ξ : Work.Drive.Whitney.Mdl k => Θ₀ (shear k (-c) ξ)), U₁, δ₀,
    ?_, ?_, ?_, ?_, hUo, hUW, hUarc, hp₂U, hq₂U, ?_, hδ₀, ?_, ?_, ?_, ?_, hc₁, hc₂⟩
  · -- smoothness of the sheared chart
    simpa only [Function.comp_def, shear_toCLM_apply] using
      ((shear k c).toContinuousLinearMap.contDiff).comp hΦ₀sm
  · -- smoothness of the sheared inverse
    simpa only [Function.comp_def, shear_toCLM_apply] using
      hΘ₀sm.comp ((shear k (-c)).toContinuousLinearMap.contDiff)
  · -- `Θ' ∘ Φ' = id`
    intro y
    show Θ₀ (shear k (-c) (shear k c (Φ₀ y))) = y
    rw [shear_neg_comp_shear, hΘΦ y]
  · -- `Φ' ∘ Θ' = id`
    intro ξ
    show shear k c (Φ₀ (Θ₀ (shear k (-c) ξ))) = ξ
    rw [hΦΘ (shear k (-c) ξ), shear_comp_shear_neg]
  · -- the tube is flat for the sheared chart
    intro x hx
    have hfix := shear_fixes_sheetASub c (hsheet x hx)
    show shear k c (Φ₀ (f x)) ∈ Work.Drive.Whitney.sheetA
    rw [hfix]
    exact hsheet x hx
  · -- the straightened segment
    intro x hx
    obtain ⟨z, hzU, hz⟩ := hseg x hx
    refine ⟨z, hzU, ?_⟩
    show shear k c (Φ₀ (f z)) = (x, 0, 0, 0)
    rw [hz]
    exact shear_fixes_sheetASub c (ξ := ((x, 0, 0, 0) : Work.Drive.Whitney.Mdl k)) ⟨rfl, rfl⟩
  · -- the first pin
    show shear k c (Φ₀ (f p₁)) = ((-1 : ℝ), 0, 0, 0)
    rw [hpin₁]
    exact shear_fixes_sheetASub c (ξ := (((-1 : ℝ), 0, 0, 0) : Work.Drive.Whitney.Mdl k))
      ⟨rfl, rfl⟩
  · -- the second pin
    show shear k c (Φ₀ (f q₁)) = ((1 : ℝ), 0, 0, 0)
    rw [hpin₂]
    exact shear_fixes_sheetASub c (ξ := (((1 : ℝ), 0, 0, 0) : Work.Drive.Whitney.Mdl k))
      ⟨rfl, rfl⟩
  · -- the arc row
    intro t ht
    show shear k c (Φ₀ (f (γ₁ t))) = (2 * t - 1, 0, 0, 0)
    rw [harc₀ t ht]
    exact shear_fixes_sheetASub c (ξ := ((2 * t - 1, 0, 0, 0) : Work.Drive.Whitney.Mdl k))
      ⟨rfl, rfl⟩

end Work.Drive.PushDisc
