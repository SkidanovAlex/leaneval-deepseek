import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.Drive.N2.roundConfigPicture

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology in
/-- **Pictures from arbitrary component curves** (§3.1 (b) of `N2Lead/NOTES_LEAD_saddlePacket.md`).

This is `Work.Drive.N2.exists_picture_of_config` (`Submission/Work/Drive/N2/pictureOfConfig.lean`,
PROVED) with the round configuration `D : RoundConfig n` replaced by *arbitrary* smooth `1`-periodic
curves `c i`.  The D2 packet of the saddle window needs exactly this: its anchor curve
`c i t = cE3 (r (Θ t) * exp (i * Θ t))` is a polar curve (and, in the Möbius case, its image under a
slab twist), not a round circle.

The conclusion is the same as that of `exists_picture_of_config`: a `C^∞` map `A : M → ℝ³`
extending the prescribed curve along `γ`, injective on the level `f = b` and `ker df`-immersive
there.  The hypotheses `hc`, `hcper`, `hcinj`, `hcderiv` are the rows that `RoundConfig.circle`
satisfies in the parent (smoothness, `1`-periodicity, injectivity modulo one period across
components, and nonvanishing velocity).  Proof sketch (shorter than copying the parent): apply
`Work.Drive.N2.exists_contMDiff_extend_of_circle` to each `c i` to get `V i` with
`V i (γ i t) = c i t`, then glue by bumps `χ i` that are `1` on the curve `i` and `0` on the others
(compactness + `hγdisj`), as in `roundConfigPictureGlobal`. -/
theorem exists_picture_of_curves {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} {b : ℝ} {n : ℕ} (γ : Fin n → ℝ → M)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = b → ¬ Work.Drive.Morse.IsCritical f x)
    (hγsm : ∀ i, ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (γ i))
    (hγval : ∀ (i : Fin n) (x : ℝ), f (γ i x) = b)
    (hγper : ∀ (i : Fin n) (x : ℝ), γ i (x + 1) = γ i x)
    (hγinj : ∀ i : Fin n, Set.InjOn (γ i) (Set.Ico 0 1))
    (hγlev : ∀ x : M, f x = b → ∃ (i : Fin n) (t : ℝ), x = γ i t)
    (hγdisj : ∀ i j : Fin n, i ≠ j → Disjoint (Set.range (γ i)) (Set.range (γ j)))
    (hγker : ∀ (i : Fin n) (x : ℝ) (v : TangentSpace (𝓡 2) (γ i x)),
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f (γ i x) v = 0 →
        ∃ t : ℝ, mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (γ i) x t = v)
    (c : Fin n → ℝ → EuclideanSpace ℝ (Fin 3))
    (hc : ∀ i : Fin n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (c i))
    (hcper : ∀ (i : Fin n) (x : ℝ), c i (x + 1) = c i x)
    (hcinj : ∀ (i j : Fin n) (x y : ℝ), c i x = c j y → i = j ∧ ∃ k : ℤ, x = y + k)
    (hcderiv : ∀ (i : Fin n) (x : ℝ), deriv (c i) x ≠ 0) :
    ∃ A : M → EuclideanSpace ℝ (Fin 3),
      ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) A ∧
      (∀ (i : Fin n) (x : ℝ), A (γ i x) = c i x) ∧
      (∀ x y : M, (∃ (i : Fin n) (t : ℝ), x = γ i t) →
        (∃ (j : Fin n) (u : ℝ), y = γ j u) → A x = A y → x = y) ∧
      (∀ x : M, (∃ (i : Fin n) (t : ℝ), x = γ i t) →
        ∀ v : TangentSpace (𝓡 2) x, mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 →
          mfderiv (𝓡 2) (𝓡 3) A x v = 0 → v = 0) := by
  classical
  haveI hLV : Work.Drive.N2.LevelHyp f b := ⟨hf, hreg⟩
  have hperγ : ∀ i : Fin n, Function.Periodic (γ i) 1 := fun i => hγper i
  -- ### every curve is an immersion
  have himm : ∀ (i : Fin n) (t : ℝ), mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (γ i) t 1 ≠ 0 := by
    intro i t h1
    obtain ⟨v, hvne, hv0⟩ :=
      Work.Drive.N2.exists_ne_zero_ker (mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (γ i t))
    obtain ⟨s, hs⟩ := hγker i t v hv0
    have hsa : s • (1 : TangentSpace 𝓘(ℝ,ℝ) t) = s := by
      show s * 1 = s
      ring
    have hs0 : (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (γ i) t) s = 0 := by
      conv_lhs => rw [← hsa, ContinuousLinearMap.map_smul]
      rw [h1, smul_zero]
    rw [hs] at hs0
    exact hvne hs0
  -- ### each prescribed curve extends to a globally smooth map
  have hext : ∀ i : Fin n, ∃ V : M → EuclideanSpace ℝ (Fin 3),
      ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) V ∧ ∀ t, V (γ i t) = c i t := by
    intro i
    obtain ⟨V, h1, h2⟩ := Work.Drive.N2.exists_contMDiff_extend_of_circle
      (f := f) (b := b) (γ i) (hγsm i) (hγval i) (hperγ i) (hγinj i) (himm i)
      (c i) (hc i) (hcper i)
    exact ⟨V, h1, h2⟩
  choose V hVsm hVval using hext
  -- ### bumps separating the curves
  have hbump : ∀ i : Fin n, ∃ χ : M → ℝ,
      ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧
      (∀ t, χ (γ i t) = 1) ∧ (∀ j, j ≠ i → ∀ t, χ (γ j t) = 0) := by
    intro i
    have hKi : IsCompact (Set.range (γ i)) := by
      rw [Work.Drive.N2.range_periodic (hperγ i)]
      exact isCompact_Icc.image (hγsm i).continuous
    have hKo : IsCompact (⋃ j : {j : Fin n // j ≠ i}, Set.range (γ j.1)) := by
      refine isCompact_iUnion fun j => ?_
      rw [Work.Drive.N2.range_periodic (hperγ j.1)]
      exact isCompact_Icc.image (hγsm j.1).continuous
    have hdisj : Disjoint (Set.range (γ i))
        (⋃ j : {j : Fin n // j ≠ i}, Set.range (γ j.1)) := by
      rw [Set.disjoint_iUnion_right]
      intro j
      exact hγdisj i j.1 (Ne.symm j.2)
    obtain ⟨U, W, hUo, hWo, hKU, hKW, hUW⟩ :=
      SeparatedNhds.of_isCompact_isCompact hKi hKo hdisj
    obtain ⟨χ, V', hχsm, hχsupp, hV'open, hKV', hχone, _⟩ :=
      Work.Drive.N2.exists_contMDiff_bump_tsupport hKi hUo hKU
    refine ⟨χ, hχsm, ?_, ?_⟩
    · intro t
      exact hχone _ (hKV' ⟨t, rfl⟩)
    · intro j hj t
      by_contra hne
      have h1 : γ j t ∈ Function.support χ := by rwa [Function.mem_support]
      have h3 : γ j t ∈ U := hχsupp (subset_closure h1)
      have h4 : γ j t ∈ W := hKW (Set.mem_iUnion.mpr ⟨⟨j, hj⟩, ⟨t, rfl⟩⟩)
      exact Set.disjoint_left.mp hUW h3 h4
  choose χ hχsm hχone hχzero using hbump
  -- ### the glued map
  let A : M → EuclideanSpace ℝ (Fin 3) := fun x => ∑ i : Fin n, χ i x • V i x
  have hAsm : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) A := by
    rw [show A = fun x : M => ∑ i : Fin n, χ i x • V i x from rfl]
    exact ContMDiff.sum fun i _ => (hχsm i).smul (hVsm i)
  have hAval : ∀ (i : Fin n) (t : ℝ), A (γ i t) = c i t := by
    intro i t
    show (∑ j : Fin n, χ j (γ i t) • V j (γ i t)) = c i t
    rw [Finset.sum_eq_single i]
    · rw [hχone i t, one_smul, hVval i t]
    · intro j _ hj
      rw [hχzero j i (Ne.symm hj) t, zero_smul]
    · intro hmem
      exact absurd (Finset.mem_univ i) hmem
  refine ⟨A, hAsm, hAval, ?_, ?_⟩
  · -- injectivity on the level set
    intro x y hx hy hxy
    obtain ⟨i, t, rfl⟩ := hx
    obtain ⟨j, u, rfl⟩ := hy
    rw [hAval i t, hAval j u] at hxy
    obtain ⟨hij, k, hk⟩ := hcinj i j t u hxy
    rw [hij, hk, Work.Drive.N2.periodic_int (hperγ j) k u]
  · -- immersion along `ker df` on the level set
    intro x hx v hv hv0
    obtain ⟨i, t, rfl⟩ := hx
    obtain ⟨t', ht'⟩ := hγker i t v hv
    have hA_diff : MDifferentiableAt (𝓡 2) (𝓡 3) A (γ i t) :=
      hAsm.contMDiffAt.mdifferentiableAt (by simp)
    have hγ_diff : MDifferentiableAt 𝓘(ℝ,ℝ) (𝓡 2) (γ i) t :=
      (hγsm i).contMDiffAt.mdifferentiableAt (by simp)
    have hcf : (A ∘ γ i) = c i := funext fun u => hAval i u
    have hcomp : (mfderiv 𝓘(ℝ,ℝ) (𝓡 3) (c i) t) t'
        = (mfderiv (𝓡 2) (𝓡 3) A (γ i t)) ((mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (γ i) t) t') := by
      have h1 : (mfderiv 𝓘(ℝ,ℝ) (𝓡 3) (c i) t)
          = mfderiv 𝓘(ℝ,ℝ) (𝓡 3) (A ∘ γ i) t := by rw [hcf]
      rw [h1]
      exact mfderiv_comp_apply (x := t) (f := γ i) (g := A) hA_diff hγ_diff t'
    have hmid : (mfderiv (𝓡 2) (𝓡 3) A (γ i t)) ((mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (γ i) t) t') = 0 := by
      rw [ht']
      exact hv0
    have hzero : (mfderiv 𝓘(ℝ,ℝ) (𝓡 3) (c i) t) t' = 0 := hcomp.trans hmid
    have hL1 : (mfderiv 𝓘(ℝ,ℝ) (𝓡 3) (c i) t) (1 : TangentSpace 𝓘(ℝ,ℝ) t) =
        deriv (c i) t := by
      rw [mfderiv_eq_fderiv]
      rfl
    have ht'0 : t' = 0 := by
      have hsa : t' • (1 : TangentSpace 𝓘(ℝ,ℝ) t) = t' := by
        show t' * 1 = t'
        ring
      have hlin : (mfderiv 𝓘(ℝ,ℝ) (𝓡 3) (c i) t) t' = t' • deriv (c i) t := by
        conv_lhs => rw [← hsa, ContinuousLinearMap.map_smul]
        exact congrArg (fun w : EuclideanSpace ℝ (Fin 3) => t' • w) hL1
      rw [hzero] at hlin
      rcases smul_eq_zero.mp hlin.symm with h | h
      · exact h
      · exact absurd h (hcderiv i t)
    obtain rfl : t' = 0 := ht'0
    rw [← ht']
    exact ContinuousLinearMap.map_zero _


end Work.Drive.N2Lead
