import Mathlib
import Submission.Work.Drive.Push.tubeFlattening
import Submission.Work.Whitney.CutPush.BigonData

namespace Work.Drive.Whitney

theorem tubeFlatteningFirst {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M] :
  ∀ (hn : 3 ≤ n) (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y, Function.Injective (mfderiv
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y))
    (W : Set M) (hWopen : IsOpen W) (hWcpt : IsCompact (closure W))
    (p₁ p₂ q₁ q₂ : M)
    (hW₁ : p₁ ∈ W) (hW₂ : p₂ ∈ W) (hW₃ : q₁ ∈ W) (hW₄ : q₂ ∈ W)
    (hp₁p₂ : p₁ ≠ p₂) (hq₁q₂ : q₁ ≠ q₂)
    (hp₁q₁ : p₁ ≠ q₁) (hp₁q₂ : p₁ ≠ q₂) (hp₂q₁ : p₂ ≠ q₁) (hp₂q₂ : p₂ ≠ q₂)
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
    (γ₁ γ₂ : ℝ → M) (hγ₁ : Continuous γ₁) (hγ₂ : Continuous γ₂)
    (hγ₁0 : γ₁ 0 = p₁) (hγ₁1 : γ₁ 1 = q₁) (hγ₂0 : γ₂ 0 = p₂) (hγ₂1 : γ₂ 1 = q₂)
    (hγW₁ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t ∈ W)
    (hγW₂ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₂ t ∈ W)
    (hγ₁inj : Set.InjOn γ₁ (Set.Icc (0 : ℝ) 1))
    (hγ₂inj : Set.InjOn γ₂ (Set.Icc (0 : ℝ) 1))
    (hγ₁smooth : ContMDiff (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) γ₁)
    (hγ₂smooth : ContMDiff (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) γ₂)
    (hγ₁imm : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      Function.Injective (mfderiv (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) γ₁ t))
    (hγ₂imm : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      Function.Injective (mfderiv (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) γ₂ t))
    (hγdisj : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      γ₁ s = γ₂ t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hγend : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      f (γ₁ s) = f (γ₂ t) → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hsign : Work.Whitney.OppositeType f γ₁ γ₂ p₁ p₂ q₁ q₂),
    ∃ (U : Set M) (A Ainv : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n)))
      (K : Submodule ℝ (EuclideanSpace ℝ (Fin (2 * n)))),
      IsOpen U ∧ closure U ⊆ W ∧ γ₁ '' Set.Icc (0 : ℝ) 1 ⊆ U ∧ p₂ ∉ U ∧ q₂ ∉ U ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ainv ∧
      Function.LeftInverse Ainv A ∧ Function.RightInverse Ainv A ∧
      Module.finrank ℝ K = n ∧ (∀ x : M, x ∈ U → A (f x) ∈ K) := by
  intro hn f hf himm W hWopen hWcpt p₁ p₂ q₁ q₂ hW₁ hW₂ hW₃ hW₄ hp₁p₂ hq₁q₂ hp₁q₁ hp₁q₂ hp₂q₁
    hp₂q₂ hfp hfq hclean hsep htransP htransQ γ₁ γ₂ hγ₁ hγ₂ hγ₁0 hγ₁1 hγ₂0 hγ₂1 hγW₁ hγW₂ hγ₁inj
    hγ₂inj hγ₁smooth hγ₂smooth hγ₁imm hγ₂imm hγdisj hγend hsign
  -- ## the points `p₂`, `q₂` of the *opposite* double point are not on the arc `γ₁ '' Icc 0 1`
  have hp₂arc : p₂ ∉ γ₁ '' Set.Icc (0 : ℝ) 1 := by
    rintro ⟨t, ht, htp⟩
    have hdisj : (t = 0 ∧ (0 : ℝ) = 0) ∨ (t = 1 ∧ (0 : ℝ) = 1) :=
      hγdisj t ht 0 (by norm_num) (by rw [htp, hγ₂0])
    rcases hdisj with ⟨ht0, -⟩ | ⟨-, h01⟩
    · rw [ht0, hγ₁0] at htp
      exact hp₁p₂ htp
    · norm_num at h01
  have hq₂arc : q₂ ∉ γ₁ '' Set.Icc (0 : ℝ) 1 := by
    rintro ⟨t, ht, htp⟩
    have hdisj : (t = 0 ∧ (1 : ℝ) = 0) ∨ (t = 1 ∧ (1 : ℝ) = 1) :=
      hγdisj t ht 1 (by norm_num) (by rw [htp, hγ₂1])
    rcases hdisj with ⟨-, h10⟩ | ⟨ht1, -⟩
    · norm_num at h10
    · rw [ht1, hγ₁1] at htp
      exact hq₁q₂ htp
  -- ## the `clean` hypothesis in the relabelled bigon (pairs swapped)
  have hclean' : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₂ ∧ z = p₁) ∨ (y = p₁ ∧ z = p₂) ∨ (y = q₂ ∧ z = q₁) ∨
        (y = q₁ ∧ z = q₂) := by
    intro y z hy hz hyz
    rcases hclean y z hy hz hyz with h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  -- ## an open tube `U₀` around the arc, avoiding `p₂`, `q₂`, on which `f` is injective
  obtain ⟨U₀, hU₀o, hU₀arc, hU₀cl, hp₂U₀, hq₂U₀, hU₀inj⟩ :=
    Work.Whitney.CutPush.exists_tube_injOn hclean' hWopen γ₁ hγ₁
      (fun t ht => hγW₁ t ht) hp₂arc hq₂arc
  -- ## the alignment half (straighten the arc `γ₁`, align the tangent planes to a fixed plane)
  obtain ⟨A₁, A₁i, A₂, A₂i, K, a, e, hA₁, hA₁i, hA₁l, hA₁r, hA₂, hA₂i, hA₂l, hA₂r,
    he, hKfin, haff, hrange⟩ :=
    Work.Drive.Push.spineAlignment hn f hf himm γ₁ hγ₁smooth hγ₁imm hγ₁inj U₀ hU₀o hU₀arc hU₀inj
  -- ## the graph-function half (fibred shear flattening the aligned tube onto `K`)
  set F : M → EuclideanSpace ℝ (Fin (2 * n)) := fun y => A₂ (A₁ (f y)) with hFdef
  have hFsm : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) F :=
    hA₂.contMDiff.comp (hA₁.contMDiff.comp hf)
  have hA₁fsm : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : M => A₁ (f y)) := hA₁.contMDiff.comp hf
  have hA₁fimm : ∀ y : M, Function.Injective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) (fun y : M => A₁ (f y)) y) :=
    Work.Whitney.CutPush.mfderiv_comp_injective f hf himm A₁ A₁i hA₁ hA₁i hA₁l
  have hFimm : ∀ y : M, Function.Injective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) F y) := by
    intro y
    exact Work.Whitney.CutPush.mfderiv_comp_injective (fun z : M => A₁ (f z)) hA₁fsm hA₁fimm
      A₂ A₂i hA₂ hA₂i hA₂l y
  obtain ⟨U, A₃, A₃i, hUo, hUarc, hA₃, hA₃i, hA₃l, hA₃r, hflat⟩ :=
    Work.Drive.Push.flattenAlignedSpine hn F hFsm hFimm γ₁ hγ₁smooth K hKfin a e he haff hrange
  -- ## assembly
  refine ⟨U ∩ U₀, fun y => A₃ (A₂ (A₁ y)), fun y => A₁i (A₂i (A₃i y)), K, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, hKfin, ?_⟩
  · exact hUo.inter hU₀o
  · exact (closure_mono Set.inter_subset_right).trans hU₀cl
  · exact fun x hx => ⟨hUarc hx, hU₀arc hx⟩
  · exact fun hx => hp₂U₀ hx.2
  · exact fun hx => hq₂U₀ hx.2
  · exact hA₃.comp (hA₂.comp hA₁)
  · exact hA₁i.comp (hA₂i.comp hA₃i)
  · intro y
    show A₁i (A₂i (A₃i (A₃ (A₂ (A₁ y))))) = y
    rw [hA₃l (A₂ (A₁ y)), hA₂l (A₁ y), hA₁l y]
  · intro y
    show A₃ (A₂ (A₁ (A₁i (A₂i (A₃i y))))) = y
    rw [hA₁r (A₂i (A₃i y)), hA₂r (A₃i y), hA₃r y]
  · intro x hx
    exact hflat x hx.1


end Work.Drive.Whitney
