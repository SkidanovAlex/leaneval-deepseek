import Mathlib
import Submission.Work.Drive.Whitney.modelChart2

/-!
# The core geometric data of the MARK II model chart

`Work.Drive.Whitney.ModelChartData2` carries the bookkeeping fields `ε` (the tube thickness), `δ`
(the separation between the two patches) and `b` (the amplitude of the push).  This module shows
that, given the *numeric margin* between the tube thickness and the separation, all of them are
forced, so that the remaining obligation of the compact `n ≥ 3` case is the two-sheet normal form
together with that margin:

* `Work.Drive.Whitney.ModelChartCore` — the two-sheet presentation (chart `Φ`, sheet chart `σ`,
  height function `c`, tube `U₁` mapping into a thin piece of `sheetA`) together with the single
  numeric clause `hsepε`: the tube's thinness radius is *strictly below* a valid separation of the
  two patches.  (`Work.Drive.Whitney.exists_separation`, `separation2.lean`, supplies the separation
  for the given tube; the strict margin is the part that depends on the choice of the tube.)
* `Work.Drive.Whitney.exists_amplitude'` — for every `ε₀ < δ` there is a smooth amplitude `b`,
  supported in `{|x| < 5/4}`, with `ε₀ < ‖b (±1)‖` and `‖b x‖ < δ` everywhere (a routine bump:
  `b x = c • (smoothTransition (16/9 * (25/16 - x²)) • e₀)` with `ε₀ < c < δ` and `e₀` a unit
  vector).
* `Work.Drive.Whitney.modelChartData2_of_core` — the assembly.
-/

namespace Work.Drive.Whitney

open scoped Manifold ContDiff
open Set Metric

set_option linter.unusedVariables false

variable {k : ℕ}

/-- **The amplitude of the push.**  For every `ε₀ < δ` there is a smooth `b`, vanishing for
`|x| ≥ 5/4`, with `ε₀ < ‖b (±1)‖` and `‖b x‖ < δ` everywhere. -/
theorem exists_amplitude' (hk : 1 ≤ k) {ε₀ δ : ℝ} (hε₀ : 0 < ε₀) (hlt : ε₀ < δ) :
    ∃ b : ℝ → EuclideanSpace ℝ (Fin k),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b ∧ (∀ x : ℝ, 5 / 4 ≤ |x| → b x = 0) ∧
      ε₀ < ‖b 1‖ ∧ ε₀ < ‖b (-1)‖ ∧ (∀ x : ℝ, ‖b x‖ < δ) := by
  classical
  -- a unit vector
  obtain ⟨i⟩ : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  set e₀ : EuclideanSpace ℝ (Fin k) := EuclideanSpace.single i 1 with he₀
  have he₀norm : ‖e₀‖ = 1 := by
    rw [he₀, PiLp.norm_single]
    simp
  -- the amplitude constant
  set c : ℝ := (ε₀ + δ) / 2 with hc
  have hcε : ε₀ < c := by rw [hc]; linarith
  have hcδ : c < δ := by rw [hc]; linarith
  have hcpos : 0 < c := lt_trans hε₀ hcε
  -- the bump
  set β : ℝ → ℝ := fun x => Real.smoothTransition (16 / 9 * (25 / 16 - x ^ 2)) with hβ
  have hβsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β := by
    rw [hβ]
    exact (Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).comp
      (contDiff_const.mul (contDiff_const.sub (contDiff_id.pow 2)))
  have hβ1 : β 1 = 1 := by
    rw [hβ]
    exact Real.smoothTransition.one_of_one_le (by norm_num)
  have hβm1 : β (-1) = 1 := by
    rw [hβ]
    exact Real.smoothTransition.one_of_one_le (by norm_num)
  have hβzero : ∀ x : ℝ, 5 / 4 ≤ |x| → β x = 0 := by
    intro x hx
    rw [hβ]
    refine Real.smoothTransition.zero_of_nonpos ?_
    have h1 : 1 ≤ |x| ^ 2 := by nlinarith [hx, abs_nonneg x]
    rw [show x ^ 2 = |x| ^ 2 from (sq_abs x).symm]
    nlinarith
  have hβnn : ∀ x : ℝ, 0 ≤ β x := fun x => Real.smoothTransition.nonneg _
  have hβle : ∀ x : ℝ, β x ≤ 1 := fun x => Real.smoothTransition.le_one _
  set b : ℝ → EuclideanSpace ℝ (Fin k) := fun x => c • (β x • e₀) with hbdef
  have hbsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b := by
    rw [hbdef]
    exact (contDiff_const (c := c)).smul (hβsmooth.smul (contDiff_const (c := e₀)))
  have hbzero : ∀ x : ℝ, 5 / 4 ≤ |x| → b x = 0 := by
    intro x hx
    show c • (β x • e₀) = 0
    rw [hβzero x hx, zero_smul, smul_zero]
  have hb1' : ε₀ < ‖b 1‖ := by
    show ε₀ < ‖c • (β 1 • e₀)‖
    rw [hβ1, one_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hcpos, he₀norm, mul_one]
    exact hcε
  have hbm1' : ε₀ < ‖b (-1)‖ := by
    show ε₀ < ‖c • (β (-1) • e₀)‖
    rw [hβm1, one_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hcpos, he₀norm, mul_one]
    exact hcε
  have hbbd' : ∀ x : ℝ, ‖b x‖ < δ := by
    intro x
    show ‖c • (β x • e₀)‖ < δ
    rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hcpos, Real.norm_eq_abs,
      abs_of_nonneg (hβnn x), he₀norm, mul_one]
    calc c * β x ≤ c * 1 := mul_le_mul_of_nonneg_left (hβle x) (le_of_lt hcpos)
      _ = c := mul_one c
      _ < δ := hcδ
  exact ⟨b, hbsmooth, hbzero, hb1', hbm1', hbbd'⟩

/-- **The core geometric data of the MARK II model chart.**  Everything except the numbers
`ε, δ, b` — which are forced by the single numeric clause `hsepε` below. -/
structure ModelChartCore (n : ℕ) {M : Type*} [TopologicalSpace M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (W : Set M) (p₁ p₂ q₁ q₂ : M) where
  k : ℕ
  hk : n = k + 1
  c : ℝ → ℝ
  hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c
  hc1 : c 1 = 0
  hcm1 : c (-1) = 0
  hczero : ∀ x : ℝ, |x| < 3 / 2 → c x = 0 → x = 1 ∨ x = -1
  Φ : EuclideanSpace ℝ (Fin (2 * n)) → Mdl k
  Θ : Mdl k → EuclideanSpace ℝ (Fin (2 * n))
  hΦsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ
  hΘsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ
  hΘΦ : ∀ y, Θ (Φ y) = y
  hΦΘ : ∀ ξ, Φ (Θ ξ) = ξ
  regσ : Set (ℝ × EuclideanSpace ℝ (Fin k))
  hregσo : IsOpen regσ
  hregsub : closure (reg2 (k := k)) ⊆ regσ
  σ : ℝ × EuclideanSpace ℝ (Fin k) → M
  hσc : Continuous σ
  hσ : ∀ p ∈ regσ, f (σ p) = Θ (p.1, c p.1, 0, p.2)
  hp₂ : σ ((-1 : ℝ), 0) = p₂
  hq₂ : σ ((1 : ℝ), 0) = q₂
  hW₀o : IsOpen (σ '' reg2 (k := k))
  hW₀σo : IsOpen (σ '' regσ)
  hW₀W : σ '' regσ ⊆ W
  hpatch₁ : p₁ ∉ σ '' regσ
  hpatch₃ : q₁ ∉ σ '' regσ
  U₁ : Set M
  hU₁o : IsOpen U₁
  hU₁p₁ : p₁ ∈ U₁
  hU₁q₁ : q₁ ∈ U₁
  hU₁A : ∀ y ∈ U₁, Φ (f y) ∈ sheetA
  /-- **the numeric clause**: there are a valid separation `δ` of the two patches and a tube
  thickness `ε₀ < δ` (the thrust of the construction: the tube is thin relative to the gap between
  the patches). -/
  hsepε : ∃ δ ε₀ : ℝ, 0 < δ ∧ 0 < ε₀ ∧ ε₀ < δ ∧
    (∀ y : M, y ∉ U₁ → y ∉ σ '' regσ → ∀ p ∈ closure (reg2 (k := k)),
      δ ≤ ‖Φ (f y) - (p.1, c p.1, 0, p.2)‖) ∧
    (∀ y ∈ U₁, ‖(Φ (f y)).2.2.1‖ < ε₀)

/-- **The core data gives the MARK II model chart.** -/
theorem modelChartData2_of_core {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (W : Set M) (p₁ p₂ q₁ q₂ : M)
    (D : ModelChartCore n f W p₁ p₂ q₁ q₂) (hk1 : 1 ≤ D.k) :
    Nonempty (ModelChartData2 n f W p₁ p₂ q₁ q₂) := by
  classical
  obtain ⟨k, hk, c, hc, hc1, hcm1, hczero, Φ, Θ, hΦsm, hΘsm, hΘΦ, hΦΘ, regσ, hregσo, hregsub,
    σ, hσc, hσ, hp₂, hq₂, hW₀o, hW₀σo, hW₀W, hpatch₁, hpatch₃, U₁, hU₁o, hU₁p₁, hU₁q₁, hU₁A,
    hsepε⟩ := D
  obtain ⟨δ, ε₀, hδ, hε₀, hε₀δ, hsep, hthin⟩ := hsepε
  obtain ⟨b, hb, hbsupp, hb1, hbm1, hbbd⟩ := exists_amplitude' (k := k) hk1 hε₀ hε₀δ
  exact ⟨⟨k, hk, c, hc, hc1, hcm1, hczero, b, hb, hbsupp, ε₀, hε₀, hb1, hbm1, δ, hδ, hbbd,
    Φ, Θ, hΦsm, hΘsm, hΘΦ, hΦΘ, regσ, hregσo, hregsub, σ, hσc, hσ, hp₂, hq₂, hW₀o, hW₀σo,
    hW₀W, hpatch₁, hpatch₃, U₁, hU₁o, hU₁p₁, hU₁q₁, hU₁A, hthin, hsep⟩⟩

end Work.Drive.Whitney

namespace Work.Drive.Whitney

open scoped Manifold ContDiff
open Set Metric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
  [T2Space M] [CompactSpace M] [SecondCountableTopology M]

/-- **The single remaining geometric obligation of the compact `n ≥ 3` case**, in its sharpest
form: the core two-sheet presentation of the bigon, together with the numeric clause `hsepε` (a
tube thin relative to the gap between the two patches).  Everything else — the model shear, the
amplitude, the separation, the frontier clause — is proved. -/
def ModelChartCoreAll (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M] : Prop :=
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
    (hγ₁smooth : ContMDiff 𝓘(ℝ, ℝ) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) γ₁)
    (hγ₂smooth : ContMDiff 𝓘(ℝ, ℝ) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) γ₂)
    (hγ₁imm : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      Function.Injective (mfderiv 𝓘(ℝ, ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) γ₁ t))
    (hγ₂imm : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      Function.Injective (mfderiv 𝓘(ℝ, ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) γ₂ t))
    (hγdisj : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      γ₁ s = γ₂ t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hγend : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      f (γ₁ s) = f (γ₂ t) → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hsign : Work.Whitney.OppositeType f γ₁ γ₂ p₁ p₂ q₁ q₂),
    Nonempty (ModelChartCore n f W p₁ p₂ q₁ q₂)

/-- **The target from the core geometric data.** -/
theorem hasPushSignedSmooth_of_modelChartCoreAll (h : ModelChartCoreAll n M) :
    Work.Drive.HasPushSignedSmooth n M := by
  refine hasPushSignedSmooth_of_modelChartDataAll2 fun hn f hf himm W hWopen hWcpt p₁ p₂ q₁ q₂
    hW₁ hW₂ hW₃ hW₄ hp₁p₂ hq₁q₂ hp₁q₁ hp₁q₂ hp₂q₁ hp₂q₂ hfp hfq hclean hsep htransP htransQ
    γ₁ γ₂ hγ₁ hγ₂ hγ₁0 hγ₁1 hγ₂0 hγ₂1 hγW₁ hγW₂ hγ₁inj hγ₂inj hγ₁smooth hγ₂smooth hγ₁imm
    hγ₂imm hγdisj hγend hsign => ?_
  obtain ⟨D⟩ := h hn f hf himm W hWopen hWcpt p₁ p₂ q₁ q₂ hW₁ hW₂ hW₃ hW₄ hp₁p₂ hq₁q₂ hp₁q₁
    hp₁q₂ hp₂q₁ hp₂q₂ hfp hfq hclean hsep htransP htransQ γ₁ γ₂ hγ₁ hγ₂ hγ₁0 hγ₁1 hγ₂0 hγ₂1
    hγW₁ hγW₂ hγ₁inj hγ₂inj hγ₁smooth hγ₂smooth hγ₁imm hγ₂imm hγdisj hγend hsign
  have hk1 : 1 ≤ D.k := by
    have hDk := D.hk
    omega
  exact modelChartData2_of_core f W p₁ p₂ q₁ q₂ D hk1

end Work.Drive.Whitney
