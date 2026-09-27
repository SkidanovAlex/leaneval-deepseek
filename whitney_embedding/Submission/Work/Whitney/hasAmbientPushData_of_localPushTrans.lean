import Mathlib
import Submission.Work.Whitney.EndgameNF

namespace Work.Whitney

open scoped Manifold ContDiff
open Topology

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

theorem hasAmbientPushData_of_localPushTrans {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (h : Work.Whitney.LocalPushNTrans n M) :
∀ (hn : 3 ≤ n) (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y, Function.Injective (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y))
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
    (hγdisj : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      γ₁ s = γ₂ t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hγend : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      f (γ₁ s) = f (γ₂ t) → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)),
    Work.Whitney.HasAmbientPushData f W p₁ p₂ q₁ q₂ := by
  intro hn f hf himm W hWopen hWcpt p₁ p₂ q₁ q₂ hW₁ hW₂ hW₃ hW₄ hp₁p₂ hq₁q₂
    hp₁q₁ hp₁q₂ hp₂q₁ hp₂q₂ hfp hfq hclean hsep htransP htransQ γ₁ γ₂ hγ₁ hγ₂ hγ₁0 hγ₁1 hγ₂0 hγ₂1
    hγW₁ hγW₂ hγ₁inj hγ₂inj hγdisj hγend
  classical
  -- ## Step 1: the two double values have no third preimage, and are distinct.
  have hpreP : ∀ y : M, f y = f p₂ → y = p₁ ∨ y = p₂ := by
    intro y hy
    by_cases hyW : y ∈ W
    · rcases hclean y p₂ hyW hW₂ hy with h | h | h | h | h
      · exact Or.inr h
      · exact Or.inl h.1
      · exact Or.inr h.1
      · exact absurd h.2 hp₂q₂
      · exact absurd h.2 hp₂q₁
    · exact absurd hy (hsep p₂ y hW₂ hyW).symm
  have hpreQ : ∀ y : M, f y = f q₂ → y = q₁ ∨ y = q₂ := by
    intro y hy
    by_cases hyW : y ∈ W
    · rcases hclean y q₂ hyW hW₄ hy with h | h | h | h | h
      · exact Or.inr h
      · exact absurd h.2 hp₂q₂.symm
      · exact absurd h.2 hp₁q₂.symm
      · exact Or.inl h.1
      · exact Or.inr h.1
    · exact absurd hy (hsep q₂ y hW₄ hyW).symm
  have hPQ : f p₂ ≠ f q₂ := by
    intro hpq
    rcases hclean p₂ q₂ hW₂ hW₄ hpq with h | h | h | h | h
    · exact hp₂q₂ h
    · exact hp₁p₂ h.1.symm
    · exact absurd h.2 hp₁q₂.symm
    · exact hp₂q₁ h.1
    · exact hp₂q₂ h.1
  -- ## Step 2: isolation radii.
  have hclosedP : IsClosed (f '' Wᶜ) :=
    (hWopen.isClosed_compl.isCompact.image hf.continuous).isClosed
  have hnotinP : f p₂ ∉ f '' Wᶜ := by
    rintro ⟨y, hy, hfy⟩
    exact hsep p₂ y hW₂ hy hfy.symm
  have isoP : ∃ ε > 0, ∀ y : M, ‖f y - f p₂‖ < ε → y ∈ W := by
    have hmain : ∃ ε > 0, ∀ b ∈ f '' Wᶜ, ε ≤ dist (f p₂) b := by
      by_contra hcon
      push_neg at hcon
      apply hnotinP
      rw [← hclosedP.closure_eq, Metric.mem_closure_iff]
      exact fun ε hε => hcon ε hε
    obtain ⟨ε, hε, hε'⟩ := hmain
    refine ⟨ε, hε, fun y hy => ?_⟩
    by_contra hyW
    have hb : f y ∈ f '' Wᶜ := ⟨y, hyW, rfl⟩
    have h1 : ε ≤ dist (f p₂) (f y) := hε' (f y) hb
    rw [dist_eq_norm, norm_sub_rev] at h1
    linarith
  have hclosedQ : IsClosed (f '' Wᶜ) := hclosedP
  have hnotinQ : f q₂ ∉ f '' Wᶜ := by
    rintro ⟨y, hy, hfy⟩
    exact hsep q₂ y hW₄ hy hfy.symm
  have isoQ : ∃ ε > 0, ∀ y : M, ‖f y - f q₂‖ < ε → y ∈ W := by
    have hmain : ∃ ε > 0, ∀ b ∈ f '' Wᶜ, ε ≤ dist (f q₂) b := by
      by_contra hcon
      push_neg at hcon
      apply hnotinQ
      rw [← hclosedQ.closure_eq, Metric.mem_closure_iff]
      exact fun ε hε => hcon ε hε
    obtain ⟨ε, hε, hε'⟩ := hmain
    refine ⟨ε, hε, fun y hy => ?_⟩
    by_contra hyW
    have hb : f y ∈ f '' Wᶜ := ⟨y, hyW, rfl⟩
    have h1 : ε ≤ dist (f q₂) (f y) := hε' (f y) hb
    rw [dist_eq_norm, norm_sub_rev] at h1
    linarith
  -- ## Step 3: the common small radius.
  obtain ⟨εP, hεPpos, hεP⟩ := isoP
  obtain ⟨εQ, hεQpos, hεQ⟩ := isoQ
  have hDpos : 0 < ‖f p₂ - f q₂‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hPQ)
  set R : ℝ := min (min εP εQ) ‖f p₂ - f q₂‖ / 100 with hRdef
  have hm1 : min (min εP εQ) ‖f p₂ - f q₂‖ ≤ εP :=
    le_trans (min_le_left _ _) (min_le_left _ _)
  have hm2 : min (min εP εQ) ‖f p₂ - f q₂‖ ≤ εQ :=
    le_trans (min_le_left _ _) (min_le_right _ _)
  have hm3 : min (min εP εQ) ‖f p₂ - f q₂‖ ≤ ‖f p₂ - f q₂‖ := min_le_right _ _
  have hRm : 100 * R ≤ min (min εP εQ) ‖f p₂ - f q₂‖ := by rw [hRdef]; linarith
  have hmpos : 0 < min (min εP εQ) ‖f p₂ - f q₂‖ := lt_min (lt_min hεPpos hεQpos) hDpos
  have hRpos : 0 < R := by rw [hRdef]; linarith
  have hRleP : R ≤ εP / 100 := by linarith [hRm, hm1]
  have hRleQ : R ≤ εQ / 100 := by linarith [hRm, hm2]
  have hRleD : R ≤ ‖f p₂ - f q₂‖ / 100 := by linarith [hRm, hm3]
  have hRεP : R < εP := by nlinarith [hRleP, hεPpos]
  have hR2εP : 2 * R < εP := by nlinarith [hRleP, hεPpos]
  have hRεQ : R < εQ := by nlinarith [hRleQ, hεQpos]
  have hR2εQ : 2 * R < εQ := by nlinarith [hRleQ, hεQpos]
  have hRD : 7 * R < ‖f p₂ - f q₂‖ := by nlinarith [hRleD, hDpos]
  -- ## Step 4: the clean-ball hypotheses for the two cuts.
  have hcleanRP : ∀ y z : M, ‖f y - f p₂‖ < R → ‖f z - f p₂‖ < R → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨ (y = q₂ ∧ z = q₁) := by
    intro y z hy hz h
    exact hclean y z (hεP y (by linarith)) (hεP z (by linarith)) h
  have hcleanRQ : ∀ y z : M, ‖f y - f q₂‖ < R → ‖f z - f q₂‖ < R → f y = f z →
      y = z ∨ (y = q₁ ∧ z = q₂) ∨ (y = q₂ ∧ z = q₁) ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) := by
    intro y z hy hz h
    rcases hclean y z (hεQ y (by linarith)) (hεQ z (by linarith)) h with h0 | h0 | h0 | h0 | h0
    · exact Or.inl h0
    · exact Or.inr (Or.inr (Or.inr (Or.inl h0)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h0)))
    · exact Or.inr (Or.inl h0)
    · exact Or.inr (Or.inr (Or.inl h0))
  have hcleanQ : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = q₁ ∧ z = q₂) ∨ (y = q₂ ∧ z = q₁) ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) := by
    intro y z hy hz h
    rcases hclean y z hy hz h with h0 | h0 | h0 | h0 | h0
    · exact Or.inl h0
    · exact Or.inr (Or.inr (Or.inr (Or.inl h0)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h0)))
    · exact Or.inr (Or.inl h0)
    · exact Or.inr (Or.inr (Or.inl h0))
  -- ## Step 5: the two local pushes.
  obtain ⟨K_P, S_P, ψ_P, σ_P, hKPclosed, hSPopen, hp₁KP, hp₂KP, hKPW, hψPsm, hσPsm,
    hσPψP, hψPσP, hSPsupp, hSPball, hSPfront, hψPdisp, hKPball, hplaceP, hσPfp⟩ :=
    h hn f hf himm W hWopen hWcpt p₁ p₂ q₁ q₂ hp₁p₂ hq₁q₂
      hfp hfq hpreP hclean hsep hW₁ hW₂ htransP R hRpos hcleanRP
  obtain ⟨K_Q, S_Q, ψ_Q, σ_Q, hKQclosed, hSQopen, hq₁KQ, hq₂KQ, hKQW, hψQsm, hσQsm,
    hσQψQ, hψQσQ, hSQsupp, hSQball, hSQfront, hψQdisp, hKQball, hplaceQ, hσQfq⟩ :=
    h hn f hf himm W hWopen hWcpt q₁ q₂ p₁ p₂ hq₁q₂ hp₁p₂
      hfq hfp hpreQ hcleanQ hsep hW₃ hW₄ htransQ R hRpos hcleanRQ
  -- ## Step 6: the objects.
  set W₀ : Set M := W ∩ K_Pᶜ ∩ K_Qᶜ with hW₀def
  set O : Set (EuclideanSpace ℝ (Fin (2 * n))) := (closure S_P ∪ closure S_Q)ᶜ with hOdef
  set ψ : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n)) :=
    fun y => ψ_P (ψ_Q y) with hψdef
  set σ : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n)) :=
    fun y => σ_Q (σ_P y) with hσdef
  have hσψ : ∀ y, σ (ψ y) = y := by
    intro y
    simp only [hσdef, hψdef]
    rw [hσPψP (ψ_Q y), hσQψQ y]
  have hψσ : ∀ y, ψ (σ y) = y := by
    intro y
    simp only [hσdef, hψdef]
    rw [hψQσQ (σ_P y), hψPσP y]
  have hSPball' : ∀ z, z ∈ S_P → ‖z - f p₂‖ < 2 * R := by
    intro z hz
    have := hSPball hz
    rwa [Metric.mem_ball, dist_eq_norm] at this
  have hSQball' : ∀ z, z ∈ S_Q → ‖z - f q₂‖ < 2 * R := by
    intro z hz
    have := hSQball hz
    rwa [Metric.mem_ball, dist_eq_norm] at this
  have hclSP : closure S_P ⊆ Metric.closedBall (f p₂) (2 * R) :=
    (closure_mono hSPball).trans Metric.closure_ball_subset_closedBall
  have hclSQ : closure S_Q ⊆ Metric.closedBall (f q₂) (2 * R) :=
    (closure_mono hSQball).trans Metric.closure_ball_subset_closedBall
  have hnotSP : ∀ z : M, 2 * R < ‖f z - f p₂‖ → f z ∉ closure S_P := by
    intro z hz hmem
    have h := hclSP hmem
    rw [Metric.mem_closedBall, dist_eq_norm] at h
    linarith
  have hnotSQ : ∀ z : M, 2 * R < ‖f z - f q₂‖ → f z ∉ closure S_Q := by
    intro z hz hmem
    have h := hclSQ hmem
    rw [Metric.mem_closedBall, dist_eq_norm] at h
    linarith
  have hεPge : ∀ z : M, z ∉ W → εP ≤ ‖f z - f p₂‖ :=
    fun z hz => not_lt.mp (fun h => hz (hεP z h))
  have hεQge : ∀ z : M, z ∉ W → εQ ≤ ‖f z - f q₂‖ :=
    fun z hz => not_lt.mp (fun h => hz (hεQ z h))
  have hfpSP : f p₂ ∈ S_P := by
    by_contra hc
    have hfix : ψ_P (f p₂) = f p₂ := by
      by_contra hc2; exact hc (hSPsupp (f p₂) hc2)
    have hσ : σ_P (f p₂) = f p₂ := by
      conv_lhs => rw [← hfix]
      exact hσPψP (f p₂)
    refine hσPfp ?_
    rw [hσ]
    exact ⟨p₂, Set.mem_univ p₂, rfl⟩
  have hfqSQ : f q₂ ∈ S_Q := by
    by_contra hc
    have hfix : ψ_Q (f q₂) = f q₂ := by
      by_contra hc2; exact hc (hSQsupp (f q₂) hc2)
    have hσ : σ_Q (f q₂) = f q₂ := by
      conv_lhs => rw [← hfix]
      exact hσQψQ (f q₂)
    refine hσQfq ?_
    rw [hσ]
    exact ⟨q₂, Set.mem_univ q₂, rfl⟩
  -- ## Step 7: assembly.
  have htri : ∀ a b c : EuclideanSpace ℝ (Fin (2 * n)), ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
    intro a b c
    have h := norm_add_le (a - b) (b - c)
    rwa [show (a - b) + (b - c) = a - c by abel] at h
  have hW₀open : IsOpen W₀ := by
    rw [hW₀def]
    exact (hWopen.inter hKPclosed.isOpen_compl).inter hKQclosed.isOpen_compl
  refine ⟨W₀, O, ψ, σ, hW₀open, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `W₀ ⊆ W`
    intro x hx; exact hx.1.1
  · -- `p₂ ∈ W₀`
    refine ⟨⟨hW₂, hp₂KP⟩, ?_⟩
    intro h
    have h1 := hKQball p₂ h
    linarith [h1, hRD]
  · -- `q₂ ∈ W₀`
    refine ⟨⟨hW₄, ?_⟩, hq₂KQ⟩
    intro h
    have h1 := hKPball q₂ h
    rw [norm_sub_rev] at h1
    linarith [h1, hRD]
  · -- `p₁ ∉ W₀`
    intro hx; exact hx.1.2 hp₁KP
  · -- `q₁ ∉ W₀`
    intro hx; exact hx.2 hq₁KQ
  · -- `O` is open
    rw [hOdef]
    exact (isClosed_closure.union isClosed_closure).isOpen_compl
  · -- `f '' frontier W₀ ⊆ O`
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hxcl : x ∈ closure W₀ := frontier_subset_closure hx
    have hxnW₀ : x ∉ W₀ := by
      have h := hx; rw [hW₀open.frontier_eq] at h; exact h.2
    have hxKPQ : x ∈ W → x ∈ K_P ∪ K_Q := by
      intro hxW
      by_contra hcon
      rw [Set.mem_union, not_or] at hcon
      exact hxnW₀ (by rw [hW₀def]; exact ⟨⟨hxW, hcon.1⟩, hcon.2⟩)
    have hxfrP : x ∈ K_P → x ∈ frontier K_P := by
      intro hKP
      rw [hKPclosed.frontier_eq]
      refine ⟨hKP, ?_⟩
      intro hint
      obtain ⟨w, hwk, hww⟩ :=
        mem_closure_iff_nhds.mp hxcl (interior K_P) (isOpen_interior.mem_nhds hint)
      exact hww.1.2 (interior_subset hwk)
    have hxfrQ : x ∈ K_Q → x ∈ frontier K_Q := by
      intro hKQ
      rw [hKQclosed.frontier_eq]
      refine ⟨hKQ, ?_⟩
      intro hint
      obtain ⟨w, hwk, hww⟩ :=
        mem_closure_iff_nhds.mp hxcl (interior K_Q) (isOpen_interior.mem_nhds hint)
      exact hww.2 (interior_subset hwk)
    change f x ∈ (closure S_P ∪ closure S_Q)ᶜ
    rw [Set.mem_compl_iff, Set.mem_union, not_or]
    constructor
    · by_cases hxW : x ∈ W
      · rcases hxKPQ hxW with hKP | hKQ
        · exact hSPfront ⟨x, hxfrP hKP, rfl⟩
        · refine hnotSP x ?_
          have hb : ‖f x - f q₂‖ < R := hKQball x hKQ
          have hD : ‖f p₂ - f q₂‖ ≤ ‖f p₂ - f x‖ + ‖f x - f q₂‖ := htri _ _ _
          have h2R : 2 * R < ‖f p₂ - f x‖ := by linarith [hb, hD, hRD]
          rwa [norm_sub_rev] at h2R
      · refine hnotSP x ?_
        linarith [hεPge x hxW, hR2εP]
    · by_cases hxW : x ∈ W
      · rcases hxKPQ hxW with hKP | hKQ
        · refine hnotSQ x ?_
          have hb : ‖f x - f p₂‖ < R := hKPball x hKP
          have hD : ‖f p₂ - f q₂‖ ≤ ‖f p₂ - f x‖ + ‖f x - f q₂‖ := htri _ _ _
          rw [norm_sub_rev] at hb
          linarith [hb, hD, hRD]
        · exact hSQfront ⟨x, hxfrQ hKQ, rfl⟩
      · refine hnotSQ x ?_
        linarith [hεQge x hxW, hR2εQ]
  · -- `ψ` is the identity on `O`
    intro y hy
    have hy' : y ∉ closure S_P ∧ y ∉ closure S_Q := by
      rw [hOdef, Set.mem_compl_iff, Set.mem_union, not_or] at hy; exact hy
    have h1 : ψ_P y = y := by
      by_contra hcon; exact hy'.1 (subset_closure (hSPsupp y hcon))
    have h2 : ψ_Q y = y := by
      by_contra hcon; exact hy'.2 (subset_closure (hSQsupp y hcon))
    simp only [hψdef]
    rw [h2, h1]
  · exact hσψ
  · exact hψσ
  · -- `ψ` is smooth
    simp only [hψdef]
    exact (hψPsm.contMDiff).comp (hψQsm.contMDiff)
  · -- `σ` is smooth
    simp only [hσdef]
    exact (hσQsm.contMDiff).comp (hσPsm.contMDiff)
  · -- placement
    rintro y ⟨w, ⟨x, hx, rfl⟩, rfl⟩
    have hxW : x ∈ W := hx.1.1
    have hxKP : x ∉ K_P := hx.1.2
    have hxKQ : x ∉ K_Q := hx.2
    have key : ∀ z : M, ψ (f x) = f z → z ∈ W₀ := by
      intro z hz
      simp only [hψdef] at hz
      by_cases hQ : f x ∈ S_Q
      · -- the `Q`-push is active: `ψ_P` fixes `ψ_Q (f x)`, then use the `Q`-placement
        have hne : ψ_P (ψ_Q (f x)) = ψ_Q (f x) := by
          by_contra hc
          have hmem : ψ_Q (f x) ∈ S_P := hSPsupp _ hc
          have h1 : ‖ψ_Q (f x) - f x‖ ≤ 3 * R := hψQdisp (f x)
          have h2 : ‖f x - f q₂‖ < 2 * R := hSQball' _ hQ
          have h3 : ‖ψ_Q (f x) - f q₂‖ ≤ 5 * R := by
            linarith [htri (ψ_Q (f x)) (f x) (f q₂), h1, h2]
          have hb : ‖ψ_Q (f x) - f p₂‖ < 2 * R := hSPball' _ hmem
          have hD : ‖f p₂ - f q₂‖ ≤ ‖f p₂ - ψ_Q (f x)‖ + ‖ψ_Q (f x) - f q₂‖ := htri _ _ _
          rw [norm_sub_rev] at hb
          linarith [h3, hD, hb, hRD]
        have hzQ : ψ_Q (f x) = f z := hne.symm.trans hz
        have hq := hplaceQ x hxW hxKQ z hzQ
        refine ⟨⟨hq.1, ?_⟩, hq.2⟩
        intro hzKP
        have h1 : ‖ψ_Q (f x) - f x‖ ≤ 3 * R := hψQdisp (f x)
        have h2 : ‖f x - f q₂‖ < 2 * R := hSQball' _ hQ
        have h3 : ‖ψ_Q (f x) - f q₂‖ ≤ 5 * R := by
          linarith [htri (ψ_Q (f x)) (f x) (f q₂), h1, h2]
        have h4 : ‖f z - f q₂‖ = ‖ψ_Q (f x) - f q₂‖ := by rw [← hzQ]
        have hb : ‖f z - f p₂‖ < R := hKPball z hzKP
        have h5 : ‖f p₂ - f q₂‖ ≤ ‖f p₂ - f z‖ + ‖f z - f q₂‖ := htri _ _ _
        rw [h4] at h5
        rw [norm_sub_rev] at hb
        linarith [h3, h5, hb, hRD]
      · -- the `Q`-push fixes `f x`: use the `P`-placement
        have hQid : ψ_Q (f x) = f x := by
          by_contra hc; exact hQ (hSQsupp _ hc)
        have hzP : ψ_P (f x) = f z := by rw [hQid] at hz; exact hz
        have hp := hplaceP x hxW hxKP z hzP
        refine ⟨⟨hp.1, hp.2⟩, ?_⟩
        by_cases hP : f x ∈ S_P
        · intro hzKQ
          have h1 : ‖ψ_P (f x) - f x‖ ≤ 3 * R := hψPdisp (f x)
          have h2 : ‖f x - f p₂‖ < 2 * R := hSPball' _ hP
          have h3 : ‖ψ_P (f x) - f p₂‖ < 5 * R := by
            linarith [htri (ψ_P (f x)) (f x) (f p₂), h1, h2]
          have h4 : ‖f z - f p₂‖ = ‖ψ_P (f x) - f p₂‖ := by rw [← hzP]
          have hb : ‖f z - f q₂‖ < R := hKQball z hzKQ
          have h5 : ‖f p₂ - f q₂‖ ≤ ‖f p₂ - f z‖ + ‖f z - f q₂‖ := htri _ _ _
          rw [norm_sub_rev] at h4
          rw [h4] at h5
          linarith [h3, h5, hb, hRD]
        · have hPid : ψ_P (f x) = f x := by
            by_contra hc; exact hP (hSPsupp _ hc)
          have hfzx : f z = f x := by rw [← hzP, hPid]
          rcases hclean x z hxW hp.1 hfzx.symm with h0 | h0 | h0 | h0 | h0
          · exact h0 ▸ hxKQ
          · exact absurd (h0.1.symm ▸ hp₁KP) hxKP
          · exact absurd (h0.1.symm ▸ hfpSP) hP
          · exact absurd (h0.1.symm ▸ hq₁KQ) hxKQ
          · exact absurd (h0.1.symm ▸ hfqSQ) hQ
    by_cases hy : ψ (f x) ∈ f '' (Set.univ : Set M)
    · left
      obtain ⟨z, -, hz⟩ := hy
      exact ⟨z, key z hz.symm, hz⟩
    · right; exact hy
  · -- `f p₂ ∉ ψ '' (f '' W₀)`
    rintro ⟨y, ⟨x, hx, rfl⟩, hxy⟩
    have hfx : f x = σ (f p₂) := by
      have h1 : σ (ψ (f x)) = f x := hσψ (f x)
      have h2 := congrArg σ hxy
      rwa [h1] at h2
    have hσPmem : σ_P (f p₂) ∈ S_P := by
      refine hSPsupp (σ_P (f p₂)) ?_
      rw [hψPσP (f p₂)]
      intro hc
      exact hσPfp (hc ▸ ⟨p₂, Set.mem_univ p₂, rfl⟩)
    have hσPnotSQ : σ_P (f p₂) ∉ S_Q := by
      intro hmem
      have h1 : ‖σ_P (f p₂) - f p₂‖ < 2 * R := hSPball' _ hσPmem
      have h2 : ‖σ_P (f p₂) - f q₂‖ < 2 * R := hSQball' _ hmem
      have hD : ‖f p₂ - f q₂‖ ≤ ‖f p₂ - σ_P (f p₂)‖ + ‖σ_P (f p₂) - f q₂‖ := htri _ _ _
      rw [norm_sub_rev] at h1
      linarith [h1, h2, hD, hRD]
    have hσval : σ (f p₂) = σ_P (f p₂) := by
      have hfix : ψ_Q (σ_P (f p₂)) = σ_P (f p₂) := by
        by_contra hc; exact hσPnotSQ (hSQsupp (σ_P (f p₂)) hc)
      have hfix2 : σ_Q (σ_P (f p₂)) = σ_P (f p₂) := by
        conv_lhs => rw [← hfix]
        exact hσQψQ (σ_P (f p₂))
      simp only [hσdef]
      rw [hfix2]
    have hfin : f x = σ_P (f p₂) := by rw [hfx, hσval]
    exact hσPfp (hfin ▸ ⟨x, Set.mem_univ x, rfl⟩)
  · -- `f q₂ ∉ ψ '' (f '' W₀)`
    rintro ⟨y, ⟨x, hx, rfl⟩, hxy⟩
    have hfx : f x = σ (f q₂) := by
      have h1 : σ (ψ (f x)) = f x := hσψ (f x)
      have h2 := congrArg σ hxy
      rwa [h1] at h2
    have hfqnotSP : f q₂ ∉ S_P := by
      intro hmem
      have h1 : ‖f q₂ - f p₂‖ < 2 * R := hSPball' _ hmem
      rw [norm_sub_rev] at h1
      linarith [h1, hRD]
    have hσPval : σ_P (f q₂) = f q₂ := by
      have hfix : ψ_P (f q₂) = f q₂ := by
        by_contra hc; exact hfqnotSP (hSPsupp (f q₂) hc)
      conv_lhs => rw [← hfix]
      exact hσPψP (f q₂)
    have hσval : σ (f q₂) = σ_Q (f q₂) := by simp only [hσdef]; rw [hσPval]
    have hfin : f x = σ_Q (f q₂) := by rw [hfx, hσval]
    exact hσQfq (hfin ▸ ⟨x, Set.mem_univ x, rfl⟩)


end Work.Whitney
