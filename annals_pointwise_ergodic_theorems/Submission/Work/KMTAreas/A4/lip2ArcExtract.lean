/-
# The single-arc extraction `Work.KMTAreas.A4.lip2ArcExtract`

Krause--Mirek--Tao, §5.2 (the proof of Proposition `lip-2`): a function whose `ℤ`-Fourier
transform is supported in a finite union `⋃_{α ∈ A} (α + [-r,r])` of arcs can be replaced, up to a
constant depending only on the number of arcs, by a single function whose Fourier transform is
supported in *one* arc of radius `4r`, without losing more than a factor `#A + 1` in the bilinear
pairing with any bounded function.

The proof is the "smearing at the `N`-th roots of unity" argument of the paper ("by applying
suitable Fourier multiplier operators one can decompose `F = Σ_a F_a`, where each `F_a` obeys
essentially the same bounds as `F` and is supported in the `ε/q`-neighbourhood of `a/q`",
followed by the pigeonhole principle).  Concretely:

* choose `N` with `1/N ≤ 2r`, and consider the exact partition of unity of the frequency circle by
  the windows `arcWin ψ N (j/N)`, `j = 0, …, N-1`, whose symbols tile: `Σ_j Σ_n χ̃(N(t-j/N+n)) = 1`
  (`arcChiSumTiling`);
* keep the windows whose symbol meets the support of `F̂` (`J`), group them according to a witness
  arc `arcSet α r ∋` the symbol's support (`α : J → A`), and observe that each group is supported
  in `arcSet α (4r)`;
* the discarded windows have symbols vanishing on `supp F̂`, so the `ZFourier` transforms of the
  two sides agree, and injectivity of `ZFourier` on `ℓ¹` (`zFourierInj`) gives the exact
  decomposition `F = Σ_j F_j`;
* the pigeonhole principle selects the group with the largest pairing.

The number of grid cells in such a group is bounded by an absolute constant (`cardGridArcLe`).
-/
import Mathlib
import Submission.Work.KMTAreas.A4.zFourierInj
import Submission.Work.KMTAreas.A4.arcTilingBump
import Submission.Work.KMTAreas.A4.arcWinNormBound
import Submission.Work.KMTAreas.A4.arcWinZFourier
import Submission.Work.KMTAreas.A4.arcChiSumSupport
import Submission.Work.KMTAreas.A4.arcChiSumTiling
import Submission.Work.KMTAreas.A4.cardGridArcLe

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-! ## Elementary facts about the frequency circle -/

/-- Every point of the frequency circle has a real representative of absolute value at most `1/2`. -/
lemma exists_rep_abs_le (α : FreqCircle) : ∃ a : ℝ, (a : FreqCircle) = α ∧ |a| ≤ 1 / 2 := by
  refine ⟨(Quotient.out α : ℝ) - (((round (Quotient.out α) : ℤ)) : ℝ), ?_, ?_⟩
  · have h2 : ((((round (Quotient.out α) : ℤ)) : ℝ) : FreqCircle) = 0 := by
      have h1 : (((round (Quotient.out α) : ℤ) : ℝ)) = (round (Quotient.out α)) • (1 : ℝ) :=
        (zsmul_one _).symm
      rw [h1, AddCircle.coe_zsmul, AddCircle.coe_period]
      simp
    rw [AddCircle.coe_sub, h2, sub_zero]
    exact Quotient.out_eq α
  · simpa using abs_sub_round (Quotient.out α)

/-- If the arcs `arcSet α r` and `arcSet β s` meet, then `arcSet α r ⊆ arcSet β (s + 2r)`. -/
lemma arcSet_subset_arcSet {α β : FreqCircle} {r s ρ : ℝ}
    (h : ∃ x : FreqCircle, x ∈ arcSet α r ∧ x ∈ arcSet β s) (hρ : s + 2 * r ≤ ρ) :
    arcSet α r ⊆ arcSet β ρ := by
  obtain ⟨x, ⟨θ₁, hθ₁, hx₁⟩, θ₂, hθ₂, hx₂⟩ := h
  intro γ hγ
  obtain ⟨θ, hθ, rfl⟩ := hγ
  have hα : α = x - ((θ₁ : ℝ) : FreqCircle) := by rw [hx₁]; abel
  have hβ : β = x - ((θ₂ : ℝ) : FreqCircle) := by rw [hx₂]; abel
  refine ⟨θ₂ - θ₁ + θ, ?_, ?_⟩
  · have h1 : |θ₂ - θ₁ + θ| ≤ |θ₂| + |θ₁| + |θ| := by
      calc |θ₂ - θ₁ + θ| ≤ |θ₂ - θ₁| + |θ| := abs_add_le _ _
        _ ≤ (|θ₂| + |θ₁|) + |θ| := by
              have h := abs_sub_le θ₂ 0 θ₁
              rw [sub_zero, zero_sub, abs_neg] at h
              linarith
    linarith
  · have hcoe : (((θ₂ - θ₁ + θ : ℝ)) : FreqCircle)
        = ((θ₂ : ℝ) : FreqCircle) - ((θ₁ : ℝ) : FreqCircle) + ((θ : ℝ) : FreqCircle) := by
      rw [AddCircle.coe_add, AddCircle.coe_sub]
    rw [hα, hβ, hcoe]
    abel

/-- An arc of radius at least `1/2` is the whole frequency circle. -/
lemma arcSet_eq_univ {γ : FreqCircle} {ρ : ℝ} (h : 1 / 2 ≤ ρ) : arcSet γ ρ = Set.univ := by
  ext ξ
  refine ⟨fun _ => Set.mem_univ _, fun _ => ?_⟩
  obtain ⟨a, ha, hle⟩ := exists_rep_abs_le (ξ - γ)
  refine ⟨a, le_trans hle h, ?_⟩
  rw [ha]
  abel

/-! ## `ZFourier` of absolutely summable functions -/

@[simp] lemma ZFourier_zero (ξ : FreqCircle) : ZFourier (0 : ℤ → ℂ) ξ = 0 := by
  rw [ZFourier]
  simp

/-- Multiplication of an `ℓ¹` sequence by a character is summable. -/
lemma summable_mul_fourier {f : ℤ → ℂ} (hf : Summable fun x : ℤ => ‖f x‖) (ξ : FreqCircle) :
    Summable fun x : ℤ => f x * (fourier (-x) ξ : ℂ) :=
  Summable.of_norm_bounded hf fun x => by
    rw [norm_mul, fourier_norm_one, mul_one]

lemma ZFourier_add_of_summable {f g : ℤ → ℂ} (hf : Summable fun x : ℤ => ‖f x‖)
    (hg : Summable fun x : ℤ => ‖g x‖) (ξ : FreqCircle) :
    ZFourier (f + g) ξ = ZFourier f ξ + ZFourier g ξ := by
  rw [ZFourier, ZFourier, ZFourier]
  have h1 := summable_mul_fourier hf ξ
  have h2 := summable_mul_fourier hg ξ
  rw [show (fun x : ℤ => (f + g) x * (fourier (-x) ξ : ℂ))
      = fun x : ℤ => f x * (fourier (-x) ξ : ℂ) + g x * (fourier (-x) ξ : ℂ) from
        funext fun x => by rw [Pi.add_apply, add_mul]]
  exact h1.tsum_add h2

lemma ZFourier_neg_of_summable (f : ℤ → ℂ) (ξ : FreqCircle) :
    ZFourier (-f) ξ = -ZFourier f ξ := by
  rw [ZFourier, ZFourier]
  rw [show (fun x : ℤ => (-f) x * (fourier (-x) ξ : ℂ))
      = fun x : ℤ => -(f x * (fourier (-x) ξ : ℂ)) from
        funext fun x => by rw [Pi.neg_apply, neg_mul]]
  rw [tsum_neg]

lemma ZFourier_sub_of_summable {f g : ℤ → ℂ} (hf : Summable fun x : ℤ => ‖f x‖)
    (hg : Summable fun x : ℤ => ‖g x‖) (ξ : FreqCircle) :
    ZFourier (f - g) ξ = ZFourier f ξ - ZFourier g ξ := by
  have hgn : Summable fun x : ℤ => ‖(-g) x‖ := by simpa using hg
  rw [sub_eq_add_neg, ZFourier_add_of_summable hf hgn ξ, ZFourier_neg_of_summable g ξ,
    sub_eq_add_neg]

/-- A finite sum of `ℓ¹` sequences is `ℓ¹`. -/
lemma summable_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ → ℂ)
    (hf : ∀ i ∈ s, Summable fun x : ℤ => ‖f i x‖) :
    Summable fun x : ℤ => ‖(∑ i ∈ s, f i) x‖ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      have hsum : Summable fun x : ℤ => ‖f a x‖ + ‖(∑ i ∈ s, f i) x‖ :=
        (hf a (Finset.mem_insert_self a s)).add
          (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
      refine Summable.of_nonneg_of_le (fun x => norm_nonneg _) (fun x => ?_) hsum
      rw [Pi.add_apply]
      exact norm_add_le _ _

lemma ZFourier_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ → ℂ)
    (hf : ∀ i ∈ s, Summable fun x : ℤ => ‖f i x‖) (ξ : FreqCircle) :
    ZFourier (∑ i ∈ s, f i) ξ = ∑ i ∈ s, ZFourier (f i) ξ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha,
        ZFourier_add_of_summable (hf a (Finset.mem_insert_self a s))
          (summable_finset_sum s f fun i hi => hf i (Finset.mem_insert_of_mem hi)) ξ,
        ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)), Finset.sum_insert ha]

/-! ## The bilinear pairing of an absolutely summable function -/

lemma bilinPair_add_of_summable {f g : ℤ → ℂ} (hf : Summable fun x : ℤ => ‖f x‖)
    (hg : Summable fun x : ℤ => ‖g x‖) {X : ℤ → ℂ} (hX : ∀ x : ℤ, ‖X x‖ ≤ 1) :
    bilinPair X (f + g) = bilinPair X f + bilinPair X g := by
  rw [bilinPair, bilinPair, bilinPair]
  have h1 : Summable fun x : ℤ => X x * f x :=
    Summable.of_norm_bounded hf fun x => by
      rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (hX x)
  have h2 : Summable fun x : ℤ => X x * g x :=
    Summable.of_norm_bounded hg fun x => by
      rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (hX x)
  rw [show (fun x : ℤ => X x * (f + g) x)
      = fun x : ℤ => X x * f x + X x * g x from
        funext fun x => by rw [Pi.add_apply, mul_add]]
  exact h1.tsum_add h2

lemma bilinPair_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ → ℂ)
    (hf : ∀ i ∈ s, Summable fun x : ℤ => ‖f i x‖) {X : ℤ → ℂ} (hX : ∀ x : ℤ, ‖X x‖ ≤ 1) :
    bilinPair X (∑ i ∈ s, f i) = ∑ i ∈ s, bilinPair X (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [bilinPair]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha,
        bilinPair_add_of_summable (hf a (Finset.mem_insert_self a s))
          (summable_finset_sum s f fun i hi => hf i (Finset.mem_insert_of_mem hi)) hX,
        ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)), Finset.sum_insert ha]

/-! ## The smoothing operator -/

/-- Pointwise bound for the smoothing operator `smoothOp w G Q`. -/
lemma norm_smoothOp_le {w G : ℤ → ℂ} (hw : Summable fun m : ℤ => ‖w m‖) {B : ℝ}
    (hG : ∀ x : ℤ, ‖G x‖ ≤ B) (Q : ℤ) (x : ℤ) :
    ‖smoothOp w G Q x‖ ≤ (∑' m : ℤ, ‖w m‖) * B := by
  have hsum : Summable fun m : ℤ => ‖w m * G (x - Q * m)‖ := by
    refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) (hw.mul_right B)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hG _) (norm_nonneg _)
  have h1 : ‖smoothOp w G Q x‖ ≤ ∑' m : ℤ, ‖w m * G (x - Q * m)‖ := by
    rw [smoothOp]
    exact norm_tsum_le_tsum_norm hsum
  refine h1.trans ?_
  rw [← Summable.tsum_mul_right B hw]
  refine Summable.tsum_le_tsum (fun m => ?_) hsum (hw.mul_right B)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hG _) (norm_nonneg _)

/-- The `ℓ¹` norm of a finite sum of `ℓ¹` functions is at most the sum of the `ℓ¹` norms. -/
lemma tsum_norm_finset_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℤ → ℂ)
    (hf : ∀ i ∈ s, Summable fun x : ℤ => ‖f i x‖) :
    (∑' x : ℤ, ‖(∑ i ∈ s, f i) x‖) ≤ ∑ i ∈ s, (∑' x : ℤ, ‖f i x‖) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have h1 : Summable fun x : ℤ => ‖f a x‖ := hf a (Finset.mem_insert_self a s)
      have h2 : Summable fun x : ℤ => ‖(∑ i ∈ s, f i) x‖ :=
        summable_finset_sum s f fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have h3 : Summable fun x : ℤ => ‖(f a + ∑ i ∈ s, f i) x‖ := by
        rw [← Finset.sum_insert ha]
        exact summable_finset_sum (insert a s) f hf
      calc (∑' x : ℤ, ‖(f a + ∑ i ∈ s, f i) x‖)
          ≤ ∑' x : ℤ, (‖f a x‖ + ‖(∑ i ∈ s, f i) x‖) := by
            refine Summable.tsum_le_tsum (fun x => ?_) h3 (h1.add h2)
            rw [Pi.add_apply]
            exact norm_add_le _ _
        _ = (∑' x : ℤ, ‖f a x‖) + (∑' x : ℤ, ‖(∑ i ∈ s, f i) x‖) := h1.tsum_add h2
        _ ≤ (∑' x : ℤ, ‖f a x‖) + ∑ i ∈ s, (∑' x : ℤ, ‖f i x‖) := by
            have := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
            linarith

lemma summable_norm_zero : Summable fun x : ℤ => ‖(0 : ℤ → ℂ) x‖ := by simp

lemma tsum_norm_zero : (∑' x : ℤ, ‖(0 : ℤ → ℂ) x‖) = 0 := by simp


/-- **The single-arc extraction.** -/
theorem lip2ArcExtract :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : Finset Work.Analysis.InverseTheory.FreqCircle) (r : ℝ), 0 < r →
    ∀ (F X : ℤ → ℂ) (BF : ℝ),
      Summable (fun x : ℤ => ‖F x‖) → (∀ x : ℤ, ‖F x‖ ≤ BF) → 0 < BF →
      (∀ x : ℤ, ‖X x‖ ≤ 1) →
      Work.Analysis.InverseTheory.FourierSupportIn F
        (⋃ α ∈ (A : Set Work.Analysis.InverseTheory.FreqCircle),
          Work.KMTAreas.A4.arcSet α r) →
      ∃ (γ : Work.Analysis.InverseTheory.FreqCircle) (F' : ℤ → ℂ),
        Work.Analysis.InverseTheory.FourierSupportIn F' (Work.KMTAreas.A4.arcSet γ (4 * r)) ∧
        Summable (fun x : ℤ => ‖F' x‖) ∧
        (∀ x : ℤ, ‖F' x‖ ≤ C * ((A.card : ℝ) + 1) * BF) ∧
        (∑' x : ℤ, ‖F' x‖ ≤ C * ((A.card : ℝ) + 1) * (∑' x : ℤ, ‖F x‖)) ∧
        ‖Work.Analysis.InverseTheory.bilinPair X F‖
          ≤ C * ((A.card : ℝ) + 1) * ‖Work.Analysis.InverseTheory.bilinPair X F'‖ := by
  classical
  obtain ⟨ψ, hψFT, hψtile, hψsupp, hψ0⟩ := arcTilingBump
  obtain ⟨hwinSum, Kw, hKwpos, hKwbound⟩ := arcWinNormBound ψ
  refine ⟨max 1 (20 * Kw), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro A r hr F X BF hFsum hFbnd hBFpos hXbnd hsupp
  have hC1 : (1 : ℝ) ≤ max 1 (20 * Kw) * ((A.card : ℝ) + 1) := by
    have h2 : (1 : ℝ) ≤ max 1 (20 * Kw) := le_max_left _ _
    have h3 : (1 : ℝ) ≤ (A.card : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) A.card
      linarith
    nlinarith
  by_cases hbig : (1 : ℝ) / 2 ≤ 4 * r
  · refine ⟨0, F, ?_, hFsum, ?_, ?_, ?_⟩
    · rw [arcSet_eq_univ hbig]
      exact fun ξ hξ => (hξ (Set.mem_univ ξ)).elim
    · intro x
      calc ‖F x‖ ≤ BF := hFbnd x
        _ = 1 * BF := (one_mul BF).symm
        _ ≤ max 1 (20 * Kw) * ((A.card : ℝ) + 1) * BF :=
              mul_le_mul_of_nonneg_right hC1 hBFpos.le
    · have h2 : (0 : ℝ) ≤ ∑' x : ℤ, ‖F x‖ := tsum_nonneg fun x => norm_nonneg _
      calc (∑' x : ℤ, ‖F x‖) = 1 * (∑' x : ℤ, ‖F x‖) := (one_mul _).symm
        _ ≤ max 1 (20 * Kw) * ((A.card : ℝ) + 1) * (∑' x : ℤ, ‖F x‖) :=
              mul_le_mul_of_nonneg_right hC1 h2
    · calc ‖bilinPair X F‖ = 1 * ‖bilinPair X F‖ := (one_mul _).symm
        _ ≤ max 1 (20 * Kw) * ((A.card : ℝ) + 1) * ‖bilinPair X F‖ :=
              mul_le_mul_of_nonneg_right hC1 (norm_nonneg _)
  · have hr8 : r < 1 / 8 := by linarith [not_le.mp hbig]
    by_cases hpair : bilinPair X F = 0
    · refine ⟨0, 0, fun ξ _ => ZFourier_zero ξ, summable_norm_zero, ?_, ?_, ?_⟩
      · intro x
        rw [Pi.zero_apply, norm_zero]
        exact mul_nonneg (mul_nonneg (le_of_lt (lt_of_lt_of_le one_pos (le_max_left _ _)))
          (by positivity)) hBFpos.le
      · rw [tsum_norm_zero]
        exact mul_nonneg (mul_nonneg (le_of_lt (lt_of_lt_of_le one_pos (le_max_left _ _)))
          (by positivity)) (tsum_nonneg fun x => norm_nonneg _)
      · rw [hpair, norm_zero, show bilinPair X (0 : ℤ → ℂ) = 0 from by simp [bilinPair],
          norm_zero, mul_zero]
    · -- main case
      have hAne : A.Nonempty := by
        by_contra hA
        have hA0 : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
        have hz : ∀ ξ : FreqCircle, ZFourier F ξ = 0 := by
          intro ξ
          refine hsupp ξ ?_
          rw [hA0]
          simp
        have hF0 : F = 0 := funext fun x => zFourierInj F hFsum hz x
        have : bilinPair X F = 0 := by rw [hF0]; simp [bilinPair]
        exact hpair this
      obtain ⟨N, hN1, hNge, hNr⟩ :
          ∃ N : ℕ, 1 ≤ N ∧ (1 : ℝ) / (2 * r) ≤ (N : ℝ) ∧ (N : ℝ) * r ≤ 1 := by
        refine ⟨⌊(1 : ℝ) / r⌋₊, ?_, ?_, ?_⟩
        · rw [Nat.one_le_iff_ne_zero]
          intro h0
          have hle : ((1 : ℕ) : ℝ) ≤ (1 : ℝ) / r := by
            rw [Nat.cast_one]
            exact one_le_one_div hr (by linarith)
          have h1 := Nat.le_floor hle
          rw [h0] at h1
          exact absurd h1 (by norm_num)
        · have h1 : (1 : ℝ) / r < (⌊(1 : ℝ) / r⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
          have h2 : (1 : ℝ) / (2 * r) ≤ (1 : ℝ) / r - 1 := by
            have h3 : (1 : ℝ) / r - 1 = (1 - r) / r := div_sub_one hr.ne'
            rw [h3, div_le_iff₀ (by linarith : (0 : ℝ) < 2 * r)]
            have h5 : (1 - r) / r * (2 * r) = 2 * (1 - r) := by
              field_simp
            rw [h5]
            nlinarith [hr8]
          linarith
        · have h1 : (⌊(1 : ℝ) / r⌋₊ : ℝ) ≤ (1 : ℝ) / r := Nat.floor_le (by positivity)
          calc (⌊(1 : ℝ) / r⌋₊ : ℝ) * r ≤ ((1 : ℝ) / r) * r :=
                mul_le_mul_of_nonneg_right h1 hr.le
            _ = 1 := by rw [one_div, inv_mul_cancel₀ hr.ne']
      have hNposR : (0 : ℝ) < (N : ℝ) := by
        have : (0 : ℕ) < N := lt_of_lt_of_le Nat.zero_lt_one hN1
        exact_mod_cast this
      have h2rle : (1 : ℝ) / (N : ℝ) ≤ 2 * r := by
        rw [div_le_iff₀ hNposR]
        have h := hNge
        rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 * r)] at h
        nlinarith [h]
      set w : ℕ → ℤ → ℂ := fun j => arcWin ψ N ((j : ℝ) / (N : ℝ)) with hwdef
      set Fp : ℕ → ℤ → ℂ := fun j => smoothOp (w j) F 1 with hFpdef
      have hwsum : ∀ j : ℕ, Summable fun m : ℤ => ‖w j m‖ := fun j => hwinSum N _
      have hwbd : ∀ j : ℕ, (∑' m : ℤ, ‖w j m‖) ≤ Kw := fun j => hKwbound N hN1 _
      have hFpsum : ∀ j : ℕ, Summable fun x : ℤ => ‖Fp j x‖ :=
        fun j => (lipSmoothOpTsumLe (hwsum j) hFsum 1).1
      have hFpts : ∀ j : ℕ, (∑' x : ℤ, ‖Fp j x‖) ≤ Kw * (∑' x : ℤ, ‖F x‖) := by
        intro j
        refine (lipSmoothOpTsumLe (hwsum j) hFsum 1).2.trans ?_
        exact mul_le_mul_of_nonneg_right (hwbd j) (tsum_nonneg fun x => norm_nonneg _)
      have hFppt : ∀ j : ℕ, ∀ x : ℤ, ‖Fp j x‖ ≤ Kw * BF := by
        intro j x
        refine (norm_smoothOp_le (hwsum j) hFbnd 1 x).trans ?_
        exact mul_le_mul_of_nonneg_right (hwbd j) hBFpos.le
      have hsym : ∀ j : ℕ, ∀ t : ℝ,
          (∑' m : ℤ, w j m * (fourier (-m) ((t : ℝ) : FreqCircle) : ℂ))
            = ∑' n : ℤ, arcChi ((N : ℝ) * (t - (j : ℝ) / (N : ℝ) + (n : ℝ))) := by
        intro j t
        have h := arcWinZFourier ψ hψFT N hN1 ((j : ℝ) / (N : ℝ)) t
        simpa only [ZFourier, ← hwdef] using h
      have hFpfourier : ∀ j : ℕ, ∀ ξ : FreqCircle,
          ZFourier (Fp j) ξ = ZFourier F ξ * (∑' m : ℤ, w j m * (fourier (-m) ξ : ℂ)) := by
        intro j ξ
        have h := lipZFourierSmoothOp (hwsum j) hFsum 1 ξ
        simpa only [hFpdef, one_mul] using h
      set J : Finset ℕ := (Finset.range N).filter (fun j => ∃ t : ℝ,
        ZFourier F ((t : ℝ) : FreqCircle) ≠ 0 ∧
        (∑' n : ℤ, arcChi ((N : ℝ) * (t - (j : ℝ) / (N : ℝ) + (n : ℝ)))) ≠ 0) with hJdef
      have hwit : ∀ j ∈ J, ∃ (t : ℝ) (α : FreqCircle),
          α ∈ (A : Set FreqCircle) ∧ ((t : ℝ) : FreqCircle) ∈ arcSet α r ∧
          (∑' n : ℤ, arcChi ((N : ℝ) * (t - (j : ℝ) / (N : ℝ) + (n : ℝ)))) ≠ 0 := by
        intro j hj
        rw [hJdef, Finset.mem_filter] at hj
        obtain ⟨-, t, ht1, ht2⟩ := hj
        have hmem : ((t : ℝ) : FreqCircle) ∈ ⋃ α ∈ (A : Set FreqCircle), arcSet α r := by
          by_contra hc
          exact ht1 (hsupp _ hc)
        rw [Set.mem_iUnion] at hmem
        obtain ⟨α, hα⟩ := hmem
        rw [Set.mem_iUnion] at hα
        exact ⟨t, α, hα.1, hα.2, ht2⟩
      have hwit2 : ∀ j : ℕ, ∃ (t : ℝ) (α : FreqCircle), j ∈ J →
          α ∈ (A : Set FreqCircle) ∧ ((t : ℝ) : FreqCircle) ∈ arcSet α r ∧
          (∑' n : ℤ, arcChi ((N : ℝ) * (t - (j : ℝ) / (N : ℝ) + (n : ℝ)))) ≠ 0 := by
        intro j
        by_cases hj : j ∈ J
        · obtain ⟨t, α, h1, h2, h3⟩ := hwit j hj
          exact ⟨t, α, fun _ => ⟨h1, h2, h3⟩⟩
        · exact ⟨0, 0, fun h => absurd h hj⟩
      choose Tof Aof hspec using hwit2
      have hTof_mem : ∀ j (hj : j ∈ J), Aof j ∈ (A : Set FreqCircle) :=
        fun j hj => (hspec j hj).1
      have hTof_arc : ∀ j (hj : j ∈ J), ((Tof j : ℝ) : FreqCircle) ∈ arcSet (Aof j) r :=
        fun j hj => (hspec j hj).2.1
      have hTof_ne : ∀ j (hj : j ∈ J),
          (∑' n : ℤ, arcChi ((N : ℝ) * (Tof j - (j : ℝ) / (N : ℝ) + (n : ℝ)))) ≠ 0 :=
        fun j hj => (hspec j hj).2.2
      have hpiece_supp : ∀ j (hj : j ∈ J) (t : ℝ),
          (∑' n : ℤ, arcChi ((N : ℝ) * (t - (j : ℝ) / (N : ℝ) + (n : ℝ)))) ≠ 0 →
          ((t : ℝ) : FreqCircle) ∈ arcSet (Aof j) (4 * r) := by
        intro j hj t ht
        have h1 : ((t : ℝ) : FreqCircle)
            ∈ arcSet (((j : ℝ) / (N : ℝ) : ℝ) : FreqCircle) (3 / (4 * (N : ℝ))) :=
          arcChiSumSupport (N : ℝ) hNposR t ((j : ℝ) / (N : ℝ)) ht
        have h2 : ((Tof j : ℝ) : FreqCircle)
            ∈ arcSet (((j : ℝ) / (N : ℝ) : ℝ) : FreqCircle) (3 / (4 * (N : ℝ))) :=
          arcChiSumSupport (N : ℝ) hNposR (Tof j) ((j : ℝ) / (N : ℝ)) (hTof_ne j hj)
        have h5 : 1 ≤ 2 * r * (N : ℝ) := by
          have h6 := h2rle
          rw [div_le_iff₀ hNposR] at h6
          linarith [h6]
        have h4 : 2 * (3 / (4 * (N : ℝ))) ≤ 3 * r := by
          have h7 : 3 / (2 * (N : ℝ)) ≤ 3 * r := by
            rw [div_le_iff₀ (by positivity)]
            nlinarith [h5]
          have h8 : 2 * (3 / (4 * (N : ℝ))) = 3 / (2 * (N : ℝ)) := by ring
          linarith [h7, h8]
        refine (arcSet_subset_arcSet ⟨((Tof j : ℝ) : FreqCircle), h2, hTof_arc j hj⟩ ?_) h1
        linarith [h4]
      have hsum_one : ∀ t : ℝ, ZFourier F ((t : ℝ) : FreqCircle) ≠ 0 →
          ∑ j ∈ J, (∑' n : ℤ, arcChi ((N : ℝ) * (t - (j : ℝ) / (N : ℝ) + (n : ℝ)))) = 1 := by
        intro t ht
        have hsub : J ⊆ Finset.range N := by
          intro j hj
          rw [hJdef, Finset.mem_filter] at hj
          exact hj.1
        rw [Finset.sum_subset hsub (fun j hjrange hjnotJ => by
          by_contra hc
          exact hjnotJ (by rw [hJdef, Finset.mem_filter]; exact ⟨hjrange, t, ht, hc⟩))]
        exact arcChiSumTiling hψtile N hN1 t
      have hsumJ : Summable fun x : ℤ => ‖(∑ j ∈ J, Fp j) x‖ :=
        summable_finset_sum J Fp fun j hj => hFpsum j
      have hFJ : (∑ j ∈ J, Fp j) = F := by
        have hsub : Summable fun x : ℤ => ‖(∑ j ∈ J, Fp j) x - F x‖ := by
          have h := hsumJ.add hFsum
          refine Summable.of_nonneg_of_le (fun x => norm_nonneg _) (fun x => ?_) h
          exact norm_sub_le _ _
        have hzero : ∀ ξ : FreqCircle, ZFourier ((∑ j ∈ J, Fp j) - F) ξ = 0 := by
          intro ξ
          obtain ⟨t, ht⟩ : ∃ t : ℝ, ((t : ℝ) : FreqCircle) = ξ :=
            ⟨Quotient.out ξ, Quotient.out_eq ξ⟩
          rw [← ht, ZFourier_sub_of_summable hsumJ hFsum ((t : ℝ) : FreqCircle),
            ZFourier_finset_sum J Fp (fun j hj => hFpsum j) ((t : ℝ) : FreqCircle)]
          have h1 : ∀ j : ℕ, ZFourier (Fp j) ((t : ℝ) : FreqCircle) =
              ZFourier F ((t : ℝ) : FreqCircle) *
                (∑' n : ℤ, arcChi ((N : ℝ) * (t - (j : ℝ) / (N : ℝ) + (n : ℝ)))) := by
            intro j
            rw [hFpfourier j, hsym j t]
          by_cases ht0 : ZFourier F ((t : ℝ) : FreqCircle) = 0
          · rw [Finset.sum_congr rfl (fun j hj => h1 j)]
            simp [ht0]
          · rw [Finset.sum_congr rfl (fun j hj => h1 j), ← Finset.mul_sum, hsum_one t ht0,
              mul_one, sub_self]
        funext x
        have hx := zFourierInj ((∑ j ∈ J, Fp j) - F) hsub hzero x
        rw [Pi.sub_apply] at hx
        exact sub_eq_zero.mp hx
      set Gp : FreqCircle → ℤ → ℂ := fun α => ∑ j ∈ J, (if Aof j = α then Fp j else 0)
        with hGpdef
      have hterm_sum : ∀ (α : FreqCircle) (j : ℕ),
          Summable fun x : ℤ => ‖(if Aof j = α then Fp j else 0) x‖ := by
        intro α j
        by_cases h : Aof j = α
        · rw [if_pos h]; exact hFpsum j
        · rw [if_neg h]; exact summable_norm_zero
      have hGp_sum : ∀ α : FreqCircle, Summable fun x : ℤ => ‖Gp α x‖ := fun α =>
        summable_finset_sum J _ fun j hj => hterm_sum α j
      have hgroup : ∑ α ∈ A, Gp α = ∑ j ∈ J, Fp j := by
        simp only [hGpdef]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.sum_ite_eq]
        rw [if_pos (Finset.mem_coe.mp (hTof_mem j hj))]
      have hGp_decomp : ∑ α ∈ A, Gp α = F := hgroup.trans hFJ
      have hGp_supp : ∀ α ∈ (A : Set FreqCircle),
          FourierSupportIn (Gp α) (arcSet α (4 * r)) := by
        intro α hα
        intro ξ hξ
        obtain ⟨t, ht⟩ : ∃ t : ℝ, ((t : ℝ) : FreqCircle) = ξ :=
          ⟨Quotient.out ξ, Quotient.out_eq ξ⟩
        rw [← ht, hGpdef,
          ZFourier_finset_sum J _ (fun j hj => hterm_sum α j) ((t : ℝ) : FreqCircle)]
        refine Finset.sum_eq_zero fun j hj => ?_
        by_cases h : Aof j = α
        · rw [if_pos h, hFpfourier j, hsym j t]
          have hne : (∑' n : ℤ, arcChi ((N : ℝ) * (t - (j : ℝ) / (N : ℝ) + (n : ℝ)))) = 0 := by
            by_contra hc
            have hx := hpiece_supp j hj t hc
            rw [h] at hx
            exact hξ (by rw [← ht]; exact hx)
          rw [hne, mul_zero]
        · rw [if_neg h, ZFourier_zero]
      have hcount : ∀ α : FreqCircle, (J.filter (fun j => Aof j = α)).card ≤ 20 := by
        intro α
        obtain ⟨a, ha, hale⟩ := exists_rep_abs_le α
        have h4r : 4 * r < 1 / 2 := by linarith
        have hNr' : (N : ℝ) * (4 * r) ≤ 4 := by nlinarith [hNr]
        refine cardGridArcLe (N := N) (a := a) (ρ := 4 * r) hale h4r hNr'
          (s := J.filter (fun j => Aof j = α)) ?_ ?_
        · intro j hj
          rw [Finset.mem_filter] at hj
          rw [hJdef, Finset.mem_filter] at hj
          exact Finset.mem_range.mp hj.1.1
        · intro j hj
          rw [Finset.mem_filter] at hj
          obtain ⟨hjJ, hjα⟩ := hj
          have hNn : ∀ n : ℤ, n ≠ 0 → arcChi ((N : ℝ) * (n : ℝ)) = 0 := by
            intro n hn
            refine hψsupp ((N : ℝ) * (n : ℝ)) ?_
            have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
              rcases lt_or_gt_of_ne hn with h' | h'
              · have h'' : (n : ℝ) ≤ -1 := by
                  have : n ≤ (-1 : ℤ) := by omega
                  exact_mod_cast this
                rw [abs_of_nonpos (by linarith)]
                linarith
              · have h'' : (1 : ℝ) ≤ (n : ℝ) := by
                  have : (1 : ℤ) ≤ n := by omega
                  exact_mod_cast this
                rw [abs_of_nonneg (by linarith)]
                linarith
            have hNge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
            rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ))]
            nlinarith [hNge1, hn1]
          have hsym0 : (∑' n : ℤ,
              arcChi ((N : ℝ) * ((j : ℝ) / (N : ℝ) - (j : ℝ) / (N : ℝ) + (n : ℝ)))) ≠ 0 := by
            have hcongr : (fun n : ℤ =>
                arcChi ((N : ℝ) * ((j : ℝ) / (N : ℝ) - (j : ℝ) / (N : ℝ) + (n : ℝ))))
                = fun n : ℤ => arcChi ((N : ℝ) * (n : ℝ)) := by
              funext n
              congr 1
              ring
            rw [hcongr, tsum_eq_single 0 hNn]
            simp [hψ0]
          have hs : ((j : ℝ) / (N : ℝ) : FreqCircle) ∈ arcSet α (4 * r) := by
            have hx := hpiece_supp j hjJ ((j : ℝ) / (N : ℝ)) hsym0
            rw [hjα] at hx
            exact hx
          obtain ⟨θ, hθ, hθeq⟩ := hs
          have hzero : (((j : ℝ) / (N : ℝ) - a - θ : ℝ) : FreqCircle) = 0 := by
            simp only [AddCircle.coe_sub, AddCircle.coe_add, hθeq, ha]
            abel
          rw [AddCircle.coe_eq_zero_iff] at hzero
          obtain ⟨k, hk⟩ := hzero
          refine ⟨k, ?_⟩
          have hk' : (k : ℝ) = (j : ℝ) / (N : ℝ) - a - θ := by
            rw [← hk, zsmul_one]
          have hval : (j : ℝ) / (N : ℝ) - a - (k : ℝ) = θ := by
            rw [hk']; ring
          rw [hval]
          exact hθ
      obtain ⟨αs, hαsA, hαsmax⟩ :=
        Finset.exists_max_image A (fun α => ‖bilinPair X (Gp α)‖) hAne
      refine ⟨αs, Gp αs, hGp_supp αs hαsA, hGp_sum αs, ?_, ?_, ?_⟩
      · intro x
        have hcard : ((J.filter (fun j => Aof j = αs)).card : ℝ) ≤ 20 := by
          exact_mod_cast hcount αs
        have hGp_eq_x : Gp αs x = ∑ j ∈ J.filter (fun j => Aof j = αs), Fp j x := by
          rw [hGpdef]
          simp only [Finset.sum_apply, ite_apply, Pi.zero_apply]
          rw [← Finset.sum_filter]
        rw [hGp_eq_x]
        calc ‖∑ j ∈ J.filter (fun j => Aof j = αs), Fp j x‖
            ≤ ∑ j ∈ J.filter (fun j => Aof j = αs), ‖Fp j x‖ := norm_sum_le _ _
          _ ≤ ((J.filter (fun j => Aof j = αs)).card : ℝ) * (Kw * BF) := by
              rw [← nsmul_eq_mul]
              exact Finset.sum_le_card_nsmul _ _ _ (fun j hj => hFppt j x)
          _ ≤ 20 * (Kw * BF) :=
              mul_le_mul_of_nonneg_right hcard (mul_nonneg hKwpos.le hBFpos.le)
          _ = 20 * Kw * BF := by ring
          _ ≤ max 1 (20 * Kw) * ((A.card : ℝ) + 1) * BF := by
              have h3 : 20 * Kw ≤ max 1 (20 * Kw) * ((A.card : ℝ) + 1) := by
                have h2 : (1 : ℝ) ≤ (A.card : ℝ) + 1 := by
                  have := Nat.cast_nonneg (α := ℝ) A.card
                  linarith
                calc 20 * Kw ≤ max 1 (20 * Kw) := le_max_right _ _
                  _ = max 1 (20 * Kw) * 1 := (mul_one _).symm
                  _ ≤ max 1 (20 * Kw) * ((A.card : ℝ) + 1) :=
                        mul_le_mul_of_nonneg_left h2
                          (le_of_lt (lt_of_lt_of_le one_pos (le_max_left _ _)))
              calc 20 * Kw * BF ≤ (max 1 (20 * Kw) * ((A.card : ℝ) + 1)) * BF :=
                    mul_le_mul_of_nonneg_right h3 hBFpos.le
                _ = max 1 (20 * Kw) * ((A.card : ℝ) + 1) * BF := by ring
      · have hcard : ((J.filter (fun j => Aof j = αs)).card : ℝ) ≤ 20 := by
          exact_mod_cast hcount αs
        have hGp_eq : Gp αs = ∑ j ∈ J.filter (fun j => Aof j = αs), Fp j := by
          rw [hGpdef]
          rw [Finset.sum_filter]
        have h3 : (0 : ℝ) ≤ ∑' x : ℤ, ‖F x‖ := tsum_nonneg fun x => norm_nonneg _
        have h1 : (∑' x : ℤ, ‖Gp αs x‖)
            ≤ ((J.filter (fun j => Aof j = αs)).card : ℝ) * (Kw * (∑' x : ℤ, ‖F x‖)) := by
          rw [hGp_eq]
          calc (∑' x : ℤ, ‖(∑ j ∈ J.filter (fun j => Aof j = αs), Fp j) x‖)
              ≤ ∑ j ∈ J.filter (fun j => Aof j = αs), (∑' x : ℤ, ‖Fp j x‖) :=
                tsum_norm_finset_sum_le _ _ (fun j hj => hFpsum j)
            _ ≤ ∑ j ∈ J.filter (fun j => Aof j = αs), Kw * (∑' x : ℤ, ‖F x‖) :=
                Finset.sum_le_sum fun j hj => hFpts j
            _ = ((J.filter (fun j => Aof j = αs)).card : ℝ) * (Kw * (∑' x : ℤ, ‖F x‖)) := by
                rw [Finset.sum_const, nsmul_eq_mul]
        calc (∑' x : ℤ, ‖Gp αs x‖)
            ≤ ((J.filter (fun j => Aof j = αs)).card : ℝ) * (Kw * (∑' x : ℤ, ‖F x‖)) := h1
          _ ≤ 20 * (Kw * (∑' x : ℤ, ‖F x‖)) :=
              mul_le_mul_of_nonneg_right hcard (mul_nonneg hKwpos.le h3)
          _ = 20 * Kw * (∑' x : ℤ, ‖F x‖) := by ring
          _ ≤ max 1 (20 * Kw) * ((A.card : ℝ) + 1) * (∑' x : ℤ, ‖F x‖) := by
              have h5 : 20 * Kw ≤ max 1 (20 * Kw) * ((A.card : ℝ) + 1) := by
                have h2' : (1 : ℝ) ≤ (A.card : ℝ) + 1 := by
                  have := Nat.cast_nonneg (α := ℝ) A.card
                  linarith
                calc 20 * Kw ≤ max 1 (20 * Kw) := le_max_right _ _
                  _ = max 1 (20 * Kw) * 1 := (mul_one _).symm
                  _ ≤ max 1 (20 * Kw) * ((A.card : ℝ) + 1) :=
                        mul_le_mul_of_nonneg_left h2'
                          (le_of_lt (lt_of_lt_of_le one_pos (le_max_left _ _)))
              calc 20 * Kw * (∑' x : ℤ, ‖F x‖)
                  ≤ (max 1 (20 * Kw) * ((A.card : ℝ) + 1)) * (∑' x : ℤ, ‖F x‖) :=
                    mul_le_mul_of_nonneg_right h5 h3
                _ = max 1 (20 * Kw) * ((A.card : ℝ) + 1) * (∑' x : ℤ, ‖F x‖) := by ring
      · have h1 : bilinPair X F = ∑ α ∈ A, bilinPair X (Gp α) := by
          rw [← hGp_decomp]
          exact bilinPair_finset_sum A Gp (fun α hα => hGp_sum α) hXbnd
        calc ‖bilinPair X F‖ = ‖∑ α ∈ A, bilinPair X (Gp α)‖ := by rw [h1]
          _ ≤ ∑ α ∈ A, ‖bilinPair X (Gp α)‖ := norm_sum_le _ _
          _ ≤ A.card • ‖bilinPair X (Gp αs)‖ :=
              Finset.sum_le_card_nsmul _ _ _ (fun α hα => hαsmax α hα)
          _ = (A.card : ℝ) * ‖bilinPair X (Gp αs)‖ := by rw [nsmul_eq_mul]
          _ ≤ max 1 (20 * Kw) * ((A.card : ℝ) + 1) * ‖bilinPair X (Gp αs)‖ := by
              have h2 : (A.card : ℝ) ≤ max 1 (20 * Kw) * ((A.card : ℝ) + 1) := by
                have h3 : (1 : ℝ) ≤ max 1 (20 * Kw) := le_max_left _ _
                have h4 : (1 : ℝ) ≤ (A.card : ℝ) + 1 := by
                  have := Nat.cast_nonneg (α := ℝ) A.card
                  linarith
                nlinarith
              exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)

end Work.KMTAreas.A4
