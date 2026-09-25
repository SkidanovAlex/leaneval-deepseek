import Mathlib

open scoped ContDiff
open Finset

namespace Work.NN.Final

universe u v

/-! ### Norm preservation of differences of iterated derivatives -/

lemma norm_iteratedFDeriv_zero_sub {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (x y : E) :
    ‖iteratedFDeriv ℝ 0 f x - iteratedFDeriv ℝ 0 f y‖ = ‖f x - f y‖ := by
  simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, ← map_sub,
    LinearIsometryEquiv.norm_map]

lemma norm_iteratedFDeriv_fderiv_sub {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (x y : E) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fderiv ℝ f) x - iteratedFDeriv ℝ n (fderiv ℝ f) y‖
      = ‖iteratedFDeriv ℝ (n + 1) f x - iteratedFDeriv ℝ (n + 1) f y‖ := by
  rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right]
  simp only [Function.comp_apply]
  rw [← LinearIsometryEquiv.map_sub (continuousMultilinearCurryRightEquiv' ℝ n E F).symm,
    LinearIsometryEquiv.norm_map]

/-! ### The ULift transfer (left composition only) -/

lemma compContinuousMultilinearMap_sub {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] {n : ℕ}
    (g : F →L[ℝ] G) (a b : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F) :
    g.compContinuousMultilinearMap a - g.compContinuousMultilinearMap b
      = g.compContinuousMultilinearMap (a - b) := by
  ext m
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    sub_apply, map_sub]

lemma iteratedFDeriv_comp_lis {E A A' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup A'] [NormedSpace ℝ A']
    (e : A ≃ₗᵢ[ℝ] A') (F : E → A) (z : E) (k : ℕ) :
    iteratedFDeriv ℝ k (⇑e ∘ F) z
      = (e : A →L[ℝ] A').compContinuousMultilinearMap (iteratedFDeriv ℝ k F z) :=
  e.toContinuousLinearEquiv.iteratedFDeriv_comp_left (f := F) (x := z) (i := k)

lemma norm_iteratedFDeriv_comp_lis {E A A' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup A'] [NormedSpace ℝ A']
    (e : A ≃ₗᵢ[ℝ] A') (F : E → A) (x : E) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (⇑e ∘ F) x‖ = ‖iteratedFDeriv ℝ k F x‖ :=
  LinearIsometryEquiv.norm_iteratedFDeriv_comp_left e F x k

lemma norm_iteratedFDeriv_comp_lis_sub {E A A' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup A'] [NormedSpace ℝ A']
    (e : A ≃ₗᵢ[ℝ] A') (F : E → A) (x y : E) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (⇑e ∘ F) x - iteratedFDeriv ℝ k (⇑e ∘ F) y‖
      = ‖iteratedFDeriv ℝ k F x - iteratedFDeriv ℝ k F y‖ := by
  rw [iteratedFDeriv_comp_lis e F x k, iteratedFDeriv_comp_lis e F y k]
  rw [compContinuousMultilinearMap_sub]
  exact LinearIsometry.norm_compContinuousMultilinearMap e.toLinearIsometry _

/-! ### The pointwise two-point bilinear Leibniz bound -/

lemma opNorm_precompR_le {D : Type u} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {E F G : Type (max u v)} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →L[ℝ] F →L[ℝ] G) (C : ℝ) (hCnn : 0 ≤ C)
    (hC : ∀ a b, ‖B a b‖ ≤ C * ‖a‖ * ‖b‖) :
    ∀ a (b : D →L[ℝ] F), ‖(B.precompR D) a b‖ ≤ C * ‖a‖ * ‖b‖ := by
  intro a b
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun g => ?_)
  calc ‖(B.precompR D) a b g‖ = ‖B a (b g)‖ := by
        simp only [ContinuousLinearMap.precompR_apply, ContinuousLinearMap.compL_apply,
          ContinuousLinearMap.comp_apply]
    _ ≤ C * ‖a‖ * ‖b g‖ := hC a (b g)
    _ ≤ C * ‖a‖ * (‖b‖ * ‖g‖) := by
        gcongr
        exact ContinuousLinearMap.le_opNorm b g
    _ = (C * ‖a‖ * ‖b‖) * ‖g‖ := by ring

lemma opNorm_precompL_le {D : Type u} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {E F G : Type (max u v)} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →L[ℝ] F →L[ℝ] G) (C : ℝ) (hCnn : 0 ≤ C)
    (hC : ∀ a b, ‖B a b‖ ≤ C * ‖a‖ * ‖b‖) :
    ∀ (f : D →L[ℝ] E) (b : F), ‖(B.precompL D) f b‖ ≤ C * ‖f‖ * ‖b‖ := by
  intro f b
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun g => ?_)
  calc ‖(B.precompL D) f b g‖ = ‖B (f g) b‖ := by
        simp only [ContinuousLinearMap.precompL_apply]
    _ ≤ C * ‖f g‖ * ‖b‖ := hC (f g) b
    _ ≤ C * (‖f‖ * ‖g‖) * ‖b‖ := by
        gcongr
        exact ContinuousLinearMap.le_opNorm f g
    _ = (C * ‖f‖ * ‖b‖) * ‖g‖ := by ring

theorem bilin_pt :
    ∀ (n : ℕ) {D : Type u} [NormedAddCommGroup D] [NormedSpace ℝ D]
      {E F G : Type (max u v)} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
      (B : E →L[ℝ] F →L[ℝ] G) (C : ℝ) (_ : 0 ≤ C)
      (_ : ∀ a b, ‖B a b‖ ≤ C * ‖a‖ * ‖b‖) {f : D → E} {g : D → F},
      ContDiff ℝ n f → ContDiff ℝ n g → ∀ x y : D,
      ‖iteratedFDeriv ℝ n (fun z => B (f z) (g z)) x
          - iteratedFDeriv ℝ n (fun z => B (f z) (g z)) y‖ ≤
        C * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          (‖iteratedFDeriv ℝ i f x‖ *
              ‖iteratedFDeriv ℝ (n - i) g x - iteratedFDeriv ℝ (n - i) g y‖
            + ‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ *
              ‖iteratedFDeriv ℝ (n - i) g y‖) := by
  intro n
  induction n with
  | zero =>
    intro D _ _ E F G _ _ _ _ _ _ B C hCnn hC f g _ _ x y
    simp only [norm_iteratedFDeriv_zero_sub, norm_iteratedFDeriv_zero, Nat.zero_add,
      Finset.sum_range_one, Nat.choose_self, Nat.cast_one, Nat.sub_zero, one_mul]
    have hkey : B (f x) (g x) - B (f y) (g y)
        = B (f x) (g x - g y) + B (f x - f y) (g y) := by
      rw [map_sub, map_sub, sub_apply]
      abel
    rw [hkey]
    calc ‖B (f x) (g x - g y) + B (f x - f y) (g y)‖
        ≤ ‖B (f x) (g x - g y)‖ + ‖B (f x - f y) (g y)‖ := norm_add_le _ _
      _ ≤ C * ‖f x‖ * ‖g x - g y‖ + C * ‖f x - f y‖ * ‖g y‖ :=
            add_le_add (hC _ _) (hC _ _)
      _ = C * (‖f x‖ * ‖g x - g y‖ + ‖f x - f y‖ * ‖g y‖) := by ring
  | succ n ih =>
    intro D _ _ E F G _ _ _ _ _ _ B C hCnn hC f g hf hg x y
    have hfk : ContDiff ℝ n f := hf.of_le (Nat.cast_le.2 (Nat.le_succ n))
    have hgk : ContDiff ℝ n g := hg.of_le (Nat.cast_le.2 (Nat.le_succ n))
    have hdg : ContDiff ℝ n (fderiv ℝ g) := hg.fderiv_right (by simp only [Nat.cast_succ, le_refl])
    have hdf : ContDiff ℝ n (fderiv ℝ f) := hf.fderiv_right (by simp only [Nat.cast_succ, le_refl])
    set Φ1 : D → (D →L[ℝ] G) := fun z => B.precompR D (f z) (fderiv ℝ g z) with hΦ1
    set Φ2 : D → (D →L[ℝ] G) := fun z => B.precompL D (fderiv ℝ f z) (g z) with hΦ2
    have hΦ1c : ContDiff ℝ n Φ1 := by
      rw [hΦ1]
      exact ((B.precompR D).isBoundedBilinearMap.contDiff).comp₂ hfk hdg
    have hΦ2c : ContDiff ℝ n Φ2 := by
      rw [hΦ2]
      exact ((B.precompL D).isBoundedBilinearMap.contDiff).comp₂ hdf hgk
    have hb1 := ih (D := D) (E := E) (F := D →L[ℝ] F) (G := D →L[ℝ] G)
      (B := B.precompR D) (C := C) hCnn (opNorm_precompR_le B C hCnn hC) hfk hdg x y
    have hb2 := ih (D := D) (E := D →L[ℝ] E) (F := F) (G := D →L[ℝ] G)
      (B := B.precompL D) (C := C) hCnn (opNorm_precompL_le B C hCnn hC) hdf hgk x y
    set S1 : ℝ := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (‖iteratedFDeriv ℝ i f x‖ *
            ‖iteratedFDeriv ℝ (n + 1 - i) g x - iteratedFDeriv ℝ (n + 1 - i) g y‖
          + ‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ *
            ‖iteratedFDeriv ℝ (n + 1 - i) g y‖) with hS1
    set S2 : ℝ := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (‖iteratedFDeriv ℝ (i + 1) f x‖ *
            ‖iteratedFDeriv ℝ (n - i) g x - iteratedFDeriv ℝ (n - i) g y‖
          + ‖iteratedFDeriv ℝ (i + 1) f x - iteratedFDeriv ℝ (i + 1) f y‖ *
            ‖iteratedFDeriv ℝ (n - i) g y‖) with hS2
    have hsum1 : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          (‖iteratedFDeriv ℝ i f x‖ *
              ‖iteratedFDeriv ℝ (n - i) (fderiv ℝ g) x
                - iteratedFDeriv ℝ (n - i) (fderiv ℝ g) y‖
            + ‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ *
              ‖iteratedFDeriv ℝ (n - i) (fderiv ℝ g) y‖)) = S1 := by
      rw [hS1]
      apply Finset.sum_congr rfl
      intro i hi
      have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      rw [show n + 1 - i = n - i + 1 by omega]
      rw [norm_iteratedFDeriv_fderiv_sub, norm_iteratedFDeriv_fderiv]
    have hsum2 : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          (‖iteratedFDeriv ℝ i (fderiv ℝ f) x‖ *
              ‖iteratedFDeriv ℝ (n - i) g x - iteratedFDeriv ℝ (n - i) g y‖
            + ‖iteratedFDeriv ℝ i (fderiv ℝ f) x - iteratedFDeriv ℝ i (fderiv ℝ f) y‖ *
              ‖iteratedFDeriv ℝ (n - i) g y‖)) = S2 := by
      rw [hS2]
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_iteratedFDeriv_fderiv_sub, norm_iteratedFDeriv_fderiv]
    have hconv1 : ‖iteratedFDeriv ℝ n Φ1 x - iteratedFDeriv ℝ n Φ1 y‖ ≤ C * S1 := by
      rw [← hsum1]
      exact hb1
    have hconv2 : ‖iteratedFDeriv ℝ n Φ2 x - iteratedFDeriv ℝ n Φ2 y‖ ≤ C * S2 := by
      rw [← hsum2]
      exact hb2
    have hmain : ‖iteratedFDeriv ℝ (n + 1) (fun z => B (f z) (g z)) x
        - iteratedFDeriv ℝ (n + 1) (fun z => B (f z) (g z)) y‖
        ≤ ‖iteratedFDeriv ℝ n Φ1 x - iteratedFDeriv ℝ n Φ1 y‖
          + ‖iteratedFDeriv ℝ n Φ2 x - iteratedFDeriv ℝ n Φ2 y‖ := by
      rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right]
      simp only [Function.comp_apply]
      rw [← LinearIsometryEquiv.map_sub (continuousMultilinearCurryRightEquiv' ℝ n D G).symm,
        LinearIsometryEquiv.norm_map]
      have hfe : (fun z => fderiv ℝ (fun w => B (f w) (g w)) z) = Φ1 + Φ2 := by
        funext z
        rw [hΦ1, hΦ2]
        exact B.fderiv_of_bilinear (hf.differentiable (by simp)).differentiableAt
          (hg.differentiable (by simp)).differentiableAt
      rw [hfe, iteratedFDeriv_add hΦ1c hΦ2c]
      simp only [Pi.add_apply]
      rw [show (iteratedFDeriv ℝ n Φ1 x + iteratedFDeriv ℝ n Φ2 x)
            - (iteratedFDeriv ℝ n Φ1 y + iteratedFDeriv ℝ n Φ2 y)
          = (iteratedFDeriv ℝ n Φ1 x - iteratedFDeriv ℝ n Φ1 y)
            + (iteratedFDeriv ℝ n Φ2 x - iteratedFDeriv ℝ n Φ2 y) from by abel]
      exact norm_add_le (iteratedFDeriv ℝ n Φ1 x - iteratedFDeriv ℝ n Φ1 y)
        (iteratedFDeriv ℝ n Φ2 x - iteratedFDeriv ℝ n Φ2 y)
    have hpascal : S1 + S2 = ∑ i ∈ Finset.range (n + 1 + 1), ((n + 1).choose i : ℝ) *
        (‖iteratedFDeriv ℝ i f x‖ *
            ‖iteratedFDeriv ℝ (n + 1 - i) g x - iteratedFDeriv ℝ (n + 1 - i) g y‖
          + ‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ *
            ‖iteratedFDeriv ℝ (n + 1 - i) g y‖) := by
      rw [hS1, hS2]
      rw [show n + 1 + 1 = n + 2 by omega]
      exact (Finset.sum_choose_succ_mul
        (fun i j => ‖iteratedFDeriv ℝ i f x‖ *
            ‖iteratedFDeriv ℝ j g x - iteratedFDeriv ℝ j g y‖
          + ‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ *
            ‖iteratedFDeriv ℝ j g y‖) n).symm
    calc ‖iteratedFDeriv ℝ (n + 1) (fun z => B (f z) (g z)) x
            - iteratedFDeriv ℝ (n + 1) (fun z => B (f z) (g z)) y‖
        ≤ ‖iteratedFDeriv ℝ n Φ1 x - iteratedFDeriv ℝ n Φ1 y‖
          + ‖iteratedFDeriv ℝ n Φ2 x - iteratedFDeriv ℝ n Φ2 y‖ := hmain
      _ ≤ C * S1 + C * S2 := add_le_add hconv1 hconv2
      _ = C * (S1 + S2) := by ring
      _ = C * (∑ i ∈ Finset.range (n + 1 + 1), ((n + 1).choose i : ℝ) *
        (‖iteratedFDeriv ℝ i f x‖ *
            ‖iteratedFDeriv ℝ (n + 1 - i) g x - iteratedFDeriv ℝ (n + 1 - i) g y‖
          + ‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ *
            ‖iteratedFDeriv ℝ (n + 1 - i) g y‖)) := by rw [hpascal]

theorem bilin_pt_univ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : Type v} [NormedRing A] [NormedAlgebra ℝ A]
    {f g : E → A} {k : ℕ} (hf : ContDiff ℝ (k : ℕ∞) f) (hg : ContDiff ℝ (k : ℕ∞) g) (x y : E) :
    ‖iteratedFDeriv ℝ k (fun z => f z * g z) x - iteratedFDeriv ℝ k (fun z => f z * g z) y‖ ≤
      ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) *
        (‖iteratedFDeriv ℝ j f x‖ * ‖iteratedFDeriv ℝ (k - j) g x - iteratedFDeriv ℝ (k - j) g y‖
          + ‖iteratedFDeriv ℝ j f x - iteratedFDeriv ℝ j f y‖ * ‖iteratedFDeriv ℝ (k - j) g y‖) := by
  let A' := ULift.{max u v, v} A
  let e : A ≃ₗᵢ[ℝ] A' := (LinearIsometryEquiv.ulift ℝ A).symm
  have hf' : ContDiff ℝ (k : ℕ∞) (⇑e ∘ f) := (e.contDiff).comp hf
  have hg' : ContDiff ℝ (k : ℕ∞) (⇑e ∘ g) := (e.contDiff).comp hg
  have hC : ∀ a b : A', ‖(ContinuousLinearMap.mul ℝ A') a b‖ ≤ 1 * ‖a‖ * ‖b‖ := by
    intro a b
    rw [one_mul]
    exact norm_mul_le a b
  have key := bilin_pt k (D := E) (E := A') (F := A') (G := A')
      (B := ContinuousLinearMap.mul ℝ A') (C := 1) (by norm_num) hC hf' hg' x y
  rw [show (fun z : E => (ContinuousLinearMap.mul ℝ A') ((⇑e ∘ f) z) ((⇑e ∘ g) z))
      = (⇑e ∘ (fun z => f z * g z)) from
        funext fun z => rfl] at key
  rw [one_mul] at key
  simp only [norm_iteratedFDeriv_comp_lis, norm_iteratedFDeriv_comp_lis_sub] at key
  exact key

/-! ### The target -/

theorem leibniz_diff_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    {f g : E → A} {k : ℕ} (hf : ContDiff ℝ (k : ℕ∞) f) (hg : ContDiff ℝ (k : ℕ∞) g) (x y : E) :
    ‖iteratedFDeriv ℝ k (fun z => f z * g z) x - iteratedFDeriv ℝ k (fun z => f z * g z) y‖ ≤
      ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) *
        (‖iteratedFDeriv ℝ j f x‖ * ‖iteratedFDeriv ℝ (k - j) g x - iteratedFDeriv ℝ (k - j) g y‖
          + ‖iteratedFDeriv ℝ j f x - iteratedFDeriv ℝ j f y‖ * ‖iteratedFDeriv ℝ (k - j) g y‖) :=
  bilin_pt_univ hf hg x y

end Work.NN.Final
