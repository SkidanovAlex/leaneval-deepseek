import Mathlib
import Submission.Work.WilE3.Frame.Setup

namespace Work.WilE3.Frame

set_option autoImplicit false
open Classical Topology
open WilkiesDesign.E

/-! ## Prerequisites for `exists_cut_forms`

We build the `k - j - 1` cut forms explicitly out of the chosen non-zero coordinate `i0` of `w`:
the `i`-th form (`i ≠ i0`) is the coefficient vector of `v ↦ w i0 * v i - w i * v i0`, i.e.
`w i0 • Pi.single i 1 - w i • Pi.single i0 1`.  These annihilate `w`, and their common kernel is
contained in `ℝ ∙ w` (it is exactly `ℝ ∙ w`), so any two of its elements are proportional. -/

/-- The functional `v ↦ v i` read off as a dot product with `Pi.single i 1`. -/
private lemma sum_single_mul {k j : ℕ} (ι : Fin j → Fin k) (i : U k ι) (v : U k ι → ℝ) :
    ∑ t, (Pi.single i (1 : ℝ) : U k ι → ℝ) t * v t = v i := by
  have h := Fintype.sum_single_smul (f := v) (r := (1 : ℝ)) (i₀ := i)
  simpa only [smul_eq_mul, one_mul] using h

/-- The dot product of the coefficient vector `w i0 • Pi.single i 1 - w i • Pi.single i0 1` with
`v` is `w i0 * v i - w i * v i0`. -/
private lemma sum_cut_apply {k j : ℕ} (ι : Fin j → Fin k) (i0 : U k ι) (w : U k ι → ℝ)
    (i : U k ι) (v : U k ι → ℝ) :
    ∑ t, (w i0 * (Pi.single i (1 : ℝ) : U k ι → ℝ) t
        - w i * (Pi.single i0 (1 : ℝ) : U k ι → ℝ) t) * v t
      = w i0 * v i - w i * v i0 := by
  simp only [sub_mul, mul_assoc]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      sum_single_mul ι i v, sum_single_mul ι i0 v]

/-- The family of cut forms indexed by an enumeration `e` of the coordinates `≠ i0`. -/
private def cutForms {k j : ℕ} (ι : Fin j → Fin k) (w : U k ι → ℝ) (i0 : U k ι)
    {n : ℕ} (e : Fin n ≃ {i : U k ι // i ≠ i0}) (a : Fin n) : U k ι → ℝ :=
  w i0 • (Pi.single (e a).val (1 : ℝ) : U k ι → ℝ)
    - w (e a).val • (Pi.single i0 (1 : ℝ) : U k ι → ℝ)

/-- Evaluation of a cut form. -/
private lemma cutForms_apply {k j : ℕ} (ι : Fin j → Fin k) (w : U k ι → ℝ) (i0 : U k ι)
    {n : ℕ} (e : Fin n ≃ {i : U k ι // i ≠ i0}) (a : Fin n) (v : U k ι → ℝ) :
    ∑ t, cutForms ι w i0 e a t * v t = w i0 * v (e a).val - w (e a).val * v i0 := by
  simp only [cutForms, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  exact sum_cut_apply ι i0 w (e a).val v

/-- Anything killed by all the cut forms is a multiple of `w`. -/
private lemma cutForms_kernel {k j : ℕ} (ι : Fin j → Fin k) (w : U k ι → ℝ) (i0 : U k ι)
    (hw0 : w i0 ≠ 0) {n : ℕ} (e : Fin n ≃ {i : U k ι // i ≠ i0}) (u : U k ι → ℝ)
    (hu : ∀ a, ∑ t, cutForms ι w i0 e a t * u t = 0) :
    u = (u i0 / w i0) • w := by
  funext i
  by_cases hi : i = i0
  · rw [hi, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ (u i0) hw0]
  · have h2 := cutForms_apply ι w i0 e (e.symm ⟨i, hi⟩) u
    have h := hu (e.symm ⟨i, hi⟩)
    rw [h2] at h
    have hval : (e (e.symm ⟨i, hi⟩)).val = i := by simp
    rw [hval] at h
    have heq : w i0 * u i = w i * u i0 := by linarith
    rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div₀, eq_div_iff hw0,
      mul_comm (u i) (w i0), mul_comm (u i0) (w i)]
    exact heq

/-- **Cutting the tangent space down to a line.**  For an injective `ι` and every non-zero real
direction `w` in the `ι`-complement space there are `k - j - 1` real linear forms `μ` with `μ w = 0`
whose common kernel is *at most* one-dimensional, so that cutting `{h = 0}` by the corresponding
affine hyperplanes through `x` leaves a curve whose germ is the curve `u ↦ Ψ (u, 0)` followed in the
direction `w`.  (`Function.Injective ι` is needed: then `U k ι` has dimension exactly `k - j` and the
annihilator of `w` has dimension `k - j - 1`.) -/
theorem exists_cut_forms {k j : ℕ} (ι : Fin j → Fin k) (hι : Function.Injective ι)
    (w : Work.WilE3.Frame.U k ι → ℝ) (hw : w ≠ 0) :
    ∃ μ : Fin (k - j - 1) → (Work.WilE3.Frame.U k ι → ℝ),
      (∀ a, ∑ i, μ a i * w i = 0) ∧
      (∀ v v' : Work.WilE3.Frame.U k ι → ℝ,
        (∀ a, ∑ i, μ a i * v i = 0) → (∀ a, ∑ i, μ a i * v' i = 0) →
        ∃ c c' : ℝ, (c, c') ≠ 0 ∧ c • v = c' • v') := by
  classical
  -- a coordinate where `w` does not vanish
  obtain ⟨i0, hw0⟩ : ∃ i : U k ι, w i ≠ 0 := by
    by_contra hc
    refine hw (funext fun i => ?_)
    by_contra h
    exact hc ⟨i, h⟩
  -- the `ι`-complement space has exactly `k - j` coordinates
  have hcard : Fintype.card (U k ι) = k - j := by
    have h1 : Fintype.card {i : Fin k // i ∈ Set.range ι} = j := by
      have h2 : Fintype.card {i : Fin k // i ∈ Set.range ι} = Fintype.card (Fin j) :=
        Fintype.card_congr (Equiv.ofInjective ι hι).symm
      simpa using h2
    show Fintype.card {i : Fin k // ¬ i ∈ Set.range ι} = k - j
    rw [Fintype.card_subtype_compl (fun i : Fin k => i ∈ Set.range ι), Fintype.card_fin, h1]
  -- hence the coordinates `≠ i0` number `k - j - 1`
  have hcard' : Fintype.card {i : U k ι // i ≠ i0} = k - j - 1 := by
    rw [Fintype.card_subtype_compl (fun i : U k ι => i = i0), Fintype.card_subtype_eq i0, hcard]
  let e : Fin (k - j - 1) ≃ {i : U k ι // i ≠ i0} :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin, hcard'])
  refine ⟨cutForms ι w i0 e, ?_, ?_⟩
  · intro a
    rw [cutForms_apply]
    ring
  · intro v v' hv hv'
    have keyv : v = (v i0 / w i0) • w := cutForms_kernel ι w i0 hw0 e v hv
    have keyv' : v' = (v' i0 / w i0) • w := cutForms_kernel ι w i0 hw0 e v' hv'
    by_cases ht : v i0 / w i0 = 0
    · by_cases ht' : v' i0 / w i0 = 0
      · exact ⟨1, 0, by simp, by rw [one_smul, zero_smul, keyv, ht, zero_smul]⟩
      · refine ⟨v' i0 / w i0, v i0 / w i0, ?_, ?_⟩
        · intro hc
          exact ht' (by simpa using congrArg Prod.fst hc)
        · conv_lhs => rw [keyv]
          conv_rhs => rw [keyv']
          funext i
          simp only [Pi.smul_apply, smul_eq_mul]
          ring
    · refine ⟨v' i0 / w i0, v i0 / w i0, ?_, ?_⟩
      · intro hc
        exact ht (by simpa using congrArg Prod.snd hc)
      · conv_lhs => rw [keyv]
        conv_rhs => rw [keyv']
        funext i
        simp only [Pi.smul_apply, smul_eq_mul]
        ring

end Work.WilE3.Frame
