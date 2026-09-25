import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.StrataCompDefs
import Submission.Work.BourgainPlan.IonescuWainger.riesz_thorin_vector_valued
import Submission.Work.BourgainPlan.IonescuWainger.extend_zero_lm

open scoped BigOperators ENNReal

namespace Work.BourgainPlan.IonescuWainger

noncomputable section

/-- The linear map underlying the family reduction: views `g : ↥f.support → ℂ` as the finitely
supported sequence `extendZeroLM f.support g`, applies `T k i`, and places the result in the
component `(n, k)` of the target — the disjoint-union index `Σ k, ι k` selects which family
member `T k i` is used. -/
noncomputable def famVecLM {κ : Type*} [Fintype κ] {ι : κ → Type*} [∀ k, Fintype (ι k)]
    (T : ∀ k, ι k → (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ)) (f : ℤ →₀ ℂ) (F : Finset ℤ) :
    (↥f.support → ℂ) →ₗ[ℂ] ((↥F × κ) → (Σ k, ι k) → ℂ) where
  toFun g b j := by
    classical
    exact if j.1 = b.2 then T j.1 j.2 (extendZeroLM f.support g) b.1 else 0
  map_add' g h := by
    classical
    funext b j
    by_cases hj : j.1 = b.2 <;> simp [hj, map_add, Pi.add_apply]
  map_smul' c g := by
    classical
    funext b j
    by_cases hj : j.1 = b.2 <;> simp [hj, map_smul, Pi.smul_apply]

/-- The fibre identity: the `ℓ²`-norm of the `(n,k)`-component of the target only sees the
`k`-th family member `T k ·`. -/
lemma sum_normSq_famVecLM {κ : Type*} [Fintype κ] {ι : κ → Type*} [∀ k, Fintype (ι k)]
    (T : ∀ k, ι k → (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ)) (f : ℤ →₀ ℂ) (F : Finset ℤ)
    (g : ↥f.support → ℂ) (b : ↥F × κ) :
    (∑ j : Σ k, ι k, ‖famVecLM T f F g b j‖ ^ 2)
      = ∑ i : ι b.2, ‖T b.2 i (extendZeroLM f.support g) (b.1 : ℤ)‖ ^ 2 := by
  classical
  rw [Fintype.sum_sigma]
  trans ∑ x : κ, (if x = b.2 then
      ∑ y : ι x, ‖T x y (extendZeroLM f.support g) (b.1 : ℤ)‖ ^ 2 else 0)
  · refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases hx : x = b.2
    · rw [if_pos hx]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      simp [famVecLM, hx]
    · rw [if_neg hx]
      refine Finset.sum_eq_zero (fun y _ => ?_)
      simp [famVecLM, hx]
  · rw [Finset.sum_ite_eq']
    simp

/-- The same fibre identity in `ℝ≥0∞` form. -/
lemma sum_ofReal_normSq_famVecLM {κ : Type*} [Fintype κ] {ι : κ → Type*}
    [∀ k, Fintype (ι k)]
    (T : ∀ k, ι k → (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ)) (f : ℤ →₀ ℂ) (F : Finset ℤ)
    (g : ↥f.support → ℂ) (b : ↥F × κ) :
    (∑ j : Σ k, ι k, ENNReal.ofReal (‖famVecLM T f F g b j‖ ^ 2))
      = ∑ i : ι b.2, ENNReal.ofReal (‖T b.2 i (extendZeroLM f.support g) (b.1 : ℤ)‖ ^ 2) := by
  rw [← ENNReal.ofReal_sum_of_nonneg
    (fun j (_ : j ∈ (Finset.univ : Finset (Σ k, ι k))) => sq_nonneg (‖famVecLM T f F g b j‖))]
  rw [sum_normSq_famVecLM]
  exact ENNReal.ofReal_sum_of_nonneg (fun i (_ : i ∈ (Finset.univ : Finset (ι b.2))) =>
    sq_nonneg (‖T b.2 i (extendZeroLM f.support g) (b.1 : ℤ)‖))

/-- **The finite-`F` reduction, parametrised by a family.** Under the two `ℝ≥0∞`-valued endpoint
hypotheses of `ellp_vector_interpolation_family`, for every finite `F ⊆ ℤ` the part of the mixed
norm of `(n,k) ↦ (i ↦ T k i f n)` sitting over `F` satisfies the interpolated bound.  The
reduction is to `riesz_thorin_vector_valued` with source `↥f.support`, target `↥F × κ` and inner
index the disjoint union `Σ k, ι k`. -/
theorem ellp_family_finite_F_bound {κ : Type*} [Fintype κ] {ι : κ → Type*}
    [∀ k, Fintype (ι k)] {p : ℝ} (hp : 2 ≤ p)
    (T : ∀ k, ι k → (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ)) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h2 : ∀ f : ℤ →₀ ℂ,
      (∑' n : ℤ, ∑ k, ∑ i, ENNReal.ofReal (‖T k i f n‖ ^ 2))
        ≤ ENNReal.ofReal (A ^ 2) * ∑' n : ℤ, ENNReal.ofReal (‖f n‖ ^ 2))
    (hinf : ∀ f : ℤ →₀ ℂ,
      (⨆ (k : κ), ⨆ n : ℤ, (∑ i, ENNReal.ofReal (‖T k i f n‖ ^ 2)) ^ ((1 : ℝ) / 2))
        ≤ ENNReal.ofReal B * (⨆ n : ℤ, ENNReal.ofReal ‖f n‖))
    (f : ℤ →₀ ℂ) (F : Finset ℤ) :
    (∑ n ∈ F, ∑ k, (∑ i, ‖T k i f n‖ ^ 2) ^ (p / 2)) ^ (1 / p)
      ≤ A ^ (2 / p) * B ^ (1 - 2 / p) * (∑' n : ℤ, ‖f n‖ ^ p) ^ (1 / p) := by
  classical
  have hp0 : 0 < p := by linarith
  -- The `ℓ²` endpoint, in `ℝ` form.
  have hT0 : ∀ g : ↥f.support → ℂ,
      (∑ b : ↥F × κ, ∑ j : Σ k, ι k, ‖famVecLM T f F g b j‖ ^ 2) ^ ((1:ℝ)/2)
        ≤ A * (∑ a : ↥f.support, ‖g a‖ ^ 2) ^ ((1:ℝ)/2) := by
    intro g
    have hRHS : (∑' n : ℤ, ENNReal.ofReal (‖extendZeroLM f.support g n‖ ^ 2))
        = ENNReal.ofReal (∑ a : ↥f.support, ‖g a‖ ^ 2) := by
      rw [tsum_eq_sum (s := f.support)
        (f := fun n : ℤ => ENNReal.ofReal (‖extendZeroLM f.support g n‖ ^ 2))]
      · rw [Finset.sum_subtype f.support (fun x => Iff.rfl)
          (fun n : ℤ => ENNReal.ofReal (‖extendZeroLM f.support g n‖ ^ 2))]
        rw [show (∑ a : ↥f.support, ENNReal.ofReal (‖extendZeroLM f.support g ↑a‖ ^ 2))
            = ∑ a : ↥f.support, ENNReal.ofReal (‖g a‖ ^ 2) from
              Finset.sum_congr rfl fun a _ => by
                rw [extendZeroLM_apply, dif_pos a.2]]
        rw [ENNReal.ofReal_sum_of_nonneg (fun a (_ : a ∈ (Finset.univ : Finset ↥f.support)) =>
          sq_nonneg (‖g a‖))]
      · intro n hn
        rw [extendZeroLM_apply, dif_neg hn, norm_zero]
        simp
    have h2g'' : (∑' n : ℤ, ∑ k, ∑ i, ENNReal.ofReal (‖T k i (extendZeroLM f.support g) n‖ ^ 2))
        ≤ ENNReal.ofReal (A ^ 2 * ∑ a : ↥f.support, ‖g a‖ ^ 2) := by
      have h := h2 (extendZeroLM f.support g)
      rw [hRHS] at h
      rwa [← ENNReal.ofReal_mul (sq_nonneg A)] at h
    have hle : ∑ n ∈ F, ∑ k, ∑ i,
        ENNReal.ofReal (‖T k i (extendZeroLM f.support g) n‖ ^ 2)
        ≤ ENNReal.ofReal (A ^ 2 * ∑ a : ↥f.support, ‖g a‖ ^ 2) := by
      refine le_trans ?_ h2g''
      rw [ENNReal.tsum_eq_iSup_sum]
      exact le_iSup (fun s : Finset ℤ =>
        ∑ n ∈ s, ∑ k, ∑ i, ENNReal.ofReal (‖T k i (extendZeroLM f.support g) n‖ ^ 2)) F
    have hE1 : ∀ n : ℤ, (∑ k : κ, ∑ i : ι k,
          ENNReal.ofReal (‖T k i (extendZeroLM f.support g) n‖ ^ 2))
        = ENNReal.ofReal (∑ k : κ, ∑ i : ι k,
            ‖T k i (extendZeroLM f.support g) n‖ ^ 2) := by
      intro n
      trans ∑ k : κ, ENNReal.ofReal (∑ i : ι k,
          ‖T k i (extendZeroLM f.support g) n‖ ^ 2)
      · refine Finset.sum_congr rfl (fun k _ => ?_)
        exact (ENNReal.ofReal_sum_of_nonneg
          (fun i (_ : i ∈ (Finset.univ : Finset (ι k))) =>
            sq_nonneg (‖T k i (extendZeroLM f.support g) n‖))).symm
      · exact (ENNReal.ofReal_sum_of_nonneg
          (fun k (_ : k ∈ (Finset.univ : Finset κ)) =>
            Finset.sum_nonneg fun i _ => sq_nonneg _)).symm
    have hE : (∑ n ∈ F, ∑ k, ∑ i,
          ENNReal.ofReal (‖T k i (extendZeroLM f.support g) n‖ ^ 2))
        = ENNReal.ofReal (∑ n ∈ F, ∑ k, ∑ i,
            ‖T k i (extendZeroLM f.support g) n‖ ^ 2) := by
      trans ∑ n ∈ F, ENNReal.ofReal (∑ k : κ, ∑ i : ι k,
          ‖T k i (extendZeroLM f.support g) n‖ ^ 2)
      · refine Finset.sum_congr rfl (fun n _ => ?_)
        exact hE1 n
      · exact (ENNReal.ofReal_sum_of_nonneg (fun n (_ : n ∈ F) =>
          Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun i _ => sq_nonneg _)).symm
    have hfin : (∑ n ∈ F, ∑ k, ∑ i, ‖T k i (extendZeroLM f.support g) n‖ ^ 2)
        ≤ A ^ 2 * ∑ a : ↥f.support, ‖g a‖ ^ 2 :=
      (ENNReal.ofReal_le_ofReal_iff
        (mul_nonneg (sq_nonneg A) (Finset.sum_nonneg fun a _ => sq_nonneg _))).mp
        (by rw [← hE]; exact hle)
    have hLHS : (∑ b : ↥F × κ, ∑ j : Σ k, ι k, ‖famVecLM T f F g b j‖ ^ 2)
        = ∑ n ∈ F, ∑ k, ∑ i, ‖T k i (extendZeroLM f.support g) n‖ ^ 2 := by
      rw [Fintype.sum_prod_type]
      have hinner : ∀ n : ↥F, (∑ k : κ, ∑ j : Σ k, ι k,
            ‖famVecLM T f F g (n, k) j‖ ^ 2)
          = ∑ k : κ, ∑ i : ι k, ‖T k i (extendZeroLM f.support g) (n : ℤ)‖ ^ 2 := by
        intro n
        refine Finset.sum_congr rfl (fun k _ => ?_)
        exact sum_normSq_famVecLM T f F g (n, k)
      rw [Finset.sum_congr rfl (fun n _ => hinner n)]
      rw [← Finset.sum_subtype F (fun x => Iff.rfl)
        (fun n : ℤ => ∑ k : κ, ∑ i : ι k, ‖T k i (extendZeroLM f.support g) n‖ ^ 2)]
    have hAsq : (A ^ 2) ^ ((1:ℝ)/2) = A := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs, abs_of_nonneg hA]
    calc (∑ b : ↥F × κ, ∑ j : Σ k, ι k, ‖famVecLM T f F g b j‖ ^ 2) ^ ((1:ℝ)/2)
        ≤ (A ^ 2 * ∑ a : ↥f.support, ‖g a‖ ^ 2) ^ ((1:ℝ)/2) :=
          Real.rpow_le_rpow
            (Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
            (by rw [hLHS]; exact hfin) (by norm_num)
      _ = A * (∑ a : ↥f.support, ‖g a‖ ^ 2) ^ ((1:ℝ)/2) := by
          rw [Real.mul_rpow (sq_nonneg A) (Finset.sum_nonneg fun a _ => sq_nonneg _), hAsq]
  -- The `ℓ^∞` endpoint, in `ℝ` form.
  have hT1 : ∀ g : ↥f.support → ℂ,
      (⨆ b : ↥F × κ, (∑ j : Σ k, ι k, ‖famVecLM T f F g b j‖ ^ 2) ^ ((1:ℝ)/2))
        ≤ B * (⨆ a : ↥f.support, ‖g a‖) := by
    intro g
    set S' : ENNReal := ⨆ a : ↥f.support, ENNReal.ofReal ‖g a‖ with hS'def
    have hS'ne : S' ≠ ⊤ := by
      rw [hS'def]
      have hb : (⨆ a : ↥f.support, ENNReal.ofReal ‖g a‖)
          ≤ ENNReal.ofReal (∑ a : ↥f.support, ‖g a‖) :=
        iSup_le fun a => ENNReal.ofReal_le_ofReal
          (Finset.single_le_sum (fun b _ => norm_nonneg _) (Finset.mem_univ a))
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb
    have hS'toReal : (⨆ a : ↥f.support, ‖g a‖) = S'.toReal := by
      rw [hS'def, ENNReal.toReal_iSup (fun a => ENNReal.ofReal_ne_top)]
      exact (iSup_congr fun a => ENNReal.toReal_ofReal (norm_nonneg _)).symm
    have hsup : (⨆ n : ℤ, ENNReal.ofReal ‖extendZeroLM f.support g n‖) ≤ S' := by
      rw [hS'def]
      refine iSup_le fun n => ?_
      by_cases hn : n ∈ f.support
      · have hn' : extendZeroLM f.support g n = g ⟨n, hn⟩ := by
          rw [extendZeroLM_apply, dif_pos hn]
        rw [hn']
        exact le_iSup (fun a : ↥f.support => ENNReal.ofReal ‖g a‖) ⟨n, hn⟩
      · have hn' : extendZeroLM f.support g n = 0 := by
          rw [extendZeroLM_apply, dif_neg hn]
        rw [hn', norm_zero, ENNReal.ofReal_zero]
        exact bot_le
    have hperb : ∀ b : ↥F × κ,
        ENNReal.ofReal ((∑ j : Σ k, ι k, ‖famVecLM T f F g b j‖ ^ 2) ^ ((1:ℝ)/2))
          ≤ ENNReal.ofReal B * S' := by
      intro b
      have hfib : (∑ j : Σ k, ι k, ENNReal.ofReal (‖famVecLM T f F g b j‖ ^ 2))
          = ∑ i : ι b.2,
              ENNReal.ofReal (‖T b.2 i (extendZeroLM f.support g) (b.1 : ℤ)‖ ^ 2) :=
        sum_ofReal_normSq_famVecLM T f F g b
      have hb : (∑ j : Σ k, ι k, ENNReal.ofReal (‖famVecLM T f F g b j‖ ^ 2)) ^ ((1:ℝ)/2)
          ≤ ENNReal.ofReal B * S' := by
        calc (∑ j : Σ k, ι k, ENNReal.ofReal (‖famVecLM T f F g b j‖ ^ 2)) ^ ((1:ℝ)/2)
            = (∑ i : ι b.2,
                ENNReal.ofReal (‖T b.2 i (extendZeroLM f.support g) (b.1 : ℤ)‖ ^ 2)) ^ ((1:ℝ)/2) := by
              rw [hfib]
          _ ≤ ⨆ (k : κ), ⨆ n : ℤ,
                (∑ i : ι k,
                  ENNReal.ofReal (‖T k i (extendZeroLM f.support g) n‖ ^ 2)) ^ ((1:ℝ)/2) := by
              refine le_trans ?_ (le_iSup (fun k : κ => ⨆ n : ℤ,
                (∑ i : ι k,
                  ENNReal.ofReal (‖T k i (extendZeroLM f.support g) n‖ ^ 2)) ^ ((1:ℝ)/2)) b.2)
              exact le_iSup (fun n : ℤ => (∑ i : ι b.2,
                ENNReal.ofReal (‖T b.2 i (extendZeroLM f.support g) n‖ ^ 2)) ^ ((1:ℝ)/2))
                (b.1 : ℤ)
          _ ≤ ENNReal.ofReal B * ⨆ n : ℤ, ENNReal.ofReal ‖extendZeroLM f.support g n‖ :=
              hinf (extendZeroLM f.support g)
          _ ≤ ENNReal.ofReal B * S' := mul_le_mul' le_rfl hsup
      calc ENNReal.ofReal ((∑ j : Σ k, ι k, ‖famVecLM T f F g b j‖ ^ 2) ^ ((1:ℝ)/2))
          = (ENNReal.ofReal (∑ j : Σ k, ι k, ‖famVecLM T f F g b j‖ ^ 2)) ^ ((1:ℝ)/2) :=
            (ENNReal.ofReal_rpow_of_nonneg
              (Finset.sum_nonneg fun j _ => sq_nonneg _) (by norm_num)).symm
        _ = (∑ j : Σ k, ι k, ENNReal.ofReal (‖famVecLM T f F g b j‖ ^ 2)) ^ ((1:ℝ)/2) := by
            rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => sq_nonneg _)]
        _ ≤ ENNReal.ofReal B * S' := hb
    calc (⨆ b : ↥F × κ, (∑ j : Σ k, ι k, ‖famVecLM T f F g b j‖ ^ 2) ^ ((1:ℝ)/2))
        = (⨆ b : ↥F × κ,
            ENNReal.ofReal ((∑ j : Σ k, ι k, ‖famVecLM T f F g b j‖ ^ 2) ^ ((1:ℝ)/2))).toReal := by
          rw [ENNReal.toReal_iSup (fun b => ENNReal.ofReal_ne_top)]
          exact (iSup_congr fun b => ENNReal.toReal_ofReal
            (Real.rpow_nonneg (Finset.sum_nonneg fun j _ => sq_nonneg _) _)).symm
      _ ≤ (ENNReal.ofReal B * S').toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS'ne) (iSup_le hperb)
      _ = B * (⨆ a : ↥f.support, ‖g a‖) := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hB, ← hS'toReal]
  -- Apply the finite-type vector-valued Riesz--Thorin theorem.
  have hmain := riesz_thorin_vector_valued hp (famVecLM T f F) A B hA hB hT0 hT1
    (fun a : ↥f.support => f a)
  have hLHS : (∑ b : ↥F × κ,
      (∑ j : Σ k, ι k, ‖famVecLM T f F (fun a : ↥f.support => f a) b j‖ ^ 2) ^ (p / 2))
      = ∑ n ∈ F, ∑ k, (∑ i, ‖T k i f n‖ ^ 2) ^ (p / 2) := by
    rw [Fintype.sum_prod_type]
    have hinner : ∀ n : ↥F, (∑ k : κ,
          (∑ j : Σ k, ι k, ‖famVecLM T f F (fun a : ↥f.support => f a) (n, k) j‖ ^ 2) ^ (p / 2))
        = ∑ k : κ, (∑ i : ι k, ‖T k i f (n : ℤ)‖ ^ 2) ^ (p / 2) := by
      intro n
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [sum_normSq_famVecLM T f F (fun a : ↥f.support => f a) (n, k), extendZeroLM_self]
    rw [Finset.sum_congr rfl (fun n _ => hinner n)]
    rw [← Finset.sum_subtype F (fun x => Iff.rfl)
      (fun n : ℤ => ∑ k : κ, (∑ i : ι k, ‖T k i f n‖ ^ 2) ^ (p / 2))]
  have hRHS : (∑ a : ↥f.support, ‖(fun a : ↥f.support => f a) a‖ ^ p)
      = (∑' n : ℤ, ‖f n‖ ^ p) := by
    rw [← tsum_norm_extendZeroLM f.support (fun a : ↥f.support => f a) hp0, extendZeroLM_self]
  rw [hLHS, hRHS] at hmain
  exact hmain

/-- Interpolation `(ℓ²(ℓ²), ℓ^∞(ℓ²)) ⟹ ℓ^p(ℓ²)` on `ℤ` with a *family* of target index sets: for a finite type `κ` (the `A₀` of Tao's `ortho-apply`(ii)), dependent inner index sets `ι k`, and linear maps `T k i : (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ)`, the two endpoint bounds -- the *total* `ℓ²` bound over all of `κ × ι`, and the per-`k` sup bound in `ℓ^∞` -- give the mixed-norm bound `(Σ'_n Σ_k (Σ_{i : ι k} ‖T k i f n‖²)^{p/2})^{1/p} ≤ A^{2/p} B^{1-2/p} (Σ'_n ‖f n‖^p)^{1/p}` for `2 ≤ p`.  (A single `k` is `Work.BourgainPlan.IonescuWainger.ellp_vector_interpolation`; the point here is that the outer sum over `A₀` must sit *inside* the `ℓ^p` norm, and that the per-`k` sup bound is all that is assumed -- the whole-family `ℓ^∞` bound would be false, e.g. for `f ≡ 1`.)  Route: reduce to `Work.BourgainPlan.IonescuWainger.riesz_thorin_vector_valued` with source `↥f.support`, target `↥F × κ` for finite `F ⊆ ℤ`, inner index the disjoint union `Σ k, ι k`, and the map `g ↦ ((n,k) ↦ (j ↦ if j.1 = k then T j.1 j.2 (extendZeroLM f.support g) n else 0))`; the fibre identity `Σ_{j : j.1 = k} = Σ_{i : ι k}` (`Finset.sum_sigma'`, `Finset.sum_filter`) transfers the hypotheses and the conclusion; finally take the supremum over the finite `F ⊆ ℤ`, as in `Work.BourgainPlan.IonescuWainger.ellp_finite_F_bound` and `ellp_vector_interpolation`. -/
theorem ellp_vector_interpolation_family {κ : Type*} [Fintype κ] {ι : κ → Type*}
    [∀ k, Fintype (ι k)] {p : ℝ} (hp : 2 ≤ p)
    (T : ∀ k, ι k → (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ)) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h2 : ∀ f : ℤ →₀ ℂ,
      (∑' n : ℤ, ∑ k, ∑ i, ENNReal.ofReal (‖T k i f n‖ ^ 2))
        ≤ ENNReal.ofReal (A ^ 2) * ∑' n : ℤ, ENNReal.ofReal (‖f n‖ ^ 2))
    (hinf : ∀ f : ℤ →₀ ℂ,
      (⨆ (k : κ), ⨆ n : ℤ, (∑ i, ENNReal.ofReal (‖T k i f n‖ ^ 2)) ^ ((1 : ℝ) / 2))
        ≤ ENNReal.ofReal B * (⨆ n : ℤ, ENNReal.ofReal ‖f n‖))
    (f : ℤ →₀ ℂ) :
    (∑' n : ℤ, ∑ k, (∑ i, ENNReal.ofReal (‖T k i f n‖ ^ 2)) ^ (p / 2)) ^ (1 / p)
      ≤ ENNReal.ofReal (A ^ (2 / p) * B ^ (1 - 2 / p))
        * (∑' n : ℤ, ENNReal.ofReal (‖f n‖ ^ p)) ^ (1 / p) := by
  classical
  have hp0 : 0 < p := by linarith
  have h1p : 0 < 1 / p := by positivity
  have hpq : (0 : ℝ) ≤ p / 2 := by linarith
  have hc : 0 ≤ A ^ (2 / p) * B ^ (1 - 2 / p) :=
    mul_nonneg (Real.rpow_nonneg hA _) (Real.rpow_nonneg hB _)
  have key : ∀ F : Finset ℤ,
      (∑ n ∈ F, ∑ k, (∑ i, ‖T k i f n‖ ^ 2) ^ (p / 2)) ^ (1 / p)
        ≤ A ^ (2 / p) * B ^ (1 - 2 / p) * (∑' n : ℤ, ‖f n‖ ^ p) ^ (1 / p) :=
    fun F => ellp_family_finite_F_bound hp T A B hA hB h2 hinf f F
  have hfs1 : (∑' n : ℤ, ‖f n‖ ^ p) = ∑ n ∈ f.support, ‖f n‖ ^ p :=
    tsum_eq_sum (fun n hn => by
      rw [Finsupp.notMem_support_iff.mp hn, norm_zero, Real.zero_rpow (ne_of_gt hp0)])
  have hfs2 : (∑' n : ℤ, ENNReal.ofReal (‖f n‖ ^ p))
      = ∑ n ∈ f.support, ENNReal.ofReal (‖f n‖ ^ p) :=
    tsum_eq_sum (fun n hn => by
      rw [Finsupp.notMem_support_iff.mp hn, norm_zero, Real.zero_rpow (ne_of_gt hp0),
        ENNReal.ofReal_zero])
  have hSnn : (0 : ℝ) ≤ ∑' n : ℤ, ‖f n‖ ^ p :=
    tsum_nonneg fun n => Real.rpow_nonneg (norm_nonneg _) p
  have hfsum : (∑' n : ℤ, ENNReal.ofReal (‖f n‖ ^ p))
      = ENNReal.ofReal (∑' n : ℤ, ‖f n‖ ^ p) := by
    rw [hfs1, hfs2,
      ENNReal.ofReal_sum_of_nonneg (fun n _ => Real.rpow_nonneg (norm_nonneg _) p)]
  set R : ENNReal := ENNReal.ofReal (A ^ (2 / p) * B ^ (1 - 2 / p))
        * (∑' n : ℤ, ENNReal.ofReal (‖f n‖ ^ p)) ^ (1 / p) with hRdef
  have hYnn : ∀ n : ℤ, (0 : ℝ) ≤ ∑ k, (∑ i, ‖T k i f n‖ ^ 2) ^ (p / 2) := fun n =>
    Finset.sum_nonneg fun k _ => Real.rpow_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) _
  -- every finite sub-sum is bounded by `R ^ p`
  have hstep : ∀ F : Finset ℤ,
      (∑ n ∈ F, ∑ k, (∑ i, ENNReal.ofReal (‖T k i f n‖ ^ 2)) ^ (p / 2)) ≤ R ^ p := by
    intro F
    have hpow : (∑ n ∈ F, ∑ k, (∑ i, ENNReal.ofReal (‖T k i f n‖ ^ 2)) ^ (p / 2))
        = ((∑ n ∈ F, ∑ k, (∑ i, ENNReal.ofReal (‖T k i f n‖ ^ 2)) ^ (p / 2)) ^ (1 / p)) ^ p := by
      rw [← ENNReal.rpow_mul, one_div_mul_cancel (ne_of_gt hp0), ENNReal.rpow_one]
    rw [hpow]
    apply ENNReal.rpow_le_rpow _ hp0.le
    have hterm : ∀ n ∈ F, (∑ k, (∑ i, ENNReal.ofReal (‖T k i f n‖ ^ 2)) ^ (p / 2))
        = ENNReal.ofReal (∑ k, (∑ i, ‖T k i f n‖ ^ 2) ^ (p / 2)) := by
      intro n _
      trans ∑ k : κ, ENNReal.ofReal ((∑ i : ι k, ‖T k i f n‖ ^ 2) ^ (p / 2))
      · refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [← ENNReal.ofReal_sum_of_nonneg (fun i (_ : i ∈ (Finset.univ : Finset (ι k))) =>
          sq_nonneg (‖T k i f n‖))]
        exact ENNReal.ofReal_rpow_of_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) hpq
      · exact (ENNReal.ofReal_sum_of_nonneg (fun k (_ : k ∈ (Finset.univ : Finset κ)) =>
          Real.rpow_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) _)).symm
    have hX : (∑ n ∈ F, ∑ k, (∑ i, ENNReal.ofReal (‖T k i f n‖ ^ 2)) ^ (p / 2))
        = ENNReal.ofReal (∑ n ∈ F, ∑ k, (∑ i, ‖T k i f n‖ ^ 2) ^ (p / 2)) := by
      rw [Finset.sum_congr rfl hterm]
      rw [ENNReal.ofReal_sum_of_nonneg (fun n _ => hYnn n)]
    have hA' : (∑ n ∈ F, ∑ k, (∑ i, ENNReal.ofReal (‖T k i f n‖ ^ 2)) ^ (p / 2)) ^ (1 / p)
        = ENNReal.ofReal ((∑ n ∈ F, ∑ k, (∑ i, ‖T k i f n‖ ^ 2) ^ (p / 2)) ^ (1 / p)) := by
      rw [hX]
      exact ENNReal.ofReal_rpow_of_nonneg (Finset.sum_nonneg fun n _ => hYnn n) h1p.le
    have hB' : R = ENNReal.ofReal
        (A ^ (2 / p) * B ^ (1 - 2 / p) * (∑' n : ℤ, ‖f n‖ ^ p) ^ (1 / p)) := by
      rw [hRdef, hfsum, ENNReal.ofReal_rpow_of_nonneg hSnn h1p.le,
        ← ENNReal.ofReal_mul hc]
    rw [hA', hB']
    exact ENNReal.ofReal_le_ofReal (key F)
  -- the full `ℤ`-sum is the supremum of the finite sub-sums
  calc (∑' n : ℤ, ∑ k, (∑ i, ENNReal.ofReal (‖T k i f n‖ ^ 2)) ^ (p / 2)) ^ (1 / p)
      = (⨆ F : Finset ℤ,
          ∑ n ∈ F, ∑ k, (∑ i, ENNReal.ofReal (‖T k i f n‖ ^ 2)) ^ (p / 2)) ^ (1 / p) := by
        rw [ENNReal.tsum_eq_iSup_sum]
    _ ≤ (R ^ p) ^ (1 / p) := ENNReal.rpow_le_rpow (iSup_le hstep) h1p.le
    _ = R := by rw [← ENNReal.rpow_mul, mul_one_div, div_self (ne_of_gt hp0),
        ENNReal.rpow_one]

end

end Work.BourgainPlan.IonescuWainger
