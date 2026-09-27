import Mathlib
import Submission.Work.Drive.iteratedDeriv_comp_sq
import Submission.Work.Drive.contDiff_iteratedDeriv_fst
import Submission.Work.Drive.flat_bounds_of_jets
import Submission.Work.Drive.contDiff_trunc_sqrt

/-!
# The even Taylor polynomial and the parametric `√`-descent

For a `C^∞` map `F : X × ℝ → E` which is even in its second variable we build, for every `m`, a
globally `C^m` function on `X × ℝ` which agrees with `(x, s) ↦ F (x, √s)` on the closed half-space
`X × [0, ∞)`.

The construction is the even Taylor truncation in the variable `t`:
`P_m (x, s) = Σ_{j ≤ m} ((2j)!)⁻¹ s^j ∂_t^{2j} F (x, 0)`, whose `t`-version `P_m (x, t^2)` matches
the `t`-jets of `F (x, ·)` up to order `2m + 1`; the remainder therefore has vanishing `t`-jets up
to order `2m + 2` and, by `Work.Drive.contDiff_trunc_sqrt` (quantitative flat descent), its
`√`-substitution — extended by `0` below the axis — is `C^m`.
-/

open Set Filter Topology
open scoped ContDiff

namespace Work.Drive

universe u v

variable {X : Type u} {E : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Auxiliary one-dimensional facts -/

/-- An even function has vanishing odd iterated derivatives at the origin. -/
theorem esq_iteratedDeriv_odd_eq_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : ℝ → F} (hg : ∀ t : ℝ, g (-t) = g t) {k : ℕ} (hk : Odd k) :
    iteratedDeriv k g 0 = 0 := by
  have h := iteratedDeriv_comp_neg (𝕜 := ℝ) k g 0
  rw [show (fun x : ℝ => g (-x)) = g from funext hg, neg_zero, hk.neg_one_pow] at h
  rw [neg_one_smul] at h
  have h2 : iteratedDeriv k g 0 + iteratedDeriv k g 0 = 0 := (eq_neg_iff_add_eq_zero).mp h
  have h3 : (2 : ℝ) • iteratedDeriv k g 0 = 0 := by rw [two_smul]; exact h2
  rcases smul_eq_zero.mp h3 with h4 | h4
  · norm_num at h4
  · exact h4

/-- Iterated derivatives distribute over finite sums. -/
theorem esq_iteratedDeriv_sum {ι : Type*} (s : Finset ι) (g : ι → ℝ → E) (x : ℝ) (n : ℕ)
    (hg : ∀ i ∈ s, ContDiffAt ℝ (n : WithTop ℕ∞) (g i) x) :
    iteratedDeriv n (fun y => ∑ i ∈ s, g i y) x = ∑ i ∈ s, iteratedDeriv n (g i) x := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a t hat ih =>
    have hsplit : (fun y => ∑ i ∈ insert a t, g i y) = g a + fun y => ∑ i ∈ t, g i y := by
      funext y
      rw [Finset.sum_insert hat]
      rfl
    rw [hsplit, iteratedDeriv_add,
      ih (fun i hi => hg i (Finset.mem_insert_of_mem hi)), Finset.sum_insert hat]
    · exact hg a (Finset.mem_insert_self a t)
    · exact ContDiffAt.sum (fun i hi => hg i (Finset.mem_insert_of_mem hi))

/-- The iterated derivatives at `0` of `s ↦ s ^ i • d`. -/
theorem esq_iteratedDeriv_pow_smul (i : ℕ) (d : E) (j : ℕ) :
    iteratedDeriv j (fun s : ℝ => s ^ i • d) 0 =
      (if j = i then (Nat.factorial i : ℝ) else 0) • d := by
  have hcd : ContDiffAt ℝ (j : WithTop ℕ∞) (fun s : ℝ => s ^ i) 0 :=
    (contDiff_id.pow i).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  rw [iteratedDeriv_smul_const (f := fun s : ℝ => s ^ i) (v := d) hcd,
    iteratedDeriv_fun_pow_zero]
  push_cast
  rfl

/-! ### The even Taylor polynomial -/

/-- The `m`-th even Taylor polynomial of `F` in its second variable, written in the variable
`s = t ^ 2`: `Σ_{j ≤ m} ((2j)!)⁻¹ s^j ∂_t^{2j} F (x, 0)`. -/
noncomputable def esqPoly (F : X × ℝ → E) (m : ℕ) : X × ℝ → E :=
  fun p => ∑ j ∈ Finset.range (m + 1),
    ((((Nat.factorial (2 * j) : ℕ) : ℝ))⁻¹) •
      (p.2 ^ j • iteratedDeriv (2 * j) (fun t : ℝ => F (p.1, t)) 0)

/-- The same polynomial composed with `t ↦ t ^ 2`. -/
noncomputable def esqPolyT (F : X × ℝ → E) (m : ℕ) : X × ℝ → E :=
  fun p => esqPoly F m (p.1, p.2 ^ 2)

/-- The remainder of the even Taylor truncation. -/
noncomputable def esqR (F : X × ℝ → E) (m : ℕ) : X × ℝ → E :=
  fun p => F p - esqPolyT F m p

theorem esqPoly_contDiff {F : X × ℝ → E} (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (m : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (esqPoly F m) := by
  refine ContDiff.sum fun j _ => ?_
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : X × ℝ => iteratedDeriv (2 * j) (fun t : ℝ => F (p.1, t)) 0) :=
    (contDiff_iteratedDeriv_fst hF (2 * j)).comp contDiff_fst
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : X × ℝ => p.2 ^ j) :=
    contDiff_snd.pow j
  exact (h2.smul h1).const_smul _

theorem esqPolyT_contDiff {F : X × ℝ → E} (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (m : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (esqPolyT F m) := by
  have hpair : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : X × ℝ => (p.1, p.2 ^ 2)) :=
    contDiff_fst.prodMk (contDiff_snd.pow 2)
  exact (esqPoly_contDiff hF m).comp hpair

/-- Coefficient bookkeeping: `((2j)! / j!) * (j! * ((2j)!)⁻¹) = 1`. -/
theorem esq_coeff (j : ℕ) :
    ((Nat.factorial (2 * j) : ℝ) / (Nat.factorial j : ℝ)) *
      ((Nat.factorial j : ℝ) * (((Nat.factorial (2 * j) : ℕ) : ℝ))⁻¹) = 1 := by
  have h1 : (((Nat.factorial (2 * j) : ℕ)) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * j)
  have h2 : ((Nat.factorial j : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero j
  field_simp

/-- The `j`-th derivative in `s` at `0` of the truncated polynomial. -/
theorem esqPoly_iteratedDeriv_zero (F : X × ℝ → E) (m j : ℕ) (hj : j ≤ m) (x : X) :
    iteratedDeriv j (fun s : ℝ => esqPoly F m (x, s)) 0 =
      (Nat.factorial j : ℝ) •
        ((((Nat.factorial (2 * j) : ℕ) : ℝ))⁻¹ •
          iteratedDeriv (2 * j) (fun t : ℝ => F (x, t)) 0) := by
  classical
  have hsum : (fun s : ℝ => esqPoly F m (x, s)) =
      fun s : ℝ => ∑ i ∈ Finset.range (m + 1),
        ((((Nat.factorial (2 * i) : ℕ) : ℝ))⁻¹) •
          (s ^ i • iteratedDeriv (2 * i) (fun t : ℝ => F (x, t)) 0) := rfl
  have hgn : ∀ i ∈ Finset.range (m + 1),
      ContDiffAt ℝ (j : WithTop ℕ∞)
        (fun s : ℝ => ((((Nat.factorial (2 * i) : ℕ) : ℝ))⁻¹) •
          (s ^ i • iteratedDeriv (2 * i) (fun t : ℝ => F (x, t)) 0)) 0 := by
    intro i _
    refine (ContDiffAt.const_smul _ ?_)
    exact ((contDiff_id.pow i).contDiffAt).smul contDiffAt_const
  rw [hsum, esq_iteratedDeriv_sum (hg := hgn)]
  rw [Finset.sum_eq_single j]
  · rw [show (fun s : ℝ => ((((Nat.factorial (2 * j) : ℕ) : ℝ))⁻¹) •
          (s ^ j • iteratedDeriv (2 * j) (fun t : ℝ => F (x, t)) 0))
        = ((((Nat.factorial (2 * j) : ℕ) : ℝ))⁻¹) •
          (fun s : ℝ => s ^ j • iteratedDeriv (2 * j) (fun t : ℝ => F (x, t)) 0)
        from rfl]
    rw [iteratedDeriv_const_smul _ _]
    · rw [esq_iteratedDeriv_pow_smul, if_pos rfl, smul_comm]
    · exact ((contDiff_id.pow j).contDiffAt).smul contDiffAt_const
  · intro i _ hij
    rw [show (fun s : ℝ => ((((Nat.factorial (2 * i) : ℕ) : ℝ))⁻¹) •
          (s ^ i • iteratedDeriv (2 * i) (fun t : ℝ => F (x, t)) 0))
        = ((((Nat.factorial (2 * i) : ℕ) : ℝ))⁻¹) •
          (fun s : ℝ => s ^ i • iteratedDeriv (2 * i) (fun t : ℝ => F (x, t)) 0)
        from rfl]
    rw [iteratedDeriv_const_smul _ _]
    · rw [esq_iteratedDeriv_pow_smul, if_neg (Ne.symm hij), zero_smul, smul_zero]
    · exact ((contDiff_id.pow i).contDiffAt).smul contDiffAt_const
  · intro hj'
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)) hj'

/-- The `(2j)`-th `t`-derivative at `0` of the polynomial slice is the `(2j)`-th `t`-derivative of
the slice of `F`. -/
theorem esqPolyT_iteratedDeriv_zero {F : X × ℝ → E}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (m j : ℕ) (hj : j ≤ m) (x : X) :
    iteratedDeriv (2 * j) (fun t : ℝ => esqPolyT F m (x, t)) 0 =
      iteratedDeriv (2 * j) (fun t : ℝ => F (x, t)) 0 := by
  have hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s : ℝ => esqPoly F m (x, s)) :=
    (esqPoly_contDiff hF m).comp (contDiff_const.prodMk contDiff_id)
  have hmain := iteratedDeriv_comp_sq hφ j
  have hpoly := esqPoly_iteratedDeriv_zero F m j hj x
  simp only [esqPolyT]
  rw [hmain, hpoly, smul_smul, smul_smul]
  have hcoef : ((Nat.factorial (2 * j) : ℝ) / (Nat.factorial j : ℝ) *
      (Nat.factorial j : ℝ) * (((Nat.factorial (2 * j) : ℕ) : ℝ))⁻¹) = 1 := by
    have h1 : ((Nat.factorial (2 * j) : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (2 * j)
    have h2 : ((Nat.factorial j : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero j
    field_simp
  rw [hcoef, one_smul]

/-- The `t`-jets of the remainder vanish up to order `2m + 2`. -/
theorem esqR_iteratedDeriv_zero {F : X × ℝ → E}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (heven : ∀ (x : X) (t : ℝ), F (x, -t) = F (x, t))
    (m i : ℕ) (hi : i < 2 * m + 2) (x : X) :
    iteratedDeriv i (fun t : ℝ => F (x, t) - esqPolyT F m (x, t)) 0 = 0 := by
  have hFc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => F (x, t)) :=
    hF.comp (contDiff_const.prodMk contDiff_id)
  have hPc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => esqPolyT F m (x, t)) :=
    (esqPolyT_contDiff hF m).comp (contDiff_const.prodMk contDiff_id)
  have hlin : (fun t : ℝ => F (x, t) - esqPolyT F m (x, t)) =
      (fun t : ℝ => F (x, t)) - (fun t : ℝ => esqPolyT F m (x, t)) := rfl
  rw [hlin, iteratedDeriv_sub (hFc.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))
    (hPc.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))]
  rcases Nat.even_or_odd i with ⟨j, hj⟩ | ⟨j, hj⟩
  · have hj2 : j + j = 2 * j := by omega
    have hjm : j ≤ m := by omega
    rw [hj, hj2, esqPolyT_iteratedDeriv_zero hF m j hjm x, sub_self]
  · subst hj
    have hFe : ∀ t : ℝ, (fun t : ℝ => F (x, t)) (-t) = (fun t : ℝ => F (x, t)) t :=
      fun t => heven x t
    have hPe : ∀ t : ℝ, (fun t : ℝ => esqPolyT F m (x, t)) (-t)
        = (fun t : ℝ => esqPolyT F m (x, t)) t := by
      intro t
      simp only [esqPolyT, esqPoly, neg_sq]
    rw [esq_iteratedDeriv_odd_eq_zero hFe (by exact ⟨j, rfl⟩),
      esq_iteratedDeriv_odd_eq_zero hPe (by exact ⟨j, rfl⟩), sub_zero]

/-- The `i`-th iterated Fréchet derivative at `(x, 0)` evaluated on the constant tuple `(0, 1)` is
the `i`-th one-variable derivative of the slice `t ↦ F (x, t)` at `0`. -/
theorem esq_iteratedFDeriv_apply_one_eq_iteratedDeriv {F : X × ℝ → E}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (x : X) (i : ℕ) :
    iteratedFDeriv ℝ i F (x, 0) (fun _ : Fin i => ((0 : X), (1 : ℝ))) =
      iteratedDeriv i (fun t : ℝ => F (x, t)) 0 := by
  have hmain : ∀ i : ℕ, ∀ t : ℝ,
      iteratedFDeriv ℝ i F (x, t) (fun _ : Fin i => ((0 : X), (1 : ℝ))) =
        iteratedDeriv i (fun u : ℝ => F (x, u)) t := by
    intro i
    induction i with
    | zero =>
      intro t
      rw [iteratedFDeriv_zero_apply, iteratedDeriv_zero]
    | succ i ih =>
      have ihf := funext ih
      intro t
      rw [iteratedDeriv_succ, ← ihf, iteratedFDeriv_succ_apply_left]
      have h1 : HasFDerivAt (fun u : ℝ => (x, u)) (ContinuousLinearMap.inr ℝ X ℝ) t :=
        hasFDerivAt_prodMk_right x t
      have hder : Differentiable ℝ (iteratedFDeriv ℝ i F) :=
        hF.differentiable_iteratedFDeriv (m := i) (by exact_mod_cast ENat.natCast_lt_top i)
      have h2 : HasFDerivAt (iteratedFDeriv ℝ i F)
          (fderiv ℝ (iteratedFDeriv ℝ i F) (x, t)) (x, t) :=
        (hder (x, t)).hasFDerivAt
      have h3 : HasFDerivAt (fun u : ℝ => iteratedFDeriv ℝ i F (x, u))
          ((fderiv ℝ (iteratedFDeriv ℝ i F) (x, t)).comp (ContinuousLinearMap.inr ℝ X ℝ)) t :=
        h2.comp t h1
      have h4 : HasDerivAt (fun u : ℝ => iteratedFDeriv ℝ i F (x, u))
          ((fderiv ℝ (iteratedFDeriv ℝ i F) (x, t)) ((0 : X), (1 : ℝ))) t := by
        simpa using h3.hasDerivAt
      have h5 : HasDerivAt (fun u : ℝ => (iteratedFDeriv ℝ i F (x, u))
            (fun _ : Fin i => ((0 : X), (1 : ℝ))))
          (((fderiv ℝ (iteratedFDeriv ℝ i F) (x, t)) ((0 : X), (1 : ℝ)))
            (fun _ : Fin i => ((0 : X), (1 : ℝ)))) t := by
        have h := HasFDerivAt.comp_hasDerivAt t
          (ContinuousLinearMap.hasFDerivAt (ContinuousMultilinearMap.apply ℝ
            (fun _ : Fin i => X × ℝ) E (fun _ : Fin i => ((0 : X), (1 : ℝ))))) h4
        simpa [ContinuousMultilinearMap.apply_apply, Function.comp_def] using h
      rw [h5.deriv, Fin.tail_def]
  exact hmain i 0

/-- The `iteratedFDeriv` form of the vanishing of the jets of the remainder. -/
theorem esqR_iteratedFDeriv_zero {F : X × ℝ → E}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (heven : ∀ (x : X) (t : ℝ), F (x, -t) = F (x, t))
    (m j : ℕ) (hj : j < 2 * m + 2) (x : X) :
    iteratedFDeriv ℝ j (esqR F m) (x, 0) (fun _ : Fin j => ((0 : X), (1 : ℝ))) = 0 := by
  have hR : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (esqR F m) :=
    hF.sub (esqPolyT_contDiff hF m)
  rw [esq_iteratedFDeriv_apply_one_eq_iteratedDeriv hR x j]
  exact esqR_iteratedDeriv_zero hF heven m j hj x

/-- **Quantitative flat descent for the Taylor remainder.**  The function which is
`R_m (x, √s)` for `s > 0` and `0` for `s ≤ 0` is `C^m`. -/
theorem esqR_drop_contDiff {F : X × ℝ → E}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (heven : ∀ (x : X) (t : ℝ), F (x, -t) = F (x, t)) (m : ℕ) :
    ContDiff ℝ m (fun p : X × ℝ =>
      if 0 < p.2 then esqR F m (p.1, Real.sqrt p.2) else 0) := by
  have hR : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (esqR F m) :=
    hF.sub (esqPolyT_contDiff hF m)
  refine contDiff_trunc_sqrt (K := 2 * m + 2) (m := m) le_rfl (fun z _ => hR.contDiffAt) ?_
  exact flat_bounds_of_jets hR (fun j hj x => esqR_iteratedFDeriv_zero hF heven m j hj x)

/-! ### The parametric descent -/

/-- **The even `√`-descent, parametric version.**  If `F : X × ℝ → E` is `C^∞` and even in its
second variable, then `(x, s) ↦ F (x, √s)` is `C^∞` on the closed half-space `X × [0, ∞)`. -/
theorem contDiffOn_evenSqrtParam {F : X × ℝ → E}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (heven : ∀ (x : X) (t : ℝ), F (x, -t) = F (x, t)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : X × ℝ => F (p.1, Real.sqrt p.2))
      (Set.univ ×ˢ Set.Ici (0 : ℝ)) := by
  rw [contDiffOn_infty]
  intro m
  have hfull : ContDiff ℝ m (fun p : X × ℝ =>
      esqPoly F m p + (if 0 < p.2 then esqR F m (p.1, Real.sqrt p.2) else 0)) := by
    refine ContDiff.add ((esqPoly_contDiff hF m).of_le (WithTop.coe_le_coe.mpr le_top)) ?_
    exact esqR_drop_contDiff hF heven m
  refine (hfull.contDiffOn).congr ?_
  intro p hp
  have hp2 : (0 : ℝ) ≤ p.2 := hp.2
  rcases eq_or_lt_of_le hp2 with h0 | hpos
  · -- `p.2 = 0`
    have hp0 : p.2 = (0 : ℝ) := h0.symm
    have hz0 : F (p.1, (0 : ℝ)) - esqPolyT F m (p.1, (0 : ℝ)) = 0 := by
      have h := esqR_iteratedDeriv_zero hF heven m 0 (by omega) p.1
      simpa [esqR, iteratedDeriv_zero] using h
    have hT0 : esqPolyT F m (p.1, (0 : ℝ)) = esqPoly F m (p.1, (0 : ℝ)) := by
      simp [esqPolyT]
    have heq : esqPoly F m (p.1, (0 : ℝ)) = F (p.1, (0 : ℝ)) := by
      rw [hT0] at hz0
      exact (sub_eq_zero.mp hz0).symm
    have hp' : p = (p.1, (0 : ℝ)) := by
      ext <;> simp [hp0]
    rw [hp', if_neg (lt_irrefl (0 : ℝ)), add_zero, Real.sqrt_zero, heq]
  · -- `p.2 > 0`
    have hval : esqR F m (p.1, Real.sqrt p.2) = F (p.1, Real.sqrt p.2) - esqPoly F m p := by
      simp only [esqR, esqPolyT]
      rw [Real.sq_sqrt hp2, Prod.mk.eta]
    rw [if_pos hpos, hval]
    abel

end Work.Drive
