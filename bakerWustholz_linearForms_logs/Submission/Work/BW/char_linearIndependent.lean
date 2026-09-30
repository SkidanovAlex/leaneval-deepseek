import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.ratSpan_saturation
import Submission.Work.BW.exists_rat_kernel_functional
import Submission.Work.BW.exists_cplx_kernel_notMem_int

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1000000

namespace Work.BW

/-! # Linear independence of the characters `y ↦ ∏_m y_m ^ (v m)` on the torus `ker M`

Let `M : Fin ρ → Fin N → ℤ` be a primitive system of integer linear forms and let `𝒵` be the
`ℤ`-span of its rows. For a vector `v : Fin N → ℤ` the monomial character
`χ_v : y ↦ ∏_m y_m ^ (v m)` of the torus is trivial on the torus points of `ker M` exactly when
`v ∈ 𝒵`. We prove this here in the exponential parametrisation: a complex vector `z` with
`M z ∈ ℤ^ρ` gives a torus point `y_m = e^{2πi z_m}` of `ker M`, and then
`∏_m y_m ^ (v m) = e^{2πi ⟨v, z⟩}`.

The main use is the linear independence of pairwise distinct characters (`linearIndependent_monoidHom`,
Dedekind's theorem), which is the content of `char_linearIndependent` below. -/

/-- The additive group of "logarithms" of points of `ker M`: the complex vectors `z` whose
`M`-image is an integral vector. Exponentiating such a `z` coordinatewise,
`y_m = e^{2πi z_m}`, produces a torus point with `∏_m y_m ^ (M j m) = 1` for every row `j`. -/
def logKer {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) : AddSubgroup (Fin N → ℂ) where
  carrier := {z | ∀ j, ∃ n : ℤ, ∑ m, (M j m : ℂ) * z m = (n : ℂ)}
  zero_mem' := by intro j; exact ⟨0, by simp⟩
  add_mem' := by
    intro z w hz hw j
    obtain ⟨n, hn⟩ := hz j
    obtain ⟨n', hn'⟩ := hw j
    refine ⟨n + n', ?_⟩
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hn, hn', Int.cast_add]
  neg_mem' := by
    intro z hz j
    obtain ⟨n, hn⟩ := hz j
    refine ⟨-n, ?_⟩
    simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, hn, Int.cast_neg]

/-- The character `y ↦ ∏_m y_m ^ (v m)` of the torus `ker M`, in the exponential parametrisation:
`z ↦ e^{2πi ⟨v, z⟩}`. -/
noncomputable def charM {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) (v : Fin N → ℤ) :
    Multiplicative (logKer M) →* ℂ where
  toFun z := Complex.exp (2 * ↑Real.pi * Complex.I * ∑ m, (v m : ℂ) * (z.toAdd : Fin N → ℂ) m)
  map_one' := by simp
  map_mul' := by
    intro a b
    have hsum : ∑ m, (v m : ℂ) * ((a * b).toAdd : Fin N → ℂ) m
        = (∑ m, (v m : ℂ) * (a.toAdd : Fin N → ℂ) m)
          + ∑ m, (v m : ℂ) * (b.toAdd : Fin N → ℂ) m := by
      simp only [toAdd_mul, AddSubgroup.coe_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    rw [hsum, mul_add, Complex.exp_add]

/-- `∏_m (e^{2πi z_m}) ^ (c_m) = e^{2πi ∑_m c_m z_m}`. -/
lemma prod_exp_zpow {N : ℕ} (c : Fin N → ℤ) (z : Fin N → ℂ) :
    ∏ m, (Complex.exp (2 * ↑Real.pi * Complex.I * z m)) ^ (c m)
      = Complex.exp (2 * ↑Real.pi * Complex.I * ∑ m, (c m : ℂ) * z m) := by
  have h1 : ∀ m, (Complex.exp (2 * ↑Real.pi * Complex.I * z m)) ^ (c m)
      = Complex.exp ((c m : ℂ) * (2 * ↑Real.pi * Complex.I * z m)) :=
    fun m => (Complex.exp_int_mul _ _).symm
  simp_rw [h1]
  rw [← Complex.exp_sum]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  ring

/-- An integral vector of the `ℚ`-span of the rows is not merely a rational combination; it is
already a rational combination in the sense needed to apply `exists_rat_kernel_functional`. -/
lemma not_rat_span_of_not_int_span {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) (hM : PrimSys M)
    (u : Fin N → ℤ) (hu : ¬ ∃ c : Fin ρ → ℤ, ∀ m, u m = ∑ r, c r * M r m) :
    ¬ ∃ c : Fin ρ → ℚ, ∀ m, (u m : ℚ) = ∑ r, c r * (M r m : ℚ) := by
  intro h
  apply ratSpan_saturation M hM u hu
  rw [Submodule.mem_span_range_iff_exists_fun ℚ]
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  funext m
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using (hc m).symm

/-- Linear independence of distinct characters on `ker M`: if `v : Fin k → Fin N → ℤ` has pairwise distinct classes modulo the `ℤ`-span `𝒵` of the rows of `M`, then a `ℂ`-linear combination of the characters `y ↦ ∏ₘ yₘ^{vᵢₘ}` vanishing on all torus points of `ker M` has all coefficients zero. (Distinct classes give distinct characters by a non-trivial character of the f.g. abelian group `ℤ^N/𝒵`; distinct characters are linearly independent by `linearIndependent_monoidHom`.) -/
theorem char_linearIndependent {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) (hM : PrimSys M) {k : ℕ}
    (v : Fin k → Fin N → ℤ)
    (hv : ∀ i j, i ≠ j → ¬ ∃ c : Fin ρ → ℤ, ∀ m, v i m - v j m = ∑ r, c r * M r m)
    (cc : Fin k → ℂ)
    (h0 : ∀ y : Fin N → ℂ, (∀ i, y i ≠ 0) → (∀ j, ∏ i, y i ^ (M j i) = 1) →
        ∑ i, cc i * ∏ m, y m ^ (v i m) = 0) :
    ∀ i, cc i = 0 := by
  classical
  -- ### Step 1: distinct classes modulo `𝒵` give distinct characters
  have hdist : ∀ i j : Fin k, i ≠ j → charM M (v i) ≠ charM M (v j) := by
    intro i j hij heq
    -- the difference vector `u = v i - v j` is outside the row lattice
    have hnotZ : ¬ ∃ c : Fin ρ → ℤ, ∀ m, (fun m => v i m - v j m) m = ∑ r, c r * M r m :=
      hv i j hij
    have hnotQ : ¬ ∃ c : Fin ρ → ℚ, ∀ m, ((v i m - v j m : ℤ) : ℚ) = ∑ r, c r * (M r m : ℚ) :=
      not_rat_span_of_not_int_span M hM (fun m => v i m - v j m) hnotZ
    -- a rational kernel vector on which `⟨u, ·⟩` is nonzero, then scaled to a complex one
    obtain ⟨ξ, hξA, hξu⟩ := exists_rat_kernel_functional M (fun m => v i m - v j m) hnotQ
    obtain ⟨z, hzA, hzu⟩ :=
      exists_cplx_kernel_notMem_int M (fun m => v i m - v j m) ξ hξA hξu
    -- `z` is a logarithm of a point of `ker M`
    have hzmem : z ∈ logKer M := by
      intro j'
      refine ⟨0, ?_⟩
      rw [hzA j']
      norm_num
    -- ... at which the two characters differ
    have hpt : charM M (v i) (Multiplicative.ofAdd ⟨z, hzmem⟩)
        ≠ charM M (v j) (Multiplicative.ofAdd ⟨z, hzmem⟩) := by
      intro hw
      rw [show charM M (v i) (Multiplicative.ofAdd ⟨z, hzmem⟩)
            = Complex.exp (2 * ↑Real.pi * Complex.I * ∑ m, (v i m : ℂ) * z m) from rfl,
          show charM M (v j) (Multiplicative.ofAdd ⟨z, hzmem⟩)
            = Complex.exp (2 * ↑Real.pi * Complex.I * ∑ m, (v j m : ℂ) * z m) from rfl] at hw
      have hexp : Complex.exp (2 * ↑Real.pi * Complex.I * ∑ m, (v i m : ℂ) * z m
            - 2 * ↑Real.pi * Complex.I * ∑ m, (v j m : ℂ) * z m) = 1 := by
        rw [Complex.exp_sub, hw, div_self (Complex.exp_ne_zero _)]
      have hsub : 2 * ↑Real.pi * Complex.I * ∑ m, (v i m : ℂ) * z m
            - 2 * ↑Real.pi * Complex.I * ∑ m, (v j m : ℂ) * z m
          = 2 * ↑Real.pi * Complex.I * ∑ m, ((v i m - v j m : ℤ) : ℂ) * z m := by
        have h1 : (∑ m, (v i m : ℂ) * z m) - (∑ m, (v j m : ℂ) * z m)
            = ∑ m, ((v i m - v j m : ℤ) : ℂ) * z m := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro m _
          push_cast
          ring
        rw [← mul_sub, h1]
      rw [hsub, Complex.exp_eq_one_iff] at hexp
      obtain ⟨n, hn⟩ := hexp
      apply hzu
      refine ⟨n, ?_⟩
      have hn' : 2 * ↑Real.pi * Complex.I * (∑ m, ((v i m - v j m : ℤ) : ℂ) * z m)
          = 2 * ↑Real.pi * Complex.I * (n : ℂ) := by
        rw [hn]
        ring
      exact mul_left_cancel₀ Complex.two_pi_I_ne_zero hn'
    exact hpt (heq ▸ rfl)
  have hinj : Function.Injective (fun i : Fin k => charM M (v i)) := by
    intro i j hij
    by_contra hne
    exact hdist i j hne hij
  -- ### Step 2: the combination vanishes at every torus point of `ker M`
  have hbridge : ∀ z : Multiplicative (logKer M), ∑ i, cc i * charM M (v i) z = 0 := by
    intro z
    have hne : ∀ m, Complex.exp (2 * ↑Real.pi * Complex.I * (z.toAdd : Fin N → ℂ) m) ≠ 0 :=
      fun m => Complex.exp_ne_zero _
    have hker : ∀ j, ∏ m,
        (Complex.exp (2 * ↑Real.pi * Complex.I * (z.toAdd : Fin N → ℂ) m)) ^ (M j m) = 1 := by
      intro j
      obtain ⟨n, hn⟩ := z.toAdd.2 j
      rw [prod_exp_zpow, hn,
        show 2 * ↑Real.pi * Complex.I * (n : ℂ) = (n : ℂ) * (2 * ↑Real.pi * Complex.I) by ring]
      exact Complex.exp_int_mul_two_pi_mul_I n
    have hmain : ∑ i, cc i * ∏ m,
        (Complex.exp (2 * ↑Real.pi * Complex.I * (z.toAdd : Fin N → ℂ) m)) ^ (v i m) = 0 :=
      h0 _ hne hker
    calc ∑ i, cc i * charM M (v i) z
        = ∑ i, cc i * ∏ m,
            (Complex.exp (2 * ↑Real.pi * Complex.I * (z.toAdd : Fin N → ℂ) m)) ^ (v i m) := by
          apply Finset.sum_congr rfl
          intro i _
          congr 1
          rw [prod_exp_zpow]
          rfl
      _ = 0 := hmain
  -- ### Step 3: Dedekind's theorem
  have hLI : LinearIndependent ℂ (fun i : Fin k => ⇑(charM M (v i))) :=
    (linearIndependent_monoidHom (Multiplicative (logKer M)) ℂ).comp
      (fun i => charM M (v i)) hinj
  have hzero : (∑ i, cc i • (⇑(charM M (v i))) : Multiplicative (logKer M) → ℂ) = 0 := by
    funext z
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
    exact hbridge z
  exact Fintype.linearIndependent_iff.mp hLI cc hzero

end Work.BW
