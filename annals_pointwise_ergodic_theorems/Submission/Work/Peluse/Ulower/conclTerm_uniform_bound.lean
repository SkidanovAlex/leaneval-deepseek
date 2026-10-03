import Mathlib
import Submission.Work.Peluse.Ulower.stepBasic
import Submission.Work.Peluse.Ulower.supportIn_tsum_le
import Submission.Work.Peluse.Ulower.dualFn_tsum_le

/-!
# The uniform bound on the conclusion term `‖L⁻¹ ∑_x F₂(x) e(θx)‖`

This module proves `Work.Peluse.Ulower.conclTerm_uniform_bound`: for `f₀, f₁ : ℤ → ℂ` bounded by
`1` in sup norm and supported in `[-L, L]`, for any polynomial `P`, any `M ≥ 1`, any family
`sh : Fin σ → ℤ × ℤ` of shift pairs with both coordinates bounded by `D ≤ L`, and any frequency
`θ : ℝ`, the Fourier coefficient at `θ` of the dual function of the two iterated
`Δ'`-differences is bounded by a constant depending only on `σ`:

`‖L⁻¹ ∑'_x F₂(x) e(θx)‖ ≤ 3 + 4σ`,  `F₂ = dualFn M P (iterDelta' σ sh f₀) (iterDelta' σ sh f₁)`.

This is the uniform *upper* bound on the terms whose *lower* bound is the content of Peluse's
Lemma 7.4 (`Work.Peluse.Ulower.lemma74_denseSet`); it is what makes the Markov/density extraction
there legitimate, since the terms of that conclusion are genuine averages of a quantity bounded by
`3 + 4σ`.

## The argument

Write `g_j = iterDelta' σ sh f_j`.

1. `‖g_j‖ ≤ 1` pointwise and `g_j` is supported in `symIcc ((2σ+1)L)`: the support of an iterated
   `Δ'`-difference is `symIcc (L + ∑ᵢ (|(sh i).1| + |(sh i).2|))`
   (`Work.Peluse.Ulower.iterDelta'_supportIn`) and `∑ᵢ (|(sh i).1| + |(sh i).2|) ≤ 2σD ≤ 2σL`.
2. `∑'_x ‖dualFn M P g₀ g₁ x‖ ≤ ∑'_x ‖g₁ x‖ ≤ 2((2σ+1)L) + 1 = (4σ+2)L + 1`, the first step being
   the `ℓ¹`-contraction `Work.Peluse.Ulower.dualFn_tsum_le` (this is where the `P`- and
   `M`-dependence of the dual function disappears) and the second the trivial cardinality bound on
   its support.
3. The phase factor `e(θx)` has modulus `1`, so the triangle inequality for `tsum` gives
   `‖∑'_x F₂(x) e(θx)‖ ≤ ∑'_x ‖F₂ x‖`; the dual function of finitely supported functions is
   finitely supported, so all the sums are genuine.
4. Dividing by `L ≥ 1`: `L⁻¹((4σ+2)L + 1) = 4σ + 2 + L⁻¹ ≤ 4σ + 3`.
-/

open scoped BigOperators

namespace Work.Peluse.Ulower

noncomputable section

open Work.Peluse

/-! ## Elementary helper lemmas -/

/-- The total shift of an iterated `Δ'`-difference is at most `2σD` when all shift coordinates
are bounded by `D` in absolute value. -/
lemma shift_sum_natAbs_le {σ D : ℕ} {sh : Fin σ → ℤ × ℤ}
    (hsh : ∀ i : Fin σ, |(sh i).1| ≤ (D : ℤ) ∧ |(sh i).2| ≤ (D : ℤ)) :
    (∑ i : Fin σ, ((sh i).1.natAbs + (sh i).2.natAbs)) ≤ 2 * σ * D := by
  have hterm : ∀ i : Fin σ, ((sh i).1.natAbs + (sh i).2.natAbs) ≤ 2 * D := by
    intro i
    have h1 : (((sh i).1.natAbs : ℕ) : ℤ) ≤ (D : ℤ) := by
      rw [Int.natCast_natAbs]; exact (hsh i).1
    have h2 : (((sh i).2.natAbs : ℕ) : ℤ) ≤ (D : ℤ) := by
      rw [Int.natCast_natAbs]; exact (hsh i).2
    omega
  calc (∑ i : Fin σ, ((sh i).1.natAbs + (sh i).2.natAbs))
      ≤ ∑ _i : Fin σ, (2 * D) := Finset.sum_le_sum fun i _ => hterm i
    _ = σ * (2 * D) := by simp
    _ = 2 * σ * D := by ring

/-- The iterated `Δ'`-difference of a function supported in `[-L, L]` is supported in
`[-((2σ+1)L), (2σ+1)L]` when all the shift coordinates are bounded by `D ≤ L` in absolute value.

This is `Work.Peluse.Ulower.iterDelta'_supportIn` (which gives the sharper support radius
`L + ∑ᵢ (|(sh i).1| + |(sh i).2|)`) combined with `shift_sum_natAbs_le` and `D ≤ L`. -/
lemma iterDelta'_supportIn_le {σ L D : ℕ} (hDL : D ≤ L) {sh : Fin σ → ℤ × ℤ}
    (hsh : ∀ i : Fin σ, |(sh i).1| ≤ (D : ℤ) ∧ |(sh i).2| ≤ (D : ℤ)) {F : ℤ → ℂ}
    (hF : ∀ x : ℤ, x ∉ symIcc L → F x = 0) :
    SupportIn (iterDelta' σ sh F) ((2 * σ + 1) * L) := by
  have hsum : (∑ i : Fin σ, ((sh i).1.natAbs + (sh i).2.natAbs)) ≤ 2 * σ * L :=
    le_trans (shift_sum_natAbs_le hsh) (Nat.mul_le_mul_left (2 * σ) hDL)
  have hN : L + (∑ i : Fin σ, ((sh i).1.natAbs + (sh i).2.natAbs)) ≤ (2 * σ + 1) * L := by
    calc L + (∑ i : Fin σ, ((sh i).1.natAbs + (sh i).2.natAbs)) ≤ L + 2 * σ * L :=
          Nat.add_le_add_left hsum L
      _ = (2 * σ + 1) * L := by ring
  intro x hx
  refine iterDelta'_supportIn σ sh hF x (fun hmem => ?_)
  rw [mem_symIcc_iff] at hmem
  omega

/-- The iterated `Δ'`-difference of a function bounded by `1` is bounded by `1`. -/
lemma norm_iterDeltaPrime_le_one : ∀ (k : ℕ) (sh : Fin k → ℤ × ℤ) (G : ℤ → ℂ),
    (∀ x : ℤ, ‖G x‖ ≤ 1) → ∀ x : ℤ, ‖iterDelta' k sh G x‖ ≤ 1 := by
  intro k
  induction k with
  | zero => intro sh G h x; exact h x
  | succ k ih =>
      intro sh G h x
      have hdef : iterDelta' (k + 1) sh G x =
          star (iterDelta' k (fun i => sh i.succ) G (x + (sh 0).1)) *
            iterDelta' k (fun i => sh i.succ) G (x + (sh 0).2) := rfl
      rw [hdef, norm_mul, norm_star]
      have h1 := ih (fun i => sh i.succ) G h (x + (sh 0).1)
      have h2 := ih (fun i => sh i.succ) G h (x + (sh 0).2)
      nlinarith [norm_nonneg (iterDelta' k (fun i => sh i.succ) G (x + (sh 0).1)),
        norm_nonneg (iterDelta' k (fun i => sh i.succ) G (x + (sh 0).2))]

/-- The phase factor `e(θx) = exp(2πiθx)` has modulus one. -/
lemma norm_exp_two_pi_I_mul (θ : ℝ) (x : ℤ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * θ * (x : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have hre : (2 * Real.pi * Complex.I * θ * (x : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  rw [hre, Real.exp_zero]

/-! ## The target -/

theorem conclTerm_uniform_bound {σ M L D : ℕ} (hL : 1 ≤ L) (hM : 1 ≤ M) (hDL : D ≤ L)
    (P : Polynomial ℤ) (f₀ f₁ : ℤ → ℂ)
    (h0 : ∀ x : ℤ, ‖f₀ x‖ ≤ 1) (h1 : ∀ x : ℤ, ‖f₁ x‖ ≤ 1)
    (hs0 : ∀ x : ℤ, x ∉ Work.Peluse.symIcc L → f₀ x = 0)
    (hs1 : ∀ x : ℤ, x ∉ Work.Peluse.symIcc L → f₁ x = 0)
    (sh : Fin σ → ℤ × ℤ) (hsh : ∀ i : Fin σ, |(sh i).1| ≤ (D : ℤ) ∧ |(sh i).2| ≤ (D : ℤ))
    (θ : ℝ) :
    ‖((L : ℂ))⁻¹ * ∑' x : ℤ, Work.Peluse.dualFn M P (Work.Peluse.Ulower.iterDelta' σ sh f₀)
        (Work.Peluse.Ulower.iterDelta' σ sh f₁) x *
      Complex.exp (2 * Real.pi * Complex.I * θ * (x : ℂ))‖ ≤ 3 + 4 * (σ : ℝ) := by
  set g₀ : ℤ → ℂ := iterDelta' σ sh f₀ with hg₀def
  set g₁ : ℤ → ℂ := iterDelta' σ sh f₁ with hg₁def
  set F : ℤ → ℂ := Work.Peluse.dualFn M P g₀ g₁ with hFdef
  show ‖((L : ℂ))⁻¹ * ∑' x : ℤ, F x * Complex.exp (2 * Real.pi * Complex.I * θ * (x : ℂ))‖
      ≤ 3 + 4 * (σ : ℝ)
  have hb0 : ∀ x : ℤ, ‖g₀ x‖ ≤ 1 := norm_iterDeltaPrime_le_one σ sh f₀ h0
  have hb1 : ∀ x : ℤ, ‖g₁ x‖ ≤ 1 := norm_iterDeltaPrime_le_one σ sh f₁ h1
  have hsupp0 : SupportIn g₀ ((2 * σ + 1) * L) := iterDelta'_supportIn_le hDL hsh hs0
  have hsupp1 : SupportIn g₁ ((2 * σ + 1) * L) := iterDelta'_supportIn_le hDL hsh hs1
  have hfin1 : FinSuppZ g₁ := FinSuppZ.of_supportIn hsupp1
  -- the `ℓ¹` mass of `g₁`
  have hl1 : (∑' x : ℤ, ‖g₁ x‖) ≤ (((4 * σ + 2) * L + 1 : ℕ) : ℝ) := by
    have h := supportIn_tsum_le hsupp1 hb1
    have hcast : (2 * ((2 * σ + 1) * L) + 1 : ℕ) = (4 * σ + 2) * L + 1 := by ring
    rw [hcast] at h
    exact h
  -- the `ℓ¹` mass of the dual function is at most that of `g₁`
  have hdual : (∑' x : ℤ, ‖F x‖) ≤ ∑' x : ℤ, ‖g₁ x‖ :=
    dualFn_tsum_le (N := M) hM P g₀ g₁ hb0 hfin1
  -- the dual function is finitely supported, hence `‖F ·‖` is summable
  have hsuppF : SupportIn F (dSup P (max ((2 * σ + 1) * L) M) M) :=
    Work.Peluse.Tools.dualFn_supportIn (Nat.lt_of_lt_of_le Nat.zero_lt_one hM) P g₀ g₁
      (hsupp0.mono (le_max_left _ _)) (hsupp1.mono (le_max_left _ _)) (le_max_right _ _)
  have hsumF : Summable (fun x : ℤ => ‖F x‖) := by
    apply summable_of_ne_finset_zero
      (s := Finset.Icc (-((dSup P (max ((2 * σ + 1) * L) M) M : ℕ) : ℤ))
        ((dSup P (max ((2 * σ + 1) * L) M) M : ℕ) : ℤ))
    intro x hx
    rw [norm_eq_zero]
    exact supportIn_off_Icc hsuppF x hx
  -- the Fourier coefficient is bounded by the `ℓ¹` mass
  have hsumFw : Summable
      (fun x : ℤ => ‖F x * Complex.exp (2 * Real.pi * Complex.I * θ * (x : ℂ))‖) := by
    refine hsumF.congr (fun x => ?_)
    rw [norm_mul, norm_exp_two_pi_I_mul θ x, mul_one]
  have hnorm_tsum : ‖∑' x : ℤ, F x * Complex.exp (2 * Real.pi * Complex.I * θ * (x : ℂ))‖
      ≤ ∑' x : ℤ, ‖F x‖ := by
    have h := norm_tsum_le_tsum_norm hsumFw
    have hcongr : (∑' x : ℤ, ‖F x * Complex.exp (2 * Real.pi * Complex.I * θ * (x : ℂ))‖)
        = ∑' x : ℤ, ‖F x‖ :=
      tsum_congr (fun x => by rw [norm_mul, norm_exp_two_pi_I_mul θ x, mul_one])
    rwa [hcongr] at h
  -- the arithmetic
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have h1L : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < (L : ℝ) := lt_of_lt_of_le zero_lt_one h1L
  have hLnonneg : (0 : ℝ) ≤ ((L : ℝ))⁻¹ := inv_nonneg.mpr (le_of_lt hLpos)
  have hlinv : ((L : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1L
  have hcast : (((4 * σ + 2) * L + 1 : ℕ) : ℝ) = (4 * (σ : ℝ) + 2) * (L : ℝ) + 1 := by
    push_cast; ring
  have hkey : ((L : ℝ))⁻¹ * (((4 * σ + 2) * L + 1 : ℕ) : ℝ)
      = 4 * (σ : ℝ) + 2 + ((L : ℝ))⁻¹ := by
    rw [hcast]
    field_simp
  calc ((L : ℝ))⁻¹ * ‖∑' x : ℤ, F x * Complex.exp (2 * Real.pi * Complex.I * θ * (x : ℂ))‖
      ≤ ((L : ℝ))⁻¹ * (∑' x : ℤ, ‖F x‖) := mul_le_mul_of_nonneg_left hnorm_tsum hLnonneg
    _ ≤ ((L : ℝ))⁻¹ * (∑' x : ℤ, ‖g₁ x‖) := mul_le_mul_of_nonneg_left hdual hLnonneg
    _ ≤ ((L : ℝ))⁻¹ * (((4 * σ + 2) * L + 1 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hl1 hLnonneg
    _ = 4 * (σ : ℝ) + 2 + ((L : ℝ))⁻¹ := hkey
    _ ≤ 3 + 4 * (σ : ℝ) := by linarith

end

end Work.Peluse.Ulower
