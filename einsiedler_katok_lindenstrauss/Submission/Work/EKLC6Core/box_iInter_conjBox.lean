import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.conjBox_nhds
import Submission.Work.EKLC6Core.Covariant
import Submission.Work.EKLProd.aDiag_nsmul

/-!
# `EKLC6Core.box_iInter_conjBox` — the contracted boxes shrink to `1`

For a horospherical subgroup `U ≤ SL₃(ℝ)` and an exponent vector `t` whose diagonal flow
`a = aDiag t` *contracts* `U` (every `u ∈ U` has `aⁿ u a⁻ⁿ → 1`), the descending family of
conjugated boxes

`conjBox U (n t) = (aDiag t)ⁿ · B₁^U · (aDiag t)⁻ⁿ`

has intersection `{1}`.

This is the "descending half" of the elementary box geometry of Pisa §7 (the descending family
`n ↦ conjBox U (n t)` plays the role that the balls `a⁻ⁿ B₁ aⁿ` play in the classical
Mautner-type arguments).

The proof is entrywise and does not need `IsHoro U` at all beyond the fact that
`g ∈ conjBox U 0 = B₁^U ⊆ U`, so that the contraction hypothesis applies to `g`.  Writing a
matrix entry as a function of `n`:

* `((aDiag t)ⁿ · g · (aDiag t)⁻ⁿ)ᵢⱼ = e^{n (tᵢ - tⱼ)} gᵢⱼ`  (`boxi_conj_pow_apply`),
* `((aDiag t)⁻ⁿ · g · (aDiag t)ⁿ)ᵢⱼ = e^{n (tⱼ - tᵢ)} gᵢⱼ`  (`boxi_conj_pow_apply_inv`);

membership of `g` in `conjBox U (n t)` says exactly that the second matrix lies in `B₁^U`, i.e.
has all entries bounded by `1` in absolute value (`boxi_conj_pow_apply_inv` + the definition of
`B₁^U`), while the contraction hypothesis says the first matrix tends to `1`, i.e. its entries
tend to `δᵢⱼ`.  Hence for `i ≠ j`:

* if `tᵢ < tⱼ`, the bound `e^{n(tⱼ-tᵢ)} |gᵢⱼ| ≤ 1` for all `n` forces `gᵢⱼ = 0` (the exponential
  is unbounded);
* if `tᵢ ≥ tⱼ`, the convergence `e^{n(tᵢ-tⱼ)} gᵢⱼ → 0` forces `gᵢⱼ = 0` (the factor
  `e^{n(tᵢ-tⱼ)}` is bounded below by `1`);

and for `i = j` the convergence is `gᵢᵢ → 1`, so `gᵢᵢ = 1`.  Thus `g = 1`.

Since the two hypotheses are used only through these two sequences, the same argument gives the
result for any subgroup `U`; `IsHoro U` is carried along to match the ambient vocabulary.
-/

open Filter Topology
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-! ## Conjugation by powers of the diagonal flow, entrywise -/

/-- `aDiag` sends the `ℝ`-scalar multiple `n • t` to the `n`-th power of `aDiag t`. -/
theorem boxi_aDiag_cast_smul (t : Fin 3 → ℝ) (n : ℕ) :
    aDiag ((n : ℝ) • t) = aDiag t ^ n := by
  have h : ((n : ℝ) • t : Fin 3 → ℝ) = n • t := by ext i; simp
  rw [h, Work.EKLProd.aDiag_nsmul]

/-- **The diagonal flow scales the entries**: conjugation by `aDiag s` multiplies the entry
`(i,j)` by `e^{sᵢ - sⱼ}`. -/
theorem boxi_conj_apply (s : Fin 3 → ℝ) (g : SL3) (i j : Fin 3) :
    (aDiag s * g * (aDiag s)⁻¹ : SL3) i j = Real.exp (s i - s j) * g i j := by
  rw [aDiag_inv_eq_neg]
  have h := aDiag_conj_entry (-s) g i j
  rw [show (-(-s) : Fin 3 → ℝ) = s from by rw [neg_neg]] at h
  rw [h]
  have hexp : (-s) j - (-s) i = s i - s j := by simp only [Pi.neg_apply]; ring
  rw [hexp]

/-- Conjugation by the `n`-th power: `((aDiag t)ⁿ g (aDiag t)⁻ⁿ)ᵢⱼ = e^{n (tᵢ - tⱼ)} gᵢⱼ`. -/
theorem boxi_conj_pow_apply (t : Fin 3 → ℝ) (n : ℕ) (g : SL3) (i j : Fin 3) :
    (aDiag t ^ n * g * (aDiag t ^ n)⁻¹ : SL3) i j
      = Real.exp ((n : ℝ) * (t i - t j)) * g i j := by
  rw [← boxi_aDiag_cast_smul t n, boxi_conj_apply]
  congr 1
  simp only [Pi.smul_apply]
  ring_nf

/-- The opposite orientation: `((aDiag t)⁻ⁿ g (aDiag t)ⁿ)ᵢⱼ = e^{n (tⱼ - tᵢ)} gᵢⱼ`. -/
theorem boxi_conj_pow_apply_inv (t : Fin 3 → ℝ) (n : ℕ) (g : SL3) (i j : Fin 3) :
    ((aDiag t ^ n)⁻¹ * g * aDiag t ^ n : SL3) i j
      = Real.exp ((n : ℝ) * (t j - t i)) * g i j := by
  have h1 : (aDiag t ^ n)⁻¹ = aDiag (-t) ^ n := by
    rw [← inv_pow (aDiag t) n, aDiag_inv_eq_neg]
  have h2 : aDiag t ^ n = ((aDiag (-t)) ^ n)⁻¹ := by
    rw [← inv_pow (aDiag (-t)) n, aDiag_inv_eq_neg, neg_neg]
  rw [h1, h2, boxi_conj_pow_apply]
  congr 1
  simp only [Pi.neg_apply]
  ring_nf

/-! ## Two scalar lemmas: the exponential factor `e^{n c}` grows (or is bounded below by `1`) -/

/-- `n ↦ e^{n c}` tends to `+∞` for `c > 0`. -/
theorem boxi_tendsto_exp_nat_mul_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * c)) atTop atTop :=
  Real.tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop.atTop_mul_const hc)

/-- If `|e^{n c} x| ≤ 1` for all `n` and `c > 0`, then `x = 0`. -/
theorem boxi_eq_zero_of_abs_exp_le_one {c x : ℝ} (hc : 0 < c)
    (h : ∀ n : ℕ, |Real.exp ((n : ℝ) * c) * x| ≤ 1) : x = 0 := by
  by_contra hx
  have hxpos : 0 < |x| := abs_pos.mpr hx
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    ((boxi_tendsto_exp_nat_mul_atTop hc).eventually_gt_atTop (2 / |x|))
  have h1 := h N
  rw [abs_mul, abs_of_pos (Real.exp_pos _)] at h1
  have h2 : 2 < Real.exp ((N : ℝ) * c) * |x| := by
    have h3 := hN N le_rfl
    rw [div_lt_iff₀ hxpos] at h3
    linarith
  linarith

/-- If `e^{n c} x → 0` with `0 ≤ c`, then `x = 0` (the factor `e^{n c}` is bounded below by
`1`). -/
theorem boxi_eq_zero_of_tendsto_exp_mul {c x : ℝ} (hc : 0 ≤ c)
    (h : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * c) * x) atTop (nhds 0)) : x = 0 := by
  rcases lt_or_eq_of_le hc with hc' | hc'
  · by_contra hx
    have hxpos : 0 < |x| := abs_pos.mpr hx
    have habs : Tendsto (fun n : ℕ => |Real.exp ((n : ℝ) * c) * x|) atTop (nhds 0) := by
      simpa using h.abs
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
      ((habs.eventually (isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ) < 1))).and
        ((boxi_tendsto_exp_nat_mul_atTop hc').eventually_gt_atTop (2 / |x|)))
    have h1 : |Real.exp ((N : ℝ) * c) * x| < 1 := (hN N le_rfl).1
    rw [abs_mul, abs_of_pos (Real.exp_pos _)] at h1
    have h2 : 2 < Real.exp ((N : ℝ) * c) * |x| := by
      have h3 := (hN N le_rfl).2
      rw [div_lt_iff₀ hxpos] at h3
      linarith
    linarith
  · have hconst : (fun n : ℕ => Real.exp ((n : ℝ) * c) * x) = fun _ => x := by
      funext n
      rw [← hc', mul_zero, Real.exp_zero, one_mul]
    rw [hconst] at h
    exact tendsto_nhds_unique tendsto_const_nhds h

/-! ## The main statement -/

theorem box_iInter_conjBox {U : Subgroup Work.EKLContract.SL3} (hU : Work.EKLContract.IsHoro U)
    {t : Fin 3 → ℝ}
    (hcontr : ∀ u ∈ U, Filter.Tendsto
      (fun n : ℕ => Work.EKLContract.aDiag t ^ n * u * (Work.EKLContract.aDiag t ^ n)⁻¹)
      Filter.atTop (nhds 1)) :
    (⋂ n : ℕ, Work.EKLC6Core.conjBox U (((n : ℝ)) • t)) = {1} := by
  refine Set.Subset.antisymm (fun g hg => ?_) (fun g hg => ?_)
  · -- `g` lies in every box.  The `n = 0` term is `B₁^U`, so `g ∈ B₁^U ⊆ U`; and the
    -- condition `g ∈ conjBox U (n t)` says `(aDiag t)⁻ⁿ g (aDiag t)ⁿ ∈ B₁^U`.
    have hg0 : g ∈ Box1 U := by
      have h := Set.mem_iInter.mp hg 0
      simpa using h
    have hgU : g ∈ U := hg0.1
    have hbox : ∀ n : ℕ, (aDiag t ^ n)⁻¹ * g * aDiag t ^ n ∈ Box1 U := by
      intro n
      have hn := Set.mem_iInter.mp hg n
      rw [conjBox, conjBy, Set.mem_image] at hn
      obtain ⟨h, hh, hheq⟩ := hn
      rw [← hheq, boxi_aDiag_cast_smul t n]
      convert hh using 1
      group
    -- the entries of the "inverse conjugate" are bounded by `1`
    have hbnd : ∀ n : ℕ, ∀ i j : Fin 3,
        |Real.exp ((n : ℝ) * (t j - t i)) * g i j
          - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 := by
      intro n i j
      have h := (hbox n).2 i j
      rwa [boxi_conj_pow_apply_inv] at h
    have hone_neM : ∀ i j : Fin 3, i ≠ j → (1 : Matrix (Fin 3) (Fin 3) ℝ) i j = 0 := by
      intro i j hij; exact Matrix.one_apply_ne hij
    have hone_eqM : ∀ i : Fin 3, (1 : Matrix (Fin 3) (Fin 3) ℝ) i i = 1 := by
      intro i; exact Matrix.one_apply_eq i
    have hone_ne : ∀ i j : Fin 3, i ≠ j → ((1 : SL3) i j) = 0 := by
      intro i j hij; exact Matrix.one_apply_ne hij
    have hone_eq : ∀ i : Fin 3, ((1 : SL3) i i) = 1 := by
      intro i; exact Matrix.one_apply_eq i
    -- the entries of the conjugate tend to those of the identity
    have hlim : ∀ i j : Fin 3,
        Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * (t i - t j)) * g i j)
          atTop (nhds ((1 : SL3) i j)) := by
      intro i j
      have hc : Continuous (fun x : SL3 => x i j) := by fun_prop
      have h1 : Tendsto (fun n : ℕ => (aDiag t ^ n * g * (aDiag t ^ n)⁻¹ : SL3) i j) atTop
          (nhds ((1 : SL3) i j)) := (hc.tendsto 1).comp (hcontr g hgU)
      simpa [boxi_conj_pow_apply] using h1
    have hoff : ∀ i j : Fin 3, i ≠ j → g i j = 0 := by
      intro i j hij
      rcases lt_trichotomy (t i) (t j) with hlt | heq | hgt
      · -- increasing direction: the box bound kills the entry
        refine boxi_eq_zero_of_abs_exp_le_one (c := t j - t i) (by linarith) (fun n => ?_)
        have h := hbnd n i j
        rw [hone_neM i j hij, sub_zero] at h
        exact h
      · -- equal exponents: the entry is constant along the sequence
        have h := hlim i j
        have hconst : (fun n : ℕ => Real.exp ((n : ℝ) * (t i - t j)) * g i j)
            = fun _ => g i j := by
          funext n
          rw [heq, sub_self, mul_zero, Real.exp_zero, one_mul]
        rw [hconst, hone_ne i j hij] at h
        exact tendsto_nhds_unique tendsto_const_nhds h
      · -- decreasing direction: the contraction kills the entry
        have h := hlim i j
        rw [hone_ne i j hij] at h
        exact boxi_eq_zero_of_tendsto_exp_mul (c := t i - t j) (by linarith) h
    have hdiag : ∀ i : Fin 3, g i i = 1 := by
      intro i
      have h := hlim i i
      have hconst : (fun n : ℕ => Real.exp ((n : ℝ) * (t i - t i)) * g i i) = fun _ => g i i := by
        funext n
        rw [sub_self, mul_zero, Real.exp_zero, one_mul]
      rw [hconst, hone_eq i] at h
      exact tendsto_nhds_unique tendsto_const_nhds h
    exact Set.mem_singleton_iff.mpr (ext_apply (fun i j => by
      by_cases hij : i = j
      · subst hij
        rw [hdiag i, hone_eq i]
      · rw [hoff i j hij, hone_ne i j hij]))
  · -- `1` lies in every box: `1 ∈ B₁^U` and conjugation fixes it
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    refine Set.mem_iInter.mpr (fun n => ?_)
    rw [conjBox, conjBy, Set.mem_image]
    refine ⟨1, ⟨one_mem U, ?_⟩, by simp⟩
    intro i j
    show |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1
    simp

end Work.EKLC6Core
