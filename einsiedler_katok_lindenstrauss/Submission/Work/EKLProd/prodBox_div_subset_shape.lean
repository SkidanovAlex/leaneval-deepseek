import Mathlib
import Submission.Work.EKLProd.ProdFlowerDefs
import Submission.Work.EKLProd.ProdPlaqueDefs
import Submission.Work.EKLComp.LeafDefs
import Submission.Work.EKLProd.aDiag_nsmul
import Submission.Work.EKLComp.aDiag_pow_entry
import Submission.Work.EKLProd.inv_entries_bound
import Submission.Work.EKLProd.mul_inv_mem_V_of_hT_bounds

namespace Work.EKLProd

open Work.EKLContract Filter

/-! ## The `T`-coordinate of a bounded element of `H`

The two elementary lemmas below (`hT_entry_block_part` and the entrywise bookkeeping of the
delegated `Work.EKLProd.mul_inv_mem_V_of_hT_bounds`) are the two quantitative inputs of
`prodBox_div_subset_shape`. -/



private lemma tendsto_exp_nat_mul_zero {c : ℝ} (hc : c < 0) :
    Tendsto (fun k : ℕ => Real.exp ((k : ℝ) * c)) atTop (nhds 0) := by
  have hlt : Real.exp c < 1 := Real.exp_lt_one_iff.mpr hc
  have hpos : 0 ≤ Real.exp c := (Real.exp_pos c).le
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one hpos hlt
  have heq : (fun k : ℕ => Real.exp ((k : ℝ) * c)) = fun k : ℕ => Real.exp c ^ k := by
    funext k; rw [Real.exp_nat_mul]
  rw [heq]; exact h

private lemma conj_mul_eq {a g u : SL3} (h : a * g = g * a) :
    a * (g * u) * a⁻¹ = g * (a * u * a⁻¹) := by
  rw [← mul_assoc a g u, h, mul_assoc g a u, mul_assoc g (a * u) a⁻¹]

/-- **The `T`-coordinate of an element of `H` is its block-diagonal part.**

With `H = T · U`, `T` centralised by `aDiag s` and `U` contracted by it, the chosen `T`-part
`hT T U t` of `t ∈ H` is the part of `t` on the blocks of equal `s`-value: its `(i,j)` entry is
`t i j` if `s i = s j` and `0` otherwise.  For `t` in the closed unit ball `Ucl H 1` the entries of
`hT T U t` are therefore bounded by `2`, and those of `hT T U t - t` by `1`.  (This is proved in
full here; `Submission/Work/EKLProd/hT_block_part.lean` is the delegated version of the same
statement.) -/
theorem hT_entry_block_part {H T U : Subgroup SL3}
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u) (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (s : Fin 3 → ℝ)
    (hcent : ∀ g ∈ T, aDiag s * g = g * aDiag s)
    (hcontr : ∀ u ∈ U, Tendsto
      (fun k : ℕ => aDiag s ^ k * u * (aDiag s ^ k)⁻¹) atTop (nhds 1))
    {t : SL3} (ht : t ∈ Work.EKLComp.Ucl H 1) :
    (∀ i j : Fin 3, (hT T U t) i j = if s i = s j then t i j else 0) ∧
    (∀ i j : Fin 3, |(hT T U t) i j| ≤ 2 ∧
      |(hT T U t) i j - t i j| ≤ 1) := by
  classical
  obtain ⟨g, hgT, u, huU, hgu⟩ := hcop t ht.1
  have hdec : hT T U t * hU T U t = t := hT_mul_hU ⟨g, hgT, u, huU, hgu⟩
  have hTt : hT T U t = g :=
    hT_hU_unique hdisj (hT_mem ⟨g, hgT, u, huU, hgu⟩) (hU_mem ⟨g, hgT, u, huU, hgu⟩)
      hgT huU (by rw [hdec, hgu])
  have hcent_pow : ∀ k : ℕ, aDiag s ^ k * g = g * aDiag s ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ n ih =>
      rw [pow_succ]
      calc aDiag s ^ n * aDiag s * g = aDiag s ^ n * (aDiag s * g) := by rw [mul_assoc]
        _ = aDiag s ^ n * (g * aDiag s) := by rw [hcent g hgT]
        _ = aDiag s ^ n * g * aDiag s := by rw [mul_assoc]
        _ = g * aDiag s ^ n * aDiag s := by rw [ih]
        _ = g * (aDiag s ^ n * aDiag s) := by rw [mul_assoc]
  have hseq : Tendsto (fun k : ℕ => aDiag s ^ k * t * (aDiag s ^ k)⁻¹) atTop (nhds g) := by
    have hcongr : (fun k : ℕ => aDiag s ^ k * t * (aDiag s ^ k)⁻¹)
        = fun k : ℕ => g * (aDiag s ^ k * u * (aDiag s ^ k)⁻¹) := by
      funext k
      rw [hgu, conj_mul_eq (hcent_pow k)]
    rw [hcongr]
    simpa using (hcontr u huU).const_mul g
  have hentry : ∀ i j : Fin 3,
      Tendsto (fun k : ℕ => Real.exp ((k : ℝ) * (s i - s j)) * t i j) atTop (nhds (g i j)) := by
    intro i j
    have hcont : Continuous (fun A : SL3 => A i j) :=
      (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
    have h2 : Tendsto (fun k : ℕ => (aDiag s ^ k * t * (aDiag s ^ k)⁻¹) i j)
        atTop (nhds (g i j)) := (hcont.tendsto g).comp hseq
    refine h2.congr' ?_
    filter_upwards with k
    rw [← toMat_apply, Work.EKLComp.aDiag_pow_entry, toMat_apply]
  have hval : ∀ i j : Fin 3, g i j = if s i = s j then t i j else 0 := by
    intro i j
    by_cases hij : s i = s j
    · rw [if_pos hij]
      have hconst : Tendsto (fun k : ℕ => Real.exp ((k : ℝ) * (s i - s j)) * t i j)
          atTop (nhds (t i j)) := by
        have he : (fun k : ℕ => Real.exp ((k : ℝ) * (s i - s j)) * t i j)
            = fun _ : ℕ => t i j := by
          funext k; rw [hij, sub_self, mul_zero, Real.exp_zero, one_mul]
        rw [he]; exact tendsto_const_nhds
      exact tendsto_nhds_unique (hentry i j) hconst
    · rw [if_neg hij]
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · have hc : s i - s j < 0 := sub_neg.mpr hlt
        have h0 : Tendsto (fun k : ℕ => Real.exp ((k : ℝ) * (s i - s j)) * t i j)
            atTop (nhds 0) := by
          have h := (tendsto_exp_nat_mul_zero hc).mul_const (t i j)
          simpa using h
        exact tendsto_nhds_unique (hentry i j) h0
      · have hc : -(s i - s j) < 0 := by linarith
        have hconst : Tendsto (fun k : ℕ => Real.exp ((k : ℝ) * (s i - s j)) * t i j
            * Real.exp ((k : ℝ) * (-(s i - s j)))) atTop (nhds (t i j)) := by
          have he : (fun k : ℕ => Real.exp ((k : ℝ) * (s i - s j)) * t i j
              * Real.exp ((k : ℝ) * (-(s i - s j)))) = fun _ : ℕ => t i j := by
            funext k
            have hz : (k : ℝ) * (s i - s j) + (k : ℝ) * (-(s i - s j)) = 0 := by ring
            calc Real.exp ((k : ℝ) * (s i - s j)) * t i j * Real.exp ((k : ℝ) * (-(s i - s j)))
                = (Real.exp ((k : ℝ) * (s i - s j))
                    * Real.exp ((k : ℝ) * (-(s i - s j)))) * t i j := by ring
              _ = Real.exp ((k : ℝ) * (s i - s j) + (k : ℝ) * (-(s i - s j))) * t i j := by
                    rw [Real.exp_add]
              _ = t i j := by rw [hz, Real.exp_zero, one_mul]
          rw [he]; exact tendsto_const_nhds
        have hlim : Tendsto (fun k : ℕ => Real.exp ((k : ℝ) * (s i - s j)) * t i j
            * Real.exp ((k : ℝ) * (-(s i - s j)))) atTop (nhds (g i j * 0)) :=
          (hentry i j).mul (tendsto_exp_nat_mul_zero hc)
        rw [mul_zero] at hlim
        have htij0 : t i j = 0 := tendsto_nhds_unique hconst hlim
        have he' := hentry i j
        simp only [htij0, mul_zero] at he'
        exact tendsto_nhds_unique he' tendsto_const_nhds
  refine ⟨fun i j => by rw [hTt]; exact hval i j, fun i j => ?_⟩
  rw [hTt]
  constructor
  · by_cases hij : s i = s j
    · rw [hval i j, if_pos hij]
      have hδ : |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 := by
        rw [Matrix.one_apply]; split <;> simp
      have h1 := ht.2 i j
      have h2 : |t i j| ≤ |t i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|
          + |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| := by
        calc |t i j| = |(t i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j)
              + (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| := by rw [sub_add_cancel]
          _ ≤ _ := abs_add_le _ _
      linarith [h1, hδ, h2]
    · rw [hval i j, if_neg hij]; simp
  · by_cases hij : s i = s j
    · rw [hval i j, if_pos hij]; simp
    · rw [hval i j, if_neg hij]
      have hij' : i ≠ j := fun h => hij (by rw [h])
      have hδ : (1 : Matrix (Fin 3) (Fin 3) ℝ) i j = 0 := by
        rw [Matrix.one_apply, if_neg hij']
      have h1 := ht.2 i j
      rw [hδ, sub_zero] at h1
      simpa using h1



/-- **The shapes of a product-box flower grow with the radius, uniformly on the base.**

If `x` lies in the base of the `n`-th flower (`x ∈ hf.G n` implies `x ∈ hf.Z n`) and its plaque
coordinate is the inverse of an element of the closed unit ball of `H` (`co n x = t⁻¹`,
`t ∈ Ucl H 1`), then the `H`-shape at `x` contains a product box whose radius is proportional to
`hf.R` — so the shapes exhaust `H` as `hf.R → ∞`.  This is what turns the local product structure
of the flowers into a global statement.

Route (corrected after a referee objection: `t ∈ Ucl H 1` is a *general* element of `H`, so
`t · u' · t⁻¹ ∈ U` is **false**; one must first split `t` using the contraction/centralisation
data `hcent`, `hcontr`).

1. `shape (mH n) H x = {g | g ∈ H ∧ g * co n x ∈ prodBox T U hf.R}` (`hf.shapeH`), and
   `prodBox T U (hf.R/C) ⊆ H`, so it suffices to produce, for `g = t' * u'` with
   `t' ∈ V (hf.R/C) ∩ T`, `u' ∈ V (hf.R/C) ∩ U`, a decomposition of `g * t⁻¹` into a `T`-factor
   and a `U`-factor both inside `V hf.R`.
2. **Coordinate bounds.** `hT T U t` has entries `≤ 2` and `hU T U t` has entries `≤ 50`, because
   `hT T U t = lim_k aDiag t₀ ^ k * t * (aDiag t₀ ^ k)⁻¹` (this is the argument of
   `Work.EKLRelProduct.measurable_coord_of_contracting`: `hcent` makes the `T`-part invariant,
   `hcontr` makes the `U`-part tend to `1`), the entries of the iterates are
   `e^{k(t₀ᵢ-t₀ⱼ)} t_{ij}` with `|t_{ij}| ≤ 2`, and `hU T U t = (hT T U t)⁻¹ * t`.
3. Writing `t = τ * υ` (`hT_mul_hU`) with `τ := hT T U t`, `υ := hU T U t`, one has
   `g * t⁻¹ = (t' * τ⁻¹) * (τ * (u' * υ⁻¹) * τ⁻¹)` (`hnorm` gives `τ * · * τ⁻¹ ∈ U`), the first
   factor is in `T` and the second in `U`, and both have entries `< hf.R` for `hf.R ≥ 5000`
   using `Work.EKLProd.abs_mul_entries_le` and the Cramer bound for `τ⁻¹` (entries `≤ 8`). -/
theorem prodBox_div_subset_shape {H T U : Subgroup Work.EKLContract.SL3} (hTH : T ≤ H) (hUH : U ≤ H) (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U) (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u) (hdisj : ∀ g ∈ T, g ∈ U → g = 1) (t₀ : Fin 3 → ℝ) (hcent : ∀ g ∈ T, Work.EKLContract.aDiag t₀ * g = g * Work.EKLContract.aDiag t₀) (hcontr : ∀ u ∈ U, Filter.Tendsto (fun k : ℕ => Work.EKLContract.aDiag t₀ ^ k * u * (Work.EKLContract.aDiag t₀ ^ k)⁻¹) Filter.atTop (nhds 1)) {μ : MeasureTheory.Measure Work.EKLContract.X3} (hf : Work.EKLProd.ProdFlowerFam H T U μ) (hR : 5000 ≤ hf.R) (n : ℕ) {x : Work.EKLContract.X3} (hx : x ∈ hf.Z n) {t : Work.EKLContract.SL3} (ht : t ∈ Work.EKLComp.Ucl H 1) (hco : hf.co n x = t⁻¹) : ∃ C : ℝ, 0 < C ∧ Work.EKLProd.prodBox T U (hf.R / C) ⊆ Work.EKLContract.shape (hf.mH n) H x := by
  classical
  -- entry bounds on the `T`-coordinate `τ = hT T U t` of the plaque coordinate `t⁻¹`
  have hτb : ∀ i j : Fin 3, |(Work.EKLProd.hT T U t) i j| ≤ 2 ∧
      |(Work.EKLProd.hT T U t) i j - t i j| ≤ 1 :=
    (hT_entry_block_part hcop hdisj t₀ hcent hcontr ht).2
  -- the two arithmetic side conditions for the factor bounds, at `C = 10⁹`
  have hineqA : 3 * (8 * (hf.R / (10 : ℝ) ^ 9)) + 9 < hf.R := by
    have h10 : (10 : ℝ) ^ 9 = 1000000000 := by norm_num
    rw [h10]; linarith
  have hineqB : 3 * (1153 * (48 * (hf.R / (10 : ℝ) ^ 9))) + 1152 < hf.R := by
    have h10 : (10 : ℝ) ^ 9 = 1000000000 := by norm_num
    rw [h10]; linarith
  refine ⟨(10 : ℝ) ^ 9, by positivity, ?_⟩
  intro g hg
  obtain ⟨t', ht', u', hu', rfl⟩ := hg
  rw [hf.shapeH n x hx]
  refine ⟨Work.EKLProd.prodBox_subset_H hTH hUH ⟨t', ht', u', hu', rfl⟩, ?_⟩
  rw [hco]
  -- the two factors of `(t' * u') * t⁻¹`
  obtain ⟨hA, hB⟩ :=
    Work.EKLProd.mul_inv_mem_V_of_hT_bounds hcop ⟨t, ht⟩ hineqA hineqB ht'.1 hu'.1 hτb
  obtain ⟨gd, hgdT, ud, hudU, hgdud⟩ := hcop t ht.1
  have hτT₀ : Work.EKLProd.hT T U t ∈ T := Work.EKLProd.hT_mem ⟨gd, hgdT, ud, hudU, hgdud⟩
  have hυU₀ : Work.EKLProd.hU T U t ∈ U := Work.EKLProd.hU_mem ⟨gd, hgdT, ud, hudU, hgdud⟩
  have hdec₀ : Work.EKLProd.hT T U t * Work.EKLProd.hU T U t = t :=
    Work.EKLProd.hT_mul_hU ⟨gd, hgdT, ud, hudU, hgdud⟩
  let τ : Work.EKLContract.SL3 := Work.EKLProd.hT T U t
  let υ : Work.EKLContract.SL3 := Work.EKLProd.hU T U t
  have hdec : τ * υ = t := hdec₀
  have hτT : τ ∈ T := hτT₀
  have hυU : υ ∈ U := hυU₀
  -- the second factor is the `hnorm`-conjugate `τ * (u' * υ⁻¹) * τ⁻¹`
  have hBmem : τ * u' * t⁻¹ ∈ U := by
    have htinv : t⁻¹ = υ⁻¹ * τ⁻¹ := by rw [← hdec, mul_inv_rev]
    have h1 : τ * u' * t⁻¹ = τ * (u' * υ⁻¹) * τ⁻¹ := by rw [htinv]; group
    rw [h1]
    exact hnorm τ hτT (u' * υ⁻¹) (U.mul_mem hu'.2 (U.inv_mem hυU))
  refine ⟨t' * τ⁻¹, ⟨hA, T.mul_mem ht'.2 (T.inv_mem hτT)⟩,
    τ * u' * t⁻¹, ⟨hB, hBmem⟩, ?_⟩
  group

end Work.EKLProd
