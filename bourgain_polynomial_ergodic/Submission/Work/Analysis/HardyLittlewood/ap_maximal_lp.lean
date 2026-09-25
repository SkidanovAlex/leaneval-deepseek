import Mathlib
import Submission.Commons.Analysis.HardyLittlewood.discrete_forward_maximal

namespace Work.Analysis.HardyLittlewood

open MeasureTheory Finset
open scoped BigOperators ENNReal

/-- The forward maximal function of a sequence on `ℕ`, as an `ℝ≥0∞`-valued function:
`fwdSup h k = sup_N |N⁻¹ ∑_{i<N} h(k+i)|`. -/
private noncomputable def fwdSup (h : ℕ → ℝ) (k : ℕ) : ℝ≥0∞ :=
  ⨆ N : ℕ, ‖(N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, h (k + i)‖ₑ

/-- The map `m ↦ (m / a, m % a)` from `ℕ` to `ℕ × Fin a` is injective. -/
private lemma injective_divMod (a : ℕ) (ha : 0 < a) :
    Function.Injective (fun m : ℕ => ((m / a, ⟨m % a, Nat.mod_lt m ha⟩) : ℕ × Fin a)) := by
  intro x y hxy
  have h1 : x / a = y / a := congrArg Prod.fst hxy
  have h2 : x % a = y % a := congrArg (fun z : ℕ × Fin a => (z.2 : ℕ)) hxy
  calc x = x % a + a * (x / a) := (Nat.mod_add_div x a).symm
    _ = y % a + a * (y / a) := by rw [h1, h2]
    _ = y := Nat.mod_add_div y a

/-- The map `(k, ρ) ↦ k * a + ρ` from `ℕ × Fin a` to `ℕ` is injective. -/
private lemma injective_mul_add (a : ℕ) (ha : 0 < a) :
    Function.Injective (fun z : ℕ × Fin a => z.1 * a + z.2.val) := by
  intro x y hxy
  change x.1 * a + x.2.val = y.1 * a + y.2.val at hxy
  have hxd : (x.1 * a + x.2.val) / a = x.1 := by
    have h : x.1 * a + x.2.val = x.2.val + a * x.1 := by ring
    rw [h, Nat.add_mul_div_left _ _ ha, Nat.div_eq_of_lt x.2.isLt, Nat.zero_add]
  have hyd : (y.1 * a + y.2.val) / a = y.1 := by
    have h : y.1 * a + y.2.val = y.2.val + a * y.1 := by ring
    rw [h, Nat.add_mul_div_left _ _ ha, Nat.div_eq_of_lt y.2.isLt, Nat.zero_add]
  have hxm : (x.1 * a + x.2.val) % a = x.2.val := by
    rw [Nat.mul_comm x.1 a, Nat.mul_add_mod, Nat.mod_eq_of_lt x.2.isLt]
  have hym : (y.1 * a + y.2.val) % a = y.2.val := by
    rw [Nat.mul_comm y.1 a, Nat.mul_add_mod, Nat.mod_eq_of_lt y.2.isLt]
  have h1 : x.1 = y.1 := by rw [← hxd, ← hyd, hxy]
  have h2 : x.2 = y.2 := by
    apply Fin.ext
    rw [← hxm, ← hym, hxy]
  exact Prod.ext h1 h2

/-- Reindexing a sum over `ℕ` as a sum over `ℕ × Fin a` along the division algorithm:
`∑'_m H m = ∑'_{(k,ρ)} H (k * a + ρ)`. -/
private lemma tsum_divMod (a : ℕ) (ha : 0 < a) (H : ℕ → ℝ≥0∞) :
    ∑' m : ℕ, H m = ∑' z : ℕ × Fin a, H (z.1 * a + z.2.val) := by
  refine le_antisymm ?_ ?_
  · calc ∑' m : ℕ, H m = ∑' m : ℕ, H ((m / a) * a + (m % a)) := by
          apply tsum_congr; intro m
          rw [Nat.mul_comm (m / a) a, Nat.div_add_mod]
      _ ≤ ∑' z : ℕ × Fin a, H (z.1 * a + z.2.val) :=
          ENNReal.tsum_comp_le_tsum_of_injective
            (f := fun m : ℕ => ((m / a, ⟨m % a, Nat.mod_lt m ha⟩) : ℕ × Fin a))
            (injective_divMod a ha) (fun z : ℕ × Fin a => H (z.1 * a + z.2.val))
  · exact ENNReal.tsum_comp_le_tsum_of_injective (injective_mul_add a ha) H

/-- **Maximal inequality for arithmetic-progression averages on `ℕ`.**  For `a ≥ 1`, `b : ℕ`
and `1 < p` the maximal function `sup_N |N⁻¹ ∑_{i<N} g (n + (a*i+b))|` of the arithmetic-progression
averages is bounded on `ℓᵖ(ℕ)`.

Route (kindly supplied by the reviewer): for `ρ = (n+b) mod a` write `n + b = ρ + a k`; the
progression starting at `n` is then exactly the consecutive block `k, k+1, …` of the subsequence
`F_ρ(m) := g (ρ + a*m)`, so the progression maximal function at `n` equals the *forward* discrete
maximal function `Commons.Analysis.HardyLittlewood.discrete_forward_maximal` of `F_ρ` at `k`.
Summing over the `a` residue classes and applying the forward maximal inequality gives the bound
with a constant depending only on `a`, `b` and `p` (uniformly, e.g. `p/(p-1)` for the forward
maximal function of each subsequence).  (A naive comparison with `fwdMaxZ` of the whole function
fails because of cancellation; do not use it.) -/
theorem ap_maximal_lp {p : ℝ} (hp : 1 < p) (a b : ℕ) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : ℕ → ℝ, (∃ s : Finset ℕ, ∀ n, n ∉ s → g n = 0) →
      ∫⁻ n : ℕ, (⨆ N : ℕ, ‖(N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, g (n + (a * i + b))‖ₑ) ^ p
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C ^ p) * ∫⁻ n : ℕ, ‖g n‖ₑ ^ p ∂MeasureTheory.Measure.count := by
  obtain ⟨C, hCpos, hC⟩ := Commons.Analysis.HardyLittlewood.discrete_forward_maximal hp
  refine ⟨C, hCpos, ?_⟩
  intro g hg
  obtain ⟨s, hs⟩ := hg
  -- the subsequences read off the `a` residue classes
  set F : Fin a → ℕ → ℝ := fun ρ m => g (ρ.val + a * m) with hF
  -- each subsequence is finitely supported
  have hFfin : ∀ ρ : Fin a, ∃ t : Finset ℕ, ∀ m, m ∉ t → F ρ m = 0 := by
    intro ρ
    refine ⟨Finset.range (s.sup id + 1), fun m hm => ?_⟩
    have hgt : s.sup id < m := by
      by_contra hcon
      exact hm (Finset.mem_range.mpr (Nat.lt_succ_of_le (not_lt.mp hcon)))
    have hnot : ρ.val + a * m ∉ s := by
      intro hmem
      have h1 : ρ.val + a * m ≤ s.sup id := Finset.le_sup (f := id) hmem
      have h2 : m ≤ a * m := Nat.le_mul_of_pos_left m ha
      omega
    rw [hF]
    exact hs (ρ.val + a * m) hnot
  -- the forward maximal inequality applied to each residue class
  have hclass : ∀ ρ : Fin a, ∑' k : ℕ, (fwdSup (F ρ) k) ^ p
      ≤ ENNReal.ofReal (C ^ p) * ∑' k : ℕ, ‖F ρ k‖ₑ ^ p := by
    intro ρ
    obtain ⟨t, ht⟩ := hFfin ρ
    have h := hC (F ρ) ⟨t, ht⟩
    rw [MeasureTheory.lintegral_count, MeasureTheory.lintegral_count] at h
    simpa only [fwdSup] using h
  -- the progression at `n` is the window at `(n+b) / a` of the subsequence `(n+b) % a`
  have hpt : ∀ m : ℕ, (⨆ N : ℕ, ‖(N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, g (m + a * i)‖ₑ) ^ p
      = (fwdSup (F ⟨m % a, Nat.mod_lt m ha⟩) (m / a)) ^ p := by
    intro m
    have hsum : ∀ N : ℕ, ∑ i ∈ Finset.range N, g (m + a * i)
        = ∑ i ∈ Finset.range N, F ⟨m % a, Nat.mod_lt m ha⟩ (m / a + i) := by
      intro N
      apply Finset.sum_congr rfl
      intro i _
      simp only [hF]
      congr 1
      rw [Nat.mul_add, ← Nat.add_assoc, Nat.mod_add_div]
    simp only [hsum, fwdSup]
  have hpt' : ∀ (k : ℕ) (ρ : Fin a),
      (⨆ N : ℕ, ‖(N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, g (k * a + ρ.val + a * i)‖ₑ) ^ p
      = (fwdSup (F ρ) k) ^ p := by
    intro k ρ
    have hsum : ∀ N : ℕ, ∑ i ∈ Finset.range N, g (k * a + ρ.val + a * i)
        = ∑ i ∈ Finset.range N, F ρ (k + i) := by
      intro N
      apply Finset.sum_congr rfl
      intro i _
      simp only [hF]
      congr 1
      ring
    simp only [hsum, fwdSup]
  -- reindexing the sum over the residue classes
  have hreindex : ∑' m : ℕ, (⨆ N : ℕ, ‖(N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, g (m + a * i)‖ₑ) ^ p
      = ∑' z : ℕ × Fin a, (fwdSup (F z.2) z.1) ^ p := by
    rw [tsum_divMod a ha
      (fun m : ℕ => (⨆ N : ℕ, ‖(N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, g (m + a * i)‖ₑ) ^ p)]
    apply tsum_congr
    intro z
    rw [hpt' z.1 z.2]
  -- reindexing the target `ℓᵖ` norm
  have htarget : ∑' m : ℕ, ‖g m‖ₑ ^ p = ∑' ρ : Fin a, ∑' k : ℕ, ‖F ρ k‖ₑ ^ p := by
    rw [tsum_divMod a ha (fun m : ℕ => ‖g m‖ₑ ^ p)]
    rw [show (∑' z : ℕ × Fin a, ‖g (z.1 * a + z.2.val)‖ₑ ^ p)
        = ∑' z : ℕ × Fin a, ‖F z.2 z.1‖ₑ ^ p from by
          apply tsum_congr; intro z
          congr 1
          congr 1
          simp only [hF]
          congr 1
          ring]
    rw [ENNReal.tsum_prod (f := fun (k : ℕ) (ρ : Fin a) => ‖F ρ k‖ₑ ^ p), ENNReal.tsum_comm]
  calc ∫⁻ n : ℕ, (⨆ N : ℕ, ‖(N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, g (n + (a * i + b))‖ₑ) ^ p
        ∂MeasureTheory.Measure.count
      = ∑' n : ℕ, (⨆ N : ℕ, ‖(N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, g ((n + b) + a * i)‖ₑ) ^ p := by
        rw [MeasureTheory.lintegral_count]
        apply tsum_congr
        intro n
        have hsum : ∀ N : ℕ, ∑ i ∈ Finset.range N, g (n + (a * i + b))
            = ∑ i ∈ Finset.range N, g ((n + b) + a * i) := by
          intro N
          apply Finset.sum_congr rfl
          intro i _
          congr 1
          ring
        simp only [hsum]
    _ ≤ ∑' m : ℕ, (⨆ N : ℕ, ‖(N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, g (m + a * i)‖ₑ) ^ p :=
        ENNReal.tsum_comp_le_tsum_of_injective (f := fun n : ℕ => n + b)
          (fun x _ hxy => Nat.add_right_cancel hxy)
          (fun m : ℕ => (⨆ N : ℕ, ‖(N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, g (m + a * i)‖ₑ) ^ p)
    _ = ∑' z : ℕ × Fin a, (fwdSup (F z.2) z.1) ^ p := hreindex
    _ = ∑' ρ : Fin a, ∑' k : ℕ, (fwdSup (F ρ) k) ^ p := by
        rw [ENNReal.tsum_prod (f := fun (k : ℕ) (ρ : Fin a) => (fwdSup (F ρ) k) ^ p),
          ENNReal.tsum_comm]
    _ ≤ ∑' ρ : Fin a, ENNReal.ofReal (C ^ p) * ∑' k : ℕ, ‖F ρ k‖ₑ ^ p :=
        ENNReal.tsum_le_tsum hclass
    _ = ENNReal.ofReal (C ^ p) * ∑' ρ : Fin a, ∑' k : ℕ, ‖F ρ k‖ₑ ^ p :=
        ENNReal.tsum_mul_left
    _ = ENNReal.ofReal (C ^ p) * ∑' m : ℕ, ‖g m‖ₑ ^ p := by rw [htarget]
    _ = ENNReal.ofReal (C ^ p) * ∫⁻ n : ℕ, ‖g n‖ₑ ^ p ∂MeasureTheory.Measure.count := by
        rw [MeasureTheory.lintegral_count]

end Work.Analysis.HardyLittlewood
