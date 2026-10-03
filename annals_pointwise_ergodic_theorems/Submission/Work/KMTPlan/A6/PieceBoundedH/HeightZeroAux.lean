import Mathlib
import Submission.Work.KMTAreas.A7.LoHelpers
import Submission.Work.KMTAreas.A7.LoErrAux
import Submission.Work.KMTAreas.A7.SmallExcBound
import Submission.Work.KMTPlan.A6.variationalNorm_prefix_zero_le

/-!
# Auxiliary lemmas for the height-zero bound (`Work.KMTPlan.A6.PieceBoundedH.heightZeroBound`)

Three ingredients, all independent of the §6--§8 machinery:

* `variationalNorm_indicator_upper_le` — the `r`-variational norm of a sequence restricted to an
  upper set of indices is at most twice the variational norm of the sequence;
* monotonicity of the guard `loGuard` in the parameter `ρ` and in the index `n` (the scale
  sequence being increasing) — so that cutting the family down to a *smaller* `ρ` restricts it to
  an upper set of indices;
* independence of the height-`0` pieces of `ρ` (`iwArithFreqs ρ 0 = {0}`), giving the pointwise
  restriction identity `mainPartTuple_heightZero_restrict`, and the absorption of the §6 loss
  weight at bounded height (`lossWeight_le_const`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6.PieceBoundedH

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems

/-! ## Restricting a sequence to an upper set of indices -/

/-- **The variational norm of a sequence restricted to an upper set.**  If `E ⊆ ℕ` is an upper set
(`n ∈ E → n ≤ m → m ∈ E`), then multiplying a sequence by the indicator of `E` increases its
`r`-variational norm by at most a factor `2`.

The proof puts `E = {n : m₀ ≤ n}` (`m₀` the least element of `E`) and applies the prefix-zero
padding estimate `variationalNorm_prefix_zero_le` to the shifted sequence `k ↦ u (k + m₀)`
together with the reindexing bound `variationalNorm_comp_mono_le`. -/
theorem variationalNorm_indicator_upper_le {r : NNReal} (hr : 1 ≤ r) (u : ℕ → ℂ) (E : Set ℕ)
    (hE : ∀ n m : ℕ, n ∈ E → n ≤ m → m ∈ E) :
    variationalNorm r (E.indicator u) ≤ 2 * variationalNorm r u := by
  classical
  have hfun : E.indicator u = fun n : ℕ => if n ∈ E then u n else 0 := by
    funext n
    simp only [Set.indicator_apply]
  rw [hfun]
  by_cases hne : E.Nonempty
  · set m₀ : ℕ := Nat.find hne with hm₀def
    have hm₀E : m₀ ∈ E := Nat.find_spec hne
    have hiff : ∀ n : ℕ, n ∈ E ↔ m₀ ≤ n := by
      intro n
      constructor
      · intro hn
        exact Nat.find_min' hne hn
      · intro hn
        exact hE m₀ n hm₀E hn
    have hcut : (fun n : ℕ => if n ∈ E then u n else 0)
        = fun n : ℕ => if n < m₀ then 0 else u n := by
      funext n
      rw [hiff n]
      by_cases h : n < m₀
      · rw [if_neg (by omega), if_pos h]
      · rw [if_pos (by omega), if_neg h]
    rw [hcut]
    have hpad := variationalNorm_prefix_zero_le r hr (fun k : ℕ => u (k + m₀)) m₀
    have hshift : (fun n : ℕ => if n < m₀ then (0 : ℂ) else (fun k : ℕ => u (k + m₀)) (n - m₀))
        = fun n : ℕ => if n < m₀ then 0 else u n := by
      funext n
      by_cases h : n < m₀
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h]
        show u (n - m₀ + m₀) = u n
        rw [Nat.sub_add_cancel (by omega : m₀ ≤ n)]
    rw [hshift] at hpad
    have hle : variationalNorm r (fun k : ℕ => u (k + m₀)) ≤ variationalNorm r u :=
      Work.KMTAreas.A7.variationalNorm_comp_mono_le u
        (monotone_nat_of_le_succ fun k => Nat.add_le_add_right (Nat.le_succ k) m₀)
    rw [two_mul] at hpad ⊢
    exact hpad.trans (add_le_add hle hle)
  · have hzero : (fun n : ℕ => if n ∈ E then u n else 0) = (0 : ℂ) • u := by
      funext n
      have hn : n ∉ E := fun hn => hne ⟨n, hn⟩
      rw [if_neg hn]
      simp
    rw [hzero, Submission.PointwiseErgodicTheorems.variationalNorm_smul hr]
    simp

/-! ## Monotonicity of the guard -/

/-- A `Λ`-lacunary sequence with `Λ > 1` and `a n ≥ 1` is increasing. -/
theorem monotone_of_lacunary' {Λ : NNReal} (hΛ : 1 < Λ) {a : ℕ → NNReal}
    (ha : Lacunary Λ a) (ha1 : ∀ m, 1 ≤ a m) : Monotone a := by
  refine monotone_nat_of_le_succ fun n => ?_
  have hpos : (0 : NNReal) < a n := lt_of_lt_of_le zero_lt_one (ha1 n)
  have h2 : Λ < a (n + 1) / a n := ha n
  rw [lt_div_iff₀ hpos] at h2
  calc a n ≤ Λ * a n := le_mul_of_one_le_left (le_of_lt hpos) (le_of_lt hΛ)
    _ ≤ a (n + 1) := le_of_lt h2

/-- `splitCut ρ L = 2 ^ (2 ^ (uScale ρ L))` is monotone in `ρ`. -/
theorem splitCut_mono_rho {ρ ρ' : ℝ} (h : ρ ≤ ρ') (L : ℕ) :
    Work.KMTAreas.A7.splitCut ρ L ≤ Work.KMTAreas.A7.splitCut ρ' L := by
  rw [Work.KMTAreas.A7.splitCut, Work.KMTAreas.A7.splitCut]
  exact Nat.pow_le_pow_right (by norm_num)
    (Nat.pow_le_pow_right (by norm_num) (Work.KMTAreas.A7.uScale_mono_rho L h))

/-- The main regime is monotone in `ρ` (larger `ρ` gives a stronger condition). -/
theorem mainRegime_le_of_rho_le {ρ ρ' : ℝ} (h : ρ ≤ ρ') {k₁ k₂ N : ℕ}
    (hreg : Work.KMTAreas.A7.mainRegime ρ' k₁ k₂ N) :
    Work.KMTAreas.A7.mainRegime ρ k₁ k₂ N := by
  obtain ⟨h1, h2⟩ := hreg
  have hu : Work.KMTAreas.A7.uScale ρ (max k₁ k₂) ≤ Work.KMTAreas.A7.uScale ρ' (max k₁ k₂) :=
    Work.KMTAreas.A7.uScale_mono_rho (max k₁ k₂) h
  refine ⟨?_, ?_⟩
  · exact (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hu) k₁).trans h1
  · exact (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hu) k₂).trans h2

/-- The index set `I^{l,k₁,k₂}` is monotone in the scale. -/
theorem inIndexSet_mono_scale {C₀ : ℕ} {l : ℤ} {k₁ k₂ : ℤ} {N M : ℕ} (hNM : N ≤ M)
    (h : Work.Analysis.EndVar.inIndexSet C₀ l k₁ k₂ N) :
    Work.Analysis.EndVar.inIndexSet C₀ l k₁ k₂ M := by
  obtain ⟨h1, h2, h3⟩ := h
  have hh : (Work.Analysis.EndVar.heightScale C₀ N : ℤ)
      ≤ (Work.Analysis.EndVar.heightScale C₀ M : ℤ) := by
    exact_mod_cast Work.Analysis.EndVar.heightScale_mono C₀ hNM
  exact ⟨le_trans h1 hh, le_trans h2 hh, le_trans h3 hh⟩

/-- The guard `loGuard` is monotone in `ρ` (larger `ρ` gives a stronger guard). -/
theorem loGuard_le_of_rho_le {ρ ρ' : ℝ} (h : ρ ≤ ρ') {C₀ : ℕ} {a : ℕ → NNReal}
    {l₁ l₂ k₁ k₂ n : ℕ} (hg : Work.KMTAreas.A7.loGuard ρ' C₀ a l₁ l₂ k₁ k₂ n) :
    Work.KMTAreas.A7.loGuard ρ C₀ a l₁ l₂ k₁ k₂ n := by
  obtain ⟨hin, hcut, hreg⟩ := hg
  exact ⟨hin, lt_of_le_of_lt (splitCut_mono_rho h _) hcut,
    mainRegime_le_of_rho_le h hreg⟩

/-- The guard `loGuard` is monotone in the index (the scale sequence is increasing). -/
theorem loGuard_mono_index {Λ : NNReal} (hΛ : 1 < Λ) {a : ℕ → NNReal}
    (ha : Lacunary Λ a) (ha1 : ∀ m, 1 ≤ a m) {ρ : ℝ} {C₀ : ℕ} {l₁ l₂ k₁ k₂ n m : ℕ}
    (hnm : n ≤ m) (hg : Work.KMTAreas.A7.loGuard ρ C₀ a l₁ l₂ k₁ k₂ n) :
    Work.KMTAreas.A7.loGuard ρ C₀ a l₁ l₂ k₁ k₂ m := by
  have hamon : Monotone a := monotone_of_lacunary' hΛ ha ha1
  have hN : Nat.floor (a n) ≤ Nat.floor (a m) := Nat.floor_mono (hamon hnm)
  obtain ⟨hin, hcut, hreg⟩ := hg
  have hlog : (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat
      ≤ (Work.Analysis.EndVar.logN (Nat.floor (a m))).toNat := by
    simp only [Work.Analysis.EndVar.logN, Int.toNat_natCast]
    exact Nat.log_mono_right (max_le_max hN le_rfl)
  exact ⟨inIndexSet_mono_scale hN hin, lt_of_lt_of_le hcut hN,
    ⟨le_trans hreg.1 hlog, le_trans hreg.2 hlog⟩⟩

/-! ## The pieces at height zero are independent of `ρ` -/

/-- At arithmetic height `0` the IW projection is independent of `ρ`
(`iwArithFreqs ρ 0 = {0}` for every `ρ`). -/
theorem kmtProj_height_zero_eq (ρ ρ' : ℝ) (k : ℤ) (f : ℤ → ℂ) :
    Work.KMTContract.kmtProj ρ 0 k f = Work.KMTContract.kmtProj ρ' 0 k f := by
  simp only [Work.KMTContract.kmtProj, Work.KMTAreas.A7.iwArithFreqs_zero]

/-- `piExact` at height `0` is independent of `ρ`. -/
theorem piExact_height_zero_eq (ρ ρ' : ℝ) (k : ℤ) (f : ℤ → ℂ) :
    Work.Analysis.EndVar.piExact (Work.KMTContract.kmtPj ρ) 0 k f
      = Work.Analysis.EndVar.piExact (Work.KMTContract.kmtPj ρ') 0 k f := by
  have h : ∀ j : ℤ, Work.KMTContract.kmtProj ρ 0 j f = Work.KMTContract.kmtProj ρ' 0 j f :=
    fun j => kmtProj_height_zero_eq ρ ρ' j f
  simp only [Work.Analysis.EndVar.piExact, if_pos rfl, Work.KMTContract.kmtPj_proj, h]

/-- `Fpiece` at the two vanishing heights is independent of `ρ`. -/
theorem Fpiece_height_zero_eq (ρ ρ' : ℝ) (k₁ : ℕ) (N : ℕ) (f : ℤ → ℂ) :
    Work.Analysis.EndVar.Fpiece (Work.KMTContract.kmtPj ρ) 0 0 (k₁ : ℤ) N f
      = Work.Analysis.EndVar.Fpiece (Work.KMTContract.kmtPj ρ') 0 0 (k₁ : ℤ) N f := by
  have h : ∀ j : ℤ, Work.Analysis.EndVar.piExact (Work.KMTContract.kmtPj ρ) 0 j f
      = Work.Analysis.EndVar.piExact (Work.KMTContract.kmtPj ρ') 0 j f :=
    fun j => piExact_height_zero_eq ρ ρ' j f
  simp only [Work.Analysis.EndVar.Fpiece, Work.Analysis.EndVar.piece, h]

/-- `Gpiece` at the two vanishing heights is independent of `ρ`. -/
theorem Gpiece_height_zero_eq (ρ ρ' : ℝ) (d : ℕ) (k₂ : ℕ) (N : ℕ) (g : ℤ → ℂ) :
    Work.Analysis.EndVar.Gpiece (Work.KMTContract.kmtPj ρ) (d : ℤ) 0 0 (k₂ : ℤ) N g
      = Work.Analysis.EndVar.Gpiece (Work.KMTContract.kmtPj ρ') (d : ℤ) 0 0 (k₂ : ℤ) N g := by
  have h : ∀ j : ℤ, Work.Analysis.EndVar.piExact (Work.KMTContract.kmtPj ρ) 0 j g
      = Work.Analysis.EndVar.piExact (Work.KMTContract.kmtPj ρ') 0 j g :=
    fun j => piExact_height_zero_eq ρ ρ' j g
  simp only [Work.Analysis.EndVar.Gpiece, Work.Analysis.EndVar.piece, h]

/-- **The §5 column at the two vanishing heights is independent of `ρ`**: with `l₁ = l₂ = 0` the
pieces only involve the height-`0` projection. -/
theorem varpPiece_height_zero_eq (ρ ρ' : ℝ) (P : Polynomial ℤ) (d : ℕ) (N : NNReal)
    (f g : ℤ → ℂ) (k₁ k₂ : ℕ) :
    Work.Analysis.EndVar.varpPiece (Work.KMTContract.kmtPj ρ) P d N f g 0 0 k₁ k₂
      = Work.Analysis.EndVar.varpPiece (Work.KMTContract.kmtPj ρ') P d N f g 0 0 k₁ k₂ := by
  rw [Work.Analysis.EndVar.varpPiece, Work.Analysis.EndVar.varpPiece,
    Fpiece_height_zero_eq ρ ρ' k₁ (Nat.floor N) f,
    Gpiece_height_zero_eq ρ ρ' d k₂ (Nat.floor N) g]

/-- **The pointwise restriction identity.**  For `ρ ≤ ρ'` the column at `(0,0)` and the *larger*
parameter `ρ'` (whose guard is the harder one) is the column at `ρ` multiplied by the indicator of
the guard `loGuard ρ'`. -/
theorem mainPartTuple_heightZero_restrict {ρ ρ' : ℝ} (h : ρ ≤ ρ') (P : Polynomial ℤ) (C₀ : ℕ)
    (a : ℕ → NNReal) (f g : ℤ → ℂ) (k₁ k₂ n : ℕ) (x : ℤ) :
    Work.KMTAreas.A7.mainPartTuple ρ' P C₀ a f g 0 0 k₁ k₂ n x
      = if Work.KMTAreas.A7.loGuard ρ' C₀ a 0 0 k₁ k₂ n then
          Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g 0 0 k₁ k₂ n x else 0 := by
  rw [Work.KMTAreas.A7.mainPartTuple_apply, Work.KMTAreas.A7.mainPartTuple_apply]
  by_cases hg : Work.KMTAreas.A7.loGuard ρ' C₀ a 0 0 k₁ k₂ n
  · have hg' : Work.KMTAreas.A7.loGuard ρ C₀ a 0 0 k₁ k₂ n :=
      @loGuard_le_of_rho_le ρ ρ' h C₀ a 0 0 k₁ k₂ n hg
    simp only [if_pos hg, if_pos hg']
    exact congrFun (varpPiece_height_zero_eq ρ' ρ P P.natDegree (a n) f g k₁ k₂) x
  · rw [if_neg hg, if_neg hg]

/-! ## The §6 loss weight at bounded height -/

/-- `lmaxR l₁ l₂ k₁ k₂ = lcL l₁ l₂ k₁ k₂`. -/
theorem lmaxR_eq_lcL' (l₁ l₂ k₁ k₂ : ℕ) :
    Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂
      = ((Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ : ℕ) : ℝ) := by
  rw [Work.KMTAreas.A7.lmaxR, ← Work.KMTPlan.A6.lcL_eq]
  simp

/-- **The §6 loss weight is a constant on the bounded-height range.** -/
theorem lossWeight_le_const {c ρ : ℝ} (hc : 0 ≤ c) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {l₁ l₂ k₁ k₂ B : ℕ} (hB : Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ ≤ B) :
    Work.KMTAreas.A7.lossWeight c ρ l₁ l₂ k₁ k₂
      ≤ (1 + (B : ℝ)) ^ c * (2 : ℝ) ^ (c * (B : ℝ)) := by
  have hL : Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ ≤ (B : ℝ) := by
    rw [lmaxR_eq_lcL']
    exact_mod_cast hB
  have hLnn : (0 : ℝ) ≤ Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ := by
    rw [lmaxR_eq_lcL']; positivity
  have h1 : (1 + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) ^ c ≤ (1 + (B : ℝ)) ^ c :=
    Real.rpow_le_rpow (by linarith) (by linarith) hc
  have hstep : ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ ≤ (B : ℝ) := by
    have hle : ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂
        ≤ 1 * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ :=
      mul_le_mul_of_nonneg_right hρ1 hLnn
    rw [one_mul] at hle
    exact hle.trans hL
  have h2 : (2 : ℝ) ^ (c * ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂)
      ≤ (2 : ℝ) ^ (c * (B : ℝ)) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    calc c * ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂
        = c * (ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) := by ring
      _ ≤ c * (B : ℝ) := mul_le_mul_of_nonneg_left hstep hc
  rw [Work.KMTAreas.A7.lossWeight]
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

end Work.KMTPlan.A6.PieceBoundedH
