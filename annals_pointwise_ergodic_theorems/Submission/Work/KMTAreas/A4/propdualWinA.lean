/-
# Proposition `propdual` at the window `A`, from Corollary `struct` at the window `A`

Krause--Mirek--Tao, §5, Proposition `propdual`, in the window-parameterised form used by the §5.1
chain (`A4/improvOneZDefs.lean`): from the *window-`A`* form of Corollary `struct`
(`StructWinA P A`, i.e. `LipWinA P A` after the Hahn--Banach step of `A4/structWinA.lean`) and the
Ionescu--Wainger multiplier theorem at even exponents (`AreaA1`), produce the `ℓ²` bound for the
good-`λ` error of the dual function,

`‖(1 - Π_{≤l,≤-Log N+l}) Ã*_N(h,g)‖_{ℓ²} ≤ C · 2^{-cl} · N^{d/2}`

for `g, h` supported in `[-N₀,N₀]` with `N^d/A ≤ N₀` and `N₀ + N ≤ A N^d`.

## Relation to `A4/propdualA.lean`

`A4/propdualA` proves the same conclusion from the *older* hypothesis `StructAClaim P A`, whose
decomposition hypothesis carries an intermediate truncation radius `M` with
`N₀ + N ≤ M ≤ A N^d` in addition to the support radius `N₀` of the data.  The present module
removes that intermediate radius: the hypothesis is `StructWinA P A`, which is exactly what
`A4/structWinA` produces from Proposition `lip` at the window `A`, and exactly what the consumer
`PropdualAHyp` supplies (`N^d/A ≤ N₀`, `N₀ + N ≤ A N^d`).

The proof is the same one as in `A4/propdualA.lean` (whose auxiliary lemmas `angleBracket_coe_le_succA`,
`rpow_prod_leA`, `eLpNorm_sub_kmtProj_leA` are reused here): the constants of the decomposition of
`Ã*_N(h,g)` carry the factor `A` (`C·A·δ^{-K}` in place of `Cδ^{-K}`) and the `ℓ²`/`ℓ^{p'}` norms of
`Ã*_N(h,g)` carry `C_sh = 2A+1` (`2(N₀+N) + 1 ≤ C_sh N^d`) in place of the pinned `9`; both are
absorbed by the final existential constant.  The single difference is the call to the structure
theorem, which is now made directly at the support radius `N₀` of the data (with the hypotheses
`N^d/A ≤ N₀` and `N₀ + N ≤ A N^d` of `StructWinA`) instead of at the intermediate radius `N₀ + N`.

## Main result

* `Work.KMTAreas.A4.propdualWinA` — Proposition `propdual` at the window `A`, from `StructWinA`.
-/
import Submission.Work.KMTAreas.A4.propdualA

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators ENNReal NNReal
open MeasureTheory Polynomial Finset Filter

namespace Work.KMTAreas.A4

open Work.Analysis.IonescuWainger (L2Z)
open Work.Analysis.IWMultiplier (angleBracket)
open Work.Analysis.InverseTheory
open Work.KMTContract (kmtProj)
open Work.KMTAreas.A5 (BoundedZ boundedZ_add kmtProj_add_bounded kmtProj_smul_bounded)

/-- **Proposition `propdual` at the window `A`**, from the window-`A` decomposition of the dual
function (`StructWinA P A`) and the Ionescu--Wainger theorem at even exponents (`AreaA1`). -/
theorem propdualWinA (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree) (hA1 : Work.KMTContract.AreaA1) (A : ℝ) (hA : 1 ≤ A) (hStruct : Work.KMTAreas.A4.StructWinA P A) : Work.KMTAreas.A4.PropdualAClaim P A := by
  classical
  obtain ⟨C, K, hCpos, hKpos, hStructAll⟩ := hStruct
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hCApos : 0 < C * A := mul_pos hCpos hApos
  -- the constant of the `ℓ²`/`ℓ^{p'}` bounds of `Ã*`
  set Kst : ℝ := 2 * A + 1 with hKstdef
  have hKst1 : 1 ≤ Kst := by rw [hKstdef]; linarith
  have hKstpos : 0 < Kst := lt_of_lt_of_le zero_lt_one hKst1
  -- the rate `c`, the auxiliary exponent `K₁`, the exponents `p < 2 < p'`
  set c : ℝ := 1 / (16 * K) with hcdef
  have hcpos : 0 < c := by rw [hcdef]; positivity
  have h8c : 8 * c * K = 1 / 2 := by rw [hcdef]; field_simp; ring
  set K₁ : ℝ := max (2 * K - 1) 1 with hK₁def
  have hK₁ge1 : 1 ≤ K₁ := le_max_right _ _
  obtain ⟨hp1, hp2, hpexp⟩ := p_choice_facts (K := K₁) hK₁ge1
  set p : ℝ := 1 + 1 / (4 * K₁ + 2) with hpdef
  have hp1' : 1 < p := by rw [hpdef]; exact hp1
  have hp2' : p < 2 := by rw [hpdef]; exact hp2
  have hpexp' : 1 / 2 ≤ (1 + K₁) / p - K₁ := by rw [hpdef]; exact hpexp
  have hp0 : 0 < p := by linarith
  set p' : ℝ := p / (p - 1) with hp'def
  have hp'm1 : 1 < p' := by
    rw [hp'def]
    rw [lt_div_iff₀ (by linarith : (0 : ℝ) < p - 1)]
    linarith
  have hp'm2 : 2 < p' := by
    rw [hp'def]
    rw [lt_div_iff₀ (by linarith : (0 : ℝ) < p - 1)]
    linarith
  have hp'0 : 0 < p' := by linarith
  have hpp' : 1 / p + 1 / p' = 1 := by
    rw [hp'def]
    field_simp
    ring
  have hrel : (1 : ℝ) / 2 = (1 - 1 / 2) / p + (1 / 2) / p' := by
    have h := hpp'
    field_simp at h ⊢
    linarith
  refine ⟨c, hcpos, fun ρ hρ0 hρ1 => ?_⟩
  -- the three Ionescu--Wainger bounds and non-aliasing
  obtain ⟨Cρ2, hCρ2pos, C2, hC2pos, hpr2⟩ :=
    Work.KMTAreas.A5.kmtProj_lp_bound_A1 hA1 (p := 2) hρ0 hρ1 (by norm_num)
  obtain ⟨Cρp, hCρppos, Cp, hCppos, hprp⟩ :=
    Work.KMTAreas.A5.kmtProj_lp_bound_A1 hA1 (p := p) hρ0 hρ1 hp1'
  obtain ⟨Cρp', hCρp'pos, Cp', hCp'pos, hprp'⟩ :=
    Work.KMTAreas.A5.kmtProj_lp_bound_A1 hA1 (p := p') hρ0 hρ1 hp'm1
  obtain ⟨CρNA, hCρNApos, hNA0⟩ :=
    Work.Analysis.IonescuWainger.exists_goodMajorArcs_nonAliasing hρ0
  set Cρ : ℝ := max 2 (max CρNA (max Cρ2 (max Cρp Cρp'))) with hCρdef
  have h2Cρ : 2 ≤ Cρ := le_max_left _ _
  have hCρNAle : CρNA ≤ Cρ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCρ2le : Cρ2 ≤ Cρ := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hCρple : Cρp ≤ Cρ := le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
  have hCρp'le : Cρp' ≤ Cρ := le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
  have hCρpos : 0 < Cρ := lt_of_lt_of_le (by norm_num) h2Cρ
  have hNonAl : ∀ (l : ℕ) (k : ℤ), Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l k →
      Work.Analysis.IonescuWainger.NonAliasing k (Work.Analysis.IonescuWainger.iwArithFreqs ρ l) :=
    fun l k hk => hNA0 l k (Work.KMTAreas.A5.goodMajorArcs_mono hCρNAle hk)
  -- the threshold beyond which the exponential gain beats all polynomial factors
  have hev1 : ∀ᶠ l : ℕ in Filter.atTop, 2 * Real.logb 2 (4 * (C * A)) ≤ (l : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  have hev2 : ∀ᶠ l : ℕ in Filter.atTop,
      max (2 * Real.logb 2 (4 * (C * A))) ((l : ℝ) + 1) ≤ (2 : ℝ) ^ (c * (l : ℝ)) :=
    Work.KMTAreas.A4.eventually_max_le_two_rpow c (2 * Real.logb 2 (4 * (C * A))) hcpos
  obtain ⟨L₁, hL₁⟩ := Filter.eventually_atTop.1 (hev1.and hev2)
  have hL₁₁ : ∀ l : ℕ, L₁ ≤ l → 2 * Real.logb 2 (4 * (C * A)) ≤ (l : ℝ) :=
    fun l hl => (hL₁ l hl).1
  have hL₁₂ : ∀ l : ℕ, L₁ ≤ l →
      max (2 * Real.logb 2 (4 * (C * A))) ((l : ℝ) + 1) ≤ (2 : ℝ) ^ (c * (l : ℝ)) :=
    fun l hl => (hL₁ l hl).2
  -- the final constant
  set Cf : ℝ := max (max (max (Kst * (1 + (C2 : ℝ)) * ((L₁ : ℝ) + 1) * (2 : ℝ) ^ (c * (L₁ : ℝ)))
      (2 * (1 + (Cp : ℝ)) * (1 + (Cp' : ℝ)) * (4 * (C * A) + 20 + Kst) + (1 + (C2 : ℝ)))) 1) 1
    with hCfdef
  have hCf1 : 1 ≤ Cf := le_max_right _ _
  have hCfpos : 0 < Cf := lt_of_lt_of_le zero_lt_one hCf1
  have hCfsmall : Kst * (1 + (C2 : ℝ)) * ((L₁ : ℝ) + 1) * (2 : ℝ) ^ (c * (L₁ : ℝ)) ≤ Cf :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hCffinal : 2 * (1 + (Cp : ℝ)) * (1 + (Cp' : ℝ)) * (4 * (C * A) + 20 + Kst) + (1 + (C2 : ℝ)) ≤ Cf :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  refine ⟨Cρ, hCρpos, ⟨Cf.toNNReal, ?_, ?_⟩⟩
  · rw [← NNReal.coe_pos, Real.coe_toNNReal Cf hCfpos.le]
    exact hCfpos
  intro N N₀ l g h hN hN0lo hN0hi hgs hhs hg1 hh1 hgood
  -- the height `k = l - log₂ N` of the projection
  set k : ℤ := (l : ℤ) - Work.Analysis.EndVar.logN N with hkdef
  have hgood' : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l k := hgood
  have hd1 : 1 ≤ P.natDegree := le_trans (by norm_num) hP
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  set Nd : ℝ := (N : ℝ) ^ P.natDegree with hNddef
  have hNdpos : 0 < Nd := by rw [hNddef]; positivity
  have hNd1 : 1 ≤ Nd := by rw [hNddef]; exact one_le_pow₀ (by exact_mod_cast hN)
  have hNleNd : (N : ℝ) ≤ Nd := by
    rw [hNddef]
    calc (N : ℝ) = (N : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (N : ℝ) ^ P.natDegree := pow_le_pow_right₀ (by exact_mod_cast hN : (1 : ℝ) ≤ (N : ℝ)) hd1
  have hN0N : (N₀ : ℝ) + (N : ℝ) ≤ A * Nd := by rw [hNddef]; exact hN0hi
  have hN0lo' : Nd / A ≤ (N₀ : ℝ) := by rw [hNddef]; exact hN0lo
  -- the trivial pointwise bound for `Ã*`
  have hApt : ∀ x : ℤ, ‖AhalfTranspose N P h g x‖ ≤ 1 := by
    have hb := (AhalfTransposeBound N P h g N₀ hhs hgs (Mh := 1) (Mg := 1) zero_le_one zero_le_one
      (fun x => hh1 x) (fun x => hg1 x)).1
    intro x; simpa using hb x
  -- `2(N₀+N) + 1 ≤ Kst · N^d`
  have hXle : 2 * ((N₀ : ℝ) + (N : ℝ)) + 1 ≤ Kst * Nd := by
    have h1 : 2 * ((N₀ : ℝ) + (N : ℝ)) ≤ 2 * (A * Nd) := by linarith [hN0N]
    have h2 : 2 * (A * Nd) + 1 ≤ (2 * A + 1) * Nd := by nlinarith [hNd1, hNdpos]
    have h3 : (2 * A + 1) * Nd ≤ Kst * Nd := by
      refine mul_le_mul_of_nonneg_right ?_ hNdpos.le
      rw [hKstdef]
    linarith [h1, h2, h3]
  have hAst : eLpNorm (fun x : ℤ => AhalfTranspose N P h g x) 2 Measure.count
      ≤ ENNReal.ofReal (Kst * Nd ^ (1 / 2 : ℝ)) := by
    refine (eLpNorm_AhalfTranspose_le hgs hhs hg1 hh1).trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    calc (2 * ((N₀ : ℝ) + (N : ℝ)) + 1) ^ (1 / 2 : ℝ) ≤ (Kst * Nd) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hXle (by norm_num)
      _ = Kst ^ (1 / 2 : ℝ) * Nd ^ (1 / 2 : ℝ) := Real.mul_rpow (le_of_lt hKstpos) hNdpos.le
      _ ≤ Kst * Nd ^ (1 / 2 : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          calc Kst ^ (1 / 2 : ℝ) ≤ Kst ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le hKst1 (by norm_num)
            _ = Kst := Real.rpow_one _
  have hAstp' : eLpNorm (fun x : ℤ => AhalfTranspose N P h g x) (ENNReal.ofReal p') Measure.count
      ≤ ENNReal.ofReal (Kst * Nd ^ (1 / p')) := by
    refine (eLpNorm_AhalfTranspose_le_rpow hhs hg1 hh1 (le_of_lt hp'm1)).trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have h1q : 1 / p' ≤ 1 := by
      rw [div_le_one (by linarith [hp'0])]; linarith
    calc (2 * ((N₀ : ℝ) + (N : ℝ)) + 1) ^ (1 / p') ≤ (Kst * Nd) ^ (1 / p') :=
          Real.rpow_le_rpow (by positivity) hXle (by positivity)
      _ = Kst ^ (1 / p') * Nd ^ (1 / p') := Real.mul_rpow (le_of_lt hKstpos) hNdpos.le
      _ ≤ Kst * Nd ^ (1 / p') := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          calc Kst ^ (1 / p') ≤ Kst ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hKst1 h1q
            _ = Kst := Real.rpow_one _
  -- the `ℓ²` projection bound
  have hproj_2 : ∀ u : ℤ → ℂ, eLpNorm (kmtProj ρ l k u) 2 Measure.count
      ≤ ENNReal.ofReal (C2 : ℝ) * ENNReal.ofReal (angleBracket l : ℝ) * eLpNorm u 2 Measure.count := by
    intro u
    have hh := hpr2 l k (Work.KMTAreas.A5.goodMajorArcs_mono hCρ2le hgood) u
    rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num] at hh
    exact hh
  have hcoeeq : ((Cf.toNNReal : NNReal) : ENNReal) = ENNReal.ofReal Cf := by
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
    exact Real.coe_toNNReal Cf hCfpos.le
  rw [hcoeeq, ← ENNReal.ofReal_mul hCfpos.le]
  by_cases hsl : l < L₁
  · -- ## small `l`: the trivial `(anf)` bound suffices
    have hprojAst : eLpNorm (kmtProj ρ l k (fun x : ℤ => AhalfTranspose N P h g x)) 2 Measure.count
        ≤ ENNReal.ofReal (C2 : ℝ) * ENNReal.ofReal (angleBracket l : ℝ)
            * ENNReal.ofReal (Kst * Nd ^ (1 / 2 : ℝ)) := by
      refine (hproj_2 _).trans ?_
      exact mul_le_mul_of_nonneg_left hAst (by positivity)
    have hmain : eLpNorm (fun x : ℤ => AhalfTranspose N P h g x
          - kmtProj ρ l k (fun x : ℤ => AhalfTranspose N P h g x) x) 2 Measure.count
        ≤ ENNReal.ofReal (Kst * Nd ^ (1 / 2 : ℝ))
          + ENNReal.ofReal (C2 : ℝ) * ENNReal.ofReal (angleBracket l : ℝ)
            * ENNReal.ofReal (Kst * Nd ^ (1 / 2 : ℝ)) :=
      (eLpNorm_sub_le (f := fun x : ℤ => AhalfTranspose N P h g x)
          (g := fun x : ℤ => kmtProj ρ l k (fun x : ℤ => AhalfTranspose N P h g x) x) (by norm_num)).trans
        (add_le_add hAst hprojAst)
    refine hmain.trans ?_
    have hangle : (angleBracket l : ℝ) ≤ (L₁ : ℝ) + 1 :=
      (angleBracket_coe_le_succA l).trans (by exact_mod_cast (Nat.add_le_add_right hsl.le 1))
    have hexp : (2 : ℝ) ^ (-(c * (L₁ : ℝ))) ≤ (2 : ℝ) ^ (-(c * (l : ℝ))) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      have hlr : (l : ℝ) ≤ (L₁ : ℝ) := by exact_mod_cast hsl.le
      nlinarith [hcpos, hlr]
    have hreal : Kst * (1 + (C2 : ℝ) * (angleBracket l : ℝ)) * Nd ^ (1 / 2 : ℝ)
        ≤ Cf * ((2 : ℝ) ^ (-(c * (l : ℝ))) * Nd ^ (1 / 2 : ℝ)) := by
      have h1 : Kst * (1 + (C2 : ℝ) * (angleBracket l : ℝ))
          ≤ Kst * (1 + (C2 : ℝ) * ((L₁ : ℝ) + 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ hKstpos.le
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hangle hC2pos.le)
      have h2 : Kst * (1 + (C2 : ℝ) * ((L₁ : ℝ) + 1)) ≤ Cf * (2 : ℝ) ^ (-(c * (l : ℝ))) := by
        have h2a : Kst * (1 + (C2 : ℝ) * ((L₁ : ℝ) + 1))
            ≤ Kst * (1 + (C2 : ℝ)) * ((L₁ : ℝ) + 1) := by
          have hL0 : (1 : ℝ) ≤ (L₁ : ℝ) + 1 := by
            have hL0a : (0 : ℝ) ≤ (L₁ : ℝ) := Nat.cast_nonneg L₁
            linarith
          nlinarith [hKstpos, hC2pos.le, hL0]
        have h2b : Kst * (1 + (C2 : ℝ)) * ((L₁ : ℝ) + 1) ≤ Cf * (2 : ℝ) ^ (-(c * (L₁ : ℝ))) := by
          have h2c : (2 : ℝ) ^ (c * (L₁ : ℝ)) * (2 : ℝ) ^ (-(c * (L₁ : ℝ))) = 1 := by
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
            simp
          calc Kst * (1 + (C2 : ℝ)) * ((L₁ : ℝ) + 1)
              = (Kst * (1 + (C2 : ℝ)) * ((L₁ : ℝ) + 1) * (2 : ℝ) ^ (c * (L₁ : ℝ)))
                  * (2 : ℝ) ^ (-(c * (L₁ : ℝ))) := by
                conv_rhs => rw [mul_assoc, h2c, mul_one]
            _ ≤ Cf * (2 : ℝ) ^ (-(c * (L₁ : ℝ))) :=
                mul_le_mul_of_nonneg_right hCfsmall (Real.rpow_nonneg (by norm_num) _)
        calc Kst * (1 + (C2 : ℝ) * ((L₁ : ℝ) + 1))
            ≤ Kst * (1 + (C2 : ℝ)) * ((L₁ : ℝ) + 1) := h2a
          _ ≤ Cf * (2 : ℝ) ^ (-(c * (L₁ : ℝ))) := h2b
          _ ≤ Cf * (2 : ℝ) ^ (-(c * (l : ℝ))) :=
              mul_le_mul_of_nonneg_left hexp hCfpos.le
      calc Kst * (1 + (C2 : ℝ) * (angleBracket l : ℝ)) * Nd ^ (1 / 2 : ℝ)
          ≤ (Cf * (2 : ℝ) ^ (-(c * (l : ℝ)))) * Nd ^ (1 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_right (h1.trans h2) (by positivity)
        _ = Cf * ((2 : ℝ) ^ (-(c * (l : ℝ))) * Nd ^ (1 / 2 : ℝ)) := by ring
    have hLHS : ENNReal.ofReal (Kst * Nd ^ (1 / 2 : ℝ))
          + ENNReal.ofReal (C2 : ℝ) * ENNReal.ofReal (angleBracket l : ℝ)
            * ENNReal.ofReal (Kst * Nd ^ (1 / 2 : ℝ))
        = ENNReal.ofReal (Kst * (1 + (C2 : ℝ) * (angleBracket l : ℝ)) * Nd ^ (1 / 2 : ℝ)) := by
      rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ (C2 : ℝ) from hC2pos.le),
        ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (C2 : ℝ) * (angleBracket l : ℝ))]
      rw [← ENNReal.ofReal_add (by positivity)
        (by positivity : (0 : ℝ) ≤ (C2 : ℝ) * (angleBracket l : ℝ) * (Kst * Nd ^ (1 / 2 : ℝ)))]
      congr 1
      ring
    rw [hLHS]
    exact ENNReal.ofReal_le_ofReal hreal
  · -- ## large `l`: the structure theorem of §5
    have hlL : L₁ ≤ l := not_lt.mp hsl
    have hmax := max_le_iff.mp (hL₁₂ l hlL)
    have hlogL : 2 * Real.logb 2 (4 * (C * A)) ≤ (l : ℝ) := hL₁₁ l hlL
    have hangleL : (angleBracket l : ℝ) ≤ (2 : ℝ) ^ (c * (l : ℝ)) :=
      (angleBracket_coe_le_succA l).trans hmax.2
    set δ : ℝ := (2 : ℝ) ^ (-(8 * c * (l : ℝ))) with hδdef
    have hδpos : 0 < δ := by rw [hδdef]; positivity
    have hδ1 : δ ≤ 1 := by
      rw [hδdef]
      refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
      have : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
      nlinarith [hcpos]
    have hδinv : δ⁻¹ = (2 : ℝ) ^ (8 * c * (l : ℝ)) := by
      rw [hδdef, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    have hδinvK : δ⁻¹ ^ K = (2 : ℝ) ^ ((l : ℝ) / 2) := by
      rw [hδinv, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      rw [show 8 * c * (l : ℝ) * K = (8 * c * K) * (l : ℝ) by ring, h8c]
      ring
    have hδquarter : δ ^ (1 / 4 : ℝ) = (2 : ℝ) ^ (-(2 * c * (l : ℝ))) := by
      rw [hδdef, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    have hδinv_pos : (0 : ℝ) < δ⁻¹ := inv_pos.mpr hδpos
    have hδinv_ge : (1 : ℝ) ≤ δ⁻¹ := (one_le_inv₀ hδpos).mpr hδ1
    have hδK1 : (1 : ℝ) ≤ δ ^ (-K₁) := by
      rw [show δ ^ (-K₁) = δ⁻¹ ^ K₁ by rw [Real.inv_rpow hδpos.le, Real.rpow_neg hδpos.le]]
      exact Real.one_le_rpow hδinv_ge (by linarith [hK₁ge1])
    have hδle : δ ≤ δ ^ (-K₁) := le_trans hδ1 hδK1
    have hδmonoK : δ ^ (-(2 * K - 1)) ≤ δ ^ (-K₁) := by
      rw [show δ ^ (-(2 * K - 1)) = δ⁻¹ ^ (2 * K - 1) by
            rw [Real.inv_rpow hδpos.le, Real.rpow_neg hδpos.le],
          show δ ^ (-K₁) = δ⁻¹ ^ K₁ by rw [Real.inv_rpow hδpos.le, Real.rpow_neg hδpos.le]]
      exact Real.rpow_le_rpow_of_exponent_le hδinv_ge (le_max_left _ _)
    obtain ⟨ι, hι, s, φ, lam, w, E₁, E₂, hφmem, hlam, hw0, hwsum, hE1, hE2, hpoint⟩ :=
      hStructAll ρ hρ0 hρ1 δ N N₀ g h hN hδpos hδ1 hN0lo' hN0hi hgs hhs hg1 hh1
    have hE1sum : Summable fun x : ℤ => ‖E₁ x‖ := hE1.1
    have hE1le : ∑' x : ℤ, ‖E₁ x‖ ≤ δ * Nd := by rw [hNddef]; exact hE1.2
    have hE2pt : ∀ x : ℤ, ‖E₂ x‖ ≤ δ := fun x =>
      (lp.norm_apply_le_norm (p := 2) (by norm_num) E₂ x).trans hE2
    have hE2norm : eLpNorm (fun x : ℤ => E₂ x) 2 Measure.count ≤ ENNReal.ofReal δ := by
      rw [eLpNorm_count_eq_lp_norm E₂]
      exact ENNReal.ofReal_le_ofReal hE2
    have hE2p' : eLpNorm (fun x : ℤ => E₂ x) (ENNReal.ofReal p') Measure.count ≤ ENNReal.ofReal δ :=
      (eLpNorm_count_le_of_two_le (f := fun x : ℤ => E₂ x) (q := p') hp'm2.le).trans hE2norm
    -- the pointwise and `ℓ¹` bounds of the structure functions
    have hφbd : ∀ i ∈ s, ∀ x : ℤ, ‖φ i x‖ ≤ C * A * (2 : ℝ) ^ ((l : ℝ) / 2) := by
      intro i hi x
      have h := (hφmem i hi).1 x
      rwa [hδinvK] at h
    have hφB : ∀ i ∈ s, BoundedZ (fun x : ℤ => φ i x) :=
      fun i hi => ⟨C * A * (2 : ℝ) ^ ((l : ℝ) / 2), hφbd i hi⟩
    -- the projections fix the structure functions
    have hkill : ∀ i ∈ s, kmtProj ρ l k (fun x : ℤ => φ i x) = fun x : ℤ => φ i x := by
      intro i hi
      obtain ⟨li, ki, hsupp, hli, hki⟩ := (hφmem i hi).2.2.2
      have hli2 : (2 : ℝ) ^ li ≤ C * A * (2 : ℝ) ^ ((l : ℝ) / 2) := by
        have h := hli; rwa [hδinvK] at h
      have hki2 : (2 : ℝ) ^ ki ≤ C * A * (2 : ℝ) ^ ((l : ℝ) / 2) / (N : ℝ) := by
        have h := hki; rwa [hδinvK] at h
      have hmain := two_pow_le_of_logb_le (C₀ := C * A) hCApos hN hlogL hli2 hki2
      have hsupp' : FourierSupportIn (fun x : ℤ => φ i x) (majorArc ρ l (k - 1)) :=
        hsupp.mono (majorArc_mono_of_subset
          (Work.Analysis.IonescuWainger.iwArithFreqs_mono hρ0 hρ1 hmain.1)
          hmain.2)
      exact kmtProjEqSelf hρ0 hρ1 h2Cρ hNonAl hgood' (hφmem i hi).2.1 hsupp'
    have hkillw : ∀ i ∈ s, kmtProj ρ l k (fun x : ℤ => (w i : ℂ) * ((lam i) * φ i x))
        = fun x : ℤ => (w i : ℂ) * ((lam i) * φ i x) := by
      intro i hi
      have hb2 : BoundedZ (fun x : ℤ => (lam i) * φ i x) :=
        ⟨‖lam i‖ * (C * A * (2 : ℝ) ^ ((l : ℝ) / 2)), fun x => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hφbd i hi x) (norm_nonneg _)⟩
      have h1 : kmtProj ρ l k (fun x : ℤ => (lam i) * φ i x)
          = fun x : ℤ => (lam i) * φ i x := by
        have hh := kmtProj_smul_bounded ρ l k (lam i) (hφB i hi)
        rw [hkill i hi] at hh
        exact hh
      have h2 := kmtProj_smul_bounded ρ l k (((w i : ℝ)) : ℂ) hb2
      rw [h1] at h2
      exact h2
    set BndS : ℝ := 4 * (C * A) * δ ^ (-(2 * K - 1)) with hBndSdef
    have hBndSeq : 4 * δ⁻¹ ^ (K - 1) * (C * A * δ⁻¹ ^ K) = BndS := by
      rw [hBndSdef]
      rw [show 4 * δ⁻¹ ^ (K - 1) * (C * A * δ⁻¹ ^ K)
          = 4 * (C * A) * (δ⁻¹ ^ (K - 1) * δ⁻¹ ^ K) by ring]
      rw [← Real.rpow_add hδinv_pos, show K - 1 + K = 2 * K - 1 by ring]
      rw [Real.inv_rpow hδpos.le, Real.rpow_neg hδpos.le]
    have hSumBound : ∀ t : Finset ι, t ⊆ s → ∀ x : ℤ,
        ‖∑ i ∈ t, (w i : ℂ) * ((lam i) * φ i x)‖ ≤ BndS := by
      intro t ht x
      have hterm : ∀ i ∈ t, ‖(w i : ℂ) * ((lam i) * φ i x)‖
          ≤ w i * (4 * δ⁻¹ ^ (K - 1) * (C * A * δ⁻¹ ^ K)) := by
        intro i hi
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw0 i)]
        refine mul_le_mul_of_nonneg_left ?_ (hw0 i)
        exact mul_le_mul (hlam i (ht hi)) ((hφmem i (ht hi)).1 x) (norm_nonneg _)
          (mul_nonneg (by linarith) (Real.rpow_nonneg (le_of_lt hδinv_pos) _))
      calc ‖∑ i ∈ t, (w i : ℂ) * ((lam i) * φ i x)‖
          ≤ ∑ i ∈ t, ‖(w i : ℂ) * ((lam i) * φ i x)‖ := norm_sum_le _ _
        _ ≤ ∑ i ∈ t, w i * (4 * δ⁻¹ ^ (K - 1) * (C * A * δ⁻¹ ^ K)) := Finset.sum_le_sum hterm
        _ = (∑ i ∈ t, w i) * (4 * δ⁻¹ ^ (K - 1) * (C * A * δ⁻¹ ^ K)) := (Finset.sum_mul ..).symm
        _ ≤ 1 * BndS := by
            rw [hBndSeq]
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ t)
              (fun i _ _ => hw0 i)).trans hwsum
        _ = BndS := one_mul _
    -- the projection fixes the whole structure sum
    have hSfix : kmtProj ρ l k (fun x : ℤ => ∑ i ∈ s, (w i : ℂ) * ((lam i) * φ i x))
        = fun x : ℤ => ∑ i ∈ s, (w i : ℂ) * ((lam i) * φ i x) := by
      have hgen : ∀ t : Finset ι, t ⊆ s →
          kmtProj ρ l k (fun x : ℤ => ∑ i ∈ t, (w i : ℂ) * ((lam i) * φ i x))
            = fun x : ℤ => ∑ i ∈ t, (w i : ℂ) * ((lam i) * φ i x) := by
        intro t
        refine Finset.induction_on t ?_ ?_
        · intro _
          have h0 : (fun x : ℤ => ∑ i ∈ (∅ : Finset ι), (w i : ℂ) * ((lam i) * φ i x)) = 0 := by
            funext x; simp
          rw [h0, Work.KMTContract.kmtProj_zero]
        · intro a t hat ih ht
          have hts : t ⊆ s := fun i hi => ht (Finset.mem_insert_of_mem hi)
          have has : a ∈ s := ht (Finset.mem_insert_self a t)
          have hwa1 : w a ≤ 1 :=
            (Finset.single_le_sum (fun i _ => hw0 i) (Finset.mem_univ a)).trans hwsum
          have hsplit : (fun x : ℤ => ∑ i ∈ insert a t, (w i : ℂ) * ((lam i) * φ i x))
              = (fun x : ℤ => (w a : ℂ) * ((lam a) * φ a x))
                + (fun x : ℤ => ∑ i ∈ t, (w i : ℂ) * ((lam i) * φ i x)) := by
            funext x
            rw [Pi.add_apply, Finset.sum_insert hat]
          have hbhead : BoundedZ (fun x : ℤ => (w a : ℂ) * ((lam a) * φ a x)) := by
            refine ⟨BndS, fun x => ?_⟩
            calc ‖(w a : ℂ) * ((lam a) * φ a x)‖
                = w a * (‖lam a‖ * ‖φ a x‖) := by
                  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw0 a)]
              _ ≤ 1 * ((4 * δ⁻¹ ^ (K - 1)) * (C * A * δ⁻¹ ^ K)) := by
                  refine mul_le_mul hwa1 (mul_le_mul (hlam a has) ((hφmem a has).1 x)
                    (norm_nonneg _) ?_) (by positivity) (by norm_num)
                  exact mul_nonneg (by linarith) (Real.rpow_nonneg (le_of_lt hδinv_pos) _)
              _ = BndS := by rw [one_mul, hBndSeq]
          rw [hsplit]
          rw [kmtProj_add_bounded ρ l k hbhead ⟨BndS, hSumBound t hts⟩]
          rw [hkillw a has, ih hts]
      exact hgen s (fun i hi => hi)
    -- the pointwise decomposition and the two error terms
    have hSS : ((∑ i ∈ s, w i • (lam i • φ i) : L2Z) : ℤ → ℂ)
        = fun x : ℤ => ∑ i ∈ s, (w i : ℂ) * ((lam i) * φ i x) := by
      funext x
      rw [lp.coeFn_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [lp.coeFn_smul, Pi.smul_apply, lp.coeFn_smul, Pi.smul_apply, Complex.real_smul]
      ring
    have hdecomp : (fun x : ℤ => AhalfTranspose N P h g x)
        = (fun x : ℤ => ∑ i ∈ s, (w i : ℂ) * ((lam i) * φ i x)) + (fun x : ℤ => E₁ x)
          + (fun x : ℤ => E₂ x) := by
      funext x
      have h := hpoint x
      rw [hSS] at h
      simpa only [Pi.add_apply] using h
    have hSB : BoundedZ (fun x : ℤ => ∑ i ∈ s, (w i : ℂ) * ((lam i) * φ i x)) :=
      ⟨BndS, hSumBound s (fun i hi => hi)⟩
    have hE1ptB : ∀ x : ℤ, ‖E₁ x‖ ≤ 1 + BndS + δ := by
      intro x
      have hx : E₁ x = AhalfTranspose N P h g x
          - (∑ i ∈ s, (w i : ℂ) * ((lam i) * φ i x)) - E₂ x := by
        have h := congrFun hdecomp x
        simp only [Pi.add_apply] at h
        rw [h]; ring
      rw [hx]
      calc ‖AhalfTranspose N P h g x - (∑ i ∈ s, (w i : ℂ) * ((lam i) * φ i x)) - E₂ x‖
          ≤ ‖AhalfTranspose N P h g x‖ + ‖∑ i ∈ s, (w i : ℂ) * ((lam i) * φ i x)‖ + ‖E₂ x‖ :=
            (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
        _ ≤ 1 + BndS + δ := add_le_add (add_le_add (hApt x) (hSumBound s (fun i hi => hi) x))
            (hE2pt x)
    have hE1B : BoundedZ (fun x : ℤ => E₁ x) := ⟨1 + BndS + δ, hE1ptB⟩
    have hE2B : BoundedZ (fun x : ℤ => E₂ x) := ⟨δ, hE2pt⟩
    have hPAsplit : kmtProj ρ l k (fun x : ℤ => AhalfTranspose N P h g x)
        = (fun x : ℤ => ∑ i ∈ s, (w i : ℂ) * ((lam i) * φ i x))
          + (fun x : ℤ => kmtProj ρ l k (fun y : ℤ => E₁ y) x)
          + (fun x : ℤ => kmtProj ρ l k (fun y : ℤ => E₂ y) x) := by
      rw [hdecomp, kmtProj_add_bounded ρ l k (boundedZ_add hSB hE1B) hE2B,
        kmtProj_add_bounded ρ l k hSB hE1B, hSfix]
    have hdiff : (fun x : ℤ => AhalfTranspose N P h g x
          - kmtProj ρ l k (fun x : ℤ => AhalfTranspose N P h g x) x)
        = (fun x : ℤ => E₁ x - kmtProj ρ l k (fun y : ℤ => E₁ y) x)
          + (fun x : ℤ => E₂ x - kmtProj ρ l k (fun y : ℤ => E₂ y) x) := by
      funext x
      have h1 := congrFun hdecomp x
      have h2 := congrFun hPAsplit x
      simp only [Pi.add_apply] at h1 h2 ⊢
      rw [h1, h2]; ring
    -- the `ℓ^p` bound for `E₁`
    have hE1p : eLpNorm (fun x : ℤ => E₁ x) (ENNReal.ofReal p) Measure.count
        ≤ ENNReal.ofReal ((4 * (C * A) + 3) * δ ^ (1 / 2 : ℝ) * Nd ^ (1 / p)) := by
      refine (eLpNorm_le_of_l1_and_bounded (f := fun x : ℤ => E₁ x) (A := δ * Nd)
        (B := (4 * (C * A) + 2) * δ ^ (-K₁)) (r := p) (by positivity) (by positivity) hp1'.le
        hE1sum hE1le ?_).trans ?_
      · intro x
        have hBndSle : BndS ≤ 4 * (C * A) * δ ^ (-K₁) := by
          rw [hBndSdef]
          exact mul_le_mul_of_nonneg_left hδmonoK (by positivity)
        calc ‖E₁ x‖ ≤ 1 + BndS + δ := hE1ptB x
          _ ≤ 1 + 4 * (C * A) * δ ^ (-K₁) + δ := by linarith [hBndSle]
          _ ≤ 2 * δ ^ (-K₁) + 4 * (C * A) * δ ^ (-K₁) := by linarith [hδK1, hδle]
          _ = (4 * (C * A) + 2) * δ ^ (-K₁) := by ring
      · exact ENNReal.ofReal_le_ofReal (rpow_prod_leA hδpos hNdpos hCApos hp1' hpexp' hδ1)
    -- the `ℓ²` and `ℓ^{p'}` bounds for `(1 - Π)E₂`
    have hE2part : eLpNorm (fun x : ℤ => E₂ x - kmtProj ρ l k (fun y : ℤ => E₂ y) x)
        2 Measure.count ≤ ENNReal.ofReal ((1 + (C2 : ℝ) * (angleBracket l : ℝ)) * δ) := by
      have hb : ∀ f : ℤ → ℂ, eLpNorm (kmtProj ρ l k f) (ENNReal.ofReal 2) Measure.count
          ≤ ENNReal.ofReal ((C2 : ℝ) * (angleBracket l : ℝ))
              * eLpNorm f (ENNReal.ofReal 2) Measure.count := by
        intro f
        rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
        refine (hproj_2 f).trans (le_of_eq ?_)
        rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ (C2 : ℝ) from hC2pos.le)]
      have hsub := eLpNorm_sub_kmtProj_leA (ρ := ρ) (l := l) (k := k) (q := 2) (by norm_num)
        (C := (C2 : ℝ) * (angleBracket l : ℝ)) hb (fun x : ℤ => E₂ x)
      rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num] at hsub
      refine hsub.trans ?_
      calc (ENNReal.ofReal ((C2 : ℝ) * (angleBracket l : ℝ)) + 1)
            * eLpNorm (fun x : ℤ => E₂ x) 2 Measure.count
          ≤ (ENNReal.ofReal ((C2 : ℝ) * (angleBracket l : ℝ)) + 1) * ENNReal.ofReal δ :=
            mul_le_mul_of_nonneg_left hE2norm (by positivity)
        _ = ENNReal.ofReal ((1 + (C2 : ℝ) * (angleBracket l : ℝ)) * δ) := by
            rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by positivity) (by norm_num),
              ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            ring
    have hE2p'' : eLpNorm (fun x : ℤ => E₂ x - kmtProj ρ l k (fun y : ℤ => E₂ y) x)
        (ENNReal.ofReal p') Measure.count
        ≤ ENNReal.ofReal ((1 + (Cp' : ℝ) * (angleBracket l : ℝ)) * δ) := by
      have hb : ∀ f : ℤ → ℂ, eLpNorm (kmtProj ρ l k f) (ENNReal.ofReal p') Measure.count
          ≤ ENNReal.ofReal ((Cp' : ℝ) * (angleBracket l : ℝ))
              * eLpNorm f (ENNReal.ofReal p') Measure.count := by
        intro f
        refine (hprp' l k (Work.KMTAreas.A5.goodMajorArcs_mono hCρp'le hgood') f).trans (le_of_eq ?_)
        rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ (Cp' : ℝ) from hCp'pos.le)]
      have hsub := eLpNorm_sub_kmtProj_leA (ρ := ρ) (l := l) (k := k) (q := p') hp'm1
        (C := (Cp' : ℝ) * (angleBracket l : ℝ)) hb (fun x : ℤ => E₂ x)
      refine hsub.trans ?_
      calc (ENNReal.ofReal ((Cp' : ℝ) * (angleBracket l : ℝ)) + 1)
            * eLpNorm (fun x : ℤ => E₂ x) (ENNReal.ofReal p') Measure.count
          ≤ (ENNReal.ofReal ((Cp' : ℝ) * (angleBracket l : ℝ)) + 1) * ENNReal.ofReal δ :=
            mul_le_mul_of_nonneg_left hE2p' (by positivity)
        _ = ENNReal.ofReal ((1 + (Cp' : ℝ) * (angleBracket l : ℝ)) * δ) := by
            rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by positivity) (by norm_num),
              ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            ring
    -- the two bounds for `(1 - Π)E₁`, with the common coefficient `Xl`
    set Xl : ℝ := ((Cp : ℝ) * (angleBracket l : ℝ) + 1) * (4 * (C * A) + 3)
      + ((Cp' : ℝ) * (angleBracket l : ℝ) + 1) * (Kst + 1) with hXldef
    have hXlnonneg : 0 ≤ Xl := by rw [hXldef]; positivity
    have hXl1 : ((Cp : ℝ) * (angleBracket l : ℝ) + 1) * (4 * (C * A) + 3) ≤ Xl := by
      rw [hXldef]; exact le_add_of_nonneg_right (by positivity)
    have hXl2 : ((Cp' : ℝ) * (angleBracket l : ℝ) + 1) * (Kst + 1) ≤ Xl := by
      rw [hXldef]; exact le_add_of_nonneg_left (by positivity)
    have hE1pX : eLpNorm (fun x : ℤ => E₁ x - kmtProj ρ l k (fun y : ℤ => E₁ y) x)
        (ENNReal.ofReal p) Measure.count
        ≤ ENNReal.ofReal (Xl * δ ^ (1 / 2 : ℝ) * Nd ^ (1 / p)) := by
      have hb : ∀ f : ℤ → ℂ, eLpNorm (kmtProj ρ l k f) (ENNReal.ofReal p) Measure.count
          ≤ ENNReal.ofReal ((Cp : ℝ) * (angleBracket l : ℝ))
              * eLpNorm f (ENNReal.ofReal p) Measure.count := by
        intro f
        refine (hprp l k (Work.KMTAreas.A5.goodMajorArcs_mono hCρple hgood') f).trans (le_of_eq ?_)
        rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ (Cp : ℝ) from hCppos.le)]
      have hsub := eLpNorm_sub_kmtProj_leA (ρ := ρ) (l := l) (k := k) (q := p) hp1'
        (C := (Cp : ℝ) * (angleBracket l : ℝ)) hb (fun x : ℤ => E₁ x)
      refine hsub.trans ?_
      calc (ENNReal.ofReal ((Cp : ℝ) * (angleBracket l : ℝ)) + 1)
            * eLpNorm (fun x : ℤ => E₁ x) (ENNReal.ofReal p) Measure.count
          ≤ (ENNReal.ofReal ((Cp : ℝ) * (angleBracket l : ℝ)) + 1)
              * ENNReal.ofReal ((4 * (C * A) + 3) * δ ^ (1 / 2 : ℝ) * Nd ^ (1 / p)) :=
            mul_le_mul_of_nonneg_left hE1p (by positivity)
        _ = ENNReal.ofReal (((Cp : ℝ) * (angleBracket l : ℝ) + 1)
              * ((4 * (C * A) + 3) * δ ^ (1 / 2 : ℝ) * Nd ^ (1 / p))) := by
            rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by positivity) (by norm_num),
              ← ENNReal.ofReal_mul (by positivity)]
        _ ≤ ENNReal.ofReal (Xl * δ ^ (1 / 2 : ℝ) * Nd ^ (1 / p)) := by
            refine ENNReal.ofReal_le_ofReal ?_
            calc ((Cp : ℝ) * (angleBracket l : ℝ) + 1)
                  * ((4 * (C * A) + 3) * δ ^ (1 / 2 : ℝ) * Nd ^ (1 / p))
                = (((Cp : ℝ) * (angleBracket l : ℝ) + 1) * (4 * (C * A) + 3))
                    * (δ ^ (1 / 2 : ℝ) * Nd ^ (1 / p)) := by ring
              _ ≤ Xl * (δ ^ (1 / 2 : ℝ) * Nd ^ (1 / p)) :=
                  mul_le_mul_of_nonneg_right hXl1 (by positivity)
              _ = Xl * δ ^ (1 / 2 : ℝ) * Nd ^ (1 / p) := by ring
    have hE1p'X : eLpNorm (fun x : ℤ => E₁ x - kmtProj ρ l k (fun y : ℤ => E₁ y) x)
        (ENNReal.ofReal p') Measure.count ≤ ENNReal.ofReal (Xl * Nd ^ (1 / p')) := by
      have hpt : ∀ x : ℤ, E₁ x - kmtProj ρ l k (fun y : ℤ => E₁ y) x
          = (AhalfTranspose N P h g x
              - kmtProj ρ l k (fun x : ℤ => AhalfTranspose N P h g x) x)
            - (E₂ x - kmtProj ρ l k (fun y : ℤ => E₂ y) x) := by
        intro x
        have h := congrFun hdiff x
        simp only [Pi.add_apply] at h
        rw [h]; ring
      have hrew : (fun x : ℤ => E₁ x - kmtProj ρ l k (fun y : ℤ => E₁ y) x)
          = (fun x : ℤ => AhalfTranspose N P h g x
              - kmtProj ρ l k (fun x : ℤ => AhalfTranspose N P h g x) x)
            - (fun x : ℤ => E₂ x - kmtProj ρ l k (fun y : ℤ => E₂ y) x) := by
        funext x
        exact hpt x
      rw [hrew]
      refine (eLpNorm_sub_le (f := fun x : ℤ => AhalfTranspose N P h g x
            - kmtProj ρ l k (fun x : ℤ => AhalfTranspose N P h g x) x)
          (g := fun x : ℤ => E₂ x - kmtProj ρ l k (fun y : ℤ => E₂ y) x)
          (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp'm1.le)).trans ?_
      -- the two pieces
      have hA1 : eLpNorm (fun x : ℤ => AhalfTranspose N P h g x
            - kmtProj ρ l k (fun x : ℤ => AhalfTranspose N P h g x) x)
          (ENNReal.ofReal p') Measure.count
          ≤ ENNReal.ofReal (((Cp' : ℝ) * (angleBracket l : ℝ) + 1)
              * (Kst * Nd ^ (1 / p'))) := by
        have hb : ∀ f : ℤ → ℂ, eLpNorm (kmtProj ρ l k f) (ENNReal.ofReal p') Measure.count
            ≤ ENNReal.ofReal ((Cp' : ℝ) * (angleBracket l : ℝ))
                * eLpNorm f (ENNReal.ofReal p') Measure.count := by
          intro f
          refine (hprp' l k (Work.KMTAreas.A5.goodMajorArcs_mono hCρp'le hgood') f).trans (le_of_eq ?_)
          rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ (Cp' : ℝ) from hCp'pos.le)]
        have hsub := eLpNorm_sub_kmtProj_leA (ρ := ρ) (l := l) (k := k) (q := p') hp'm1
          (C := (Cp' : ℝ) * (angleBracket l : ℝ)) hb (fun x : ℤ => AhalfTranspose N P h g x)
        refine hsub.trans ?_
        calc (ENNReal.ofReal ((Cp' : ℝ) * (angleBracket l : ℝ)) + 1)
              * eLpNorm (fun x : ℤ => AhalfTranspose N P h g x) (ENNReal.ofReal p') Measure.count
            ≤ (ENNReal.ofReal ((Cp' : ℝ) * (angleBracket l : ℝ)) + 1)
                * ENNReal.ofReal (Kst * Nd ^ (1 / p')) :=
              mul_le_mul_of_nonneg_left hAstp' (by positivity)
          _ = ENNReal.ofReal (((Cp' : ℝ) * (angleBracket l : ℝ) + 1)
                * (Kst * Nd ^ (1 / p'))) := by
              rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by positivity) (by norm_num),
                ← ENNReal.ofReal_mul (by positivity)]
      have hB1 : eLpNorm (fun x : ℤ => E₂ x - kmtProj ρ l k (fun y : ℤ => E₂ y) x)
          (ENNReal.ofReal p') Measure.count
          ≤ ENNReal.ofReal (((Cp' : ℝ) * (angleBracket l : ℝ) + 1) * Nd ^ (1 / p')) := by
        refine hE2p''.trans ?_
        refine ENNReal.ofReal_le_ofReal ?_
        have hNd1' : (1 : ℝ) ≤ Nd ^ (1 / p') := Real.one_le_rpow hNd1 (by positivity)
        have hδle : δ ≤ Nd ^ (1 / p') := le_trans hδ1 hNd1'
        calc (1 + (Cp' : ℝ) * (angleBracket l : ℝ)) * δ
            ≤ (1 + (Cp' : ℝ) * (angleBracket l : ℝ)) * Nd ^ (1 / p') :=
              mul_le_mul_of_nonneg_left hδle (by positivity)
          _ = ((Cp' : ℝ) * (angleBracket l : ℝ) + 1) * Nd ^ (1 / p') := by ring
      refine (add_le_add hA1 hB1).trans ?_
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      calc ((Cp' : ℝ) * (angleBracket l : ℝ) + 1) * (Kst * Nd ^ (1 / p'))
            + ((Cp' : ℝ) * (angleBracket l : ℝ) + 1) * Nd ^ (1 / p')
          = ((Cp' : ℝ) * (angleBracket l : ℝ) + 1) * (Kst + 1) * Nd ^ (1 / p') := by ring
        _ ≤ Xl * Nd ^ (1 / p') := mul_le_mul_of_nonneg_right hXl2 (by positivity)
    -- the interpolation
    have hE1part : eLpNorm (fun x : ℤ => E₁ x - kmtProj ρ l k (fun y : ℤ => E₁ y) x)
        2 Measure.count ≤ ENNReal.ofReal (Xl * δ ^ (1 / 4 : ℝ) * Nd ^ (1 / 2 : ℝ)) := by
      have hint := eLpNorm_two_le_of_interp (w := fun x : ℤ => E₁ x
          - kmtProj ρ l k (fun y : ℤ => E₁ y) x) hp1' hp'm1 (by norm_num) (by norm_num)
        hrel (by positivity)
        (by positivity : (0 : ℝ) ≤ Xl * Nd ^ (1 / p')) hE1pX hE1p'X
      have hX := rpowHalf_mul_rpow_rpowHalf (X := Xl) (δ := δ) (Nd := Nd) (p := p) (q := p')
        hXlnonneg hδpos.le hNdpos.le hp0 hp'0 hpp'
      rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at hint
      rw [hX] at hint
      exact hint
    -- the final assembly
    have hangle_delta : (angleBracket l : ℝ) * δ ^ (1 / 4 : ℝ) ≤ (2 : ℝ) ^ (-(c * (l : ℝ))) := by
      rw [hδquarter]
      have h2 : (0 : ℝ) < (2 : ℝ) ^ (-(2 * c * (l : ℝ))) := Real.rpow_pos_of_pos (by norm_num) _
      calc (angleBracket l : ℝ) * (2 : ℝ) ^ (-(2 * c * (l : ℝ)))
          ≤ (2 : ℝ) ^ (c * (l : ℝ)) * (2 : ℝ) ^ (-(2 * c * (l : ℝ))) :=
            mul_le_mul_of_nonneg_right hangleL h2.le
        _ = (2 : ℝ) ^ (-(c * (l : ℝ))) := by
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
            congr 1; ring
    have hangle_delta2 : (angleBracket l : ℝ) * δ ≤ (2 : ℝ) ^ (-(c * (l : ℝ))) := by
      rw [hδdef]
      have h2 : (0 : ℝ) < (2 : ℝ) ^ (-(8 * c * (l : ℝ))) := Real.rpow_pos_of_pos (by norm_num) _
      calc (angleBracket l : ℝ) * (2 : ℝ) ^ (-(8 * c * (l : ℝ)))
          ≤ (2 : ℝ) ^ (c * (l : ℝ)) * (2 : ℝ) ^ (-(8 * c * (l : ℝ))) :=
            mul_le_mul_of_nonneg_right hangleL h2.le
        _ = (2 : ℝ) ^ (c * (l : ℝ) + -(8 * c * (l : ℝ))) := by
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        _ ≤ (2 : ℝ) ^ (-(c * (l : ℝ))) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by
            have hcl : (0 : ℝ) ≤ c * (l : ℝ) := mul_nonneg hcpos.le (Nat.cast_nonneg l)
            linarith only [hcl])
    have hXlbound : Xl ≤ 2 * (1 + (Cp : ℝ)) * (1 + (Cp' : ℝ)) * (4 * (C * A) + 20 + Kst)
        * (angleBracket l : ℝ) := by
      have hbl : (1 : ℝ) ≤ (angleBracket l : ℝ) := angleBracket_coe_le_oneA l
      have hbl0 : (0 : ℝ) ≤ (angleBracket l : ℝ) := angleBracket_coe_nonnegA l
      have h1 : (Cp : ℝ) * (angleBracket l : ℝ) + 1 ≤ (1 + (Cp : ℝ)) * (angleBracket l : ℝ) := by
        nlinarith only [hbl]
      have h2 : (Cp' : ℝ) * (angleBracket l : ℝ) + 1 ≤ (1 + (Cp' : ℝ)) * (angleBracket l : ℝ) := by
        nlinarith only [hbl]
      have hbig : (0 : ℝ) < 4 * (C * A) + 20 + Kst := by linarith [hCApos, hKstpos]
      have h3 : (4 * (C * A) + 3 : ℝ) ≤ (1 + (Cp' : ℝ)) * (4 * (C * A) + 20 + Kst) := by
        have h1' : (1 : ℝ) ≤ 1 + (Cp' : ℝ) := by linarith [hCp'pos.le]
        calc (4 * (C * A) + 3 : ℝ) ≤ 4 * (C * A) + 20 + Kst := by linarith [hKstpos]
          _ ≤ (1 + (Cp' : ℝ)) * (4 * (C * A) + 20 + Kst) := le_mul_of_one_le_left hbig.le h1'
      have h4 : (Kst + 1 : ℝ) ≤ (1 + (Cp : ℝ)) * (4 * (C * A) + 20 + Kst) := by
        have h4a : Kst + 1 ≤ 4 * (C * A) + 20 + Kst := by linarith [hCApos]
        have h1' : (1 : ℝ) ≤ 1 + (Cp : ℝ) := by linarith [hCppos.le]
        exact h4a.trans (le_mul_of_one_le_left hbig.le h1')
      have ha : (1 + (Cp : ℝ)) * (angleBracket l : ℝ) * (4 * (C * A) + 3)
          ≤ (angleBracket l : ℝ) * ((1 + (Cp : ℝ)) * (1 + (Cp' : ℝ))
              * (4 * (C * A) + 20 + Kst)) := by
        have hc1n : (0 : ℝ) ≤ 1 + (Cp : ℝ) := by linarith [hCppos.le]
        have hstep2 : (1 + (Cp : ℝ)) * (4 * (C * A) + 3)
            ≤ (1 + (Cp : ℝ)) * (1 + (Cp' : ℝ)) * (4 * (C * A) + 20 + Kst) := by
          calc (1 + (Cp : ℝ)) * (4 * (C * A) + 3)
              ≤ (1 + (Cp : ℝ)) * ((1 + (Cp' : ℝ)) * (4 * (C * A) + 20 + Kst)) :=
                mul_le_mul_of_nonneg_left h3 hc1n
            _ = (1 + (Cp : ℝ)) * (1 + (Cp' : ℝ)) * (4 * (C * A) + 20 + Kst) := by ring
        calc (1 + (Cp : ℝ)) * (angleBracket l : ℝ) * (4 * (C * A) + 3)
            = (angleBracket l : ℝ) * ((1 + (Cp : ℝ)) * (4 * (C * A) + 3)) := by ring
          _ ≤ (angleBracket l : ℝ) * ((1 + (Cp : ℝ)) * (1 + (Cp' : ℝ))
                * (4 * (C * A) + 20 + Kst)) :=
              mul_le_mul_of_nonneg_left hstep2 hbl0
      have hb : (1 + (Cp' : ℝ)) * (angleBracket l : ℝ) * (Kst + 1)
          ≤ (angleBracket l : ℝ) * ((1 + (Cp : ℝ)) * (1 + (Cp' : ℝ))
              * (4 * (C * A) + 20 + Kst)) := by
        have hc2n : (0 : ℝ) ≤ 1 + (Cp' : ℝ) := by linarith [hCp'pos.le]
        have hstep2 : (1 + (Cp' : ℝ)) * (Kst + 1)
            ≤ (1 + (Cp : ℝ)) * (1 + (Cp' : ℝ)) * (4 * (C * A) + 20 + Kst) := by
          calc (1 + (Cp' : ℝ)) * (Kst + 1)
              ≤ (1 + (Cp' : ℝ)) * ((1 + (Cp : ℝ)) * (4 * (C * A) + 20 + Kst)) :=
                mul_le_mul_of_nonneg_left h4 hc2n
            _ = (1 + (Cp : ℝ)) * (1 + (Cp' : ℝ)) * (4 * (C * A) + 20 + Kst) := by ring
        calc (1 + (Cp' : ℝ)) * (angleBracket l : ℝ) * (Kst + 1)
            = (angleBracket l : ℝ) * ((1 + (Cp' : ℝ)) * (Kst + 1)) := by ring
          _ ≤ (angleBracket l : ℝ) * ((1 + (Cp : ℝ)) * (1 + (Cp' : ℝ))
                * (4 * (C * A) + 20 + Kst)) :=
              mul_le_mul_of_nonneg_left hstep2 hbl0
      rw [hXldef]
      calc ((Cp : ℝ) * (angleBracket l : ℝ) + 1) * (4 * (C * A) + 3)
            + ((Cp' : ℝ) * (angleBracket l : ℝ) + 1) * (Kst + 1)
          ≤ (1 + (Cp : ℝ)) * (angleBracket l : ℝ) * (4 * (C * A) + 3)
            + (1 + (Cp' : ℝ)) * (angleBracket l : ℝ) * (Kst + 1) :=
            add_le_add (mul_le_mul_of_nonneg_right h1 (by linarith [hCApos]))
              (mul_le_mul_of_nonneg_right h2 (by linarith [hKstpos]))
        _ ≤ (angleBracket l : ℝ) * ((1 + (Cp : ℝ)) * (1 + (Cp' : ℝ))
              * (4 * (C * A) + 20 + Kst))
            + (angleBracket l : ℝ) * ((1 + (Cp : ℝ)) * (1 + (Cp' : ℝ))
              * (4 * (C * A) + 20 + Kst)) := add_le_add ha hb
        _ = 2 * (1 + (Cp : ℝ)) * (1 + (Cp' : ℝ)) * (4 * (C * A) + 20 + Kst)
              * (angleBracket l : ℝ) := by ring
    have hXl_leA : Xl * δ ^ (1 / 4 : ℝ)
        ≤ (2 * (1 + (Cp : ℝ)) * (1 + (Cp' : ℝ)) * (4 * (C * A) + 20 + Kst))
          * (2 : ℝ) ^ (-(c * (l : ℝ))) := by
      calc Xl * δ ^ (1 / 4 : ℝ)
          ≤ (2 * (1 + (Cp : ℝ)) * (1 + (Cp' : ℝ)) * (4 * (C * A) + 20 + Kst)
              * (angleBracket l : ℝ)) * δ ^ (1 / 4 : ℝ) :=
            mul_le_mul_of_nonneg_right hXlbound (by positivity)
        _ = (2 * (1 + (Cp : ℝ)) * (1 + (Cp' : ℝ)) * (4 * (C * A) + 20 + Kst))
              * ((angleBracket l : ℝ) * δ ^ (1 / 4 : ℝ)) := by rw [mul_assoc]
        _ ≤ (2 * (1 + (Cp : ℝ)) * (1 + (Cp' : ℝ)) * (4 * (C * A) + 20 + Kst))
              * (2 : ℝ) ^ (-(c * (l : ℝ))) :=
            mul_le_mul_of_nonneg_left hangle_delta (by positivity)
    have hreal : Xl * δ ^ (1 / 4 : ℝ) * Nd ^ (1 / 2 : ℝ)
          + (1 + (C2 : ℝ) * (angleBracket l : ℝ)) * δ
        ≤ Cf * ((2 : ℝ) ^ (-(c * (l : ℝ))) * Nd ^ (1 / 2 : ℝ)) := by
      have hNd12 : (1 : ℝ) ≤ Nd ^ (1 / 2 : ℝ) := Real.one_le_rpow hNd1 (by norm_num)
      have h1 : Xl * δ ^ (1 / 4 : ℝ) * Nd ^ (1 / 2 : ℝ)
          ≤ (2 * (1 + (Cp : ℝ)) * (1 + (Cp' : ℝ)) * (4 * (C * A) + 20 + Kst)
              * (2 : ℝ) ^ (-(c * (l : ℝ)))) * Nd ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right hXl_leA (by positivity)
      have h2 : (1 + (C2 : ℝ) * (angleBracket l : ℝ)) * δ
          ≤ ((1 + (C2 : ℝ)) * (2 : ℝ) ^ (-(c * (l : ℝ)))) * Nd ^ (1 / 2 : ℝ) := by
        have h2a : (1 + (C2 : ℝ) * (angleBracket l : ℝ)) ≤ (1 + (C2 : ℝ)) * (angleBracket l : ℝ) := by
          have hbl := angleBracket_coe_le_oneA l
          nlinarith only [hbl]
        have h2b : (1 + (C2 : ℝ)) * (angleBracket l : ℝ) * δ ≤ (1 + (C2 : ℝ)) * (2 : ℝ) ^ (-(c * (l : ℝ))) := by
          calc (1 + (C2 : ℝ)) * (angleBracket l : ℝ) * δ
              = (1 + (C2 : ℝ)) * ((angleBracket l : ℝ) * δ) := by ring
            _ ≤ (1 + (C2 : ℝ)) * (2 : ℝ) ^ (-(c * (l : ℝ))) :=
                mul_le_mul_of_nonneg_left hangle_delta2 (by linarith [hC2pos.le])
        have h2c : (1 + (C2 : ℝ)) * (2 : ℝ) ^ (-(c * (l : ℝ)))
            ≤ ((1 + (C2 : ℝ)) * (2 : ℝ) ^ (-(c * (l : ℝ)))) * Nd ^ (1 / 2 : ℝ) :=
          le_mul_of_one_le_right (by positivity) hNd12
        calc (1 + (C2 : ℝ) * (angleBracket l : ℝ)) * δ
            ≤ (1 + (C2 : ℝ)) * (angleBracket l : ℝ) * δ :=
              mul_le_mul_of_nonneg_right h2a hδpos.le
          _ ≤ (1 + (C2 : ℝ)) * (2 : ℝ) ^ (-(c * (l : ℝ))) := h2b
          _ ≤ ((1 + (C2 : ℝ)) * (2 : ℝ) ^ (-(c * (l : ℝ)))) * Nd ^ (1 / 2 : ℝ) := h2c
      calc Xl * δ ^ (1 / 4 : ℝ) * Nd ^ (1 / 2 : ℝ) + (1 + (C2 : ℝ) * (angleBracket l : ℝ)) * δ
          ≤ (2 * (1 + (Cp : ℝ)) * (1 + (Cp' : ℝ)) * (4 * (C * A) + 20 + Kst)
              * (2 : ℝ) ^ (-(c * (l : ℝ)))) * Nd ^ (1 / 2 : ℝ)
            + ((1 + (C2 : ℝ)) * (2 : ℝ) ^ (-(c * (l : ℝ)))) * Nd ^ (1 / 2 : ℝ) := add_le_add h1 h2
        _ = (2 * (1 + (Cp : ℝ)) * (1 + (Cp' : ℝ)) * (4 * (C * A) + 20 + Kst)
              + (1 + (C2 : ℝ))) * ((2 : ℝ) ^ (-(c * (l : ℝ))) * Nd ^ (1 / 2 : ℝ)) := by ring
        _ ≤ Cf * ((2 : ℝ) ^ (-(c * (l : ℝ))) * Nd ^ (1 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_right hCffinal (by positivity)
    have hgoal : eLpNorm (fun x : ℤ => AhalfTranspose N P h g x
          - kmtProj ρ l k (fun x : ℤ => AhalfTranspose N P h g x) x) 2 Measure.count
        ≤ ENNReal.ofReal (Cf * ((2 : ℝ) ^ (-(c * (l : ℝ))) * Nd ^ (1 / 2 : ℝ))) := by
      rw [hdiff]
      refine (eLpNorm_add_le (f := fun x : ℤ => E₁ x - kmtProj ρ l k (fun y : ℤ => E₁ y) x)
        (g := fun x : ℤ => E₂ x - kmtProj ρ l k (fun y : ℤ => E₂ y) x) (by norm_num)).trans ?_
      refine (add_le_add hE1part hE2part).trans ?_
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      exact ENNReal.ofReal_le_ofReal hreal
    simpa only [hNddef] using hgoal


end Work.KMTAreas.A4
