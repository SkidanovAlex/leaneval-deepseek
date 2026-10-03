/-
# Corollary `struct-iii-second` from Proposition `propdual-second` (Krause--Mirek--Tao, §5.2)

This module proves the implication

  `PropdualSecondClaim P  ⟹  StructIiiSecondClaim P`

of §5.2: the `ℓ²` bound for `(1 - Π_{≤l,≤d(l-Log N)}) Ã_N^{**}(f,h)` for `1`-bounded `f`
(Proposition `propdual-second`) is upgraded to the same bound with `‖f‖_{ℓ²}` in place of the
`ℓ^∞` bound `N^{d/2}`, i.e. Corollary `struct-iii-second`.

## The argument

Fix `N`, `N₀ ~ N^d`, `l` and `f, h` supported in `[-N₀,N₀]` with `‖h‖_∞ ≤ 1` and `f ∈ ℓ²`.  The
operator `U f = (1 - Π_{≤l,≤d(l-Log N)}) Ã_N^{**}(f,h)` satisfies two estimates:

* (i) (from Proposition `propdual-second`) `‖U g‖_{ℓ²} ≤ A` for every `1`-bounded `g` supported in
  `[-N₀,N₀]`, with `A = C₀ 2^{-c₀l} N^{d/2}`;
* (ii) (from Lemma `iw-prop`(i) — area `A1` — and the `ℓ^p`-improving estimate `lp-improv` for the
  average `A_N^{P-X}`, i.e. area `A3`) `‖U g‖_{ℓ²} ≤ B ‖g‖_{ℓ^p}`, with
  `B = (1 + C₁⟨l⟩) C₃ N^{d(1/2 - 1/p)}` for some `1 < p < 2`;

and it is *linear on bounded functions* (`A5.kmtProj_add_bounded` / `A5.kmtProj_smul_bounded`).
Truncating `f` at the level `λ = t ‖f‖_{ℓ²}`, applying (i) to the low part and (ii) to the high
part, and using the elementary level-set bound `‖f 1_{|f|>λ}‖_{ℓ^p} ≤ λ^{1-2/p} ‖f‖_{ℓ²}^{2/p}`,
gives `‖U f‖_{ℓ²} ≤ (A t + B t^{1-2/p}) ‖f‖_{ℓ²}`, and the choice `t = (B/A)^{p/2}` turns this
into `2 A^{1-p/2} B^{p/2} ‖f‖_{ℓ²}`.  In that product the powers of `N` cancel exactly
(`(1/2)(1-p/2) + (1/2-1/p)(p/2) = 0`) and what remains is
`C₀^{1-p/2} C₃^{p/2} (1+C₁⟨l⟩)^{p/2} 2^{-c₀(1-p/2)l}`, which is at most a constant times
`2^{-cl}` for `c = c₀(1-p/2)/2 > 0`: the polynomial loss `⟨l⟩^{p/2}` is absorbed by the
exponential saving (the elementary estimate `Work.KMTAreas.A5.logbPowLeConstMulRpow`).

## Main result

* `Work.KMTAreas.A4Z.structIiiSecondClaim_of_propdualSecondClaim`.

## Auxiliary results (delegated, in `Submission/Work/KMTAreas/A4Z/`)

* `eLpNorm_two_le_of_interp_levelSet` (in `A4Z/interpLevelSet.lean`) — the two-endpoint truncation
  lemma for an operator `T` that is linear on bounded functions, with an `ℓ^∞ → ℓ²` and an
  `ℓ^p → ℓ²` endpoint; it uses `eLpNorm_levelSetHigh_le` (the level-set `ℓ^p` bound);
* `eLpNorm_sub_kmtProj_ahalfTransposeTwo_le` — estimate (ii) above, from areas `A1` and `A3`;
* `interp_rpow_prod_le` — the arithmetic bookkeeping `A^{1-p/2} B^{p/2} ≤ K 2^{-cl}`.
-/
import Mathlib
import Submission.Work.KMTAreas.A4Z.Defs
import Submission.Work.KMTAreas.A4Z.interpLevelSet
import Submission.Work.KMTAreas.A4Z.eLpNorm_sub_kmtProj_ahalfTransposeTwo_le
import Submission.Work.KMTAreas.A4Z.interp_rpow_prod_le
import Submission.Work.KMTAreas.A7.ProjBound

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger
open Work.Analysis.InverseTheory
open Work.Analysis.EndVar
open Work.KMTAreas.A5 (BoundedZ boundedZ_of_bound boundedZ_add boundedZ_smul boundedZ_sub boundedZ_zero
  kmtProj_add_bounded kmtProj_smul_bounded)

namespace Work.KMTAreas.A4Z

/-! ## Two elementary facts about `Ã_N^{**}` -/

/-- `Ã_N^{**}(g,h)` is bounded when `g` is bounded and `h` is `1`-bounded. -/
theorem boundedZ_ahalfTransposeTwo {N : ℕ} {P : Polynomial ℤ} {g h : ℤ → ℂ}
    (hg : BoundedZ g) (hh : ∀ x : ℤ, ‖h x‖ ≤ 1) :
    BoundedZ (fun x : ℤ => AhalfTranspose₂ N P g h x) := by
  obtain ⟨M, hM⟩ := hg
  set M' : ℝ := max 0 M with hM'def
  have hM'0 : (0 : ℝ) ≤ M' := le_max_left _ _
  have hM' : ∀ y : ℤ, ‖g y‖ ≤ M' := fun y => le_trans (hM y) (le_max_right _ _)
  refine boundedZ_of_bound (C := 2 * M') fun x => ?_
  have hsub : Finset.Ioc (N / 2) N ⊆ Finset.Icc 0 N := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    rw [Finset.mem_Icc]
    omega
  have hcard : (((Finset.Ioc (N / 2) N).card : ℝ)) ≤ (N : ℝ) + 1 := by
    have h := Finset.card_le_card hsub
    rw [Nat.card_Icc] at h
    calc ((Finset.Ioc (N / 2) N).card : ℝ) ≤ (((N + 1 - 0 : ℕ)) : ℝ) := by exact_mod_cast h
      _ = (N : ℝ) + 1 := by rw [Nat.sub_zero]; push_cast; ring
  have hterm : ∀ n ∈ Finset.Ioc (N / 2) N,
      ‖g (x + (n : ℤ) - P.eval (n : ℤ)) * h (x - P.eval (n : ℤ))‖ ≤ M' := by
    intro n _
    rw [norm_mul]
    exact (mul_le_mul (hM' _) (hh _) (norm_nonneg _) hM'0).trans_eq (mul_one _)
  have hsum : ‖∑ n ∈ Finset.Ioc (N / 2) N,
      g (x + (n : ℤ) - P.eval (n : ℤ)) * h (x - P.eval (n : ℤ))‖
      ≤ ((Finset.Ioc (N / 2) N).card : ℝ) * M' :=
    (norm_sum_le_of_le _ hterm).trans (le_of_eq (by rw [Finset.sum_const, nsmul_eq_mul]))
  have hinv : (N : ℝ)⁻¹ * ((Finset.Ioc (N / 2) N).card : ℝ) ≤ 2 := by
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; simp
    · have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have h2 : (N : ℝ)⁻¹ * ((N : ℝ) + 1) ≤ 2 := by
        rw [inv_mul_eq_div, div_le_iff₀ hN0]
        linarith
      exact (mul_le_mul_of_nonneg_left hcard (by positivity)).trans h2
  rw [AhalfTranspose₂, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  calc (N : ℝ)⁻¹ * ‖∑ n ∈ Finset.Ioc (N / 2) N,
        g (x + (n : ℤ) - P.eval (n : ℤ)) * h (x - P.eval (n : ℤ))‖
      ≤ (N : ℝ)⁻¹ * (((Finset.Ioc (N / 2) N).card : ℝ) * M') :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ((N : ℝ)⁻¹ * ((Finset.Ioc (N / 2) N).card : ℝ)) * M' := by ring
    _ ≤ 2 * M' := mul_le_mul_of_nonneg_right hinv hM'0

/-- Additivity of `Ã_N^{**(·,h)}` in its first argument. -/
theorem ahalfTransposeTwo_add (N : ℕ) (P : Polynomial ℤ) (f g h : ℤ → ℂ) :
    AhalfTranspose₂ N P (f + g) h = AhalfTranspose₂ N P f h + AhalfTranspose₂ N P g h := by
  funext x
  simp only [AhalfTranspose₂, Pi.add_apply, add_mul, mul_add, Finset.mul_sum,
    Finset.sum_add_distrib]

/-- Homogeneity of `Ã_N^{**(·,h)}`. -/
theorem ahalfTransposeTwo_smul (N : ℕ) (P : Polynomial ℤ) (c : ℂ) (f h : ℤ → ℂ) :
    AhalfTranspose₂ N P (c • f) h = c • AhalfTranspose₂ N P f h := by
  funext x
  simp only [AhalfTranspose₂, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-! ## The main theorem -/

/-- **Corollary `struct-iii-second` from Proposition `propdual-second`.**  If the `(1 - Π_{≤l,≤k})`
`ℓ²` bound of Proposition `propdual-second` holds (with its `N^{d/2}` right-hand side), and the
`ℓ^p`-improving estimate of area `A3` holds for `P - X`, then the same bound holds with
`‖f‖_{ℓ²}` in place of `N^{d/2}` (Corollary `struct-iii-second`).

`hA1` (the Ionescu--Wainger multiplier theorem) is used only through the boundedness of the
projections `kmtProj ρ l k` on `ℓ²` (`Work.KMTAreas.A7.kmtProj_lp_bound_holds`). -/
theorem structIiiSecondClaim_of_propdualSecondClaim (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (hA3 : Work.KMTContract.PolyImproving (P - Polynomial.X))
    (h : Work.KMTAreas.A4Z.PropdualSecondClaim P) :
    Work.KMTAreas.A4Z.StructIiiSecondClaim P := by
  obtain ⟨c₀, hc₀, hmain⟩ := h
  obtain ⟨p, hp1, hp2, C₃, hC₃, hA3b⟩ := hA3
  have hC₃R : (0 : ℝ) < (C₃ : ℝ) := by exact_mod_cast hC₃
  have hXdeg : (Polynomial.X : ℤ[X]).natDegree < P.natDegree := by
    rw [Polynomial.natDegree_X]; omega
  have hdeg : (P - Polynomial.X).natDegree = P.natDegree :=
    Polynomial.natDegree_sub_eq_left_of_natDegree_lt hXdeg
  have hexpr : ((P - Polynomial.X).natDegree : ℝ) * (1 / 2 - 1 / p)
      = (P.natDegree : ℝ) * (1 / 2 - 1 / p) := by rw [hdeg]
  have hA3gen : ∀ (N : ℕ) (u : ℤ → ℂ), 1 ≤ N →
      eLpNorm (fun x : ℤ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N,
          u (x - (P - Polynomial.X).eval (n : ℤ))) 2 Measure.count
        ≤ ENNReal.ofReal (C₃ : ℝ)
            * ENNReal.ofReal ((N : ℝ) ^ ((P.natDegree : ℝ) * (1 / 2 - 1 / p)))
            * eLpNorm u (ENNReal.ofReal p) Measure.count := by
    intro N u hN
    have h := hA3b N u hN
    rw [← ENNReal.ofReal_coe_nnreal (p := C₃), hexpr] at h
    exact h
  refine ⟨c₀ * (1 - p / 2) / 2, by nlinarith, fun ρ hρ0 hρ1 => ?_⟩
  obtain ⟨Cρ₀, hCρ₀, C₀, hC₀, hprop⟩ := hmain ρ hρ0 hρ1
  obtain ⟨Cρ₁, hCρ₁, C₁, hC₁, hproj⟩ :=
    Work.KMTAreas.A7.kmtProj_lp_bound_holds hA1 ρ hρ0 hρ1 2 (by norm_num)
  have hC₀R : (0 : ℝ) < (C₀ : ℝ) := by exact_mod_cast hC₀
  have hC₁R : (0 : ℝ) ≤ (C₁ : ℝ) := by positivity
  obtain ⟨K, hKpos, hKbound⟩ := interp_rpow_prod_le hc₀ hp1 hp2 hC₀R hC₁R hC₃R
  refine ⟨max Cρ₀ Cρ₁, lt_of_lt_of_le hCρ₀ (le_max_left _ _), Real.toNNReal (2 * K), ?_, ?_⟩
  · rw [Real.toNNReal_pos]; linarith
  intro N N₀ l f h₂ hN hN₀lo hN₀hi hfs hhs hfM hh1 harc
  set A : ℝ := (C₀ : ℝ) * ((2 : ℝ) ^ (-(c₀ * (l : ℝ))) * ((N : ℝ) ^ P.natDegree) ^ (1 / 2 : ℝ))
    with hAdef
  set B : ℝ := (1 + (C₁ : ℝ) * (Work.Analysis.IWMultiplier.angleBracket l : ℝ)) * (C₃ : ℝ)
    * ((N : ℝ) ^ P.natDegree) ^ (1 / 2 - 1 / p) with hBdef
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hApos : 0 < A := by
    rw [hAdef]
    exact mul_pos hC₀R (mul_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
      (Real.rpow_pos_of_pos (pow_pos hNpos _) _))
  have hBpos : 0 < B := by
    rw [hBdef]
    refine mul_pos (mul_pos ?_ hC₃R) (Real.rpow_pos_of_pos (pow_pos hNpos _) _)
    have : (0 : ℝ) ≤ (C₁ : ℝ) * (Work.Analysis.IWMultiplier.angleBracket l : ℝ) :=
      mul_nonneg hC₁R (by positivity)
    linarith
  -- the good-arc condition at `max Cρ₀ Cρ₁` implies it at both smaller constants
  have harc_mono : ∀ {Cρ Cρ' : ℝ}, Cρ ≤ Cρ' →
      GoodMajorArcs ρ Cρ' l ((P.natDegree : ℤ) * ((l : ℤ) - logN N)) →
      GoodMajorArcs ρ Cρ l ((P.natDegree : ℤ) * ((l : ℤ) - logN N)) := by
    intro Cρ Cρ' hle hgood
    show (((P.natDegree : ℤ) * ((l : ℤ) - logN N) : ℤ) : ℝ)
      ≤ -Cρ * (2 : ℝ) ^ (ρ * (l : ℝ))
    have hgood' : (((P.natDegree : ℤ) * ((l : ℤ) - logN N) : ℤ) : ℝ)
        ≤ -Cρ' * (2 : ℝ) ^ (ρ * (l : ℝ)) := hgood
    have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (ρ * (l : ℝ)) := Real.rpow_nonneg (by norm_num) _
    have h3 : -Cρ' * (2 : ℝ) ^ (ρ * (l : ℝ)) ≤ -Cρ * (2 : ℝ) ^ (ρ * (l : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith) h2
    exact le_trans hgood' h3
  have harc₀ := harc_mono (le_max_left Cρ₀ Cρ₁) harc
  have harc₁ := harc_mono (le_max_right Cρ₀ Cρ₁) harc
  have hbdd : BoundedZ f := by
    obtain ⟨M, hM⟩ := Work.KMTContract.bound_of_memLp_count (p := 2) (by norm_num) hfM
    exact boundedZ_of_bound fun x => hM x
  have hmulNat : (N : ℝ) ^ ((P.natDegree : ℝ) * (1 / 2 - 1 / p))
      = ((N : ℝ) ^ P.natDegree) ^ (1 / 2 - 1 / p) := by
    rw [Real.rpow_mul (x := (N : ℝ)) (by positivity) (P.natDegree : ℝ) (1 / 2 - 1 / p),
      Real.rpow_natCast]
  -- the two hypotheses of the interpolation
  have h1inst : ∀ g : ℤ → ℂ, SupportIn g N₀ → (∀ x : ℤ, ‖g x‖ ≤ 1) →
      eLpNorm (fun x : ℤ => AhalfTranspose₂ N P g h₂ x
        - Work.KMTContract.kmtProj ρ l ((P.natDegree : ℤ) * ((l : ℤ) - logN N))
            (fun y : ℤ => AhalfTranspose₂ N P g h₂ y) x) 2 Measure.count
      ≤ ENNReal.ofReal A := by
    intro g hgs hgb
    have h := hprop N N₀ l g h₂ hN hN₀lo hN₀hi hgs hhs hgb hh1 harc₀
    have hAeq : (C₀ : ℝ≥0∞) * ENNReal.ofReal
        ((2 : ℝ) ^ (-(c₀ * (l : ℝ))) * ((N : ℝ) ^ P.natDegree) ^ (1 / 2 : ℝ))
        = ENNReal.ofReal A := by
      rw [hAdef, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (le_of_lt hC₀R)]
    rw [hAeq] at h
    exact h
  have h2inst : ∀ g : ℤ → ℂ, BoundedZ g →
      eLpNorm (fun x : ℤ => AhalfTranspose₂ N P g h₂ x
        - Work.KMTContract.kmtProj ρ l ((P.natDegree : ℤ) * ((l : ℤ) - logN N))
            (fun y : ℤ => AhalfTranspose₂ N P g h₂ y) x) 2 Measure.count
      ≤ ENNReal.ofReal B * eLpNorm g (ENNReal.ofReal p) Measure.count := by
    intro g hg
    have hproj_g := hproj l _ harc₁ (fun y : ℤ => AhalfTranspose₂ N P g h₂ y)
    rw [show ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) by norm_num] at hproj_g
    have h := eLpNorm_sub_kmtProj_ahalfTransposeTwo_le P hP hp1 hp2 hC₃R hA3gen hN hg hh1
      hC₁R hproj_g
    rw [hmulNat] at h
    exact h
  -- the linearity hypotheses
  have hadd : ∀ f g : ℤ → ℂ, BoundedZ f → BoundedZ g →
      (fun x : ℤ => AhalfTranspose₂ N P (f + g) h₂ x
        - Work.KMTContract.kmtProj ρ l ((P.natDegree : ℤ) * ((l : ℤ) - logN N))
            (fun y : ℤ => AhalfTranspose₂ N P (f + g) h₂ y) x)
      = (fun x : ℤ => AhalfTranspose₂ N P f h₂ x
          - Work.KMTContract.kmtProj ρ l ((P.natDegree : ℤ) * ((l : ℤ) - logN N))
              (fun y : ℤ => AhalfTranspose₂ N P f h₂ y) x)
        + (fun x : ℤ => AhalfTranspose₂ N P g h₂ x
          - Work.KMTContract.kmtProj ρ l ((P.natDegree : ℤ) * ((l : ℤ) - logN N))
              (fun y : ℤ => AhalfTranspose₂ N P g h₂ y) x) := by
    intro f g hf hg
    have hbf : BoundedZ (fun y : ℤ => AhalfTranspose₂ N P f h₂ y) :=
      boundedZ_ahalfTransposeTwo hf hh1
    have hbg : BoundedZ (fun y : ℤ => AhalfTranspose₂ N P g h₂ y) :=
      boundedZ_ahalfTransposeTwo hg hh1
    funext x
    rw [show AhalfTranspose₂ N P (f + g) h₂ x
          = AhalfTranspose₂ N P f h₂ x + AhalfTranspose₂ N P g h₂ x from
        congrFun (ahalfTransposeTwo_add N P f g h₂) x,
      show (fun y : ℤ => AhalfTranspose₂ N P (f + g) h₂ y)
          = (fun y : ℤ => AhalfTranspose₂ N P f h₂ y)
            + (fun y : ℤ => AhalfTranspose₂ N P g h₂ y) from ahalfTransposeTwo_add N P f g h₂,
      kmtProj_add_bounded ρ l ((P.natDegree : ℤ) * ((l : ℤ) - logN N)) hbf hbg]
    simp only [Pi.add_apply]
    ring
  have hsmul : ∀ (c : ℂ) (f : ℤ → ℂ), BoundedZ f →
      (fun x : ℤ => AhalfTranspose₂ N P (c • f) h₂ x
        - Work.KMTContract.kmtProj ρ l ((P.natDegree : ℤ) * ((l : ℤ) - logN N))
            (fun y : ℤ => AhalfTranspose₂ N P (c • f) h₂ y) x)
      = c • (fun x : ℤ => AhalfTranspose₂ N P f h₂ x
          - Work.KMTContract.kmtProj ρ l ((P.natDegree : ℤ) * ((l : ℤ) - logN N))
              (fun y : ℤ => AhalfTranspose₂ N P f h₂ y) x) := by
    intro c f hf
    have hbf : BoundedZ (fun y : ℤ => AhalfTranspose₂ N P f h₂ y) :=
      boundedZ_ahalfTransposeTwo hf hh1
    funext x
    rw [show AhalfTranspose₂ N P (c • f) h₂ x
          = c * AhalfTranspose₂ N P f h₂ x from
        congrFun (ahalfTransposeTwo_smul N P c f h₂) x,
      show (fun y : ℤ => AhalfTranspose₂ N P (c • f) h₂ y)
          = c • (fun y : ℤ => AhalfTranspose₂ N P f h₂ y) from ahalfTransposeTwo_smul N P c f h₂,
      kmtProj_smul_bounded ρ l ((P.natDegree : ℤ) * ((l : ℤ) - logN N)) c hbf]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hd1 := eLpNorm_two_le_of_interp_levelSet N₀ _ hadd hsmul hp1 hp2 hApos hBpos h1inst h2inst hfM hbdd hfs
  -- the arithmetic
  have hNd1 : (1 : ℝ) ≤ (N : ℝ) ^ P.natDegree :=
    one_le_pow₀ (by exact_mod_cast hN)
  have hKb := hKbound ((N : ℝ) ^ P.natDegree) hNd1 l
  have hKb' : A ^ (1 - p / 2) * B ^ (p / 2)
      ≤ K * (2 : ℝ) ^ (-((c₀ * (1 - p / 2) / 2) * (l : ℝ))) := hKb
  have hstep : 2 * A ^ (1 - p / 2) * B ^ (p / 2)
      ≤ (2 * K) * (2 : ℝ) ^ (-((c₀ * (1 - p / 2) / 2) * (l : ℝ))) := by
    have := mul_le_mul_of_nonneg_left hKb' (by norm_num : (0 : ℝ) ≤ 2)
    calc 2 * A ^ (1 - p / 2) * B ^ (p / 2)
        = 2 * (A ^ (1 - p / 2) * B ^ (p / 2)) := by ring
      _ ≤ 2 * (K * (2 : ℝ) ^ (-((c₀ * (1 - p / 2) / 2) * (l : ℝ)))) := this
      _ = (2 * K) * (2 : ℝ) ^ (-((c₀ * (1 - p / 2) / 2) * (l : ℝ))) := by ring
  have hcoe : (Real.toNNReal (2 * K) : ℝ≥0∞) = ENNReal.ofReal (2 * K) := by
    rw [← ENNReal.ofReal_coe_nnreal (p := Real.toNNReal (2 * K)),
      Real.coe_toNNReal _ (by linarith)]
  calc eLpNorm (fun x : ℤ => AhalfTranspose₂ N P f h₂ x
        - Work.KMTContract.kmtProj ρ l ((P.natDegree : ℤ) * ((l : ℤ) - logN N))
            (fun y : ℤ => AhalfTranspose₂ N P f h₂ y) x) 2 Measure.count
      ≤ ENNReal.ofReal (2 * A ^ (1 - p / 2) * B ^ (p / 2)) * eLpNorm f 2 Measure.count := hd1
    _ ≤ ENNReal.ofReal ((2 * K) * (2 : ℝ) ^ (-((c₀ * (1 - p / 2) / 2) * (l : ℝ))))
          * eLpNorm f 2 Measure.count := by
        gcongr
    _ = (Real.toNNReal (2 * K) : ℝ≥0∞)
          * ENNReal.ofReal ((2 : ℝ) ^ (-((c₀ * (1 - p / 2) / 2) * (l : ℝ))))
          * eLpNorm f 2 Measure.count := by
        rw [ENNReal.ofReal_mul (by linarith), hcoe]

end Work.KMTAreas.A4Z
