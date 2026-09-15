import Submission.Work.RelSzem2
import Submission.Work.KvnStruct2
import Submission.Commons.NumberTheory.Sieve.KPseudorandom_data
import Submission.Commons.NumberTheory.Sieve.corrCond_finset_moment
import Submission.Commons.NumberTheory.Sieve.Unorm_sub_one_le_of_KPseudorandom

set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Green–Tao Theorem 3.5 from `k`-pseudorandomness: the composition

Combining the unconditional structure theorem `GTTrans.exists_kvn_structure`
(`Submission/Work/KvnStruct2.lean`) with the assembly
`GTTrans.relative_szemeredi_of_structure` (`Submission/Work/RelSzem2.lean`) yields Green–Tao
Theorem 3.5 (Szemerédi relative to a pseudorandom measure) for large primes, with all constants
allowed to depend on the data.
-/

open Finset
open scoped BigOperators
open Commons.Combinatorics.Transference
open Commons.Combinatorics.Additive.Szemeredi
open FinSigma

namespace GTTrans

variable {p : ℕ} [Fact p.Prime]

/-- **Green–Tao Theorem 3.5 (relative Szemerédi) for a `k`-pseudorandom measure**, for primes
`p` above an explicit (data-dependent) threshold. -/
theorem relative_szemeredi_of_pseudorandom {k : ℕ} (hk : 3 ≤ k) (hkp : k ≤ p)
    {C : ℝ} (hC : 5 ≤ C) {gr : ℝ} (hgr : 0 < gr)
    (ν f : ZMod p → ℝ) (hν0 : ∀ x, 0 ≤ ν x) (hf0 : ∀ x, 0 ≤ f x) (hfν : ∀ x, f x ≤ ν x)
    {C₀ : ℕ → ℕ → ℝ} {εp δ δd cd : ℝ} (hP : KPseudorandom p k ν C₀ εp) (hεp : 0 ≤ εp)
    (hδ : 0 < δ) (hdens : δ * (p : ℝ) ≤ ∑ x, f x) (hδd : 0 < δd) (hcd : 0 < cd)
    {P₀ : ℕ}
    (hDense : ∀ (q : ℕ) [NeZero q], Nat.Prime q → P₀ ≤ q → ∀ g : ZMod q → ℝ,
      (∀ x, 0 ≤ g x) → (∀ x, g x ≤ 1) → δd * (q : ℝ) ≤ ∑ x, g x →
      cd * (q : ℝ) ^ 2 ≤ ∑ x : ZMod q, ∑ r : ZMod q,
        ∏ j ∈ Finset.range k, g (x + (j : ZMod q) * r))
    (hP₀ : P₀ ≤ p) (hδδd : 4 * δd * 3 ≤ δ) :
    ∃ (N₀ : ℕ) (εp₀ : ℝ), 0 < εp₀ ∧ εp₀ ≤ 1 ∧
      (N₀ ≤ p → εp ≤ εp₀ →
          ((1 + 2) ^ k * cd
            - ((2 : ℝ) ^ k - 1) * ((1 + 2) ^ k
                * ((16 * (2:ℝ)^k) * (gr ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹) / (1 + 2)
                    + εp ^ (((2^k : ℕ) : ℝ))⁻¹)))) * (p : ℝ) ^ 2
            ≤ ∑ x : ZMod p, ∑ r : ZMod p, ∏ i : Fin k, f (x + ((i : ℕ) : ZMod p) * r)) := by
  classical
  have hν : ∀ x, 0 ≤ ν x := hν0
  -- the level-set resolution and the exceptional-mass target
  set ε : ℝ := gr / (36 * (2 * C) ^ (2 ^ (k - 1) - 1)) with hε
  have hCpos : (0 : ℝ) < C := by linarith
  have hdenpos : (0 : ℝ) < 36 * (2 * C) ^ (2 ^ (k - 1) - 1) := by positivity
  have hεpos : 0 < ε := div_pos hgr hdenpos
  have hεgr : 9 * (2 * C) ^ (2 ^ (k - 1) - 1) * ε ≤ gr / 4 := by
    rw [hε]
    have hWpos : (0 : ℝ) < (2 * C) ^ (2 ^ (k - 1) - 1) := by positivity
    have hval : 9 * (2 * C) ^ (2 ^ (k - 1) - 1)
        * (gr / (36 * (2 * C) ^ (2 ^ (k - 1) - 1))) = gr / 4 := by
      field_simp
      ring
    rw [hval]
  set ρtgt : ℝ := 3 * δ / 4 with hρtgtdef
  have hρtgt : 0 < ρtgt := by rw [hρtgtdef]; linarith
  -- the moment bound extracted from `C₀`
  set CmB : ℕ → ℝ := fun q => (((2 ^ (k - 1) - 1 : ℕ)) : ℝ) ^ (q - 1)
    * ∑ m : {m : ℕ // m ∈ Finset.Icc 2 (2 ^ (k - 1))}, max (C₀ m.1 q) 0 with hCmB
  obtain ⟨η, η', εp₀, N₀, hηpos, hη1, hη'pos, hεp₀0, hεp₀1, hstruct⟩ :=
    exists_kvn_structure hk hC hεpos hgr hεgr CmB ρtgt hρtgt
  refine ⟨N₀, εp₀, hεp₀0, hεp₀1, ?_⟩
  intro hN₀ hεple
  -- the correlation data with the explicit moment bound
  have hd : 1 ≤ k - 1 := by omega
  have hcorr := Commons.NumberTheory.Sieve.corrCond_finset_moment (p := p) (d := k - 1) hd hP.2
  have hLFC : ∀ A : Finset (Fin (k - 1) → Bool),
      A ⊆ Finset.univ.erase (0 : Fin (k - 1) → Bool) → A.Nonempty → ∀ b : ZMod p,
      |((Fintype.card (Fin (k - 1) → ZMod p) : ℝ))⁻¹ *
        (∑ h : Fin (k - 1) → ZMod p,
          ∏ ω ∈ A, ν (b + ∑ j : Fin (k - 1), (if ω j then (1 : ZMod p) else 0) * h j)) - 1|
        ≤ εp := by
    intro A hA hne b
    exact pseudo_cube_lfc (by omega : 2 ≤ k) hP A hne (fun h0 => by
      have h1 := hA h0
      simp at h1) b
  have hmean : |((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x, ν x - 1| ≤ εp :=
    Commons.NumberTheory.Sieve.KPseudorandom_mean (by omega) hP
  have hUnorm : Unorm (k - 1) (fun x => ν x - 1)
      ≤ 2 * εp ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹) :=
    Commons.NumberTheory.Sieve.Unorm_sub_one_le_of_KPseudorandom (p := p) (k := k) (by omega) hP
  -- unpack the correlation condition (with the explicit moment bound)
  obtain ⟨τw, hτw0, hτmom, hτcorr⟩ := hcorr
  obtain ⟨ρs, c, K₀, hρs0, hc0, hρsle, hsmall, s, hInv, hsn, hterm⟩ :=
    hstruct p hN₀ hkp ν f τw εp hν hf0 hfν hτw0
      (fun q hq => hτmom q hq) hτcorr hmean hLFC hUnorm hεp hεple
  -- the structure data
  obtain ⟨hBmem, hBeq, hΩsat, hρsdata, hcE, hGbound, hα0, hαε, hTmass, hTcov⟩ := hInv
  obtain ⟨hρs0', hsρ, hΩmass⟩ := hρsdata
  have hmass : ∑ x ∈ s.Ω, (ν x + 1) ≤ ρtgt * (p : ℝ) := by
    have h1 : s.ρ ≤ ((s.n : ℝ) + 1) * ρs := hsρ
    have h2 : ((s.n : ℝ) + 1) ≤ (K₀ : ℝ) + 1 := by
      have : s.n + 1 ≤ K₀ + 1 := by omega
      exact_mod_cast this
    have h3 : ((s.n : ℝ) + 1) * ρs ≤ ((K₀ : ℝ) + 1) * ρs :=
      mul_le_mul_of_nonneg_right h2 hρs0.le
    calc ∑ x ∈ s.Ω, (ν x + 1) ≤ s.ρ := hΩmass
      _ ≤ ((s.n : ℝ) + 1) * ρs := h1
      _ ≤ ((K₀ : ℝ) + 1) * ρs := h3
      _ ≤ ρtgt * (Fintype.card (ZMod p) : ℝ) := hρsle
      _ = ρtgt * (p : ℝ) := by rw [ZMod.card]
  have hres : Unorm (k - 1) (fun x => if x ∈ s.Ω then 0 else f x - cE (KvnSt.B (k - 1) C ε s) f x)
      ≤ gr ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹) := by
    have h1 : Unorm (k - 1) (KvnSt.residual f (k - 1) C ε s) ^ (2 ^ (k - 1)) ≤ gr := hterm
    have h2 : (0 : ℝ) ≤ Unorm (k - 1) (KvnSt.residual f (k - 1) C ε s) :=
      Unorm_nonneg (k - 1) hd _
    have hgrn : (0 : ℝ) ≤ gr := le_of_lt hgr
    calc Unorm (k - 1) (fun x => if x ∈ s.Ω then 0 else f x - cE (KvnSt.B (k - 1) C ε s) f x)
        = Unorm (k - 1) (KvnSt.residual f (k - 1) C ε s) := rfl
      _ = (Unorm (k - 1) (KvnSt.residual f (k - 1) C ε s) ^ (2 ^ (k - 1)))
            ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹) := by
          rw [← Real.rpow_natCast (Unorm (k - 1) (KvnSt.residual f (k - 1) C ε s)) (2 ^ (k - 1))]
          rw [← Real.rpow_mul h2]
          rw [mul_inv_cancel₀ (by positivity : (((2 ^ (k - 1) : ℕ)) : ℝ) ≠ 0), Real.rpow_one]
      _ ≤ gr ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹) :=
          Real.rpow_le_rpow (pow_nonneg h2 _) h1 (inv_nonneg.mpr (Nat.cast_nonneg _))
  exact relative_szemeredi_of_structure (p := p) hk hkp (KvnSt.B (k - 1) C ε s) hBmem hBeq s.Ω
      hΩsat ν f hν0 hf0 hfν (C₀ := C₀) (εp := εp) (δ := δ) (τ := 2)
      (γ := gr ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹))
      (ρ := ρtgt * (p : ℝ)) (δd := δd) (cd := cd)
      hP hεp (le_trans hεple hεp₀1) hδ (by norm_num) hmass hcE hres hdens
      (by rw [hρtgtdef]; nlinarith [hδ])
      hδd hcd hDense hP₀ (by linarith [hδδd] : 4 * δd * (1 + 2) ≤ δ)

/-- The error budget of the relative Szemerédi theorem: the largest value of
`(16·2^k)·(γ/(1+τ) + ε^{2^{-k}})` for which the assembly still produces the sharp count
`cd·p² ≤ APcount`.  It is the solution of `(2^k-1)·3^k·T = (3^k-1)·cd`. -/
noncomputable def relSzemBudget (k : ℕ) (cd : ℝ) : ℝ :=
  (((3 : ℝ) ^ k - 1) * cd) / (((2 : ℝ) ^ k - 1) * (3 : ℝ) ^ k)

/-- **Relative Szemerédi in sharp form.**  Under the same hypotheses as
`relative_szemeredi_of_pseudorandom`, if in addition the Gowers-uniformity parameter `gr` is small
enough (`(16·2^k)·gr^{2^{-(k-1)}}/3 ≤ T/2` with `T = relSzemBudget k cd`), then the conclusion takes
the sharp form `cd·p² ≤ APcount f` with a `p`-independent constant `cd`. -/
theorem relative_szemeredi_of_pseudorandom_final {k : ℕ} (hk : 3 ≤ k) (hkp : k ≤ p)
    {C : ℝ} (hC : 5 ≤ C) {gr : ℝ} (hgr : 0 < gr)
    (ν f : ZMod p → ℝ) (hν0 : ∀ x, 0 ≤ ν x) (hf0 : ∀ x, 0 ≤ f x) (hfν : ∀ x, f x ≤ ν x)
    {C₀ : ℕ → ℕ → ℝ} {εp δ δd cd : ℝ}
    (hP : Commons.NumberTheory.Sieve.KPseudorandom p k ν C₀ εp) (hεp : 0 ≤ εp)
    (hδ : 0 < δ) (hdens : δ * (p : ℝ) ≤ ∑ x, f x) (hδd : 0 < δd) (hcd : 0 < cd) {P₀ : ℕ}
    (hDense : ∀ (q : ℕ) [NeZero q], Nat.Prime q → P₀ ≤ q → ∀ g : ZMod q → ℝ,
      (∀ x, 0 ≤ g x) → (∀ x, g x ≤ 1) → δd * (q : ℝ) ≤ ∑ x, g x →
      cd * (q : ℝ) ^ 2 ≤ ∑ x : ZMod q, ∑ r : ZMod q,
        ∏ j ∈ Finset.range k, g (x + (j : ZMod q) * r))
    (hP₀ : P₀ ≤ p) (hδδd : 4 * δd * 3 ≤ δ)
    (hgrT : (16 * (2:ℝ)^k) * (gr ^ (((2 ^ (k-1) : ℕ) : ℝ)⁻¹) / 3)
      ≤ relSzemBudget k cd / 2) :
    ∃ (N₀ : ℕ) (εp₀ : ℝ), 0 < εp₀ ∧ εp₀ ≤ 1 ∧
      (N₀ ≤ p → εp ≤ εp₀ → cd * (p : ℝ) ^ 2
        ≤ ∑ x : ZMod p, ∑ r : ZMod p, ∏ i : Fin k, f (x + ((i : ℕ) : ZMod p) * r)) := by
  classical
  obtain ⟨N₀, εp₀, hεp₀0, hεp₀1, hmain⟩ :=
    relative_szemeredi_of_pseudorandom (p := p) hk hkp hC hgr ν f hν0 hf0 hfν hP hεp hδ hdens
      hδd hcd hDense hP₀ hδδd
  set T : ℝ := relSzemBudget k cd with hT
  have h3k : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  have h2k1 : (0 : ℝ) < (2 : ℝ) ^ k - 1 := by
    have : (1 : ℝ) < (2 : ℝ) ^ k := one_lt_pow₀ (by norm_num) (by omega)
    linarith
  have h3k1 : (1 : ℝ) < (3 : ℝ) ^ k := one_lt_pow₀ (by norm_num) (by omega)
  have hTpos : 0 < T := by
    rw [hT, relSzemBudget]
    exact div_pos (by nlinarith [h3k1, hcd]) (by positivity)
  set εT : ℝ := (T / (2 * 16 * (2:ℝ)^k)) ^ (2^k : ℕ) with hεT
  have hden : (0 : ℝ) < 2 * 16 * (2:ℝ)^k := by positivity
  have hεT0 : 0 < εT := by rw [hεT]; positivity
  have hεTpow : εT ^ (((2^k : ℕ) : ℝ)⁻¹) = T / (2 * 16 * (2:ℝ)^k) := by
    rw [hεT, ← Real.rpow_natCast (T / (2 * 16 * (2:ℝ)^k)) (2^k),
      ← Real.rpow_mul (le_of_lt (div_pos hTpos hden))]
    rw [mul_inv_cancel₀ (by positivity : (((2^k : ℕ)) : ℝ) ≠ 0), Real.rpow_one]
  refine ⟨N₀, min εp₀ εT, lt_min hεp₀0 hεT0, le_trans (min_le_left _ _) hεp₀1, ?_⟩
  intro hN₀ hεple
  have h1 : εp ≤ εp₀ := le_trans hεple (min_le_left _ _)
  have h2 : εp ≤ εT := le_trans hεple (min_le_right _ _)
  have hb := hmain hN₀ h1
  -- the error term
  set X : ℝ := (16 * (2:ℝ)^k) * (gr ^ (((2 ^ (k-1) : ℕ) : ℝ)⁻¹) / (1 + 2)
    + εp ^ (((2^k : ℕ) : ℝ))⁻¹) with hX
  have hA0 : (0:ℝ) ≤ 16 * (2:ℝ)^k := by positivity
  have hpow_le : εp ^ (((2^k : ℕ) : ℝ)⁻¹) ≤ εT ^ (((2^k : ℕ) : ℝ)⁻¹) :=
    Real.rpow_le_rpow hεp h2 (by positivity)
  have herr2 : (16 * (2:ℝ)^k) * εp ^ (((2^k : ℕ) : ℝ)⁻¹) ≤ T / 2 := by
    have h := mul_le_mul_of_nonneg_left hpow_le hA0
    rw [hεTpow] at h
    have h' : 16 * (2:ℝ)^k * (T / (2 * 16 * (2:ℝ)^k)) = T / 2 := by
      field_simp
    linarith [h, h']
  have hXT : X ≤ T := by
    rw [hX, mul_add]
    have hgr' : (16 * (2:ℝ)^k) * (gr ^ (((2 ^ (k-1) : ℕ) : ℝ)⁻¹) / (1 + 2)) ≤ T / 2 := by
      rw [show gr ^ (((2 ^ (k-1) : ℕ) : ℝ)⁻¹) / (1 + 2)
          = gr ^ (((2 ^ (k-1) : ℕ) : ℝ)⁻¹) / 3 from by norm_num]
      exact hgrT
    linarith
  have hA : cd ≤ (1 + 2) ^ k * cd
      - ((2 : ℝ) ^ k - 1) * ((1 + 2) ^ k * X) := by
    have hkey : ((1 + 2 : ℝ)) ^ k = (3 : ℝ) ^ k := by norm_num
    rw [hkey]
    have hTval : (((2 : ℝ) ^ k - 1) * (3 : ℝ) ^ k) * T = ((3 : ℝ) ^ k - 1) * cd := by
      rw [hT, relSzemBudget]
      field_simp
    have hmono : ((2 : ℝ) ^ k - 1) * ((3 : ℝ) ^ k * X)
        ≤ (((2 : ℝ) ^ k - 1) * (3 : ℝ) ^ k) * T := by
      rw [show ((2 : ℝ) ^ k - 1) * ((3 : ℝ) ^ k * X)
          = (((2 : ℝ) ^ k - 1) * (3 : ℝ) ^ k) * X from by ring]
      exact mul_le_mul_of_nonneg_left hXT (by positivity)
    linarith [hmono, hTval]
  have hp2 : (0:ℝ) ≤ (p : ℝ) ^ 2 := by positivity
  calc cd * (p : ℝ) ^ 2
      ≤ ((1 + 2) ^ k * cd - ((2 : ℝ) ^ k - 1) * ((1 + 2) ^ k * X)) * (p : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hA hp2
    _ ≤ _ := hb


/-- **Green–Tao Theorem 3.5 (relative Szemerédi) in uniform form.**  The thresholds `N₀` and
`εp₀` are produced *before* the measure `ν`, the function `f` and the error `εp`: this is what the
pseudorandom-majorant assembly needs (the majorant's error is `o(1)` but the transference error
threshold is only known once the other data are fixed). -/
theorem relative_szemeredi_uniform {k : ℕ} (hk : 3 ≤ k)
    {C : ℝ} (hC : 5 ≤ C) {gr : ℝ} (hgr : 0 < gr)
    {C₀ : ℕ → ℕ → ℝ} {δ δd cd : ℝ}
    (hδ : 0 < δ) (hδd : 0 < δd) (hcd : 0 < cd) {P₀ : ℕ}
    (hDense : ∀ (q : ℕ) [NeZero q], Nat.Prime q → P₀ ≤ q → ∀ g : ZMod q → ℝ,
      (∀ x, 0 ≤ g x) → (∀ x, g x ≤ 1) → δd * (q : ℝ) ≤ ∑ x, g x →
      cd * (q : ℝ) ^ 2 ≤ ∑ x : ZMod q, ∑ r : ZMod q,
        ∏ j ∈ Finset.range k, g (x + (j : ZMod q) * r))
    (hδδd : 4 * δd * 3 ≤ δ) :
    ∃ (N₀ : ℕ) (εp₀ : ℝ), 0 < εp₀ ∧ εp₀ ≤ 1 ∧
      ∀ (p : ℕ) [Fact p.Prime], k ≤ p → N₀ ≤ p → P₀ ≤ p →
      ∀ (ν f : ZMod p → ℝ) (εp : ℝ),
        (∀ x, 0 ≤ ν x) → (∀ x, 0 ≤ f x) → (∀ x, f x ≤ ν x) →
        KPseudorandom p k ν C₀ εp → 0 ≤ εp → δ * (p : ℝ) ≤ ∑ x, f x → εp ≤ εp₀ →
          ((1 + 2) ^ k * cd
            - ((2 : ℝ) ^ k - 1) * ((1 + 2) ^ k
                * ((16 * (2:ℝ)^k) * (gr ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹) / (1 + 2)
                    + εp ^ (((2^k : ℕ) : ℝ))⁻¹)))) * (p : ℝ) ^ 2
            ≤ ∑ x : ZMod p, ∑ r : ZMod p, ∏ i : Fin k, f (x + ((i : ℕ) : ZMod p) * r) := by
  classical
  -- the level-set resolution and the exceptional-mass target
  set ε : ℝ := gr / (36 * (2 * C) ^ (2 ^ (k - 1) - 1)) with hε
  have hCpos : (0 : ℝ) < C := by linarith
  have hdenpos : (0 : ℝ) < 36 * (2 * C) ^ (2 ^ (k - 1) - 1) := by positivity
  have hεpos : 0 < ε := div_pos hgr hdenpos
  have hεgr : 9 * (2 * C) ^ (2 ^ (k - 1) - 1) * ε ≤ gr / 4 := by
    rw [hε]
    have hWpos : (0 : ℝ) < (2 * C) ^ (2 ^ (k - 1) - 1) := by positivity
    have hval : 9 * (2 * C) ^ (2 ^ (k - 1) - 1)
        * (gr / (36 * (2 * C) ^ (2 ^ (k - 1) - 1))) = gr / 4 := by
      field_simp
      ring
    rw [hval]
  set ρtgt : ℝ := 3 * δ / 4 with hρtgtdef
  have hρtgt : 0 < ρtgt := by rw [hρtgtdef]; linarith
  -- the moment bound extracted from `C₀`
  set CmB : ℕ → ℝ := fun q => (((2 ^ (k - 1) - 1 : ℕ)) : ℝ) ^ (q - 1)
    * ∑ m : {m : ℕ // m ∈ Finset.Icc 2 (2 ^ (k - 1))}, max (C₀ m.1 q) 0 with hCmB
  obtain ⟨η, η', εp₀, N₀, hηpos, hη1, hη'pos, hεp₀0, hεp₀1, hstruct⟩ :=
    exists_kvn_structure hk hC hεpos hgr hεgr CmB ρtgt hρtgt
  refine ⟨N₀, εp₀, hεp₀0, hεp₀1, ?_⟩
  intro p _ hkp hN₀ hP₀ ν f εp hν0 hf0 hfν hP hεp hdens hεple
  have hν : ∀ x, 0 ≤ ν x := hν0
  -- the correlation data with the explicit moment bound
  have hd : 1 ≤ k - 1 := by omega
  have hcorr := Commons.NumberTheory.Sieve.corrCond_finset_moment (p := p) (d := k - 1) hd hP.2
  have hLFC : ∀ A : Finset (Fin (k - 1) → Bool),
      A ⊆ Finset.univ.erase (0 : Fin (k - 1) → Bool) → A.Nonempty → ∀ b : ZMod p,
      |((Fintype.card (Fin (k - 1) → ZMod p) : ℝ))⁻¹ *
        (∑ h : Fin (k - 1) → ZMod p,
          ∏ ω ∈ A, ν (b + ∑ j : Fin (k - 1), (if ω j then (1 : ZMod p) else 0) * h j)) - 1|
        ≤ εp := by
    intro A hA hne b
    exact pseudo_cube_lfc (by omega : 2 ≤ k) hP A hne (fun h0 => by
      have h1 := hA h0
      simp at h1) b
  have hmean : |((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x, ν x - 1| ≤ εp :=
    Commons.NumberTheory.Sieve.KPseudorandom_mean (by omega) hP
  have hUnorm : Unorm (k - 1) (fun x => ν x - 1)
      ≤ 2 * εp ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹) :=
    Commons.NumberTheory.Sieve.Unorm_sub_one_le_of_KPseudorandom (p := p) (k := k) (by omega) hP
  -- unpack the correlation condition (with the explicit moment bound)
  obtain ⟨τw, hτw0, hτmom, hτcorr⟩ := hcorr
  obtain ⟨ρs, c, K₀, hρs0, hc0, hρsle, hsmall, s, hInv, hsn, hterm⟩ :=
    hstruct p hN₀ hkp ν f τw εp hν hf0 hfν hτw0
      (fun q hq => hτmom q hq) hτcorr hmean hLFC hUnorm hεp hεple
  -- the structure data
  obtain ⟨hBmem, hBeq, hΩsat, hρsdata, hcE, hGbound, hα0, hαε, hTmass, hTcov⟩ := hInv
  obtain ⟨hρs0', hsρ, hΩmass⟩ := hρsdata
  have hmass : ∑ x ∈ s.Ω, (ν x + 1) ≤ ρtgt * (p : ℝ) := by
    have h1 : s.ρ ≤ ((s.n : ℝ) + 1) * ρs := hsρ
    have h2 : ((s.n : ℝ) + 1) ≤ (K₀ : ℝ) + 1 := by
      have : s.n + 1 ≤ K₀ + 1 := by omega
      exact_mod_cast this
    have h3 : ((s.n : ℝ) + 1) * ρs ≤ ((K₀ : ℝ) + 1) * ρs :=
      mul_le_mul_of_nonneg_right h2 hρs0.le
    calc ∑ x ∈ s.Ω, (ν x + 1) ≤ s.ρ := hΩmass
      _ ≤ ((s.n : ℝ) + 1) * ρs := h1
      _ ≤ ((K₀ : ℝ) + 1) * ρs := h3
      _ ≤ ρtgt * (Fintype.card (ZMod p) : ℝ) := hρsle
      _ = ρtgt * (p : ℝ) := by rw [ZMod.card]
  have hres : Unorm (k - 1) (fun x => if x ∈ s.Ω then 0 else f x - cE (KvnSt.B (k - 1) C ε s) f x)
      ≤ gr ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹) := by
    have h1 : Unorm (k - 1) (KvnSt.residual f (k - 1) C ε s) ^ (2 ^ (k - 1)) ≤ gr := hterm
    have h2 : (0 : ℝ) ≤ Unorm (k - 1) (KvnSt.residual f (k - 1) C ε s) :=
      Unorm_nonneg (k - 1) hd _
    have hgrn : (0 : ℝ) ≤ gr := le_of_lt hgr
    calc Unorm (k - 1) (fun x => if x ∈ s.Ω then 0 else f x - cE (KvnSt.B (k - 1) C ε s) f x)
        = Unorm (k - 1) (KvnSt.residual f (k - 1) C ε s) := rfl
      _ = (Unorm (k - 1) (KvnSt.residual f (k - 1) C ε s) ^ (2 ^ (k - 1)))
            ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹) := by
          rw [← Real.rpow_natCast (Unorm (k - 1) (KvnSt.residual f (k - 1) C ε s)) (2 ^ (k - 1))]
          rw [← Real.rpow_mul h2]
          rw [mul_inv_cancel₀ (by positivity : (((2 ^ (k - 1) : ℕ)) : ℝ) ≠ 0), Real.rpow_one]
      _ ≤ gr ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹) :=
          Real.rpow_le_rpow (pow_nonneg h2 _) h1 (inv_nonneg.mpr (Nat.cast_nonneg _))
  exact relative_szemeredi_of_structure (p := p) hk hkp (KvnSt.B (k - 1) C ε s) hBmem hBeq s.Ω
      hΩsat ν f hν0 hf0 hfν (C₀ := C₀) (εp := εp) (δ := δ) (τ := 2)
      (γ := gr ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹))
      (ρ := ρtgt * (p : ℝ)) (δd := δd) (cd := cd)
      hP hεp (le_trans hεple hεp₀1) hδ (by norm_num) hmass hcE hres hdens
      (by rw [hρtgtdef]; nlinarith [hδ])
      hδd hcd hDense hP₀ (by linarith [hδδd] : 4 * δd * (1 + 2) ≤ δ)


/-- **Sharp uniform relative Szemerédi.** -/
theorem relative_szemeredi_uniform_final {k : ℕ} (hk : 3 ≤ k)
    {C : ℝ} (hC : 5 ≤ C) {gr : ℝ} (hgr : 0 < gr)
    {C₀ : ℕ → ℕ → ℝ} {δ δd cd : ℝ}
    (hδ : 0 < δ) (hδd : 0 < δd) (hcd : 0 < cd) {P₀ : ℕ}
    (hDense : ∀ (q : ℕ) [NeZero q], Nat.Prime q → P₀ ≤ q → ∀ g : ZMod q → ℝ,
      (∀ x, 0 ≤ g x) → (∀ x, g x ≤ 1) → δd * (q : ℝ) ≤ ∑ x, g x →
      cd * (q : ℝ) ^ 2 ≤ ∑ x : ZMod q, ∑ r : ZMod q,
        ∏ j ∈ Finset.range k, g (x + (j : ZMod q) * r))
    (hδδd : 4 * δd * 3 ≤ δ)
    (hgrT : (16 * (2:ℝ)^k) * (gr ^ (((2 ^ (k-1) : ℕ) : ℝ)⁻¹) / 3)
      ≤ relSzemBudget k cd / 2) :
    ∃ (N₀ : ℕ) (εp₀ : ℝ), 0 < εp₀ ∧ εp₀ ≤ 1 ∧
      ∀ (p : ℕ) [Fact p.Prime], k ≤ p → N₀ ≤ p → P₀ ≤ p →
      ∀ (ν f : ZMod p → ℝ) (εp : ℝ),
        (∀ x, 0 ≤ ν x) → (∀ x, 0 ≤ f x) → (∀ x, f x ≤ ν x) →
        KPseudorandom p k ν C₀ εp → 0 ≤ εp → δ * (p : ℝ) ≤ ∑ x, f x → εp ≤ εp₀ →
          cd * (p : ℝ) ^ 2
            ≤ ∑ x : ZMod p, ∑ r : ZMod p, ∏ i : Fin k, f (x + ((i : ℕ) : ZMod p) * r) := by
  classical
  obtain ⟨N₀, εp₀, hεp₀0, hεp₀1, hmain⟩ :=
    relative_szemeredi_uniform (k := k) hk hC hgr (C₀ := C₀) hδ hδd hcd hDense hδδd
  set T : ℝ := relSzemBudget k cd with hT
  have h3k : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  have h2k1 : (0 : ℝ) < (2 : ℝ) ^ k - 1 := by
    have : (1 : ℝ) < (2 : ℝ) ^ k := one_lt_pow₀ (by norm_num) (by omega)
    linarith
  have h3k1 : (1 : ℝ) < (3 : ℝ) ^ k := one_lt_pow₀ (by norm_num) (by omega)
  have hTpos : 0 < T := by
    rw [hT, relSzemBudget]
    exact div_pos (by nlinarith [h3k1, hcd]) (by positivity)
  set εT : ℝ := (T / (2 * 16 * (2:ℝ)^k)) ^ (2^k : ℕ) with hεT
  have hden : (0 : ℝ) < 2 * 16 * (2:ℝ)^k := by positivity
  have hεT0 : 0 < εT := by rw [hεT]; positivity
  have hεTpow : εT ^ (((2^k : ℕ) : ℝ)⁻¹) = T / (2 * 16 * (2:ℝ)^k) := by
    rw [hεT, ← Real.rpow_natCast (T / (2 * 16 * (2:ℝ)^k)) (2^k),
      ← Real.rpow_mul (le_of_lt (div_pos hTpos hden))]
    rw [mul_inv_cancel₀ (by positivity : (((2^k : ℕ)) : ℝ) ≠ 0), Real.rpow_one]
  refine ⟨N₀, min εp₀ εT, lt_min hεp₀0 hεT0, le_trans (min_le_left _ _) hεp₀1, ?_⟩
  intro p _ hkp hN₀ hP₀ ν f εp hν0 hf0 hfν hP hεp hdens hεple₀
  have h1 : εp ≤ εp₀ := le_trans hεple₀ (min_le_left _ _)
  have h2 : εp ≤ εT := le_trans hεple₀ (min_le_right _ _)
  have hb := hmain p hkp hN₀ hP₀ ν f εp hν0 hf0 hfν hP hεp hdens h1
  -- the error term
  set X : ℝ := (16 * (2:ℝ)^k) * (gr ^ (((2 ^ (k-1) : ℕ) : ℝ)⁻¹) / (1 + 2)
    + εp ^ (((2^k : ℕ) : ℝ))⁻¹) with hX
  have hA0 : (0:ℝ) ≤ 16 * (2:ℝ)^k := by positivity
  have hpow_le : εp ^ (((2^k : ℕ) : ℝ)⁻¹) ≤ εT ^ (((2^k : ℕ) : ℝ)⁻¹) :=
    Real.rpow_le_rpow hεp h2 (by positivity)
  have herr2 : (16 * (2:ℝ)^k) * εp ^ (((2^k : ℕ) : ℝ)⁻¹) ≤ T / 2 := by
    have h := mul_le_mul_of_nonneg_left hpow_le hA0
    rw [hεTpow] at h
    have h' : 16 * (2:ℝ)^k * (T / (2 * 16 * (2:ℝ)^k)) = T / 2 := by
      field_simp
    linarith [h, h']
  have hXT : X ≤ T := by
    rw [hX, mul_add]
    have hgr' : (16 * (2:ℝ)^k) * (gr ^ (((2 ^ (k-1) : ℕ) : ℝ)⁻¹) / (1 + 2)) ≤ T / 2 := by
      rw [show gr ^ (((2 ^ (k-1) : ℕ) : ℝ)⁻¹) / (1 + 2)
          = gr ^ (((2 ^ (k-1) : ℕ) : ℝ)⁻¹) / 3 from by norm_num]
      exact hgrT
    linarith
  have hA : cd ≤ (1 + 2) ^ k * cd
      - ((2 : ℝ) ^ k - 1) * ((1 + 2) ^ k * X) := by
    have hkey : ((1 + 2 : ℝ)) ^ k = (3 : ℝ) ^ k := by norm_num
    rw [hkey]
    have hTval : (((2 : ℝ) ^ k - 1) * (3 : ℝ) ^ k) * T = ((3 : ℝ) ^ k - 1) * cd := by
      rw [hT, relSzemBudget]
      field_simp
    have hmono : ((2 : ℝ) ^ k - 1) * ((3 : ℝ) ^ k * X)
        ≤ (((2 : ℝ) ^ k - 1) * (3 : ℝ) ^ k) * T := by
      rw [show ((2 : ℝ) ^ k - 1) * ((3 : ℝ) ^ k * X)
          = (((2 : ℝ) ^ k - 1) * (3 : ℝ) ^ k) * X from by ring]
      exact mul_le_mul_of_nonneg_left hXT (by positivity)
    linarith [hmono, hTval]
  have hp2 : (0:ℝ) ≤ (p : ℝ) ^ 2 := by positivity
  calc cd * (p : ℝ) ^ 2
      ≤ ((1 + 2) ^ k * cd - ((2 : ℝ) ^ k - 1) * ((1 + 2) ^ k * X)) * (p : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hA hp2
    _ ≤ _ := hb



end GTTrans
