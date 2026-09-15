import Submission.Work.KvnFinal
import Submission.Work.KvnCount
import Submission.Commons.Combinatorics.Transference.card_image_kpart_le

set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Discharging the §7 smallness hypothesis: the arithmetic assembly

This file contains `kvn_small_of_ED`: given the Green-Tao data (pseudorandomness of `ν` in the
raw form produced by `KPseudorandom_data`), the caller-supplied quantitative Weierstrass data
`E, D`, the sup-norm/atom-count bounds `E₀max`, `Abnd`, and the four numeric conditions
`hεC, hρsC, hγC, hsC` (which are all uniform in the tower state `s`), the analytic smallness
hypothesis `KvnSt.small` of the Furstenberg tower holds at every invariant state with
`s.n < K₀` that has not terminated.
-/

open Finset
open scoped BigOperators
open Commons.Combinatorics.Transference
open FinSigma

namespace GTTrans

variable {p : ℕ} [Fact p.Prime]

/-- The uniform `(ν+1)`-atom-count bound of the tower: `(2⌈M/ε⌉+5)` with `M = 2^{2^{k-1}-1}·2`
(the sup-norm bound of `𝒟(F/(2C))` for `εp ≤ 1`). -/
noncomputable def KvnAbndU (k : ℕ) (ε : ℝ) : ℕ :=
  (2 * (⌈(2 : ℝ) ^ (2 ^ (k - 1) - 1) * 2 / ε⌉ + 2) + 1).toNat

/-- **The §7 arithmetic assembly.**  From the raw pseudorandomness data of `ν`, the
Weierstrass data `E, D`, the explicit `E₀max` and `Abnd`, and the four numeric conditions,
`KvnSt.small` holds at every invariant non-terminated state with `s.n < K₀`. -/
theorem kvn_small_of_ED {k : ℕ} (hk : 3 ≤ k) {C : ℝ} (hC : 5 ≤ C) {ε η : ℝ} (hε : 0 < ε)
    (hη : 0 < η) (hη1 : η ≤ 1 / 4)
    {ν f : ZMod p → ℝ} (hν : ∀ x, 0 ≤ ν x) (hf0 : ∀ x, 0 ≤ f x) (hfν : ∀ x, f x ≤ ν x)
    {εp εp₀ : ℝ} (hεp : 0 ≤ εp) (hεp₀ : εp ≤ εp₀) (hεp₀1 : εp₀ ≤ 1)
    {τ : ZMod p → ℝ} (hτ0 : ∀ x, 0 ≤ τ x) {Cm : ℕ → ℝ}
    (hmom : ∀ q : ℕ, 1 ≤ q →
      ((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x, (τ x) ^ q ≤ Cm q)
    (hcorr : ∀ (A : Finset (Fin (k - 1) → Bool)), 2 ≤ A.card → ∀ h : Fin (k - 1) → ZMod p,
      ((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ y : ZMod p,
          ∏ ω ∈ A, ν (y + ∑ i, (if ω i then h i else 0))
        ≤ ∑ ω ∈ A, ∑ ω' ∈ A.filter (fun ω' => ω ≠ ω'),
            τ ((∑ i, (if ω' i then h i else 0)) - (∑ i, (if ω i then h i else 0))))
    (hmean : |((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x, ν x - 1| ≤ εp)
    (hLFC : ∀ A : Finset (Fin (k - 1) → Bool), A ⊆ Finset.univ.erase (0 : Fin (k - 1) → Bool) →
      A.Nonempty → ∀ b : ZMod p,
      |((Fintype.card (Fin (k - 1) → ZMod p) : ℝ))⁻¹ *
        (∑ h : Fin (k - 1) → ZMod p,
          ∏ ω ∈ A, ν (b + ∑ j : Fin (k - 1), (if ω j then (1 : ZMod p) else 0) * h j)) - 1| ≤ εp)
    {η' : ℝ} (hη' : 0 < η') {ρs c gr : ℝ} (hgr : 0 < gr)
    {K₀ : ℕ} {E : ℝ} (hE : 0 ≤ E) {D : ℕ}
    (hpoly : ∀ (K' : ℕ) (hK' : K' ≤ K₀) (c : Fin K' → ℝ),
      (∀ j, |c j| ≤ (2 : ℝ) ^ (2 ^ (k - 1) - 1) * (1 + εp₀) + ε) →
      ∃ P : MvPolynomial (Fin K') ℝ,
        (∀ t ∈ Set.pi Set.univ (fun _ : Fin K' => Set.Icc (-((2 : ℝ) ^ (2 ^ (k - 1) - 1)
            * (1 + εp₀))) ((2 : ℝ) ^ (2 ^ (k - 1) - 1) * (1 + εp₀))),
          |∏ j, levelJoinPsi η ((t j - c j) / ε) - MvPolynomial.eval t P| ≤ η') ∧
        (∑ m ∈ P.support, |P.coeff m|) ≤ E ∧
        P.totalDegree ≤ D)
    (hUnorm : Unorm (k - 1) (fun x => ν x - 1) ≤ 2 * εp ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹))
    {E₀max : ℝ} (hE₀max0 : 0 ≤ E₀max)
    (hE₀le : E * (1 + (((2 ^ (k - 1) * 2 ^ (k - 1) : ℕ)) : ℝ) ^ D *
        ((6 : ℝ) ^ D * (∑ j ∈ Finset.range (D + 1), (if j = 0 then 1 else max (Cm j) 0))))
      ≤ E₀max)
    (hεC : 9 * (2 * C) ^ (2 ^ (k - 1) - 1) * ε ≤ gr / 4)
    (hρsC : (Fintype.card (ZMod p) : ℝ) *
        (2 * (2 * εp₀ ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹) * E₀max + 3 * η' + 27 * (K₀ : ℝ) ^ 2 * η))
        * (KvnAbndU k ε : ℝ) ^ K₀ + (KvnAbndU k ε : ℝ) ^ K₀ ≤ ρs)
    (hγC : (2 * C) ^ (2 ^ (k - 1) - 1) * (2 : ℝ) ^ (2 ^ (k - 1) - 1) * (1 + εp₀) *
        (4 * ((K₀ : ℝ) + 1)) * ρs ≤ (Fintype.card (ZMod p) : ℝ) * gr / 4)
    (hsC : (3 * 3 ^ 2 + 2 * 3) * ((K₀ : ℝ) + 1) * ρs + c ≤
        ((Fintype.card (ZMod p) : ℝ) * gr / 2) ^ 2 /
          ((Fintype.card (ZMod p) : ℝ)
            * ((2 * C) ^ (2 ^ (k - 1) - 1) * ((2 : ℝ) ^ (2 ^ (k - 1) - 1) * (1 + εp))) ^ 2)) :
    ∀ s : KvnSt p, KvnSt.Inv (k - 1) C ε 2 η ρs ν s → s.n < K₀ →
      ¬ KvnSt.term f (k - 1) C ε gr s → KvnSt.small (k - 1) C ε η 2 c ρs ν f s := by
  intro s hInv hsK hnt
  have hd : 1 ≤ k - 1 := by omega
  have hεp1 : εp ≤ 1 := le_trans hεp₀ hεp₀1
  have hC0 : (0 : ℝ) < C := by linarith
  have hC1 : (1 : ℝ) ≤ C := by linarith
  have hNpos : (0 : ℝ) < (Fintype.card (ZMod p) : ℝ) := by
    have h : 0 < Fintype.card (ZMod p) := Fintype.card_pos_iff.mpr ⟨0⟩
    exact_mod_cast h
  have hNne : ((Fintype.card (ZMod p) : ℝ)) ≠ 0 := ne_of_gt hNpos
  have hNnn : (0 : ℝ) ≤ (Fintype.card (ZMod p) : ℝ) := le_of_lt hNpos
  obtain ⟨αnew, Tnew, E₀bnd, hαnew0, hαnewε, hTcov, hTmass, hMpos, hεrawpos, hMb, hQcl,
      hE₀bnd0, hE₀bndle, hAtom, hDelta⟩ :=
    exists_kvn_geo_ED (p := p) hk hC hε hη hη1 hν hf0 hfν hεp hεp1 hτ0 hmom hcorr hmean hLFC
      s hInv hη' hsK hεp₀ hεp₀1 hE hpoly hE₀max0 hE₀le hUnorm
  obtain ⟨hm1, hm2, hm3⟩ := mass_bounds (p := p) hν hεp1 hmean
  set Msb : ℝ := (2 : ℝ) ^ (2 ^ (k - 1) - 1) * 2 with hMsb
  set B₀ : ℝ := 2 * εp₀ ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹) * E₀max + 3 * η'
    + 27 * (K₀ : ℝ) ^ 2 * η with hB₀
  set Abnd : ℕ := KvnAbndU k ε with hAbnd
  have hMsb0 : (0 : ℝ) ≤ Msb := by rw [hMsb]; positivity
  have hB₀0 : (0 : ℝ) ≤ B₀ := by
    rw [hB₀]
    refine add_nonneg (add_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (Real.rpow_nonneg (le_trans hεp hεp₀) _)) hE₀max0) (by linarith)) (by positivity)
  have hMraw0 : (0 : ℝ) ≤ (2 * C) ^ (2 ^ (k - 1) - 1) * ((2 : ℝ) ^ (2 ^ (k - 1) - 1) * (1 + εp)) :=
    mul_nonneg (pow_nonneg (by linarith : (0:ℝ) ≤ 2 * C) _) (mul_nonneg (pow_nonneg (by norm_num) _)
      (by linarith))
  have hMraw0' : (0 : ℝ) ≤ (2 * C) ^ (2 ^ (k - 1) - 1) * ((2 : ℝ) ^ (2 ^ (k - 1) - 1) * (1 + εp₀)) :=
    mul_nonneg (pow_nonneg (by linarith : (0:ℝ) ≤ 2 * C) _) (mul_nonneg (pow_nonneg (by norm_num) _)
      (by linarith))
  -- the residual bound
  have hFnew : ∀ x, |KvnSt.residual f (k - 1) C ε s x| ≤ C * (ν x + 1) := by
    intro x
    have hb := residual_abs_le (d := k - 1) (τ := 2) (C := C) (ε := ε) hν (by norm_num) s hInv
      hf0 hfν x
    have hb' : |KvnSt.residual f (k - 1) C ε s x| ≤ 3 * (ν x + 1) := by
      have h23 : (2 : ℝ) + 1 = 3 := by norm_num
      rw [h23] at hb
      exact hb
    have hνx : (0 : ℝ) ≤ ν x + 1 := by linarith [hν x]
    calc |KvnSt.residual f (k - 1) C ε s x| ≤ 3 * (ν x + 1) := hb'
      _ ≤ C * (ν x + 1) := by nlinarith
  -- the generator bound
  have hFj : ∀ (j : Fin (s.n + 1)) (x : ZMod p),
      |(Function.update s.G s.n (KvnSt.residual f (k - 1) C ε s)) (j : ℕ) x| ≤ C * (ν x + 1) := by
    intro j x
    obtain ⟨hBmem, hBeq, hΩsat, hmassdata, hcE, hGbound, hα0, hαε, hTmassInv, hTcovInv⟩ := hInv
    rcases eq_or_lt_of_le (show (j : ℕ) ≤ s.n by have := j.isLt; omega) with h | h
    · rw [h, Function.update_self]
      exact hFnew x
    · rw [Function.update_of_ne (by omega : (j : ℕ) ≠ s.n)]
      exact hGbound (j : ℕ) h x
  -- sup-norm bound
  have hMscaled : ∀ (j : Fin (s.n + 1)) (x : ZMod p),
      |davg (k - 1) (fun z => (Function.update s.G s.n (KvnSt.residual f (k - 1) C ε s))
          (j : ℕ) z / (2 * C)) x| ≤ Msb := by
    intro j x
    have h := Commons.Combinatorics.Transference.davg_halfC_bound (p := p) (d := k - 1) hd ν _
      hν hC1 (hFj j) hεp hLFC x
    have h2 : (2 : ℝ) ^ (2 ^ (k - 1) - 1) * (1 + εp) ≤ (2 : ℝ) ^ (2 ^ (k - 1) - 1) * 2 :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    rw [hMsb]
    linarith
  -- the atom count
  have hα0fin : ∀ j : ℕ, 0 ≤ (Function.update s.α s.n αnew) j := by
    intro j
    obtain ⟨hBmem, hBeq, hΩsat, hmassdata, hcE, hGbound, hα0, hαε, hTmassInv, hTcovInv⟩ := hInv
    by_cases hje : j = s.n
    · rw [hje, Function.update_self]; exact hαnew0
    · rw [Function.update_of_ne hje]; exact hα0 j
  have hαεfin : ∀ j : ℕ, (Function.update s.α s.n αnew) j < ε := by
    intro j
    obtain ⟨hBmem, hBeq, hΩsat, hmassdata, hcE, hGbound, hα0, hαε, hTmassInv, hTcovInv⟩ := hInv
    by_cases hje : j = s.n
    · rw [hje, Function.update_self]; exact hαnewε
    · rw [Function.update_of_ne hje]; exact hαε j
  have hcard := card_image_kpart_le (X := ZMod p) (K := s.n + 1)
    (fun j y => davg (k - 1) (fun z => (Function.update s.G s.n
        (KvnSt.residual f (k - 1) C ε s)) j z / (2 * C)) y)
    (Function.update s.α s.n αnew) hε hMsb0
    (fun j hj x => hMscaled ⟨j, hj⟩ x) hα0fin hαεfin
  have hAtomCount_nat : (Finset.univ.image
      (kpartExt (k - 1) C ε s.n s.G s.α (KvnSt.residual f (k - 1) C ε s) αnew)).card
      ≤ Abnd ^ (s.n + 1) := by
    have himg : (Finset.univ.image
        (kpartExt (k - 1) C ε s.n s.G s.α (KvnSt.residual f (k - 1) C ε s) αnew)).card
        = (Finset.univ.image (fun x => Finset.univ.filter (fun y => ∀ j : ℕ, j < s.n + 1 →
            ⌊(davg (k - 1) (fun z => (Function.update s.G s.n
                (KvnSt.residual f (k - 1) C ε s)) j z / (2 * C)) y
              - (Function.update s.α s.n αnew) j) / ε⌋
            = ⌊(davg (k - 1) (fun z => (Function.update s.G s.n
                (KvnSt.residual f (k - 1) C ε s)) j z / (2 * C)) x
              - (Function.update s.α s.n αnew) j) / ε⌋))).card := by
      congr 1
    rw [himg]
    have hAb : Abnd = (2 * (⌈Msb / ε⌉ + 2) + 1).toNat := by rw [hAbnd, KvnAbndU]
    rw [hAb]
    exact hcard
  have hAtomCountR : KvnAtomCount (k - 1) C ε f s αnew ≤ (Abnd : ℝ) ^ (s.n + 1) := by
    rw [KvnAtomCount, ← Nat.cast_pow]
    exact_mod_cast hAtomCount_nat
  have hAbnd1 : (1 : ℝ) ≤ (Abnd : ℝ) := by
    have hnat : 1 ≤ Abnd := by
      rw [hAbnd, KvnAbndU]
      have hc0 : (0 : ℤ) ≤ ⌈(2 : ℝ) ^ (2 ^ (k - 1) - 1) * 2 / ε⌉ :=
        Int.ceil_nonneg (by positivity)
      rw [Int.le_toNat (by omega : (0 : ℤ) ≤ 2 *
        (⌈(2 : ℝ) ^ (2 ^ (k - 1) - 1) * 2 / ε⌉ + 2) + 1)]
      omega
    exact_mod_cast hnat
  have hsnK : s.n + 1 ≤ K₀ := by omega
  have hAtomCount : KvnAtomCount (k - 1) C ε f s αnew ≤ (Abnd : ℝ) ^ K₀ :=
    le_trans hAtomCountR (pow_le_pow_right₀ hAbnd1 hsnK)
  -- the state-independent bound on `δ/N`
  have hδ : KvnDelta (k - 1) ν E₀bnd η' s Tnew ≤ (Fintype.card (ZMod p) : ℝ) * B₀ := by
    have hεpr : εp ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹) ≤ εp₀ ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹) :=
      Real.rpow_le_rpow hεp hεp₀ (inv_nonneg.mpr (Nat.cast_nonneg _))
    have hA : 2 * εp ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹) * E₀bnd
        ≤ 2 * εp₀ ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹) * E₀max :=
      mul_le_mul (mul_le_mul_of_nonneg_left hεpr (by norm_num)) hE₀bndle hE₀bnd0
        (mul_nonneg (by norm_num) (Real.rpow_nonneg (le_trans hεp hεp₀) _))
    have hB : 27 * (((s.n + 1 : ℕ)) : ℝ) ^ 2 * η ≤ 27 * (K₀ : ℝ) ^ 2 * η := by
      have h1 : (((s.n + 1 : ℕ)) : ℝ) ≤ (K₀ : ℝ) := by exact_mod_cast hsnK
      have h3 : (((s.n + 1 : ℕ)) : ℝ) ^ 2 ≤ (K₀ : ℝ) ^ 2 := by nlinarith
      nlinarith
    calc KvnDelta (k - 1) ν E₀bnd η' s Tnew
        ≤ (Fintype.card (ZMod p) : ℝ)
            * (2 * εp ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹) * E₀bnd + 3 * η')
          + 27 * (((s.n + 1 : ℕ)) : ℝ) ^ 2 * η * (Fintype.card (ZMod p) : ℝ) := hDelta
      _ = (Fintype.card (ZMod p) : ℝ)
            * (2 * εp ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹) * E₀bnd + 3 * η'
              + 27 * (((s.n + 1 : ℕ)) : ℝ) ^ 2 * η) := by ring
      _ ≤ (Fintype.card (ZMod p) : ℝ) * B₀ := by
          apply mul_le_mul_of_nonneg_left _ hNnn
          rw [hB₀]; linarith [hA, hB]
  have hKvnDelta0 : (0 : ℝ) ≤ KvnDelta (k - 1) ν E₀bnd η' s Tnew :=
    KvnDelta_nonneg (d := k - 1) hd hν hE₀bnd0 (le_of_lt hη') s Tnew
  have hKvnTheta0 : (0 : ℝ) ≤ KvnTheta (k - 1) ν E₀bnd η' s Tnew := by
    rw [KvnTheta]; exact div_nonneg (by linarith [hKvnDelta0]) hNnn
  have hAtomCount0 : (0 : ℝ) ≤ KvnAtomCount (k - 1) C ε f s αnew := by
    rw [KvnAtomCount]; positivity
  have hθA0 : (0 : ℝ) ≤ (Fintype.card (ZMod p) : ℝ) * KvnTheta (k - 1) ν E₀bnd η' s Tnew
      * KvnAtomCount (k - 1) C ε f s αnew :=
    mul_nonneg (mul_nonneg hNnn hKvnTheta0) hAtomCount0
  -- the state-independent bound on `ρs`
  have hρs : (Fintype.card (ZMod p) : ℝ) * KvnTheta (k - 1) ν E₀bnd η' s Tnew
      * KvnAtomCount (k - 1) C ε f s αnew ≤ ρs := by
    have hθeq : (Fintype.card (ZMod p) : ℝ) * KvnTheta (k - 1) ν E₀bnd η' s Tnew
        = 2 * KvnDelta (k - 1) ν E₀bnd η' s Tnew + 1 := by
      rw [KvnTheta, mul_div_cancel₀ _ hNne]
    rw [hθeq]
    have h1 : 2 * KvnDelta (k - 1) ν E₀bnd η' s Tnew + 1
        ≤ (Fintype.card (ZMod p) : ℝ) * (2 * B₀) + 1 := by linarith [hδ]
    have h2 : (2 * KvnDelta (k - 1) ν E₀bnd η' s Tnew + 1) * KvnAtomCount (k - 1) C ε f s αnew
        ≤ ((Fintype.card (ZMod p) : ℝ) * (2 * B₀) + 1) * (Abnd : ℝ) ^ K₀ :=
      mul_le_mul h1 hAtomCount hAtomCount0 (by nlinarith [hNnn, hB₀0])
    have h3 : ((Fintype.card (ZMod p) : ℝ) * (2 * B₀) + 1) * (Abnd : ℝ) ^ K₀
        = (Fintype.card (ZMod p) : ℝ) * (2 * B₀) * (Abnd : ℝ) ^ K₀ + (Abnd : ℝ) ^ K₀ := by ring
    rw [h3] at h2
    linarith [h2, hρsC]
  have hρs0 : (0 : ℝ) ≤ ρs := by
    have h0 : (0 : ℝ) ≤ (Fintype.card (ZMod p) : ℝ) * (2 * B₀) * (Abnd : ℝ) ^ K₀
        + (Abnd : ℝ) ^ K₀ :=
      add_nonneg (mul_nonneg (mul_nonneg hNnn (by linarith [hB₀0])) (by positivity)) (by positivity)
    linarith [hρsC]
  have hMrawb_le : (2 * C) ^ (2 ^ (k - 1) - 1) * ((2 : ℝ) ^ (2 ^ (k - 1) - 1) * (1 + εp))
      ≤ (2 * C) ^ (2 ^ (k - 1) - 1) * ((2 : ℝ) ^ (2 ^ (k - 1) - 1) * (1 + εp₀)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
      (pow_nonneg (by linarith : (0:ℝ) ≤ 2 * C) _)
  have hTX : (Fintype.card (ZMod p) : ℝ) * KvnTheta (k - 1) ν E₀bnd η' s Tnew
      * KvnAtomCount (k - 1) C ε f s αnew + ((s.n : ℝ) + 1) * ρs
      ≤ (((K₀ : ℝ) + 1)) * ρs := by
    have h1 : ((s.n : ℝ) + 1) * ρs ≤ (K₀ : ℝ) * ρs := by
      have hle : ((s.n : ℝ) + 1) ≤ (K₀ : ℝ) := by
        exact_mod_cast (show s.n + 1 ≤ K₀ from hsnK)
      exact mul_le_mul_of_nonneg_right hle hρs0
    linarith [hρs, h1]
  have hc0 : (0 : ℝ) ≤ (1 + 3) * ((Fintype.card (ZMod p) : ℝ) * KvnTheta (k - 1) ν E₀bnd η' s Tnew
      * KvnAtomCount (k - 1) C ε f s αnew + ((s.n : ℝ) + 1) * ρs) :=
    mul_nonneg (by norm_num) (add_nonneg hθA0 (mul_nonneg (by positivity : (0:ℝ) ≤ (s.n : ℝ) + 1) hρs0))
  -- hγpos
  have hγpos : (2 * C) ^ (2 ^ (k - 1) - 1) * ((2 : ℝ) ^ (2 ^ (k - 1) - 1) * (1 + εp))
      * ((1 + 3) * ((Fintype.card (ZMod p) : ℝ) * KvnTheta (k - 1) ν E₀bnd η' s Tnew
          * KvnAtomCount (k - 1) C ε f s αnew + ((s.n : ℝ) + 1) * ρs))
      + (2 * C) ^ (2 ^ (k - 1) - 1) * ε
        * (∑ x, |KvnSt.residual f (k - 1) C ε s x|)
      ≤ (Fintype.card (ZMod p) : ℝ) * gr / 2 := by
    have hmain : (2 * C) ^ (2 ^ (k - 1) - 1) * ((2 : ℝ) ^ (2 ^ (k - 1) - 1) * (1 + εp))
          * ((1 + 3) * ((Fintype.card (ZMod p) : ℝ) * KvnTheta (k - 1) ν E₀bnd η' s Tnew
            * KvnAtomCount (k - 1) C ε f s αnew + ((s.n : ℝ) + 1) * ρs))
        ≤ (Fintype.card (ZMod p) : ℝ) * gr / 4 := by
      have hstep : (2 * C) ^ (2 ^ (k - 1) - 1) * ((2 : ℝ) ^ (2 ^ (k - 1) - 1) * (1 + εp))
            * ((1 + 3) * ((Fintype.card (ZMod p) : ℝ) * KvnTheta (k - 1) ν E₀bnd η' s Tnew
              * KvnAtomCount (k - 1) C ε f s αnew + ((s.n : ℝ) + 1) * ρs))
          ≤ (2 * C) ^ (2 ^ (k - 1) - 1) * ((2 : ℝ) ^ (2 ^ (k - 1) - 1) * (1 + εp₀))
            * ((1 + 3) * (((K₀ : ℝ) + 1) * ρs)) :=
        mul_le_mul hMrawb_le (mul_le_mul_of_nonneg_left hTX (by norm_num)) hc0 hMraw0'
      have h4 : (1 + 3) * (((K₀ : ℝ) + 1) * ρs) = 4 * ((K₀ : ℝ) + 1) * ρs := by ring
      rw [h4] at hstep
      linarith [hstep, hγC]
    have hres : (∑ x, |KvnSt.residual f (k - 1) C ε s x|) ≤ 9 * (Fintype.card (ZMod p) : ℝ) := by
      have hpt : ∀ x, |KvnSt.residual f (k - 1) C ε s x| ≤ 3 * (ν x + 1) := by
        intro x
        have hb := residual_abs_le (d := k - 1) (τ := 2) (C := C) (ε := ε) hν (by norm_num) s
          hInv hf0 hfν x
        have h23 : (2 : ℝ) + 1 = 3 := by norm_num
        rw [h23] at hb; exact hb
      calc (∑ x, |KvnSt.residual f (k - 1) C ε s x|) ≤ ∑ x, 3 * (ν x + 1) :=
            Finset.sum_le_sum (fun x _ => hpt x)
        _ = 3 * ∑ x, (ν x + 1) := by rw [Finset.mul_sum]
        _ ≤ 3 * (3 * (Fintype.card (ZMod p) : ℝ)) :=
            mul_le_mul_of_nonneg_left hm2 (by norm_num)
        _ = 9 * (Fintype.card (ZMod p) : ℝ) := by ring
    have hsec : (2 * C) ^ (2 ^ (k - 1) - 1) * ε * (∑ x, |KvnSt.residual f (k - 1) C ε s x|)
        ≤ (Fintype.card (ZMod p) : ℝ) * gr / 4 := by
      have hε0 : (0 : ℝ) ≤ (2 * C) ^ (2 ^ (k - 1) - 1) * ε :=
        mul_nonneg (pow_nonneg (by linarith : (0:ℝ) ≤ 2 * C) _) (le_of_lt hε)
      calc (2 * C) ^ (2 ^ (k - 1) - 1) * ε * (∑ x, |KvnSt.residual f (k - 1) C ε s x|)
          ≤ (2 * C) ^ (2 ^ (k - 1) - 1) * ε * (9 * (Fintype.card (ZMod p) : ℝ)) :=
            mul_le_mul_of_nonneg_left hres hε0
        _ = 9 * ((2 * C) ^ (2 ^ (k - 1) - 1) * ε) * (Fintype.card (ZMod p) : ℝ) := by ring
        _ ≤ (Fintype.card (ZMod p) : ℝ) * gr / 4 := by
            have := mul_le_mul_of_nonneg_right hεC hNnn
            linarith
    linarith [hmain, hsec]
  -- hsmall
  have hsmall : (3 * 3 ^ 2 + 2 * 3)
      * ((Fintype.card (ZMod p) : ℝ) * KvnTheta (k - 1) ν E₀bnd η' s Tnew
          * KvnAtomCount (k - 1) C ε f s αnew + ((s.n : ℝ) + 1) * ρs) + c
      ≤ ((Fintype.card (ZMod p) : ℝ) * gr / 2) ^ 2
        / ((Fintype.card (ZMod p) : ℝ)
            * ((2 * C) ^ (2 ^ (k - 1) - 1) * ((2 : ℝ) ^ (2 ^ (k - 1) - 1) * (1 + εp))) ^ 2) := by
    have hstep : (3 * 3 ^ 2 + 2 * 3)
        * ((Fintype.card (ZMod p) : ℝ) * KvnTheta (k - 1) ν E₀bnd η' s Tnew
            * KvnAtomCount (k - 1) C ε f s αnew + ((s.n : ℝ) + 1) * ρs) + c
        ≤ (3 * 3 ^ 2 + 2 * 3) * (((K₀ : ℝ) + 1) * ρs) + c := by
      have hc := mul_le_mul_of_nonneg_left hTX (by norm_num : (0:ℝ) ≤ 3 * 3 ^ 2 + 2 * 3)
      linarith
    linarith [hstep, hsC]
  exact kvn_small_assembly (p := p) hk hC hε hη hη1 hη' hν hf0 hfν s hInv hgr hnt
    hαnew0 hαnewε Tnew hTcov hTmass hMpos hεrawpos hMb hQcl hE₀bnd0 hAtom hρs hγpos hsmall

end GTTrans
