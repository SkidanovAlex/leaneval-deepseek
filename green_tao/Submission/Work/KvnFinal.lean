import Submission.Work.KvnSmall
import Submission.Commons.Combinatorics.Transference.bohr_sigma_atom_bound_of_weierstrass

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# The Green–Tao §7 step with the Weierstrass data supplied by the caller

`exists_kvn_geo_ED` is `exists_kvn_geo_bounded` with the quantitative Weierstrass data `E, D`
supplied by the caller (as `hpoly`).  This is what allows the tower's constants `ρs`, `c` to be
chosen once and for all from `E, D`, since (by `exists_poly_weight_family_deg_K0`) the data
`E = KvnPolyE K₀ Msb ε η η'`, `D = KvnPolyD …` do not depend on the state.
-/

open Finset
open scoped BigOperators
open Commons.Combinatorics.Transference
open FinSigma

namespace GTTrans

variable {p : ℕ} [Fact p.Prime]

/-- **The geometric data of a §7 step with fully explicit constants.**

Given `k`-pseudorandomness of `ν` and the bound `‖ν-1‖_{U^{k-1}} ≤ 2 εp^{1/2^{k-1}}`, there are a
shift `αnew` and a boundary set `Tnew`, an explicit bound `E₀bnd` for the `bohr-sigma` error
constant, and the resulting bound

`δ = KvnDelta ≤ N(2 εp^{1/2^{k-1}} E₀bnd + 3η') + 27 (n+1) η N`

where the `Mraw` and `εraw` of the step are the explicit values
`(2C)^{2^{k-1}-1} · 2^{2^{k-1}-1}(1+εp)` and `(2C)^{2^{k-1}-1} · ε`. -/
theorem exists_kvn_geo_ED {k : ℕ} (hk : 3 ≤ k) {C : ℝ} (hC : 5 ≤ C) {ε η : ℝ} (hε : 0 < ε)
    (hη : 0 < η) (hη1 : η ≤ 1 / 4)
    {ν f : ZMod p → ℝ} (hν : ∀ x, 0 ≤ ν x) (hf0 : ∀ x, 0 ≤ f x) (hfν : ∀ x, f x ≤ ν x)
    {εp : ℝ} (hεp : 0 ≤ εp) (hεp1 : εp ≤ 1)
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
    (s : KvnSt p) {ρs : ℝ} (hInv : KvnSt.Inv (k - 1) C ε 2 η ρs ν s) {η' : ℝ} (hη' : 0 < η')
    {K₀ : ℕ} (hK₀ : s.n < K₀) {εp₀ : ℝ} (hεp₀ : εp ≤ εp₀) (hεp₀1 : εp₀ ≤ 1)
    {E : ℝ} (hE : 0 ≤ E) {D : ℕ}
    (hpoly : ∀ (K' : ℕ) (hK' : K' ≤ K₀) (c : Fin K' → ℝ),
      (∀ j, |c j| ≤ (2 : ℝ) ^ (2 ^ (k - 1) - 1) * (1 + εp₀) + ε) →
      ∃ P : MvPolynomial (Fin K') ℝ,
        (∀ t ∈ Set.pi Set.univ (fun _ : Fin K' => Set.Icc (-((2 : ℝ) ^ (2 ^ (k - 1) - 1) * (1 + εp₀))) ((2 : ℝ) ^ (2 ^ (k - 1) - 1) * (1 + εp₀))),
          |∏ j, levelJoinPsi η ((t j - c j) / ε) - MvPolynomial.eval t P| ≤ η') ∧
        (∑ m ∈ P.support, |P.coeff m|) ≤ E ∧
        P.totalDegree ≤ D)
    {E₀max : ℝ} (hE₀max0 : 0 ≤ E₀max)
    (hE₀le : E * (1 + (((2 ^ (k - 1) * 2 ^ (k - 1) : ℕ)) : ℝ) ^ D *
        ((6 : ℝ) ^ D * (∑ j ∈ Finset.range (D + 1), (if j = 0 then 1 else max (Cm j) 0))))
      ≤ E₀max)
    (hUnorm : Unorm (k - 1) (fun x => ν x - 1)
      ≤ 2 * εp ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹)) :
    ∃ (αnew : ℝ) (Tnew : Finset (ZMod p)) (E₀bnd : ℝ),
      0 ≤ αnew ∧ αnew < ε ∧
      (∀ y : ZMod p,
        (∃ m : ℤ, |(davg (k - 1) (fun z => KvnSt.residual f (k - 1) C ε s z / (2 * C)) y
          - αnew) / ε - (m : ℝ)| ≤ η) → y ∈ Tnew) ∧
      (∑ y ∈ Tnew, (ν y + 1) ≤ 3 * η * ∑ x, (ν x + 1)) ∧
      0 < (2 * C) ^ (2 ^ (k - 1) - 1) * ((2 : ℝ) ^ (2 ^ (k - 1) - 1) * (1 + εp)) ∧
      0 < (2 * C) ^ (2 ^ (k - 1) - 1) * ε ∧
      (∀ x, |davg (k - 1) (KvnSt.residual f (k - 1) C ε s) x|
        ≤ (2 * C) ^ (2 ^ (k - 1) - 1) * ((2 : ℝ) ^ (2 ^ (k - 1) - 1) * (1 + εp))) ∧
      (∀ x y : ZMod p,
        y ∈ kpartExt (k - 1) C ε s.n s.G s.α (KvnSt.residual f (k - 1) C ε s) αnew x →
        |davg (k - 1) (KvnSt.residual f (k - 1) C ε s) y
          - davg (k - 1) (KvnSt.residual f (k - 1) C ε s) x|
          ≤ (2 * C) ^ (2 ^ (k - 1) - 1) * ε) ∧
      0 ≤ E₀bnd ∧ E₀bnd ≤ E₀max ∧
      (∀ x, |∑ y ∈ kpartExt (k - 1) C ε s.n s.G s.α
          (KvnSt.residual f (k - 1) C ε s) αnew x, (ν y - 1)|
        ≤ KvnDelta (k - 1) ν E₀bnd η' s Tnew) ∧
      KvnDelta (k - 1) ν E₀bnd η' s Tnew
        ≤ (Fintype.card (ZMod p) : ℝ) * (2 * εp ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹) * E₀bnd
            + 3 * η')
          + 27 * (((s.n + 1 : ℕ)) : ℝ) ^ 2 * η * (Fintype.card (ZMod p) : ℝ) := by
  classical
  have hd : 1 ≤ k - 1 := by omega
  have hC1 : (1 : ℝ) ≤ C := by linarith
  have hk2 : 2 ≤ k := by omega
  have hNpos : (0 : ℝ) < (Fintype.card (ZMod p) : ℝ) := by
    have h : 0 < Fintype.card (ZMod p) := Fintype.card_pos_iff.mpr ⟨0⟩
    exact_mod_cast h
  -- the residual bound
  have hFnew : ∀ x, |KvnSt.residual f (k - 1) C ε s x| ≤ C * (ν x + 1) := by
    intro x
    have hb := residual_abs_le (d := k - 1) (τ := 2) (C := C) (ε := ε) hν (by norm_num) s hInv
      hf0 hfν x
    have hνx : (0 : ℝ) ≤ ν x + 1 := by linarith [hν x]
    have h3C : (3 : ℝ) ≤ C := by linarith
    have hb' : |KvnSt.residual f (k - 1) C ε s x| ≤ 3 * (ν x + 1) := by
      have h23 : (2 : ℝ) + 1 = 3 := by norm_num
      rw [h23] at hb
      exact hb
    calc |KvnSt.residual f (k - 1) C ε s x| ≤ 3 * (ν x + 1) := hb'
      _ ≤ C * (ν x + 1) := by nlinarith
  -- the mass bounds
  obtain ⟨hmass1, hmass2, hmass3⟩ := mass_bounds hν hεp1 hmean
  -- the geometric data, with explicit constants
  obtain ⟨αnew, Tnew, hαnew0, hαnewε, hTcov, hTmass, hMb, hQcl⟩ :=
    exists_step_geo_data_bound (p := p) (d := k - 1) hd (C := C) (ε := ε) (η := η) hC1 hε hη
      (by linarith) hν hFnew (εp := εp) hεp hLFC
  -- the generator family
  have hFj : ∀ (j : Fin (s.n + 1)) (x : ZMod p),
      |(Function.update s.G s.n (KvnSt.residual f (k - 1) C ε s)) (j : ℕ) x|
        ≤ C * (ν x + 1) := by
    intro j x
    obtain ⟨hBmem, hBeq, hΩsat, hmassdata, hcE, hGbound, hα0, hαε, hTmassInv, hTcovInv⟩ := hInv
    rcases eq_or_lt_of_le (show (j : ℕ) ≤ s.n by have := j.isLt; omega) with h | h
    · rw [h, Function.update_self]
      exact hFnew x
    · rw [Function.update_of_ne (by omega : (j : ℕ) ≠ s.n)]
      exact hGbound (j : ℕ) h x
  -- the sup-norm bound for the scaled generators
  have hεp₀0 : (0 : ℝ) ≤ εp₀ := le_trans hεp hεp₀
  have hMsb : (0 : ℝ) ≤ (2 : ℝ) ^ (2 ^ (k - 1) - 1) * (1 + εp₀) :=
    mul_nonneg (by positivity) (by linarith)
  have hεp1' : εp ≤ 1 := le_trans hεp₀ hεp₀1
  have hMbound : ∀ (j : Fin (s.n + 1)) (x : ZMod p),
      |davg (k - 1) (fun y => (Function.update s.G s.n (KvnSt.residual f (k - 1) C ε s))
          (j : ℕ) y / (2 * C)) x| ≤ (2 : ℝ) ^ (2 ^ (k - 1) - 1) * (1 + εp₀) := by
    intro j x
    have h := Commons.Combinatorics.Transference.davg_halfC_bound (p := p) (d := k - 1) hd ν _
      hν hC1 (hFj j) hεp hLFC x
    have h2 : (2 : ℝ) ^ (2 ^ (k - 1) - 1) * (1 + εp)
        ≤ (2 : ℝ) ^ (2 ^ (k - 1) - 1) * (1 + εp₀) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  -- the shifts and boundary sets
  have hα0fin : ∀ j : Fin (s.n + 1),
      0 ≤ (Function.update s.α s.n αnew) (j : ℕ) := by
    intro j
    obtain ⟨hBmem, hBeq, hΩsat, hmassdata, hcE, hGbound, hα0, hαε, hTmassInv, hTcovInv⟩ := hInv
    rcases eq_or_lt_of_le (show (j : ℕ) ≤ s.n by have := j.isLt; omega) with h | h
    · rw [h, Function.update_self]; exact hαnew0
    · rw [Function.update_of_ne (by omega : (j : ℕ) ≠ s.n)]
      exact hα0 (j : ℕ)
  have hαεfin : ∀ j : Fin (s.n + 1),
      (Function.update s.α s.n αnew) (j : ℕ) < ε := by
    intro j
    obtain ⟨hBmem, hBeq, hΩsat, hmassdata, hcE, hGbound, hα0, hαε, hTmassInv, hTcovInv⟩ := hInv
    rcases eq_or_lt_of_le (show (j : ℕ) ≤ s.n by have := j.isLt; omega) with h | h
    · rw [h, Function.update_self]; exact hαnewε
    · rw [Function.update_of_ne (by omega : (j : ℕ) ≠ s.n)]
      exact hαε (j : ℕ)
  have hTfin : ∀ (j : Fin (s.n + 1)) (y : ZMod p),
      (∃ n : ℤ, |(davg (k - 1) (fun z => (Function.update s.G s.n
            (KvnSt.residual f (k - 1) C ε s)) (j : ℕ) z / (2 * C)) y
          - (Function.update s.α s.n αnew) (j : ℕ)) / ε - n| ≤ η) →
        y ∈ (Function.update s.T s.n Tnew) (j : ℕ) := by
    intro j y hy
    obtain ⟨hBmem, hBeq, hΩsat, hmassdata, hcE, hGbound, hα0, hαε, hTmassInv, hTcovInv⟩ := hInv
    rcases eq_or_lt_of_le (show (j : ℕ) ≤ s.n by have := j.isLt; omega) with h | h
    · simp only [h, Function.update_self] at hy ⊢
      exact hTcov y hy
    · simp only [Function.update_of_ne (by omega : (j : ℕ) ≠ s.n)] at hy ⊢
      exact hTcovInv (j : ℕ) h y hy
  -- the tight atom-mass bound with the caller-supplied Weierstrass data
  have hAtomFin := bohr_sigma_atom_bound_of_weierstrass (p := p) (d := k - 1) (K := s.n + 1)
    (K₀ := K₀) hd (by omega)
    (fun (j : Fin (s.n + 1)) (z : ZMod p) =>
      (Function.update s.G s.n (KvnSt.residual f (k - 1) C ε s)) (j : ℕ) z)
    hν hτ0 hC1 hFj hcorr hmom hεp hεp1' hmean hεp hLFC hMsb hMbound hε hη hη1 hη'
    (fun j => (Function.update s.α s.n αnew) (j : ℕ)) hα0fin hαεfin
    (fun j => (Function.update s.T s.n Tnew) (j : ℕ)) hTfin hE hpoly
  set E₀bnd : ℝ := E * (1 + (((2 ^ (k - 1) * 2 ^ (k - 1) : ℕ)) : ℝ) ^ D *
      ((6 : ℝ) ^ D * (∑ j ∈ Finset.range (D + 1), (if j = 0 then 1 else max (Cm j) 0))))
    with hE₀bnddef
  have hE₀bnd0 : 0 ≤ E₀bnd := by
    rw [hE₀bnddef]
    refine mul_nonneg hE (by
      refine add_nonneg zero_le_one ?_
      refine mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) ?_
      refine mul_nonneg (pow_nonneg (by norm_num) _) ?_
      exact Finset.sum_nonneg (fun j _ => by
        by_cases hj : j = 0
        · simp [hj]
        · simp only [hj, if_false]; exact le_max_right _ _))
  -- the atom bound with `E₀bnd`
  have hAtom : ∀ x, |∑ y ∈ kpartExt (k - 1) C ε s.n s.G s.α
      (KvnSt.residual f (k - 1) C ε s) αnew x, (ν y - 1)|
      ≤ KvnDelta (k - 1) ν E₀bnd η' s Tnew := by
    intro x
    rw [kpartExt_eq_atomFilter, KvnDelta]
    exact hAtomFin x
  -- the explicit `KvnDelta` bound
  have hDelta : KvnDelta (k - 1) ν E₀bnd η' s Tnew
      ≤ (Fintype.card (ZMod p) : ℝ) * (2 * εp ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹) * E₀bnd + 3 * η')
        + 27 * (((s.n + 1 : ℕ)) : ℝ) ^ 2 * η * (Fintype.card (ZMod p) : ℝ) := by
    rw [KvnDelta]
    have h1 : Unorm (k - 1) (fun y : ZMod p => ν y - 1) * E₀bnd
        ≤ (2 * εp ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹)) * E₀bnd :=
      mul_le_mul_of_nonneg_right hUnorm hE₀bnd0
    have h2 : η' * ((Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ y, |ν y - 1|) ≤ 3 * η' := by
      calc η' * ((Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ y, |ν y - 1|)
          ≤ η' * 3 := mul_le_mul_of_nonneg_left hmass3 (le_of_lt hη')
        _ = 3 * η' := by ring
    have hNnn : (0 : ℝ) ≤ (Fintype.card (ZMod p) : ℝ) := le_of_lt hNpos
    have h3 : (Fintype.card (ZMod p) : ℝ)
          * (Unorm (k - 1) (fun y : ZMod p => ν y - 1) * E₀bnd
            + η' * ((Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ y, |ν y - 1|))
        ≤ (Fintype.card (ZMod p) : ℝ)
          * (2 * εp ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹) * E₀bnd + 3 * η') :=
      mul_le_mul_of_nonneg_left (add_le_add h1 h2) hNnn
    have h4 : ∑ j : Fin (s.n + 1), ∑ y ∈ (Function.update s.T s.n Tnew) (j : ℕ), (ν y + 1)
        ≤ (s.n + 1 : ℕ) * (3 * η * ∑ x, (ν x + 1)) := by
      have h5 : ∀ j : Fin (s.n + 1),
          ∑ y ∈ (Function.update s.T s.n Tnew) (j : ℕ), (ν y + 1) ≤ 3 * η * ∑ x, (ν x + 1) := by
        intro j
        rcases eq_or_lt_of_le (show (j : ℕ) ≤ s.n by have := j.isLt; omega) with h | h
        · rw [h, Function.update_self]; exact hTmass
        · rw [Function.update_of_ne (by omega : (j : ℕ) ≠ s.n)]
          obtain ⟨hBmem, hBeq, hΩsat, hmassdata, hcE, hGbound, hα0, hαε, hTmassInv, hTcovInv⟩ :=
            hInv
          exact hTmassInv (j : ℕ) h
      calc ∑ j : Fin (s.n + 1), ∑ y ∈ (Function.update s.T s.n Tnew) (j : ℕ), (ν y + 1)
          ≤ ∑ _j : Fin (s.n + 1), (3 * η * ∑ x, (ν x + 1)) :=
            Finset.sum_le_sum (fun j _ => h5 j)
        _ = (s.n + 1 : ℕ) * (3 * η * ∑ x, (ν x + 1)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h6 : ((3 * (s.n + 1) : ℕ) : ℝ) * ∑ j : Fin (s.n + 1),
          ∑ y ∈ (Function.update s.T s.n Tnew) (j : ℕ), (ν y + 1)
        ≤ ((3 * (s.n + 1) : ℕ) : ℝ) * ((s.n + 1 : ℕ) * (3 * η * ∑ x, (ν x + 1))) :=
      mul_le_mul_of_nonneg_left h4 (Nat.cast_nonneg _)
    have h7 : ((3 * (s.n + 1) : ℕ) : ℝ) * ((s.n + 1 : ℕ) * (3 * η * ∑ x, (ν x + 1)))
        ≤ 27 * (((s.n + 1 : ℕ)) : ℝ) ^ 2 * η * (Fintype.card (ZMod p) : ℝ) := by
      have hcast : ((3 * (s.n + 1) : ℕ) : ℝ) = 3 * ((s.n + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [hcast]
      have h9 : (0 : ℝ) ≤ 9 * (((s.n + 1 : ℕ)) : ℝ) ^ 2 * η := by positivity
      have hmain := mul_le_mul_of_nonneg_left hmass2 h9
      linarith [hmain]
    linarith [h3, h6, h7]
  have hQcl' : ∀ x y : ZMod p,
      y ∈ kpartExt (k - 1) C ε s.n s.G s.α (KvnSt.residual f (k - 1) C ε s) αnew x →
      |davg (k - 1) (KvnSt.residual f (k - 1) C ε s) y
        - davg (k - 1) (KvnSt.residual f (k - 1) C ε s) x|
        ≤ (2 * C) ^ (2 ^ (k - 1) - 1) * ε := by
    intro x y hy
    have hy' : ∀ j : ℕ, j < s.n + 1 →
        ⌊(davg (k - 1) (fun z => (Function.update s.G s.n (KvnSt.residual f (k - 1) C ε s)) j z
            / (2 * C)) y - (Function.update s.α s.n αnew) j) / ε⌋
          = ⌊(davg (k - 1) (fun z => (Function.update s.G s.n (KvnSt.residual f (k - 1) C ε s)) j z
            / (2 * C)) x - (Function.update s.α s.n αnew) j) / ε⌋ := by
      have h := hy
      rw [kpartExt, mem_kpart] at h
      exact h
    have hnew := hy' s.n (by omega)
    simp only [Function.update_self] at hnew
    exact hQcl x y hnew
  exact ⟨αnew, Tnew, E₀bnd, hαnew0, hαnewε, hTcov, hTmass, by positivity,
    mul_pos (pow_pos (by linarith) _) hε, hMb, hQcl', hE₀bnd0, hE₀le, hAtom, hDelta⟩


/-- The number of atoms of the tower's σ-algebra `B_K`, uniformly bounded via
`card_image_kpart_le`. -/
noncomputable def KvnAbnd (k : ℕ) (ε εp₀ : ℝ) : ℕ :=
  (2 * (⌈((2 : ℝ) ^ (2 ^ (k - 1) - 1) * (1 + εp₀)) / ε⌉ + 2) + 1).toNat

end GTTrans
