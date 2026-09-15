import Submission.Work.KvnTower2
import Submission.Work.KvnBridge
import Submission.Commons.Combinatorics.Transference.exists_step_geo_data
import Submission.Commons.Combinatorics.Transference.exists_bohr_sigma_atom_bound
import Submission.Commons.Combinatorics.Transference.davg_halfC_bound
import Submission.Commons.NumberTheory.Sieve.KPseudorandom_data
import Submission.Commons.Combinatorics.Transference.exists_step_geo_data_bound
import Submission.Commons.Combinatorics.Transference.exists_bohr_sigma_atom_bound_deg
import Submission.Commons.Combinatorics.Transference.exists_bohr_sigma_atom_bound_deg_K0
import Submission.Commons.Analysis.Approximation.exists_poly_weight_family_deg_K0

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Discharging the smallness hypothesis of the Green–Tao §7 tower

`KvnSt.small` (`Submission/Work/KvnTower2.lean`) is the analytic input of the Furstenberg
tower: at every non-terminated invariant state it produces the shift `αnew`, the boundary set
`Tnew`, the sup-norm/regularity data `Mraw`, `εraw`, the atom-mass bound `δ`, the threshold `θ`,
the constants `B`, `γ₀` and their compatibility conditions.

This file supplies that data from Green–Tao's `k`-pseudorandomness hypothesis:

* `exists_kvn_geo` — the geometric data (`αnew`, `Tnew`, `Mraw`, `εraw`) and the atom-mass bound
  with an explicit `E₀`, from `exists_step_geo_data` + `exists_bohr_sigma_atom_bound`;
* `KvnDelta` — the explicit `δ`;
* `kvn_small_assembly` — the assembly of `KvnSt.small` from that data plus the quantitative
  smallness conditions.
-/

open Finset
open scoped BigOperators
open Commons.Combinatorics.Transference
open FinSigma

namespace GTTrans

variable {p : ℕ} [Fact p.Prime]

/-- On the complement of the exceptional set, `𝔼(f|B)` is bounded by `τ + 1`. -/
lemma cE_abs_le_one_add_tau {d : ℕ} {C ε τ η ρs : ℝ} {ν f : ZMod p → ℝ}
    (hτ0 : 0 ≤ τ) (s : KvnSt p) (hInv : KvnSt.Inv d C ε τ η ρs ν s) (hf0 : ∀ x, 0 ≤ f x)
    (hfν : ∀ x, f x ≤ ν x) :
    ∀ x, x ∉ s.Ω → |cE (KvnSt.B d C ε s) f x| ≤ τ + 1 := by
  intro x hx
  obtain ⟨hBmem, hBeq, hΩsat, hmassdata, hcE, hGbound, hα0, hαε, hTmass, hTcov⟩ := hInv
  obtain ⟨-, -, hmass⟩ := hmassdata
  have hPmem : ∀ y, y ∈ KvnSt.B d C ε s y := hBmem
  set P : ZMod p → Finset (ZMod p) := KvnSt.B d C ε s with hP
  have h1 : cE P f x ≤ cE P (fun y => ν y - 1) x + 1 := by
    have hmono := cE_mono (part := P) f ν (fun y => hfν y) x
    have hsplit : cE P ν x = cE P (fun y => ν y - 1) x + 1 := by
      have hfun : ν = (fun y => ν y - 1) + (fun _ => (1 : ℝ)) := by
        funext y; simp
      rw [hfun, cE_add, cE_const (part := P) hPmem]
      simp
    linarith
  have h2 : cE P (fun y => ν y - 1) x ≤ τ := (abs_le.mp (hcE x hx)).2
  have h3 : 0 ≤ cE P f x := cE_nonneg (part := P) f hf0 x
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-- The residual `(1 - 1_Ω)(f - 𝔼(f|B))` is bounded by `(τ+1)(ν+1)`. -/
lemma residual_abs_le {d : ℕ} {C ε τ η ρs : ℝ} {ν f : ZMod p → ℝ} (hν : ∀ x, 0 ≤ ν x)
    (hτ0 : 0 ≤ τ) (s : KvnSt p) (hInv : KvnSt.Inv d C ε τ η ρs ν s) (hf0 : ∀ x, 0 ≤ f x)
    (hfν : ∀ x, f x ≤ ν x) :
    ∀ x, |KvnSt.residual f d C ε s x| ≤ (τ + 1) * (ν x + 1) := by
  intro x
  by_cases hx : x ∈ s.Ω
  · rw [KvnSt.residual, if_pos hx, abs_zero]
    have hνx := hν x
    have : (0 : ℝ) ≤ (τ + 1) * (ν x + 1) :=
      mul_nonneg (by linarith) (by linarith)
    exact this
  · rw [KvnSt.residual, if_neg hx]
    have hb := cE_abs_le_one_add_tau (p := p) (d := d) hτ0 s hInv hf0 hfν x hx
    have hbx : -(τ + 1) ≤ cE (KvnSt.B d C ε s) f x := (abs_le.mp hb).1
    have hbx' : cE (KvnSt.B d C ε s) f x ≤ τ + 1 := (abs_le.mp hb).2
    have hf0x := hf0 x
    have hfνx := hfν x
    have hνx := hν x
    rw [abs_le]
    constructor <;> nlinarith

/-- The explicit atom-mass threshold `δ` of a §7 step: `δ` is the bound supplied by
`exists_bohr_sigma_atom_bound` for the atoms of the join `B_n ∨ B(𝒟F_{n+1})`. -/
noncomputable def KvnDelta (d : ℕ) (ν : ZMod p → ℝ) (E₀ η' : ℝ) (s : KvnSt p)
    (Tnew : Finset (ZMod p)) : ℝ :=
  (Fintype.card (ZMod p) : ℝ) * (Unorm d (fun y => ν y - 1) * E₀
      + η' * ((Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ y, |ν y - 1|))
    + ((3 * (s.n + 1) : ℕ) : ℝ) * ∑ j : Fin (s.n + 1),
        ∑ y ∈ (Function.update s.T s.n Tnew) (j : ℕ), (ν y + 1)

lemma KvnDelta_nonneg {d : ℕ} (hd : 1 ≤ d) {ν : ZMod p → ℝ} (hν : ∀ x, 0 ≤ ν x)
    {E₀ η' : ℝ} (hE₀ : 0 ≤ E₀) (hη' : 0 ≤ η') (s : KvnSt p) (Tnew : Finset (ZMod p)) :
    0 ≤ KvnDelta d ν E₀ η' s Tnew := by
  rw [KvnDelta]
  refine add_nonneg (mul_nonneg (Nat.cast_nonneg _) (add_nonneg (mul_nonneg ?_ hE₀) ?_)) ?_
  · exact Unorm_nonneg d hd _
  · exact mul_nonneg hη'
      (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
        (Finset.sum_nonneg (fun y _ => abs_nonneg _)))
  · exact mul_nonneg (Nat.cast_nonneg _)
      (Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun y _ => by have := hν y; linarith)))

/-- The number of atoms of the join `B_n ∨ B(𝒟F_{n+1})`, as a real number. -/
noncomputable def KvnAtomCount (d : ℕ) (C ε : ℝ) (f : ZMod p → ℝ) (s : KvnSt p)
    (αnew : ℝ) : ℝ :=
  ((Finset.univ.image (kpartExt d C ε s.n s.G s.α (KvnSt.residual f d C ε s) αnew)).card : ℝ)

/-- The explicit threshold `θ = (2δ+1)/N` of a §7 step. -/
noncomputable def KvnTheta (d : ℕ) (ν : ZMod p → ℝ) (E₀ η' : ℝ) (s : KvnSt p)
    (Tnew : Finset (ZMod p)) : ℝ :=
  (2 * KvnDelta d ν E₀ η' s Tnew + 1) / (Fintype.card (ZMod p) : ℝ)

/-- The atom of the join `B_n ∨ B(𝒟F_{n+1})`, in the `Fin`-indexed filter form used by the
commons `bohr-sigma` estimates. -/
lemma kpartExt_eq_atomFilter (d : ℕ) (C ε : ℝ) (n : ℕ) (G : ℕ → ZMod p → ℝ) (α : ℕ → ℝ)
    (Fnew : ZMod p → ℝ) (αnew : ℝ) (x : ZMod p) :
    kpartExt d C ε n G α Fnew αnew x
      = Finset.univ.filter (fun y : ZMod p => ∀ j : Fin (n + 1),
          y ∈ Finset.univ.filter (fun y : ZMod p =>
            ⌊(davg d (fun z => (Function.update G n Fnew) (j : ℕ) z / (2 * C)) y
                - (Function.update α n αnew) (j : ℕ)) / ε⌋
              = ⌊(davg d (fun z => (Function.update G n Fnew) (j : ℕ) z / (2 * C)) x
                - (Function.update α n αnew) (j : ℕ)) / ε⌋)) := by
  rw [kpartExt_eq_fin_filter]
  apply Finset.filter_congr
  intro y _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]


/-- **Assembly of `KvnSt.small`.**  Given the geometric data of a §7 step (`αnew`, `Tnew`,
`Mraw`, `εraw`), the atom-mass bound with constant `E₀`, the per-step mass bound
`θ · #atoms ≤ ρs` and the two quantitative smallness conditions (`hγpos`, `hsmall`), the state
can be advanced: `KvnSt.small` holds with `δ := KvnDelta`, `θ := KvnTheta = (2δ+1)/N`,
`B := 3`, `γ₀ := gr`. -/
theorem kvn_small_assembly {k : ℕ} (hk : 3 ≤ k) {C : ℝ} (hC : 5 ≤ C)
    {ε η η' ρs : ℝ} (hε : 0 < ε) (hη : 0 < η) (hη1 : η ≤ 1 / 4) (hη' : 0 < η')
    {ν f : ZMod p → ℝ} (hν : ∀ x, 0 ≤ ν x) (hf0 : ∀ x, 0 ≤ f x) (hfν : ∀ x, f x ≤ ν x)
    (s : KvnSt p) (hInv : KvnSt.Inv (k - 1) C ε 2 η ρs ν s) {gr c : ℝ} (hgr : 0 < gr)
    (hnt : ¬ KvnSt.term f (k - 1) C ε gr s)
    {αnew : ℝ} (hαnew0 : 0 ≤ αnew) (hαnewε : αnew < ε)
    (Tnew : Finset (ZMod p))
    (hTcov : ∀ y : ZMod p,
      (∃ m : ℤ, |(davg (k - 1) (fun z => KvnSt.residual f (k - 1) C ε s z / (2 * C)) y
        - αnew) / ε - (m : ℝ)| ≤ η) → y ∈ Tnew)
    (hTmass : ∑ y ∈ Tnew, (ν y + 1) ≤ 3 * η * ∑ x, (ν x + 1))
    {Mraw εraw : ℝ} (hMraw : 0 < Mraw) (hεraw : 0 < εraw)
    (hMb : ∀ x, |davg (k - 1) (KvnSt.residual f (k - 1) C ε s) x| ≤ Mraw)
    (hQcl : ∀ x y : ZMod p,
      y ∈ kpartExt (k - 1) C ε s.n s.G s.α (KvnSt.residual f (k - 1) C ε s) αnew x →
      |davg (k - 1) (KvnSt.residual f (k - 1) C ε s) y
        - davg (k - 1) (KvnSt.residual f (k - 1) C ε s) x| ≤ εraw)
    {E₀ : ℝ} (hE₀ : 0 ≤ E₀)
    (hAtom : ∀ x, |∑ y ∈ kpartExt (k - 1) C ε s.n s.G s.α
        (KvnSt.residual f (k - 1) C ε s) αnew x, (ν y - 1)|
      ≤ KvnDelta (k - 1) ν E₀ η' s Tnew)
    (hρs : (Fintype.card (ZMod p) : ℝ) * KvnTheta (k - 1) ν E₀ η' s Tnew
        * KvnAtomCount (k - 1) C ε f s αnew ≤ ρs)
    (hγpos : Mraw * ((1 + 3) * ((Fintype.card (ZMod p) : ℝ) * KvnTheta (k - 1) ν E₀ η' s Tnew
          * KvnAtomCount (k - 1) C ε f s αnew + (s.n + 1) * ρs))
        + εraw * (∑ x, |KvnSt.residual f (k - 1) C ε s x|)
      ≤ (Fintype.card (ZMod p) : ℝ) * gr / 2)
    (hsmall : (3 * 3 ^ 2 + 2 * 3) * ((Fintype.card (ZMod p) : ℝ)
          * KvnTheta (k - 1) ν E₀ η' s Tnew * KvnAtomCount (k - 1) C ε f s αnew
          + (s.n + 1) * ρs) + c
      ≤ ((Fintype.card (ZMod p) : ℝ) * gr / 2) ^ 2
          / ((Fintype.card (ZMod p) : ℝ) * Mraw ^ 2)) :
    KvnSt.small (k - 1) C ε η 2 c ρs ν f s := by
  have hd : 1 ≤ k - 1 := by omega
  have hNpos : (0 : ℝ) < (Fintype.card (ZMod p) : ℝ) := by
    have h : 0 < Fintype.card (ZMod p) := Fintype.card_pos_iff.mpr ⟨0⟩
    exact_mod_cast h
  have hNne : (Fintype.card (ZMod p) : ℝ) ≠ 0 := ne_of_gt hNpos
  have hδ0 : 0 ≤ KvnDelta (k - 1) ν E₀ η' s Tnew :=
    KvnDelta_nonneg hd hν hE₀ (le_of_lt hη') s Tnew
  have hθeq : (Fintype.card (ZMod p) : ℝ) * KvnTheta (k - 1) ν E₀ η' s Tnew
      = 2 * KvnDelta (k - 1) ν E₀ η' s Tnew + 1 := by
    rw [KvnTheta, mul_div_cancel₀ _ hNne]
  refine ⟨αnew, Tnew, Mraw, εraw, KvnDelta (k - 1) ν E₀ η' s Tnew,
    KvnTheta (k - 1) ν E₀ η' s Tnew, 3, gr, hαnew0, hαnewε, hTcov, hTmass, hMraw, hεraw, hMb,
    hQcl, ?_, hδ0, by norm_num, le_of_lt hgr, ?_, hAtom, ?_, ?_, hρs, hγpos, ?_, by linarith,
    hsmall⟩
  · exact div_pos (by linarith) hNpos
  · rw [hθeq]; linarith
  · intro x hx
    have h := cE_abs_le_one_add_tau (d := k - 1) (τ := 2) (by norm_num) s hInv hf0 hfν x hx
    linarith
  · exact le_of_lt (not_le.mp hnt)
  · rw [hθeq]
    have hpos : 0 < 2 * KvnDelta (k - 1) ν E₀ η' s Tnew + 1
        - KvnDelta (k - 1) ν E₀ η' s Tnew := by linarith
    rw [div_le_iff₀ hpos]
    linarith


/-- **The geometric data of a §7 step** (Green–Tao's `bohr-sigma` estimate with explicit
constant), from `k`-pseudorandomness of `ν`. -/
theorem exists_kvn_geo {k : ℕ} (hk : 3 ≤ k) {C : ℝ} (hC : 5 ≤ C) {ε η : ℝ} (hε : 0 < ε)
    (hη : 0 < η) (hη1 : η ≤ 1 / 4)
    {ν f : ZMod p → ℝ} (hν : ∀ x, 0 ≤ ν x) (hf0 : ∀ x, 0 ≤ f x) (hfν : ∀ x, f x ≤ ν x)
    {C₀ : ℕ → ℕ → ℝ} {εp : ℝ} (hP : Commons.NumberTheory.Sieve.KPseudorandom p k ν C₀ εp)
    (hεp : 0 ≤ εp) (hεp1 : εp ≤ 1)
    (s : KvnSt p) {ρs : ℝ} (hInv : KvnSt.Inv (k - 1) C ε 2 η ρs ν s) {η' : ℝ} (hη' : 0 < η') :
    ∃ (αnew : ℝ) (Tnew : Finset (ZMod p)) (Mraw εraw E₀ : ℝ),
      0 ≤ αnew ∧ αnew < ε ∧
      (∀ y : ZMod p,
        (∃ m : ℤ, |(davg (k - 1) (fun z => KvnSt.residual f (k - 1) C ε s z / (2 * C)) y
          - αnew) / ε - (m : ℝ)| ≤ η) → y ∈ Tnew) ∧
      (∑ y ∈ Tnew, (ν y + 1) ≤ 3 * η * ∑ x, (ν x + 1)) ∧
      0 < Mraw ∧ 0 < εraw ∧
      (∀ x, |davg (k - 1) (KvnSt.residual f (k - 1) C ε s) x| ≤ Mraw) ∧
      (∀ x y : ZMod p,
        y ∈ kpartExt (k - 1) C ε s.n s.G s.α (KvnSt.residual f (k - 1) C ε s) αnew x →
        |davg (k - 1) (KvnSt.residual f (k - 1) C ε s) y
          - davg (k - 1) (KvnSt.residual f (k - 1) C ε s) x| ≤ εraw) ∧
      0 ≤ E₀ ∧
      (∀ x, |∑ y ∈ kpartExt (k - 1) C ε s.n s.G s.α
          (KvnSt.residual f (k - 1) C ε s) αnew x, (ν y - 1)|
        ≤ KvnDelta (k - 1) ν E₀ η' s Tnew) := by
  classical
  have hd : 1 ≤ k - 1 := by omega
  have hC1 : (1 : ℝ) ≤ C := by linarith
  -- the residual
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
  -- unpack pseudorandomness
  obtain ⟨τ, Cm, hτ0, hmom, hcorr, hmean, hLFC⟩ :=
    Commons.NumberTheory.Sieve.KPseudorandom_data hk hP hεp
  -- the geometric data
  obtain ⟨αnew, Tnew, Mraw, εraw, hαnew0, hαnewε, hTcov, hTmass, hMraw, hεraw, hMb, hQcl⟩ :=
    exists_step_geo_data (p := p) (d := k - 1) hd (C := C) (ε := ε) (η := η) hC1 hε hη
      (by linarith) hν hFnew (εp := εp) hεp hLFC
  -- the generator family indexed by `Fin (s.n+1)`
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
  -- the sup-norm bound `Mscaled`
  have hMbound : ∀ (j : Fin (s.n + 1)) (x : ZMod p),
      |davg (k - 1) (fun y => (Function.update s.G s.n (KvnSt.residual f (k - 1) C ε s))
          (j : ℕ) y / (2 * C)) x| ≤ (2 : ℝ) ^ (2 ^ (k - 1) - 1) * (1 + εp) := by
    intro j x
    exact Commons.Combinatorics.Transference.davg_halfC_bound (p := p) (d := k - 1) hd ν _
      hν hC1 (hFj j) hεp hLFC x
  have hMnn : (0 : ℝ) ≤ (2 : ℝ) ^ (2 ^ (k - 1) - 1) * (1 + εp) := by positivity
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
  -- the atom-mass bound
  obtain ⟨E₀, hE₀, hAtomFin⟩ :=
    exists_bohr_sigma_atom_bound (p := p) (d := k - 1) (K := s.n + 1) hd
      (fun (j : Fin (s.n + 1)) (z : ZMod p) =>
        (Function.update s.G s.n (KvnSt.residual f (k - 1) C ε s)) (j : ℕ) z)
      hν hτ0 hC1 hFj hcorr hmom hεp hεp1 hmean hεp hLFC hMnn hMbound hε hη hη1 hη'
      (fun j => (Function.update s.α s.n αnew) (j : ℕ)) hα0fin hαεfin
      (fun j => (Function.update s.T s.n Tnew) (j : ℕ)) hTfin
  have hQcl' : ∀ x y : ZMod p,
      y ∈ kpartExt (k - 1) C ε s.n s.G s.α (KvnSt.residual f (k - 1) C ε s) αnew x →
      |davg (k - 1) (KvnSt.residual f (k - 1) C ε s) y
        - davg (k - 1) (KvnSt.residual f (k - 1) C ε s) x| ≤ εraw := by
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
  refine ⟨αnew, Tnew, Mraw, εraw, E₀, hαnew0, hαnewε, hTcov, hTmass, hMraw, hεraw, hMb, hQcl',
    hE₀, ?_⟩
  intro x
  rw [kpartExt_eq_atomFilter, KvnDelta]
  exact hAtomFin x


/-- **The `(ν+1)`-mass bounds** used in the §7 arithmetic, from the mean bound `𝔼ν = 1+O(εp)`
and `ν ≥ 0`. -/
lemma mass_bounds {ν : ZMod p → ℝ} (hν : ∀ x, 0 ≤ ν x)
    {εp : ℝ} (hεp1 : εp ≤ 1)
    (hmean : |((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x, ν x - 1| ≤ εp) :
    (∑ x, ν x ≤ (Fintype.card (ZMod p) : ℝ) * (1 + εp)) ∧
    (∑ x, (ν x + 1) ≤ 3 * (Fintype.card (ZMod p) : ℝ)) ∧
    ((Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ x, |ν x - 1| ≤ 3) := by
  classical
  have hNpos : (0 : ℝ) < (Fintype.card (ZMod p) : ℝ) := by
    have h : 0 < Fintype.card (ZMod p) := Fintype.card_pos_iff.mpr ⟨0⟩
    exact_mod_cast h
  have h1 : (Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ x, ν x ≤ 1 + εp := by
    linarith [(abs_le.mp hmean).2]
  have h2 : ∑ x, ν x ≤ (Fintype.card (ZMod p) : ℝ) * (1 + εp) := by
    have h3 : ∑ x, ν x = (Fintype.card (ZMod p) : ℝ) * ((Fintype.card (ZMod p) : ℝ)⁻¹
        * ∑ x, ν x) := by
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hNpos), one_mul]
    rw [h3]
    exact mul_le_mul_of_nonneg_left h1 (le_of_lt hNpos)
  refine ⟨h2, ?_, ?_⟩
  · have h4 : ∑ x, (ν x + 1) = (∑ x, ν x) + (Fintype.card (ZMod p) : ℝ) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [h4]
    nlinarith
  · have h5 : ∀ x, |ν x - 1| ≤ ν x + 1 := by
      intro x
      have h := hν x
      rw [abs_le]
      constructor <;> linarith
    have h6 : ∑ x, (ν x + 1) ≤ 3 * (Fintype.card (ZMod p) : ℝ) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      nlinarith
    calc (Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ x, |ν x - 1|
        ≤ (Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ x, (ν x + 1) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun x _ => h5 x))
            (inv_nonneg.mpr (le_of_lt hNpos))
      _ ≤ (Fintype.card (ZMod p) : ℝ)⁻¹ * (3 * (Fintype.card (ZMod p) : ℝ)) :=
          mul_le_mul_of_nonneg_left h6 (inv_nonneg.mpr (le_of_lt hNpos))
      _ = 3 := by
          rw [mul_comm (3 : ℝ) _, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hNpos), one_mul]

/-- **The geometric data of a §7 step with fully explicit constants.**

Given `k`-pseudorandomness of `ν` and the bound `‖ν-1‖_{U^{k-1}} ≤ 2 εp^{1/2^{k-1}}`, there are a
shift `αnew` and a boundary set `Tnew`, an explicit bound `E₀bnd` for the `bohr-sigma` error
constant, and the resulting bound

`δ = KvnDelta ≤ N(2 εp^{1/2^{k-1}} E₀bnd + 3η') + 27 (n+1) η N`

where the `Mraw` and `εraw` of the step are the explicit values
`(2C)^{2^{k-1}-1} · 2^{2^{k-1}-1}(1+εp)` and `(2C)^{2^{k-1}-1} · ε`. -/
theorem exists_kvn_geo_bounded {k : ℕ} (hk : 3 ≤ k) {C : ℝ} (hC : 5 ≤ C) {ε η : ℝ} (hε : 0 < ε)
    (hη : 0 < η) (hη1 : η ≤ 1 / 4)
    {ν f : ZMod p → ℝ} (hν : ∀ x, 0 ≤ ν x) (hf0 : ∀ x, 0 ≤ f x) (hfν : ∀ x, f x ≤ ν x)
    {C₀ : ℕ → ℕ → ℝ} {εp : ℝ} (hP : Commons.NumberTheory.Sieve.KPseudorandom p k ν C₀ εp)
    (hεp : 0 ≤ εp) (hεp1 : εp ≤ 1)
    (s : KvnSt p) {ρs : ℝ} (hInv : KvnSt.Inv (k - 1) C ε 2 η ρs ν s) {η' : ℝ} (hη' : 0 < η')
    {K₀ : ℕ} (hK₀ : s.n < K₀)
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
      0 ≤ E₀bnd ∧
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
  -- pseudorandomness
  obtain ⟨τ, Cm, hτ0, hmom, hcorr, hmean, hLFC⟩ :=
    Commons.NumberTheory.Sieve.KPseudorandom_data hk hP hεp
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
  have hMsb : (0 : ℝ) ≤ (2 : ℝ) ^ (2 ^ (k - 1) - 1) * (1 + εp) := by positivity
  have hMbound : ∀ (j : Fin (s.n + 1)) (x : ZMod p),
      |davg (k - 1) (fun y => (Function.update s.G s.n (KvnSt.residual f (k - 1) C ε s))
          (j : ℕ) y / (2 * C)) x| ≤ (2 : ℝ) ^ (2 ^ (k - 1) - 1) * (1 + εp) := by
    intro j x
    exact Commons.Combinatorics.Transference.davg_halfC_bound (p := p) (d := k - 1) hd ν _
      hν hC1 (hFj j) hεp hLFC x
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
  -- the tight atom-mass bound
  obtain ⟨E, D, E₀, hEnn, hE₀0, hE₀le, hAtomFin⟩ :=
    exists_bohr_sigma_atom_bound_deg_K0 (p := p) (d := k - 1) (K₀ := K₀) (K := s.n + 1) hd
      (by omega)
      (fun (j : Fin (s.n + 1)) (z : ZMod p) =>
        (Function.update s.G s.n (KvnSt.residual f (k - 1) C ε s)) (j : ℕ) z)
      hν hτ0 hC1 hFj hcorr hmom hεp hεp1 hmean hεp hLFC hMsb hMbound hε hη hη1 hη'
      (fun j => (Function.update s.α s.n αnew) (j : ℕ)) hα0fin hαεfin
      (fun j => (Function.update s.T s.n Tnew) (j : ℕ)) hTfin
  set E₀bnd : ℝ := E * (1 + (((2 ^ (k - 1) * 2 ^ (k - 1) : ℕ)) : ℝ) ^ D *
      ((6 : ℝ) ^ D * (∑ j ∈ Finset.range (D + 1), (if j = 0 then 1 else max (Cm j) 0))))
    with hE₀bnddef
  have hE₀bnd0 : 0 ≤ E₀bnd := by
    rw [hE₀bnddef]
    refine mul_nonneg hEnn (by
      refine add_nonneg zero_le_one ?_
      refine mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) ?_
      refine mul_nonneg (pow_nonneg (by norm_num) _) ?_
      exact Finset.sum_nonneg (fun j _ => by
        by_cases hj : j = 0
        · simp [hj]
        · simp only [hj, if_false]; exact le_max_right _ _))
  have hE₀le' : E₀ ≤ E₀bnd := hE₀bnddef ▸ hE₀le
  -- the atom bound with `E₀bnd`
  have hAtom : ∀ x, |∑ y ∈ kpartExt (k - 1) C ε s.n s.G s.α
      (KvnSt.residual f (k - 1) C ε s) αnew x, (ν y - 1)|
      ≤ KvnDelta (k - 1) ν E₀bnd η' s Tnew := by
    intro x
    rw [kpartExt_eq_atomFilter, KvnDelta]
    have hUnn : 0 ≤ Unorm (k - 1) (fun y : ZMod p => ν y - 1) := Unorm_nonneg (k - 1) hd _
    have hmain : (Fintype.card (ZMod p) : ℝ)
          * (Unorm (k - 1) (fun y : ZMod p => ν y - 1) * E₀
            + η' * ((Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ y, |ν y - 1|))
        ≤ (Fintype.card (ZMod p) : ℝ)
          * (Unorm (k - 1) (fun y : ZMod p => ν y - 1) * E₀bnd
            + η' * ((Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ y, |ν y - 1|)) := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hNpos)
      exact add_le_add (mul_le_mul_of_nonneg_left hE₀le' hUnn) le_rfl
    linarith [hAtomFin x, hmain]
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
    mul_pos (pow_pos (by linarith) _) hε, hMb, hQcl', hE₀bnd0, hAtom, hDelta⟩


/-- The trivial initial state of the Furstenberg tower: no generators, no exceptional set. -/
noncomputable def KvnSt.triv (p : ℕ) [Fact p.Prime] : KvnSt p :=
  ⟨0, fun _ _ => 0, fun _ => 0, fun _ => ∅, ∅, 0⟩

/-- The invariant holds for the trivial state, provided `ν` has mean `1 + O(1)`. -/
lemma KvnSt.inv_triv {k : ℕ} {C ε η ρs : ℝ} (hε : 0 < ε) (hρs : 0 ≤ ρs)
    {ν : ZMod p → ℝ} (hmean : |((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x, ν x - 1| ≤ 2) :
    KvnSt.Inv (k - 1) C ε 2 η ρs ν (KvnSt.triv p) := by
  classical
  have hNpos : (0 : ℝ) < (Fintype.card (ZMod p) : ℝ) := by
    have h : 0 < Fintype.card (ZMod p) := Fintype.card_pos_iff.mpr ⟨0⟩
    exact_mod_cast h
  have hB : ∀ x : ZMod p,
      KvnSt.B (k - 1) C ε (KvnSt.triv p) x = (Finset.univ : Finset (ZMod p)) := by
    intro x
    rw [KvnSt.B, KvnSt.triv, kpart]
    simp
  have hcE : ∀ x : ZMod p,
      |cE (KvnSt.B (k - 1) C ε (KvnSt.triv p)) (fun y => ν y - 1) x| ≤ 2 := by
    intro x
    have h1 : cE (KvnSt.B (k - 1) C ε (KvnSt.triv p)) (fun y => ν y - 1) x
        = ((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ y, (ν y - 1) := by
      rw [cE_apply, hB x]
      simp
    have h2 : ∑ y : ZMod p, (ν y - 1) = (∑ y : ZMod p, ν y) - (Fintype.card (ZMod p) : ℝ) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [h1, h2]
    have h3 : ((Fintype.card (ZMod p) : ℝ))⁻¹ *
        ((∑ y : ZMod p, ν y) - (Fintype.card (ZMod p) : ℝ))
        = ((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ y : ZMod p, ν y - 1 := by
      rw [mul_sub, inv_mul_cancel₀ (ne_of_gt hNpos)]
    rw [h3]
    exact hmean
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x; rw [hB x]; exact Finset.mem_univ x
  · intro x y hy; rw [hB x, hB y]
  · intro x hx; exact absurd hx (Finset.notMem_empty x)
  · refine ⟨hρs, ?_, ?_⟩
    · show (0 : ℝ) ≤ ((0 : ℕ) + 1) * ρs
      push_cast
      linarith
    · show ∑ x ∈ (∅ : Finset (ZMod p)), (ν x + 1) ≤ (0 : ℝ)
      simp
  · intro x hx
    exact hcE x
  · intro j hj; exact absurd hj (Nat.not_lt_zero j)
  · intro j; rfl
  · intro j; exact hε
  · intro j hj; exact absurd hj (Nat.not_lt_zero j)
  · intro j hj; exact absurd hj (Nat.not_lt_zero j)


open Commons.Analysis.Approximation in
/-- The elementary properties of the commons profile `levelJoinPsi η` needed to feed it to the
quantitative Weierstrass lemmas: continuity, values in `[0,1]`, and `ψ 0 = 1`. -/
lemma continuous_levelJoinPsi (η : ℝ) : Continuous (levelJoinPsi η) := by
  unfold Commons.Combinatorics.Transference.levelJoinPsi
  apply Continuous.mul
  · exact Continuous.min continuous_const
      (Continuous.max continuous_const ((continuous_id.add continuous_const).div_const η))
  · exact Continuous.min continuous_const
      (Continuous.max continuous_const
        (((continuous_const.add continuous_const).sub continuous_id).div_const η))

lemma levelJoinPsi_nonneg (η u : ℝ) : 0 ≤ levelJoinPsi η u := by
  unfold Commons.Combinatorics.Transference.levelJoinPsi
  exact mul_nonneg (le_min zero_le_one (le_max_left 0 _))
    (le_min zero_le_one (le_max_left 0 _))

lemma levelJoinPsi_le_one (η u : ℝ) : levelJoinPsi η u ≤ 1 := by
  unfold Commons.Combinatorics.Transference.levelJoinPsi
  have h1 : min 1 (max 0 ((u + η) / η)) ≤ 1 := min_le_left _ _
  have h2 : min 1 (max 0 ((1 + η - u) / η)) ≤ 1 := min_le_left _ _
  have h2' : 0 ≤ min 1 (max 0 ((1 + η - u) / η)) := le_min zero_le_one (le_max_left 0 _)
  calc min 1 (max 0 ((u + η) / η)) * min 1 (max 0 ((1 + η - u) / η))
      ≤ 1 * 1 := mul_le_mul h1 h2 h2' zero_le_one
    _ = 1 := by norm_num

lemma levelJoinPsi_zero {η : ℝ} (hη : 0 < η) : levelJoinPsi η 0 = 1 := by
  unfold Commons.Combinatorics.Transference.levelJoinPsi
  have h1 : (1 : ℝ) ≤ (0 + η) / η := by
    rw [zero_add, div_self (ne_of_gt hη)]
  have h2 : (1 : ℝ) ≤ (1 + η - 0) / η := by
    rw [sub_zero, le_div_iff₀ hη]; linarith
  rw [max_eq_right (le_trans zero_le_one h1), min_eq_left h1,
      max_eq_right (le_trans zero_le_one h2), min_eq_left h2, mul_one]

/-- The `K₀`-uniform quantitative Weierstrass data of the tower's profiles: the coefficient-mass
bound `E` and total-degree bound `D` valid for every `K ≤ K₀` and every shift vector. -/
noncomputable def KvnPolyED (K₀ : ℕ) (M ε η η' : ℝ) (hM : 0 ≤ M) (hε : 0 < ε)
    (hη : 0 < η) (hη' : 0 < η') : ℝ × ℕ :=
  let h := Commons.Analysis.Approximation.exists_poly_weight_family_deg_K0 (K₀ := K₀) (M := M) (ε := ε) (C := M + ε) (η' := η')
    hM hε (by linarith) hη' (continuous_levelJoinPsi η).continuousOn
    (fun u _ => ⟨levelJoinPsi_nonneg η u, levelJoinPsi_le_one η u⟩) (levelJoinPsi_zero hη)
  (Classical.choose h, Classical.choose (Classical.choose_spec h))

noncomputable def KvnPolyE (K₀ : ℕ) (M ε η η' : ℝ) (hM : 0 ≤ M) (hε : 0 < ε)
    (hη : 0 < η) (hη' : 0 < η') : ℝ := (KvnPolyED K₀ M ε η η' hM hε hη hη').1

noncomputable def KvnPolyD (K₀ : ℕ) (M ε η η' : ℝ) (hM : 0 ≤ M) (hε : 0 < ε)
    (hη : 0 < η) (hη' : 0 < η') : ℕ := (KvnPolyED K₀ M ε η η' hM hε hη hη').2

/-- The defining property of `KvnPolyE`, `KvnPolyD`. -/
lemma KvnPoly_spec {K₀ : ℕ} {M ε η η' : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) (hη : 0 < η)
    (hη' : 0 < η') :
    ∀ (K : ℕ) (hK : K ≤ K₀) (c : Fin K → ℝ), (∀ j, |c j| ≤ M + ε) →
      ∃ P : MvPolynomial (Fin K) ℝ,
        (∀ t ∈ Set.pi Set.univ (fun _ : Fin K => Set.Icc (-M) M),
          |∏ j, levelJoinPsi η ((t j - c j) / ε) - MvPolynomial.eval t P| ≤ η') ∧
        (∑ m ∈ P.support, |P.coeff m|) ≤ KvnPolyE K₀ M ε η η' hM hε hη hη' ∧
        P.totalDegree ≤ KvnPolyD K₀ M ε η η' hM hε hη hη' :=
  (Classical.choose_spec (Classical.choose_spec (Commons.Analysis.Approximation.exists_poly_weight_family_deg_K0 (K₀ := K₀)
    (M := M) (ε := ε) (C := M + ε) (η' := η') hM hε (by linarith) hη'
    (continuous_levelJoinPsi η).continuousOn
    (fun u _ => ⟨levelJoinPsi_nonneg η u, levelJoinPsi_le_one η u⟩) (levelJoinPsi_zero hη)))).2

end GTTrans
