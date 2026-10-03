import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.DualityDefs
import Submission.Work.ORHughesFree.NaturalExtension.DualityAPI
import Submission.Work.ORHughesFree.NaturalExtension.supConstDefs
import Submission.Work.ORHughesFree.NaturalExtension.blim_of_tendsto
import Submission.Work.ORHughesFree.NaturalExtension.blim_mono
import Submission.Work.ORHughesFree.NaturalExtension.blim_congr
import Submission.Work.ORHughesFree.NaturalExtension.rdim_fin_one_eq
import Submission.Work.ORHughesFree.NaturalExtension.rk_trunc_eq_rk_Cmat
import Submission.Work.ORHughesFree.NaturalExtension.rdim_rowSpanBmat_add_kerBmat
import Submission.Work.ORHughesFree.NaturalExtension.DensityDuality
import Submission.Work.ORHughesFree.NaturalExtension.CmatDegPartCompare
import Submission.Work.ORHughesFree.NaturalExtension.rowSpanBmat_degPart_kerBmat
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.RankAPI.rk_le_left
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

universe u

namespace Work.ORHughesFree.NaturalExtension

open Matrix Work.ORHughesFree Filter

variable {R : Type u} [Ring R] [VonNeumannRegularRing R] [MulSemiringAction (Multiplicative ℤ) R]

/-- **The duality `σ + τ ≥ 1`** (JZLA20, Prop. 3.4; López-Álvarez thesis, Prop. 1.5.5): for a
von Neumann regular ring `R` with a `τ`-compatible Sylvester rank function `rk` and a polynomial
`p ∈ R[t^{±1};τ]`, the supremum of the ranks of the constant terms of the polynomial left
multiples of `p` plus the supremum of the ranks of the constant terms of the polynomial left
annihilators of `p` is at least `1`.

Proof outline: writing `σ` and `τ` for the two suprema, the sequence
`F i = rk (trunc i (oneByOne p)) / i` satisfies `F i ≤ σ + O(1/i)` (via
`CmatDegPartCompare` and the iterated density `rdim_degPart_add_le` for the ideal `S·p`) and
`F i ≥ 1 - τ - O(1/i)` (via `rdim_rowSpanBmat_add_kerBmat`, `rowSpanBmat_degPart_kerBmat` and
the density for the annihilator ideal).  Taking the ultralimit along any ultrafilter containing
the cofinite filter gives both `blim ω F ≤ σ` and `1 - τ ≤ blim ω F`, hence `σ + τ ≥ 1`. -/
theorem supConstMain {R : Type u} [Ring R] [VonNeumannRegularRing R] [MulSemiringAction (Multiplicative ℤ) R]
    (rk : SylvesterRank R)
    (hτ : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) R),
      rk.rk n m (A.map (fun a => (Multiplicative.ofAdd (1 : ℤ)) • a)) = rk.rk n m A)
    (p : SkewL R) (hp : ∀ k : ℤ, k < 0 → coeffElt p k = 0) :
    sSup {y : ℝ | ∃ c ∈ C0set R p, y = rk.rk 1 1 (oneByOne c)}
      + sSup {y : ℝ | ∃ c ∈ C1set R p, y = rk.rk 1 1 (oneByOne c)} ≥ 1 := by
  classical
  set σ : ℝ := sSup {y : ℝ | ∃ c ∈ C0set R p, y = rk.rk 1 1 (oneByOne c)} with hσdef
  set τ : ℝ := sSup {y : ℝ | ∃ c ∈ C1set R p, y = rk.rk 1 1 (oneByOne c)} with hτdef
  have hzero0 : (0 : R) ∈ C0set R p :=
    ⟨0, 0, by rw [zero_mul], fun k _ => by simp [coeffElt], by simp [coeffElt]⟩
  have hzero1 : (0 : R) ∈ C1set R p :=
    ⟨0, by rw [zero_mul], fun k _ => by simp [coeffElt], by simp [coeffElt]⟩
  have hle_one : ∀ c : R, rk.rk 1 1 (oneByOne c) ≤ 1 :=
    fun c => by simpa using RankAPI.rk_le_left rk (oneByOne c)
  have hbdd0 : BddAbove {y : ℝ | ∃ c ∈ C0set R p, y = rk.rk 1 1 (oneByOne c)} :=
    ⟨1, by rintro y ⟨c, -, rfl⟩; exact hle_one c⟩
  have hbdd1 : BddAbove {y : ℝ | ∃ c ∈ C1set R p, y = rk.rk 1 1 (oneByOne c)} :=
    ⟨1, by rintro y ⟨c, -, rfl⟩; exact hle_one c⟩
  have hone : oneByOne (0 : R) = 0 := by ext i j; simp [oneByOne]
  have hσ0 : 0 ≤ σ := by
    rw [hσdef]
    exact le_csSup hbdd0 ⟨0, hzero0, by rw [hone, rk.rk_zero]⟩
  have hτ0 : 0 ≤ τ := by
    rw [hτdef]
    exact le_csSup hbdd1 ⟨0, hzero1, by rw [hone, rk.rk_zero]⟩
  have hσeq : σ = rdim rk (C0sub p) := by
    rw [hσdef, rdim_fin_one_eq rk (C0sub p)]
    congr 1
  have hτeq : τ = rdim rk (C1sub p) := by
    rw [hτdef, rdim_fin_one_eq rk (C1sub p)]
    congr 1
  have hbσ : ∀ j : ℕ, rdim rk (constIdeal (genIdeal p) j) ≤ σ := by
    intro j
    rw [hσeq]
    exact rdim_mono rk (constIdeal_genIdeal_le_C0sub p j)
  have hbτ : ∀ j : ℕ, rdim rk (constIdeal (annSet p) j) ≤ τ := by
    intro j
    rw [hτeq]
    exact rdim_mono rk (constIdeal_annSet_le_C1sub p j)
  have hub : ∀ n : ℕ, rk.rk (n + 1) (n + 1) (Cmat p n)
      ≤ rdim rk (degPart R (genIdeal p) 0) + (n : ℝ) * σ + (upDeg p : ℝ) := by
    intro n
    have h1 := (CmatDegPartCompare rk p hp n).1
    have h2 : rdim rk (degPart R (genIdeal p) n)
        ≤ rdim rk (degPart R (genIdeal p) 0) + (n : ℝ) * σ := by
      have h := rdim_degPart_add_le rk hτ (genIdeal p) (isLeftIdeal_genIdeal p) σ hbσ 0 n
      rw [Nat.zero_add] at h
      exact h
    linarith
  have hlb : ∀ n : ℕ, (n : ℝ) + 1 - rdim rk (degPart R (annSet p) 0) - (n : ℝ) * τ
      - ((upDeg p : ℝ) + (upDeg p : ℝ) * σ) ≤ rk.rk (n + 1) (n + 1) (Cmat p n) := by
    intro n
    have h1 := rdim_rowSpanBmat_add_kerBmat rk p hp n
    have h2 : rdim rk (rowSpanBmat p n) ≤ rdim rk (degPart R (genIdeal p) (n + upDeg p)) :=
      rdim_mono rk (rowSpanBmat_degPart_kerBmat rk p hp n).1
    have h3 : rdim rk (degPart R (genIdeal p) (n + upDeg p))
        ≤ rdim rk (degPart R (genIdeal p) n) + ((upDeg p : ℕ) : ℝ) * σ :=
      rdim_degPart_add_le rk hτ (genIdeal p) (isLeftIdeal_genIdeal p) σ hbσ n (upDeg p)
    have h4 : rdim rk (kerBmat p n) ≤ rdim rk (degPart R (annSet p) n) :=
      rdim_mono rk (rowSpanBmat_degPart_kerBmat rk p hp n).2
    have h5 : rdim rk (degPart R (annSet p) n)
        ≤ rdim rk (degPart R (annSet p) 0) + (n : ℝ) * τ := by
      have h := rdim_degPart_add_le rk hτ (annSet p) (isLeftIdeal_annSet p) τ hbτ 0 n
      rw [Nat.zero_add] at h
      exact h
    have h6 := (CmatDegPartCompare rk p hp n).2
    linarith
  obtain ⟨ω, hω⟩ := exists_ultrafilter_le_atTop
  set F : ℕ → ℝ := fun i => rk.rk (1 * i) (1 * i) (trunc i (oneByOne p)) / (i : ℝ) with hF
  set Fσ : ℕ → ℝ := fun i => if i = 0 then 0 else F i with hFσ
  set Fτ : ℕ → ℝ := fun i => if i = 0 then 1 - τ else F i with hFτ
  have hFσ0 : Fσ 0 = 0 := by simp [hFσ]
  have hFτ0 : Fτ 0 = 1 - τ := by simp [hFτ]
  have hFσsucc : ∀ n : ℕ, Fσ (n + 1) = F (n + 1) := by intro n; simp [hFσ]
  have hFτsucc : ∀ n : ℕ, Fτ (n + 1) = F (n + 1) := by intro n; simp [hFτ]
  have hFn : ∀ n : ℕ, F (n + 1) = rk.rk (n + 1) (n + 1) (Cmat p n) / (((n + 1 : ℕ)) : ℝ) := by
    intro n
    simp only [hF]
    rw [rk_trunc_eq_rk_Cmat rk p n]
  have hFσeq : Fσ =ᶠ[Filter.atTop] F := by
    filter_upwards [Filter.eventually_ge_atTop 1] with i hi
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    exact hFσsucc n
  have hFτeq : Fτ =ᶠ[Filter.atTop] F := by
    filter_upwards [Filter.eventually_ge_atTop 1] with i hi
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    exact hFτsucc n
  have hFpos : ∀ n : ℕ, 0 ≤ F (n + 1) := by
    intro n; rw [hFn n]; exact div_nonneg (rk.nonneg _) (by positivity)
  have hFle1 : ∀ n : ℕ, F (n + 1) ≤ 1 := by
    intro n
    rw [hFn n, div_le_iff₀ (by positivity : (0:ℝ) < (((n + 1 : ℕ)) : ℝ))]
    have h := RankAPI.rk_le_left rk (Cmat p n)
    push_cast at h ⊢
    linarith
  have hFσbdd : ∀ i : ℕ, |Fσ i| ≤ 1 := by
    intro i
    rw [abs_le]
    constructor
    · rcases Nat.eq_zero_or_pos i with hi | hi
      · subst hi; rw [hFσ0]; norm_num
      · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hi)
        rw [hFσsucc n]; linarith [hFpos n]
    · rcases Nat.eq_zero_or_pos i with hi | hi
      · subst hi; rw [hFσ0]; norm_num
      · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hi)
        rw [hFσsucc n]; exact hFle1 n
  have hFτbdd : ∀ i : ℕ, |Fτ i| ≤ |1 - τ| + 1 := by
    intro i
    rcases Nat.eq_zero_or_pos i with hi | hi
    · subst hi; rw [hFτ0]; linarith [abs_nonneg (1 - τ)]
    · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hi)
      rw [hFτsucc n]
      have h1 : |F (n + 1)| ≤ 1 := by
        rw [abs_le]; exact ⟨by linarith [hFpos n], hFle1 n⟩
      linarith [abs_nonneg (1 - τ)]
  have hFσub : ∀ i : ℕ, Fσ i
      ≤ σ + (rdim rk (degPart R (genIdeal p) 0) + (upDeg p : ℝ)) / (i : ℝ) := by
    intro i
    rcases Nat.eq_zero_or_pos i with hi | hi
    · subst hi; rw [hFσ0, Nat.cast_zero, div_zero, add_zero]; exact hσ0
    · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hi)
      rw [hFσsucc n, hFn n]
      have hx : (0 : ℝ) < (((n + 1 : ℕ)) : ℝ) := by positivity
      have hcast : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [div_le_iff₀ hx, add_mul, div_mul_cancel₀ _ (ne_of_gt hx), hcast]
      have h1 := hub n
      nlinarith [h1, hσ0]
  have hFτlb : ∀ i : ℕ, 1 - τ - (rdim rk (degPart R (annSet p) 0) + (upDeg p : ℝ)
      + (upDeg p : ℝ) * σ) / (i : ℝ) ≤ Fτ i := by
    intro i
    rcases Nat.eq_zero_or_pos i with hi | hi
    · subst hi; rw [hFτ0, Nat.cast_zero, div_zero, sub_zero]
    · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hi)
      rw [hFτsucc n, hFn n]
      have hx : (0 : ℝ) < (((n + 1 : ℕ)) : ℝ) := by positivity
      have hcast : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [le_div_iff₀ hx, sub_mul, sub_mul, div_mul_cancel₀ _ (ne_of_gt hx), hcast]
      have h1 := hlb n
      nlinarith [h1, hτ0]
  have hdiv_le : ∀ (C : ℝ) (i : ℕ), 0 ≤ C → C / (i : ℝ) ≤ C := by
    intro C i hC
    rcases Nat.eq_zero_or_pos i with hi | hi
    · subst hi; simp [hC]
    · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hi)
      rw [div_le_iff₀ (by positivity : (0:ℝ) < (((n + 1 : ℕ)) : ℝ))]
      have hcast : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      nlinarith [hC, Nat.cast_nonneg (α := ℝ) n]
  have hub_bdd : ∀ i : ℕ, |σ + (rdim rk (degPart R (genIdeal p) 0) + (upDeg p : ℝ)) / (i : ℝ)|
      ≤ σ + (rdim rk (degPart R (genIdeal p) 0) + (upDeg p : ℝ)) := by
    intro i
    have hC : 0 ≤ rdim rk (degPart R (genIdeal p) 0) + (upDeg p : ℝ) := by
      have := rdim_nonneg rk (degPart R (genIdeal p) 0); positivity
    rw [abs_le]
    constructor
    · have h2 : 0 ≤ (rdim rk (degPart R (genIdeal p) 0) + (upDeg p : ℝ)) / (i : ℝ) :=
        div_nonneg hC (by positivity)
      linarith
    · linarith [hdiv_le _ i hC]
  have hlb_bdd : ∀ i : ℕ, |1 - τ - (rdim rk (degPart R (annSet p) 0) + (upDeg p : ℝ)
      + (upDeg p : ℝ) * σ) / (i : ℝ)|
      ≤ (rdim rk (degPart R (annSet p) 0) + (upDeg p : ℝ) + (upDeg p : ℝ) * σ) + |1 - τ| := by
    intro i
    have hC : 0 ≤ rdim rk (degPart R (annSet p) 0) + (upDeg p : ℝ) + (upDeg p : ℝ) * σ := by
      have h1 := rdim_nonneg rk (degPart R (annSet p) 0); positivity
    rw [abs_le]
    constructor
    · have h2 : (rdim rk (degPart R (annSet p) 0) + (upDeg p : ℝ) + (upDeg p : ℝ) * σ) / (i : ℝ) ≤
          rdim rk (degPart R (annSet p) 0) + (upDeg p : ℝ) + (upDeg p : ℝ) * σ :=
        hdiv_le _ i hC
      have h3 := neg_abs_le (1 - τ)
      linarith
    · have h2 : 0 ≤ (rdim rk (degPart R (annSet p) 0) + (upDeg p : ℝ) + (upDeg p : ℝ) * σ) / (i : ℝ) :=
        div_nonneg hC (by positivity)
      linarith [le_abs_self (1 - τ)]
  have h1 : blim ω Fσ ≤ blim ω (fun i : ℕ =>
      σ + (rdim rk (degPart R (genIdeal p) 0) + (upDeg p : ℝ)) / (i : ℝ)) :=
    blim_mono ω hFσbdd hub_bdd hFσub
  have h2 : blim ω (fun i : ℕ =>
      σ + (rdim rk (degPart R (genIdeal p) 0) + (upDeg p : ℝ)) / (i : ℝ)) = σ :=
    blim_of_tendsto ω hω hub_bdd (by
      simpa using (Tendsto.add tendsto_const_nhds
        (tendsto_const_div_atTop_nhds_zero_nat
          (rdim rk (degPart R (genIdeal p) 0) + (upDeg p : ℝ)))))
  have h3 : blim ω Fσ = blim ω F := blim_congr ω hω hFσeq
  have h4 : blim ω Fτ = blim ω F := blim_congr ω hω hFτeq
  have h5 : blim ω (fun i : ℕ => 1 - τ - (rdim rk (degPart R (annSet p) 0) + (upDeg p : ℝ)
      + (upDeg p : ℝ) * σ) / (i : ℝ)) ≤ blim ω Fτ :=
    blim_mono ω hlb_bdd hFτbdd hFτlb
  have h6 : blim ω (fun i : ℕ => 1 - τ - (rdim rk (degPart R (annSet p) 0) + (upDeg p : ℝ)
      + (upDeg p : ℝ) * σ) / (i : ℝ)) = 1 - τ :=
    blim_of_tendsto ω hω hlb_bdd (by
      simpa using (Tendsto.sub tendsto_const_nhds
        (tendsto_const_div_atTop_nhds_zero_nat
          (rdim rk (degPart R (annSet p) 0) + (upDeg p : ℝ) + (upDeg p : ℝ) * σ))))
  linarith

end Work.ORHughesFree.NaturalExtension
