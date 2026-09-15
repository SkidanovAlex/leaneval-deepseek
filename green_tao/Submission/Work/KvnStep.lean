import Submission.Work.KvnCorr
import Submission.Work.KvnCount
import Submission.Commons.Combinatorics.Transference.bohr_sigma_atom_gen
import Submission.Commons.Combinatorics.Transference.bohr_sigma_Omega
import Submission.Commons.Combinatorics.Transference.exists_shift_boundary_cover
import Submission.Commons.Combinatorics.Transference.cube_lfc_half
import Submission.Commons.Combinatorics.Transference.davg_bound
import Submission.Commons.Combinatorics.Transference.energy_increment_exceptional

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# The Green–Tao §7 iterative step

Green–Tao §8 (`Proposition 8.2`, `Proposition 7.2` of the published paper) run a Furstenberg
tower: starting from the trivial σ-algebra and the exceptional set `∅`, at each stage one adds
the level sets of `𝒟F_{K+1}` (where `F_{K+1} = (1 - 1_{Ω_K})(f - 𝔼(f|B_K))`) to the σ-algebra,
and lets `Ω_{K+1}` be the exceptional set produced by the `bohr-sigma` estimate.  If the
Gowers `U^{k-1}` norm of `F_{K+1}` is still `> ε^{1/2^k}`, the `L²` energy of `𝔼(f|B_K)`
increases by a definite amount, so the algorithm terminates.

This file sets up the σ-algebras `B_K` as joins of level-set σ-algebras (indexed by `ℕ` so that
the recursion is straightforward) and proves the helper lemmas used by the single step.
-/

open Finset
open scoped BigOperators

namespace GTTrans

open Commons.Combinatorics.Transference
open FinSigma

/-- The σ-algebra `B_K` of Green–Tao §8: the join of the level-set σ-algebras of
`𝒟(F_j/(2C))` at resolution `ε` with shift `α j`, over all generators `j < K`, presented by its
atoms. -/
noncomputable def kpart {p : ℕ} [Fact p.Prime] (d : ℕ) (C ε : ℝ) (K : ℕ)
    (G : ℕ → ZMod p → ℝ) (α : ℕ → ℝ) (x : ZMod p) : Finset (ZMod p) :=
  Finset.univ.filter (fun y => ∀ j : ℕ, j < K →
    ⌊(davg d (fun z => G j z / (2 * C)) y - α j) / ε⌋
      = ⌊(davg d (fun z => G j z / (2 * C)) x - α j) / ε⌋)

lemma mem_kpart {p : ℕ} [Fact p.Prime] (d : ℕ) (C ε : ℝ) (K : ℕ)
    (G : ℕ → ZMod p → ℝ) (α : ℕ → ℝ) (x y : ZMod p) :
    y ∈ kpart d C ε K G α x ↔ ∀ j : ℕ, j < K →
      ⌊(davg d (fun z => G j z / (2 * C)) y - α j) / ε⌋
        = ⌊(davg d (fun z => G j z / (2 * C)) x - α j) / ε⌋ := by
  rw [kpart, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ y, h⟩⟩

lemma kpart_mem_self {p : ℕ} [Fact p.Prime] (d : ℕ) (C ε : ℝ) (K : ℕ)
    (G : ℕ → ZMod p → ℝ) (α : ℕ → ℝ) (x : ZMod p) : x ∈ kpart d C ε K G α x := by
  rw [mem_kpart]; intro j _; rfl

lemma kpart_eq_of_mem {p : ℕ} [Fact p.Prime] (d : ℕ) (C ε : ℝ) (K : ℕ)
    (G : ℕ → ZMod p → ℝ) (α : ℕ → ℝ) {x y : ZMod p}
    (hy : y ∈ kpart d C ε K G α x) : kpart d C ε K G α y = kpart d C ε K G α x := by
  rw [mem_kpart] at hy
  ext z
  rw [mem_kpart, mem_kpart]
  exact ⟨fun hz j hj => (hz j hj).trans (hy j hj), fun hz j hj => (hz j hj).trans (hy j hj).symm⟩

/-- The `ℕ`-indexed σ-algebra `kpart` agrees with the `Fin K`-indexed `levelJoin`. -/
lemma kpart_eq_levelJoin {p : ℕ} [Fact p.Prime] (d : ℕ) (C ε : ℝ) (K : ℕ)
    (G : ℕ → ZMod p → ℝ) (α : ℕ → ℝ) (x : ZMod p) :
    kpart d C ε K G α x
      = levelJoin d (fun j : Fin K => fun z => G (j : ℕ) z / (2 * C)) ε
          (fun j : Fin K => α (j : ℕ)) x := by
  rw [kpart, levelJoin]
  apply Finset.filter_congr
  intro y _
  constructor
  · intro h j; exact h (j : ℕ) j.isLt
  · intro h j hj; exact h ⟨j, hj⟩

/-- The join `kpart (K+1)` refines `kpart K` (the generators `j < K` are unchanged). -/
lemma kpart_succ_subset {p : ℕ} [Fact p.Prime] (d : ℕ) (C ε : ℝ) (K : ℕ)
    (G : ℕ → ZMod p → ℝ) (α : ℕ → ℝ) (Fnew : ZMod p → ℝ) (αnew : ℝ) (x : ZMod p) :
    kpart d C ε (K + 1) (Function.update G K Fnew) (Function.update α K αnew) x
      ⊆ kpart d C ε K G α x := by
  intro y hy
  rw [mem_kpart] at hy ⊢
  intro j hj
  have hlt : j < K := hj
  have hne : j ≠ K := by omega
  have := hy j (by omega)
  rwa [Function.update_of_ne hne, Function.update_of_ne hne] at this

/-- **Sup-norm bound for the scaled generator.**  If `ν` satisfies the cube linear forms
condition at scale `d` with error `ε` and `|F| ≤ C(ν+1)` with `C ≥ 1`, `ν ≥ 0`, then the scaled
dual function `𝒟(F/(2C))` is bounded by `2^{2^d-1}(1+ε)`.  This is the `M` of Green–Tao
`(8.17)`. -/
lemma davg_halfC_bound {p : ℕ} [Fact p.Prime] {d : ℕ} (hd : 1 ≤ d) (ν F : ZMod p → ℝ)
    (hν : ∀ x, 0 ≤ ν x) {C : ℝ} (hC : 1 ≤ C) (hF : ∀ x, |F x| ≤ C * (ν x + 1))
    {ε : ℝ} (hε : 0 ≤ ε)
    (hLFC : ∀ A : Finset (Fin d → Bool), A ⊆ Finset.univ.erase (0 : Fin d → Bool) →
      A.Nonempty → ∀ b : ZMod p,
      |((Fintype.card (Fin d → ZMod p) : ℝ))⁻¹ *
        (∑ h : Fin d → ZMod p,
          ∏ ω ∈ A, ν (b + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j)) - 1| ≤ ε) :
    ∀ x, |davg d (fun y => F y / (2 * C)) x| ≤ (2 : ℝ) ^ (2 ^ d - 1) * (1 + ε) := by
  intro x
  have hCpos : 0 < C := by linarith
  have hLFC' := cube_lfc_half (d := d) ν hε hLFC
  have hF' : ∀ y, |F y / (2 * C)| ≤ (ν y + 1) / 2 + 1 := by
    intro y
    have h2C : (0 : ℝ) < 2 * C := by linarith
    rw [abs_div, abs_of_pos h2C]
    have hstep : |F y| / (2 * C) ≤ C * (ν y + 1) / (2 * C) :=
      div_le_div_of_nonneg_right (hF y) h2C.le
    have heq : C * (ν y + 1) / (2 * C) = (ν y + 1) / 2 := by
      rw [show (2 : ℝ) * C = C * 2 by ring]
      exact mul_div_mul_left (ν y + 1) 2 (ne_of_gt hCpos)
    linarith
  exact davg_bound hd (fun y => (ν y + 1) / 2) (fun y => F y / (2 * C)) hF' hε hLFC' x

/-- The σ-algebra `B_{K+1}` obtained from `B_K` (atoms `kpart d C ε K G α`) by adjoining the
level sets of the new generator `Fnew` at resolution `ε` with shift `αnew`. -/
noncomputable def kpartExt {p : ℕ} [Fact p.Prime] (d : ℕ) (C ε : ℝ) (K : ℕ)
    (G : ℕ → ZMod p → ℝ) (α : ℕ → ℝ) (Fnew : ZMod p → ℝ) (αnew : ℝ) : ZMod p → Finset (ZMod p) :=
  kpart d C ε (K + 1) (Function.update G K Fnew) (Function.update α K αnew)

lemma kpartExt_mem_self {p : ℕ} [Fact p.Prime] (d : ℕ) (C ε : ℝ) (K : ℕ)
    (G : ℕ → ZMod p → ℝ) (α : ℕ → ℝ) (Fnew : ZMod p → ℝ) (αnew : ℝ) (x : ZMod p) :
    x ∈ kpartExt d C ε K G α Fnew αnew x :=
  kpart_mem_self d C ε (K + 1) _ _ x

lemma kpartExt_eq_of_mem {p : ℕ} [Fact p.Prime] (d : ℕ) (C ε : ℝ) (K : ℕ)
    (G : ℕ → ZMod p → ℝ) (α : ℕ → ℝ) (Fnew : ZMod p → ℝ) (αnew : ℝ) {x y : ZMod p}
    (hy : y ∈ kpartExt d C ε K G α Fnew αnew x) :
    kpartExt d C ε K G α Fnew αnew y = kpartExt d C ε K G α Fnew αnew x :=
  kpart_eq_of_mem d C ε (K + 1) _ _ hy

lemma kpartExt_subset_kpart {p : ℕ} [Fact p.Prime] (d : ℕ) (C ε : ℝ) (K : ℕ)
    (G : ℕ → ZMod p → ℝ) (α : ℕ → ℝ) (Fnew : ZMod p → ℝ) (αnew : ℝ) (x : ZMod p) :
    kpartExt d C ε K G α Fnew αnew x ⊆ kpart d C ε K G α x :=
  kpart_succ_subset d C ε K G α Fnew αnew x


/-- **The core of the Green–Tao §7 iterative step, abstract σ-algebra form.**

Given a partition `P = B_K` (atoms `P`), a refinement `Q = B_{K+1}` of `P`, an exceptional set
`Ω` which is a union of `P`-atoms, a new generator `Fnew` vanishing on `Ω` and equal to the
residual `f - 𝔼(f|P)` outside `Ω`, the atom-mass bound `δ` for `Q`, and the threshold `θ`,
there is a `Q`-saturated exceptional set `Ω' ⊇ Ω` with

* `∑_{Ω'}(ν+1) ≤ |G|θ·#atoms(Q) + ∑_Ω(ν+1)`,
* `|𝔼(ν-1|Q)| ≤ 2δ/(|G|θ-δ)` outside `Ω'`,
* (energy increment) `‖(1-1_Ω)𝔼(f|P)‖² + (|G|γ₀/2)²/(|G|M²) ≤ ‖(1-1_{Ω'})𝔼(f|Q)‖² + O(η)`.

The two analytic inputs — the atom-mass bound (`bohr_sigma_atom_gen`) and the correlation
lower bound (`dual_corr_lower`) — enter as hypotheses. -/
theorem energy_step_core {p : ℕ} [Fact p.Prime] {d : ℕ} (hd : 1 ≤ d)
    (P Q : ZMod p → Finset (ZMod p)) (hPmem : ∀ x, x ∈ P x)
    (hPeq : ∀ x y : ZMod p, y ∈ P x → P y = P x) (hQmem : ∀ x, x ∈ Q x)
    (hQeq : ∀ x y : ZMod p, y ∈ Q x → Q y = Q x) (href : ∀ x, Q x ⊆ P x)
    (Ω : Finset (ZMod p)) (hΩsat : ∀ x ∈ Ω, P x ⊆ Ω)
    (ν : ZMod p → ℝ) (hν : ∀ x, 0 ≤ ν x)
    (f : ZMod p → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hfν : ∀ x, f x ≤ ν x)
    (Fnew : ZMod p → ℝ) (hFnew_0 : ∀ x ∈ Ω, Fnew x = 0)
    (hFnew_out : ∀ x, x ∉ Ω → Fnew x = f x - cE P f x)
    {Mraw εraw : ℝ} (hMpos : 0 < Mraw) (hεraw : 0 < εraw)
    (hMb : ∀ x, |davg d Fnew x| ≤ Mraw)
    (hQcl : ∀ x y : ZMod p, y ∈ Q x → |davg d Fnew y - davg d Fnew x| ≤ εraw)
    {θ δ B γ₀ ρ : ℝ} (hθ : 0 < θ) (hδ0 : 0 ≤ δ) (hB0 : 0 ≤ B) (hγ0 : 0 ≤ γ₀)
    (hδθ : δ < (Fintype.card (ZMod p) : ℝ) * θ)
    (hAtom : ∀ x, |∑ y ∈ Q x, (ν y - 1)| ≤ δ)
    (hAbound : ∀ x, x ∉ Ω → |cE P f x| ≤ B)
    (hUb : γ₀ ≤ Unorm d Fnew ^ (2 ^ d))
    (hmass : ∑ x ∈ Ω, (ν x + 1) ≤ ρ)
    (hγpos : Mraw * ((1 + B) * ((Fintype.card (ZMod p) : ℝ) * θ *
          ((Finset.univ.image Q).card : ℝ) + ρ))
        + εraw * (∑ x, |Fnew x|) ≤ (Fintype.card (ZMod p) : ℝ) * γ₀ / 2) :
    ∃ Ω' : Finset (ZMod p), Ω ⊆ Ω' ∧
      (∀ x ∈ Ω', Q x ⊆ Ω') ∧
      (∑ x ∈ Ω', (ν x + 1) ≤ (Fintype.card (ZMod p) : ℝ) * θ *
          ((Finset.univ.image Q).card : ℝ) + ρ) ∧
      (∀ x : ZMod p, x ∉ Ω' → |cE Q (fun y => ν y - 1) x|
          ≤ 2 * δ / ((Fintype.card (ZMod p) : ℝ) * θ - δ)) ∧
      (∑ x ∈ Finset.univ \ Ω, (cE P f x) ^ 2
          + ((Fintype.card (ZMod p) : ℝ) * γ₀ / 2) ^ 2 /
              ((Fintype.card (ZMod p) : ℝ) * Mraw ^ 2)
        ≤ ∑ x ∈ Finset.univ \ Ω', (cE Q f x) ^ 2
          + B ^ 2 * (((Ω' \ Ω).card : ℝ)) + 2 * B * ((1 + B) *
              ((Fintype.card (ZMod p) : ℝ) * θ *
                ((Finset.univ.image Q).card : ℝ) + ρ))) := by
  classical
  haveI : Nonempty (ZMod p) := ⟨0⟩
  set N : ℝ := (Fintype.card (ZMod p) : ℝ) with hNdef
  set hh : ZMod p → ℝ := cE Q (davg d Fnew) with hhh
  have hΩsatQ : ∀ x ∈ Ω, Q x ⊆ Ω := fun x hx => (href x).trans (hΩsat x hx)
  -- ## the exceptional set from `bohr_sigma_Omega`
  obtain ⟨Ωnew, hmass_new, hsat_new, hcE_new⟩ :=
    bohr_sigma_Omega Q hQmem hQeq ν hν hθ hδ0 hδθ hAtom
  refine ⟨Ω ∪ Ωnew, Finset.subset_union_left, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_union] at hx
    rcases hx with hx | hx
    · exact (hΩsatQ x hx).trans Finset.subset_union_left
    · exact (hsat_new x hx).trans Finset.subset_union_right
  · -- mass bound
    have h1 := Finset.sum_union_inter (s₁ := Ω) (s₂ := Ωnew)
      (f := fun x : ZMod p => ν x + 1)
    have h2 : (0 : ℝ) ≤ ∑ x ∈ Ω ∩ Ωnew, (ν x + 1) :=
      Finset.sum_nonneg (fun x _ => by have := hν x; linarith)
    have h3 : ∑ x ∈ Ωnew, (ν x + 1) ≤ N * θ *
        ((Finset.univ.image Q).card : ℝ) := hmass_new
    linarith
  · -- `cE (ν-1)` bound outside `Ω'`
    intro x hx
    rw [Finset.mem_union] at hx
    push Not at hx
    exact hcE_new x hx.2
  · -- energy increment
    have hΩsub : Ω ⊆ Ω ∪ Ωnew := Finset.subset_union_left
    have hΩ'sat : ∀ x ∈ Ω ∪ Ωnew, Q x ⊆ Ω ∪ Ωnew := by
      intro x hx
      rw [Finset.mem_union] at hx
      rcases hx with hx | hx
      · exact (hΩsatQ x hx).trans Finset.subset_union_left
      · exact (hsat_new x hx).trans Finset.subset_union_right
    have hhmeas : ∀ x y : ZMod p, y ∈ Q x → hh y = hh x := by
      intro x y hy
      rw [hhh]
      exact cE_measurable hQeq (davg d Fnew) x y hy
    have hhM : ∀ x, |hh x| ≤ Mraw := by
      intro x
      rw [hhh]
      refine le_trans (abs_cE_le (part := Q) (davg d Fnew) x) ?_
      refine le_trans (cE_mono (part := Q) (fun y => |davg d Fnew y|) (fun _ => Mraw)
        (fun y => hMb y) x) ?_
      rw [cE_const hQmem]
    have hdual := dual_corr_lower (p := p) (d := d) hd P Q hQmem Ω (Ω ∪ Ωnew) hΩsub
      hΩ'sat Fnew f hFnew_0
      (fun x hx => by
        rw [Finset.mem_union] at hx; push Not at hx
        exact hFnew_out x hx.1)
      hMpos.le hεraw hMb hQcl hUb
    have hFnew_bound : ∀ x, |Fnew x| ≤ (1 + B) * (ν x + 1) := by
      intro x
      by_cases hx : x ∈ Ω
      · rw [hFnew_0 x hx]
        have h1 : (0:ℝ) ≤ (1 + B) * (ν x + 1) := by
          have := hν x; nlinarith
        rw [abs_zero]; exact h1
      · rw [hFnew_out x hx]
        have hab := hAbound x hx
        have h2 : f x ≤ ν x := hfν x
        have h3 : 0 ≤ f x := hf0 x
        have h4 : cE P f x ≤ B := (abs_le.mp hab).2
        have h5 : -(cE P f x) ≤ B := by linarith [(abs_le.mp hab).1]
        rw [abs_le]
        constructor
        · nlinarith [h3, h4, hν x, hB0]
        · nlinarith [h2, h5, hν x, hB0]
    have hsum' : ∑ y ∈ Ω ∪ Ωnew, |Fnew y| ≤ (1 + B) *
        (N * θ * ((Finset.univ.image Q).card : ℝ) + ρ) := by
      have h1 : ∑ y ∈ Ω ∪ Ωnew, |Fnew y| ≤ ∑ y ∈ Ω ∪ Ωnew, (1 + B) * (ν y + 1) :=
        Finset.sum_le_sum (fun y _ => hFnew_bound y)
      have h2 : ∑ y ∈ Ω ∪ Ωnew, (1 + B) * (ν y + 1)
          = (1 + B) * ∑ y ∈ Ω ∪ Ωnew, (ν y + 1) := by rw [Finset.mul_sum]
      have h3 : ∑ y ∈ Ω ∪ Ωnew, (ν y + 1) ≤ N * θ * ((Finset.univ.image Q).card : ℝ) + ρ := by
        have h1 := Finset.sum_union_inter (s₁ := Ω) (s₂ := Ωnew)
          (f := fun x : ZMod p => ν x + 1)
        have h2 : (0 : ℝ) ≤ ∑ x ∈ Ω ∩ Ωnew, (ν x + 1) :=
          Finset.sum_nonneg (fun x _ => by have := hν x; linarith)
        have h4 : ∑ x ∈ Ωnew, (ν x + 1) ≤ N * θ * ((Finset.univ.image Q).card : ℝ) :=
          hmass_new
        linarith
      have h4 : (0:ℝ) ≤ 1 + B := by linarith
      calc ∑ y ∈ Ω ∪ Ωnew, |Fnew y| ≤ ∑ y ∈ Ω ∪ Ωnew, (1 + B) * (ν y + 1) := h1
        _ = (1 + B) * ∑ y ∈ Ω ∪ Ωnew, (ν y + 1) := h2
        _ ≤ (1 + B) * (N * θ * ((Finset.univ.image Q).card : ℝ) + ρ) :=
            mul_le_mul_of_nonneg_left h3 h4
    have hE : ∑ x ∈ (Ω ∪ Ωnew) \ Ω, |f x - cE P f x| ≤
        (1 + B) * (N * θ * ((Finset.univ.image Q).card : ℝ) + ρ) := by
      have hstep : ∑ x ∈ (Ω ∪ Ωnew) \ Ω, |f x - cE P f x|
          ≤ ∑ x ∈ (Ω ∪ Ωnew) \ Ω, |Fnew x| := by
        apply Finset.sum_le_sum
        intro x hx
        rw [Finset.mem_sdiff] at hx
        rw [hFnew_out x hx.2]
      refine le_trans hstep ?_
      exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
        (fun x _ _ => abs_nonneg _)) hsum'
    have hγ : (Fintype.card (ZMod p) : ℝ) * γ₀ / 2 ≤ |∑ x ∈ Finset.univ \ (Ω ∪ Ωnew),
        (f x - cE P f x) * hh x| := by
      have h4 : Mraw * (∑ y ∈ Ω ∪ Ωnew, |Fnew y|) ≤
          Mraw * ((1 + B) * (N * θ * ((Finset.univ.image Q).card : ℝ) + ρ)) :=
        mul_le_mul_of_nonneg_left hsum' hMpos.le
      nlinarith [hdual, hγpos, h4]
    have hγ0' : (0 : ℝ) ≤ (Fintype.card (ZMod p) : ℝ) * γ₀ / 2 := by positivity
    exact Commons.Combinatorics.Transference.energy_increment_exceptional P Q hPmem hPeq
      hQmem hQeq href hΩsub hΩsat hΩ'sat f hh hhmeas hMpos hγ0' hB0 hAbound hhM hγ hE

end GTTrans
