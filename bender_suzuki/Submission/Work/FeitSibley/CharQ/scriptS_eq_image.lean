import Mathlib
import Submission.Work.FeitSibley.CharQ.Defs
import Submission.Work.FeitSibley.GroupTheory.S_Q1
import Submission.Work.Clifford.clifford_correspondence
import Submission.Work.Frobenius.Induced.irr_eq_one_of_fpf
import Submission.Work.Frobenius.Bridge.mem_Irr_iff_coherence
import Submission.Work.FeitSibley.CharQ.exists_prodChar_of_mem_Irr
import Submission.Work.FeitSibley.CharQ.prodChar_inj
import Submission.Work.FeitSibley.CharQ.prodChar_Q1_kernel_iff
import Submission.Work.FeitSibley.CharQ.prodChar_conjFun
import Submission.Work.CharCore.Main
import Submission.Work.Clifford.clifford_constituents
import Submission.Work.Induction.indFun_apply_one
import Submission.Work.Induction.indFun_trans
import Submission.Work.FeitSibley.CharQ.ScriptSAPI
import Submission.Work.FeitSibley.CharQ.scriptS_vanish

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.FeitSibley.CharQ.scriptS_eq_image`

Peterfalvi II, Appendice XII: the set `𝒮 = {χ ∈ Irr H | Q₁ ⊄ ker χ}` (Feit–Sibley) is exactly
the set of characters of `H` induced from the irreducible characters of `Q` that are non-trivial
on `Q₁`:

`scriptS h.H h.Q₁ = {Ind_Q^H φ | φ ∈ Irr Q, ∃ x ∈ Q₁, φ x ≠ φ 1}`.

## The mathematical content

Write `H = Q ⋊ D`, `Q = S × Q₁`, with `D` acting fixed point freely on `Q₁` and `Q ⊴ H`.  The
whole statement is Clifford theory for the normal subgroup `Q ⊴ H`, in the situation where the
inertia group of a character of `Q` which is non-trivial on `Q₁` is exactly `Q`:

1. *inertia.*  Let `φ ∈ Irr Q` with `φ x ≠ φ 1` for some `x ∈ Q₁`.  Since `H = QD` and
   conjugation by an element of `Q` fixes the class function `φ`, the inertia group of `φ` meets
   `D` trivially; otherwise some `1 ≠ d ∈ D` would fix `φ`, and writing `φ = prodChar h lam theta`
   (`exists_prodChar_of_mem_Irr`) the identity `φ^d = φ` evaluated at the elements `prodIso (1,b)`
   forces `theta^d = theta`, so `theta = 1` (`Work.Frobenius.Induced.irr_eq_one_of_fpf`, i.e. the
   fixed-point-freeness of `D`), contradicting `φ x ≠ φ 1` — this is the already-proved
   `conjChar_ne_self_of_notMem_kernel` of the area.  Hence `I_H(φ) = Q` (`inertia_pull_eq`).

2. *irreducibility.*  `Ind_Q^H φ` is a virtual character of norm `|I_H(φ)| / |Q| = 1`
   (`Work.Clifford.cfInner_indFun_normal`), and the negative sign is excluded by the value at
   `1`; hence `Ind_Q^H φ ∈ Irr H` (`indQH_mem_Irr_of_inertia`).

3. *extraction.*  Conversely, if `χ ∈ Irr H` with `χ x ≠ χ 1` for some `x ∈ Q₁`, then
   `χ = Ind_Q^H φ` for some `φ ∈ Irr Q` which is itself non-trivial on `Q₁`
   (`exists_witness_indQH`).  This is the Feit–Sibley/Isaacs 6.34 argument packaged in the area
   as `Work.FeitSibley.CharQ.exists_indFun_of_complement_of_inertia` (with the inertia input (1)
   and the complement `H = Q ⋊ D`), transported from `Q.subgroupOf H` back to `Q`.

4. *non-triviality.*  For the converse direction one needs that `Ind_Q^H φ` is non-trivial on
   `Q₁` when `φ` is.  If `Ind_Q^H φ` were trivial at `x ∈ Q₁`, then by the Clifford decomposition
   `χ|_Q = e • (orbit sum)` of `χ = Ind_Q^H φ`, applied at `x`, every constituent of `χ|_Q` —
   in particular `φ` — would be trivial at `x` (`apply_eq_one_of_constituent`, the "triviality
   propagates to constituents" step, whose proof is the usual real-part/triangle-inequality
   argument for character values `‖ψ x‖ ≤ ψ 1`).

## Layout

* `CharCore_Irr_inst_eq` — `Work.CharCore.Irr` does not depend on the `Fintype` instance;
* `inertia_pull_eq`, `indQH_mem_Irr_of_inertia` — steps 1 and 2;
* `apply_eq_one_of_constituent` — step 4;
* `exists_witness_indQH`, `indQH_has_witness` — steps 3 and 4 in the form used below;
* `scriptS_eq_image` — the theorem.
-/

noncomputable section

open Classical

namespace Work.FeitSibley.CharQ

variable {G : Type} [Group G] [Fintype G]

/-! ### `Work.CharCore.Irr` is independent of the `Fintype` instance -/

/-- `Work.CharCore.Irr` does not depend on the chosen `Fintype` instance (both are the image of
`irrSubmodules`, and `mem_Irr_iff_fdrep` is instance-independent).  Used to move memberships
between the `Fintype` instances of the blueprint and of this file. -/
theorem CharCore_Irr_inst_eq {L : Type} [Group L] (i₁ i₂ : Fintype L) :
    @Work.CharCore.Irr L _ i₁ = @Work.CharCore.Irr L _ i₂ := by
  apply Finset.ext
  intro χ
  simp only [Work.CharCore.mem_Irr_iff_fdrep]

/-- The pullback `pull h φ` of an irreducible character of `Q` to `Q.subgroupOf H`, in the
`Work.Frobenius` interface. -/
theorem pull_mem_Frobenius_Irr (h : Work.FeitSibley.FSData G) {φ : ↥h.Q → ℂ}
    (hφ : φ ∈ Work.CharCore.Irr ↥h.Q) :
    pull h φ ∈ Work.Frobenius.Irr ↥(h.Q.subgroupOf h.H) :=
  (Work.Frobenius.Bridge.mem_Irr_iff_coherence).mpr
    ((Work.Clifford.mem_Irr_iff_coherence).mp (pull_mem_Irr h hφ))

/-! ### Step 1: the inertia of a character of `Q` non-trivial on `Q₁` is `Q` -/

/-- **The inertia group of `φ ∈ Irr Q` non-trivial on `Q₁` is `Q`.** -/
theorem inertia_pull_eq (h : Work.FeitSibley.FSData G) {φ : ↥h.Q → ℂ}
    (hφ : φ ∈ Work.CharCore.Irr ↥h.Q)
    (hw : ∃ x : ↥h.Q, (x : G) ∈ h.Q1 ∧ φ x ≠ φ 1) :
    Work.Clifford.inertia (h.Q.subgroupOf h.H) (pull h φ) = h.Q.subgroupOf h.H := by
  have hclass : Work.CharCore.IsClassFun φ := Work.CharCore.isClassFun_of_mem_Irr hφ
  refine le_antisymm ?_ ?_
  · -- every `g ∈ H` with `pull h φ` invariant lies in `Q`
    intro g hg
    have hg' : Work.Clifford.conjFun (h.Q.subgroupOf h.H) g (pull h φ) = pull h φ :=
      (Work.Clifford.mem_inertia _ _ g).mp hg
    obtain ⟨q, hq, d, hd, hqd⟩ := h.mem_H_decomp g.2
    have hgd : g = (⟨q, h.Q_le_H hq⟩ : ↥h.H) * (⟨d, h.D_le_H hd⟩ : ↥h.H) := by
      apply Subtype.ext
      rw [Subgroup.coe_mul]
      exact hqd
    have hqN : (⟨q, h.Q_le_H hq⟩ : ↥h.H) ∈ h.Q.subgroupOf h.H := hq
    -- conjugation by the `Q`-part does nothing
    have hstep : Work.Clifford.conjFun (h.Q.subgroupOf h.H) (⟨d, h.D_le_H hd⟩ : ↥h.H)
        (pull h φ) = pull h φ := by
      have h1 : Work.Clifford.conjFun (h.Q.subgroupOf h.H) g (pull h φ)
          = Work.Clifford.conjFun (h.Q.subgroupOf h.H) (⟨d, h.D_le_H hd⟩ : ↥h.H)
            (Work.Clifford.conjFun (h.Q.subgroupOf h.H) (⟨q, h.Q_le_H hq⟩ : ↥h.H)
              (pull h φ)) := by
        rw [hgd, Work.Clifford.conjFun_mul]
      rw [h1] at hg'
      rwa [conjFun_pull_of_mem_Q h hclass ⟨⟨q, h.Q_le_H hq⟩, hqN⟩] at hg'
    by_cases hd1 : d = 1
    · -- then `g = q ∈ Q`
      show (g : G) ∈ h.Q
      have hdH1 : (⟨d, h.D_le_H hd⟩ : ↥h.H) = 1 := Subtype.ext hd1
      rw [hgd, hdH1, mul_one]
      exact hq
    · -- otherwise `d` fixes a character of `Q₁` non-trivial there, which is impossible
      exfalso
      have hd1H : (⟨d, h.D_le_H hd⟩ : ↥h.H) ≠ 1 := fun hc => hd1 (Subtype.ext_iff.mp hc)
      have hdD : (⟨d, h.D_le_H hd⟩ : ↥h.H) ∈ h.D.subgroupOf h.H := hd
      have hwit : ∃ y : ↥(h.Q.subgroupOf h.H),
          ((y : ↥h.H) : G) ∈ h.Q1 ∧ pull h φ y ≠ pull h φ 1 := by
        obtain ⟨x, hxQ1, hxne⟩ := hw
        exact ⟨toQ h x, by rw [toQ_coe]; exact hxQ1,
          by rw [pull_toQ, pull_one]; exact hxne⟩
      have hθF : pull h φ ∈ Work.Frobenius.Irr ↥(h.Q.subgroupOf h.H) :=
        pull_mem_Frobenius_Irr h hφ
      have hcontra := conjChar_ne_self_of_notMem_kernel h hθF hwit hdD hd1H
      rw [Work.Frobenius.Induced.conjChar_eq_conjFun] at hcontra
      exact hcontra hstep
  · -- `Q` lies in the inertia group (its elements act trivially on class functions)
    intro n hn
    rw [Work.Clifford.mem_inertia]
    exact conjFun_pull_of_mem_Q h hclass ⟨n, hn⟩

/-! ### Step 2: the induced character is irreducible -/

/-- **`Ind_Q^H φ` is irreducible when the inertia of `φ` is `Q`.**  The norm is
`|I_H(φ)| / |Q| = 1`, and the negative sign in `vchar_norm_one` is excluded by positivity of the
degree `[H : Q] · φ(1)`. -/
theorem indQH_mem_Irr_of_inertia (h : Work.FeitSibley.FSData G) {φ : ↥h.Q → ℂ}
    (hφ : φ ∈ Work.CharCore.Irr ↥h.Q)
    (hI : Work.Clifford.inertia (h.Q.subgroupOf h.H) (pull h φ) = h.Q.subgroupOf h.H) :
    h.indQH φ ∈ Work.CharCore.Irr ↥h.H := by
  have hθC : pull h φ ∈ Work.CharCore.Irr ↥(h.Q.subgroupOf h.H) :=
    (Work.Clifford.corr_mem_Irr_charCore).mp (pull_mem_Irr h hφ)
  -- the norm is one
  have hnorm : Work.CharCore.cfInner (h.indQH φ) (h.indQH φ) = 1 := by
    rw [indQH_eq_indFun]
    rw [show Work.CharCore.cfInner (Work.Clifford.indFun (h.Q.subgroupOf h.H) (pull h φ))
        (Work.Clifford.indFun (h.Q.subgroupOf h.H) (pull h φ))
        = Work.Clifford.cfInner (Work.Clifford.indFun (h.Q.subgroupOf h.H) (pull h φ))
          (Work.Clifford.indFun (h.Q.subgroupOf h.H) (pull h φ)) from rfl]
    rw [Work.Clifford.cfInner_indFun_normal (pull_mem_Irr h hφ), hI]
    have hN : (Nat.card ↥(h.Q.subgroupOf h.H) : ℂ) ≠ 0 := by
      rw [Nat.cast_ne_zero]
      exact Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
    rw [mul_inv_cancel₀ hN]
  have hV : Work.CharCore.IsVChar (h.indQH φ) := by
    rw [indQH_eq_indFun]
    exact Work.Induction.isVChar_indFun (Work.CharCore.IsVChar.of_mem_Irr hθC)
  obtain ⟨χ, hχ, hcase⟩ := Work.CharCore.vchar_norm_one hV hnorm
  rcases hcase with hpos | hneg
  · rw [hpos]
    exact hχ
  · exfalso
    have h1 : (Work.Induction.indFun (h.Q.subgroupOf h.H) (pull h φ)) 1 = -χ 1 := by
      rw [show Work.Induction.indFun (h.Q.subgroupOf h.H) (pull h φ) = h.indQH φ from rfl,
        hneg]
      rfl
    rw [Work.Induction.indFun_apply_one, Work.CharCore.irrDeg_spec hθC,
      Work.CharCore.irrDeg_spec hχ] at h1
    have h2 : (((h.Q.subgroupOf h.H).index : ℕ) : ℝ) *
        ((Work.CharCore.irrDeg (pull h φ) : ℕ) : ℝ) = -(((Work.CharCore.irrDeg χ : ℕ)) : ℝ) := by
      apply Complex.ofReal_injective
      push_cast
      exact h1
    have h3 : (0 : ℝ) < (((h.Q.subgroupOf h.H).index : ℕ) : ℝ) :=
      Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite))
    have h4 : (0 : ℝ) < ((Work.CharCore.irrDeg (pull h φ) : ℕ) : ℝ) :=
      Nat.cast_pos.mpr (Work.CharCore.irrDeg_pos hθC)
    have h5 : (0 : ℝ) < ((Work.CharCore.irrDeg χ : ℕ) : ℝ) :=
      Nat.cast_pos.mpr (Work.CharCore.irrDeg_pos hχ)
    nlinarith

/-! ### Step 4: triviality of `χ` at `x` propagates to its constituents on `Q` -/

/-- **If `χ ∈ Irr H` is trivial at `x ∈ Q ≤ H`, then every constituent of `χ|_Q` is trivial at
`x`.**  Write `χ|_Q = e • (orbit sum)` (Clifford decomposition).  At `x` and at `1` the two
sides are equal, so the orbit sums agree; taking real parts and using `‖ψ x‖ ≤ ψ 1` for the
(irreducible) orbit elements `ψ`, every term must be an equality, i.e. `ψ x = ψ 1`. -/
theorem apply_eq_one_of_constituent (h : Work.FeitSibley.FSData G) {χ : ↥h.H → ℂ}
    (hχ : χ ∈ Work.CharCore.Irr ↥h.H)
    {φ : ↥(h.Q.subgroupOf h.H) → ℂ} (hφ : φ ∈ Work.Clifford.Irr ↥(h.Q.subgroupOf h.H))
    (hc : Work.Clifford.IsConstituentOf φ (Work.Clifford.resFun (h.Q.subgroupOf h.H) χ))
    {x : ↥(h.Q.subgroupOf h.H)} (hx : χ (x : ↥h.H) = χ 1) : φ x = φ 1 := by
  set s := Work.Clifford.charOrbit (h.Q.subgroupOf h.H)
  have hχC : χ ∈ Work.Clifford.Irr ↥h.H := (Work.Clifford.corr_mem_Irr_charCore).mpr hχ
  obtain ⟨θ, hθ, e, he, hdec⟩ := Work.Clifford.clifford_decomposition (G := ↥h.H)
    (N := h.Q.subgroupOf h.H) hχC
  -- `φ` is a constituent, hence lies in the orbit of `θ`
  have hφorb : φ ∈ s θ := by
    have h0 : Work.Clifford.cfInner (Work.Clifford.orbitSum (h.Q.subgroupOf h.H) θ) φ ≠ 0 := by
      intro hzero
      apply hc
      rw [hdec, Work.Clifford.cfInner_smul_left, hzero, mul_zero]
    rw [Work.Clifford.cfInner_orbitSum_eq_ite hθ hφ] at h0
    by_contra hnot
    rw [if_neg hnot] at h0
    exact h0 rfl
  -- the orbit sums at `x` and at `1` agree
  have hsum : ∑ ψ ∈ s θ, ψ x = ∑ ψ ∈ s θ, ψ 1 := by
    have h1 : Work.Clifford.orbitSum (h.Q.subgroupOf h.H) θ x
        = Work.Clifford.orbitSum (h.Q.subgroupOf h.H) θ 1 := by
      have h2 : Work.Clifford.resFun (h.Q.subgroupOf h.H) χ x
          = Work.Clifford.resFun (h.Q.subgroupOf h.H) χ 1 := by
        show χ (x : ↥h.H) = χ ((1 : ↥(h.Q.subgroupOf h.H)) : ↥h.H)
        rw [hx]
        exact congrArg χ (Subtype.ext rfl)
      rw [hdec] at h2
      simp only [Pi.smul_apply, smul_eq_mul] at h2
      exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr he.ne') h2
    simpa only [Work.Clifford.orbitSum_apply] using h1
  -- every element of the orbit is an irreducible character
  have horbIrr : ∀ ψ ∈ s θ, ψ ∈ Work.Clifford.Irr ↥(h.Q.subgroupOf h.H) := by
    intro ψ hψ
    obtain ⟨g, -, hg⟩ := Finset.mem_image.mp hψ
    rw [← hg]
    exact Work.Clifford.conjFun_mem_Irr g hθ
  have horbCI : ∀ ψ ∈ s θ, ψ ∈ Work.CharCore.Irr ↥(h.Q.subgroupOf h.H) :=
    fun ψ hψ => (Work.Clifford.corr_mem_Irr_charCore).mp (horbIrr ψ hψ)
  have hdeg : ∀ ψ ∈ s θ, (ψ 1).re = (Work.CharCore.irrDeg ψ : ℝ) := by
    intro ψ hψ
    rw [Work.CharCore.irrDeg_spec (horbCI ψ hψ)]
    simp
  have hle : ∀ ψ ∈ s θ, (ψ x).re ≤ (Work.CharCore.irrDeg ψ : ℝ) := fun ψ hψ =>
    le_trans (Complex.re_le_norm _) (Work.CharCore.norm_char_le (horbCI ψ hψ) x)
  -- sums of real parts agree
  have hre : ∑ ψ ∈ s θ, (ψ x).re = ∑ ψ ∈ s θ, (ψ 1).re := by
    have h := congrArg Complex.re hsum
    simpa using h
  have hzero : ∑ ψ ∈ s θ, ((Work.CharCore.irrDeg ψ : ℝ) - (ψ x).re) = 0 := by
    rw [Finset.sum_sub_distrib]
    have h1 : ∑ ψ ∈ s θ, (Work.CharCore.irrDeg ψ : ℝ) = ∑ ψ ∈ s θ, (ψ 1).re :=
      Finset.sum_congr rfl fun ψ hψ => (hdeg ψ hψ).symm
    rw [h1, ← hre]
    ring
  have hnonneg : ∀ ψ ∈ s θ, 0 ≤ (Work.CharCore.irrDeg ψ : ℝ) - (ψ x).re :=
    fun ψ hψ => by linarith [hle ψ hψ]
  have hmain : ∀ ψ ∈ s θ, ψ x = ψ 1 := by
    intro ψ hψ
    have hψeq := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hzero ψ hψ
    exact character_apply_eq_deg_of_re (horbCI ψ hψ) x (by linarith)
  exact hmain φ hφorb

/-! ### Step 3: extraction of a non-trivial constituent -/

/-- **A character of `H` non-trivial on `Q₁` is induced from a character of `Q` non-trivial on
`Q₁`.**  This is `Work.FeitSibley.CharQ.exists_indFun_of_complement_of_inertia` (the
Feit–Sibley/Isaacs 6.34 argument), applied to the complement `H = Q ⋊ D` with the inertia input
`conjChar_ne_self_of_notMem_kernel`, and transported from `Q.subgroupOf H` back to `Q` along
`eQ h`. -/
theorem exists_witness_indQH (h : Work.FeitSibley.FSData G) {χ : ↥h.H → ℂ}
    (hχ : χ ∈ Work.CharCore.Irr ↥h.H)
    (hw : ∃ x : ↥h.H, (x : G) ∈ h.Q1 ∧ χ x ≠ χ 1) :
    ∃ φ ∈ Work.CharCore.Irr ↥h.Q, (∃ x : ↥h.Q, (x : G) ∈ h.Q1 ∧ φ x ≠ φ 1) ∧
      χ = h.indQH φ := by
  have hcomp : Subgroup.IsComplement' (h.Q.subgroupOf h.H) (h.D.subgroupOf h.H) :=
    isComplement'_Q_D h
  have hAle : h.Q1.subgroupOf h.H ≤ h.Q.subgroupOf h.H :=
    Subgroup.subgroupOf_mono h.H h.Q1_le_Q
  have hFchi : χ ∈ Work.Frobenius.Irr ↥h.H :=
    (Work.Frobenius.Bridge.mem_Irr_iff_coherence).mpr
      ((Work.CharCore.mem_Irr_iff_coherence).mp hχ)
  have hker : ∃ y : ↥h.H, y ∈ h.Q1.subgroupOf h.H ∧ χ y ≠ χ 1 := by
    obtain ⟨x, hxQ1, hxne⟩ := hw
    exact ⟨x, hxQ1, hxne⟩
  obtain ⟨θ, hθ, hθw, hθeq⟩ := exists_indFun_of_complement_of_inertia (G := ↥h.H)
    (K := h.Q.subgroupOf h.H) (He := h.D.subgroupOf h.H) (A := h.Q1.subgroupOf h.H)
    hcomp hAle (fun θ hθ hθA d hd hd1 => conjChar_ne_self_of_notMem_kernel h hθ hθA hd hd1)
    hFchi hker
  -- transport back to `↥Q`
  let φ : ↥h.Q → ℂ := fun q => θ ((eQ h).symm q)
  have hθC : θ ∈ Work.Clifford.Irr ↥(h.Q.subgroupOf h.H) :=
    (Work.Clifford.mem_Irr_iff_coherence).mpr
      ((Work.Frobenius.Bridge.mem_Irr_iff_coherence).mp hθ)
  have hφCl : φ ∈ Work.Clifford.Irr ↥h.Q := Work.Clifford.irr_precomp_mulEquiv (eQ h).symm hθC
  have hφC : φ ∈ Work.CharCore.Irr ↥h.Q :=
    (Work.CharCore.mem_Irr_iff_coherence).mpr ((Work.Clifford.mem_Irr_iff_coherence).mp hφCl)
  refine ⟨φ, hφC, ?_, ?_⟩
  · obtain ⟨y, hyQ1, hyne⟩ := hθw
    refine ⟨eQ h y, ?_, ?_⟩
    · rw [eQ_apply_val]
      exact hyQ1
    · have h1 : φ (eQ h y) = θ y := by
        show θ ((eQ h).symm (eQ h y)) = θ y
        rw [MulEquiv.symm_apply_apply]
      have h2 : φ 1 = θ 1 := by
        show θ ((eQ h).symm 1) = θ 1
        rw [map_one]
      rw [h1, h2]
      exact hyne
  · have hpull : pull h φ = θ := by
      funext y
      rw [pull_apply_eQ]
      show θ ((eQ h).symm (eQ h y)) = θ y
      rw [MulEquiv.symm_apply_apply]
    rw [hθeq, indQH_eq_indFun h φ, hpull]
    rfl

/-! ### Step 4 (conclusion): `Ind_Q^H φ` is non-trivial on `Q₁` -/

/-- **`Ind_Q^H φ` is non-trivial on `Q₁` when `φ` is.**  If `χ = Ind_Q^H φ` were trivial on
`Q₁`, then `φ` — a constituent of `χ|_Q` by Frobenius reciprocity — would be trivial there by
`apply_eq_one_of_constituent`, contradiction. -/
theorem indQH_has_witness (h : Work.FeitSibley.FSData G) {φ : ↥h.Q → ℂ}
    (hφ : φ ∈ Work.CharCore.Irr ↥h.Q)
    (hw : ∃ x : ↥h.Q, (x : G) ∈ h.Q1 ∧ φ x ≠ φ 1)
    (hIrr : h.indQH φ ∈ Work.CharCore.Irr ↥h.H) :
    ∃ x : ↥h.H, (x : G) ∈ h.Q1 ∧ h.indQH φ x ≠ h.indQH φ 1 := by
  by_contra hcon
  push_neg at hcon
  have hθ : pull h φ ∈ Work.Clifford.Irr ↥(h.Q.subgroupOf h.H) := pull_mem_Irr h hφ
  have hχC : h.indQH φ ∈ Work.Clifford.Irr ↥h.H :=
    (Work.Clifford.corr_mem_Irr_charCore).mpr hIrr
  -- Frobenius reciprocity turns `⟪χ, χ⟫ = 1` into the constituent hypothesis
  have hB : Work.Clifford.cfInner (pull h φ)
      (Work.Clifford.resFun (h.Q.subgroupOf h.H) (h.indQH φ)) = 1 := by
    have hA : Work.Clifford.cfInner
        (Work.Clifford.indFun (h.Q.subgroupOf h.H) (pull h φ)) (h.indQH φ)
        = Work.Clifford.cfInner (pull h φ)
          (Work.Clifford.resFun (h.Q.subgroupOf h.H) (h.indQH φ)) :=
      Work.Clifford.cfInner_indFun (pull h φ) (Work.CharCore.isClassFun_of_mem_Irr hIrr)
    rw [← hA, ← indQH_eq_indFun h φ, Work.Clifford.cfInner_eq_ite_of_mem_Irr hχC hχC]
    simp
  have hc : Work.Clifford.IsConstituentOf (pull h φ)
      (Work.Clifford.resFun (h.Q.subgroupOf h.H) (h.indQH φ)) := by
    rw [Work.Clifford.IsConstituentOf, Work.Clifford.cfInner_conj_symm, hB]
    simp
  obtain ⟨x₀, hx₀Q1, hx₀ne⟩ := hw
  have hx : h.indQH φ ((toQ h x₀ : ↥(h.Q.subgroupOf h.H)) : ↥h.H) = h.indQH φ 1 := by
    refine hcon _ ?_
    rw [toQ_coe]
    exact hx₀Q1
  have h1 := apply_eq_one_of_constituent h hIrr hθ hc (x := toQ h x₀) hx
  rw [pull_toQ, pull_one] at h1
  exact hx₀ne h1

/-! ### The theorem -/

/-- **`𝒮 = {Ind_Q^H φ | φ ∈ Irr Q, Q₁ ⊄ ker φ}`** (Peterfalvi II, Appendice XII). -/
theorem scriptS_eq_image {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    {chi : ↥h.H → ℂ} :
    chi ∈ Work.FeitSibley.scriptS h.H h.Q1 ↔
      ∃ phi ∈ Work.CharCore.Irr ↥h.Q,
        (∃ x : ↥h.Q, (x : G) ∈ h.Q1 ∧ phi x ≠ phi 1) ∧
        chi = h.indQH phi := by
  constructor
  · intro hchi
    -- align the `Fintype` instance with the one used by the blueprint's `excludingKernel`
    letI : Fintype ↥h.H := h.H.instFintypeSubtypeMemOfDecidablePred
    have hchi' : chi ∈ Work.CharCore.Irr ↥h.H ∧
        ∃ x : ↥h.H, (x : G) ∈ h.Q1 ∧ chi x ≠ chi 1 := by
      have hh := hchi
      simp only [Work.FeitSibley.scriptS, Submission.Blueprint.excludingKernel,
        Finset.mem_filter] at hh
      exact hh
    obtain ⟨hchiIrr, hwit⟩ := hchi'
    obtain ⟨φ, hφ, hw, hneq⟩ := exists_witness_indQH h hchiIrr hwit
    exact ⟨φ, hφ, hw, hneq⟩
  · rintro ⟨φ, hφ, hw, rfl⟩
    -- align the `Fintype` instance with the one used by the blueprint's `excludingKernel`
    letI : Fintype ↥h.H := h.H.instFintypeSubtypeMemOfDecidablePred
    have hI := inertia_pull_eq h hφ hw
    have hIrr := indQH_mem_Irr_of_inertia h hφ hI
    have hwit := indQH_has_witness h hφ hw hIrr
    have hgoal : h.indQH φ ∈ (Work.CharCore.Irr ↥h.H).filter
        (fun χ => ∃ x : ↥h.H, (x : G) ∈ h.Q1 ∧ χ x ≠ χ 1) :=
      Finset.mem_filter.mpr ⟨hIrr, hwit⟩
    simpa only [Work.FeitSibley.scriptS, Submission.Blueprint.excludingKernel] using hgoal

end Work.FeitSibley.CharQ
