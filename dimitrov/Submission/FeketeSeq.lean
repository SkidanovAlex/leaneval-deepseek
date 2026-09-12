import Mathlib
import Submission.Fekete
import Submission.FeketeRev
import Submission.FeketeAt

/-!
# Isolated task: sequence relations at Fekete configurations

These two relations between the Chebyshev numbers `t_n := chebyshevNumber
E n` and the Fekete numbers `m_n := feketeNumber E n` (for a nonempty
compact `E`, `1 ≤ n`) are the bridge from the finitary comparisons to the
Cesàro/limsup Fekete equality:

  DL1 (from the reverse finitary comparison at an attained (n+1)-config):
      m_{n+1} ≤ (n+1) · t_n · m_n
  DL2 (from the forward finitary comparison at an attained n-config):
      t_n ≤ m_{n+1} / m_n          (when 0 < m_n)

The three imported modules (Submission.Fekete, Submission.FeketeRev,
Submission.FeketeAt) each define their OWN copies of `vdm`/`feketeSet`/
`feketeNumber` (all definitionally equal: each `feketeNumber` is `sSup` of
the same set body).  When combining them, convert with
`simpa [Submission.X.feketeNumber, Submission.X.feketeSet, Submission.X.vdm]`
or `rfl`-based rewriting.

USEFUL LEMMAS (fully qualified):
* Submission.FeketeRev.vdm_le_of_monic_bound (monic deg-N p bounded by M on
  E ⟹ every (N+1)-config vdm ≤ (N+1)·M·feketeNumber E N), with hypotheses
  `hN : 1 ≤ N`, `hpmonic`, `hpdeg : p.natDegree = N`, `hM : 0 ≤ M`,
  `hb : ∀ X ∈ E, ‖p.eval X‖ ≤ M`, `hx : ∀ i < N+1, x i ∈ E`;
* Submission.Fekete.fekete_ratio_poly (root poly of a well-spread n-config
  bounded by feketeNumber E (n+1)/vdm x n) and
  Submission.Fekete.chebyshevNumber_le_fekete_ratio;
* Submission.FeketeAt.exists_fekete_points (attainment of Fekete points);
* local `member_lt_of_sInf_lt` (copied below): strict bounds on a
  nonempty bounded-below sInf are beaten by a member (used to choose a
  monic polynomial whose sup is < t_n + ε for any ε > 0, from
  `chebyshevNumber E n = sInf …`).

PROOF GUIDES:

DL1 (`fekete_succ_le`, hypotheses: `hEne : E.Nonempty`,
`hEc : IsCompact E`, `hn : 1 ≤ n`; note IsCompact gives
Bornology.IsBounded E automatically -- `IsCompact.isBounded`):
  1. Let `tn := chebyshevNumber E n`.  Show `∀ ε > 0, feketeNumber E
     (n+1) ≤ (n+1) * (tn + ε) * feketeNumber E n`:
     a. attain an (n+1)-config `x*` (FeketeAt.exists_fekete_points with
        `hEc`, `hEne`, `n+1`): `x* i ∈ E` and `vdm x* (n+1) =
        feketeNumber E (n+1)`.
     b. choose a monic degree-`n` polynomial `p` with
        `∀ X ∈ E, ‖p.eval X‖ ≤ tn + ε` (from `member_lt_of_sInf_lt` on the
        defining set of `chebyshevNumber E n`, since `sInf … ≤ tn < tn+ε`;
        unfold `chebyshevNumber` first).
     c. apply `FeketeRev.vdm_le_of_monic_bound` to `p` (with `N := n`,
        `M := tn + ε`, the config `x*`) to get
        `vdm x* (n+1) ≤ (n+1)·(tn+ε)·feketeNumber E n` (the module's own
        `feketeNumber`; convert with `simpa`).
  2. Let `ε → 0`: from `∀ ε > 0, A ≤ B + (n+1)·m_n·ε` (with `A :=
     feketeNumber E (n+1)`, `B := (n+1)·tn·m_n`) conclude `A ≤ B` by a
     standard argument (`le_of_forall_pos_le_add`: prove by contradiction,
     `linarith` with `ε := (A - B)/(2·(n+1)·m_n)` when `A > B`; handle
     `m_n = 0` by the same inequality or by cases).

DL2 (`cheb_le_fekete_succ_div`, hypotheses: `hEne`, `hEc`, `hn : 1 ≤ n`,
`hm : 0 < feketeNumber E n`):
  1. attain an `n`-config `x*` with `vdm x* n = feketeNumber E n`
     (FeketeAt, with `n`).
  2. instantiate `Fekete.chebyshevNumber_le_fekete_ratio` (with the SAME
     `E`, `n`, config `x*`, `hv := hm` after conversion) to get
     `chebyshevNumber E n ≤ feketeNumber E (n+1) / vdm x* n`, and rewrite
     `vdm x* n ↦ feketeNumber E n`.

Notes: all definitions over ℝ use the conditionally complete lattice
lemmas (`csInf_le`/`le_csInf`/`le_csSup`/`csSup_le` with the
BddAbove/BddBelow/Nonempty arguments).  Add whatever helpers you need.
Do NOT change the two theorem statements.  Convert between the three
modules' identical definitions liberally with `simpa`/`change`/`rfl`.
-/

noncomputable section

open scoped Real Polynomial Topology BigOperators

namespace Submission.FeketeSeq

open Polynomial

/-- If `sInf S < a` then some member of the (nonempty, bounded-below) set
`S` is strictly below `a`. -/
lemma member_lt_of_sInf_lt {S : Set ℝ} (hne : S.Nonempty) (hbdd : BddBelow S) {a : ℝ}
    (h : sInf S < a) : ∃ b ∈ S, b < a := by
  exact (csInf_lt_iff hbdd hne).1 h

/-- From `A ≤ B + C·ε` for every `ε > 0` (with `0 ≤ C`) conclude `A ≤ B`. -/
lemma le_of_forall_pos_le_smul {A B : ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ ε : ℝ, 0 < ε → A ≤ B + C * ε) : A ≤ B := by
  by_cases hC0 : C = 0
  · have h1 : A ≤ B + C * 1 := h 1 (by norm_num)
    simpa [hC0] using h1
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
    apply le_of_forall_pos_le_add
    intro ε hε
    have hδ : 0 < ε / C := div_pos hε hCpos
    have hh := h (ε / C) hδ
    have hmul : C * (ε / C) = ε := by field_simp [ne_of_gt hCpos]
    simpa [hmul] using hh

/-- **DL1.**  `m_{n+1} ≤ (n+1)·t_n·m_n` for a nonempty compact `E`. -/
theorem fekete_succ_le {E : Set ℂ} (hEne : E.Nonempty) (hEc : IsCompact E)
    {n : ℕ} (hn : 1 ≤ n) :
    Submission.FeketeRev.feketeNumber E (n + 1)
      ≤ (n + 1 : ℝ) * Submission.Fekete.chebyshevNumber E n
        * Submission.FeketeRev.feketeNumber E n := by
  let tn : ℝ := Submission.Fekete.chebyshevNumber E n
  let mN : ℝ := Submission.FeketeRev.feketeNumber E n
  let mN1 : ℝ := Submission.FeketeRev.feketeNumber E (n + 1)
  change mN1 ≤ ((n + 1 : ℝ) * tn) * mN
  have hEb : Bornology.IsBounded E := hEc.isBounded
  -- `m_n` is nonnegative (the constant configuration is a member of the
  -- Fekete set, whose values are all nonnegative).
  have hmn0 : 0 ≤ mN := by
    rcases hEne with ⟨e, he⟩
    have hmem : Submission.FeketeRev.vdm (fun _ : ℕ => e) n ∈
        Submission.FeketeRev.feketeSet E n := by
      refine ⟨fun _ : ℕ => e, ?_, rfl⟩
      intro i hi
      exact he
    have hbdd : BddAbove (Submission.FeketeRev.feketeSet E n) :=
      Submission.FeketeRev.feketeSet_bddAbove hEb
    have hle : Submission.FeketeRev.vdm (fun _ : ℕ => e) n ≤ mN := by
      dsimp [mN]
      exact le_csSup hbdd hmem
    exact le_trans (Submission.FeketeRev.vdm_nonneg (fun _ : ℕ => e) n) hle
  -- Claim: for every ε > 0 the desired inequality holds with `t_n` replaced
  -- by `t_n + ε`; then let ε → 0.
  have hinner : ∀ ε : ℝ, 0 < ε → mN1 ≤ ((n + 1 : ℝ) * (tn + ε)) * mN := by
    intro ε hε
    -- S := the set whose sInf is the Chebyshev number
    let S : Set ℝ := {c : ℝ | 0 ≤ c ∧ ∃ p : ℂ[X],
      p ∈ Submission.Fekete.MonicDeg n ∧ ∀ X ∈ E, ‖p.eval X‖ ≤ c}
    have hS_bdd : BddBelow S := by
      refine ⟨0, ?_⟩
      intro c hc
      exact hc.1
    have hS_ne : S.Nonempty := by
      -- p = X^n is monic of degree n and bounded on the compact E
      let p : ℂ[X] := (Polynomial.X : ℂ[X]) ^ n
      rcases hEb.exists_pos_norm_le with ⟨R, hRpos, hR⟩
      refine ⟨R ^ n, ⟨pow_nonneg (le_of_lt hRpos) n, p, ?_, ?_⟩⟩
      · dsimp [p, Submission.Fekete.MonicDeg]
        constructor
        · exact Polynomial.monic_X.pow n
        · rw [Polynomial.natDegree_X_pow]
      · intro z hz
        have hzR : ‖z‖ ≤ R := hR z hz
        calc
          ‖p.eval z‖ = ‖z ^ n‖ := by simp [p]
          _ = ‖z‖ ^ n := by rw [norm_pow]
          _ ≤ R ^ n := by gcongr
    -- `sInf S = t_n < t_n + ε`, so some member `c` of `S` is `< t_n + ε`
    have hS_eq : sInf S = tn := by rfl
    have hlt : sInf S < tn + ε := by
      rw [hS_eq]
      linarith
    rcases member_lt_of_sInf_lt hS_ne hS_bdd hlt with ⟨c, hcS, hclt⟩
    rcases hcS with ⟨hc0, p, hpMem, hpb⟩
    rcases hpMem with ⟨hpmonic, hpdeg⟩
    have hc_le : c ≤ tn + ε := le_of_lt hclt
    have hM : 0 ≤ tn + ε := le_trans hc0 hc_le
    have hbM : ∀ X ∈ E, ‖p.eval X‖ ≤ tn + ε := fun X hX => le_trans (hpb X hX) hc_le
    -- attain an (n+1)-point Fekete configuration
    rcases Submission.FeketeAt.exists_fekete_points hEc hEne (n + 1) with ⟨xS, hxmem, hxattain⟩
    -- reverse finitary comparison applied to `p` on the attained config
    have hvdmle : Submission.FeketeRev.vdm xS (n + 1) ≤ ((n + 1 : ℝ) * (tn + ε)) * mN := by
      have hv : Submission.FeketeRev.vdm xS (n + 1) ≤
          (n + 1 : ℝ) * (tn + ε) * Submission.FeketeRev.feketeNumber E n :=
        Submission.FeketeRev.vdm_le_of_monic_bound (E := E) (N := n) (hN := hn) (p := p)
          (hpmonic := hpmonic) (hpdeg := hpdeg) (M := tn + ε) (hM := hM) (hb := hbM)
          (x := xS) (hx := hxmem)
      simpa [mN] using hv
    -- convert the attained value (all modules' copies of `vdm`/`feketeNumber`
    -- are definitionally equal)
    have hxattain' : Submission.FeketeAt.vdm xS (n + 1) = mN1 := by
      dsimp [mN1]
      exact hxattain
    have hvdmle' : mN1 ≤ ((n + 1 : ℝ) * (tn + ε)) * mN := by
      rw [← hxattain']
      exact hvdmle
    exact hvdmle'
  -- let ε → 0
  apply le_of_forall_pos_le_smul (C := (n + 1 : ℝ) * mN)
  · exact mul_nonneg (by positivity) hmn0
  · intro ε hε
    have hh := hinner ε hε
    nlinarith

/-- **DL2.**  `t_n ≤ m_{n+1}/m_n` at a positive Fekete number. -/
theorem cheb_le_fekete_succ_div {E : Set ℂ} (hEne : E.Nonempty) (hEc : IsCompact E)
    {n : ℕ} (hn : 1 ≤ n) (hm : 0 < Submission.Fekete.feketeNumber E n) :
    Submission.Fekete.chebyshevNumber E n
      ≤ Submission.FeketeRev.feketeNumber E (n + 1)
        / Submission.Fekete.feketeNumber E n := by
  have hEb : Bornology.IsBounded E := hEc.isBounded
  -- attain an `n`-point Fekete configuration
  rcases Submission.FeketeAt.exists_fekete_points hEc hEne n with ⟨x, hxmem, hxattain⟩
  -- all module copies of `vdm`/`feketeNumber` agree definitionally
  have hvdm : Submission.Fekete.vdm x n = Submission.Fekete.feketeNumber E n := by
    exact hxattain
  have hv : 0 < Submission.Fekete.vdm x n := by
    rw [hvdm]
    exact hm
  have hmain := Submission.Fekete.chebyshevNumber_le_fekete_ratio (E := E) (n := n) hn hEb hxmem hv
  rw [hvdm] at hmain
  exact hmain

end Submission.FeketeSeq

end
