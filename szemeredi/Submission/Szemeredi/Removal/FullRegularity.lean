import Mathlib
import Submission.Szemeredi.Removal.Regularity

/-!
# The full regularity lemma (Tao, arXiv:math/0503572, Lemma 2.6)

With `H_d = Hd` given and `H_j := ∂H_{j+1} = lev H_d (d-j)`, and coarse edge
σ-algebras `Bd` of complexity `≤ M_d`, we produce coarse algebras `B_f` and fine
algebras `B'_f ⊇ B_f` at every order `0 ≤ j < d`, together with complexities `M_j`
satisfying the recursion `M j = max (F (M (j+1))) (sup_f complexity (B_f))`
(hence `M_d ≤ F(M_d) ≤ M_{d-1} ≤ … ≤ M_0`; `M_0` is the LARGEST), such that

* `complexity (B_f) ≤ M_j`;
* the energy gap `Energy(∨_{f∈∂e} B'_f) - Energy(∨_{f∈∂e} B_f) ≤ 1/F(M_j)^2` for `e ∈ H_j`;
* the discrepancy `Δ_e(E_e | ∨_{f∈∂e} B'_f) ≤ 1/F(M_{j-1})` for `e ∈ H_j`.

NOTE (see Submission/NOTES.md, "SESSION 7"): the counting lemma needs the bound
`1/F(M_0)` with `M_0` the LARGEST complexity.  The present lemma gives
`1/F(M_{j-1})` with `M_{j-1} ≤ M_0`, i.e. the wrong direction.  The fix is to run
the *top* preliminary-regularity step with the artificially small target
`1/Ffast(A)`, `Ffast n = max (F n) (F (Mbdd d (∂Hd) n F)) + 1`, where `Mbdd` is an
explicit a priori bound for the bottom complexity; this needs the *bounded*
preliminary regularity (ladder schedule), see NOTES.
-/

open scoped BigOperators
open Finset
open Szemeredi.Removal.SigAlg

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Szemeredi.Removal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : ι → Type*} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] [∀ i, Nonempty (V i)]

/-- `lev Hd n` is the `n`-fold boundary `∂ⁿ Hd`. -/
noncomputable def lev (Hd : Finset (Finset ι)) : ℕ → Finset (Finset ι) :=
  Nat.rec Hd (fun _ H => bdry H)

@[simp] theorem lev_zero (Hd : Finset (Finset ι)) : lev Hd 0 = Hd := rfl
@[simp] theorem lev_succ (Hd : Finset (Finset ι)) (n : ℕ) : lev Hd (n + 1) = bdry (lev Hd n) := rfl
@[simp] theorem lev_one (Hd : Finset (Finset ι)) : lev Hd 1 = bdry Hd := rfl

theorem lev_lev (Hd : Finset (Finset ι)) (n : ℕ) : lev (lev Hd 1) n = lev Hd (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have h1 : lev (lev Hd 1) (n + 1) = bdry (lev (lev Hd 1) n) := rfl
      have h2 : lev Hd (n + 1 + 1) = bdry (lev Hd (n + 1)) := rfl
      rw [h1, h2, ih]

theorem lev_shift (Hd : Finset (Finset ι)) {j d : ℕ} (hj : j ≤ d) :
    lev Hd (d + 1 - j) = lev (lev Hd 1) (d - j) := by
  rw [lev_lev]
  congr 1
  omega

/-- The σ-algebra on the edges at level `j`: the input `Bd` at the top level `d`,
and `B j` below. -/
noncomputable def edgeAlg (Bd : Finset ι → SigAlg (Pt V)) (B : ℕ → Finset ι → SigAlg (Pt V))
    (d j : ℕ) : Finset ι → SigAlg (Pt V) := if j = d then Bd else B j

/-- Overwrite level `m` of a family of σ-algebras by a single family. -/
noncomputable def glue (m : ℕ) (B0 : Finset ι → SigAlg (Pt V)) (B1 : ℕ → Finset ι → SigAlg (Pt V)) :
    ℕ → Finset ι → SigAlg (Pt V) := fun j => if j = m then B0 else B1 j

@[simp] theorem glue_self (m : ℕ) (B0 : Finset ι → SigAlg (Pt V))
    (B1 : ℕ → Finset ι → SigAlg (Pt V)) : glue m B0 B1 m = B0 := by
  show (if m = m then B0 else B1 m) = B0
  exact if_pos rfl

@[simp] theorem glue_of_ne (m : ℕ) (B0 : Finset ι → SigAlg (Pt V))
    (B1 : ℕ → Finset ι → SigAlg (Pt V)) {j : ℕ} (h : j ≠ m) : glue m B0 B1 j = B1 j := by
  show (if j = m then B0 else B1 j) = B1 j
  exact if_neg h

/-- Overwrite level `m` of a sequence of natural numbers. -/
def glueNat (m : ℕ) (a : ℕ) (M1 : ℕ → ℕ) : ℕ → ℕ := fun j => if j = m then a else M1 j

@[simp] theorem glueNat_self (m : ℕ) (a : ℕ) (M1 : ℕ → ℕ) : glueNat m a M1 m = a := if_pos rfl
@[simp] theorem glueNat_of_ne (m : ℕ) (a : ℕ) (M1 : ℕ → ℕ) {j : ℕ} (h : j ≠ m) :
    glueNat m a M1 j = M1 j := if_neg h

theorem edgeAlg_glue_ne {Bd : Finset ι → SigAlg (Pt V)} {B0 : Finset ι → SigAlg (Pt V)}
    {B1 : ℕ → Finset ι → SigAlg (Pt V)} {d j : ℕ} (h : j ≠ d + 1) :
    edgeAlg (V := V) Bd (glue d B0 B1) (d + 1) j = edgeAlg (V := V) B0 B1 d j := by
  simp only [edgeAlg, glue, if_neg h]

/-- The conclusion of the full regularity lemma, packaged as a predicate. -/
def RegOK (d : ℕ) (Hd : Finset (Finset ι)) (Bd : Finset ι → SigAlg (Pt V)) (Md : ℕ)
    (F : ℕ → ℕ) (B B' : ℕ → Finset ι → SigAlg (Pt V)) (M : ℕ → ℕ) : Prop :=
  M d = Md ∧
  (∀ j < d, M j = max (F (M (j + 1)))
      ((lev Hd (d - j)).sup (fun f => (B j f).complexity))) ∧
  (∀ j < d, ∀ f ∈ lev Hd (d - j), (B j f).Refines (coord (V := V) f)) ∧
  (∀ j < d, ∀ f ∈ lev Hd (d - j), (B j f).Refines (B' j f)) ∧
  (∀ j < d, ∀ f ∈ lev Hd (d - j), (B' j f).Refines (coord (V := V) f)) ∧
  (∀ j < d, ∀ f ∈ lev Hd (d - j), (B j f).complexity ≤ M j) ∧
  (∀ j, 1 ≤ j → j ≤ d → ∀ e ∈ lev Hd (d - j), ∀ Ee : Finset (Pt V),
      (edgeAlg (V := V) Bd B d j e).IsMeas Ee →
        (SigAlg.iInf (B' (j - 1)) (del e)).energy (indicator Ee) ≤
          (SigAlg.iInf (B (j - 1)) (del e)).energy (indicator Ee)
            + (1 / (F (M j) : ℝ)) ^ 2) ∧
  (∀ j, 1 ≤ j → j ≤ d → ∀ e ∈ lev Hd (d - j), ∀ Ee : Finset (Pt V),
      (edgeAlg (V := V) Bd B d j e).IsMeas Ee →
        Pseudorandom (V := V) e Ee (SigAlg.iInf (B' (j - 1)) (del e))
          (1 / (F (M (j - 1)) : ℝ)))

/-- The complexities `M j` decrease in `j`. -/
theorem RegOK.M_anti {d : ℕ} {Hd : Finset (Finset ι)} {Bd : Finset ι → SigAlg (Pt V)} {Md : ℕ}
    {F : ℕ → ℕ} {B B' : ℕ → Finset ι → SigAlg (Pt V)} {M : ℕ → ℕ}
    (h : RegOK (V := V) d Hd Bd Md F B B' M) (hF : ∀ n, n + 1 ≤ F n) (hFmono : Monotone F) :
    ∀ j k, j ≤ k → k ≤ d → M k ≤ M j := by
  have hstep : ∀ j, j < d → M (j + 1) ≤ M j := by
    intro j hj
    rw [h.2.1 j hj]
    have h1 := hF (M (j + 1))
    have h2 : F (M (j + 1)) ≤ max (F (M (j + 1)))
        ((lev Hd (d - j)).sup fun f => (B j f).complexity) := le_max_left _ _
    omega
  intro j k hjk hkd
  induction k with
  | zero =>
      have h0 : j = 0 := by omega
      rw [h0]
  | succ k ih =>
      rcases Nat.eq_or_lt_of_le hjk with h' | h'
      · rw [h']
      · have hkj : j ≤ k := by omega
        exact le_trans (hstep k (by omega)) (ih hkj (by omega))

/-- **Full regularity lemma** (Tao, arXiv:math/0503572, Lemma 2.6). -/
theorem full_regularity : ∀ (d : ℕ) (Hd : Finset (Finset ι)) (Bd : Finset ι → SigAlg (Pt V))
    (Md : ℕ) (F : ℕ → ℕ),
    (∀ e ∈ Hd, (Bd e).complexity ≤ Md) → (∀ n, n + 1 ≤ F n) →
    ∃ B B' : ℕ → Finset ι → SigAlg (Pt V), ∃ M : ℕ → ℕ, RegOK (V := V) d Hd Bd Md F B B' M := by
  intro d
  induction d with
  | zero =>
      intro Hd Bd Md F hm hF
      exact ⟨fun _ _ => SigAlg.triv, fun _ _ => SigAlg.triv, fun _ => Md,
        rfl, fun j hj => absurd hj (Nat.not_lt_zero j),
        fun j hj => absurd hj (Nat.not_lt_zero j), fun j hj => absurd hj (Nat.not_lt_zero j),
        fun j hj => absurd hj (Nat.not_lt_zero j), fun j hj => absurd hj (Nat.not_lt_zero j),
        fun j hj1 hj2 => absurd hj2 (by omega), fun j hj1 hj2 => absurd hj2 (by omega)⟩
  | succ d ih =>
      intro Hd Bd Md F hm hF
      have hFpos : (0 : ℝ) < (F Md : ℝ) := by
        have h1 : 1 ≤ F Md := by have := hF Md; omega
        exact_mod_cast h1
      have hε : 0 < 1 / (F Md : ℝ) := by positivity
      obtain ⟨B0, h0ref, h0done⟩ :=
        preliminary_regularity (V := V) (H := lev Hd 0) (Be := Bd) (m := Md)
          (ε := 1 / (F Md : ℝ)) (F := F) hm hε hF
      obtain ⟨B0', h0r, h0c', h0e1, h0e2⟩ := h0done
      set M' : ℕ := Mbound F Md (lev Hd 0) B0 with hM'
      have hM'bound : ∀ e ∈ lev Hd 1, (B0 e).complexity ≤ M' := by
        intro e he
        rw [hM']
        unfold Mbound
        exact le_trans (Finset.le_sup (s := lev Hd 1) (f := fun f => (B0 f).complexity) he)
          (le_max_right _ _)
      obtain ⟨B1, B1', M1, hM1d, hM1rec, hM1c, hM1r, hM1c', hM1cx, hM1e, hM1dsc⟩ :=
        ih (lev Hd 1) B0 M' F hM'bound hF
      refine ⟨glue d B0 B1, glue d B0' B1', glueNat (d + 1) Md M1,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact glueNat_self (d + 1) Md M1
      · -- the recursion
        intro j hj
        have hjd : j ≤ d := by omega
        by_cases h : j = d
        · rw [h] at ⊢
          rw [glueNat_of_ne (d + 1) Md M1 (by omega : d ≠ d + 1), glueNat_self,
            glue_self, hM1d]
          have hh : lev Hd (d + 1 - d) = lev Hd 1 := by congr 1; omega
          rw [hh]
          show Mbound F Md (lev Hd 0) B0
            = max (F Md) ((lev Hd 1).sup fun f => (B0 f).complexity)
          unfold Mbound
          rw [show bdry (lev Hd 0) = lev Hd 1 from (lev_one Hd).symm]
        · rw [glueNat_of_ne (d + 1) Md M1 (by omega : j ≠ d + 1),
            glueNat_of_ne (d + 1) Md M1 (by omega : j + 1 ≠ d + 1)]
          rw [hM1rec j (by omega)]
          rw [lev_shift Hd hjd, glue_of_ne d B0 B1 h]
      · -- B refines coord
        intro j hj f hf
        have hjd : j ≤ d := by omega
        by_cases h : j = d
        · rw [h] at hf ⊢
          rw [glue_self]
          have hf' : f ∈ lev Hd 1 := by
            have hh : d + 1 - d = 1 := by omega
            rwa [hh] at hf
          exact h0ref f hf'
        · rw [glue_of_ne d B0 B1 h]
          have hf' : f ∈ lev (lev Hd 1) (d - j) := by rwa [lev_shift Hd hjd] at hf
          exact hM1c j (by omega) f hf'
      · -- B refines B'
        intro j hj f hf
        have hjd : j ≤ d := by omega
        by_cases h : j = d
        · rw [h] at hf ⊢
          simp only [glue_self]
          have hf' : f ∈ lev Hd 1 := by
            have hh : d + 1 - d = 1 := by omega
            rwa [hh] at hf
          exact h0r f hf'
        · rw [glue_of_ne d B0 B1 h, glue_of_ne d B0' B1' h]
          have hf' : f ∈ lev (lev Hd 1) (d - j) := by rwa [lev_shift Hd hjd] at hf
          exact hM1r j (by omega) f hf'
      · -- B' refines coord
        intro j hj f hf
        have hjd : j ≤ d := by omega
        by_cases h : j = d
        · rw [h] at hf ⊢
          rw [glue_self]
          have hf' : f ∈ lev Hd 1 := by
            have hh : d + 1 - d = 1 := by omega
            rwa [hh] at hf
          exact h0c' f hf'
        · rw [glue_of_ne d B0' B1' h]
          have hf' : f ∈ lev (lev Hd 1) (d - j) := by rwa [lev_shift Hd hjd] at hf
          exact hM1c' j (by omega) f hf'
      · -- complexity
        intro j hj f hf
        have hjd : j ≤ d := by omega
        by_cases h : j = d
        · rw [h] at hf ⊢
          rw [glue_self, glueNat_of_ne (d + 1) Md M1 (by omega : d ≠ d + 1), hM1d]
          have hh : d + 1 - d = 1 := by omega
          rw [hh] at hf
          exact hM'bound f hf
        · rw [glue_of_ne d B0 B1 h,
            glueNat_of_ne (d + 1) Md M1 (by omega : j ≠ d + 1)]
          have hf' : f ∈ lev (lev Hd 1) (d - j) := by rwa [lev_shift Hd hjd] at hf
          exact hM1cx j (by omega) f hf'
      · -- energy gap
        intro j hj1 hj2 e he Ee hmeas
        by_cases h : j = d + 1
        · rw [h] at he hmeas ⊢
          have he' : e ∈ lev Hd 0 := by
            have hh : d + 1 - (d + 1) = 0 := by omega
            rwa [hh] at he
          have hmeas' : (Bd e).IsMeas Ee := by
            have hh : edgeAlg (V := V) Bd (glue d B0 B1) (d + 1) (d + 1) = Bd := by
              show (if d + 1 = d + 1 then Bd else glue d B0 B1 (d + 1)) = Bd
              rw [if_pos rfl]
            rwa [hh] at hmeas
          have h1 := h0e1 e he' Ee hmeas'
          have hh1 : (d + 1) - 1 = d := by omega
          rw [hh1, glue_self, glue_self, glueNat_self]
          exact le_of_lt h1
        · have hjd : j ≤ d := by omega
          have hmeas' : (edgeAlg (V := V) B0 B1 d j e).IsMeas Ee := by
            have hh := edgeAlg_glue_ne (V := V) (Bd := Bd) (B0 := B0) (B1 := B1) h
            rwa [hh] at hmeas
          have he' : e ∈ lev (lev Hd 1) (d - j) := by rwa [lev_shift Hd hjd] at he
          have h1 := hM1e j hj1 hjd e he' Ee hmeas'
          have hh1 : j - 1 ≠ d := by omega
          rw [glue_of_ne d B0' B1' hh1, glue_of_ne d B0 B1 hh1,
            glueNat_of_ne (d + 1) Md M1 (by omega : j ≠ d + 1)]
          exact h1
      · -- discrepancy
        intro j hj1 hj2 e he Ee hmeas
        by_cases h : j = d + 1
        · rw [h] at he hmeas ⊢
          have he' : e ∈ lev Hd 0 := by
            have hh : d + 1 - (d + 1) = 0 := by omega
            rwa [hh] at he
          have hmeas' : (Bd e).IsMeas Ee := by
            have hh : edgeAlg (V := V) Bd (glue d B0 B1) (d + 1) (d + 1) = Bd := by
              show (if d + 1 = d + 1 then Bd else glue d B0 B1 (d + 1)) = Bd
              rw [if_pos rfl]
            rwa [hh] at hmeas
          have h1 := h0e2 e he' Ee hmeas'
          have hh1 : (d + 1) - 1 = d := by omega
          rw [hh1, glue_self,
            glueNat_of_ne (d + 1) Md M1 (by omega : d ≠ d + 1), hM1d]
          exact h1
        · have hjd : j ≤ d := by omega
          have hmeas' : (edgeAlg (V := V) B0 B1 d j e).IsMeas Ee := by
            have hh := edgeAlg_glue_ne (V := V) (Bd := Bd) (B0 := B0) (B1 := B1) h
            rwa [hh] at hmeas
          have he' : e ∈ lev (lev Hd 1) (d - j) := by rwa [lev_shift Hd hjd] at he
          have h1 := hM1dsc j hj1 hjd e he' Ee hmeas'
          have hh1 : j - 1 ≠ d := by omega
          rw [glue_of_ne d B0' B1' hh1,
            glueNat_of_ne (d + 1) Md M1 (by omega : j - 1 ≠ d + 1)]
          exact h1

end Szemeredi.Removal
