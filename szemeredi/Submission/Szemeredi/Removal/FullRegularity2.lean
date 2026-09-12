import Mathlib
import Submission.Szemeredi.Removal.LadderM

/-!
# The corrected full regularity lemma

Tao's full regularity lemma (`Szemeredi.Removal.full_regularity`) derives a
discrepancy bound `1/F(M_{j-1})` which is in the wrong direction for the counting
lemma: the counting lemma needs the bound `1/F(M_0)` where `M_0` is the *largest*
complexity in the hierarchy.

This file implements Tao's repair: run the top preliminary-regularity step with an
artificial growth function `Gfast` that dominates `F` at the a priori bound
`Mbdd` for the bottom complexity.  The a priori bounds are built as explicit
recursive functions of the inputs.
-/

open scoped BigOperators
open Finset
open Szemeredi.Removal.SigAlg

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Szemeredi.Removal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : ι → Type*} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] [∀ i, Nonempty (V i)]

/-- Bundled a priori complexity data.  At level `d` it consists of
* `Mbdd d Hd Md`: an a priori bound for the bottom complexity `M 0` of the
  regularity lemma run on the `d`-uniform hypergraph `Hd` with input complexity
  `Md`;
* `Gfast d Hd`: the growth function with which the *top* preliminary-regularity
  step of that run must be executed. -/
noncomputable def auxB (F : ℕ → ℕ) :
    ℕ → ((Finset (Finset ι) → ℕ → ℕ) × (Finset (Finset ι) → ℕ → ℕ))
| 0 => (fun _ Md => Md, fun _ n => F n)
| (d + 1) =>
    let p := auxB F d
    let G : Finset (Finset ι) → ℕ → ℕ := fun Hd n => max (F n) (F (p.1 (bdry Hd) n)) + 1
    (fun Hd Md => p.1 (bdry Hd)
        (max (G Hd Md) (ladderM Hd Md (G Hd) (stepCnt Hd Md F))), G)

/-- The a priori bound for the bottom complexity. -/
noncomputable def MbddF (F : ℕ → ℕ) (d : ℕ) (Hd : Finset (Finset ι)) (Md : ℕ) : ℕ :=
  (auxB (ι := ι) F d).1 Hd Md

/-- The growth function for the top preliminary-regularity step. -/
noncomputable def GfastF (F : ℕ → ℕ) (d : ℕ) (Hd : Finset (Finset ι)) (n : ℕ) : ℕ :=
  (auxB (ι := ι) F d).2 Hd n

@[simp] theorem MbddF_zero (F : ℕ → ℕ) (Hd : Finset (Finset ι)) (Md : ℕ) :
    MbddF F 0 Hd Md = Md := rfl

@[simp] theorem GfastF_zero (F : ℕ → ℕ) (Hd : Finset (Finset ι)) (n : ℕ) :
    GfastF F 0 Hd n = F n := rfl

theorem GfastF_succ (F : ℕ → ℕ) (d : ℕ) (Hd : Finset (Finset ι)) (n : ℕ) :
    GfastF F (d + 1) Hd n = max (F n) (F (MbddF F d (bdry Hd) n)) + 1 := rfl

theorem MbddF_succ (F : ℕ → ℕ) (d : ℕ) (Hd : Finset (Finset ι)) (Md : ℕ) :
    MbddF F (d + 1) Hd Md
      = MbddF F d (bdry Hd) (max (GfastF F (d + 1) Hd Md)
          (ladderM Hd Md (GfastF F (d + 1) Hd) (stepCnt Hd Md F))) := rfl

/-- Monotonicity of the a priori data. -/
theorem auxB_good {F : ℕ → ℕ} (hF : Monotone F) (d : ℕ) :
    (∀ Hd : Finset (Finset ι), Monotone (fun n => MbddF F d Hd n)) ∧
    (∀ Hd : Finset (Finset ι), Monotone (GfastF F d Hd)) := by
  induction d with
  | zero =>
      refine ⟨fun Hd => monotone_id, fun Hd => hF⟩
  | succ d ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have hGmono : ∀ Hd : Finset (Finset ι), Monotone (GfastF F (d + 1) Hd) := by
        intro Hd n1 n2 h
        rw [GfastF_succ F d Hd n1, GfastF_succ F d Hd n2]
        exact Nat.add_le_add_right
          (max_le_max (hF h) (hF (ih1 (bdry Hd) h))) 1
      refine ⟨fun Hd n1 n2 h => ?_, hGmono⟩
      dsimp only
      rw [MbddF_succ F d Hd n1, MbddF_succ F d Hd n2]
      refine ih1 (bdry Hd) ?_
      refine max_le_max (hGmono Hd h) ?_
      exact ladderM_mono (G := GfastF F (d + 1) Hd) (hGmono Hd) h
        (stepCnt_mono Hd F hF h)

theorem MbddF_mono {F : ℕ → ℕ} (hF : Monotone F) (d : ℕ) (Hd : Finset (Finset ι)) :
    Monotone (fun n => MbddF F d Hd n) := (auxB_good (ι := ι) hF d).1 Hd

theorem GfastF_mono {F : ℕ → ℕ} (hF : Monotone F) (d : ℕ) (Hd : Finset (Finset ι)) :
    Monotone (GfastF F d Hd) := (auxB_good (ι := ι) hF d).2 Hd

theorem Pseudorandom.mono {e : Finset ι} {Ee : Finset (Pt V)} {B : SigAlg (Pt V)}
    {δ δ' : ℝ} (h : Pseudorandom (V := V) e Ee B δ) (hδ : δ ≤ δ') :
    Pseudorandom (V := V) e Ee B δ' :=
  fun Ex hEx => le_trans (h Ex hEx) hδ

/-- The conclusion of the corrected full regularity lemma.  Compared with
`RegOK`, the recursion is stated as an inequality (the top preliminary step uses
the faster growth function `Gfast`), the discrepancy bound is `1/F(M 0)` with
`M 0` the *largest* complexity, and the a priori bound `M 0 ≤ MbddF F d Hd Md` is
recorded. -/
def RegOK2 (d : ℕ) (Hd : Finset (Finset ι)) (Bd : Finset ι → SigAlg (Pt V)) (Md : ℕ)
    (F : ℕ → ℕ) (B B' : ℕ → Finset ι → SigAlg (Pt V)) (M : ℕ → ℕ) : Prop :=
  M d = Md ∧
  M 0 ≤ MbddF F d Hd Md ∧
  (∀ j < d, max (F (M (j + 1)))
      ((lev Hd (d - j)).sup (fun f => (B j f).complexity)) ≤ M j) ∧
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
          (1 / (F (M 0) : ℝ)))

/-- The complexities `M j` decrease in `j`. -/
theorem RegOK2.M_anti {d : ℕ} {Hd : Finset (Finset ι)} {Bd : Finset ι → SigAlg (Pt V)} {Md : ℕ}
    {F : ℕ → ℕ} {B B' : ℕ → Finset ι → SigAlg (Pt V)} {M : ℕ → ℕ}
    (h : RegOK2 (V := V) d Hd Bd Md F B B' M) (hF : ∀ n, n + 1 ≤ F n) :
    ∀ j k, j ≤ k → k ≤ d → M k ≤ M j := by
  have hstep : ∀ j, j < d → M (j + 1) ≤ M j := by
    intro j hj
    have h1 := h.2.2.1 j hj
    have h2 := hF (M (j + 1))
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

/-- **Corrected full regularity lemma.**  Same as Tao's Lemma 2.6
(`Szemeredi.Removal.full_regularity`) except that the discrepancy bound is
`1/F(M 0)` with `M 0` the *largest* complexity, which is what the counting lemma
needs.  To obtain it, the top preliminary-regularity step is run with the faster
growth function `GfastF F d Hd`, which dominates `F` at the a priori bound for
the bottom complexity. -/
theorem full_regularity2 (d : ℕ) :
    ∀ (Hd : Finset (Finset ι)) (Bd : Finset ι → SigAlg (Pt V)) (Md : ℕ) (F : ℕ → ℕ),
    (∀ n, n + 1 ≤ F n) → Monotone F → (∀ e ∈ Hd, (Bd e).complexity ≤ Md) →
    ∃ B B' : ℕ → Finset ι → SigAlg (Pt V), ∃ M : ℕ → ℕ,
      RegOK2 (V := V) d Hd Bd Md F B B' M := by
  induction d with
  | zero =>
      intro Hd Bd Md F hF hFmono hm
      refine ⟨fun _ _ => SigAlg.triv, fun _ _ => SigAlg.triv, fun _ => Md, ?_⟩
      refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp
      · intro j hj; exact absurd hj (Nat.not_lt_zero j)
      · intro j hj; exact absurd hj (Nat.not_lt_zero j)
      · intro j hj; exact absurd hj (Nat.not_lt_zero j)
      · intro j hj; exact absurd hj (Nat.not_lt_zero j)
      · intro j hj; exact absurd hj (Nat.not_lt_zero j)
      · intro j hj1 hj2; omega
      · intro j hj1 hj2; omega
  | succ d ih =>
      intro Hd Bd Md F hF hFmono hm
      have hFpos_nat : 1 ≤ F Md := by have := hF Md; omega
      have hFpos : (0 : ℝ) < (F Md : ℝ) := by exact_mod_cast hFpos_nat
      have hε : (0 : ℝ) < 1 / (F Md : ℝ) := by positivity
      have hG1 : ∀ n, 1 ≤ GfastF F (d + 1) Hd n := by
        intro n
        rw [GfastF_succ F d Hd n]
        have := hF n
        omega
      have hGsucc : ∀ n, n + 1 ≤ GfastF F (d + 1) Hd n := by
        intro n
        rw [GfastF_succ F d Hd n]
        have := hF n
        omega
      have hGmono : Monotone (GfastF F (d + 1) Hd) := GfastF_mono hFmono (d + 1) Hd
      have hB : ladder (lev Hd 0) Md (1 / (F Md : ℝ)) (GfastF F (d + 1) Hd)
            (prelimK (lev Hd 0) Md (1 / (F Md : ℝ)))
          ≤ ladderM (lev Hd 0) Md (GfastF F (d + 1) Hd)
              (stepCnt (lev Hd 0) Md F) := by
        refine le_trans (ladder_le_ladderM (H := lev Hd 0) (m := Md) (ε := 1 / (F Md : ℝ))
          (G := GfastF F (d + 1) Hd) hε ?_ hG1 hGmono _) ?_
        · rw [div_le_one hFpos]
          exact_mod_cast hFpos_nat
        · exact ladderM_mono_K _ _ _ (prelimK_one_div_le_stepCnt (lev Hd 0) Md F (by omega))
      obtain ⟨B0, hB0coord, hB0c, hB0done⟩ :=
        preliminary_regularity_bounded (V := V) (H := lev Hd 0) (Be := Bd) (m := Md)
          (ε := 1 / (F Md : ℝ)) (G := GfastF F (d + 1) Hd)
          (B := ladderM (lev Hd 0) Md (GfastF F (d + 1) Hd) (stepCnt (lev Hd 0) Md F))
          hm hε hGsucc hGmono hB
      obtain ⟨B0', hB0ref, hB0c', hb0e1, hb0e2⟩ := hB0done
      set M' : ℕ := Mbound (GfastF F (d + 1) Hd) Md (lev Hd 0) B0 with hM'def
      have hM'le : M' ≤ max (GfastF F (d + 1) Hd Md)
          (ladderM (lev Hd 0) Md (GfastF F (d + 1) Hd) (stepCnt (lev Hd 0) Md F)) := by
        rw [hM'def]
        unfold Mbound
        exact max_le_max (le_refl _) (Finset.sup_le (fun f hf => hB0c f hf))
      have hM'bound : ∀ e ∈ lev Hd 1, (B0 e).complexity ≤ M' := by
        intro e he
        rw [hM'def]
        unfold Mbound
        exact le_trans (Finset.le_sup (s := bdry (lev Hd 0))
            (f := fun f => (B0 f).complexity) he) (le_max_right _ _)
      obtain ⟨B1, B1', M1, hReg1⟩ := ih (lev Hd 1) B0 M' F hF hFmono hM'bound
      refine ⟨glue d B0 B1, glue d B0' B1', glueNat (d + 1) Md M1, ?_⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact glueNat_self (d + 1) Md M1
      · -- a priori bound on the bottom complexity
        have h0 : glueNat (d + 1) Md M1 0 = M1 0 :=
          glueNat_of_ne (d + 1) Md M1 (by omega : 0 ≠ d + 1)
        rw [h0]
        refine le_trans hReg1.2.1 ?_
        rw [MbddF_succ F d Hd Md]
        exact MbddF_mono hFmono d (bdry Hd) hM'le
      · -- the recursion
        intro j hj
        have hjd : j ≤ d := by omega
        by_cases h : j = d
        · rw [h] at ⊢
          rw [glueNat_of_ne (d + 1) Md M1 (by omega : d ≠ d + 1), glueNat_self,
            glue_self, hReg1.1]
          have hh : lev Hd (d + 1 - d) = lev Hd 1 := by congr 1; omega
          rw [hh, hM'def]
          unfold Mbound
          refine max_le_max ?_ (le_refl _)
          rw [GfastF_succ F d Hd Md]
          exact le_trans (le_max_left _ _) (Nat.le_succ _)
        · rw [glueNat_of_ne (d + 1) Md M1 (by omega : j ≠ d + 1),
            glueNat_of_ne (d + 1) Md M1 (by omega : j + 1 ≠ d + 1),
            lev_shift Hd hjd, glue_of_ne d B0 B1 h]
          exact hReg1.2.2.1 j (by omega)
      · -- B refines coord
        intro j hj f hf
        have hjd : j ≤ d := by omega
        by_cases h : j = d
        · rw [h] at hf ⊢
          rw [glue_self]
          have hf' : f ∈ lev Hd 1 := by
            have hh : d + 1 - d = 1 := by omega
            rwa [hh] at hf
          exact hB0coord f hf'
        · rw [glue_of_ne d B0 B1 h]
          have hf' : f ∈ lev (lev Hd 1) (d - j) := by rwa [lev_shift Hd hjd] at hf
          exact hReg1.2.2.2.1 j (by omega) f hf'
      · -- B refines B'
        intro j hj f hf
        have hjd : j ≤ d := by omega
        by_cases h : j = d
        · rw [h] at hf ⊢
          simp only [glue_self]
          have hf' : f ∈ lev Hd 1 := by
            have hh : d + 1 - d = 1 := by omega
            rwa [hh] at hf
          exact hB0ref f hf'
        · rw [glue_of_ne d B0 B1 h, glue_of_ne d B0' B1' h]
          have hf' : f ∈ lev (lev Hd 1) (d - j) := by rwa [lev_shift Hd hjd] at hf
          exact hReg1.2.2.2.2.1 j (by omega) f hf'
      · -- B' refines coord
        intro j hj f hf
        have hjd : j ≤ d := by omega
        by_cases h : j = d
        · rw [h] at hf ⊢
          rw [glue_self]
          have hf' : f ∈ lev Hd 1 := by
            have hh : d + 1 - d = 1 := by omega
            rwa [hh] at hf
          exact hB0c' f hf'
        · rw [glue_of_ne d B0' B1' h]
          have hf' : f ∈ lev (lev Hd 1) (d - j) := by rwa [lev_shift Hd hjd] at hf
          exact hReg1.2.2.2.2.2.1 j (by omega) f hf'
      · -- complexity
        intro j hj f hf
        have hjd : j ≤ d := by omega
        by_cases h : j = d
        · rw [h] at hf ⊢
          rw [glue_self, glueNat_of_ne (d + 1) Md M1 (by omega : d ≠ d + 1), hReg1.1]
          have hh : d + 1 - d = 1 := by omega
          rw [hh] at hf
          exact hM'bound f hf
        · rw [glue_of_ne d B0 B1 h,
            glueNat_of_ne (d + 1) Md M1 (by omega : j ≠ d + 1)]
          have hf' : f ∈ lev (lev Hd 1) (d - j) := by rwa [lev_shift Hd hjd] at hf
          exact hReg1.2.2.2.2.2.2.1 j (by omega) f hf'
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
          have h1 := hb0e1 e he' Ee hmeas'
          have hh1 : (d + 1) - 1 = d := by omega
          rw [hh1, glue_self, glue_self, glueNat_self]
          exact le_of_lt h1
        · have hjd : j ≤ d := by omega
          have hmeas' : (edgeAlg (V := V) B0 B1 d j e).IsMeas Ee := by
            have hh := edgeAlg_glue_ne (V := V) (Bd := Bd) (B0 := B0) (B1 := B1) h
            rwa [hh] at hmeas
          have he' : e ∈ lev (lev Hd 1) (d - j) := by rwa [lev_shift Hd hjd] at he
          have h1 := hReg1.2.2.2.2.2.2.2.1 j hj1 hjd e he' Ee hmeas'
          have hh1 : j - 1 ≠ d := by omega
          rw [glue_of_ne d B0' B1' hh1, glue_of_ne d B0 B1 hh1,
            glueNat_of_ne (d + 1) Md M1 (by omega : j ≠ d + 1)]
          exact h1
      · -- discrepancy with respect to the *largest* complexity
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
          have h1 := hb0e2 e he' Ee hmeas'
          have hh1 : (d + 1) - 1 = d := by omega
          rw [hh1, glue_self, glueNat_of_ne (d + 1) Md M1 (by omega : 0 ≠ d + 1)]
          refine Pseudorandom.mono h1 ?_
          unfold deltaOf
          rw [← hM'def]
          have hle_nat : F (M1 0) ≤ GfastF F (d + 1) Hd M' := by
            rw [GfastF_succ F d Hd M']
            exact le_trans (hFmono hReg1.2.1) (le_trans (le_max_right _ _) (Nat.le_succ _))
          have hle : (F (M1 0) : ℝ) ≤ (GfastF F (d + 1) Hd M' : ℝ) := by
            exact_mod_cast hle_nat
          have hpos : (0 : ℝ) < (F (M1 0) : ℝ) := by
            have h1 : 0 < F (M1 0) := by have := hF (M1 0); omega
            exact_mod_cast h1
          exact one_div_le_one_div_of_le (a := (F (M1 0) : ℝ)) hpos hle
        · have hjd : j ≤ d := by omega
          have hmeas' : (edgeAlg (V := V) B0 B1 d j e).IsMeas Ee := by
            have hh := edgeAlg_glue_ne (V := V) (Bd := Bd) (B0 := B0) (B1 := B1) h
            rwa [hh] at hmeas
          have he' : e ∈ lev (lev Hd 1) (d - j) := by rwa [lev_shift Hd hjd] at he
          have h1 := hReg1.2.2.2.2.2.2.2.2 j hj1 hjd e he' Ee hmeas'
          have hh1 : j - 1 ≠ d := by omega
          rw [glue_of_ne d B0' B1' hh1,
            glueNat_of_ne (d + 1) Md M1 (by omega : 0 ≠ d + 1)]
          exact h1

end Szemeredi.Removal
