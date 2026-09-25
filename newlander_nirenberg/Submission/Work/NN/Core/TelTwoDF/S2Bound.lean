/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The loss-free `C^{k,α}` estimate for the parameterised `(0,2)`-telescoping

`S2 G η` (`Submission/Work/NN/Core/TelTwoDF/Defs.lean`) is the solution operator of the
parameterised `(0,2)`-`∂̄`-recursion: it processes the coordinates one at a time, multiplying the
stage data by the smooth cutoffs `1 - kappa G s` and applying the Cauchy-type transform
`TL G s = dbarTransform (G.r s) s`.

This file proves that, for every `k`, the `C^{k,α}`-norm of `S2 G η` on the solving polydisc
`Eset G n = polydisc 0 G.e` is bounded by a constant times the sum of the `C^{k,α}`-norms of the
datum `η` on `Eset G 0 = polydisc 0 G.b`, *conditional on the localised transform bound*
`dbarTransform_Eset_le` (whose statement is exactly the hypothesis `hT` below, so that the
iteration can be developed and checked independently of it).

The proof iterates the one-step bound over the `n` stages of the recursion, exactly as in the
fixed-cutoff `Work.NN.Final.uS2_holderNorm_uniform`.  Writing
`S := Σ_{i,l} ‖η_{i l}‖_{C^{k,α}(Eset G 0)}` and `Kl` for the one-step constant, the invariant is

  `‖uD G η m i l‖_{C^{k,α}(Eset G m)} ≤ Kl ^ m * S`   (`m ≤ n`),

which is proved by induction: the stage `m+1` data are `uStep G ⟨m⟩ (uD G η m)`, the tracking
polydisc shrinks from `Eset G m` to `Eset G (m+1) ⊆ Eset G m`, and the one-step bound is applied
with `A := Kl ^ m * S` (finite as soon as `S` is).  The `(0,1)`-form `uPsi G η s l` is the transform
of `kappa G s · uD G η s s l`, so the localised transform bound (measured on `Eset G (s+1)`) and
the cutoff product bound finish it, and `S2` is the sum of the `n` summands `uPsi`.
-/
import Mathlib
import Submission.Work.NN.Core.TelTwoDF.Defs
import Submission.Work.NN.Core.TelTwoDF.EstimateDefs
import Submission.Work.NN.Core.TelTwoDF.Rec2
import Submission.Work.NN.Core.TelTwoDF.ContDiffRec
import Submission.Work.NN.Core.TelTwoDF.cut_mul_Eset_le
import Submission.Work.CR.Flat.Holder.holderNorm_add_le
import Submission.Work.CR.Flat.Holder.holderNorm_sum_le

set_option maxHeartbeats 4000000

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.Core.TelTwoDF

variable {n : ℕ}

/-- The `C^{k,α}`-size of the datum `η`, measured on the support polydisc `Eset G 0`. -/
noncomputable def datumSum (k : ℕ) (α : ℝ) (G : Geom n)
    (η : Fin n → Fin n → (Fin n → ℂ) → ℂ) : ENNReal :=
  ∑ i : Fin n, ∑ l : Fin n, Work.CR.Flat.holderNorm k α (η i l) (Eset G 0)

lemma le_datumSum {k : ℕ} {α : ℝ} {G : Geom n} {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (i l : Fin n) :
    Work.CR.Flat.holderNorm k α (η i l) (Eset G 0) ≤ datumSum k α G η := by
  have h1 : Work.CR.Flat.holderNorm k α (η i l) (Eset G 0)
      ≤ ∑ l' : Fin n, Work.CR.Flat.holderNorm k α (η i l') (Eset G 0) :=
    Finset.single_le_sum
      (f := fun l' : Fin n => Work.CR.Flat.holderNorm k α (η i l') (Eset G 0))
      (fun _ _ => zero_le) (Finset.mem_univ l)
  have h2 : (∑ l' : Fin n, Work.CR.Flat.holderNorm k α (η i l') (Eset G 0))
      ≤ ∑ i' : Fin n, ∑ l' : Fin n, Work.CR.Flat.holderNorm k α (η i' l') (Eset G 0) :=
    Finset.single_le_sum
      (f := fun i' : Fin n => ∑ l' : Fin n, Work.CR.Flat.holderNorm k α (η i' l') (Eset G 0))
      (fun _ _ => zero_le) (Finset.mem_univ i)
  rw [datumSum]
  exact le_trans h1 h2

theorem S2_holderNorm_E_le_of_transform {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (k : ℕ)
    (G : Geom n)
    (hT : ∃ C : ℝ, 0 < C ∧ ∀ (s : Fin n) (g : (Fin n → ℂ) → ℂ),
      ContDiff ℝ k g →
      (∀ y : Fin n → ℂ, G.b s ≤ ‖y s‖ → g y = 0) →
      Work.CR.Flat.holderNorm k α (Work.CR.Flat.Cauchy.dbarTransform (G.r s) s g)
          (Eset G ((s : ℕ) + 1))
        ≤ ENNReal.ofReal C * Work.CR.Flat.holderNorm k α g (Eset G (s : ℕ))) :
    ∃ C : ENNReal, C ≠ ⊤ ∧ ∀ (η : Fin n → Fin n → (Fin n → ℂ) → ℂ),
      (∀ i l, ContDiff ℝ k (η i l)) → ∀ j : Fin n,
      Work.CR.Flat.holderNorm k α (S2 G η j) (Eset G n)
        ≤ C * ∑ i : Fin n, ∑ l : Fin n,
            Work.CR.Flat.holderNorm k α (η i l) (Eset G 0) := by
  obtain ⟨CT, hCT0, hCT⟩ := hT
  obtain ⟨L, hLne, hL1, hL2, hL3⟩ := cut_mul_Eset_le (n := n) hα0 hα1 k G
  have hCTne : ENNReal.ofReal CT ≠ ⊤ := ENNReal.ofReal_ne_top
  -- the one-step constant
  set Kl : ENNReal := (L + ENNReal.ofReal CT * L) + 1 with hKldef
  have hKl1 : 1 ≤ Kl := by rw [hKldef]; exact le_add_left le_rfl
  have hKlne : Kl ≠ ⊤ := by
    rw [hKldef]
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr ⟨hLne, ENNReal.mul_ne_top hCTne hLne⟩, by simp⟩
  have hLKl : L ≤ Kl := by rw [hKldef]; exact le_add_right (le_add_right le_rfl)
  have hTLKl : ENNReal.ofReal CT * L ≤ Kl := by
    rw [hKldef]; exact le_add_right (le_add_left le_rfl)
  -- the one-step bound
  have hstep : ∀ (s : Fin n) (D : Fin n → Fin n → (Fin n → ℂ) → ℂ),
      (∀ i l, ContDiff ℝ k (D i l)) → ∀ A : ENNReal, A ≠ ⊤ →
      (∀ i l, Work.CR.Flat.holderNorm k α (D i l) (Eset G (s : ℕ)) ≤ A) →
      ∀ i l, Work.CR.Flat.holderNorm k α (uStep G s D i l) (Eset G ((s : ℕ) + 1)) ≤ Kl * A := by
    intro s D hD A hA hAb i l
    have hmono : ∀ {g : (Fin n → ℂ) → ℂ},
        Work.CR.Flat.holderNorm k α g (Eset G ((s : ℕ) + 1))
          ≤ Work.CR.Flat.holderNorm k α g (Eset G (s : ℕ)) := fun {g} =>
      Work.CR.Flat.holderNorm_mono_set (isOpen_Eset G (s : ℕ)) (isOpen_Eset G ((s : ℕ) + 1))
        (Eset_succ_subset G (s : ℕ)) k α g
    have hdir : Work.CR.Flat.holderNorm k α
        (fun z => (1 - kappa G s z) * D i l z) (Eset G ((s : ℕ) + 1)) ≤ L * A :=
      le_trans hmono (hL3 s (D i l) (hD i l) A hA (hAb i l))
    have hg : ContDiff ℝ k (fun y : Fin n → ℂ => kappabar G s y * D i l y) :=
      ((contDiff_kappabar G s).of_le (by exact_mod_cast le_top)).mul (hD i l)
    have hTLc : ContDiff ℝ k (fun z => TL G s (fun y => kappabar G s y * D i l y) z) := by
      change ContDiff ℝ k (TL G s fun y => kappabar G s y * D i l y)
      rw [TL_eq G s hg.continuous]
      exact contDiff_dbarTransform_univ (G.b_pos s).le s k hg
        (fun y hy => by rw [kappabar_eq_zero_of_ge G s hy, zero_mul])
    have htr : Work.CR.Flat.holderNorm k α
        (fun z => TL G s (fun y => kappabar G s y * D i l y) z) (Eset G ((s : ℕ) + 1))
        ≤ ENNReal.ofReal CT * L * A := by
      have heq : (fun z => TL G s (fun y => kappabar G s y * D i l y) z)
          = Work.CR.Flat.Cauchy.dbarTransform (G.r s) s
              (fun y => kappabar G s y * D i l y) := by
        rw [show (fun z => TL G s (fun y => kappabar G s y * D i l y) z)
            = TL G s (fun y => kappabar G s y * D i l y) from rfl, TL_eq G s hg.continuous]
      rw [heq]
      have h1 : Work.CR.Flat.holderNorm k α (Work.CR.Flat.Cauchy.dbarTransform (G.r s) s
            (fun y => kappabar G s y * D i l y)) (Eset G ((s : ℕ) + 1))
          ≤ ENNReal.ofReal CT * Work.CR.Flat.holderNorm k α
              (fun y => kappabar G s y * D i l y) (Eset G (s : ℕ)) :=
        hCT s (fun y => kappabar G s y * D i l y) hg
          (fun y hy => by rw [kappabar_eq_zero_of_ge G s hy, zero_mul])
      have h2 : Work.CR.Flat.holderNorm k α (fun y => kappabar G s y * D i l y)
          (Eset G (s : ℕ)) ≤ L * A :=
        hL2 s (D i l) (hD i l) A hA (hAb i l)
      calc Work.CR.Flat.holderNorm k α (Work.CR.Flat.Cauchy.dbarTransform (G.r s) s
              (fun y => kappabar G s y * D i l y)) (Eset G ((s : ℕ) + 1))
          ≤ ENNReal.ofReal CT * Work.CR.Flat.holderNorm k α
              (fun y => kappabar G s y * D i l y) (Eset G (s : ℕ)) := h1
        _ ≤ ENNReal.ofReal CT * (L * A) := mul_le_mul_right h2 (ENNReal.ofReal CT)
        _ = ENNReal.ofReal CT * L * A := by rw [mul_assoc]
    by_cases hc : i = s ∨ l = s
    · rw [show uStep G s D i l = fun z => (1 - kappa G s z) * D i l z from by
        funext z; rw [uStep_apply, if_pos hc]; ring]
      exact le_trans hdir (mul_le_mul_left hLKl A)
    · rw [show uStep G s D i l = fun z => (1 - kappa G s z) * D i l z
          + TL G s (fun y => kappabar G s y * D i l y) z from by
        funext z; rw [uStep_apply, if_neg hc]]
      refine le_trans (Work.CR.Flat.Holder.holderNorm_add_le (k := k) (α := α)
        (f := fun z => (1 - kappa G s z) * D i l z)
        (g := fun z => TL G s (fun y => kappabar G s y * D i l y) z)
        (Ω := Eset G ((s : ℕ) + 1))
        ((((contDiff_const.sub (contDiff_kappa G s)).of_le (by exact_mod_cast le_top)).mul
          (hD i l)).contDiffOn) hTLc.contDiffOn
        (isOpen_Eset G ((s : ℕ) + 1)).uniqueDiffOn) ?_
      refine le_trans (add_le_add hdir htr) ?_
      rw [← add_mul]
      exact mul_le_mul_left (le_add_right le_rfl) A
  -- the stage bound
  have hiter : ∀ (η : Fin n → Fin n → (Fin n → ℂ) → ℂ), (∀ i l, ContDiff ℝ k (η i l)) →
      datumSum k α G η ≠ ⊤ → ∀ m ≤ n, ∀ i l,
      Work.CR.Flat.holderNorm k α (uD G η m i l) (Eset G m) ≤ Kl ^ m * datumSum k α G η := by
    intro η hη hS m
    induction m with
    | zero =>
        intro _ i l
        rw [uD_zero, pow_zero, one_mul]
        exact le_datumSum i l
    | succ m ih =>
        intro hm i l
        have hm' : m < n := by omega
        have hIH : ∀ i' l', Work.CR.Flat.holderNorm k α (uD G η m i' l') (Eset G m)
            ≤ Kl ^ m * datumSum k α G η := fun i' l' => ih (by omega) i' l'
        have hAne : Kl ^ m * datumSum k α G η ≠ ⊤ :=
          ENNReal.mul_ne_top (ENNReal.pow_ne_top hKlne) hS
        rw [uD_succ_of_lt G η hm']
        refine le_trans (hstep ⟨m, hm'⟩ (uD G η m) (fun i l => uD_contDiff_k G hη m (by omega) i l)
          (Kl ^ m * datumSum k α G η) hAne hIH i l) ?_
        rw [pow_succ]
        exact le_of_eq (by ac_rfl)
  -- the summand bound
  have hpsi : ∀ (η : Fin n → Fin n → (Fin n → ℂ) → ℂ), (∀ i l, ContDiff ℝ k (η i l)) →
      datumSum k α G η ≠ ⊤ → ∀ s l,
      Work.CR.Flat.holderNorm k α (uPsi G η s l) (Eset G n)
        ≤ (ENNReal.ofReal CT * L * Kl ^ n) * datumSum k α G η := by
    intro η hη hS s l
    have hD : ContDiff ℝ k (uD G η (s : ℕ) s l) :=
      uD_contDiff_k G hη (s : ℕ) (le_of_lt s.isLt) s l
    have hg : ContDiff ℝ k (fun y : Fin n → ℂ => kappa G s y * uD G η (s : ℕ) s l y) :=
      ((contDiff_kappa G s).of_le (by exact_mod_cast le_top)).mul hD
    have heq : uPsi G η s l = Work.CR.Flat.Cauchy.dbarTransform (G.r s) s
        (fun y => kappa G s y * uD G η (s : ℕ) s l y) := by
      rw [show uPsi G η s l = TL G s (fun y => kappa G s y * uD G η (s : ℕ) s l y) from rfl,
        TL_eq G s hg.continuous]
    have hB : Kl ^ (s : ℕ) * datumSum k α G η ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.pow_ne_top hKlne) hS
    have hcut := hL1 s (uD G η (s : ℕ) s l) hD (Kl ^ (s : ℕ) * datumSum k α G η) hB
      (hiter η hη hS (s : ℕ) (le_of_lt s.isLt) s l)
    have hmono : Work.CR.Flat.holderNorm k α (uPsi G η s l) (Eset G n)
        ≤ Work.CR.Flat.holderNorm k α (uPsi G η s l) (Eset G ((s : ℕ) + 1)) :=
      Work.CR.Flat.holderNorm_mono_set (Ω := Eset G ((s : ℕ) + 1)) (Ω' := Eset G n)
        (isOpen_Eset G ((s : ℕ) + 1)) (isOpen_Eset G n)
        (Eset_mono G (by omega : (s : ℕ) + 1 ≤ n)) k α (uPsi G η s l)
    have h1 : Work.CR.Flat.holderNorm k α (uPsi G η s l) (Eset G ((s : ℕ) + 1))
        ≤ ENNReal.ofReal CT * Work.CR.Flat.holderNorm k α
            (fun y => kappa G s y * uD G η (s : ℕ) s l y) (Eset G (s : ℕ)) := by
      rw [heq]
      exact hCT s _ hg (fun y hy => by rw [kappa_eq_zero G s hy, zero_mul])
    have h2 : Work.CR.Flat.holderNorm k α (fun y => kappa G s y * uD G η (s : ℕ) s l y)
        (Eset G (s : ℕ)) ≤ L * (Kl ^ (s : ℕ) * datumSum k α G η) := hcut
    have h3 : Kl ^ (s : ℕ) * datumSum k α G η ≤ Kl ^ n * datumSum k α G η :=
      mul_le_mul_left (pow_le_pow_right₀ hKl1 (le_of_lt s.isLt)) (datumSum k α G η)
    calc Work.CR.Flat.holderNorm k α (uPsi G η s l) (Eset G n)
        ≤ Work.CR.Flat.holderNorm k α (uPsi G η s l) (Eset G ((s : ℕ) + 1)) := hmono
      _ ≤ ENNReal.ofReal CT * Work.CR.Flat.holderNorm k α
            (fun y => kappa G s y * uD G η (s : ℕ) s l y) (Eset G (s : ℕ)) := h1
      _ ≤ ENNReal.ofReal CT * (L * (Kl ^ (s : ℕ) * datumSum k α G η)) :=
            mul_le_mul_right h2 (ENNReal.ofReal CT)
      _ ≤ ENNReal.ofReal CT * (L * (Kl ^ n * datumSum k α G η)) :=
            mul_le_mul_right (mul_le_mul_right h3 L) (ENNReal.ofReal CT)
      _ = (ENNReal.ofReal CT * L * Kl ^ n) * datumSum k α G η := by ac_rfl
  -- the final assembly
  have hfinal : ∀ (η : Fin n → Fin n → (Fin n → ℂ) → ℂ), (∀ i l, ContDiff ℝ k (η i l)) →
      datumSum k α G η ≠ ⊤ → ∀ j : Fin n,
      Work.CR.Flat.holderNorm k α (S2 G η j) (Eset G n)
        ≤ ((n : ENNReal) * (ENNReal.ofReal CT * L * Kl ^ n)) * datumSum k α G η := by
    intro η hη hS j
    have hS2eq : S2 G η j = fun z => ∑ s ∈ Finset.univ, uPsi G η s j z := by
      funext z
      rw [S2_apply]
    rw [hS2eq]
    refine le_trans (Work.CR.Flat.Holder.holderNorm_sum_le (k := k) (α := α) Finset.univ
      (fun s _ => (uPsi_contDiff_k G hη s j).contDiffOn)
      (isOpen_Eset G n).uniqueDiffOn) ?_
    calc ∑ s ∈ Finset.univ, Work.CR.Flat.holderNorm k α (uPsi G η s j) (Eset G n)
        ≤ ∑ _s ∈ Finset.univ, (ENNReal.ofReal CT * L * Kl ^ n) * datumSum k α G η :=
          Finset.sum_le_sum fun s _ => hpsi η hη hS s j
      _ = (n : ENNReal) * ((ENNReal.ofReal CT * L * Kl ^ n) * datumSum k α G η) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = ((n : ENNReal) * (ENNReal.ofReal CT * L * Kl ^ n)) * datumSum k α G η := by
          ac_rfl
  refine ⟨(n : ENNReal) * (ENNReal.ofReal CT * L * Kl ^ n) + 1, ?_, ?_⟩
  · refine ENNReal.add_ne_top.mpr ⟨?_, by simp⟩
    exact ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top (ENNReal.mul_ne_top hCTne hLne)
      (ENNReal.pow_ne_top hKlne))
  · intro η hη j
    by_cases hS : datumSum k α G η = ⊤
    · have hS' : (∑ i : Fin n, ∑ l : Fin n,
          Work.CR.Flat.holderNorm k α (η i l) (Eset G 0)) = ⊤ := hS
      rw [hS', ENNReal.mul_top]
      · exact le_top
      · intro h0
        have h1 : (1 : ENNReal) ≤ 0 := by rw [← h0]; exact le_add_left le_rfl
        exact one_ne_zero (le_antisymm h1 bot_le)
    · refine le_trans (hfinal η hη hS j) ?_
      rw [datumSum]
      exact mul_le_mul_left (le_add_right le_rfl) _

end Work.NN.Core.TelTwoDF
