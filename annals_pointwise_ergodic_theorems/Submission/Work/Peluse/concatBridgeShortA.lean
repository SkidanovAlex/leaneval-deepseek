import Mathlib
import Submission.Work.Peluse.Holds.Corrected
import Submission.Work.Peluse.PET.boxNormPow_control_linear_v2
import Submission.Work.Peluse.Holds.ExpPET.petExpansion
import Submission.Work.Peluse.Holds.ExpPET.existsPairExpansion
import Submission.Work.Peluse.Concat.cruxDefs
import Submission.Work.Peluse.Concat.Zbox_omegaOf_indep
import Submission.Work.Peluse.Concat.uNormPow_level_raise_expl
import Submission.Work.Peluse.LadderB.boxLadder_le_norm

/-!
# `Work.Peluse.concatBridgeShortA` — assembly of the frozen §5 bridge from the ladder step

> ## WARNING — OFF-ROUTE since the lead's route change of 2026-10-03 (see `LADDER_STEP_LEAD.md`)
>
> This lane is **superseded** and its prover was cancelled by the project lead.  Every constant-loss
> one-step interface it was built on (`ladderStep`, `ladderStepA`, `ladderStepB`, `ladderStepQ`, the
> `LadderQ` Lemma 5.4/5.5/5.6 statements) is **FALSE** (CRT tensor family, `LADDER_STEP_LEAD.md` §1),
> and the frozen target `C46.ConcatBridgeShortA` itself, though not refuted, is *unreachable from the
> paper* (§2).  The live route is the lead-frozen power-loss `Holds/LadderP.lean`; its consumer is
> `Submission/Work/Peluse/Route.lean` (`PeluseConcatFixed_of_Pchain`,
> `KMTContract_AreaA2_of_openNodes`).  Do **not** consume this module; if you need the bridge, use
> `Work.Peluse.LadderP.ConcatBridgeShortB`.  The file is kept only as the record of the assembly's
> bookkeeping (iteration of the step along `Holds.boxLadder`, exponent bookkeeping, carve wiring),
> which the P5 node reuses.  The `sorry` below is *not* on any proved result's axiom footprint.
>
> The frozen target `Work.Peluse.C46.ConcatBridgeShortA` (the second half of Peluse's Theorem 3.5:
the `s` applications of her Lemma 5.6, from the short window `⌊γ'M₂⌋` to the uniformity norm at the
concatenated scale `⌊γ'γ'M₁M₂⌋`) is reduced here to the single one-step interface
`Work.Peluse.ladderStep` (`Submission/Work/Peluse/LadderStepDefs.lean`), whose proof is the
concatenation chapter of Peluse, *Bounds for sets with no polynomial progressions*
(arXiv:1909.00309), §5 — her Lemmas 5.1, 5.4, 5.5, 5.6 with the gcd input Lemma 5.2.

The assembly is the `s`-fold iteration of `ladderStep` along the ladder
`Work.Peluse.Holds.boxLadder`:
`Holds.boxLadder s 0 = Concat.boxAvg` (the short-window box average of the hypothesis) down to
`Holds.boxLadder 0 n = uNormPow` (the power of the uniformity norm at the concatenated scale).
The frozen statement's non-degeneracy hypotheses `A γ' ≤ γ^K` and `A ≤ M₂ (γ γ')^K` supply, with
`A = 1`, exactly the data conditions of the step (`1 ≤ L`, `1 ≤ D'`, `D' ≤ 2 M₁ L`, …); the
exponent bookkeeping (`C·(γ γ')^K` with the *same* `K` as the hypothesis) is handled by taking the
threshold `K₀` large enough to dominate the accumulated exponent of the `s` steps.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.Peluse

noncomputable section

/-! ## The running constants of the ladder iteration -/

/-! ## The two ends of the ladder -/

/-- The top of the ladder is the short-window box average of the frozen hypothesis, for the *same*
enumeration `ωOf` and for **any** value of the long window `D'` (which is unused when `n = 0`). -/
lemma boxLadder_top' (j : ℕ) (M₁ : ℕ) (c : ℤ) (ωOf : Fin (2 ^ j - 1) → (Fin j → Bool))
    (L D' N : ℕ) (f : ℤ → ℂ) :
    Holds.boxLadder j 0 M₁ c ωOf L D' N f = Concat.boxAvg j M₁ c ωOf L N f := by
  have hsl : ∀ h h' : Fin j → Fin M₁,
      Holds.ladderSlots j 0 M₁ c ωOf L D' h h'
        = Holds.ladderSlots j 0 M₁ c ωOf L 0 h h' := by
    intro h h'
    funext i
    simp only [Holds.ladderSlots]
    rw [dif_pos (by simpa using i.isLt), dif_pos (by simpa using i.isLt)]
  have h : Holds.boxLadder j 0 M₁ c ωOf L D' N f = Holds.boxLadder j 0 M₁ c ωOf L 0 N f := by
    unfold Holds.boxLadder
    rw [Finset.sum_congr rfl (fun h _ => Finset.sum_congr rfl (fun h' _ => by rw [hsl h h']))]
  rw [h, Holds.boxLadder_top]

/-- `Concat.boxAvg` is independent of the enumeration of the nonzero sign patterns. -/
lemma boxAvg_omegaOf_indep {s : ℕ} {c : ℤ} {L N M₁ : ℕ} {f : ℤ → ℂ}
    {ωOf : Fin (2 ^ s - 1) → (Fin s → Bool)}
    (hinj : Function.Injective ωOf) (hnz : ∀ i : Fin (2 ^ s - 1), ωOf i ≠ 0) :
    Concat.boxAvg s M₁ c ωOf L N f = Concat.boxAvg s M₁ c (Holds.omegaOf s) L N f := by
  have h : Concat.Zsum c L N M₁ ωOf f = Concat.Zsum c L N M₁ (Holds.omegaOf s) f := by
    simp only [Concat.Zsum]
    exact Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun h' _ =>
      Concat.Zbox_omegaOf_indep_gen (Concat.tupSub h h') ωOf (Holds.omegaOf s) hinj
        (Holds.omegaOf_injective s) hnz (Holds.omegaOf_ne_zero s)
  rw [Concat.boxAvg_eq, Concat.boxAvg_eq, h]

/-! ## The assembly

**Status (2026-10-03).**  `concatBridgeShortA_of_ladderStep` below is *proved* (sorry-free,
axiom-clean: `#print axioms = [propext, Classical.choice, Quot.sound]`), but it is **vacuous** for
two independent reasons, and the target is therefore *not* yet established:

1. it fixes the frozen statement's existential constant at `A = 1`, which does **not** exclude the
   collapsed window `L = ⌊γ'M₂⌋ = 1`; with `A ≥ 2` one instead gets `M₂ ≥ A^{K+1}γ^{-K(K+1)}` and
   `γ'M₂ ≥ A^K ≥ 2`, so the collapsed case is excluded — this is exactly the design of the frozen
   statement (`CONCAT_AUDIT_LEAD.md` §1.17: the existential `A` is what kills the collapsed window);
2. the hypothesis `∀ j, ladderStep j` is **FALSE**: `Submission/Work/Peluse/Ladder/ladderStepZero.lean`
   contains a machine-checked refutation (`not_ladderStepZero`).  At `L = 1` every short slot
   `arithIcc (c·d) 1` is a singleton and the level-1 box-norm power at a singleton is the normalised
   `ℓ²`-mass, independent of the shift, so the hypothesis carries no Gowers information while the
   conclusion demands a data-independent lower bound for the uniformity norm (the chirp of degree
   `s'+1` refutes it).

The corrected interface is `Work.Peluse.ladderStepA`
(`Submission/Work/Peluse/LadderStepDefs.lean`), which adds the paper's input normalisation `γ` with
`x ≤ γ ≤ x^{1/2^t}` (power mean ≥ mean) and the non-degeneracy `2 ≤ L·γ^K·(D'/(M₁L))^{K-1}` (the
frozen hypothesis `A ≤ M₂(γγ')^K` at `A = 2`, in the ladder's variables), together with the window
condition `D' ≤ M₁ L` (the paper's `γ' ≤ 1`; note `D' ≤ 2M₁L` would make the exponent `K-1`
vacuous for `D' ≥ M₁L` and re-admit the collapsed window).  Its two halves are delegated as
`Work.Peluse.LadderA.ladderStepAZero` and `Work.Peluse.LadderA.ladderStepASucc`.

**Remaining work.**  Rewrite this assembly against `ladderStepA`: choose `A = 2` (so that `γ' ≤ 1/2`
and hence `D'' ≤ 2γ'M₁L ≤ M₁L`); run the ladder with, at each step, `γ := x_j^{1/2^{t_j}}` (which
satisfies `x_j ≤ γ` and `γ ≤ x_j^{1/2^{t_j}}`), and discharge the non-degeneracy
`2 ≤ Lγ^K(D''/(M₁L))^{K-1}` from the frozen hypothesis `2 ≤ M₂(γγ')^K`, i.e. prove
`x_j^{1/2^{t_j}} ≥ γ`, which is `ladderCst_j^{1/2^{t_j}}·C₁^{Kexp_j/2^{t_j}}·γ^{K·Kexp_j/2^{t_j}-1} ≥ 1`:
it holds as soon as `K·Kexp_j ≤ 2^{t_j}`, and in the remaining range `K·Kexp_j > 2^{t_j}` the frozen
hypothesis `2 ≤ M₂(γγ')^K` forces `γ` close to `1`. -/


/-- The one-step level raising in the uniformity-norm normalisation:
`uNorm 1 ≤ 2^{1/4} · uNorm 2`. -/
lemma uNorm_one_le_two {Q : Finset ℤ} {N : ℕ} {f : ℤ → ℂ} (hN : 0 < N) (hQ : Q.Nonempty)
    (hbd : ∀ x ∈ Q, |x| ≤ (N : ℤ)) (hsup : SupportIn f N) (hbd1 : ∀ x : ℤ, ‖f x‖ ≤ 1) :
    Work.Peluse.uNorm 1 Q (Work.Peluse.symIcc N) f
      ≤ (2 : ℝ) ^ (1 / 4 : ℝ) * Work.Peluse.uNorm 2 Q (Work.Peluse.symIcc N) f := by
  have hraise := Concat.uNormPow_level_raise_expl 1 2 (le_refl 1) (by norm_num) Q (N := N) hN
    (f := f) hQ hbd hsup hbd1
  have hUnn : (0 : ℝ) ≤ Work.Peluse.uNormPow 1 Q (Work.Peluse.symIcc N) f := by
    simp only [Work.Peluse.uNormPow, Work.Peluse.boxNormPow]
    exact norm_nonneg _
  have hmain : (1 / 2 : ℝ) ^ (1 / 4 : ℝ) * Work.Peluse.uNorm 1 Q (Work.Peluse.symIcc N) f
      ≤ Work.Peluse.uNorm 2 Q (Work.Peluse.symIcc N) f := by
    have h1 : ((1 / 2 : ℝ) * (Work.Peluse.uNormPow 1 Q (Work.Peluse.symIcc N) f) ^ 2) ^ (1 / 4 : ℝ)
        = (1 / 2 : ℝ) ^ (1 / 4 : ℝ) * Work.Peluse.uNorm 1 Q (Work.Peluse.symIcc N) f := by
      rw [Real.mul_rpow (by norm_num) (pow_nonneg hUnn 2)]
      rw [Work.Peluse.uNorm]
      rw [← Real.rpow_natCast (Work.Peluse.uNormPow 1 Q (Work.Peluse.symIcc N) f) 2,
        ← Real.rpow_mul hUnn]
      congr 1
      norm_num
    have h2 : (Work.Peluse.uNormPow 2 Q (Work.Peluse.symIcc N) f) ^ (1 / 4 : ℝ)
        = Work.Peluse.uNorm 2 Q (Work.Peluse.symIcc N) f := by
      rw [Work.Peluse.uNorm]
      congr 1
      norm_num
    have haux : (1 / 2 : ℝ) * (Work.Peluse.uNormPow 1 Q (Work.Peluse.symIcc N) f) ^ 2
        ≤ Work.Peluse.uNormPow 2 Q (Work.Peluse.symIcc N) f := by
      have h := hraise
      norm_num at h
      exact h
    have h3 := Real.rpow_le_rpow
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (pow_nonneg hUnn 2)) haux
      (show (0 : ℝ) ≤ (1 / 4 : ℝ) by norm_num)
    rwa [h1, h2] at h3
  have h4 : (0 : ℝ) < (2 : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have h5 : (2 : ℝ) ^ (1 / 4 : ℝ) * ((1 / 2 : ℝ) ^ (1 / 4 : ℝ)
        * Work.Peluse.uNorm 1 Q (Work.Peluse.symIcc N) f)
      = Work.Peluse.uNorm 1 Q (Work.Peluse.symIcc N) f := by
    rw [← mul_assoc, ← Real.mul_rpow (by norm_num) (by norm_num)]
    norm_num
  calc Work.Peluse.uNorm 1 Q (Work.Peluse.symIcc N) f
      = (2 : ℝ) ^ (1 / 4 : ℝ) * ((1 / 2 : ℝ) ^ (1 / 4 : ℝ)
          * Work.Peluse.uNorm 1 Q (Work.Peluse.symIcc N) f) := h5.symm
    _ ≤ (2 : ℝ) ^ (1 / 4 : ℝ) * Work.Peluse.uNorm 2 Q (Work.Peluse.symIcc N) f :=
        mul_le_mul_of_nonneg_left hmain (le_of_lt h4)

/-! ## Helpers for the corrected assembly -/

/-- The ladder state is at most `1`: it is a weighted average of box-norm powers of a `1`-bounded
function supported in `symIcc N`. -/
lemma boxLadder_le_one (j n M₁ : ℕ) (c : ℤ) (ωOf : Fin (2 ^ j - 1) → (Fin j → Bool))
    (L D' N : ℕ) {f : ℤ → ℂ} (hM₁ : 1 ≤ M₁) (hsup : SupportIn f N)
    (hbd : ∀ x : ℤ, ‖f x‖ ≤ 1) :
    Holds.boxLadder j n M₁ c ωOf L D' N f ≤ 1 := by
  classical
  have hsupp : ∀ x : ℤ, x ∉ Work.Peluse.symIcc N → f x = 0 := by
    intro x hx
    refine hsup x ?_
    by_contra hcon
    apply hx
    rw [Work.Peluse.symIcc, Finset.mem_Icc]
    have hle : |x| ≤ (N : ℤ) := by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast (le_of_not_gt hcon)
    exact abs_le.mp hle
  have hterm : ∀ h h' : Fin j → Fin M₁,
      Work.Peluse.boxNormPow (2 ^ j - 1 + n) (Holds.ladderSlots j n M₁ c ωOf L D' h h')
          (Work.Peluse.symIcc N) f ≤ 1 := fun h h' =>
    Work.Peluse.BoxNorm.boxNormPow_le_one hbd hsupp
  have hsum : (∑ h : Fin j → Fin M₁, ∑ h' : Fin j → Fin M₁,
        Work.Peluse.boxNormPow (2 ^ j - 1 + n) (Holds.ladderSlots j n M₁ c ωOf L D' h h')
          (Work.Peluse.symIcc N) f) ≤ (M₁ : ℝ) ^ (2 * j) := by
    calc (∑ h : Fin j → Fin M₁, ∑ h' : Fin j → Fin M₁,
            Work.Peluse.boxNormPow (2 ^ j - 1 + n) (Holds.ladderSlots j n M₁ c ωOf L D' h h')
              (Work.Peluse.symIcc N) f)
        ≤ ∑ _h : Fin j → Fin M₁, ∑ _h' : Fin j → Fin M₁, (1 : ℝ) :=
          Finset.sum_le_sum fun h _ => Finset.sum_le_sum fun h' _ => hterm h h'
      _ = (M₁ : ℝ) ^ (2 * j) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
            nsmul_eq_mul]
          push_cast
          ring
  calc Holds.boxLadder j n M₁ c ωOf L D' N f
      = ((M₁ : ℝ))⁻¹ ^ (2 * j) * (∑ h : Fin j → Fin M₁, ∑ h' : Fin j → Fin M₁,
          Work.Peluse.boxNormPow (2 ^ j - 1 + n) (Holds.ladderSlots j n M₁ c ωOf L D' h h')
            (Work.Peluse.symIcc N) f) := rfl
    _ ≤ ((M₁ : ℝ))⁻¹ ^ (2 * j) * (M₁ : ℝ) ^ (2 * j) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ (by
          have : (0 : ℝ) < M₁ := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hM₁
          positivity), one_pow]

/-! ## The constant-factor one-step interface and the assembly (session 5)

The interface `ladderStepQ` is defined in `Submission/Work/Peluse/LadderB/stepDefsQ.lean`.  Its loss
is the **constant factor** `C·u`, which is the weakest form that still composes with the frozen
conditions re-established at every stage: with `x_{k+1} = C_k x_k` the running value is
`x_k = ladderCst s Cs (fun _ => 1) k · (C₁γ^K)`, so the stage-`k` non-degeneracy constant is
`C₁^{(k)} = ladderCst s Cs (fun _ => 1) k · C₁`, which is bounded *below* by its final value
`ladderCst s Cs (fun _ => 1) s · C₁` (the step constants are `≤ 1`).  The assembly therefore
chooses the target's existential constant `A` large enough once and for all. -/

/-- The level-raising estimate `uNorm n ≤ 2^{1/4}·uNorm (max n 2)` for `1 ≤ n`. -/
lemma uNorm_le_uNorm_max_two (n : ℕ) (hn : 1 ≤ n) {Q : Finset ℤ} {N : ℕ} {f : ℤ → ℂ}
    (hN : 0 < N) (hQ : Q.Nonempty) (hbd : ∀ x ∈ Q, |x| ≤ (N : ℤ)) (hsup : SupportIn f N)
    (hbd1 : ∀ x : ℤ, ‖f x‖ ≤ 1) :
    uNorm n Q (symIcc N) f ≤ (2 : ℝ) ^ (1 / 4 : ℝ) * uNorm (max n 2) Q (symIcc N) f := by
  by_cases h2 : 2 ≤ n
  · rw [max_eq_left h2]
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (1 / 4 : ℝ) := Real.one_le_rpow (by norm_num) (by norm_num)
    have h2' : 0 ≤ uNorm n Q (symIcc N) f := Concat.uNorm_nonneg _ _ _ _
    nlinarith
  · have h2' : n < 2 := lt_of_not_ge h2
    have hn1 : n = 1 := by omega
    rw [hn1, max_eq_right (by norm_num : (1:ℕ) ≤ 2)]
    exact uNorm_one_le_two hN hQ hbd hsup hbd1

/-- For `0 < y ≤ x` and `0 ≤ t` the negative power is antitone: `x^{-t} ≤ y^{-t}`. -/
lemma rpow_neg_antitone {x y : ℝ} (hy : 0 < y) (hyx : y ≤ x) {t : ℝ} (ht : 0 ≤ t) :
    x ^ (-t) ≤ y ^ (-t) := by
  have hx : 0 < x := lt_of_lt_of_le hy hyx
  rw [Real.rpow_neg hx.le, Real.rpow_neg hy.le]
  refine (inv_le_inv₀ (Real.rpow_pos_of_pos hx t) (Real.rpow_pos_of_pos hy t)).mpr ?_
  exact Real.rpow_le_rpow hy.le hyx ht

/-- The bottom of `boxLadderNorm`: at `j = 0` there are no short slots and all slots are the long
window `c[D']`, so the state is the uniformity norm at the level `n`. -/
lemma boxLadderNorm_zero (n M₁ : ℕ) (c : ℤ) (ωOf : Fin (2 ^ 0 - 1) → (Fin 0 → Bool))
    (L D' N : ℕ) (f : ℤ → ℂ) :
    boxLadderNorm 0 n M₁ c ωOf L D' N f = uNorm n (arithIcc c D') (symIcc N) f := by
  have hlev : 2 ^ 0 - 1 + n = n := by norm_num
  have hslots : ∀ h h' : Fin 0 → Fin M₁,
      Holds.ladderSlots 0 n M₁ c ωOf L D' h h'
        = fun _ : Fin (2 ^ 0 - 1 + n) => arithIcc c D' := by
    intro h h'
    funext i
    rw [Holds.ladderSlots, dif_neg (by simp)]
  unfold boxLadderNorm uNorm uNormPow boxNorm
  rw [Finset.sum_congr rfl (fun h _ => Finset.sum_congr rfl (fun h' _ => by
    rw [hslots h h', Holds.boxNormPow_cast hlev (fun _ => arithIcc c D') (symIcc N) f]))]
  simp

theorem concatBridgeShortA : Work.Peluse.C46.ConcatBridgeShortA := by sorry

end

end Work.Peluse
