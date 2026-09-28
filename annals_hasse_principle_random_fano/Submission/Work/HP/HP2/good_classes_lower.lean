import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.IntForm
import Submission.Work.HP.BridgeDefs
import Submission.Work.HP.HP2.primes_span_top

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.style.haveILetI false

namespace Work.HP.HP2

open Work.HP

/-- The canonical lift `b ↦ fun i => (b i).val` from `(ZMod W)^{n+1}` to `ℤ^{n+1}`
(`W ≠ 0`) is injective: `ZMod.val` is the representative in `[0,W)` and is injective. -/
lemma val_lift_injective (n W : ℕ) [NeZero W] :
    Function.Injective (fun b : Fin (n + 1) → ZMod W => fun i => ((b i).val : ℤ)) := by
  intro b c h
  funext i
  have h' : (b i).val = (c i).val := by
    have hh := congrFun h i
    simp only [] at hh
    omega
  rw [← ZMod.natCast_zmod_val (b i), ← ZMod.natCast_zmod_val (c i), h']

/-- `W` divides `formEval` at the canonical integer lift of `b` iff `formEval` vanishes at `b`
(as a class modulo `W`). -/
lemma dvd_formEval_lift (d n W : ℕ) [NeZero W] (a : Mon d n → ℤ)
    (b : Fin (n + 1) → ZMod W) :
    ((W : ℤ) ∣ formEval d n a (fun i => ((b i).val : ℤ))) ↔ formEval d n a b = 0 := by
  have hfun : (fun i => (((b i).val : ℤ) : ZMod W)) = b := by
    funext i
    rw [Int.cast_natCast]
    exact ZMod.natCast_zmod_val (b i)
  rw [formEval_dvd_iff, hfun]

/-- The number of elements of a finite type satisfying a decidable predicate, as the `ncard`
of the corresponding set. -/
lemma card_filter_eq_ncard {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card = ({b | P b} : Set α).ncard := by
  rw [← Set.ncard_coe_finset (Finset.univ.filter P)]
  congr 1
  ext b
  simp

/-- The residue classes mod `W` at which the form vanishes, counted over `ZMod W`, are exactly the
canonical integer lifts in the box `[0,W)^{n+1}` that are "primitive at every prime divisor of `W`".

Note `sigmaLoc d n a W * W^n` is by definition the cardinality of
`{b : Fin (n+1) → ZMod W | Ideal.span (Set.range b) = ⊤ ∧ formEval d n a b = 0}`
(`sigmaLoc d n a Q = (that ncard : ℝ) / Q^n`), so the conclusion below is an equality of counts.

Route.  The canonical lift `b ↦ fun i => (b i).val` is injective and lands in the box.
`ZMod.natCast_zmod_val : ((b i).val : ZMod W) = b i`, so `0 ≤ (b i).val < W`; and by
`formEval_intCast_zmod` in `Submission.Work.HP.IntForm`, `formEval d n a b = 0` at a class `b`
implies `(W : ℤ) ∣ formEval d n a (fun i => (b i).val)` — use
`((formEval a y : ℤ) : ZMod W) = formEval a (fun i => (y i : ZMod W))`.
Unimodularity: `Ideal.span (Set.range b) = ⊤` gives `Σ r_i b_i = 1` over `ZMod W`; lifting the `r_i`
to integers and reducing mod `W` shows `gcd(W, (b i).val) ∣ 1`, so for every prime `p ∣ W` some
`i` has `p ∤ (b i).val` (if `p` divided all `(b i).val` then `p · ZMod W` would contain `1`). -/
theorem good_classes_lower (d n : ℕ) (W : ℕ) (hW : 0 < W) (a : Mon d n → ℤ) :
    ∃ G : Finset (Fin (n + 1) → ℤ),
      (∀ b ∈ G, (∀ i, 0 ≤ b i ∧ b i < W) ∧
        (∀ p : ℕ, p.Prime → p ∣ W → ∃ i, ¬ (p : ℤ) ∣ b i) ∧
        (W : ℤ) ∣ formEval d n a b) ∧
      (G.card : ℝ) = sigmaLoc d n a W * (W : ℝ) ^ n := by
  classical
  haveI hWnz : NeZero W := ⟨hW.ne'⟩
  refine ⟨(Finset.univ.filter (fun b : Fin (n + 1) → ZMod W =>
      Ideal.span (Set.range b) = ⊤ ∧ formEval d n a b = 0)).image
        (fun b => fun i => ((b i).val : ℤ)), ?_, ?_⟩
  · intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨b, hb, rfl⟩ := hy
    rw [Finset.mem_filter] at hb
    obtain ⟨-, hspan, hform⟩ := hb
    refine ⟨?_, ?_, ?_⟩
    · intro i
      have hb1 : (0 : ℤ) ≤ ((b i).val : ℤ) := Int.natCast_nonneg _
      have hb2 : ((b i).val : ℤ) < (W : ℤ) := by exact_mod_cast ZMod.val_lt (b i)
      exact ⟨hb1, hb2⟩
    · intro p hp hpW
      exact primes_span_top n W b hspan p hp hpW
    · exact (dvd_formEval_lift d n W a b).mpr hform
  · rw [Finset.card_image_of_injective _ (val_lift_injective n W)]
    rw [card_filter_eq_ncard]
    unfold sigmaLoc
    rw [div_mul_cancel₀ _ (pow_ne_zero _ (by exact_mod_cast hW.ne'))]

end Work.HP.HP2
