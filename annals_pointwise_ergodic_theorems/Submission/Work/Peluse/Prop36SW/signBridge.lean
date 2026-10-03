import Mathlib
import Submission.Work.Peluse.Prop36SW.GenDefs
import Submission.Work.Peluse.ladderA_defs

/-!
# The sign bridge: the family hypothesis is invariant under `p ↦ |p|`

`Work.Peluse.C46.PeluseLadderA` (Peluse's Lemma 5.7) demands that the coefficient functions
`p i a` be **strictly positive** on the parameter set `A` (`(∀ i a, a ∈ A → 0 < p i a)`), because the
peeled parameter is averaged over the half box `[1,M₂]` in the concatenation theorem, and the
positive coefficient is what turns that into the symmetric average over the peeled coordinate
(see `Submission/Work/Peluse/ladderA_main.lean`, `hppos`).

The natural coefficient function of Peluse's chain is however
`q_j s a = Λ_j (d-j+1) · dir (d,lc P) (j-1) (par (j-1) s) a`, and `dir` is a multilinear polynomial
with **positive** integer coefficients whose sign therefore varies over the box: `q_j` is *not*
positive, so the ladder cannot be applied to `(q_j)` as it stands.  (For `d = 2` and the top level
`j = d-1` this is invisible — there `q_{d-1} s a = 2·dir (d-2) (·) a` is linear in the level-`(d-2)`
parameters — but at level `2` it already fails.)

This module supplies the reconciliation.  For a *fixed* outer parameter `a`, the parameter box
`paramBox (k := fun _ : ι => 1) M₂ = ∏_{s} Ioo (-M₂) M₂` is symmetric, so the per-slot sign
substitution `a'_s ↦ ε_s · a'_s` with `ε_s = ±1` is a bijection of it onto itself, and converts

`ω ↦ arithIcc (∑_{s ∈ ω} p s a · a'_s) M₁`  into  `ω ↦ arithIcc (∑_{s ∈ ω} (ε_s p s a) · a'_s) M₁`.

Taking `ε_s = intSign (p s a)` (so `ε_s p s a = |p s a|`) gives: **the box average of any function
of the direction family is unchanged when `p` is replaced by `|p|`**
(`sum_paramBox_pDirFamG_abs`).  Hence a state hypothesis stated with the *signed* coefficient
function is *equivalent* to the same hypothesis stated with the positive `|p|` — and the latter is
what the ladder consumes.

The price is paid at the *conclusion*: the ladder's conclusion with `|p|` has long directions
`arithIcc (|p s₀ a|) L'`, while the chain needs `arithIcc (p s₀ a) L'`; the two differ by the
reflection `Q ↦ -Q` of the direction sets, which
`Work.Peluse.Pairing.boxSumPow_neg_directions` converts into the reflection `f ↦ f ∘ neg` of the
function.  That bookkeeping is carried by the round (`NOTES_prop36SW_of_ladderA_SESSION5.md`).
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.Prop36SW

noncomputable section

open Work.Peluse.UControl

/-! ## Signs -/

/-- The sign of an integer, as an element of `{1, -1}` (with `intSign 0 = 1`). -/
def intSign (q : ℤ) : ℤ := if q < 0 then -1 else 1

lemma intSign_mul_self (q : ℤ) : intSign q * q = |q| := by
  unfold intSign
  split_ifs with h
  · rw [abs_of_neg h]; ring
  · rw [abs_of_nonneg (not_lt.mp h)]; ring

lemma intSign_sq (q : ℤ) : intSign q * intSign q = 1 := by
  unfold intSign
  split_ifs <;> norm_num

lemma intSign_eq_one_or_neg_one (q : ℤ) : intSign q = 1 ∨ intSign q = -1 := by
  unfold intSign
  split_ifs <;> [right; left] <;> rfl

/-- Multiplication by `±1` preserves the symmetric box `Ioo (-M) M`. -/
lemma mul_pm_one_mem_Ioo {ε y : ℤ} (hε : ε = 1 ∨ ε = -1) (M : ℕ) :
    ε * y ∈ Finset.Ioo (-(M : ℤ)) (M : ℤ) ↔ y ∈ Finset.Ioo (-(M : ℤ)) (M : ℤ) := by
  rcases hε with rfl | rfl
  · simp
  · simp only [Finset.mem_Ioo, neg_mul]; omega

/-! ## The sign substitution on the parameter box -/

/-- The per-slot sign substitution `b ↦ (k ↦ ε_{k.1} · b k)` on the slot parameters. -/
def signSubst {ι : Type} (ε : ι → ℤ) (b : Slot ι (fun _ => 1) → ℤ) : Slot ι (fun _ => 1) → ℤ :=
  fun k => ε k.1 * b k

lemma signSubst_invol {ι : Type} (ε : ι → ℤ) (hε : ∀ i, ε i * ε i = 1)
    (b : Slot ι (fun _ => 1) → ℤ) : signSubst ε (signSubst ε b) = b := by
  funext k
  simp only [signSubst]
  rw [← mul_assoc, hε k.1, one_mul]

lemma signSubst_mem_paramBox {ι : Type} [Fintype ι] [DecidableEq ι] (ε : ι → ℤ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) (M : ℕ) (b : Slot ι (fun _ => 1) → ℤ) :
    signSubst ε b ∈ paramBox (k := fun _ : ι => 1) M ↔ b ∈ paramBox (k := fun _ : ι => 1) M := by
  simp only [paramBox, Fintype.mem_piFinset, signSubst]
  exact forall_congr' fun k => mul_pm_one_mem_Ioo (hε k.1) M

/-! ## The direction family under the sign substitution -/

/-- The direction set `pDirG` is the same whether the coefficient is read at `p` and the parameters
at `signSubst ε b`, or at `ε · p` and the parameters at `b`. -/
lemma pDirG_signSubst {ι : Type} {P : Type} (p : ι → P → ℤ) (M₁ : ℕ) (a : P) (ε : ι → ℤ)
    (b : Slot ι (fun _ => 1) → ℤ) (ω : SlotSet ι (fun _ => 1)) :
    pDirG p M₁ a (signSubst ε b) ω = pDirG (fun s _ => ε s * p s a) M₁ a b ω := by
  simp only [pDirG, signSubst]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

lemma pDirFamG_signSubst {ι : Type} {P : Type} (p : ι → P → ℤ) (M₁ : ℕ) (a : P) (ε : ι → ℤ)
    (b : Slot ι (fun _ => 1) → ℤ) (kω : SlotSet ι (fun _ => 1) → ℕ) :
    pDirFamG (kω := kω) p M₁ a (signSubst ε b)
      = pDirFamG (kω := kω) (fun s _ => ε s * p s a) M₁ a b := by
  funext j
  exact congrArg (fun F => F j.1) (funext fun ω => pDirG_signSubst p M₁ a ε b ω)

/-! ## The box average is invariant -/

/-- **The sign bridge.**  For a slotwise sign pattern `ε` (`ε_s = ±1`), the box average of any
function of the direction family is unchanged under replacing `p s a` by `ε_s · p s a`. -/
theorem sum_paramBox_pDirFamG_mul {ι : Type} [Fintype ι] [DecidableEq ι] {P : Type}
    (kω : SlotSet ι (fun _ => 1) → ℕ) (p : ι → P → ℤ) (M₁ M₂ : ℕ) (a : P) (ε : ι → ℤ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (Φ : (Fin (Fintype.card (FamIdx kω)) → Finset ℤ) → ℝ) :
    (∑ b ∈ paramBox (k := fun _ : ι => 1) M₂,
        Φ (fun j => pDirFamG (kω := kω) p M₁ a b
          ((Fintype.equivFin (FamIdx kω)).symm j)))
      = ∑ b ∈ paramBox (k := fun _ : ι => 1) M₂,
        Φ (fun j => pDirFamG (kω := kω) (fun s _ => ε s * p s a) M₁ a b
          ((Fintype.equivFin (FamIdx kω)).symm j)) := by
  classical
  have hsq : ∀ i, ε i * ε i = 1 := by
    intro i
    rcases hε i with h | h <;> rw [h] <;> norm_num
  have hbij : ∀ b ∈ paramBox (k := fun _ : ι => 1) M₂,
      signSubst ε b ∈ paramBox (k := fun _ : ι => 1) M₂ :=
    fun b hb => (signSubst_mem_paramBox ε hε M₂ b).mpr hb
  have hleft : ∀ b ∈ paramBox (k := fun _ : ι => 1) M₂,
      signSubst ε (signSubst ε b) = b := fun b _ => signSubst_invol ε hsq b
  have h1 : (∑ b ∈ paramBox (k := fun _ : ι => 1) M₂,
        Φ (fun j => pDirFamG (kω := kω) p M₁ a b
          ((Fintype.equivFin (FamIdx kω)).symm j)))
      = ∑ b ∈ paramBox (k := fun _ : ι => 1) M₂,
        Φ (fun j => pDirFamG (kω := kω) p M₁ a (signSubst ε b)
          ((Fintype.equivFin (FamIdx kω)).symm j)) := by
    refine Finset.sum_bij' (fun b _ => signSubst ε b) (fun b _ => signSubst ε b)
      hbij hbij hleft hleft ?_
    intro b hb
    rw [hleft b hb]
  have h2 : (∑ b ∈ paramBox (k := fun _ : ι => 1) M₂,
        Φ (fun j => pDirFamG (kω := kω) p M₁ a (signSubst ε b)
          ((Fintype.equivFin (FamIdx kω)).symm j)))
      = ∑ b ∈ paramBox (k := fun _ : ι => 1) M₂,
        Φ (fun j => pDirFamG (kω := kω) (fun s _ => ε s * p s a) M₁ a b
          ((Fintype.equivFin (FamIdx kω)).symm j)) := by
    refine Finset.sum_congr rfl fun b _ => ?_
    congr 1
    exact funext fun j => congrArg (fun F => F ((Fintype.equivFin (FamIdx kω)).symm j))
      (pDirFamG_signSubst p M₁ a ε b kω)
  rw [h1, h2]

/-- **The sign bridge for the absolute value.**  The box average of any function of the direction
family is unchanged when the coefficient function `p` is replaced by `|p|` slotwise. -/
theorem sum_paramBox_pDirFamG_abs {ι : Type} [Fintype ι] [DecidableEq ι] {P : Type}
    (kω : SlotSet ι (fun _ => 1) → ℕ) (p : ι → P → ℤ) (M₁ M₂ : ℕ) (a : P)
    (Φ : (Fin (Fintype.card (FamIdx kω)) → Finset ℤ) → ℝ) :
    (∑ b ∈ paramBox (k := fun _ : ι => 1) M₂,
        Φ (fun j => pDirFamG (kω := kω) p M₁ a b
          ((Fintype.equivFin (FamIdx kω)).symm j)))
      = ∑ b ∈ paramBox (k := fun _ : ι => 1) M₂,
        Φ (fun j => pDirFamG (kω := kω) (fun s _ => |p s a|) M₁ a b
          ((Fintype.equivFin (FamIdx kω)).symm j)) := by
  have hcoe : (fun s (_ : P) => intSign (p s a) * p s a) = fun s (_ : P) => |p s a| := by
    funext s _
    exact intSign_mul_self (p s a)
  rw [← hcoe]
  exact sum_paramBox_pDirFamG_mul kω p M₁ M₂ a (fun i => intSign (p i a))
    (fun i => intSign_eq_one_or_neg_one (p i a)) Φ

/-- **The sign bridge in the form the chain consumes**: the box average of the box-norm powers. -/
theorem sum_paramBox_boxNormPow_abs {ι : Type} [Fintype ι] [DecidableEq ι] {P : Type}
    (kω : SlotSet ι (fun _ => 1) → ℕ) (p : ι → P → ℤ) (M₁ M₂ : ℕ) (a : P)
    (S : Finset ℤ) (f : ℤ → ℂ) :
    (∑ b ∈ paramBox (k := fun _ : ι => 1) M₂,
        Work.Peluse.boxNormPow (Fintype.card (FamIdx kω))
          (fun j => pDirFamG (kω := kω) p M₁ a b ((Fintype.equivFin (FamIdx kω)).symm j))
          S f)
      = ∑ b ∈ paramBox (k := fun _ : ι => 1) M₂,
        Work.Peluse.boxNormPow (Fintype.card (FamIdx kω))
          (fun j => pDirFamG (kω := kω) (fun s _ => |p s a|) M₁ a b
            ((Fintype.equivFin (FamIdx kω)).symm j)) S f :=
  sum_paramBox_pDirFamG_abs kω p M₁ M₂ a
    (fun F => Work.Peluse.boxNormPow (Fintype.card (FamIdx kω)) F S f)

/-- **The sign bridge for `boxNorm`** (the level-normalised form in which `LState`'s hypothesis is
stated). -/
theorem sum_paramBox_boxNorm_abs {ι : Type} [Fintype ι] [DecidableEq ι] {P : Type}
    (kω : SlotSet ι (fun _ => 1) → ℕ) (p : ι → P → ℤ) (M₁ M₂ : ℕ) (a : P)
    (S : Finset ℤ) (f : ℤ → ℂ) :
    (∑ b ∈ paramBox (k := fun _ : ι => 1) M₂,
        Work.Peluse.boxNorm (Fintype.card (FamIdx kω))
          (fun j => pDirFamG (kω := kω) p M₁ a b ((Fintype.equivFin (FamIdx kω)).symm j))
          S f)
      = ∑ b ∈ paramBox (k := fun _ : ι => 1) M₂,
        Work.Peluse.boxNorm (Fintype.card (FamIdx kω))
          (fun j => pDirFamG (kω := kω) (fun s _ => |p s a|) M₁ a b
            ((Fintype.equivFin (FamIdx kω)).symm j)) S f :=
  sum_paramBox_pDirFamG_abs kω p M₁ M₂ a
    (fun F => Work.Peluse.boxNorm (Fintype.card (FamIdx kω)) F S f)

/-- **The sign bridge at the `LState` hypothesis level**: the average over the outer parameter set
`A` and the box `paramBox M₂` of the level-`card (FamIdx kω)` box norm is unchanged when the
coefficient function is replaced by `|p|`.  This is the form in which `LState`'s hypothesis is
stated, and it is what lets the chain carry the *signed* slot coefficients while applying
`PeluseLadderA` (whose hypothesis demands positivity) to `|p|`. -/
theorem sum_LState_hyp_abs {ι : Type} [Fintype ι] [DecidableEq ι] {P : Type}
    (kω : SlotSet ι (fun _ => 1) → ℕ) (p : ι → P → ℤ) (M₁ M₂ N : ℕ) (A : Finset P)
    (g : P → ℤ → ℂ) :
    (∑ a ∈ A, ∑ a' ∈ paramBox (k := fun _ : ι => 1) M₂,
        Work.Peluse.boxNorm (Fintype.card (FamIdx kω))
          (fun j => pDirFamG (kω := kω) p M₁ a a'
            ((Fintype.equivFin (FamIdx kω)).symm j)) (Work.Peluse.symIcc N) (g a))
      = ∑ a ∈ A, ∑ a' ∈ paramBox (k := fun _ : ι => 1) M₂,
        Work.Peluse.boxNorm (Fintype.card (FamIdx kω))
          (fun j => pDirFamG (kω := kω) (fun s _ => |p s a|) M₁ a a'
            ((Fintype.equivFin (FamIdx kω)).symm j)) (Work.Peluse.symIcc N) (g a) :=
  Finset.sum_congr rfl fun a _ =>
    sum_paramBox_boxNorm_abs kω p M₁ M₂ a (Work.Peluse.symIcc N) (g a)

end

end Work.Peluse.Prop36SW
