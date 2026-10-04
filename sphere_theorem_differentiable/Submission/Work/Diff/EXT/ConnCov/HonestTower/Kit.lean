import Mathlib
import Submission.Work.Diff.EXT.ConnCov.honestTower
import Submission.Work.Diff.EXT.ATens.Defs
import Submission.Work.Diff.T.lc_smooth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Kit for the *boundedness* of the honest tower (compactness route)

## What this module is for

The target `Work.Diff.EXT.ConnCov.honest_tower_twoConn` bounds the `m`-th covariant derivative of a
base operator `base` (an `Op3 0` which *ignores* its third value slot, `CIndep base`) with respect
to the connection `∇^{g₀} = lcOf g₀`, in terms of the `g₁`-norm products.

The route followed here is the **compactness route**: the honest tower is a smooth tensor field on
the compact manifold `M`, so its operator norm is bounded; the constant of the statement may
therefore be taken arbitrarily large.  Concretely, for every `m` we produce a constant `B m` with

  `|gP g₀ base m (pack2 v A B) x| ≤ B m · ∏ᵢ √⟨vᵢ,vᵢ⟩ · √⟨A,A⟩ · √⟨B,B⟩`

independent of `x, v, A, B` (and *not* depending on the data `D, E, R` of the statement at all;
`Ck := (max_{m ≤ k} B m) / S` with `S = 1 + ΣD + ΣE + ΣR ≥ 1` then finishes).

## The packed honest tower

Since `base` is `CIndep`, `htower (lcOf g) base k` does not depend on the field in its third value
slot (`cIndep_htower`), so that slot may be set to the zero field.  The recursion then becomes

  `gP (k+1) F y = mvfderiv (gP k (F_{≥1})) y (F 0 y)
     - ∑_{s : Fin (k+2)} gP k (update F_{≥1} s (∇_{F 0} (F_{s+1}))) y`

for `F : Fin (k+3) → TF` (the first `k+1` entries are the differentiation slots, the last two the
value slots).  This is exactly the shape of the recursion of `Work.Diff.EXT.ckt`
(`Submission/Work/Diff/EXT/curvNormK_frame_indep.lean`) and of `Work.Diff.EXT.cktA`
(`Submission/Work/Diff/EXT/ATens/`), with arity `k + 2` (two value slots instead of three or four)
and an arbitrary base.

## Contents

* `gP`, `gP_succ` — the packed honest tower and its recursion;
* `pack2`, `pairF` and the `Fin` bookkeeping;
* `TensPropG` — the induction invariant (smoothness, slotwise linearity, locality);
* `tensPropG_zero` — the base case, from the hypotheses on `base`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Commons.Geometry.Manifold.VectorField

namespace Work.Diff.EXT.ConnCov.HonestTower

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-- Tangent fields on `M`. -/
abbrev Tf : Type _ := Π y : M, TangentSpace I y

/-- Smooth tangent fields on `M`. -/
abbrev Sm (X : Tf (I := I) (M := M)) : Prop := CMDiff ∞ (T% X)

/-- The zero tangent field is smooth. -/
theorem sm_zeroField : Sm (I := I) (M := M) (0 : Tf (I := I) (M := M)) :=
  contMDiff_zeroSection ℝ (TangentSpace I (M := M))

/-! ## The packed recursion -/

/-- **The packed honest tower.**  `gP g base k F` is the `k`-th covariant derivative of `base`
(with its third value slot set to `0`) with respect to the Levi-Civita connection of `g`, evaluated
on the `k + 2` fields of `F`: the first `k` entries are the differentiation slots, the last two the
value slots.  The bridge to the honest tower is `gP_eq_htower`. -/
noncomputable def gP (g : Submission.Diff.SMet I M)
    (base : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) 0) :
    ∀ k : ℕ, (Fin (k + 2) → Tf (I := I) (M := M)) → M → ℝ
  | 0, F => fun y =>
      base (fun i : Fin 0 => i.elim0) (F 0) (F 1) (0 : Tf (I := I) (M := M)) y
  | k + 1, F => fun y =>
      mvfderiv I (gP g base k (fun i : Fin (k + 2) => F i.succ)) y (F 0 y)
        - ∑ s : Fin (k + 2), gP g base k (Function.update (fun i : Fin (k + 2) => F i.succ) s
            (Work.Diff.EXT.dirFA g ((fun i : Fin (k + 2) => F i.succ) s) (F 0))) y

/-- Level `0` of the recursion. -/
theorem gP_zero (g : Submission.Diff.SMet I M)
    (base : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) 0)
    (F : Fin 2 → Tf (I := I) (M := M)) :
    gP g base 0 F
      = fun y => base (fun i : Fin 0 => i.elim0) (F 0) (F 1)
          (0 : Tf (I := I) (M := M)) y := rfl

/-- Level `0` of the recursion, pointwise. -/
theorem gP_zero_apply (g : Submission.Diff.SMet I M)
    (base : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) 0)
    (F : Fin 2 → Tf (I := I) (M := M)) (y : M) :
    gP g base 0 F y
      = base (fun i : Fin 0 => i.elim0) (F 0) (F 1) (0 : Tf (I := I) (M := M)) y :=
  congrFun (gP_zero g base F) y

/-- The recursion, as an equality of functions. -/
theorem gP_succ (g : Submission.Diff.SMet I M)
    (base : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) 0) (k : ℕ)
    (F : Fin (k + 3) → Tf (I := I) (M := M)) :
    gP g base (k + 1) F
      = (fun y : M => (mvfderiv I (gP g base k (fun i : Fin (k + 2) => F i.succ)) y) (F 0 y))
        - ∑ s : Fin (k + 2), gP g base k (Function.update (fun i : Fin (k + 2) => F i.succ) s
            (Work.Diff.EXT.dirFA g ((fun i : Fin (k + 2) => F i.succ) s) (F 0))) := by
  funext y
  simp only [gP, Finset.sum_apply, Pi.sub_apply]

/-! ## The packing of `k` directions together with the two value slots -/

/-- The two value slots, as a `Fin 2`-tuple. -/
def pairF (A B : Tf (I := I) (M := M)) : Fin 2 → Tf (I := I) (M := M) :=
  fun p => if (p : ℕ) = 0 then A else B

@[simp] lemma pairF_zero (A B : Tf (I := I) (M := M)) : pairF A B 0 = A := by
  simp [pairF]

@[simp] lemma pairF_one (A B : Tf (I := I) (M := M)) : pairF A B 1 = B := by
  simp [pairF]

/-- Assemble a `Fin (k+2)`-tuple of fields from a `k`-tuple of differentiation slots together with
the two value slots `A B`. -/
def pack2 {k : ℕ} (v : Fin k → Tf (I := I) (M := M)) (A B : Tf (I := I) (M := M)) :
    Fin (k + 2) → Tf (I := I) (M := M) :=
  Fin.addCases (motive := fun _ => Tf (I := I) (M := M)) (fun i => v i) (pairF A B)

lemma pack2_castAdd {k : ℕ} (v : Fin k → Tf (I := I) (M := M)) (A B : Tf (I := I) (M := M))
    (i : Fin k) : pack2 v A B (Fin.castAdd 2 i) = v i := Fin.addCases_left i

lemma pack2_natAdd {k : ℕ} (v : Fin k → Tf (I := I) (M := M)) (A B : Tf (I := I) (M := M))
    (p : Fin 2) : pack2 v A B (Fin.natAdd k p) = pairF A B p := Fin.addCases_right p

lemma succ_castAdd_two {k : ℕ} (i : Fin k) :
    (Fin.castAdd 2 i).succ = Fin.castAdd 2 i.succ := by
  ext; simp

lemma succ_natAdd_two {k : ℕ} (p : Fin 2) :
    (Fin.natAdd k p).succ = Fin.natAdd (k + 1) p := by
  ext
  simp only [Fin.val_succ, Fin.val_natAdd]
  omega

lemma natAdd_ne_castAdd_two {k : ℕ} (p : Fin 2) (i : Fin k) :
    Fin.natAdd k p ≠ Fin.castAdd 2 i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
  omega

lemma update_castAdd_pack2 {k : ℕ} (v : Fin k → Tf (I := I) (M := M))
    (A B : Tf (I := I) (M := M)) (i : Fin k) (X : Tf (I := I) (M := M)) :
    Function.update (pack2 v A B) (Fin.castAdd 2 i) X = pack2 (Function.update v i X) A B := by
  funext s
  refine Fin.addCases ?_ ?_ s
  · intro j
    rw [pack2_castAdd (Function.update v i X) A B j]
    rcases eq_or_ne j i with h | h
    · subst h; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne (fun hh => h (Fin.castAdd_inj.mp hh)) X (pack2 v A B),
        Function.update_of_ne h X v, pack2_castAdd]
  · intro p
    rw [pack2_natAdd (Function.update v i X) A B p,
      Function.update_of_ne (natAdd_ne_castAdd_two p i) X (pack2 v A B), pack2_natAdd]

lemma update_natAdd_pack2 {k : ℕ} (v : Fin k → Tf (I := I) (M := M))
    (A B X : Tf (I := I) (M := M)) (p : Fin 2) :
    Function.update (pack2 v A B) (Fin.natAdd k p) X
      = pack2 v (if p = 0 then X else A) (if p = 1 then X else B) := by
  funext s
  refine Fin.addCases ?_ ?_ s
  · intro i
    rw [pack2_castAdd, Function.update_of_ne (Ne.symm (natAdd_ne_castAdd_two p i)) X (pack2 v A B),
      pack2_castAdd]
  · intro q
    have hpq : (Fin.natAdd k q = Fin.natAdd k p) ↔ q = p := Fin.natAdd_inj k
    rw [Function.update_apply, pack2_natAdd, pack2_natAdd]
    by_cases h : q = p
    · rw [if_pos (hpq.mpr h), ← h]
      fin_cases q <;> simp
    · rw [if_neg (fun hh => h (hpq.mp hh))]
      fin_cases q <;> fin_cases p <;> simp_all

lemma pack2_comp_succ {k : ℕ} (v : Fin (k + 1) → Tf (I := I) (M := M))
    (A B : Tf (I := I) (M := M)) :
    (fun i : Fin (k + 2) => pack2 v A B i.succ) = pack2 (fun i : Fin k => v i.succ) A B := by
  funext s
  refine Fin.addCases ?_ ?_ s
  · intro i
    rw [pack2_castAdd (fun i : Fin k => v i.succ) A B i, succ_castAdd_two, pack2_castAdd]
  · intro p
    rw [pack2_natAdd (fun i : Fin k => v i.succ) A B p, succ_natAdd_two, pack2_natAdd]

/-! ## `Fin.cons` bookkeeping for the induction steps -/

lemma update_zero_eq_consG {k : ℕ} (F : Fin (k + 3) → Tf (I := I) (M := M))
    (W : Tf (I := I) (M := M)) :
    Function.update F 0 W = (Fin.cons W (fun i : Fin (k + 2) => F i.succ) : Fin (k + 3) → Tf) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rw [Fin.cons_zero (α := fun _ : Fin (k + 3) => Tf (I := I) (M := M)), Function.update_self]
  · intro j
    rw [Fin.cons_succ (α := fun _ : Fin (k + 3) => Tf (I := I) (M := M)),
      Function.update_of_ne (Fin.succ_ne_zero j) W F]

lemma update_succ_eq_consG {k : ℕ} (F : Fin (k + 3) → Tf (I := I) (M := M)) (j : Fin (k + 2))
    (W : Tf (I := I) (M := M)) :
    Function.update F j.succ W
      = (Fin.cons (F 0) (Function.update (fun i : Fin (k + 2) => F i.succ) j W)
          : Fin (k + 3) → Tf) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rw [Fin.cons_zero (α := fun _ : Fin (k + 3) => Tf (I := I) (M := M)),
      Function.update_of_ne (Ne.symm (Fin.succ_ne_zero j)) W F]
  · intro j'
    rw [Fin.cons_succ (α := fun _ : Fin (k + 3) => Tf (I := I) (M := M))]
    rcases eq_or_ne j' j with h | h
    · subst h; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne (fun hh => h (Fin.succ_inj.mp hh)), Function.update_of_ne h]

lemma sm_update {k : ℕ} {F : Fin k → Tf (I := I) (M := M)} (hF : ∀ i, Sm (I := I) (M := M) (F i))
    {j : Fin k} {W : Tf (I := I) (M := M)} (hW : Sm (I := I) (M := M) W) :
    ∀ q, Sm (I := I) (M := M) ((Function.update F j W) q) := by
  intro q
  rcases eq_or_ne q j with h | h
  · subst h; rw [Function.update_self]; exact hW
  · rw [Function.update_of_ne h]; exact hF q

/-! ## The induction invariant -/

/-- **The induction invariant of the packed honest tower.**  For every tuple of smooth fields, the
packed tower is smooth, `C^∞`-linear in each of its `k + 2` slots, and local. -/
def TensPropG (g : Submission.Diff.SMet I M)
    (base : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) 0) (k : ℕ) : Prop :=
  ∀ F : Fin (k + 2) → Tf (I := I) (M := M),
    (∀ s, Sm (I := I) (M := M) (F s)) →
    CMDiff ∞ (fun y : M => gP g base k F y) ∧
    (∀ (s : Fin (k + 2)) (X₁ X₂ : Tf (I := I) (M := M)) (f₁ f₂ : M → ℝ),
      Sm (I := I) (M := M) X₁ → Sm (I := I) (M := M) X₂ → CMDiff ∞ f₁ → CMDiff ∞ f₂ →
      gP g base k (Function.update F s (f₁ • X₁ + f₂ • X₂))
        = f₁ • gP g base k (Function.update F s X₁) + f₂ • gP g base k (Function.update F s X₂)) ∧
    (∀ (x : M) (F' : Fin (k + 2) → Tf (I := I) (M := M)),
      (∀ s, Sm (I := I) (M := M) (F' s)) →
      (∀ s, F s =ᶠ[𝓝 x] F' s) → gP g base k F =ᶠ[𝓝 x] gP g base k F')

/-! ## The base case -/

/-- **The base case of the invariant**, from the hypotheses on `base`: smoothness, `C^∞`-linearity
in the two value slots, and value-dependence. -/
theorem tensPropG_zero (g : Submission.Diff.SMet I M)
    {base : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) 0}
    (hsm : ∀ (v : Fin 0 → Tf (I := I) (M := M)) (A B C : Tf (I := I) (M := M)),
      Sm (I := I) (M := M) A → Sm (I := I) (M := M) B → Sm (I := I) (M := M) C →
      CMDiff ∞ (base v A B C))
    (hlinA : ∀ (b0 : Fin 0 → Tf (I := I) (M := M)) (X₁ X₂ : Tf (I := I) (M := M))
      (f₁ f₂ : M → ℝ),
      CMDiff ∞ f₁ → CMDiff ∞ f₂ → Sm (I := I) (M := M) X₁ → Sm (I := I) (M := M) X₂ →
      ∀ (B C : Tf (I := I) (M := M)) (x : M),
      base b0 (f₁ • X₁ + f₂ • X₂) B C x
        = f₁ x * base b0 X₁ B C x + f₂ x * base b0 X₂ B C x)
    (hlinB : ∀ (b0 : Fin 0 → Tf (I := I) (M := M)) (X₁ X₂ : Tf (I := I) (M := M))
      (f₁ f₂ : M → ℝ),
      CMDiff ∞ f₁ → CMDiff ∞ f₂ → Sm (I := I) (M := M) X₁ → Sm (I := I) (M := M) X₂ →
      ∀ (A C : Tf (I := I) (M := M)) (x : M),
      base b0 A (f₁ • X₁ + f₂ • X₂) C x
        = f₁ x * base b0 A X₁ C x + f₂ x * base b0 A X₂ C x)
    (hvd : ∀ (b0 : Fin 0 → Tf (I := I) (M := M))
      (A A' B B' C C' : Tf (I := I) (M := M)) (x : M),
      Sm (I := I) (M := M) A → Sm (I := I) (M := M) A' →
      Sm (I := I) (M := M) B → Sm (I := I) (M := M) B' →
      Sm (I := I) (M := M) C → Sm (I := I) (M := M) C' →
      A x = A' x → B x = B' x → C x = C' x →
      base b0 A B C x = base b0 A' B' C' x) :
    TensPropG (I := I) (M := M) g base 0 := by
  intro F hF
  refine ⟨?_, ?_, ?_⟩
  · rw [gP_zero]
    exact hsm (fun i : Fin 0 => i.elim0) (F 0) (F 1) (0 : Tf (I := I) (M := M))
      (hF 0) (hF 1) sm_zeroField
  · intro s X₁ X₂ f₁ f₂ hX₁ hX₂ hf₁ hf₂
    fin_cases s
    · funext y
      simp only [Pi.add_apply, Pi.smul_apply', smul_eq_mul, Function.update_self,
        Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0), gP_zero_apply]
      exact hlinA (fun i : Fin 0 => i.elim0) X₁ X₂ f₁ f₂ hf₁ hf₂ hX₁ hX₂
        (F 1) (0 : Tf (I := I) (M := M)) y
    · funext y
      simp only [Pi.add_apply, Pi.smul_apply', smul_eq_mul, Function.update_self,
        Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1), gP_zero_apply]
      exact hlinB (fun i : Fin 0 => i.elim0) X₁ X₂ f₁ f₂ hf₁ hf₂ hX₁ hX₂
        (F 0) (0 : Tf (I := I) (M := M)) y
  · intro x F' hF' h
    obtain ⟨U, hU, hUU⟩ := (h 0).exists_mem
    obtain ⟨V, hV, hVV⟩ := (h 1).exists_mem
    refine (Filter.eventuallyEq_iff_exists_mem).mpr ⟨U ∩ V, Filter.inter_mem hU hV, fun y hy => ?_⟩
    rw [gP_zero_apply, gP_zero_apply]
    exact hvd _ _ _ _ _ _ _ y (hF 0) (hF' 0) (hF 1) (hF' 1) sm_zeroField sm_zeroField
      (hUU hy.1) (hVV hy.2) rfl

end Work.Diff.EXT.ConnCov.HonestTower
