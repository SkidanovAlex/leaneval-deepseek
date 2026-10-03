import Mathlib
import Submission.Work.Peluse.Prop36SW.unpeelAt

/-!
# The **unpeel** step of the §5 chain round

`NOTES_prop36SW_of_ladderA_SESSION8.md` §2 step 4: after the slot `s₀` of a chain state has been
peeled (its `t'` long directions consumed as the `iterDelta` shifts of the peeled state), the
identity `Concat.boxNormPow_iteratedPeel` turns the average over the accumulated shift parameters of
the box-norm power of the iterated difference back into the box-norm power of the **original**
function family, over the union of *all* the long directions.

Concretely, this module proves `roundUnpeel`: from the peeled state's conclusion

`γ ≤ (card (shiftSetFin p M₁ M₂ A γ₀ t' s₀))⁻¹ ∑_{x} boxNormPow (card (Σ s : PeelSlot s₀, Fin (trest s)))
      (fun i => arithIcc (p sᵢ a) (Lrest sᵢ)) (symIcc N') (peelGFin t' g x)`

(where each `x` carries a parameter `a = restr x ∈ A` and the `t'` shift values of the peeled slot),
deduce the unpeeled conclusion

`γ ≤ (card A)⁻¹ ∑_{a ∈ A} boxNormPow (card (Σ s : ι, Fin (t s)))
      (fun i => arithIcc (p sᵢ a) (Lw sᵢ)) (symIcc N') (g a)`

in the flat (`Fin n → ℤ`) parameter type, with `t s₀.1 = t'`, `Lw s₀.1 = ⌊γ₀M₁M₂⌋` and
`t (s.1.1) = trest s`, `Lw (s.1.1) = Lrest s` for `s : PeelSlot s₀`.

The proof is the fibre decomposition of `shiftSetFin` (`lstatePeelFin.sum_toFin` +
`lstatePeelFin.card_peelParam` + the cardinality of the peeled parameter type) together with the
*per-parameter* peel identity `unpeelAt` (`Submission/Work/Peluse/Prop36SW/unpeelAt.lean`), which is
`Concat.boxNormPow_iteratedPeel` after the reindexing of the conclusion's family along
`Σ s : ι, Fin (t s) ≃ Fin t' ⊕ Σ s : PeelSlot s₀, Fin (trest s)`.

**Warning (module hygiene).**  `Submission/Work/Peluse/Prop36SW/card_peelParam.lean` (a delegated
side lemma, superseded by the private `card_peelParamSum` below and *not* imported here) declares
`Work.Peluse.Prop36SW.card_peelParam`, a name that **already exists in `lstatePeelFin.lean`** with a
different statement; do not import both modules into one file.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.Prop36SW

noncomputable section

open Work.Peluse.UControl

/-! ## 1. The peeled families -/

/-- The number of directions of the peeled (i.e. *remaining*, non-`s₀`) slots. -/
def unpeelSlotCard {ι : Type} [Fintype ι] [DecidableEq ι] (s₀ : Slot ι (fun _ => 1))
    (trest : PeelSlot s₀ → ℕ) : ℕ :=
  Fintype.card (Σ s : PeelSlot s₀, Fin (trest s))

/-- The peeled state's direction family in `Fin`-normal form, read at the parameter `a`:
`trest s` copies of the direction `p (s.1.1) a` with window `Lrest s`, over
`s : PeelSlot s₀` (i.e. over the slots other than `s₀`). -/
def unpeelFamDir {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (p : ι → (Fin n → ℤ) → ℤ)
    (s₀ : Slot ι (fun _ => 1)) (trest : PeelSlot s₀ → ℕ) (Lrest : PeelSlot s₀ → ℕ)
    (a : Fin n → ℤ) : Fin (unpeelSlotCard s₀ trest) → Finset ℤ :=
  fun i => arithIcc
    (p (((Fintype.equivFin (Σ s : PeelSlot s₀, Fin (trest s))).symm i).1).1.1 a)
    (Lrest ((Fintype.equivFin (Σ s : PeelSlot s₀, Fin (trest s))).symm i).1)

/-- The unpeeled state's direction family in `Fin`-normal form, read at the parameter `a`:
`t s` copies of the direction `p s a` with window `Lw s`, over `s : ι`. -/
def unpeelFullDir {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (p : ι → (Fin n → ℤ) → ℤ)
    (t : ι → ℕ) (Lw : ι → ℕ) (a : Fin n → ℤ) :
    Fin (Fintype.card (Σ s : ι, Fin (t s))) → Finset ℤ :=
  fun i => arithIcc (p ((Fintype.equivFin (Σ s : ι, Fin (t s))).symm i).1 a)
    (Lw ((Fintype.equivFin (Σ s : ι, Fin (t s))).symm i).1)

/-- The summand of the peel's average: the `2^{unpeelSlotCard}`-th power of the box norm of the
iterated difference `iterDelta t' sh (g a)` at the peeled direction family. -/
def unpeelSummand {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (p : ι → (Fin n → ℤ) → ℤ)
    (L₀ t' : ℕ) (s₀ : Slot ι (fun _ => 1)) (trest : PeelSlot s₀ → ℕ)
    (Lrest : PeelSlot s₀ → ℕ) (a : Fin n → ℤ) (S : Finset ℤ)
    (g : (Fin n → ℤ) → ℤ → ℂ)
    (sh : (j : Fin t') → ↥(arithIcc (p s₀.1 a) L₀) × ↥(arithIcc (p s₀.1 a) L₀)) : ℝ :=
  boxNormPow (unpeelSlotCard s₀ trest) (unpeelFamDir p s₀ trest Lrest a) S
    (Work.Peluse.Ulower.iterDelta t' (fun j => (((sh j).1 : ℤ), ((sh j).2 : ℤ))) (g a))

/-- The sum over the `t'` shift pairs of the peeled slot. -/
def unpeelSum {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (p : ι → (Fin n → ℤ) → ℤ)
    (L₀ t' : ℕ) (s₀ : Slot ι (fun _ => 1)) (trest : PeelSlot s₀ → ℕ)
    (Lrest : PeelSlot s₀ → ℕ) (a : Fin n → ℤ) (S : Finset ℤ)
    (g : (Fin n → ℤ) → ℤ → ℂ) : ℝ :=
  ∑ sh, unpeelSummand p L₀ t' s₀ trest Lrest a S g sh

/-- The unpeeled box-norm power at the parameter `a`. -/
def unpeelBox {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (p : ι → (Fin n → ℤ) → ℤ)
    (t : ι → ℕ) (Lw : ι → ℕ) (a : Fin n → ℤ) (S : Finset ℤ)
    (g : (Fin n → ℤ) → ℤ → ℂ) : ℝ :=
  boxNormPow (Fintype.card (Σ s : ι, Fin (t s))) (unpeelFullDir p t Lw a) S (g a)

/-- The summand of the peeled state's hypothesis, as a function of the flat parameter `x`: the
box-norm power of the iterated difference of `g (restr x)` at the peeled direction family read at
`restr x`. -/
def unpeelPhi {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (p : ι → (Fin n → ℤ) → ℤ)
    (t' : ℕ) (s₀ : Slot ι (fun _ => 1)) (trest : PeelSlot s₀ → ℕ) (Lrest : PeelSlot s₀ → ℕ)
    (S : Finset ℤ) (g : (Fin n → ℤ) → ℤ → ℂ) (x : Fin (n + 2 * t') → ℤ) : ℝ :=
  boxNormPow (unpeelSlotCard s₀ trest) (unpeelFamDir p s₀ trest Lrest (restr n t' x)) S
    (peelGFin t' g x)

/-- The "swap-if-odd" involution of the block of `t'` shift pairs: the parity of `n` decides
whether the stored pair `(shiftC false, shiftC true)` of `toFin` is the pair itself or its swap. -/
def swapIfOddEquiv {m : ℕ} (n : ℕ) (Q : Finset ℤ) :
    ((j : Fin m) → ↥Q × ↥Q) ≃ ((j : Fin m) → ↥Q × ↥Q) :=
  if n % 2 = 0 then Equiv.refl _ else Equiv.piCongrRight (fun _ : Fin m => Equiv.prodComm _ _)

/-- The underlying map of `swapIfOddEquiv` (definitionally its application). -/
def swapIfOddFun {m : ℕ} (n : ℕ) (Q : Finset ℤ) (sh : (j : Fin m) → ↥Q × ↥Q) :
    (j : Fin m) → ↥Q × ↥Q :=
  swapIfOddEquiv n Q sh

/-- The pointwise description of `swapIfOddFun`. -/
private lemma swapIfOddFun_apply {m : ℕ} (n : ℕ) (Q : Finset ℤ)
    (sh : (j : Fin m) → ↥Q × ↥Q) (j : Fin m) :
    swapIfOddFun n Q sh j = if n % 2 = 0 then sh j else (sh j).swap := by
  by_cases h : n % 2 = 0 <;> simp [swapIfOddFun, swapIfOddEquiv, h]

/-! ## 2. Cardinality of the peeled parameter type -/

private lemma card_arithIcc' {c : ℤ} (hc : c ≠ 0) (D : ℕ) : (arithIcc c D).card = D := by
  rw [arithIcc, Finset.card_image_of_injOn]
  · simp
  · intro a _ b _ hab
    have h : (a : ℤ) = (b : ℤ) := mul_left_cancel₀ hc hab
    exact_mod_cast h

private lemma card_shiftBlock (c : ℤ) (L t' : ℕ) (hc : c ≠ 0) :
    Fintype.card ((j : Fin t') → ↥(arithIcc c L) × ↥(arithIcc c L)) = L ^ (2 * t') := by
  have h2 : ∀ _j : Fin t',
      Fintype.card (↥(arithIcc c L) × ↥(arithIcc c L)) = L ^ 2 := by
    intro j
    rw [Fintype.card_prod, Fintype.card_coe, card_arithIcc' hc]
    ring
  rw [Fintype.card_pi, Finset.prod_congr rfl (fun j _ => h2 j), Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← pow_mul]

/-- **The cardinality of the peeled parameter type**, in the "unwound" form: the product of the
cardinalities of `A`, of the parameter box and of the shift block. -/
private theorem card_peelParamSum {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (p : ι → (Fin n → ℤ) → ℤ) (M₁ M₂ : ℕ) (A : Finset (Fin n → ℤ)) (γ' : ℝ) (t' : ℕ)
    (s₀ : Slot ι (fun _ => 1)) (hgood : ∀ a ∈ A, p s₀.1 a ≠ 0) :
    Fintype.card (PeelParam p M₁ M₂ A γ' t' s₀)
      = A.card * (paramBox (k := fun _ : ι => 1) M₂).card *
        (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat ^ (2 * t') := by
  rw [Fintype.card_sigma]
  have h : ∀ ab : {a : Fin n → ℤ // a ∈ A} ×
      {b : Slot ι (fun _ => 1) → ℤ // b ∈ paramBox (k := fun _ : ι => 1) M₂},
      Fintype.card ((j : Fin t') →
          ↥(arithIcc (p s₀.1 ab.1.1) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat) ×
          ↥(arithIcc (p s₀.1 ab.1.1) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat))
        = ((⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat) ^ (2 * t') :=
    fun ab => card_shiftBlock _ _ t' (hgood _ ab.1.2)
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_coe]
  ring

private lemma sum_subtype_sum' {P Q : Type} (A : Finset P) (Box : Finset Q)
    (Sh : P → Type) [∀ a, Fintype (Sh a)] (f : (a : P) → Q → Sh a → ℝ) :
    (∑ a : ↥A, ∑ b : ↥Box, ∑ sh : Sh a.1, f a.1 b.1 sh)
      = ∑ a ∈ A, ∑ b ∈ Box, ∑ sh : Sh a, f a b sh := by
  have hX : ∀ a : P, (∑ b : ↥Box, ∑ sh : Sh a, f a b.1 sh) = ∑ b ∈ Box, ∑ sh : Sh a, f a b sh :=
    fun a => (Finset.sum_subtype Box (fun x => Iff.rfl) (fun b => ∑ sh : Sh a, f a b sh)).symm
  calc (∑ a : ↥A, ∑ b : ↥Box, ∑ sh : Sh a.1, f a.1 b.1 sh)
      = ∑ a : ↥A, ∑ b ∈ Box, ∑ sh : Sh a.1, f a.1 b sh := by
        apply Finset.sum_congr rfl
        intro a _
        exact hX a.1
    _ = ∑ a ∈ A, ∑ b ∈ Box, ∑ sh : Sh a, f a b sh :=
        (Finset.sum_subtype A (fun x => Iff.rfl) (fun a => ∑ b ∈ Box, ∑ sh : Sh a, f a b sh)).symm

/-- **Fubini for the peeled parameter type.**  The sum over the dependent sigma type `PeelParam`
unwinds to the iterated sum over `A`, the parameter box and the shift block. -/
private lemma peelParam_fubini {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (p : ι → (Fin n → ℤ) → ℤ) (M₁ M₂ : ℕ) (A : Finset (Fin n → ℤ)) (γ' : ℝ) (t' : ℕ)
    (s₀ : Slot ι (fun _ => 1))
    (Φ : (a : Fin n → ℤ) → (Slot ι (fun _ => 1) → ℤ) →
      ((j : Fin t') → ↥(arithIcc (p s₀.1 a) (peelL M₁ M₂ γ')) ×
        ↥(arithIcc (p s₀.1 a) (peelL M₁ M₂ γ'))) → ℝ) :
    (∑ q : PeelParam p M₁ M₂ A γ' t' s₀, Φ (q.1.1 : Fin n → ℤ)
        (q.1.2 : Slot ι (fun _ => 1) → ℤ) q.2)
      = ∑ a ∈ A, ∑ b ∈ paramBox (k := fun _ : ι => 1) M₂, ∑ sh, Φ a b sh := by
  rw [Fintype.sum_sigma]
  dsimp only
  rw [Fintype.sum_prod_type]
  dsimp only
  exact sum_subtype_sum' A (paramBox (k := fun _ : ι => 1) M₂) _ Φ

/-! ## 3. The peeled summand read at a nested parameter -/

/-- The `t'` shift values stored in a nested parameter, as a `ℤ × ℤ`-valued function.  This is the
parity-normalised form of the stored pairs: for even `n` it is `q.2` itself, for odd `n` the swap. -/
def peelSh {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (p : ι → (Fin n → ℤ) → ℤ)
    (M₁ M₂ : ℕ) (A : Finset (Fin n → ℤ)) (γ' : ℝ) (t' : ℕ) (s₀ : Slot ι (fun _ => 1))
    (q : PeelParam p M₁ M₂ A γ' t' s₀) : Fin t' → ℤ × ℤ :=
  fun j => (((swapIfOddFun n (arithIcc (p s₀.1 (q.1.1 : Fin n → ℤ)) (peelL M₁ M₂ γ')) q.2)
      j).1,
    ((swapIfOddFun n (arithIcc (p s₀.1 (q.1.1 : Fin n → ℤ)) (peelL M₁ M₂ γ')) q.2) j).2)

private lemma unpeelPhi_toFin {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (p : ι → (Fin n → ℤ) → ℤ) (M₁ M₂ : ℕ) (A : Finset (Fin n → ℤ)) (γ' : ℝ) (t' : ℕ)
    (s₀ : Slot ι (fun _ => 1)) (trest : PeelSlot s₀ → ℕ) (Lrest : PeelSlot s₀ → ℕ)
    (S : Finset ℤ) (g : (Fin n → ℤ) → ℤ → ℂ) (q : PeelParam p M₁ M₂ A γ' t' s₀) :
    unpeelPhi p t' s₀ trest Lrest S g (toFin p M₁ M₂ A γ' t' s₀ q)
      = unpeelSummand p (peelL M₁ M₂ γ') t' s₀ trest Lrest (q.1.1 : Fin n → ℤ) S g
          (swapIfOddFun n (arithIcc (p s₀.1 (q.1.1 : Fin n → ℤ)) (peelL M₁ M₂ γ')) q.2) := by
  have hsh : ∀ j : Fin t',
      (shiftC n t' (toFin p M₁ M₂ A γ' t' s₀ q) j false,
        shiftC n t' (toFin p M₁ M₂ A γ' t' s₀ q) j true)
      = peelSh p M₁ M₂ A γ' t' s₀ q j := by
    have hpt : ∀ j : Fin t',
        swapIfOddFun n (arithIcc (p s₀.1 (q.1.1 : Fin n → ℤ)) (peelL M₁ M₂ γ')) q.2 j
          = if n % 2 = 0 then q.2 j else (q.2 j).swap :=
      fun j => swapIfOddFun_apply n _ q.2 j
    intro j
    rw [shiftC_toFin_false, shiftC_toFin_true]
    simp only [peelSh, hpt]
    by_cases h : n % 2 = 0 <;> simp [h, Prod.swap]
  simp only [unpeelPhi, unpeelSummand, peelGFin]
  rw [restr_toFin, show (fun j : Fin t' =>
        (shiftC n t' (toFin p M₁ M₂ A γ' t' s₀ q) j false,
          shiftC n t' (toFin p M₁ M₂ A γ' t' s₀ q) j true))
      = peelSh p M₁ M₂ A γ' t' s₀ q from funext hsh]
  rfl

/-! ## 4. The assembly -/

/-- **The unpeel, given the per-parameter peel identity.**  From the peeled state's conclusion `h`
and the per-parameter identity `hAt0`, deduce the unpeeled conclusion. -/
private theorem roundUnpeelMain {ι : Type} [Fintype ι] [DecidableEq ι] (n : ℕ)
    (p : ι → (Fin n → ℤ) → ℤ) (M₁ M₂ : ℕ) (A : Finset (Fin n → ℤ))
    (g : (Fin n → ℤ) → ℤ → ℂ) (γ₀ : ℝ) (t' : ℕ)
    (s₀ : Work.Peluse.UControl.Slot ι (fun _ => 1))
    (trest : Work.Peluse.Prop36SW.PeelSlot s₀ → ℕ)
    (Lrest : Work.Peluse.Prop36SW.PeelSlot s₀ → ℕ)
    (t : ι → ℕ) (Lw : ι → ℕ) (N' : ℕ) (γ : ℝ)
    (hgood : ∀ a ∈ A, p s₀.1 a ≠ 0)
    (hSne : (Work.Peluse.Prop36SW.shiftSetFin p M₁ M₂ A γ₀ t' s₀).card ≠ 0)
    (h : γ ≤ ((Work.Peluse.Prop36SW.shiftSetFin p M₁ M₂ A γ₀ t' s₀).card : ℝ)⁻¹ *
        ∑ x ∈ Work.Peluse.Prop36SW.shiftSetFin p M₁ M₂ A γ₀ t' s₀,
          unpeelPhi p t' s₀ trest Lrest (Work.Peluse.symIcc N') g x)
    (hAt0 : ∀ a ∈ A,
        unpeelBox p t Lw a (Work.Peluse.symIcc N') g
          = ((peelL M₁ M₂ γ₀ : ℝ))⁻¹ ^ (2 * t') *
            unpeelSum p (peelL M₁ M₂ γ₀) t' s₀ trest Lrest a (Work.Peluse.symIcc N') g) :
    γ ≤ (A.card : ℝ)⁻¹ * ∑ a ∈ A, unpeelBox p t Lw a (Work.Peluse.symIcc N') g := by
  classical
  -- the parameter box is nonempty
  have hBne : ((paramBox (k := fun _ : ι => 1) M₂).card : ℝ) ≠ 0 := by
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hSne)
    obtain ⟨q, -, -⟩ := Finset.mem_image.mp hx
    have hBpos : 0 < (paramBox (k := fun _ : ι => 1) M₂).card :=
      Finset.card_pos.mpr ⟨q.1.2.1, q.1.2.2⟩
    exact_mod_cast hBpos.ne'
  -- the two forms of the cardinality of `PeelParam`
  have hNcard : (Fintype.card (PeelParam p M₁ M₂ A γ₀ t' s₀) : ℝ)
      = (A.card : ℝ) * ((paramBox (k := fun _ : ι => 1) M₂).card : ℝ)
        * ((peelL M₁ M₂ γ₀ : ℝ) ^ (2 * t')) := by
    rw [card_peelParamSum p M₁ M₂ A γ₀ t' s₀ hgood]
    simp only [peelL]
    push_cast
    ring
  have hNK : (Fintype.card (PeelParam p M₁ M₂ A γ₀ t' s₀) : ℝ)
      = ((paramBox (k := fun _ : ι => 1) M₂).card : ℝ)
        * ((Work.Peluse.Prop36SW.shiftSetFin p M₁ M₂ A γ₀ t' s₀).card : ℝ) := by
    rw [card_peelParam]
    push_cast
    ring
  -- the cardinality of the flat parameter set
  have hcardS : ((Work.Peluse.Prop36SW.shiftSetFin p M₁ M₂ A γ₀ t' s₀).card : ℝ)
      = (A.card : ℝ) * ((peelL M₁ M₂ γ₀ : ℝ) ^ (2 * t')) := by
    have h2 : ((paramBox (k := fun _ : ι => 1) M₂).card : ℝ)
          * ((Work.Peluse.Prop36SW.shiftSetFin p M₁ M₂ A γ₀ t' s₀).card : ℝ)
        = ((paramBox (k := fun _ : ι => 1) M₂).card : ℝ)
          * ((A.card : ℝ) * ((peelL M₁ M₂ γ₀ : ℝ) ^ (2 * t'))) := by
      rw [← hNK, hNcard]
      ring
    exact mul_left_cancel₀ hBne h2
  have hLne : ((peelL M₁ M₂ γ₀ : ℝ) ^ (2 * t')) ≠ 0 := by
    have h3 : (A.card : ℝ) * ((peelL M₁ M₂ γ₀ : ℝ) ^ (2 * t')) ≠ 0 := by
      rw [← hcardS]
      exact_mod_cast hSne
    exact right_ne_zero_of_mul h3
  -- the per-parameter identity, in the direction the algebra uses
  have hAt : ∀ a ∈ A,
      unpeelSum p (peelL M₁ M₂ γ₀) t' s₀ trest Lrest a (Work.Peluse.symIcc N') g
        = ((peelL M₁ M₂ γ₀ : ℝ) ^ (2 * t')) *
          unpeelBox p t Lw a (Work.Peluse.symIcc N') g := by
    intro a ha
    have hxne : (((peelL M₁ M₂ γ₀ : ℝ))⁻¹ ^ (2 * t')) ≠ 0 := by
      rcases Nat.eq_zero_or_pos t' with h0 | hpos
      · subst h0
        simp
      · have hL0ne : (peelL M₁ M₂ γ₀ : ℝ) ≠ 0 := by
          intro hz
          exact hLne (by rw [hz]; exact zero_pow (by omega))
        rw [inv_pow]
        exact inv_ne_zero (pow_ne_zero _ hL0ne)
    have hxinv : ((((peelL M₁ M₂ γ₀ : ℝ))⁻¹ ^ (2 * t'))⁻¹)
        = ((peelL M₁ M₂ γ₀ : ℝ) ^ (2 * t')) := by
      rw [inv_pow, inv_inv]
    calc unpeelSum p (peelL M₁ M₂ γ₀) t' s₀ trest Lrest a (Work.Peluse.symIcc N') g
        = ((((peelL M₁ M₂ γ₀ : ℝ))⁻¹ ^ (2 * t'))⁻¹)
            * ((((peelL M₁ M₂ γ₀ : ℝ))⁻¹ ^ (2 * t'))
              * unpeelSum p (peelL M₁ M₂ γ₀) t' s₀ trest Lrest a (Work.Peluse.symIcc N') g) := by
          rw [← mul_assoc, inv_mul_cancel₀ hxne, one_mul]
      _ = ((((peelL M₁ M₂ γ₀ : ℝ))⁻¹ ^ (2 * t'))⁻¹)
            * unpeelBox p t Lw a (Work.Peluse.symIcc N') g := by rw [← hAt0 a ha]
      _ = ((peelL M₁ M₂ γ₀ : ℝ) ^ (2 * t')) *
            unpeelBox p t Lw a (Work.Peluse.symIcc N') g := by rw [hxinv]
  -- the fibre identity
  have hAtt : (∑ x ∈ Work.Peluse.Prop36SW.shiftSetFin p M₁ M₂ A γ₀ t' s₀,
          unpeelPhi p t' s₀ trest Lrest (Work.Peluse.symIcc N') g x)
      = ∑ x : ↥(Work.Peluse.Prop36SW.shiftSetFin p M₁ M₂ A γ₀ t' s₀),
          unpeelPhi p t' s₀ trest Lrest (Work.Peluse.symIcc N') g x.1 := by
    rw [← Finset.sum_attach]
    rfl
  have hsum1 : (∑ x ∈ Work.Peluse.Prop36SW.shiftSetFin p M₁ M₂ A γ₀ t' s₀,
          unpeelPhi p t' s₀ trest Lrest (Work.Peluse.symIcc N') g x)
      = ((paramBox (k := fun _ : ι => 1) M₂).card : ℝ)⁻¹ *
        ∑ q : PeelParam p M₁ M₂ A γ₀ t' s₀,
          unpeelPhi p t' s₀ trest Lrest (Work.Peluse.symIcc N') g
            (toFin p M₁ M₂ A γ₀ t' s₀ q) := by
    have hsum := sum_toFin p M₁ M₂ A γ₀ t' s₀
      (unpeelPhi p t' s₀ trest Lrest (Work.Peluse.symIcc N') g)
    rw [hAtt]
    rw [hsum]
    rw [← mul_assoc, inv_mul_cancel₀ hBne, one_mul]
  -- the sum over the peeled parameter type
  have hsum2 : (∑ q : PeelParam p M₁ M₂ A γ₀ t' s₀,
          unpeelPhi p t' s₀ trest Lrest (Work.Peluse.symIcc N') g
            (toFin p M₁ M₂ A γ₀ t' s₀ q))
      = ((paramBox (k := fun _ : ι => 1) M₂).card : ℝ) * ((peelL M₁ M₂ γ₀ : ℝ) ^ (2 * t'))
        * ∑ a ∈ A, unpeelBox p t Lw a (Work.Peluse.symIcc N') g := by
    rw [Finset.sum_congr rfl (fun q _ => unpeelPhi_toFin p M₁ M₂ A γ₀ t' s₀ trest Lrest
      (Work.Peluse.symIcc N') g q)]
    rw [peelParam_fubini p M₁ M₂ A γ₀ t' s₀
      (fun a b sh => unpeelSummand p (peelL M₁ M₂ γ₀) t' s₀ trest Lrest a
        (Work.Peluse.symIcc N') g (swapIfOddFun n (arithIcc (p s₀.1 a) (peelL M₁ M₂ γ₀)) sh))]
    have hstep : ∀ a ∈ A, ∀ _b : Slot ι (fun _ => 1) → ℤ,
        (∑ sh : (j : Fin t') → ↥(arithIcc (p s₀.1 a) (peelL M₁ M₂ γ₀)) ×
            ↥(arithIcc (p s₀.1 a) (peelL M₁ M₂ γ₀)),
          unpeelSummand p (peelL M₁ M₂ γ₀) t' s₀ trest Lrest a (Work.Peluse.symIcc N') g
            (swapIfOddFun n (arithIcc (p s₀.1 a) (peelL M₁ M₂ γ₀)) sh))
          = ((peelL M₁ M₂ γ₀ : ℝ) ^ (2 * t')) *
            unpeelBox p t Lw a (Work.Peluse.symIcc N') g := by
      intro a ha b
      rw [show (∑ sh : (j : Fin t') → ↥(arithIcc (p s₀.1 a) (peelL M₁ M₂ γ₀)) ×
              ↥(arithIcc (p s₀.1 a) (peelL M₁ M₂ γ₀)),
            unpeelSummand p (peelL M₁ M₂ γ₀) t' s₀ trest Lrest a (Work.Peluse.symIcc N') g
              (swapIfOddFun n (arithIcc (p s₀.1 a) (peelL M₁ M₂ γ₀)) sh))
          = unpeelSum p (peelL M₁ M₂ γ₀) t' s₀ trest Lrest a (Work.Peluse.symIcc N') g from
        Equiv.sum_comp (swapIfOddEquiv n (arithIcc (p s₀.1 a) (peelL M₁ M₂ γ₀)))
          (fun sh => unpeelSummand p (peelL M₁ M₂ γ₀) t' s₀ trest Lrest a
            (Work.Peluse.symIcc N') g sh)]
      exact hAt a ha
    rw [Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun b _ => hstep a ha b))]
    rw [Finset.sum_congr rfl (fun a _ =>
      (Finset.sum_const (s := paramBox (k := fun _ : ι => 1) M₂)
        (b := ((peelL M₁ M₂ γ₀ : ℝ) ^ (2 * t')) *
          unpeelBox p t Lw a (Work.Peluse.symIcc N') g)).trans (by rw [nsmul_eq_mul]))]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    ring
  refine h.trans (le_of_eq ?_)
  calc ((Work.Peluse.Prop36SW.shiftSetFin p M₁ M₂ A γ₀ t' s₀).card : ℝ)⁻¹ *
        ∑ x ∈ Work.Peluse.Prop36SW.shiftSetFin p M₁ M₂ A γ₀ t' s₀,
          unpeelPhi p t' s₀ trest Lrest (Work.Peluse.symIcc N') g x
      = ((Work.Peluse.Prop36SW.shiftSetFin p M₁ M₂ A γ₀ t' s₀).card : ℝ)⁻¹ *
        (((paramBox (k := fun _ : ι => 1) M₂).card : ℝ)⁻¹ *
          ∑ q : PeelParam p M₁ M₂ A γ₀ t' s₀,
            unpeelPhi p t' s₀ trest Lrest (Work.Peluse.symIcc N') g
              (toFin p M₁ M₂ A γ₀ t' s₀ q)) := by rw [hsum1]
    _ = ((Work.Peluse.Prop36SW.shiftSetFin p M₁ M₂ A γ₀ t' s₀).card : ℝ)⁻¹ *
        (((paramBox (k := fun _ : ι => 1) M₂).card : ℝ)⁻¹ *
          (((paramBox (k := fun _ : ι => 1) M₂).card : ℝ) * ((peelL M₁ M₂ γ₀ : ℝ) ^ (2 * t'))
            * ∑ a ∈ A, unpeelBox p t Lw a (Work.Peluse.symIcc N') g)) := by rw [hsum2]
    _ = (A.card : ℝ)⁻¹ * ∑ a ∈ A, unpeelBox p t Lw a (Work.Peluse.symIcc N') g := by
      rw [hcardS]
      field_simp

/-! ## 5. The target -/

theorem roundUnpeel {ι : Type} [Fintype ι] [DecidableEq ι] (n : ℕ)
    (p : ι → (Fin n → ℤ) → ℤ) (M₁ M₂ : ℕ) (A : Finset (Fin n → ℤ))
    (g : (Fin n → ℤ) → ℤ → ℂ) (γ₀ : ℝ) (t' : ℕ)
    (s₀ : Work.Peluse.UControl.Slot ι (fun _ => 1))
    (trest : Work.Peluse.Prop36SW.PeelSlot s₀ → ℕ)
    (Lrest : Work.Peluse.Prop36SW.PeelSlot s₀ → ℕ)
    (t : ι → ℕ) (Lw : ι → ℕ) (N' : ℕ) (γ : ℝ)
    (ht0 : t s₀.1 = t')
    (hL0 : Lw s₀.1 = (⌊γ₀ * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat)
    (ht : ∀ s : Work.Peluse.Prop36SW.PeelSlot s₀, t s.1.1 = trest s)
    (hLw : ∀ s : Work.Peluse.Prop36SW.PeelSlot s₀, Lw s.1.1 = Lrest s)
    (hm : 1 ≤ Fintype.card (Σ s : Work.Peluse.Prop36SW.PeelSlot s₀, Fin (trest s)))
    (hgood : ∀ a ∈ A, p s₀.1 a ≠ 0)
    (hfin : ∀ a ∈ A, Work.Peluse.FinSuppZ (g a))
    (h : γ ≤ ((Work.Peluse.Prop36SW.shiftSetFin p M₁ M₂ A γ₀ t' s₀).card : ℝ)⁻¹ *
        ∑ x ∈ Work.Peluse.Prop36SW.shiftSetFin p M₁ M₂ A γ₀ t' s₀,
          Work.Peluse.boxNormPow
            (Fintype.card (Σ s : Work.Peluse.Prop36SW.PeelSlot s₀, Fin (trest s)))
            (fun i => Work.Peluse.arithIcc
              (Work.Peluse.Prop36SW.peelPFin p t' s₀
                ((Fintype.equivFin (Σ s : Work.Peluse.Prop36SW.PeelSlot s₀, Fin (trest s))).symm i).1 x)
              (Lrest ((Fintype.equivFin (Σ s : Work.Peluse.Prop36SW.PeelSlot s₀, Fin (trest s))).symm i).1))
            (Work.Peluse.symIcc N') (Work.Peluse.Prop36SW.peelGFin t' g x)) :
    γ ≤ (A.card : ℝ)⁻¹ * ∑ a ∈ A,
          Work.Peluse.boxNormPow (Fintype.card (Σ s : ι, Fin (t s)))
            (fun i => Work.Peluse.arithIcc
              (p ((Fintype.equivFin (Σ s : ι, Fin (t s))).symm i).1 a)
              (Lw ((Fintype.equivFin (Σ s : ι, Fin (t s))).symm i).1))
            (Work.Peluse.symIcc N') (g a) := by
  classical
  by_cases hS : (Work.Peluse.Prop36SW.shiftSetFin p M₁ M₂ A γ₀ t' s₀).card = 0
  · -- the degenerate case: the hypothesis forces `γ ≤ 0`
    have hle : γ ≤ 0 := by
      have h' := h
      rw [hS] at h'
      simpa using h'
    have hRHS : (0 : ℝ) ≤ (A.card : ℝ)⁻¹ *
        ∑ a ∈ A, unpeelBox p t Lw a (Work.Peluse.symIcc N') g := by
      refine mul_nonneg (by positivity) (Finset.sum_nonneg (fun a _ => ?_))
      simp only [unpeelBox, boxNormPow]
      positivity
    change γ ≤ (A.card : ℝ)⁻¹ * ∑ a ∈ A, unpeelBox p t Lw a (Work.Peluse.symIcc N') g
    exact hle.trans hRHS
  · change γ ≤ (A.card : ℝ)⁻¹ * ∑ a ∈ A, unpeelBox p t Lw a (Work.Peluse.symIcc N') g
    refine roundUnpeelMain n p M₁ M₂ A g γ₀ t' s₀ trest Lrest t Lw N' γ hgood hS ?_ ?_
    · -- the hypothesis, in the vocabulary of the peeled families
      have h' := h
      rw [show (∑ x ∈ Work.Peluse.Prop36SW.shiftSetFin p M₁ M₂ A γ₀ t' s₀,
            Work.Peluse.boxNormPow
              (Fintype.card (Σ s : Work.Peluse.Prop36SW.PeelSlot s₀, Fin (trest s)))
              (fun i => Work.Peluse.arithIcc
                (Work.Peluse.Prop36SW.peelPFin p t' s₀
                  ((Fintype.equivFin (Σ s : Work.Peluse.Prop36SW.PeelSlot s₀, Fin (trest s))).symm i).1 x)
                (Lrest ((Fintype.equivFin (Σ s : Work.Peluse.Prop36SW.PeelSlot s₀, Fin (trest s))).symm i).1))
              (Work.Peluse.symIcc N') (Work.Peluse.Prop36SW.peelGFin t' g x))
          = (∑ x ∈ Work.Peluse.Prop36SW.shiftSetFin p M₁ M₂ A γ₀ t' s₀,
              unpeelPhi p t' s₀ trest Lrest (Work.Peluse.symIcc N') g x) from rfl] at h'
      exact h'
    · -- the per-parameter peel identity, from the delegated `unpeelAt`
      intro a ha
      exact unpeelAt p s₀ trest Lrest t Lw t' (peelL M₁ M₂ γ₀) ht0 hL0 ht hLw hm g a
        (Work.Peluse.symIcc N') (hgood a ha) (hfin a ha)

end

end Work.Peluse.Prop36SW
