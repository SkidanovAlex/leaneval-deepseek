import Mathlib
import Submission.Work.Peluse.Prop36SW.dirShift

/-!
# The sign invariance of the ladder's conclusion

`NOTES_prop36SW_of_ladderA_SESSION5.md` §3 proves that the natural coefficient of Peluse's §5 chain
is **signed**, while the frozen `PeluseLadderA` demands a **positive** coefficient; §6/§9 worried that
the reconciliation needs a partial reflection of the conclusion, which has no clean identity.

This module settles it: **no reflection is needed.**  The sign substitution `b ↦ signSubst ε b`
(`ε_s = intSign (p s a)`) makes the *short* directions of `conclDirG p … a b` and
`conclDirG (|p|) … a (signSubst ε b)` **equal**, and the *long* directions
`arithIcc (|p s₀ a|) L'` and `arithIcc (p s₀ a) L'` are **translates** of one another
(`arithIcc_abs_eq_image_shift`), which the box sum does not see
(`boxNormPow_image_shift_idx`).  Hence

  `boxNormPow N (conclDirG p … a b) S X = boxNormPow N (conclDirG (|p|) … a (signSubst ε b)) S X`

(`boxNormPow_conclDirG_abs`), and summing over the box and reindexing by `b ↦ signSubst ε b`
(`sum_paramBox_boxNorm_conclDirG_abs`) gives the form consumed by the chain: the ladder's conclusion
for the **positive** coefficient `|p|` is the conclusion for the **signed** `p`.

Together with `signBridge.sum_paramBox_pDirFamG_abs` (the *hypothesis* is also sign-invariant), the
chain can be run with the signed coefficient `p` — which is what makes the round's regrouping
identity exact and keeps the function family `f` — while the ladder is always applied to `|p|`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.Prop36SW

noncomputable section

open Work.Peluse.UControl

/-- The translation of the long direction sets that turns `arithIcc (p s₀ a) L'` into
`arithIcc (|p s₀ a|) L'`. -/
def longShift {ι : Type} [Fintype ι] [DecidableEq ι] (kω : SlotSet ι (fun _ => 1) → ℕ)
    {P : Type} (p : ι → P → ℤ) (M₁ M₂ : ℕ) (γ' : ℝ) (s₀ : Slot ι (fun _ => 1)) (t' : ℕ)
    (a : P) : Fin (Fintype.card (ConclIdx s₀ kω t')) → ℤ :=
  fun i => match (Fintype.equivFin (ConclIdx s₀ kω t')).symm i with
    | Sum.inl _ => (if p s₀.1 a < 0 then
        -((((⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat : ℤ) + 1)) * p s₀.1 a else 0)
    | Sum.inr _ => 0

/-- The pointwise form: the sign-substituted conclusion with `|p|` is the conclusion with `p` after
translating the long direction sets. -/
lemma conclDirG_abs_shift {ι : Type} [Fintype ι] [DecidableEq ι]
    (kω : SlotSet ι (fun _ => 1) → ℕ) {P : Type} (p : ι → P → ℤ) (M₁ M₂ : ℕ) (γ' : ℝ)
    (s₀ : Slot ι (fun _ => 1)) (t' : ℕ) (a : P) (b : Slot ι (fun _ => 1) → ℤ)
    (i : Fin (Fintype.card (ConclIdx s₀ kω t'))) :
    conclDirG (k := fun _ : ι => 1) (kω := kω) (fun s _ => |p s a|) M₁ M₂ γ' s₀ t' a
        (signSubst (fun s => intSign (p s a)) b)
        ((Fintype.equivFin (ConclIdx s₀ kω t')).symm i)
      = (conclDirG (k := fun _ : ι => 1) (kω := kω) p M₁ M₂ γ' s₀ t' a b
          ((Fintype.equivFin (ConclIdx s₀ kω t')).symm i)).image
        (fun z : ℤ => z + longShift kω p M₁ M₂ γ' s₀ t' a i) := by
  have hid : (fun z : ℤ => z + 0) = id := funext (fun z => add_zero z)
  rcases h : (Fintype.equivFin (ConclIdx s₀ kω t')).symm i with kk | ⟨ω, r⟩
  · show Work.Peluse.arithIcc |p s₀.1 a| (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat
      = (Work.Peluse.arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat).image
          (fun z : ℤ => z + longShift kω p M₁ M₂ γ' s₀ t' a i)
    rw [longShift, h]
    exact arithIcc_abs_eq_image_shift (p s₀.1 a) _
  · have hτ : longShift kω p M₁ M₂ γ' s₀ t' a i = 0 := by
      rw [longShift, h]
    rw [hτ, hid, Finset.image_id]
    refine congrArg (fun t => Work.Peluse.arithIcc t M₁) ?_
    refine Finset.sum_congr rfl ?_
    intro s hs
    show |p s.1 a| * (intSign (p s.1 a) * b s) = p s.1 a * b s
    have h2 : intSign (p s.1 a) * intSign (p s.1 a) = 1 := intSign_sq (p s.1 a)
    calc |p s.1 a| * (intSign (p s.1 a) * b s)
        = (intSign (p s.1 a) * p s.1 a) * (intSign (p s.1 a) * b s) := by
          rw [← intSign_mul_self (p s.1 a)]
      _ = (intSign (p s.1 a) * intSign (p s.1 a)) * (p s.1 a * b s) := by ring
      _ = p s.1 a * b s := by rw [h2, one_mul]

/-- **The box-norm power of the ladder's conclusion is sign-invariant.**  The conclusion with the
signed coefficient `p` and box parameter `b` has the same box-norm power as the conclusion with `|p|`
and the sign-substituted parameter `signSubst ε b`. -/
theorem boxNormPow_conclDirG_abs {ι : Type} [Fintype ι] [DecidableEq ι]
    (kω : SlotSet ι (fun _ => 1) → ℕ) {P : Type} (p : ι → P → ℤ) (M₁ M₂ : ℕ) (γ' : ℝ)
    (s₀ : Slot ι (fun _ => 1)) (t' : ℕ) (a : P) (b : Slot ι (fun _ => 1) → ℤ)
    (S : Finset ℤ) (X : ℤ → ℂ) :
    Work.Peluse.boxNormPow (Fintype.card (ConclIdx s₀ kω t'))
      (fun i => conclDirG (k := fun _ : ι => 1) (kω := kω) p M₁ M₂ γ' s₀ t' a b
        ((Fintype.equivFin (ConclIdx s₀ kω t')).symm i)) S X
    = Work.Peluse.boxNormPow (Fintype.card (ConclIdx s₀ kω t'))
      (fun i => conclDirG (k := fun _ : ι => 1) (kω := kω) (fun s _ => |p s a|) M₁ M₂ γ' s₀ t' a
        (signSubst (fun s => intSign (p s a)) b)
        ((Fintype.equivFin (ConclIdx s₀ kω t')).symm i)) S X := by
  set Q : Fin (Fintype.card (ConclIdx s₀ kω t')) → Finset ℤ :=
    fun i => conclDirG (k := fun _ : ι => 1) (kω := kω) p M₁ M₂ γ' s₀ t' a b
      ((Fintype.equivFin (ConclIdx s₀ kω t')).symm i) with hQ
  set Q' : Fin (Fintype.card (ConclIdx s₀ kω t')) → Finset ℤ :=
    fun i => conclDirG (k := fun _ : ι => 1) (kω := kω) (fun s _ => |p s a|) M₁ M₂ γ' s₀ t' a
      (signSubst (fun s => intSign (p s a)) b)
      ((Fintype.equivFin (ConclIdx s₀ kω t')).symm i) with hQ'
  have hfam : Q' = fun i => (Q i).image (fun z : ℤ => z + longShift kω p M₁ M₂ γ' s₀ t' a i) := by
    funext i
    rw [hQ, hQ']
    exact conclDirG_abs_shift kω p M₁ M₂ γ' s₀ t' a b i
  rw [show Work.Peluse.boxNormPow (Fintype.card (ConclIdx s₀ kω t')) Q S X
      = Work.Peluse.boxNormPow (Fintype.card (ConclIdx s₀ kω t')) Q' S X from by
    rw [hfam]
    exact (boxNormPow_image_shift_idx (Fintype.card (ConclIdx s₀ kω t')) Q
      (longShift kω p M₁ M₂ γ' s₀ t' a) S X).symm]

/-- The `boxNorm` form of the sign invariance of the conclusion. -/
theorem boxNorm_conclDirG_abs {ι : Type} [Fintype ι] [DecidableEq ι]
    (kω : SlotSet ι (fun _ => 1) → ℕ) {P : Type} (p : ι → P → ℤ) (M₁ M₂ : ℕ) (γ' : ℝ)
    (s₀ : Slot ι (fun _ => 1)) (t' : ℕ) (a : P) (b : Slot ι (fun _ => 1) → ℤ)
    (S : Finset ℤ) (X : ℤ → ℂ) :
    Work.Peluse.boxNorm (Fintype.card (ConclIdx s₀ kω t'))
      (fun i => conclDirG (k := fun _ : ι => 1) (kω := kω) p M₁ M₂ γ' s₀ t' a b
        ((Fintype.equivFin (ConclIdx s₀ kω t')).symm i)) S X
    = Work.Peluse.boxNorm (Fintype.card (ConclIdx s₀ kω t'))
      (fun i => conclDirG (k := fun _ : ι => 1) (kω := kω) (fun s _ => |p s a|) M₁ M₂ γ' s₀ t' a
        (signSubst (fun s => intSign (p s a)) b)
        ((Fintype.equivFin (ConclIdx s₀ kω t')).symm i)) S X := by
  rw [Work.Peluse.boxNorm, Work.Peluse.boxNorm,
    boxNormPow_conclDirG_abs kω p M₁ M₂ γ' s₀ t' a b S X]

/-- **The box average of the conclusion's box norm is sign-invariant.**  Summing
`boxNorm_conclDirG_abs` over the parameter box and reindexing by the involution
`b ↦ signSubst ε b` (a bijection of the box, `signBridge.signSubst_mem_paramBox`) gives the form
consumed by the chain. -/
theorem sum_paramBox_boxNorm_conclDirG_abs {ι : Type} [Fintype ι] [DecidableEq ι]
    (kω : SlotSet ι (fun _ => 1) → ℕ) {P : Type} (p : ι → P → ℤ) (M₁ M₂ : ℕ) (γ' : ℝ)
    (s₀ : Slot ι (fun _ => 1)) (t' : ℕ) (a : P) (S : Finset ℤ) (X : ℤ → ℂ) :
    (∑ b ∈ paramBox (k := fun _ : ι => 1) M₂,
        Work.Peluse.boxNorm (Fintype.card (ConclIdx s₀ kω t'))
          (fun i => conclDirG (k := fun _ : ι => 1) (kω := kω) p M₁ M₂ γ' s₀ t' a b
            ((Fintype.equivFin (ConclIdx s₀ kω t')).symm i)) S X)
      = ∑ b ∈ paramBox (k := fun _ : ι => 1) M₂,
        Work.Peluse.boxNorm (Fintype.card (ConclIdx s₀ kω t'))
          (fun i => conclDirG (k := fun _ : ι => 1) (kω := kω) (fun s _ => |p s a|) M₁ M₂ γ' s₀ t'
            a b ((Fintype.equivFin (ConclIdx s₀ kω t')).symm i)) S X := by
  classical
  set ε : ι → ℤ := fun s => intSign (p s a) with hε
  have hsq : ∀ s, ε s * ε s = 1 := fun s => intSign_sq (p s a)
  have hbij : ∀ b ∈ paramBox (k := fun _ : ι => 1) M₂,
      signSubst ε b ∈ paramBox (k := fun _ : ι => 1) M₂ :=
    fun b hb => (signSubst_mem_paramBox ε (fun s => intSign_eq_one_or_neg_one (p s a)) M₂ b).mpr hb
  have hinv : ∀ b ∈ paramBox (k := fun _ : ι => 1) M₂, signSubst ε (signSubst ε b) = b :=
    fun b _ => signSubst_invol ε hsq b
  have hinj : Set.InjOn (signSubst ε) ↑(paramBox (k := fun _ : ι => 1) M₂) := by
    intro x hx y hy hxy
    rw [Finset.mem_coe] at hx hy
    rw [← hinv x hx, hxy, hinv y hy]
  have himg : (paramBox (k := fun _ : ι => 1) M₂).image (signSubst ε)
      = paramBox (k := fun _ : ι => 1) M₂ := by
    refine Finset.Subset.antisymm (fun c hc => ?_) (fun b hb => ?_)
    · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc
      exact hbij d hd
    · exact Finset.mem_image.mpr ⟨signSubst ε b, hbij b hb, hinv b hb⟩
  have hstep : (∑ b ∈ paramBox (k := fun _ : ι => 1) M₂,
        Work.Peluse.boxNorm (Fintype.card (ConclIdx s₀ kω t'))
          (fun i => conclDirG (k := fun _ : ι => 1) (kω := kω) p M₁ M₂ γ' s₀ t' a b
            ((Fintype.equivFin (ConclIdx s₀ kω t')).symm i)) S X)
      = ∑ b ∈ paramBox (k := fun _ : ι => 1) M₂,
        Work.Peluse.boxNorm (Fintype.card (ConclIdx s₀ kω t'))
          (fun i => conclDirG (k := fun _ : ι => 1) (kω := kω) (fun s _ => |p s a|) M₁ M₂ γ' s₀ t'
            a (signSubst ε b) ((Fintype.equivFin (ConclIdx s₀ kω t')).symm i)) S X :=
    Finset.sum_congr rfl (fun b _ => boxNorm_conclDirG_abs kω p M₁ M₂ γ' s₀ t' a b S X)
  have h1 : (∑ x ∈ (paramBox (k := fun _ : ι => 1) M₂).image (signSubst ε),
        Work.Peluse.boxNorm (Fintype.card (ConclIdx s₀ kω t'))
          (fun i => conclDirG (k := fun _ : ι => 1) (kω := kω) (fun s _ => |p s a|) M₁ M₂ γ' s₀ t'
            a x ((Fintype.equivFin (ConclIdx s₀ kω t')).symm i)) S X)
      = ∑ x ∈ paramBox (k := fun _ : ι => 1) M₂,
        Work.Peluse.boxNorm (Fintype.card (ConclIdx s₀ kω t'))
          (fun i => conclDirG (k := fun _ : ι => 1) (kω := kω) (fun s _ => |p s a|) M₁ M₂ γ' s₀ t'
            a (signSubst ε x) ((Fintype.equivFin (ConclIdx s₀ kω t')).symm i)) S X :=
    Finset.sum_image hinj
  rw [himg] at h1
  rw [hstep, ← h1]

end

end Work.Peluse.Prop36SW
