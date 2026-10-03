import Mathlib
import Submission.Work.Peluse.LadderA.hyp_avg_split
import Submission.Work.Peluse.LadderA.concl_avg_sum
import Submission.Work.Peluse.LadderA.peel_split_pair
import Submission.Work.Peluse.LadderA.levelRaiseAppendBd
import Submission.Work.Peluse.LadderA.rpowLevelRaise

/-!
# The zero branch of the ladder's peel

This file proves `Work.Peluse.LadderA.zeroBranch`: the case of Peluse's Lemma 5.7 in which the
`A`-part of the hypothesis's index set (the subsets `ω ∋ s₀` of slots) is empty.  In that case the
peel of the hypothesis family is trivial: the whole family consists of `B`-directions
(`ω ∌ s₀`), so the hypothesis already bounds the box norm of `f a` at level
`card (FamIdx kω) = card (BIdx k kω s₀)` with exactly the directions that the conclusion carries,
and the conclusion is obtained from it by *raising the level*: appending the `tbig` long directions
`arithIcc (p s₀.1 a) (⌊γ'M₁M₂⌋)` to the `B`-family.

The arithmetic of the level raise (`Work.Peluse.LadderA.levelRaiseAppendBd`) costs the constant
`(1/2)^{2^tbig - 1}` on the `2^tbig`-th power; taking the `2^card (ConclIdx)`-th root
(`Work.Peluse.LadderA.rpowLevelRaise`) turns this into the constant
`c₀ = ((1/2)^{2^tbig-1})^{1/2^{card (ConclIdx s₀ kω tbig)}}` on the box norms themselves.  Since
`card (ConclIdx s₀ kω tbig) = card (FamIdx kω) + tbig`, the exponent `2^tbig / 2^{card ConclIdx}`
reduces to `2^{-card (FamIdx kω)}`, which is exactly the exponent that converts the hypothesis's
box-norm *power* into its box *norm*.  The final constant is `cc = c₀ / 2`, and
`cc (γγ')^{Kbig} ≤ c₀ γ` because `γ ≤ 1`, `γ' ≤ 1` and `Kbig ≥ 1`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.LadderA

noncomputable section

open Work.Peluse Work.Peluse.UControl

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## 1. The index-set bookkeeping of the zero branch -/

/-- **The zero-branch equivalence.**  If the `A`-part of the index set is empty, then every index of
the hypothesis's family `FamIdx kω = Σ_{ω} [k_ω]` has `s₀ ∉ ω`: otherwise the pair `(ω, r)` would
be an element of `AIdx k kω s₀`.  Hence `FamIdx kω ≃ BIdx k kω s₀` by forgetting and restoring the
(automatic) side condition `s₀ ∉ ω`. -/
def zeroEquiv (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (s₀ : Slot ι k)
    (hs0 : Fintype.card (AIdx k kω s₀) = 0) : FamIdx kω ≃ BIdx k kω s₀ where
  toFun j :=
    ⟨⟨j.1, by
        by_contra h
        have hpos : 0 < Fintype.card (AIdx k kω s₀) :=
          Fintype.card_pos_iff.mpr ⟨⟨⟨j.1, h⟩, j.2⟩⟩
        omega⟩, j.2⟩
  invFun y := ⟨y.1.1, y.2⟩
  left_inv j := by rcases j with ⟨⟨s, hs⟩, r⟩; rfl
  right_inv y := by rcases y with ⟨⟨ω, h⟩, r⟩; rfl

/-- The `B`-family of the peel, evaluated at the image of `zeroEquiv`, is the hypothesis's
direction family. -/
lemma qB_zeroEquiv_eq_pDirFam (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (p : ι → (Fin n → ℤ) → ℤ)
    (M₁ : ℕ) (a : Fin n → ℤ) (b : Slot ι k → ℤ) (s₀ : Slot ι k)
    (hs0 : Fintype.card (AIdx k kω s₀) = 0) (j : FamIdx kω) :
    qB k kω p M₁ a b s₀ (zeroEquiv k kω s₀ hs0 j) = pDirFam p M₁ a b j := by
  rw [qB, pDirFam]
  congr 1

/-- The two index sets have the same cardinality in the zero branch. -/
lemma card_famIdx_eq_card_BIdx (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (s₀ : Slot ι k)
    (hs0 : Fintype.card (AIdx k kω s₀) = 0) :
    Fintype.card (FamIdx kω) = Fintype.card (BIdx k kω s₀) := by
  rw [card_famIdx k kω s₀, hs0]
  simp

/-! ## 2. Reindexing the hypothesis's and the conclusion's box-norm powers -/

/-- **The hypothesis's box-norm power in the `B`-form.**  In the zero branch the family
`pDirFam p M₁ a b` (indexed by `FamIdx kω`) is, after reindexing along `zeroEquiv`, exactly the
`B`-family `QBfin k kω p M₁ a b s₀`. -/
lemma hypBoxNormPow_eq (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (p : ι → (Fin n → ℤ) → ℤ) (M₁ : ℕ)
    (a : Fin n → ℤ) (b : Slot ι k → ℤ) (s₀ : Slot ι k)
    (hs0 : Fintype.card (AIdx k kω s₀) = 0) (S : Finset ℤ) (g : ℤ → ℂ) :
    boxNormPow (Fintype.card (FamIdx kω))
        (fun j => pDirFam p M₁ a b ((Fintype.equivFin (FamIdx kω)).symm j)) S g
      = boxNormPow (Fintype.card (BIdx k kω s₀)) (QBfin k kω p M₁ a b s₀) S g := by
  have hcard : Fintype.card (FamIdx kω) = Fintype.card (BIdx k kω s₀) :=
    card_famIdx_eq_card_BIdx k kω s₀ hs0
  let E : Fin (Fintype.card (FamIdx kω)) ≃ Fin (Fintype.card (BIdx k kω s₀)) :=
    (Fintype.equivFin (FamIdx kω)).symm.trans
      ((zeroEquiv k kω s₀ hs0).trans (Fintype.equivFin (BIdx k kω s₀)))
  let e : Fin (Fintype.card (BIdx k kω s₀)) ≃ Fin (Fintype.card (FamIdx kω)) :=
    { toFun := E.symm, invFun := E, left_inv := fun x => E.right_inv x,
      right_inv := fun y => E.left_inv y }
  have hfam : (fun i : Fin (Fintype.card (FamIdx kω)) =>
        QBfin k kω p M₁ a b s₀ (e.symm i))
      = fun j : Fin (Fintype.card (FamIdx kω)) =>
          pDirFam p M₁ a b ((Fintype.equivFin (FamIdx kω)).symm j) := by
    funext i
    have hsym : e.symm i = (Fintype.equivFin (BIdx k kω s₀))
        (zeroEquiv k kω s₀ hs0 ((Fintype.equivFin (FamIdx kω)).symm i)) := rfl
    rw [hsym, QBfin, Equiv.symm_apply_apply]
    exact qB_zeroEquiv_eq_pDirFam k kω p M₁ a b s₀ hs0 ((Fintype.equivFin (FamIdx kω)).symm i)
  rw [← hfam]
  exact boxNormPow_reindex hcard e (QBfin k kω p M₁ a b s₀) S g

/-- **The conclusion's box-norm power in the `Fin.append` form.**  The conclusion's family
`conclDir p M₁ M₂ γ' s₀ t' a b` is the concatenation of the `B`-family with the `t'` long directions
`arithIcc (p s₀.1 a) (⌊γ'M₁M₂⌋)`, and `card (ConclIdx s₀ kω t')` is
`card (BIdx k kω s₀) + t'`; the equivalence `conclFinEquiv` performs that identification. -/
lemma conclBoxNormPow_eq (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (p : ι → (Fin n → ℤ) → ℤ)
    (M₁ M₂ : ℕ) (γ' : ℝ) (s₀ : Slot ι k) (t' : ℕ) (a : Fin n → ℤ) (b : Slot ι k → ℤ)
    (S : Finset ℤ) (g : ℤ → ℂ) :
    boxNormPow (Fintype.card (ConclIdx s₀ kω t'))
        (fun j => conclDir p M₁ M₂ γ' s₀ t' a b ((Fintype.equivFin (ConclIdx s₀ kω t')).symm j))
        S g
      = boxNormPow (Fintype.card (BIdx k kω s₀) + t')
          (Fin.append (QBfin k kω p M₁ a b s₀)
            (fun _ : Fin t' => arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat))
          S g := by
  have hcard : Fintype.card (BIdx k kω s₀) + t' = Fintype.card (ConclIdx s₀ kω t') :=
    card_conclIdx k kω s₀ t'
  have hfam : (fun i : Fin (Fintype.card (BIdx k kω s₀) + t') =>
        conclDir p M₁ M₂ γ' s₀ t' a b
          ((Fintype.equivFin (ConclIdx s₀ kω t')).symm ((conclFinEquiv k kω s₀ t').symm i)))
      = Fin.append (QBfin k kω p M₁ a b s₀)
          (fun _ : Fin t' => arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat) := by
    funext i
    simpa only [Equiv.apply_symm_apply] using
      conclFamily_eq_append k kω p M₁ M₂ a b s₀ t' γ' ((conclFinEquiv k kω s₀ t').symm i)
  rw [← hfam]
  exact (boxNormPow_reindex hcard (conclFinEquiv k kω s₀ t')
    (fun j => conclDir p M₁ M₂ γ' s₀ t' a b ((Fintype.equivFin (ConclIdx s₀ kω t')).symm j))
    S g).symm

/-! ## 3. Small direction-set facts -/

/-- The arithmetic progression `c[L]` is nonempty when `L ≥ 1`. -/
lemma arithIcc_nonempty {c : ℤ} {L : ℕ} (hL : 1 ≤ L) : (arithIcc c L).Nonempty :=
  ⟨c * 1, Finset.mem_image.mpr ⟨1, by simp [hL], by ring⟩⟩

/-- A function supported in `[-N,N]` vanishes off `symIcc N`. -/
lemma eq_zero_of_not_mem_symIcc {N : ℕ} {g : ℤ → ℂ} (h : SupportIn g N) {x : ℤ}
    (hx : x ∉ symIcc N) : g x = 0 := by
  apply h
  have h1 : ¬ (|x| ≤ (N : ℤ)) := fun hc => hx (PET.mem_symIcc_iff_abs.mpr hc)
  have h2 : (N : ℤ) < |x| := lt_of_not_ge h1
  rw [← Int.natCast_natAbs] at h2
  exact_mod_cast h2

/-- The `B`-directions of the ladder are nonempty (`M₁ ≥ 1`). -/
lemma QBfin_nonempty (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (p : ι → (Fin n → ℤ) → ℤ) (M₁ : ℕ)
    (a : Fin n → ℤ) (b : Slot ι k → ℤ) (s₀ : Slot ι k) (hM₁ : 1 ≤ M₁)
    (j : Fin (Fintype.card (BIdx k kω s₀))) :
    (QBfin k kω p M₁ a b s₀ j).Nonempty := by
  rw [QBfin, qB, pDir]
  exact arithIcc_nonempty hM₁

/-! ## 4. The pointwise comparison -/

/-- **The pointwise step of the zero branch.**  For `a` a good parameter (positive coefficient
`p s₀.1 a > 0` with `p s₀.1 a · M₁M₂ ≤ N`) and any `b`, the conclusion's box norm of `f` at
parameter `b` dominates the hypothesis's box norm at parameter `b`, up to the explicit constant
`c₀ = ((1/2)^{2^tbig-1})^{1/2^{card (ConclIdx s₀ kω tbig)}}`. -/
theorem zeroBranch_pointwise (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (p : ι → (Fin n → ℤ) → ℤ)
    (D : ℕ) (s₀ : Slot ι k) (m : ℕ)
    (hm : Fintype.card (FamIdx kω) = m) (hs0 : Fintype.card (AIdx k kω s₀) = 0)
    (tbig : ℕ) (M₁ M₂ N : ℕ) (γ' : ℝ) (a : Fin n → ℤ) (b : Slot ι k → ℤ) (ft : ℤ → ℂ)
    (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂) (hN : 1 ≤ N) (hγ'0 : 0 < γ') (hγ'1 : γ' ≤ 1)
    (hγ'M : 1 ≤ γ' * (M₁ : ℝ) * (M₂ : ℝ))
    (hcpos : 0 < p s₀.1 a) (hcN : p s₀.1 a * (M₁ : ℤ) * (M₂ : ℤ) ≤ (N : ℤ))
    (hfsupp : SupportIn ft N) :
    ((1 / 2 : ℝ) ^ (2 ^ tbig - 1)) ^ (1 / (2 : ℝ) ^ (Fintype.card (ConclIdx s₀ kω tbig)))
        * boxNorm (Fintype.card (FamIdx kω))
            (fun j => pDirFam p M₁ a b ((Fintype.equivFin (FamIdx kω)).symm j))
            (symIcc N) ft
      ≤ boxNorm (Fintype.card (ConclIdx s₀ kω tbig))
          (fun j => conclDir p M₁ M₂ γ' s₀ tbig a b
            ((Fintype.equivFin (ConclIdx s₀ kω tbig)).symm j))
          (symIcc N) ft := by
  classical
  set L₀ : ℕ := (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat with hL₀
  set Long : Fin tbig → Finset ℤ :=
    fun _ => arithIcc (p s₀.1 a) L₀ with hLong
  -- the long directions are nonempty and their elements are bounded by `N`
  have hflnn : (0 : ℤ) ≤ ⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋ :=
    Int.floor_nonneg.mpr (by positivity)
  have hL₀cast : ((⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat : ℤ) =
      ⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋ := Int.toNat_of_nonneg hflnn
  have hfloor1 : (1 : ℤ) ≤ ⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋ := by
    rw [Int.le_floor]
    push_cast
    linarith [hγ'M]
  have hL₀1 : 1 ≤ L₀ := by
    rw [hL₀, Int.le_toNat hflnn]
    exact hfloor1
  have hL₀bound : (L₀ : ℝ) ≤ γ' * (M₁ : ℝ) * (M₂ : ℝ) := by
    have h1 : (L₀ : ℤ) ≤ ⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋ := by rw [hL₀, hL₀cast]
    have h2 : (L₀ : ℝ) ≤ ((⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋ : ℤ) : ℝ) := by exact_mod_cast h1
    linarith [Int.floor_le (γ' * (M₁ : ℝ) * (M₂ : ℝ))]
  have hL : ∀ i : Fin tbig, (Long i).Nonempty := fun i => by
    rw [hLong]; exact arithIcc_nonempty hL₀1
  have hLbd : ∀ i : Fin tbig, ∀ z : ℤ, z ∈ Long i → |z| ≤ (N : ℤ) := by
    intro i z hz
    rw [hLong] at hz
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
    have htL : t ≤ L₀ := (Finset.mem_Icc.mp ht).2
    have hc0 : (0 : ℤ) ≤ p s₀.1 a := le_of_lt hcpos
    have ht0 : (0 : ℤ) ≤ (t : ℤ) := by positivity
    rw [abs_of_nonneg (mul_nonneg hc0 ht0)]
    have htR : (t : ℝ) ≤ (L₀ : ℝ) := by exact_mod_cast htL
    have hpR : (0 : ℝ) ≤ (p s₀.1 a : ℝ) := by positivity
    have h1 : (p s₀.1 a : ℝ) * (t : ℝ) ≤ (p s₀.1 a : ℝ) * (L₀ : ℝ) :=
      mul_le_mul_of_nonneg_left htR hpR
    have h2 : (p s₀.1 a : ℝ) * (L₀ : ℝ) ≤
        (p s₀.1 a : ℝ) * (γ' * (M₁ : ℝ) * (M₂ : ℝ)) :=
      mul_le_mul_of_nonneg_left hL₀bound hpR
    have h3 : (p s₀.1 a : ℝ) * (γ' * (M₁ : ℝ) * (M₂ : ℝ)) ≤
        (p s₀.1 a : ℝ) * (M₁ : ℝ) * (M₂ : ℝ) := by
      have hMnn : (0 : ℝ) ≤ (M₁ : ℝ) * (M₂ : ℝ) := by positivity
      have hγ'M' : γ' * ((M₁ : ℝ) * (M₂ : ℝ)) ≤ (M₁ : ℝ) * (M₂ : ℝ) := by
        simpa using mul_le_mul_of_nonneg_right hγ'1 hMnn
      calc (p s₀.1 a : ℝ) * (γ' * (M₁ : ℝ) * (M₂ : ℝ))
          = (p s₀.1 a : ℝ) * (γ' * ((M₁ : ℝ) * (M₂ : ℝ))) := by ring
        _ ≤ (p s₀.1 a : ℝ) * ((M₁ : ℝ) * (M₂ : ℝ)) := mul_le_mul_of_nonneg_left hγ'M' hpR
        _ = (p s₀.1 a : ℝ) * (M₁ : ℝ) * (M₂ : ℝ) := by ring
    have h4 : (p s₀.1 a : ℝ) * (M₁ : ℝ) * (M₂ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hcN
    have h5 : ((p s₀.1 a * (t : ℤ) : ℤ) : ℝ) ≤ (N : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h5
  have hsup : ∀ x : ℤ, x ∉ symIcc N → ft x = 0 :=
    fun x hx => eq_zero_of_not_mem_symIcc hfsupp hx
  -- the level raise
  have hlev := levelRaiseAppendBd (a := Fintype.card (BIdx k kω s₀)) (b := tbig) (N := N)
    (by omega) (QBfin k kω p M₁ a b s₀) Long ft
    (fun j => QBfin_nonempty k kω p M₁ a b s₀ hM₁ j) hL hLbd hsup
  -- rewrite both sides of the level raise
  have hHypPow := hypBoxNormPow_eq k kω p M₁ a b s₀ hs0 (symIcc N) ft
  have hConPow := conclBoxNormPow_eq k kω p M₁ M₂ γ' s₀ tbig a b (symIcc N) ft
  -- cardinalities
  have hcardBF : Fintype.card (FamIdx kω) = Fintype.card (BIdx k kω s₀) :=
    card_famIdx_eq_card_BIdx k kω s₀ hs0
  have hβ : Fintype.card (ConclIdx s₀ kω tbig) = Fintype.card (FamIdx kω) + tbig := by
    rw [← card_conclIdx k kω s₀ tbig, hcardBF]
  -- the rpow step
  have hrp := rpowLevelRaise (X := boxNormPow (Fintype.card (BIdx k kω s₀))
        (QBfin k kω p M₁ a b s₀) (symIcc N) ft)
    (Y := boxNormPow (Fintype.card (BIdx k kω s₀) + tbig)
        (Fin.append (QBfin k kω p M₁ a b s₀) Long) (symIcc N) ft)
    (c := (1 / 2 : ℝ) ^ (2 ^ tbig - 1))
    (mm := Fintype.card (FamIdx kω)) (tt := tbig)
    (β := Fintype.card (ConclIdx s₀ kω tbig))
    (norm_nonneg _) (by positivity) hβ hlev
  -- convert back to `boxNorm`
  have hX : (boxNormPow (Fintype.card (BIdx k kω s₀)) (QBfin k kω p M₁ a b s₀) (symIcc N) ft)
        ^ (1 / (2 : ℝ) ^ (Fintype.card (FamIdx kω)))
      = boxNorm (Fintype.card (FamIdx kω))
          (fun j => pDirFam p M₁ a b ((Fintype.equivFin (FamIdx kω)).symm j)) (symIcc N) ft := by
    rw [boxNorm, ← hHypPow]
  have hY : (boxNormPow (Fintype.card (BIdx k kω s₀) + tbig)
        (Fin.append (QBfin k kω p M₁ a b s₀) Long) (symIcc N) ft)
        ^ (1 / (2 : ℝ) ^ (Fintype.card (ConclIdx s₀ kω tbig)))
      = boxNorm (Fintype.card (ConclIdx s₀ kω tbig))
          (fun j => conclDir p M₁ M₂ γ' s₀ tbig a b
            ((Fintype.equivFin (ConclIdx s₀ kω tbig)).symm j)) (symIcc N) ft := by
    rw [boxNorm, ← hConPow]
  rw [hX, hY] at hrp
  exact hrp

/-! ## 5. The numerical step and the branch itself -/

/-- The purely numerical step `cc (γγ')^Kbig ≤ c₀ γ` for `cc = c₀/2`. -/
lemma half_mul_pow_le {c₀ γ γ' : ℝ} {Kbig : ℕ} (hc₀ : 0 ≤ c₀) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hγ' : 0 ≤ γ') (hγ'1 : γ' ≤ 1) (hK : 1 ≤ Kbig) :
    (c₀ / 2) * (γ * γ') ^ Kbig ≤ c₀ * γ := by
  have hpow : (γ * γ') ^ Kbig ≤ γ := by
    have h1 : γ ^ Kbig ≤ γ ^ 1 := pow_le_pow_of_le_one (le_of_lt hγ0) hγ1 hK
    have h2 : γ' ^ Kbig ≤ (1 : ℝ) := pow_le_one₀ hγ' hγ'1
    calc (γ * γ') ^ Kbig = γ ^ Kbig * γ' ^ Kbig := by rw [mul_pow]
      _ ≤ γ ^ 1 * 1 := by
          exact mul_le_mul h1 h2 (pow_nonneg hγ' _) (by positivity)
      _ = γ := by rw [pow_one, mul_one]
  have h2 : (c₀ / 2) * (γ * γ') ^ Kbig ≤ (c₀ / 2) * γ :=
    mul_le_mul_of_nonneg_left hpow (by linarith)
  have h3 : (c₀ / 2) * γ ≤ c₀ * γ := by nlinarith [hγ0, hc₀]
  linarith

theorem zeroBranch {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (k : ι → ℕ)
    (kω : Work.Peluse.UControl.SlotSet ι k → ℕ) (p : ι → (Fin n → ℤ) → ℤ) (D : ℕ)
    (s₀ : Work.Peluse.UControl.Slot ι k) (m : ℕ)
    (hm : Fintype.card (Work.Peluse.UControl.FamIdx kω) = m)
    (hs0 : Fintype.card (Work.Peluse.LadderA.AIdx k kω s₀) = 0)
    (tbig : ℕ) (htm : m ≤ tbig) (Kbig : ℕ) (hK : 1 ≤ Kbig) :
    ∃ cc : ℝ, 0 < cc ∧ ∀ (Adata : Finset (Fin n → ℤ)) (M₁ M₂ N : ℕ) (γ γ' : ℝ)
      (f : (Fin n → ℤ) → ℤ → ℂ),
      1 ≤ M₂ → M₂ ≤ M₁ → 1 ≤ N → ((M₁ : ℝ) * (M₂ : ℝ) ≤ (N : ℝ)) →
      0 < γ → γ ≤ 1 → 0 < γ' → γ' ≤ 1 → 1 ≤ γ' * (M₁ : ℝ) * (M₂ : ℝ) →
      (∀ i a, a ∈ Adata → 0 < p i a) →
      (∀ i a, a ∈ Adata → p i a * (M₁ : ℤ) * (M₂ : ℤ) ≤ (N : ℤ)) →
      (∀ i a, a ∈ Adata → |p i a| * (M₁ : ℤ) * (M₂ : ℤ) ≤ (D : ℤ) * (N : ℤ)) →
      (∀ a ∈ Adata, ∀ x : ℤ, ‖f a x‖ ≤ 1) → (∀ a ∈ Adata, Work.Peluse.SupportIn (f a) N) →
      γ ≤ ((Adata.card : ℝ))⁻¹ *
            ((Work.Peluse.UControl.paramBox (k := k) M₂).card : ℝ)⁻¹ *
            ∑ a ∈ Adata, ∑ a' ∈ Work.Peluse.UControl.paramBox (k := k) M₂,
              Work.Peluse.boxNorm (Fintype.card (Work.Peluse.UControl.FamIdx kω))
                (fun j => Work.Peluse.UControl.pDirFam p M₁ a a'
                  ((Fintype.equivFin (Work.Peluse.UControl.FamIdx kω)).symm j))
                (Work.Peluse.symIcc N) (f a) →
      cc * (γ * γ') ^ Kbig ≤ ((Adata.card : ℝ))⁻¹ *
            ((Work.Peluse.UControl.paramBox (k := k) M₂).card : ℝ)⁻¹ *
            ∑ a ∈ Adata, ∑ b ∈ Work.Peluse.UControl.paramBox (k := k) M₂,
              Work.Peluse.boxNorm (Fintype.card (Work.Peluse.UControl.ConclIdx s₀ kω tbig))
                (fun j => Work.Peluse.UControl.conclDir p M₁ M₂ γ' s₀ tbig a b
                  ((Fintype.equivFin (Work.Peluse.UControl.ConclIdx s₀ kω tbig)).symm j))
                (Work.Peluse.symIcc N) (f a) := by
  classical
  set c₀ : ℝ := ((1 / 2 : ℝ) ^ (2 ^ tbig - 1)) ^
    (1 / (2 : ℝ) ^ (Fintype.card (ConclIdx s₀ kω tbig))) with hc₀def
  have hc₀pos : 0 < c₀ := by
    rw [hc₀def]
    exact Real.rpow_pos_of_pos (by positivity) _
  have hc₀nn : 0 ≤ c₀ := le_of_lt hc₀pos
  refine ⟨c₀ / 2, by linarith, ?_⟩
  intro Adata M₁ M₂ N γ γ' f hM₂ hM₂M₁ hN hM₁M₂ hγ0 hγ1 hγ'0 hγ'1 hγ'M hppos hpshift hDpshift
    hfb hfsupp hhyp
  have hM₁ : 1 ≤ M₁ := le_trans hM₂ hM₂M₁
  -- the two families, as functions
  set Hyp : (Fin n → ℤ) → (Slot ι k → ℤ) → ℝ := fun a b =>
    boxNorm (Fintype.card (FamIdx kω))
      (fun j => pDirFam p M₁ a b ((Fintype.equivFin (FamIdx kω)).symm j)) (symIcc N) (f a)
    with hHypdef
  set Con : (Fin n → ℤ) → (Slot ι k → ℤ) → ℝ := fun a b =>
    boxNorm (Fintype.card (ConclIdx s₀ kω tbig))
      (fun j => conclDir p M₁ M₂ γ' s₀ tbig a b
        ((Fintype.equivFin (ConclIdx s₀ kω tbig)).symm j)) (symIcc N) (f a)
    with hCondef
  -- `Adata` and the parameter box are nonempty
  have hAdata_ne : Adata.card ≠ 0 := by
    intro h0
    have hle : γ ≤ 0 := by
      have h := hhyp
      rw [h0] at h
      simpa using h
    linarith
  have hparam_ne : (paramBox (k := k) M₂).Nonempty :=
    ⟨fun _ => 0, by
      rw [paramBox, Fintype.mem_piFinset]
      intro s
      rw [Finset.mem_Ioo]
      have : (0 : ℤ) < (M₂ : ℤ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hM₂
      omega⟩
  have hparam_pos : 0 < (paramBox (k := k) M₂).card := Finset.card_pos.mpr hparam_ne
  have hAcard_pos : 0 < (Adata.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (Finset.card_pos.mp (Nat.pos_of_ne_zero hAdata_ne))
  have hPcard_pos : 0 < ((paramBox (k := k) M₂).card : ℝ) := by exact_mod_cast hparam_pos
  -- the hypothesis, cleared of denominators
  have hS : γ * ((Adata.card : ℝ) * ((paramBox (k := k) M₂).card : ℝ)) ≤
      ∑ a ∈ Adata, ∑ b ∈ paramBox (k := k) M₂, Hyp a b := by
    rw [show (∑ a ∈ Adata, ∑ b ∈ paramBox (k := k) M₂, Hyp a b)
        = ∑ a ∈ Adata, ∑ a' ∈ paramBox (k := k) M₂,
            boxNorm (Fintype.card (FamIdx kω))
              (fun j => pDirFam p M₁ a a' ((Fintype.equivFin (FamIdx kω)).symm j))
              (symIcc N) (f a) from by simp only [hHypdef]]
    have h := mul_le_mul_of_nonneg_right hhyp
      (by positivity : (0 : ℝ) ≤ (Adata.card : ℝ) * ((paramBox (k := k) M₂).card : ℝ))
    have hcancel : ((Adata.card : ℝ)⁻¹ * ((paramBox (k := k) M₂).card : ℝ)⁻¹ *
        ∑ a ∈ Adata, ∑ a' ∈ paramBox (k := k) M₂,
          boxNorm (Fintype.card (FamIdx kω))
            (fun j => pDirFam p M₁ a a' ((Fintype.equivFin (FamIdx kω)).symm j))
            (symIcc N) (f a)) *
        ((Adata.card : ℝ) * ((paramBox (k := k) M₂).card : ℝ))
        = ∑ a ∈ Adata, ∑ a' ∈ paramBox (k := k) M₂,
          boxNorm (Fintype.card (FamIdx kω))
            (fun j => pDirFam p M₁ a a' ((Fintype.equivFin (FamIdx kω)).symm j))
            (symIcc N) (f a) := by
      have hA : (Adata.card : ℝ) ≠ 0 := ne_of_gt hAcard_pos
      have hP : ((paramBox (k := k) M₂).card : ℝ) ≠ 0 := ne_of_gt hPcard_pos
      have hkey : (Adata.card : ℝ)⁻¹ * ((paramBox (k := k) M₂).card : ℝ)⁻¹ *
            (∑ a ∈ Adata, ∑ a' ∈ paramBox (k := k) M₂,
              boxNorm (Fintype.card (FamIdx kω))
                (fun j => pDirFam p M₁ a a' ((Fintype.equivFin (FamIdx kω)).symm j))
                (symIcc N) (f a)) *
            ((Adata.card : ℝ) * ((paramBox (k := k) M₂).card : ℝ))
          = ((Adata.card : ℝ)⁻¹ * (Adata.card : ℝ)) *
            (((paramBox (k := k) M₂).card : ℝ)⁻¹ * ((paramBox (k := k) M₂).card : ℝ)) *
            (∑ a ∈ Adata, ∑ a' ∈ paramBox (k := k) M₂,
              boxNorm (Fintype.card (FamIdx kω))
                (fun j => pDirFam p M₁ a a' ((Fintype.equivFin (FamIdx kω)).symm j))
                (symIcc N) (f a)) := by ring
      rw [hkey, inv_mul_cancel₀ hA, inv_mul_cancel₀ hP, one_mul, one_mul]
    rw [hcancel] at h
    exact h
  -- the pointwise bound
  have hpt : ∀ a ∈ Adata, ∀ b, c₀ * Hyp a b ≤ Con a b := by
    intro a ha b
    have hone := zeroBranch_pointwise k kω p D s₀ m hm hs0 tbig M₁ M₂ N γ' a b (f a)
      hM₁ hM₂ hN hγ'0 hγ'1 hγ'M (hppos s₀.1 a ha) (hpshift s₀.1 a ha) (hfsupp a ha)
    simpa only [hc₀def, hHypdef, hCondef] using hone
  -- sum the pointwise bound
  have hsum : c₀ * (∑ a ∈ Adata, ∑ b ∈ paramBox (k := k) M₂, Hyp a b) ≤
      ∑ a ∈ Adata, ∑ b ∈ paramBox (k := k) M₂, Con a b := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun a ha => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun b _ => hpt a ha b)
  -- assemble
  have hmain : c₀ * γ ≤ ((Adata.card : ℝ))⁻¹ *
      ((paramBox (k := k) M₂).card : ℝ)⁻¹ *
      ∑ a ∈ Adata, ∑ b ∈ paramBox (k := k) M₂, Con a b := by
    have hAP : (0 : ℝ) < (Adata.card : ℝ) * ((paramBox (k := k) M₂).card : ℝ) := by positivity
    have h1 : c₀ * γ * ((Adata.card : ℝ) * ((paramBox (k := k) M₂).card : ℝ)) ≤
        ∑ a ∈ Adata, ∑ b ∈ paramBox (k := k) M₂, Con a b := by
      have h2 : c₀ * (γ * ((Adata.card : ℝ) * ((paramBox (k := k) M₂).card : ℝ))) ≤
          c₀ * (∑ a ∈ Adata, ∑ b ∈ paramBox (k := k) M₂, Hyp a b) :=
        mul_le_mul_of_nonneg_left hS hc₀nn
      linarith [hsum, h2]
    have h2 : c₀ * γ ≤ (∑ a ∈ Adata, ∑ b ∈ paramBox (k := k) M₂, Con a b) /
        ((Adata.card : ℝ) * ((paramBox (k := k) M₂).card : ℝ)) := by
      rw [le_div_iff₀ hAP]
      exact h1
    rwa [div_eq_inv_mul, mul_inv] at h2
  -- the numerical step
  have hnum := half_mul_pow_le (c₀ := c₀) (γ := γ) (γ' := γ') (Kbig := Kbig) hc₀nn hγ0 hγ1
    (le_of_lt hγ'0) hγ'1 hK
  linarith [hnum, hmain]

end

end Work.Peluse.LadderA
