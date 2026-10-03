import Mathlib
import Submission.Work.Peluse.Prop36SW.uNormPowGeMeanPow
import Submission.Work.Peluse.Prop36SW.supportInPeelG
import Submission.Work.Peluse.Prop36SW.conclPeelAvgShort
import Submission.Work.Peluse.Prop36SW.peelPowSum_eq_shortSum

namespace Work.Peluse.Prop36SW

open Work.Peluse.UControl

noncomputable section

/-! ## Elementary facts about `boxNormPow` used by the peel

* `boxNormPow_card_eq` : the box-norm power depends on the support box only through its
  cardinality (the inner `tsum` does not mention `S`);
* `boxNormPow_le_one_of_support_sub_image` : it is at most `1` when the function is `1`-bounded and
  vanishes off a translate of the support box;
* `iterDelta_support_sub_image` : the iterated difference `iterDelta t' sh F` vanishes off the
  translate `symIcc N - ∑_j (sh j).1` of `symIcc N` when `F` vanishes off `symIcc N`;
* `boxNorm_average_pow_varying` : Jensen for the average of box norms, with a direction family
  varying with the index;
* `boxNorm_ge_ratio_mul_boxNormPow` : the comparison between the box norm at a larger support box
  and the box-norm power at a smaller one. -/

/-- The box-norm power `boxNormPow t Q S f` depends on the box `S` only through `|S|`. -/
lemma boxNormPow_card_eq {t : ℕ} (Q : Fin t → Finset ℤ) {S S' : Finset ℤ}
    (hcard : S.card = S'.card) (f : ℤ → ℂ) :
    Work.Peluse.boxNormPow t Q S f = Work.Peluse.boxNormPow t Q S' f := by
  rcases S.eq_empty_or_nonempty with hS | hS
  · rw [hS, Finset.card_empty] at hcard
    have hS' : S' = ∅ := Finset.card_eq_zero.mp hcard.symm
    rw [hS, hS']
  · have hS' : S'.Nonempty := by
      rw [← Finset.card_pos, ← hcard, Finset.card_pos]; exact hS
    rw [Work.Peluse.Ulower.boxNormPow_eq_mul_card t Q S S' f hS']
    rw [hcard]
    field_simp

/-- If `f` is `1`-bounded and vanishes off the translate `S + z`, then `boxNormPow t Q S f ≤ 1`. -/
lemma boxNormPow_le_one_of_support_sub_image {t : ℕ} {Q : Fin t → Finset ℤ} {S : Finset ℤ}
    {f : ℤ → ℂ} {z : ℤ} (hf : ∀ x, ‖f x‖ ≤ 1)
    (hsupp : ∀ x, x ∉ S.image (fun y => y + z) → f x = 0) :
    Work.Peluse.boxNormPow t Q S f ≤ 1 := by
  have hcard : S.card = (S.image (fun y => y + z)).card := (Finset.card_image_of_injective _
    (fun a b h => add_right_cancel h)).symm
  rw [boxNormPow_card_eq Q hcard f]
  exact Work.Peluse.BoxNorm.boxNormPow_le_one hf hsupp

/-- **The iterated difference lives on a translate of the support box.**  If `F` vanishes off
`symIcc N`, then `iterDelta k sh F` vanishes off the translate
`symIcc N - ∑_{j<k} (sh j).1`. -/
lemma iterDelta_support_sub_image (k : ℕ) (sh : Fin k → ℤ × ℤ) :
    ∀ {F : ℤ → ℂ} {N : ℕ}, Work.Peluse.SupportIn F N →
      ∀ x : ℤ, x ∉ (Work.Peluse.symIcc N).image (fun y => y - ∑ j : Fin k, (sh j).1) →
        Work.Peluse.Ulower.iterDelta k sh F x = 0 := by
  induction k with
  | zero =>
    intro F N hF x hx
    rw [Work.Peluse.Ulower.iterDelta_zero]
    have hx' : x ∉ Work.Peluse.symIcc N := by simpa using hx
    exact hF x (Work.Peluse.Ulower.lt_natAbs_of_notMem_symIcc hx')
  | succ k ih =>
    intro F N hF x hx
    have hx' : (x + (sh 0).1) ∉ (Work.Peluse.symIcc N).image
        (fun y => y - ∑ j : Fin k, (sh j.succ).1) := by
      intro hmem
      apply hx
      obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hmem
      refine Finset.mem_image.mpr ⟨y, hy, ?_⟩
      rw [Fin.sum_univ_succ]
      linarith [hyx]
    have hzero : Work.Peluse.Ulower.iterDelta k (fun i => sh i.succ) F (x + (sh 0).1) = 0 :=
      ih (fun i => sh i.succ) hF _ hx'
    rw [Work.Peluse.Ulower.iterDelta_succ]
    show Work.Peluse.Ulower.iterDelta k (fun i => sh i.succ) F (x + (sh 0).1) *
        star (Work.Peluse.Ulower.iterDelta k (fun i => sh i.succ) F (x + (sh 0).2)) = 0
    rw [hzero, zero_mul]

/-- **Jensen for the average of box norms.**  For a finite family of functions and a family of
direction sets, the `2^t`-th power of the average of the box norms is at most the average of the
box-norm powers. -/
lemma boxNorm_average_pow_varying {t : ℕ} {ι : Type} (s : Finset ι)
    (Q : ι → Fin t → Finset ℤ) (S : Finset ℤ) (F : ι → ℤ → ℂ) :
    ((s.card : ℝ)⁻¹ * ∑ i ∈ s, Work.Peluse.boxNorm t (Q i) S (F i)) ^ (2 ^ t)
      ≤ (s.card : ℝ)⁻¹ * ∑ i ∈ s, Work.Peluse.boxNormPow t (Q i) S (F i) := by
  have hn1 : 1 ≤ 2 ^ t := Nat.one_le_two_pow
  have hn0 : (2 ^ t : ℕ) ≠ 0 := Nat.one_le_iff_ne_zero.mp hn1
  have hkey : ∀ i : ι, Work.Peluse.boxNorm t (Q i) S (F i) ^ (2 ^ t)
      = Work.Peluse.boxNormPow t (Q i) S (F i) := by
    intro i
    have hg : 0 ≤ Work.Peluse.boxNormPow t (Q i) S (F i) := norm_nonneg _
    have hcast : (2 : ℝ) ^ t = ((2 ^ t : ℕ) : ℝ) := by rw [Nat.cast_pow]; norm_num
    simp only [Work.Peluse.boxNorm, hcast]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hg]
    have hmul : (1 / ((2 ^ t : ℕ) : ℝ)) * ((2 ^ t : ℕ) : ℝ) = 1 :=
      div_mul_cancel₀ 1 (by exact_mod_cast hn0)
    rw [hmul, Real.rpow_one]
  have hfn : ∀ i ∈ s, 0 ≤ Work.Peluse.boxNorm t (Q i) S (F i) :=
    fun i _ => Real.rpow_nonneg (norm_nonneg _) _
  have hjens : (∑ i ∈ s, Work.Peluse.boxNorm t (Q i) S (F i)) ^ (2 ^ t)
      ≤ (s.card : ℝ) ^ (2 ^ t - 1) * ∑ i ∈ s, Work.Peluse.boxNormPow t (Q i) S (F i) := by
    have h := sum_pow_le_card_pow_mul_sum_pow (s := s)
      (f := fun i => Work.Peluse.boxNorm t (Q i) S (F i)) (n := 2 ^ t) hn1 hfn
    simpa only [hkey] using h
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ (s.card : ℝ) by positivity) with hc | hc
  · have hcard : s.card = 0 := by exact_mod_cast hc.symm
    rw [Finset.card_eq_zero.mp hcard]
    simp
  · rw [mul_pow]
    calc ((s.card : ℝ)⁻¹) ^ (2 ^ t) * (∑ i ∈ s, Work.Peluse.boxNorm t (Q i) S (F i)) ^ (2 ^ t)
        ≤ ((s.card : ℝ)⁻¹) ^ (2 ^ t)
            * ((s.card : ℝ) ^ (2 ^ t - 1) * ∑ i ∈ s, Work.Peluse.boxNormPow t (Q i) S (F i)) :=
          mul_le_mul_of_nonneg_left hjens (pow_nonneg (by positivity) _)
      _ = (((s.card : ℝ)⁻¹) ^ (2 ^ t) * (s.card : ℝ) ^ (2 ^ t - 1))
            * ∑ i ∈ s, Work.Peluse.boxNormPow t (Q i) S (F i) := by ring
      _ = (s.card : ℝ)⁻¹ * ∑ i ∈ s, Work.Peluse.boxNormPow t (Q i) S (F i) := by
          rw [inv_pow_mul_pow_sub hc hn1]

/-- **The box norm at a larger support box dominates the box-norm power at a smaller one.**  If
`S.card ≤ S'.card` and the box-norm power at `S` is at most `1`, then
`(|S|/|S'|)^{1/2^t} · boxNormPow t Q S f ≤ boxNorm t Q S' f`. -/
lemma boxNorm_ge_ratio_mul_boxNormPow {t : ℕ} {Q : Fin t → Finset ℤ} {S S' : Finset ℤ} {f : ℤ → ℂ}
    (hS : S.Nonempty) (hS' : S'.Nonempty) (hcard : S.card ≤ S'.card)
    (hZ : Work.Peluse.boxNormPow t Q S f ≤ 1) :
    (((S.card : ℝ) / (S'.card : ℝ)) ^ (1 / (2 : ℝ) ^ t)) * Work.Peluse.boxNormPow t Q S f
      ≤ Work.Peluse.boxNorm t Q S' f := by
  have hSc : 0 < (S.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hS
  have hS'c : 0 < (S'.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hS'
  have hρnn : 0 ≤ (S.card : ℝ) / (S'.card : ℝ) := by positivity
  have hZnn : 0 ≤ Work.Peluse.boxNormPow t Q S f := norm_nonneg _
  have hscale : Work.Peluse.boxNormPow t Q S' f
      = ((S.card : ℝ) / (S'.card : ℝ)) * Work.Peluse.boxNormPow t Q S f := by
    have h := Work.Peluse.Ulower.boxNormPow_eq_mul_card t Q S S' f hS'
    rw [h]
    field_simp
  have hc1 : (1 : ℝ) / (2 : ℝ) ^ t ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact one_le_pow₀ (by norm_num)
  have hcpos : (0 : ℝ) < 1 / (2 : ℝ) ^ t := by positivity
  have hself : Work.Peluse.boxNormPow t Q S f
      ≤ (Work.Peluse.boxNormPow t Q S f) ^ (1 / (2 : ℝ) ^ t) := by
    rcases eq_or_lt_of_le hZnn with h | h
    · rw [← h]
      exact Real.rpow_nonneg le_rfl _
    · have h1 : (Work.Peluse.boxNormPow t Q S f) ^ (1 : ℝ)
          ≤ (Work.Peluse.boxNormPow t Q S f) ^ (1 / (2 : ℝ) ^ t) :=
        Real.rpow_le_rpow_of_exponent_ge h hZ hc1
      simpa using h1
  rw [Work.Peluse.boxNorm, hscale, Real.mul_rpow hρnn hZnn]
  exact mul_le_mul_of_nonneg_left hself (Real.rpow_nonneg hρnn _)

/-! ## The peeled family and the peeled function, as functions of the old parameter alone -/

/-- The arithmetic progression `c[L]` (`c = p s₀ a`, `L = ⌊γ'M₁M₂⌋`) of the peel at the parameter
`a`: the type of the shifts extracted at the peeled slot. -/
abbrev PeelShift {ι : Type} {P : Type} (p : ι → P → ℤ) (M₁ M₂ : ℕ) (γ' : ℝ)
    (s₀ : Work.Peluse.UControl.Slot ι (fun _ => 1)) (a : P) : Type :=
  ↥(Work.Peluse.arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat)

/-- The direction family of the state after the peel, as a function of the *old* parameter `a` and
of the new direction parameters `a'` only (it does not depend on the remaining components of the
`PeelParam`).  This is `pDirFamG (peelP p M₁ M₂ A γ' t' s₀) M₁ q a'` for any `q` with
`q.1.1.1 = a`; see `famPre_eq_pDirFamG`. -/
def famPre {ι : Type} [Fintype ι] [DecidableEq ι]
    (kω : Work.Peluse.UControl.SlotSet ι (fun _ => 1) → ℕ) {P : Type} (p : ι → P → ℤ) (M₁ : ℕ)
    (s₀ : Work.Peluse.UControl.Slot ι (fun _ => 1)) (a : P)
    (a' : Work.Peluse.UControl.Slot (Work.Peluse.Prop36SW.PeelSlot s₀) (fun _ => 1) → ℤ) :
    Fin (Fintype.card (Work.Peluse.UControl.FamIdx (Work.Peluse.Prop36SW.peelKω kω s₀))) → Finset ℤ :=
  fun j => Work.Peluse.arithIcc
    (∑ s ∈ ((Fintype.equivFin
        (Work.Peluse.UControl.FamIdx (Work.Peluse.Prop36SW.peelKω kω s₀))).symm j).1.1,
      p s.1.1.1 a * a' s) M₁

/-- The iterated difference of the peel, as a function of the old parameter `a` and of the shifts
only: `peelG p M₁ M₂ A γ' t' s₀ g q` for any `q` with `q.1.1.1 = a` and `q.2 = sh`. -/
def uPre {ι : Type} {P : Type} (p : ι → P → ℤ) (M₁ M₂ : ℕ) (γ' : ℝ)
    (s₀ : Work.Peluse.UControl.Slot ι (fun _ => 1)) (t' : ℕ) (g : P → ℤ → ℂ) (a : P)
    (sh : (j : Fin t') → PeelShift p M₁ M₂ γ' s₀ a × PeelShift p M₁ M₂ γ' s₀ a) : ℤ → ℂ :=
  Work.Peluse.Ulower.iterDelta t' (fun j => (((sh j).1 : ℤ), ((sh j).2 : ℤ))) (g a)

/-- `famPre` computes the family of the peel data at `q` when `a = q.1.1.1`. -/
lemma famPre_eq_pDirFamG {ι : Type} [Fintype ι] [DecidableEq ι]
    (kω : Work.Peluse.UControl.SlotSet ι (fun _ => 1) → ℕ) {P : Type} [DecidableEq P]
    (p : ι → P → ℤ) (M₁ M₂ : ℕ) (A : Finset P) (γ' : ℝ) (t' : ℕ)
    (s₀ : Work.Peluse.UControl.Slot ι (fun _ => 1))
    (q : Work.Peluse.Prop36SW.PeelParam p M₁ M₂ A γ' t' s₀)
    (a' : Work.Peluse.UControl.Slot (Work.Peluse.Prop36SW.PeelSlot s₀) (fun _ => 1) → ℤ)
    (j : Fin (Fintype.card (Work.Peluse.UControl.FamIdx (Work.Peluse.Prop36SW.peelKω kω s₀)))) :
    famPre kω p M₁ s₀ q.1.1.1 a' j
      = Work.Peluse.Prop36SW.pDirFamG (Work.Peluse.Prop36SW.peelP p M₁ M₂ A γ' t' s₀) M₁ q a'
          ((Fintype.equivFin
            (Work.Peluse.UControl.FamIdx (Work.Peluse.Prop36SW.peelKω kω s₀))).symm j) := by
  simp only [famPre, Work.Peluse.Prop36SW.pDirFamG, Work.Peluse.Prop36SW.pDirG,
    Work.Peluse.Prop36SW.peelP]

/-- `uPre` computes the iterated difference of the peel data at `q`. -/
lemma uPre_eq_peelG {ι : Type} [Fintype ι] [DecidableEq ι] {P : Type} [DecidableEq P]
    (p : ι → P → ℤ) (M₁ M₂ : ℕ) (A : Finset P) (γ' : ℝ) (t' : ℕ)
    (s₀ : Work.Peluse.UControl.Slot ι (fun _ => 1)) (g : P → ℤ → ℂ)
    (q : Work.Peluse.Prop36SW.PeelParam p M₁ M₂ A γ' t' s₀) :
    uPre p M₁ M₂ γ' s₀ t' g q.1.1.1 q.2
      = Work.Peluse.Prop36SW.peelG p M₁ M₂ A γ' t' s₀ g q := by
  simp only [uPre, Work.Peluse.Prop36SW.peelG]

/-- **The bridge to the short family.**  At a parameter `a ∈ A` and a box point `b`, the family of
the peeled state with direction parameters `a' = b|_PeelSlot` is the ladder's short family. -/
lemma boxNormPow_famPre_restrict_eq_short {ι : Type} [Fintype ι] [DecidableEq ι]
    (kω : Work.Peluse.UControl.SlotSet ι (fun _ => 1) → ℕ) {P : Type} [DecidableEq P]
    (p : ι → P → ℤ) (M₁ M₂ : ℕ) (A : Finset P) (γ' : ℝ) (t' : ℕ)
    (s₀ : Work.Peluse.UControl.Slot ι (fun _ => 1)) {a : P} (ha : a ∈ A)
    {b : Work.Peluse.UControl.Slot ι (fun _ => 1) → ℤ}
    (hb : b ∈ Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) M₂)
    (sh : (j : Fin t') → PeelShift p M₁ M₂ γ' s₀ a × PeelShift p M₁ M₂ γ' s₀ a)
    (S : Finset ℤ) (f : ℤ → ℂ) :
    Work.Peluse.boxNormPow (Fintype.card (Work.Peluse.UControl.FamIdx (Work.Peluse.Prop36SW.peelKω kω s₀)))
        (famPre kω p M₁ s₀ a
          (fun s' : Work.Peluse.UControl.Slot (Work.Peluse.Prop36SW.PeelSlot s₀) (fun _ => 1) =>
            b s'.1.1)) S f
      = Work.Peluse.boxNormPow (Fintype.card (Work.Peluse.Prop36SW.ShortIdx (k := fun _ : ι => 1) kω s₀))
        (Work.Peluse.Prop36SW.shortFamG kω p M₁ a b s₀) S f := by
  have hfam : famPre kω p M₁ s₀ a
        (fun s' : Work.Peluse.UControl.Slot (Work.Peluse.Prop36SW.PeelSlot s₀) (fun _ => 1) =>
          b s'.1.1)
      = (fun j => Work.Peluse.Prop36SW.pDirFamG
          (Work.Peluse.Prop36SW.peelP p M₁ M₂ A γ' t' s₀) M₁ ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, sh⟩
          (fun s' : Work.Peluse.UControl.Slot (Work.Peluse.Prop36SW.PeelSlot s₀) (fun _ => 1) =>
            b s'.1.1)
          ((Fintype.equivFin
            (Work.Peluse.UControl.FamIdx (Work.Peluse.Prop36SW.peelKω kω s₀))).symm j)) :=
    funext fun j => famPre_eq_pDirFamG kω p M₁ M₂ A γ' t' s₀ ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, sh⟩ _ j
  rw [hfam, Work.Peluse.Prop36SW.boxNormPowPeelFamily kω p M₁ M₂ A γ' t' s₀
    ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, sh⟩ S f]

/-- The conclusion's direction family of the peel, in `Fin`-normal form. -/
def conclFam {ι : Type} [Fintype ι] [DecidableEq ι] {P : Type} (p : ι → P → ℤ)
    (M₁ M₂ : ℕ) (γ' : ℝ) (s₀ : Work.Peluse.UControl.Slot ι (fun _ => 1)) (t' : ℕ)
    (kω : Work.Peluse.UControl.SlotSet ι (fun _ => 1) → ℕ) (a : P)
    (b : Work.Peluse.UControl.Slot ι (fun _ => 1) → ℤ) :
    Fin (Fintype.card (Work.Peluse.UControl.ConclIdx s₀ kω t')) → Finset ℤ :=
  fun i => Work.Peluse.Prop36SW.conclDirG p M₁ M₂ γ' s₀ t' a b
    ((Fintype.equivFin (Work.Peluse.UControl.ConclIdx s₀ kω t')).symm i)

/-- The direction family of the peeled state, in `Fin`-normal form. -/
def peelFam {ι : Type} [Fintype ι] [DecidableEq ι] {P : Type} [DecidableEq P]
    (kω : Work.Peluse.UControl.SlotSet ι (fun _ => 1) → ℕ) (p : ι → P → ℤ) (M₁ M₂ : ℕ)
    (A : Finset P) (γ' : ℝ) (t' : ℕ) (s₀ : Work.Peluse.UControl.Slot ι (fun _ => 1))
    (q : Work.Peluse.Prop36SW.PeelParam p M₁ M₂ A γ' t' s₀)
    (a' : Work.Peluse.UControl.Slot (Work.Peluse.Prop36SW.PeelSlot s₀) (fun _ => 1) → ℤ) :
    Fin (Fintype.card (Work.Peluse.UControl.FamIdx (Work.Peluse.Prop36SW.peelKω kω s₀))) → Finset ℤ :=
  fun j => Work.Peluse.Prop36SW.pDirFamG (Work.Peluse.Prop36SW.peelP p M₁ M₂ A γ' t' s₀) M₁ q a'
    ((Fintype.equivFin
      (Work.Peluse.UControl.FamIdx (Work.Peluse.Prop36SW.peelKω kω s₀))).symm j)

/-- `famPre` is `peelFam` at the peel data `q` (the family does not depend on the box component of
`q`). -/
lemma famPre_eq_peelFam {ι : Type} [Fintype ι] [DecidableEq ι]
    (kω : Work.Peluse.UControl.SlotSet ι (fun _ => 1) → ℕ) {P : Type} [DecidableEq P]
    (p : ι → P → ℤ) (M₁ M₂ : ℕ) (A : Finset P) (γ' : ℝ) (t' : ℕ)
    (s₀ : Work.Peluse.UControl.Slot ι (fun _ => 1))
    (q : Work.Peluse.Prop36SW.PeelParam p M₁ M₂ A γ' t' s₀)
    (a' : Work.Peluse.UControl.Slot (Work.Peluse.Prop36SW.PeelSlot s₀) (fun _ => 1) → ℤ) :
    famPre kω p M₁ s₀ q.1.1.1 a' = peelFam kω p M₁ M₂ A γ' t' s₀ q a' :=
  funext fun j => famPre_eq_pDirFamG kω p M₁ M₂ A γ' t' s₀ q a' j

/-- `boxNormPow`, at the ambient `symIcc N`, of the peeled state's family at the old parameter `a`,
the new direction parameters `a'` and the shifts `sh`. -/
def famPow {ι : Type} [Fintype ι] [DecidableEq ι] {P : Type} [DecidableEq P]
    (kω : Work.Peluse.UControl.SlotSet ι (fun _ => 1) → ℕ) (p : ι → P → ℤ) (M₁ M₂ N : ℕ) (γ' : ℝ)
    (t' : ℕ) (s₀ : Work.Peluse.UControl.Slot ι (fun _ => 1)) (g : P → ℤ → ℂ) (a : P)
    (a' : Work.Peluse.UControl.Slot (Work.Peluse.Prop36SW.PeelSlot s₀) (fun _ => 1) → ℤ)
    (sh : (j : Fin t') → PeelShift p M₁ M₂ γ' s₀ a × PeelShift p M₁ M₂ γ' s₀ a) : ℝ :=
  Work.Peluse.boxNormPow (Fintype.card (Work.Peluse.UControl.FamIdx (Work.Peluse.Prop36SW.peelKω kω s₀)))
    (famPre kω p M₁ s₀ a a') (Work.Peluse.symIcc N) (uPre p M₁ M₂ γ' s₀ t' g a sh)

/-- `boxNormPow`, at the ambient `symIcc N`, of the ladder's *short* family at the old parameter
`a`, the box point `b` and the shifts `sh`. -/
def shortPow {ι : Type} [Fintype ι] [DecidableEq ι] {P : Type}
    (kω : Work.Peluse.UControl.SlotSet ι (fun _ => 1) → ℕ) (p : ι → P → ℤ) (M₁ M₂ N : ℕ) (γ' : ℝ)
    (t' : ℕ) (s₀ : Work.Peluse.UControl.Slot ι (fun _ => 1)) (g : P → ℤ → ℂ) (a : P)
    (b : Work.Peluse.UControl.Slot ι (fun _ => 1) → ℤ)
    (sh : (j : Fin t') → PeelShift p M₁ M₂ γ' s₀ a × PeelShift p M₁ M₂ γ' s₀ a) : ℝ :=
  Work.Peluse.boxNormPow
    (Fintype.card (Work.Peluse.Prop36SW.ShortIdx (k := fun _ : ι => 1) kω s₀))
    (Work.Peluse.Prop36SW.shortFamG kω p M₁ a b s₀) (Work.Peluse.symIcc N)
    (uPre p M₁ M₂ γ' s₀ t' g a sh)

/-- **The bridge**: the box-norm power of the peeled family at the direction parameters obtained by
restricting a box point `b` is the box-norm power of the ladder's short family at `b`. -/
lemma famPow_restrict_eq_shortPow {ι : Type} [Fintype ι] [DecidableEq ι] {P : Type} 
    [DecidableEq P] (kω : Work.Peluse.UControl.SlotSet ι (fun _ => 1) → ℕ) (p : ι → P → ℤ)
    (M₁ M₂ N : ℕ) (A : Finset P) (γ' : ℝ) (t' : ℕ)
    (s₀ : Work.Peluse.UControl.Slot ι (fun _ => 1)) (g : P → ℤ → ℂ) {a : P} (ha : a ∈ A)
    {b : Work.Peluse.UControl.Slot ι (fun _ => 1) → ℤ}
    (hb : b ∈ Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) M₂)
    (sh : (j : Fin t') → PeelShift p M₁ M₂ γ' s₀ a × PeelShift p M₁ M₂ γ' s₀ a) :
    famPow kω p M₁ M₂ N γ' t' s₀ g a
        (fun s' : Work.Peluse.UControl.Slot (Work.Peluse.Prop36SW.PeelSlot s₀) (fun _ => 1) =>
          b s'.1.1) sh
      = shortPow kω p M₁ M₂ N γ' t' s₀ g a b sh :=
  boxNormPow_famPre_restrict_eq_short kω p M₁ M₂ A γ' t' s₀ ha hb sh (Work.Peluse.symIcc N)
    (uPre p M₁ M₂ γ' s₀ t' g a sh)

/-- The `boxNorm` of the peeled family at the enlarged ambient `symIcc (peelN N D t' γ')`, for the
peel data `q` and the direction parameters `a'`. -/
def famNorm {ι : Type} [Fintype ι] [DecidableEq ι] {P : Type} [DecidableEq P]
    (kω : Work.Peluse.UControl.SlotSet ι (fun _ => 1) → ℕ) (p : ι → P → ℤ) (M₁ M₂ N D : ℕ)
    (A : Finset P) (γ' : ℝ) (t' : ℕ) (s₀ : Work.Peluse.UControl.Slot ι (fun _ => 1))
    (g : P → ℤ → ℂ)
    (q : Work.Peluse.Prop36SW.PeelParam p M₁ M₂ A γ' t' s₀)
    (a' : Work.Peluse.UControl.Slot (Work.Peluse.Prop36SW.PeelSlot s₀) (fun _ => 1) → ℤ) : ℝ :=
  Work.Peluse.boxNorm (Fintype.card (Work.Peluse.UControl.FamIdx (Work.Peluse.Prop36SW.peelKω kω s₀)))
    (peelFam kω p M₁ M₂ A γ' t' s₀ q a')
    (Work.Peluse.symIcc (Work.Peluse.Prop36SW.peelN N D t' γ'))
    (Work.Peluse.Prop36SW.peelG p M₁ M₂ A γ' t' s₀ g q)

/-- The `boxNormPow` of the peeled family at the ambient `symIcc N`, for the peel data `q`: it is
`famPow` at the data of `q`. -/
lemma famNorm_eq_famPow_peel {ι : Type} [Fintype ι] [DecidableEq ι] {P : Type} 
    [DecidableEq P] (kω : Work.Peluse.UControl.SlotSet ι (fun _ => 1) → ℕ) (p : ι → P → ℤ)
    (M₁ M₂ N : ℕ) (A : Finset P) (γ' : ℝ) (t' : ℕ)
    (s₀ : Work.Peluse.UControl.Slot ι (fun _ => 1)) (g : P → ℤ → ℂ)
    (q : Work.Peluse.Prop36SW.PeelParam p M₁ M₂ A γ' t' s₀)
    (a' : Work.Peluse.UControl.Slot (Work.Peluse.Prop36SW.PeelSlot s₀) (fun _ => 1) → ℤ) :
    Work.Peluse.boxNormPow (Fintype.card (Work.Peluse.UControl.FamIdx (Work.Peluse.Prop36SW.peelKω kω s₀)))
        (peelFam kω p M₁ M₂ A γ' t' s₀ q a') (Work.Peluse.symIcc N)
        (Work.Peluse.Prop36SW.peelG p M₁ M₂ A γ' t' s₀ g q)
      = famPow kω p M₁ M₂ N γ' t' s₀ g q.1.1.1 a' q.2 := by
  rw [famPow, ← famPre_eq_peelFam kω p M₁ M₂ A γ' t' s₀ q a',
    ← uPre_eq_peelG p M₁ M₂ A γ' t' s₀ g q]

/-- `famNorm` is the `boxNorm` of the same family at the enlarged ambient. -/
lemma famNorm_eq_boxNorm {ι : Type} [Fintype ι] [DecidableEq ι] {P : Type} 
    [DecidableEq P] (kω : Work.Peluse.UControl.SlotSet ι (fun _ => 1) → ℕ) (p : ι → P → ℤ)
    (M₁ M₂ N D : ℕ) (A : Finset P) (γ' : ℝ) (t' : ℕ)
    (s₀ : Work.Peluse.UControl.Slot ι (fun _ => 1)) (g : P → ℤ → ℂ)
    (q : Work.Peluse.Prop36SW.PeelParam p M₁ M₂ A γ' t' s₀)
    (a' : Work.Peluse.UControl.Slot (Work.Peluse.Prop36SW.PeelSlot s₀) (fun _ => 1) → ℤ) :
    famNorm kω p M₁ M₂ N D A γ' t' s₀ g q a'
      = Work.Peluse.boxNorm
          (Fintype.card (Work.Peluse.UControl.FamIdx (Work.Peluse.Prop36SW.peelKω kω s₀)))
          (fun j => Work.Peluse.Prop36SW.pDirFamG
            (Work.Peluse.Prop36SW.peelP p M₁ M₂ A γ' t' s₀) M₁ q a'
            ((Fintype.equivFin
              (Work.Peluse.UControl.FamIdx (Work.Peluse.Prop36SW.peelKω kω s₀))).symm j))
          (Work.Peluse.symIcc (Work.Peluse.Prop36SW.peelN N D t' γ'))
          (Work.Peluse.Prop36SW.peelG p M₁ M₂ A γ' t' s₀ g q) := rfl

end

end Work.Peluse.Prop36SW
