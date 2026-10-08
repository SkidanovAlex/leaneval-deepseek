import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The join of two normal nilpotent subgroups is nilpotent

This file proves `Work.Fitting.nilpotent_sup_of_normal`: in a group `X`, if `H` and `K` are
normal nilpotent subgroups, then `H ⊔ K` is nilpotent.  This is the classical "Fitting"
closure property of normal nilpotent subgroups (Fitting's theorem).

## The argument

Write `γ_n(S) = S.lowerCentralSeries (n-1)` for the lower central series of a subgroup `S`,
and set `gammaSeq S 0 = ⊤`, `gammaSeq S (n+1) = γ_{n+1}(S)` (i.e. `S.lowerCentralSeries n`),
so that `gammaSeq` is antitone with `gammaSeq S 0 = ⊤` and `gammaSeq S 1 = S`.

Since `H` and `K` are normal in the ambient group `X`, every term `gammaSeq H a` and
`gammaSeq K b` is normal.  The point of the proof is the two-parameter family

  `fittingSeries H K k = ⨆_{a+b=k} (gammaSeq H a ⊓ gammaSeq K b)`.

For normal subgroups the commutator distributes over joins
(`Subgroup.commutator_sup_left/right`, and `commutator_iSup_le` below), and one checks

  `⁅gammaSeq H a ⊓ gammaSeq K b, H⁆ ≤ gammaSeq H (a+1) ⊓ gammaSeq K b`,
  `⁅gammaSeq H a ⊓ gammaSeq K b, K⁆ ≤ gammaSeq H a ⊓ gammaSeq K (b+1)`,

so that `⁅fittingSeries H K k, H ⊔ K⁆ ≤ fittingSeries H K (k+1)`: the family
`fittingSeries H K` is a descending central series of `H ⊔ K`.

If `H.lowerCentralSeries c = ⊥` and `K.lowerCentralSeries d = ⊥`, then for `k = c+d+2` every
pair `(a,b)` with `a+b=k` has `a ≥ c+1` or `b ≥ d+1`, hence
`fittingSeries H K (c+d+2) = ⊥`.  Consequently the lower central series of `H ⊔ K` vanishes,
which is exactly nilpotency.
-/

set_option linter.style.haveILetI false

open scoped commutatorElement
open Subgroup

namespace Work.Fitting

/-- `gammaSeq H n` is the `n`-th term of the lower central series of `H`, computed in the
ambient group, with the convention `gammaSeq H 0 = ⊤` and `gammaSeq H (n+1) = γ_{n+1}(H)`. -/
def gammaSeq {G : Type*} [Group G] (H : Subgroup G) : ℕ → Subgroup G
  | 0 => ⊤
  | (n + 1) => H.lowerCentralSeries n

@[simp] theorem gammaSeq_zero {G : Type*} [Group G] (H : Subgroup G) : gammaSeq H 0 = ⊤ := rfl
@[simp] theorem gammaSeq_succ {G : Type*} [Group G] (H : Subgroup G) (n : ℕ) :
    gammaSeq H (n + 1) = H.lowerCentralSeries n := rfl

/-- Every term of `gammaSeq H` is normal in the ambient group when `H` is. -/
theorem gammaSeq_normal {G : Type*} [Group G] (H : Subgroup G) [H.Normal] (n : ℕ) :
    (gammaSeq H n).Normal := by
  cases n with
  | zero => exact Subgroup.normal_top
  | succ n => exact Subgroup.lowerCentralSeries_normal H n

/-- `⁅gammaSeq H n, H⁆ ≤ gammaSeq H (n+1)`. -/
theorem commutator_gammaSeq_le {G : Type*} [Group G] (H : Subgroup G) [H.Normal] (n : ℕ) :
    ⁅gammaSeq H n, H⁆ ≤ gammaSeq H (n + 1) := by
  cases n with
  | zero => exact Subgroup.commutator_le_right (H₁ := ⊤) (H₂ := H)
  | succ n => exact le_of_eq (Subgroup.lowerCentralSeries_succ H n)

/-- `gammaSeq H` is antitone. -/
theorem gammaSeq_antitone {G : Type*} [Group G] (H : Subgroup G) : Antitone (gammaSeq H) := by
  refine antitone_nat_of_succ_le ?_
  intro n
  cases n with
  | zero => exact le_top
  | succ n => exact Subgroup.lowerCentralSeries_antitone H (Nat.le_succ n)

/-- Once the lower central series of `H` has reached `⊥`, all later terms of `gammaSeq H`
vanish (the first such term being `gammaSeq H (c+1)`). -/
theorem gammaSeq_eq_bot_of {G : Type*} [Group G] (H : Subgroup G) {c : ℕ}
    (hc : H.lowerCentralSeries c = ⊥) {n : ℕ} (hn : c + 1 ≤ n) : gammaSeq H n = ⊥ := by
  rcases n with _ | n
  · exact absurd hn (by omega)
  · rw [gammaSeq_succ]
    have h : H.lowerCentralSeries n ≤ H.lowerCentralSeries c :=
      Subgroup.lowerCentralSeries_antitone H (by omega)
    rw [hc] at h
    exact le_bot_iff.mp h

/-- The commutator with a fixed normal subgroup distributes over an arbitrary join of normal
subgroups: `⁅⨆ i, f i, Y⁆ ≤ ⨆ i, ⁅f i, Y⁆`. -/
theorem commutator_iSup_le {G : Type*} [Group G] {ι : Type*} (f : ι → Subgroup G) (Y : Subgroup G)
    (hf : ∀ i, (f i).Normal) (hY : Y.Normal) :
    ⁅(⨆ i, f i), Y⁆ ≤ ⨆ i, ⁅f i, Y⁆ := by
  have hRnorm : (⨆ i, ⁅f i, Y⁆).Normal := by
    haveI : ∀ i, (⁅f i, Y⁆).Normal := fun i => by haveI := hf i; haveI := hY; infer_instance
    infer_instance
  set R : Subgroup G := ⨆ i, ⁅f i, Y⁆ with hRdef
  let T : Subgroup G :=
  { carrier := {x | ∀ y ∈ Y, ⁅x, y⁆ ∈ R}
    one_mem' := by intro y hy; simp
    mul_mem' := by
      intro a b ha hb y hy
      rw [commutatorElement_mul_left_eq_conj_mul]
      exact Subgroup.mul_mem _ (hRnorm.conj_mem _ (hb y hy) a) (ha y hy)
    inv_mem' := by
      intro a ha y hy
      rw [commutatorElement_inv_left]
      have h1 : ⁅y, a⁆ ∈ R := by simpa using R.inv_mem (ha y hy)
      simpa using hRnorm.conj_mem _ h1 a⁻¹ }
  have hle : (⨆ i, f i) ≤ T := by
    apply iSup_le
    intro i x hx
    intro y hy
    exact le_iSup (fun i => ⁅f i, Y⁆) i (commutator_mem_commutator hx hy)
  rw [Subgroup.commutator_le]
  intro x hx y hy
  exact hle hx y hy

/-- The two-parameter family `fittingSeries H K k = ⨆_{a+b=k} (gammaSeq H a ⊓ gammaSeq K b)`
(when `a+b > k` the term `gammaSeq K (k-a)` is read with truncated subtraction, which only adds
the harmless terms `gammaSeq H a`, `a > k`).

This is the descending central series of `H ⊔ K` used to prove Fitting's theorem. -/
def fittingSeries {G : Type*} [Group G] (H K : Subgroup G) (k : ℕ) : Subgroup G :=
  ⨆ p : {p : ℕ × ℕ // p.1 + p.2 = k}, (gammaSeq H p.1.1 ⊓ gammaSeq K p.1.2)

/-- Every term of `fittingSeries H K` is normal when `H` and `K` are. -/
theorem fittingSeries_normal {G : Type*} [Group G] (H K : Subgroup G) [H.Normal] [K.Normal]
    (k : ℕ) : (fittingSeries H K k).Normal := by
  rw [fittingSeries]
  haveI : ∀ p : {p : ℕ × ℕ // p.1 + p.2 = k},
      (gammaSeq H p.1.1 ⊓ gammaSeq K p.1.2).Normal := by
    intro p
    haveI := gammaSeq_normal H p.1.1
    haveI := gammaSeq_normal K p.1.2
    infer_instance
  infer_instance

/-- `fittingSeries H K 0 = ⊤`. -/
theorem fittingSeries_zero {G : Type*} [Group G] (H K : Subgroup G) :
    fittingSeries H K 0 = ⊤ := by
  rw [fittingSeries]
  apply le_antisymm le_top
  have h := le_iSup (fun p : {p : ℕ × ℕ // p.1 + p.2 = 0} =>
      (gammaSeq H p.1.1 ⊓ gammaSeq K p.1.2)) ⟨(0, 0), rfl⟩
  simpa using h

/-- The defining property of the descending central series `fittingSeries H K`: the commutator
with `H ⊔ K` lowers the index by one. -/
theorem fittingSeries_step {G : Type*} [Group G] (H K : Subgroup G) [H.Normal] [K.Normal]
    (k : ℕ) : ⁅fittingSeries H K k, H ⊔ K⁆ ≤ fittingSeries H K (k + 1) := by
  haveI hsup : (H ⊔ K).Normal := Subgroup.sup_normal H K
  rw [fittingSeries]
  refine (commutator_iSup_le (fun p : {p : ℕ × ℕ // p.1 + p.2 = k} =>
      (gammaSeq H p.1.1 ⊓ gammaSeq K p.1.2)) (H ⊔ K) ?_ hsup).trans ?_
  · intro p
    haveI := gammaSeq_normal H p.1.1
    haveI := gammaSeq_normal K p.1.2
    infer_instance
  apply iSup_le
  intro p
  haveI hX : (gammaSeq H p.1.1 ⊓ gammaSeq K p.1.2).Normal := by
    haveI := gammaSeq_normal H p.1.1
    haveI := gammaSeq_normal K p.1.2
    infer_instance
  rw [Subgroup.commutator_sup_left (gammaSeq H p.1.1 ⊓ gammaSeq K p.1.2) H K]
  rw [fittingSeries]
  apply sup_le
  · refine (le_inf ?_ ?_).trans (le_iSup (fun q : {q : ℕ × ℕ // q.1 + q.2 = k+1} =>
        gammaSeq H q.1.1 ⊓ gammaSeq K q.1.2) ⟨(p.1.1 + 1, p.1.2), by have := p.2; omega⟩)
    · exact (Subgroup.commutator_mono_left inf_le_left).trans (commutator_gammaSeq_le H p.1.1)
    · exact (Subgroup.commutator_mono_left inf_le_right).trans
        ((Subgroup.commutator_mono_right le_top).trans
          (Subgroup.commutator_top_right_le_iff.mpr (gammaSeq_normal K p.1.2)))
  · refine (le_inf ?_ ?_).trans (le_iSup (fun q : {q : ℕ × ℕ // q.1 + q.2 = k+1} =>
        gammaSeq H q.1.1 ⊓ gammaSeq K q.1.2) ⟨(p.1.1, p.1.2 + 1), by have := p.2; omega⟩)
    · exact (Subgroup.commutator_mono_left inf_le_left).trans
        ((Subgroup.commutator_mono_right le_top).trans
          (Subgroup.commutator_top_right_le_iff.mpr (gammaSeq_normal H p.1.1)))
    · exact (Subgroup.commutator_mono_left inf_le_right).trans (commutator_gammaSeq_le K p.1.2)

/-- If `H` and `K` have nilpotency classes bounded by `c` and `d` in the sense
`H.lowerCentralSeries c = ⊥`, `K.lowerCentralSeries d = ⊥`, then `fittingSeries H K k`
vanishes for `k ≥ c+d+2`. -/
theorem fittingSeries_eq_bot {G : Type*} [Group G] (H K : Subgroup G) [H.Normal] [K.Normal]
    {c d k : ℕ} (hc : H.lowerCentralSeries c = ⊥) (hd : K.lowerCentralSeries d = ⊥)
    (hk : c + d + 2 ≤ k) : fittingSeries H K k = ⊥ := by
  rw [fittingSeries]
  apply iSup_eq_bot.mpr
  intro p
  have hp : p.1.1 + p.1.2 = k := p.2
  by_cases h : c + 1 ≤ p.1.1
  · rw [gammaSeq_eq_bot_of H hc h, bot_inf_eq]
  · have hk' : d + 1 ≤ p.1.2 := by omega
    rw [gammaSeq_eq_bot_of K hd hk', inf_bot_eq]

/-- The lower central series of `H ⊔ K` is bounded above by `fittingSeries H K`. -/
theorem lowerCentralSeries_le_fittingSeries {G : Type*} [Group G] (H K : Subgroup G) [H.Normal]
    [K.Normal] (n : ℕ) : (H ⊔ K).lowerCentralSeries n ≤ fittingSeries H K n := by
  induction n with
  | zero => rw [Subgroup.lowerCentralSeries_zero, fittingSeries_zero]; exact le_top
  | succ n ih =>
    rw [Subgroup.lowerCentralSeries_succ]
    exact (Subgroup.commutator_mono ih le_rfl).trans (fittingSeries_step H K n)

/-- **Fitting's theorem.** The join of two normal nilpotent subgroups is nilpotent. -/
theorem nilpotent_sup_of_normal {X : Type*} [Group X] (H K : Subgroup X) [H.Normal] [K.Normal]
    [Group.IsNilpotent ↥H] [Group.IsNilpotent ↥K] : Group.IsNilpotent ↥(H ⊔ K) := by
  obtain ⟨c, hc⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries H).mp inferInstance
  obtain ⟨d, hd⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries K).mp inferInstance
  refine (Subgroup.isNilpotent_iff_lowerCentralSeries (H ⊔ K)).mpr ⟨c + d + 2, ?_⟩
  refine le_bot_iff.mp ((lowerCentralSeries_le_fittingSeries H K (c + d + 2)).trans ?_)
  rw [fittingSeries_eq_bot H K hc hd (le_refl (c + d + 2))]

end Work.Fitting
